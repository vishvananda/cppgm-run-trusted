#include "pa12_internal.h"
#include "pa12_templates_function_support.h"

#include <algorithm>
#include <stdexcept>

using namespace std;

namespace pa12 {
namespace internal {

namespace {

bool record_has_nonpublic_field(TypePtr record)
{
	TypePtr bare = pa11::strip_cv(record);
	if (bare->kind != pa11::TypeKind::Record)
		return false;
	pa11::layout_record_type(bare);
	for (size_t i = 0; i < bare->fields.size(); ++i)
		if (bare->fields[i]->is_private ||
		    bare->fields[i]->is_protected_member)
			return true;
	return false;
}

bool is_destructor_binding(Binding* binding)
{
	return binding != NULL && !binding->name.empty() && binding->name[0] == '~';
}

bool same_virtual_instance_type(TypePtr left, TypePtr right);

void append_normalized_virtual_instance_arguments(
	vector<pa11::TemplateInstanceArgument>& out,
	const vector<pa11::TemplateInstanceArgument>& arguments)
{
	for (size_t i = 0; i < arguments.size(); ++i)
	{
		if (arguments[i].kind == pa11::TemplateInstanceArgumentKind::Pack)
		{
			append_normalized_virtual_instance_arguments(
				out,
				arguments[i].pack);
			continue;
		}
		out.push_back(arguments[i]);
	}
}

bool same_virtual_instance_arguments(
	const vector<pa11::TemplateInstanceArgument>& left,
	const vector<pa11::TemplateInstanceArgument>& right);

bool same_virtual_instance_argument(
	const pa11::TemplateInstanceArgument& left,
	const pa11::TemplateInstanceArgument& right)
{
	if (left.kind != right.kind)
		return false;
	if (left.kind == pa11::TemplateInstanceArgumentKind::Type)
		return same_virtual_instance_type(left.type, right.type);
	if (left.kind == pa11::TemplateInstanceArgumentKind::Value)
		return left.dependent == right.dependent &&
		       left.value_negated == right.value_negated &&
		       left.value == right.value &&
		       left.value_name == right.value_name &&
		       left.value_owner_template_name ==
			       right.value_owner_template_name &&
		       left.value_member_name == right.value_member_name &&
		       same_virtual_instance_type(left.type, right.type) &&
		       same_virtual_instance_arguments(
			       left.value_owner_template_arguments,
			       right.value_owner_template_arguments);
	if (left.kind == pa11::TemplateInstanceArgumentKind::Template)
		return left.template_name == right.template_name &&
		       left.dependent == right.dependent;
	if (left.pack.size() != right.pack.size())
		return false;
	for (size_t i = 0; i < left.pack.size(); ++i)
		if (!same_virtual_instance_argument(left.pack[i], right.pack[i]))
			return false;
	return true;
}

bool same_virtual_instance_arguments(
	const vector<pa11::TemplateInstanceArgument>& left,
	const vector<pa11::TemplateInstanceArgument>& right)
{
	vector<pa11::TemplateInstanceArgument> flat_left;
	vector<pa11::TemplateInstanceArgument> flat_right;
	append_normalized_virtual_instance_arguments(flat_left, left);
	append_normalized_virtual_instance_arguments(flat_right, right);
	if (flat_left.size() != flat_right.size())
		return false;
	for (size_t i = 0; i < flat_left.size(); ++i)
		if (!same_virtual_instance_argument(flat_left[i], flat_right[i]))
			return false;
	return true;
}

bool same_virtual_instance_type(TypePtr left, TypePtr right)
{
	if (pa11::same_type(left, right))
		return true;
	TypePtr l = pa11::strip_cv(left);
	TypePtr r = pa11::strip_cv(right);
	return l->kind == pa11::TypeKind::Record &&
	       r->kind == pa11::TypeKind::Record &&
	       l->is_template_specialization &&
	       r->is_template_specialization &&
	       !l->template_primary_name.empty() &&
	       l->template_primary_name == r->template_primary_name &&
	       same_virtual_instance_arguments(l->template_arguments,
	                                       r->template_arguments);
}

bool same_virtual_completion_record(TypePtr left, TypePtr right)
{
	if (left.get() == NULL || right.get() == NULL)
		return left.get() == right.get();
	if (left.get() == right.get())
		return true;
	return same_virtual_instance_type(left, right);
}

bool virtual_completion_active(const vector<TypePtr>& active, TypePtr type)
{
	for (size_t i = 0; i < active.size(); ++i)
		if (same_virtual_completion_record(active[i], type))
			return true;
	return false;
}

void stamp_template_member_function_symbol(Binding* binding)
{
	if (binding == NULL ||
	    binding->kind != BindingKind::Function ||
	    !binding->function_specialization_symbol.empty() ||
	    binding->owner == NULL ||
	    binding->owner->kind != ScopeKind::Class)
		return;
	TypePtr record = pa11::record_type_for_scope(binding->owner);
	record = record.get() != NULL ? pa11::strip_cv(record) : TypePtr();
	if (record.get() == NULL ||
	    record->kind != pa11::TypeKind::Record ||
	    !record->is_template_specialization)
		return;
	binding->function_specialization_symbol =
		abi_binding_symbol(binding, map<string, size_t>());
}

unsigned pointed_record_cv(TypePtr ptr)
{
	TypePtr bare = pa11::strip_cv(ptr);
	if (bare->kind != pa11::TypeKind::Pointer)
		return pa11::CV_NONE;
	TypePtr pointee = bare->base;
	return pointee->kind == pa11::TypeKind::Cv ? pointee->cv : pa11::CV_NONE;
}

bool same_parameter_tail(const vector<TypePtr>& left,
                         const vector<TypePtr>& right)
{
	if (left.size() != right.size())
		return false;
	if (left.empty())
		return true;
	if (pointed_record_cv(left[0]) != pointed_record_cv(right[0]))
		return false;
	for (size_t i = 1; i < left.size(); ++i)
		if (!pa11::same_type(left[i], right[i]))
			return false;
	return true;
}

bool record_derives_from(TypePtr source, TypePtr target)
{
	TypePtr wanted = pa11::strip_cv(target);
	for (TypePtr cur = pa11::strip_cv(source);
	     cur.get() != NULL && cur->kind == pa11::TypeKind::Record;
	     cur = cur->base.get() != NULL ? pa11::strip_cv(cur->base) : TypePtr())
		if (pa11::same_type(cur, wanted))
			return true;
	return false;
}

bool covariant_return(TypePtr derived_return, TypePtr base_return)
{
	TypePtr d = pa11::strip_cv(derived_return);
	TypePtr b = pa11::strip_cv(base_return);
	if (d->kind == pa11::TypeKind::Pointer &&
	    b->kind == pa11::TypeKind::Pointer)
	{
		TypePtr dr = pa11::strip_cv(d->base);
		TypePtr br = pa11::strip_cv(b->base);
		return dr->kind == pa11::TypeKind::Record &&
		       br->kind == pa11::TypeKind::Record &&
		       record_derives_from(dr, br);
	}
	if (d->kind == pa11::TypeKind::LValueReference &&
	    b->kind == pa11::TypeKind::LValueReference)
	{
		TypePtr dr = pa11::strip_cv(d->base);
		TypePtr br = pa11::strip_cv(b->base);
		return dr->kind == pa11::TypeKind::Record &&
		       br->kind == pa11::TypeKind::Record &&
		       record_derives_from(dr, br);
	}
	return false;
}

bool virtual_signature_matches(Binding* base, Binding* derived)
{
	if (base == NULL || derived == NULL ||
	    base->type.get() == NULL || derived->type.get() == NULL ||
	    base->type->kind != pa11::TypeKind::Function ||
	    derived->type->kind != pa11::TypeKind::Function)
		return false;
	if (is_destructor_binding(base) || is_destructor_binding(derived))
		return is_destructor_binding(base) && is_destructor_binding(derived);
	if (base->name != derived->name ||
	    base->type->variadic != derived->type->variadic ||
	    !same_parameter_tail(base->type->parameters, derived->type->parameters))
		return false;
	if (pa11::same_type(base->type->base, derived->type->base))
		return true;
	return covariant_return(derived->type->base, base->type->base);
}

bool class_has_polymorphic_base(TypePtr type)
{
	TypePtr bare = pa11::strip_cv(type);
	vector<TypePtr> bases = pa11::record_direct_bases(bare);
	for (size_t i = 0; i < bases.size(); ++i)
	{
		TypePtr base = bases[i].get() != NULL
			? pa11::strip_cv(bases[i]) : TypePtr();
		if (base.get() != NULL &&
		    base->kind == pa11::TypeKind::Record &&
		    base->is_polymorphic)
			return true;
	}
	return false;
}

TypePtr primary_polymorphic_base(TypePtr type)
{
	TypePtr bare = pa11::strip_cv(type);
	vector<TypePtr> bases = pa11::record_direct_bases(bare);
	for (size_t i = 0; i < bases.size(); ++i)
	{
		TypePtr base = bases[i].get() != NULL
			? pa11::strip_cv(bases[i]) : TypePtr();
		if (base.get() != NULL &&
		    base->kind == pa11::TypeKind::Record &&
		    base->is_polymorphic)
			return base;
	}
	return TypePtr();
}

bool has_declared_destructor(TypePtr record)
{
	TypePtr bare = pa11::strip_cv(record);
	if (bare->kind != pa11::TypeKind::Record || bare->scope == NULL)
		return false;
	return bare->scope->members.find("~" + bare->scope->name) !=
	       bare->scope->members.end();
}

bool inherits_virtual_destructor(TypePtr record)
{
	TypePtr bare = pa11::strip_cv(record);
	vector<TypePtr> pending = pa11::record_direct_bases(bare);
	vector<TypePtr> seen;
	for (size_t pending_i = 0; pending_i < pending.size(); ++pending_i)
	{
		TypePtr cur = pending[pending_i].get() != NULL
			? pa11::strip_cv(pending[pending_i]) : TypePtr();
		if (cur.get() == NULL || cur->kind != pa11::TypeKind::Record)
			continue;
		bool already = false;
		for (size_t i = 0; i < seen.size(); ++i)
			if (pa11::same_type(seen[i], cur))
				already = true;
		if (already)
			continue;
		seen.push_back(cur);
		for (size_t i = 0; i < cur->virtual_entries.size(); ++i)
		{
			Binding* fn = cur->virtual_entries[i].function;
			if (fn != NULL && is_destructor_binding(fn))
				return true;
		}
		vector<TypePtr> bases = pa11::record_direct_bases(cur);
		pending.insert(pending.end(), bases.begin(), bases.end());
	}
	return false;
}

size_t local_static_decl_span_begin(const vector<Token>& tokens,
                                    size_t begin,
                                    size_t end)
{
	size_t pos = begin;
	while (pos < end && tokens[pos].kind == posttoken::TokenKind::Simple &&
	       (tokens[pos].type == KW_STATIC ||
	        tokens[pos].type == KW_THREAD_LOCAL ||
	        tokens[pos].type == KW_CONST ||
	        tokens[pos].type == KW_VOLATILE ||
	        tokens[pos].type == KW_CONSTEXPR))
		++pos;
	return pos;
}

}  // namespace

void Parser::parse_declaration_into(Node& out)
{
	if (consume(OP_SEMICOLON))
		return;
	if (at_identifier() && current().source == "__extension__")
	{
		++pos_;
		parse_declaration_into(out);
		return;
	}
	if ((at(KW_INLINE) && lookahead(KW_NAMESPACE, 1)) || at(KW_NAMESPACE))
	{
		parse_namespace_or_alias(out);
		return;
	}
	if (at(KW_USING))
	{
		parse_using_family(out);
		return;
	}
	if (at(KW_STATIC_ASSERT))
	{
		parse_static_assert_declaration();
		return;
	}
	if (at(KW_EXTERN) && lookahead(OP_LBRACE, 1))
	{
		parse_linkage_specification(out);
		return;
	}
	if (at(KW_EXTERN) && pos_ + 1 < tokens_.size() &&
	    tokens_[pos_ + 1].kind == posttoken::TokenKind::Literal)
		{
			parse_linkage_specification(out);
			return;
		}
	if (at(KW_EXTERN) && lookahead(KW_TEMPLATE, 1))
	{
		parse_explicit_template_instantiation(true);
		return;
	}
	if (at(KW_TEMPLATE))
	{
		parse_template_declaration();
		return;
	}
	if (current_scope()->kind == ScopeKind::Namespace && at_identifier())
	{
		size_t guide_save = pos_;
		string guide_name = current().source;
		if (find_class_template(current_scope(), guide_name) != NULL)
		{
			++pos_;
			if (at(OP_LPAREN))
			{
				skip_balanced(OP_LPAREN, OP_RPAREN);
				if (consume(OP_ARROW))
				{
					while (!at_eof() && !at(OP_SEMICOLON))
						++pos_;
					expect(OP_SEMICOLON);
					return;
				}
			}
		}
		pos_ = guide_save;
	}
	parse_simple_or_function_declaration(out, true);
}


void Parser::skip_template_parameter_clause()
{
	expect(OP_LT);
	int depth = 1;
	while (depth > 0 && !at_eof())
	{
		if (consume(OP_LT))
			++depth;
		else if (consume(OP_GT))
			--depth;
		else
			++pos_;
	}
}

bool Parser::parse_structured_binding_declaration(const DeclSpecs& specs,
                                                 Node& out,
                                                 bool emit_node)
{
	if (!specs.auto_decl || !at(OP_LSQUARE))
		return false;
	vector<string> names;
	expect(OP_LSQUARE);
	while (!at(OP_RSQUARE))
	{
		names.push_back(consume_identifier());
		if (!consume(OP_COMMA))
			break;
	}
	expect(OP_RSQUARE);
	Expr init;
	if (consume(OP_ASS))
	{
		init = at(OP_LBRACE) ? parse_braced_init_list() : parse_expression();
		init.copy_initialization = true;
	}
	else
		throw runtime_error("structured binding requires initializer");
	expect(OP_SEMICOLON);
	Node node(current_scope()->kind == ScopeKind::Namespace ? "" :
	          "simple-declaration");
	DeclSpecs hidden_specs = specs;
	hidden_specs.no_unique_address_decl = false;
	Declarator hidden_declarator;
	hidden_declarator.has_name = true;
	hidden_declarator.name.name =
		"__structured_binding_" + to_string(local_type_counter_++);
	Binding* hidden = declare_one(hidden_specs,
	                              pa11::make_fundamental(FT_VOID),
	                              hidden_declarator,
	                              &init,
	                              false,
	                              node);
	if (hidden == NULL || hidden->type.get() == NULL)
		throw runtime_error("invalid structured binding object");
	TypePtr record = pa11::strip_cv(expression_object_type(hidden->type));
	if (record->kind != pa11::TypeKind::Record)
		throw runtime_error("structured binding requires class type");
	pa11::layout_record_type(record);
	if (names.size() != record->fields.size())
		throw runtime_error("structured binding element count mismatch");
	Expr object;
	object.valid = true;
	object.binding = hidden;
	object.type = hidden->type;
	object.category = ValueCategory::LValue;
	object.node = Node("id-expression lvalue " +
	                   pa11::describe_type(hidden->type) + " " +
	                   hidden->name);
	object.node.binding = hidden;
	object.node.type = hidden->type;
	object.node.category = object.category;
	annotate_expr_node(object);
	for (size_t i = 0; i < names.size(); ++i)
	{
		Binding* field = record->fields[i];
		Expr field_expr = make_member_expr(object, field->name, ".");
		DeclSpecs binding_specs;
		Declarator binding_declarator;
		binding_declarator.has_name = true;
		binding_declarator.name.name = names[i];
		binding_declarator.prefix.push_back(
			PtrOp(PtrKind::LValueReference, pa11::CV_NONE));
		declare_one(binding_specs,
		            field->type,
		            binding_declarator,
		            &field_expr,
		            false,
		            node);
	}
	if (emit_node && !node.children.empty())
	{
		if (node.line.empty())
			for (size_t i = 0; i < node.children.size(); ++i)
				add_child(out, node.children[i]);
		else
			add_child(out, node);
	}
	return true;
}

void Parser::parse_simple_or_function_declaration(Node& out, bool emit_node)
{
	bool declaration_no_unique_address = false;
	skip_attributes(&declaration_no_unique_address);
	if (parse_qualified_destructor_definition(out, emit_node))
		return;
	if (parse_qualified_conversion_definition(out, emit_node))
		return;
	if (parse_qualified_constructor_definition(out, emit_node))
		return;
	if (at(KW_INLINE) || at(KW_CONSTEXPR))
	{
		size_t qualified_member_save = pos_;
		bool inline_spec = false;
		bool constexpr_spec = false;
		for (;;)
		{
			if (consume(KW_INLINE))
			{
				inline_spec = true;
				continue;
			}
			if (consume(KW_CONSTEXPR))
			{
				constexpr_spec = true;
				continue;
			}
			break;
		}
		if (parse_qualified_destructor_definition(out, emit_node))
			return;
		if (parse_qualified_conversion_definition(out, emit_node))
			return;
		if (parse_qualified_constructor_definition(out,
		                                           emit_node,
		                                           inline_spec,
		                                           constexpr_spec))
			return;
		pos_ = qualified_member_save;
	}
	if (current_scope()->kind == ScopeKind::Class && at(KW_EXPLICIT))
	{
		bool explicit_member = consume_explicit_specifier();
		skip_attributes();
		bool constexpr_member = consume(KW_CONSTEXPR);
		if (parse_constructor_like_member(explicit_member, constexpr_member))
			return;
		if (parse_conversion_function_member(explicit_member, constexpr_member))
			return;
		throw runtime_error("explicit specifier without constructor or conversion");
	}
	if (current_scope()->kind == ScopeKind::Class && at(KW_CONSTEXPR))
	{
		size_t constexpr_save = pos_;
		consume(KW_CONSTEXPR);
		skip_attributes();
		bool explicit_member = consume_explicit_specifier();
		if (parse_constructor_like_member(explicit_member, true))
			return;
		if (parse_conversion_function_member(explicit_member, true))
			return;
		pos_ = constexpr_save;
	}
	if (parse_conversion_function_member())
		return;
	if (parse_constructor_like_member())
		return;
	size_t decl_start = pos_;
	DeclSpecs specs = parse_decl_specifier_seq(false);
	specs.no_unique_address_decl =
		specs.no_unique_address_decl || declaration_no_unique_address;
	TypePtr base = type_from_decl_specs(specs);
	if (parse_structured_binding_declaration(specs, out, emit_node))
		return;
	if (consume(OP_SEMICOLON))
	{
		if (current_scope()->kind != ScopeKind::Namespace)
		{
			TypePtr bare = pa11::strip_cv(base);
			Node simple("simple-declaration");
			if (bare->kind == pa11::TypeKind::Record &&
			    bare->name.find("__anonymous_union_type__") == 0)
			{
				string storage_name = bare->name;
				const string prefix = "__anonymous_union_type__";
				storage_name.replace(0,
				                     prefix.size(),
				                     "__anonymous_union_storage__");
					Binding* storage = add_value(current_scope(),
					                             BindingKind::Variable,
					                             storage_name,
					                             bare);
					Node var("variable " + storage_name + " " +
					         pa11::describe_type(bare));
					try
					{
						if (ensure_default_constructor(bare) != NULL)
							add_child(var, default_constructor_action(storage));
					}
					catch (const runtime_error& err)
					{
						if (string(err.what()) !=
						    "member has no default constructor")
							throw;
					}
					add_child(simple, var);
				if (bare->scope != NULL)
					inject_anonymous_union_members(bare->scope, storage);
			}
			add_child(out, simple);
		}
		return;
	}

	if (current_scope()->kind == ScopeKind::Class && at(OP_COLON))
	{
		expect(OP_COLON);
		Expr width = parse_expression();
		if (!width.has_constant_value && !validating_template_definition_)
			throw runtime_error("invalid bit-field width");
		Binding* field = add_value(current_scope(),
		                           BindingKind::Variable,
		                           "__anonymous_bitfield_" + to_string(pos_),
		                           base);
		field->is_bit_field = true;
		field->bit_width = width.has_constant_value ? width.constant_value : 0;
		TypePtr record = pa11::record_type_for_scope(current_scope());
		if (record.get() != NULL)
			record->layout_valid = false;
		expect(OP_SEMICOLON);
		return;
	}

	Scope* declarator_scope = NULL;
	if (at(OP_COLON2) ||
	    (at_identifier() &&
	     (lookahead(OP_COLON2, 1) || lookahead(OP_LT, 1))))
	{
		size_t qualifier_save = pos_;
		try
		{
			Scope* qualifier = parse_nested_name_specifier(NULL);
			if (qualifier != NULL &&
			    qualifier->kind == ScopeKind::Class &&
			    !at(OP_STAR))
				declarator_scope = qualifier;
		}
		catch (const exception&)
		{
		}
		pos_ = qualifier_save;
	}
	vector<Scope*> saved_declarator_scopes;
	if (declarator_scope != NULL)
	{
		saved_declarator_scopes = scopes_;
		scopes_.push_back(declarator_scope);
	}
	Declarator declarator;
	try
	{
		declarator = parse_declarator(false);
	}
	catch (const exception&)
	{
		if (declarator_scope != NULL)
			scopes_ = saved_declarator_scopes;
		throw;
	}
		if (declarator_scope != NULL)
			scopes_ = saved_declarator_scopes;
		TypePtr probe_base = specs.auto_decl
			? pa11::make_cv(pa11::make_fundamental(FT_INT), specs.cv)
			: base;
		TypePtr declared_type = apply_declarator(declarator, probe_base);
		bool declares_function =
			declared_type->kind == pa11::TypeKind::Function;
		bool bit_field = false;
		uint64_t bit_width = 0;
	if (current_scope()->kind == ScopeKind::Class && consume(OP_COLON))
	{
		Expr width = parse_expression();
		if (!width.has_constant_value && !validating_template_definition_)
			throw runtime_error("invalid bit-field width");
		bit_field = true;
		bit_width = width.has_constant_value ? width.constant_value : 0;
	}
	for (;;)
	{
		if (starts_attribute())
		{
			skip_attributes(&specs.no_unique_address_decl);
			continue;
		}
		if (at_gnu_asm())
		{
			skip_gnu_asm();
			continue;
		}
		break;
	}
	if ((at(OP_LBRACE) || at(KW_TRY)) && declares_function)
	{
		Node node(current_scope()->kind == ScopeKind::Namespace ? "" :
		          "simple-declaration");
		bool defer_body =
			defer_function_template_bodies_ &&
			current_scope()->kind == ScopeKind::Namespace;
			Binding* function =
				declare_one(specs,
				            base,
				            declarator,
				            NULL,
				            !defer_body,
				            node);
			if (current_scope()->kind == ScopeKind::Class)
			{
				if (force_new_function_binding_ &&
				    active_class_instantiations_.empty() &&
				    function_template_candidate_instantiation_depth_ == 0)
				{
					parse_function_body(function, declarator, node);
					if (emit_node && !node.children.empty())
						add_child(out, node.children.back());
					else if (!node.children.empty())
						extra_lowir_nodes_.push_back(node.children.back());
					return;
				}
				const Suffix* suffix = declarator_function_suffix(declarator);
				PendingFunctionBody pending;
				pending.function = function;
			pending.node = node.children.back();
			if (suffix != NULL)
				pending.parameters = suffix->parameters;
			pending.body_pos = pos_;
			if (consume(KW_TRY))
			{
				skip_balanced(OP_LBRACE, OP_RBRACE);
				while (at(KW_CATCH))
				{
					consume(KW_CATCH);
					skip_balanced(OP_LPAREN, OP_RPAREN);
					skip_balanced(OP_LBRACE, OP_RBRACE);
				}
			}
			else
				skip_balanced(OP_LBRACE, OP_RBRACE);
			enqueue_pending_member_body(current_scope(), pending);
			if (force_new_function_binding_ && emit_node &&
			    !node.children.empty())
			{
				if (node.line.empty())
					add_child(out, node.children.back());
				else
					add_child(out, node);
			}
			return;
		}
		if (defer_body)
		{
			const Suffix* suffix = declarator_function_suffix(declarator);
			Node fn("function-definition " + qualified_decl_name(function) +
			        " " + pa11::describe_type(function->type));
			fn.binding = function;
			fn.type = function->type;
			PendingFunctionBody pending;
			pending.function = function;
			pending.node = fn;
			if (suffix != NULL)
				pending.parameters = suffix->parameters;
			pending.body_pos = pos_;
			if (consume(KW_TRY))
			{
				skip_balanced(OP_LBRACE, OP_RBRACE);
				while (at(KW_CATCH))
				{
					consume(KW_CATCH);
					skip_balanced(OP_LPAREN, OP_RPAREN);
					skip_balanced(OP_LBRACE, OP_RBRACE);
				}
			}
			else
				skip_balanced(OP_LBRACE, OP_RBRACE);
			enqueue_pending_function_body(pending);
			if (emit_node)
			{
				if (node.line.empty())
					add_child(out, node.children.back());
				else
					add_child(out, node);
			}
			return;
		}
		parse_function_body(function, declarator, node);
		if (emit_node)
		{
			if (node.line.empty())
				add_child(out, node.children.back());
			else
				add_child(out, node);
		}
		else if (current_scope()->kind == ScopeKind::Class &&
		         !node.children.empty())
			extra_lowir_nodes_.push_back(node.children.back());
		return;
	}

		if (at(OP_ASS) && lookahead(KW_DELETE, 1) && declares_function)
	{
		Node node(current_scope()->kind == ScopeKind::Namespace ? "" :
		          "simple-declaration");
		Binding* function =
			declare_one(specs, base, declarator, NULL, false, node);
		deleted_functions_.insert(function);
		for (size_t i = 0; i < node.children.size(); ++i)
			if (node.children[i].binding == function)
				node.children[i].token_text = "deleted";
		expect(OP_ASS);
		expect(KW_DELETE);
		expect(OP_SEMICOLON);
		if (emit_node && !node.children.empty())
		{
			if (node.line.empty())
			{
				for (size_t i = 0; i < node.children.size(); ++i)
					add_child(out, node.children[i]);
			}
			else
				add_child(out, node);
		}
		return;
	}

		if (at(OP_ASS) && lookahead(KW_DEFAULT, 1) && declares_function)
	{
		Node node(current_scope()->kind == ScopeKind::Namespace ? "" :
		          "simple-declaration");
		const QualifiedName& qname = declarator_name(declarator);
		bool defaulted_definition =
			(current_scope()->kind != ScopeKind::Class &&
			 qname.qualifier != NULL &&
			 qname.qualifier->kind == ScopeKind::Class) ||
			(current_scope()->kind == ScopeKind::Class &&
			 qname.name == "operator=");
		Binding* function =
			declare_one(specs,
			            base,
			            declarator,
			            NULL,
			            defaulted_definition,
			            node);
		expect(OP_ASS);
		expect(KW_DEFAULT);
		if (function != NULL)
			function->is_defaulted = true;
		expect(OP_SEMICOLON);
		if (defaulted_definition &&
		    function != NULL &&
		    !node.children.empty())
		{
			Node& fn = node.children.back();
			map<Binding*, vector<string> >::const_iterator names =
				function_parameter_names_.find(function);
			for (size_t i = 0; i < function->type->parameters.size(); ++i)
			{
				string pname = i == 0 ? "this" : "__param" + to_string(i);
				if (names != function_parameter_names_.end() &&
				    i < names->second.size() &&
				    !names->second[i].empty())
					pname = names->second[i];
				Node param("parameter " + pname + " " +
				           pa11::describe_type(function->type->parameters[i]));
				param.type = function->type->parameters[i];
				add_child(fn, param);
			}
			add_child(fn, Node("compound-statement"));
			Scope* member_scope =
				function->owner != NULL &&
				function->owner->kind == ScopeKind::Class
				? function->owner : qname.qualifier;
			if (member_scope != NULL &&
			    member_scope->kind == ScopeKind::Class &&
			    function->type.get() != NULL &&
			    function->type->kind == pa11::TypeKind::Function)
			{
				if (function->name == member_scope->name &&
				    function->type->parameters.size() == 1)
					function->is_noop_constructor = true;
				if (function->name == "~" + member_scope->name)
					function->is_noop_destructor = true;
			}
		}
		if (function != NULL &&
		    current_scope()->kind == ScopeKind::Class &&
		    function->name == "operator=" &&
		    function->type->kind == pa11::TypeKind::Function &&
		    function->type->parameters.size() == 2 &&
		    function->type->parameters[1]->kind ==
		    pa11::TypeKind::RValueReference)
		{
			defaulted_move_assignments_.push_back(function);
			TypePtr record = pa11::record_type_for_scope(current_scope());
			if (record.get() != NULL)
			{
				pa11::layout_record_type(record);
				for (size_t i = 0; i < record->fields.size(); ++i)
					if (pa11::type_has_const(record->fields[i]->type) ||
					    pa11::is_reference_type(record->fields[i]->type))
						deleted_functions_.insert(function);
			}
		}
		if (emit_node && !node.children.empty())
		{
			if (node.line.empty())
			{
				for (size_t i = 0; i < node.children.size(); ++i)
					add_child(out, node.children[i]);
			}
			else
				add_child(out, node);
		}
		else if (defaulted_definition &&
		         current_scope()->kind == ScopeKind::Class &&
		         !node.children.empty())
			extra_lowir_nodes_.push_back(node.children.back());
		return;
	}

		if (at(OP_ASS) &&
		    current_scope()->kind == ScopeKind::Class &&
		    declares_function)
	{
		Node node(current_scope()->kind == ScopeKind::Namespace ? "" :
		          "simple-declaration");
		Binding* function =
			declare_one(specs, base, declarator, NULL, false, node);
		expect(OP_ASS);
		Expr pure_value = parse_expression();
		if (!pure_value.has_constant_value || pure_value.constant_value != 0)
			throw runtime_error("unsupported function pure-specifier");
		if (function != NULL)
		{
			function->is_pure_virtual = true;
			function->is_virtual = true;
		}
		expect(OP_SEMICOLON);
		if (emit_node && !node.children.empty())
		{
			if (node.line.empty())
			{
				for (size_t i = 0; i < node.children.size(); ++i)
					add_child(out, node.children[i]);
			}
			else
				add_child(out, node);
		}
		return;
	}

	Expr init;
	bool has_init = false;
	bool brace_init = false;
	const QualifiedName& init_qname = declarator_name(declarator);
	bool initializer_ahead = at(OP_ASS) ||
	                         at(OP_LBRACE) ||
	                         (at(OP_LPAREN) && !declares_function);
	if (initializer_ahead &&
	    current_scope()->kind != ScopeKind::Namespace &&
	    current_scope()->kind != ScopeKind::Class &&
	    !specs.typedef_decl &&
	    !specs.auto_decl &&
	    !declares_function &&
	    init_qname.qualifier == NULL &&
	    !init_qname.name.empty())
	{
		TypePtr provisional_type = declared_type;
		if (specs.constexpr_decl &&
		    !pa11::is_reference_type(provisional_type) &&
		    provisional_type->kind != pa11::TypeKind::Function)
			provisional_type = pa11::make_cv(provisional_type,
			                                 pa11::CV_CONST);
		TypePtr provisional_bare = pa11::strip_cv(provisional_type);
		if (!(provisional_bare->kind == pa11::TypeKind::Array &&
		      provisional_bare->unknown_bound))
		{
			Binding* provisional_initializer_binding =
				add_value(current_scope(),
				          BindingKind::Variable,
				          init_qname.name,
				          provisional_type);
			provisional_initializer_bindings_.insert(
				provisional_initializer_binding);
		}
	}
	vector<Scope*> saved_initializer_scopes;
	bool pushed_initializer_scope = false;
	if (declarator_scope != NULL && !declares_function)
	{
		saved_initializer_scopes = scopes_;
		scopes_.push_back(declarator_scope);
		pushed_initializer_scope = true;
	}
	try
	{
	if (consume(OP_ASS))
	{
		if (at(OP_LBRACE))
		{
			has_init = true;
			init = parse_braced_init_list();
		}
		else
		{
			has_init = true;
			init = parse_expression();
		}
		if (has_init)
			init.copy_initialization = true;
	}
	else if ((brace_init = consume(OP_LBRACE)))
	{
		has_init = true;
		--pos_;
		init = parse_braced_init_list();
	}
		else if (at(OP_LPAREN) && !declares_function)
		{
		expect(OP_LPAREN);
		if (!at(OP_RPAREN))
		{
			vector<Expr> args = parse_argument_list();
				TypePtr decl_type = declared_type;
			if (pa11::strip_cv(decl_type)->kind == pa11::TypeKind::Record)
			{
				try
				{
					init = make_constructor_init_expr(decl_type, args, false);
				}
				catch (const runtime_error& err)
				{
					if (string(err.what()) != "no matching constructor" ||
					    args.size() != 1)
						throw;
					TypePtr src_record =
						pa11::strip_cv(expression_object_type(args[0].type));
					TypePtr dst_record = pa11::strip_cv(decl_type);
					if (src_record->kind != pa11::TypeKind::Record ||
					    !pa11::same_type(src_record, dst_record))
						throw;
					ensure_copy_move_constructor(dst_record,
					                             args[0].category == ValueCategory::XValue);
					init = args[0];
				}
			}
			else if (args.size() == 1)
				init = args[0];
			else
			{
				throw runtime_error("unsupported direct initializer");
			}
			has_init = true;
		}
		expect(OP_RPAREN);
	}
	}
	catch (...)
	{
		if (pushed_initializer_scope)
			scopes_ = saved_initializer_scopes;
		throw;
	}
	if (pushed_initializer_scope)
		scopes_ = saved_initializer_scopes;

	size_t decl_span_begin = local_static_decl_span_begin(tokens_,
	                                                      decl_start,
	                                                      pos_);
	Node node(current_scope()->kind == ScopeKind::Namespace ? "" :
	          "simple-declaration");
	Binding* first =
		declare_one(specs, base, declarator, has_init ? &init : NULL, false, node);
	if (first != NULL && first->is_local_static)
		first->local_static_discriminator =
			"tokens" + to_string(decl_span_begin + 1) + "_" +
			to_string(pos_);
	if (bit_field)
	{
		first->is_bit_field = true;
		first->bit_width = bit_width;
	}
	while (consume(OP_COMMA))
	{
		size_t next_begin = pos_;
		Declarator next = parse_declarator(false);
		TypePtr next_declared_type = apply_declarator(next, probe_base);
		Expr next_init;
		bool next_has_init =
			parse_trailing_declarator_initializer(next_declared_type, next_init);
		Binding* next_binding =
			declare_one(specs, base, next, next_has_init ? &next_init : NULL, false, node);
		if (next_binding != NULL && next_binding->is_local_static)
			next_binding->local_static_discriminator =
				"tokens" + to_string(next_begin + 1) + "_" +
				to_string(pos_);
	}
	skip_attributes(&specs.no_unique_address_decl);
	expect(OP_SEMICOLON);
	if (emit_node && !node.children.empty())
	{
		if (node.line.empty())
		{
			for (size_t i = 0; i < node.children.size(); ++i)
				add_child(out, node.children[i]);
		}
		else
			add_child(out, node);
	}
}

void Parser::validate_record_copy_initialization(TypePtr type, const Expr& init)
{
	TypePtr record = pa11::strip_cv(type);
	pa11::layout_record_type(record);
	TypePtr init_record = init.type.get() != NULL
		? pa11::strip_cv(expression_object_type(init.type)) : TypePtr();
	if (init_record.get() != NULL &&
	    init_record->kind == pa11::TypeKind::Record &&
	    pa11::same_type(init_record, record) &&
	    (init.node.direct_call != NULL || !init.braced_init_list))
		return;
	if (record->scope != NULL &&
	    init.node.direct_call != NULL &&
	    init.node.direct_call->owner == record->scope &&
	    init.node.direct_call->name == record->scope->name)
	{
		if (init.node.direct_call->is_explicit)
			throw runtime_error("explicit constructor in copy initialization");
		return;
	}
	if (init.braced_init_list && init.node.direct_call != NULL)
		return;
	if (init.braced_init_list && record->scope != NULL)
	{
		map<string, vector<Binding*> >::const_iterator ctors =
			record->scope->members.find(record->scope->name);
		if (ctors != record->scope->members.end())
		{
			for (size_t i = 0; i < ctors->second.size(); ++i)
			{
				Binding* ctor = ctors->second[i];
				if (ctor->kind == BindingKind::Function &&
				    ctor->type->kind == pa11::TypeKind::Function &&
				    !ctor->is_explicit &&
				    ctor->type->parameters.size() ==
					    init.node.children.size() + 1)
					return;
			}
		}
	}
	if (init.braced_init_list)
	{
		validate_aggregate_braced_initialization(record);
	}
	if (!init.braced_init_list &&
	    init_record.get() != NULL &&
	    init_record->kind == pa11::TypeKind::Record &&
	    !pa11::same_type(init_record, record))
	{
		try
		{
			Conversion conv = convert_to(init, type);
			if (conv.viable)
				return;
		}
		catch (const runtime_error&)
		{
		}
	}
	size_t arg_count = init.braced_init_list ? init.node.children.size() : 1;
	if (record->scope == NULL)
		return;
	map<string, vector<Binding*> >::const_iterator found =
		record->scope->members.find(record->scope->name);
	if (found == record->scope->members.end())
		return;
	for (size_t i = 0; i < found->second.size(); ++i)
	{
		Binding* ctor = found->second[i];
		if (ctor->kind != BindingKind::Function ||
		    !ctor->is_explicit ||
		    ctor->type->parameters.size() != arg_count + 1)
			continue;
		bool viable = true;
		for (size_t j = 0; j < arg_count; ++j)
		{
			Expr arg;
			if (init.braced_init_list)
			{
				arg.valid = true;
				arg.node = init.node.children[j];
				arg.type = arg.node.type;
				arg.category = arg.node.category;
				arg.binding = arg.node.binding;
			}
			else
				arg = init;
			try
			{
				Conversion conv =
					convert_to(arg, ctor->type->parameters[j + 1]);
				if (!conv.viable)
					viable = false;
			}
			catch (const runtime_error&)
			{
				viable = false;
			}
			if (!viable)
				break;
		}
		if (viable)
			throw runtime_error("explicit constructor in copy initialization");
	}
}

void Parser::validate_aggregate_braced_initialization(TypePtr record)
{
	TypePtr bare = pa11::strip_cv(record);
	if (bare->kind != pa11::TypeKind::Record)
		return;
	pa11::layout_record_type(bare);
	if (record_has_aggregate_blocking_constructor(bare))
		return;
	if (record_has_nonpublic_field(bare))
		throw runtime_error("non-public member disqualifies aggregate");
	for (size_t i = 0; i < bare->fields.size(); ++i)
		if (default_member_initializers_.find(bare->fields[i]) !=
		    default_member_initializers_.end())
			throw runtime_error(
				"default member initializer disqualifies aggregate");
}

Binding* Parser::find_overridden_virtual(TypePtr record, Binding* function) const
{
	TypePtr bare = pa11::strip_cv(record);
	vector<TypePtr> pending = pa11::record_direct_bases(bare);
	vector<TypePtr> seen;
	while (!pending.empty())
	{
		TypePtr cur = pending.back().get() != NULL
			? pa11::strip_cv(pending.back()) : TypePtr();
		pending.pop_back();
		if (cur.get() == NULL || cur->kind != pa11::TypeKind::Record)
			continue;
		bool already = false;
		for (size_t i = 0; i < seen.size(); ++i)
			if (pa11::same_type(seen[i], cur))
				already = true;
		if (already)
			continue;
		seen.push_back(cur);
		for (size_t i = 0; i < cur->virtual_entries.size(); ++i)
		{
			Binding* candidate = cur->virtual_entries[i].function;
			if (candidate != NULL &&
			    !cur->virtual_entries[i].deleting_entry &&
			    virtual_signature_matches(candidate, function))
				return candidate;
		}
		vector<TypePtr> bases = pa11::record_direct_bases(cur);
		pending.insert(pending.end(), bases.begin(), bases.end());
	}
	return NULL;
}

void Parser::complete_class_virtuals(TypePtr type)
{
	TypePtr bare = pa11::strip_cv(type);
	if (bare->kind != pa11::TypeKind::Record || bare->scope == NULL)
		return;
	if (virtual_completion_active(active_class_virtual_completions_, bare))
		return;
	active_class_virtual_completions_.push_back(bare);
	struct ActiveVirtualCompletionGuard
	{
		vector<TypePtr>& active;
		TypePtr key;
		ActiveVirtualCompletionGuard(vector<TypePtr>& active_records,
		                             TypePtr active_key)
			: active(active_records), key(active_key)
		{
		}
		~ActiveVirtualCompletionGuard()
		{
			for (size_t i = active.size(); i > 0; --i)
			{
				if (same_virtual_completion_record(active[i - 1], key))
				{
					active.erase(active.begin() + (i - 1));
					return;
				}
			}
		}
	} active_guard(active_class_virtual_completions_, bare);
	vector<TypePtr> direct_bases = pa11::record_direct_bases(bare);
	bool dependent_base_validation =
		validating_template_definition_ &&
		record_dependent_base_lookup_skips_.count(bare.get()) != 0;
	if (!dependent_base_validation)
	{
		for (size_t i = 0; i < direct_bases.size(); ++i)
		{
			TypePtr direct_base = direct_bases[i].get() != NULL
				? pa11::strip_cv(direct_bases[i]) : TypePtr();
			if (direct_base.get() != NULL &&
			    direct_base->kind == pa11::TypeKind::Record &&
			    direct_base.get() != bare.get())
			{
				complete_template_record(direct_base);
				complete_class_virtuals(direct_base);
			}
		}
	}
	if (!dependent_base_validation &&
	    inherits_virtual_destructor(bare) &&
	    !has_declared_destructor(bare))
		ensure_default_destructor(bare);
	auto demand_virtual_function_body = [this](Binding* member) {
		if (member == NULL ||
		    member->is_pure_virtual ||
		    validating_template_definition_ ||
		    function_template_candidate_instantiation_depth_ != 0)
			return;
		parse_pending_function_body(member);
		parse_pending_member_body(member);
		ensure_function_body_extra_node(member);
		if (member->aliased_binding != NULL)
		{
			parse_pending_function_body(member->aliased_binding);
			parse_pending_member_body(member->aliased_binding);
			ensure_function_body_extra_node(member->aliased_binding);
		}
	};
	bare->virtual_entries.clear();
	TypePtr direct_base = primary_polymorphic_base(bare);
	if (!dependent_base_validation &&
	    direct_base.get() != NULL &&
	    direct_base->kind == pa11::TypeKind::Record &&
	    direct_base->is_polymorphic)
	{
		bare->virtual_entries = direct_base->virtual_entries;
		bare->is_polymorphic = true;
	}
	bare->introduces_vptr =
		bare->is_polymorphic && !class_has_polymorphic_base(bare);
	for (size_t i = 0; i < bare->scope->binding_order.size(); ++i)
	{
		Binding* member = bare->scope->binding_order[i];
		if (member->kind != BindingKind::Function ||
		    member->is_static_member ||
		    member->name == bare->scope->name)
			continue;
		Binding* overridden = find_overridden_virtual(bare, member);
		if (overridden != NULL)
		{
			if (overridden->is_final_virtual)
				throw runtime_error("cannot override final virtual member");
			member->is_virtual = true;
			member->overrides_virtual = overridden;
			member->virtual_slot_index = overridden->virtual_slot_index;
			member->virtual_slot_width = overridden->virtual_slot_width;
			for (size_t j = 0; j < bare->virtual_entries.size(); ++j)
			{
				if (bare->virtual_entries[j].function == overridden)
					bare->virtual_entries[j].function = member;
			}
			demand_virtual_function_body(member);
			bare->is_polymorphic = true;
			continue;
		}
		if (member->is_override_specified && !dependent_base_validation)
			throw runtime_error("override requires virtual base member");
		if (!member->is_virtual)
			continue;
		member->virtual_slot_index =
			static_cast<int>(bare->virtual_entries.size());
		member->virtual_slot_width = is_destructor_binding(member) ? 2 : 1;
		bare->virtual_entries.push_back(pa11::VirtualTableEntry(member, false));
		if (is_destructor_binding(member))
			bare->virtual_entries.push_back(pa11::VirtualTableEntry(member, true));
		demand_virtual_function_body(member);
		bare->is_polymorphic = true;
	}
	bare->introduces_vptr =
		bare->is_polymorphic && !class_has_polymorphic_base(bare);
	bare->layout_valid = false;
}

Binding* Parser::declare_function_entity(const DeclSpecs& specs,
                                         Scope* target,
                                         const string& name,
                                         TypePtr type,
	                                         const Declarator& declarator,
	                                         bool function_definition,
	                                         bool nonstatic_member_function,
	                                         bool hidden_friend,
	                                         Node& out)
{
	const Suffix* suffix = declarator_function_suffix(declarator);
	int ref_qualifier = suffix != NULL ? suffix->ref_qualifier : 0;
		bool is_static_member =
			target->kind == ScopeKind::Class && !nonstatic_member_function;
		type = substitute_template_type(type);
		Binding* function = NULL;
	const bool namespace_function = target->kind == ScopeKind::Namespace;
	const bool current_c_linkage = current_language_linkage() == "c";
	const bool current_namespace_static =
		specs.static_decl && namespace_function;
	map<string, vector<Binding*> >::iterator found = target->members.find(name);
	if (!force_new_function_binding_ && found != target->members.end())
	{
		for (size_t i = 0; i < found->second.size(); ++i)
		{
			Binding* candidate = found->second[i];
			if (namespace_function &&
			    (current_c_linkage ||
			     (current_namespace_static &&
			      candidate->language_linkage == "c") ||
			     (current_c_linkage && candidate->is_namespace_static)))
			{
				if (candidate->kind == BindingKind::Variable &&
				    (candidate->language_linkage == "c" ||
				     candidate->is_namespace_static))
					throw runtime_error("conflicting C linkage declaration");
				if (candidate->kind == BindingKind::Function &&
				    (candidate->language_linkage == "c" ||
				     candidate->is_namespace_static))
				{
					bool same_function =
						candidate->language_linkage == "c" &&
						pa11::same_type(candidate->type, type) &&
						candidate->ref_qualifier == ref_qualifier &&
						candidate->is_static_member == is_static_member &&
						!candidate->is_namespace_static &&
						!current_namespace_static;
					if (!same_function)
						throw runtime_error("conflicting C linkage declaration");
				}
			}
			if (candidate->kind == BindingKind::Function &&
			    pa11::same_type(candidate->type, type) &&
			    candidate->ref_qualifier == ref_qualifier &&
			    candidate->is_static_member == is_static_member)
			{
				function = candidate;
				break;
			}
		}
	}
		if (function == NULL)
			function = hidden_friend
				? add_function_binding(target, name, type, true)
				: add_value(target, BindingKind::Function, name, type);
	if (!hidden_friend)
		function->is_hidden_friend = false;
	function->language_linkage = current_language_linkage();
	function->is_constexpr = function->is_constexpr || specs.constexpr_decl;
	function->is_namespace_static =
		function->is_namespace_static ||
		(specs.static_decl && target->kind == ScopeKind::Namespace);
	function->is_static_member = is_static_member;
	function->is_declared_inline =
		function->is_declared_inline ||
		specs.inline_decl ||
		specs.constexpr_decl;
	function->is_inline_definition =
		function->is_inline_definition ||
		(function_definition &&
		 (current_scope()->kind == ScopeKind::Class ||
		  function->is_declared_inline ||
		  specs.inline_decl ||
		  specs.constexpr_decl));
	function->is_private =
		target->kind == ScopeKind::Class &&
		!class_private_access_.empty() &&
		class_private_access_.back();
		function->is_protected_member =
			target->kind == ScopeKind::Class &&
			!class_protected_access_.empty() &&
			class_protected_access_.back();
			function->unwind_no = suffix != NULL && suffix->noexcept_decl;
			function->ref_qualifier = ref_qualifier;
			if (suffix != NULL && !suffix->abi_tags.empty())
				function->abi_tags = suffix->abi_tags;
			if (suffix != NULL &&
			    target->kind == ScopeKind::Class &&
		    constructor_name_matches_scope(target, name))
			for (size_t i = 0; i < suffix->parameters.size(); ++i)
				if (suffix->parameters[i].has_default)
					function->has_default_arguments = true;
		if (specs.auto_decl)
	{
		auto_return_functions_.insert(function);
		auto_return_patterns_[function] = type->base;
	}
	if (validating_template_definition_)
		function->is_dependent_template_artifact = true;
	if (target->kind == ScopeKind::Class && !is_static_member)
	{
		function->is_virtual = function->is_virtual || specs.virtual_decl;
		function->is_override_specified =
			function->is_override_specified ||
			(suffix != NULL && suffix->override_decl);
		function->is_final_virtual =
			function->is_final_virtual ||
			(suffix != NULL && suffix->final_decl);
	}
	if (!active_class_instantiation_dependent())
		stamp_template_member_function_symbol(function);
	if (suffix != NULL)
	{
		vector<Expr> defaults;
		vector<string> names;
		bool use_parameter_name_override =
			override_function_parameter_names_;
		vector<string> parameter_name_override =
			function_parameter_name_override_;
		if (use_parameter_name_override)
		{
			override_function_parameter_names_ = false;
			function_parameter_name_override_.clear();
		}
			map<Binding*, vector<Expr> >::const_iterator old_defaults =
				default_arguments_.find(function);
			map<Binding*, vector<string> >::const_iterator old_names =
				function_parameter_names_.find(function);
			vector<string> borrowed_names;
			bool have_borrowed_names = false;
			if (old_names == function_parameter_names_.end() &&
			    found != target->members.end())
				for (size_t j = 0; j < found->second.size(); ++j)
				{
					Binding* candidate = found->second[j];
					if (candidate == function ||
					    candidate->kind != BindingKind::Function ||
					    !pa11::same_type(candidate->type, type) ||
					    candidate->ref_qualifier != ref_qualifier ||
					    candidate->is_static_member != is_static_member)
						continue;
					map<Binding*, vector<string> >::const_iterator names =
						function_parameter_names_.find(candidate);
					if (names != function_parameter_names_.end())
					{
						borrowed_names = names->second;
						have_borrowed_names = true;
						break;
					}
				}
			if (use_parameter_name_override &&
			    is_static_member &&
			    old_names == function_parameter_names_.end())
				use_parameter_name_override = false;
			if (nonstatic_member_function)
			{
				defaults.push_back(Expr());
				names.push_back("this");
		}
		for (size_t i = 0; i < suffix->parameters.size(); ++i)
		{
			if (suffix->parameters[i].type.get() == NULL)
				continue;
			Expr default_value = suffix->parameters[i].default_value;
			string parameter_name = suffix->parameters[i].name;
			size_t slot = names.size();
			size_t override_slot =
				nonstatic_member_function &&
				parameter_name_override.size() == suffix->parameters.size()
				? i : slot;
			if (!default_value.valid &&
			    old_defaults != default_arguments_.end() &&
			    slot < old_defaults->second.size())
				default_value = old_defaults->second[slot];
			if (use_parameter_name_override &&
			    override_slot < parameter_name_override.size() &&
			    !parameter_name_override[override_slot].empty())
				parameter_name = parameter_name_override[override_slot];
				else if (parameter_name.empty() &&
				         old_names != function_parameter_names_.end() &&
				    slot < old_names->second.size())
					parameter_name = old_names->second[slot];
				else if (parameter_name.empty() &&
				         have_borrowed_names &&
				         slot < borrowed_names.size())
					parameter_name = borrowed_names[slot];
				defaults.push_back(default_value);
				names.push_back(parameter_name);
			}
			default_arguments_[function] = defaults;
			function_parameter_names_[function] = names;
			if (use_parameter_name_override)
				override_function_parameter_name_bindings_.insert(function);
	}
	string keyword = function_definition ? "function-definition " :
		"function-declaration ";
	Node fn(keyword + qualified_decl_name(function) + " " +
	        pa11::describe_type(type));
	fn.binding = function;
	fn.type = type;
	add_child(out, fn);
	return function;
}


}  // namespace internal
}  // namespace pa12
