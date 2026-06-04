#include "pa12_internal.h"

#include <stdexcept>

using namespace std;

namespace pa12 {
namespace internal {
namespace {

bool aggregate_blocking_constructor(Binding* binding)
{
	if (binding->kind != BindingKind::Function ||
	    binding->type->kind != pa11::TypeKind::Function)
		return false;
	if (binding->is_generated_default_constructor ||
	    binding->is_generated_aggregate_constructor ||
	    binding->is_generated_copy_move_constructor)
		return false;
	if (binding->is_defaulted && binding->type->parameters.size() == 1)
		return false;
	return true;
}

bool record_has_aggregate_blocking_constructor(TypePtr record)
{
	TypePtr bare = pa11::strip_cv(record);
	if (bare->kind != pa11::TypeKind::Record || bare->scope == NULL)
		return false;
	map<string, vector<Binding*> >::const_iterator found =
		bare->scope->members.find(bare->scope->name);
	if (found == bare->scope->members.end())
		return false;
	for (size_t i = 0; i < found->second.size(); ++i)
		if (aggregate_blocking_constructor(found->second[i]))
			return true;
	return false;
}

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
	TypePtr base = bare->base.get() != NULL ? pa11::strip_cv(bare->base) : TypePtr();
	return base.get() != NULL &&
	       base->kind == pa11::TypeKind::Record &&
	       base->is_polymorphic;
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
	TypePtr base = bare->base.get() != NULL ? pa11::strip_cv(bare->base) : TypePtr();
	for (TypePtr cur = base;
	     cur.get() != NULL && cur->kind == pa11::TypeKind::Record;
	     cur = cur->base.get() != NULL ? pa11::strip_cv(cur->base) : TypePtr())
	{
		for (size_t i = 0; i < cur->virtual_entries.size(); ++i)
		{
			Binding* fn = cur->virtual_entries[i].function;
			if (fn != NULL && is_destructor_binding(fn))
				return true;
		}
	}
	return false;
}

}  // namespace

void Parser::parse_declaration_into(Node& out)
{
	if (consume(OP_SEMICOLON))
		return;
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
	if (at(KW_TEMPLATE))
	{
		parse_template_declaration();
		return;
	}
	parse_simple_or_function_declaration(out, true);
}

void Parser::parse_namespace_or_alias(Node& out)
{
	bool inline_ns = consume(KW_INLINE);
	expect(KW_NAMESPACE);
	if (!inline_ns && at_identifier() && lookahead(OP_ASS, 1))
	{
		string alias = consume_identifier();
		expect(OP_ASS);
		Scope* target = parse_qualified_namespace_specifier();
		expect(OP_SEMICOLON);
		pa11::add_namespace_alias(current_scope(), alias, target);
		return;
	}

	string name;
	bool named = false;
	if (at_identifier())
	{
		named = true;
		name = consume_identifier();
	}
	expect(OP_LBRACE);
	Scope* child = NULL;
	if (named)
		child = pa11::get_or_create_namespace(current_scope(), name, inline_ns);
	else
	{
		if (current_scope()->unnamed_namespace == NULL)
		{
			current_scope()->unnamed_namespace =
				pa11::create_child_scope(current_scope(),
				                         ScopeKind::Namespace,
				                         "<unnamed>");
			pa11::add_using_directive(current_scope(),
			                          current_scope()->unnamed_namespace);
		}
		child = current_scope()->unnamed_namespace;
		name = "<unnamed>";
	}

	Node node("namespace-definition " + name);
	scopes_.push_back(child);
	while (!at(OP_RBRACE))
		parse_declaration_into(node);
	scopes_.pop_back();
	expect(OP_RBRACE);
	add_child(out, node);
}

void Parser::parse_using_family(Node& out)
{
	expect(KW_USING);
	if (consume(KW_NAMESPACE))
	{
		Scope* target = parse_qualified_namespace_specifier();
		expect(OP_SEMICOLON);
		pa11::add_using_directive(current_scope(), target);
		return;
	}
	if (at_identifier() && lookahead(OP_ASS, 1))
	{
		string name = consume_identifier();
		expect(OP_ASS);
		TypePtr type = parse_type_id();
		expect(OP_SEMICOLON);
		add_alias(current_scope(), name, type);
		Node node("type-alias " + name + " " + pa11::describe_type(type));
		add_child(out, node);
		return;
	}
	string spelling;
	Scope* qualifier = parse_nested_name_specifier(&spelling);
	string name = consume_identifier();
	expect(OP_SEMICOLON);
	vector<Binding*> targets = lookup_qualified_set(qualifier, name, pa11::LOOKUP_ANY);
	if (targets.empty())
		throw runtime_error("using declaration target not found");
	if (current_scope()->kind == ScopeKind::Class &&
	    qualifier->kind == ScopeKind::Class &&
	    name == qualifier->name)
	{
			TypePtr derived = pa11::record_type_for_scope(current_scope());
			TypePtr base = pa11::record_type_for_scope(qualifier);
			if (derived.get() == NULL || base.get() == NULL)
				throw runtime_error("invalid inheriting constructor");
			for (size_t i = 0; i < targets.size(); ++i)
			{
				Binding* inherited = targets[i];
				if (inherited->kind != BindingKind::Function ||
				    inherited->type->parameters.empty())
					continue;
				vector<TypePtr> params;
				params.push_back(pa11::make_pointer(derived));
				for (size_t j = 1; j < inherited->type->parameters.size(); ++j)
					params.push_back(inherited->type->parameters[j]);
				TypePtr fn_type = pa11::make_function(pa11::make_fundamental(FT_VOID),
				                                      params,
				                                      inherited->type->variadic);
				Binding* ctor = add_value(current_scope(),
				                          BindingKind::Function,
				                          current_scope()->name,
				                          fn_type);
				map<Binding*, vector<string> >::const_iterator nit =
					function_parameter_names_.find(inherited);
				vector<string> inherited_names =
					nit != function_parameter_names_.end()
					? nit->second : vector<string>();
				vector<string> ctor_names(1, "this");
				ctor->is_inline_definition = true;
				Node fn("function-definition " + qualified_decl_name(ctor) + " " +
				        pa11::describe_type(fn_type));
				fn.binding = ctor;
				fn.type = fn_type;
				Scope* function_scope =
					pa11::create_child_scope(current_scope(),
					                         ScopeKind::Function,
					                         ctor->name);
				Binding* this_binding =
					pa11::add_binding(function_scope,
					                  BindingKind::Parameter,
					                  "this",
					                  params[0]);
				Node this_node("parameter this " + pa11::describe_type(params[0]));
				this_node.binding = this_binding;
				this_node.type = params[0];
				add_child(fn, this_node);
				Node init("braced-init-list");
				for (size_t j = 1; j < params.size(); ++j)
				{
					string pname = j < inherited_names.size() &&
					               !inherited_names[j].empty()
						? inherited_names[j] : "__param" + to_string(j);
					ctor_names.push_back(pname);
					Binding* param =
						pa11::add_binding(function_scope,
						                  BindingKind::Parameter,
						                  pname,
						                  params[j]);
					Node param_node("parameter " + pname + " " +
					                pa11::describe_type(params[j]));
					param_node.binding = param;
					param_node.type = params[j];
					add_child(fn, param_node);
					Node arg("id-expression lvalue " +
					         pa11::describe_type(params[j]) + " " + pname);
					arg.binding = param;
					arg.type = params[j];
					arg.category = ValueCategory::LValue;
					add_child(init, arg);
				}
				Node body("compound-statement");
				Node base_action = make_base_init_action(base, &init);
				base_action.direct_call = inherited;
				add_child(body, base_action);
				add_child(fn, body);
				function_parameter_names_[ctor] = ctor_names;
				extra_lowir_nodes_.push_back(fn);
			}
			return;
		}
	for (size_t i = 0; i < targets.size(); ++i)
		pa11::add_using_declaration(current_scope(), name, targets[i]);
}

void Parser::parse_linkage_specification(Node& out)
{
	expect(KW_EXTERN);
	string language = current_language_linkage();
	if (at_literal())
	{
		if (current().source == "\"C\"")
			language = "c";
		else if (current().source == "\"C++\"")
			language = "cpp";
		++pos_;
	}
	if (consume(OP_LBRACE))
	{
		language_linkages_.push_back(language);
		while (!at(OP_RBRACE))
			parse_declaration_into(out);
		language_linkages_.pop_back();
		expect(OP_RBRACE);
		return;
	}
	language_linkages_.push_back(language);
	parse_simple_or_function_declaration(out, true);
	language_linkages_.pop_back();
}

void Parser::parse_template_declaration()
{
	expect(KW_TEMPLATE);
	skip_template_parameter_clause();
	Node ignored;
	parse_declaration_into(ignored);
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

void Parser::parse_simple_or_function_declaration(Node& out, bool emit_node)
{
	if (parse_qualified_destructor_definition(out, emit_node))
		return;
	if (parse_qualified_conversion_definition(out, emit_node))
		return;
	if (parse_qualified_constructor_definition(out, emit_node))
		return;
	if (current_scope()->kind == ScopeKind::Class && consume(KW_EXPLICIT))
	{
		if (parse_constructor_like_member(true))
			return;
		if (parse_conversion_function_member(true))
			return;
		throw runtime_error("explicit specifier without constructor or conversion");
	}
	if (parse_conversion_function_member())
		return;
	if (parse_constructor_like_member())
		return;
	DeclSpecs specs = parse_decl_specifier_seq(false);
	TypePtr base = type_from_decl_specs(specs);
	if (consume(OP_SEMICOLON))
	{
		if (current_scope()->kind != ScopeKind::Namespace)
		{
			TypePtr bare = pa11::strip_cv(base);
			Node simple("simple-declaration");
			if (bare->kind == pa11::TypeKind::Record &&
			    bare->tag == "union" &&
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
				if (ensure_default_constructor(bare) != NULL)
					add_child(var, default_constructor_action(storage));
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
		if (!width.has_constant_value)
			throw runtime_error("invalid bit-field width");
		Binding* field = add_value(current_scope(),
		                           BindingKind::Variable,
		                           "__anonymous_bitfield_" + to_string(pos_),
		                           base);
		field->is_bit_field = true;
		field->bit_width = width.constant_value;
		TypePtr record = pa11::record_type_for_scope(current_scope());
		if (record.get() != NULL)
			record->layout_valid = false;
		expect(OP_SEMICOLON);
		return;
	}

	Declarator declarator = parse_declarator(false);
	bool bit_field = false;
	uint64_t bit_width = 0;
	if (current_scope()->kind == ScopeKind::Class && consume(OP_COLON))
	{
		Expr width = parse_expression();
		if (!width.has_constant_value)
			throw runtime_error("invalid bit-field width");
		bit_field = true;
		bit_width = width.constant_value;
	}
	if (at(OP_LBRACE) && declarator_function_suffix(declarator) != NULL)
	{
		Node node(current_scope()->kind == ScopeKind::Namespace ? "" :
		          "simple-declaration");
		Binding* function =
			declare_one(specs, base, declarator, NULL, true, node);
		if (current_scope()->kind == ScopeKind::Class)
		{
			const Suffix* suffix = declarator_function_suffix(declarator);
			PendingFunctionBody pending;
			pending.function = function;
			pending.node = node.children.back();
			if (suffix != NULL)
				pending.parameters = suffix->parameters;
			pending.body_pos = pos_;
			skip_balanced(OP_LBRACE, OP_RBRACE);
			pending_member_bodies_[current_scope()].push_back(pending);
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

	if (at(OP_ASS) && lookahead(KW_DELETE, 1) &&
	    declarator_function_suffix(declarator) != NULL)
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

	if (at(OP_ASS) && lookahead(KW_DEFAULT, 1) &&
	    declarator_function_suffix(declarator) != NULL)
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
	    declarator_function_suffix(declarator) != NULL)
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
	else if (at(OP_LPAREN) && !declarator_function_suffix(declarator))
	{
		expect(OP_LPAREN);
		if (!at(OP_RPAREN))
		{
			vector<Expr> args = parse_argument_list();
			TypePtr decl_type = apply_declarator(declarator, base);
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

	Node node(current_scope()->kind == ScopeKind::Namespace ? "" :
	          "simple-declaration");
	Binding* first =
		declare_one(specs, base, declarator, has_init ? &init : NULL, false, node);
	if (bit_field)
	{
		first->is_bit_field = true;
		first->bit_width = bit_width;
	}
	while (consume(OP_COMMA))
	{
		Declarator next = parse_declarator(false);
		Expr next_init;
		bool next_has_init = false;
		if (consume(OP_ASS))
		{
			next_has_init = true;
			next_init = at(OP_LBRACE) ? parse_braced_init_list() :
				parse_expression();
			next_init.copy_initialization = true;
		}
		declare_one(specs, base, next, next_has_init ? &next_init : NULL, false, node);
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
}

bool Parser::parse_friend_declaration()
{
	if (current_scope()->kind != ScopeKind::Class || !at(KW_FRIEND))
		return false;
	Scope* class_scope = current_scope();
	expect(KW_FRIEND);
	if (starts_class_key())
	{
		ETokenType key = current().type;
		++pos_;
		QualifiedName name = parse_id_expression_name();
		Scope* target = name.qualifier != NULL
			? name.qualifier : nearest_namespace_scope(class_scope);
		vector<Binding*> found = lookup_qualified_set(target,
		                                              name.name,
		                                              pa11::LOOKUP_TYPE);
		TypePtr friend_type;
		if (!found.empty() &&
		    found[0]->type.get() != NULL &&
		    pa11::strip_cv(found[0]->type)->kind == pa11::TypeKind::Record)
			friend_type = found[0]->type;
		else
			friend_type = add_record(target,
			                         name.name,
			                         class_tag(key),
			                         false,
			                         NULL);
		add_friend_class(class_scope, friend_type);
		expect(OP_SEMICOLON);
		return true;
	}

	DeclSpecs specs = parse_decl_specifier_seq(false);
	specs.friend_decl = true;
	TypePtr base = type_from_decl_specs(specs);
	Declarator declarator = parse_declarator(false);
	TypePtr type = apply_declarator(declarator, base);
	if (type->kind != pa11::TypeKind::Function)
		throw runtime_error("unsupported friend declaration");
	const QualifiedName& qname = declarator_name(declarator);
	Scope* target = qname.qualifier != NULL
		? qname.qualifier : nearest_namespace_scope(class_scope);
	Binding* function =
		add_function_binding(target, qname.name, type, !qname.qualified);
	function->language_linkage = current_language_linkage();
	const Suffix* suffix = declarator_function_suffix(declarator);
	function->unwind_no = suffix != NULL && suffix->noexcept_decl;
	function->ref_qualifier = suffix != NULL ? suffix->ref_qualifier : 0;
	if (pa11::strip_cv(type->base)->kind == pa11::TypeKind::Record &&
	    pa11::strip_cv(type->base)->scope != NULL)
		ensure_default_destructor(type->base);
	for (size_t i = 0; i < type->parameters.size(); ++i)
	{
		TypePtr param = pa11::strip_cv(type->parameters[i]);
		if (param->kind == pa11::TypeKind::Record && param->scope != NULL)
			ensure_default_destructor(type->parameters[i]);
	}
	if (suffix != NULL)
	{
		vector<Expr> defaults;
		vector<string> names;
		for (size_t i = 0; i < suffix->parameters.size(); ++i)
		{
			defaults.push_back(suffix->parameters[i].default_value);
			names.push_back(suffix->parameters[i].name);
		}
		default_arguments_[function] = defaults;
		function_parameter_names_[function] = names;
	}
	add_friend_function(class_scope, function);

	if (at(OP_LBRACE))
	{
		function->is_inline_definition = true;
		Node node;
		Node fn("function-definition " + qualified_decl_name(function) + " " +
		        pa11::describe_type(type));
		fn.binding = function;
		fn.type = type;
		add_child(node, fn);
		parse_function_body(function, declarator, node);
		if (!node.children.empty())
			extra_lowir_nodes_.push_back(node.children.back());
		return true;
	}
	expect(OP_SEMICOLON);
	return true;
}


void Parser::validate_record_copy_initialization(TypePtr type, const Expr& init)
{
	TypePtr record = pa11::strip_cv(type);
	pa11::layout_record_type(record);
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
		bool aggregate_candidate =
			!record_has_aggregate_blocking_constructor(record);
		if (aggregate_candidate)
		{
			if (record_has_nonpublic_field(record))
				throw runtime_error("non-public member disqualifies aggregate");
			for (size_t i = 0; i < record->fields.size(); ++i)
				if (default_member_initializers_.find(record->fields[i]) !=
				    default_member_initializers_.end())
					throw runtime_error(
						"default member initializer disqualifies aggregate");
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

Binding* Parser::find_overridden_virtual(TypePtr record, Binding* function) const
{
	TypePtr bare = pa11::strip_cv(record);
	TypePtr base = bare->base.get() != NULL ? pa11::strip_cv(bare->base) : TypePtr();
	for (TypePtr cur = base;
	     cur.get() != NULL && cur->kind == pa11::TypeKind::Record;
	     cur = cur->base.get() != NULL ? pa11::strip_cv(cur->base) : TypePtr())
	{
		for (size_t i = 0; i < cur->virtual_entries.size(); ++i)
		{
			Binding* candidate = cur->virtual_entries[i].function;
			if (candidate != NULL &&
			    !cur->virtual_entries[i].deleting_entry &&
			    virtual_signature_matches(candidate, function))
				return candidate;
		}
	}
	return NULL;
}

void Parser::complete_class_virtuals(TypePtr type)
{
	TypePtr bare = pa11::strip_cv(type);
	if (bare->kind != pa11::TypeKind::Record || bare->scope == NULL)
		return;
	TypePtr direct_base =
		bare->base.get() != NULL ? pa11::strip_cv(bare->base) : TypePtr();
	if (inherits_virtual_destructor(bare) && !has_declared_destructor(bare))
		ensure_default_destructor(bare);
	bare->virtual_entries.clear();
	if (direct_base.get() != NULL &&
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
			bare->is_polymorphic = true;
			continue;
		}
		if (member->is_override_specified)
			throw runtime_error("override requires virtual base member");
		if (!member->is_virtual)
			continue;
		member->virtual_slot_index =
			static_cast<int>(bare->virtual_entries.size());
		member->virtual_slot_width = is_destructor_binding(member) ? 2 : 1;
		bare->virtual_entries.push_back(pa11::VirtualTableEntry(member, false));
		if (is_destructor_binding(member))
			bare->virtual_entries.push_back(pa11::VirtualTableEntry(member, true));
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
                                         Node& out)
{
	const Suffix* suffix = declarator_function_suffix(declarator);
	int ref_qualifier = suffix != NULL ? suffix->ref_qualifier : 0;
	bool is_static_member = target->kind == ScopeKind::Class && specs.static_decl;
	Binding* function = NULL;
	map<string, vector<Binding*> >::iterator found = target->members.find(name);
	if (found != target->members.end())
	{
		for (size_t i = 0; i < found->second.size(); ++i)
		{
			Binding* candidate = found->second[i];
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
		function = add_value(target, BindingKind::Function, name, type);
	function->language_linkage = current_language_linkage();
	function->is_static_member = is_static_member;
	function->is_inline_definition =
		function->is_inline_definition ||
		(function_definition && current_scope()->kind == ScopeKind::Class);
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
	if (suffix != NULL)
	{
		vector<Expr> defaults;
		vector<string> names;
		if (nonstatic_member_function)
		{
			defaults.push_back(Expr());
			names.push_back("this");
		}
		for (size_t i = 0; i < suffix->parameters.size(); ++i)
		{
			defaults.push_back(suffix->parameters[i].default_value);
			names.push_back(suffix->parameters[i].name);
		}
		default_arguments_[function] = defaults;
		function_parameter_names_[function] = names;
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

void Parser::apply_braced_variable_initializer(Scope* target,
                                               Binding* variable,
                                               TypePtr type,
                                               const Expr& init,
                                               Node& var)
{
	Node list = init.node;
	if (pa11::strip_cv(type)->kind == pa11::TypeKind::Record)
	{
		vector<Expr> args;
		for (size_t i = 0; i < init.node.children.size(); ++i)
		{
			Expr arg;
			arg.valid = true;
			arg.node = init.node.children[i];
			arg.type = arg.node.type;
			arg.category = arg.node.category;
			arg.binding = arg.node.binding;
			args.push_back(arg);
		}
		try
		{
			Expr constructed =
				make_constructor_init_expr(type, args, init.copy_initialization);
			list = constructed.node;
		}
		catch (const runtime_error& err)
		{
			if (string(err.what()) != "no matching constructor")
				throw;
		}
	}
	ensure_aggregate_constructors_for_init(type, list);
	list.line += " lvalue " + pa11::describe_type(type);
	list.type = type;
	if (target->kind == ScopeKind::Class && !variable->is_static_member)
		default_member_initializers_[variable] = list;
	add_child(var, list);
}

void Parser::apply_record_variable_initializer(Scope* target,
                                               Binding* variable,
                                               TypePtr type,
                                               const Expr& init,
                                               Node& var)
{
	Expr constructed;
	TypePtr src_record = pa11::strip_cv(expression_object_type(init.type));
	TypePtr dst_record = pa11::strip_cv(type);
	if (src_record->kind == pa11::TypeKind::Record &&
	    pa11::same_type(src_record, dst_record) &&
	    init.category == ValueCategory::PRValue)
	{
		constructed = init;
		if (target->kind == ScopeKind::Class && !variable->is_static_member)
			default_member_initializers_[variable] = constructed.node;
		add_child(var, constructed.node);
		return;
	}
	try
	{
		vector<Expr> args;
		args.push_back(init);
		constructed = make_constructor_init_expr(type, args, init.copy_initialization);
	}
	catch (const runtime_error& err)
	{
		if (string(err.what()) != "no matching constructor")
			throw;
		if (src_record->kind != pa11::TypeKind::Record ||
		    !pa11::same_type(src_record, dst_record))
			throw;
		bool declared_copy_or_move = false;
		bool trivial_defaulted_match = false;
		if (dst_record->scope != NULL)
		{
			map<string, vector<Binding*> >::const_iterator found =
				dst_record->scope->members.find(dst_record->scope->name);
			if (found != dst_record->scope->members.end())
				for (size_t i = 0; i < found->second.size(); ++i)
				{
					Binding* ctor = found->second[i];
					if (ctor->kind == BindingKind::Function &&
					    ctor->type->kind == pa11::TypeKind::Function &&
					    ctor->type->parameters.size() == 2 &&
					    pa11::is_reference_type(ctor->type->parameters[1]) &&
					    pa11::same_type(
						    pa11::strip_cv(ctor->type->parameters[1]->base),
						    dst_record))
					{
						TypePtr param = ctor->type->parameters[1];
						if (ctor->is_defaulted &&
						    !ctor->is_inline_definition &&
						    ((init.category == ValueCategory::XValue &&
						      param->kind == pa11::TypeKind::RValueReference) ||
						     (init.category != ValueCategory::XValue &&
						      param->kind == pa11::TypeKind::LValueReference)))
							trivial_defaulted_match = true;
						else
							declared_copy_or_move = true;
					}
				}
		}
		if (declared_copy_or_move && !trivial_defaulted_match)
			throw;
		constructed = init;
	}
	if (target->kind == ScopeKind::Class && !variable->is_static_member)
		default_member_initializers_[variable] = constructed.node;
	add_child(var, constructed.node);
}

void Parser::apply_scalar_variable_initializer(const DeclSpecs& specs,
                                               Scope* target,
                                               Binding* variable,
                                               TypePtr type,
                                               const Expr& init,
                                               Node& var)
{
	Conversion conv = convert_to(init, type);
	if (!conv.viable)
		throw runtime_error("invalid initializer conversion");
	if (target->kind == ScopeKind::Class && !variable->is_static_member)
		default_member_initializers_[variable] = conv.expr.node;
	add_child(var, conv.expr.node);
	if ((specs.constexpr_decl || pa11::type_has_const(type)) &&
	    conv.expr.has_constant_value)
	{
		variable->has_constant = true;
		variable->constant_value = conv.expr.constant_value;
	}
}

void Parser::apply_variable_initializer(const DeclSpecs& specs,
                                        Scope* target,
                                        Binding* variable,
                                        TypePtr type,
                                        const Expr* init,
                                        Node& var)
{
	if (init != NULL &&
	    init->copy_initialization &&
	    pa11::strip_cv(type)->kind == pa11::TypeKind::Record)
		validate_record_copy_initialization(type, *init);
	if (init != NULL)
	{
		if (init->braced_init_list)
		{
			apply_braced_variable_initializer(target, variable, type, *init, var);
			return;
		}
		if (pa11::strip_cv(type)->kind == pa11::TypeKind::Record)
		{
			apply_record_variable_initializer(target, variable, type, *init, var);
			return;
		}
		apply_scalar_variable_initializer(specs, target, variable, type, *init, var);
	}
	else if (pa11::strip_cv(type)->kind == pa11::TypeKind::Record &&
	         ensure_default_constructor(type) != NULL)
	{
		add_child(var, default_constructor_action(variable));
	}
}

Binding* Parser::declare_one(const DeclSpecs& specs,
                             TypePtr base,
                             const Declarator& declarator,
                             const Expr* init,
                             bool function_definition,
                             Node& out)
{
	const QualifiedName& qname = declarator_name(declarator);
	Scope* target = qname.qualifier != NULL ? qname.qualifier : current_scope();
	TypePtr type = apply_declarator(declarator, base);
	if (specs.typedef_decl)
	{
		Binding* alias = add_alias(target, qname.name, type);
		add_child(out, Node("type-alias " + qname.name + " " +
		                    pa11::describe_type(alias->type)));
		return alias;
	}

	if (specs.constexpr_decl && !pa11::is_reference_type(type))
		type = pa11::make_cv(type, pa11::CV_CONST);
	if (init != NULL &&
	    init->braced_init_list &&
	    type->kind == pa11::TypeKind::Array &&
	    type->unknown_bound)
		type = pa11::make_array(type->base, false, init->node.children.size());
	bool nonstatic_member_function =
		target->kind == ScopeKind::Class &&
		type->kind == pa11::TypeKind::Function &&
		!specs.static_decl;
	if (nonstatic_member_function)
		type = make_member_function_type(target, type);
	if (type->kind == pa11::TypeKind::Function || function_definition)
	{
		return declare_function_entity(specs,
		                               target,
		                               qname.name,
		                               type,
		                               declarator,
		                               function_definition,
		                               nonstatic_member_function,
		                               out);
	}

	Binding* variable = NULL;
	if ((target->kind == ScopeKind::Namespace ||
	     target->kind == ScopeKind::Class) &&
	    (qname.qualifier != NULL || target->kind == ScopeKind::Namespace))
	{
		Binding* existing =
			pa11::find_owned_binding(target, qname.name, BindingKind::Variable);
		if (existing != NULL && pa11::same_type(existing->type, type))
			variable = existing;
	}
	if (variable == NULL)
		variable = add_value(target, BindingKind::Variable, qname.name, type);
	variable->language_linkage = current_language_linkage();
	variable->is_static_member =
		variable->is_static_member ||
		(target->kind == ScopeKind::Class &&
		 (specs.static_decl || qname.qualifier != NULL));
	variable->is_thread_local =
		variable->is_thread_local || specs.thread_local_decl;
	variable->is_mutable_member =
		target->kind == ScopeKind::Class && specs.mutable_decl;
	variable->is_private =
		target->kind == ScopeKind::Class &&
		!class_private_access_.empty() &&
		class_private_access_.back();
	variable->is_protected_member =
		target->kind == ScopeKind::Class &&
		!class_protected_access_.empty() &&
		class_protected_access_.back();
	if (target->kind == ScopeKind::Class)
	{
		TypePtr record = pa11::record_type_for_scope(target);
		if (record.get() != NULL)
			record->layout_valid = false;
	}
	ensure_default_destructor(type);
	Node var("variable " + qname.name + " " + pa11::describe_type(type));
	var.binding = variable;
	var.type = type;
	if (specs.extern_decl && target->kind == ScopeKind::Namespace && init == NULL)
		return variable;
	apply_variable_initializer(specs, target, variable, type, init, var);
	add_child(out, var);
	return variable;
}

}  // namespace internal
}  // namespace pa12
