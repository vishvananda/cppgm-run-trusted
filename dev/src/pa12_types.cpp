#include "pa12_internal.h"

#include <algorithm>
#include <stdexcept>

using namespace std;

namespace pa12 {
namespace internal {
namespace {

TypePtr adjust_parameter_type(TypePtr type)
{
	if (type->kind == pa11::TypeKind::Array)
		return pa11::make_pointer(type->base);
	if (type->kind == pa11::TypeKind::Function)
		return pa11::make_pointer(type);
	return type;
}

bool type_contains_template_parameter_name(TypePtr type, string& name)
{
	if (type.get() == NULL)
		return false;
	type = pa11::strip_cv(type);
	if (type->kind == pa11::TypeKind::TemplateParameter)
	{
		name = type->name;
		return true;
	}
	if (type->kind == pa11::TypeKind::Pointer ||
	    type->kind == pa11::TypeKind::LValueReference ||
	    type->kind == pa11::TypeKind::RValueReference ||
	    type->kind == pa11::TypeKind::Array)
		return type_contains_template_parameter_name(type->base, name);
	if (type->kind == pa11::TypeKind::Function)
	{
		if (type_contains_template_parameter_name(type->base, name))
			return true;
		for (size_t i = 0; i < type->parameters.size(); ++i)
			if (type_contains_template_parameter_name(type->parameters[i],
			                                          name))
				return true;
	}
	if (type->kind == pa11::TypeKind::MemberPointer)
		return type_contains_template_parameter_name(type->member_class,
		                                             name) ||
		       type_contains_template_parameter_name(type->base, name);
	return false;
}

void skip_angle_tokens(const vector<Token>& tokens, size_t& pos)
{
	if (pos >= tokens.size() ||
	    tokens[pos].kind != posttoken::TokenKind::Simple ||
	    tokens[pos].type != OP_LT)
		return;
	int depth = 0;
	while (pos < tokens.size())
	{
		const Token& tok = tokens[pos];
		if (tok.kind == posttoken::TokenKind::Simple &&
		    tok.type == OP_LT)
			++depth;
		else if (tok.kind == posttoken::TokenKind::Simple &&
		         tok.type == OP_GT)
		{
			--depth;
			++pos;
			if (depth == 0)
				return;
			continue;
		}
		++pos;
	}
}

}  // namespace

DeclSpecs Parser::parse_decl_specifier_seq(bool type_id_context)
{
	DeclSpecs specs;
	bool saw_any = false;
	bool saw_non_cv_type = false;
	for (;;)
	{
		if (!type_id_context && consume(KW_TYPEDEF))
		{
			specs.typedef_decl = true;
			saw_any = true;
		}
		else if (!type_id_context && consume(KW_CONSTEXPR))
		{
			specs.constexpr_decl = true;
			saw_any = true;
		}
		else if (!type_id_context && consume(KW_MUTABLE))
		{
			specs.mutable_decl = true;
			saw_any = true;
		}
		else if (!type_id_context && consume(KW_FRIEND))
		{
			specs.friend_decl = true;
			saw_any = true;
		}
		else if (!type_id_context && at_simple_ignored_specifier())
		{
			if (at(KW_STATIC))
				specs.static_decl = true;
			if (at(KW_EXTERN))
				specs.extern_decl = true;
			if (at(KW_THREAD_LOCAL))
				specs.thread_local_decl = true;
			if (at(KW_VIRTUAL))
				specs.virtual_decl = true;
			if (at(KW_INLINE))
				specs.inline_decl = true;
			++pos_;
			saw_any = true;
		}
		else if (at_simple_cv())
		{
			specs.cv |= consume_cv_flag();
			saw_any = true;
		}
		else if (at_simple_builtin())
		{
			if (at(KW_AUTO))
				specs.auto_decl = true;
			else
				specs.builtin.push_back(tokens_[pos_].type);
			++pos_;
			saw_any = true;
			saw_non_cv_type = true;
		}
		else if (!saw_non_cv_type && at(KW_DECLTYPE))
		{
			specs.named_type = parse_decltype_specifier();
			saw_any = true;
			saw_non_cv_type = true;
		}
		else if (!saw_non_cv_type && starts_class_key())
		{
			specs.named_type = parse_class_specifier();
			saw_any = true;
			saw_non_cv_type = true;
		}
		else if (!saw_non_cv_type && at(KW_ENUM))
		{
			specs.named_type = parse_enum_specifier();
			saw_any = true;
			saw_non_cv_type = true;
		}
		else if (!saw_non_cv_type && try_parse_type_name(specs.named_type))
		{
			saw_any = true;
			saw_non_cv_type = true;
		}
		else
			break;
	}
	if (!saw_any || !saw_non_cv_type)
		throw runtime_error("expected declaration specifiers");
	return specs;
}

TypePtr Parser::type_from_decl_specs(const DeclSpecs& specs)
{
	TypePtr type = specs.named_type.get() != NULL ? specs.named_type :
		specs.auto_decl ? pa11::make_fundamental(FT_VOID) :
		pa11::make_fundamental(pa11::fundamental_from_specs(specs.builtin));
	return pa11::make_cv(type, specs.cv);
}

TypePtr Parser::parse_type_id()
{
	DeclSpecs specs = parse_decl_specifier_seq(true);
	TypePtr base = type_from_decl_specs(specs);
	if (!starts_abstract_declarator())
		return base;
	size_t save = pos_;
	try
	{
		return apply_declarator(parse_abstract_declarator(), base);
	}
	catch (const exception&)
	{
		pos_ = save;
		return base;
	}
}

TypePtr Parser::parse_decltype_specifier()
{
	expect(KW_DECLTYPE);
	expect(OP_LPAREN);
	if (at(KW_SIZEOF))
	{
		Expr expr = parse_type_trait_expression(KW_SIZEOF);
		expect(OP_RPAREN);
		return expr.type;
	}
	size_t save = pos_;
	try
	{
		if (!at(OP_LPAREN))
		{
			QualifiedName name = parse_id_expression_name();
			if (at(OP_RPAREN))
			{
				Binding* binding = resolve_single_name(name, pa11::LOOKUP_VALUE);
				if (binding == NULL)
					throw runtime_error("decltype target not found");
				expect(OP_RPAREN);
				return binding->type;
			}
		}
	}
	catch (const exception&)
	{
	}
	pos_ = save;
	Expr expr = parse_expression();
	expect(OP_RPAREN);
	TypePtr object = expression_object_type(expr.type);
	if (expr.category == ValueCategory::LValue)
		return pa11::make_lvalue_reference(object);
	if (expr.category == ValueCategory::XValue)
		return pa11::make_rvalue_reference(object);
	return expr.type;
}

TypePtr Parser::parse_class_specifier()
{
	const size_t start_index = pos_;
	ETokenType key = current().type;
	++pos_;
	uint64_t forced_align = 0;
	while (consume(KW_ALIGNAS))
	{
		expect(OP_LPAREN);
		uint64_t align_value = 0;
		if (at_identifier() && current().source == "__alignof")
		{
			++pos_;
			expect(OP_LPAREN);
			TypePtr align_type = parse_type_id();
			expect(OP_RPAREN);
			align_value = pa11::type_align(align_type);
		}
		else
		{
			size_t align_save = pos_;
			try
			{
				TypePtr align_type = parse_type_id();
				if (!at(OP_RPAREN))
					throw runtime_error("alignas type parse left tokens");
				align_value = pa11::type_align(align_type);
			}
			catch (const exception&)
			{
				pos_ = align_save;
				Expr align_expr = parse_expression();
				if (!align_expr.has_constant_value)
					throw runtime_error("invalid alignas");
				align_value = align_expr.constant_value;
			}
		}
		expect(OP_RPAREN);
		forced_align = max<uint64_t>(forced_align, align_value);
	}
	string name;
	Scope* qualified_owner = NULL;
	bool template_id_qualifier = false;
	if (at_identifier() && lookahead(OP_LT, 1))
	{
		size_t p = pos_ + 1;
		int depth = 0;
		while (p < tokens_.size())
		{
			if (tokens_[p].kind == posttoken::TokenKind::Simple &&
			    tokens_[p].type == OP_LT)
				++depth;
			else if (tokens_[p].kind == posttoken::TokenKind::Simple &&
			         tokens_[p].type == OP_GT)
			{
				--depth;
				if (depth == 0)
				{
					template_id_qualifier =
						p + 1 < tokens_.size() &&
						tokens_[p + 1].kind == posttoken::TokenKind::Simple &&
						tokens_[p + 1].type == OP_COLON2;
					break;
				}
			}
			++p;
		}
	}
	if (at(OP_COLON2) ||
	    (at_identifier() &&
	     (lookahead(OP_COLON2, 1) || template_id_qualifier)))
		qualified_owner = parse_nested_name_specifier(NULL);
	if (at_identifier())
		name = consume_identifier();
	if (at(OP_LT))
	{
		vector<TemplateArgument> ignored_template_id;
		parse_template_argument_list(ignored_template_id);
	}
	if (!at(OP_LBRACE) && !at(OP_COLON))
	{
		if (name.empty())
			throw runtime_error("anonymous class declaration is not a type");
		vector<Binding*> found =
			qualified_owner != NULL
			? lookup_qualified_set(qualified_owner, name, pa11::LOOKUP_TYPE)
			: lookup_unqualified_set(current_scope(), name, pa11::LOOKUP_TYPE);
		if (!found.empty() &&
		    found[0]->type->kind == pa11::TypeKind::Record)
			return found[0]->type;
		return add_record(qualified_owner != NULL ? qualified_owner :
		                  current_scope(),
		                  name,
		                  class_tag(key),
		                  false,
		                  NULL);
	}

	bool anonymous = name.empty();
	if (anonymous)
	{
		size_t p = pos_;
		int depth = 0;
		do
		{
			if (tokens_[p].kind == posttoken::TokenKind::Simple &&
			    tokens_[p].type == OP_LBRACE)
				++depth;
			else if (tokens_[p].kind == posttoken::TokenKind::Simple &&
			         tokens_[p].type == OP_RBRACE)
				--depth;
			++p;
		}
		while (p < tokens_.size() && depth > 0);
		const bool injected_union =
			key == KW_UNION && p < tokens_.size() &&
			tokens_[p].kind == posttoken::TokenKind::Simple &&
			tokens_[p].type == OP_SEMICOLON;
		name = injected_union
			? "__anonymous_union_type__" + to_string(start_index) +
			  "_" + to_string(p + 1)
			: make_local_type_name("__local_type");
	}
	TypePtr direct_base;
	if (consume(OP_COLON))
	{
		if (at(KW_PUBLIC) || at(KW_PRIVATE) || at(KW_PROTECTED))
			++pos_;
		if (!try_parse_type_name(direct_base))
			throw runtime_error("invalid base class");
		if (consume(OP_DOTS))
			direct_base.reset();
		TypePtr base_bare = direct_base.get() != NULL
			? pa11::strip_cv(direct_base) : TypePtr();
		if (base_bare.get() != NULL &&
		    base_bare->kind != pa11::TypeKind::Record &&
		    base_bare->kind != pa11::TypeKind::TemplateParameter)
			throw runtime_error("invalid base class");
	}
	bool active_template_class =
		!active_class_instantiations_.empty() &&
		active_class_instantiations_.back().declaration != NULL &&
		active_class_instantiations_.back().declaration->name == name;
	Scope* class_scope = NULL;
	TypePtr type;
	if (active_template_class)
	{
		type = active_class_instantiations_.back().type;
		class_scope = type->scope;
		type->complete = true;
		type->tag = class_tag(key);
	}
	else
	{
		Scope* owner = qualified_owner != NULL ? qualified_owner : current_scope();
		bool named_local_record =
			!anonymous &&
			qualified_owner == NULL &&
			owner->kind != ScopeKind::Namespace &&
			owner->kind != ScopeKind::Class;
		Binding* existing = qualified_owner != NULL
			? pa11::lookup_qualified(qualified_owner,
			                         name,
			                         pa11::LOOKUP_TYPE)
			: NULL;
		TypePtr existing_record = existing != NULL
			? pa11::strip_cv(existing->type) : TypePtr();
		if (existing_record.get() != NULL &&
		    existing_record->kind == pa11::TypeKind::Record &&
		    !existing_record->complete)
		{
			type = existing_record;
			class_scope = type->scope != NULL
				? type->scope
				: pa11::create_child_scope(owner, ScopeKind::Class, name);
			type->scope = class_scope;
			type->complete = true;
			type->tag = class_tag(key);
			existing->target_scope = class_scope;
		}
		else
		{
			class_scope =
				pa11::create_child_scope(owner, ScopeKind::Class, name);
			type = add_record(owner,
			                  name,
			                  class_tag(key),
			                  true,
			                  class_scope);
			if (named_local_record)
				type->name = make_local_type_name(name + "__local_type");
			type->scope = class_scope;
		}
	}
	type->base = direct_base;
	if (active_template_class && direct_base.get() != NULL)
	{
		TemplateDeclaration* declaration =
			active_class_instantiations_.back().declaration;
		if (type_is_template_dependent(direct_base))
			class_templates_with_dependent_base_.insert(declaration);
		if (class_templates_with_dependent_base_.count(declaration) != 0)
			record_dependent_base_lookup_skips_.insert(type.get());
	}
	if (forced_align > type->record_forced_align)
	{
		type->record_forced_align = forced_align;
		type->layout_valid = false;
	}
	expect(OP_LBRACE);
	scopes_.push_back(class_scope);
	parse_class_body(class_scope, key == KW_CLASS);
	scopes_.pop_back();
	expect(OP_RBRACE);
	for (size_t i = 0; i < extra_lowir_nodes_.size(); ++i)
		if (extra_lowir_nodes_[i].binding != NULL &&
		    extra_lowir_nodes_[i].binding->owner == class_scope)
			resolve_pending_member_initializers(class_scope,
			                                    extra_lowir_nodes_[i]);
	pa11::layout_record_type(type);
	return type;
}

void Parser::parse_class_body(Scope* class_scope, bool default_private)
{
	Scope* open_parent_class = NULL;
	for (size_t i = 0; i + 1 < scopes_.size(); ++i)
		if (scopes_[i] == class_scope->parent &&
		    scopes_[i]->kind == ScopeKind::Class)
			open_parent_class = scopes_[i];
	class_private_access_.push_back(default_private);
	class_protected_access_.push_back(false);
	while (!at(OP_RBRACE))
	{
		if (consume(OP_SEMICOLON))
			continue;
		if (consume(KW_PUBLIC))
		{
			class_private_access_.back() = false;
			class_protected_access_.back() = false;
			expect(OP_COLON);
			continue;
		}
		if (consume(KW_PRIVATE))
		{
			class_private_access_.back() = true;
			class_protected_access_.back() = false;
			expect(OP_COLON);
			continue;
		}
		if (consume(KW_PROTECTED))
		{
			class_private_access_.back() = false;
			class_protected_access_.back() = true;
			expect(OP_COLON);
			continue;
		}
		if (at(KW_USING))
		{
			Node ignored;
			parse_using_family(ignored);
			continue;
		}
		if (at(KW_STATIC_ASSERT))
		{
			parse_static_assert_declaration();
			continue;
		}
		if (parse_friend_declaration())
			continue;
		Node ignored;
		size_t save = pos_;
		try
		{
			parse_simple_or_function_declaration(ignored, false);
		}
		catch (const exception&)
		{
			pos_ = save;
			if (!parse_constructor_like_member() &&
			    !parse_destructor_like_member())
				throw;
		}
		(void)class_scope;
	}
	TypePtr class_type = pa11::record_type_for_scope(class_scope);
	if (class_type.get() != NULL)
	{
		complete_class_virtuals(class_type);
		pa11::layout_record_type(class_type);
		for (size_t i = 0; i < defaulted_move_assignments_.size(); ++i)
		{
			Binding* function = defaulted_move_assignments_[i];
			if (function->owner != class_scope)
				continue;
			for (size_t j = 0; j < class_type->fields.size(); ++j)
				if (pa11::type_has_const(class_type->fields[j]->type) ||
				    pa11::is_reference_type(class_type->fields[j]->type))
					deleted_functions_.insert(function);
		}
		vector<Binding*> members = class_scope->binding_order;
		for (size_t i = 0; i < members.size(); ++i)
		{
			Binding* function = members[i];
			if (function->kind != BindingKind::Function ||
			    !function->is_defaulted ||
			    function->name != class_scope->name ||
			    function->type->kind != pa11::TypeKind::Function ||
			    function->type->parameters.size() != 2 ||
			    !pa11::is_reference_type(function->type->parameters[1]))
				continue;
			ensure_copy_move_constructor(
				class_type,
				function->type->parameters[1]->kind ==
					pa11::TypeKind::RValueReference);
		}
	}
	if (open_parent_class != NULL)
		deferred_nested_member_body_scopes_[open_parent_class].push_back(
			class_scope);
	else
	{
		parse_pending_member_bodies(class_scope);
		parse_deferred_nested_member_bodies(class_scope);
	}
	class_protected_access_.pop_back();
	class_private_access_.pop_back();
}

TypePtr Parser::parse_enum_specifier()
{
	expect(KW_ENUM);
	bool scoped = consume(KW_CLASS) || consume(KW_STRUCT);
	string name;
	if (at_identifier())
		name = consume_identifier();
	EFundamentalType underlying = FT_INT;
	if (consume(OP_COLON))
		underlying = parse_enum_underlying_type();
	if (!at(OP_LBRACE))
	{
		if (name.empty())
			throw runtime_error("opaque enum requires name");
		return add_enum(current_scope(), name, scoped, underlying, true, scoped);
	}

	if (name.empty())
		name = make_local_type_name("__anonymous_enum");
	TypePtr type = add_enum(current_scope(), name, scoped, underlying, true, scoped);
	Scope* enum_scope = scoped && type->scope != NULL ? type->scope : current_scope();
	expect(OP_LBRACE);
	if (scoped)
		scopes_.push_back(enum_scope);
	uint64_t next_value = 0;
	while (!at(OP_RBRACE))
	{
		string enumerator = consume_identifier();
		uint64_t value = next_value;
		if (consume(OP_ASS))
		{
			Expr explicit_value = parse_assignment_expression();
			if (!explicit_value.has_constant_value)
				throw runtime_error("invalid enumerator initializer");
			value = explicit_value.constant_value;
		}
		Binding* binding =
			pa11::add_binding(enum_scope, BindingKind::Enumerator, enumerator, type);
		binding->has_constant = true;
		binding->constant_value = value;
		next_value = value + 1;
		if (!consume(OP_COMMA))
			break;
	}
	if (scoped)
		scopes_.pop_back();
	expect(OP_RBRACE);
	return type;
}

EFundamentalType Parser::parse_enum_underlying_type()
{
	DeclSpecs specs = parse_decl_specifier_seq(true);
	if (specs.named_type.get() != NULL)
		return FT_INT;
	return pa11::fundamental_from_specs(specs.builtin);
}

bool Parser::try_parse_type_name(TypePtr& out)
{
	size_t save = pos_;
	string spelling;
	Scope* qualifier = NULL;
	bool typename_disambiguator = consume(KW_TYPENAME);
	bool template_id_qualifier = false;
	if (typename_disambiguator && at_identifier())
	{
		size_t dep_save = pos_;
		string dep_name = consume_identifier();
		bool dependent_root = false;
		TypePtr subst;
		if (find_template_type_substitution(dep_name, subst) &&
		    pa11::strip_cv(subst)->kind ==
		    pa11::TypeKind::TemplateParameter)
			dependent_root = true;
		if (at(OP_LT))
		{
			vector<TemplateArgument> root_arguments;
			try
			{
				parse_template_argument_list(root_arguments);
			}
			catch (const exception&)
			{
				pos_ = dep_save;
				root_arguments.clear();
			}
			if (pos_ != dep_save)
			{
				dep_name += "<>";
				for (size_t i = 0; i < root_arguments.size(); ++i)
				{
					vector<TemplateArgument> pending;
					pending.push_back(root_arguments[i]);
					while (!pending.empty())
					{
						TemplateArgument arg = pending.back();
						pending.pop_back();
						if (arg.kind == TemplateArgumentKind::Type)
						{
							if (type_is_template_dependent(arg.type))
								dependent_root = true;
						}
						else if (arg.kind == TemplateArgumentKind::Value)
						{
							if (arg.dependent ||
							    type_is_template_dependent(arg.type))
								dependent_root = true;
						}
						else
						{
							for (size_t p = 0; p < arg.pack.size(); ++p)
								pending.push_back(arg.pack[p]);
						}
					}
				}
			}
		}
		if (dependent_root && at(OP_COLON2))
		{
			while (consume(OP_COLON2))
			{
				dep_name += "::";
				consume(KW_TEMPLATE);
				if (!at_identifier())
				{
					pos_ = dep_save;
					break;
				}
				dep_name += consume_identifier();
				if (at(OP_LT))
				{
					dep_name += "<>";
					skip_angle_tokens(tokens_, pos_);
				}
			}
			if (pos_ != dep_save)
			{
			out = pa11::make_template_parameter_type(dep_name);
			return true;
			}
		}
		pos_ = dep_save;
	}
	if (at_identifier() && lookahead(OP_LT, 1))
	{
		size_t p = pos_ + 1;
		int depth = 0;
		while (p < tokens_.size())
		{
			if (tokens_[p].kind == posttoken::TokenKind::Simple &&
			    tokens_[p].type == OP_LT)
				++depth;
			else if (tokens_[p].kind == posttoken::TokenKind::Simple &&
			         tokens_[p].type == OP_GT)
			{
				--depth;
				if (depth == 0)
				{
					template_id_qualifier =
						p + 1 < tokens_.size() &&
						tokens_[p + 1].kind == posttoken::TokenKind::Simple &&
						tokens_[p + 1].type == OP_COLON2;
					break;
				}
			}
			++p;
		}
	}
	if (at(KW_DECLTYPE) ||
	    at(OP_COLON2) ||
	    (at_identifier() &&
	     (lookahead(OP_COLON2, 1) || template_id_qualifier)))
		qualifier = parse_nested_name_specifier(&spelling);
	if (!at_identifier())
	{
		pos_ = save;
		return false;
	}
	string name = consume_identifier();
	if (qualifier == NULL)
	{
		TypePtr subst;
		if (find_template_type_substitution(name, subst))
		{
			out = subst;
			return true;
		}
	}
	if (at(OP_LT))
	{
		TemplateDeclaration* templ = find_class_template(qualifier, name);
		if (templ != NULL)
		{
			vector<TemplateArgument> arguments;
			parse_template_argument_list(arguments);
			out = instantiate_class_template(templ, arguments);
			return true;
		}
	}
	vector<Binding*> found = qualifier != NULL
		? lookup_qualified_set(qualifier, name, pa11::LOOKUP_TYPE)
		: lookup_unqualified_set(current_scope(), name, pa11::LOOKUP_TYPE);
	if (found.empty())
	{
		pos_ = save;
		return false;
	}
	Binding* binding = found[0];
	if (binding->is_private || binding->is_protected_member)
	{
		if (binding->is_private &&
		    !active_context_has_class_access(binding->owner))
			throw runtime_error("private type access");
		if (binding->is_protected_member &&
		    !active_context_has_class_access(binding->owner))
			throw runtime_error("protected type access");
	}
	out = binding->type;
	complete_member_class_template_record(binding);
	if (!type_is_template_dependent(out))
		complete_template_record(out);
	(void)typename_disambiguator;
	return true;
}

Declarator Parser::parse_declarator(bool abstract_allowed)
{
	Declarator declarator;
	parse_ptr_prefix(declarator.prefix);
	parse_noptr_declarator_root(declarator, abstract_allowed);
	if (declarator.has_name &&
	    declarator.name.qualifier != NULL &&
	    declarator.name.qualifier->kind == ScopeKind::Class)
	{
		vector<Scope*> saved_scopes = scopes_;
		scopes_.push_back(declarator.name.qualifier);
		try
		{
			parse_suffixes(declarator.suffixes);
		}
		catch (...)
		{
			scopes_ = saved_scopes;
			throw;
		}
		scopes_ = saved_scopes;
	}
	else
		parse_suffixes(declarator.suffixes);
	return declarator;
}

Declarator Parser::parse_abstract_declarator()
{
	Declarator declarator;
	parse_ptr_prefix(declarator.prefix);
	if (starts_parenthesized_abstract_declarator())
	{
		expect(OP_LPAREN);
		declarator.inner.reset(new Declarator(parse_abstract_declarator()));
		expect(OP_RPAREN);
	}
	parse_suffixes(declarator.suffixes);
	if (declarator.prefix.empty() && declarator.suffixes.empty() &&
	    declarator.inner.get() == NULL)
		throw runtime_error("expected abstract declarator");
	return declarator;
}

void Parser::parse_noptr_declarator_root(Declarator& declarator,
                                         bool abstract_allowed)
{
	if (consume(OP_LPAREN))
	{
		declarator.inner.reset(new Declarator(parse_declarator(true)));
		expect(OP_RPAREN);
		return;
	}
	if (!abstract_allowed || at_identifier() || at(OP_COLON2))
	{
		declarator.name = parse_id_expression_name();
		declarator.has_name = true;
		return;
	}
}

void Parser::parse_ptr_prefix(vector<PtrOp>& ops)
{
	for (;;)
	{
		if (at_identifier() && lookahead(OP_COLON2, 1))
		{
			size_t save = pos_;
			string class_name = consume_identifier();
			expect(OP_COLON2);
			vector<Binding*> found =
				lookup_unqualified_set(current_scope(), class_name, pa11::LOOKUP_TYPE);
			if (found.empty() || !consume(OP_STAR))
			{
				pos_ = save;
				return;
			}
			TypePtr class_type = found[0]->type;
			unsigned cv = pa11::CV_NONE;
			while (at_simple_cv())
				cv |= consume_cv_flag();
			ops.push_back(PtrOp(class_type, cv));
		}
		else if (consume(OP_STAR))
		{
			unsigned cv = pa11::CV_NONE;
			while (at_simple_cv())
				cv |= consume_cv_flag();
			ops.push_back(PtrOp(PtrKind::Pointer, cv));
		}
		else if (consume(OP_AMP))
			ops.push_back(PtrOp(PtrKind::LValueReference, pa11::CV_NONE));
		else if (consume(OP_LAND))
			ops.push_back(PtrOp(PtrKind::RValueReference, pa11::CV_NONE));
		else
			return;
	}
}

void Parser::parse_suffixes(vector<Suffix>& suffixes)
{
	for (;;)
	{
		if (at(OP_LSQUARE))
			suffixes.push_back(parse_array_suffix());
		else if (at(OP_LPAREN))
		{
			if (pos_ + 1 < tokens_.size() &&
			    tokens_[pos_ + 1].kind == posttoken::TokenKind::Identifier &&
			    pa11::lookup_unqualified(current_scope(),
			                             tokens_[pos_ + 1].source,
			                             pa11::LOOKUP_VARIABLE |
			                             pa11::LOOKUP_PARAMETER) != NULL)
				return;
			size_t save = pos_;
			try
			{
				suffixes.push_back(parse_function_suffix());
			}
			catch (const exception&)
			{
				if (save + 1 < tokens_.size() &&
				    tokens_[save + 1].kind == posttoken::TokenKind::Simple &&
				    tokens_[save + 1].type == OP_RPAREN)
					throw;
				pos_ = save;
				return;
			}
		}
		else
			return;
	}
}

Suffix Parser::parse_array_suffix()
{
	Suffix suffix(SuffixKind::Array);
	expect(OP_LSQUARE);
	if (consume(OP_RSQUARE))
	{
		suffix.unknown_bound = true;
		return suffix;
	}
	Expr bound = parse_expression();
	ConstexprValue value;
	if (try_evaluate_constexpr_expr(bound.node, value) &&
	    value.valid &&
	    !value.is_float &&
	    !value.is_object &&
	    !value.is_pointer)
	{
		bound.has_constant_value = true;
		bound.constant_value = value.int_value;
	}
	bool dependent_validation =
		!active_class_instantiations_.empty() &&
		(active_class_instantiations_.back().specialization_name.find(
			 "dependent") != string::npos ||
		 active_class_instantiations_.back().specialization_name.find(
			 "typename ") != string::npos);
	if ((!bound.has_constant_value || bound.constant_value == 0) &&
	    dependent_validation)
	{
		suffix.unknown_bound = true;
		expect(OP_RSQUARE);
		return suffix;
	}
	if (!bound.has_constant_value || bound.constant_value == 0)
		throw runtime_error("invalid array bound");
	suffix.bound = bound.constant_value;
	expect(OP_RSQUARE);
	return suffix;
}

Suffix Parser::parse_function_suffix()
{
	Suffix suffix(SuffixKind::Function);
	expect(OP_LPAREN);
	vector<Scope*> saved_scopes = scopes_;
	Scope* parameter_scope =
		pa11::create_child_scope(current_scope(),
		                         ScopeKind::Function,
		                         "");
	scopes_.push_back(parameter_scope);
	try
	{
		parse_parameter_clause(suffix.parameters, suffix.variadic);
		expect(OP_RPAREN);
		parse_function_suffix_tail(suffix);
	}
	catch (const exception&)
	{
		scopes_ = saved_scopes;
		throw;
	}
	scopes_ = saved_scopes;
	return suffix;
}

void Parser::parse_function_suffix_tail(Suffix& suffix)
{
	for (;;)
	{
		if (at_simple_cv())
		{
			suffix.function_cv |= consume_cv_flag();
			continue;
		}
		if (consume(OP_AMP))
		{
			suffix.ref_qualifier = 1;
			continue;
		}
		if (consume(OP_LAND))
		{
			suffix.ref_qualifier = 2;
			continue;
		}
		if (consume(KW_NOEXCEPT))
		{
			suffix.noexcept_decl = true;
			if (at(OP_LPAREN))
				skip_balanced(OP_LPAREN, OP_RPAREN);
			continue;
		}
		if (consume(KW_THROW))
		{
			suffix.noexcept_decl = true;
			if (at(OP_LPAREN))
				skip_balanced(OP_LPAREN, OP_RPAREN);
			continue;
		}
		if (at_identifier() && current().source == "override")
		{
			++pos_;
			suffix.override_decl = true;
			continue;
		}
		if (at_identifier() && current().source == "final")
		{
			++pos_;
			suffix.final_decl = true;
			continue;
		}
		if (consume(OP_ARROW))
		{
			vector<Scope*> saved_scopes = scopes_;
			Scope* parameter_scope =
				pa11::create_child_scope(current_scope(),
				                         ScopeKind::Function,
				                         "");
			scopes_.push_back(parameter_scope);
			for (size_t i = 0; i < suffix.parameters.size(); ++i)
			{
				const ParameterInfo& parameter = suffix.parameters[i];
				if (parameter.name.empty())
					continue;
				pa11::add_binding(parameter_scope,
				                  BindingKind::Parameter,
				                  parameter.name,
				                  parameter.type);
			}
			try
			{
				suffix.trailing_return = parse_type_id();
			}
			catch (const exception&)
			{
				scopes_ = saved_scopes;
				throw;
			}
			scopes_ = saved_scopes;
			continue;
		}
		break;
	}
}

void Parser::parse_parameter_clause(vector<ParameterInfo>& parameters,
                                    bool& variadic)
{
	variadic = false;
	Scope* parameter_scope =
		pa11::create_child_scope(current_scope(), ScopeKind::Function, "");
	scopes_.push_back(parameter_scope);
	try
	{
		if (consume(OP_DOTS))
		{
			variadic = true;
		}
		else if (!at(OP_RPAREN))
		{
			for (;;)
			{
				ParameterInfo parsed = parse_parameter_declaration();
				vector<ParameterInfo> expanded =
					expand_parameter_pack(parsed);
				for (size_t i = 0; i < expanded.size(); ++i)
				{
					parameters.push_back(expanded[i]);
					ParameterInfo& parameter = parameters.back();
					if (!parameter.name.empty())
						pa11::add_binding(parameter_scope,
						                  BindingKind::Parameter,
						                  parameter.name,
						                  parameter.type);
				}
				if (!consume(OP_COMMA))
					break;
				if (consume(OP_DOTS))
				{
					variadic = true;
					break;
				}
			}
			if (!variadic && !parameters.empty() &&
			    !parameters.back().is_pack_expansion &&
			    consume(OP_DOTS))
				variadic = true;
		}
	}
	catch (...)
	{
		scopes_.pop_back();
		throw;
	}
	scopes_.pop_back();
}

vector<ParameterInfo> Parser::expand_parameter_pack(
	const ParameterInfo& parameter) const
{
	vector<ParameterInfo> out;
	if (!parameter.is_pack_expansion)
	{
		out.push_back(parameter);
		return out;
	}
	TemplateArgument subst;
	if (!find_template_value_substitution(parameter.pack_name, subst) ||
	    subst.kind != TemplateArgumentKind::Pack)
	{
		out.push_back(parameter);
		return out;
	}
	if (subst.pack.empty() && !parameter.pack_expression_name.empty())
	{
		ParameterInfo marker = parameter;
		marker.name.clear();
		marker.type.reset();
		marker.is_pack_expansion = false;
		out.push_back(marker);
		return out;
	}
	for (size_t i = 0; i < subst.pack.size(); ++i)
	{
		if (subst.pack[i].kind != TemplateArgumentKind::Type)
			throw runtime_error("type parameter pack required");
		ParameterInfo expanded = parameter;
		expanded.is_pack_expansion = false;
		expanded.type =
			substitute_template_type_parameter(parameter.type,
			                                   parameter.pack_name,
			                                   subst.pack[i].type);
		if (!parameter.name.empty() && i > 0)
			expanded.name = parameter.name + "__pack" + to_string(i + 1);
		out.push_back(expanded);
	}
	return out;
}

ParameterInfo Parser::parse_parameter_declaration()
{
	DeclSpecs specs = parse_decl_specifier_seq(false);
	TypePtr base = type_from_decl_specs(specs);
	ParameterInfo info;
	size_t save = pos_;
	if (starts_declarator())
	{
		try
		{
			Declarator declarator = parse_declarator(true);
			info.type = adjust_parameter_type(apply_declarator(declarator, base));
			if (declarator_has_name(declarator))
				info.name = declarator_name(declarator).name;
			string pack_name;
			if (at(OP_DOTS) &&
			    type_contains_template_parameter_name(info.type, pack_name))
			{
				expect(OP_DOTS);
				info.is_pack_expansion = true;
				info.pack_name = pack_name;
				if (info.name.empty() && at_identifier())
					info.name = consume_identifier();
				info.pack_expression_name = info.name;
			}
			if (consume(OP_ASS))
			{
				info.has_default = true;
				info.default_value = parse_assignment_expression();
			}
			return info;
		}
		catch (const exception&)
		{
			pos_ = save;
		}
	}
	if (starts_abstract_declarator())
		info.type = adjust_parameter_type(
			apply_declarator(parse_abstract_declarator(), base));
	else
		info.type = adjust_parameter_type(base);
	string pack_name;
	if (at(OP_DOTS) &&
	    type_contains_template_parameter_name(info.type, pack_name))
	{
		expect(OP_DOTS);
		info.is_pack_expansion = true;
		info.pack_name = pack_name;
		if (info.name.empty() && at_identifier())
			info.name = consume_identifier();
		info.pack_expression_name = info.name;
	}
	if (consume(OP_ASS))
	{
		info.has_default = true;
		info.default_value = parse_assignment_expression();
	}
	return info;
}

bool Parser::starts_declaration()
{
	if (at(KW_TYPEDEF) || at(KW_CONSTEXPR) || at(KW_EXTERN) ||
	    at(KW_STATIC) || at(KW_DECLTYPE) || at(KW_TYPENAME) ||
	    starts_class_key() || at(KW_ENUM) || at(KW_STATIC_ASSERT))
		return true;
	if (at_simple_cv() || at_simple_builtin())
		return true;
	if (at_identifier() &&
	    pos_ + 1 < tokens_.size() &&
	    tokens_[pos_ + 1].kind == posttoken::TokenKind::Identifier)
		return true;
	if (!at_identifier() && !at(OP_COLON2) && !at(KW_TYPENAME))
		return false;
	TypePtr type;
	size_t save = pos_;
	bool ok = try_parse_type_name(type);
	pos_ = save;
	return ok;
}

bool Parser::starts_class_key() const
{
	return at(KW_STRUCT) || at(KW_CLASS) || at(KW_UNION);
}

bool Parser::starts_ptr_operator() const
{
	return at(OP_STAR) || at(OP_AMP) || at(OP_LAND) ||
	       (at_identifier() && lookahead(OP_COLON2, 1));
}

bool Parser::starts_declarator() const
{
	return starts_ptr_operator() || at(OP_LPAREN) || at(OP_COLON2) ||
	       at_identifier();
}

bool Parser::starts_abstract_declarator() const
{
	return starts_ptr_operator() || at(OP_LPAREN) || at(OP_LSQUARE);
}

bool Parser::starts_parenthesized_abstract_declarator() const
{
	if (!at(OP_LPAREN))
		return false;
	return lookahead(OP_STAR, 1) || lookahead(OP_AMP, 1) ||
	       lookahead(OP_LAND, 1) || lookahead(OP_LPAREN, 1) ||
	       lookahead(OP_RPAREN, 1);
}

bool Parser::at_simple_ignored_specifier() const
{
	return pos_ < tokens_.size() &&
	       tokens_[pos_].kind == posttoken::TokenKind::Simple &&
	       pa11::is_storage_or_function_specifier(tokens_[pos_].type);
}

bool Parser::at_simple_cv() const
{
	return pos_ < tokens_.size() &&
	       tokens_[pos_].kind == posttoken::TokenKind::Simple &&
	       pa11::is_cv_token(tokens_[pos_].type);
}

bool Parser::at_simple_builtin() const
{
	return pos_ < tokens_.size() &&
	       tokens_[pos_].kind == posttoken::TokenKind::Simple &&
	       pa11::is_builtin_type_token(tokens_[pos_].type);
}

unsigned Parser::consume_cv_flag()
{
	if (consume(KW_CONST))
		return pa11::CV_CONST;
	expect(KW_VOLATILE);
	return pa11::CV_VOLATILE;
}

}  // namespace internal
}  // namespace pa12
