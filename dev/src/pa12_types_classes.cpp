#include "pa12_types_support.h"

#include <algorithm>
#include <stdexcept>

using namespace std;

namespace pa12 {
namespace internal {

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
				{
					ConstexprValue value;
					if (try_evaluate_constexpr_expr(align_expr.node,
					                                value) &&
					    !value.is_object)
					{
						align_expr.has_constant_value = true;
						align_expr.constant_value = value.int_value;
					}
				}
				if (!align_expr.has_constant_value)
				{
					bool dependent_align =
						validating_template_definition_ &&
						(type_is_template_dependent(align_expr.type) ||
						 !align_expr.dependent_value_name.empty());
					if (dependent_align)
						align_value = 0;
					else
						throw runtime_error("invalid alignas");
				}
				else
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
	bool active_template_class =
		!active_class_instantiations_.empty() &&
		active_class_instantiations_.back().declaration != NULL &&
		active_class_instantiations_.back().declaration->name == name;
	if (at(OP_LT))
	{
		if (active_template_class)
		{
			if (!skip_template_id_syntax(tokens_, pos_))
				throw runtime_error("invalid class template-id");
		}
		else
		{
			vector<TemplateArgument> ignored_template_id;
			parse_template_argument_list(ignored_template_id);
		}
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
			const bool injected_anonymous_member =
				(key == KW_UNION || key == KW_STRUCT) &&
				current_scope()->kind != ScopeKind::Namespace &&
				p < tokens_.size() &&
				tokens_[p].kind == posttoken::TokenKind::Simple &&
				tokens_[p].type == OP_SEMICOLON;
		name = injected_anonymous_member
			? "__anonymous_union_type__" + to_string(start_index) +
			  "_" + to_string(p + 1)
			: make_local_type_name("__local_type");
	}
	if (!anonymous && !active_template_class)
	{
		Scope* owner = qualified_owner != NULL ? qualified_owner : current_scope();
		Binding* existing = qualified_owner != NULL
			? pa11::lookup_qualified(qualified_owner,
			                         name,
			                         pa11::LOOKUP_TYPE)
			: pa11::lookup_unqualified(owner, name, pa11::LOOKUP_TYPE);
		TypePtr existing_record = existing != NULL
			? pa11::strip_cv(existing->type) : TypePtr();
		if (existing_record.get() == NULL ||
		    existing_record->kind != pa11::TypeKind::Record)
			add_record(owner,
			           name,
			           class_tag(key),
			           false,
			           NULL);
	}
	TypePtr direct_base;
	if (consume(OP_COLON))
	{
		do
		{
			if (at(KW_PUBLIC) || at(KW_PRIVATE) || at(KW_PROTECTED))
				++pos_;
			TypePtr parsed_direct_base;
			bool save_parsing_base = parsing_base_specifier_;
			parsing_base_specifier_ = true;
			bool parsed_base = false;
			try
			{
				if (at(KW_DECLTYPE))
				{
					parsed_direct_base = parse_decltype_specifier();
					parsed_base = true;
				}
				else
					parsed_base = try_parse_type_name(parsed_direct_base);
			}
			catch (...)
			{
				parsing_base_specifier_ = save_parsing_base;
				throw;
			}
			parsing_base_specifier_ = save_parsing_base;
			if (!parsed_base)
				throw runtime_error("invalid base class");
			if (consume(OP_DOTS))
				parsed_direct_base.reset();
			if (parsed_direct_base.get() != NULL)
				direct_base = parsed_direct_base;
		}
		while (consume(OP_COMMA));
		if (direct_base.get() != NULL &&
		    (direct_base->is_dependent_typename ||
		     type_is_template_dependent(direct_base)) &&
		    (!template_type_substitutions_.empty() ||
		     !template_value_substitutions_.empty()))
		{
			try
			{
				direct_base = substitute_template_type(direct_base);
			}
			catch (const runtime_error&)
			{
			}
		}
		TypePtr base_bare = direct_base.get() != NULL
			? pa11::strip_cv(direct_base) : TypePtr();
		if (base_bare.get() != NULL &&
		    base_bare->kind != pa11::TypeKind::Record &&
		    base_bare->kind != pa11::TypeKind::TemplateParameter)
			throw runtime_error("invalid base class");
	}
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
		TypePtr concrete_base = direct_base.get() != NULL
		? pa11::strip_cv(direct_base) : TypePtr();
	if (concrete_base.get() != NULL &&
	    concrete_base->kind == pa11::TypeKind::Record &&
	    concrete_base.get() != type.get() &&
	    !type_is_template_dependent(concrete_base))
	{
		complete_template_record(concrete_base);
	}
	bool defer_dependent_base_layout = false;
			if (active_template_class && direct_base.get() != NULL)
			{
				TemplateDeclaration* declaration =
					active_class_instantiations_.back().declaration;
				bool dependent_base = type_is_template_dependent(direct_base);
				if (!dependent_base && direct_base.get() == type.get())
					dependent_base = true;
				if (dependent_base)
				{
				defer_dependent_base_layout = true;
				class_templates_with_dependent_base_.insert(declaration);
				record_dependent_base_lookup_skips_.insert(type.get());
				if (direct_base.get() == type.get())
					type->base.reset();
			}
			else
				record_dependent_base_lookup_skips_.erase(type.get());
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
	for (size_t i = 0; class_scope != NULL &&
	     i < class_scope->binding_order.size(); ++i)
	{
		Binding* field = class_scope->binding_order[i];
		if (field->kind != BindingKind::Variable ||
		    field->is_static_member ||
		    field->aliased_binding != NULL)
			continue;
		field->type = substitute_template_type(field->type);
		TypePtr field_type = field->type;
		field_type = field_type.get() != NULL
			? pa11::strip_cv(field_type) : TypePtr();
		while (field_type.get() != NULL &&
		       field_type->kind == pa11::TypeKind::Array)
			field_type = pa11::strip_cv(field_type->base);
		if (field_type.get() != NULL &&
		    field_type->kind == pa11::TypeKind::Record)
			complete_template_record(field_type);
	}
	for (size_t i = 0; i < extra_lowir_nodes_.size(); ++i)
		if (extra_lowir_nodes_[i].binding != NULL &&
		    extra_lowir_nodes_[i].binding->owner == class_scope)
			resolve_pending_member_initializers(class_scope,
			                                    extra_lowir_nodes_[i]);
	TypePtr direct_base_bare =
		direct_base.get() != NULL ? pa11::strip_cv(direct_base) : TypePtr();
	if (direct_base_bare.get() != NULL &&
	    direct_base_bare->kind == pa11::TypeKind::Record &&
	    direct_base_bare.get() != type.get() &&
	    !type_is_template_dependent(direct_base_bare))
		complete_template_record(direct_base_bare);
	try
	{
		if (!defer_dependent_base_layout)
			pa11::layout_record_type(type);
	}
	catch (const runtime_error& err)
	{
		if ((string(err.what()) != "incomplete class type" &&
		     string(err.what()) != "incomplete object type" &&
		     string(err.what()) != "incomplete array type") ||
		    active_class_instantiations_.empty())
			throw;
	}
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
		if (at(KW_TEMPLATE))
		{
			parse_template_declaration();
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
			bool layout_ok = true;
			try
			{
				pa11::layout_record_type(class_type);
			}
			catch (const runtime_error& err)
			{
					if ((string(err.what()) != "incomplete class type" &&
					     string(err.what()) != "incomplete object type" &&
					     string(err.what()) != "incomplete array type") ||
					    active_class_instantiations_.empty())
						throw;
				layout_ok = false;
			}
			for (size_t i = 0; i < defaulted_move_assignments_.size(); ++i)
			{
				if (!layout_ok)
					break;
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

}  // namespace internal
}  // namespace pa12
