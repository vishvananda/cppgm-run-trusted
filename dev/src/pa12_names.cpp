#include "pa12_internal.h"

#include <stdexcept>

using namespace std;

namespace pa12 {
namespace internal {

namespace {

pa11::TemplateInstanceArgument nested_name_template_instance_argument(
	const TemplateArgument& argument)
{
	if (argument.kind == TemplateArgumentKind::Type)
		return pa11::TemplateInstanceArgument::type_arg(argument.type);
	if (argument.kind == TemplateArgumentKind::Value)
	{
		pa11::TemplateInstanceArgument out = argument.dependent
			? pa11::TemplateInstanceArgument::dependent_value_arg(argument.type)
			: pa11::TemplateInstanceArgument::value_arg(argument.type,
			                                            argument.value);
		out.value_name = argument.value_name;
		out.value_negated = argument.value_negated;
		out.value_owner_template_name = argument.value_owner_template_name;
		out.value_member_name = argument.value_member_name;
		out.value_owner_template_arguments =
			argument.value_owner_template_arguments;
		out.value_expr_begin = argument.value_expr_begin;
		out.value_expr_end = argument.value_expr_end;
		return out;
	}
	if (argument.kind == TemplateArgumentKind::Template)
	{
			pa11::TemplateInstanceArgument out =
				pa11::TemplateInstanceArgument::template_arg(
					argument.template_declaration != NULL
					? qualified_template_declaration_name(
						argument.template_declaration)
					: argument.value_name);
		out.dependent = argument.template_declaration == NULL;
		return out;
	}
	vector<pa11::TemplateInstanceArgument> pack;
	for (size_t i = 0; i < argument.pack.size(); ++i)
		pack.push_back(nested_name_template_instance_argument(
			argument.pack[i]));
	pa11::TemplateInstanceArgument out =
		pa11::TemplateInstanceArgument::pack_arg(pack);
	out.value_name = argument.value_name;
	out.template_name = argument.value_name;
	return out;
}

vector<pa11::TemplateInstanceArgument> nested_name_template_instance_arguments(
	const vector<TemplateArgument>& arguments)
{
	vector<pa11::TemplateInstanceArgument> out;
	for (size_t i = 0; i < arguments.size(); ++i)
		out.push_back(nested_name_template_instance_argument(arguments[i]));
	return out;
}

bool type_argument_names_parameter(TypePtr type,
                                   const TemplateParameterInfo& parameter)
{
	if (parameter.kind != TemplateParameterKind::Type ||
	    type.get() == NULL)
		return false;
	TypePtr bare = pa11::strip_cv(type);
	return bare.get() != NULL &&
	       bare->kind == pa11::TypeKind::TemplateParameter &&
	       bare->name == parameter.name;
}

bool template_argument_names_parameter(
	const TemplateArgument& argument,
	const TemplateParameterInfo& parameter)
{
	if (parameter.name.empty())
		return false;
	if (parameter.kind == TemplateParameterKind::Type)
		return argument.kind == TemplateArgumentKind::Type &&
		       type_argument_names_parameter(argument.type, parameter);
	if (parameter.kind == TemplateParameterKind::NonType)
		return argument.kind == TemplateArgumentKind::Value &&
		       argument.dependent &&
		       argument.value_name == parameter.name;
	return argument.kind == TemplateArgumentKind::Template &&
	       argument.template_declaration == NULL &&
	       argument.value_name == parameter.name;
}

bool select_dependent_specialization_arguments(
	TemplateDeclaration* specialization,
	const vector<TemplateArgument>& pattern,
	const vector<TemplateArgument>& arguments,
	vector<TemplateArgument>& selected)
{
	selected.clear();
	for (size_t pi = 0; pi < specialization->parameters.size(); ++pi)
	{
		const TemplateParameterInfo& parameter =
			specialization->parameters[pi];
		bool found = false;
		for (size_t ai = 0;
		     ai < pattern.size() && ai < arguments.size();
		     ++ai)
		{
			if (!template_argument_names_parameter(pattern[ai],
			                                      parameter))
				continue;
			selected.push_back(arguments[ai]);
			found = true;
			break;
		}
		if (!found)
			return false;
	}
	return true;
}

bool template_argument_list_has_value(
	const vector<TemplateArgument>& arguments)
{
	for (size_t i = 0; i < arguments.size(); ++i)
	{
		const TemplateArgument& arg = arguments[i];
		if (arg.kind == TemplateArgumentKind::Value)
			return true;
		if (arg.kind == TemplateArgumentKind::Pack &&
		    template_argument_list_has_value(arg.pack))
			return true;
	}
	return false;
}

}  // namespace

bool template_id_followed_by_qualifier(const vector<Token>& tokens,
                                       size_t pos)
{
	int angle_depth = 0;
	int paren_depth = 0;
	int bracket_depth = 0;
	int brace_depth = 0;
	for (; pos < tokens.size(); ++pos)
	{
		const Token& tok = tokens[pos];
		if (tok.kind != posttoken::TokenKind::Simple)
			continue;
		if (tok.type == OP_LPAREN)
			++paren_depth;
		else if (tok.type == OP_RPAREN)
		{
			if (paren_depth > 0)
				--paren_depth;
		}
		else if (tok.type == OP_LSQUARE)
			++bracket_depth;
		else if (tok.type == OP_RSQUARE)
		{
			if (bracket_depth > 0)
				--bracket_depth;
		}
		else if (tok.type == OP_LBRACE)
			++brace_depth;
		else if (tok.type == OP_RBRACE)
		{
			if (brace_depth > 0)
				--brace_depth;
		}
		else if (paren_depth == 0 &&
		         bracket_depth == 0 &&
		         brace_depth == 0 &&
		         tok.type == OP_LT)
			++angle_depth;
		else if (paren_depth == 0 &&
		         bracket_depth == 0 &&
		         brace_depth == 0 &&
		         tok.type == OP_GT)
		{
			--angle_depth;
			if (angle_depth == 0)
				return pos + 1 < tokens.size() &&
				       tokens[pos + 1].kind == posttoken::TokenKind::Simple &&
				       tokens[pos + 1].type == OP_COLON2;
			if (angle_depth < 0)
				return false;
		}
	}
	return false;
}

string Parser::conversion_operator_name(TypePtr type) const
{
	return "operator " + pa11::describe_type(type);
}

TypePtr Parser::parse_conversion_type_id()
{
	DeclSpecs specs = parse_decl_specifier_seq(true);
	TypePtr type = type_from_decl_specs(specs);
	TypePtr bare = type.get() != NULL ? pa11::strip_cv(type) : TypePtr();
	if (bare.get() != NULL &&
	    bare->kind == pa11::TypeKind::TemplateTemplateParameter &&
	    at(OP_LT))
	{
		vector<TemplateArgument> arguments;
		parse_template_argument_list(arguments);
		TypePtr specialized =
			pa11::make_record_type(bare->name + "<>",
			                       "struct",
			                       false,
			                       NULL);
		specialized->is_template_specialization = true;
		specialized->is_dependent_typename = true;
		specialized->dependent_typename_template_id = true;
		specialized->template_primary_name = bare->name;
		specialized->template_arguments =
			nested_name_template_instance_arguments(arguments);
		record_template_arguments_[specialized.get()] = arguments;
		type = specialized;
	}
	vector<PtrOp> ops;
	parse_ptr_prefix(ops);
	return apply_ptr_ops(type, ops);
}

string Parser::consume_operator_function_name()
{
	expect(KW_OPERATOR);
	if (consume(KW_NEW))
	{
		if (consume(OP_LSQUARE))
		{
			expect(OP_RSQUARE);
			return "operatornew[]";
		}
		return "operatornew";
	}
	if (consume(KW_DELETE))
	{
		if (consume(OP_LSQUARE))
		{
			expect(OP_RSQUARE);
			return "operatordelete[]";
		}
		return "operatordelete";
	}
	{
		size_t save = pos_;
		try
		{
			return conversion_operator_name(parse_conversion_type_id());
		}
		catch (const exception&)
		{
			pos_ = save;
		}
	}
	if (consume(OP_LPAREN))
	{
		expect(OP_RPAREN);
		return "operator()";
	}
	if (consume(OP_LSQUARE))
	{
		expect(OP_RSQUARE);
		return "operator[]";
	}
	if (at(OP_GT) && lookahead(OP_GT, 1))
	{
		pos_ += 2;
		return "operator>>";
	}
	if (at_literal())
		return "operator" + consume_literal();
	if (current().kind != posttoken::TokenKind::Simple)
		throw runtime_error("expected operator token");
	string name = "operator" + current().source;
	++pos_;
	return name;
}

QualifiedName Parser::parse_id_expression_name()
{
	QualifiedName name;
	bool template_id_qualifier = false;
	if (at_identifier() && lookahead(OP_LT, 1))
		template_id_qualifier =
			template_id_followed_by_qualifier(tokens_, pos_ + 1);
	if (at(KW_DECLTYPE) ||
	    at(OP_COLON2) ||
	    (at_identifier() &&
	     (lookahead(OP_COLON2, 1) || template_id_qualifier)))
	{
		string spelling;
		name.qualifier = parse_nested_name_specifier(&spelling);
		name.spelling = spelling;
		name.qualified = true;
	}
	bool template_disambiguator = false;
	if (name.qualified)
		template_disambiguator = consume(KW_TEMPLATE);
	if (consume(KW_OPERATOR))
	{
		--pos_;
		name.name = consume_operator_function_name();
	}
	else
		name.name = consume_identifier();
	if (at(OP_LT))
	{
		size_t template_save = pos_;
		try
		{
			name.has_template_arguments = true;
			parse_template_argument_list(name.template_arguments);
			bool adl_template_call =
				!name.qualified &&
				direct_template_call_depth_ != 0 &&
				at(OP_LPAREN);
			if ((template_argument_expression_depth_ > 0 ||
			     template_argument_list_has_value(name.template_arguments)) &&
			    !adl_template_call &&
			    !template_disambiguator &&
			    !visible_function_template_name(name) &&
			    !visible_variable_template_name(name))
			{
				name.has_template_arguments = false;
				name.template_arguments.clear();
				pos_ = template_save;
			}
		}
		catch (const exception&)
		{
			vector<TemplateDeclaration*> templates =
				find_function_templates(name);
			if (!templates.empty())
				throw;
			name.has_template_arguments = false;
			name.template_arguments.clear();
			pos_ = template_save;
		}
	}
	if (name.qualified)
		name.spelling += name.name;
	else
		name.spelling = name.name;
	return name;
}

Scope* Parser::parse_nested_name_specifier(string* spelling)
{
	Scope* scope = NULL;
	string text;
	auto enter_dependent_component =
			[&](Scope* owner_scope,
			    const string& component_spelling,
			    Scope*& dependent_scope) -> bool
	{
		TypePtr owner = pa11::record_type_for_scope(owner_scope);
		owner = owner.get() != NULL ? pa11::strip_cv(owner) : TypePtr();
		if (owner.get() == NULL ||
		    owner->kind != pa11::TypeKind::Record ||
		    !owner->is_template_specialization ||
		    !type_is_template_dependent(owner))
			return false;
		Scope* new_scope =
			pa11::create_child_scope(current_scope(),
			                         ScopeKind::Class,
			                         component_spelling);
		TypePtr dependent_type =
			pa11::make_record_type(component_spelling,
			                       "struct",
			                       false,
			                       new_scope);
		dependent_type->is_template_specialization = true;
		dependent_type->is_dependent_typename = true;
		dependent_type->dependent_typename_qualified = true;
		dependent_type->dependent_typename_template_id =
			owner->dependent_typename_template_id;
		dependent_type->template_primary_name =
			owner->template_primary_name.empty()
			? owner->name : owner->template_primary_name;
		size_t primary_template =
			dependent_type->template_primary_name.find('<');
		if (primary_template != string::npos)
			dependent_type->template_primary_name =
				dependent_type->template_primary_name.substr(
					0,
					primary_template);
		dependent_type->template_arguments = owner->template_arguments;
		dependent_type->dependent_typename_template_argument_lists =
			owner->dependent_typename_template_argument_lists;
		map<const void*, vector<TemplateArgument> >::const_iterator args =
			record_template_arguments_.find(owner.get());
		if (args != record_template_arguments_.end())
			record_template_arguments_[dependent_type.get()] = args->second;
		pa11::add_binding(current_scope(),
		                  BindingKind::Type,
		                  component_spelling,
		                  dependent_type);
			dependent_scope = new_scope;
			return true;
		};
	auto attach_dependent_scope_record =
		[&](Scope* dependent_scope,
		    const string& component_spelling,
		    TypePtr source_type) -> void
	{
		if (dependent_scope == NULL ||
		    dependent_scope->kind != ScopeKind::Class)
			return;
		TypePtr bare_source = source_type.get() != NULL
			? pa11::strip_cv(source_type) : TypePtr();
		TypePtr dependent_type =
			pa11::make_record_type(component_spelling,
			                       "struct",
			                       false,
			                       dependent_scope);
		dependent_type->is_template_specialization =
			bare_source.get() != NULL &&
			bare_source->is_template_specialization;
		dependent_type->is_dependent_typename = true;
		dependent_type->dependent_typename_qualified = true;
		dependent_type->dependent_typename_template_id =
			bare_source.get() != NULL &&
			bare_source->dependent_typename_template_id;
		if (bare_source.get() != NULL)
		{
			dependent_type->template_primary_name =
				bare_source->template_primary_name.empty()
				? bare_source->name
				: bare_source->template_primary_name;
			dependent_type->template_arguments =
				bare_source->template_arguments;
			dependent_type->dependent_typename_template_argument_lists =
				bare_source->dependent_typename_template_argument_lists;
			map<const void*, vector<TemplateArgument> >::const_iterator args =
				record_template_arguments_.find(bare_source.get());
			if (args != record_template_arguments_.end())
				record_template_arguments_[dependent_type.get()] =
					args->second;
			map<const void*, TemplateDeclaration*>::const_iterator decl =
				record_template_declarations_.find(bare_source.get());
			if (decl != record_template_declarations_.end())
				record_template_declarations_[dependent_type.get()] =
					decl->second;
		}
		dependent_scope->record_type = dependent_type;
	};
	auto enter_member_class_component =
		[&](Scope* owner_scope,
		    const string& component,
		    Scope*& member_scope) -> bool
	{
		TemplateDeclaration* declaration =
			find_class_template(owner_scope, component);
		if (declaration == NULL)
			return false;
		Binding* binding =
			pa11::lookup_qualified(owner_scope, component, pa11::LOOKUP_TYPE);
		if (binding == NULL)
		{
			Scope* class_scope =
				pa11::create_child_scope(owner_scope,
				                         ScopeKind::Class,
				                         component);
			TypePtr type =
				add_record(owner_scope,
				           component,
				           declaration->tag.empty()
				           ? string("class") : declaration->tag,
				           false,
				           class_scope);
			TypePtr bare = pa11::strip_cv(type);
			record_template_declarations_[bare.get()] = declaration;
			record_template_arguments_[bare.get()] = vector<TemplateArgument>();
			binding = pa11::lookup_qualified(owner_scope,
			                                 component,
			                                 pa11::LOOKUP_TYPE);
		}
		if (binding == NULL || binding->type.get() == NULL)
			return false;
		complete_member_class_template_record(binding);
		TypePtr bare = pa11::strip_cv(binding->type);
		if (bare->kind != pa11::TypeKind::Record || bare->scope == NULL)
			return false;
		member_scope = bare->scope;
		return true;
	};
	auto make_dependent_template_qualifier =
		[&](TemplateDeclaration* declaration,
		    const string& component,
		    const vector<TemplateArgument>& arguments) -> TypePtr
	{
		TemplateDeclaration* recorded_declaration = declaration;
		vector<TemplateArgument> recorded_arguments = arguments;
		if (declaration != NULL)
		{
			string argument_key = template_argument_key(arguments);
			for (size_t i = 0;
			     i < declaration->class_specialization_declarations.size();
			     ++i)
			{
				TemplateDeclaration* candidate =
					declaration->class_specialization_declarations[i];
				if (template_argument_key(
					    candidate->class_specialization_pattern) !=
				    argument_key)
					continue;
				vector<TemplateArgument> selected;
				if (!select_dependent_specialization_arguments(
					    candidate,
					    candidate->class_specialization_pattern,
					    arguments,
					    selected))
					continue;
				recorded_declaration = candidate;
				recorded_arguments = selected;
				break;
			}
		}
		Scope* dependent_scope =
			pa11::create_child_scope(current_scope(),
			                         ScopeKind::Class,
			                         component);
		TypePtr type = pa11::make_record_type(component + "<>",
		                                      "struct",
		                                      false,
		                                      dependent_scope);
		type->is_template_specialization = true;
		type->is_dependent_typename = true;
		type->dependent_typename_template_id = true;
		type->template_primary_name =
			declaration != NULL
			? qualified_template_declaration_name(declaration)
			: component;
		type->template_arguments =
			nested_name_template_instance_arguments(arguments);
		if (recorded_declaration != NULL)
			record_template_declarations_[type.get()] =
				recorded_declaration;
		record_template_arguments_[type.get()] = recorded_arguments;
		pa11::add_binding(current_scope(),
		                  BindingKind::Type,
		                  component + "<>",
		                  type);
		return type;
	};
	auto make_hosted_trait_template_qualifier =
		[&](const string& component,
		    const vector<TemplateArgument>& arguments) -> TypePtr
	{
		Scope* dependent_scope =
			pa11::create_child_scope(current_scope(),
			                         ScopeKind::Class,
			                         component + "<>");
		TypePtr type = pa11::make_record_type(component + "<>",
		                                      "struct",
		                                      false,
		                                      dependent_scope);
		type->is_template_specialization = true;
		type->is_dependent_typename = true;
		type->dependent_typename_template_id = true;
		type->template_primary_name = component;
		type->template_arguments =
			nested_name_template_instance_arguments(arguments);
		record_template_arguments_[type.get()] = arguments;
		pa11::add_binding(current_scope(),
		                  BindingKind::Type,
		                  component + "<>",
		                  type);
		return type;
	};
	auto complete_qualifier_record = [&](TypePtr qualifier_type) {
		size_t saved_pos = pos_;
		vector<Scope*> saved_scopes = scopes_;
		complete_template_record(qualifier_type);
		scopes_ = saved_scopes;
		pos_ = saved_pos;
	};
	auto instantiate_qualifier_template_members = [&](TypePtr qualifier_type) {
		size_t saved_pos = pos_;
		vector<Scope*> saved_scopes = scopes_;
		complete_template_record(qualifier_type);
		if (suppress_qualifier_template_member_instantiation_depth_ == 0)
		{
			instantiate_member_function_templates(qualifier_type);
			instantiate_member_variable_templates(qualifier_type);
		}
		scopes_ = saved_scopes;
		pos_ = saved_pos;
	};
	auto complete_qualifier_binding = [&](Binding* binding) {
		size_t saved_pos = pos_;
		vector<Scope*> saved_scopes = scopes_;
		if (binding != NULL && binding->type.get() != NULL)
			complete_member_class_template_record(binding);
		if (binding != NULL && binding->type.get() != NULL)
			complete_template_record(binding->type);
		scopes_ = saved_scopes;
		pos_ = saved_pos;
	};
	if (consume(OP_COLON2))
	{
		scope = global_scope();
		text = "::";
		while (at_identifier())
		{
			size_t component_save = pos_;
			string component = consume_identifier();
			if (at(OP_LT))
			{
				TemplateDeclaration* alias =
					find_alias_template(scope, component);
				TemplateDeclaration* templ = alias == NULL
					? find_class_template(scope, component) : NULL;
					if (alias != NULL || templ != NULL)
					{
						vector<TemplateArgument> arguments;
						parse_template_argument_list(arguments);
						if (consume(OP_COLON2))
						{
								bool dependent_arguments =
									template_arguments_dependent(arguments);
								TypePtr type;
								if (hosted_compatibility_ &&
								    component == "__empty_not_final")
									type =
										make_hosted_trait_template_qualifier(
											component,
											arguments);
								else
									type =
										dependent_arguments && templ != NULL
										? make_dependent_template_qualifier(
											templ,
											component,
											arguments)
										: (alias != NULL
										   ? instantiate_alias_template(alias, arguments)
										   : instantiate_class_template(templ, arguments));
							TypePtr dependent_bare =
								type.get() != NULL
								? pa11::strip_cv(type) : TypePtr();
							bool dependent_has_scope =
								dependent_bare.get() != NULL &&
								dependent_bare->kind == pa11::TypeKind::Record &&
								dependent_bare->scope != NULL;
							if (type_is_template_dependent(type) &&
							    !dependent_has_scope &&
							    template_argument_expression_depth_ == 0 &&
							    templ != NULL)
							{
								Binding* primary =
									pa11::lookup_qualified(templ->owner,
									                       templ->name,
									                       pa11::LOOKUP_TYPE);
								if (primary != NULL &&
								    primary->type.get() != NULL)
									type = primary->type;
							}
							if (!type_is_template_dependent(type))
								instantiate_qualifier_template_members(type);
						type = pa11::strip_cv(type);
						if (type->kind != pa11::TypeKind::Record ||
						    type->scope == NULL)
							throw runtime_error(
								"template-id qualifier is not a scope");
						scope = type->scope;
						text += component + "::";
						continue;
					}
				}
				pos_ = component_save;
				break;
			}
			Binding* binding =
				pa11::lookup_qualified(scope,
				                       component,
				                       pa11::LOOKUP_QUALIFIER);
			if (binding == NULL || !consume(OP_COLON2))
			{
				pos_ = component_save;
				break;
			}
			if (binding->type.get() != NULL)
				complete_qualifier_record(binding->type);
			Scope* next = resolve_qualifier(binding);
			if (next == NULL)
				throw runtime_error("qualified lookup root not found: " +
				                    component);
			scope = next;
			text += component + "::";
		}
	}
	else if (at(KW_DECLTYPE))
	{
		TypePtr type = parse_decltype_specifier();
		expect(OP_COLON2);
		TypePtr bare_decltype =
			type.get() != NULL ? pa11::strip_cv(type) : TypePtr();
		if (bare_decltype.get() != NULL &&
		    bare_decltype->is_dependent_typename &&
		    bare_decltype->dependent_typename_decltype)
		{
			try
			{
				type = substitute_template_type(type);
			}
			catch (const runtime_error&)
			{
			}
		}
		type = expression_object_type(type);
		type = pa11::strip_cv(type);
		complete_qualifier_record(type);
		if ((type->kind != pa11::TypeKind::Record &&
		     type->kind != pa11::TypeKind::Enum) ||
		    type->scope == NULL)
			throw runtime_error("decltype qualifier is not a scope");
		scope = type->scope;
		text = "decltype::";
	}
	else if (at_identifier())
	{
		size_t save = pos_;
		string root = consume_identifier();
			if (at(OP_LT))
			{
				TemplateArgument template_subst;
				bool have_template_subst =
					find_template_value_substitution(root, template_subst) &&
					template_subst.kind == TemplateArgumentKind::Template;
					TemplateDeclaration* alias = find_alias_template(NULL, root);
					TemplateDeclaration* templ = alias == NULL
						? find_class_template(NULL, root) : NULL;
					if (alias == NULL &&
					    templ == NULL &&
					    !active_functions_.empty() &&
					    active_functions_.back() != NULL &&
					    active_functions_.back()->owner != NULL &&
					    active_functions_.back()->owner->kind == ScopeKind::Class)
					{
						Scope* owner_scope = active_functions_.back()->owner;
						alias = find_alias_template(owner_scope, root);
						templ = alias == NULL
							? find_class_template(owner_scope, root) : NULL;
					}
					if (have_template_subst ||
					    alias != NULL ||
					    templ != NULL)
					{
						vector<TemplateArgument> arguments;
						parse_template_argument_list(arguments);
						if (consume(OP_COLON2))
						{
							TypePtr type;
						if (have_template_subst &&
						    template_subst.template_declaration != NULL)
						{
							if (template_subst.template_declaration->kind ==
							    TemplateDeclarationKind::Alias)
								type = instantiate_alias_template(
									template_subst.template_declaration,
									arguments);
							else
								type = instantiate_class_template(
									template_subst.template_declaration,
									arguments);
						}
							else if (have_template_subst)
							{
								Scope* dependent_scope =
									pa11::create_child_scope(current_scope(),
								                         ScopeKind::Class,
								                         root + "<>");
							type = pa11::make_record_type(root + "<>",
							                              "struct",
							                              false,
							                              dependent_scope);
							type->is_template_specialization = true;
							type->is_dependent_typename = true;
							type->dependent_typename_template_id = true;
							type->template_primary_name = root;
							type->template_arguments =
								nested_name_template_instance_arguments(
									arguments);
							record_template_arguments_[type.get()] = arguments;
								pa11::add_binding(current_scope(),
								                  BindingKind::Type,
								                  root + "<>",
								                  type);
							}
								else
								{
									bool dependent_arguments =
										template_arguments_dependent(arguments);
									if (hosted_compatibility_ &&
									    root == "__empty_not_final")
										type =
											make_hosted_trait_template_qualifier(
												root,
												arguments);
									else
										type =
											dependent_arguments && templ != NULL
											? make_dependent_template_qualifier(
												templ,
												root,
												arguments)
											: (alias != NULL
											   ? instantiate_alias_template(alias, arguments)
											   : instantiate_class_template(templ, arguments));
								}
							TypePtr dependent_bare =
								type.get() != NULL
								? pa11::strip_cv(type) : TypePtr();
							bool dependent_has_scope =
								dependent_bare.get() != NULL &&
								dependent_bare->kind == pa11::TypeKind::Record &&
								dependent_bare->scope != NULL;
							if (type_is_template_dependent(type) &&
							    !dependent_has_scope &&
							    template_argument_expression_depth_ == 0 &&
							    templ != NULL)
						{
							Binding* primary =
								pa11::lookup_qualified(templ->owner,
								                       templ->name,
								                       pa11::LOOKUP_TYPE);
							if (primary != NULL &&
							    primary->type.get() != NULL)
								type = primary->type;
						}
							if (!type_is_template_dependent(type))
								instantiate_qualifier_template_members(type);
						type = pa11::strip_cv(type);
					if (type->kind != pa11::TypeKind::Record ||
					    type->scope == NULL)
						throw runtime_error(
							"template-id qualifier is not a scope");
					scope = type->scope;
					text = root + "::";
				}
				else
					pos_ = save;
			}
			else
				pos_ = save;
			}
			else
			{
				pos_ = save;
			}
			if (scope == NULL)
			{
				string ordinary_root = consume_identifier();
				expect(OP_COLON2);
				TypePtr subst_root;
			if (find_template_type_substitution(ordinary_root, subst_root))
			{
				subst_root = pa11::strip_cv(subst_root);
				if (subst_root.get() != NULL &&
				    subst_root->kind == pa11::TypeKind::Record &&
				    subst_root->scope == NULL &&
				    subst_root->is_template_specialization &&
				    !type_is_template_dependent(subst_root))
				{
					map<const void*, TemplateDeclaration*>::iterator decl =
						record_template_declarations_.find(subst_root.get());
					map<const void*, vector<TemplateArgument> >::iterator args =
						record_template_arguments_.find(subst_root.get());
					if (decl != record_template_declarations_.end() &&
					    args != record_template_arguments_.end())
						subst_root = pa11::strip_cv(
							instantiate_class_template(decl->second,
							                           args->second));
				}
				complete_qualifier_record(subst_root);
				if (subst_root->kind == pa11::TypeKind::Record &&
				    subst_root->scope != NULL)
				{
					scope = subst_root->scope;
					text = ordinary_root + "::";
				}
				else if (subst_root->kind == pa11::TypeKind::TemplateParameter)
				{
					scope = pa11::create_child_scope(current_scope(),
					                                ScopeKind::Class,
					                                ordinary_root);
					attach_dependent_scope_record(scope,
					                              ordinary_root,
					                              subst_root);
					text = ordinary_root + "::";
				}
			}
			if (scope != NULL)
				;
			else
			{
					Binding* binding =
						pa11::lookup_unqualified(current_scope(),
						                         ordinary_root,
						                         pa11::LOOKUP_QUALIFIER);
					if (binding == NULL &&
					    current_scope()->kind == ScopeKind::Class &&
					    current_scope()->name == ordinary_root)
					{
						scope = current_scope();
						text = ordinary_root + "::";
					}
					TypePtr binding_type =
						binding != NULL ? binding->type : TypePtr();
				if (binding_type.get() != NULL &&
				    binding_type->is_dependent_typename)
				{
					if (binding_type->dependent_typename_decltype)
					{
						try
						{
							binding_type =
								substitute_template_type(binding_type);
						}
						catch (const runtime_error&)
						{
						}
					}
					else
					{
						TypePtr resolved =
							resolve_dependent_typename_type(binding_type);
						if (resolved.get() != NULL)
							binding_type = substitute_template_type(resolved);
					}
				}
				if (binding_type.get() != NULL)
				{
					complete_qualifier_record(binding_type);
					TypePtr bare = pa11::strip_cv(binding_type);
					if (bare->kind == pa11::TypeKind::Record &&
					    bare->scope != NULL)
						scope = bare->scope;
				}
				if (scope == NULL &&
				    binding_type.get() != NULL &&
				    (pa11::strip_cv(binding_type)->kind ==
				     pa11::TypeKind::TemplateParameter ||
				     pa11::strip_cv(binding_type)->is_dependent_typename))
				{
					scope = pa11::create_child_scope(current_scope(),
					                                ScopeKind::Class,
					                                ordinary_root);
					attach_dependent_scope_record(scope,
					                              ordinary_root,
					                              binding_type);
				}
				if (scope == NULL)
					scope = resolve_qualifier(binding);
				if (scope == NULL)
				{
					string detail = ordinary_root;
					detail += binding != NULL ? " binding" : " no-binding";
					if (binding_type.get() != NULL)
						detail += " type=" + pa11::describe_type(binding_type);
					throw runtime_error("qualified lookup root not found: " +
					                    detail);
				}
				text = ordinary_root + "::";
			}
		}
	}
	else
	{
		string root = consume_identifier();
		expect(OP_COLON2);
			Binding* binding =
				pa11::lookup_unqualified(current_scope(), root, pa11::LOOKUP_QUALIFIER);
			if (binding == NULL &&
			    current_scope()->kind == ScopeKind::Class &&
			    current_scope()->name == root)
			{
				scope = current_scope();
				text = root + "::";
			}
			TypePtr binding_type =
				binding != NULL && binding->type.get() != NULL
				? pa11::strip_cv(binding->type) : TypePtr();
		if (binding_type.get() != NULL &&
		    binding_type->is_dependent_typename)
		{
			if (binding_type->dependent_typename_decltype)
			{
				try
				{
					binding_type = substitute_template_type(binding_type);
				}
				catch (const runtime_error&)
				{
				}
			}
			else
			{
				TypePtr resolved =
					resolve_dependent_typename_type(binding_type);
				if (resolved.get() != NULL)
					binding_type = substitute_template_type(resolved);
			}
		}
		if (binding_type.get() != NULL)
		{
			complete_qualifier_record(binding_type);
			TypePtr bare = pa11::strip_cv(binding_type);
			if (bare->kind == pa11::TypeKind::Record &&
			    bare->scope != NULL)
				scope = bare->scope;
		}
			if (scope == NULL &&
			    binding_type.get() != NULL &&
			    (pa11::strip_cv(binding_type)->kind ==
			     pa11::TypeKind::TemplateParameter ||
			     pa11::strip_cv(binding_type)->is_dependent_typename))
			{
				scope = pa11::create_child_scope(current_scope(),
				                                ScopeKind::Class,
			                                root);
				attach_dependent_scope_record(scope,
				                              root,
				                              binding_type);
		}
			if (scope == NULL)
				scope = resolve_qualifier(binding);
			if (scope == NULL)
			{
				string detail = root;
				detail += binding != NULL ? " binding" : " no-binding";
				if (binding_type.get() != NULL)
					detail += " type=" + pa11::describe_type(binding_type);
				throw runtime_error("qualified lookup root not found: " + detail);
			}
			text = root + "::";
	}
	while (at_identifier() && lookahead(OP_COLON2, 1))
	{
		string component = consume_identifier();
		expect(OP_COLON2);
		vector<Binding*> found =
			lookup_qualified_set(scope, component, pa11::LOOKUP_QUALIFIER);
		if (found.empty())
		{
			Scope* member_class_scope = NULL;
			if (enter_member_class_component(scope,
			                                 component,
			                                 member_class_scope))
			{
				scope = member_class_scope;
				text += component + "::";
				continue;
			}
			Scope* dependent_scope = NULL;
			if (enter_dependent_component(scope,
			                              text + component,
			                              dependent_scope))
			{
				scope = dependent_scope;
				text += component + "::";
				continue;
			}
				throw runtime_error("qualified lookup component not found");
		}
		if (found[0]->type.get() != NULL)
			complete_qualifier_binding(found[0]);
		scope = resolve_qualifier(found[0]);
		if (scope == NULL)
			throw runtime_error("qualified lookup component not a scope");
		text += component + "::";
	}
	for (;;)
	{
		size_t save = pos_;
		consume(KW_TEMPLATE);
		if (!at_identifier())
		{
			pos_ = save;
			break;
		}
			string component = consume_identifier();
			if (!at(OP_LT))
			{
				pos_ = save;
				break;
			}
				TemplateDeclaration* alias = find_alias_template(scope, component);
				TemplateDeclaration* templ = alias == NULL
					? find_class_template(scope, component) : NULL;
				if (alias == NULL && templ == NULL)
				{
					pos_ = save;
					break;
				}
			vector<TemplateArgument> arguments;
		parse_template_argument_list(arguments);
		if (!consume(OP_COLON2))
		{
			pos_ = save;
			break;
		}
			TypePtr type = alias != NULL
				? instantiate_alias_template(alias, arguments)
				: instantiate_class_template(templ, arguments);
			if (!type_is_template_dependent(type))
				instantiate_qualifier_template_members(type);
		type = pa11::strip_cv(type);
		if (type->kind != pa11::TypeKind::Record || type->scope == NULL)
			throw runtime_error("template-id qualifier is not a scope");
		scope = type->scope;
		text += component + "::";
		while (at_identifier() && lookahead(OP_COLON2, 1))
		{
			string nested = consume_identifier();
			expect(OP_COLON2);
			vector<Binding*> found =
				lookup_qualified_set(scope, nested, pa11::LOOKUP_QUALIFIER);
			if (found.empty())
			{
				Scope* member_class_scope = NULL;
				if (enter_member_class_component(scope,
				                                 nested,
				                                 member_class_scope))
				{
					scope = member_class_scope;
					text += nested + "::";
					continue;
				}
				Scope* dependent_scope = NULL;
				if (enter_dependent_component(scope,
				                              text + nested,
				                              dependent_scope))
				{
					scope = dependent_scope;
					text += nested + "::";
					continue;
				}
					throw runtime_error("qualified lookup component not found");
			}
			if (found[0]->type.get() != NULL)
				complete_qualifier_binding(found[0]);
			scope = resolve_qualifier(found[0]);
			if (scope == NULL)
				throw runtime_error("qualified lookup component not a scope");
			text += nested + "::";
		}
	}
	if (spelling != NULL)
		*spelling = text;
	return scope;
}

Scope* Parser::parse_qualified_namespace_specifier()
{
	string spelling;
	Scope* qualifier = NULL;
	if (at(OP_COLON2) || (at_identifier() && lookahead(OP_COLON2, 1)))
		qualifier = parse_nested_name_specifier(&spelling);
	string name = consume_identifier();
	vector<Binding*> found = qualifier != NULL
		? lookup_qualified_set(qualifier, name, pa11::LOOKUP_NAMESPACE)
		: lookup_unqualified_set(current_scope(), name, pa11::LOOKUP_NAMESPACE);
	if (found.empty())
		throw runtime_error("namespace specifier not found");
	Scope* scope = resolve_qualifier(found[0]);
	if (scope == NULL || scope->kind != ScopeKind::Namespace)
		throw runtime_error("namespace specifier is not namespace");
	return scope;
}

bool Parser::is_assignment_operator(ETokenType& op) const
{
	if (current().kind != posttoken::TokenKind::Simple)
		return false;
	switch (current().type)
	{
	case OP_ASS:
	case OP_PLUSASS:
	case OP_MINUSASS:
	case OP_STARASS:
	case OP_DIVASS:
	case OP_MODASS:
	case OP_XORASS:
	case OP_BANDASS:
	case OP_BORASS:
	case OP_LSHIFTASS:
	case OP_RSHIFTASS:
		op = current().type;
		return true;
	default:
		return false;
	}
}

bool Parser::binary_operator(ETokenType& op, int& prec) const
{
	if (current().kind != posttoken::TokenKind::Simple)
		return false;
	op = current().type;
	if (current().type == OP_GT && current().split_rshift &&
	    pos_ + 1 < tokens_.size() && tokens_[pos_ + 1].split_rshift &&
	    tokens_[pos_ + 1].split_group == current().split_group)
		op = OP_RSHIFT;
	switch (op)
	{
	case OP_LOR: prec = 1; return true;
	case OP_LAND: prec = 2; return true;
	case OP_BOR: prec = 3; return true;
	case OP_XOR: prec = 4; return true;
	case OP_AMP: prec = 5; return true;
	case OP_EQ: case OP_NE: prec = 6; return true;
	case OP_LT: case OP_GT: case OP_LE: case OP_GE: prec = 7; return true;
	case OP_LSHIFT: case OP_RSHIFT: prec = 8; return true;
	case OP_PLUS: case OP_MINUS: prec = 9; return true;
	case OP_STAR: case OP_DIV: case OP_MOD: prec = 10; return true;
	case OP_DOTSTAR: case OP_ARROWSTAR: prec = 11; return true;
	default:
		return false;
	}
}

string Parser::operator_function_name(ETokenType type, const string& source) const
{
	if (type == OP_LPAREN)
		return "operator()";
	if (type == OP_LSQUARE)
		return "operator[]";
	return "operator" + source;
}

bool Parser::expression_starts_type_name(TypePtr& type)
{
	size_t save = pos_;
	++defer_class_template_completion_depth_;
	try
	{
		DeclSpecs specs = parse_decl_specifier_seq(true);
		type = type_from_decl_specs(specs);
		if (at(OP_LPAREN) || at(OP_LBRACE))
		{
			bool qualified_value_member = false;
			TypePtr bare = type.get() != NULL ? pa11::strip_cv(type) : TypePtr();
			if (bare.get() != NULL &&
			    bare->is_dependent_typename &&
			    bare->dependent_typename_qualified)
			{
				size_t member_pos = bare->name.rfind("::");
				string member_name = member_pos != string::npos
					? bare->name.substr(member_pos + 2) : string();
				size_t member_template_pos = member_name.find('<');
				if (member_template_pos != string::npos)
					member_name = member_name.substr(0, member_template_pos);
				string primary_name = bare->template_primary_name;
				if (primary_name.empty())
				{
					string root_name = member_pos != string::npos
						? bare->name.substr(0, member_pos) : bare->name;
					size_t root_template_pos = root_name.find('<');
					if (root_template_pos != string::npos)
						root_name = root_name.substr(0, root_template_pos);
					primary_name = root_name;
				}
				const vector<pa11::TemplateInstanceArgument>* owner_instances =
					!bare->template_arguments.empty()
					? &bare->template_arguments
					: (!bare->dependent_typename_template_argument_lists.empty()
					   ? &bare->dependent_typename_template_argument_lists[0]
					   : static_cast<const vector<pa11::TemplateInstanceArgument>*>(
						   NULL));
				vector<TemplateArgument> owner_args;
				bool owner_dependent = false;
				if (owner_instances != NULL)
					for (size_t i = 0; i < owner_instances->size(); ++i)
					{
						TemplateArgument arg =
							template_argument_from_instance_argument(
								(*owner_instances)[i]);
						arg = substitute_template_argument(arg);
						if (template_argument_has_template_parameter(
							    arg,
							    record_template_arguments_))
							owner_dependent = true;
						owner_args.push_back(arg);
					}
				if (!owner_dependent &&
				    !member_name.empty() &&
				    !primary_name.empty())
				{
					TemplateDeclaration* alias =
						find_alias_template(NULL, primary_name);
					TemplateDeclaration* klass = alias == NULL
						? find_class_template(NULL, primary_name)
						: NULL;
					TypePtr owner = alias != NULL
						? instantiate_alias_template(alias, owner_args)
						: (klass != NULL
						   ? instantiate_class_template(klass, owner_args)
						   : TypePtr());
					owner = owner.get() != NULL ? pa11::strip_cv(owner) : TypePtr();
					if (owner.get() != NULL &&
					    owner->kind == pa11::TypeKind::Record &&
					    owner->scope != NULL &&
					    !type_is_template_dependent(owner))
					{
						complete_template_record(owner);
						vector<Binding*> types =
							lookup_qualified_set(owner->scope,
							                     member_name,
							                     pa11::LOOKUP_TYPE);
						vector<Binding*> values =
							lookup_qualified_set(owner->scope,
							                     member_name,
							                     pa11::LOOKUP_VALUE);
						qualified_value_member =
							types.empty() && !values.empty();
					}
				}
			}
			if (qualified_value_member)
			{
				--defer_class_template_completion_depth_;
				pos_ = save;
				type.reset();
				return false;
			}
			--defer_class_template_completion_depth_;
			return true;
		}
	}
	catch (const exception&)
	{
		}
	--defer_class_template_completion_depth_;
	pos_ = save;
	type.reset();
	return false;
}

}  // namespace internal
}  // namespace pa12
