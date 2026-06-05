#include "pa12_internal.h"

#include <algorithm>
#include <stdexcept>

using namespace std;

namespace pa12 {
namespace internal {
namespace {

bool has_token(const vector<Token>& tokens,
               size_t begin,
               size_t end,
               ETokenType type)
{
	for (size_t i = begin; i < end && i < tokens.size(); ++i)
		if (tokens[i].kind == posttoken::TokenKind::Simple &&
		    tokens[i].type == type)
			return true;
	return false;
}

void merge_template_defaults(vector<TemplateParameterInfo>& target,
                             const vector<TemplateParameterInfo>& source)
{
	if (target.size() < source.size())
		target.resize(source.size());
	for (size_t i = 0; i < source.size(); ++i)
	{
		target[i].kind = source[i].kind;
		if (!source[i].name.empty())
			target[i].name = source[i].name;
		if (source[i].type.get() != NULL)
			target[i].type = source[i].type;
		if (!source[i].template_parameters.empty())
			target[i].template_parameters = source[i].template_parameters;
		target[i].is_pack = source[i].is_pack;
		if (source[i].has_default)
		{
			target[i].has_default = true;
			target[i].default_begin = source[i].default_begin;
			target[i].default_end = source[i].default_end;
		}
	}
}

Binding* find_matching_function(Scope* scope,
                                const string& name,
                                TypePtr type)
{
	if (scope == NULL)
		return NULL;
	map<string, vector<Binding*> >::iterator it = scope->members.find(name);
	if (it == scope->members.end())
		return NULL;
	for (size_t i = 0; i < it->second.size(); ++i)
	{
		Binding* binding = it->second[i];
		if (binding->kind == BindingKind::Function &&
		    pa11::same_type(binding->type, type))
			return binding;
	}
	return NULL;
}

void collect_template_parameter_placeholders(
	const vector<TemplateParameterInfo>& parameters,
	map<string, TypePtr>& parameter_types,
	map<string, TemplateArgument>& parameter_values)
{
	for (size_t i = 0; i < parameters.size(); ++i)
	{
		const TemplateParameterInfo& parameter = parameters[i];
		if (parameter.name.empty())
			continue;
		if (parameter.kind == TemplateParameterKind::Type)
			parameter_types[parameter.name] =
				pa11::make_template_parameter_type(parameter.name);
		else if (parameter.kind == TemplateParameterKind::NonType)
			parameter_values[parameter.name] =
				TemplateArgument::dependent_value_arg(
					parameter.type.get() != NULL
					? parameter.type
					: pa11::make_fundamental(FT_INT));
		else if (parameter.kind == TemplateParameterKind::TemplateTemplate)
			parameter_values[parameter.name] =
				TemplateArgument::template_arg(NULL);
	}
}

}  // namespace

vector<TemplateParameterInfo> Parser::parse_template_parameter_clause()
{
	vector<TemplateParameterInfo> parameters;
	expect(OP_LT);
	vector<map<string, TypePtr> > save_subst = template_type_substitutions_;
	vector<map<string, TemplateArgument> > save_value_subst =
		template_value_substitutions_;
	template_type_substitutions_.push_back(map<string, TypePtr>());
	template_value_substitutions_.push_back(map<string, TemplateArgument>());
	if (consume(OP_GT))
	{
		template_type_substitutions_ = save_subst;
		template_value_substitutions_ = save_value_subst;
		return parameters;
	}
	for (;;)
	{
		TemplateParameterInfo parameter = parse_template_parameter_info();
		parameters.push_back(parameter);
		if (!parameter.name.empty() &&
		    parameter.kind == TemplateParameterKind::Type)
			template_type_substitutions_.back()[parameter.name] =
				pa11::make_template_parameter_type(parameter.name);
		else if (!parameter.name.empty() &&
		         parameter.kind == TemplateParameterKind::TemplateTemplate)
			template_value_substitutions_.back()[parameter.name] =
				TemplateArgument::template_arg(NULL);
		if (!consume(OP_COMMA))
			break;
	}
	expect(OP_GT);
	template_type_substitutions_ = save_subst;
	template_value_substitutions_ = save_value_subst;
	return parameters;
}

TemplateParameterInfo Parser::parse_template_parameter_info()
{
	TemplateParameterInfo parameter;
	if (consume(KW_TEMPLATE))
	{
		parameter.kind = TemplateParameterKind::TemplateTemplate;
		parameter.template_parameters = parse_template_parameter_clause();
		if (!consume(KW_CLASS) && !consume(KW_TYPENAME))
			throw runtime_error("unsupported template template parameter");
		parameter.is_pack = consume(OP_DOTS);
		if (at_identifier())
			parameter.name = consume_identifier();
		if (consume(OP_ASS))
			skip_template_parameter_default(parameter);
		return parameter;
	}
	bool typename_qualified_type =
		at(KW_TYPENAME) &&
		pos_ + 2 < tokens_.size() &&
		tokens_[pos_ + 1].kind == posttoken::TokenKind::Identifier &&
		tokens_[pos_ + 2].kind == posttoken::TokenKind::Simple &&
		tokens_[pos_ + 2].type == OP_COLON2;
	if (!typename_qualified_type &&
	    (consume(KW_CLASS) || consume(KW_TYPENAME)))
	{
		parameter.kind = TemplateParameterKind::Type;
		parameter.is_pack = consume(OP_DOTS);
		if (at_identifier())
			parameter.name = consume_identifier();
		if (parameter.name.empty())
			parameter.name = "__template_param" +
			                 to_string(template_declarations_.size()) + "_" +
			                 to_string(pos_);
		if (consume(OP_ASS))
			skip_template_parameter_default(parameter);
		return parameter;
	}

	parameter.kind = TemplateParameterKind::NonType;
	DeclSpecs specs = parse_decl_specifier_seq(false);
	TypePtr base = type_from_decl_specs(specs);
	parameter.is_pack = consume(OP_DOTS);
	if (!at(OP_COMMA) && !at(OP_GT) && !at(OP_ASS))
	{
		Declarator declarator = parse_declarator(false);
		parameter.type = apply_declarator(declarator, base);
		if (declarator_has_name(declarator))
			parameter.name = declarator_name(declarator).name;
	}
	else
	{
		parameter.type = base;
	}
	if (consume(OP_ASS))
	{
		skip_template_parameter_default(parameter);
		return parameter;
	}
	return parameter;
}

void Parser::skip_template_parameter_default(TemplateParameterInfo& parameter)
{
	parameter.has_default = true;
	parameter.default_begin = pos_;
	int angle = 0;
	int paren = 0;
	int square = 0;
	int brace = 0;
	while (!at_eof())
	{
		if (angle == 0 && paren == 0 && square == 0 && brace == 0 &&
		    (at(OP_COMMA) || at(OP_GT)))
			break;
		if (at(OP_LT))
			++angle;
		else if (at(OP_GT))
		{
			if (angle == 0)
				break;
			--angle;
		}
		else if (at(OP_LPAREN))
			++paren;
		else if (at(OP_RPAREN))
			--paren;
		else if (at(OP_LSQUARE))
			++square;
		else if (at(OP_RSQUARE))
			--square;
		else if (at(OP_LBRACE))
			++brace;
		else if (at(OP_RBRACE))
			--brace;
		++pos_;
	}
	parameter.default_end = pos_;
}

size_t Parser::skip_template_declaration_body(size_t begin) const
{
	int paren = 0;
	int square = 0;
	for (size_t p = begin; p < tokens_.size(); ++p)
	{
		const Token& tok = tokens_[p];
		if (tok.kind != posttoken::TokenKind::Simple)
			continue;
		if (tok.type == OP_LPAREN)
			++paren;
		else if (tok.type == OP_RPAREN)
			--paren;
		else if (tok.type == OP_LSQUARE)
			++square;
		else if (tok.type == OP_RSQUARE)
			--square;
		else if (tok.type == OP_LBRACE && paren == 0 && square == 0)
		{
			size_t q = p + 1;
			int brace = 1;
			while (q < tokens_.size() && brace > 0)
			{
				if (tokens_[q].kind == posttoken::TokenKind::Simple &&
				    tokens_[q].type == OP_LBRACE)
					++brace;
				else if (tokens_[q].kind == posttoken::TokenKind::Simple &&
				         tokens_[q].type == OP_RBRACE)
					--brace;
				++q;
			}
			if (q < tokens_.size() &&
			    tokens_[q].kind == posttoken::TokenKind::Simple &&
			    tokens_[q].type == OP_SEMICOLON)
				++q;
			return q;
		}
		else if (tok.type == OP_SEMICOLON && paren == 0 && square == 0)
			return p + 1;
	}
	return tokens_.size();
}

void Parser::parse_template_declaration()
{
	expect(KW_TEMPLATE);
	if (!at(OP_LT))
	{
		--pos_;
		parse_explicit_template_instantiation(false);
		return;
	}
	vector<TemplateParameterInfo> parameters = parse_template_parameter_clause();
	size_t decl_begin = pos_;
	size_t decl_end = skip_template_declaration_body(decl_begin);
	register_template_declaration(parameters, decl_begin, decl_end);
	pos_ = decl_end;
}

void Parser::parse_explicit_template_instantiation(bool extern_declaration)
{
	if (extern_declaration)
		expect(KW_EXTERN);
	expect(KW_TEMPLATE);
	if (starts_class_key())
	{
		++pos_;
		TypePtr type;
		if (!try_parse_type_name(type))
			throw runtime_error("invalid explicit class instantiation");
		if (!extern_declaration)
		{
			complete_template_record(type);
			instantiate_member_function_templates(type, true);
		}
		expect(OP_SEMICOLON);
		return;
	}

	DeclSpecs specs = parse_decl_specifier_seq(false);
	TypePtr base = type_from_decl_specs(specs);
	Declarator declarator = parse_declarator(false);
	TypePtr declared_type = apply_declarator(declarator, base);
	if (declared_type->kind != pa11::TypeKind::Function)
		throw runtime_error("invalid explicit function instantiation");
	const QualifiedName& qname = declarator_name(declarator);
	if (qname.name.compare(0, 8, "operator") == 0)
	{
		bool overloaded_parameter = false;
		for (size_t i = 0; i < declared_type->parameters.size(); ++i)
		{
			TypePtr param =
				pa11::strip_cv(expression_object_type(declared_type->parameters[i]));
			if (param->kind == pa11::TypeKind::Record ||
			    param->kind == pa11::TypeKind::Enum)
				overloaded_parameter = true;
		}
		if (!overloaded_parameter)
			throw runtime_error("invalid overloaded operator instantiation");
	}
	vector<TemplateDeclaration*> declarations = find_function_templates(qname);
	TemplateDeclaration* selected = NULL;
	vector<TemplateArgument> selected_args;
	for (size_t i = 0; i < declarations.size(); ++i)
	{
		vector<TemplateArgument> full_args;
		if (!deduce_function_template_target_type(declarations[i],
		                                          declared_type,
		                                          qname.template_arguments,
		                                          full_args))
			continue;
		if (selected != NULL)
			throw runtime_error("ambiguous explicit function instantiation");
		selected = declarations[i];
		selected_args = full_args;
	}
	if (selected == NULL)
		throw runtime_error("function template not found");
	string key = template_argument_key(selected_args);
	if (extern_declaration)
	{
		Binding* binding = add_function_binding(selected->owner,
		                                        selected->name,
		                                        declared_type,
		                                        false);
		binding->language_linkage = current_language_linkage();
		binding->is_object_root = true;
		selected->function_specializations[key] = binding;
		function_template_placeholders_[binding] = selected;
	}
	else
	{
		selected->function_specializations.erase(key);
		Binding* binding = instantiate_function_template(selected,
		                                                 selected_args);
		binding->is_object_root = true;
	}
	expect(OP_SEMICOLON);
}

TemplateDeclaration* Parser::register_template_declaration(
	const vector<TemplateParameterInfo>& parameters,
	size_t decl_begin,
	size_t decl_end)
{
	unique_ptr<TemplateDeclaration> holder(new TemplateDeclaration());
	holder->owner = current_scope();
	holder->lexical_scope = current_scope();
	holder->parameters = parameters;
	holder->decl_begin = decl_begin;
	holder->decl_end = decl_end;
	holder->outer_type_substitutions = template_type_substitutions_;
	holder->outer_value_substitutions = template_value_substitutions_;
	TemplateDeclaration* declaration = holder.get();
	template_declarations_.push_back(std::move(holder));

	size_t save = pos_;
	pos_ = decl_begin;
	if (starts_class_key())
		register_class_template(declaration);
	else if (at(KW_USING))
		register_alias_template(declaration);
	else
		register_function_template(declaration);
	pos_ = save;
	return declaration;
}

void Parser::register_alias_template(TemplateDeclaration* declaration)
{
	declaration->kind = TemplateDeclarationKind::Alias;
	expect(KW_USING);
	if (!at_identifier())
		throw runtime_error("expected alias template name");
	declaration->name = consume_identifier();
	declaration->has_definition = true;
	expect(OP_ASS);
	declaration->owner = current_scope();
	TemplateDeclaration*& slot =
		alias_templates_[declaration->owner][declaration->name];
	if (slot == NULL)
		slot = declaration;
	else
	{
		merge_template_defaults(slot->parameters, declaration->parameters);
		slot->lexical_scope = declaration->lexical_scope;
		slot->decl_begin = declaration->decl_begin;
		slot->decl_end = declaration->decl_end;
		slot->has_definition = true;
	}
}

void Parser::register_class_template(TemplateDeclaration* declaration)
{
	declaration->kind = TemplateDeclarationKind::Class;
	map<string, TypePtr> parameter_types;
	map<string, TemplateArgument> parameter_values;
	for (size_t i = 0; i < declaration->parameters.size(); ++i)
		if (!declaration->parameters[i].name.empty() &&
		    declaration->parameters[i].kind == TemplateParameterKind::Type)
			parameter_types[declaration->parameters[i].name] =
				pa11::make_template_parameter_type(
					declaration->parameters[i].name);
		else if (!declaration->parameters[i].name.empty() &&
		         declaration->parameters[i].kind ==
		         TemplateParameterKind::TemplateTemplate)
			parameter_values[declaration->parameters[i].name] =
				TemplateArgument::template_arg(NULL);
	vector<map<string, TypePtr> > save_subst = template_type_substitutions_;
	vector<map<string, TemplateArgument> > save_value_subst =
		template_value_substitutions_;
	template_type_substitutions_.push_back(parameter_types);
	template_value_substitutions_.push_back(parameter_values);
	ETokenType key = current().type;
	declaration->tag = class_tag(key);
	++pos_;
	while (consume(KW_ALIGNAS))
		skip_balanced(OP_LPAREN, OP_RPAREN);
	Scope* owner = current_scope();
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
		owner = parse_nested_name_specifier(NULL);
	if (!at_identifier())
		throw runtime_error("expected class template name");
	declaration->owner = owner;
	declaration->name = consume_identifier();
	if (at(OP_LT))
	{
		vector<TemplateArgument> pattern;
		parse_template_argument_list(pattern);
		declaration->class_specialization = true;
		declaration->class_specialization_pattern = pattern;
		declaration->has_definition =
			has_token(tokens_, pos_, declaration->decl_end, OP_LBRACE);
		TemplateDeclaration* primary = find_class_template(owner,
		                                                   declaration->name);
		if (primary == NULL)
			throw runtime_error("class template specialization without primary");
		primary->class_specialization_declarations.push_back(declaration);
		template_type_substitutions_ = save_subst;
		template_value_substitutions_ = save_value_subst;
		if (declaration->has_definition)
			validate_class_template_definition(declaration);
		return;
	}
	declaration->has_definition =
		has_token(tokens_, pos_, declaration->decl_end, OP_LBRACE);

	TemplateDeclaration*& slot = class_templates_[owner][declaration->name];
	TypePtr owner_record = pa11::record_type_for_scope(owner);
	if (owner_record.get() != NULL)
	{
		map<const void*, TemplateDeclaration*>::iterator outer =
			record_template_declarations_.find(
				pa11::strip_cv(owner_record).get());
		if (outer != record_template_declarations_.end())
			member_class_templates_[make_pair(outer->second,
			                                  declaration->name)] =
				declaration;
	}
	if (slot == NULL)
	{
		slot = declaration;
	}
	else
	{
		merge_template_defaults(slot->parameters, declaration->parameters);
		if (declaration->has_definition)
		{
			slot->lexical_scope = declaration->lexical_scope;
			slot->decl_begin = declaration->decl_begin;
			slot->decl_end = declaration->decl_end;
			slot->tag = declaration->tag;
			slot->has_definition = true;
		}
	}
	template_type_substitutions_ = save_subst;
	template_value_substitutions_ = save_value_subst;
	if (declaration->has_definition)
	{
		validate_class_template_definition(declaration);
		if (slot != declaration &&
		    class_templates_with_dependent_base_.count(declaration) != 0)
			class_templates_with_dependent_base_.insert(slot);
	}
}

void Parser::register_explicit_function_template_specialization(
	TemplateDeclaration* declaration,
	const QualifiedName& qname,
	TypePtr declared_type,
	size_t save_pos,
	const vector<map<string, TypePtr> >& save_subst,
	const vector<map<string, TemplateArgument> >& save_value_subst)
{
	vector<TemplateDeclaration*> primaries = find_function_templates(qname);
	if (primaries.empty())
		throw runtime_error("function template specialization without primary");
	TemplateDeclaration* primary = primaries[0];
	vector<TemplateArgument> full_args;
	if (!deduce_function_template_target_type(primary,
	                                          declared_type,
	                                          qname.template_arguments,
	                                          full_args))
		throw runtime_error("function template specialization mismatch");
	string key = template_argument_key(full_args);
	template_type_substitutions_ = save_subst;
	template_value_substitutions_ = save_value_subst;
	pos_ = declaration->decl_begin;
	bool save_force = force_new_function_binding_;
	bool save_override = override_function_parameter_names_;
	vector<string> save_override_names = function_parameter_name_override_;
	map<Binding*, vector<string> >::iterator primary_names =
		function_parameter_names_.find(primary->placeholder);
	force_new_function_binding_ = true;
	if (primary_names != function_parameter_names_.end())
	{
		override_function_parameter_names_ = true;
		function_parameter_name_override_ = primary_names->second;
	}
	Node node;
	try
	{
		parse_simple_or_function_declaration(node, true);
	}
	catch (...)
	{
		force_new_function_binding_ = save_force;
		override_function_parameter_names_ = save_override;
		function_parameter_name_override_ = save_override_names;
		pos_ = save_pos;
		throw;
	}
	force_new_function_binding_ = save_force;
	override_function_parameter_names_ = save_override;
	function_parameter_name_override_ = save_override_names;
	if (node.line.compare(0, 19, "function-definition") == 0 &&
	    node.binding != NULL)
	{
		primary->function_specializations[key] = node.binding;
		add_child(root_, node);
	}
	else if (!node.children.empty() && node.children.back().binding != NULL)
	{
		primary->function_specializations[key] =
			node.children.back().binding;
		add_child(root_, node.children.back());
	}
	else
		throw runtime_error("function template specialization failed");
	pos_ = save_pos;
}

void Parser::register_function_template(TemplateDeclaration* declaration)
{
	if (register_constructor_template(declaration))
		return;
	declaration->kind = TemplateDeclarationKind::Function;
	map<string, TypePtr> parameter_types;
	map<string, TemplateArgument> parameter_values;
	collect_template_parameter_placeholders(declaration->parameters,
	                                        parameter_types, parameter_values);

	size_t save_pos = pos_;
	vector<map<string, TypePtr> > save_subst = template_type_substitutions_;
	vector<map<string, TemplateArgument> > save_value_subst = template_value_substitutions_;
	template_type_substitutions_.push_back(parameter_types);
	template_value_substitutions_.push_back(parameter_values);
	pos_ = declaration->decl_begin;
	try
	{
		DeclSpecs specs = parse_decl_specifier_seq(false);
		TypePtr base = type_from_decl_specs(specs);
		Declarator declarator = parse_declarator(false);
		TypePtr type = apply_declarator(declarator, base);
		if (type->kind != pa11::TypeKind::Function)
		{
			const QualifiedName& qname = declarator_name(declarator);
				Scope* target = qname.qualifier != NULL ? qname.qualifier : declaration->owner;
			declaration->owner = target;
			declaration->name = qname.name;
			if (qname.has_template_arguments)
			{
				declaration->class_specialization = true;
					declaration->class_specialization_pattern = qname.template_arguments;
			}
			template_type_substitutions_ = save_subst;
			template_value_substitutions_ = save_value_subst;
			pos_ = save_pos;
			if (register_static_member_variable_template(declaration))
				return;
			declaration->kind = TemplateDeclarationKind::Variable;
			variable_templates_[target][qname.name].push_back(declaration);
			return;
			}
			const QualifiedName& qname = declarator_name(declarator);
					Scope* friend_class_scope =
						specs.friend_decl && declaration->owner != NULL &&
						declaration->owner->kind == ScopeKind::Class ? declaration->owner : NULL;
					Scope* target = qname.qualifier != NULL ? qname.qualifier
						: (friend_class_scope != NULL
						   ? nearest_namespace_scope(friend_class_scope) : declaration->owner);
				if (declaration->parameters.empty())
				{
						register_explicit_function_template_specialization(
							declaration, qname, type, save_pos, save_subst, save_value_subst);
				return;
			}
			declaration->owner = target;
			declaration->friend_class_scope = friend_class_scope;
			declaration->hidden_friend =
				friend_class_scope != NULL && qname.qualifier == NULL;
			declaration->name = qname.name;
			if (target->kind == ScopeKind::Class && !specs.static_decl)
				type = make_member_function_type(target, type);
			declaration->generic_function_type = type;
				declaration->has_definition = has_token(tokens_, pos_,
				                                        declaration->decl_end, OP_LBRACE);
				Binding* placeholder =
					add_function_binding(target, qname.name, type, declaration->hidden_friend);
		placeholder->is_static_member =
			target->kind == ScopeKind::Class && specs.static_decl;
		declaration->placeholder = placeholder;
		const Suffix* primary_suffix = declarator_function_suffix(declarator);
		if (primary_suffix != NULL)
		{
			vector<string> names;
			for (size_t i = 0; i < primary_suffix->parameters.size(); ++i)
				if (primary_suffix->parameters[i].type.get() != NULL ||
				    !primary_suffix->parameters[i].name.empty())
					names.push_back(primary_suffix->parameters[i].name);
			function_parameter_names_[placeholder] = names;
		}
			function_template_placeholders_[placeholder] = declaration;
			if (friend_class_scope != NULL)
				add_friend_function(friend_class_scope, placeholder);
			vector<TemplateDeclaration*>& overloads = function_templates_[target][qname.name];
		if (find(overloads.begin(), overloads.end(), declaration) ==
		    overloads.end())
			overloads.push_back(declaration);
		TypePtr owner_record = pa11::record_type_for_scope(target);
		if (owner_record.get() != NULL)
		{
			map<const void*, TemplateDeclaration*>::iterator outer =
				record_template_declarations_.find(
					pa11::strip_cv(owner_record).get());
			if (outer != record_template_declarations_.end())
					member_function_templates_[make_pair(outer->second, qname.name)]
					.push_back(declaration);
		}
	}
	catch (const exception&)
	{
		template_type_substitutions_ = save_subst;
		template_value_substitutions_ = save_value_subst;
		pos_ = save_pos;
		if (register_constructor_template(declaration))
			return;
		if (register_static_member_variable_template(declaration))
			return;
		declaration->kind = TemplateDeclarationKind::Variable;
	}
	template_type_substitutions_ = save_subst;
	template_value_substitutions_ = save_value_subst;
	pos_ = save_pos;
}

bool Parser::register_constructor_template(TemplateDeclaration* declaration)
{
	map<string, TypePtr> parameter_types;
	map<string, TemplateArgument> parameter_values;
	for (size_t i = 0; i < declaration->parameters.size(); ++i)
		if (!declaration->parameters[i].name.empty() &&
		    declaration->parameters[i].kind == TemplateParameterKind::Type)
				parameter_types[declaration->parameters[i].name] =
					pa11::make_template_parameter_type(declaration->parameters[i].name);
		else if (!declaration->parameters[i].name.empty() &&
		         declaration->parameters[i].kind ==
		         TemplateParameterKind::TemplateTemplate)
			parameter_values[declaration->parameters[i].name] =
				TemplateArgument::template_arg(NULL);

	size_t save_pos = pos_;
	vector<Scope*> save_scopes = scopes_;
	vector<map<string, TypePtr> > save_subst = template_type_substitutions_;
	vector<map<string, TemplateArgument> > save_value_subst = template_value_substitutions_;
	template_type_substitutions_.push_back(parameter_types);
	template_value_substitutions_.push_back(parameter_values);
	pos_ = declaration->decl_begin;
		bool matched_constructor = false;
		try
		{
			bool explicit_ctor = consume(KW_EXPLICIT);
			bool constexpr_ctor = consume(KW_CONSTEXPR);
			if (!explicit_ctor)
				explicit_ctor = consume(KW_EXPLICIT);
			QualifiedName qname = parse_id_expression_name();
			Scope* class_scope = qname.qualifier;
			if (class_scope == NULL &&
			    current_scope() != NULL &&
			    current_scope()->kind == ScopeKind::Class &&
			    qname.name == current_scope()->name)
				class_scope = current_scope();
			if (class_scope == NULL ||
			    class_scope->kind != ScopeKind::Class ||
			    qname.name != class_scope->name ||
			    !at(OP_LPAREN))
				throw runtime_error("not a constructor template definition");
			matched_constructor = true;
			TypePtr class_type = pa11::record_type_for_scope(class_scope);
			if (class_type.get() == NULL)
				throw runtime_error("constructor without class type");
			expect(OP_LPAREN);
			vector<ParameterInfo> parameters;
			bool variadic = false;
			scopes_.push_back(class_scope);
			parse_parameter_clause(parameters, variadic);
			scopes_.pop_back();
			expect(OP_RPAREN);
			Suffix suffix(SuffixKind::Function);
			parse_function_suffix_tail(suffix);
			if (!at(OP_LBRACE) && !at(OP_COLON) && !at(OP_ASS))
				throw runtime_error("constructor template missing body");

			vector<TypePtr> fn_params;
			fn_params.push_back(pa11::make_pointer(class_type));
				for (size_t i = 0; i < parameters.size(); ++i)
					fn_params.push_back(parameters[i].type);
				TypePtr fn_type =
					pa11::make_function(pa11::make_fundamental(FT_VOID), fn_params, variadic);
			Binding* existing =
				find_matching_function(class_scope, qname.name, fn_type);
		if (existing != NULL && existing->unwind_no != suffix.noexcept_decl)
			throw runtime_error("exception specification mismatch");
		Binding* placeholder = existing != NULL
				? existing
					: add_function_binding(class_scope, qname.name, fn_type, false);
			placeholder->unwind_no = suffix.noexcept_decl;
			placeholder->is_explicit = explicit_ctor;
				placeholder->is_constexpr = placeholder->is_constexpr || constexpr_ctor;
			declaration->kind = TemplateDeclarationKind::Function;
			declaration->constructor_template = true;
			declaration->owner = class_scope;
			declaration->name = qname.name;
		declaration->generic_function_type = fn_type;
		declaration->placeholder = placeholder;
		function_template_placeholders_[placeholder] = declaration;
			declaration->has_definition = has_token(tokens_, pos_, declaration->decl_end, OP_LBRACE);
		TemplateDeclaration* outer_template = NULL;
				for (Scope* owner_scope = class_scope;
				     owner_scope != NULL && outer_template == NULL;
				     owner_scope = owner_scope->parent)
		{
			TypePtr owner_record = pa11::record_type_for_scope(owner_scope);
			if (owner_record.get() == NULL)
				continue;
			map<const void*, TemplateDeclaration*>::iterator outer =
				record_template_declarations_.find(
					pa11::strip_cv(owner_record).get());
			if (outer != record_template_declarations_.end())
				outer_template = outer->second;
		}
		if (outer_template != NULL)
				member_function_templates_[make_pair(outer_template, qname.name)]
				.push_back(declaration);
		template_type_substitutions_ = save_subst;
		template_value_substitutions_ = save_value_subst;
		scopes_ = save_scopes;
		pos_ = save_pos;
		return true;
	}
	catch (const exception&)
	{
		template_type_substitutions_ = save_subst;
		template_value_substitutions_ = save_value_subst;
		scopes_ = save_scopes;
		pos_ = save_pos;
		if (matched_constructor)
			throw;
		return false;
	}
}

bool Parser::register_static_member_variable_template(
	TemplateDeclaration* declaration)
{
	map<string, TypePtr> parameter_types;
	map<string, TemplateArgument> parameter_values;
	for (size_t i = 0; i < declaration->parameters.size(); ++i)
		if (!declaration->parameters[i].name.empty() &&
		    declaration->parameters[i].kind == TemplateParameterKind::Type)
			parameter_types[declaration->parameters[i].name] =
				pa11::make_template_parameter_type(
					declaration->parameters[i].name);
		else if (!declaration->parameters[i].name.empty() &&
		         declaration->parameters[i].kind == TemplateParameterKind::NonType)
			parameter_values[declaration->parameters[i].name] =
				TemplateArgument::dependent_value_arg(
					declaration->parameters[i].type.get() != NULL
					? declaration->parameters[i].type
					: pa11::make_fundamental(FT_INT));

	size_t save_pos = pos_;
	vector<Scope*> save_scopes = scopes_;
	vector<map<string, TypePtr> > save_subst = template_type_substitutions_;
	vector<map<string, TemplateArgument> > save_value_subst =
		template_value_substitutions_;
	template_type_substitutions_.push_back(parameter_types);
	template_value_substitutions_.push_back(parameter_values);
	pos_ = declaration->decl_begin;
	bool matched = false;
	try
	{
		DeclSpecs specs = parse_decl_specifier_seq(false);
		TypePtr base = type_from_decl_specs(specs);
		Declarator declarator = parse_declarator(false);
		TypePtr type = apply_declarator(declarator, base);
		(void)type;
		const QualifiedName& qname = declarator_name(declarator);
		if (qname.qualifier == NULL ||
		    qname.qualifier->kind != ScopeKind::Class)
			throw runtime_error("not a static member template definition");
		matched = true;
		declaration->kind = TemplateDeclarationKind::Variable;
		declaration->owner = qname.qualifier;
		declaration->name = qname.name;
		TypePtr owner_record = pa11::record_type_for_scope(qname.qualifier);
		TemplateDeclaration* outer_template = NULL;
		for (Scope* owner_scope = qname.qualifier;
		     owner_scope != NULL && outer_template == NULL;
		     owner_scope = owner_scope->parent)
		{
			owner_record = pa11::record_type_for_scope(owner_scope);
			if (owner_record.get() == NULL)
				continue;
			map<const void*, TemplateDeclaration*>::iterator outer =
				record_template_declarations_.find(
					pa11::strip_cv(owner_record).get());
			if (outer != record_template_declarations_.end())
				outer_template = outer->second;
		}
		if (outer_template != NULL)
			member_variable_templates_[make_pair(outer_template,
			                                    qname.name)]
				.push_back(declaration);
		template_type_substitutions_ = save_subst;
		template_value_substitutions_ = save_value_subst;
		scopes_ = save_scopes;
		pos_ = save_pos;
		return true;
	}
	catch (const exception&)
	{
		template_type_substitutions_ = save_subst;
		template_value_substitutions_ = save_value_subst;
		scopes_ = save_scopes;
		pos_ = save_pos;
		if (matched)
			throw;
		size_t fallback_pos = pos_;
		vector<map<string, TypePtr> > fallback_subst =
			template_type_substitutions_;
		vector<map<string, TemplateArgument> > fallback_value_subst =
			template_value_substitutions_;
		try
		{
			template_type_substitutions_.push_back(parameter_types);
			template_value_substitutions_.push_back(parameter_values);
			pos_ = declaration->decl_begin;
			DeclSpecs specs = parse_decl_specifier_seq(false);
			(void)type_from_decl_specs(specs);
			vector<PtrOp> ignored_ptrs;
			parse_ptr_prefix(ignored_ptrs);
			if (!at_identifier() || !lookahead(OP_LT, 1))
				throw runtime_error("not a dependent static member template definition");
			string root = consume_identifier();
			TemplateDeclaration* outer_template = find_class_template(NULL, root);
			if (outer_template == NULL)
				throw runtime_error("static member template owner not found");
			vector<TemplateArgument> ignored_args;
			parse_template_argument_list(ignored_args);
			expect(OP_COLON2);
			if (!at_identifier())
				throw runtime_error("static member template name missing");
			string member_name = consume_identifier();
			declaration->kind = TemplateDeclarationKind::Variable;
			declaration->owner = outer_template->owner;
			declaration->name = member_name;
			member_variable_templates_[make_pair(outer_template,
			                                    member_name)]
				.push_back(declaration);
			template_type_substitutions_ = fallback_subst;
			template_value_substitutions_ = fallback_value_subst;
			pos_ = fallback_pos;
			return true;
		}
		catch (const exception&)
		{
			template_type_substitutions_ = fallback_subst;
			template_value_substitutions_ = fallback_value_subst;
			pos_ = fallback_pos;
		}
		return false;
	}
}

bool Parser::find_template_type_substitution(const string& name,
                                             TypePtr& out) const
{
	for (size_t i = template_type_substitutions_.size(); i > 0; --i)
	{
		map<string, TypePtr>::const_iterator found =
			template_type_substitutions_[i - 1].find(name);
		if (found != template_type_substitutions_[i - 1].end())
		{
			out = found->second;
			return true;
		}
	}
	return false;
}

bool Parser::find_template_value_substitution(const string& name,
                                              TemplateArgument& out) const
{
	for (size_t i = template_value_substitutions_.size(); i > 0; --i)
	{
		map<string, TemplateArgument>::const_iterator found =
			template_value_substitutions_[i - 1].find(name);
		if (found != template_value_substitutions_[i - 1].end())
		{
			out = found->second;
			return true;
		}
	}
	return false;
}

bool Parser::find_function_parameter_pack_substitution(
	const string& name,
	vector<Binding*>& out) const
{
	for (size_t i = function_parameter_pack_substitutions_.size(); i > 0; --i)
	{
		map<string, vector<Binding*> >::const_iterator found =
			function_parameter_pack_substitutions_[i - 1].find(name);
		if (found != function_parameter_pack_substitutions_[i - 1].end())
		{
			out = found->second;
			return true;
		}
	}
	return false;
}

bool Parser::try_parse_template_template_argument(TemplateArgument& out)
{
	size_t save = pos_;
	Scope* qualifier = NULL;
	if (at(OP_COLON2) ||
	    (at_identifier() && lookahead(OP_COLON2, 1)))
	{
		try
		{
			qualifier = parse_nested_name_specifier(NULL);
		}
		catch (const exception&)
		{
			pos_ = save;
			return false;
		}
		consume(KW_TEMPLATE);
	}
	if (!at_identifier())
	{
		pos_ = save;
		return false;
	}
	string name = consume_identifier();
	if (at(OP_LT) || (!at(OP_COMMA) && !at(OP_GT) && !at(OP_DOTS)))
	{
		pos_ = save;
		return false;
	}
	if (qualifier == NULL)
	{
		TemplateArgument subst;
		if (find_template_value_substitution(name, subst) &&
		    subst.kind == TemplateArgumentKind::Template)
		{
			out = subst;
			return true;
		}
	}
	TemplateDeclaration* declaration = find_class_template(qualifier, name);
	if (declaration == NULL)
	{
		pos_ = save;
		return false;
	}
	out = TemplateArgument::template_arg(declaration);
	return true;
}

TemplateArgument Parser::parse_non_type_template_argument_expression()
{
	++template_argument_expression_depth_;
	Expr expr;
	try
	{
		expr = parse_assignment_expression();
	}
	catch (...)
	{
		--template_argument_expression_depth_;
		throw;
	}
	--template_argument_expression_depth_;
	if (expr.valid && !expr.has_constant_value)
	{
		ConstexprValue value;
		if (try_evaluate_constexpr_expr(expr.node, value) &&
		    !value.is_object)
		{
			expr.has_constant_value = true;
			expr.constant_value = value.int_value;
			expr.node.has_constant_value = true;
			expr.node.constant_value = value.int_value;
		}
	}
	if (expr.valid && !expr.has_constant_value)
	{
		try
		{
			Conversion conv =
				convert_to(expr, pa11::make_fundamental(FT_BOOL));
			if (conv.viable && !conv.expr.has_constant_value)
			{
				ConstexprValue value;
				if (try_evaluate_constexpr_expr(conv.expr.node, value))
					apply_constexpr_value(conv.expr, value);
			}
			if (conv.viable && conv.expr.has_constant_value)
				expr = conv.expr;
		}
		catch (const runtime_error&)
		{
		}
	}
	if (!expr.has_constant_value)
	{
		if (!active_class_instantiations_.empty() ||
		    !template_type_substitutions_.empty() ||
		    !template_value_substitutions_.empty())
			return TemplateArgument::dependent_value_arg(
				expression_object_type(expr.type));
		throw runtime_error("invalid non-type template argument");
	}
	return TemplateArgument::value_arg(expression_object_type(expr.type),
	                                   expr.constant_value);
}

bool Parser::parse_template_argument_list(vector<TemplateArgument>& arguments)
{
	if (!consume(OP_LT))
		return false;
	if (consume(OP_GT))
		return true;
	for (;;)
	{
		size_t save = pos_;
		try
		{
			TypePtr type = parse_type_id();
			bool pack_expansion = consume(OP_DOTS);
			if (at(OP_COMMA) || at(OP_GT))
			{
				TemplateArgument arg = TemplateArgument::type_arg(type);
				arg.pack_expansion = pack_expansion;
				arguments.push_back(arg);
			}
			else
				throw runtime_error("template argument is not a type");
		}
		catch (const exception&)
		{
			pos_ = save;
			TemplateArgument template_argument;
			if (try_parse_template_template_argument(template_argument))
			{
				template_argument.pack_expansion = consume(OP_DOTS);
				arguments.push_back(template_argument);
				if (!consume(OP_COMMA))
					break;
				continue;
			}
			if (at_identifier() && lookahead(OP_DOTS, 1))
			{
				string pack_name = consume_identifier();
				expect(OP_DOTS);
				TypePtr type_subst;
				if (find_template_type_substitution(pack_name, type_subst))
				{
					TemplateArgument arg =
						TemplateArgument::type_arg(type_subst);
					arg.pack_expansion = true;
					arguments.push_back(arg);
					if (!at(OP_COMMA) && !at(OP_GT))
						throw runtime_error("template argument is not a type");
					if (!consume(OP_COMMA))
						break;
					continue;
				}
				TemplateArgument subst;
				if (!find_template_value_substitution(pack_name, subst) ||
				    subst.kind != TemplateArgumentKind::Pack)
					throw runtime_error("invalid template argument pack");
				TemplateArgument arg = subst;
				arg.pack_expansion = true;
				arguments.push_back(arg);
				if (!at(OP_COMMA) && !at(OP_GT))
					throw runtime_error("template argument is not a value");
				if (!consume(OP_COMMA))
					break;
				continue;
			}
			if (at_identifier())
			{
				string value_name = current().source;
				TemplateArgument subst;
				if (find_template_value_substitution(value_name, subst) &&
				    subst.kind == TemplateArgumentKind::Value)
				{
					++pos_;
					TemplateArgument arg = subst;
					arg.pack_expansion = consume(OP_DOTS);
					if (!at(OP_COMMA) && !at(OP_GT))
						throw runtime_error("template argument is not a value");
					arguments.push_back(arg);
					if (!consume(OP_COMMA))
						break;
					continue;
				}
			}
			TemplateArgument arg =
				parse_non_type_template_argument_expression();
			arg.pack_expansion = consume(OP_DOTS);
			arguments.push_back(arg);
		}
		if (!consume(OP_COMMA))
			break;
	}
	expect(OP_GT);
	return true;
}

}  // namespace internal
}  // namespace pa12
