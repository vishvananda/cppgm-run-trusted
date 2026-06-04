#include "pa12_internal.h"

#include <algorithm>
#include <sstream>
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
		if (!source[i].name.empty())
			target[i].name = source[i].name;
		if (source[i].has_default)
		{
			target[i].has_default = true;
			target[i].default_begin = source[i].default_begin;
			target[i].default_end = source[i].default_end;
		}
	}
}

bool type_contains_template_parameter(
	TypePtr type,
	const map<const void*, vector<TypePtr> >& record_template_arguments)
{
	if (type.get() == NULL)
		return false;
	type = pa11::strip_cv(type);
	if (type->kind == pa11::TypeKind::TemplateParameter)
		return true;
	if (type->kind == pa11::TypeKind::Pointer ||
	    type->kind == pa11::TypeKind::LValueReference ||
	    type->kind == pa11::TypeKind::RValueReference ||
	    type->kind == pa11::TypeKind::Array)
		return type_contains_template_parameter(type->base,
		                                        record_template_arguments);
	if (type->kind == pa11::TypeKind::Function)
	{
		if (type_contains_template_parameter(type->base,
		                                     record_template_arguments))
			return true;
		for (size_t i = 0; i < type->parameters.size(); ++i)
			if (type_contains_template_parameter(
				    type->parameters[i],
				    record_template_arguments))
				return true;
	}
	if (type->kind == pa11::TypeKind::MemberPointer)
		return type_contains_template_parameter(
			       type->member_class,
			       record_template_arguments) ||
		       type_contains_template_parameter(type->base,
		                                        record_template_arguments);
	if (type->kind == pa11::TypeKind::Record)
	{
		map<const void*, vector<TypePtr> >::const_iterator found =
			record_template_arguments.find(type.get());
		if (found != record_template_arguments.end())
			for (size_t i = 0; i < found->second.size(); ++i)
				if (type_contains_template_parameter(
					    found->second[i],
					    record_template_arguments))
					return true;
	}
	return false;
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

string template_type_spelling(TypePtr type)
{
	if (type.get() == NULL)
		return "";
	switch (type->kind)
	{
	case pa11::TypeKind::Fundamental:
		return pa11::describe_type(type);
	case pa11::TypeKind::Cv:
		if (type->cv == (pa11::CV_CONST | pa11::CV_VOLATILE))
			return "const volatile " + template_type_spelling(type->base);
		if (type->cv == pa11::CV_CONST)
			return "const " + template_type_spelling(type->base);
		return "volatile " + template_type_spelling(type->base);
	case pa11::TypeKind::Pointer:
		return "pointer to " + template_type_spelling(type->base);
	case pa11::TypeKind::LValueReference:
		return "lvalue-reference to " + template_type_spelling(type->base);
	case pa11::TypeKind::RValueReference:
		return "rvalue-reference to " + template_type_spelling(type->base);
	case pa11::TypeKind::Array:
		if (type->unknown_bound)
			return "array of unknown bound of " +
			       template_type_spelling(type->base);
		return "array of " + to_string(type->bound) + " " +
		       template_type_spelling(type->base);
	case pa11::TypeKind::Function:
	{
		ostringstream out;
		out << "function of (";
		for (size_t i = 0; i < type->parameters.size(); ++i)
		{
			if (i != 0)
				out << ", ";
			out << template_type_spelling(type->parameters[i]);
		}
		if (type->variadic)
			out << (type->parameters.empty() ? "..." : ", ...");
		out << ")";
		if (type->cv == pa11::CV_CONST)
			out << " const";
		else if (type->cv == pa11::CV_VOLATILE)
			out << " volatile";
		else if (type->cv == (pa11::CV_CONST | pa11::CV_VOLATILE))
			out << " const volatile";
		out << " returning " << template_type_spelling(type->base);
		return out.str();
	}
	case pa11::TypeKind::MemberPointer:
		return "member-pointer of " +
		       template_type_spelling(type->member_class) + " to " +
		       template_type_spelling(type->base);
	case pa11::TypeKind::Record:
	case pa11::TypeKind::Enum:
		return type->name;
	case pa11::TypeKind::TemplateParameter:
		return "typename " + type->name;
	case pa11::TypeKind::TemplateTemplateParameter:
		return "template-parameter " + type->name;
	}
	throw logic_error("unknown type kind");
}

string template_type_key(TypePtr type)
{
	if (type.get() == NULL)
		return "";
	switch (type->kind)
	{
	case pa11::TypeKind::Cv:
		return "cv(" + to_string(type->cv) + "," +
		       template_type_key(type->base) + ")";
	case pa11::TypeKind::Pointer:
		return "ptr(" + template_type_key(type->base) + ")";
	case pa11::TypeKind::LValueReference:
		return "lref(" + template_type_key(type->base) + ")";
	case pa11::TypeKind::RValueReference:
		return "rref(" + template_type_key(type->base) + ")";
	case pa11::TypeKind::Array:
		return string("array(") +
		       (type->unknown_bound ? "?" : to_string(type->bound)) + "," +
		       template_type_key(type->base) + ")";
	case pa11::TypeKind::Function:
	{
		ostringstream out;
		out << "fn(";
		for (size_t i = 0; i < type->parameters.size(); ++i)
		{
			if (i != 0)
				out << ",";
			out << template_type_key(type->parameters[i]);
		}
		out << ")->" << template_type_key(type->base);
		return out.str();
	}
	case pa11::TypeKind::MemberPointer:
		return "memptr(" + template_type_key(type->member_class) + "," +
		       template_type_key(type->base) + ")";
	case pa11::TypeKind::Record:
	case pa11::TypeKind::Enum:
	{
		ostringstream out;
		out << template_type_spelling(type) << "@" << type.get();
		return out.str();
	}
	default:
		return template_type_spelling(type);
	}
}

string template_argument_spelling(const vector<TypePtr>& arguments)
{
	ostringstream out;
	for (size_t i = 0; i < arguments.size(); ++i)
	{
		if (i != 0)
			out << ",";
		out << template_type_spelling(arguments[i]);
	}
	return out.str();
}

}  // namespace

vector<TemplateParameterInfo> Parser::parse_template_parameter_clause()
{
	vector<TemplateParameterInfo> parameters;
	expect(OP_LT);
	if (consume(OP_GT))
		return parameters;
	for (;;)
	{
		parameters.push_back(parse_template_parameter_info());
		if (!consume(OP_COMMA))
			break;
	}
	expect(OP_GT);
	return parameters;
}

TemplateParameterInfo Parser::parse_template_parameter_info()
{
	TemplateParameterInfo parameter;
	if (consume(KW_TEMPLATE))
	{
		skip_template_parameter_clause();
		if (!consume(KW_CLASS) && !consume(KW_TYPENAME))
			throw runtime_error("unsupported template template parameter");
		if (at_identifier())
			parameter.name = consume_identifier();
		if (consume(OP_ASS))
			skip_template_parameter_default(parameter);
		return parameter;
	}
	if (consume(KW_CLASS) || consume(KW_TYPENAME))
	{
		consume(OP_DOTS);
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

	while (!at_eof() && !at(OP_COMMA) && !at(OP_GT))
	{
		if (consume(OP_ASS))
		{
			skip_template_parameter_default(parameter);
			break;
		}
		++pos_;
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
		if (!starts_class_key())
			throw runtime_error("unsupported explicit template instantiation");
		++pos_;
		TypePtr type;
		if (!try_parse_type_name(type))
			throw runtime_error("invalid explicit class instantiation");
		complete_template_record(type);
		instantiate_member_function_templates(type);
		TypePtr bare = pa11::strip_cv(type);
		if (bare->kind == pa11::TypeKind::Record && bare->scope != NULL)
			for (size_t i = 0; i < bare->scope->binding_order.size(); ++i)
			{
				Binding* binding = bare->scope->binding_order[i];
				if (binding->kind != BindingKind::Function ||
				    binding->is_generated_default_constructor ||
				    binding->is_generated_aggregate_constructor ||
				    binding->is_generated_copy_move_constructor ||
				    binding->is_generated_copy_move_assignment ||
				    binding->is_generated_default_destructor ||
				    binding->name == bare->scope->name ||
				    (!binding->name.empty() && binding->name[0] == '~'))
					continue;
				binding->is_object_root = true;
			}
		expect(OP_SEMICOLON);
		return;
	}
	vector<TemplateParameterInfo> parameters = parse_template_parameter_clause();
	size_t decl_begin = pos_;
	size_t decl_end = skip_template_declaration_body(decl_begin);
	register_template_declaration(parameters, decl_begin, decl_end);
	pos_ = decl_end;
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
	TemplateDeclaration* declaration = holder.get();
	template_declarations_.push_back(std::move(holder));

	size_t save = pos_;
	pos_ = decl_begin;
	if (starts_class_key())
		register_class_template(declaration);
	else
		register_function_template(declaration);
	pos_ = save;
	return declaration;
}

void Parser::register_class_template(TemplateDeclaration* declaration)
{
	declaration->kind = TemplateDeclarationKind::Class;
	map<string, TypePtr> parameter_types;
	for (size_t i = 0; i < declaration->parameters.size(); ++i)
		if (!declaration->parameters[i].name.empty())
			parameter_types[declaration->parameters[i].name] =
				pa11::make_template_parameter_type(
					declaration->parameters[i].name);
	vector<map<string, TypePtr> > save_subst = template_type_substitutions_;
	template_type_substitutions_.push_back(parameter_types);
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
		declaration->kind = TemplateDeclarationKind::Variable;
		template_type_substitutions_ = save_subst;
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
	if (declaration->has_definition)
	{
		validate_class_template_definition(declaration);
		if (slot != declaration &&
		    class_templates_with_dependent_base_.count(declaration) != 0)
			class_templates_with_dependent_base_.insert(slot);
	}
}

void Parser::register_function_template(TemplateDeclaration* declaration)
{
	if (register_constructor_template(declaration))
		return;
	declaration->kind = TemplateDeclarationKind::Function;
	map<string, TypePtr> parameter_types;
	for (size_t i = 0; i < declaration->parameters.size(); ++i)
		if (!declaration->parameters[i].name.empty())
			parameter_types[declaration->parameters[i].name] =
				pa11::make_template_parameter_type(
					declaration->parameters[i].name);

	size_t save_pos = pos_;
	vector<map<string, TypePtr> > save_subst = template_type_substitutions_;
	template_type_substitutions_.push_back(parameter_types);
	pos_ = declaration->decl_begin;
	try
	{
		DeclSpecs specs = parse_decl_specifier_seq(false);
		TypePtr base = type_from_decl_specs(specs);
		Declarator declarator = parse_declarator(false);
		TypePtr type = apply_declarator(declarator, base);
		if (type->kind != pa11::TypeKind::Function)
		{
			template_type_substitutions_ = save_subst;
			pos_ = save_pos;
			if (register_static_member_variable_template(declaration))
				return;
			declaration->kind = TemplateDeclarationKind::Variable;
			return;
		}
		const QualifiedName& qname = declarator_name(declarator);
		Scope* target = qname.qualifier != NULL ? qname.qualifier :
			declaration->owner;
		declaration->owner = target;
		declaration->name = qname.name;
		declaration->generic_function_type = type;
		Binding* placeholder =
			add_function_binding(target, qname.name, type, false);
		declaration->placeholder = placeholder;
		function_template_placeholders_[placeholder] = declaration;
		vector<TemplateDeclaration*>& overloads =
			function_templates_[target][qname.name];
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
				member_function_templates_[make_pair(outer->second,
				                                    qname.name)]
					.push_back(declaration);
		}
	}
	catch (const exception&)
	{
		template_type_substitutions_ = save_subst;
		pos_ = save_pos;
		if (register_constructor_template(declaration))
			return;
		if (register_static_member_variable_template(declaration))
			return;
		declaration->kind = TemplateDeclarationKind::Variable;
	}
	template_type_substitutions_ = save_subst;
	pos_ = save_pos;
}

bool Parser::register_constructor_template(TemplateDeclaration* declaration)
{
	map<string, TypePtr> parameter_types;
	for (size_t i = 0; i < declaration->parameters.size(); ++i)
		if (!declaration->parameters[i].name.empty())
			parameter_types[declaration->parameters[i].name] =
				pa11::make_template_parameter_type(
					declaration->parameters[i].name);

	size_t save_pos = pos_;
	vector<Scope*> save_scopes = scopes_;
	vector<map<string, TypePtr> > save_subst = template_type_substitutions_;
	template_type_substitutions_.push_back(parameter_types);
	pos_ = declaration->decl_begin;
	bool matched_constructor = false;
	try
	{
		QualifiedName qname = parse_id_expression_name();
		if (qname.qualifier == NULL ||
		    qname.qualifier->kind != ScopeKind::Class ||
		    qname.name != qname.qualifier->name)
			throw runtime_error("not a constructor template definition");
		matched_constructor = true;
		TypePtr class_type = pa11::record_type_for_scope(qname.qualifier);
		if (class_type.get() == NULL)
			throw runtime_error("constructor without class type");
		expect(OP_LPAREN);
		vector<ParameterInfo> parameters;
		bool variadic = false;
		scopes_.push_back(qname.qualifier);
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
		TypePtr fn_type = pa11::make_function(pa11::make_fundamental(FT_VOID),
		                                      fn_params,
		                                      variadic);
		Binding* existing =
			find_matching_function(qname.qualifier, qname.name, fn_type);
		if (existing != NULL && existing->unwind_no != suffix.noexcept_decl)
			throw runtime_error("exception specification mismatch");
		Binding* placeholder = existing != NULL
			? existing
			: add_function_binding(qname.qualifier,
			                       qname.name,
			                       fn_type,
			                       false);
		placeholder->unwind_no = suffix.noexcept_decl;
		declaration->kind = TemplateDeclarationKind::Function;
		declaration->constructor_template = true;
		declaration->owner = qname.qualifier;
		declaration->name = qname.name;
		declaration->generic_function_type = fn_type;
		declaration->placeholder = placeholder;
		declaration->has_definition =
			has_token(tokens_, pos_, declaration->decl_end, OP_LBRACE);
		TemplateDeclaration* outer_template = NULL;
		for (Scope* owner_scope = qname.qualifier;
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
			member_function_templates_[make_pair(outer_template,
			                                    qname.name)]
				.push_back(declaration);
		template_type_substitutions_ = save_subst;
		scopes_ = save_scopes;
		pos_ = save_pos;
		return true;
	}
	catch (const exception&)
	{
		template_type_substitutions_ = save_subst;
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
	for (size_t i = 0; i < declaration->parameters.size(); ++i)
		if (!declaration->parameters[i].name.empty())
			parameter_types[declaration->parameters[i].name] =
				pa11::make_template_parameter_type(
					declaration->parameters[i].name);

	size_t save_pos = pos_;
	vector<Scope*> save_scopes = scopes_;
	vector<map<string, TypePtr> > save_subst = template_type_substitutions_;
	template_type_substitutions_.push_back(parameter_types);
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
		scopes_ = save_scopes;
		pos_ = save_pos;
		return true;
	}
	catch (const exception&)
	{
		template_type_substitutions_ = save_subst;
		scopes_ = save_scopes;
		pos_ = save_pos;
		if (matched)
			throw;
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

bool Parser::parse_template_argument_list(vector<TypePtr>& arguments)
{
	if (!consume(OP_LT))
		return false;
	if (consume(OP_GT))
		return true;
	for (;;)
	{
		arguments.push_back(parse_type_id());
		if (!consume(OP_COMMA))
			break;
	}
	expect(OP_GT);
	return true;
}

vector<TypePtr> Parser::complete_template_arguments(
	TemplateDeclaration* declaration,
	const vector<TypePtr>& explicit_arguments)
{
	if (explicit_arguments.size() > declaration->parameters.size())
		throw runtime_error("too many template arguments");
	vector<TypePtr> out = explicit_arguments;
	while (out.size() < declaration->parameters.size())
	{
		const TemplateParameterInfo& parameter =
			declaration->parameters[out.size()];
		if (!parameter.has_default)
			throw runtime_error("missing template argument");
		size_t save_pos = pos_;
		vector<map<string, TypePtr> > save_subst =
			template_type_substitutions_;
		map<string, TypePtr> subst;
		for (size_t i = 0; i < out.size(); ++i)
			if (!declaration->parameters[i].name.empty())
				subst[declaration->parameters[i].name] = out[i];
		template_type_substitutions_.push_back(subst);
		pos_ = parameter.default_begin;
		TypePtr type = parse_type_id();
		if (pos_ != parameter.default_end)
			throw runtime_error("invalid default template argument");
		out.push_back(type);
		template_type_substitutions_ = save_subst;
		pos_ = save_pos;
	}
	return out;
}

string Parser::template_argument_key(const vector<TypePtr>& arguments) const
{
	ostringstream out;
	for (size_t i = 0; i < arguments.size(); ++i)
	{
		if (i != 0)
			out << ",";
		out << template_type_key(arguments[i]);
	}
	return out.str();
}

string Parser::template_specialization_name(
	TemplateDeclaration* declaration,
	const vector<TypePtr>& arguments) const
{
	return declaration->name + "<" + template_argument_spelling(arguments) + ">";
}

TemplateDeclaration* Parser::find_class_template(Scope* scope,
                                                 const string& name)
{
	if (scope != NULL)
	{
		map<Scope*, map<string, TemplateDeclaration*> >::iterator sit =
			class_templates_.find(scope);
		if (sit != class_templates_.end())
		{
			map<string, TemplateDeclaration*>::iterator it =
				sit->second.find(name);
			if (it != sit->second.end())
				return it->second;
		}
		for (size_t i = 0; i < scope->using_directives.size(); ++i)
		{
			TemplateDeclaration* found =
				find_class_template(scope->using_directives[i], name);
			if (found != NULL)
				return found;
		}
		return NULL;
	}
	for (Scope* cur = current_scope(); cur != NULL; cur = cur->parent)
	{
		TemplateDeclaration* found = find_class_template(cur, name);
		if (found != NULL)
			return found;
	}
	return NULL;
}

TypePtr Parser::instantiate_class_template(
	TemplateDeclaration* declaration,
	const vector<TypePtr>& arguments)
{
	vector<TypePtr> full_args =
		complete_template_arguments(declaration, arguments);
	bool dependent = false;
	for (size_t i = 0; i < full_args.size(); ++i)
		if (type_contains_template_parameter(full_args[i],
		                                     record_template_arguments_))
			dependent = true;
	string key = template_argument_key(full_args);
	map<string, TypePtr>::iterator existing =
		declaration->class_specializations.find(key);
	if (existing != declaration->class_specializations.end())
	{
		if (!dependent)
			complete_template_record(existing->second);
		return existing->second;
	}

	string special_name = template_specialization_name(declaration, full_args);
	Scope* class_scope =
		pa11::create_child_scope(declaration->owner,
		                         ScopeKind::Class,
		                         declaration->name);
	TypePtr type =
		pa11::make_record_type(scoped_type_display_name(declaration->owner,
		                                                special_name),
		                       declaration->tag.empty() ? "struct" :
		                       declaration->tag,
		                       false,
		                       class_scope);
	type->is_template_specialization = true;
	Binding* binding =
		pa11::add_binding(declaration->owner,
		                  BindingKind::Type,
		                  special_name,
		                  type);
	binding->target_scope = class_scope;
	Binding* injected =
		pa11::add_binding(class_scope,
		                  BindingKind::Type,
		                  declaration->name,
		                  type);
	injected->target_scope = class_scope;
	declaration->class_specializations[key] = type;
	record_template_declarations_[type.get()] = declaration;
	record_template_arguments_[type.get()] = full_args;
	if (!dependent)
		complete_template_record(type);
	return type;
}

void Parser::complete_template_record(TypePtr type)
{
	TypePtr bare = pa11::strip_cv(type);
	if (bare->kind != pa11::TypeKind::Record || bare->complete)
		return;
	map<const void*, TemplateDeclaration*>::iterator found =
		record_template_declarations_.find(bare.get());
	if (found == record_template_declarations_.end())
		return;
	TemplateDeclaration* declaration = found->second;
	if (!declaration->has_definition)
		return;
	vector<TypePtr> args = record_template_arguments_[bare.get()];
	bool dependent = false;
	for (size_t i = 0; i < args.size(); ++i)
		if (type_contains_template_parameter(args[i],
		                                     record_template_arguments_))
			dependent = true;
	string key = template_argument_key(args);
	if (declaration->completing_specializations.count(key) != 0)
		return;
	declaration->completing_specializations.insert(key);

	size_t save_pos = pos_;
	vector<Scope*> save_scopes = scopes_;
	vector<map<string, TypePtr> > save_subst = template_type_substitutions_;
	map<string, TypePtr> subst;
	for (size_t i = 0; i < args.size() && i < declaration->parameters.size(); ++i)
		if (!declaration->parameters[i].name.empty())
			subst[declaration->parameters[i].name] = args[i];
	template_type_substitutions_.push_back(subst);
	active_class_instantiations_.push_back(
		ActiveClassInstantiation(
			declaration,
			template_specialization_name(declaration, args),
			bare));
	scopes_.clear();
	scopes_.push_back(declaration->lexical_scope != NULL
	                  ? declaration->lexical_scope
	                  : declaration->owner);
	pos_ = declaration->decl_begin;
	try
	{
		TypePtr parsed = parse_class_specifier();
		(void)parsed;
	}
	catch (const runtime_error& err)
	{
		active_class_instantiations_.pop_back();
		template_type_substitutions_ = save_subst;
		scopes_ = save_scopes;
		pos_ = save_pos;
		declaration->completing_specializations.erase(key);
		if (dependent &&
		    (string(err.what()) == "incomplete object type" ||
		     string(err.what()) == "incomplete class type" ||
		     string(err.what()) == "no matching constructor"))
			return;
		throw;
	}
	catch (...)
	{
		active_class_instantiations_.pop_back();
		template_type_substitutions_ = save_subst;
		scopes_ = save_scopes;
		pos_ = save_pos;
		declaration->completing_specializations.erase(key);
		throw;
	}
	active_class_instantiations_.pop_back();
	template_type_substitutions_ = save_subst;
	scopes_ = save_scopes;
	pos_ = save_pos;
	declaration->completing_specializations.erase(key);
	instantiate_member_function_templates(type);
	instantiate_member_variable_templates(type);
}

void Parser::complete_member_class_template_record(Binding* binding)
{
	if (binding == NULL || binding->type.get() == NULL)
		return;
	TypePtr bare = pa11::strip_cv(binding->type);
	if (bare->kind != pa11::TypeKind::Record ||
	    (bare->complete && bare->scope != NULL))
		return;
	TypePtr owner_record = binding->owner != NULL
		? pa11::record_type_for_scope(binding->owner) : TypePtr();
	if (owner_record.get() == NULL)
		return;
	owner_record = pa11::strip_cv(owner_record);
	map<const void*, TemplateDeclaration*>::iterator outer =
		record_template_declarations_.find(owner_record.get());
	if (outer == record_template_declarations_.end())
		return;
	map<pair<TemplateDeclaration*, string>, TemplateDeclaration*>::iterator found =
		member_class_templates_.find(make_pair(outer->second, binding->name));
	TemplateDeclaration* declaration = found != member_class_templates_.end()
		? found->second : NULL;
	if (declaration == NULL)
	{
		for (map<pair<TemplateDeclaration*, string>,
		         TemplateDeclaration*>::iterator it =
			     member_class_templates_.begin();
		     it != member_class_templates_.end();
		     ++it)
		{
			TemplateDeclaration* candidate_outer = it->first.first;
			if (it->first.second == binding->name &&
			    candidate_outer != NULL &&
			    candidate_outer->name == outer->second->name &&
			    candidate_outer->owner == outer->second->owner)
			{
				declaration = it->second;
				break;
			}
		}
	}
	if (declaration == NULL)
		return;
	if (!declaration->has_definition)
		return;
	vector<TypePtr> args = record_template_arguments_[owner_record.get()];
	string key = template_argument_key(args) + "::" + binding->name;
	if (declaration->completing_specializations.count(key) != 0)
		return;
	declaration->completing_specializations.insert(key);

	size_t save_pos = pos_;
	vector<Scope*> save_scopes = scopes_;
	vector<map<string, TypePtr> > save_subst = template_type_substitutions_;
	map<string, TypePtr> subst;
	for (size_t i = 0; i < args.size() && i < declaration->parameters.size(); ++i)
		if (!declaration->parameters[i].name.empty())
			subst[declaration->parameters[i].name] = args[i];
	template_type_substitutions_.push_back(subst);
	scopes_.clear();
	scopes_.push_back(declaration->lexical_scope != NULL
	                  ? declaration->lexical_scope
	                  : declaration->owner);
	pos_ = declaration->decl_begin;
	TypePtr parsed = parse_class_specifier();
	TypePtr parsed_bare = pa11::strip_cv(parsed);
	if (!bare->complete &&
	    parsed_bare.get() != NULL &&
	    parsed_bare->kind == pa11::TypeKind::Record &&
	    parsed_bare->complete &&
	    parsed_bare->scope != NULL)
	{
		*bare = *parsed_bare;
		binding->target_scope = bare->scope;
	}
	template_type_substitutions_ = save_subst;
	scopes_ = save_scopes;
	pos_ = save_pos;
	declaration->completing_specializations.erase(key);
}

void Parser::instantiate_member_function_templates(TypePtr type)
{
	TypePtr bare = pa11::strip_cv(type);
	if (bare->kind != pa11::TypeKind::Record)
		return;
	map<const void*, TemplateDeclaration*>::iterator outer =
		record_template_declarations_.find(bare.get());
	if (outer == record_template_declarations_.end())
		return;
	map<const void*, vector<TypePtr> >::iterator args_it =
		record_template_arguments_.find(bare.get());
	if (args_it == record_template_arguments_.end())
		return;
	for (map<pair<TemplateDeclaration*, string>,
	         vector<TemplateDeclaration*> >::iterator it =
		     member_function_templates_.begin();
	     it != member_function_templates_.end();
	     ++it)
	{
		if (it->first.first != outer->second)
		{
			TemplateDeclaration* candidate = it->first.first;
			if (candidate == NULL ||
			    candidate->name != outer->second->name ||
			    candidate->owner != outer->second->owner)
				continue;
		}
		for (size_t i = 0; i < it->second.size(); ++i)
		{
			string key = template_argument_key(args_it->second);
			if (it->second[i]->completing_specializations.count(key) != 0)
				continue;
			try
			{
				instantiate_function_template(it->second[i], args_it->second);
			}
			catch (const runtime_error&)
			{
			}
		}
	}
}

void Parser::instantiate_member_variable_templates(TypePtr type)
{
	TypePtr bare = pa11::strip_cv(type);
	if (bare->kind != pa11::TypeKind::Record)
		return;
	map<const void*, TemplateDeclaration*>::iterator outer =
		record_template_declarations_.find(bare.get());
	if (outer == record_template_declarations_.end())
		return;
	map<const void*, vector<TypePtr> >::iterator args_it =
		record_template_arguments_.find(bare.get());
	if (args_it == record_template_arguments_.end())
		return;
	for (map<pair<TemplateDeclaration*, string>,
	         vector<TemplateDeclaration*> >::iterator it =
		     member_variable_templates_.begin();
	     it != member_variable_templates_.end();
	     ++it)
	{
		if (it->first.first != outer->second)
			continue;
		for (size_t i = 0; i < it->second.size(); ++i)
		{
			TemplateDeclaration* declaration = it->second[i];
			string key = template_argument_key(args_it->second) +
			             "::" + declaration->name;
			if (!declaration->emitted_variable_specializations.insert(key).second)
				continue;
			size_t save_pos = pos_;
			vector<Scope*> save_scopes = scopes_;
			vector<map<string, TypePtr> > save_subst =
				template_type_substitutions_;
			map<string, TypePtr> subst;
			for (size_t j = 0; j < args_it->second.size() &&
			     j < declaration->parameters.size(); ++j)
				if (!declaration->parameters[j].name.empty())
					subst[declaration->parameters[j].name] =
						args_it->second[j];
			template_type_substitutions_.push_back(subst);
			scopes_.clear();
			scopes_.push_back(declaration->lexical_scope != NULL
			                  ? declaration->lexical_scope
			                  : declaration->owner);
			pos_ = declaration->decl_begin;
			Node node;
			parse_simple_or_function_declaration(node, true);
			if (!node.line.empty())
				add_child(root_, node);
			else
				for (size_t j = 0; j < node.children.size(); ++j)
					add_child(root_, node.children[j]);
			template_type_substitutions_ = save_subst;
			scopes_ = save_scopes;
			pos_ = save_pos;
		}
	}
}

bool Parser::type_is_template_dependent(TypePtr type) const
{
	return type_contains_template_parameter(type, record_template_arguments_);
}

TypePtr Parser::substitute_template_type(TypePtr type) const
{
	if (type.get() == NULL)
		return type;
	if (type->kind == pa11::TypeKind::TemplateParameter)
	{
		TypePtr subst;
		if (find_template_type_substitution(type->name, subst))
			return subst;
		return type;
	}
	if (type->kind == pa11::TypeKind::Cv)
		return pa11::make_cv(substitute_template_type(type->base), type->cv);
	if (type->kind == pa11::TypeKind::Pointer)
		return pa11::make_pointer(substitute_template_type(type->base));
	if (type->kind == pa11::TypeKind::LValueReference)
	{
		TypePtr base = substitute_template_type(type->base);
		if (base->kind == pa11::TypeKind::LValueReference ||
		    base->kind == pa11::TypeKind::RValueReference)
			return pa11::make_lvalue_reference(base->base);
		return pa11::make_lvalue_reference(base);
	}
	if (type->kind == pa11::TypeKind::RValueReference)
	{
		TypePtr base = substitute_template_type(type->base);
		if (base->kind == pa11::TypeKind::LValueReference)
			return base;
		if (base->kind == pa11::TypeKind::RValueReference)
			return pa11::make_rvalue_reference(base->base);
		return pa11::make_rvalue_reference(base);
	}
	if (type->kind == pa11::TypeKind::Array)
		return pa11::make_array(substitute_template_type(type->base),
		                        type->unknown_bound,
		                        type->bound);
	if (type->kind == pa11::TypeKind::Function)
	{
		vector<TypePtr> params;
		for (size_t i = 0; i < type->parameters.size(); ++i)
			params.push_back(substitute_template_type(type->parameters[i]));
		TypePtr out = pa11::make_function(substitute_template_type(type->base),
		                                  params,
		                                  type->variadic);
		out->cv = type->cv;
		return out;
	}
	if (type->kind == pa11::TypeKind::MemberPointer)
		return pa11::make_member_pointer(
			substitute_template_type(type->member_class),
			substitute_template_type(type->base));
	return type;
}

vector<TemplateDeclaration*> Parser::find_function_templates(
	const QualifiedName& name)
{
	vector<TemplateDeclaration*> out;
	if (name.qualifier != NULL)
	{
		map<Scope*, map<string, vector<TemplateDeclaration*> > >::iterator sit =
			function_templates_.find(name.qualifier);
		if (sit != function_templates_.end())
		{
			map<string, vector<TemplateDeclaration*> >::iterator it =
				sit->second.find(name.name);
			if (it != sit->second.end())
				out = it->second;
			if (!out.empty())
				return out;
		}
		for (size_t i = 0; i < name.qualifier->using_directives.size(); ++i)
		{
			QualifiedName nested = name;
			nested.qualifier = name.qualifier->using_directives[i];
			out = find_function_templates(nested);
			if (!out.empty())
				return out;
		}
		return out;
	}
	for (Scope* cur = current_scope(); cur != NULL; cur = cur->parent)
	{
		map<Scope*, map<string, vector<TemplateDeclaration*> > >::iterator sit =
			function_templates_.find(cur);
		if (sit == function_templates_.end())
			continue;
		map<string, vector<TemplateDeclaration*> >::iterator it =
			sit->second.find(name.name);
		if (it != sit->second.end())
			return it->second;
	}
	return out;
}

bool Parser::visible_function_template_name(const QualifiedName& name)
{
	return !find_function_templates(name).empty();
}

vector<Binding*> Parser::instantiate_explicit_function_templates(
	const QualifiedName& name)
{
	vector<Binding*> out;
	vector<TemplateDeclaration*> declarations = find_function_templates(name);
	for (size_t i = 0; i < declarations.size(); ++i)
		out.push_back(instantiate_function_template(declarations[i],
		                                            name.template_arguments));
	return out;
}

}  // namespace internal
}  // namespace pa12
