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
		target[i].kind = source[i].kind;
		if (!source[i].name.empty())
			target[i].name = source[i].name;
		if (source[i].type.get() != NULL)
			target[i].type = source[i].type;
		target[i].is_pack = source[i].is_pack;
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
	const map<const void*, vector<TemplateArgument> >& record_template_arguments);

bool template_argument_contains_template_parameter(
	const TemplateArgument& arg,
	const map<const void*, vector<TemplateArgument> >& record_template_arguments)
{
	if (arg.kind == TemplateArgumentKind::Type)
		return type_contains_template_parameter(arg.type,
		                                        record_template_arguments);
	if (arg.kind == TemplateArgumentKind::Value)
		return arg.dependent ||
		       type_contains_template_parameter(arg.type,
		                                        record_template_arguments);
	for (size_t i = 0; i < arg.pack.size(); ++i)
		if (template_argument_contains_template_parameter(
			    arg.pack[i],
			    record_template_arguments))
			return true;
	return false;
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

bool template_argument_kind_matches_parameter(
	const TemplateArgument& argument,
	const TemplateParameterInfo& parameter)
{
	if (parameter.kind == TemplateParameterKind::Type)
		return argument.kind == TemplateArgumentKind::Type;
	if (parameter.kind == TemplateParameterKind::NonType)
		return argument.kind == TemplateArgumentKind::Value;
	return false;
}

bool type_contains_template_parameter(
	TypePtr type,
	const map<const void*, vector<TemplateArgument> >& record_template_arguments)
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
		map<const void*, vector<TemplateArgument> >::const_iterator found =
			record_template_arguments.find(type.get());
		if (found != record_template_arguments.end())
			for (size_t i = 0; i < found->second.size(); ++i)
				if (template_argument_contains_template_parameter(
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

string template_argument_spelling(const TemplateArgument& argument)
{
	if (argument.kind == TemplateArgumentKind::Type)
		return template_type_spelling(argument.type) +
		       (argument.pack_expansion ? "..." : "");
	if (argument.kind == TemplateArgumentKind::Value)
	{
		if (argument.dependent)
			return "dependent-value";
		TypePtr bare = argument.type.get() != NULL
			? pa11::strip_cv(argument.type) : TypePtr();
		if (bare.get() != NULL && bare->kind == pa11::TypeKind::Enum)
			return template_type_spelling(bare) + " " +
			       to_string(argument.value) +
			       (argument.pack_expansion ? "..." : "");
		return to_string(argument.value) +
		       (argument.pack_expansion ? "..." : "");
	}
	ostringstream out;
	for (size_t i = 0; i < argument.pack.size(); ++i)
	{
		if (i != 0)
			out << ",";
		out << template_argument_spelling(argument.pack[i]);
	}
	return out.str();
}

string template_argument_key_part(const TemplateArgument& argument)
{
	if (argument.kind == TemplateArgumentKind::Type)
		return string(argument.pack_expansion ? "TE(" : "T(") +
		       template_type_key(argument.type) + ")";
	if (argument.kind == TemplateArgumentKind::Value)
		return string(argument.pack_expansion ? "VE(" : "V(") +
		       template_type_key(argument.type) + "," +
		       (argument.dependent ? string("?") :
		        to_string(argument.value)) + ")";
	ostringstream out;
	out << "P(";
	for (size_t i = 0; i < argument.pack.size(); ++i)
	{
		if (i != 0)
			out << ",";
		out << template_argument_key_part(argument.pack[i]);
	}
	out << ")";
	return out.str();
}

string template_argument_spelling(const vector<TemplateArgument>& arguments)
{
	ostringstream out;
	for (size_t i = 0; i < arguments.size(); ++i)
	{
		if (i != 0)
			out << ",";
		out << template_argument_spelling(arguments[i]);
	}
	return out.str();
}

bool same_template_argument_value(const TemplateArgument& left,
                                  const TemplateArgument& right)
{
	if (left.kind != right.kind)
		return false;
	if (left.kind == TemplateArgumentKind::Type)
		return pa11::same_type(left.type, right.type);
	if (left.kind == TemplateArgumentKind::Value)
		return !left.dependent && !right.dependent &&
		       left.value == right.value;
	if (left.pack.size() != right.pack.size())
		return false;
	for (size_t i = 0; i < left.pack.size(); ++i)
		if (!same_template_argument_value(left.pack[i], right.pack[i]))
			return false;
	return true;
}

bool match_template_argument_pattern(
	const TemplateArgument& pattern,
	const TemplateArgument& actual,
	map<string, TemplateArgument>& deduced)
{
	if (pattern.kind == TemplateArgumentKind::Type &&
	    pattern.type.get() != NULL &&
	    pattern.type->kind == pa11::TypeKind::TemplateParameter)
	{
		map<string, TemplateArgument>::iterator found =
			deduced.find(pattern.type->name);
		if (found == deduced.end())
		{
			deduced[pattern.type->name] = actual;
			return true;
		}
		return same_template_argument_value(found->second, actual);
	}
	if (pattern.kind != actual.kind)
		return false;
	if (pattern.kind == TemplateArgumentKind::Type)
		return pa11::same_type(pattern.type, actual.type);
	if (pattern.kind == TemplateArgumentKind::Value)
		return !pattern.dependent && !actual.dependent &&
		       pattern.value == actual.value;
	if (pattern.pack.size() != actual.pack.size())
		return false;
	for (size_t i = 0; i < pattern.pack.size(); ++i)
		if (!match_template_argument_pattern(pattern.pack[i],
		                                     actual.pack[i],
		                                     deduced))
			return false;
	return true;
}

bool match_class_specialization(TemplateDeclaration* specialization,
                                const vector<TemplateArgument>& full_args,
                                vector<TemplateArgument>& selected_args)
{
	if (specialization->class_specialization_pattern.size() != full_args.size())
		return false;
	map<string, TemplateArgument> deduced;
	for (size_t i = 0; i < full_args.size(); ++i)
		if (!match_template_argument_pattern(
			    specialization->class_specialization_pattern[i],
			    full_args[i],
			    deduced))
			return false;
	for (size_t i = 0; i < specialization->parameters.size(); ++i)
	{
		const string& name = specialization->parameters[i].name;
		map<string, TemplateArgument>::iterator found = deduced.find(name);
		if (found == deduced.end())
			return false;
		selected_args.push_back(found->second);
	}
	return true;
}

}  // namespace

vector<TemplateParameterInfo> Parser::parse_template_parameter_clause()
{
	vector<TemplateParameterInfo> parameters;
	expect(OP_LT);
	vector<map<string, TypePtr> > save_subst = template_type_substitutions_;
	template_type_substitutions_.push_back(map<string, TypePtr>());
	if (consume(OP_GT))
	{
		template_type_substitutions_ = save_subst;
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
		if (!consume(OP_COMMA))
			break;
	}
	expect(OP_GT);
	template_type_substitutions_ = save_subst;
	return parameters;
}

TemplateParameterInfo Parser::parse_template_parameter_info()
{
	TemplateParameterInfo parameter;
	if (consume(KW_TEMPLATE))
	{
		parameter.kind = TemplateParameterKind::TemplateTemplate;
		skip_template_parameter_clause();
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
		if (!declaration->parameters[i].name.empty() &&
		    declaration->parameters[i].kind == TemplateParameterKind::Type)
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
	vector<map<string, TypePtr> > save_subst = template_type_substitutions_;
	vector<map<string, TemplateArgument> > save_value_subst =
		template_value_substitutions_;
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
			Scope* target = qname.qualifier != NULL ? qname.qualifier :
				declaration->owner;
			declaration->owner = target;
			declaration->name = qname.name;
			if (qname.has_template_arguments)
			{
				declaration->class_specialization = true;
				declaration->class_specialization_pattern =
					qname.template_arguments;
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
		Scope* target = qname.qualifier != NULL ? qname.qualifier :
			declaration->owner;
		if (declaration->parameters.empty() && qname.has_template_arguments)
		{
			vector<TemplateDeclaration*> primaries =
				find_function_templates(qname);
			if (primaries.empty())
				throw runtime_error("function template specialization without primary");
			TemplateDeclaration* primary = primaries[0];
			vector<TemplateArgument> full_args =
				complete_template_arguments(primary, qname.template_arguments);
			string key = template_argument_key(full_args);
			template_type_substitutions_ = save_subst;
			template_value_substitutions_ = save_value_subst;
			pos_ = declaration->decl_begin;
			bool save_force = force_new_function_binding_;
			bool save_override = override_function_parameter_names_;
			vector<string> save_override_names =
				function_parameter_name_override_;
			map<Binding*, vector<string> >::iterator primary_names =
				function_parameter_names_.find(primary->placeholder);
			force_new_function_binding_ = true;
			if (primary_names != function_parameter_names_.end())
			{
				override_function_parameter_names_ = true;
				function_parameter_name_override_ =
					primary_names->second;
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
			else if (!node.children.empty() &&
			         node.children.back().binding != NULL)
			{
				primary->function_specializations[key] =
					node.children.back().binding;
				add_child(root_, node.children.back());
			}
			else
				throw runtime_error("function template specialization failed");
			pos_ = save_pos;
			return;
		}
		declaration->owner = target;
		declaration->name = qname.name;
		declaration->generic_function_type = type;
		Binding* placeholder =
			add_function_binding(target, qname.name, type, false);
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
	for (size_t i = 0; i < declaration->parameters.size(); ++i)
		if (!declaration->parameters[i].name.empty() &&
		    declaration->parameters[i].kind == TemplateParameterKind::Type)
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
			if (at_identifier() && lookahead(OP_DOTS, 1))
			{
				string pack_name = consume_identifier();
				expect(OP_DOTS);
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
			if (!expr.has_constant_value)
				throw runtime_error("invalid non-type template argument");
			TemplateArgument arg =
				TemplateArgument::value_arg(expression_object_type(expr.type),
				                            expr.constant_value);
			arg.pack_expansion = consume(OP_DOTS);
			arguments.push_back(arg);
		}
		if (!consume(OP_COMMA))
			break;
	}
	expect(OP_GT);
	return true;
}

vector<TemplateArgument> Parser::expand_template_argument_pack(
	const TemplateArgument& argument) const
{
	if (!argument.pack_expansion)
	{
		vector<TemplateArgument> single;
		single.push_back(argument);
		return single;
	}
	if (argument.kind == TemplateArgumentKind::Pack)
		return argument.pack;

	string pack_name;
	if (argument.kind == TemplateArgumentKind::Type &&
	    type_contains_template_parameter_name(argument.type, pack_name))
	{
		TemplateArgument subst;
		if (!find_template_value_substitution(pack_name, subst) ||
		    subst.kind != TemplateArgumentKind::Pack)
		{
			vector<TemplateArgument> unresolved;
			unresolved.push_back(argument);
			return unresolved;
		}
		vector<TemplateArgument> out;
		for (size_t i = 0; i < subst.pack.size(); ++i)
		{
			if (subst.pack[i].kind != TemplateArgumentKind::Type)
				throw runtime_error("type template argument pack required");
			TypePtr expanded =
				substitute_template_type_parameter(argument.type,
				                                   pack_name,
				                                   subst.pack[i].type);
			out.push_back(TemplateArgument::type_arg(expanded));
		}
		return out;
	}
	if (argument.kind == TemplateArgumentKind::Value)
	{
		TemplateArgument subst;
		if (argument.type.get() != NULL &&
		    type_contains_template_parameter_name(argument.type, pack_name) &&
		    find_template_value_substitution(pack_name, subst) &&
		    subst.kind == TemplateArgumentKind::Pack)
		{
			vector<TemplateArgument> out;
			for (size_t i = 0; i < subst.pack.size(); ++i)
			{
				if (subst.pack[i].kind != TemplateArgumentKind::Value)
					throw runtime_error("value template argument pack required");
				out.push_back(subst.pack[i]);
			}
			return out;
		}
		vector<TemplateArgument> unresolved;
		unresolved.push_back(argument);
		return unresolved;
	}
	throw runtime_error("unsupported template argument pack expansion");
}

vector<TemplateArgument> Parser::complete_template_arguments(
	TemplateDeclaration* declaration,
	const vector<TemplateArgument>& explicit_arguments)
{
	vector<TemplateArgument> explicit_expanded;
	for (size_t i = 0; i < explicit_arguments.size(); ++i)
	{
		vector<TemplateArgument> expansion =
			expand_template_argument_pack(explicit_arguments[i]);
		explicit_expanded.insert(explicit_expanded.end(),
		                         expansion.begin(),
		                         expansion.end());
	}
	vector<TemplateArgument> out;
	size_t explicit_index = 0;
	for (size_t param_index = 0;
	     param_index < declaration->parameters.size();
	     ++param_index)
	{
		const TemplateParameterInfo& parameter =
			declaration->parameters[param_index];
		if (parameter.is_pack)
		{
			if (explicit_index < explicit_expanded.size() &&
			    explicit_expanded[explicit_index].kind ==
				    TemplateArgumentKind::Pack)
			{
				TemplateArgument arg = explicit_expanded[explicit_index++];
				for (size_t i = 0; i < arg.pack.size(); ++i)
					if (!template_argument_kind_matches_parameter(arg.pack[i],
					                                              parameter))
						throw runtime_error("template pack argument kind mismatch");
				out.push_back(arg);
				continue;
			}
			size_t required_after = 0;
			for (size_t j = param_index + 1;
			     j < declaration->parameters.size();
			     ++j)
				if (!declaration->parameters[j].is_pack &&
				    !declaration->parameters[j].has_default)
					++required_after;
			if (explicit_index + required_after > explicit_expanded.size())
				throw runtime_error("missing template argument");
			size_t take =
				explicit_expanded.size() - explicit_index - required_after;
			vector<TemplateArgument> pack;
			for (size_t i = 0; i < take; ++i)
			{
				TemplateArgument arg = explicit_expanded[explicit_index++];
				if (arg.kind == TemplateArgumentKind::Pack)
				{
					for (size_t p = 0; p < arg.pack.size(); ++p)
					{
						if (!template_argument_kind_matches_parameter(
							    arg.pack[p],
							    parameter))
							throw runtime_error("template pack argument kind mismatch");
						pack.push_back(arg.pack[p]);
					}
					continue;
				}
				if (!template_argument_kind_matches_parameter(arg, parameter))
					throw runtime_error("template pack argument kind mismatch");
				pack.push_back(arg);
			}
			out.push_back(TemplateArgument::pack_arg(pack));
			continue;
		}
		if (explicit_index < explicit_expanded.size())
		{
			TemplateArgument arg = explicit_expanded[explicit_index++];
			if (!template_argument_kind_matches_parameter(arg, parameter))
				throw runtime_error("template argument kind mismatch");
			out.push_back(arg);
			continue;
		}
		if (!parameter.has_default)
			throw runtime_error("missing template argument");
		size_t save_pos = pos_;
		vector<map<string, TypePtr> > save_subst =
			template_type_substitutions_;
		vector<map<string, TemplateArgument> > save_value_subst =
			template_value_substitutions_;
		map<string, TypePtr> subst;
		map<string, TemplateArgument> value_subst;
		for (size_t i = 0; i < out.size(); ++i)
			if (!declaration->parameters[i].name.empty())
			{
				if (declaration->parameters[i].is_pack)
				{
					subst[declaration->parameters[i].name] =
						pa11::make_template_parameter_type(
							declaration->parameters[i].name);
					value_subst[declaration->parameters[i].name] =
						out[i];
				}
				else if (declaration->parameters[i].kind ==
				    TemplateParameterKind::Type)
					subst[declaration->parameters[i].name] =
						out[i].type;
				else
					value_subst[declaration->parameters[i].name] =
						out[i];
		}
		template_type_substitutions_.push_back(subst);
		template_value_substitutions_.push_back(value_subst);
		pos_ = parameter.default_begin;
		TemplateArgument arg;
		try
		{
			if (parameter.kind == TemplateParameterKind::Type)
				arg = TemplateArgument::type_arg(parse_type_id());
			else
			{
				bool default_dependent =
					type_is_template_dependent(parameter.type);
				for (size_t i = 0; i < out.size(); ++i)
					if (template_argument_contains_template_parameter(
						    out[i],
						    record_template_arguments_))
						default_dependent = true;
				int save_expression_depth = template_argument_expression_depth_;
				++template_argument_expression_depth_;
				Expr expr;
				try
				{
					expr = parse_assignment_expression();
				}
				catch (...)
				{
					template_argument_expression_depth_ = save_expression_depth;
					if (!default_dependent)
						throw;
					expr = Expr();
				}
				template_argument_expression_depth_ = save_expression_depth;
				if (!expr.has_constant_value && !default_dependent)
					throw runtime_error("invalid default template argument");
				if (expr.has_constant_value)
					arg = TemplateArgument::value_arg(expression_object_type(expr.type),
					                                  expr.constant_value);
				else
					arg = TemplateArgument::dependent_value_arg(parameter.type);
			}
			if (pos_ != parameter.default_end)
				throw runtime_error("invalid default template argument");
		}
		catch (...)
		{
			template_type_substitutions_ = save_subst;
			template_value_substitutions_ = save_value_subst;
			pos_ = save_pos;
			throw;
		}
		out.push_back(arg);
		template_type_substitutions_ = save_subst;
		template_value_substitutions_ = save_value_subst;
		pos_ = save_pos;
	}
	if (explicit_index != explicit_expanded.size())
		throw runtime_error("too many template arguments");
	return out;
}


}  // namespace internal
}  // namespace pa12
