#include "pa12_internal.h"
#include "pa12_templates_function_support.h"

using namespace std;

namespace pa12 {
namespace internal {
namespace {

size_t explicit_member_parameter_count(Binding* function)
{
	if (function == NULL ||
	    function->type.get() == NULL ||
	    function->type->kind != pa11::TypeKind::Function)
		return 0;
	size_t count = function->type->parameters.size();
	if (function->owner != NULL &&
	    function->owner->kind == ScopeKind::Class &&
	    !function->is_static_member &&
	    count != 0)
		--count;
	return count;
}

TypePtr explicit_member_parameter_type(Binding* function, size_t explicit_index)
{
	if (function == NULL ||
	    function->type.get() == NULL ||
	    function->type->kind != pa11::TypeKind::Function)
		return TypePtr();
	size_t index = explicit_index;
	if (function->owner != NULL &&
	    function->owner->kind == ScopeKind::Class &&
	    !function->is_static_member)
		++index;
	if (index >= function->type->parameters.size())
		return TypePtr();
	return function->type->parameters[index];
}

TypePtr explicit_declaration_parameter_type(
	const TemplateDeclaration* declaration,
	size_t explicit_index)
{
	if (declaration == NULL ||
	    declaration->generic_function_type.get() == NULL ||
	    declaration->generic_function_type->kind != pa11::TypeKind::Function)
		return TypePtr();
	size_t index = explicit_index;
	if (declaration->placeholder != NULL &&
	    declaration->placeholder->owner != NULL &&
	    declaration->placeholder->owner->kind == ScopeKind::Class &&
	    !declaration->placeholder->is_static_member)
		++index;
	if (index >= declaration->generic_function_type->parameters.size())
		return TypePtr();
	return declaration->generic_function_type->parameters[index];
}

TypePtr parameter_core_type(TypePtr type)
{
	type = type.get() != NULL ? pa11::strip_cv(type) : TypePtr();
	while (type.get() != NULL &&
	       (type->kind == pa11::TypeKind::LValueReference ||
	        type->kind == pa11::TypeKind::RValueReference))
		type = pa11::strip_cv(type->base);
	return type;
}

string parameter_record_primary(TypePtr type)
{
	TypePtr bare = parameter_core_type(type);
	if (bare.get() == NULL || bare->kind != pa11::TypeKind::Record)
		return "";
	string primary = bare->template_primary_name.empty()
		? bare->name : bare->template_primary_name;
	size_t scope = primary.rfind("::");
	if (scope != string::npos)
		primary = primary.substr(scope + 2);
	size_t args = primary.find('<');
	if (args != string::npos)
		primary = primary.substr(0, args);
	return primary;
}

bool dependent_parameter_core(TypePtr type)
{
	TypePtr bare = parameter_core_type(type);
	return bare.get() == NULL ||
	       bare->is_dependent_typename ||
	       bare->kind == pa11::TypeKind::TemplateParameter ||
	       bare->kind == pa11::TypeKind::TemplateTemplateParameter;
}

bool confident_parameter_mismatch(TypePtr declaration_type,
                                  TypePtr function_type)
{
	TypePtr left = parameter_core_type(declaration_type);
	TypePtr right = parameter_core_type(function_type);
	if (left.get() == NULL || right.get() == NULL ||
	    pa11::same_type(left, right))
		return false;
	if (dependent_parameter_core(left) || dependent_parameter_core(right))
		return false;
	if (left->kind != right->kind)
		return true;
	if (left->kind == pa11::TypeKind::Fundamental)
		return left->fundamental != right->fundamental;
	if (left->kind == pa11::TypeKind::Record)
	{
		string lprimary = parameter_record_primary(left);
		string rprimary = parameter_record_primary(right);
		return !lprimary.empty() &&
		       !rprimary.empty() &&
		       lprimary != rprimary;
	}
	return false;
}

bool simple_token(const vector<Token>& tokens, size_t pos, ETokenType type)
{
	return pos < tokens.size() &&
	       tokens[pos].kind == posttoken::TokenKind::Simple &&
	       tokens[pos].type == type;
}

size_t matching_paren(const vector<Token>& tokens, size_t lparen, size_t end)
{
	if (!simple_token(tokens, lparen, OP_LPAREN))
		return end;
	int depth = 0;
	for (size_t i = lparen; i < end && i < tokens.size(); ++i)
	{
		if (tokens[i].kind != posttoken::TokenKind::Simple)
			continue;
		if (tokens[i].type == OP_LPAREN)
			++depth;
		else if (tokens[i].type == OP_RPAREN)
		{
			--depth;
			if (depth == 0)
				return i;
		}
	}
	return end;
}

size_t operator_assignment_parameter_lparen(const vector<Token>& tokens,
                                            size_t begin,
                                            size_t end)
{
	for (size_t i = begin; i + 2 < end && i + 2 < tokens.size(); ++i)
	{
		if (!simple_token(tokens, i, KW_OPERATOR) ||
		    !simple_token(tokens, i + 1, OP_ASS))
			continue;
		for (size_t p = i + 2; p < end && p < tokens.size(); ++p)
		{
			if (simple_token(tokens, p, OP_LPAREN))
				return p;
			if (simple_token(tokens, p, OP_LBRACE) ||
			    simple_token(tokens, p, OP_SEMICOLON))
				return end;
		}
	}
	return end;
}

size_t first_parameter_end(const vector<Token>& tokens,
                           size_t begin,
                           size_t end)
{
	int paren = 0;
	int square = 0;
	int angle = 0;
	for (size_t i = begin; i < end && i < tokens.size(); ++i)
	{
		if (tokens[i].kind != posttoken::TokenKind::Simple)
			continue;
		ETokenType type = tokens[i].type;
		if (type == OP_LPAREN)
			++paren;
		else if (type == OP_RPAREN)
		{
			if (paren == 0 && square == 0 && angle == 0)
				return i;
			if (paren > 0)
				--paren;
		}
		else if (type == OP_LSQUARE)
			++square;
		else if (type == OP_RSQUARE && square > 0)
			--square;
		else if (type == OP_LT && paren == 0 && square == 0)
			++angle;
		else if (type == OP_GT && angle > 0)
			--angle;
		else if ((type == OP_COMMA || type == OP_ASS) &&
		         paren == 0 && square == 0 && angle == 0)
			return i;
	}
	return end;
}

enum class ParameterReferenceCategory
{
	Unknown,
	LValue,
	RValue
};

ParameterReferenceCategory first_parameter_reference_category(
	const vector<Token>& tokens,
	size_t begin,
	size_t end)
{
	int paren = 0;
	int square = 0;
	int angle = 0;
	for (size_t i = begin; i < end && i < tokens.size(); ++i)
	{
		if (tokens[i].kind != posttoken::TokenKind::Simple)
			continue;
		ETokenType type = tokens[i].type;
		if (type == OP_LPAREN)
			++paren;
		else if (type == OP_RPAREN && paren > 0)
			--paren;
		else if (type == OP_LSQUARE)
			++square;
		else if (type == OP_RSQUARE && square > 0)
			--square;
		else if (type == OP_LT && paren == 0 && square == 0)
			++angle;
		else if (type == OP_GT && angle > 0)
			--angle;
		else if (paren == 0 && square == 0 && angle == 0)
		{
			if (type == OP_LAND)
				return ParameterReferenceCategory::RValue;
			if (type == OP_AMP)
				return ParameterReferenceCategory::LValue;
		}
	}
	return ParameterReferenceCategory::Unknown;
}

ParameterReferenceCategory ordinary_operator_assignment_parameter_category(
	const TemplateDeclaration* declaration,
	const vector<Token>& tokens)
{
	if (declaration == NULL)
		return ParameterReferenceCategory::Unknown;
	size_t header_end = function_body_start(tokens,
	                                        declaration->decl_begin,
	                                        declaration->decl_end);
	if (header_end == declaration->decl_end)
		header_end = declaration->decl_end;
	size_t lparen = operator_assignment_parameter_lparen(tokens,
	                                                     declaration->decl_begin,
	                                                     header_end);
	size_t rparen = matching_paren(tokens, lparen, header_end);
	if (rparen == header_end)
		return ParameterReferenceCategory::Unknown;
	size_t param_begin = lparen + 1;
	size_t param_end = first_parameter_end(tokens, param_begin, rparen);
	return first_parameter_reference_category(tokens, param_begin, param_end);
}

struct MemberFunctionQualifiers
{
	unsigned cv;
	int ref_qualifier;
	bool known;

	MemberFunctionQualifiers()
		: cv(pa11::CV_NONE),
		  ref_qualifier(0),
		  known(false)
	{
	}
};

size_t ordinary_member_parameter_lparen(const vector<Token>& tokens,
                                        size_t begin,
                                        size_t end)
{
	int paren = 0;
	int square = 0;
	int angle = 0;
	size_t candidate = end;
	for (size_t i = begin; i < end && i < tokens.size(); ++i)
	{
		if (tokens[i].kind != posttoken::TokenKind::Simple)
			continue;
		ETokenType type = tokens[i].type;
		if (type == OP_LPAREN)
		{
			if (paren == 0 && square == 0 && angle == 0)
				candidate = i;
			++paren;
		}
		else if (type == OP_RPAREN)
		{
			if (paren > 0)
				--paren;
		}
		else if (type == OP_LSQUARE)
			++square;
		else if (type == OP_RSQUARE && square > 0)
			--square;
		else if (type == OP_LT && paren == 0 && square == 0)
			++angle;
		else if (type == OP_GT && angle > 0)
			--angle;
	}
	return candidate;
}

MemberFunctionQualifiers ordinary_member_definition_qualifiers(
	const TemplateDeclaration* declaration,
	const vector<Token>& tokens)
{
	MemberFunctionQualifiers out;
	if (declaration == NULL)
		return out;
	size_t header_end = function_body_start(tokens,
	                                        declaration->decl_begin,
	                                        declaration->decl_end);
	if (header_end == declaration->decl_end)
		header_end = declaration->decl_end;
	size_t lparen = ordinary_member_parameter_lparen(
		tokens,
		declaration->decl_begin,
		header_end);
	size_t rparen = matching_paren(tokens, lparen, header_end);
	if (rparen == header_end)
		return out;
	out.known = true;
	for (size_t i = rparen + 1; i < header_end && i < tokens.size(); ++i)
	{
		if (tokens[i].kind != posttoken::TokenKind::Simple)
			continue;
		ETokenType type = tokens[i].type;
		if (type == OP_ARROW)
			break;
		if (type == KW_CONST)
			out.cv |= pa11::CV_CONST;
		else if (type == KW_VOLATILE)
			out.cv |= pa11::CV_VOLATILE;
		else if (type == OP_AMP)
			out.ref_qualifier = 1;
		else if (type == OP_LAND)
			out.ref_qualifier = 2;
		else if ((type == KW_NOEXCEPT || type == KW_THROW) &&
		         i + 1 < header_end &&
		         simple_token(tokens, i + 1, OP_LPAREN))
		{
			size_t close = matching_paren(tokens, i + 1, header_end);
			if (close != header_end)
				i = close;
		}
	}
	return out;
}

unsigned member_function_this_cv(Binding* function)
{
	if (function == NULL ||
	    function->type.get() == NULL ||
	    function->type->kind != pa11::TypeKind::Function ||
	    function->type->parameters.empty())
		return pa11::CV_NONE;
	unsigned cv = function->type->cv;
	TypePtr this_type = pa11::strip_cv(function->type->parameters[0]);
	if (this_type.get() != NULL &&
	    this_type->kind == pa11::TypeKind::Pointer &&
	    this_type->base.get() != NULL &&
	    this_type->base->kind == pa11::TypeKind::Cv)
		cv |= this_type->base->cv;
	return cv;
}

bool ordinary_member_definition_qualifiers_match(
	const TemplateDeclaration* declaration,
	Binding* function,
	const vector<Token>& tokens)
{
	if (function == NULL ||
	    function->owner == NULL ||
	    function->owner->kind != ScopeKind::Class ||
	    function->is_static_member)
		return true;
	MemberFunctionQualifiers qualifiers =
		ordinary_member_definition_qualifiers(declaration, tokens);
	if (!qualifiers.known)
		return true;
	return qualifiers.cv == member_function_this_cv(function) &&
	       qualifiers.ref_qualifier == function->ref_qualifier;
}

bool ordinary_member_definition_arity_matches(
	const TemplateDeclaration* declaration,
	Binding* function)
{
	if (declaration == NULL || declaration->function_parameter_names.empty())
		return true;
	size_t count = declaration->function_parameter_names.size();
	if (declaration->function_parameter_names[0] == "this" && count != 0)
		--count;
	return count == explicit_member_parameter_count(function);
}

bool ordinary_member_definition_parameter_types_match(
	const TemplateDeclaration* declaration,
	Binding* function)
{
	size_t count = explicit_member_parameter_count(function);
	for (size_t i = 0; i < count; ++i)
	{
		TypePtr declaration_type =
			explicit_declaration_parameter_type(declaration, i);
		TypePtr function_type = explicit_member_parameter_type(function, i);
		if (confident_parameter_mismatch(declaration_type, function_type))
			return false;
	}
	return true;
}

}

bool ordinary_member_definition_matches_placeholder(
	const TemplateDeclaration* declaration,
	Binding* function,
	const vector<Token>& tokens)
{
	if (!ordinary_member_definition_arity_matches(declaration, function))
		return false;
	if (!ordinary_member_definition_qualifiers_match(declaration,
	                                                function,
	                                                tokens))
		return false;
	if (!ordinary_member_definition_parameter_types_match(declaration,
	                                                     function))
		return false;
	if (declaration == NULL || declaration->name != "operator=" ||
	    explicit_member_parameter_count(function) != 1)
		return true;
	ParameterReferenceCategory category =
		ordinary_operator_assignment_parameter_category(declaration, tokens);
	if (category == ParameterReferenceCategory::Unknown)
		return true;
	TypePtr parameter = explicit_member_parameter_type(function, 0);
	if (parameter.get() == NULL)
		return true;
	if (category == ParameterReferenceCategory::RValue)
		return parameter->kind == pa11::TypeKind::RValueReference;
	if (category == ParameterReferenceCategory::LValue)
		return parameter->kind == pa11::TypeKind::LValueReference;
	return true;
}

}
}
