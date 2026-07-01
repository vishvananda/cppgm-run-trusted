#include "pa12_internal.h"
#include "pa12_expr_semantics_support.h"
#include "pa12_templates_function_support.h"
#include <functional>
using namespace std;
namespace pa12 {
namespace internal {

	bool owner_pattern_is_primary_parameter_list(
	const vector<TemplateArgument>& pattern,
	const vector<TemplateParameterInfo>& parameters)
{
	if (pattern.size() != parameters.size())
		return false;
	for (size_t i = 0; i < pattern.size(); ++i)
	{
		const TemplateParameterInfo& parameter = parameters[i];
		const TemplateArgument& argument = pattern[i];
		if (parameter.name.empty())
			return false;
		if (parameter.kind == TemplateParameterKind::Type)
		{
			if (argument.kind != TemplateArgumentKind::Type ||
			    argument.pack_expansion != parameter.is_pack)
				return false;
			TypePtr bare = argument.type.get() != NULL
				? pa11::strip_cv(argument.type) : TypePtr();
			if (bare.get() == NULL ||
			    bare->kind != pa11::TypeKind::TemplateParameter ||
			    bare->name.empty())
				return false;
		}
		else if (parameter.kind == TemplateParameterKind::NonType)
		{
			if (argument.kind != TemplateArgumentKind::Value ||
			    !argument.dependent ||
			    argument.value_name.empty())
				return false;
		}
		else
			return false;
	}
	return true;
}
bool skip_template_id_argument_tokens(const vector<Token>& tokens, size_t& pos)
{
	if (pos >= tokens.size() ||
	    tokens[pos].kind != posttoken::TokenKind::Simple ||
	    tokens[pos].type != OP_LT)
		return false;
	int depth = 0;
	int paren = 0;
	int square = 0;
	int brace = 0;
	while (pos < tokens.size())
	{
		const Token& tok = tokens[pos];
		if (tok.kind != posttoken::TokenKind::Simple)
		{
			++pos;
			continue;
		}
		if (tok.type == OP_LPAREN)
			++paren;
		else if (tok.type == OP_RPAREN && paren > 0)
			--paren;
		else if (tok.type == OP_LSQUARE)
			++square;
		else if (tok.type == OP_RSQUARE && square > 0)
			--square;
		else if (tok.type == OP_LBRACE)
			++brace;
		else if (tok.type == OP_RBRACE && brace > 0)
			--brace;
		else if (paren == 0 && square == 0 && brace == 0 &&
		         tok.type == OP_LT)
			++depth;
		else if (paren == 0 && square == 0 && brace == 0 &&
		         tok.type == OP_GT)
		{
			--depth;
			++pos;
			if (depth == 0)
				return true;
			continue;
		}
		++pos;
	}
	return false;
}

}  // namespace internal
}  // namespace pa12
