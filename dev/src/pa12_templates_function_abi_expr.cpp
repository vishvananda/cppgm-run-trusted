#include "pa12_templates_function_abi_internal.h"
#include "pa12_templates_instance_support.h"

#include <utility>

using namespace std;

namespace pa12 {
namespace internal {

namespace {

string abi_dependent_expression_with_substitutions(
	const vector<Token>& tokens,
	size_t begin,
	size_t end,
	AbiSubstitutionContext& ctx);

void abi_split_template_arguments(const vector<Token>& tokens,
                                  size_t begin,
                                  size_t end,
                                  vector<pair<size_t, size_t> >& out);

string abi_function_parameter_expression(const string& name,
                                         const AbiSubstitutionContext& ctx)
{
	if (ctx.function_parameter_names == NULL)
		return "";
	for (size_t i = 0; i < ctx.function_parameter_names->size(); ++i)
		if ((*ctx.function_parameter_names)[i] == name)
			return i == 0
				? string("fp_")
				: string("fp") + abi_base36_number(i - 1) + "_";
	return "";
}

bool abi_find_call_open(const vector<Token>& tokens,
                        size_t begin,
                        size_t end,
                        size_t& open)
{
	if (end <= begin + 2 || !abi_token_is_simple(tokens, end - 1, OP_RPAREN))
		return false;
	int depth = 0;
	for (size_t i = end; i > begin; --i)
	{
		size_t pos = i - 1;
		if (tokens[pos].kind != posttoken::TokenKind::Simple)
			continue;
		if (tokens[pos].type == OP_RPAREN)
			++depth;
		else if (tokens[pos].type == OP_LPAREN)
		{
			--depth;
			if (depth == 0)
			{
				open = pos;
				return open > begin;
			}
		}
	}
	return false;
}

bool abi_find_top_level_member_operator(const vector<Token>& tokens,
                                        size_t begin,
                                        size_t end,
                                        size_t& op)
{
	int paren = 0;
	int square = 0;
	int brace = 0;
	bool found = false;
	for (size_t i = begin; i < end; ++i)
	{
		if (tokens[i].kind != posttoken::TokenKind::Simple)
			continue;
		ETokenType type = tokens[i].type;
		if (type == OP_LPAREN)
			++paren;
		else if (type == OP_RPAREN)
			--paren;
		else if (type == OP_LSQUARE)
			++square;
		else if (type == OP_RSQUARE)
			--square;
		else if (type == OP_LBRACE)
			++brace;
		else if (type == OP_RBRACE)
			--brace;
		else if (paren == 0 && square == 0 && brace == 0 &&
		         (type == OP_DOT || type == OP_ARROW))
		{
			op = i;
			found = true;
		}
	}
	return found;
}

void abi_split_top_level_arguments(const vector<Token>& tokens,
                                   size_t begin,
                                   size_t end,
                                   vector<pair<size_t, size_t> >& out)
{
	int paren = 0;
	int square = 0;
	int brace = 0;
	size_t arg_begin = begin;
	for (size_t i = begin; i < end; ++i)
	{
		if (tokens[i].kind != posttoken::TokenKind::Simple)
			continue;
		ETokenType type = tokens[i].type;
		if (type == OP_LPAREN)
			++paren;
		else if (type == OP_RPAREN)
			--paren;
		else if (type == OP_LSQUARE)
			++square;
		else if (type == OP_RSQUARE)
			--square;
		else if (type == OP_LBRACE)
			++brace;
		else if (type == OP_RBRACE)
			--brace;
		else if (type == OP_COMMA && paren == 0 && square == 0 &&
		         brace == 0)
		{
			out.push_back(make_pair(arg_begin, i));
			arg_begin = i + 1;
		}
	}
	if (arg_begin < end)
		out.push_back(make_pair(arg_begin, end));
}

string abi_encode_type_tokens_with_substitutions(const vector<Token>& tokens,
                                                 size_t begin,
                                                 size_t end,
                                                 AbiSubstitutionContext& ctx)
{
	abi_trim_wrapping_parens(tokens, begin, end);
	if (begin >= end)
		return "";
	if (abi_token_is_simple(tokens, end - 1, OP_AMP) ||
	    abi_token_is_simple(tokens, end - 1, OP_LAND) ||
	    abi_token_is_simple(tokens, end - 1, OP_STAR))
	{
		string base = abi_encode_type_tokens_with_substitutions(
			tokens, begin, end - 1, ctx);
		if (base.empty())
			return "";
		string encoded = string(abi_token_is_simple(tokens, end - 1, OP_AMP)
		                        ? "R"
		                        : abi_token_is_simple(tokens, end - 1, OP_LAND)
		                          ? "O" : "P") + base;
		abi_add_substitution(ctx, encoded);
		return encoded;
	}
	if (end > begin + 3 &&
	    abi_token_is_simple(tokens, end - 1, OP_RPAREN))
	{
		int angle = 0;
		int square = 0;
		int brace = 0;
		size_t function_open = end;
		for (size_t i = begin; i < end; ++i)
		{
			if (tokens[i].kind != posttoken::TokenKind::Simple)
				continue;
			ETokenType type = tokens[i].type;
			if (type == OP_LT)
				++angle;
			else if (type == OP_GT && angle > 0)
				--angle;
			else if (type == OP_LSQUARE)
				++square;
			else if (type == OP_RSQUARE && square > 0)
				--square;
			else if (type == OP_LBRACE)
				++brace;
			else if (type == OP_RBRACE && brace > 0)
				--brace;
			else if (type == OP_LPAREN && angle == 0 &&
			         square == 0 && brace == 0)
			{
				function_open = i;
				break;
			}
		}
		if (function_open > begin && function_open < end - 1)
		{
			string result = abi_encode_type_tokens_with_substitutions(
				tokens, begin, function_open, ctx);
			if (result.empty())
				return "";
			string encoded = "F" + result;
			vector<pair<size_t, size_t> > args;
			abi_split_top_level_arguments(tokens,
			                              function_open + 1,
			                              end - 1,
			                              args);
			for (size_t i = 0; i < args.size(); ++i)
			{
				string arg = abi_encode_type_tokens_with_substitutions(
					tokens, args[i].first, args[i].second, ctx);
				if (arg.empty())
					return "";
				encoded += arg;
			}
			if (args.empty())
				encoded += "v";
			encoded += "E";
			return abi_use_or_add_substitution(ctx, encoded);
		}
	}
	if (begin + 3 <= end &&
	    tokens[begin].kind == posttoken::TokenKind::Identifier &&
	    abi_token_is_simple(tokens, begin + 1, OP_LT) &&
	    abi_token_is_simple(tokens, end - 1, OP_GT))
	{
		string out = abi_source_name(tokens[begin].source) + "I";
		vector<pair<size_t, size_t> > args;
		abi_split_template_arguments(tokens, begin + 2, end - 1, args);
		for (size_t i = 0; i < args.size(); ++i)
		{
			string type_arg = abi_encode_type_tokens_with_substitutions(
				tokens, args[i].first, args[i].second, ctx);
			if (!type_arg.empty())
			{
				out += type_arg;
				continue;
			}
			string value_arg = abi_dependent_expression_with_substitutions(
				tokens, args[i].first, args[i].second, ctx);
			if (value_arg.empty())
				return "";
			out += "X" + value_arg + "E";
		}
		return out + "E";
	}
	if (end == begin + 1 &&
	    tokens[begin].kind == posttoken::TokenKind::Identifier)
	{
		map<string, size_t>::const_iterator found =
			ctx.template_parameters.find(tokens[begin].source);
		if (found != ctx.template_parameters.end())
		{
			string encoded = found->second == 0
				? string("T_")
				: string("T") + to_string(found->second - 1) + "_";
			abi_add_substitution(ctx, encoded);
			return encoded;
		}
	}
	AbiTokenType raw =
		abi_encode_type_tokens(tokens, begin, end, ctx.template_parameters);
	if (raw.dependent)
		abi_add_substitution(ctx, raw.encoded);
	return raw.encoded;
}

void abi_split_template_arguments(const vector<Token>& tokens,
                                  size_t begin,
                                  size_t end,
                                  vector<pair<size_t, size_t> >& out)
{
	int angle = 0;
	int paren = 0;
	int square = 0;
	size_t arg_begin = begin;
	for (size_t i = begin; i < end; ++i)
	{
		if (tokens[i].kind != posttoken::TokenKind::Simple)
			continue;
		ETokenType type = tokens[i].type;
		if (type == OP_LT)
			++angle;
		else if (type == OP_GT && angle > 0)
			--angle;
		else if (type == OP_LPAREN)
			++paren;
		else if (type == OP_RPAREN && paren > 0)
			--paren;
		else if (type == OP_LSQUARE)
			++square;
		else if (type == OP_RSQUARE && square > 0)
			--square;
		else if (type == OP_COMMA && angle == 0 &&
		         paren == 0 && square == 0)
		{
			out.push_back(make_pair(arg_begin, i));
			arg_begin = i + 1;
		}
	}
	if (arg_begin < end)
		out.push_back(make_pair(arg_begin, end));
}

string abi_template_id_expression_with_substitutions(
	const vector<Token>& tokens,
	size_t begin,
	size_t end,
	AbiSubstitutionContext& ctx)
{
	if (begin + 3 > end ||
	    tokens[begin].kind != posttoken::TokenKind::Identifier ||
	    !abi_token_is_simple(tokens, begin + 1, OP_LT) ||
	    !abi_token_is_simple(tokens, end - 1, OP_GT))
		return "";
	string callee_name = abi_source_name(tokens[begin].source);
	abi_add_substitution(ctx, callee_name);
	string out = callee_name + "I";
	vector<pair<size_t, size_t> > args;
	abi_split_template_arguments(tokens, begin + 2, end - 1, args);
	for (size_t i = 0; i < args.size(); ++i)
	{
		string type_arg = abi_encode_type_tokens_with_substitutions(
			tokens, args[i].first, args[i].second, ctx);
		if (!type_arg.empty())
		{
			out += type_arg;
			continue;
		}
		string value_arg = abi_dependent_expression_with_substitutions(
			tokens, args[i].first, args[i].second, ctx);
		if (value_arg.empty())
			return "";
		out += "X" + value_arg + "E";
	}
	return out + "E";
}

string abi_call_expression_with_substitutions(const vector<Token>& tokens,
                                              size_t callee_begin,
                                              size_t call_open,
                                              size_t end,
                                              AbiSubstitutionContext& ctx)
{
	string callee = abi_dependent_expression_with_substitutions(
		tokens, callee_begin, call_open, ctx);
	if (callee.empty())
		return "";
	string out = "cl" + callee;
	vector<pair<size_t, size_t> > args;
	abi_split_top_level_arguments(tokens, call_open + 1, end - 1, args);
	for (size_t i = 0; i < args.size(); ++i)
	{
		string arg = abi_dependent_expression_with_substitutions(
			tokens, args[i].first, args[i].second, ctx);
		if (arg.empty())
			return "";
		out += arg;
	}
	return out + "E";
}

bool abi_find_top_level_colon2(const vector<Token>& tokens,
                               size_t begin,
                               size_t end,
                               size_t& colon)
{
	int angle = 0;
	int paren = 0;
	int square = 0;
	int brace = 0;
	bool found = false;
	for (size_t i = begin; i < end; ++i)
	{
		if (tokens[i].kind != posttoken::TokenKind::Simple)
			continue;
		ETokenType type = tokens[i].type;
		if (type == OP_LT)
			++angle;
		else if (type == OP_GT && angle > 0)
			--angle;
		else if (type == OP_LPAREN)
			++paren;
		else if (type == OP_RPAREN && paren > 0)
			--paren;
		else if (type == OP_LSQUARE)
			++square;
		else if (type == OP_RSQUARE && square > 0)
			--square;
		else if (type == OP_LBRACE)
			++brace;
		else if (type == OP_RBRACE && brace > 0)
			--brace;
		else if (type == OP_COLON2 && angle == 0 && paren == 0 &&
		         square == 0 && brace == 0)
		{
			colon = i;
			found = true;
		}
	}
	return found;
}

bool abi_type_token_span_is_template_id(const vector<Token>& tokens,
                                        size_t begin,
                                        size_t end)
{
	return begin + 3 <= end &&
	       tokens[begin].kind == posttoken::TokenKind::Identifier &&
	       abi_token_is_simple(tokens, begin + 1, OP_LT) &&
	       abi_token_is_simple(tokens, end - 1, OP_GT);
}

bool abi_qualified_member_expression_with_substitutions(
	const vector<Token>& tokens,
	size_t begin,
	size_t end,
	AbiSubstitutionContext& ctx,
	string& out)
{
	size_t colon = 0;
	if (!abi_find_top_level_colon2(tokens, begin, end, colon) ||
	    colon <= begin || colon + 1 >= end)
		return false;
	size_t member = colon + 1;
	if (member < end &&
	    tokens[member].kind == posttoken::TokenKind::Simple &&
	    tokens[member].type == KW_TEMPLATE)
		++member;
	if (member + 1 != end ||
	    tokens[member].kind != posttoken::TokenKind::Identifier)
		return false;
	string owner = abi_encode_type_tokens_with_substitutions(
		tokens, begin, colon, ctx);
	if (owner.empty())
		return false;
	out = "sr" + owner;
	if (abi_type_token_span_is_template_id(tokens, begin, colon))
		out += "E";
	out += abi_source_name(tokens[member].source);
	return true;
}

bool abi_find_matching_angle_close(const vector<Token>& tokens,
                                   size_t open,
                                   size_t end,
                                   size_t& close)
{
	if (!abi_token_is_simple(tokens, open, OP_LT))
		return false;
	int angle = 0;
	for (size_t i = open; i < end; ++i)
	{
		if (tokens[i].kind != posttoken::TokenKind::Simple)
			continue;
		if (tokens[i].type == OP_LT)
			++angle;
		else if (tokens[i].type == OP_GT)
		{
			--angle;
			if (angle == 0)
			{
				close = i;
				return true;
			}
		}
	}
	return false;
}

string abi_cast_operator_code(ETokenType type)
{
	if (type == KW_STATIC_CAST)
		return "sc";
	if (type == KW_CONST_CAST)
		return "cc";
	if (type == KW_REINTERPET_CAST)
		return "rc";
	if (type == KW_DYNAMIC_CAST)
		return "dc";
	return "";
}

string abi_cast_target_type_with_substitutions(const vector<Token>& tokens,
                                               size_t begin,
                                               size_t end,
                                               AbiSubstitutionContext& ctx)
{
	abi_trim_wrapping_parens(tokens, begin, end);
	if (begin + 2 == end &&
	    (abi_token_is_simple(tokens, end - 1, OP_AMP) ||
	     abi_token_is_simple(tokens, end - 1, OP_LAND)) &&
	    tokens[begin].kind == posttoken::TokenKind::Identifier)
	{
		map<string, size_t>::const_iterator found =
			ctx.template_parameters.find(tokens[begin].source);
		if (found != ctx.template_parameters.end())
		{
			string encoded = found->second == 0
				? string("T_")
				: string("T") + to_string(found->second - 1) + "_";
			return abi_use_or_add_substitution(ctx, encoded);
		}
	}
	return abi_encode_type_tokens_with_substitutions(tokens, begin, end, ctx);
}

string abi_cast_expression_with_substitutions(const vector<Token>& tokens,
                                              size_t begin,
                                              size_t end,
                                              AbiSubstitutionContext& ctx)
{
	if (end <= begin + 5 ||
	    tokens[begin].kind != posttoken::TokenKind::Simple)
		return "";
	string code = abi_cast_operator_code(tokens[begin].type);
	if (code.empty() || !abi_token_is_simple(tokens, begin + 1, OP_LT))
		return "";
	size_t close = 0;
	if (!abi_find_matching_angle_close(tokens, begin + 1, end, close) ||
	    close + 3 > end ||
	    !abi_token_is_simple(tokens, close + 1, OP_LPAREN) ||
	    !abi_token_is_simple(tokens, end - 1, OP_RPAREN))
		return "";
	string type = abi_cast_target_type_with_substitutions(
		tokens, begin + 2, close, ctx);
	string expr = abi_dependent_expression_with_substitutions(
		tokens, close + 2, end - 1, ctx);
	return type.empty() || expr.empty() ? string("") : code + type + expr;
}

bool abi_binary_group_expression_with_substitutions(
	const vector<Token>& tokens,
	size_t begin,
	size_t end,
	const ETokenType* group,
	size_t group_size,
	AbiSubstitutionContext& ctx,
	string& out)
{
	vector<ETokenType> ops(group, group + group_size);
	size_t op = 0;
	if (!abi_find_top_level_operator(tokens, begin, end, ops, op))
		return false;
	string left = abi_dependent_expression_with_substitutions(
		tokens, begin, op, ctx);
	string right = abi_dependent_expression_with_substitutions(
		tokens, op + 1, end, ctx);
	string code = abi_binary_operator_code(tokens[op].type);
	out = !left.empty() && !right.empty() && !code.empty()
		? code + left + right : string("");
	return true;
}

bool abi_binary_expression_with_substitutions(const vector<Token>& tokens,
                                              size_t begin,
                                              size_t end,
                                              AbiSubstitutionContext& ctx,
                                              string& out)
{
	static const ETokenType comma_ops[] = { OP_COMMA };
	static const ETokenType lor_ops[] = { OP_LOR };
	static const ETokenType land_ops[] = { OP_LAND };
	static const ETokenType equality_ops[] = { OP_EQ, OP_NE };
	static const ETokenType relational_ops[] = { OP_LT, OP_GT, OP_LE, OP_GE };
	static const ETokenType shift_ops[] = { OP_LSHIFT, OP_RSHIFT };
	static const ETokenType additive_ops[] = { OP_PLUS, OP_MINUS };
	static const ETokenType multiplicative_ops[] = { OP_STAR, OP_DIV, OP_MOD };
	static const ETokenType bit_and_ops[] = { OP_AMP };
	static const ETokenType bit_xor_ops[] = { OP_XOR };
	static const ETokenType bit_or_ops[] = { OP_BOR };
	const ETokenType* groups[] = {
		comma_ops, lor_ops, land_ops, bit_or_ops, bit_xor_ops,
		bit_and_ops, equality_ops, relational_ops, shift_ops,
		additive_ops, multiplicative_ops
	};
	const size_t group_sizes[] = { 1, 1, 1, 1, 1, 1, 2, 4, 2, 2, 3 };
	for (size_t g = 0; g < sizeof(groups) / sizeof(groups[0]); ++g)
		if (abi_binary_group_expression_with_substitutions(
			    tokens, begin, end, groups[g], group_sizes[g], ctx, out))
			return true;
	return false;
}

bool abi_member_expression_with_substitutions(const vector<Token>& tokens,
                                              size_t begin,
                                              size_t end,
                                              AbiSubstitutionContext& ctx,
                                              string& out)
{
	size_t member_op = 0;
	if (!abi_find_top_level_member_operator(tokens, begin, end, member_op) ||
	    member_op + 1 >= end ||
	    tokens[member_op + 1].kind != posttoken::TokenKind::Identifier)
		return false;
	string object = abi_dependent_expression_with_substitutions(
		tokens, begin, member_op, ctx);
	out = object.empty()
		? string("")
		: string(tokens[member_op].type == OP_ARROW ? "pt" : "dt") +
		  object + abi_source_name(tokens[member_op + 1].source);
	return true;
}

string abi_leaf_expression_with_substitutions(const vector<Token>& tokens,
                                              size_t begin,
                                              size_t end,
                                              AbiSubstitutionContext& ctx)
{
	if (end != begin + 1)
		return "";
	string literal = abi_literal_expression(tokens[begin]);
	if (!literal.empty())
		return literal;
	if (tokens[begin].kind != posttoken::TokenKind::Identifier)
		return "";
	string param = abi_function_parameter_expression(tokens[begin].source, ctx);
	if (!param.empty())
		return param;
	return abi_template_parameter_expression(tokens[begin].source,
	                                        ctx.template_parameters);
}

string abi_dependent_expression_with_substitutions(
	const vector<Token>& tokens,
	size_t begin,
	size_t end,
	AbiSubstitutionContext& ctx)
{
	if (end > tokens.size() || begin >= end)
		return "";
	abi_trim_wrapping_parens(tokens, begin, end);
	if (begin >= end)
		return "";
	if (abi_token_is_simple(tokens, begin, OP_STAR) ||
	    abi_token_is_simple(tokens, begin, OP_AMP) ||
	    abi_token_is_simple(tokens, begin, OP_PLUS) ||
	    abi_token_is_simple(tokens, begin, OP_MINUS))
	{
		string inner = abi_dependent_expression_with_substitutions(
			tokens, begin + 1, end, ctx);
		if (inner.empty())
			return "";
		if (abi_token_is_simple(tokens, begin, OP_STAR))
			return "de" + inner;
		if (abi_token_is_simple(tokens, begin, OP_AMP))
			return "ad" + inner;
		return abi_token_is_simple(tokens, begin, OP_PLUS)
			? string("ps") + inner : string("ng") + inner;
	}
	string out = abi_template_id_expression_with_substitutions(
		tokens, begin, end, ctx);
	if (!out.empty())
		return out;
	if (abi_qualified_member_expression_with_substitutions(
		    tokens, begin, end, ctx, out))
		return out;
	out = abi_cast_expression_with_substitutions(tokens, begin, end, ctx);
	if (!out.empty())
		return out;
	size_t call_open = 0;
	if (abi_find_call_open(tokens, begin, end, call_open) &&
	    call_open > begin + 2 &&
	    tokens[begin].kind == posttoken::TokenKind::Identifier &&
	    abi_token_is_simple(tokens, begin + 1, OP_LT) &&
	    abi_token_is_simple(tokens, call_open - 1, OP_GT))
		return abi_call_expression_with_substitutions(
			tokens, begin, call_open, end, ctx);
	size_t qualified_colon = 0;
	if (abi_find_call_open(tokens, begin, end, call_open) &&
	    abi_find_top_level_colon2(tokens, begin, call_open, qualified_colon))
		return abi_call_expression_with_substitutions(
			tokens, begin, call_open, end, ctx);
	if (abi_binary_expression_with_substitutions(tokens, begin, end, ctx, out))
		return out;
	if (abi_token_is_simple(tokens, begin, OP_LNOT))
	{
		string inner = abi_dependent_expression_with_substitutions(
			tokens, begin + 1, end, ctx);
		return inner.empty() ? string("") : string("nt") + inner;
	}
	if (begin + 3 == end &&
	    abi_token_is_simple(tokens, begin + 1, OP_LPAREN) &&
	    abi_token_is_simple(tokens, begin + 2, OP_RPAREN))
	{
		AbiTokenType cast_type =
			abi_encode_type_tokens(tokens, begin, begin + 1,
			                       ctx.template_parameters);
		if (!cast_type.encoded.empty())
			return "cv" + cast_type.encoded + "_E";
	}
	if (abi_find_call_open(tokens, begin, end, call_open))
		return abi_call_expression_with_substitutions(
			tokens, begin, call_open, end, ctx);
	if (abi_member_expression_with_substitutions(tokens, begin, end, ctx, out))
		return out;
	return abi_leaf_expression_with_substitutions(tokens, begin, end, ctx);
}

}  // namespace

string abi_dependent_decltype_type_with_substitutions(
	TypePtr type,
	AbiSubstitutionContext& ctx)
{
	if (type.get() == NULL || type->name.compare(0, 9, "decltype(") != 0)
		return "";
	vector<Token> tokens;
	if (!collect_replay_tokens(type->name, tokens) || tokens.size() < 4)
		return "";
	size_t end = tokens.size();
	while (end > 0 && tokens[end - 1].kind == posttoken::TokenKind::EndOfFile)
		--end;
	if (end < 4 ||
	    !abi_token_is_simple(tokens, 0, KW_DECLTYPE) ||
	    !abi_token_is_simple(tokens, 1, OP_LPAREN) ||
	    !abi_token_is_simple(tokens, end - 1, OP_RPAREN))
		return "";
	string expression = abi_dependent_expression_with_substitutions(
		tokens, 2, end - 1, ctx);
	return expression.empty() ? string("") : string("DT") + expression + "E";
}

}  // namespace internal
}  // namespace pa12
