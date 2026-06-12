#include "pa12_templates_function_abi_internal.h"
#include "pa12_templates_instance_support.h"
#include "pa12_types_support.h"

#include <algorithm>
#include <functional>
#include <stdexcept>

using namespace std;

namespace pa12 {
namespace internal {

string abi_source_name(const string& name)
{
	string unqualified = name;
	size_t pos = unqualified.rfind("::");
	if (pos != string::npos)
		unqualified = unqualified.substr(pos + 2);
	if (unqualified == "operator[]")
		return "ix";
	if (unqualified == "operator=")
		return "aS";
	if (unqualified == "operator+")
		return "pl";
	if (unqualified == "operator-")
		return "mi";
	if (unqualified == "operator*")
		return "ml";
	if (unqualified == "operator/")
		return "dv";
	if (unqualified == "operator%")
		return "rm";
	if (unqualified == "operator&")
		return "ad";
	if (unqualified == "operator&=")
		return "aN";
	if (unqualified == "operator|")
		return "or";
	if (unqualified == "operator^")
		return "eo";
	if (unqualified == "operator<<")
		return "ls";
	if (unqualified == "operator>>")
		return "rs";
	if (unqualified == "operator==")
		return "eq";
	if (unqualified == "operator!=")
		return "ne";
	if (unqualified == "operator<")
		return "lt";
	if (unqualified == "operator>")
		return "gt";
	if (unqualified == "operator<=")
		return "le";
	if (unqualified == "operator>=")
		return "ge";
	if (unqualified == "operator()")
		return "cl";
	if (unqualified == "operator," || unqualified == "operator ,")
		return "cm";
	string safe;
	static const char hex[] = "0123456789ABCDEF";
	for (size_t i = 0; i < unqualified.size(); ++i)
	{
		unsigned char c =
			static_cast<unsigned char>(unqualified[i]);
		if ((c >= 'A' && c <= 'Z') ||
		    (c >= 'a' && c <= 'z') ||
		    (c >= '0' && c <= '9') ||
		    c == '_')
			safe += static_cast<char>(c);
		else
		{
			safe += '_';
			safe += hex[(c >> 4) & 0xf];
			safe += hex[c & 0xf];
		}
	}
	if (safe.empty())
		safe = "v";
	return to_string(safe.size()) + safe;
}

string abi_binding_source_name(const Binding* binding)
{
	if (binding == NULL)
		return abi_source_name("v");
	string name = binding->name;
	if (name == "operator+" || name == "operator-" ||
	    name == "operator*" || name == "operator&")
	{
		size_t first_param =
			binding->owner != NULL &&
			binding->owner->kind == ScopeKind::Class &&
			!binding->is_static_member ? 1 : 0;
		size_t arity =
			binding->type.get() != NULL &&
			binding->type->kind == pa11::TypeKind::Function &&
			binding->type->parameters.size() >= first_param
			? binding->type->parameters.size() - first_param : 0;
		if (arity <= 1)
		{
			if (name == "operator+")
				return "ps";
			if (name == "operator-")
				return "ng";
			if (name == "operator*")
				return "de";
			if (name == "operator&")
				return "ad";
		}
		if (name == "operator&")
			return "an";
	}
	if (name == "operator++")
		return "pp";
	if (name == "operator--")
		return "mm";
	return abi_source_name(name);
}

string abi_fundamental_type(EFundamentalType type)
{
	switch (type)
	{
	case FT_VOID: return "v";
	case FT_BOOL: return "b";
	case FT_CHAR: return "c";
	case FT_SIGNED_CHAR: return "a";
	case FT_UNSIGNED_CHAR: return "h";
	case FT_SHORT_INT: return "s";
	case FT_UNSIGNED_SHORT_INT: return "t";
	case FT_INT: return "i";
	case FT_UNSIGNED_INT: return "j";
	case FT_LONG_INT: return "l";
	case FT_UNSIGNED_LONG_INT: return "m";
	case FT_LONG_LONG_INT: return "x";
	case FT_UNSIGNED_LONG_LONG_INT: return "y";
	case FT_INT128: return "n";
	case FT_UNSIGNED_INT128: return "o";
	case FT_FLOAT: return "f";
	case FT_DOUBLE: return "d";
	default: return "i";
	}
}

string abi_type(TypePtr type,
                const map<string, size_t>& template_parameters,
                const vector<Token>* expression_tokens = NULL);
string abi_record_type(TypePtr type,
                       const map<string, size_t>& template_parameters,
                       const vector<Token>* expression_tokens = NULL,
                       bool include_namespace = true);
string abi_binding_symbol_with_substitutions(
	const Binding* binding,
	const map<string, size_t>& template_parameters);
string abi_function_template_specialization_symbol_with_substitutions(
	TemplateDeclaration* declaration,
	const vector<TemplateArgument>& full_args,
	Binding* binding,
	const vector<Token>* expression_tokens);

string abi_encode_name_path(const vector<string>& scopes,
                            const string& name)
{
	if (scopes.empty())
		return abi_source_name(name);
	string out = "N";
	for (size_t i = 0; i < scopes.size(); ++i)
		out += abi_source_name(scopes[i]);
	out += abi_source_name(name);
	out += "E";
	return out;
}

string abi_encode_binding_name(
	const Binding* binding,
	const map<string, size_t>& template_parameters)
{
	vector<string> reversed;
	for (Scope* scope = binding != NULL ? binding->owner : NULL;
	     scope != NULL;
	     scope = scope->parent)
	{
		if (scope->kind == ScopeKind::Namespace &&
		    !scope->name.empty())
		{
			string name = scope->name == "<unnamed>"
				? string("_GLOBAL__N_1") : scope->name;
			reversed.push_back(abi_source_name(name));
		}
		else if (scope->kind == ScopeKind::Class &&
		         !scope->name.empty() &&
		         scope->name != "<unnamed>")
		{
			TypePtr record = pa11::record_type_for_scope(scope);
			TypePtr bare = record.get() != NULL
				? pa11::strip_cv(record) : TypePtr();
			if (bare.get() != NULL && bare->is_template_specialization)
				reversed.push_back(abi_record_type(bare,
				                                   template_parameters,
				                                   NULL,
				                                   false));
			else
				reversed.push_back(abi_source_name(scope->name));
		}
	}
	string leaf = abi_source_name(binding != NULL ? binding->name : string("v"));
	if (reversed.empty())
		return leaf;
	string out = "N";
	if (binding != NULL &&
	    binding->kind == BindingKind::Function &&
	    binding->owner != NULL &&
	    binding->owner->kind == ScopeKind::Class &&
	    !binding->is_static_member &&
	    binding->type.get() != NULL &&
	    binding->type->kind == pa11::TypeKind::Function)
	{
		bool const_member = (binding->type->cv & pa11::CV_CONST) != 0;
		bool volatile_member = (binding->type->cv & pa11::CV_VOLATILE) != 0;
		if (!binding->type->parameters.empty() &&
		    pa11::strip_cv(binding->type->parameters[0])->kind ==
			    pa11::TypeKind::Pointer)
		{
			TypePtr self =
				pa11::strip_cv(binding->type->parameters[0])->base;
			const_member = const_member || pa11::type_has_const(self);
		}
		if (const_member)
			out += "K";
		if (volatile_member)
			out += "V";
	}
	for (size_t i = reversed.size(); i > 0; --i)
		out += reversed[i - 1];
	out += leaf;
	out += "E";
	return out;
}

string abi_binding_symbol(const Binding* binding,
                          const map<string, size_t>& template_parameters)
{
	return abi_binding_symbol_with_substitutions(binding,
	                                             template_parameters);
}

string abi_encoded_stable_value_name(const string& name)
{
	vector<string> parts;
	size_t begin = 0;
	while (begin <= name.size())
	{
		size_t pos = name.find("::", begin);
		string part = name.substr(begin,
		                          pos == string::npos
		                          ? string::npos : pos - begin);
		if (!part.empty())
			parts.push_back(part);
		if (pos == string::npos)
			break;
		begin = pos + 2;
	}
	if (parts.empty())
		return "0v";
	string leaf = parts.back();
	parts.pop_back();
	return abi_encode_name_path(parts, leaf);
}

vector<string> abi_split_qualified_name(const string& name)
{
	vector<string> parts;
	size_t begin = 0;
	while (begin <= name.size())
	{
		size_t pos = name.find("::", begin);
		string part = name.substr(begin,
		                          pos == string::npos
		                          ? string::npos : pos - begin);
		if (!part.empty())
			parts.push_back(part);
		if (pos == string::npos)
			break;
		begin = pos + 2;
	}
	return parts;
}

string abi_template_name(const string& name)
{
	vector<string> parts = abi_split_qualified_name(name);
	if (parts.empty())
		return abi_source_name("v");
	string leaf = parts.back();
	parts.pop_back();
	return abi_encode_name_path(parts, leaf);
}

string abi_unresolved_name_path(const string& name)
{
	vector<string> parts = abi_split_qualified_name(name);
	string out;
	for (size_t i = 0; i < parts.size(); ++i)
		out += abi_source_name(parts[i]);
	return out;
}

string abi_template_parameter_expression(
	const string& name,
	const map<string, size_t>& template_parameters)
{
	map<string, size_t>::const_iterator found =
		template_parameters.find(name);
	if (found == template_parameters.end())
		return "";
	return found->second == 0
		? string("T_")
		: string("T") + to_string(found->second - 1) + "_";
}

bool abi_token_is_simple(const vector<Token>& tokens,
                         size_t pos,
                         ETokenType type)
{
	return pos < tokens.size() &&
	       tokens[pos].kind == posttoken::TokenKind::Simple &&
	       tokens[pos].type == type;
}

bool abi_matching_close_token(ETokenType open, ETokenType& close)
{
	if (open == OP_LPAREN)
	{
		close = OP_RPAREN;
		return true;
	}
	if (open == OP_LSQUARE)
	{
		close = OP_RSQUARE;
		return true;
	}
	if (open == OP_LBRACE)
	{
		close = OP_RBRACE;
		return true;
	}
	return false;
}

bool abi_span_is_wrapped(const vector<Token>& tokens, size_t begin, size_t end)
{
	if (end <= begin + 1 ||
	    tokens[begin].kind != posttoken::TokenKind::Simple)
		return false;
	ETokenType close;
	if (!abi_matching_close_token(tokens[begin].type, close) ||
	    !abi_token_is_simple(tokens, end - 1, close))
		return false;
	int depth = 0;
	for (size_t i = begin; i < end; ++i)
	{
		if (tokens[i].kind != posttoken::TokenKind::Simple)
			continue;
		if (tokens[i].type == tokens[begin].type)
			++depth;
		else if (tokens[i].type == close)
		{
			--depth;
			if (depth == 0)
				return i == end - 1;
		}
	}
	return false;
}

void abi_trim_wrapping_parens(const vector<Token>& tokens,
                              size_t& begin,
                              size_t& end)
{
	while (abi_span_is_wrapped(tokens, begin, end))
	{
		++begin;
		--end;
	}
}

bool abi_find_top_level_operator(const vector<Token>& tokens,
                                 size_t begin,
                                 size_t end,
                                 const vector<ETokenType>& operators,
                                 size_t& out)
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
		         find(operators.begin(), operators.end(), type) !=
				 operators.end())
		{
			out = i;
			found = true;
		}
	}
	return found;
}

string abi_binary_operator_code(ETokenType type)
{
	switch (type)
	{
	case OP_COMMA: return "cm";
	case OP_LOR: return "oo";
	case OP_LAND: return "aa";
	case OP_EQ: return "eq";
	case OP_NE: return "ne";
	case OP_LT: return "lt";
	case OP_GT: return "gt";
	case OP_LE: return "le";
	case OP_GE: return "ge";
	case OP_LSHIFT: return "ls";
	case OP_RSHIFT: return "rs";
	case OP_PLUS: return "pl";
	case OP_MINUS: return "mi";
	case OP_STAR: return "ml";
	case OP_DIV: return "dv";
	case OP_MOD: return "rm";
	case OP_AMP: return "an";
	case OP_XOR: return "eo";
	case OP_BOR: return "or";
	default: return "";
	}
}


bool abi_type_keyword(const Token& token, ETokenType type)
{
	return token.kind == posttoken::TokenKind::Simple && token.type == type;
}

AbiTokenType abi_encode_fundamental_type_tokens(const vector<Token>& tokens,
                                                size_t begin,
                                                size_t end)
{
	AbiTokenType out;
	bool saw_signed = false;
	bool saw_unsigned = false;
	bool saw_short = false;
	size_t longs = 0;
	bool saw_char = false;
	bool saw_bool = false;
	bool saw_void = false;
	bool saw_float = false;
	bool saw_double = false;
	for (size_t i = begin; i < end; ++i)
	{
		if (tokens[i].kind != posttoken::TokenKind::Simple)
			return out;
		if (abi_type_keyword(tokens[i], KW_SIGNED))
			saw_signed = true;
		else if (abi_type_keyword(tokens[i], KW_UNSIGNED))
			saw_unsigned = true;
		else if (abi_type_keyword(tokens[i], KW_SHORT))
			saw_short = true;
		else if (abi_type_keyword(tokens[i], KW_LONG))
			++longs;
		else if (abi_type_keyword(tokens[i], KW_INT))
			continue;
		else if (abi_type_keyword(tokens[i], KW_CHAR))
			saw_char = true;
		else if (abi_type_keyword(tokens[i], KW_BOOL))
			saw_bool = true;
		else if (abi_type_keyword(tokens[i], KW_VOID))
			saw_void = true;
		else if (abi_type_keyword(tokens[i], KW_FLOAT))
			saw_float = true;
		else if (abi_type_keyword(tokens[i], KW_DOUBLE))
			saw_double = true;
		else
			return out;
	}
	EFundamentalType type = FT_INT;
	if (saw_void)
		type = FT_VOID;
	else if (saw_bool)
		type = FT_BOOL;
	else if (saw_float)
		type = FT_FLOAT;
	else if (saw_double && longs != 0)
		type = FT_LONG_DOUBLE;
	else if (saw_double)
		type = FT_DOUBLE;
	else if (saw_char && saw_unsigned)
		type = FT_UNSIGNED_CHAR;
	else if (saw_char && saw_signed)
		type = FT_SIGNED_CHAR;
	else if (saw_char)
		type = FT_CHAR;
	else if (saw_short && saw_unsigned)
		type = FT_UNSIGNED_SHORT_INT;
	else if (saw_short)
		type = FT_SHORT_INT;
	else if (longs >= 2 && saw_unsigned)
		type = FT_UNSIGNED_LONG_LONG_INT;
	else if (longs >= 2)
		type = FT_LONG_LONG_INT;
	else if (longs == 1 && saw_unsigned)
		type = FT_UNSIGNED_LONG_INT;
	else if (longs == 1)
		type = FT_LONG_INT;
	else if (saw_unsigned)
		type = FT_UNSIGNED_INT;
	out.encoded = abi_fundamental_type(type);
	out.concrete = true;
	out.concrete_type = pa11::make_fundamental(type);
	return out;
}

AbiTokenType abi_encode_type_tokens(const vector<Token>& tokens,
                                    size_t begin,
                                    size_t end,
                                    const map<string, size_t>& template_parameters)
{
	abi_trim_wrapping_parens(tokens, begin, end);
	AbiTokenType out;
	while (begin < end && abi_token_is_simple(tokens, begin, KW_TYPENAME))
		++begin;
	bool leading_const = false;
	bool leading_volatile = false;
	while (begin < end &&
	       (abi_token_is_simple(tokens, begin, KW_CONST) ||
	        abi_token_is_simple(tokens, begin, KW_VOLATILE)))
	{
		leading_const = leading_const ||
			abi_token_is_simple(tokens, begin, KW_CONST);
		leading_volatile = leading_volatile ||
			abi_token_is_simple(tokens, begin, KW_VOLATILE);
		++begin;
	}
	if (begin >= end)
		return out;
	if (abi_token_is_simple(tokens, end - 1, OP_AMP))
	{
		AbiTokenType base =
			abi_encode_type_tokens(tokens, begin, end - 1,
			                       template_parameters);
		if (base.encoded.empty())
			return out;
		base.encoded = "R" + base.encoded;
		return base;
	}
	if (abi_token_is_simple(tokens, end - 1, OP_LAND))
	{
		AbiTokenType base =
			abi_encode_type_tokens(tokens, begin, end - 1,
			                       template_parameters);
		if (base.encoded.empty())
			return out;
		base.encoded = "O" + base.encoded;
		return base;
	}
	if (abi_token_is_simple(tokens, end - 1, OP_STAR))
	{
		AbiTokenType base =
			abi_encode_type_tokens(tokens, begin, end - 1,
			                       template_parameters);
		if (base.encoded.empty())
			return out;
		base.encoded = "P" + base.encoded;
		return base;
	}
	bool trailing_const = false;
	bool trailing_volatile = false;
	while (begin < end &&
	       (abi_token_is_simple(tokens, end - 1, KW_CONST) ||
	        abi_token_is_simple(tokens, end - 1, KW_VOLATILE)))
	{
		trailing_const = trailing_const ||
			abi_token_is_simple(tokens, end - 1, KW_CONST);
		trailing_volatile = trailing_volatile ||
			abi_token_is_simple(tokens, end - 1, KW_VOLATILE);
		--end;
	}
	if (begin >= end)
		return out;
	if (end == begin + 1 &&
	    tokens[begin].kind == posttoken::TokenKind::Identifier)
	{
		map<string, size_t>::const_iterator found =
			template_parameters.find(tokens[begin].source);
		if (found != template_parameters.end())
		{
			out.encoded = found->second == 0
				? string("T_")
				: string("T") + to_string(found->second - 1) + "_";
			out.dependent = true;
		}
		else
		{
			out.encoded = abi_source_name(tokens[begin].source);
			out.concrete = true;
		}
	}
	else
		out = abi_encode_fundamental_type_tokens(tokens, begin, end);
	if (!out.encoded.empty() && (leading_const || trailing_const))
		out.encoded = "K" + out.encoded;
	if (!out.encoded.empty() && (leading_volatile || trailing_volatile))
		out.encoded = "V" + out.encoded;
	return out;
}

string abi_literal_expression(const Token& token)
{
	if (token.kind == posttoken::TokenKind::Simple &&
	    token.type == KW_TRUE)
		return "Lb1E";
	if (token.kind == posttoken::TokenKind::Simple &&
	    token.type == KW_FALSE)
		return "Lb0E";
	if (token.kind != posttoken::TokenKind::Literal)
		return "";
	IntegerLiteralInfo info;
	if (!AnalyzeIntegerLiteral(token.source, info) || info.user_defined)
		return "";
	return "L" + abi_fundamental_type(info.type) +
	       to_string(info.value) + "E";
}

string abi_template_value_expression(
	const vector<Token>& tokens,
	size_t begin,
	size_t end,
	const map<string, size_t>& template_parameters)
{
	if (end > tokens.size() || begin >= end)
		return "";
	abi_trim_wrapping_parens(tokens, begin, end);
	if (begin >= end)
		return "";
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
	const size_t group_sizes[] = {
		1, 1, 1, 1, 1, 1, 2, 4, 2, 2, 3
	};
	for (size_t g = 0; g < sizeof(groups) / sizeof(groups[0]); ++g)
	{
		vector<ETokenType> ops(groups[g], groups[g] + group_sizes[g]);
		size_t op = 0;
		if (!abi_find_top_level_operator(tokens, begin, end, ops, op))
			continue;
		string left = abi_template_value_expression(tokens, begin, op,
		                                            template_parameters);
		string right = abi_template_value_expression(tokens, op + 1, end,
		                                             template_parameters);
		string code = abi_binary_operator_code(tokens[op].type);
		if (!left.empty() && !right.empty() && !code.empty())
			return code + left + right;
		return "";
	}
	if (abi_token_is_simple(tokens, begin, OP_LNOT))
	{
		string inner = abi_template_value_expression(tokens, begin + 1, end,
		                                             template_parameters);
		return inner.empty() ? string("") : string("nt") + inner;
	}
	if (abi_token_is_simple(tokens, begin, KW_SIZEOF) &&
	    begin + 4 == end &&
	    abi_token_is_simple(tokens, begin + 1, OP_DOTS) &&
	    abi_token_is_simple(tokens, begin + 2, OP_LPAREN) &&
	    abi_token_is_simple(tokens, end - 1, OP_RPAREN) &&
	    tokens[begin + 3].kind == posttoken::TokenKind::Identifier)
	{
		AbiTokenType pack =
			abi_encode_type_tokens(tokens, begin + 3, begin + 4,
			                       template_parameters);
		return pack.encoded.empty() ? string("") : string("sZ") + pack.encoded;
	}
	if ((abi_token_is_simple(tokens, begin, KW_SIZEOF) ||
	     abi_token_is_simple(tokens, begin, KW_ALIGNOF)) &&
	    begin + 2 < end &&
	    abi_token_is_simple(tokens, begin + 1, OP_LPAREN) &&
	    abi_token_is_simple(tokens, end - 1, OP_RPAREN))
	{
		AbiTokenType operand =
			abi_encode_type_tokens(tokens, begin + 2, end - 1,
			                       template_parameters);
		if (operand.encoded.empty())
			return "";
		if (operand.dependent)
			return string(abi_token_is_simple(tokens, begin, KW_SIZEOF)
			              ? "st" : "at") + operand.encoded;
		if (operand.concrete && operand.concrete_type.get() != NULL)
		{
			uint64_t value = abi_token_is_simple(tokens, begin, KW_SIZEOF)
				? pa11::type_size(operand.concrete_type)
				: pa11::type_align(operand.concrete_type);
			return "L" + abi_fundamental_type(FT_UNSIGNED_LONG_INT) +
			       to_string(value) + "E";
		}
	}
	if (abi_token_is_simple(tokens, begin, KW_SIZEOF) && begin + 1 < end)
	{
		string inner = abi_template_value_expression(tokens, begin + 1, end,
		                                             template_parameters);
		return inner.empty() ? string("") : string("sz") + inner;
	}
	if (end == begin + 1)
	{
		string literal = abi_literal_expression(tokens[begin]);
		if (!literal.empty())
			return literal;
		if (tokens[begin].kind == posttoken::TokenKind::Identifier)
		{
			map<string, size_t>::const_iterator found =
				template_parameters.find(tokens[begin].source);
			if (found != template_parameters.end())
				return found->second == 0
					? string("T_")
					: string("T") + to_string(found->second - 1) + "_";
			return abi_source_name(tokens[begin].source);
		}
	}
	return "";
}

string abi_template_instance_argument(
	const pa11::TemplateInstanceArgument& arg,
	const map<string, size_t>& template_parameters,
	const vector<Token>* expression_tokens = NULL)
{
	if (arg.kind == pa11::TemplateInstanceArgumentKind::Type)
		return abi_type(arg.type, template_parameters, expression_tokens);
	if (arg.kind == pa11::TemplateInstanceArgumentKind::Value)
	{
		if (arg.dependent)
		{
			if (!arg.value_owner_template_name.empty() &&
			    !arg.value_member_name.empty())
			{
				string owner_name = arg.value_owner_template_name;
				size_t owner_args = owner_name.find('<');
				if (owner_args != string::npos)
					owner_name = owner_name.substr(0, owner_args);
				string out = "Xsr" + abi_unresolved_name_path(owner_name);
				if (!arg.value_owner_template_arguments.empty())
				{
					out += "I";
					for (size_t i = 0;
					     i < arg.value_owner_template_arguments.size();
					     ++i)
						out += abi_template_instance_argument(
							arg.value_owner_template_arguments[i],
							template_parameters,
							expression_tokens);
					out += "E";
					out += "E";
				}
				out += abi_source_name(arg.value_member_name) + "E";
				if (arg.value_negated)
					out = "Xnt" + out.substr(1);
				return out;
			}
			if (expression_tokens != NULL &&
			    arg.value_expr_end > arg.value_expr_begin)
			{
				string expression = abi_template_value_expression(
					*expression_tokens,
					arg.value_expr_begin,
					arg.value_expr_end,
					template_parameters);
				if (!expression.empty())
					return "X" + expression + "E";
			}
			if (!arg.value_name.empty())
			{
				string parameter_expr =
					abi_template_parameter_expression(arg.value_name,
					                                  template_parameters);
				if (!parameter_expr.empty())
					return "X" + parameter_expr + "E";
				return "X" + abi_encoded_stable_value_name(arg.value_name) +
				       "E";
			}
		}
		if (!arg.value_name.empty())
			return "L" + abi_type(arg.type,
			                      template_parameters,
			                      expression_tokens) +
			       abi_encoded_stable_value_name(arg.value_name) + "E";
		return "L" + abi_type(arg.type,
		                      template_parameters,
		                      expression_tokens) +
		       to_string(arg.value) + "E";
	}
	if (arg.kind == pa11::TemplateInstanceArgumentKind::Pack)
	{
		string out = "J";
		for (size_t i = 0; i < arg.pack.size(); ++i)
			out += abi_template_instance_argument(arg.pack[i],
			                                     template_parameters,
			                                     expression_tokens);
		out += "E";
		return out;
	}
	return abi_template_name(arg.template_name);
}

string abi_dependent_typename_type(
	TypePtr type,
	const map<string, size_t>& template_parameters,
	const vector<Token>* expression_tokens,
	bool include_typename_marker)
{
	vector<string> parts = abi_split_qualified_name(type->name);
	if (parts.empty())
		return abi_source_name(type->name);
		if (!type->dependent_typename_qualified &&
		    type->dependent_typename_template_id)
		{
			string root = type->template_primary_name.empty()
				? parts[0] : type->template_primary_name;
		size_t template_pos = root.find('<');
		if (template_pos != string::npos)
			root = root.substr(0, template_pos);
		if (internal_type_transform_name(root))
		{
			string out = include_typename_marker ? "Tn" : "";
			out += "u" + abi_source_name(root);
			vector<pa11::TemplateInstanceArgument> arguments =
				!type->dependent_typename_template_argument_lists.empty()
				? type->dependent_typename_template_argument_lists[0]
				: type->template_arguments;
			if (!arguments.empty())
			{
				out += "I";
				for (size_t i = 0; i < arguments.size(); ++i)
					out += abi_template_instance_argument(arguments[i],
					                                      template_parameters,
					                                      expression_tokens);
				out += "E";
			}
				return out;
			}
		}
		if (!type->dependent_typename_qualified &&
		    type->dependent_typename_template_id)
		{
			string root = type->template_primary_name.empty()
				? parts[0] : type->template_primary_name;
			size_t template_pos = root.find('<');
			if (template_pos != string::npos)
				root = root.substr(0, template_pos);
			if (root == "enable_if_t")
			{
				vector<pa11::TemplateInstanceArgument> arguments =
					!type->dependent_typename_template_argument_lists.empty()
					? type->dependent_typename_template_argument_lists[0]
					: type->template_arguments;
				string out = include_typename_marker ? "TnN" : "N";
				out += abi_source_name("enable_if");
				if (!arguments.empty())
				{
					out += "I";
					for (size_t i = 0; i < arguments.size(); ++i)
						out += abi_template_instance_argument(arguments[i],
						                                      template_parameters,
						                                      expression_tokens);
					out += "E";
				}
				out += abi_source_name("type") + "E";
				return out;
			}
		}
		string out;
	if (type->dependent_typename_qualified)
		out = include_typename_marker ? "TnN" : "N";
	else
		out = include_typename_marker ? "Tn" : "";
	size_t list_index = 0;
	for (size_t i = 0; i < parts.size(); ++i)
		{
			string part = parts[i];
			size_t template_pos = part.find('<');
			bool has_template_id = template_pos != string::npos;
			bool implicit_template_id =
				!has_template_id &&
				i == 0 &&
				type->dependent_typename_template_id &&
				(!type->template_arguments.empty() ||
				 !type->dependent_typename_template_argument_lists.empty());
			if (has_template_id)
				part = part.substr(0, template_pos);
			out += abi_source_name(part);
			vector<pa11::TemplateInstanceArgument> arguments;
			if ((has_template_id || implicit_template_id) &&
			    list_index <
				    type->dependent_typename_template_argument_lists.size())
				arguments =
					type->dependent_typename_template_argument_lists[list_index++];
			else if ((has_template_id || implicit_template_id) && i == 0 &&
			         !type->template_arguments.empty())
				arguments = type->template_arguments;
		if (!arguments.empty())
		{
			out += "I";
			for (size_t j = 0; j < arguments.size(); ++j)
				out += abi_template_instance_argument(arguments[j],
				                                      template_parameters,
				                                      expression_tokens);
			out += "E";
		}
	}
	if (type->dependent_typename_qualified)
		out += "E";
	return out;
}

string abi_template_argument(const TemplateArgument& arg,
                             const map<string, size_t>& template_parameters,
                             const vector<Token>* expression_tokens = NULL)
{
	if (arg.kind == TemplateArgumentKind::Type)
		return abi_type(arg.type, template_parameters, expression_tokens);
	if (arg.kind == TemplateArgumentKind::Value)
	{
		if (arg.dependent)
		{
			if (!arg.value_owner_template_name.empty() &&
			    !arg.value_member_name.empty())
			{
				string owner_name = arg.value_owner_template_name;
				size_t owner_args = owner_name.find('<');
				if (owner_args != string::npos)
					owner_name = owner_name.substr(0, owner_args);
				string out = "Xsr" + abi_unresolved_name_path(owner_name);
				if (!arg.value_owner_template_arguments.empty())
				{
					out += "I";
					for (size_t i = 0;
					     i < arg.value_owner_template_arguments.size();
					     ++i)
						out += abi_template_instance_argument(
							arg.value_owner_template_arguments[i],
							template_parameters,
							expression_tokens);
					out += "E";
					out += "E";
				}
				out += abi_source_name(arg.value_member_name) + "E";
				if (arg.value_negated)
					out = "Xnt" + out.substr(1);
				return out;
			}
			if (expression_tokens != NULL &&
			    arg.value_expr_end > arg.value_expr_begin)
			{
				string expression = abi_template_value_expression(
					*expression_tokens,
					arg.value_expr_begin,
					arg.value_expr_end,
					template_parameters);
				if (!expression.empty())
					return "X" + expression + "E";
			}
			if (!arg.value_name.empty())
			{
				string parameter_expr =
					abi_template_parameter_expression(arg.value_name,
					                                  template_parameters);
				if (!parameter_expr.empty())
					return "X" + parameter_expr + "E";
				return "X" + abi_encoded_stable_value_name(arg.value_name) +
				       "E";
			}
		}
		if (arg.value_binding != NULL)
			return "XadL" +
			       abi_binding_symbol(arg.value_binding,
			                          template_parameters) +
			       "E";
		return "L" + abi_type(arg.type, template_parameters) +
		       to_string(arg.value) + "E";
	}
	if (arg.kind == TemplateArgumentKind::Pack)
	{
		string out = "J";
		for (size_t i = 0; i < arg.pack.size(); ++i)
			out += abi_template_argument(arg.pack[i],
			                             template_parameters,
			                             expression_tokens);
		out += "E";
		return out;
	}
	string name = arg.template_declaration != NULL
		? qualified_template_declaration_name(arg.template_declaration)
		: !arg.value_name.empty()
		  ? arg.value_name
		  : string("v");
	return abi_template_name(name);
}

bool abi_type_is_dependent_parameter(TypePtr type)
{
	if (type.get() == NULL)
		return false;
	TypePtr bare = pa11::strip_cv(type);
	if (bare->is_dependent_typename ||
	    bare->kind == pa11::TypeKind::TemplateParameter ||
	    bare->kind == pa11::TypeKind::TemplateTemplateParameter)
		return true;
	if (bare->kind == pa11::TypeKind::Pointer ||
	    bare->kind == pa11::TypeKind::LValueReference ||
	    bare->kind == pa11::TypeKind::RValueReference ||
	    bare->kind == pa11::TypeKind::Array)
		return abi_type_is_dependent_parameter(bare->base);
	if (bare->kind == pa11::TypeKind::Function)
	{
		if (abi_type_is_dependent_parameter(bare->base))
			return true;
		for (size_t i = 0; i < bare->parameters.size(); ++i)
			if (abi_type_is_dependent_parameter(bare->parameters[i]))
				return true;
	}
	if (bare->kind == pa11::TypeKind::MemberPointer)
		return abi_type_is_dependent_parameter(bare->member_class) ||
		       abi_type_is_dependent_parameter(bare->base);
	if (bare->kind == pa11::TypeKind::Record ||
	    bare->kind == pa11::TypeKind::Enum)
	{
		for (size_t i = 0; i < bare->template_arguments.size(); ++i)
			if (bare->template_arguments[i].dependent)
				return true;
	}
	return false;
}

string abi_template_argument_for_parameter(
	const TemplateParameterInfo& parameter,
	const TemplateArgument& arg,
	const map<string, size_t>& template_parameters,
	const vector<Token>* expression_tokens = NULL)
{
	if (parameter.kind == TemplateParameterKind::NonType &&
	    parameter.type.get() != NULL &&
	    abi_type_is_dependent_parameter(parameter.type))
	{
		if (arg.kind == TemplateArgumentKind::Value)
			return abi_type(parameter.type,
			                template_parameters,
			                expression_tokens) +
			       abi_template_argument(arg,
			                             template_parameters,
			                             expression_tokens);
		if (arg.kind == TemplateArgumentKind::Pack)
		{
			string out = "J";
			for (size_t i = 0; i < arg.pack.size(); ++i)
			{
				if (arg.pack[i].kind == TemplateArgumentKind::Value)
					out += abi_type(parameter.type,
					                template_parameters,
					                expression_tokens) +
					       abi_template_argument(arg.pack[i],
					                             template_parameters,
					                             expression_tokens);
				else
					out += abi_template_argument(arg.pack[i],
					                             template_parameters,
					                             expression_tokens);
			}
			out += "E";
			return out;
		}
	}
	return abi_template_argument(arg, template_parameters, expression_tokens);
}

string abi_record_type(TypePtr type,
                       const map<string, size_t>& template_parameters,
                       const vector<Token>* expression_tokens,
                       bool include_namespace)
{
	TypePtr bare = pa11::strip_cv(type);
	string name = bare->is_template_specialization &&
	              !bare->template_primary_name.empty()
		? bare->template_primary_name : bare->name;
	size_t args = name.find('<');
	if (args != string::npos)
		name = name.substr(0, args);
	string out = abi_source_name(name);
	if (bare->is_template_specialization)
	{
		out += "I";
		for (size_t i = 0; i < bare->template_arguments.size(); ++i)
			out += abi_template_instance_argument(
				bare->template_arguments[i],
				template_parameters,
				expression_tokens);
		out += "E";
	}
	if (include_namespace && bare->scope != NULL)
	{
		vector<string> reversed_namespaces;
		for (Scope* scope = bare->scope->parent;
		     scope != NULL;
		     scope = scope->parent)
		{
			if (scope->kind == ScopeKind::Namespace &&
			    !scope->name.empty())
				reversed_namespaces.push_back(
					scope->name == "<unnamed>"
					? string("_GLOBAL__N_1") : scope->name);
			else if (scope->kind == ScopeKind::Class)
				break;
		}
		if (!reversed_namespaces.empty())
		{
			string nested = "N";
			for (size_t i = reversed_namespaces.size(); i > 0; --i)
				nested += abi_source_name(reversed_namespaces[i - 1]);
			nested += out;
			nested += "E";
			return nested;
		}
	}
	return out;
}

bool template_argument_matches_instance(
	const TemplateArgument& arg,
	const pa11::TemplateInstanceArgument& instance)
{
	bool same_arg_type =
		(arg.type.get() == NULL || instance.type.get() == NULL)
		? arg.type.get() == instance.type.get()
		: pa11::same_type(arg.type, instance.type);
	if (arg.kind == TemplateArgumentKind::Type)
		return instance.kind == pa11::TemplateInstanceArgumentKind::Type &&
		       same_arg_type;
	if (arg.kind == TemplateArgumentKind::Value)
		return instance.kind == pa11::TemplateInstanceArgumentKind::Value &&
		       arg.dependent == instance.dependent &&
		       same_arg_type &&
		       (arg.dependent || arg.value == instance.value);
	if (arg.kind == TemplateArgumentKind::Template)
		return instance.kind == pa11::TemplateInstanceArgumentKind::Template &&
		       arg.template_declaration != NULL &&
		       arg.template_declaration->name == instance.template_name;
	if (instance.kind != pa11::TemplateInstanceArgumentKind::Pack ||
	    arg.pack.size() != instance.pack.size())
		return false;
	for (size_t i = 0; i < arg.pack.size(); ++i)
		if (!template_argument_matches_instance(arg.pack[i],
		                                        instance.pack[i]))
			return false;
	return true;
}

bool template_arguments_match_owner_record(
	TypePtr owner_record,
	const vector<TemplateArgument>& full_args)
{
	owner_record = owner_record.get() != NULL
		? pa11::strip_cv(owner_record) : TypePtr();
	if (owner_record.get() == NULL ||
	    !owner_record->is_template_specialization ||
	    owner_record->template_arguments.size() != full_args.size())
		return false;
	for (size_t i = 0; i < full_args.size(); ++i)
		if (!template_argument_matches_instance(
			    full_args[i],
			    owner_record->template_arguments[i]))
			return false;
	return true;
}

string abi_type(TypePtr type,
                const map<string, size_t>& template_parameters,
                const vector<Token>* expression_tokens)
{
	if (type.get() == NULL)
		return "v";
	if (type->is_dependent_typename)
		return abi_dependent_typename_type(type,
		                                   template_parameters,
		                                   expression_tokens,
		                                   true);
	if (type->kind == pa11::TypeKind::Cv)
	{
		string quals;
		if ((type->cv & pa11::CV_CONST) != 0)
			quals += "K";
		if ((type->cv & pa11::CV_VOLATILE) != 0)
			quals += "V";
		return quals + abi_type(type->base,
		                        template_parameters,
		                        expression_tokens);
	}
	if (type->kind == pa11::TypeKind::Pointer)
		return "P" + abi_type(type->base,
		                      template_parameters,
		                      expression_tokens);
	if (type->kind == pa11::TypeKind::LValueReference)
		return "R" + abi_type(type->base,
		                      template_parameters,
		                      expression_tokens);
	if (type->kind == pa11::TypeKind::RValueReference)
		return "O" + abi_type(type->base,
		                      template_parameters,
		                      expression_tokens);
	if (type->kind == pa11::TypeKind::Array)
		return "A" + (type->unknown_bound ? string("") :
		       to_string(type->bound)) + "_" +
		       abi_type(type->base,
		                template_parameters,
		                expression_tokens);
	if (type->kind == pa11::TypeKind::Function)
	{
		string out;
		if ((type->cv & pa11::CV_CONST) != 0)
			out += "K";
		if ((type->cv & pa11::CV_VOLATILE) != 0)
			out += "V";
		out += "F" + abi_type(type->base,
		                       template_parameters,
		                       expression_tokens);
		for (size_t i = 0; i < type->parameters.size(); ++i)
			out += abi_type(type->parameters[i],
			                template_parameters,
			                expression_tokens);
		if (type->parameters.empty())
			out += "v";
		out += "E";
		return out;
	}
	if (type->kind == pa11::TypeKind::Record ||
	    type->kind == pa11::TypeKind::Enum)
		return abi_record_type(type,
		                       template_parameters,
		                       expression_tokens);
	if (type->kind == pa11::TypeKind::TemplateParameter)
	{
		map<string, size_t>::const_iterator found =
			template_parameters.find(type->name);
		size_t index = found == template_parameters.end() ? 0 : found->second;
		return index == 0 ? string("T_") :
		       string("T") + to_string(index - 1) + "_";
	}
	if (type->kind == pa11::TypeKind::MemberPointer)
		return "M" + abi_type(type->member_class,
		                      template_parameters,
		                      expression_tokens) +
		       abi_type(type->base,
		                template_parameters,
		                expression_tokens);
	return abi_fundamental_type(type->fundamental);
}

string abi_function_return_type(
	TypePtr type,
	const map<string, size_t>& template_parameters,
	const vector<Token>* expression_tokens)
{
	if (type.get() != NULL && type->is_dependent_typename)
		return abi_dependent_typename_type(type,
		                                   template_parameters,
		                                   expression_tokens,
		                                   false);
	return abi_type(type, template_parameters, expression_tokens);
}

}  // namespace internal
}  // namespace pa12
