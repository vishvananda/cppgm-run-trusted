#include <cstdint>
#include <cstdlib>
#include <functional>
#include <iostream>
#include <limits>
#include <sstream>
#include <stdexcept>
#include <string>
#include <utility>
#include <vector>

using namespace std;

#include "IPPTokenStream.h"
#include "ctrlexpr_support.h"
#include "posttoken_support.h"
#include "pptoken_lib.h"

namespace ctrlexpr {
namespace {

enum class TokenKind
{
	Invalid,
	Simple,
	Identifier,
	Literal
};

struct ExprValue
{
	bool is_unsigned;
	uint64_t bits;
	bool active;
};

struct Token
{
	TokenKind kind;
	ETokenType simple;
	string source;
	bool from_identifier;
	ExprValue literal;
};

ExprValue MakeExpr(bool is_unsigned, uint64_t bits, bool active)
{
	ExprValue value;
	value.is_unsigned = is_unsigned;
	value.bits = bits;
	value.active = active;
	return value;
}

ExprValue MakeSigned(uint64_t bits, bool active = true)
{
	return MakeExpr(false, bits, active);
}

ExprValue MakeUnsigned(uint64_t bits, bool active = true)
{
	return MakeExpr(true, bits, active);
}

bool MakeIntegerLiteral(const string& source, ExprValue& out)
{
	IntegerLiteralInfo info;
	if (!AnalyzeIntegerLiteral(source, info) || info.user_defined)
		return false;
	if (FundamentalTypeIsUnsigned(info.type))
		out = MakeUnsigned(static_cast<uint64_t>(info.value));
	else
		out = MakeSigned(static_cast<uint64_t>(info.value));
	return true;
}

bool MakeCharacterLiteral(const string& source, ExprValue& out)
{
	CharacterLiteralInfo info;
	if (!AnalyzeCharacterLiteral(source, false, info))
		return false;
	if (FundamentalTypeIsUnsigned(info.type))
		out = MakeUnsigned(info.code_point);
	else
		out = MakeSigned(info.code_point);
	return true;
}

Token MakeInvalidToken(const string& source)
{
	Token token;
	token.kind = TokenKind::Invalid;
	token.simple = OP_LPAREN;
	token.source = source;
	token.from_identifier = false;
	token.literal = MakeSigned(0, false);
	return token;
}

Token MakeSimpleToken(const string& source, ETokenType simple, bool from_identifier)
{
	Token token;
	token.kind = TokenKind::Simple;
	token.simple = simple;
	token.source = source;
	token.from_identifier = from_identifier;
	token.literal = MakeSigned(0, false);
	return token;
}

Token MakeIdentifierToken(const string& source)
{
	Token token;
	token.kind = TokenKind::Identifier;
	token.simple = OP_LPAREN;
	token.source = source;
	token.from_identifier = true;
	token.literal = MakeSigned(0, false);
	return token;
}

Token MakeLiteralToken(const string& source, const ExprValue& literal)
{
	Token token;
	token.kind = TokenKind::Literal;
	token.simple = OP_LPAREN;
	token.source = source;
	token.from_identifier = false;
	token.literal = literal;
	return token;
}

bool IsOperatorToken(ETokenType token_type)
{
	return token_type >= OP_LBRACE;
}

bool is_identifier_like_operator_name(const string& data)
{
	static const char* const names[] = {
		"new", "delete", "and", "and_eq", "bitand", "bitor", "compl",
		"not", "not_eq", "or", "or_eq", "xor", "xor_eq"
	};
	for (size_t i = 0; i < sizeof(names) / sizeof(names[0]); ++i)
	{
		if (data == names[i])
			return true;
	}
	return false;
}

bool MockIsDefinedIdentifier(const string& identifier)
{
	return !identifier.empty() && (identifier[0] % 2) != 0;
}

int64_t ToSigned(uint64_t bits)
{
	return static_cast<int64_t>(bits);
}

bool IsZero(const ExprValue& value)
{
	return value.bits == 0;
}

ExprValue Converted(const ExprValue& value, bool to_unsigned)
{
	return MakeExpr(to_unsigned, value.bits, value.active);
}

bool CommonUnsigned(const ExprValue& lhs, const ExprValue& rhs)
{
	return lhs.is_unsigned || rhs.is_unsigned;
}

uint64_t ArithmeticShiftRight(uint64_t bits, unsigned count)
{
	if (count == 0 || (bits & (uint64_t(1) << 63)) == 0)
		return bits >> count;
	return (bits >> count) | (~uint64_t(0) << (64 - count));
}

bool ShiftCount(const ExprValue& value, unsigned& count)
{
	if (value.is_unsigned)
	{
		if (value.bits >= 64)
			return false;
		count = static_cast<unsigned>(value.bits);
		return true;
	}
	const int64_t signed_count = ToSigned(value.bits);
	if (signed_count < 0 || signed_count >= 64)
		return false;
	count = static_cast<unsigned>(signed_count);
	return true;
}

bool ApplyUnary(ETokenType op, const ExprValue& operand, ExprValue& out)
{
	if (op == OP_PLUS)
	{
		out = operand;
		return true;
	}
	if (op == OP_LNOT)
	{
		out = operand.active ? MakeSigned(IsZero(operand) ? 1 : 0) : MakeSigned(0, false);
		return true;
	}
	if (!operand.active)
	{
		out = MakeExpr(operand.is_unsigned, 0, false);
		return true;
	}
	if (op == OP_MINUS)
		out = MakeExpr(operand.is_unsigned, uint64_t(0) - operand.bits, true);
	else if (op == OP_COMPL)
		out = MakeExpr(operand.is_unsigned, ~operand.bits, true);
	else
		return false;
	return true;
}

bool ApplyMultiplicative(ETokenType op, const ExprValue& lhs,
                         const ExprValue& rhs, ExprValue& out)
{
	const bool result_unsigned = CommonUnsigned(lhs, rhs);
	if (!lhs.active || !rhs.active)
	{
		out = MakeExpr(result_unsigned, 0, false);
		return true;
	}
	const uint64_t a = lhs.bits;
	const uint64_t b = rhs.bits;
	if (op == OP_STAR)
		out = MakeExpr(result_unsigned, a * b, true);
	else if (result_unsigned)
	{
		if (b == 0)
			return false;
		out = MakeUnsigned(op == OP_DIV ? a / b : a % b);
	}
	else
	{
		const int64_t sa = ToSigned(a);
		const int64_t sb = ToSigned(b);
		if (sb == 0 ||
		    (sa == numeric_limits<int64_t>::min() && sb == -1))
			return false;
		out = MakeSigned(static_cast<uint64_t>(op == OP_DIV ? sa / sb : sa % sb));
	}
	return true;
}

bool ApplyAdditive(ETokenType op, const ExprValue& lhs,
                   const ExprValue& rhs, ExprValue& out)
{
	const bool result_unsigned = CommonUnsigned(lhs, rhs);
	if (!lhs.active || !rhs.active)
	{
		out = MakeExpr(result_unsigned, 0, false);
		return true;
	}
	out = MakeExpr(result_unsigned,
		op == OP_PLUS ? lhs.bits + rhs.bits : lhs.bits - rhs.bits,
		true);
	return true;
}

bool ApplyShift(ETokenType op, const ExprValue& lhs,
                const ExprValue& rhs, ExprValue& out)
{
	if (!lhs.active || !rhs.active)
	{
		out = MakeExpr(lhs.is_unsigned, 0, false);
		return true;
	}
	unsigned count = 0;
	if (!ShiftCount(rhs, count))
		return false;
	if (op == OP_LSHIFT)
		out = MakeExpr(lhs.is_unsigned, lhs.bits << count, true);
	else if (lhs.is_unsigned)
		out = MakeUnsigned(lhs.bits >> count);
	else
		out = MakeSigned(ArithmeticShiftRight(lhs.bits, count));
	return true;
}

bool ApplyComparison(ETokenType op, const ExprValue& lhs,
                     const ExprValue& rhs, ExprValue& out)
{
	if (!lhs.active || !rhs.active)
	{
		out = MakeSigned(0, false);
		return true;
	}
	const bool use_unsigned = CommonUnsigned(lhs, rhs);
	bool result = false;
	if (use_unsigned)
	{
		if (op == OP_LT) result = lhs.bits < rhs.bits;
		else if (op == OP_GT) result = lhs.bits > rhs.bits;
		else if (op == OP_LE) result = lhs.bits <= rhs.bits;
		else if (op == OP_GE) result = lhs.bits >= rhs.bits;
	}
	else
	{
		const int64_t a = ToSigned(lhs.bits);
		const int64_t b = ToSigned(rhs.bits);
		if (op == OP_LT) result = a < b;
		else if (op == OP_GT) result = a > b;
		else if (op == OP_LE) result = a <= b;
		else if (op == OP_GE) result = a >= b;
	}
	out = MakeSigned(result ? 1 : 0);
	return true;
}

bool ApplyEquality(ETokenType op, const ExprValue& lhs,
                   const ExprValue& rhs, ExprValue& out)
{
	if (!lhs.active || !rhs.active)
	{
		out = MakeSigned(0, false);
		return true;
	}
	const bool equal = lhs.bits == rhs.bits;
	out = MakeSigned((op == OP_EQ ? equal : !equal) ? 1 : 0);
	return true;
}

bool ApplyBitwise(ETokenType op, const ExprValue& lhs,
                  const ExprValue& rhs, ExprValue& out)
{
	const bool result_unsigned = CommonUnsigned(lhs, rhs);
	if (!lhs.active || !rhs.active)
	{
		out = MakeExpr(result_unsigned, 0, false);
		return true;
	}
	if (op == OP_AMP)
		out = MakeExpr(result_unsigned, lhs.bits & rhs.bits, true);
	else if (op == OP_XOR)
		out = MakeExpr(result_unsigned, lhs.bits ^ rhs.bits, true);
	else
		out = MakeExpr(result_unsigned, lhs.bits | rhs.bits, true);
	return true;
}

class Parser
{
public:
	Parser(const vector<Token>& tokens, const ctrlexpr::DefinedPredicate& is_defined)
		: tokens_(tokens), pos_(0), is_defined_(is_defined) {}

	bool parse(ExprValue& out)
	{
		return parse_controlling(true, out) && pos_ == tokens_.size() && out.active;
	}

private:
	bool at(ETokenType type) const
	{
		return pos_ < tokens_.size() &&
			tokens_[pos_].kind == TokenKind::Simple &&
			tokens_[pos_].simple == type;
	}

	bool consume(ETokenType type)
	{
		if (!at(type))
			return false;
		++pos_;
		return true;
	}

	bool parse_identifier_operand(string& source)
	{
		if (pos_ >= tokens_.size())
			return false;
		if (!tokens_[pos_].from_identifier &&
		    !is_identifier_like_operator_name(tokens_[pos_].source))
			return false;
		source = tokens_[pos_].source;
		++pos_;
		return true;
	}

	bool parse_defined(bool active, ExprValue& out)
	{
		++pos_;
		string identifier;
		if (consume(OP_LPAREN))
		{
			if (!parse_identifier_operand(identifier) || !consume(OP_RPAREN))
				return false;
		}
		else if (!parse_identifier_operand(identifier))
			return false;
		out = active ? MakeSigned(is_defined_(identifier) ? 1 : 0)
			: MakeSigned(0, false);
		return true;
	}

	bool parse_primary(bool active, ExprValue& out)
	{
		if (pos_ >= tokens_.size() || tokens_[pos_].kind == TokenKind::Invalid)
			return false;
		if (tokens_[pos_].kind == TokenKind::Literal)
		{
			out = active ? tokens_[pos_].literal
				: MakeExpr(tokens_[pos_].literal.is_unsigned, 0, false);
			++pos_;
			return true;
		}
		if (tokens_[pos_].kind == TokenKind::Identifier &&
		    tokens_[pos_].source == "defined")
			return parse_defined(active, out);
		if (tokens_[pos_].kind == TokenKind::Identifier)
		{
			const string source = tokens_[pos_].source;
			++pos_;
			if (source == "true")
				out = active ? MakeSigned(1) : MakeSigned(0, false);
			else
				out = MakeSigned(0, active);
			return true;
		}
		if (consume(OP_LPAREN))
		{
			if (!parse_controlling(active, out) || !consume(OP_RPAREN))
				return false;
			return true;
		}
		return false;
	}

	bool parse_unary(bool active, ExprValue& out)
	{
		if (at(OP_PLUS) || at(OP_MINUS) || at(OP_LNOT) || at(OP_COMPL))
		{
			const ETokenType op = tokens_[pos_++].simple;
			ExprValue operand;
			return parse_unary(active, operand) && ApplyUnary(op, operand, out);
		}
		return parse_primary(active, out);
	}

	bool parse_multiplicative(bool active, ExprValue& out)
	{
		if (!parse_unary(active, out))
			return false;
		while (at(OP_STAR) || at(OP_DIV) || at(OP_MOD))
		{
			const ETokenType op = tokens_[pos_++].simple;
			ExprValue rhs;
			if (!parse_unary(active, rhs) || !ApplyMultiplicative(op, out, rhs, out))
				return false;
		}
		return true;
	}

	bool parse_additive(bool active, ExprValue& out)
	{
		if (!parse_multiplicative(active, out))
			return false;
		while (at(OP_PLUS) || at(OP_MINUS))
		{
			const ETokenType op = tokens_[pos_++].simple;
			ExprValue rhs;
			if (!parse_multiplicative(active, rhs) || !ApplyAdditive(op, out, rhs, out))
				return false;
		}
		return true;
	}

	bool parse_shift(bool active, ExprValue& out)
	{
		if (!parse_additive(active, out))
			return false;
		while (at(OP_LSHIFT) || at(OP_RSHIFT))
		{
			const ETokenType op = tokens_[pos_++].simple;
			ExprValue rhs;
			if (!parse_additive(active, rhs) || !ApplyShift(op, out, rhs, out))
				return false;
		}
		return true;
	}

	bool parse_relational(bool active, ExprValue& out)
	{
		if (!parse_shift(active, out))
			return false;
		while (at(OP_LT) || at(OP_GT) || at(OP_LE) || at(OP_GE))
		{
			const ETokenType op = tokens_[pos_++].simple;
			ExprValue rhs;
			if (!parse_shift(active, rhs) || !ApplyComparison(op, out, rhs, out))
				return false;
		}
		return true;
	}

	bool parse_equality(bool active, ExprValue& out)
	{
		if (!parse_relational(active, out))
			return false;
		while (at(OP_EQ) || at(OP_NE))
		{
			const ETokenType op = tokens_[pos_++].simple;
			ExprValue rhs;
			if (!parse_relational(active, rhs) || !ApplyEquality(op, out, rhs, out))
				return false;
		}
		return true;
	}

	bool parse_and(bool active, ExprValue& out)
	{
		if (!parse_equality(active, out))
			return false;
		while (at(OP_AMP))
		{
			++pos_;
			ExprValue rhs;
			if (!parse_equality(active, rhs) || !ApplyBitwise(OP_AMP, out, rhs, out))
				return false;
		}
		return true;
	}

	bool parse_exclusive_or(bool active, ExprValue& out)
	{
		if (!parse_and(active, out))
			return false;
		while (at(OP_XOR))
		{
			++pos_;
			ExprValue rhs;
			if (!parse_and(active, rhs) || !ApplyBitwise(OP_XOR, out, rhs, out))
				return false;
		}
		return true;
	}

	bool parse_inclusive_or(bool active, ExprValue& out)
	{
		if (!parse_exclusive_or(active, out))
			return false;
		while (at(OP_BOR))
		{
			++pos_;
			ExprValue rhs;
			if (!parse_exclusive_or(active, rhs) || !ApplyBitwise(OP_BOR, out, rhs, out))
				return false;
		}
		return true;
	}

	bool parse_logical_and(bool active, ExprValue& out)
	{
		if (!parse_inclusive_or(active, out))
			return false;
		while (at(OP_LAND))
		{
			++pos_;
			const bool lhs_true = active && !IsZero(out);
			ExprValue rhs;
			if (!parse_inclusive_or(lhs_true, rhs))
				return false;
			if (active)
				out = MakeSigned(lhs_true && !IsZero(rhs) ? 1 : 0);
			else
				out = MakeSigned(0, false);
		}
		return true;
	}

	bool parse_logical_or(bool active, ExprValue& out)
	{
		if (!parse_logical_and(active, out))
			return false;
		while (at(OP_LOR))
		{
			++pos_;
			const bool lhs_true = active && !IsZero(out);
			ExprValue rhs;
			if (!parse_logical_and(active && !lhs_true, rhs))
				return false;
			if (active)
				out = MakeSigned((lhs_true || !IsZero(rhs)) ? 1 : 0);
			else
				out = MakeSigned(0, false);
		}
		return true;
	}

	bool parse_controlling(bool active, ExprValue& out)
	{
		if (!parse_logical_or(active, out))
			return false;
		if (!consume(OP_QMARK))
			return true;

		const bool condition_true = active && !IsZero(out);
		ExprValue true_branch;
		ExprValue false_branch;
		if (!parse_controlling(condition_true, true_branch) || !consume(OP_COLON) ||
		    !parse_controlling(active && !condition_true, false_branch))
			return false;

		const bool result_unsigned = CommonUnsigned(true_branch, false_branch);
		if (active)
			out = Converted(condition_true ? true_branch : false_branch, result_unsigned);
		else
			out = MakeExpr(result_unsigned, 0, false);
		return true;
	}

	const vector<Token>& tokens_;
	size_t pos_;
	ctrlexpr::DefinedPredicate is_defined_;
};

bool EvaluateTokens(const vector<Token>& tokens,
                    const ctrlexpr::DefinedPredicate& is_defined,
                    ExprValue& out)
{
	Parser parser(tokens, is_defined);
	return parser.parse(out);
}

class CtrlExprTokenStream : public IPPTokenStream
{
public:
	CtrlExprTokenStream(ostream& out, const ctrlexpr::DefinedPredicate& is_defined)
		: out_(out), is_defined_(is_defined) {}

	void emit_whitespace_sequence() {}

	void emit_new_line()
	{
		finish_line();
	}

	void emit_header_name(const string& data)
	{
		line_.push_back(MakeInvalidToken(data));
	}

	void emit_identifier(const string& data)
	{
		unordered_map<string, ETokenType>::const_iterator it = StringToTokenTypeMap.find(data);
		if (it != StringToTokenTypeMap.end() && IsOperatorToken(it->second))
			line_.push_back(MakeSimpleToken(data, it->second, true));
		else
			line_.push_back(MakeIdentifierToken(data));
	}

	void emit_pp_number(const string& data)
	{
		ExprValue literal;
		if (MakeIntegerLiteral(data, literal))
			line_.push_back(MakeLiteralToken(data, literal));
		else
			line_.push_back(MakeInvalidToken(data));
	}

	void emit_character_literal(const string& data)
	{
		ExprValue literal;
		if (MakeCharacterLiteral(data, literal))
			line_.push_back(MakeLiteralToken(data, literal));
		else
			line_.push_back(MakeInvalidToken(data));
	}

	void emit_user_defined_character_literal(const string& data)
	{
		line_.push_back(MakeInvalidToken(data));
	}

	void emit_string_literal(const string& data)
	{
		line_.push_back(MakeInvalidToken(data));
	}

	void emit_user_defined_string_literal(const string& data)
	{
		line_.push_back(MakeInvalidToken(data));
	}

	void emit_preprocessing_op_or_punc(const string& data)
	{
		if (data == "#" || data == "##" || data == "%:" || data == "%:%:")
		{
			line_.push_back(MakeInvalidToken(data));
			return;
		}
		unordered_map<string, ETokenType>::const_iterator it = StringToTokenTypeMap.find(data);
		if (it == StringToTokenTypeMap.end() || !IsOperatorToken(it->second))
			line_.push_back(MakeInvalidToken(data));
		else
			line_.push_back(MakeSimpleToken(data, it->second, false));
	}

	void emit_non_whitespace_char(const string& data)
	{
		line_.push_back(MakeInvalidToken(data));
	}

	void emit_eof()
	{
		finish_line();
		output_ += "eof\n";
		out_ << output_;
	}

private:
	void finish_line()
	{
		if (line_.empty())
			return;
		ExprValue value;
		if (EvaluateTokens(line_, is_defined_, value))
			write_value(value);
		else
			output_ += "error\n";
		line_.clear();
	}

	void write_value(const ExprValue& value)
	{
		if (value.is_unsigned)
		{
			output_ += to_string(value.bits);
			output_ += "u\n";
		}
		else
		{
			output_ += to_string(ToSigned(value.bits));
			output_ += '\n';
		}
	}

	ostream& out_;
	ctrlexpr::DefinedPredicate is_defined_;
	vector<Token> line_;
	string output_;
};

void AppendPPTokenAsCtrlExprToken(const PPToken& token, vector<Token>& out)
{
	if (IsWhitespace(token) || token.kind == PPTokenKind::EndOfFile ||
	    token.kind == PPTokenKind::Placemarker)
		return;
	if (token.kind == PPTokenKind::HeaderName)
		out.push_back(MakeInvalidToken(token.text));
	else if (token.kind == PPTokenKind::Identifier)
	{
		unordered_map<string, ETokenType>::const_iterator it =
			StringToTokenTypeMap.find(token.text);
		if (it != StringToTokenTypeMap.end() && IsOperatorToken(it->second))
			out.push_back(MakeSimpleToken(token.text, it->second, true));
		else
			out.push_back(MakeIdentifierToken(token.text));
	}
	else if (token.kind == PPTokenKind::PPNumber)
	{
		ExprValue literal;
		if (MakeIntegerLiteral(token.text, literal))
			out.push_back(MakeLiteralToken(token.text, literal));
		else
			out.push_back(MakeInvalidToken(token.text));
	}
	else if (token.kind == PPTokenKind::CharacterLiteral)
	{
		ExprValue literal;
		if (MakeCharacterLiteral(token.text, literal))
			out.push_back(MakeLiteralToken(token.text, literal));
		else
			out.push_back(MakeInvalidToken(token.text));
	}
	else if (token.kind == PPTokenKind::PreprocessingOpOrPunc)
	{
		if (token.text == "#" || token.text == "##" ||
		    token.text == "%:" || token.text == "%:%:")
			out.push_back(MakeInvalidToken(token.text));
		else
		{
			unordered_map<string, ETokenType>::const_iterator it =
				StringToTokenTypeMap.find(token.text);
			if (it == StringToTokenTypeMap.end() || !IsOperatorToken(it->second))
				out.push_back(MakeInvalidToken(token.text));
			else
				out.push_back(MakeSimpleToken(token.text, it->second, false));
		}
	}
	else
		out.push_back(MakeInvalidToken(token.text));
}

}  // namespace

bool evaluate_tokens(const vector<PPToken>& tokens,
                     const DefinedPredicate& is_defined,
                     bool& out)
{
	vector<Token> converted;
	for (size_t i = 0; i < tokens.size(); ++i)
		AppendPPTokenAsCtrlExprToken(tokens[i], converted);
	ExprValue value;
	if (!EvaluateTokens(converted, is_defined, value))
		return false;
	out = value.bits != 0;
	return true;
}

void run_ctrlexpr(istream& in, ostream& out)
{
	CtrlExprTokenStream tokens(out, MockIsDefinedIdentifier);
	pptoken::run_pptoken(in, tokens);
}

}  // namespace ctrlexpr
