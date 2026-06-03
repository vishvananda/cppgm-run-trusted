#include <cstdint>
#include <cstdlib>
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

bool PA3Mock_IsDefinedIdentifier(const string& identifier);

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

struct IntSuffix
{
	bool is_unsigned;
	int long_rank;
};

struct IntegerCore
{
	size_t digits_begin;
	size_t digits_end;
	int base;
	bool decimal;
};

enum class LiteralEncoding
{
	Ordinary,
	U,
	UpperU,
	L
};

bool IsAsciiDigit(char c)
{
	return c >= '0' && c <= '9';
}

bool IsOctalDigit(char c)
{
	return c >= '0' && c <= '7';
}

bool IsHexDigitChar(char c)
{
	return (c >= '0' && c <= '9') ||
		(c >= 'a' && c <= 'f') ||
		(c >= 'A' && c <= 'F');
}

int HexDigitValue(char c)
{
	if (c >= '0' && c <= '9')
		return c - '0';
	if (c >= 'a' && c <= 'f')
		return c - 'a' + 10;
	if (c >= 'A' && c <= 'F')
		return c - 'A' + 10;
	throw logic_error("hex digit expected");
}

bool IsIdentifierSuffixBodyByte(unsigned char c)
{
	return c == '_' || (c >= '0' && c <= '9') ||
		(c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z') ||
		c >= 0x80;
}

bool IsValidUdSuffix(const string& suffix)
{
	if (suffix.empty() || suffix[0] != '_')
		return false;
	for (size_t i = 1; i < suffix.size(); ++i)
	{
		if (!IsIdentifierSuffixBodyByte(static_cast<unsigned char>(suffix[i])))
			return false;
	}
	return true;
}

bool AddCheckedDigit(unsigned __int128& value, int base, int digit)
{
	const unsigned __int128 limit =
		static_cast<unsigned __int128>(numeric_limits<unsigned long long>::max());
	if (value > (limit - static_cast<unsigned>(digit)) / static_cast<unsigned>(base))
		return false;
	value = value * static_cast<unsigned>(base) + static_cast<unsigned>(digit);
	return true;
}

bool ParseIntegerCore(const string& s, IntegerCore& core)
{
	if (s.empty() || !IsAsciiDigit(s[0]))
		return false;

	if (s.size() >= 2 && s[0] == '0' && (s[1] == 'x' || s[1] == 'X'))
	{
		size_t i = 2;
		while (i < s.size() && IsHexDigitChar(s[i]))
			++i;
		if (i == 2)
			return false;
		core.digits_begin = 2;
		core.digits_end = i;
		core.base = 16;
		core.decimal = false;
		return true;
	}

	if (s[0] == '0')
	{
		size_t i = 1;
		while (i < s.size() && IsOctalDigit(s[i]))
			++i;
		core.digits_begin = 0;
		core.digits_end = i;
		core.base = 8;
		core.decimal = false;
		return true;
	}

	size_t i = 0;
	while (i < s.size() && IsAsciiDigit(s[i]))
		++i;
	core.digits_begin = 0;
	core.digits_end = i;
	core.base = 10;
	core.decimal = true;
	return true;
}

bool ParseIntegerValue(const string& s, const IntegerCore& core,
                       unsigned long long& out)
{
	unsigned __int128 value = 0;
	for (size_t i = core.digits_begin; i < core.digits_end; ++i)
	{
		const int digit = core.base == 16 ? HexDigitValue(s[i]) : s[i] - '0';
		if (!AddCheckedDigit(value, core.base, digit))
			return false;
	}
	out = static_cast<unsigned long long>(value);
	return true;
}

bool MatchLongSuffix(const string& s, size_t pos, int& rank, size_t& consumed)
{
	if (pos >= s.size() || (s[pos] != 'l' && s[pos] != 'L'))
		return false;
	if (pos + 1 < s.size() && s[pos + 1] == s[pos])
	{
		rank = 2;
		consumed = 2;
		return true;
	}
	rank = 1;
	consumed = 1;
	return true;
}

bool ParseIntegerSuffix(const string& suffix, IntSuffix& out)
{
	out.is_unsigned = false;
	out.long_rank = 0;
	size_t pos = 0;
	if (pos < suffix.size() && (suffix[pos] == 'u' || suffix[pos] == 'U'))
	{
		out.is_unsigned = true;
		++pos;
		int rank = 0;
		size_t consumed = 0;
		if (MatchLongSuffix(suffix, pos, rank, consumed))
		{
			out.long_rank = rank;
			pos += consumed;
		}
		return pos == suffix.size();
	}

	int rank = 0;
	size_t consumed = 0;
	if (MatchLongSuffix(suffix, pos, rank, consumed))
	{
		out.long_rank = rank;
		pos += consumed;
		if (pos < suffix.size() && (suffix[pos] == 'u' || suffix[pos] == 'U'))
		{
			out.is_unsigned = true;
			++pos;
		}
		return pos == suffix.size();
	}
	return suffix.empty();
}

bool FitsUnsigned(unsigned long long value, EFundamentalType type)
{
	switch (type)
	{
	case FT_INT:
		return value <= static_cast<unsigned long long>(numeric_limits<int>::max());
	case FT_LONG_INT:
		return value <= static_cast<unsigned long long>(numeric_limits<long int>::max());
	case FT_LONG_LONG_INT:
		return value <= static_cast<unsigned long long>(numeric_limits<long long int>::max());
	case FT_UNSIGNED_INT:
		return value <= static_cast<unsigned long long>(numeric_limits<unsigned int>::max());
	case FT_UNSIGNED_LONG_INT:
		return value <= static_cast<unsigned long long>(numeric_limits<unsigned long int>::max());
	case FT_UNSIGNED_LONG_LONG_INT:
		return true;
	default:
		return false;
	}
}

vector<EFundamentalType> IntegerCandidateTypes(bool decimal, const IntSuffix& suffix)
{
	vector<EFundamentalType> types;
	if (suffix.is_unsigned)
	{
		if (suffix.long_rank == 0)
		{
			types.push_back(FT_UNSIGNED_INT);
			types.push_back(FT_UNSIGNED_LONG_INT);
			types.push_back(FT_UNSIGNED_LONG_LONG_INT);
		}
		else if (suffix.long_rank == 1)
		{
			types.push_back(FT_UNSIGNED_LONG_INT);
			types.push_back(FT_UNSIGNED_LONG_LONG_INT);
		}
		else
			types.push_back(FT_UNSIGNED_LONG_LONG_INT);
		return types;
	}

	if (suffix.long_rank == 1)
	{
		types.push_back(FT_LONG_INT);
		if (!decimal)
			types.push_back(FT_UNSIGNED_LONG_INT);
		types.push_back(FT_LONG_LONG_INT);
		if (!decimal)
			types.push_back(FT_UNSIGNED_LONG_LONG_INT);
		return types;
	}
	if (suffix.long_rank == 2)
	{
		types.push_back(FT_LONG_LONG_INT);
		if (!decimal)
			types.push_back(FT_UNSIGNED_LONG_LONG_INT);
		return types;
	}

	if (decimal)
	{
		types.push_back(FT_INT);
		types.push_back(FT_LONG_INT);
		types.push_back(FT_LONG_LONG_INT);
	}
	else
	{
		types.push_back(FT_INT);
		types.push_back(FT_UNSIGNED_INT);
		types.push_back(FT_LONG_INT);
		types.push_back(FT_UNSIGNED_LONG_INT);
		types.push_back(FT_LONG_LONG_INT);
		types.push_back(FT_UNSIGNED_LONG_LONG_INT);
	}
	return types;
}

bool FundamentalTypeIsUnsigned(EFundamentalType type)
{
	return type == FT_UNSIGNED_CHAR || type == FT_UNSIGNED_SHORT_INT ||
		type == FT_UNSIGNED_INT || type == FT_UNSIGNED_LONG_INT ||
		type == FT_UNSIGNED_LONG_LONG_INT || type == FT_CHAR16_T ||
		type == FT_CHAR32_T;
}

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
	IntegerCore core;
	if (!ParseIntegerCore(source, core))
		return false;

	const string suffix = source.substr(core.digits_end);
	if (IsValidUdSuffix(suffix))
		return false;

	IntSuffix int_suffix;
	if (!ParseIntegerSuffix(suffix, int_suffix))
		return false;

	unsigned long long parsed = 0;
	if (!ParseIntegerValue(source, core, parsed))
		return false;

	const vector<EFundamentalType> candidates =
		IntegerCandidateTypes(core.decimal, int_suffix);
	for (size_t i = 0; i < candidates.size(); ++i)
	{
		if (FitsUnsigned(parsed, candidates[i]))
		{
			if (FundamentalTypeIsUnsigned(candidates[i]))
				out = MakeUnsigned(static_cast<uint64_t>(parsed));
			else
				out = MakeSigned(static_cast<uint64_t>(parsed));
			return true;
		}
	}
	return false;
}

bool DecodeUtf8At(const string& s, size_t& pos, uint32_t& cp)
{
	if (pos >= s.size())
		return false;
	const unsigned char c0 = static_cast<unsigned char>(s[pos]);
	if (c0 <= 0x7F)
	{
		cp = c0;
		++pos;
		return true;
	}
	if (c0 >= 0xC2 && c0 <= 0xDF && pos + 1 < s.size())
	{
		const unsigned char c1 = static_cast<unsigned char>(s[pos + 1]);
		if ((c1 & 0xC0) != 0x80)
			return false;
		cp = ((c0 & 0x1F) << 6) | (c1 & 0x3F);
		pos += 2;
		return true;
	}
	if (c0 >= 0xE0 && c0 <= 0xEF && pos + 2 < s.size())
	{
		const unsigned char c1 = static_cast<unsigned char>(s[pos + 1]);
		const unsigned char c2 = static_cast<unsigned char>(s[pos + 2]);
		if ((c1 & 0xC0) != 0x80 || (c2 & 0xC0) != 0x80)
			return false;
		cp = ((c0 & 0x0F) << 12) | ((c1 & 0x3F) << 6) | (c2 & 0x3F);
		pos += 3;
		return cp >= 0x800 && (cp < 0xD800 || cp > 0xDFFF);
	}
	if (c0 >= 0xF0 && c0 <= 0xF4 && pos + 3 < s.size())
	{
		const unsigned char c1 = static_cast<unsigned char>(s[pos + 1]);
		const unsigned char c2 = static_cast<unsigned char>(s[pos + 2]);
		const unsigned char c3 = static_cast<unsigned char>(s[pos + 3]);
		if ((c1 & 0xC0) != 0x80 || (c2 & 0xC0) != 0x80 || (c3 & 0xC0) != 0x80)
			return false;
		cp = ((c0 & 0x07) << 18) | ((c1 & 0x3F) << 12) |
			((c2 & 0x3F) << 6) | (c3 & 0x3F);
		pos += 4;
		return cp >= 0x10000 && cp <= 0x10FFFF;
	}
	return false;
}

bool IsValidCodePoint(uint32_t cp)
{
	return cp < 0xD800 || (cp >= 0xE000 && cp < 0x110000);
}

bool DecodeSimpleEscape(char c, uint32_t& cp)
{
	switch (c)
	{
	case '\'': cp = '\''; return true;
	case '"': cp = '"'; return true;
	case '?': cp = '?'; return true;
	case '\\': cp = '\\'; return true;
	case 'a': cp = 0x07; return true;
	case 'b': cp = 0x08; return true;
	case 'f': cp = 0x0C; return true;
	case 'n': cp = 0x0A; return true;
	case 'r': cp = 0x0D; return true;
	case 't': cp = 0x09; return true;
	case 'v': cp = 0x0B; return true;
	default: return false;
	}
}

bool DecodeEscapedCodePoint(const string& s, size_t& pos, size_t end, uint32_t& cp)
{
	if (pos >= end || s[pos] != '\\')
		return false;
	++pos;
	if (pos >= end)
		return false;
	if (DecodeSimpleEscape(s[pos], cp))
	{
		++pos;
		return IsValidCodePoint(cp);
	}
	if (IsOctalDigit(s[pos]))
	{
		uint32_t value = 0;
		size_t count = 0;
		while (pos < end && count < 3 && IsOctalDigit(s[pos]))
		{
			value = value * 8 + static_cast<uint32_t>(s[pos] - '0');
			++pos;
			++count;
		}
		cp = value;
		return IsValidCodePoint(cp);
	}
	if (s[pos] != 'x')
		return false;

	++pos;
	if (pos >= end || !IsHexDigitChar(s[pos]))
		return false;
	unsigned __int128 value = 0;
	while (pos < end && IsHexDigitChar(s[pos]))
	{
		value = value * 16 + static_cast<unsigned>(HexDigitValue(s[pos]));
		if (value >= 0x110000)
			return false;
		++pos;
	}
	cp = static_cast<uint32_t>(value);
	return IsValidCodePoint(cp);
}

bool DecodeOrdinaryBody(const string& s, size_t begin, size_t end,
                        vector<uint32_t>& code_points)
{
	size_t pos = begin;
	while (pos < end)
	{
		uint32_t cp = 0;
		if (s[pos] == '\\')
		{
			if (!DecodeEscapedCodePoint(s, pos, end, cp))
				return false;
		}
		else if (!DecodeUtf8At(s, pos, cp))
			return false;
		if (!IsValidCodePoint(cp))
			return false;
		code_points.push_back(cp);
	}
	return true;
}

size_t PrefixLengthForCharacterLiteral(const string& source, LiteralEncoding& encoding)
{
	if (source.size() >= 2 && source[0] == 'u' && source[1] == '\'')
	{
		encoding = LiteralEncoding::U;
		return 1;
	}
	if (source.size() >= 2 && source[0] == 'U' && source[1] == '\'')
	{
		encoding = LiteralEncoding::UpperU;
		return 1;
	}
	if (source.size() >= 2 && source[0] == 'L' && source[1] == '\'')
	{
		encoding = LiteralEncoding::L;
		return 1;
	}
	if (!source.empty() && source[0] == '\'')
	{
		encoding = LiteralEncoding::Ordinary;
		return 0;
	}
	return string::npos;
}

bool FindClosingQuote(const string& source, size_t quote_pos, size_t& close_pos)
{
	size_t pos = quote_pos + 1;
	while (pos < source.size())
	{
		if (source[pos] == '\\')
		{
			++pos;
			if (pos >= source.size())
				return false;
			if (source[pos] == 'x')
			{
				++pos;
				while (pos < source.size() && IsHexDigitChar(source[pos]))
					++pos;
			}
			else if (IsOctalDigit(source[pos]))
			{
				size_t count = 0;
				while (pos < source.size() && count < 3 && IsOctalDigit(source[pos]))
				{
					++pos;
					++count;
				}
			}
			else
				++pos;
			continue;
		}
		if (source[pos] == '\'')
		{
			close_pos = pos;
			return true;
		}
		uint32_t cp = 0;
		if (!DecodeUtf8At(source, pos, cp))
			return false;
	}
	return false;
}

bool MakeCharacterLiteral(const string& source, ExprValue& out)
{
	LiteralEncoding encoding = LiteralEncoding::Ordinary;
	const size_t prefix_len = PrefixLengthForCharacterLiteral(source, encoding);
	if (prefix_len == string::npos)
		return false;
	const size_t quote_pos = prefix_len;
	size_t close_pos = 0;
	vector<uint32_t> code_points;
	if (!FindClosingQuote(source, quote_pos, close_pos) ||
	    !DecodeOrdinaryBody(source, quote_pos + 1, close_pos, code_points) ||
	    code_points.size() != 1 ||
	    close_pos + 1 != source.size())
		return false;

	const uint32_t cp = code_points[0];
	if (encoding == LiteralEncoding::Ordinary)
		out = cp <= 127 ? MakeSigned(cp) : MakeSigned(cp);
	else if (encoding == LiteralEncoding::U)
	{
		if (cp > 0xFFFF)
			return false;
		out = MakeUnsigned(cp);
	}
	else if (encoding == LiteralEncoding::UpperU)
		out = MakeUnsigned(cp);
	else
		out = MakeSigned(cp);
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
	explicit Parser(const vector<Token>& tokens) : tokens_(tokens), pos_(0) {}

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
		if (pos_ >= tokens_.size() || !tokens_[pos_].from_identifier)
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
		out = active ? MakeSigned(PA3Mock_IsDefinedIdentifier(identifier) ? 1 : 0)
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
};

bool EvaluateTokens(const vector<Token>& tokens, ExprValue& out)
{
	Parser parser(tokens);
	return parser.parse(out);
}

class CtrlExprTokenStream : public IPPTokenStream
{
public:
	explicit CtrlExprTokenStream(ostream& out) : out_(out) {}

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
		out_ << "eof\n";
	}

private:
	void finish_line()
	{
		if (line_.empty())
			return;
		ExprValue value;
		if (EvaluateTokens(line_, value))
			write_value(value);
		else
			out_ << "error\n";
		line_.clear();
	}

	void write_value(const ExprValue& value)
	{
		if (value.is_unsigned)
			out_ << value.bits << "u\n";
		else
			out_ << ToSigned(value.bits) << '\n';
	}

	ostream& out_;
	vector<Token> line_;
};

}  // namespace

void run_ctrlexpr(istream& in, ostream& out)
{
	CtrlExprTokenStream tokens(out);
	pptoken::run_pptoken(in, tokens);
}

}  // namespace ctrlexpr
