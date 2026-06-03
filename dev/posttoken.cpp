// (C) 2013 CPPGM Foundation www.cppgm.org.  All rights reserved.

#include <iostream>
#include <sstream>
#include <fstream>
#include <stdexcept>
#include <algorithm>
#include <unordered_map>
#include <unordered_set>
#include <cassert>
#include <memory>
#include <cstring>
#include <cstdint>
#include <climits>
#include <cstddef>
#include <cerrno>
#include <limits>
#include <vector>
#include <map>
#include <utility>

using namespace std;

#include "exceptions.h"
#include "IPPTokenStream.h"
#include "pptoken_lib.h"

#include "posttoken_support.h"

namespace
{

enum class LiteralEncoding
{
	Ordinary,
	U8,
	U,
	UpperU,
	L
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

struct ParsedStringPiece
{
	string source;
	LiteralEncoding encoding;
	string ud_suffix;
	bool valid_suffix;
	vector<uint32_t> code_points;
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
	throw logic_error("HexDigitValue of non-hex value");
}

bool IsIdentifierSuffixStart(char c)
{
	return c == '_';
}

bool IsIdentifierSuffixBodyByte(unsigned char c)
{
	return c == '_' || (c >= '0' && c <= '9') ||
		(c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z') ||
		c >= 0x80;
}

bool IsValidUdSuffix(const string& suffix)
{
	if (suffix.empty() || !IsIdentifierSuffixStart(suffix[0]))
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

bool ParseIntegerValue(const string& s,
                       const IntegerCore& core,
                       unsigned long long& out)
{
	unsigned __int128 value = 0;
	for (size_t i = core.digits_begin; i < core.digits_end; ++i)
	{
		int digit = 0;
		if (core.base == 16)
			digit = HexDigitValue(s[i]);
		else
			digit = s[i] - '0';
		if (!AddCheckedDigit(value, core.base, digit))
			return false;
	}
	out = static_cast<unsigned long long>(value);
	return true;
}

bool MatchLongSuffix(const string& s, size_t pos, int& rank, size_t& consumed)
{
	if (pos >= s.size())
		return false;
	const char c = s[pos];
	if (c != 'l' && c != 'L')
		return false;
	if (pos + 1 < s.size() && s[pos + 1] == c)
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
		{
			types.push_back(FT_UNSIGNED_LONG_LONG_INT);
		}
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

void EmitIntegerValue(DebugPostTokenOutputStream& output,
                      const string& source,
                      EFundamentalType type,
                      unsigned long long value)
{
	switch (type)
	{
	case FT_INT:
	{
		int x = static_cast<int>(value);
		output.emit_literal(source, type, &x, sizeof(x));
		break;
	}
	case FT_LONG_INT:
	{
		long int x = static_cast<long int>(value);
		output.emit_literal(source, type, &x, sizeof(x));
		break;
	}
	case FT_LONG_LONG_INT:
	{
		long long int x = static_cast<long long int>(value);
		output.emit_literal(source, type, &x, sizeof(x));
		break;
	}
	case FT_UNSIGNED_INT:
	{
		unsigned int x = static_cast<unsigned int>(value);
		output.emit_literal(source, type, &x, sizeof(x));
		break;
	}
	case FT_UNSIGNED_LONG_INT:
	{
		unsigned long int x = static_cast<unsigned long int>(value);
		output.emit_literal(source, type, &x, sizeof(x));
		break;
	}
	case FT_UNSIGNED_LONG_LONG_INT:
	{
		unsigned long long int x = static_cast<unsigned long long int>(value);
		output.emit_literal(source, type, &x, sizeof(x));
		break;
	}
	default:
		throw logic_error("bad integer literal type");
	}
}

bool ParseExponentPart(const string& s, size_t& pos)
{
	if (pos >= s.size() || (s[pos] != 'e' && s[pos] != 'E'))
		return false;
	++pos;
	if (pos < s.size() && (s[pos] == '+' || s[pos] == '-'))
		++pos;
	const size_t digits_begin = pos;
	while (pos < s.size() && IsAsciiDigit(s[pos]))
		++pos;
	return pos > digits_begin;
}

bool ParseFloatingCore(const string& s, size_t& end)
{
	size_t pos = 0;
	const size_t leading_begin = pos;
	while (pos < s.size() && IsAsciiDigit(s[pos]))
		++pos;
	const bool has_leading_digits = pos > leading_begin;
	bool has_dot = false;
	bool has_fraction_digits = false;

	if (pos < s.size() && s[pos] == '.')
	{
		has_dot = true;
		++pos;
		const size_t fraction_begin = pos;
		while (pos < s.size() && IsAsciiDigit(s[pos]))
			++pos;
		has_fraction_digits = pos > fraction_begin;
		if (!has_leading_digits && !has_fraction_digits)
			return false;
	}

	size_t exponent_pos = pos;
	const bool has_exponent = ParseExponentPart(s, exponent_pos);
	if (has_exponent)
		pos = exponent_pos;

	if (!has_dot && !has_exponent)
		return false;
	if (!has_dot && !has_leading_digits)
		return false;
	end = pos;
	return end > 0;
}

void EmitFloatingLiteral(DebugPostTokenOutputStream& output,
                         const string& source,
                         char suffix)
{
	if (suffix == 'f' || suffix == 'F')
	{
		float x = PA2Decode_float(source);
		output.emit_literal(source, FT_FLOAT, &x, sizeof(x));
	}
	else if (suffix == 'l' || suffix == 'L')
	{
		long double x = PA2Decode_long_double(source);
		output.emit_literal(source, FT_LONG_DOUBLE, &x, sizeof(x));
	}
	else
	{
		double x = PA2Decode_double(source);
		output.emit_literal(source, FT_DOUBLE, &x, sizeof(x));
	}
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
		if (cp < 0x800 || (cp >= 0xD800 && cp <= 0xDFFF))
			return false;
		pos += 3;
		return true;
	}
	if (c0 >= 0xF0 && c0 <= 0xF4 && pos + 3 < s.size())
	{
		const unsigned char c1 = static_cast<unsigned char>(s[pos + 1]);
		const unsigned char c2 = static_cast<unsigned char>(s[pos + 2]);
		const unsigned char c3 = static_cast<unsigned char>(s[pos + 3]);
		if ((c1 & 0xC0) != 0x80 || (c2 & 0xC0) != 0x80 || (c3 & 0xC0) != 0x80)
			return false;
		cp = ((c0 & 0x07) << 18) |
			((c1 & 0x3F) << 12) |
			((c2 & 0x3F) << 6) |
			(c3 & 0x3F);
		if (cp < 0x10000 || cp > 0x10FFFF)
			return false;
		pos += 4;
		return true;
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

bool DecodeEscapedCodePoint(const string& s,
                            size_t& pos,
                            size_t end,
                            uint32_t& cp)
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
	if (s[pos] == 'x')
	{
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
	return false;
}

bool DecodeOrdinaryBody(const string& s,
                        size_t begin,
                        size_t end,
                        vector<uint32_t>& code_points)
{
	code_points.reserve(code_points.size() + (end - begin));
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
		{
			return false;
		}
		if (!IsValidCodePoint(cp))
			return false;
		code_points.push_back(cp);
	}
	return true;
}

size_t PrefixLengthForQuotedLiteral(const string& source,
                                    char quote,
                                    LiteralEncoding& encoding)
{
	if (quote == '"' && source.compare(0, 3, "u8\"") == 0)
	{
		encoding = LiteralEncoding::U8;
		return 2;
	}
	if (source.size() >= 2 && source[0] == 'u' && source[1] == quote)
	{
		encoding = LiteralEncoding::U;
		return 1;
	}
	if (source.size() >= 2 && source[0] == 'U' && source[1] == quote)
	{
		encoding = LiteralEncoding::UpperU;
		return 1;
	}
	if (source.size() >= 2 && source[0] == 'L' && source[1] == quote)
	{
		encoding = LiteralEncoding::L;
		return 1;
	}
	if (!source.empty() && source[0] == quote)
	{
		encoding = LiteralEncoding::Ordinary;
		return 0;
	}
	return string::npos;
}

bool FindOrdinaryClosingQuote(const string& source,
                              size_t quote_pos,
                              char quote,
                              size_t& close_pos)
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
				continue;
			}
			if (IsOctalDigit(source[pos]))
			{
				size_t count = 0;
				while (pos < source.size() && count < 3 && IsOctalDigit(source[pos]))
				{
					++pos;
					++count;
				}
				continue;
			}
			++pos;
			continue;
		}
		if (source[pos] == quote)
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

bool ParseCharacterLiteral(const string& source,
                           LiteralEncoding& encoding,
                           string& ud_suffix,
                           vector<uint32_t>& code_points)
{
	size_t prefix_len = PrefixLengthForQuotedLiteral(source, '\'', encoding);
	if (prefix_len == string::npos)
		return false;
	const size_t quote_pos = prefix_len;
	size_t close_pos = 0;
	if (!FindOrdinaryClosingQuote(source, quote_pos, '\'', close_pos))
		return false;
	ud_suffix = source.substr(close_pos + 1);
	if (!DecodeOrdinaryBody(source, quote_pos + 1, close_pos, code_points))
		return false;
	return true;
}

bool StartsRawString(const string& source,
                     size_t& prefix_len,
                     LiteralEncoding& encoding)
{
	if (source.compare(0, 4, "u8R\"") == 0)
	{
		prefix_len = 3;
		encoding = LiteralEncoding::U8;
		return true;
	}
	if (source.compare(0, 3, "uR\"") == 0)
	{
		prefix_len = 2;
		encoding = LiteralEncoding::U;
		return true;
	}
	if (source.compare(0, 3, "UR\"") == 0)
	{
		prefix_len = 2;
		encoding = LiteralEncoding::UpperU;
		return true;
	}
	if (source.compare(0, 3, "LR\"") == 0)
	{
		prefix_len = 2;
		encoding = LiteralEncoding::L;
		return true;
	}
	if (source.compare(0, 2, "R\"") == 0)
	{
		prefix_len = 1;
		encoding = LiteralEncoding::Ordinary;
		return true;
	}
	return false;
}

bool ParseRawStringLiteral(const string& source,
                           LiteralEncoding& encoding,
                           string& ud_suffix,
                           vector<uint32_t>& code_points)
{
	size_t prefix_len = 0;
	if (!StartsRawString(source, prefix_len, encoding))
		return false;
	const size_t delimiter_begin = prefix_len + 1;
	const size_t open = source.find('(', delimiter_begin);
	if (open == string::npos)
		return false;
	const string delimiter = source.substr(delimiter_begin, open - delimiter_begin);
	const string close_marker = ")" + delimiter + "\"";
	const size_t close = source.rfind(close_marker);
	if (close == string::npos || close < open)
		return false;
	ud_suffix = source.substr(close + close_marker.size());
	size_t pos = open + 1;
	code_points.reserve(close - pos);
	while (pos < close)
	{
		uint32_t cp = 0;
		if (!DecodeUtf8At(source, pos, cp) || !IsValidCodePoint(cp))
			return false;
		code_points.push_back(cp);
	}
	return true;
}

bool ParseStringLiteralPiece(const string& source, ParsedStringPiece& piece)
{
	piece.source = source;
	piece.ud_suffix.clear();
	piece.valid_suffix = true;
	piece.code_points.clear();
	if (ParseRawStringLiteral(source, piece.encoding, piece.ud_suffix, piece.code_points))
	{
		piece.valid_suffix = piece.ud_suffix.empty() || IsValidUdSuffix(piece.ud_suffix);
		return true;
	}

	size_t prefix_len = PrefixLengthForQuotedLiteral(source, '"', piece.encoding);
	if (prefix_len == string::npos)
		return false;
	const size_t quote_pos = prefix_len;
	size_t close_pos = 0;
	if (!FindOrdinaryClosingQuote(source, quote_pos, '"', close_pos))
		return false;
	piece.ud_suffix = source.substr(close_pos + 1);
	piece.valid_suffix = piece.ud_suffix.empty() || IsValidUdSuffix(piece.ud_suffix);
	return DecodeOrdinaryBody(source, quote_pos + 1, close_pos, piece.code_points);
}

void AppendByte(vector<unsigned char>& bytes, uint32_t value)
{
	bytes.push_back(static_cast<unsigned char>(value & 0xFF));
}

void AppendUint16(vector<unsigned char>& bytes, uint32_t value)
{
	bytes.push_back(static_cast<unsigned char>(value & 0xFF));
	bytes.push_back(static_cast<unsigned char>((value >> 8) & 0xFF));
}

void AppendUint32(vector<unsigned char>& bytes, uint32_t value)
{
	bytes.push_back(static_cast<unsigned char>(value & 0xFF));
	bytes.push_back(static_cast<unsigned char>((value >> 8) & 0xFF));
	bytes.push_back(static_cast<unsigned char>((value >> 16) & 0xFF));
	bytes.push_back(static_cast<unsigned char>((value >> 24) & 0xFF));
}

void AppendUtf8CodePoint(vector<unsigned char>& bytes, uint32_t cp)
{
	if (cp <= 0x7F)
	{
		AppendByte(bytes, cp);
	}
	else if (cp <= 0x7FF)
	{
		AppendByte(bytes, 0xC0 | (cp >> 6));
		AppendByte(bytes, 0x80 | (cp & 0x3F));
	}
	else if (cp <= 0xFFFF)
	{
		AppendByte(bytes, 0xE0 | (cp >> 12));
		AppendByte(bytes, 0x80 | ((cp >> 6) & 0x3F));
		AppendByte(bytes, 0x80 | (cp & 0x3F));
	}
	else
	{
		AppendByte(bytes, 0xF0 | (cp >> 18));
		AppendByte(bytes, 0x80 | ((cp >> 12) & 0x3F));
		AppendByte(bytes, 0x80 | ((cp >> 6) & 0x3F));
		AppendByte(bytes, 0x80 | (cp & 0x3F));
	}
}

bool EncodeStringData(const vector<uint32_t>& code_points,
                      LiteralEncoding encoding,
                      EFundamentalType& type,
                      size_t& elements,
                      vector<unsigned char>& bytes)
{
	bytes.clear();
	elements = 0;
	if (encoding == LiteralEncoding::Ordinary || encoding == LiteralEncoding::U8)
	{
		bytes.reserve(code_points.size() * 4 + 1);
		type = FT_CHAR;
		for (size_t i = 0; i < code_points.size(); ++i)
			AppendUtf8CodePoint(bytes, code_points[i]);
		AppendByte(bytes, 0);
		elements = bytes.size();
		return true;
	}
	if (encoding == LiteralEncoding::U)
	{
		bytes.reserve((code_points.size() * 2 + 1) * sizeof(uint16_t));
		type = FT_CHAR16_T;
		for (size_t i = 0; i < code_points.size(); ++i)
		{
			const uint32_t cp = code_points[i];
			if (cp <= 0xFFFF)
			{
				if (cp >= 0xD800 && cp <= 0xDFFF)
					return false;
				AppendUint16(bytes, cp);
				++elements;
			}
			else if (cp <= 0x10FFFF)
			{
				const uint32_t v = cp - 0x10000;
				AppendUint16(bytes, 0xD800 + (v >> 10));
				AppendUint16(bytes, 0xDC00 + (v & 0x3FF));
				elements += 2;
			}
			else
			{
				return false;
			}
		}
		AppendUint16(bytes, 0);
		++elements;
		return true;
	}

	type = encoding == LiteralEncoding::L ? FT_WCHAR_T : FT_CHAR32_T;
	bytes.reserve((code_points.size() + 1) * sizeof(uint32_t));
	for (size_t i = 0; i < code_points.size(); ++i)
	{
		if (code_points[i] > 0x10FFFF)
			return false;
		AppendUint32(bytes, code_points[i]);
		++elements;
	}
	AppendUint32(bytes, 0);
	++elements;
	return true;
}

string JoinSources(const vector<ParsedStringPiece>& pieces)
{
	size_t size = pieces.empty() ? 0 : pieces.size() - 1;
	for (size_t i = 0; i < pieces.size(); ++i)
		size += pieces[i].source.size();

	string source;
	source.reserve(size);
	for (size_t i = 0; i < pieces.size(); ++i)
	{
		if (i != 0)
			source += ' ';
		source += pieces[i].source;
	}
	return source;
}

bool ValidEncodingCombination(const vector<ParsedStringPiece>& pieces,
                              LiteralEncoding& encoding)
{
	bool have_prefix = false;
	encoding = LiteralEncoding::Ordinary;
	for (size_t i = 0; i < pieces.size(); ++i)
	{
		const LiteralEncoding piece_encoding = pieces[i].encoding;
		if (piece_encoding == LiteralEncoding::Ordinary)
			continue;
		if (!have_prefix)
		{
			encoding = piece_encoding;
			have_prefix = true;
			continue;
		}
		if (encoding != piece_encoding)
			return false;
	}
	return true;
}

bool ValidUdSuffixCombination(const vector<ParsedStringPiece>& pieces,
                              string& ud_suffix)
{
	ud_suffix.clear();
	for (size_t i = 0; i < pieces.size(); ++i)
	{
		if (!pieces[i].valid_suffix)
			return false;
		if (pieces[i].ud_suffix.empty())
			continue;
		if (ud_suffix.empty())
		{
			ud_suffix = pieces[i].ud_suffix;
			continue;
		}
		if (ud_suffix != pieces[i].ud_suffix)
			return false;
	}
	return true;
}

struct PostTokenStream : IPPTokenStream
{
	DebugPostTokenOutputStream output;
	vector<ParsedStringPiece> pending_strings;

	void emit_whitespace_sequence()
	{
	}

	void emit_new_line()
	{
	}

	void emit_header_name(const string& data)
	{
		flush_strings();
		output.emit_invalid(data);
	}

	void emit_identifier(const string& data)
	{
		flush_strings();
		unordered_map<string, ETokenType>::const_iterator it = StringToTokenTypeMap.find(data);
		if (it != StringToTokenTypeMap.end())
			output.emit_simple(data, it->second);
		else
			output.emit_identifier(data);
	}

	void emit_pp_number(const string& data)
	{
		flush_strings();
		if (!try_emit_floating(data))
			try_emit_integer_or_invalid(data);
	}

	void emit_character_literal(const string& data)
	{
		flush_strings();
		emit_character(data, false);
	}

	void emit_user_defined_character_literal(const string& data)
	{
		flush_strings();
		emit_character(data, true);
	}

	void emit_string_literal(const string& data)
	{
		buffer_string(data);
	}

	void emit_user_defined_string_literal(const string& data)
	{
		buffer_string(data);
	}

	void emit_preprocessing_op_or_punc(const string& data)
	{
		flush_strings();
		if (data == "#" || data == "##" || data == "%:" || data == "%:%:")
		{
			output.emit_invalid(data);
			return;
		}
		unordered_map<string, ETokenType>::const_iterator it = StringToTokenTypeMap.find(data);
		if (it != StringToTokenTypeMap.end())
			output.emit_simple(data, it->second);
		else
			output.emit_invalid(data);
	}

	void emit_non_whitespace_char(const string& data)
	{
		flush_strings();
		output.emit_invalid(data);
	}

	void emit_eof()
	{
		flush_strings();
		output.emit_eof();
	}

	void buffer_string(const string& data)
	{
		ParsedStringPiece piece;
		if (!ParseStringLiteralPiece(data, piece))
		{
			piece.source = data;
			piece.encoding = LiteralEncoding::Ordinary;
			piece.valid_suffix = false;
		}
		pending_strings.push_back(std::move(piece));
	}

	void flush_strings()
	{
		if (pending_strings.empty())
			return;

		const string source = JoinSources(pending_strings);
		LiteralEncoding encoding = LiteralEncoding::Ordinary;
		string ud_suffix;
		if (!ValidEncodingCombination(pending_strings, encoding) ||
		    !ValidUdSuffixCombination(pending_strings, ud_suffix))
		{
			output.emit_invalid(source);
			pending_strings.clear();
			return;
		}

		vector<uint32_t> code_points;
		size_t total_code_points = 0;
		for (size_t i = 0; i < pending_strings.size(); ++i)
			total_code_points += pending_strings[i].code_points.size();
		code_points.reserve(total_code_points);
		for (size_t i = 0; i < pending_strings.size(); ++i)
		{
			code_points.insert(code_points.end(),
			                   pending_strings[i].code_points.begin(),
			                   pending_strings[i].code_points.end());
		}

		EFundamentalType type = FT_CHAR;
		size_t elements = 0;
		vector<unsigned char> bytes;
		if (!EncodeStringData(code_points, encoding, type, elements, bytes))
		{
			output.emit_invalid(source);
			pending_strings.clear();
			return;
		}

		if (ud_suffix.empty())
			output.emit_literal_array(source, elements, type, bytes.data(), bytes.size());
		else
			output.emit_user_defined_literal_string_array(source, ud_suffix, elements, type, bytes.data(), bytes.size());
		pending_strings.clear();
	}

	bool try_emit_floating(const string& data)
	{
		size_t core_end = 0;
		if (!ParseFloatingCore(data, core_end))
			return false;
		if (core_end == data.size())
		{
			EmitFloatingLiteral(output, data, '\0');
			return true;
		}
		if (core_end + 1 == data.size() &&
		    (data[core_end] == 'f' || data[core_end] == 'F' ||
		     data[core_end] == 'l' || data[core_end] == 'L'))
		{
			EmitFloatingLiteral(output, data, data[core_end]);
			return true;
		}
		const string suffix = data.substr(core_end);
		if (IsValidUdSuffix(suffix))
		{
			output.emit_user_defined_literal_floating(data, suffix, data.substr(0, core_end));
			return true;
		}
		output.emit_invalid(data);
		return true;
	}

	void try_emit_integer_or_invalid(const string& data)
	{
		IntegerCore core;
		if (!ParseIntegerCore(data, core))
		{
			output.emit_invalid(data);
			return;
		}

		const string suffix = data.substr(core.digits_end);
		if (IsValidUdSuffix(suffix))
		{
			output.emit_user_defined_literal_integer(data, suffix, data.substr(0, core.digits_end));
			return;
		}

		IntSuffix int_suffix;
		if (!ParseIntegerSuffix(suffix, int_suffix))
		{
			output.emit_invalid(data);
			return;
		}

		unsigned long long value = 0;
		if (!ParseIntegerValue(data, core, value))
		{
			output.emit_invalid(data);
			return;
		}

		const vector<EFundamentalType> candidates =
			IntegerCandidateTypes(core.decimal, int_suffix);
		for (size_t i = 0; i < candidates.size(); ++i)
		{
			if (FitsUnsigned(value, candidates[i]))
			{
				EmitIntegerValue(output, data, candidates[i], value);
				return;
			}
		}
		output.emit_invalid(data);
	}

	void emit_character(const string& data, bool user_defined)
	{
		LiteralEncoding encoding = LiteralEncoding::Ordinary;
		string ud_suffix;
		vector<uint32_t> code_points;
		if (!ParseCharacterLiteral(data, encoding, ud_suffix, code_points) ||
		    code_points.size() != 1 ||
		    (user_defined && !IsValidUdSuffix(ud_suffix)) ||
		    (!user_defined && !ud_suffix.empty()))
		{
			output.emit_invalid(data);
			return;
		}

		const uint32_t cp = code_points[0];
		EFundamentalType type = FT_CHAR;
		vector<unsigned char> bytes;
		if (encoding == LiteralEncoding::Ordinary)
		{
			if (cp <= 127)
			{
				type = FT_CHAR;
				AppendByte(bytes, cp);
			}
			else
			{
				type = FT_INT;
				AppendUint32(bytes, cp);
			}
		}
		else if (encoding == LiteralEncoding::U)
		{
			if (cp > 0xFFFF)
			{
				output.emit_invalid(data);
				return;
			}
			type = FT_CHAR16_T;
			AppendUint16(bytes, cp);
		}
		else if (encoding == LiteralEncoding::UpperU)
		{
			type = FT_CHAR32_T;
			AppendUint32(bytes, cp);
		}
		else if (encoding == LiteralEncoding::L)
		{
			type = FT_WCHAR_T;
			AppendUint32(bytes, cp);
		}
		else
		{
			output.emit_invalid(data);
			return;
		}

		if (user_defined)
			output.emit_user_defined_literal_character(data, ud_suffix, type, bytes.data(), bytes.size());
		else
			output.emit_literal(data, type, bytes.data(), bytes.size());
	}
};

} // namespace

int main(int argc, char** argv)
{
	(void)argc;
	(void)argv;
	try
	{
		PostTokenStream output;
		pptoken::run_pptoken(cin, output);
		return EXIT_SUCCESS;
	}
	catch (exception& e)
	{
		cerr << "ERROR: " << e.what() << endl;
		return EXIT_FAILURE;
	}
}
