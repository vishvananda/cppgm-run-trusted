#include <cstddef>
#include <cstdint>
#include <iostream>
#include <limits>
#include <sstream>
#include <stdexcept>
#include <vector>

using namespace std;

#include "posttoken_support.h"

// convert EFundamentalType to a source code
const map<EFundamentalType, string> FundamentalTypeToStringMap
{
	{FT_SIGNED_CHAR, "signed char"},
	{FT_SHORT_INT, "short int"},
	{FT_INT, "int"},
	{FT_LONG_INT, "long int"},
	{FT_LONG_LONG_INT, "long long int"},
	{FT_UNSIGNED_CHAR, "unsigned char"},
	{FT_UNSIGNED_SHORT_INT, "unsigned short int"},
	{FT_UNSIGNED_INT, "unsigned int"},
	{FT_UNSIGNED_LONG_INT, "unsigned long int"},
	{FT_UNSIGNED_LONG_LONG_INT, "unsigned long long int"},
	{FT_WCHAR_T, "wchar_t"},
	{FT_CHAR, "char"},
	{FT_CHAR16_T, "char16_t"},
	{FT_CHAR32_T, "char32_t"},
	{FT_BOOL, "bool"},
	{FT_FLOAT, "float"},
	{FT_DOUBLE, "double"},
	{FT_LONG_DOUBLE, "long double"},
	{FT_VOID, "void"},
	{FT_NULLPTR_T, "nullptr_t"}
};

// StringToETokenTypeMap map of `simple` `preprocessing-tokens` to ETokenType
const unordered_map<string, ETokenType> StringToTokenTypeMap =
{
	// keywords
	{"alignas", KW_ALIGNAS},
	{"alignof", KW_ALIGNOF},
	{"asm", KW_ASM},
	{"auto", KW_AUTO},
	{"bool", KW_BOOL},
	{"break", KW_BREAK},
	{"case", KW_CASE},
	{"catch", KW_CATCH},
	{"char", KW_CHAR},
	{"char16_t", KW_CHAR16_T},
	{"char32_t", KW_CHAR32_T},
	{"class", KW_CLASS},
	{"const", KW_CONST},
	{"constexpr", KW_CONSTEXPR},
	{"const_cast", KW_CONST_CAST},
	{"continue", KW_CONTINUE},
	{"decltype", KW_DECLTYPE},
	{"default", KW_DEFAULT},
	{"delete", KW_DELETE},
	{"do", KW_DO},
	{"double", KW_DOUBLE},
	{"dynamic_cast", KW_DYNAMIC_CAST},
	{"else", KW_ELSE},
	{"enum", KW_ENUM},
	{"explicit", KW_EXPLICIT},
	{"export", KW_EXPORT},
	{"extern", KW_EXTERN},
	{"false", KW_FALSE},
	{"float", KW_FLOAT},
	{"for", KW_FOR},
	{"friend", KW_FRIEND},
	{"goto", KW_GOTO},
	{"if", KW_IF},
	{"inline", KW_INLINE},
	{"int", KW_INT},
	{"long", KW_LONG},
	{"mutable", KW_MUTABLE},
	{"namespace", KW_NAMESPACE},
	{"new", KW_NEW},
	{"noexcept", KW_NOEXCEPT},
	{"nullptr", KW_NULLPTR},
	{"operator", KW_OPERATOR},
	{"private", KW_PRIVATE},
	{"protected", KW_PROTECTED},
	{"public", KW_PUBLIC},
	{"register", KW_REGISTER},
	{"reinterpret_cast", KW_REINTERPET_CAST},
	{"return", KW_RETURN},
	{"short", KW_SHORT},
	{"signed", KW_SIGNED},
	{"sizeof", KW_SIZEOF},
	{"static", KW_STATIC},
	{"static_assert", KW_STATIC_ASSERT},
	{"static_cast", KW_STATIC_CAST},
	{"struct", KW_STRUCT},
	{"switch", KW_SWITCH},
	{"template", KW_TEMPLATE},
	{"this", KW_THIS},
	{"thread_local", KW_THREAD_LOCAL},
	{"throw", KW_THROW},
	{"true", KW_TRUE},
	{"try", KW_TRY},
	{"typedef", KW_TYPEDEF},
	{"typeid", KW_TYPEID},
	{"typename", KW_TYPENAME},
	{"union", KW_UNION},
	{"unsigned", KW_UNSIGNED},
	{"using", KW_USING},
	{"virtual", KW_VIRTUAL},
	{"void", KW_VOID},
	{"volatile", KW_VOLATILE},
	{"wchar_t", KW_WCHAR_T},
	{"while", KW_WHILE},

	// operators/punctuation
	{"{", OP_LBRACE},
	{"<%", OP_LBRACE},
	{"}", OP_RBRACE},
	{"%>", OP_RBRACE},
	{"[", OP_LSQUARE},
	{"<:", OP_LSQUARE},
	{"]", OP_RSQUARE},
	{":>", OP_RSQUARE},
	{"(", OP_LPAREN},
	{")", OP_RPAREN},
	{"|", OP_BOR},
	{"bitor", OP_BOR},
	{"^", OP_XOR},
	{"xor", OP_XOR},
	{"~", OP_COMPL},
	{"compl", OP_COMPL},
	{"&", OP_AMP},
	{"bitand", OP_AMP},
	{"!", OP_LNOT},
	{"not", OP_LNOT},
	{";", OP_SEMICOLON},
	{":", OP_COLON},
	{"...", OP_DOTS},
	{"?", OP_QMARK},
	{"::", OP_COLON2},
	{".", OP_DOT},
	{".*", OP_DOTSTAR},
	{"+", OP_PLUS},
	{"-", OP_MINUS},
	{"*", OP_STAR},
	{"/", OP_DIV},
	{"%", OP_MOD},
	{"=", OP_ASS},
	{"<", OP_LT},
	{">", OP_GT},
	{"+=", OP_PLUSASS},
	{"-=", OP_MINUSASS},
	{"*=", OP_STARASS},
	{"/=", OP_DIVASS},
	{"%=", OP_MODASS},
	{"^=", OP_XORASS},
	{"xor_eq", OP_XORASS},
	{"&=", OP_BANDASS},
	{"and_eq", OP_BANDASS},
	{"|=", OP_BORASS},
	{"or_eq", OP_BORASS},
	{"<<", OP_LSHIFT},
	{">>", OP_RSHIFT},
	{">>=", OP_RSHIFTASS},
	{"<<=", OP_LSHIFTASS},
	{"==", OP_EQ},
	{"!=", OP_NE},
	{"not_eq", OP_NE},
	{"<=", OP_LE},
	{">=", OP_GE},
	{"&&", OP_LAND},
	{"and", OP_LAND},
	{"||", OP_LOR},
	{"or", OP_LOR},
	{"++", OP_INC},
	{"--", OP_DEC},
	{",", OP_COMMA},
	{"->*", OP_ARROWSTAR},
	{"->", OP_ARROW}
};

// map of enum to string
const map<ETokenType, string> TokenTypeToStringMap =
{
	{KW_ALIGNAS, "KW_ALIGNAS"},
	{KW_ALIGNOF, "KW_ALIGNOF"},
	{KW_ASM, "KW_ASM"},
	{KW_AUTO, "KW_AUTO"},
	{KW_BOOL, "KW_BOOL"},
	{KW_BREAK, "KW_BREAK"},
	{KW_CASE, "KW_CASE"},
	{KW_CATCH, "KW_CATCH"},
	{KW_CHAR, "KW_CHAR"},
	{KW_CHAR16_T, "KW_CHAR16_T"},
	{KW_CHAR32_T, "KW_CHAR32_T"},
	{KW_CLASS, "KW_CLASS"},
	{KW_CONST, "KW_CONST"},
	{KW_CONSTEXPR, "KW_CONSTEXPR"},
	{KW_CONST_CAST, "KW_CONST_CAST"},
	{KW_CONTINUE, "KW_CONTINUE"},
	{KW_DECLTYPE, "KW_DECLTYPE"},
	{KW_DEFAULT, "KW_DEFAULT"},
	{KW_DELETE, "KW_DELETE"},
	{KW_DO, "KW_DO"},
	{KW_DOUBLE, "KW_DOUBLE"},
	{KW_DYNAMIC_CAST, "KW_DYNAMIC_CAST"},
	{KW_ELSE, "KW_ELSE"},
	{KW_ENUM, "KW_ENUM"},
	{KW_EXPLICIT, "KW_EXPLICIT"},
	{KW_EXPORT, "KW_EXPORT"},
	{KW_EXTERN, "KW_EXTERN"},
	{KW_FALSE, "KW_FALSE"},
	{KW_FLOAT, "KW_FLOAT"},
	{KW_FOR, "KW_FOR"},
	{KW_FRIEND, "KW_FRIEND"},
	{KW_GOTO, "KW_GOTO"},
	{KW_IF, "KW_IF"},
	{KW_INLINE, "KW_INLINE"},
	{KW_INT, "KW_INT"},
	{KW_LONG, "KW_LONG"},
	{KW_MUTABLE, "KW_MUTABLE"},
	{KW_NAMESPACE, "KW_NAMESPACE"},
	{KW_NEW, "KW_NEW"},
	{KW_NOEXCEPT, "KW_NOEXCEPT"},
	{KW_NULLPTR, "KW_NULLPTR"},
	{KW_OPERATOR, "KW_OPERATOR"},
	{KW_PRIVATE, "KW_PRIVATE"},
	{KW_PROTECTED, "KW_PROTECTED"},
	{KW_PUBLIC, "KW_PUBLIC"},
	{KW_REGISTER, "KW_REGISTER"},
	{KW_REINTERPET_CAST, "KW_REINTERPET_CAST"},
	{KW_RETURN, "KW_RETURN"},
	{KW_SHORT, "KW_SHORT"},
	{KW_SIGNED, "KW_SIGNED"},
	{KW_SIZEOF, "KW_SIZEOF"},
	{KW_STATIC, "KW_STATIC"},
	{KW_STATIC_ASSERT, "KW_STATIC_ASSERT"},
	{KW_STATIC_CAST, "KW_STATIC_CAST"},
	{KW_STRUCT, "KW_STRUCT"},
	{KW_SWITCH, "KW_SWITCH"},
	{KW_TEMPLATE, "KW_TEMPLATE"},
	{KW_THIS, "KW_THIS"},
	{KW_THREAD_LOCAL, "KW_THREAD_LOCAL"},
	{KW_THROW, "KW_THROW"},
	{KW_TRUE, "KW_TRUE"},
	{KW_TRY, "KW_TRY"},
	{KW_TYPEDEF, "KW_TYPEDEF"},
	{KW_TYPEID, "KW_TYPEID"},
	{KW_TYPENAME, "KW_TYPENAME"},
	{KW_UNION, "KW_UNION"},
	{KW_UNSIGNED, "KW_UNSIGNED"},
	{KW_USING, "KW_USING"},
	{KW_VIRTUAL, "KW_VIRTUAL"},
	{KW_VOID, "KW_VOID"},
	{KW_VOLATILE, "KW_VOLATILE"},
	{KW_WCHAR_T, "KW_WCHAR_T"},
	{KW_WHILE, "KW_WHILE"},
	{OP_LBRACE, "OP_LBRACE"},
	{OP_RBRACE, "OP_RBRACE"},
	{OP_LSQUARE, "OP_LSQUARE"},
	{OP_RSQUARE, "OP_RSQUARE"},
	{OP_LPAREN, "OP_LPAREN"},
	{OP_RPAREN, "OP_RPAREN"},
	{OP_BOR, "OP_BOR"},
	{OP_XOR, "OP_XOR"},
	{OP_COMPL, "OP_COMPL"},
	{OP_AMP, "OP_AMP"},
	{OP_LNOT, "OP_LNOT"},
	{OP_SEMICOLON, "OP_SEMICOLON"},
	{OP_COLON, "OP_COLON"},
	{OP_DOTS, "OP_DOTS"},
	{OP_QMARK, "OP_QMARK"},
	{OP_COLON2, "OP_COLON2"},
	{OP_DOT, "OP_DOT"},
	{OP_DOTSTAR, "OP_DOTSTAR"},
	{OP_PLUS, "OP_PLUS"},
	{OP_MINUS, "OP_MINUS"},
	{OP_STAR, "OP_STAR"},
	{OP_DIV, "OP_DIV"},
	{OP_MOD, "OP_MOD"},
	{OP_ASS, "OP_ASS"},
	{OP_LT, "OP_LT"},
	{OP_GT, "OP_GT"},
	{OP_PLUSASS, "OP_PLUSASS"},
	{OP_MINUSASS, "OP_MINUSASS"},
	{OP_STARASS, "OP_STARASS"},
	{OP_DIVASS, "OP_DIVASS"},
	{OP_MODASS, "OP_MODASS"},
	{OP_XORASS, "OP_XORASS"},
	{OP_BANDASS, "OP_BANDASS"},
	{OP_BORASS, "OP_BORASS"},
	{OP_LSHIFT, "OP_LSHIFT"},
	{OP_RSHIFT, "OP_RSHIFT"},
	{OP_RSHIFTASS, "OP_RSHIFTASS"},
	{OP_LSHIFTASS, "OP_LSHIFTASS"},
	{OP_EQ, "OP_EQ"},
	{OP_NE, "OP_NE"},
	{OP_LE, "OP_LE"},
	{OP_GE, "OP_GE"},
	{OP_LAND, "OP_LAND"},
	{OP_LOR, "OP_LOR"},
	{OP_INC, "OP_INC"},
	{OP_DEC, "OP_DEC"},
	{OP_COMMA, "OP_COMMA"},
	{OP_ARROWSTAR, "OP_ARROWSTAR"},
	{OP_ARROW, "OP_ARROW"}
};

namespace
{

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

bool IsIdentifierSuffixBodyByte(unsigned char c)
{
	return c == '_' || (c >= '0' && c <= '9') ||
		(c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z') ||
		c >= 0x80;
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

bool ParseCharacterLiteral(const string& source,
                           LiteralEncoding& encoding,
                           string& ud_suffix,
                           vector<uint32_t>& code_points)
{
	const size_t prefix_len = PrefixLengthForQuotedLiteral(source, '\'', encoding);
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

}  // namespace

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

bool FundamentalTypeIsUnsigned(EFundamentalType type)
{
	return type == FT_UNSIGNED_CHAR || type == FT_UNSIGNED_SHORT_INT ||
		type == FT_UNSIGNED_INT || type == FT_UNSIGNED_LONG_INT ||
		type == FT_UNSIGNED_LONG_LONG_INT || type == FT_CHAR16_T ||
		type == FT_CHAR32_T;
}

bool AnalyzeIntegerLiteral(const string& source, IntegerLiteralInfo& out)
{
	IntegerCore core;
	if (!ParseIntegerCore(source, core))
		return false;

	out.type = FT_INT;
	out.value = 0;
	out.user_defined = false;
	out.ud_suffix.clear();
	out.prefix.clear();

	const string suffix = source.substr(core.digits_end);
	if (IsValidUdSuffix(suffix))
	{
		out.user_defined = true;
		out.ud_suffix = suffix;
		out.prefix = source.substr(0, core.digits_end);
		return true;
	}

	IntSuffix int_suffix;
	if (!ParseIntegerSuffix(suffix, int_suffix))
		return false;

	unsigned long long value = 0;
	if (!ParseIntegerValue(source, core, value))
		return false;

	const vector<EFundamentalType> candidates =
		IntegerCandidateTypes(core.decimal, int_suffix);
	for (size_t i = 0; i < candidates.size(); ++i)
	{
		if (FitsUnsigned(value, candidates[i]))
		{
			out.type = candidates[i];
			out.value = value;
			return true;
		}
	}
	return false;
}

bool AnalyzeCharacterLiteral(const string& source,
                             bool user_defined,
                             CharacterLiteralInfo& out)
{
	LiteralEncoding encoding = LiteralEncoding::Ordinary;
	string ud_suffix;
	vector<uint32_t> code_points;
	if (!ParseCharacterLiteral(source, encoding, ud_suffix, code_points) ||
	    code_points.size() != 1 ||
	    (user_defined && !IsValidUdSuffix(ud_suffix)) ||
	    (!user_defined && !ud_suffix.empty()))
		return false;

	const uint32_t cp = code_points[0];
	EFundamentalType type = FT_CHAR;
	if (encoding == LiteralEncoding::Ordinary)
		type = cp <= 127 ? FT_CHAR : FT_INT;
	else if (encoding == LiteralEncoding::U)
	{
		if (cp > 0xFFFF)
			return false;
		type = FT_CHAR16_T;
	}
	else if (encoding == LiteralEncoding::UpperU)
		type = FT_CHAR32_T;
	else if (encoding == LiteralEncoding::L)
		type = FT_WCHAR_T;
	else
		return false;

	out.encoding = encoding;
	out.type = type;
	out.code_point = cp;
	out.ud_suffix = ud_suffix;
	return true;
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
		cp = ((c0 & 0x07) << 18) | ((c1 & 0x3F) << 12) |
			((c2 & 0x3F) << 6) | (c3 & 0x3F);
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
			return false;
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

// convert integer [0,15] to hexadecimal digit
char ValueToHexChar(int c)
{
	switch (c)
	{
	case 0: return '0';
	case 1: return '1';
	case 2: return '2';
	case 3: return '3';
	case 4: return '4';
	case 5: return '5';
	case 6: return '6';
	case 7: return '7';
	case 8: return '8';
	case 9: return '9';
	case 10: return 'A';
	case 11: return 'B';
	case 12: return 'C';
	case 13: return 'D';
	case 14: return 'E';
	case 15: return 'F';
	default: throw logic_error("ValueToHexChar of nonhex value");
	}
}

// hex dump memory range
string HexDump(const void* pdata, size_t nbytes)
{
	unsigned char* p = (unsigned char*) pdata;

	string s(nbytes*2, '?');

	for (size_t i = 0; i < nbytes; i++)
	{
		s[2*i+0] = ValueToHexChar((p[i] & 0xF0) >> 4);
		s[2*i+1] = ValueToHexChar((p[i] & 0x0F) >> 0);
	}

	return s;
}


void DebugPostTokenOutputStream::emit_invalid(const string& source)
{
	cout << "invalid " << source << endl;
}

void DebugPostTokenOutputStream::emit_simple(const string& source, ETokenType token_type)
{
	cout << "simple " << source << " " << TokenTypeToStringMap.at(token_type) << endl;
}

void DebugPostTokenOutputStream::emit_identifier(const string& source)
{
	cout << "identifier " << source << endl;
}

void DebugPostTokenOutputStream::emit_literal(const string& source,
                                             EFundamentalType type,
                                             const void* data,
                                             size_t nbytes)
{
	cout << "literal " << source << " " << FundamentalTypeToStringMap.at(type) << " " << HexDump(data, nbytes) << endl;
}

void DebugPostTokenOutputStream::emit_literal_array(const string& source,
                                                   size_t num_elements,
                                                   EFundamentalType type,
                                                   const void* data,
                                                   size_t nbytes)
{
	cout << "literal " << source << " array of " << num_elements << " " << FundamentalTypeToStringMap.at(type) << " " << HexDump(data, nbytes) << endl;
}

void DebugPostTokenOutputStream::emit_user_defined_literal_character(const string& source,
                                                                    const string& ud_suffix,
                                                                    EFundamentalType type,
                                                                    const void* data,
                                                                    size_t nbytes)
{
	cout << "user-defined-literal " << source << " " << ud_suffix << " character " << FundamentalTypeToStringMap.at(type) << " " << HexDump(data, nbytes) << endl;
}

void DebugPostTokenOutputStream::emit_user_defined_literal_string_array(const string& source,
                                                                       const string& ud_suffix,
                                                                       size_t num_elements,
                                                                       EFundamentalType type,
                                                                       const void* data,
                                                                       size_t nbytes)
{
	cout << "user-defined-literal " << source << " " << ud_suffix << " string array of " << num_elements << " " << FundamentalTypeToStringMap.at(type) << " " << HexDump(data, nbytes) << endl;
}

void DebugPostTokenOutputStream::emit_user_defined_literal_integer(const string& source,
                                                                  const string& ud_suffix,
                                                                  const string& prefix)
{
	cout << "user-defined-literal " << source << " " << ud_suffix << " integer " << prefix << endl;
}

void DebugPostTokenOutputStream::emit_user_defined_literal_floating(const string& source,
                                                                   const string& ud_suffix,
                                                                   const string& prefix)
{
	cout << "user-defined-literal " << source << " " << ud_suffix << " floating " << prefix << endl;
}

void DebugPostTokenOutputStream::emit_eof()
{
	cout << "eof" << endl;
}

// use these 3 functions to scan `floating-literals` (see PA2)
// for example PA2Decode_float("12.34") returns "12.34" as a `float` type
float PA2Decode_float(const string& s)
{
	istringstream iss(s);
	float x;
	iss >> x;
	return x;
}

double PA2Decode_double(const string& s)
{
	istringstream iss(s);
	double x;
	iss >> x;
	return x;
}

long double PA2Decode_long_double(const string& s)
{
	istringstream iss(s);
	long double x;
	iss >> x;
	return x;
}
