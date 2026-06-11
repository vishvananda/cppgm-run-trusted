#pragma once

#include <cstddef>
#include <cstdint>
#include <iosfwd>
#include <map>
#include <string>
#include <unordered_map>
#include <vector>

using namespace std;

// See 3.9.1: Fundamental Types
enum EFundamentalType
{
	// 3.9.1.2
	FT_SIGNED_CHAR,
	FT_SHORT_INT,
	FT_INT,
	FT_LONG_INT,
	FT_LONG_LONG_INT,
	FT_INT128,

	// 3.9.1.3
	FT_UNSIGNED_CHAR,
	FT_UNSIGNED_SHORT_INT,
	FT_UNSIGNED_INT,
	FT_UNSIGNED_LONG_INT,
	FT_UNSIGNED_LONG_LONG_INT,
	FT_UNSIGNED_INT128,

	// 3.9.1.1 / 3.9.1.5
	FT_WCHAR_T,
	FT_CHAR,
	FT_CHAR16_T,
	FT_CHAR32_T,

	// 3.9.1.6
	FT_BOOL,

	// 3.9.1.8
	FT_FLOAT,
	FT_DOUBLE,
	FT_LONG_DOUBLE,

	// 3.9.1.9
	FT_VOID,

	// 3.9.1.10
	FT_NULLPTR_T
};


// token type enum for `simples`
enum ETokenType
{
	// keywords
	KW_ALIGNAS,
	KW_ALIGNOF,
	KW_ASM,
	KW_AUTO,
	KW_BOOL,
	KW_BREAK,
	KW_CASE,
	KW_CATCH,
	KW_CHAR,
	KW_CHAR16_T,
	KW_CHAR32_T,
	KW_CLASS,
	KW_CONST,
	KW_CONSTEXPR,
	KW_CONST_CAST,
	KW_CONTINUE,
	KW_DECLTYPE,
	KW_DEFAULT,
	KW_DELETE,
	KW_DO,
	KW_DOUBLE,
	KW_DYNAMIC_CAST,
	KW_ELSE,
	KW_ENUM,
	KW_EXPLICIT,
	KW_EXPORT,
	KW_EXTERN,
	KW_FALSE,
	KW_FLOAT,
	KW_FOR,
	KW_FRIEND,
	KW_GOTO,
	KW_IF,
	KW_INLINE,
	KW_INT,
	KW_LONG,
	KW_MUTABLE,
	KW_NAMESPACE,
	KW_NEW,
	KW_NOEXCEPT,
	KW_NULLPTR,
	KW_OPERATOR,
	KW_PRIVATE,
	KW_PROTECTED,
	KW_PUBLIC,
	KW_REGISTER,
	KW_REINTERPET_CAST,
	KW_RETURN,
	KW_SHORT,
	KW_SIGNED,
	KW_SIZEOF,
	KW_STATIC,
	KW_STATIC_ASSERT,
	KW_STATIC_CAST,
	KW_STRUCT,
	KW_SWITCH,
	KW_TEMPLATE,
	KW_THIS,
	KW_THREAD_LOCAL,
	KW_THROW,
	KW_TRUE,
	KW_TRY,
	KW_TYPEDEF,
	KW_TYPEID,
	KW_TYPENAME,
	KW_UNION,
	KW_UNSIGNED,
	KW_USING,
	KW_VIRTUAL,
	KW_VOID,
	KW_VOLATILE,
	KW_WCHAR_T,
	KW_WHILE,

	// operators/punctuation
	OP_LBRACE,
	OP_RBRACE,
	OP_LSQUARE,
	OP_RSQUARE,
	OP_LPAREN,
	OP_RPAREN,
	OP_BOR,
	OP_XOR,
	OP_COMPL,
	OP_AMP,
	OP_LNOT,
	OP_SEMICOLON,
	OP_COLON,
	OP_DOTS,
	OP_QMARK,
	OP_COLON2,
	OP_DOT,
	OP_DOTSTAR,
	OP_PLUS,
	OP_MINUS,
	OP_STAR,
	OP_DIV,
	OP_MOD,
	OP_ASS,
	OP_LT,
	OP_GT,
	OP_PLUSASS,
	OP_MINUSASS,
	OP_STARASS,
	OP_DIVASS,
	OP_MODASS,
	OP_XORASS,
	OP_BANDASS,
	OP_BORASS,
	OP_LSHIFT,
	OP_RSHIFT,
	OP_RSHIFTASS,
	OP_LSHIFTASS,
	OP_EQ,
	OP_NE,
	OP_LE,
	OP_GE,
	OP_LAND,
	OP_LOR,
	OP_INC,
	OP_DEC,
	OP_COMMA,
	OP_ARROWSTAR,
	OP_ARROW,
};


extern const map<EFundamentalType, string> FundamentalTypeToStringMap;
extern const unordered_map<string, ETokenType> StringToTokenTypeMap;
extern const map<ETokenType, string> TokenTypeToStringMap;

enum class LiteralEncoding
{
	Ordinary,
	U8,
	U,
	UpperU,
	L
};

struct IntegerLiteralInfo
{
	EFundamentalType type;
	unsigned long long value;
	bool user_defined;
	string ud_suffix;
	string prefix;
};

struct CharacterLiteralInfo
{
	LiteralEncoding encoding;
	EFundamentalType type;
	uint32_t code_point;
	string ud_suffix;
};

struct StringLiteralInfo
{
	LiteralEncoding encoding;
	EFundamentalType type;
	size_t elements;
	vector<unsigned char> bytes;
	string ud_suffix;
};

bool IsAsciiDigit(char c);
bool IsOctalDigit(char c);
bool IsHexDigitChar(char c);
int HexDigitValue(char c);
bool IsValidUdSuffix(const string& suffix);
bool FundamentalTypeIsUnsigned(EFundamentalType type);
bool AnalyzeIntegerLiteral(const string& source, IntegerLiteralInfo& out);
bool AnalyzeCharacterLiteral(const string& source,
                             bool user_defined,
                             CharacterLiteralInfo& out);
bool AnalyzeStringLiteral(const string& source, StringLiteralInfo& out);
bool DecodeUtf8At(const string& s, size_t& pos, uint32_t& cp);
bool IsValidCodePoint(uint32_t cp);
bool DecodeOrdinaryBody(const string& s,
                        size_t begin,
                        size_t end,
                        vector<uint32_t>& code_points);
size_t PrefixLengthForQuotedLiteral(const string& source,
                                    char quote,
                                    LiteralEncoding& encoding);
bool FindOrdinaryClosingQuote(const string& source,
                              size_t quote_pos,
                              char quote,
                              size_t& close_pos);
void AppendByte(vector<unsigned char>& bytes, uint32_t value);
void AppendUint16(vector<unsigned char>& bytes, uint32_t value);
void AppendUint32(vector<unsigned char>& bytes, uint32_t value);
void AppendUtf8CodePoint(vector<unsigned char>& bytes, uint32_t cp);

char ValueToHexChar(int c);
string HexDump(const void* pdata, size_t nbytes);

struct DebugPostTokenOutputStream
{
	DebugPostTokenOutputStream();
	explicit DebugPostTokenOutputStream(ostream& out);

	void emit_invalid(const string& source);
	void emit_simple(const string& source, ETokenType token_type);
	void emit_identifier(const string& source);
	void emit_literal(const string& source, EFundamentalType type, const void* data, size_t nbytes);
	void emit_literal_array(const string& source, size_t num_elements, EFundamentalType type, const void* data, size_t nbytes);
	void emit_user_defined_literal_character(const string& source, const string& ud_suffix, EFundamentalType type, const void* data, size_t nbytes);
	void emit_user_defined_literal_string_array(const string& source, const string& ud_suffix, size_t num_elements, EFundamentalType type, const void* data, size_t nbytes);
	void emit_user_defined_literal_integer(const string& source, const string& ud_suffix, const string& prefix);
	void emit_user_defined_literal_floating(const string& source, const string& ud_suffix, const string& prefix);
	void emit_eof();

private:
	ostream* out_;
};

float PA2Decode_float(const string& s);
double PA2Decode_double(const string& s);
long double PA2Decode_long_double(const string& s);
