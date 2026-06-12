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
#include "posttoken_pipeline.h"
#include "pp_token.h"
#include "pptoken_lib.h"

#include "posttoken_support.h"

namespace
{

struct ParsedStringPiece
{
	string source;
	LiteralEncoding encoding;
	string ud_suffix;
	bool valid_suffix;
	vector<uint32_t> code_points;
};

template <class Output>
void EmitIntegerValue(Output& output,
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

bool ParseBinaryExponentPart(const string& s, size_t& pos)
{
	if (pos >= s.size() || (s[pos] != 'p' && s[pos] != 'P'))
		return false;
	++pos;
	if (pos < s.size() && (s[pos] == '+' || s[pos] == '-'))
		++pos;
	const size_t digits_begin = pos;
	while (pos < s.size() && IsAsciiDigit(s[pos]))
		++pos;
	return pos > digits_begin;
}

bool ParseHexFloatingCore(const string& s, size_t& end)
{
	if (s.size() < 3 || s[0] != '0' || (s[1] != 'x' && s[1] != 'X'))
		return false;
	size_t pos = 2;
	const size_t leading_begin = pos;
	while (pos < s.size() && IsHexDigitChar(s[pos]))
		++pos;
	const bool has_leading_digits = pos > leading_begin;
	bool has_dot = false;
	bool has_fraction_digits = false;
	if (pos < s.size() && s[pos] == '.')
	{
		has_dot = true;
		++pos;
		const size_t fraction_begin = pos;
		while (pos < s.size() && IsHexDigitChar(s[pos]))
			++pos;
		has_fraction_digits = pos > fraction_begin;
	}
	if (!has_leading_digits && !has_fraction_digits)
		return false;
	size_t exponent_pos = pos;
	if (!ParseBinaryExponentPart(s, exponent_pos))
		return false;
	pos = exponent_pos;
	(void)has_dot;
	end = pos;
	return true;
}

bool ParseFloatingCore(const string& s, size_t& end)
{
	if (s.size() >= 2 && s[0] == '0' && (s[1] == 'x' || s[1] == 'X'))
		return ParseHexFloatingCore(s, end);

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

template <class Output>
void EmitFloatingLiteral(Output& output,
                         const string& source,
                         char suffix)
{
	if (suffix == 'f' || suffix == 'F')
	{
		float x = PA2Decode_float(source);
		output.emit_literal(source, FT_FLOAT, &x, sizeof(x));
	}
	else if (suffix == 'l' || suffix == 'L' ||
	         suffix == 'q' || suffix == 'Q')
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

struct CollectPostTokenOutputStream
{
	vector<posttoken::Token>* tokens;

	explicit CollectPostTokenOutputStream(vector<posttoken::Token>& out)
		: tokens(&out)
	{
	}

	void emit_invalid(const string& source)
	{
		tokens->push_back(posttoken::Token(posttoken::TokenKind::Invalid, source));
	}

	void emit_simple(const string& source, ETokenType token_type)
	{
		tokens->push_back(posttoken::Token(source, token_type));
	}

	void emit_identifier(const string& source)
	{
		tokens->push_back(posttoken::Token(posttoken::TokenKind::Identifier, source));
	}

	void emit_literal(const string& source,
	                  EFundamentalType type,
	                  const void* data,
	                  size_t nbytes)
	{
		(void)type;
		(void)data;
		(void)nbytes;
		tokens->push_back(posttoken::Token(posttoken::TokenKind::Literal, source));
	}

	void emit_literal_array(const string& source,
	                        size_t num_elements,
	                        EFundamentalType type,
	                        const void* data,
	                        size_t nbytes)
	{
		(void)num_elements;
		emit_literal(source, type, data, nbytes);
	}

	void emit_user_defined_literal_character(const string& source,
	                                         const string& ud_suffix,
	                                         EFundamentalType type,
	                                         const void* data,
	                                         size_t nbytes)
	{
		(void)ud_suffix;
		emit_literal(source, type, data, nbytes);
	}

	void emit_user_defined_literal_string_array(const string& source,
	                                            const string& ud_suffix,
	                                            size_t num_elements,
	                                            EFundamentalType type,
	                                            const void* data,
	                                            size_t nbytes)
	{
		(void)ud_suffix;
		(void)num_elements;
		emit_literal(source, type, data, nbytes);
	}

	void emit_user_defined_literal_integer(const string& source,
	                                       const string& ud_suffix,
	                                       const string& prefix)
	{
		(void)ud_suffix;
		(void)prefix;
		tokens->push_back(posttoken::Token(posttoken::TokenKind::Literal, source));
	}

	void emit_user_defined_literal_floating(const string& source,
	                                        const string& ud_suffix,
	                                        const string& prefix)
	{
		(void)ud_suffix;
		(void)prefix;
		tokens->push_back(posttoken::Token(posttoken::TokenKind::Literal, source));
	}

	void emit_eof()
	{
		tokens->push_back(posttoken::Token(posttoken::TokenKind::EndOfFile, ""));
	}
};

template <class Output>
struct BasicPostTokenStream : IPPTokenStream
{
	Output output;
	vector<ParsedStringPiece> pending_strings;
	bool invalid_seen;

	explicit BasicPostTokenStream(const Output& out)
		: output(out), invalid_seen(false)
	{
	}

	void emit_whitespace_sequence()
	{
	}

	void emit_new_line()
	{
	}

	void emit_header_name(const string& data)
	{
		flush_strings();
		emit_invalid(data);
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
			emit_invalid(data);
			return;
		}
		unordered_map<string, ETokenType>::const_iterator it = StringToTokenTypeMap.find(data);
		if (it != StringToTokenTypeMap.end())
			output.emit_simple(data, it->second);
		else
			emit_invalid(data);
	}

	void emit_non_whitespace_char(const string& data)
	{
		flush_strings();
		emit_invalid(data);
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
			emit_invalid(source);
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
			emit_invalid(source);
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
		     data[core_end] == 'l' || data[core_end] == 'L' ||
		     data[core_end] == 'q' || data[core_end] == 'Q'))
		{
			EmitFloatingLiteral(output, data, data[core_end]);
			return true;
		}
		const string suffix = data.substr(core_end);
		if (suffix == "f16" || suffix == "F16" ||
		    suffix == "f32" || suffix == "F32" ||
		    suffix == "bf16" || suffix == "BF16")
		{
			float x = PA2Decode_float(data.substr(0, core_end));
			output.emit_literal(data, FT_FLOAT, &x, sizeof(x));
			return true;
		}
		if (suffix == "f64" || suffix == "F64")
		{
			double x = PA2Decode_double(data.substr(0, core_end));
			output.emit_literal(data, FT_DOUBLE, &x, sizeof(x));
			return true;
		}
		if (suffix == "f128" || suffix == "F128")
		{
			long double x = PA2Decode_long_double(data.substr(0, core_end));
			output.emit_literal(data, FT_LONG_DOUBLE, &x, sizeof(x));
			return true;
		}
		if (IsValidUdSuffix(suffix))
		{
			output.emit_user_defined_literal_floating(data, suffix, data.substr(0, core_end));
			return true;
		}
		emit_invalid(data);
		return true;
	}

	void try_emit_integer_or_invalid(const string& data)
	{
		IntegerLiteralInfo info;
		if (!AnalyzeIntegerLiteral(data, info))
			emit_invalid(data);
		else if (info.user_defined)
			output.emit_user_defined_literal_integer(data, info.ud_suffix, info.prefix);
		else
			EmitIntegerValue(output, data, info.type, info.value);
	}

	void emit_character(const string& data, bool user_defined)
	{
		CharacterLiteralInfo info;
		if (!AnalyzeCharacterLiteral(data, user_defined, info))
		{
			emit_invalid(data);
			return;
		}

		vector<unsigned char> bytes;
		if (info.type == FT_CHAR)
			AppendByte(bytes, info.code_point);
		else if (info.type == FT_CHAR16_T)
			AppendUint16(bytes, info.code_point);
		else if (info.type == FT_INT || info.type == FT_CHAR32_T ||
		         info.type == FT_WCHAR_T)
			AppendUint32(bytes, info.code_point);
		else
		{
			emit_invalid(data);
			return;
		}

		if (user_defined)
			output.emit_user_defined_literal_character(data, info.ud_suffix, info.type, bytes.data(), bytes.size());
		else
			output.emit_literal(data, info.type, bytes.data(), bytes.size());
	}

	void emit_invalid(const string& data)
	{
		invalid_seen = true;
		output.emit_invalid(data);
	}
};

}  // namespace

namespace posttoken {

void emit_posttokens(const vector<PPToken>& tokens)
{
	emit_posttokens(tokens, cout);
}

void emit_posttokens(const vector<PPToken>& tokens, ostream& out)
{
	(void)emit_posttokens_checked(tokens, out);
}

bool emit_posttokens_checked(const vector<PPToken>& tokens, ostream& out)
{
	DebugPostTokenOutputStream debug(out);
	BasicPostTokenStream<DebugPostTokenOutputStream> output(debug);
	EmitPPTokens(tokens, output);
	output.emit_eof();
	return !output.invalid_seen;
}

bool collect_posttokens_checked(const vector<PPToken>& tokens,
                                vector<Token>& out)
{
	out.clear();
	CollectPostTokenOutputStream collector(out);
	BasicPostTokenStream<CollectPostTokenOutputStream> output(collector);
	EmitPPTokens(tokens, output);
	output.emit_eof();
	return !output.invalid_seen;
}

void run_posttoken(istream& in)
{
	DebugPostTokenOutputStream debug(cout);
	BasicPostTokenStream<DebugPostTokenOutputStream> output(debug);
	pptoken::run_pptoken(in, output);
}

}  // namespace posttoken
