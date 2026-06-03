#include "pp_token.h"

#include <sstream>
#include <stdexcept>

#include "pptoken_lib.h"

using namespace std;

namespace
{

void AddToken(PPTokenCollector& collector, PPTokenKind kind, const string& text)
{
	PPToken token(kind, text);
	SetTokenLocation(token,
	                 collector.source_file,
	                 collector.pending_line,
	                 collector.pending_column);
	collector.tokens.push_back(token);
}

}  // namespace

void PPTokenCollector::note_source_location(int line, int column)
{
	pending_line = line;
	pending_column = column;
}

void PPTokenCollector::emit_whitespace_sequence()
{
	AddToken(*this, PPTokenKind::Whitespace, "");
}

void PPTokenCollector::emit_new_line()
{
	AddToken(*this, PPTokenKind::NewLine, "");
}

void PPTokenCollector::emit_header_name(const string& data)
{
	AddToken(*this, PPTokenKind::HeaderName, data);
}

void PPTokenCollector::emit_identifier(const string& data)
{
	AddToken(*this, PPTokenKind::Identifier, data);
}

void PPTokenCollector::emit_pp_number(const string& data)
{
	AddToken(*this, PPTokenKind::PPNumber, data);
}

void PPTokenCollector::emit_character_literal(const string& data)
{
	AddToken(*this, PPTokenKind::CharacterLiteral, data);
}

void PPTokenCollector::emit_user_defined_character_literal(const string& data)
{
	AddToken(*this, PPTokenKind::UserDefinedCharacterLiteral, data);
}

void PPTokenCollector::emit_string_literal(const string& data)
{
	AddToken(*this, PPTokenKind::StringLiteral, data);
}

void PPTokenCollector::emit_user_defined_string_literal(const string& data)
{
	AddToken(*this, PPTokenKind::UserDefinedStringLiteral, data);
}

void PPTokenCollector::emit_preprocessing_op_or_punc(const string& data)
{
	AddToken(*this, PPTokenKind::PreprocessingOpOrPunc, data);
}

void PPTokenCollector::emit_non_whitespace_char(const string& data)
{
	AddToken(*this, PPTokenKind::NonWhitespaceChar, data);
}

void PPTokenCollector::emit_eof()
{
	AddToken(*this, PPTokenKind::EndOfFile, "");
}

bool IsWhitespace(const PPToken& token)
{
	return token.kind == PPTokenKind::Whitespace ||
	       token.kind == PPTokenKind::NewLine;
}

bool IsNewLine(const PPToken& token)
{
	return token.kind == PPTokenKind::NewLine;
}

bool IsRealToken(const PPToken& token)
{
	return token.kind != PPTokenKind::Whitespace &&
	       token.kind != PPTokenKind::NewLine &&
	       token.kind != PPTokenKind::EndOfFile &&
	       token.kind != PPTokenKind::Placemarker;
}

bool IsIdentifier(const PPToken& token)
{
	return token.kind == PPTokenKind::Identifier;
}

bool IsIdentifier(const PPToken& token, const string& text)
{
	return IsIdentifier(token) && token.text == text;
}

bool IsOp(const PPToken& token, const string& text)
{
	return token.kind == PPTokenKind::PreprocessingOpOrPunc &&
	       token.text == text;
}

bool IsHash(const PPToken& token)
{
	return IsOp(token, "#") || IsOp(token, "%:");
}

bool IsHashHash(const PPToken& token)
{
	return IsOp(token, "##") || IsOp(token, "%:%:");
}

bool IsActivePaste(const PPToken& token)
{
	return IsHashHash(token) && token.active_paste;
}

PPToken MakeWhitespaceToken()
{
	return PPToken(PPTokenKind::Whitespace, "");
}

PPToken MakeStringLiteralToken(const string& text)
{
	return PPToken(PPTokenKind::StringLiteral, text);
}

PPToken MakePlacemarkerToken()
{
	return PPToken(PPTokenKind::Placemarker, "");
}

void SetTokenLocation(PPToken& token,
                      const string& file,
                      int line,
                      int column)
{
	token.source_file = file;
	token.source_line = line;
	token.source_column = column;
}

void CopyTokenLocation(PPToken& token, const PPToken& from)
{
	SetTokenLocation(token, from.source_file, from.source_line, from.source_column);
}

void EmitPPToken(const PPToken& token, IPPTokenStream& out)
{
	switch (token.kind)
	{
	case PPTokenKind::Whitespace: out.emit_whitespace_sequence(); break;
	case PPTokenKind::NewLine: out.emit_new_line(); break;
	case PPTokenKind::HeaderName: out.emit_header_name(token.text); break;
	case PPTokenKind::Identifier: out.emit_identifier(token.text); break;
	case PPTokenKind::PPNumber: out.emit_pp_number(token.text); break;
	case PPTokenKind::CharacterLiteral: out.emit_character_literal(token.text); break;
	case PPTokenKind::UserDefinedCharacterLiteral:
		out.emit_user_defined_character_literal(token.text);
		break;
	case PPTokenKind::StringLiteral: out.emit_string_literal(token.text); break;
	case PPTokenKind::UserDefinedStringLiteral:
		out.emit_user_defined_string_literal(token.text);
		break;
	case PPTokenKind::PreprocessingOpOrPunc:
		out.emit_preprocessing_op_or_punc(token.text);
		break;
	case PPTokenKind::NonWhitespaceChar:
		out.emit_non_whitespace_char(token.text);
		break;
	case PPTokenKind::EndOfFile: out.emit_eof(); break;
	case PPTokenKind::Placemarker: break;
	}
}

void EmitPPTokens(const vector<PPToken>& tokens, IPPTokenStream& out)
{
	for (size_t i = 0; i < tokens.size(); ++i)
		EmitPPToken(tokens[i], out);
}

vector<PPToken> TokenizePPString(const string& source)
{
	istringstream in(source);
	PPTokenCollector collector;
	pptoken::run_pptoken(in, collector);
	if (!collector.tokens.empty() &&
	    collector.tokens.back().kind == PPTokenKind::EndOfFile)
		collector.tokens.pop_back();
	return collector.tokens;
}
