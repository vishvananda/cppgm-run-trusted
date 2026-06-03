#pragma once

#include <set>
#include <string>
#include <vector>

using namespace std;

#include "IPPTokenStream.h"

enum class PPTokenKind
{
	Whitespace,
	NewLine,
	HeaderName,
	Identifier,
	PPNumber,
	CharacterLiteral,
	UserDefinedCharacterLiteral,
	StringLiteral,
	UserDefinedStringLiteral,
	PreprocessingOpOrPunc,
	NonWhitespaceChar,
	EndOfFile,
	Placemarker
};

struct PPToken
{
	PPTokenKind kind;
	string text;
	set<string> unavailable;
	bool active_paste;

	PPToken() : kind(PPTokenKind::Whitespace), active_paste(false) {}
	PPToken(PPTokenKind k, const string& s)
		: kind(k), text(s), active_paste(false) {}
};

struct PPTokenCollector : IPPTokenStream
{
	vector<PPToken> tokens;

	void emit_whitespace_sequence();
	void emit_new_line();
	void emit_header_name(const string& data);
	void emit_identifier(const string& data);
	void emit_pp_number(const string& data);
	void emit_character_literal(const string& data);
	void emit_user_defined_character_literal(const string& data);
	void emit_string_literal(const string& data);
	void emit_user_defined_string_literal(const string& data);
	void emit_preprocessing_op_or_punc(const string& data);
	void emit_non_whitespace_char(const string& data);
	void emit_eof();
};

bool IsWhitespace(const PPToken& token);
bool IsNewLine(const PPToken& token);
bool IsRealToken(const PPToken& token);
bool IsIdentifier(const PPToken& token);
bool IsIdentifier(const PPToken& token, const string& text);
bool IsOp(const PPToken& token, const string& text);
bool IsHash(const PPToken& token);
bool IsHashHash(const PPToken& token);
bool IsActivePaste(const PPToken& token);

PPToken MakeWhitespaceToken();
PPToken MakeStringLiteralToken(const string& text);
PPToken MakePlacemarkerToken();

void EmitPPToken(const PPToken& token, IPPTokenStream& out);
void EmitPPTokens(const vector<PPToken>& tokens, IPPTokenStream& out);
vector<PPToken> TokenizePPString(const string& source);
