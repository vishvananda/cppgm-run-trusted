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
	string source_file;
	int source_line;
	int source_column;

	PPToken() : kind(PPTokenKind::Whitespace), active_paste(false),
		source_line(0), source_column(0) {}
	PPToken(PPTokenKind k, const string& s)
		: kind(k), text(s), active_paste(false),
		  source_line(0), source_column(0) {}
};

struct PPTokenCollector : IPPTokenStream
{
	vector<PPToken> tokens;
	string source_file;
	int pending_line;
	int pending_column;

	PPTokenCollector() : pending_line(0), pending_column(0) {}

	void note_source_location(int line, int column);
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

void SetTokenLocation(PPToken& token,
                      const string& file,
                      int line,
                      int column);
void CopyTokenLocation(PPToken& token, const PPToken& from);
void EmitPPToken(const PPToken& token, IPPTokenStream& out);
void EmitPPTokens(const vector<PPToken>& tokens, IPPTokenStream& out);
vector<PPToken> TokenizePPString(const string& source);
