#pragma once

#include <istream>
#include <ostream>
#include <vector>

#include "pp_token.h"
#include "posttoken_support.h"

using namespace std;

namespace posttoken {

enum class TokenKind
{
	Invalid,
	Simple,
	Identifier,
	Literal,
	EndOfFile
};

struct Token
{
	TokenKind kind;
	string source;
	ETokenType token_type;

	Token() : kind(TokenKind::Invalid), token_type(OP_LBRACE) {}
	Token(TokenKind k, const string& s)
		: kind(k), source(s), token_type(OP_LBRACE) {}
	Token(const string& s, ETokenType tt)
		: kind(TokenKind::Simple), source(s), token_type(tt) {}
};

void emit_posttokens(const vector<PPToken>& tokens);
void emit_posttokens(const vector<PPToken>& tokens, ostream& out);
bool emit_posttokens_checked(const vector<PPToken>& tokens, ostream& out);
bool collect_posttokens_checked(const vector<PPToken>& tokens,
                                vector<Token>& out);
void run_posttoken(istream& in);

}  // namespace posttoken
