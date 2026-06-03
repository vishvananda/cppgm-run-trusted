#pragma once

#include <istream>
#include <ostream>
#include <vector>

#include "pp_token.h"

using namespace std;

namespace posttoken {

void emit_posttokens(const vector<PPToken>& tokens);
void emit_posttokens(const vector<PPToken>& tokens, ostream& out);
bool emit_posttokens_checked(const vector<PPToken>& tokens, ostream& out);
void run_posttoken(istream& in);

}  // namespace posttoken
