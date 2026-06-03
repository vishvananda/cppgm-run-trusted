#pragma once

#include <istream>
#include <vector>

#include "pp_token.h"

using namespace std;

namespace posttoken {

void emit_posttokens(const vector<PPToken>& tokens);
void run_posttoken(istream& in);

}  // namespace posttoken
