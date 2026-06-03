#pragma once

#include <functional>
#include <iosfwd>
#include <string>
#include <vector>

#include "pp_token.h"

namespace ctrlexpr {

typedef std::function<bool(const std::string&)> DefinedPredicate;

bool evaluate_tokens(const std::vector<PPToken>& tokens,
                     const DefinedPredicate& is_defined,
                     bool& out);
void run_ctrlexpr(std::istream& in, std::ostream& out);

}  // namespace ctrlexpr
