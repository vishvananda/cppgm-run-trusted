#pragma once

#include <iosfwd>

struct IPPTokenStream;

namespace pptoken {

void run_pptoken(std::istream & in, IPPTokenStream & output);

}  // namespace pptoken
