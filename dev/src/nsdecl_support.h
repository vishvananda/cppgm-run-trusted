#pragma once

#include <iosfwd>
#include <string>
#include <vector>

#include "preproc_support.h"

using namespace std;

namespace nsdecl {

struct Options
{
	preproc::Options preprocess;
};

void describe_translation_units(const vector<string>& srcfiles,
                                const Options& options,
                                ostream& out);

}  // namespace nsdecl
