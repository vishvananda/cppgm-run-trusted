#pragma once

#include <string>
#include <vector>

#include "preproc_support.h"

using namespace std;

namespace pa11 {

struct Options
{
	preproc::Options preprocess;
};

void emit_types(const vector<string>& srcfiles,
                const string& outfile,
                const Options& options);

}  // namespace pa11
