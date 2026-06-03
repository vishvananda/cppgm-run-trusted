#pragma once

#include <string>
#include <vector>

#include "preproc_support.h"

using namespace std;

namespace nsinit {

struct Options
{
	preproc::Options preprocess;
};

void compile_to_file(const vector<string>& srcfiles,
                     const Options& options,
                     const string& outfile);

}  // namespace nsinit
