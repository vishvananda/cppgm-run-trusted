#pragma once

#include <string>
#include <vector>

#include "preproc_support.h"

using namespace std;

namespace pa12 {

struct Options
{
	preproc::Options preprocess;
	bool hosted_compatibility;

	Options() : hosted_compatibility(false) {}
};

void emit_semantics(const vector<string>& srcfiles,
                    const string& outfile,
                    const Options& options);

}  // namespace pa12
