#pragma once

#include <string>
#include <vector>

#include "preproc_support.h"

using namespace std;

namespace pa14 {

struct Options
{
	preproc::Options preprocess;
	bool native_lowering;
	bool host_object_lowering;
	bool hosted_compatibility;

	Options()
		: native_lowering(false),
		  host_object_lowering(false),
		  hosted_compatibility(false)
	{
	}
};

void emit_lowir(const vector<string>& srcfiles,
                const string& outfile,
                const Options& options);

}  // namespace pa14
