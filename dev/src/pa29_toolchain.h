#pragma once

#include <string>
#include <vector>

#include "preproc_support.h"

using namespace std;

namespace pa29 {

struct Options
{
	preproc::Options preprocess;
	string target;
	int optimization_level;
	bool hosted_compatibility;
	vector<string> library_paths;
	vector<string> libraries;

	Options() : optimization_level(0), hosted_compatibility(false) {}
};

bool is_object_like_path(const string& path);
void compile_source_to_object(const string& srcfile,
                              const string& objfile,
                              const Options& options);
void link_inputs_to_executable(const vector<string>& inputs,
                               const string& outfile,
                               const Options& options);

}  // namespace pa29
