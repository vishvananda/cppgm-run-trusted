#pragma once

#include <string>
#include <vector>

using namespace std;

namespace lowir2native {

struct Options
{
	string target;
	string outfile;
	string machine_ir_file;
};

void compile(const vector<string>& srcfiles, const Options& options);

}  // namespace lowir2native
