#pragma once

#include <string>
#include <vector>

#include "lowir2cy86.h"

using namespace std;

namespace lowir2native {

struct Options
{
	string target;
	string outfile;
	string machine_ir_file;
	vector<string> external_objects;
};

void compile(const vector<string>& srcfiles, const Options& options);
void compile_program(lowir2cy86::Program program, const Options& options);

}  // namespace lowir2native
