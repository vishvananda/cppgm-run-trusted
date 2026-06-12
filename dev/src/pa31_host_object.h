#pragma once

#include "lowir2cy86.h"

#include <string>

using namespace std;

namespace pa31 {

struct Options
{
	int optimization_level;

	Options() : optimization_level(0) {}
};

void write_host_object(lowir2cy86::Program& program,
                       const string& outfile,
                       const Options& options = Options());

}  // namespace pa31
