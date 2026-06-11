#pragma once

#include "lowir2cy86.h"

#include <string>

using namespace std;

namespace pa31 {

void write_host_object(lowir2cy86::Program& program, const string& outfile);

}  // namespace pa31
