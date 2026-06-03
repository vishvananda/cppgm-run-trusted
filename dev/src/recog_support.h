#pragma once

#include <string>

#include "preproc_support.h"

using namespace std;

namespace recog {

struct Options
{
	preproc::Options preprocess;
};

bool recognize_source_file(const string& srcfile, const Options& options);

}  // namespace recog
