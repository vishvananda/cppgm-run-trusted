#pragma once

#include <iosfwd>
#include <string>
#include <vector>

#include "pp_token.h"

using namespace std;

namespace preproc {

struct Options
{
	string author;
	string build_date;
	string build_time;
};

void run_preproc(const vector<string>& srcfiles,
                 ostream& out,
                 const Options& options);
vector<PPToken> preprocess_source_file(const string& srcfile,
                                       const Options& options);

}  // namespace preproc
