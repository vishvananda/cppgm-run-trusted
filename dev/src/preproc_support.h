#pragma once

#include <iosfwd>
#include <string>
#include <vector>

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

}  // namespace preproc
