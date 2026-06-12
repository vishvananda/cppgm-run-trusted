#pragma once

#include <iosfwd>
#include <string>
#include <vector>

#include "pp_token.h"

using namespace std;

namespace preproc {

struct MacroCommand
{
	enum Kind
	{
		Define,
		Undefine
	};

	Kind kind;
	string value;

	MacroCommand();
	MacroCommand(Kind kind, const string& value);
};

struct Options
{
	string author;
	string build_date;
	string build_time;
	vector<string> include_paths;
	vector<string> forced_includes;
	vector<MacroCommand> macro_commands;
	bool import_host_predefined_macros;
	bool import_host_include_paths;

	Options();
};

void run_preproc(const vector<string>& srcfiles,
                 ostream& out,
                 const Options& options);
vector<PPToken> preprocess_source_file(const string& srcfile,
                                       const Options& options);

}  // namespace preproc
