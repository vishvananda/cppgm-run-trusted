// (C) 2013 CPPGM Foundation www.cppgm.org.  All rights reserved.

#include <cstdlib>
#include <ctime>
#include <fstream>
#include <iostream>
#include <stdexcept>
#include <string>
#include <vector>

using namespace std;

#include "preproc_support.h"

namespace
{

preproc::Options MakeOptions()
{
	time_t now = time(NULL);
	tm* local = localtime(&now);
	if (local == NULL)
		throw runtime_error("cannot read build time");
	char* text = asctime(local);
	if (text == NULL)
		throw runtime_error("cannot format build time");
	const string stamp(text);
	if (stamp.size() < 24)
		throw runtime_error("invalid build time");

	preproc::Options options;
	options.author = "Vishvananda Ishaya";
	options.build_date = stamp.substr(4, 6) + " " + stamp.substr(20, 4);
	options.build_time = stamp.substr(11, 8);
	return options;
}

}  // namespace

int main(int argc, char** argv)
{
	try
	{
		vector<string> args;
		for (int i = 1; i < argc; ++i)
			args.push_back(argv[i]);
		if (args.size() < 3 || args[0] != "-o")
			throw logic_error("invalid usage");

		ofstream out(args[1].c_str());
		if (!out)
			throw runtime_error("cannot open output file");

		vector<string> srcfiles;
		for (size_t i = 2; i < args.size(); ++i)
			srcfiles.push_back(args[i]);

		preproc::run_preproc(srcfiles, out, MakeOptions());
		return EXIT_SUCCESS;
	}
	catch (const exception& e)
	{
		cerr << "ERROR: " << e.what() << endl;
		return EXIT_FAILURE;
	}
}
