// (C) 2013 CPPGM Foundation www.cppgm.org.  All rights reserved.

#include <ctime>
#include <iostream>
#include <stdexcept>
#include <string>
#include <vector>

#include "cy86_model.h"

using namespace std;

namespace
{

preproc::Options MakePreprocOptions()
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

cy86::Options MakeCy86Options(const string& target)
{
	cy86::Options options;
	options.preprocess = MakePreprocOptions();
	options.target = target;
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

		string target;
		string outfile;
		vector<string> srcfiles;
		for (size_t i = 0; i < args.size(); ++i)
		{
			if (args[i] == "--target")
			{
				if (i + 1 >= args.size())
					throw logic_error("missing target after --target");
				target = args[++i];
			}
			else if (args[i] == "-o")
			{
				if (i + 1 >= args.size())
					throw logic_error("missing output file after -o");
				outfile = args[++i];
			}
			else
				srcfiles.push_back(args[i]);
		}

		if (outfile.empty() || srcfiles.empty())
			throw logic_error("invalid usage");
		cy86::compile_to_file(srcfiles, MakeCy86Options(target), outfile);
	}
	catch (exception& e)
	{
		cerr << "ERROR: " << e.what() << endl;
		return EXIT_FAILURE;
	}
	return EXIT_SUCCESS;
}
