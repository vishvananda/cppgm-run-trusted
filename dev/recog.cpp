// (C) 2013 CPPGM Foundation www.cppgm.org.  All rights reserved.

#include <vector>
#include <string>
#include <stdexcept>
#include <fstream>
#include <iostream>
#include <cstdlib>
#include <ctime>

#include "recog_support.h"

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

recog::Options MakeRecogOptions()
{
	recog::Options options;
	options.preprocess = MakePreprocOptions();
	return options;
}

}  // namespace

int main(int argc, char** argv)
{
	try
	{
		vector<string> args;

		for (int i = 1; i < argc; i++)
			args.emplace_back(argv[i]);

		if (args.size() < 3 || args[0] != "-o")
			throw logic_error("invalid usage");

		string outfile = args[1];
		size_t nsrcfiles = args.size() - 2;

		ofstream out(outfile);
		if (!out)
			throw runtime_error("cannot open output file");

		out << "recog " << nsrcfiles << endl;
		const recog::Options options = MakeRecogOptions();

		for (size_t i = 0; i < nsrcfiles; i++)
		{
			string srcfile = args[i+2];

			try
			{
				bool ok = recog::recognize_source_file(srcfile, options);
				out << srcfile << (ok ? " OK" : " BAD") << endl;
			}
			catch (const exception& e)
			{
				cerr << e.what() << endl;
				out << srcfile << " BAD" << endl;
			}
		}
	}
	catch (exception& e)
	{
		cerr << "ERROR: " << e.what() << endl;
		return EXIT_FAILURE;
	}
	return EXIT_SUCCESS;
}
