// (C) 2013 CPPGM Foundation www.cppgm.org.  All rights reserved.

#include <cstdlib>
#include <exception>
#include <iostream>

using namespace std;

#include "posttoken_pipeline.h"

int main(int argc, char** argv)
{
	(void)argc;
	(void)argv;
	try
	{
		posttoken::run_posttoken(cin);
		return EXIT_SUCCESS;
	}
	catch (exception& e)
	{
		cerr << "ERROR: " << e.what() << endl;
		return EXIT_FAILURE;
	}
}
