// (C) 2013 CPPGM Foundation www.cppgm.org.  All rights reserved.

#include <iostream>
#include <string>

using namespace std;

#include "ctrlexpr_support.h"

// mock implementation of IsDefinedIdentifier for PA3
// return true iff first code point is odd
bool PA3Mock_IsDefinedIdentifier(const string& identifier)
{
	if (identifier.empty())
		return false;
	else
		return identifier[0] % 2;
}

int main(int argc, char** argv)
{
	(void)argc;
	(void)argv;
	ios::sync_with_stdio(false);
	cin.tie(NULL);
	try
	{
		ctrlexpr::run_ctrlexpr(cin, cout);
		return EXIT_SUCCESS;
	}
	catch (exception& e)
	{
		cerr << "ERROR: " << e.what() << endl;
		return EXIT_FAILURE;
	}
}
