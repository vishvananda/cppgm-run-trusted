#include <cstdlib>
#include <exception>
#include <iostream>
#include <string>

using namespace std;

#include "DebugPPTokenStream.h"
#include "pptoken_lib.h"

int main(int argc, char ** argv)
{
  (void)argc;
  (void)argv;
  try {
    DebugPPTokenStream output;
    pptoken::run_pptoken(cin, output);
    return EXIT_SUCCESS;
  } catch(const exception & e) {
    cerr << "ERROR:" << e.what() << endl;
    return EXIT_FAILURE;
  }
}
