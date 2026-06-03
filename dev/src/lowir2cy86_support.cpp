#include "lowir2cy86.h"

#include <fstream>
#include <stdexcept>

using namespace std;

namespace lowir2cy86 {

void compile_to_file(const vector<string>& srcfiles, const string& outfile)
{
	Program program = parse_files(srcfiles);
	validate_and_layout(program);
	const string text = emit_cy86(program);
	ofstream out(outfile.c_str());
	if (!out)
		throw runtime_error("cannot open output file");
	out << text;
	out.close();
	if (!out)
		throw runtime_error("cannot write output file");
}

}  // namespace lowir2cy86
