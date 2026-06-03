#include "nsinit_support.h"

#include <fstream>
#include <stdexcept>

#include "nsinit_internal.h"

using namespace std;

namespace nsinit {

void compile_to_file(const vector<string>& srcfiles,
                     const Options& options,
                     const string& outfile)
{
	Program program;
	for (size_t i = 0; i < srcfiles.size(); ++i)
		program.translation_units.push_back(
			parse_source_file(srcfiles[i], options, program));
	link_program(program);
	analyze_program_initializers(program);
	vector<char> image;
	write_program_image(program, image);

	ofstream out(outfile.c_str(), ios::binary);
	if (!out)
		throw runtime_error("cannot open output file");
	if (!image.empty())
		out.write(image.data(), static_cast<streamsize>(image.size()));
}

}  // namespace nsinit
