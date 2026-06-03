#include "cy86_model.h"

#include <fstream>
#include <stdexcept>

#include "cy86_x86.h"

using namespace std;

namespace cy86 {
namespace {

extern "C" long int syscall(long int n, ...) throw ();

bool set_file_executable(const string& path)
{
	return syscall(90, path.c_str(), 0755) == 0;
}

}  // namespace

void compile_to_file(const vector<string>& srcfiles,
                     const Options& options,
                     const string& outfile)
{
	Program program = parse_program_files(srcfiles, options);
	vector<unsigned char> image = build_elf_image(program);
	ofstream out(outfile.c_str(), ios::binary);
	if (!out)
		throw runtime_error("cannot open output file");
	if (!image.empty())
		out.write(reinterpret_cast<const char*>(image.data()),
		          static_cast<streamsize>(image.size()));
	out.close();
	if (!out)
		throw runtime_error("cannot write output file");
	if (!set_file_executable(outfile))
		throw runtime_error("cannot make output executable");
}

}  // namespace cy86
