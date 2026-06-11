#include "lowir2native.h"
#include "lowir2cy86.h"
#include "lowir2native_mir_dumper.h"
#include "lowir2native_mir_helpers.h"

#include <stdexcept>
#include <string>
#include <vector>

using namespace std;

namespace lowir2native {

void write_native_file(const lowir2cy86::Program& program,
                       const Options& options);

void write_machine_ir_file(const lowir2cy86::Program& program,
                           const Options& options)
{
	MirDumper dumper(program, effective_target(options));
	write_text_file(options.machine_ir_file, dumper.dump());
}

void compile(const vector<string>& srcfiles, const Options& options)
{
	if (!options.target.empty() && options.target != "linux")
		throw runtime_error("unsupported target");
	lowir2cy86::Program program = lowir2cy86::parse_files(srcfiles);
	compile_program(program, options);
}

void compile_program(lowir2cy86::Program program, const Options& options)
{
	if (!options.target.empty() && options.target != "linux")
		throw runtime_error("unsupported target");
	lowir2cy86::validate_and_layout_allow_f80(program);
	if (!options.machine_ir_file.empty())
		write_machine_ir_file(program, options);
	if (!options.outfile.empty())
		write_native_file(program, options);
}

}  // namespace lowir2native
