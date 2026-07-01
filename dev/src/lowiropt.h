#pragma once

#include "lowir2cy86.h"

#include <map>
#include <string>
#include <vector>

using namespace std;

namespace lowiropt {

struct Options
{
	int optimization_level;
	string outfile;
	bool prune_unreachable_weak;

	Options() : optimization_level(0), prune_unreachable_weak(true) {}
};

void rebuild_program(lowir2cy86::Program& program);
void rebuild_function(lowir2cy86::Function& fn);
lowir2cy86::Type instruction_result_type(const lowir2cy86::Instruction& ins);
lowir2cy86::Type value_type(const lowir2cy86::Function& fn,
                            const lowir2cy86::Program& program,
                            const lowir2cy86::Value& value);
bool same_type(const lowir2cy86::Type& a, const lowir2cy86::Type& b);
bool is_terminator(lowir2cy86::InstrKind kind);
bool inline_o1_once(lowir2cy86::Program& program);
bool inline_o1_once(lowir2cy86::Program& program,
                    map<string, int>& inline_index_cache);
bool remove_unused_temps(lowir2cy86::Function& fn,
                         const lowir2cy86::Program& program);
bool promote_o2_slots_once(lowir2cy86::Program& program);
void canonicalize_optimized_program(lowir2cy86::Program& program,
                                    const lowir2cy86::Program& original,
                                    bool preserve_weak_order = false);
lowir2cy86::Program optimize_program(lowir2cy86::Program program,
                                     int level,
                                     bool prune_unreachable_weak = true);
void optimize_files_to_file(const vector<string>& srcfiles,
                            const Options& options);
string emit_lowir(const lowir2cy86::Program& program);
void write_lowir_file(const string& outfile, const string& text);

}  // namespace lowiropt
