#include "lowir2native.h"

#include "cy86_model.h"
#include "lowir2cy86.h"
#include "lowir2native_mir_helpers.h"

#include <cstdio>
#include <map>
#include <set>
#include <string>
#include <vector>

using namespace std;

namespace lowir2native {
namespace {

string temp_cy86_path(const string& outfile)
{
	return outfile + ".lowir2native.cy86.tmp";
}

void note_temp_use(const lowir2cy86::Value& value, map<string, int>& uses)
{
	if (value.kind == lowir2cy86::ValueKind::Temp)
		++uses[value.text];
}

void count_instruction_temp_uses(const lowir2cy86::Instruction& ins,
                                 map<string, int>& uses)
{
	note_temp_use(ins.a, uses);
	note_temp_use(ins.b, uses);
	note_temp_use(ins.c, uses);
	for (size_t i = 0; i < ins.args.size(); ++i)
		note_temp_use(ins.args[i], uses);
	for (size_t i = 0; i < ins.switch_cases.size(); ++i)
		note_temp_use(ins.switch_cases[i].value, uses);
}

bool is_scalar_ptr_global(const lowir2cy86::Program& program, const string& name)
{
	map<string, size_t>::const_iterator it = program.global_by_name.find(name);
	if (it == program.global_by_name.end())
		return false;
	const lowir2cy86::Global& g = program.globals[it->second];
	return g.has_type && lowir2cy86::is_ptr_type(g.type);
}

void rewrite_indirect_global_pointer_callees(lowir2cy86::Program& program)
{
	const lowir2cy86::Type ptr_type = lowir2cy86::parse_type_text("ptr");
	for (size_t f = 0; f < program.functions.size(); ++f)
	{
		lowir2cy86::Function& fn = program.functions[f];
		map<string, int> uses;
		map<string, lowir2cy86::Instruction*> defs;
		set<string> indirect_callees;
		for (size_t b = 0; b < fn.blocks.size(); ++b)
			for (size_t i = 0; i < fn.blocks[b].instructions.size(); ++i)
			{
				lowir2cy86::Instruction& ins = fn.blocks[b].instructions[i];
				count_instruction_temp_uses(ins, uses);
				if (ins.has_dest)
					defs[ins.dest] = &ins;
				if (ins.kind == lowir2cy86::InstrKind::Call &&
				    ins.a.kind == lowir2cy86::ValueKind::Temp)
					indirect_callees.insert(ins.a.text);
			}
		for (set<string>::const_iterator it = indirect_callees.begin();
		     it != indirect_callees.end(); ++it)
		{
			if (uses[*it] != 1)
				continue;
			map<string, lowir2cy86::Instruction*>::iterator dit = defs.find(*it);
			if (dit == defs.end() || dit->second->kind != lowir2cy86::InstrKind::Addr ||
			    dit->second->a.kind != lowir2cy86::ValueKind::Global ||
			    !is_scalar_ptr_global(program, dit->second->a.text))
				continue;
			dit->second->kind = lowir2cy86::InstrKind::Load;
			dit->second->type = ptr_type;
		}
	}
}

}  // namespace

void write_native_file(const lowir2cy86::Program& program,
                       const Options& options)
{
	lowir2cy86::Program native_program = program;
	rewrite_indirect_global_pointer_callees(native_program);
	const string tmp = temp_cy86_path(options.outfile);
	write_text_file(tmp, lowir2cy86::emit_cy86_for_native(native_program));
	cy86::Options cy_options;
	cy_options.target = effective_target(options);
	cy_options.external_objects = options.external_objects;
	try
	{
		cy86::compile_to_file(vector<string>(1, tmp), cy_options, options.outfile);
	}
	catch (...)
	{
		remove(tmp.c_str());
		throw;
	}
	remove(tmp.c_str());
}

}  // namespace lowir2native
