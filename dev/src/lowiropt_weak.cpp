#include "lowiropt.h"

#include <deque>
#include <map>
#include <set>
#include <string>
#include <vector>

using namespace std;

namespace lowiropt {
namespace {

using lowir2cy86::Function;
using lowir2cy86::Global;
using lowir2cy86::InstrKind;
using lowir2cy86::Instruction;
using lowir2cy86::Program;
using lowir2cy86::Value;
using lowir2cy86::ValueKind;

bool metadata_is(const lowir2cy86::Metadata& md,
                 const string& key,
                 const string& value)
{
	return lowir2cy86::metadata_value(md, key) == value;
}

bool weak_definition(const Function& fn)
{
	return !fn.declaration &&
	       lowir2cy86::metadata_value(fn.metadata, "binding") == "weak";
}

bool internal_definition(const Function& fn)
{
	return !fn.declaration &&
	       lowir2cy86::metadata_value(fn.metadata, "binding") == "internal";
}

bool prune_candidate_definition(const Function& fn)
{
	return weak_definition(fn) || internal_definition(fn);
}

bool required_function_definition(const Function& fn)
{
	if (fn.declaration)
		return false;
	if (!prune_candidate_definition(fn))
		return true;
	return !lowir2cy86::metadata_value(fn.metadata, "role").empty() ||
	       metadata_is(fn.metadata, "keep_alias", "yes") ||
	       fn.name == "@main" ||
	       fn.name == "@__cppgm_init" ||
	       fn.name == "@__cppgm_fini";
}

bool function_value_name(const Program& program, const Value& value, string& name)
{
	if (value.kind == ValueKind::Function)
		name = value.text;
	else if (value.kind == ValueKind::Global &&
	         program.function_by_name.find(value.text) != program.function_by_name.end())
		name = value.text;
	else
		return false;
	return program.function_by_name.find(name) != program.function_by_name.end();
}

void mark_live_function(const Program& program,
                        const string& name,
                        set<string>& live,
                        deque<string>& work)
{
	if (program.function_by_name.find(name) == program.function_by_name.end())
		return;
	if (live.insert(name).second)
		work.push_back(name);
}

void mark_function_value_live(const Program& program,
                              const Value& value,
                              set<string>& live,
                              deque<string>& work)
{
	string name;
	if (function_value_name(program, value, name))
		mark_live_function(program, name, live, work);
}

void mark_global_target_live(const Program& program,
                             const string& target,
                             set<string>& live,
                             deque<string>& work)
{
	if (program.function_by_name.find(target) != program.function_by_name.end())
		mark_live_function(program, target, live, work);
}

void mark_global_function_references(const Program& program,
                                     set<string>& live,
                                     deque<string>& work)
{
	for (size_t i = 0; i < program.globals.size(); ++i)
	{
		const Global& global = program.globals[i];
		if (global.init.kind == "addr")
			mark_global_target_live(program, global.init.target, live, work);
		for (size_t j = 0; j < global.data.size(); ++j)
			if (global.data[j].kind == "addr")
				mark_global_target_live(program, global.data[j].target,
				                        live, work);
	}
}

void mark_reachable_instruction_references(const Program& program,
                                           const Instruction& ins,
                                           set<string>& live,
                                           deque<string>& work)
{
	if (ins.kind == InstrKind::Call)
	{
		if (ins.a.kind == ValueKind::Function)
			mark_live_function(program, ins.a.text, live, work);
		else
			mark_function_value_live(program, ins.a, live, work);
	}
	else
		mark_function_value_live(program, ins.a, live, work);
	mark_function_value_live(program, ins.b, live, work);
	mark_function_value_live(program, ins.c, live, work);
	for (size_t i = 0; i < ins.args.size(); ++i)
		mark_function_value_live(program, ins.args[i], live, work);
	for (size_t i = 0; i < ins.switch_cases.size(); ++i)
		mark_function_value_live(program, ins.switch_cases[i].value, live, work);
}

set<string> reachable_required_functions(const Program& program)
{
	set<string> live;
	deque<string> work;
	for (size_t i = 0; i < program.functions.size(); ++i)
		if (required_function_definition(program.functions[i]))
			mark_live_function(program, program.functions[i].name, live, work);
	mark_global_function_references(program, live, work);
	while (!work.empty())
	{
		const string name = work.front();
		work.pop_front();
		map<string, size_t>::const_iterator it =
		    program.function_by_name.find(name);
		if (it == program.function_by_name.end())
			continue;
		const Function& fn = program.functions[it->second];
		if (fn.declaration)
			continue;
		for (size_t b = 0; b < fn.blocks.size(); ++b)
			for (size_t i = 0; i < fn.blocks[b].instructions.size(); ++i)
				mark_reachable_instruction_references(
				    program, fn.blocks[b].instructions[i], live, work);
	}
	return live;
}

}  // namespace

bool remove_unreachable_weak_functions(Program& program)
{
	rebuild_program(program);
	const set<string> live = reachable_required_functions(program);
	vector<Function> kept;
	set<string> kept_symbols;
	for (size_t i = 0; i < program.functions.size(); ++i)
		if (!prune_candidate_definition(program.functions[i]) ||
		    live.count(program.functions[i].name) != 0)
		{
			kept_symbols.insert(program.functions[i].name);
			kept.push_back(program.functions[i]);
		}
	for (size_t i = 0; i < program.globals.size(); ++i)
		kept_symbols.insert(program.globals[i].name);
	vector<lowir2cy86::ObjectAlias> kept_aliases;
	for (size_t i = 0; i < program.aliases.size(); ++i)
		if (kept_symbols.count(program.aliases[i].target) != 0)
			kept_aliases.push_back(program.aliases[i]);
	if (kept.size() == program.functions.size())
	{
		if (kept_aliases.size() == program.aliases.size())
			return false;
		program.aliases.swap(kept_aliases);
		rebuild_program(program);
		return true;
	}
	program.functions.swap(kept);
	program.aliases.swap(kept_aliases);
	rebuild_program(program);
	return true;
}

}  // namespace lowiropt
