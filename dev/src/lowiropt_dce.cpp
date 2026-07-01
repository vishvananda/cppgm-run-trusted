#include "lowiropt.h"

#include <deque>
#include <map>
#include <set>
#include <vector>

using namespace std;

namespace lowiropt {
namespace {

using lowir2cy86::Function;
using lowir2cy86::InstrKind;
using lowir2cy86::Instruction;
using lowir2cy86::Metadata;
using lowir2cy86::Program;
using lowir2cy86::Value;
using lowir2cy86::ValueKind;

void count_value_use(const Value& value, map<string, int>& uses)
{
	if (value.kind == ValueKind::Temp)
		++uses[value.text];
}

map<string, int> count_temp_uses(const Function& fn)
{
	map<string, int> uses;
	for (size_t b = 0; b < fn.blocks.size(); ++b)
		for (size_t i = 0; i < fn.blocks[b].instructions.size(); ++i)
		{
			const Instruction& ins = fn.blocks[b].instructions[i];
			count_value_use(ins.a, uses);
			count_value_use(ins.b, uses);
			count_value_use(ins.c, uses);
			for (size_t a = 0; a < ins.args.size(); ++a)
				count_value_use(ins.args[a], uses);
			for (size_t c = 0; c < ins.switch_cases.size(); ++c)
				count_value_use(ins.switch_cases[c].value, uses);
		}
	return uses;
}

bool metadata_is(const Metadata& md, const string& key, const string& value)
{
	return lowir2cy86::metadata_value(md, key) == value;
}

bool direct_function_readnone_nothrow(const Program& program, const string& name)
{
	map<string, size_t>::const_iterator it = program.function_by_name.find(name);
	if (it == program.function_by_name.end())
		return false;
	const Function& fn = program.functions[it->second];
	if (metadata_is(fn.metadata, "effects", "readnone") &&
	    metadata_is(fn.metadata, "unwind", "no") &&
	    !metadata_is(fn.metadata, "return", "noreturn"))
		return true;
	if (fn.declaration)
		return false;
	for (size_t b = 0; b < fn.blocks.size(); ++b)
		for (size_t i = 0; i < fn.blocks[b].instructions.size(); ++i)
		{
			const Instruction& ins = fn.blocks[b].instructions[i];
			if (ins.kind == InstrKind::Call || ins.kind == InstrKind::Store ||
			    ins.kind == InstrKind::AtomicStore ||
			    ins.kind == InstrKind::AtomicExchange ||
			    ins.kind == InstrKind::AtomicCompareExchange ||
			    ins.kind == InstrKind::AtomicAddFetch ||
			    ins.kind == InstrKind::Throw || ins.kind == InstrKind::Resume ||
			    ins.kind == InstrKind::EhTry || ins.kind == InstrKind::EhCleanup)
				return false;
		}
	return true;
}

bool removable_unused_call(const Program& program, const Instruction& ins)
{
	if (ins.kind != InstrKind::Call || !ins.has_dest)
		return false;
	if (ins.a.kind == ValueKind::Function)
		return direct_function_readnone_nothrow(program, ins.a.text);
	return metadata_is(ins.signature.metadata, "effects", "readnone") &&
	       metadata_is(ins.signature.metadata, "unwind", "no") &&
	       !metadata_is(ins.signature.metadata, "return", "noreturn");
}

bool pure_unused_instruction(const Program& program, const Instruction& ins)
{
	if (!ins.has_dest)
		return false;
	if (removable_unused_call(program, ins))
		return true;
	if (ins.kind == InstrKind::Const || ins.kind == InstrKind::Copy ||
	    ins.kind == InstrKind::Addr || ins.kind == InstrKind::Index ||
	    ins.kind == InstrKind::Unary || ins.kind == InstrKind::Binary ||
	    ins.kind == InstrKind::Cmp || ins.kind == InstrKind::Convert)
		return true;
	if (ins.kind == InstrKind::Load && ins.a.kind == ValueKind::Slot)
		return true;
	return false;
}

void enqueue_if_dead_temp(const Program& program,
                          const Function& fn,
                          const string& temp,
                          const map<string, pair<size_t, size_t> >& defs,
                          deque<string>& work)
{
	map<string, pair<size_t, size_t> >::const_iterator def = defs.find(temp);
	if (def == defs.end())
		return;
	const Instruction& candidate =
	    fn.blocks[def->second.first].instructions[def->second.second];
	if (pure_unused_instruction(program, candidate))
		work.push_back(temp);
}

void decrement_temp_use(const Program& program,
                        const Function& fn,
                        const Value& value,
                        map<string, int>& uses,
                        const map<string, pair<size_t, size_t> >& defs,
                        deque<string>& work)
{
	if (value.kind != ValueKind::Temp)
		return;
	map<string, int>::iterator use = uses.find(value.text);
	if (use == uses.end() || use->second == 0)
		return;
	--use->second;
	if (use->second == 0)
		enqueue_if_dead_temp(program, fn, value.text, defs, work);
}

void decrement_instruction_temp_uses(const Program& program,
                                     const Function& fn,
                                     const Instruction& ins,
                                     map<string, int>& uses,
                                     const map<string, pair<size_t, size_t> >& defs,
                                     deque<string>& work)
{
	decrement_temp_use(program, fn, ins.a, uses, defs, work);
	decrement_temp_use(program, fn, ins.b, uses, defs, work);
	decrement_temp_use(program, fn, ins.c, uses, defs, work);
	for (size_t a = 0; a < ins.args.size(); ++a)
		decrement_temp_use(program, fn, ins.args[a], uses, defs, work);
	for (size_t c = 0; c < ins.switch_cases.size(); ++c)
		decrement_temp_use(program,
		                   fn,
		                   ins.switch_cases[c].value,
		                   uses,
		                   defs,
		                   work);
}

}  // namespace

bool remove_unused_temps(Function& fn, const Program& program)
{
	map<string, int> uses = count_temp_uses(fn);
	map<string, pair<size_t, size_t> > defs;
	vector<vector<bool> > remove(fn.blocks.size());
	deque<string> work;
	for (size_t b = 0; b < fn.blocks.size(); ++b)
	{
		remove[b].assign(fn.blocks[b].instructions.size(), false);
		for (size_t i = 0; i < fn.blocks[b].instructions.size(); ++i)
		{
			const Instruction& ins = fn.blocks[b].instructions[i];
			if (!ins.has_dest)
				continue;
			defs[ins.dest] = make_pair(b, i);
			if (uses[ins.dest] == 0 && pure_unused_instruction(program, ins))
				work.push_back(ins.dest);
		}
	}

	bool changed = false;
	while (!work.empty())
	{
		string temp = work.front();
		work.pop_front();
		map<string, pair<size_t, size_t> >::const_iterator found =
		    defs.find(temp);
		if (found == defs.end())
			continue;
		const size_t b = found->second.first;
		const size_t i = found->second.second;
		if (remove[b][i])
			continue;
		const Instruction& ins = fn.blocks[b].instructions[i];
		if (!ins.has_dest || uses[ins.dest] != 0 ||
		    !pure_unused_instruction(program, ins))
			continue;
		remove[b][i] = true;
		changed = true;
		decrement_instruction_temp_uses(program, fn, ins, uses, defs, work);
	}
	if (!changed)
		return false;
	for (size_t b = 0; b < fn.blocks.size(); ++b)
	{
		vector<Instruction> kept;
		kept.reserve(fn.blocks[b].instructions.size());
		for (size_t i = 0; i < fn.blocks[b].instructions.size(); ++i)
			if (!remove[b][i])
				kept.push_back(fn.blocks[b].instructions[i]);
		fn.blocks[b].instructions.swap(kept);
	}
	return changed;
}

}  // namespace lowiropt
