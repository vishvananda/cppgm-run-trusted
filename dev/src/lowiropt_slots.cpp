#include "lowiropt.h"

#include <cstdlib>
#include <map>
#include <set>
#include <vector>

using namespace std;

namespace lowiropt {
namespace {

using lowir2cy86::Block;
using lowir2cy86::Function;
using lowir2cy86::InstrKind;
using lowir2cy86::Instruction;
using lowir2cy86::Program;
using lowir2cy86::Slot;
using lowir2cy86::Type;
using lowir2cy86::Value;
using lowir2cy86::ValueKind;

struct SlotFact
{
	bool known;
	Value value;

	SlotFact() : known(false) {}
};

typedef map<string, SlotFact> SlotState;

bool same_value(const Value& a, const Value& b)
{
	return a.kind == b.kind && a.text == b.text;
}

bool parse_int_literal(const string& text, long long& out)
{
	char* end = 0;
	out = strtoll(text.c_str(), &end, 0);
	return end != text.c_str() && *end == '\0';
}

bool literal_truth(const Value& value, bool& out)
{
	if (value.kind != ValueKind::Literal)
		return false;
	long long n = 0;
	if (!parse_int_literal(value.text, n))
		return false;
	out = n != 0;
	return true;
}

map<string, size_t> block_indices(const Function& fn)
{
	map<string, size_t> out;
	for (size_t i = 0; i < fn.blocks.size(); ++i)
		out[fn.blocks[i].name] = i;
	return out;
}

void add_target(const map<string, size_t>& index,
                const string& target,
                vector<size_t>& out)
{
	map<string, size_t>::const_iterator it = index.find(target);
	if (it != index.end())
		out.push_back(it->second);
}

vector<size_t> block_successors(const Function& fn,
                                const map<string, size_t>& index,
                                size_t block)
{
	vector<size_t> out;
	const Block& b = fn.blocks[block];
	for (size_t i = 0; i < b.instructions.size(); ++i)
	{
		const Instruction& ins = b.instructions[i];
		if ((ins.kind == InstrKind::EhTry || ins.kind == InstrKind::EhCleanup) &&
		    !ins.target.empty())
			add_target(index, ins.target, out);
	}
	if (b.instructions.empty())
		return out;
	const Instruction& term = b.instructions.back();
	if (term.kind == InstrKind::Jump)
		add_target(index, term.target, out);
	else if (term.kind == InstrKind::Branch)
	{
		add_target(index, term.target, out);
		add_target(index, term.target_false, out);
	}
	else if (term.kind == InstrKind::Switch)
	{
		add_target(index, term.target, out);
		for (size_t i = 0; i < term.switch_cases.size(); ++i)
			add_target(index, term.switch_cases[i].target, out);
	}
	return out;
}

SlotFact state_value(const SlotState& state, const string& slot)
{
	map<string, SlotFact>::const_iterator it = state.find(slot);
	if (it == state.end())
		return SlotFact();
	return it->second;
}

void set_known(SlotState& state, const string& slot, const Value& value)
{
	SlotFact fact;
	fact.known = true;
	fact.value = value;
	state[slot] = fact;
}

SlotState merge_states(const SlotState& a,
                       const SlotState& b,
                       const set<string>& slots)
{
	SlotState out;
	for (set<string>::const_iterator s = slots.begin(); s != slots.end(); ++s)
	{
		SlotFact av = state_value(a, *s);
		SlotFact bv = state_value(b, *s);
		if (av.known && bv.known && same_value(av.value, bv.value))
			set_known(out, *s, av.value);
	}
	return out;
}

bool state_equal(const SlotState& a,
                 const SlotState& b,
                 const set<string>& slots)
{
	for (set<string>::const_iterator s = slots.begin(); s != slots.end(); ++s)
	{
		SlotFact av = state_value(a, *s);
		SlotFact bv = state_value(b, *s);
		if (av.known != bv.known)
			return false;
		if (av.known && !same_value(av.value, bv.value))
			return false;
	}
	return true;
}

void replace_value(Value& value, const map<string, Value>& temps)
{
	set<string> seen;
	while (value.kind == ValueKind::Temp)
	{
		map<string, Value>::const_iterator it = temps.find(value.text);
		if (it == temps.end() || !seen.insert(value.text).second)
			return;
		value = it->second;
	}
}

void replace_instruction_values(Instruction& ins, const map<string, Value>& temps)
{
	replace_value(ins.a, temps);
	replace_value(ins.b, temps);
	replace_value(ins.c, temps);
	for (size_t i = 0; i < ins.args.size(); ++i)
		replace_value(ins.args[i], temps);
	for (size_t i = 0; i < ins.switch_cases.size(); ++i)
		replace_value(ins.switch_cases[i].value, temps);
}

bool candidate_slot_type(const Type& type)
{
	return !lowir2cy86::is_obj_type(type);
}

void collect_candidate_slots(const Function& fn, set<string>& candidates)
{
	set<string> escapes;
	for (size_t i = 0; i < fn.slots.size(); ++i)
		if (candidate_slot_type(fn.slots[i].type))
			candidates.insert(fn.slots[i].name);
	for (size_t b = 0; b < fn.blocks.size(); ++b)
	{
		for (size_t i = 0; i < fn.blocks[b].instructions.size(); ++i)
		{
			const Instruction& ins = fn.blocks[b].instructions[i];
			if (ins.kind == InstrKind::Load && ins.a.kind == ValueKind::Slot)
				continue;
			if (ins.kind == InstrKind::Store && ins.b.kind == ValueKind::Slot)
			{
				if (ins.a.kind == ValueKind::Slot)
					escapes.insert(ins.a.text);
				continue;
			}
			if (ins.a.kind == ValueKind::Slot) escapes.insert(ins.a.text);
			if (ins.b.kind == ValueKind::Slot) escapes.insert(ins.b.text);
			if (ins.c.kind == ValueKind::Slot) escapes.insert(ins.c.text);
			for (size_t a = 0; a < ins.args.size(); ++a)
				if (ins.args[a].kind == ValueKind::Slot)
					escapes.insert(ins.args[a].text);
		}
	}
	for (set<string>::const_iterator e = escapes.begin(); e != escapes.end(); ++e)
		candidates.erase(*e);
}

bool pointer_literal_value(const Function& fn, const string& slot, const Value& value)
{
	if (value.kind != ValueKind::Literal)
		return false;
	map<string, Type>::const_iterator it = fn.slot_types.find(slot);
	return it != fn.slot_types.end() && it->second.text == "ptr";
}

void count_storage_temp(const Value& value, set<string>& out)
{
	if (value.kind == ValueKind::Temp)
		out.insert(value.text);
}

set<string> storage_temp_uses(const Function& fn)
{
	set<string> out;
	for (size_t b = 0; b < fn.blocks.size(); ++b)
	{
		for (size_t i = 0; i < fn.blocks[b].instructions.size(); ++i)
		{
			const Instruction& ins = fn.blocks[b].instructions[i];
			if (ins.kind == InstrKind::Load ||
			    ins.kind == InstrKind::AtomicLoad ||
			    ins.kind == InstrKind::VaArg)
				count_storage_temp(ins.a, out);
			else if (ins.kind == InstrKind::Store ||
			         ins.kind == InstrKind::AtomicStore ||
			         ins.kind == InstrKind::AtomicExchange ||
			         ins.kind == InstrKind::AtomicCompareExchange ||
			         ins.kind == InstrKind::AtomicAddFetch)
				count_storage_temp(ins.b, out);
			else if (ins.kind == InstrKind::CopyObj)
				count_storage_temp(ins.b, out);
			else if (ins.kind == InstrKind::ZeroInit)
				count_storage_temp(ins.a, out);
		}
	}
	return out;
}

void merge_into_block(size_t target,
                      const SlotState& incoming,
                      const set<string>& slots,
                      vector<SlotState>& in_states,
                      vector<bool>& initialized,
                      vector<size_t>& work)
{
	if (!initialized[target])
	{
		in_states[target] = incoming;
		initialized[target] = true;
		work.push_back(target);
		return;
	}
	SlotState merged = merge_states(in_states[target], incoming, slots);
	if (!state_equal(merged, in_states[target], slots))
	{
		in_states[target] = merged;
		work.push_back(target);
	}
}

void simulate_successors(const Function& fn,
                         const map<string, size_t>& index,
                         size_t block,
                         const SlotState& state,
                         const map<string, Value>& temps,
                         const set<string>& slots,
                         vector<SlotState>& in_states,
                         vector<bool>& initialized,
                         vector<size_t>& work)
{
	if (fn.blocks[block].instructions.empty())
		return;
	Instruction term = fn.blocks[block].instructions.back();
	replace_instruction_values(term, temps);
	if (term.kind == InstrKind::Jump)
	{
		map<string, size_t>::const_iterator it = index.find(term.target);
		if (it != index.end())
			merge_into_block(it->second, state, slots, in_states, initialized, work);
	}
	else if (term.kind == InstrKind::Branch)
	{
		bool truth = false;
		if (literal_truth(term.a, truth))
		{
			map<string, size_t>::const_iterator it =
			    index.find(truth ? term.target : term.target_false);
			if (it != index.end())
				merge_into_block(it->second, state, slots, in_states, initialized, work);
		}
		else
		{
			map<string, size_t>::const_iterator t = index.find(term.target);
			map<string, size_t>::const_iterator f = index.find(term.target_false);
			if (t != index.end())
				merge_into_block(t->second, state, slots, in_states, initialized, work);
			if (f != index.end())
				merge_into_block(f->second, state, slots, in_states, initialized, work);
		}
	}
	else if (term.kind == InstrKind::Switch)
	{
		long long selector = 0;
		string target = term.target;
		if (term.a.kind == ValueKind::Literal && parse_int_literal(term.a.text, selector))
		{
			for (size_t i = 0; i < term.switch_cases.size(); ++i)
			{
				long long case_value = 0;
				if (parse_int_literal(term.switch_cases[i].value.text, case_value) &&
				    case_value == selector)
					target = term.switch_cases[i].target;
			}
			map<string, size_t>::const_iterator it = index.find(target);
			if (it != index.end())
				merge_into_block(it->second, state, slots, in_states, initialized, work);
		}
		else
		{
			map<string, size_t>::const_iterator d = index.find(term.target);
			if (d != index.end())
				merge_into_block(d->second, state, slots, in_states, initialized, work);
			for (size_t i = 0; i < term.switch_cases.size(); ++i)
			{
				map<string, size_t>::const_iterator c =
				    index.find(term.switch_cases[i].target);
				if (c != index.end())
					merge_into_block(c->second, state, slots, in_states, initialized, work);
			}
		}
	}
}

void analyze_slot_states(const Function& fn,
                         const set<string>& slots,
                         vector<SlotState>& in_states,
                         vector<bool>& reachable)
{
	const map<string, size_t> index = block_indices(fn);
	vector<bool> initialized(fn.blocks.size(), false);
	vector<size_t> work;
	if (fn.blocks.empty())
		return;
	initialized[0] = true;
	reachable[0] = true;
	work.push_back(0);
	while (!work.empty())
	{
		const size_t block = work.back();
		work.pop_back();
		reachable[block] = true;
		SlotState state = in_states[block];
		map<string, Value> temps;
		for (size_t i = 0; i < fn.blocks[block].instructions.size(); ++i)
		{
			Instruction ins = fn.blocks[block].instructions[i];
			replace_instruction_values(ins, temps);
			if ((ins.kind == InstrKind::EhTry || ins.kind == InstrKind::EhCleanup) &&
			    !ins.target.empty())
			{
				map<string, size_t>::const_iterator it = index.find(ins.target);
				if (it != index.end())
					merge_into_block(it->second, state, slots, in_states,
					                 initialized, work);
			}
			if (ins.kind == InstrKind::Load && ins.has_dest &&
			    ins.a.kind == ValueKind::Slot && slots.count(ins.a.text) != 0)
			{
				SlotFact fact = state_value(state, ins.a.text);
				if (fact.known)
					temps[ins.dest] = fact.value;
			}
			else if (ins.kind == InstrKind::Store &&
			         ins.b.kind == ValueKind::Slot &&
			         slots.count(ins.b.text) != 0)
				set_known(state, ins.b.text, ins.a);
			else if (ins.has_dest && (ins.kind == InstrKind::Const ||
			                          ins.kind == InstrKind::Copy))
				temps[ins.dest] = ins.a;
		}
		simulate_successors(fn, index, block, state, temps, slots,
		                    in_states, initialized, work);
	}
}

bool fold_terminator(Instruction& ins)
{
	if (ins.kind == InstrKind::Branch)
	{
		bool truth = false;
		if (literal_truth(ins.a, truth))
		{
			ins.kind = InstrKind::Jump;
			ins.target = truth ? ins.target : ins.target_false;
			ins.target_false.clear();
			return true;
		}
	}
	else if (ins.kind == InstrKind::Switch)
	{
		long long selector = 0;
		if (ins.a.kind != ValueKind::Literal ||
		    !parse_int_literal(ins.a.text, selector))
			return false;
		string target = ins.target;
		for (size_t i = 0; i < ins.switch_cases.size(); ++i)
		{
			long long case_value = 0;
			if (parse_int_literal(ins.switch_cases[i].value.text, case_value) &&
			    case_value == selector)
				target = ins.switch_cases[i].target;
		}
		ins.kind = InstrKind::Jump;
		ins.target = target;
		ins.switch_cases.clear();
		return true;
	}
	return false;
}

bool rewrite_slot_loads(Function& fn,
                        const set<string>& slots,
                        const vector<SlotState>& in_states,
                        const vector<bool>& reachable)
{
	set<string> unknown_load_slots;
	set<string> seen_slots = slots;
	set<string> storage_temps = storage_temp_uses(fn);
	bool changed = false;
	vector<Block> new_blocks;
	for (size_t b = 0; b < fn.blocks.size(); ++b)
	{
		if (!reachable[b])
		{
			changed = true;
			continue;
		}
		SlotState state = in_states[b];
		map<string, Value> temps;
		Block block = fn.blocks[b];
		vector<Instruction> kept;
		for (size_t i = 0; i < block.instructions.size(); ++i)
		{
			Instruction ins = block.instructions[i];
			replace_instruction_values(ins, temps);
			if (ins.kind == InstrKind::Load && ins.has_dest &&
			    ins.a.kind == ValueKind::Slot && slots.count(ins.a.text) != 0)
			{
				SlotFact fact = state_value(state, ins.a.text);
				if (fact.known &&
				    pointer_literal_value(fn, ins.a.text, fact.value) &&
				    storage_temps.count(ins.dest) != 0)
				{
					ins.kind = InstrKind::Const;
					ins.a = fact.value;
					ins.b = Value();
					ins.c = Value();
					kept.push_back(ins);
					changed = true;
					continue;
				}
				if (fact.known)
				{
					temps[ins.dest] = fact.value;
					changed = true;
					continue;
				}
				unknown_load_slots.insert(ins.a.text);
			}
			else if (ins.kind == InstrKind::Store &&
			         ins.b.kind == ValueKind::Slot &&
			         slots.count(ins.b.text) != 0)
				set_known(state, ins.b.text, ins.a);
			else if (ins.has_dest && (ins.kind == InstrKind::Const ||
			                          ins.kind == InstrKind::Copy))
				temps[ins.dest] = ins.a;
			changed = fold_terminator(ins) || changed;
			kept.push_back(ins);
		}
		block.instructions.swap(kept);
		new_blocks.push_back(block);
	}
	fn.blocks.swap(new_blocks);

	set<string> promoted;
	for (set<string>::const_iterator s = seen_slots.begin(); s != seen_slots.end(); ++s)
		if (unknown_load_slots.count(*s) == 0)
			promoted.insert(*s);
	if (promoted.empty())
		return changed;

	for (size_t b = 0; b < fn.blocks.size(); ++b)
	{
		vector<Instruction> kept;
		for (size_t i = 0; i < fn.blocks[b].instructions.size(); ++i)
		{
			const Instruction& ins = fn.blocks[b].instructions[i];
			if (ins.kind == InstrKind::Store && ins.b.kind == ValueKind::Slot &&
			    promoted.count(ins.b.text) != 0)
			{
				changed = true;
				continue;
			}
			kept.push_back(ins);
		}
		fn.blocks[b].instructions.swap(kept);
	}
	vector<Slot> kept_slots;
	for (size_t i = 0; i < fn.slots.size(); ++i)
	{
		if (promoted.count(fn.slots[i].name) != 0)
		{
			changed = true;
			continue;
		}
		kept_slots.push_back(fn.slots[i]);
	}
	fn.slots.swap(kept_slots);
	return changed;
}

bool propagate_slot_values(Function& fn)
{
	set<string> slots;
	collect_candidate_slots(fn, slots);
	if (slots.empty())
		return false;
	vector<SlotState> in_states(fn.blocks.size());
	vector<bool> reachable(fn.blocks.size(), false);
	analyze_slot_states(fn, slots, in_states, reachable);
	return rewrite_slot_loads(fn, slots, in_states, reachable);
}

bool remove_dead_slot_stores(Function& fn)
{
	set<string> slots;
	collect_candidate_slots(fn, slots);
	if (slots.empty())
		return false;
	const map<string, size_t> index = block_indices(fn);
	vector<vector<size_t> > succs(fn.blocks.size());
	for (size_t b = 0; b < fn.blocks.size(); ++b)
		succs[b] = block_successors(fn, index, b);

	vector<set<string> > in_live(fn.blocks.size());
	vector<set<string> > out_live(fn.blocks.size());
	bool changed = true;
	while (changed)
	{
		changed = false;
		for (size_t rb = 0; rb < fn.blocks.size(); ++rb)
		{
			const size_t b = fn.blocks.size() - 1 - rb;
			set<string> out;
			for (size_t s = 0; s < succs[b].size(); ++s)
				out.insert(in_live[succs[b][s]].begin(), in_live[succs[b][s]].end());
			set<string> live = out;
			for (size_t ri = 0; ri < fn.blocks[b].instructions.size(); ++ri)
			{
				const size_t i = fn.blocks[b].instructions.size() - 1 - ri;
				const Instruction& ins = fn.blocks[b].instructions[i];
				if (ins.kind == InstrKind::Load && ins.a.kind == ValueKind::Slot &&
				    slots.count(ins.a.text) != 0)
					live.insert(ins.a.text);
				else if (ins.kind == InstrKind::Store &&
				         ins.b.kind == ValueKind::Slot &&
				         slots.count(ins.b.text) != 0)
					live.erase(ins.b.text);
			}
			if (out != out_live[b] || live != in_live[b])
			{
				out_live[b].swap(out);
				in_live[b].swap(live);
				changed = true;
			}
		}
	}

	bool removed = false;
	for (size_t b = 0; b < fn.blocks.size(); ++b)
	{
		set<string> live = out_live[b];
		vector<bool> keep(fn.blocks[b].instructions.size(), true);
		for (size_t ri = 0; ri < fn.blocks[b].instructions.size(); ++ri)
		{
			const size_t i = fn.blocks[b].instructions.size() - 1 - ri;
			const Instruction& ins = fn.blocks[b].instructions[i];
			if (ins.kind == InstrKind::Load && ins.a.kind == ValueKind::Slot &&
			    slots.count(ins.a.text) != 0)
				live.insert(ins.a.text);
			else if (ins.kind == InstrKind::Store &&
			         ins.b.kind == ValueKind::Slot &&
			         slots.count(ins.b.text) != 0)
			{
				if (live.count(ins.b.text) == 0)
				{
					keep[i] = false;
					removed = true;
				}
				else
					live.erase(ins.b.text);
			}
		}
		vector<Instruction> kept;
		for (size_t i = 0; i < fn.blocks[b].instructions.size(); ++i)
			if (keep[i])
				kept.push_back(fn.blocks[b].instructions[i]);
		fn.blocks[b].instructions.swap(kept);
	}
	return removed;
}

}  // namespace

bool promote_o2_slots_once(Program& program)
{
	rebuild_program(program);
	bool changed = false;
	for (size_t i = 0; i < program.functions.size(); ++i)
	{
		if (program.functions[i].declaration)
			continue;
		changed = propagate_slot_values(program.functions[i]) || changed;
		rebuild_program(program);
		changed = remove_dead_slot_stores(program.functions[i]) || changed;
		rebuild_program(program);
	}
	return changed;
}

}  // namespace lowiropt
