#include "pa31_host_object_internal.h"

#include <algorithm>
#include <map>
#include <set>

using namespace std;

namespace pa31 {
namespace host {
bool eh_stack_equal(const vector<EhRange>& a, const vector<EhRange>& b)
{
	if (a.size() != b.size())
		return false;
	for (size_t i = 0; i < a.size(); ++i)
		if (a[i].target != b[i].target)
			return false;
	return true;
}
vector<EhRange> common_eh_stack_prefix(const vector<EhRange>& a,
                                       const vector<EhRange>& b)
{
	vector<EhRange> out;
	const size_t limit = min(a.size(), b.size());
	for (size_t i = 0; i < limit; ++i)
	{
		if (a[i].target != b[i].target)
			break;
		out.push_back(a[i]);
	}
	return out;
}
void append_successor(vector<string>& out, const string& target)
{
	if (!target.empty())
		out.push_back(target);
}
vector<string> normal_successors(const Block& block)
{
	vector<string> out;
	if (block.instructions.empty())
		return out;
	const Instruction& ins = block.instructions.back();
	if (ins.kind == InstrKind::Jump)
		append_successor(out, ins.target);
	else if (ins.kind == InstrKind::Branch)
	{
		append_successor(out, ins.target);
		append_successor(out, ins.target_false);
	}
	else if (ins.kind == InstrKind::Switch)
	{
		append_successor(out, ins.target);
		for (size_t i = 0; i < ins.switch_cases.size(); ++i)
			append_successor(out, ins.switch_cases[i].target);
	}
	return out;
}
vector<EhRange> eh_stack_after_block(vector<EhRange> stack,
                                     const Block& block)
{
	for (size_t i = 0; i < block.instructions.size(); ++i)
	{
		const Instruction& ins = block.instructions[i];
		if ((ins.kind == InstrKind::EhTry ||
		     ins.kind == InstrKind::EhCleanup) &&
		    !ins.target.empty())
		{
			EhRange r;
			r.target = ins.target;
			stack.push_back(r);
		}
		else if (ins.kind == InstrKind::EhEnd)
		{
			if (!stack.empty())
				stack.pop_back();
		}
	}
	return stack;
}
void FuncGen::analyze_eh_regions()
{
	block_entry_ranges.clear();
	landing_blocks.clear();
	cleanup_blocks.clear();
	cleanup_action_blocks.clear();
	catches.clear();
	lsda_types.clear();
	lsda_spec_table.clear();
	map<string, size_t> block_index;
	for (size_t b = 0; b < fn.blocks.size(); ++b)
		block_index[fn.blocks[b].name] = b;
	for (size_t b = 0; b < fn.blocks.size(); ++b)
	{
		const Block& block = fn.blocks[b];
		for (size_t i = 0; i < block.instructions.size(); ++i)
		{
			const Instruction& ins = block.instructions[i];
			if (ins.kind == InstrKind::EhTry ||
			    ins.kind == InstrKind::EhCleanup)
			{
				if (!ins.target.empty())
				{
					landing_blocks.insert(ins.target);
					if (ins.kind == InstrKind::EhCleanup)
						cleanup_blocks.insert(ins.target);
				}
				else if (ins.kind == InstrKind::EhCleanup)
					cleanup_action_blocks.insert(block.name);
			}
			else if (ins.kind == InstrKind::EhCatch)
			{
				CatchInfo c;
				c.type_symbol = target_symbol(unit.program, ins.a.text);
				c.selector = ins.order_a;
				catches[block.name].push_back(c);
			}
			else if (ins.kind == InstrKind::EhCatchAll)
			{
				CatchInfo c;
				c.selector = ins.order_a;
				c.catch_all = true;
				catches[block.name].push_back(c);
			}
			else if (ins.kind == InstrKind::EhFilter)
			{
				CatchInfo c;
				c.selector = ins.order_a;
				c.exception_spec = true;
				for (size_t a = 0; a < ins.args.size(); ++a)
					c.exception_spec_types.push_back(
						target_symbol(unit.program, ins.args[a].text));
				catches[block.name].push_back(c);
			}
		}
	}
	assign_lsda_selectors();
	vector<size_t> work;
	set<string> queued;
	if (!fn.blocks.empty())
	{
		block_entry_ranges[fn.blocks[0].name] = vector<EhRange>();
		work.push_back(0);
		queued.insert(fn.blocks[0].name);
	}
	for (set<string>::const_iterator it = landing_blocks.begin();
	     it != landing_blocks.end(); ++it)
	{
		map<string, size_t>::const_iterator bit = block_index.find(*it);
		if (bit == block_index.end())
			continue;
		if (block_entry_ranges.find(*it) == block_entry_ranges.end())
			block_entry_ranges[*it] = vector<EhRange>();
		if (queued.insert(*it).second)
			work.push_back(bit->second);
	}
	while (!work.empty())
	{
		const size_t index = work.back();
		work.pop_back();
		queued.erase(fn.blocks[index].name);
		vector<EhRange> exit_stack =
			eh_stack_after_block(block_entry_ranges[fn.blocks[index].name],
			                     fn.blocks[index]);
		vector<string> succs = normal_successors(fn.blocks[index]);
		for (size_t i = 0; i < succs.size(); ++i)
		{
			map<string, size_t>::const_iterator sit =
				block_index.find(succs[i]);
			if (sit == block_index.end())
				continue;
			// These are ordinary CFG edges. Exceptional landing-pad entry is
			// handled when emitting landing blocks, so keep the active range.
			vector<EhRange> successor_stack = exit_stack;
			map<string, vector<EhRange> >::iterator entry =
				block_entry_ranges.find(succs[i]);
			if (entry == block_entry_ranges.end())
			{
				block_entry_ranges[succs[i]] = successor_stack;
				if (queued.insert(succs[i]).second)
					work.push_back(sit->second);
			}
			else if (!eh_stack_equal(entry->second, successor_stack))
			{
				vector<EhRange> merged =
					common_eh_stack_prefix(entry->second, successor_stack);
				if (!eh_stack_equal(entry->second, merged))
				{
					entry->second = merged;
					if (queued.insert(succs[i]).second)
						work.push_back(sit->second);
				}
			}
		}
	}
}
void FuncGen::assign_lsda_selectors()
{
	map<string, int> type_index;
	map<string, int> spec_filters;
	for (size_t b = 0; b < fn.blocks.size(); ++b)
	{
		map<string, vector<CatchInfo> >::iterator found =
			catches.find(fn.blocks[b].name);
		if (found == catches.end())
			continue;
		for (size_t i = 0; i < found->second.size(); ++i)
		{
			CatchInfo& c = found->second[i];
			c.raw_selector = c.exception_spec
				? ensure_exception_spec_filter(type_index, lsda_types,
				                               spec_filters,
				                               lsda_spec_table, c)
				: ensure_catch_type_index(type_index, lsda_types, c);
		}
	}
}
}  // namespace host
}  // namespace pa31
