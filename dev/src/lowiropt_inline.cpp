#include "lowiropt.h"

#include <algorithm>
#include <map>
#include <set>
#include <stdexcept>
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
using lowir2cy86::SwitchCase;
using lowir2cy86::Type;
using lowir2cy86::Value;
using lowir2cy86::ValueKind;

string body_name(const string& name)
{
	return name.size() > 1 ? name.substr(1) : name;
}

Value named_value(ValueKind kind, const string& text)
{
	Value value;
	value.kind = kind;
	value.text = text;
	return value;
}

string prefixed_temp(const string& prefix, const string& name)
{
	return "%" + prefix + body_name(name);
}

string prefixed_slot(const string& prefix, const string& name)
{
	return "$" + prefix + body_name(name);
}

string prefixed_block(const string& prefix, const string& name)
{
	return "^" + prefix + body_name(name);
}

bool has_metadata(const Function& fn, const string& key, const string& value)
{
	return lowir2cy86::metadata_value(fn.metadata, key) == value;
}

bool function_has_eh(const Function& fn)
{
	for (size_t b = 0; b < fn.blocks.size(); ++b)
		for (size_t i = 0; i < fn.blocks[b].instructions.size(); ++i)
		{
			InstrKind kind = fn.blocks[b].instructions[i].kind;
			if (kind == InstrKind::EhTry || kind == InstrKind::EhCleanup ||
			    kind == InstrKind::EhCatch || kind == InstrKind::EhCatchAll ||
			    kind == InstrKind::EhFilter || kind == InstrKind::EhEnd ||
			    kind == InstrKind::Throw || kind == InstrKind::Resume)
				return true;
		}
	return false;
}

bool direct_call_may_unwind(const Program& program,
                            const Instruction& ins,
                            set<string>& visiting);

bool function_may_unwind(const Program& program,
                         const Function& fn,
                         set<string>& visiting)
{
	if (has_metadata(fn, "unwind", "no"))
		return false;
	if (fn.declaration)
		return true;
	if (!visiting.insert(fn.name).second)
		return false;
	for (size_t b = 0; b < fn.blocks.size(); ++b)
		for (size_t i = 0; i < fn.blocks[b].instructions.size(); ++i)
		{
			const Instruction& ins = fn.blocks[b].instructions[i];
			if (ins.kind == InstrKind::Throw || ins.kind == InstrKind::Resume ||
			    ins.kind == InstrKind::EhTry || ins.kind == InstrKind::EhCleanup)
				return true;
			if (ins.kind == InstrKind::Call &&
			    direct_call_may_unwind(program, ins, visiting))
				return true;
		}
	visiting.erase(fn.name);
	return false;
}

bool function_may_unwind(const Program& program, const Function& fn)
{
	set<string> visiting;
	return function_may_unwind(program, fn, visiting);
}

bool direct_call_may_unwind(const Program& program,
                            const Instruction& ins,
                            set<string>& visiting)
{
	if (ins.kind != InstrKind::Call)
		return false;
	if (ins.a.kind != ValueKind::Function)
		return lowir2cy86::metadata_value(ins.signature.metadata, "unwind") != "no";
	map<string, size_t>::const_iterator it =
	    program.function_by_name.find(ins.a.text);
	if (it == program.function_by_name.end())
		return true;
	return function_may_unwind(program, program.functions[it->second], visiting);
}

void collect_direct_calls(const Function& fn, set<string>& calls)
{
	for (size_t b = 0; b < fn.blocks.size(); ++b)
		for (size_t i = 0; i < fn.blocks[b].instructions.size(); ++i)
		{
			const Instruction& ins = fn.blocks[b].instructions[i];
			if (ins.kind == InstrKind::Call && ins.a.kind == ValueKind::Function)
				calls.insert(ins.a.text);
		}
}

bool reaches_function(const Program& program,
                      const string& from,
                      const string& target,
                      set<string>& visiting)
{
	if (from == target)
		return true;
	if (!visiting.insert(from).second)
		return false;
	map<string, size_t>::const_iterator it = program.function_by_name.find(from);
	if (it == program.function_by_name.end())
		return false;
	set<string> calls;
	collect_direct_calls(program.functions[it->second], calls);
	for (set<string>::const_iterator c = calls.begin(); c != calls.end(); ++c)
		if (reaches_function(program, *c, target, visiting))
			return true;
	return false;
}

bool recursive_if_inlined(const Program& program,
                          const Function& caller,
                          const Function& callee)
{
	set<string> visiting;
	return reaches_function(program, callee.name, caller.name, visiting);
}

bool function_is_recursive(const Program& program, const Function& fn)
{
	set<string> calls;
	collect_direct_calls(fn, calls);
	for (set<string>::const_iterator c = calls.begin(); c != calls.end(); ++c)
	{
		set<string> visiting;
		if (reaches_function(program, *c, fn.name, visiting))
			return true;
	}
	return false;
}

size_t instruction_count(const Function& fn)
{
	size_t n = 0;
	for (size_t b = 0; b < fn.blocks.size(); ++b)
		n += fn.blocks[b].instructions.size();
	return n;
}

bool function_contains_call(const Function& fn)
{
	for (size_t b = 0; b < fn.blocks.size(); ++b)
		for (size_t i = 0; i < fn.blocks[b].instructions.size(); ++i)
			if (fn.blocks[b].instructions[i].kind == InstrKind::Call)
				return true;
	return false;
}

bool statically_eligible_callee(const Program& program,
                                const Function& callee,
                                map<string, bool>& cache)
{
	map<string, bool>::const_iterator found = cache.find(callee.name);
	if (found != cache.end())
		return found->second;
	bool eligible = true;
	if (callee.declaration || function_has_eh(callee))
		eligible = false;
	else if (function_is_recursive(program, callee))
		eligible = false;
	else if (lowir2cy86::metadata_value(callee.metadata, "prefer_local") != "yes")
	{
		eligible = instruction_count(callee) <= 18;
	}
	cache[callee.name] = eligible;
	return eligible;
}

bool recursive_if_inlined_cached(const Program& program,
                                 const Function& caller,
                                 const Function& callee,
                                 map<pair<string, string>, bool>& cache)
{
	pair<string, string> key = make_pair(caller.name, callee.name);
	map<pair<string, string>, bool>::const_iterator found = cache.find(key);
	if (found != cache.end())
		return found->second;
	bool recursive = recursive_if_inlined(program, caller, callee);
	cache[key] = recursive;
	return recursive;
}

bool function_may_unwind_cached(const Program& program,
                                const Function& fn,
                                map<string, bool>& cache)
{
	map<string, bool>::const_iterator found = cache.find(fn.name);
	if (found != cache.end())
		return found->second;
	bool may_unwind = function_may_unwind(program, fn);
	cache[fn.name] = may_unwind;
	return may_unwind;
}

bool eligible_callee(const Program& program,
                     const Function& caller,
                     const Function& callee,
                     map<string, bool>& static_cache,
                     map<pair<string, string>, bool>& recursive_cache)
{
	if (!statically_eligible_callee(program, callee, static_cache))
		return false;
	return !recursive_if_inlined_cached(program, caller, callee, recursive_cache);
}

set<string> eh_handler_blocks(const Function& fn)
{
	set<string> out;
	for (size_t b = 0; b < fn.blocks.size(); ++b)
		for (size_t i = 0; i < fn.blocks[b].instructions.size(); ++i)
		{
			const Instruction& ins = fn.blocks[b].instructions[i];
			if ((ins.kind == InstrKind::EhTry ||
			     ins.kind == InstrKind::EhCleanup) &&
			    !ins.target.empty())
				out.insert(ins.target);
		}
	return out;
}

bool active_eh_before(const Block& block, size_t ins_index)
{
	int depth = 0;
	for (size_t i = 0; i < ins_index; ++i)
	{
		if (block.instructions[i].kind == InstrKind::EhTry ||
		    block.instructions[i].kind == InstrKind::EhCleanup)
			++depth;
		else if (block.instructions[i].kind == InstrKind::EhEnd && depth > 0)
			--depth;
	}
	return depth > 0;
}

void remap_value(Value& value,
                 const map<string, Value>& value_map,
                 const map<string, string>& slot_map)
{
	if (value.kind == ValueKind::Temp)
	{
		map<string, Value>::const_iterator it = value_map.find(value.text);
		if (it != value_map.end())
			value = it->second;
	}
	else if (value.kind == ValueKind::Slot)
	{
		map<string, string>::const_iterator it = slot_map.find(value.text);
		if (it != slot_map.end())
			value.text = it->second;
	}
}

void remap_instruction(Instruction& ins,
                       const map<string, Value>& value_map,
                       const map<string, string>& slot_map,
                       const map<string, string>& block_map)
{
	remap_value(ins.a, value_map, slot_map);
	remap_value(ins.b, value_map, slot_map);
	remap_value(ins.c, value_map, slot_map);
	for (size_t i = 0; i < ins.args.size(); ++i)
		remap_value(ins.args[i], value_map, slot_map);
	for (size_t i = 0; i < ins.switch_cases.size(); ++i)
	{
		remap_value(ins.switch_cases[i].value, value_map, slot_map);
		map<string, string>::const_iterator it =
		    block_map.find(ins.switch_cases[i].target);
		if (it != block_map.end())
			ins.switch_cases[i].target = it->second;
	}
	if (!ins.target.empty())
	{
		map<string, string>::const_iterator it = block_map.find(ins.target);
		if (it != block_map.end())
			ins.target = it->second;
	}
	if (!ins.target_false.empty())
	{
		map<string, string>::const_iterator it = block_map.find(ins.target_false);
		if (it != block_map.end())
			ins.target_false = it->second;
	}
}

Instruction clone_nonreturn_instruction(const Instruction& src,
                                        const string& prefix,
                                        map<string, Value>& value_map,
                                        const map<string, string>& slot_map,
                                        const map<string, string>& block_map)
{
	Instruction out = src;
	if (out.has_dest)
	{
		out.dest = prefixed_temp(prefix, src.dest);
		value_map[src.dest] = named_value(ValueKind::Temp, out.dest);
	}
	remap_instruction(out, value_map, slot_map, block_map);
	return out;
}

Instruction make_jump(const string& target)
{
	Instruction ins;
	ins.kind = InstrKind::Jump;
	ins.target = target;
	return ins;
}

Instruction make_store(const Type& type, const Value& src, const string& slot)
{
	Instruction ins;
	ins.kind = InstrKind::Store;
	ins.type = type;
	ins.a = src;
	ins.b = named_value(ValueKind::Slot, slot);
	return ins;
}

Instruction make_load(const string& dest, const Type& type, const string& slot)
{
	Instruction ins;
	ins.kind = InstrKind::Load;
	ins.has_dest = true;
	ins.dest = dest;
	ins.type = type;
	ins.a = named_value(ValueKind::Slot, slot);
	return ins;
}

Instruction make_copyobj(const Type& type, const Value& src, const string& dst)
{
	Instruction ins;
	ins.kind = InstrKind::CopyObj;
	ins.span.bytes = type.obj_size;
	ins.span.align = type.obj_align;
	ins.a = src;
	ins.b = named_value(ValueKind::Slot, dst);
	return ins;
}

void replace_temp_uses(Function& fn, const string& temp, const Value& replacement)
{
	map<string, Value> value_map;
	value_map[temp] = replacement;
	map<string, string> slots;
	map<string, string> blocks;
	for (size_t b = 0; b < fn.blocks.size(); ++b)
		for (size_t i = 0; i < fn.blocks[b].instructions.size(); ++i)
			remap_instruction(fn.blocks[b].instructions[i],
			                  value_map,
			                  slots,
			                  blocks);
}

int next_inline_index(const Function& fn)
{
	int max_seen = -1;
	for (size_t b = 0; b < fn.blocks.size(); ++b)
	{
		vector<string> names;
		names.push_back(fn.blocks[b].name);
		for (size_t i = 0; i < fn.blocks[b].instructions.size(); ++i)
			if (fn.blocks[b].instructions[i].has_dest)
				names.push_back(fn.blocks[b].instructions[i].dest);
		for (size_t i = 0; i < fn.slots.size(); ++i)
			names.push_back(fn.slots[i].name);
		for (size_t n = 0; n < names.size(); ++n)
		{
			const string needle = "__o1inl";
			size_t pos = names[n].find(needle);
			while (pos != string::npos)
			{
				size_t begin = pos + needle.size();
				size_t end = begin;
				while (end < names[n].size() && names[n][end] >= '0' &&
				       names[n][end] <= '9')
					++end;
				if (end > begin)
					max_seen = max(max_seen, atoi(names[n].substr(begin, end - begin).c_str()));
				pos = names[n].find(needle, end);
			}
		}
	}
	return max_seen + 1;
}

void prepare_maps(const Function& callee,
                  const Instruction& call,
                  const string& prefix,
                  map<string, Value>& value_map,
                  map<string, string>& slot_map,
                  map<string, string>& block_map,
                  vector<Slot>& new_slots)
{
	for (size_t i = 0; i < callee.params.size() && i < call.args.size(); ++i)
		value_map[callee.params[i].name] = call.args[i];
	for (size_t i = 0; i < callee.slots.size(); ++i)
	{
		Slot slot = callee.slots[i];
		slot.name = prefixed_slot(prefix, slot.name);
		slot_map[callee.slots[i].name] = slot.name;
		new_slots.push_back(slot);
	}
	for (size_t i = 0; i < callee.blocks.size(); ++i)
		block_map[callee.blocks[i].name] =
		    prefixed_block(prefix, callee.blocks[i].name);
}

bool inline_single_block(Function& caller,
                         const Function& callee,
                         size_t block_index,
                         size_t ins_index,
                         const string& prefix)
{
	if (callee.blocks.size() != 1)
		return false;
	if (lowir2cy86::is_void_type(callee.ret) && function_contains_call(callee))
		return false;
	const Block& cb = callee.blocks[0];
	if (cb.instructions.empty() || cb.instructions.back().kind != InstrKind::Return)
		return false;
	Instruction call = caller.blocks[block_index].instructions[ins_index];
	map<string, Value> value_map;
	map<string, string> slot_map;
	map<string, string> block_map;
	vector<Slot> new_slots;
	prepare_maps(callee, call, prefix, value_map, slot_map, block_map, new_slots);
	caller.slots.insert(caller.slots.end(), new_slots.begin(), new_slots.end());
	vector<Instruction> cloned;
	for (size_t i = 0; i + 1 < cb.instructions.size(); ++i)
		cloned.push_back(clone_nonreturn_instruction(cb.instructions[i],
		                                             prefix,
		                                             value_map,
		                                             slot_map,
		                                             block_map));
	Instruction ret = cb.instructions.back();
	remap_instruction(ret, value_map, slot_map, block_map);
	Block& block = caller.blocks[block_index];
	vector<Instruction> out;
	out.insert(out.end(), block.instructions.begin(), block.instructions.begin() + ins_index);
	out.insert(out.end(), cloned.begin(), cloned.end());
	out.insert(out.end(), block.instructions.begin() + ins_index + 1, block.instructions.end());
	block.instructions.swap(out);
	if (call.has_dest && !lowir2cy86::is_void_type(ret.type))
		replace_temp_uses(caller, call.dest, ret.a);
	return true;
}

void append_return_rewrite(Block& out,
                           const Instruction& ret,
                           const Type& ret_type,
                           const string& cont,
                           const string& ret_slot,
                           bool object_return)
{
	if (!lowir2cy86::is_void_type(ret_type))
	{
		if (object_return)
			out.instructions.push_back(make_copyobj(ret_type, ret.a, ret_slot));
		else
			out.instructions.push_back(make_store(ret_type, ret.a, ret_slot));
	}
	out.instructions.push_back(make_jump(cont));
}

size_t count_returns(const Function& fn)
{
	size_t count = 0;
	for (size_t b = 0; b < fn.blocks.size(); ++b)
		for (size_t i = 0; i < fn.blocks[b].instructions.size(); ++i)
			if (fn.blocks[b].instructions[i].kind == InstrKind::Return)
				++count;
	return count;
}

void append_original_suffix(Block& out,
                            const Block& original,
                            size_t ins_index,
                            const Instruction& call,
                            const Value* replacement)
{
	map<string, Value> value_map;
	if (replacement != 0 && call.has_dest)
		value_map[call.dest] = *replacement;
	map<string, string> slot_map;
	map<string, string> block_map;
	for (size_t i = ins_index + 1; i < original.instructions.size(); ++i)
	{
		Instruction ins = original.instructions[i];
		remap_instruction(ins, value_map, slot_map, block_map);
		out.instructions.push_back(ins);
	}
}

bool inline_multi_block(Function& caller,
                        const Function& callee,
                        size_t block_index,
                        size_t ins_index,
                        const string& prefix,
                        bool keep_entry_separate)
{
	Instruction call = caller.blocks[block_index].instructions[ins_index];
	const bool object_return = lowir2cy86::is_obj_type(callee.ret);
	const bool scalar_return = !lowir2cy86::is_void_type(callee.ret) && !object_return;
	const bool void_multi_block =
	    lowir2cy86::is_void_type(callee.ret) && callee.blocks.size() > 1;
	const bool void_call_wrapper =
	    lowir2cy86::is_void_type(callee.ret) && function_contains_call(callee);
	const bool use_continuation =
	    count_returns(callee) != 1 || void_multi_block || void_call_wrapper;
	const bool needs_ret_slot =
	    use_continuation && (scalar_return || object_return);
	const string cont = "^" + prefix + "cont";
	const string ret_slot = object_return
	                            ? "$" + prefix + "retmergeobj__1"
	                            : "$" + prefix + "retmerge__1";
	map<string, Value> value_map;
	map<string, string> slot_map;
	map<string, string> block_map;
	vector<Slot> new_slots;
	prepare_maps(callee, call, prefix, value_map, slot_map, block_map, new_slots);
	caller.slots.insert(caller.slots.end(), new_slots.begin(), new_slots.end());
	if (needs_ret_slot)
	{
		Slot slot;
		slot.name = ret_slot;
		slot.type = callee.ret;
		caller.slots.push_back(slot);
	}

	Block original = caller.blocks[block_index];
	vector<Block> replacement;
	bool replace_whole_function = false;
	Value whole_function_replacement;
	Block entry = original;
	entry.instructions.assign(original.instructions.begin(),
	                          original.instructions.begin() + ins_index);
	vector<Block> cloned_blocks;
	for (size_t b = 0; b < callee.blocks.size(); ++b)
	{
		Block nb;
		nb.name = block_map[callee.blocks[b].name];
		for (size_t i = 0; i < callee.blocks[b].instructions.size(); ++i)
		{
			Instruction ins = callee.blocks[b].instructions[i];
			if (ins.kind == InstrKind::Return)
			{
				remap_instruction(ins, value_map, slot_map, block_map);
				if (use_continuation)
					append_return_rewrite(nb, ins, callee.ret, cont, ret_slot,
					                      object_return);
				else
				{
					const Value* suffix_replacement = 0;
					Value replacement;
					if ((scalar_return || object_return) && call.has_dest)
					{
						replacement = ins.a;
						suffix_replacement = &replacement;
						whole_function_replacement = replacement;
						replace_whole_function = true;
					}
					append_original_suffix(nb, original, ins_index, call,
					                       suffix_replacement);
				}
			}
			else
				nb.instructions.push_back(clone_nonreturn_instruction(ins,
				                                                      prefix,
				                                                      value_map,
				                                                      slot_map,
				                                                      block_map));
		}
		cloned_blocks.push_back(nb);
	}

	if (keep_entry_separate)
	{
		entry.instructions.push_back(make_jump(cloned_blocks[0].name));
		replacement.push_back(entry);
		replacement.insert(replacement.end(), cloned_blocks.begin(), cloned_blocks.end());
	}
	else
	{
		entry.instructions.insert(entry.instructions.end(),
		                          cloned_blocks[0].instructions.begin(),
		                          cloned_blocks[0].instructions.end());
		replacement.push_back(entry);
		replacement.insert(replacement.end(), cloned_blocks.begin() + 1, cloned_blocks.end());
	}

	if (use_continuation)
	{
		Block cont_block;
		cont_block.name = cont;
		if (scalar_return && call.has_dest)
			cont_block.instructions.push_back(make_load(call.dest, callee.ret, ret_slot));
		Value object_slot = named_value(ValueKind::Slot, ret_slot);
		append_original_suffix(cont_block,
		                       original,
		                       ins_index,
		                       call,
		                       object_return && call.has_dest ? &object_slot : 0);
		replacement.push_back(cont_block);
	}

	caller.blocks.erase(caller.blocks.begin() + block_index);
	caller.blocks.insert(caller.blocks.begin() + block_index,
	                     replacement.begin(),
	                     replacement.end());
	if (replace_whole_function)
		replace_temp_uses(caller, call.dest, whole_function_replacement);
	return true;
}

bool inline_call(Function& caller,
                 const Program& program,
                 size_t block_index,
                 size_t ins_index,
                 int index,
                 const set<string>& handlers,
                 map<string, bool>& static_eligible_cache,
                 map<pair<string, string>, bool>& recursive_inline_cache,
                 map<string, bool>& may_unwind_cache)
{
	Instruction& call = caller.blocks[block_index].instructions[ins_index];
	if (call.kind != InstrKind::Call || call.a.kind != ValueKind::Function)
		return false;
	map<string, size_t>::const_iterator it =
	    program.function_by_name.find(call.a.text);
	if (it == program.function_by_name.end())
		return false;
	const Function& callee = program.functions[it->second];
	if (!eligible_callee(program,
	                     caller,
	                     callee,
	                     static_eligible_cache,
	                     recursive_inline_cache))
		return false;
	if (handlers.count(caller.blocks[block_index].name) != 0)
		return false;
	const bool active_eh = active_eh_before(caller.blocks[block_index], ins_index);
	if (active_eh && function_may_unwind_cached(program, callee, may_unwind_cache))
		return false;
	const string prefix = "__o1inl" + to_string(index) + "__";
	if (inline_single_block(caller, callee, block_index, ins_index, prefix))
		return true;
	if (active_eh && !has_metadata(callee, "unwind", "no"))
		return false;
	return inline_multi_block(caller, callee, block_index, ins_index, prefix,
	                          active_eh);
}

int cached_next_inline_index(Function& fn, map<string, int>& inline_index_cache)
{
	map<string, int>::const_iterator found = inline_index_cache.find(fn.name);
	if (found != inline_index_cache.end())
		return found->second;
	int index = next_inline_index(fn);
	inline_index_cache[fn.name] = index;
	return index;
}

bool inline_function_once(Function& fn,
                          const Program& program,
                          map<string, int>& inline_index_cache)
{
	bool changed = false;
	map<string, bool> static_eligible_cache;
	map<pair<string, string>, bool> recursive_inline_cache;
	map<string, bool> may_unwind_cache;
	for (;;)
	{
		bool pass = false;
		int index = -1;
		set<string> handlers = eh_handler_blocks(fn);
		for (size_t b = 0; b < fn.blocks.size() && !pass; ++b)
			for (size_t i = 0; i < fn.blocks[b].instructions.size(); ++i)
			{
				const Instruction& candidate = fn.blocks[b].instructions[i];
				if (candidate.kind != InstrKind::Call ||
				    candidate.a.kind != ValueKind::Function)
					continue;
				if (index < 0)
					index = cached_next_inline_index(fn, inline_index_cache);
				if (inline_call(fn,
				                program,
				                b,
				                i,
				                index,
				                handlers,
				                static_eligible_cache,
				                recursive_inline_cache,
				                may_unwind_cache))
				{
					inline_index_cache[fn.name] = index + 1;
					rebuild_function(fn);
					pass = true;
					changed = true;
					break;
				}
			}
		if (!pass)
			break;
	}
	return changed;
}

int inline_visit_priority(const Function& fn)
{
	if (lowir2cy86::metadata_value(fn.metadata, "binding") == "strong" &&
	    lowir2cy86::metadata_value(fn.metadata, "role") != "entry")
		return 0;
	if (lowir2cy86::metadata_value(fn.metadata, "role") == "entry")
		return 1;
	if (lowir2cy86::metadata_value(fn.metadata, "binding") != "weak")
		return 6;
	string name = body_name(fn.name);
	size_t pos = name.find("__");
	string klass = pos == string::npos ? name : name.substr(0, pos);
	if (name == klass + "__" + klass)
		return 2;
	if (name == klass + "___" + klass)
		return 3;
	if (name.find("__operator_") != string::npos)
		return 4;
	return 5;
}

string inline_visit_order_key(const Function& fn)
{
	return lowir2cy86::metadata_value(fn.metadata, "object");
}

}  // namespace

bool inline_o1_once(Program& program, map<string, int>& inline_index_cache)
{
	for (int priority = 0; priority < 7; ++priority)
	{
		bool changed = false;
		vector<size_t> order;
		for (size_t i = 0; i < program.functions.size(); ++i)
		{
			if (program.functions[i].declaration ||
			    inline_visit_priority(program.functions[i]) != priority)
				continue;
			order.push_back(i);
		}
		stable_sort(order.begin(),
		            order.end(),
		            [&program](size_t lhs, size_t rhs) {
			            string lkey = inline_visit_order_key(program.functions[lhs]);
			            string rkey = inline_visit_order_key(program.functions[rhs]);
			            if (lkey.empty() && rkey.empty())
				            return false;
			            if (lkey.empty() != rkey.empty())
				            return !lkey.empty();
			            if (lkey != rkey)
				            return lkey < rkey;
			            return program.functions[lhs].name <
			                   program.functions[rhs].name;
		            });
		for (size_t oi = 0; oi < order.size(); ++oi)
		{
			if (inline_function_once(program.functions[order[oi]],
			                         program,
			                         inline_index_cache))
				changed = true;
		}
		if (changed)
			return true;
	}
	return false;
}

bool inline_o1_once(Program& program)
{
	map<string, int> inline_index_cache;
	return inline_o1_once(program, inline_index_cache);
}

}  // namespace lowiropt
