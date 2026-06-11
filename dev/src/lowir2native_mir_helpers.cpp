#include "lowir2cy86.h"
#include "lowir2native.h"
#include "lowir2native_mir_helpers.h"

#include <algorithm>
#include <cstddef>
#include <fstream>
#include <map>
#include <ostream>
#include <set>
#include <stdexcept>
#include <string>

using namespace std;

namespace lowir2native {

bool metadata_is(const lowir2cy86::Metadata& md,
                 const string& key,
                 const string& value);
void note_slot_escapes(const lowir2cy86::Instruction& ins,
                       set<string>& escaped);
void note_slot_escape(const lowir2cy86::Value& value,
                      set<string>& escaped);
bool metadata_is_pass_address(const lowir2cy86::Metadata& md);
bool mir_param_is_used(const lowir2cy86::Function& fn, const string& name);
bool mir_value_uses_name(const lowir2cy86::Value& value, const string& name);
bool mir_all_nonfloat_params_homed(const lowir2cy86::Function& fn);
bool mir_has_full_gpr_indirect_call(const lowir2cy86::Function& fn);
bool mir_has_chained_indirect_call(const lowir2cy86::Function& fn);
bool mir_has_direct_object_call_arg_temp(const lowir2cy86::Program& program,
                                         const lowir2cy86::Function& fn);
bool mir_has_stack_arg_call(const lowir2cy86::Program& program,
                            const lowir2cy86::Function& fn);
bool mir_has_read_only_param_forwarding_frame(const lowir2cy86::Function& fn);
bool mir_has_direct_param_copyobj_forwarding_frame(
    const lowir2cy86::Function& fn);
bool mir_has_call_result_branch_after_call(const lowir2cy86::Function& fn);
bool mir_has_narrow_rcx_global_store_param(const lowir2cy86::Function& fn);
bool mir_has_thread_local_store_pressure(const lowir2cy86::Program& program,
                                         const lowir2cy86::Function& fn);
bool mir_has_sret_frame_temps(const lowir2cy86::Function& fn);
bool mir_has_reference_store_frame_temps(const lowir2cy86::Function& fn);
string mir_temp_reference_origin(
    const lowir2cy86::Function& fn,
    const string& name,
    const map<string, const lowir2cy86::Instruction*>& definitions,
    const map<string, string>& slot_params,
    set<string>& seen);
bool mir_temp_used_after_position(const lowir2cy86::Function& fn,
                                  const string& name,
                                  int after_pos);
void note_mir_live_use(const lowir2cy86::Value& value, int pos,
                       map<string, int>& last_use);
bool mir_temp_live_across_call(const lowir2cy86::Function& fn,
                               const string& name);
string mir_param_abi_type_text(const lowir2cy86::Type& type);
string storage_suffix(const lowir2cy86::Type& type);
string abi_gpr(size_t index);
string mem_for_offset(size_t offset);
bool function_uses_float(const lowir2cy86::Program& program,
                         const lowir2cy86::Function& fn);
bool function_uses_f80(const lowir2cy86::Function& fn);
size_t mir_slot_offset(const lowir2cy86::Function& fn,
                       const string& name,
                       const set<string>& omitted_slots);
size_t raw_stack_size(const lowir2cy86::Function& fn,
                      const set<string>& omitted_slots);
size_t mir_f80_offset(const lowir2cy86::Function& fn, const string& name);
bool mir_f80_temp_has_storage(const lowir2cy86::Function& fn, const string& name);
size_t align_to(size_t value, size_t alignment);

string effective_target(const Options& options)
{
	return options.target.empty() ? "linux" : options.target;
}

void write_text_file(const string& path, const string& text)
{
	ofstream out(path.c_str(), ios::binary);
	if (!out)
		throw runtime_error("cannot open output file");
	out << text;
	out.close();
	if (!out)
		throw runtime_error("cannot write output file");
}

void dump_mir_startup(ostream& out, const lowir2cy86::Program& program)
{
	if (program.entry_function.empty())
		return;
	out << "startup\n";
	if (!program.init_function.empty())
		out << "    call " << program.init_function << "\n";
	out << "    call " << program.entry_function << "\n";
	if (!program.fini_function.empty())
	{
		out << "    mov r12, rax\n";
		out << "    call " << program.fini_function << "\n";
		out << "    mov rdi, r12\n";
	}
	else
		out << "    mov rdi, rax\n";
	out << "    exit\n\n";
}

string addend_text(bool has, int addend)
{
	if (!has)
		return "";
	return addend >= 0 ? " + " + to_string(addend)
	                   : " - " + to_string(-addend);
}

void dump_global_item(ostream& out, const lowir2cy86::GlobalDataItem& item)
{
	if (item.kind == "zero")
		out << "  item zero " << item.zero_bytes << "\n";
	else if (item.kind == "addr")
		out << "  item ptr addr " << item.target
		    << addend_text(item.has_addend, item.addend) << "\n";
	else
		out << "  item " << item.type.text << " " << item.literal << "\n";
}

void dump_mir_globals(ostream& out, const lowir2cy86::Program& program)
{
	for (size_t i = 0; i < program.globals.size(); ++i)
	{
		const lowir2cy86::Global& g = program.globals[i];
		if (g.declaration)
			continue;
		out << "global " << g.name;
		if (metadata_is(g.metadata, "storage", "readonly"))
			out << " readonly";
		if (metadata_is(g.metadata, "storage", "thread_local"))
			out << " thread_local";
		out << "\n";
		if (g.has_type)
		{
			out << "  storage scalar " << g.type.text << "\n";
			if (g.init.kind == "zero")
				out << "  init " << g.type.text << " 0\n";
			else if (g.init.kind == "addr")
				out << "  init addr " << g.init.target
				    << addend_text(g.init.has_addend, g.init.addend) << "\n";
			else
				out << "  init " << g.type.text << " " << g.init.literal << "\n";
		}
		else
		{
			out << "  storage data\n";
			for (size_t j = 0; j < g.data.size(); ++j)
				dump_global_item(out, g.data[j]);
		}
		out << "\n";
	}
}

void analyze_mir_promoted_slots(const lowir2cy86::Function& fn,
                                map<string, string>& promoted_slot_params,
                                map<string, string>& promoted_loads,
                                set<string>& omitted_slots)
{
	map<string, int> stores;
	map<string, int> loads;
	map<string, string> stored_param;
	map<string, string> addr_slot;
	set<string> late_load_slots;
	set<string> escaped;
	for (size_t i = 0; i < fn.blocks.size(); ++i)
		for (size_t j = 0; j < fn.blocks[i].instructions.size(); ++j)
		{
			const lowir2cy86::Instruction& ins = fn.blocks[i].instructions[j];
			if (ins.kind == lowir2cy86::InstrKind::Addr &&
			    ins.a.kind == lowir2cy86::ValueKind::Slot)
				addr_slot[ins.dest] = ins.a.text;
		}
	for (size_t i = 0; i < fn.blocks.size(); ++i)
	{
		for (size_t j = 0; j < fn.blocks[i].instructions.size(); ++j)
		{
			const lowir2cy86::Instruction& ins = fn.blocks[i].instructions[j];
			if (ins.kind == lowir2cy86::InstrKind::Addr &&
			    ins.a.kind == lowir2cy86::ValueKind::Slot)
				continue;
			if (ins.kind == lowir2cy86::InstrKind::Store &&
			    ins.b.kind == lowir2cy86::ValueKind::Slot)
			{
				++stores[ins.b.text];
				if (ins.a.kind == lowir2cy86::ValueKind::Temp &&
				    fn.param_types.find(ins.a.text) != fn.param_types.end() &&
				    fn.slot_types.find(ins.b.text) != fn.slot_types.end() &&
				    fn.param_types.find(ins.a.text)->second.text ==
				        fn.slot_types.find(ins.b.text)->second.text)
					stored_param[ins.b.text] = ins.a.text;
				else
					escaped.insert(ins.b.text);
			}
			else if (ins.kind == lowir2cy86::InstrKind::Load &&
			         ins.a.kind == lowir2cy86::ValueKind::Slot)
			{
				++loads[ins.a.text];
				if (i != 0)
					late_load_slots.insert(ins.a.text);
			}
			else if (ins.kind == lowir2cy86::InstrKind::Load &&
			         ins.a.kind == lowir2cy86::ValueKind::Temp &&
			         addr_slot.find(ins.a.text) != addr_slot.end())
			{
				const string& slot = addr_slot[ins.a.text];
				++loads[slot];
				if (i != 0)
					late_load_slots.insert(slot);
			}
			else if (ins.kind == lowir2cy86::InstrKind::CopyObj &&
			         ins.a.kind == lowir2cy86::ValueKind::Temp &&
			         ins.b.kind == lowir2cy86::ValueKind::Temp &&
			         addr_slot.find(ins.b.text) != addr_slot.end() &&
			         fn.param_types.find(ins.a.text) != fn.param_types.end() &&
			         lowir2cy86::is_obj_type(fn.param_types.find(ins.a.text)->second))
			{
				const string& slot = addr_slot[ins.b.text];
				map<string, lowir2cy86::Type>::const_iterator sit =
				    fn.slot_types.find(slot);
				const lowir2cy86::Type& param_type =
				    fn.param_types.find(ins.a.text)->second;
				if (sit != fn.slot_types.end() &&
				    sit->second.text == param_type.text &&
				    param_type.obj_size == ins.span.bytes &&
				    param_type.obj_align == ins.span.align)
				{
					++stores[slot];
					stored_param[slot] = ins.a.text;
				}
				else
					escaped.insert(slot);
			}
			else
			{
				note_slot_escapes(ins, escaped);
				if (ins.a.kind == lowir2cy86::ValueKind::Temp &&
				    addr_slot.find(ins.a.text) != addr_slot.end())
					escaped.insert(addr_slot[ins.a.text]);
				if (ins.b.kind == lowir2cy86::ValueKind::Temp &&
				    addr_slot.find(ins.b.text) != addr_slot.end())
					escaped.insert(addr_slot[ins.b.text]);
				if (ins.c.kind == lowir2cy86::ValueKind::Temp &&
				    addr_slot.find(ins.c.text) != addr_slot.end())
					escaped.insert(addr_slot[ins.c.text]);
				for (size_t a = 0; a < ins.args.size(); ++a)
					if (ins.args[a].kind == lowir2cy86::ValueKind::Temp &&
					    addr_slot.find(ins.args[a].text) != addr_slot.end())
						escaped.insert(addr_slot[ins.args[a].text]);
			}
		}
	}
	for (map<string, int>::const_iterator it = stores.begin();
	     it != stores.end(); ++it)
	{
		if (it->second == 1 && escaped.find(it->first) == escaped.end() &&
		    stored_param.find(it->first) != stored_param.end())
		{
				bool late_param_load = false;
				if (late_load_slots.find(it->first) != late_load_slots.end())
					for (size_t p = 0; p < fn.params.size(); ++p)
						if (fn.params[p].name == stored_param[it->first] &&
						    (mir_param_needs_slot(fn, p) || fn.blocks.size() > 1))
							late_param_load = true;
				if (late_param_load)
					continue;
			omitted_slots.insert(it->first);
			if (loads[it->first] != 0)
				promoted_slot_params[it->first] = stored_param[it->first];
		}
	}
	for (size_t i = 0; i < fn.blocks.size(); ++i)
		for (size_t j = 0; j < fn.blocks[i].instructions.size(); ++j)
		{
			const lowir2cy86::Instruction& ins = fn.blocks[i].instructions[j];
			if (ins.kind == lowir2cy86::InstrKind::Load &&
			    ins.a.kind == lowir2cy86::ValueKind::Slot)
			{
				map<string, string>::const_iterator pit =
				    promoted_slot_params.find(ins.a.text);
				if (pit != promoted_slot_params.end())
					promoted_loads[ins.dest] = pit->second;
			}
		}
}

void note_slot_escapes(const lowir2cy86::Instruction& ins,
                       set<string>& escaped)
{
	note_slot_escape(ins.a, escaped);
	note_slot_escape(ins.b, escaped);
	note_slot_escape(ins.c, escaped);
	for (size_t i = 0; i < ins.args.size(); ++i)
		note_slot_escape(ins.args[i], escaped);
}

void note_slot_escape(const lowir2cy86::Value& value,
                      set<string>& escaped)
{
	if (value.kind == lowir2cy86::ValueKind::Slot)
		escaped.insert(value.text);
}

void analyze_mir_frame_temps(const lowir2cy86::Program& program,
                             const lowir2cy86::Function& fn,
                             set<string>& frame_temps)
{
	for (size_t i = 0; i < fn.blocks.size(); ++i)
		for (size_t j = 0; j < fn.blocks[i].instructions.size(); ++j)
		{
			const lowir2cy86::Instruction& ins = fn.blocks[i].instructions[j];
			if (ins.kind != lowir2cy86::InstrKind::Call)
				continue;
			for (size_t a = 0; a < ins.args.size(); ++a)
				if (mir_call_arg_needs_address(program, ins, a) &&
			    ins.args[a].kind == lowir2cy86::ValueKind::Temp &&
				    !lowir2cy86::is_ptr_type(mir_lookup_type(fn, ins.args[a])))
					frame_temps.insert(ins.args[a].text);
		}
}

void dump_mir_frame_temps(ostream& out,
                          const lowir2cy86::Function& fn,
                          const set<string>& frame_temps,
                          const set<string>& omitted_slots)
{
	size_t bytes = 0;
	for (size_t i = 0; i < fn.params.size(); ++i)
		if (mir_param_needs_slot(fn, i))
			bytes = max(bytes, mir_param_slot_offset(fn, i));
	for (size_t i = 0; i < fn.slots.size(); ++i)
		bytes = max(bytes, mir_slot_offset(fn, fn.slots[i].name, omitted_slots));
	for (size_t i = 0; i < fn.temp_order.size(); ++i)
	{
		const string& name = fn.temp_order[i];
		if (frame_temps.find(name) == frame_temps.end())
			continue;
		const lowir2cy86::Type& type = fn.temp_types.find(name)->second;
		const size_t align = lowir2cy86::is_obj_type(type)
		                         ? type.align
		                         : lowir2cy86::storage_size(type);
		bytes = align_to(bytes, align);
		bytes += lowir2cy86::is_obj_type(type)
		             ? lowir2cy86::stack_storage_size(type)
		             : lowir2cy86::storage_size(type);
		out << "    temp " << name << " -> "
		    << mem_for_offset(bytes)
		    << " : " << type.text << "\n";
	}
}

bool mir_call_arg_needs_address(const lowir2cy86::Program& program,
                                const lowir2cy86::Instruction& ins,
                                size_t index)
{
	if (index < ins.signature.params.size() &&
	    lowir2cy86::is_ptr_type(ins.signature.params[index].type))
		return metadata_is_pass_address(ins.signature.params[index].metadata);
	if (ins.a.kind != lowir2cy86::ValueKind::Function)
		return false;
	map<string, size_t>::const_iterator it = program.function_by_name.find(ins.a.text);
	if (it == program.function_by_name.end())
		return false;
	const lowir2cy86::Function& callee = program.functions[it->second];
	return index < callee.params.size() &&
	       lowir2cy86::is_ptr_type(callee.params[index].type) &&
	       metadata_is_pass_address(callee.params[index].metadata);
}

bool metadata_is_pass_address(const lowir2cy86::Metadata& md)
{
	const string pass = lowir2cy86::metadata_value(md, "pass");
	return pass == "reference" || pass == "indirect_result";
}

bool mir_is_xmm_type(const lowir2cy86::Type& type)
{
	return lowir2cy86::is_float_type(type) && !lowir2cy86::is_f80_type(type);
}

string abi_xmm(size_t index)
{
	return "xmm" + to_string(index);
}

size_t abi_stack_bytes(const lowir2cy86::Type& type)
{
	return lowir2cy86::is_f80_type(type) ? 16 : 8;
}

string mir_abi_param_location(const lowir2cy86::Function& fn, size_t index)
{
	size_t gpr = 0;
	size_t xmm = 0;
	size_t stack = 0;
	for (size_t i = 0; i < fn.params.size(); ++i)
	{
		const lowir2cy86::Type& type = fn.params[i].type;
		string loc;
		if (mir_is_xmm_type(type) && xmm < 8)
			loc = abi_xmm(xmm++);
		else if (!lowir2cy86::is_f80_type(type) && gpr < 6)
			loc = abi_gpr(gpr++);
		else
		{
			loc = "[rbp+" + to_string(16 + stack) + "]";
			stack += abi_stack_bytes(type);
		}
		if (i == index)
			return loc;
	}
	return "";
}

bool mir_param_needs_slot(const lowir2cy86::Function& fn, size_t index)
{
	if (index >= fn.params.size())
		return false;
	const string loc = mir_abi_param_location(fn, index);
	return mir_is_xmm_type(fn.params[index].type) ||
	       lowir2cy86::is_f80_type(fn.params[index].type) ||
	       (lowir2cy86::is_obj_type(fn.params[index].type) &&
	        fn.params[index].type.obj_size <= 8) ||
	       loc.find("[rbp+") == 0 ||
	       !mir_param_is_used(fn, fn.params[index].name);
}

bool mir_value_uses_name(const lowir2cy86::Value& value, const string& name)
{
	return value.kind == lowir2cy86::ValueKind::Temp && value.text == name;
}

bool mir_param_is_used(const lowir2cy86::Function& fn, const string& name)
{
	for (size_t i = 0; i < fn.blocks.size(); ++i)
		for (size_t j = 0; j < fn.blocks[i].instructions.size(); ++j)
		{
			const lowir2cy86::Instruction& ins = fn.blocks[i].instructions[j];
			if (mir_value_uses_name(ins.a, name) ||
			    mir_value_uses_name(ins.b, name) ||
			    mir_value_uses_name(ins.c, name))
				return true;
			for (size_t a = 0; a < ins.args.size(); ++a)
				if (mir_value_uses_name(ins.args[a], name))
					return true;
			for (size_t s = 0; s < ins.switch_cases.size(); ++s)
				if (mir_value_uses_name(ins.switch_cases[s].value, name))
					return true;
		}
	return false;
}

bool mir_all_nonfloat_params_homed(const lowir2cy86::Function& fn)
{
	if (fn.params.empty())
		return false;
	for (size_t i = 0; i < fn.params.size(); ++i)
	{
		if (lowir2cy86::is_float_type(fn.params[i].type))
			return false;
		if (!mir_param_needs_slot(fn, i))
			return false;
	}
	return true;
}

lowir2cy86::Type mir_call_param_type(const lowir2cy86::Program& program,
                                     const lowir2cy86::Function& fn,
                                     const lowir2cy86::Instruction& ins,
                                     size_t index)
{
	if (index < ins.signature.params.size())
		return ins.signature.params[index].type;
	if (ins.a.kind == lowir2cy86::ValueKind::Function)
	{
		map<string, size_t>::const_iterator it =
		    program.function_by_name.find(ins.a.text);
		if (it != program.function_by_name.end() &&
		    index < program.functions[it->second].params.size())
			return program.functions[it->second].params[index].type;
	}
	if (index < ins.args.size())
		return mir_lookup_type(fn, ins.args[index]);
	return lowir2cy86::Type();
}

string mir_call_arg_register(const lowir2cy86::Program& program,
                             const lowir2cy86::Function& fn,
                             const lowir2cy86::Instruction& ins,
                             size_t index)
{
	size_t gpr = 0;
	size_t xmm = 0;
	for (size_t i = 0; i <= index && i < ins.args.size(); ++i)
	{
		const lowir2cy86::Type type = mir_call_param_type(program, fn, ins, i);
		string reg;
		if (mir_is_xmm_type(type) && xmm < 8)
			reg = abi_xmm(xmm++);
		else if (!lowir2cy86::is_f80_type(type) && gpr < 6)
			reg = abi_gpr(gpr++);
		if (i == index)
			return reg;
	}
	return "";
}

size_t mir_call_stack_arg_offset(const lowir2cy86::Program& program,
                                 const lowir2cy86::Function& fn,
                                 const lowir2cy86::Instruction& ins,
                                 size_t index)
{
	size_t stack = 0;
	for (size_t i = 0; i <= index && i < ins.args.size(); ++i)
	{
		if (mir_call_arg_register(program, fn, ins, i).empty())
		{
			if (i == index)
				return stack;
			stack += abi_stack_bytes(mir_call_param_type(program, fn, ins, i));
		}
	}
	return stack;
}

size_t mir_call_stack_arg_bytes(const lowir2cy86::Program& program,
                                const lowir2cy86::Function& fn,
                                const lowir2cy86::Instruction& ins)
{
	size_t bytes = 0;
	for (size_t i = 0; i < ins.args.size(); ++i)
		if (mir_call_arg_register(program, fn, ins, i).empty())
			bytes += abi_stack_bytes(mir_call_param_type(program, fn, ins, i));
	return align_to(bytes, 16);
}

bool mir_has_stack_arg_call(const lowir2cy86::Program& program,
                            const lowir2cy86::Function& fn)
{
	for (size_t b = 0; b < fn.blocks.size(); ++b)
		for (size_t i = 0; i < fn.blocks[b].instructions.size(); ++i)
		{
			const lowir2cy86::Instruction& ins = fn.blocks[b].instructions[i];
			if (ins.kind == lowir2cy86::InstrKind::Call &&
			    !lowir2cy86::is_f80_type(ins.type) &&
			    !mir_call_has_f80_arg(fn, ins) &&
			    mir_call_stack_arg_bytes(program, fn, ins) != 0)
				return true;
		}
	return false;
}

bool mir_has_sret_frame_temps(const lowir2cy86::Function& fn)
{
	if (mir_has_reference_store_frame_temps(fn))
		return true;
	if (fn.params.empty() ||
	    fn.params[0].name != "%ret" ||
	    metadata_value(fn.params[0].metadata, "pass") != "indirect_result")
		return false;
	if (fn.blocks.size() > 1)
		return true;
	for (size_t b = 0; b < fn.blocks.size(); ++b)
		for (size_t i = 0; i < fn.blocks[b].instructions.size(); ++i)
			if (fn.blocks[b].instructions[i].kind ==
			    lowir2cy86::InstrKind::Call)
				return true;
	return false;
}

bool mir_has_reference_store_frame_temps(const lowir2cy86::Function& fn)
{
	if (fn.blocks.size() <= 1 || fn.blocks.empty())
		return false;
	map<string, string> slot_params;
	for (size_t b = 0; b < fn.blocks.size(); ++b)
		for (size_t i = 0; i < fn.blocks[b].instructions.size(); ++i)
		{
			const lowir2cy86::Instruction& ins = fn.blocks[b].instructions[i];
			if (ins.kind != lowir2cy86::InstrKind::Store ||
			    ins.a.kind != lowir2cy86::ValueKind::Temp ||
			    ins.b.kind != lowir2cy86::ValueKind::Slot)
				continue;
			for (size_t p = 0; p < fn.params.size(); ++p)
				if (fn.params[p].name == ins.a.text &&
				    metadata_value(fn.params[p].metadata, "pass") ==
				        "reference")
					slot_params[ins.b.text] = ins.a.text;
		}
	if (slot_params.empty())
		return false;
	map<string, const lowir2cy86::Instruction*> definitions;
	for (size_t b = 0; b < fn.blocks.size(); ++b)
		for (size_t i = 0; i < fn.blocks[b].instructions.size(); ++i)
			if (fn.blocks[b].instructions[i].has_dest)
				definitions[fn.blocks[b].instructions[i].dest] =
				    &fn.blocks[b].instructions[i];
	const lowir2cy86::Block& entry = fn.blocks[0];
	for (size_t i = 0; i < entry.instructions.size(); ++i)
	{
		const lowir2cy86::Instruction& ins = entry.instructions[i];
		if (ins.kind == lowir2cy86::InstrKind::Branch ||
		    ins.kind == lowir2cy86::InstrKind::Jump ||
		    ins.kind == lowir2cy86::InstrKind::Switch ||
		    ins.kind == lowir2cy86::InstrKind::Return)
			break;
		if (ins.kind != lowir2cy86::InstrKind::Store ||
		    ins.b.kind != lowir2cy86::ValueKind::Temp)
			continue;
		set<string> seen;
		if (!mir_temp_reference_origin(fn, ins.b.text, definitions,
		                               slot_params, seen).empty())
			return true;
	}
	return false;
}

string mir_temp_reference_origin(
    const lowir2cy86::Function& fn,
    const string& name,
    const map<string, const lowir2cy86::Instruction*>& definitions,
    const map<string, string>& slot_params,
    set<string>& seen)
{
	if (!seen.insert(name).second)
		return "";
	for (size_t p = 0; p < fn.params.size(); ++p)
		if (fn.params[p].name == name)
			return metadata_value(fn.params[p].metadata, "pass") ==
			               "reference"
			           ? name
			           : "";
	map<string, const lowir2cy86::Instruction*>::const_iterator it =
	    definitions.find(name);
	if (it == definitions.end())
		return "";
	const lowir2cy86::Instruction& ins = *it->second;
	if (ins.kind == lowir2cy86::InstrKind::Load)
	{
		if (ins.a.kind == lowir2cy86::ValueKind::Slot)
		{
			map<string, string>::const_iterator sit =
			    slot_params.find(ins.a.text);
			return sit == slot_params.end() ? "" : sit->second;
		}
		if (ins.a.kind == lowir2cy86::ValueKind::Temp)
			return mir_temp_reference_origin(fn, ins.a.text,
			                                 definitions, slot_params,
			                                 seen);
	}
	if ((ins.kind == lowir2cy86::InstrKind::Index ||
	     ins.kind == lowir2cy86::InstrKind::Copy ||
	     (ins.kind == lowir2cy86::InstrKind::Unary && ins.op == "decay")) &&
	    ins.a.kind == lowir2cy86::ValueKind::Temp)
		return mir_temp_reference_origin(fn, ins.a.text, definitions,
		                                 slot_params, seen);
	return "";
}

bool mir_has_full_gpr_indirect_call(const lowir2cy86::Function& fn)
{
	for (size_t b = 0; b < fn.blocks.size(); ++b)
		for (size_t i = 0; i < fn.blocks[b].instructions.size(); ++i)
		{
			const lowir2cy86::Instruction& ins = fn.blocks[b].instructions[i];
			if (ins.kind != lowir2cy86::InstrKind::Call ||
			    ins.a.kind == lowir2cy86::ValueKind::Function ||
			    ins.args.size() < 6)
				continue;
			bool full = true;
			for (size_t a = 0; a < 6; ++a)
			{
				const lowir2cy86::Type type =
				    a < ins.signature.params.size()
				        ? ins.signature.params[a].type
				        : mir_lookup_type(fn, ins.args[a]);
				if (mir_is_xmm_type(type) || lowir2cy86::is_f80_type(type))
					full = false;
			}
			if (full &&
			    (ins.args[0].kind != lowir2cy86::ValueKind::Temp ||
			     !mir_temp_live_across_call(fn, ins.args[0].text)))
				return true;
		}
	return false;
}

void note_mir_live_use(const lowir2cy86::Value& value, int pos,
                       map<string, int>& last_use)
{
	if (value.kind == lowir2cy86::ValueKind::Temp)
		last_use[value.text] = pos;
}

bool mir_temp_live_across_call(const lowir2cy86::Function& fn,
                               const string& name)
{
	map<string, int> def_pos;
	map<string, int> last_use;
	vector<int> calls;
	for (size_t i = 0; i < fn.params.size(); ++i)
		def_pos[fn.params[i].name] = -1;
	int pos = 0;
	for (size_t b = 0; b < fn.blocks.size(); ++b)
		for (size_t i = 0; i < fn.blocks[b].instructions.size(); ++i, ++pos)
		{
			const lowir2cy86::Instruction& ins = fn.blocks[b].instructions[i];
			note_mir_live_use(ins.a, pos, last_use);
			note_mir_live_use(ins.b, pos, last_use);
			note_mir_live_use(ins.c, pos, last_use);
			for (size_t a = 0; a < ins.args.size(); ++a)
				note_mir_live_use(ins.args[a], pos, last_use);
			for (size_t s = 0; s < ins.switch_cases.size(); ++s)
				note_mir_live_use(ins.switch_cases[s].value, pos, last_use);
			if (ins.kind == lowir2cy86::InstrKind::Call)
				calls.push_back(pos);
			if (ins.has_dest)
				def_pos[ins.dest] = pos;
		}
	map<string, int>::const_iterator dit = def_pos.find(name);
	map<string, int>::const_iterator lit = last_use.find(name);
	if (dit == def_pos.end() || lit == last_use.end())
		return false;
	for (size_t i = 0; i < calls.size(); ++i)
		if (dit->second < calls[i] && calls[i] < lit->second)
			return true;
	return false;
}

bool mir_has_narrow_rcx_global_store_param(const lowir2cy86::Function& fn)
{
	size_t global_stores = 0;
	for (size_t b = 0; b < fn.blocks.size(); ++b)
		for (size_t i = 0; i < fn.blocks[b].instructions.size(); ++i)
			if (fn.blocks[b].instructions[i].kind == lowir2cy86::InstrKind::Store &&
			    fn.blocks[b].instructions[i].b.kind ==
			        lowir2cy86::ValueKind::Global)
				++global_stores;
	if (global_stores < 2)
		return false;
	for (size_t b = 0; b < fn.blocks.size(); ++b)
		for (size_t i = 0; i < fn.blocks[b].instructions.size(); ++i)
		{
			const lowir2cy86::Instruction& ins = fn.blocks[b].instructions[i];
			if (ins.kind != lowir2cy86::InstrKind::Store ||
			    ins.b.kind != lowir2cy86::ValueKind::Global ||
			    ins.a.kind != lowir2cy86::ValueKind::Temp)
				continue;
			for (size_t p = 0; p < fn.params.size(); ++p)
				if (fn.params[p].name == ins.a.text &&
				    mir_abi_param_location(fn, p) == "rcx" &&
				    lowir2cy86::is_integer_type(fn.params[p].type) &&
				    fn.params[p].type.bits < 64)
					return true;
		}
	return false;
}

bool mir_has_thread_local_store_pressure(const lowir2cy86::Program& program,
                                         const lowir2cy86::Function& fn)
{
	map<string, int> def_pos;
	int pos = 0;
	for (size_t b = 0; b < fn.blocks.size(); ++b)
		for (size_t i = 0; i < fn.blocks[b].instructions.size(); ++i, ++pos)
			if (fn.blocks[b].instructions[i].has_dest)
				def_pos[fn.blocks[b].instructions[i].dest] = pos;
	pos = 0;
	for (size_t b = 0; b < fn.blocks.size(); ++b)
		for (size_t i = 0; i < fn.blocks[b].instructions.size(); ++i, ++pos)
		{
			const lowir2cy86::Instruction& ins = fn.blocks[b].instructions[i];
			if (ins.kind != lowir2cy86::InstrKind::Store ||
			    ins.a.kind != lowir2cy86::ValueKind::Temp ||
			    ins.b.kind != lowir2cy86::ValueKind::Global)
				continue;
			map<string, size_t>::const_iterator git =
			    program.global_by_name.find(ins.b.text);
			if (git != program.global_by_name.end() &&
			    metadata_value(program.globals[git->second].metadata,
			                   "storage") == "thread_local")
			{
				size_t live_temps = 0;
				for (map<string, int>::const_iterator it = def_pos.begin();
				     it != def_pos.end(); ++it)
					if (it->second < pos &&
					    mir_temp_used_after_position(fn, it->first, pos))
						++live_temps;
				if (live_temps > 1)
					return true;
			}
		}
	return false;
}

bool mir_temp_used_after_position(const lowir2cy86::Function& fn,
                                  const string& name,
                                  int after_pos)
{
	int pos = 0;
	for (size_t b = 0; b < fn.blocks.size(); ++b)
		for (size_t i = 0; i < fn.blocks[b].instructions.size(); ++i, ++pos)
			if (pos > after_pos &&
			    mir_value_uses_name(fn.blocks[b].instructions[i].a, name))
				return true;
			else if (pos > after_pos &&
			         mir_value_uses_name(fn.blocks[b].instructions[i].b, name))
				return true;
			else if (pos > after_pos &&
			         mir_value_uses_name(fn.blocks[b].instructions[i].c, name))
				return true;
			else if (pos > after_pos)
			{
				const lowir2cy86::Instruction& ins =
				    fn.blocks[b].instructions[i];
				for (size_t a = 0; a < ins.args.size(); ++a)
					if (mir_value_uses_name(ins.args[a], name))
						return true;
				for (size_t s = 0; s < ins.switch_cases.size(); ++s)
					if (mir_value_uses_name(ins.switch_cases[s].value, name))
						return true;
			}
	return false;
}

bool mir_has_chained_indirect_call(const lowir2cy86::Function& fn)
{
	map<string, const lowir2cy86::Instruction*> defs;
	for (size_t b = 0; b < fn.blocks.size(); ++b)
		for (size_t i = 0; i < fn.blocks[b].instructions.size(); ++i)
		{
			const lowir2cy86::Instruction& ins = fn.blocks[b].instructions[i];
			if (ins.has_dest)
				defs[ins.dest] = &ins;
		}
	for (size_t b = 0; b < fn.blocks.size(); ++b)
		for (size_t i = 0; i < fn.blocks[b].instructions.size(); ++i)
		{
			const lowir2cy86::Instruction& ins = fn.blocks[b].instructions[i];
			if (ins.kind != lowir2cy86::InstrKind::Call ||
			    ins.a.kind != lowir2cy86::ValueKind::Temp)
				continue;
			map<string, const lowir2cy86::Instruction*>::const_iterator it =
			    defs.find(ins.a.text);
			if (it != defs.end() &&
			    it->second->kind == lowir2cy86::InstrKind::Load &&
			    it->second->a.kind == lowir2cy86::ValueKind::Temp)
				return true;
		}
	return false;
}

bool mir_has_direct_object_call_arg_temp(const lowir2cy86::Program& program,
                                         const lowir2cy86::Function& fn)
{
	map<string, const lowir2cy86::Instruction*> defs;
	for (size_t b = 0; b < fn.blocks.size(); ++b)
		for (size_t i = 0; i < fn.blocks[b].instructions.size(); ++i)
		{
			const lowir2cy86::Instruction& ins = fn.blocks[b].instructions[i];
			if (ins.has_dest)
				defs[ins.dest] = &ins;
		}
	for (size_t b = 0; b < fn.blocks.size(); ++b)
		for (size_t i = 0; i < fn.blocks[b].instructions.size(); ++i)
		{
			const lowir2cy86::Instruction& ins = fn.blocks[b].instructions[i];
			if (ins.kind != lowir2cy86::InstrKind::Call)
				continue;
			for (size_t a = 0; a < ins.args.size(); ++a)
			{
				if (ins.args[a].kind != lowir2cy86::ValueKind::Temp)
					continue;
				lowir2cy86::Type param_type;
				if (a < ins.signature.params.size())
					param_type = ins.signature.params[a].type;
				else if (ins.a.kind == lowir2cy86::ValueKind::Function)
				{
					map<string, size_t>::const_iterator fit =
					    program.function_by_name.find(ins.a.text);
					if (fit != program.function_by_name.end() &&
					    a < program.functions[fit->second].params.size())
						param_type = program.functions[fit->second].params[a].type;
				}
				if (!lowir2cy86::is_obj_type(param_type))
					continue;
				map<string, const lowir2cy86::Instruction*>::const_iterator it =
				    defs.find(ins.args[a].text);
				if (it != defs.end() &&
				    it->second->kind == lowir2cy86::InstrKind::Call &&
				    lowir2cy86::is_obj_type(it->second->type))
					return true;
			}
		}
	return false;
}

bool mir_has_read_only_param_forwarding_frame(const lowir2cy86::Function& fn)
{
	map<string, const lowir2cy86::Instruction*> defs;
	map<string, string> slot_param;
	for (size_t b = 0; b < fn.blocks.size(); ++b)
		for (size_t i = 0; i < fn.blocks[b].instructions.size(); ++i)
		{
			const lowir2cy86::Instruction& ins = fn.blocks[b].instructions[i];
			if (ins.has_dest)
				defs[ins.dest] = &ins;
			if (ins.kind == lowir2cy86::InstrKind::Store &&
			    ins.a.kind == lowir2cy86::ValueKind::Temp &&
			    ins.b.kind == lowir2cy86::ValueKind::Slot &&
			    fn.param_types.find(ins.a.text) != fn.param_types.end())
				slot_param[ins.b.text] = ins.a.text;
		}
	for (size_t b = 0; b < fn.blocks.size(); ++b)
		for (size_t i = 0; i < fn.blocks[b].instructions.size(); ++i)
		{
			const lowir2cy86::Instruction& ins = fn.blocks[b].instructions[i];
			if (ins.kind != lowir2cy86::InstrKind::Index ||
			    ins.a.kind != lowir2cy86::ValueKind::Temp)
				continue;
			map<string, const lowir2cy86::Instruction*>::const_iterator lit =
			    defs.find(ins.a.text);
			if (lit == defs.end() ||
			    lit->second->kind != lowir2cy86::InstrKind::Load ||
			    lit->second->a.kind != lowir2cy86::ValueKind::Temp)
				continue;
			map<string, const lowir2cy86::Instruction*>::const_iterator pit =
			    defs.find(lit->second->a.text);
			if (pit == defs.end() ||
			    pit->second->kind != lowir2cy86::InstrKind::Index ||
			    pit->second->a.kind != lowir2cy86::ValueKind::Temp)
				continue;
			map<string, const lowir2cy86::Instruction*>::const_iterator bit =
			    defs.find(pit->second->a.text);
			if (bit == defs.end() ||
			    bit->second->kind != lowir2cy86::InstrKind::Load ||
			    bit->second->a.kind != lowir2cy86::ValueKind::Slot)
				continue;
			map<string, string>::const_iterator sit =
			    slot_param.find(bit->second->a.text);
			if (sit != slot_param.end())
				return true;
	}
	return false;
}

bool mir_has_direct_param_copyobj_forwarding_frame(
    const lowir2cy86::Function& fn)
{
	map<string, const lowir2cy86::Instruction*> defs;
	map<string, string> slot_param;
	for (size_t b = 0; b < fn.blocks.size(); ++b)
		for (size_t i = 0; i < fn.blocks[b].instructions.size(); ++i)
		{
			const lowir2cy86::Instruction& ins = fn.blocks[b].instructions[i];
			if (ins.has_dest)
				defs[ins.dest] = &ins;
			if (ins.kind == lowir2cy86::InstrKind::Store &&
			    ins.a.kind == lowir2cy86::ValueKind::Temp &&
			    ins.b.kind == lowir2cy86::ValueKind::Slot &&
			    fn.param_types.find(ins.a.text) != fn.param_types.end())
				slot_param[ins.b.text] = ins.a.text;
		}
	for (size_t b = 0; b < fn.blocks.size(); ++b)
		for (size_t i = 0; i < fn.blocks[b].instructions.size(); ++i)
		{
			const lowir2cy86::Instruction& ins = fn.blocks[b].instructions[i];
			if (ins.kind != lowir2cy86::InstrKind::CopyObj ||
			    ins.a.kind != lowir2cy86::ValueKind::Temp ||
			    ins.b.kind != lowir2cy86::ValueKind::Temp)
				continue;
			map<string, const lowir2cy86::Instruction*>::const_iterator src =
			    defs.find(ins.a.text);
			map<string, const lowir2cy86::Instruction*>::const_iterator dst =
			    defs.find(ins.b.text);
			if (src == defs.end() || dst == defs.end() ||
			    src->second->kind != lowir2cy86::InstrKind::Load ||
			    dst->second->kind != lowir2cy86::InstrKind::Load ||
			    src->second->a.kind != lowir2cy86::ValueKind::Slot ||
			    dst->second->a.kind != lowir2cy86::ValueKind::Slot)
				continue;
			if (slot_param.find(src->second->a.text) != slot_param.end() &&
			    slot_param.find(dst->second->a.text) != slot_param.end())
				return true;
		}
	return false;
}

bool mir_has_call_result_branch_after_call(const lowir2cy86::Function& fn)
{
	map<string, const lowir2cy86::Instruction*> defs;
	map<string, int> def_pos;
	vector<int> call_positions;
	int pos = 0;
	for (size_t b = 0; b < fn.blocks.size(); ++b)
		for (size_t i = 0; i < fn.blocks[b].instructions.size(); ++i, ++pos)
		{
			const lowir2cy86::Instruction& ins = fn.blocks[b].instructions[i];
			if (ins.kind == lowir2cy86::InstrKind::Call)
				call_positions.push_back(pos);
			if (ins.has_dest)
			{
				defs[ins.dest] = &ins;
				def_pos[ins.dest] = pos;
			}
		}
	pos = 0;
	for (size_t b = 0; b < fn.blocks.size(); ++b)
		for (size_t i = 0; i < fn.blocks[b].instructions.size(); ++i, ++pos)
		{
			const lowir2cy86::Instruction& branch =
			    fn.blocks[b].instructions[i];
			if (branch.kind != lowir2cy86::InstrKind::Branch ||
			    branch.a.kind != lowir2cy86::ValueKind::Temp)
				continue;
			map<string, const lowir2cy86::Instruction*>::const_iterator cit =
			    defs.find(branch.a.text);
			if (cit == defs.end() ||
			    cit->second->kind != lowir2cy86::InstrKind::Cmp)
				continue;
			const lowir2cy86::Instruction& cmp = *cit->second;
			map<string, int>::const_iterator cp = def_pos.find(cmp.dest);
			if (cp == def_pos.end())
				continue;
			const lowir2cy86::Value values[] = {cmp.a, cmp.b};
			for (size_t v = 0; v < 2; ++v)
			{
				if (values[v].kind != lowir2cy86::ValueKind::Temp)
					continue;
				map<string, const lowir2cy86::Instruction*>::const_iterator vit =
				    defs.find(values[v].text);
				if (vit == defs.end() ||
				    vit->second->kind != lowir2cy86::InstrKind::Call)
					continue;
				for (size_t c = 0; c < call_positions.size(); ++c)
					if (cp->second < call_positions[c] &&
					    call_positions[c] < pos)
						return true;
			}
		}
	return false;
}

bool mir_skip_promoted_slot_instruction(
    const lowir2cy86::Instruction& ins,
    const set<string>& omitted_slots,
    const map<string, string>& promoted_slot_params)
{
	if (ins.kind == lowir2cy86::InstrKind::Store &&
	    ins.b.kind == lowir2cy86::ValueKind::Slot &&
	    omitted_slots.find(ins.b.text) != omitted_slots.end())
		return true;
	if (ins.kind == lowir2cy86::InstrKind::Load &&
	    ins.a.kind == lowir2cy86::ValueKind::Slot &&
	    promoted_slot_params.find(ins.a.text) != promoted_slot_params.end())
		return true;
	return false;
}

lowir2cy86::Type mir_lookup_type(const lowir2cy86::Function& fn,
                                 const lowir2cy86::Value& value)
{
	if (value.kind == lowir2cy86::ValueKind::Temp)
	{
		map<string, lowir2cy86::Type>::const_iterator pit =
		    fn.param_types.find(value.text);
		if (pit != fn.param_types.end())
			return pit->second;
		map<string, lowir2cy86::Type>::const_iterator it =
		    fn.temp_types.find(value.text);
		if (it != fn.temp_types.end())
			return it->second;
	}
	if (value.kind == lowir2cy86::ValueKind::Slot)
	{
		map<string, lowir2cy86::Type>::const_iterator it =
		    fn.slot_types.find(value.text);
		if (it != fn.slot_types.end())
			return it->second;
	}
	return lowir2cy86::Type();
}

void dump_mir_abi(ostream& out, const lowir2cy86::Function& fn)
{
	out << "  abi\n";
	for (size_t i = 0; i < fn.params.size(); ++i)
	{
		out << "    param " << fn.params[i].name << " -> "
		    << mir_abi_param_location(fn, i)
		    << " : " << mir_param_abi_type_text(fn.params[i].type) << "\n";
	}
	out << "    return " << storage_suffix(fn.ret) << " -> "
	    << (lowir2cy86::is_void_type(fn.ret) ? "void" :
	        lowir2cy86::is_f80_type(fn.ret) ? "st0" :
	        mir_is_xmm_type(fn.ret) ? "xmm0" : "rax") << "\n";
}

void dump_mir_frame(ostream& out, const lowir2cy86::Program& program,
                    const lowir2cy86::Function& fn,
                    const vector<string>& preserves,
                    const set<string>& omitted_slots)
{
	const bool float_frame = function_uses_float(program, fn);
	const size_t saved_reg_bytes = preserves.size() * 8;
	out << "  frame\n";
	const size_t scratch = (float_frame || fn.needs_convert_scratch ? 48 : 0);
	const bool f80_frame = function_uses_f80(fn);
	const size_t raw = raw_stack_size(fn, omitted_slots);
	const size_t home_pad =
	    (!float_frame && mir_all_nonfloat_params_homed(fn)) ? 8 : 0;
	const size_t object_result_pad =
	    (!float_frame && !fn.params.empty() && fn.params[0].name == "%ret" &&
	     metadata_value(fn.params[0].metadata, "pass") != "indirect_result" &&
	     saved_reg_bytes != 0 && raw == 0) ? 16 : 0;
	const size_t full_gpr_indirect_pad =
	    mir_has_full_gpr_indirect_call(fn) ? 16 : 0;
	const size_t stack_arg_call_pad =
	    mir_has_stack_arg_call(program, fn) ? 32 : 0;
	const size_t direct_object_arg_temp_pad =
	    mir_has_direct_object_call_arg_temp(program, fn) ? 16 : 0;
	const size_t narrow_global_param_pad =
	    mir_has_narrow_rcx_global_store_param(fn) ? 16 : 0;
	const size_t tls_store_pressure_pad =
	    mir_has_thread_local_store_pressure(program, fn) ? 48 : 0;
	const size_t sret_frame_temp_pad =
	    mir_has_sret_frame_temps(fn)
	        ? (mir_has_stack_arg_call(program, fn)
	               ? (preserves.size() >= 5 ? 128 : 144)
	               : 96)
	        : 0;
	const size_t two_preserve_pad =
	    (!float_frame && preserves.size() == 2 && raw == 0 &&
	     object_result_pad == 0 &&
	     !mir_has_call_result_branch_after_call(fn) &&
	     (mir_has_chained_indirect_call(fn) ||
	      (fn.blocks.size() > 1 && !fn.params.empty()) ||
	      mir_has_read_only_param_forwarding_frame(fn) ||
	      mir_has_direct_param_copyobj_forwarding_frame(fn))) ? 16 : 0;
	out << "    stack_size "
	    << max(max(align_to(raw + home_pad + saved_reg_bytes +
	                        object_result_pad +
	                        full_gpr_indirect_pad +
	                        stack_arg_call_pad +
	                        direct_object_arg_temp_pad +
	                        narrow_global_param_pad +
	                        tls_store_pressure_pad +
	                        sret_frame_temp_pad +
	                        two_preserve_pad +
	                        (float_frame || f80_frame ||
	                         fn.needs_convert_scratch ? scratch : 0), 16),
	               fn.params.empty() ? static_cast<size_t>(0)
	                                 : static_cast<size_t>(16)),
	           float_frame ? static_cast<size_t>(48) : static_cast<size_t>(0))
	    << "\n";
	out << "    scratch_bytes " << scratch << "\n";
	if (!preserves.empty())
	{
		out << "    preserve";
		for (size_t i = 0; i < preserves.size(); ++i)
			out << " " << preserves[i];
		out << "\n";
	}
	for (size_t i = 0; i < fn.params.size(); ++i)
		if (mir_param_needs_slot(fn, i))
			out << "    param-slot " << fn.params[i].name << " -> "
			    << mem_for_offset(mir_param_slot_offset(fn, i)) << " : "
			    << fn.params[i].type.text << "\n";
	for (size_t i = 0; i < fn.slots.size(); ++i)
	{
		if (omitted_slots.find(fn.slots[i].name) != omitted_slots.end())
			continue;
		out << "    slot " << fn.slots[i].name << " -> "
		    << mem_for_offset(mir_slot_offset(fn, fn.slots[i].name,
		                                      omitted_slots)) << " : "
		    << fn.slots[i].type.text << "\n";
	}
	for (size_t i = 0; i < fn.temp_order.size(); ++i)
	{
		map<string, lowir2cy86::Type>::const_iterator it =
		    fn.temp_types.find(fn.temp_order[i]);
		if (it != fn.temp_types.end() && lowir2cy86::is_f80_type(it->second) &&
		    mir_f80_temp_has_storage(fn, fn.temp_order[i]))
			out << "    temp " << fn.temp_order[i] << " -> "
			    << mem_for_offset(mir_f80_offset(fn, fn.temp_order[i]))
			    << " : f80\n";
	}
}

void dump_mir_f80_param_saves(ostream& out, const lowir2cy86::Function& fn)
{
	size_t f80 = 0;
	for (size_t i = 0; i < fn.params.size(); ++i)
		if (lowir2cy86::is_f80_type(fn.params[i].type))
		{
			out << "    fmov.f80 " << mem_for_offset(mir_param_slot_offset(fn, i))
			    << ", [rbp+" << (16 + f80 * 16) << "]\n";
			++f80;
		}
}

bool mir_call_has_f80_arg(const lowir2cy86::Function& fn,
                          const lowir2cy86::Instruction& ins)
{
	for (size_t i = 0; i < ins.args.size(); ++i)
		if (lowir2cy86::is_f80_type(mir_lookup_type(fn, ins.args[i])))
			return true;
	return false;
}

size_t mir_call_f80_arg_bytes(const lowir2cy86::Function& fn,
                              const lowir2cy86::Instruction& ins)
{
	size_t bytes = 0;
	for (size_t i = 0; i < ins.args.size(); ++i)
		if (lowir2cy86::is_f80_type(mir_lookup_type(fn, ins.args[i])))
			bytes += 16;
	return bytes;
}

void dump_mir_f80_call(ostream& out,
                       const lowir2cy86::Function& fn,
                       const lowir2cy86::Instruction& ins,
                       const set<string>& omitted_slots)
{
	const size_t bytes = mir_call_f80_arg_bytes(fn, ins);
	if (bytes != 0)
		out << "    sub rsp, " << bytes << "\n";
	size_t off = 0;
	for (size_t i = 0; i < ins.args.size(); ++i)
		if (lowir2cy86::is_f80_type(mir_lookup_type(fn, ins.args[i])))
		{
			out << "    fmov.f80 [rsp" << (off ? "+" + to_string(off) : "")
			    << "], " << mir_f80_value(fn, ins.args[i], omitted_slots) << "\n";
			off += 16;
		}
	out << "    call " << ins.a.text << "\n";
	if (bytes != 0)
		out << "    add rsp, " << bytes << "\n";
	if (ins.has_dest && lowir2cy86::is_f80_type(ins.type))
	{
		lowir2cy86::Value dst;
		dst.kind = lowir2cy86::ValueKind::Temp;
		dst.text = ins.dest;
		out << "    fstp.f80 " << mir_f80_value(fn, dst, omitted_slots) << "\n";
	}
}

string storage_suffix(const lowir2cy86::Type& type)
{
	return type.text.empty() ? "void" : type.text;
}

string mir_param_abi_type_text(const lowir2cy86::Type& type)
{
	if (lowir2cy86::is_obj_type(type))
	{
		if (type.obj_size <= 4)
			return "i32";
		if (type.obj_size <= 8)
			return "i64";
	}
	return type.text;
}

string reg_for_index(size_t index)
{
	static const char* const regs[] = {
		"r8", "r9", "rbx", "r12", "r13", "r14", "r15", "r10", "r11"
	};
	return regs[index % (sizeof(regs) / sizeof(regs[0]))];
}

string abi_gpr(size_t index)
{
	static const char* const regs[] = {"rdi", "rsi", "rdx", "rcx", "r8", "r9"};
	if (index < sizeof(regs) / sizeof(regs[0]))
		return regs[index];
	return "[rbp+" + to_string(16 + (index - 6) * 8) + "]";
}

bool metadata_is(const lowir2cy86::Metadata& md,
                 const string& key,
                 const string& value)
{
	for (size_t i = 0; i < md.size(); ++i)
	{
		if (md[i].key == key && md[i].value == value)
			return true;
	}
	return false;
}

string value_text(const lowir2cy86::Value& value)
{
	return value.text;
}

string mem_for_offset(size_t offset)
{
	return "[rbp-" + to_string(offset) + "]";
}

bool function_uses_float(const lowir2cy86::Program& program,
                         const lowir2cy86::Function& fn)
{
	for (size_t i = 0; i < fn.blocks.size(); ++i)
	{
		for (size_t j = 0; j < fn.blocks[i].instructions.size(); ++j)
		{
			const lowir2cy86::Instruction& ins = fn.blocks[i].instructions[j];
			if (lowir2cy86::is_float_type(ins.type) ||
			    lowir2cy86::is_float_type(ins.src_type))
				return true;
			for (size_t a = 0; a < ins.signature.params.size(); ++a)
				if (lowir2cy86::is_float_type(ins.signature.params[a].type))
					return true;
			if (ins.kind == lowir2cy86::InstrKind::Call &&
			    ins.a.kind == lowir2cy86::ValueKind::Function)
			{
				map<string, size_t>::const_iterator it =
				    program.function_by_name.find(ins.a.text);
				if (it != program.function_by_name.end())
					for (size_t a = 0; a < program.functions[it->second].params.size(); ++a)
						if (lowir2cy86::is_float_type(
						        program.functions[it->second].params[a].type))
							return true;
			}
		}
	}
	return false;
}

bool function_uses_f80(const lowir2cy86::Function& fn)
{
	if (lowir2cy86::is_f80_type(fn.ret))
		return true;
	for (size_t i = 0; i < fn.params.size(); ++i)
		if (lowir2cy86::is_f80_type(fn.params[i].type))
			return true;
	for (size_t i = 0; i < fn.temp_order.size(); ++i)
		if (lowir2cy86::is_f80_type(fn.temp_types.find(fn.temp_order[i])->second) &&
		    mir_f80_temp_has_storage(fn, fn.temp_order[i]))
			return true;
	return false;
}

size_t mir_slot_size(const lowir2cy86::Type& type)
{
	if (lowir2cy86::is_obj_type(type) && type.size < 4)
		return 4;
	if (!lowir2cy86::is_obj_type(type))
		return lowir2cy86::storage_size(type);
	return lowir2cy86::stack_storage_size(type);
}

size_t mir_slot_offset(const lowir2cy86::Function& fn,
                       const string& name,
                       const set<string>& omitted_slots)
{
	size_t bytes = 0;
	for (size_t i = 0; i < fn.params.size(); ++i)
		if (mir_param_needs_slot(fn, i))
			bytes = max(bytes, mir_param_slot_offset(fn, i));
	for (size_t i = 0; i < fn.slots.size(); ++i)
	{
		if (omitted_slots.find(fn.slots[i].name) != omitted_slots.end())
			continue;
		const size_t align = lowir2cy86::is_obj_type(fn.slots[i].type)
		                         ? fn.slots[i].type.align
		                         : lowir2cy86::storage_size(fn.slots[i].type);
		bytes = align_to(bytes, align);
		bytes += mir_slot_size(fn.slots[i].type);
		if (fn.slots[i].name == name)
			return bytes;
	}
	return bytes;
}

size_t mir_param_slot_offset(const lowir2cy86::Function& fn, size_t index)
{
	size_t bytes = 0;
	for (size_t i = 0; i < fn.params.size(); ++i)
	{
		if (!mir_param_needs_slot(fn, i))
			continue;
		const lowir2cy86::Type& type = fn.params[i].type;
		const size_t align = lowir2cy86::is_obj_type(type)
		                         ? type.align
		                         : lowir2cy86::storage_size(type);
		bytes = align_to(bytes, align);
		bytes += mir_slot_size(type);
		if (i == index)
			return bytes;
	}
	return bytes;
}

size_t raw_stack_size(const lowir2cy86::Function& fn,
                      const set<string>& omitted_slots)
{
	size_t bytes = 0;
	for (size_t i = 0; i < fn.slots.size(); ++i)
		if (omitted_slots.find(fn.slots[i].name) == omitted_slots.end())
			bytes = mir_slot_offset(fn, fn.slots[i].name, omitted_slots);
	for (size_t i = 0; i < fn.params.size(); ++i)
		if (mir_param_needs_slot(fn, i))
			bytes = max(bytes, mir_param_slot_offset(fn, i));
	for (size_t i = 0; i < fn.temp_order.size(); ++i)
		if (lowir2cy86::is_f80_type(fn.temp_types.find(fn.temp_order[i])->second))
			bytes = max(bytes, mir_f80_offset(fn, fn.temp_order[i]));
	return bytes;
}

size_t mir_f80_offset(const lowir2cy86::Function& fn, const string& name)
{
	size_t bytes = 0;
	for (size_t i = 0; i < fn.params.size(); ++i)
		if (mir_param_needs_slot(fn, i))
			bytes = max(bytes, mir_param_slot_offset(fn, i));
	set<string> none;
	for (size_t i = 0; i < fn.slots.size(); ++i)
		bytes = max(bytes, mir_slot_offset(fn, fn.slots[i].name, none));
	for (size_t i = 0; i < fn.temp_order.size(); ++i)
	{
		const string& temp = fn.temp_order[i];
		map<string, lowir2cy86::Type>::const_iterator it = fn.temp_types.find(temp);
		if (it == fn.temp_types.end() || !lowir2cy86::is_f80_type(it->second) ||
		    !mir_f80_temp_has_storage(fn, temp))
			continue;
		bytes += 16;
		if (temp == name)
			return bytes;
	}
	return bytes;
}

bool mir_f80_temp_has_storage(const lowir2cy86::Function& fn, const string& name)
{
	for (size_t i = 0; i < fn.blocks.size(); ++i)
		for (size_t j = 0; j < fn.blocks[i].instructions.size(); ++j)
			if (fn.blocks[i].instructions[j].has_dest &&
			    fn.blocks[i].instructions[j].dest == name)
				return fn.blocks[i].instructions[j].kind != lowir2cy86::InstrKind::Cmp;
	return true;
}

string mir_f80_value(const lowir2cy86::Function& fn,
                     const lowir2cy86::Value& value,
                     const set<string>& omitted_slots)
{
	if (value.kind == lowir2cy86::ValueKind::Temp)
	{
		map<string, lowir2cy86::Type>::const_iterator pit =
		    fn.param_types.find(value.text);
		if (pit != fn.param_types.end() && lowir2cy86::is_f80_type(pit->second))
		{
			for (size_t i = 0; i < fn.params.size(); ++i)
				if (fn.params[i].name == value.text)
					return mem_for_offset(mir_param_slot_offset(fn, i));
		}
		map<string, size_t>::const_iterator it = fn.temp_offsets.find(value.text);
		if (it != fn.temp_offsets.end())
			return mem_for_offset(mir_f80_offset(fn, value.text));
	}
	if (value.kind == lowir2cy86::ValueKind::Slot)
		return mem_for_offset(mir_slot_offset(fn, value.text, omitted_slots));
	return value.text;
}

size_t align_to(size_t value, size_t alignment)
{
	if (alignment == 0)
		return value;
	const size_t rem = value % alignment;
	return rem == 0 ? value : value + alignment - rem;
}


}  // namespace lowir2native
