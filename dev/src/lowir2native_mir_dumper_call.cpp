#include "lowir2native_mir_dumper.h"

namespace lowir2native {

void MirDumper::dump_call(const lowir2cy86::Function& fn,
               const lowir2cy86::Instruction& ins) {
	if (lowir2cy86::is_f80_type(ins.type) || mir_call_has_f80_arg(fn, ins)) {
		dump_mir_f80_call(out_, fn, ins, omitted_slots_);
		return;
	}
	const size_t stack_bytes = mir_call_stack_arg_bytes(program_, fn, ins);
	if (full_gpr_indirect_call(fn, ins) &&
	    full_gpr_first_arg_needs_home(ins))
		dump_full_gpr_first_arg_home(fn, ins);
	const bool preserve_first_indirect_arg =
	    indirect_reference_first_arg_needs_preserve(fn, ins);
	if (preserve_first_indirect_arg)
		out_ << "    mov rbx, " << mir_abi_param_location(fn, 0) << "\n";
	dump_late_indirect_arg_homes(fn, ins);
	if (ins.a.kind != lowir2cy86::ValueKind::Function)
		dump_indirect_callee(fn, ins.a);
	if (stack_bytes != 0)
		dump_stack_call_pre_homes(fn, ins);
	if (stack_bytes != 0)
		out_ << "    sub rsp, " << stack_bytes << "\n";
	for (size_t i = 0; i < ins.args.size(); ++i) {
		const string reg = mir_call_arg_register(program_, fn, ins, i);
		if (!reg.empty() && call_arg_needs_temp_home(fn, ins, i))
			dump_call_arg_temp_home(fn, ins, i); }
	for (size_t i = 0; i < ins.args.size(); ++i) {
		const string reg = mir_call_arg_register(program_, fn, ins, i);
			if (!reg.empty() &&
			    !mir_is_xmm_type(mir_call_param_type(program_, fn, ins, i))) {
				if (preserve_first_indirect_arg && i == 0) {
					out_ << "    mov " << reg << ", rbx\n";
					continue;
				}
				dump_call_arg(fn, ins, i, reg);
			}
		}
		for (size_t i = 0; i < ins.args.size(); ++i) {
		const string reg = mir_call_arg_register(program_, fn, ins, i);
		if (!reg.empty() && mir_is_xmm_type(mir_call_param_type(program_, fn, ins, i)))
			dump_call_arg(fn, ins, i, reg); } for (size_t i = 0; i < ins.args.size(); ++i)
		if (mir_call_arg_register(program_, fn, ins, i).empty())
			dump_stack_call_arg(fn, ins, i);
	if (ins.a.kind == lowir2cy86::ValueKind::Function)
		out_ << "    call " << ins.a.text << debug_suffix(ins) << "\n";
	else
		out_ << "    call *r10" << debug_suffix(ins) << "\n";
	if (stack_bytes != 0)
		out_ << "    add rsp, " << stack_bytes << "\n";
	if (ins.has_dest && full_gpr_indirect_call(fn, ins)) {
		const string mem = frame_temp_mem(fn, ins.dest);
		out_ << "    store." << ins.type.text << " " << mem << ", rax\n";
		out_ << "    load." << ins.type.text << " r8, " << mem << "\n";
		remember_fixed_temp_reg(ins.dest, "r8");
		return;
	}
	if (ins.has_dest &&
	    stack_call_result_arg_temps_.find(ins.dest) !=
	        stack_call_result_arg_temps_.end()) {
		out_ << "    mov r9, rax\n";
		dump_narrow_extend(ins.type, "r9");
		remember_fixed_temp_reg(ins.dest, "r9");
		return;
	}
	if (ins.has_dest &&
	    stack_call_result_temps_.find(ins.dest) !=
	        stack_call_result_temps_.end()) {
		const string mem = frame_temp_mem(fn, ins.dest);
		out_ << "    store." << ins.type.text << " " << mem << ", rax\n";
		out_ << "    load." << ins.type.text << " r8, " << mem << "\n";
		remember_fixed_temp_reg(ins.dest, "r8");
		return;
	}
	if (ins.has_dest && !lowir2cy86::is_void_type(ins.type)) {
		if (lowir2cy86::is_obj_type(ins.type)) {
			if (frame_temps_.find(ins.dest) != frame_temps_.end()) {
				const string mem = frame_temp_mem(fn, ins.dest);
				out_ << "    lea r11, " << mem << "\n";
				out_ << "    store." << direct_object_chunk_type(ins.type)
				     << " [r11], rax\n";
			}
			remember_fixed_temp_reg(ins.dest, "rax");
			} else if (mir_is_xmm_type(ins.type)) {
				const string dst = xmm_reg(ins.dest);
				out_ << "    fmov." << ins.type.text << " "
				     << dst << ", xmm0\n";
				remember_xmm_reg(ins.dest, dst); } else if (single_use_temp(ins.dest)) {
				if (late_indirect_arg_temps_.find(ins.dest) !=
				        late_indirect_arg_temps_.end() &&
				    live_across_calls_.find(ins.dest) ==
				        live_across_calls_.end()) {
					out_ << "    mov r8, rax\n";
					dump_narrow_extend(ins.type, "r8");
					remember_fixed_temp_reg(ins.dest, "r8");
				} else if (live_across_calls_.find(ins.dest) != live_across_calls_.end())
					{
						const string dst = temp_reg(ins.dest);
						out_ << "    mov " << dst << ", rax\n";
						dump_narrow_extend(ins.type, dst);
					}
				else if (call_result_stays_in_rax(ins.dest))
					remember_fixed_temp_reg(ins.dest, "rax");
				else {
					const string dst = call_result_reg(fn, ins);
					out_ << "    mov " << dst << ", rax\n";
					dump_narrow_extend(ins.type, dst);
					remember_fixed_temp_reg(ins.dest, dst);
				}
			} else
				if (live_across_calls_.find(ins.dest) != live_across_calls_.end())
					{
						const string dst = temp_reg(ins.dest);
						out_ << "    mov " << dst << ", rax\n";
						dump_narrow_extend(ins.type, dst);
					}
				else {
					const string dst = call_result_reg(fn, ins);
					out_ << "    mov " << dst << ", rax\n";
					dump_narrow_extend(ins.type, dst);
					remember_fixed_temp_reg(ins.dest, dst);
				}
	} }

bool MirDumper::indirect_reference_first_arg_needs_preserve(
    const lowir2cy86::Function& fn,
    const lowir2cy86::Instruction& ins) const {
	if (ins.kind != lowir2cy86::InstrKind::Call ||
	    ins.a.kind == lowir2cy86::ValueKind::Function ||
	    ins.args.empty() ||
	    !mir_call_arg_needs_address(program_, ins, 0) ||
	    ins.args[0].kind != lowir2cy86::ValueKind::Temp)
		return false;
	map<string, string>::const_iterator pit =
	    promoted_loads_.find(ins.args[0].text);
	return pit != promoted_loads_.end() &&
	       delayed_entry_param_regs_.find(pit->second) !=
	           delayed_entry_param_regs_.end();
}

bool MirDumper::full_gpr_first_arg_needs_home(
    const lowir2cy86::Instruction& ins) const {
	if (!full_gpr_indirect_call_placeholder(ins))
		return false;
	if (ins.args.empty() || ins.args[0].kind != lowir2cy86::ValueKind::Temp)
		return true;
	return live_across_calls_.find(ins.args[0].text) ==
	       live_across_calls_.end();
}

bool MirDumper::full_gpr_indirect_call_placeholder(
    const lowir2cy86::Instruction& ins) const {
	return ins.kind == lowir2cy86::InstrKind::Call &&
	       ins.a.kind != lowir2cy86::ValueKind::Function &&
	       ins.args.size() >= 6;
}

void MirDumper::dump_stack_call_pre_homes(const lowir2cy86::Function& fn,
                               const lowir2cy86::Instruction& ins) {
	prehomed_stack_call_reg_args_.clear();
	stack_call_index_arg_spills_.clear();
	stack_call_result_arg_spills_.clear();
	const bool has_index_arg = call_has_reference_stack_index_arg(ins);
	for (size_t i = 0; i < ins.args.size(); ++i) {
		if (!mir_call_arg_register(program_, fn, ins, i).empty())
			continue;
		const lowir2cy86::Value& arg = ins.args[i];
		if (arg.kind != lowir2cy86::ValueKind::Temp ||
		    stack_call_arg_temps_.find(arg.text) ==
		        stack_call_arg_temps_.end())
			continue;
		if (sret_frame_temps_.find(arg.text) !=
		    sret_frame_temps_.end())
			continue;
		if (stack_call_result_temps_.find(arg.text) !=
		    stack_call_result_temps_.end())
			continue;
		const lowir2cy86::Type type = mir_call_param_type(program_, fn, ins, i);
		out_ << "    store." << type.text << " "
		     << frame_temp_mem(fn, arg.text) << ", "
		     << value_reg(fn, arg) << "\n";
	}
	size_t spill = 0;
	for (size_t i = 0; i < ins.args.size() && spill < 2; ++i) {
		if (has_index_arg && spill >= 1)
			break;
		const string reg = mir_call_arg_register(program_, fn, ins, i);
		if (reg.empty())
			continue;
		const lowir2cy86::Value& arg = ins.args[i];
		if (arg.kind != lowir2cy86::ValueKind::Temp ||
		    mir_is_xmm_type(mir_call_param_type(program_, fn, ins, i)))
			continue;
		const lowir2cy86::Type type = mir_call_param_type(program_, fn, ins, i);
		const lowir2cy86::Instruction* addr = nullptr;
		map<string, const lowir2cy86::Instruction*>::const_iterator ait =
		    definitions_.find(arg.text);
		if (ait != definitions_.end() &&
		    ait->second->kind == lowir2cy86::InstrKind::Addr)
			addr = ait->second;
		if (addr != nullptr)
			continue;
		const string src = value_reg(fn, arg);
		if (src == "rbx" || src == "r12" || src == "r13" ||
		    src == "r14" || src == "r15")
			continue;
		if (addr != nullptr) {
			dump_address_to_reg(fn, addr->a, "r11");
			out_ << "    store.i64 "
			     << call_spill_mem(fn, spill) << ", r11\n";
		} else {
			out_ << "    store.i64 "
			     << call_spill_mem(fn, spill) << ", "
			     << src << "\n";
		}
		prehomed_stack_call_reg_args_.insert(i);
		++spill;
	}
	for (size_t i = 0; i < ins.args.size(); ++i) {
		const lowir2cy86::Value& arg = ins.args[i];
		if (arg.kind != lowir2cy86::ValueKind::Temp ||
		    stack_call_result_arg_temps_.find(arg.text) ==
		        stack_call_result_arg_temps_.end())
			continue;
		out_ << "    store.i64 " << call_spill_mem(fn, spill)
		     << ", " << value_reg(fn, arg) << "\n";
		stack_call_result_arg_spills_[arg.text] = spill;
		++spill;
	}
	for (size_t i = 0; i < ins.args.size(); ++i) {
		const lowir2cy86::Value& arg = ins.args[i];
		if (arg.kind != lowir2cy86::ValueKind::Temp ||
		    stack_call_index_args_.find(arg.text) ==
		        stack_call_index_args_.end())
			continue;
		map<string, const lowir2cy86::Instruction*>::const_iterator dit =
		    definitions_.find(arg.text);
		if (dit == definitions_.end() ||
		    dit->second->kind != lowir2cy86::InstrKind::Index ||
		    dit->second->a.kind != lowir2cy86::ValueKind::Temp)
			continue;
		out_ << "    store.i64 " << call_spill_mem(fn, spill)
		     << ", " << value_reg(fn, dit->second->a) << "\n";
		stack_call_index_arg_spills_[arg.text] = spill;
		++spill;
	}
}

bool MirDumper::call_has_reference_stack_index_arg(
    const lowir2cy86::Instruction& ins) const {
	for (size_t i = 0; i < ins.args.size(); ++i)
		if (ins.args[i].kind == lowir2cy86::ValueKind::Temp &&
		    stack_call_index_args_.find(ins.args[i].text) !=
		        stack_call_index_args_.end())
			return true;
	return false;
}

string MirDumper::call_spill_mem(const lowir2cy86::Function& fn, size_t index) const {
	return mem_for_offset(frame_temps_end_offset(fn) + (index + 1) * 8);
}

size_t MirDumper::frame_temps_end_offset(const lowir2cy86::Function& fn) const {
	size_t bytes = 0;
	for (size_t i = 0; i < fn.params.size(); ++i)
		if (mir_param_needs_slot(fn, i))
			bytes = max(bytes, mir_param_slot_offset(fn, i));
	for (size_t i = 0; i < fn.slots.size(); ++i)
		bytes = max(bytes, mir_slot_offset(fn, fn.slots[i].name, omitted_slots_));
	for (size_t i = 0; i < fn.temp_order.size(); ++i) {
		const string& temp = fn.temp_order[i];
		if (frame_temps_.find(temp) == frame_temps_.end())
			continue;
		const lowir2cy86::Type& type = fn.temp_types.find(temp)->second;
		const size_t align = lowir2cy86::is_obj_type(type)
		                         ? type.align
		                         : lowir2cy86::storage_size(type);
		bytes = align_to(bytes, align);
		bytes += lowir2cy86::is_obj_type(type)
		             ? lowir2cy86::stack_storage_size(type)
		             : lowir2cy86::storage_size(type);
	}
	return bytes;
}

string MirDumper::call_result_reg(const lowir2cy86::Function& fn,
                       const lowir2cy86::Instruction& ins) const {
	if (call_has_xmm_arg(fn, ins)) {
		if (ins.a.kind != lowir2cy86::ValueKind::Function)
			return "r9";
		if (call_has_temp_arg(ins))
			return "rbx";
	}
	if (reg_is_live("r8"))
		return "r9";
	return "r8";
}

bool MirDumper::call_has_xmm_arg(const lowir2cy86::Function& fn,
                      const lowir2cy86::Instruction& ins) const {
	for (size_t i = 0; i < ins.args.size(); ++i)
		if (mir_is_xmm_type(mir_call_param_type(program_, fn, ins, i)))
			return true;
	return false;
}

bool MirDumper::call_has_temp_arg(const lowir2cy86::Instruction& ins) const {
	for (size_t i = 0; i < ins.args.size(); ++i)
		if (ins.args[i].kind == lowir2cy86::ValueKind::Temp)
			return true;
	return false;
}

bool MirDumper::call_arg_needs_temp_home(const lowir2cy86::Function& fn,
                              const lowir2cy86::Instruction& ins,
                              size_t index) const {
	return mir_call_arg_needs_address(program_, ins, index) &&
	       ins.args[index].kind == lowir2cy86::ValueKind::Temp &&
	       !lowir2cy86::is_ptr_type(mir_lookup_type(fn, ins.args[index])); }

bool MirDumper::full_gpr_indirect_call(const lowir2cy86::Function& fn,
                            const lowir2cy86::Instruction& ins) const {
	if (ins.kind != lowir2cy86::InstrKind::Call ||
	    ins.a.kind == lowir2cy86::ValueKind::Function ||
	    ins.args.size() < 6)
		return false;
	for (size_t i = 0; i < 6; ++i)
		if (mir_call_arg_register(program_, fn, ins, i).empty() ||
		    mir_is_xmm_type(mir_call_param_type(program_, fn, ins, i)))
			return false;
	return true; }

bool MirDumper::call_uses_full_gpr_args(const lowir2cy86::Function& fn,
                             const lowir2cy86::Instruction& ins) const {
	size_t gpr_args = 0;
	for (size_t i = 0; i < ins.args.size(); ++i) {
		const string reg = mir_call_arg_register(program_, fn, ins, i);
		if (reg.empty())
			continue;
		const lowir2cy86::Type type =
		    mir_call_param_type(program_, fn, ins, i);
		if (!mir_is_xmm_type(type))
			++gpr_args;
	}
	return gpr_args >= 6;
}

bool MirDumper::function_has_call_or_multiple_blocks(const lowir2cy86::Function& fn) const {
	if (fn.blocks.size() > 1)
		return true;
	for (size_t b = 0; b < fn.blocks.size(); ++b)
		for (size_t i = 0; i < fn.blocks[b].instructions.size(); ++i)
			if (fn.blocks[b].instructions[i].kind ==
			    lowir2cy86::InstrKind::Call)
				return true;
	return false;
}

bool MirDumper::has_indirect_result_param(const lowir2cy86::Function& fn) const {
	return !fn.params.empty() &&
	       fn.params[0].name == "%ret" &&
	       param_pass_is(fn, 0, "indirect_result");
}

bool MirDumper::sret_constructor_like(const lowir2cy86::Function& fn) const {
	if (!has_indirect_result_param(fn) || fn.blocks.empty())
		return false;
	for (size_t i = 0; i < fn.blocks[0].instructions.size(); ++i) {
		const lowir2cy86::Instruction& ins = fn.blocks[0].instructions[i];
		if (ins.kind != lowir2cy86::InstrKind::Call)
			continue;
		return ins.a.kind == lowir2cy86::ValueKind::Function &&
		       ins.args.size() == 1 &&
		       ins.args[0].kind == lowir2cy86::ValueKind::Temp &&
		       ins.args[0].text == "%ret";
	}
	return false;
}

void MirDumper::dump_full_gpr_first_arg_home(const lowir2cy86::Function& fn,
                                  const lowir2cy86::Instruction& ins) {
	const lowir2cy86::Type type = mir_call_param_type(program_, fn, ins, 0);
	out_ << "    store." << type.text << " [rbp-16], "
	     << value_reg(fn, ins.args[0]) << "\n"; }

void MirDumper::dump_call_arg_temp_home(const lowir2cy86::Function& fn,
                             const lowir2cy86::Instruction& ins,
                             size_t index) {
	const lowir2cy86::Value& arg = ins.args[index];
	const lowir2cy86::Type type = mir_lookup_type(fn, arg);
	const string mem = frame_temp_mem(fn, arg.text);
	out_ << "    store." << type.text << " " << mem << ", "
	     << value_reg(fn, arg) << "\n"; }

bool MirDumper::call_result_stays_in_rax(const string& name) const {
	map<string, int>::const_iterator it = use_counts_.find(name);
	return direct_return_values_.find(name) != direct_return_values_.end() ||
       branch_call_results_.find(name) != branch_call_results_.end() ||
       call_arg_results_.find(name) != call_arg_results_.end() ||
       convert_call_results_.find(name) != convert_call_results_.end() ||
       it == use_counts_.end() || it->second == 0; }

void MirDumper::dump_indirect_callee(const lowir2cy86::Function& fn,
                          const lowir2cy86::Value& value) {
	const lowir2cy86::Instruction* addr = inline_addr_definition_for_call(value);
	if (addr != nullptr && addr->a.kind == lowir2cy86::ValueKind::Global) {
		map<string, size_t>::const_iterator it =
		    program_.global_by_name.find(addr->a.text);
		if (it != program_.global_by_name.end()) {
			const lowir2cy86::Global& g = program_.globals[it->second];
			if (g.has_type && lowir2cy86::is_ptr_type(g.type)) {
				out_ << "    load.ptr r10, " << addr->a.text << "\n";
				return;
			}
		}
	}
	const string src = value_reg(fn, value);
	if (src != "r10")
		out_ << "    mov r10, " << src << "\n"; }

const lowir2cy86::Instruction* MirDumper::inline_addr_definition_for_call(
    const lowir2cy86::Value& value) const {
	if (value.kind != lowir2cy86::ValueKind::Temp) return nullptr;
	map<string, const lowir2cy86::Instruction*>::const_iterator it =
	    definitions_.find(value.text);
	if (it == definitions_.end() || it->second->kind != lowir2cy86::InstrKind::Addr) return nullptr; return it->second; }

void MirDumper::dump_call_arg(const lowir2cy86::Function& fn,
                   const lowir2cy86::Instruction& ins, size_t index, const string& reg) {
	const lowir2cy86::Value& arg = ins.args[index];
	const lowir2cy86::Type type = mir_call_param_type(program_, fn, ins, index);
	if (mir_call_stack_arg_bytes(program_, fn, ins) != 0 &&
	    index < 2 && arg.kind == lowir2cy86::ValueKind::Temp &&
	    !mir_is_xmm_type(type) &&
	    prehomed_stack_call_reg_args_.find(index) !=
	        prehomed_stack_call_reg_args_.end()) {
		out_ << "    load.i64 " << reg
		     << ", " << call_spill_mem(fn, index) << "\n";
		return;
	}
	if (arg.kind == lowir2cy86::ValueKind::Temp) {
		map<string, string>::const_iterator pit =
		    promoted_loads_.find(arg.text);
		if (pit != promoted_loads_.end() && reg == "rdi") {
			if (pre_call_param_copies_.find(pit->second) !=
			    pre_call_param_copies_.end()) {
				out_ << "    mov r9, " << mir_abi_param_location(fn, 0) << "\n";
				out_ << "    mov rdi, r8\n";
				return;
			}
			map<string, string>::const_iterator eit =
			    entry_param_regs_.find(pit->second);
			if (eit != entry_param_regs_.end() && eit->second == "rbx") {
				out_ << "    mov r8, " << mir_abi_param_location(fn, 0) << "\n";
				return;
			}
			if (ins.a.kind != lowir2cy86::ValueKind::Function) {
				if (mir_call_arg_needs_address(program_, ins, index) &&
				    delayed_entry_param_regs_.find(pit->second) !=
				        delayed_entry_param_regs_.end()) {
					out_ << "    mov rbx, "
					     << mir_abi_param_location(fn, 0) << "\n";
					out_ << "    mov rdi, rbx\n";
					return;
				}
				out_ << "    mov rdi, r9\n";
				return;
			}
		}
	}
	if (index == 0 && full_gpr_indirect_call(fn, ins) &&
	    full_gpr_first_arg_needs_home(ins)) {
		out_ << "    load." << type.text << " " << reg << ", [rbp-16]\n";
		return;
	}
	if (mir_is_xmm_type(type)) {
		const string src = float_value(fn, arg);
		if (src != reg)
			out_ << "    fmov." << type.text << " " << reg
			     << ", " << src << "\n";
		return;
	}
	if (lowir2cy86::is_obj_type(type) &&
	    arg.kind == lowir2cy86::ValueKind::Temp &&
	    frame_temps_.find(arg.text) != frame_temps_.end()) {
		const string mem = frame_temp_mem(fn, arg.text);
		out_ << "    lea r11, " << mem << "\n";
		out_ << "    load." << direct_object_chunk_type(type)
		     << " " << reg << ", [r11]\n";
		return;
	}
	if (arg.kind == lowir2cy86::ValueKind::Temp &&
	    late_indirect_arg_temps_.find(arg.text) !=
	        late_indirect_arg_temps_.end() &&
	    live_across_calls_.find(arg.text) == live_across_calls_.end()) {
		const string mem = late_indirect_arg_mem(fn, ins, index);
		out_ << "    load." << type.text << " " << reg
		     << ", " << mem << "\n";
		return;
	}
	if (arg.kind == lowir2cy86::ValueKind::Temp &&
	    inline_call_arg_addrs_.find(arg.text) != inline_call_arg_addrs_.end()) {
		const lowir2cy86::Instruction& addr = *definitions_[arg.text];
		const string op =
		    addr.a.kind == lowir2cy86::ValueKind::Global ? "mov" : "lea";
		out_ << "    " << op << " " << reg << ", "
		     << value_reg(fn, addr.a) << debug_suffix(ins) << "\n";
		return;
	}
	if (mir_call_arg_needs_address(program_, ins, index) && arg.kind == lowir2cy86::ValueKind::Slot) {
		out_ << "    lea " << reg << ", "
		     << value_reg(fn, arg) << debug_suffix(ins) << "\n";
		return;
	}
	if (mir_call_arg_needs_address(program_, ins, index) && arg.kind == lowir2cy86::ValueKind::Temp &&
	    !lowir2cy86::is_ptr_type(mir_lookup_type(fn, arg))) {
		const string mem = frame_temp_mem(fn, arg.text);
		out_ << "    lea " << reg << ", " << mem << "\n";
		return;
	}
	string literal;
	if (optimization_level_ >= 1 &&
		    !mir_call_arg_needs_address(program_, ins, index) &&
		    lowir2cy86::is_integer_type(type) &&
		    value_is_const_integer_literal(arg, literal)) {
		out_ << "    mov " << reg << ", " << literal
		     << debug_suffix(ins) << "\n";
		return;
	}
	const bool saved_force_entry_param_reg = force_entry_param_reg_;
	force_entry_param_reg_ = true;
	const string src = value_reg(fn, arg);
	force_entry_param_reg_ = saved_force_entry_param_reg;
	if (src != reg)
		out_ << "    mov " << reg << ", " << src
		     << debug_suffix(ins) << "\n"; }

bool MirDumper::single_use_temp(const string& name) const {
	map<string, int>::const_iterator it = use_counts_.find(name); return it == use_counts_.end() || it->second <= 1; }

bool MirDumper::is_dead_dest(const string& name) const {
	map<string, int>::const_iterator it = use_counts_.find(name); return it == use_counts_.end() || it->second == 0; }

void MirDumper::dump_late_indirect_arg_homes(const lowir2cy86::Function& fn,
                                  const lowir2cy86::Instruction& ins) {
	if (ins.kind != lowir2cy86::InstrKind::Call)
		return;
	for (size_t i = 0; i < ins.args.size(); ++i) {
		const lowir2cy86::Value& arg = ins.args[i];
		if (arg.kind != lowir2cy86::ValueKind::Temp ||
		    late_indirect_arg_temps_.find(arg.text) ==
		        late_indirect_arg_temps_.end() ||
		    live_across_calls_.find(arg.text) != live_across_calls_.end())
			continue;
		const lowir2cy86::Type type =
		    mir_call_param_type(program_, fn, ins, i);
		out_ << "    store." << type.text << " "
		     << late_indirect_arg_mem(fn, ins, i) << ", "
		     << value_reg(fn, arg) << "\n";
	}
}

string MirDumper::late_indirect_arg_mem(const lowir2cy86::Function& fn,
                             const lowir2cy86::Instruction& ins,
                             size_t index) const {
	if (index < ins.args.size() &&
	    ins.args[index].kind == lowir2cy86::ValueKind::Temp &&
	    frame_temps_.find(ins.args[index].text) != frame_temps_.end())
		return frame_temp_mem(fn, ins.args[index].text);
	return call_spill_mem(fn, late_indirect_arg_spill_index(ins, index));
}

size_t MirDumper::late_indirect_arg_spill_index(const lowir2cy86::Instruction& ins,
                                     size_t index) const {
	size_t slot = 0;
	for (size_t i = 0; i < index && i < ins.args.size(); ++i) {
		const lowir2cy86::Value& arg = ins.args[i];
		if (arg.kind == lowir2cy86::ValueKind::Temp &&
		    late_indirect_arg_temps_.find(arg.text) !=
		        late_indirect_arg_temps_.end() &&
		    live_across_calls_.find(arg.text) == live_across_calls_.end())
			++slot;
	}
	return slot;
}

void MirDumper::dump_stack_call_arg(const lowir2cy86::Function& fn,
                         const lowir2cy86::Instruction& ins, size_t index) {
	const lowir2cy86::Value& arg = ins.args[index];
	const lowir2cy86::Type type = mir_call_param_type(program_, fn, ins, index);
	const size_t off = mir_call_stack_arg_offset(program_, fn, ins, index);
	const string dst = off == 0 ? "[rsp]" : "[rsp+" + to_string(off) + "]";
	if (mir_is_xmm_type(type)) {
		out_ << "    fmov." << type.text << " " << dst
		     << ", " << float_value(fn, arg) << "\n";
		return;
	}
	if (arg.kind == lowir2cy86::ValueKind::Temp &&
	    stack_call_index_args_.find(arg.text) !=
	        stack_call_index_args_.end()) {
		dump_stack_index_call_arg(fn, arg, type, dst);
		return;
	}
	if (arg.kind == lowir2cy86::ValueKind::Temp &&
	    stack_call_result_arg_temps_.find(arg.text) !=
	        stack_call_result_arg_temps_.end()) {
		map<string, size_t>::const_iterator sit =
		    stack_call_result_arg_spills_.find(arg.text);
		if (sit != stack_call_result_arg_spills_.end()) {
			out_ << "    load.i64 r11, "
			     << call_spill_mem(fn, sit->second) << "\n";
			out_ << "    store." << type.text << " " << dst
			     << ", r11\n";
			return;
		}
	}
	if (arg.kind == lowir2cy86::ValueKind::Temp &&
	    stack_call_arg_temps_.find(arg.text) !=
	        stack_call_arg_temps_.end()) {
		out_ << "    load." << type.text << " r11, "
		     << frame_temp_mem(fn, arg.text) << "\n";
		out_ << "    store." << type.text << " " << dst
		     << ", r11\n";
		return;
	}
	out_ << "    store." << type.text << " " << dst
	     << ", " << value_reg(fn, arg) << "\n"; }

void MirDumper::dump_stack_index_call_arg(const lowir2cy86::Function& fn,
                               const lowir2cy86::Value& arg,
                               const lowir2cy86::Type& type,
                               const string& dst) {
	map<string, size_t>::const_iterator sit =
	    stack_call_index_arg_spills_.find(arg.text);
	map<string, const lowir2cy86::Instruction*>::const_iterator dit =
	    definitions_.find(arg.text);
	if (sit == stack_call_index_arg_spills_.end() ||
	    dit == definitions_.end() ||
	    dit->second->kind != lowir2cy86::InstrKind::Index) {
		out_ << "    store." << type.text << " " << dst
		     << ", " << value_reg(fn, arg) << "\n";
		return;
	}
	out_ << "    load.i64 r11, " << call_spill_mem(fn, sit->second)
	     << "\n";
	const size_t scale = lowir2cy86::storage_size(dit->second->type);
	if (dit->second->b.kind == lowir2cy86::ValueKind::Literal) {
		const long offset =
		    stol(dit->second->b.text) * static_cast<long>(scale);
		if (offset != 0)
			out_ << "    lea r11, [r11+" << offset << "]\n";
	} else {
		out_ << "    lea r11, [r11+"
		     << value_reg(fn, dit->second->b)
		     << (scale == 1 ? "" : "*" + to_string(scale)) << "]\n";
	}
	out_ << "    store." << type.text << " " << dst << ", r11\n";
}

}  // namespace lowir2native
