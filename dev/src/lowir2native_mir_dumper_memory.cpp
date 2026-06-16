#include "lowir2native_mir_dumper.h"

namespace lowir2native {

void MirDumper::dump_const(const lowir2cy86::Function& fn,
                const lowir2cy86::Instruction& ins) {
	if (optimization_level_ >= 1 &&
	    rematerialized_binary_immediates_.find(ins.dest) !=
	        rematerialized_binary_immediates_.end())
		return;
	if (lowir2cy86::is_f80_type(ins.type)) {
		lowir2cy86::Value dst;
		dst.kind = lowir2cy86::ValueKind::Temp;
		dst.text = ins.dest;
		out_ << "    fmov.f80 " << mir_f80_value(fn, dst, omitted_slots_)
		     << ", " << ins.a.text << debug_suffix(ins) << "\n";
		return;
	}
	if (lowir2cy86::is_float_type(ins.type) && !lowir2cy86::is_f80_type(ins.type)) {
		out_ << "    fmov." << ins.type.text << " " << xmm_reg(ins.dest)
		     << ", " << ins.a.text << debug_suffix(ins) << "\n";
		return;
	}
	const string dst = const_dest_reg(ins);
	out_ << "    mov " << dst << ", " << ins.a.text
	     << debug_suffix(ins) << "\n";
	dump_narrow_extend(ins.type, dst, ins.debug);
	remember_const_dest(ins.dest, dst); }

string MirDumper::const_dest_reg(const lowir2cy86::Instruction& ins) {
	if (optimization_level_ >= 1 &&
	    direct_branch_value_operands_.find(ins.dest) !=
	        direct_branch_value_operands_.end() &&
	    lowir2cy86::is_integer_type(ins.type))
		return "rax";
	if (!preferred_literal_reg_.empty() && lowir2cy86::is_integer_type(ins.type)) {
		const string reg = preferred_literal_reg_;
		preferred_literal_reg_.clear();
		fixed_const_dest_ = true;
		return reg;
	}
	if (prefer_r8_literal_ && lowir2cy86::is_integer_type(ins.type)) {
		prefer_r8_literal_ = false;
		return "r8";
	}
	if (stack_call_arg_temps_.find(ins.dest) !=
	    stack_call_arg_temps_.end())
		return "rax";
	return temp_reg(ins.dest); }

void MirDumper::remember_const_dest(const string& name, const string& reg) {
	if (fixed_const_dest_) {
		fixed_temp_regs_[name] = reg;
		note_temp_reg(reg);
		fixed_const_dest_ = false;
		return;
	}
	remember_temp_reg(name, reg); }

	void MirDumper::dump_addr(const lowir2cy86::Function& fn,
	               const lowir2cy86::Instruction& ins,
	               const string& debug) {
		const string op =
		    ins.a.kind == lowir2cy86::ValueKind::Global ? "mov" : "lea";
		map<string, string>::const_iterator bit =
		    direct_branch_addr_regs_.find(ins.dest);
		map<string, string>::const_iterator cit =
		    call_arg_addr_regs_.find(ins.dest);
		const string fixed = fixed_addr_dest_reg(ins);
		const string dst = bit != direct_branch_addr_regs_.end() ? bit->second :
		    cit != call_arg_addr_regs_.end() ? cit->second :
		    indirect_callee_base_loads_.find(ins.dest) !=
		        indirect_callee_base_loads_.end() ? "r9" :
		    !fixed.empty() ? fixed :
		    addr_prefers_rcx(ins) ? "rcx" :
		        global_store_addrs_.find(ins.dest) != global_store_addrs_.end()
		            ? "rbx" : temp_reg(ins.dest);
	out_ << "    " << op << " " << dst << ", "
	     << value_reg(fn, ins.a) << debug_suffix(debug) << "\n";
	if (bit != direct_branch_addr_regs_.end())
		remember_fixed_temp_reg(ins.dest, bit->second);
	else if (cit != call_arg_addr_regs_.end())
		remember_temp_reg(ins.dest, cit->second);
		else if (indirect_callee_base_loads_.find(ins.dest) !=
		         indirect_callee_base_loads_.end())
			remember_fixed_temp_reg(ins.dest, "r9");
		else if (!fixed.empty())
			remember_fixed_temp_reg(ins.dest, fixed);
		else if (addr_prefers_rcx(ins))
			remember_fixed_temp_reg(ins.dest, "rcx");
		else if (global_store_addrs_.find(ins.dest) != global_store_addrs_.end())
			remember_fixed_temp_reg(ins.dest, "rbx"); }

	string MirDumper::fixed_addr_dest_reg(const lowir2cy86::Instruction& ins) const {
		if (store_source_addrs_.find(ins.dest) != store_source_addrs_.end())
			return "rax";
		if (large_slot_frame_ &&
		    ins.a.kind == lowir2cy86::ValueKind::Slot &&
		    single_use_temp(ins.dest))
			return reg_is_live("r8") ? "r9" : "r8";
		return "";
	}

void MirDumper::dump_copy(const lowir2cy86::Function& fn,
               const lowir2cy86::Instruction& ins) {
		if (lowir2cy86::is_float_type(ins.type) && !lowir2cy86::is_f80_type(ins.type)) {
			if (optimization_level_ >= 1 && copy_can_forward(fn, ins)) {
				remember_xmm_reg(ins.dest, float_value(fn, ins.a));
				return;
			}
			out_ << "    fmov." << ins.type.text << " " << xmm_reg(ins.dest)
			     << ", " << float_value(fn, ins.a) << "\n";
			return;
		}
		if (large_frame_pointer_literal_copy(ins)) {
			out_ << "    mov r8, " << value_reg(fn, ins.a) << "\n";
			remember_fixed_temp_reg(ins.dest, "r8");
			return;
		}
		if (copy_alias_call_args_.find(ins.dest) !=
		    copy_alias_call_args_.end()) {
			out_ << "    mov r8, " << value_reg(fn, ins.a) << "\n";
			remember_fixed_temp_reg(ins.dest, "r8");
			return;
	}
	if (copy_can_forward(fn, ins)) {
		remember_fixed_temp_reg(ins.dest, value_reg(fn, ins.a));
		return;
	}
	if (copy_can_narrow_in_place(fn, ins)) {
		const string reg = value_reg(fn, ins.a);
		dump_narrow_extend(ins.type, reg);
		remember_fixed_temp_reg(ins.dest, reg);
		return;
	}
		out_ << "    mov " << temp_reg(ins.dest) << ", "
		     << value_reg(fn, ins.a) << "\n"; }

	bool MirDumper::large_frame_pointer_literal_copy(
	    const lowir2cy86::Instruction& ins) const {
		return large_slot_frame_ &&
		       ins.kind == lowir2cy86::InstrKind::Copy &&
		       lowir2cy86::is_ptr_type(ins.type) &&
		       ins.a.kind == lowir2cy86::ValueKind::Literal;
	}

bool MirDumper::copy_can_forward(const lowir2cy86::Function& fn,
                      const lowir2cy86::Instruction& ins) const {
	if (copy_is_integer_narrow(fn, ins)) return false;
	if (ins.a.kind == lowir2cy86::ValueKind::Temp &&
	    param_index(fn, ins.a.text) >= 0 &&
	    live_across_calls_.find(ins.dest) == live_across_calls_.end())
		return true;
	if (ins.a.kind == lowir2cy86::ValueKind::Temp && is_last_use(ins.a))
		return true;
	return direct_return_values_.find(ins.dest) != direct_return_values_.end() ||
	       (ins.a.kind == lowir2cy86::ValueKind::Temp &&
	        single_use_temp(ins.dest) && is_last_use(ins.a)); }

bool MirDumper::copy_is_integer_narrow(const lowir2cy86::Function& fn,
                            const lowir2cy86::Instruction& ins) const {
	const lowir2cy86::Type src = mir_lookup_type(fn, ins.a);
	return lowir2cy86::is_integer_type(src) &&
	       lowir2cy86::is_integer_type(ins.type) &&
	       src.bits > ins.type.bits; }

bool MirDumper::copy_can_narrow_in_place(const lowir2cy86::Function& fn,
                              const lowir2cy86::Instruction& ins) const {
	return copy_is_integer_narrow(fn, ins) &&
	       ins.a.kind == lowir2cy86::ValueKind::Temp && is_last_use(ins.a); }

bool MirDumper::addr_prefers_rcx(const lowir2cy86::Instruction& ins) const {
	if (direct_branch_addr_regs_.find(ins.dest) !=
	    direct_branch_addr_regs_.end())
		return false;
	if (large_slot_frame_)
		return false;
	return ins.a.kind == lowir2cy86::ValueKind::Slot &&
	       single_use_temp(ins.dest); }

bool MirDumper::optimized_addr_temp_feeds_load(const string& name) const {
	return optimization_level_ >= 1 &&
	       optimized_addr_load_temps_.find(name) !=
	           optimized_addr_load_temps_.end();
}

const lowir2cy86::Instruction* MirDumper::optimized_addr_definition(
    const lowir2cy86::Value& value) const {
	if (optimization_level_ < 1 || value.kind != lowir2cy86::ValueKind::Temp)
		return nullptr;
	map<string, const lowir2cy86::Instruction*>::const_iterator it =
	    definitions_.find(value.text);
	if (it == definitions_.end() ||
	    it->second->kind != lowir2cy86::InstrKind::Addr ||
	    (it->second->a.kind != lowir2cy86::ValueKind::Slot &&
	     it->second->a.kind != lowir2cy86::ValueKind::Global))
		return nullptr;
	return it->second;
}

const lowir2cy86::Instruction* MirDumper::optimized_literal_store_for_addr(
    const string& name) const {
	if (optimization_level_ < 1)
		return nullptr;
	map<string, const lowir2cy86::Instruction*>::const_iterator it =
	    optimized_literal_stores_by_addr_.find(name);
	return it == optimized_literal_stores_by_addr_.end() ? nullptr : it->second;
}

bool MirDumper::has_large_slot_frame(const lowir2cy86::Function& fn) const {
	size_t bytes = 0;
	for (size_t i = 0; i < fn.slots.size(); ++i) {
		const lowir2cy86::Type& type = fn.slots[i].type;
		bytes += lowir2cy86::is_obj_type(type)
		             ? lowir2cy86::stack_storage_size(type)
		             : lowir2cy86::storage_size(type);
	}
	return bytes >= 128;
}

void MirDumper::dump_copyobj(const lowir2cy86::Function& fn,
                  const lowir2cy86::Instruction& ins) {
	if (copyobj_uses_direct_param_loads(ins)) {
		out_ << "    copy_bytes " << ins.span.bytes << "x"
		     << ins.span.align << ", rdi, rsi\n";
		return;
	}
	if (copyobj_source_is_direct_object(fn, ins)) {
		dump_direct_object_copy(fn, ins);
		return;
	}
	string src = value_reg(fn, ins.a);
	if (src == "rdi") {
		out_ << "    mov r8, rdi\n";
		src = "r8";
	}
	dump_copy_addr_or_move(fn, ins.b, "rdi");
	if (inline_copy_addrs_.find(ins.a.text) != inline_copy_addrs_.end())
		dump_copy_addr_or_move(fn, ins.a, "rsi");
	else
		out_ << "    mov rsi, " << src << "\n";
	out_ << "    copy_bytes " << ins.span.bytes << "x" << ins.span.align
	     << ", rdi, rsi\n";
	remember_copied_object_load(fn, ins); }

bool MirDumper::copyobj_uses_direct_param_loads(
    const lowir2cy86::Instruction& ins) const {
	return ins.a.kind == lowir2cy86::ValueKind::Temp &&
	       ins.b.kind == lowir2cy86::ValueKind::Temp &&
	       direct_param_copy_loads_.find(ins.a.text) !=
	           direct_param_copy_loads_.end() &&
	       direct_param_copy_loads_.find(ins.b.text) !=
	           direct_param_copy_loads_.end();
}

bool MirDumper::copyobj_source_is_direct_object(const lowir2cy86::Function& fn,
                                     const lowir2cy86::Instruction& ins) const {
	const lowir2cy86::Type src = mir_lookup_type(fn, ins.a);
	return lowir2cy86::is_obj_type(src) &&
	       src.obj_size == ins.span.bytes &&
	       src.obj_align == ins.span.align &&
	       !direct_object_chunk_type(src).empty(); }

void MirDumper::dump_direct_object_copy(const lowir2cy86::Function& fn,
                             const lowir2cy86::Instruction& ins) {
	const string type = direct_object_chunk_type(mir_lookup_type(fn, ins.a));
	dump_address_value_to_reg(fn, ins.b, "r11");
	string src = value_reg(fn, ins.a);
	if (is_memory_operand(src)) {
		out_ << "    load." << type << " rax, " << src << "\n";
		src = "rax";
	}
	out_ << "    store." << type << " [r11], " << src << "\n"; }

void MirDumper::simulate_direct_object_copy(const lowir2cy86::Function& fn,
                                 const lowir2cy86::Instruction& ins) {
	if (ins.b.kind == lowir2cy86::ValueKind::Temp) {
		map<string, const lowir2cy86::Instruction*>::const_iterator it =
		    definitions_.find(ins.b.text);
		if (it != definitions_.end() &&
		    it->second->kind == lowir2cy86::InstrKind::Addr)
			value_reg(fn, it->second->a);
		else
			value_reg(fn, ins.b);
	} else {
		value_reg(fn, ins.b);
	}
	value_reg(fn, ins.a); }

string MirDumper::direct_object_chunk_type(const lowir2cy86::Type& type) const {
	if (!lowir2cy86::is_obj_type(type))
		return "";
	if (type.obj_size <= 4)
		return "i32";
	if (type.obj_size <= 8)
		return "i64";
	return ""; }

bool MirDumper::is_memory_operand(const string& text) const {
	return text.size() >= 2 && text[0] == '[' &&
	       text[text.size() - 1] == ']'; }

const lowir2cy86::Instruction* MirDumper::inline_addr_definition_for_direct_object(
    const lowir2cy86::Value& value) const {
	if (value.kind != lowir2cy86::ValueKind::Temp)
		return nullptr;
	map<string, const lowir2cy86::Instruction*>::const_iterator it =
	    definitions_.find(value.text);
	if (it == definitions_.end() ||
	    it->second->kind != lowir2cy86::InstrKind::Addr)
		return nullptr;
	return it->second; }

void MirDumper::dump_copy_addr_or_move(const lowir2cy86::Function& fn,
                            const lowir2cy86::Value& value,
                            const string& reg) {
	if (value.kind == lowir2cy86::ValueKind::Temp &&
	    inline_copy_addrs_.find(value.text) != inline_copy_addrs_.end()) {
		const lowir2cy86::Instruction& addr = *definitions_[value.text];
		const string op =
		    addr.a.kind == lowir2cy86::ValueKind::Global ? "mov" : "lea";
		out_ << "    " << op << " " << reg << ", "
		     << value_reg(fn, addr.a) << "\n";
		return;
	}
	out_ << "    mov " << reg << ", " << value_reg(fn, value) << "\n"; }

void MirDumper::dump_zeroinit(const lowir2cy86::Function& fn,
                   const lowir2cy86::Instruction& ins) {
	const lowir2cy86::Instruction* addr =
	    inline_zero_addr_definition(ins.a);
	if (addr != nullptr)
		dump_address_to_reg(fn, addr->a, "rdi");
	else
		out_ << "    mov rdi, " << value_reg(fn, ins.a) << "\n";
	out_ << "    zero_bytes " << ins.span.bytes << "x" << ins.span.align
	     << ", rdi\n"; }

void MirDumper::remember_copied_object_load(const lowir2cy86::Function& fn,
                                 const lowir2cy86::Instruction& ins) {
	if (!can_reuse_written_value(ins.a)) return;
	const string target = direct_addr_target(fn, ins.b);
	if (!target.empty())
		remember_reload(target, value_reg(fn, ins.a), false); }

string MirDumper::direct_addr_target(const lowir2cy86::Function& fn,
                          const lowir2cy86::Value& value) {
	if (value.kind == lowir2cy86::ValueKind::Temp) {
		map<string, const lowir2cy86::Instruction*>::const_iterator it =
		    definitions_.find(value.text);
		if (it != definitions_.end() &&
		    it->second->kind == lowir2cy86::InstrKind::Addr)
			return value_reg(fn, it->second->a);
	} return value_reg(fn, value); }

void MirDumper::dump_address_to_reg(const lowir2cy86::Function& fn,
                         const lowir2cy86::Value& value,
                         const string& reg) {
	const string op =
	    value.kind == lowir2cy86::ValueKind::Global ? "mov" : "lea";
	out_ << "    " << op << " " << reg << ", "
	     << value_reg(fn, value) << "\n"; }

void MirDumper::dump_address_value_to_reg(const lowir2cy86::Function& fn,
                               const lowir2cy86::Value& value,
                               const string& reg) {
	if (value.kind == lowir2cy86::ValueKind::Temp) {
		map<string, const lowir2cy86::Instruction*>::const_iterator it =
		    definitions_.find(value.text);
		if (it != definitions_.end() &&
		    it->second->kind == lowir2cy86::InstrKind::Addr) {
			dump_address_to_reg(fn, it->second->a, reg);
			return;
		}
	}
	if (value.kind == lowir2cy86::ValueKind::Slot ||
	    value.kind == lowir2cy86::ValueKind::Global) {
		dump_address_to_reg(fn, value, reg);
		return;
	}
	out_ << "    mov " << reg << ", " << value_reg(fn, value) << "\n"; }

void MirDumper::dump_index(const lowir2cy86::Function& fn,
                const lowir2cy86::Instruction& ins) {
	if (sret_frame_temps_.find(ins.dest) != sret_frame_temps_.end()) {
		dump_sret_frame_index(fn, ins);
		return;
	}
	const bool saved_force_entry_param_reg = force_entry_param_reg_;
	if (call_arg_index_regs_.find(ins.dest) != call_arg_index_regs_.end())
		force_entry_param_reg_ = true;
	const size_t scale = lowir2cy86::storage_size(ins.type);
	if (ins.a.kind == lowir2cy86::ValueKind::Temp &&
	    param_base_loads_.find(ins.a.text) != param_base_loads_.end() &&
	    ins.b.kind != lowir2cy86::ValueKind::Literal) {
		const string base = value_reg(fn, ins.a);
		const string idx = value_reg(fn, ins.b);
		out_ << "    mov rdx, " << idx << "\n";
		if (scale != 1)
			out_ << "    imul rdx, " << scale << "\n";
		out_ << "    add " << base << ", rdx\n";
		remember_fixed_temp_reg(ins.dest, base);
		force_entry_param_reg_ = saved_force_entry_param_reg;
		return;
	}
	string dst = index_dest_reg(fn, ins);
	if (!fn.params.empty() && fn.params[0].name == "%ret" &&
	    current_block_index_ == 0 &&
	    ins.a.kind == lowir2cy86::ValueKind::Temp) {
		const string base_probe = value_reg(fn, ins.a);
		if (dst == base_probe &&
		    (base_probe == "rbx" || base_probe == "r12" ||
		     base_probe == "r13" || base_probe == "r14" ||
		     base_probe == "r15"))
			dst = base_probe == "r15" ? "r14" : "r15";
	}
	const lowir2cy86::Instruction* base_addr =
	    inline_zero_addr_definition(ins.a);
	string base;
	if (base_addr != nullptr) {
		dump_address_to_reg(fn, base_addr->a, dst);
		base = dst;
	} else {
		base = value_reg(fn, ins.a);
		if (dst != base)
			out_ << "    mov " << dst << ", " << base << "\n";
	}
	if (ins.b.kind == lowir2cy86::ValueKind::Literal) {
		const long offset = stol(ins.b.text) * static_cast<long>(scale);
		if (offset != 0)
			out_ << "    lea " << dst << ", [" << dst << "+"
			     << offset << "]\n"; } else
		out_ << "    lea " << dst << ", [" << dst << "+"
		     << value_reg(fn, ins.b)
		     << (scale == 1 ? "" : "*" + to_string(scale)) << "]\n";
	if (temp_used_only_as_store_dest(fn, ins.dest))
		remember_fixed_temp_reg(ins.dest, dst);
	else if (dst == base)
		remember_fixed_temp_reg(ins.dest, dst);
	else
		remember_temp_reg(ins.dest, dst);
	force_entry_param_reg_ = saved_force_entry_param_reg; }

void MirDumper::dump_sret_frame_index(const lowir2cy86::Function& fn,
                           const lowir2cy86::Instruction& ins) {
	const size_t scale = lowir2cy86::storage_size(ins.type);
	string base;
	bool base_from_frame = false;
	if (ins.a.kind == lowir2cy86::ValueKind::Temp &&
	    sret_frame_temps_.find(ins.a.text) != sret_frame_temps_.end()) {
		out_ << "    load.ptr rax, " << frame_temp_mem(fn, ins.a.text)
		     << "\n";
		base = "rax";
		base_from_frame = true;
	} else {
		base = value_reg(fn, ins.a);
	}
	if (ins.b.kind == lowir2cy86::ValueKind::Literal) {
		const long offset = stol(ins.b.text) * static_cast<long>(scale);
		if (offset == 0 && !base_from_frame) {
			out_ << "    store.ptr " << frame_temp_mem(fn, ins.dest)
			     << ", " << base << "\n";
			return;
		}
		if (base != "rax")
			out_ << "    mov rax, " << base << "\n";
		if (offset != 0)
			out_ << "    lea rax, [rax+" << offset << "]\n";
	} else {
		if (base != "rax")
			out_ << "    mov rax, " << base << "\n";
		out_ << "    lea rax, [rax+" << value_reg(fn, ins.b)
		     << (scale == 1 ? "" : "*" + to_string(scale)) << "]\n";
	}
	out_ << "    store.ptr " << frame_temp_mem(fn, ins.dest)
	     << ", rax\n";
}

const lowir2cy86::Instruction* MirDumper::inline_zero_addr_definition(
    const lowir2cy86::Value& value) const {
	if (value.kind != lowir2cy86::ValueKind::Temp ||
	    inline_zero_addrs_.find(value.text) == inline_zero_addrs_.end())
		return nullptr;
	map<string, const lowir2cy86::Instruction*>::const_iterator it =
	    definitions_.find(value.text);
	if (it == definitions_.end() ||
	    it->second->kind != lowir2cy86::InstrKind::Addr)
		return nullptr;
	return it->second; }

string MirDumper::index_dest_reg(const lowir2cy86::Function& fn,
                      const lowir2cy86::Instruction& ins) {
	if (index_literal_offset(ins) == 0 && ins.op == "field") {
		if (index_is_single_param_store_dest(fn, ins))
			return "r9";
		return value_reg(fn, ins.a);
	}
	if (ins.a.kind == lowir2cy86::ValueKind::Temp &&
	    entry_branch_param_loads_.find(ins.a.text) !=
	        entry_branch_param_loads_.end())
		return "r12";
	if (has_indirect_result_param(fn) &&
	    current_block_index_ != 0 &&
	    !past_stack_call_in_block_ &&
	    index_feeds_stack_call_arg_load(fn, ins.dest) &&
	    ins.a.kind == lowir2cy86::ValueKind::Temp &&
	    temp_origin_is_reference_param(fn, ins.a.text))
		return "r9";
	map<string, string>::const_iterator cit =
	    call_arg_index_regs_.find(ins.dest);
	if (cit != call_arg_index_regs_.end())
		return cit->second;
		if (ins.a.kind == lowir2cy86::ValueKind::Temp) {
			map<string, string>::const_iterator it =
			    entry_param_regs_.find(ins.a.text);
			if (it != entry_param_regs_.end() && it->second == "rbx")
				return "r12";
		}
		if (sret_constructor_like(fn) && current_block_index_ != 0 &&
		    ins.a.kind == lowir2cy86::ValueKind::Temp &&
		    temp_used_only_as_store_dest(fn, ins.dest)) {
			map<string, string>::const_iterator pit =
			    promoted_loads_.find(ins.a.text);
			const string base =
			    pit != promoted_loads_.end() ? pit->second : ins.a.text;
			if (base == "%ret")
				return "r9";
		}
		if (current_block_index_ != 0 &&
		    temp_used_only_as_store_dest(fn, ins.dest) &&
		    temp_origin_is_reference_param(fn, ins.dest)) {
			const lowir2cy86::Instruction* store =
			    unique_store_to_temp(fn, ins.dest);
			if (store != nullptr && store->a.kind == lowir2cy86::ValueKind::Literal)
				return "r8";
			if (store != nullptr && store_source_is_load(store->a))
				return "r9";
		}
		if (sret_constructor_like(fn) && current_block_index_ == 0 &&
		    ins.a.kind == lowir2cy86::ValueKind::Temp) {
			map<string, string>::const_iterator pit =
			    promoted_loads_.find(ins.a.text);
		const string base =
		    pit != promoted_loads_.end() ? pit->second :
		    !temp_origin_param(fn, ins.a.text).empty()
		        ? temp_origin_param(fn, ins.a.text)
		        : ins.a.text;
		const int index = param_index(fn, base);
		if ((base == "%ret") ||
		    (index >= 0 && param_pass_is(fn, index, "reference")))
			return "r15";
	}
	if (ins.a.kind == lowir2cy86::ValueKind::Temp &&
	    param_index(fn, ins.a.text) >= 0)
		return temp_reg(ins.dest);
	if (ins.a.kind == lowir2cy86::ValueKind::Temp &&
	    !function_has_call_or_multiple_blocks(fn)) {
		const string param = param_for_projected_load_base(fn, ins.a.text);
		const int index = param.empty() ? -1 : param_index(fn, param);
		if (index >= 0 && param_pass_is(fn, index, "reference"))
			return value_reg(fn, ins.a);
	}
	if (!fn.params.empty() && fn.params[0].name == "%ret" &&
	    param_pass_is(fn, 0, "indirect_result") &&
	    current_block_index_ == 0 &&
	    ins.a.kind == lowir2cy86::ValueKind::Temp) {
		const string origin = temp_origin_param(fn, ins.a.text);
		const int index = origin.empty() ? -1 : param_index(fn, origin);
		if (index >= 0 && param_pass_is(fn, index, "reference"))
			return "r15";
	}
	if (ins.a.kind == lowir2cy86::ValueKind::Temp &&
	    promoted_loads_.find(ins.a.text) != promoted_loads_.end() &&
	    temp_used_only_as_store_dest(fn, ins.dest)) {
		const string& param = promoted_loads_.find(ins.a.text)->second;
		return entry_param_regs_.find(param) == entry_param_regs_.end()
		           ? "r9"
		           : "r8";
	}
	if (ins.a.kind == lowir2cy86::ValueKind::Temp &&
	    promoted_loads_.find(ins.a.text) != promoted_loads_.end())
		return temp_reg(ins.dest);
	if (ins.a.kind == lowir2cy86::ValueKind::Temp &&
	    direct_branch_value_operands_.find(ins.a.text) !=
	        direct_branch_value_operands_.end())
		return temp_reg(ins.dest);
	if (!fn.params.empty() && fn.params[0].name == "%ret" &&
	    param_pass_is(fn, 0, "indirect_result") &&
	    current_block_index_ == 0 &&
	    ins.a.kind == lowir2cy86::ValueKind::Temp) {
		const string base = value_reg(fn, ins.a);
		if (base == "rbx" || base == "r12" || base == "r13" ||
		    base == "r14" || base == "r15")
			return base == "r15" ? "r14" : "r15";
	}
	if (is_last_use(ins.a)) return value_reg(fn, ins.a); return temp_reg(ins.dest); }

bool MirDumper::index_is_single_param_store_dest(const lowir2cy86::Function& fn,
                                      const lowir2cy86::Instruction& ins) const {
	if (fn.params.size() != 1 ||
	    !temp_used_only_as_store_dest(fn, ins.dest) ||
	    ins.a.kind != lowir2cy86::ValueKind::Temp)
		return false;
	const string param = temp_origin_param(fn, ins.a.text);
	if (param.empty() || param_index(fn, param) != 0)
		return false;
	map<string, lowir2cy86::Type>::const_iterator tit =
	    fn.param_types.find(param);
	return tit != fn.param_types.end() && lowir2cy86::is_ptr_type(tit->second);
}

const lowir2cy86::Instruction* MirDumper::unique_store_to_temp(
    const lowir2cy86::Function& fn, const string& name) const {
	const lowir2cy86::Instruction* result = nullptr;
	for (size_t b = 0; b < fn.blocks.size(); ++b)
		for (size_t i = 0; i < fn.blocks[b].instructions.size(); ++i) {
			const lowir2cy86::Instruction& ins = fn.blocks[b].instructions[i];
			if (ins.kind != lowir2cy86::InstrKind::Store ||
			    !temp_value_named(ins.b, name))
				continue;
			if (result != nullptr)
				return nullptr;
			result = &ins;
		}
	return result;
}

bool MirDumper::store_source_is_load(const lowir2cy86::Value& value) const {
	if (value.kind != lowir2cy86::ValueKind::Temp)
		return false;
	map<string, const lowir2cy86::Instruction*>::const_iterator it =
	    definitions_.find(value.text);
	return it != definitions_.end() &&
	       it->second->kind == lowir2cy86::InstrKind::Load;
}

bool MirDumper::index_feeds_stack_call_arg_load(const lowir2cy86::Function& fn,
                                     const string& name) const {
	for (size_t b = 0; b < fn.blocks.size(); ++b)
		for (size_t i = 0; i < fn.blocks[b].instructions.size(); ++i) {
			const lowir2cy86::Instruction& ins = fn.blocks[b].instructions[i];
			if (ins.kind == lowir2cy86::InstrKind::Load &&
			    temp_value_named(ins.a, name) &&
			    stack_call_arg_temps_.find(ins.dest) !=
			        stack_call_arg_temps_.end())
				return true;
	}
	return false;
}

bool MirDumper::load_result_feeds_pre_stack_call_index(
    const lowir2cy86::Function& fn, const string& name) const {
	for (size_t b = 0; b < fn.blocks.size(); ++b)
		for (size_t i = 0; i < fn.blocks[b].instructions.size(); ++i) {
			const lowir2cy86::Instruction& ins = fn.blocks[b].instructions[i];
			if (ins.kind != lowir2cy86::InstrKind::Index ||
			    !temp_value_named(ins.a, name))
				continue;
			if (stack_call_index_args_.find(ins.dest) !=
			        stack_call_index_args_.end() ||
			    index_feeds_stack_call_arg_load(fn, ins.dest))
				return true;
		}
	return false;
}

bool MirDumper::load_result_feeds_store_source_load(
    const lowir2cy86::Function& fn, const string& name) const {
	set<string> seen;
	return load_result_feeds_store_source_load(fn, name, seen);
}

bool MirDumper::load_result_feeds_store_source_load(
    const lowir2cy86::Function& fn, const string& name,
    set<string>& seen) const {
	if (!seen.insert(name).second)
		return false;
	for (size_t b = 0; b < fn.blocks.size(); ++b)
		for (size_t i = 0; i < fn.blocks[b].instructions.size(); ++i) {
			const lowir2cy86::Instruction& ins = fn.blocks[b].instructions[i];
			if (ins.kind == lowir2cy86::InstrKind::Load &&
			    temp_value_named(ins.a, name) &&
			    store_source_loads_.find(ins.dest) !=
			        store_source_loads_.end())
				return true;
			if (ins.kind == lowir2cy86::InstrKind::Index &&
			    temp_value_named(ins.a, name) &&
			    load_result_feeds_store_source_load(fn, ins.dest, seen))
				return true;
		}
	return false;
}

bool MirDumper::load_result_feeds_post_stack_value_load(
    const lowir2cy86::Function& fn, const string& name) const {
	set<string> seen;
	return load_result_feeds_post_stack_value_load(fn, name, seen);
}

bool MirDumper::load_result_feeds_post_stack_value_load(
    const lowir2cy86::Function& fn, const string& name,
    set<string>& seen) const {
	if (!seen.insert(name).second)
		return false;
	for (size_t b = 0; b < fn.blocks.size(); ++b)
		for (size_t i = 0; i < fn.blocks[b].instructions.size(); ++i) {
			const lowir2cy86::Instruction& ins = fn.blocks[b].instructions[i];
			if (ins.kind == lowir2cy86::InstrKind::Load &&
			    temp_value_named(ins.a, name) &&
			    (live_across_calls_.find(ins.dest) !=
			         live_across_calls_.end() ||
			     stack_call_arg_temps_.find(ins.dest) !=
			         stack_call_arg_temps_.end()))
				return true;
			if (ins.kind == lowir2cy86::InstrKind::Index &&
			    temp_value_named(ins.a, name) &&
			    load_result_feeds_post_stack_value_load(fn, ins.dest, seen))
				return true;
		}
	return false;
}

bool MirDumper::promoted_load_feeds_direct_call_index(
    const lowir2cy86::Function& fn, const string& name) const {
	if (promoted_loads_.find(name) == promoted_loads_.end())
		return false;
	for (size_t b = 0; b < fn.blocks.size(); ++b)
		for (size_t i = 0; i < fn.blocks[b].instructions.size(); ++i) {
			const lowir2cy86::Instruction& index = fn.blocks[b].instructions[i];
			if (index.kind != lowir2cy86::InstrKind::Index ||
			    !temp_value_named(index.a, name))
				continue;
			for (size_t cb = 0; cb < fn.blocks.size(); ++cb)
				for (size_t ci = 0; ci < fn.blocks[cb].instructions.size(); ++ci) {
					const lowir2cy86::Instruction& call =
					    fn.blocks[cb].instructions[ci];
					if (call.kind != lowir2cy86::InstrKind::Call ||
					    call.a.kind != lowir2cy86::ValueKind::Function ||
					    call.args.size() != 1)
						continue;
					for (size_t a = 0; a < call.args.size(); ++a)
						if (temp_value_named(call.args[a], index.dest))
							return true;
				}
		}
	return false;
}

bool MirDumper::temp_used_only_as_store_dest(const lowir2cy86::Function& fn,
                                  const string& name) const {
	size_t uses = 0;
	bool only_store_dest = true;
	for (size_t b = 0; b < fn.blocks.size(); ++b)
		for (size_t i = 0; i < fn.blocks[b].instructions.size(); ++i) {
			const lowir2cy86::Instruction& ins = fn.blocks[b].instructions[i];
			if (temp_value_named(ins.b, name) &&
			    ins.kind == lowir2cy86::InstrKind::Store) {
				++uses;
				continue;
			}
			if (temp_value_named(ins.a, name) ||
			    temp_value_named(ins.b, name) ||
			    temp_value_named(ins.c, name))
				only_store_dest = false;
			for (size_t a = 0; a < ins.args.size(); ++a)
				if (temp_value_named(ins.args[a], name))
					only_store_dest = false;
		}
	return uses == 1 && only_store_dest;
}

long MirDumper::index_literal_offset(const lowir2cy86::Instruction& ins) const {
	if (ins.kind != lowir2cy86::InstrKind::Index ||
	    ins.b.kind != lowir2cy86::ValueKind::Literal)
		return -1;
	return stol(ins.b.text) *
	       static_cast<long>(lowir2cy86::storage_size(ins.type));
}

string MirDumper::load_source(const lowir2cy86::Function& fn,
                   const lowir2cy86::Value& value) {
	const lowir2cy86::Instruction* addr = optimized_addr_definition(value);
	if (addr != nullptr)
		return value_reg(fn, addr->a);
	if (value.kind == lowir2cy86::ValueKind::Temp) return "[" + value_reg(fn, value) + "]"; return value_reg(fn, value); }

bool MirDumper::is_thread_local_global(const string& name) const {
	map<string, size_t>::const_iterator it = program_.global_by_name.find(name);
	return it != program_.global_by_name.end() &&
	       lowir2cy86::metadata_value(program_.globals[it->second].metadata,
	                                  "storage") == "thread_local"; }

string MirDumper::tls_wrapper_for_global(const string& name) const {
	for (size_t i = 0; i < program_.functions.size(); ++i)
		if (lowir2cy86::metadata_value(program_.functions[i].metadata,
		                               "tls_for") == name)
			return program_.functions[i].name; return name; }

void MirDumper::dump_load(const lowir2cy86::Function& fn,
               const lowir2cy86::Instruction& ins) {
	map<string, string>::const_iterator ebit =
	    entry_branch_param_loads_.find(ins.dest);
	if (ebit != entry_branch_param_loads_.end()) {
		map<string, string>::const_iterator eit =
		    entry_param_regs_.find(ebit->second);
		if (eit != entry_param_regs_.end()) {
			remember_fixed_temp_reg(ins.dest, eit->second);
			return;
		}
	}
	if (sret_frame_temps_.find(ins.dest) != sret_frame_temps_.end()) {
		if (ins.a.kind == lowir2cy86::ValueKind::Temp &&
		    sret_frame_temps_.find(ins.a.text) !=
		        sret_frame_temps_.end()) {
			out_ << "    load.ptr rcx, "
			     << frame_temp_mem(fn, ins.a.text) << "\n";
			out_ << "    load." << ins.type.text << " rax, [rcx]\n";
		} else {
			out_ << "    load." << ins.type.text << " rax, "
			     << load_source(fn, ins.a) << "\n";
		}
		if (stack_call_arg_temps_.find(ins.dest) == stack_call_arg_temps_.end())
			dump_narrow_extend(ins.type, "rax");
		out_ << "    store." << ins.type.text << " "
		     << frame_temp_mem(fn, ins.dest) << ", rax\n";
		return;
	}
	if (lowir2cy86::is_f80_type(ins.type)) {
		lowir2cy86::Value dst;
		dst.kind = lowir2cy86::ValueKind::Temp;
		dst.text = ins.dest;
		const string src = ins.a.kind == lowir2cy86::ValueKind::Temp
		                       ? "[" + value_reg(fn, ins.a) + "]"
		                       : value_reg(fn, ins.a);
		out_ << "    fmov.f80 " << mir_f80_value(fn, dst, omitted_slots_)
		     << ", " << src << "\n";
		return;
	}
	if (mir_is_xmm_type(ins.type)) {
		out_ << "    fmov." << ins.type.text << " " << xmm_reg(ins.dest)
		     << ", " << load_source(fn, ins.a) << "\n";
		return;
	}
	if (ins.a.kind == lowir2cy86::ValueKind::Global &&
	    is_thread_local_global(ins.a.text)) {
		const string dst = load_dest_reg(fn, ins);
		out_ << "    tls_addr r11, "
		     << tls_wrapper_for_global(ins.a.text) << "\n";
		out_ << "    load." << ins.type.text << " " << dst
		     << ", [r11]\n";
		dump_narrow_extend(ins.type, dst);
		remember_load_dest(ins.dest, dst);
		return;
	}
	if (ins.a.kind == lowir2cy86::ValueKind::Temp &&
	    direct_object_copy_addrs_.find(ins.a.text) !=
	        direct_object_copy_addrs_.end()) {
		const lowir2cy86::Instruction& addr = *definitions_[ins.a.text];
		dump_address_to_reg(fn, addr.a, "rcx");
		const string dst = load_dest_reg(fn, ins);
		out_ << "    load." << ins.type.text << " " << dst
		     << ", [rcx]\n";
		dump_narrow_extend(ins.type, dst);
		remember_load_dest(ins.dest, dst);
		return;
	}
	if (ins.a.kind == lowir2cy86::ValueKind::Temp &&
	    promoted_addr_params_.find(ins.a.text) !=
	        promoted_addr_params_.end()) {
		lowir2cy86::Value param;
		param.kind = lowir2cy86::ValueKind::Temp;
		param.text = promoted_addr_params_[ins.a.text];
		out_ << "    lea rcx, " << param_slot_mem(fn, param) << "\n";
		const string dst = load_dest_reg(fn, ins);
		out_ << "    load." << ins.type.text << " " << dst
		     << ", [rcx]\n";
		dump_narrow_extend(ins.type, dst);
		remember_load_dest(ins.dest, dst);
		return;
	}
	lowir2cy86::Value src_value = promoted_store_dest(ins.a);
	if (src_value.kind == lowir2cy86::ValueKind::Temp &&
	    param_index(fn, src_value.text) >= 0 &&
	    lowir2cy86::is_ptr_type(mir_lookup_type(fn, src_value))) {
		const bool promoted = ins.a.kind == lowir2cy86::ValueKind::Temp &&
		    promoted_loads_.find(ins.a.text) != promoted_loads_.end();
		const string src = value_reg(fn, src_value);
		string base = pointer_load_base_reg(fn, src_value, promoted);
		if (optimization_level_ >= 1 &&
		    direct_return_values_.find(ins.dest) !=
		        direct_return_values_.end())
			base = src;
		if (src != base)
			out_ << "    mov " << base << ", " << src << "\n";
		const string dst = load_dest_reg(fn, ins);
		out_ << "    load." << ins.type.text << " " << dst
		     << ", [" << base << "]" << debug_suffix(ins) << "\n";
		dump_narrow_extend(ins.type, dst, ins.debug);
		remember_load_dest(ins.dest, dst);
		return;
	}
	const string dst = load_dest_reg(fn, ins);
	out_ << "    load." << ins.type.text << " " << dst << ", "
	     << load_source(fn, ins.a) << debug_suffix(ins) << "\n";
	if (post_call_direct_branch_loads_.find(ins.dest) !=
	    post_call_direct_branch_loads_.end()) {
		out_ << "    store." << ins.type.text << " "
		     << frame_temp_mem(fn, ins.dest) << ", " << dst << "\n";
		remember_fixed_temp_reg(ins.dest, dst);
		return;
	}
	if (stack_call_arg_temps_.find(ins.dest) == stack_call_arg_temps_.end())
		dump_narrow_extend(ins.type, dst, ins.debug);
	remember_load_dest(ins.dest, dst); }

string MirDumper::pointer_load_base_reg(const lowir2cy86::Function& fn,
                             const lowir2cy86::Value& value,
                             bool promoted) const {
	const int index = param_index(fn, value.text);
	if (promoted || (index >= 0 && param_pass_is(fn, index, "reference")))
		return "r9";
	return "r8"; }

string MirDumper::load_dest_reg(const lowir2cy86::Function& fn,
                                const lowir2cy86::Instruction& ins) {
	if (ins.kind == lowir2cy86::InstrKind::AtomicLoad)
		return atomic_load_dest_reg(fn, ins);
	string reg = store_source_load_dest_reg(fn, ins);
	if (!reg.empty())
		return reg;
	reg = indirect_result_load_dest_reg(fn, ins);
	if (!reg.empty())
		return reg;
	reg = fixed_analysis_load_dest_reg(fn, ins);
	if (!reg.empty())
		return reg;
	return fallback_load_dest_reg(fn, ins);
}

string MirDumper::atomic_load_dest_reg(const lowir2cy86::Function& fn,
                                       const lowir2cy86::Instruction& ins) {
	const string ptr = value_reg(fn, ins.a);
	if (!preferred_load_reg_.empty() && ptr == preferred_load_ptr_) {
		const string reg = preferred_load_reg_;
		preferred_load_ptr_.clear();
		preferred_load_reg_.clear();
		fixed_load_dest_ = true;
		if (preferred_load_sets_literal_)
			prefer_r8_literal_ = true;
		preferred_load_sets_literal_ = false;
		return reg;
	}
	return temp_reg(ins.dest);
}

string MirDumper::store_source_load_dest_reg(
    const lowir2cy86::Function& fn, const lowir2cy86::Instruction& ins) {
	if (store_source_loads_.find(ins.dest) == store_source_loads_.end())
		return "";
	if (current_block_index_ != 0 &&
	    store_source_feeds_reference_param_dest(fn, ins.dest)) {
		fixed_load_dest_ = true;
		return "r8";
	}
	if (has_indirect_result_param(fn) && current_block_index_ != 0 &&
	    past_stack_call_in_block_ &&
	    live_across_calls_.find(ins.dest) == live_across_calls_.end() &&
	    stack_call_arg_temps_.find(ins.dest) == stack_call_arg_temps_.end() &&
	    ins.a.kind == lowir2cy86::ValueKind::Temp &&
	    temp_origin_is_reference_param(fn, ins.a.text)) {
		fixed_load_dest_ = true;
		return "r9";
	}
	if (sret_constructor_like(fn) && current_block_index_ != 0 &&
	    ins.a.kind == lowir2cy86::ValueKind::Slot &&
	    lowir2cy86::is_integer_type(ins.type) && ins.type.bits <= 32) {
		fixed_load_dest_ = true;
		return "r8";
	}
	fixed_load_dest_ = true;
	return "rax";
}

string MirDumper::indirect_result_load_dest_reg(
    const lowir2cy86::Function& fn, const lowir2cy86::Instruction& ins) {
	if (current_block_index_ != 0) {
		const string reference_store_base =
		    reference_store_dest_base_reg(fn, ins.dest);
		if (!reference_store_base.empty()) {
			fixed_load_dest_ = true;
			return reference_store_base;
		}
	}
	if (!has_indirect_result_param(fn) || current_block_index_ == 0)
		return "";
	if (!past_stack_call_in_block_ &&
	    load_result_feeds_pre_stack_call_index(fn, ins.dest)) {
		fixed_load_dest_ = true;
		return "r9";
	}
	if (past_stack_call_in_block_ &&
	    load_result_feeds_store_source_load(fn, ins.dest)) {
		fixed_load_dest_ = true;
		return "r8";
	}
	if (past_stack_call_in_block_ &&
	    load_result_feeds_post_stack_value_load(fn, ins.dest)) {
		fixed_load_dest_ = true;
		return "r8";
	}
	if (past_stack_call_in_block_ &&
	    live_across_calls_.find(ins.dest) == live_across_calls_.end() &&
	    temp_used_as_direct_call_arg(fn, ins.dest)) {
		fixed_load_dest_ = true;
		return "r8";
	}
	return "";
}

string MirDumper::fixed_analysis_load_dest_reg(
    const lowir2cy86::Function& fn, const lowir2cy86::Instruction& ins) {
	if (optimization_level_ >= 1 &&
	    direct_return_values_.find(ins.dest) != direct_return_values_.end() &&
	    lowir2cy86::is_integer_type(ins.type) && ins.type.bits < 64 &&
	    ins.a.kind == lowir2cy86::ValueKind::Temp &&
	    param_index(fn, ins.a.text) >= 0 &&
	    lowir2cy86::is_ptr_type(mir_lookup_type(fn, ins.a))) {
		fixed_load_dest_ = true;
		return "r9";
	}
	if (direct_return_values_.find(ins.dest) != direct_return_values_.end() &&
	    (!lowir2cy86::is_integer_type(ins.type) || ins.type.bits == 64)) {
		fixed_load_dest_ = true;
		return "rax";
	}
	if (post_call_direct_branch_loads_.find(ins.dest) !=
	    post_call_direct_branch_loads_.end()) {
		fixed_load_dest_ = true;
		return "rax";
	}
	if (materialized_branch_loads_.find(ins.dest) !=
	    materialized_branch_loads_.end()) {
		fixed_load_dest_ = true;
		return "rax";
	}
	if (param_base_loads_.find(ins.dest) != param_base_loads_.end()) {
		fixed_load_dest_ = true;
		return "r12";
	}
	if (reference_store_cmp_sources_.find(ins.dest) !=
	    reference_store_cmp_sources_.end()) {
		fixed_load_dest_ = true;
		return "r15";
	}
	if (reference_store_source_temps_.find(ins.dest) !=
	    reference_store_source_temps_.end() &&
	    lowir2cy86::is_integer_type(ins.type)) {
		fixed_load_dest_ = true;
		return "r15";
	}
	if (entry_branch_param_value_loads_.find(ins.dest) !=
	    entry_branch_param_value_loads_.end()) {
		fixed_load_dest_ = true;
		return "r13";
	}
	if (ins.a.kind == lowir2cy86::ValueKind::Temp) {
		const string projected = param_for_projected_load_base(fn, ins.a.text);
		if (!projected.empty()) {
			const int index = param_index(fn, projected);
			if (index >= 0 && param_pass_is(fn, index, "reference")) {
				fixed_load_dest_ = true;
				return "rbx";
			}
		}
	}
	if (current_block_index_ != 0 && function_has_float(fn) &&
	    direct_branch_value_operands_.find(ins.dest) !=
	        direct_branch_value_operands_.end()) {
		fixed_load_dest_ = true;
		return preserve_reg(0);
	}
	if (full_gpr_indirect_callee_loads_.find(ins.dest) !=
	    full_gpr_indirect_callee_loads_.end()) {
		fixed_load_dest_ = true;
		return "r15";
	}
	if (indirect_callee_loads_.find(ins.dest) != indirect_callee_loads_.end()) {
		fixed_load_dest_ = true;
		return "r10";
	}
	if (indirect_callee_base_loads_.find(ins.dest) !=
	    indirect_callee_base_loads_.end()) {
		fixed_load_dest_ = true;
		return "rbx";
	}
	return "";
}

string MirDumper::fallback_load_dest_reg(const lowir2cy86::Function& fn,
                                         const lowir2cy86::Instruction& ins) {
	if (optimization_level_ >= 1 && optimized_addr_definition(ins.a) != nullptr)
		return "r8";
	const string source = value_reg(fn, ins.a);
	if (live_across_calls_.find(ins.dest) != live_across_calls_.end())
		return temp_reg(ins.dest);
	if (direct_return_values_.find(ins.dest) != direct_return_values_.end() &&
	    lowir2cy86::is_integer_type(ins.type) && ins.type.bits < 64 &&
	    (source == "rcx" || (large_slot_frame_ && source == "r8"))) {
		fixed_load_dest_ = true;
		return "r9";
	}
	if (!preferred_load_reg_.empty() && source == preferred_load_ptr_) {
		const string reg = preferred_load_reg_;
		preferred_load_ptr_.clear();
		preferred_load_reg_.clear();
		preferred_load_sets_literal_ = false;
		fixed_load_dest_ = true;
		return reg;
	}
	if (prefer_r8_stack_load_ && ins.a.kind == lowir2cy86::ValueKind::Slot) {
		prefer_r8_stack_load_ = false;
		fixed_load_dest_ = true;
		return "r8";
	}
	if (ins.a.kind == lowir2cy86::ValueKind::Global)
		return reg_is_live("r8") ? "r9" : "r8";
	if (large_slot_frame_ &&
	    direct_branch_value_operands_.find(ins.dest) !=
	        direct_branch_value_operands_.end() &&
	    ins.a.kind == lowir2cy86::ValueKind::Temp && source == "r8")
		return "r9";
	if (ins.a.kind == lowir2cy86::ValueKind::Temp && source != "r8")
		return reg_is_live("r8") ? "r9" : "r8";
	return temp_reg(ins.dest);
}

bool MirDumper::store_source_feeds_reference_param_dest(
    const lowir2cy86::Function& fn, const string& name) const {
	for (size_t b = 0; b < fn.blocks.size(); ++b)
		for (size_t i = 0; i < fn.blocks[b].instructions.size(); ++i) {
			const lowir2cy86::Instruction& ins = fn.blocks[b].instructions[i];
			if (ins.kind != lowir2cy86::InstrKind::Store ||
			    !temp_value_named(ins.a, name) ||
			    ins.b.kind != lowir2cy86::ValueKind::Temp)
				continue;
			return temp_origin_is_reference_param(fn, ins.b.text);
	}
	return false;
}

string MirDumper::reference_store_dest_base_reg(
    const lowir2cy86::Function& fn, const string& name) const {
	for (size_t b = 0; b < fn.blocks.size(); ++b)
		for (size_t i = 0; i < fn.blocks[b].instructions.size(); ++i) {
			const lowir2cy86::Instruction& index = fn.blocks[b].instructions[i];
			if (index.kind != lowir2cy86::InstrKind::Index ||
			    !temp_value_named(index.a, name) ||
			    !temp_origin_is_reference_param(fn, index.dest))
				continue;
			const lowir2cy86::Instruction* store =
			    unique_store_to_temp(fn, index.dest);
			if (store == nullptr)
				continue;
			if (store->a.kind == lowir2cy86::ValueKind::Literal)
				return "r8";
			if (store_source_is_load(store->a))
				return "r9";
	}
	return "";
}

bool MirDumper::temp_used_as_direct_call_arg(const lowir2cy86::Function& fn,
                                  const string& name) const {
	for (size_t b = 0; b < fn.blocks.size(); ++b)
		for (size_t i = 0; i < fn.blocks[b].instructions.size(); ++i) {
			const lowir2cy86::Instruction& ins = fn.blocks[b].instructions[i];
			if (ins.kind != lowir2cy86::InstrKind::Call ||
			    ins.a.kind != lowir2cy86::ValueKind::Function)
				continue;
			for (size_t a = 0; a < ins.args.size(); ++a)
				if (temp_value_named(ins.args[a], name))
					return true;
		}
	return false;
}

bool MirDumper::function_has_float(const lowir2cy86::Function& fn) const {
	for (size_t b = 0; b < fn.blocks.size(); ++b)
		for (size_t i = 0; i < fn.blocks[b].instructions.size(); ++i) {
			const lowir2cy86::Instruction& ins = fn.blocks[b].instructions[i];
			if (lowir2cy86::is_float_type(ins.type) ||
			    lowir2cy86::is_float_type(ins.src_type))
				return true;
			for (size_t a = 0; a < ins.signature.params.size(); ++a)
				if (lowir2cy86::is_float_type(ins.signature.params[a].type))
					return true;
		}
	return false;
}

void MirDumper::remember_load_dest(const string& name, const string& reg) {
	if (fixed_load_dest_) {
		remember_fixed_temp_reg(name, reg);
		fixed_load_dest_ = false;
		return;
	}
	remember_temp_reg(name, reg); }

void MirDumper::dump_atomic_store(const lowir2cy86::Function& fn,
                       const lowir2cy86::Instruction& ins) {
	const string ptr = value_reg(fn, ins.b);
	const string src = value_reg(fn, ins.a);
	if (ins.order_a >= 5) {
		out_ << "    mov rax, " << src << "\n";
		out_ << "    xchg." << ins.type.text << " [" << ptr << "], rax\n";
		remember_reload(ptr, src, true);
		return;
	}
	out_ << "    store." << ins.type.text << " [" << ptr << "], " << src << "\n";
	remember_reload(ptr, src, true); }

void MirDumper::remember_store_reload(const lowir2cy86::Function& fn,
                           const lowir2cy86::Value& ptr_value,
                           const lowir2cy86::Value& src_value) {
	remember_reload(value_reg(fn, ptr_value), value_reg(fn, src_value), true); }

void MirDumper::remember_reload(const string& ptr, const string& reg, bool prefer_literal) {
	preferred_load_ptr_ = ptr;
	preferred_load_reg_ = reg;
	preferred_load_sets_literal_ = prefer_literal;
	note_temp_reg(reg); }

void MirDumper::dump_narrow_extend(const lowir2cy86::Type& type,
                                   const string& reg,
                                   const string& debug) {
	if (lowir2cy86::is_signed_integer_type(type) && type.bits < 64)
		out_ << "    sext.i" << type.bits << " " << reg
		     << debug_suffix(debug) << "\n";
	else if (type.kind == lowir2cy86::TypeKind::UnsignedInt && type.bits < 64)
		out_ << "    zext.i" << type.bits << " " << reg
		     << debug_suffix(debug) << "\n"; }

string MirDumper::store_dest(const lowir2cy86::Function& fn,
                  const lowir2cy86::Value& value) {
	if (value.kind == lowir2cy86::ValueKind::Temp &&
	    sret_frame_temps_.find(value.text) != sret_frame_temps_.end()) {
		out_ << "    load.ptr rcx, " << frame_temp_mem(fn, value.text)
		     << "\n";
		return "[rcx]";
	}
	if (value.kind == lowir2cy86::ValueKind::Temp) {
		map<string, string>::const_iterator ait = promoted_loads_.find(value.text);
		if (ait != promoted_loads_.end()) {
			lowir2cy86::Value param;
			param.kind = lowir2cy86::ValueKind::Temp;
			param.text = ait->second;
			return store_dest(fn, param);
		}
	}
	if (value.kind == lowir2cy86::ValueKind::Temp &&
	    inline_copy_addrs_.find(value.text) != inline_copy_addrs_.end()) {
		const lowir2cy86::Instruction& addr = *definitions_[value.text];
		const string op =
		    addr.a.kind == lowir2cy86::ValueKind::Global ? "mov" : "lea";
		out_ << "    " << op << " rcx, " << value_reg(fn, addr.a) << "\n";
		return "[rcx]";
	}
	if (value.kind == lowir2cy86::ValueKind::Temp &&
	    entry_param_regs_.find(value.text) != entry_param_regs_.end())
		return "[" + value_reg(fn, value) + "]";
	if (value.kind == lowir2cy86::ValueKind::Temp &&
	    param_index(fn, value.text) >= 0 &&
	    lowir2cy86::is_ptr_type(mir_lookup_type(fn, value))) {
		const string reg = fn.params.size() == 1 ? "r9" : "r8";
		out_ << "    mov " << reg << ", " << value_reg(fn, value) << "\n";
		return "[" + reg + "]";
	}
	const lowir2cy86::Instruction* addr = optimized_addr_definition(value);
	if (addr != nullptr)
		return value_reg(fn, addr->a);
	if (value.kind == lowir2cy86::ValueKind::Temp) return "[" + value_reg(fn, value) + "]"; return value_reg(fn, value); }

}  // namespace lowir2native
