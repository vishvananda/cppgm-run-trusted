#include "lowir2native_mir_dumper.h"

namespace lowir2native {

void MirDumper::dump_binary(const lowir2cy86::Function& fn,
                 const lowir2cy86::Instruction& ins) {
	if (lowir2cy86::is_f80_type(ins.type)) {
		lowir2cy86::Value dst;
		dst.kind = lowir2cy86::ValueKind::Temp;
		dst.text = ins.dest;
		out_ << "    f" << float_binary_opcode(ins.op) << ".f80 "
		     << mir_f80_value(fn, dst, omitted_slots_) << ", "
		     << mir_f80_value(fn, ins.a, omitted_slots_) << ", "
		     << mir_f80_value(fn, ins.b, omitted_slots_) << "\n";
		return;
	}
	if (lowir2cy86::is_float_type(ins.type) && !lowir2cy86::is_f80_type(ins.type)) {
		dump_float_binary(fn, ins);
		return;
	}
	const string dst = binary_dest_reg(fn, ins);
	string left;
	if (ins.a.kind == lowir2cy86::ValueKind::Temp &&
	    tls_pressure_frame_temps_.find(ins.a.text) !=
	        tls_pressure_frame_temps_.end()) {
		out_ << "    load." << ins.type.text << " " << dst
		     << ", " << frame_temp_mem(fn, ins.a.text) << "\n";
		left = dst;
	} else
		left = value_reg(fn, ins.a);
	if (is_param_slot_value(fn, ins.a)) {
		out_ << "    load." << ins.type.text << " " << dst
		     << ", " << param_slot_mem(fn, ins.a) << "\n";
		dump_narrow_extend(ins.type, dst); } else if (dst != left)
		out_ << "    mov " << dst << ", " << left << "\n";
	if (ins.op == "udiv" || ins.op == "umod")
		dump_divmod(fn, ins, dst, false);
	else if (ins.op == "div" || ins.op == "mod")
		dump_divmod(fn, ins, dst, true);
	else if (ins.op == "ushr") {
		const string rhs = shift_rhs(fn, ins.b);
		out_ << "    shr " << dst << ", " << rhs << "\n"; } else if (ins.op == "shr") {
		const string rhs = shift_rhs(fn, ins.b);
		out_ << "    sar " << dst << ", " << rhs << "\n"; } else if (ins.op == "shl") {
		const string rhs = shift_rhs(fn, ins.b);
		out_ << "    shl " << dst << ", " << rhs << "\n"; } else {
		string rhs;
			const bool rhs_tls_frame =
			    ins.b.kind == lowir2cy86::ValueKind::Temp &&
			    tls_pressure_frame_temps_.find(ins.b.text) !=
			        tls_pressure_frame_temps_.end();
			string literal_rhs;
			if (optimization_level_ >= 1 &&
			    rematerialized_binary_immediates_.find(ins.b.text) !=
			        rematerialized_binary_immediates_.end() &&
			    value_is_const_integer_literal(ins.b, literal_rhs))
				rhs = literal_rhs;
			else if (rhs_tls_frame) {
				out_ << "    load." << ins.type.text << " rdx"
				     << ", " << frame_temp_mem(fn, ins.b.text) << "\n";
				rhs = "rdx";
			} else
				rhs = value_reg(fn, ins.b);
		if (is_param_slot_value(fn, ins.b)) {
			out_ << "    load." << ins.type.text << " rdx"
			     << ", " << param_slot_mem(fn, ins.b) << "\n";
			dump_narrow_extend(ins.type, "rdx");
			rhs = "rdx";
		}
		if (ins.b.kind == lowir2cy86::ValueKind::Literal &&
		    (literal_needs_reg(ins.b.text) ||
		     binary_literal_prefers_reg(ins))) {
			out_ << "    mov rdx, " << ins.b.text << "\n";
			rhs = "rdx";
		}
		if (ins.a.kind == lowir2cy86::ValueKind::Temp &&
		    ins.b.kind == lowir2cy86::ValueKind::Temp &&
		    ins.a.text == ins.b.text && dst != left)
			rhs = dst;
			out_ << "    " << binary_opcode(ins.op) << " " << dst << ", "
			     << rhs << debug_suffix(ins) << "\n";
	}
	dump_narrow_extend(ins.type, dst);
	if (tls_pressure_frame_temps_.find(ins.dest) !=
	    tls_pressure_frame_temps_.end()) {
		out_ << "    store." << ins.type.text << " "
		     << frame_temp_mem(fn, ins.dest) << ", " << dst << "\n";
		return;
	}
	remember_temp_reg(ins.dest, dst); }

void MirDumper::dump_float_binary(const lowir2cy86::Function& fn,
                       const lowir2cy86::Instruction& ins) {
	const string dst = float_binary_dest(ins);
	out_ << "    f" << float_binary_opcode(ins.op) << "." << ins.type.text << " "
	     << dst << ", " << float_value(fn, ins.a) << ", "
	     << float_value(fn, ins.b) << debug_suffix(ins) << "\n";
	remember_xmm_reg(ins.dest, dst); }

string MirDumper::float_binary_dest(const lowir2cy86::Instruction& ins) {
	if (ins.b.kind == lowir2cy86::ValueKind::Literal) return "xmm0"; return xmm_reg(ins.dest); }

bool MirDumper::literal_needs_reg(const string& text) const {
	char* end = nullptr;
	const long long value = strtoll(text.c_str(), &end, 0);
	return end != text.c_str() && *end == '\0' &&
	       (value > 2147483647LL || value < -2147483648LL); }

bool MirDumper::binary_literal_prefers_reg(const lowir2cy86::Instruction& ins) const {
	if (ins.op != "or" || ins.a.kind != lowir2cy86::ValueKind::Temp)
		return false;
	map<string, const lowir2cy86::Instruction*>::const_iterator it =
	    definitions_.find(ins.a.text);
	if (it == definitions_.end() ||
	    it->second->kind != lowir2cy86::InstrKind::Copy ||
	    it->second->a.kind != lowir2cy86::ValueKind::Temp)
		return false;
	map<string, const lowir2cy86::Instruction*>::const_iterator ait =
	    definitions_.find(it->second->a.text);
	return ait != definitions_.end() &&
	       ait->second->kind == lowir2cy86::InstrKind::Addr &&
	       ait->second->a.kind == lowir2cy86::ValueKind::Global;
}

string MirDumper::binary_dest_reg(const lowir2cy86::Function& fn,
                       const lowir2cy86::Instruction& ins) {
	if (tls_accumulator_temps_.find(ins.dest) !=
	    tls_accumulator_temps_.end())
		return "r14";
	if (tls_pressure_frame_temps_.find(ins.dest) !=
	    tls_pressure_frame_temps_.end())
		return "rax";
	if (live_across_calls_.find(ins.dest) != live_across_calls_.end())
		return temp_reg(ins.dest);
	if (is_param_slot_value(fn, ins.a)) return temp_reg(ins.dest);
	if (ins.a.kind == lowir2cy86::ValueKind::Temp &&
	    entry_param_regs_.find(ins.a.text) != entry_param_regs_.end())
		return value_reg(fn, ins.a);
	if (ins.a.kind == lowir2cy86::ValueKind::Temp &&
	    param_index(fn, ins.a.text) >= 0 &&
	    mixed_gpr_xmm_abi_shape(fn) &&
	    param_index(fn, ins.a.text) == 0)
		return "r13";
	if (ins.a.kind == lowir2cy86::ValueKind::Temp &&
	    param_index(fn, ins.a.text) >= 0 &&
	    fn.params.size() == 1 && ins.b.kind == lowir2cy86::ValueKind::Literal)
		return "r9";
	if (ins.a.kind == lowir2cy86::ValueKind::Temp &&
	    param_index(fn, ins.a.text) >= 0)
		return live_preserve_reg();
	if (ins.a.kind == lowir2cy86::ValueKind::Temp &&
	    ins.b.kind == lowir2cy86::ValueKind::Temp &&
	    ins.a.text == ins.b.text) {
		const string reg = value_reg(fn, ins.a);
		if (reg == "rax")
			return "r8";
		return reg;
	}
	if (current_block_index_ != 0 &&
	    ins.a.kind == lowir2cy86::ValueKind::Temp &&
	    live_across_calls_.find(ins.a.text) != live_across_calls_.end())
		return reg_is_live("r8") ? "r9" : "r8";
	if (is_last_use(ins.a)) return value_reg(fn, ins.a); return temp_reg(ins.dest); }

void MirDumper::remember_temp_reg(const string& name, const string& reg) {
	note_temp_reg(reg);
	for (size_t i = 0; i < temp_names_.size(); ++i) {
		if (temp_names_[i] == name) {
			temp_regs_[i] = reg;
			return;
		}
	}
	temp_names_.push_back(name);
	temp_regs_.push_back(reg); }

void MirDumper::remember_fixed_temp_reg(const string& name, const string& reg) {
	fixed_temp_regs_[name] = reg;
	note_temp_reg(reg); }

string MirDumper::shift_rhs(const lowir2cy86::Function& fn,
                 const lowir2cy86::Value& value) {
	if (value.kind == lowir2cy86::ValueKind::Literal) {
		out_ << "    mov rdx, " << value.text << "\n";
		out_ << "    mov rcx, rdx\n";
		return "cl";
	}
	const string reg = value_reg(fn, value);
	if (reg != "rcx")
		out_ << "    mov rcx, " << reg << "\n"; return "cl"; }

void MirDumper::dump_divmod(const lowir2cy86::Function& fn,
                 const lowir2cy86::Instruction& ins,
                 const string& dst,
                 bool signed_div) {
	if (ins.b.kind == lowir2cy86::ValueKind::Literal) {
		out_ << "    mov rdx, " << ins.b.text << "\n";
		out_ << "    mov rcx, rdx\n"; } else
		out_ << "    mov rcx, " << value_reg(fn, ins.b) << "\n";
	out_ << "    mov rax, " << dst << "\n";
	out_ << "    mov rdx, 0\n";
	out_ << "    " << (signed_div ? "idiv" : "div") << " rcx\n";
	if (ins.op == "mod" || ins.op == "umod")
		out_ << "    mov " << dst << ", rdx\n";
	else
		out_ << "    mov " << dst << ", rax\n"; }

void MirDumper::dump_cmp_value(const lowir2cy86::Function& fn,
                    const lowir2cy86::Instruction& ins) {
	if (lowir2cy86::is_f80_type(ins.type)) {
		out_ << "    f" << condition_word(ins.op) << ".f80 rax, "
		     << mir_f80_value(fn, ins.a, omitted_slots_) << ", "
		     << mir_f80_value(fn, ins.b, omitted_slots_) << "\n";
		dump_rax_condition_result(ins.dest);
		return;
	}
	if (lowir2cy86::is_float_type(ins.type)) {
		out_ << "    f" << condition_word(ins.op) << "." << ins.type.text
		     << " rax, " << float_value(fn, ins.a) << ", "
		     << float_value(fn, ins.b) << "\n";
		dump_rax_condition_result(ins.dest);
		return;
	}
	const string dst = cmp_value_dest_reg(fn, ins);
	const string lhs = value_reg(fn, ins.a);
	if (dst != lhs)
		out_ << "    mov " << dst << ", " << lhs << "\n";
	const string rhs = compare_rhs(fn, ins.b);
	out_ << "    cmp." << ins.type.text << " " << dst << ", " << rhs << "\n";
	out_ << "    set" << condition_suffix(ins.op) << " " << dst << "\n";
	out_ << "    movzx " << dst << ", " << dst << "\n";
	if (dst == lhs && is_last_use(ins.a))
		remember_fixed_temp_reg(ins.dest, dst);
	else
		remember_temp_reg(ins.dest, dst); }

bool MirDumper::cmp_result_stays_in_rax(const string& name) const {
	map<string, int>::const_iterator it = use_counts_.find(name);
	return direct_return_values_.find(name) != direct_return_values_.end() ||
	       it == use_counts_.end() || it->second == 0; }

void MirDumper::dump_rax_condition_result(const string& name) {
	if (cmp_result_stays_in_rax(name)) {
		remember_fixed_temp_reg(name, "rax");
		return;
	}
	const string dst = temp_reg(name);
	out_ << "    mov " << dst << ", rax\n"; }

string MirDumper::cmp_value_dest_reg(const lowir2cy86::Function& fn,
                          const lowir2cy86::Instruction& ins) {
	if (ins.a.kind == lowir2cy86::ValueKind::Temp &&
	    is_last_use(ins.a))
		return value_reg(fn, ins.a); return temp_reg(ins.dest); }

string MirDumper::compare_rhs(const lowir2cy86::Function& fn,
                   const lowir2cy86::Value& value) {
	if (value.kind == lowir2cy86::ValueKind::Literal) {
		out_ << "    mov rdx, " << value.text << "\n";
		return "rdx";
	} return value_reg(fn, value); }

void MirDumper::dump_branch(const lowir2cy86::Function& fn,
                 const lowir2cy86::Instruction& ins) {
	if (ins.a.kind == lowir2cy86::ValueKind::Temp &&
	    direct_branch_cmp_.find(ins.a.text) != direct_branch_cmp_.end()) {
		const lowir2cy86::Instruction& cmp = *definitions_[ins.a.text];
		if (lowir2cy86::is_float_type(cmp.type)) {
			dump_float_branch(fn, cmp, ins.target, ins.target_false);
			return;
		}
		if (cmp.b.kind == lowir2cy86::ValueKind::Literal &&
		    literal_needs_reg(cmp.b.text)) {
			const string src = value_reg(fn, cmp.a);
			if (src != "rax")
				out_ << "    mov rax, " << src << "\n";
			out_ << "    mov rdx, " << cmp.b.text << "\n";
			out_ << "    cmp." << cmp.type.text << " rax, rdx\n";
			dump_conditional_branch(branch_suffix(cmp.op),
			                        ins.target, ins.target_false, ins.debug);
			return;
		}
		const string lhs = direct_cmp_lhs(fn, cmp);
		const string rhs = direct_cmp_rhs(fn, cmp);
		out_ << "    cmp." << cmp.type.text << " " << lhs << ", "
		     << rhs << "\n";
		dump_conditional_branch(branch_suffix(cmp.op),
		                        ins.target, ins.target_false, ins.debug);
		return;
	}
	if (ins.a.kind == lowir2cy86::ValueKind::Temp &&
	    direct_branch_not_.find(ins.a.text) != direct_branch_not_.end()) {
		const lowir2cy86::Instruction& un = *definitions_[ins.a.text];
		string cond = value_reg(fn, un.a);
		if (branch_uses_fresh_call_result(un.a))
			cond = "rax";
		if (optimization_level_ >= 1) {
			out_ << "    test." << un.type.text << " " << cond
			     << ", " << cond << debug_suffix(ins) << "\n";
			dump_conditional_branch("e", ins.target,
			                        ins.target_false, ins.debug);
			return;
		}
		if (cond != "rax")
			out_ << "    mov rax, " << cond << "\n";
		out_ << "    cmp.i64 rax, 0\n";
		out_ << "    je " << ins.target << "\n";
		out_ << "    jmp " << ins.target_false << "\n";
		return;
	}
	string cond = value_reg(fn, ins.a);
	if (branch_uses_fresh_call_result(ins.a))
		cond = "rax";
	if (optimization_level_ >= 1) {
		const lowir2cy86::Type cond_type = mir_lookup_type(fn, ins.a);
		out_ << "    test." << cond_type.text << " " << cond
		     << ", " << cond << debug_suffix(ins) << "\n";
		dump_conditional_branch("ne", ins.target,
		                        ins.target_false, ins.debug);
		return;
	}
	if (cond != "rax")
		out_ << "    mov rax, " << cond << "\n";
	out_ << "    cmp.i64 rax, 0\n";
	out_ << "    jne " << ins.target << "\n";
	out_ << "    jmp " << ins.target_false << "\n"; }

string MirDumper::inverse_branch_suffix(const string& suffix) const {
	if (suffix == "e") return "ne";
	if (suffix == "ne") return "e";
	if (suffix == "l") return "ge";
	if (suffix == "le") return "g";
	if (suffix == "g") return "le";
	if (suffix == "ge") return "l";
	if (suffix == "b") return "ae";
	if (suffix == "be") return "a";
	if (suffix == "a") return "be";
	if (suffix == "ae") return "b";
	return "";
}

void MirDumper::dump_conditional_branch(const string& suffix,
                                        const string& true_target,
                                        const string& false_target,
                                        const string& debug) {
	if (optimization_level_ >= 1 && true_target == current_fallthrough_block_) {
		const string inverse = inverse_branch_suffix(suffix);
		if (!inverse.empty()) {
			out_ << "    j" << inverse << " " << false_target
			     << debug_suffix(debug) << "\n";
			return;
		}
	}
	out_ << "    j" << suffix << " " << true_target
	     << debug_suffix(debug) << "\n";
	if (optimization_level_ < 1 || false_target != current_fallthrough_block_)
		out_ << "    jmp " << false_target << debug_suffix(debug) << "\n";
}

bool MirDumper::branch_uses_fresh_call_result(const lowir2cy86::Value& value) const {
	if (value.kind != lowir2cy86::ValueKind::Temp) return false;
	map<string, const lowir2cy86::Instruction*>::const_iterator it =
	    definitions_.find(value.text);
	return it != definitions_.end() &&
	       it->second->kind == lowir2cy86::InstrKind::Call; }

void MirDumper::dump_float_branch(const lowir2cy86::Function& fn,
                       const lowir2cy86::Instruction& cmp,
                       const string& target,
                       const string& target_false) {
	out_ << "    fcmp." << cmp.type.text << " " << float_value(fn, cmp.a)
	     << ", " << float_value(fn, cmp.b) << "\n";
	if (cmp.op == "ne")
		out_ << "    jp " << target << "\n";
	else
		out_ << "    jp " << target_false << "\n";
	out_ << "    j" << float_branch_suffix(cmp.op) << " " << target << "\n";
	if (optimization_level_ < 1 || target_false != current_fallthrough_block_)
		out_ << "    jmp " << target_false << "\n"; }

string MirDumper::direct_cmp_lhs(const lowir2cy86::Function& fn,
                      const lowir2cy86::Instruction& cmp) {
	if (cmp.a.kind == lowir2cy86::ValueKind::Literal) {
		out_ << "    mov rax, " << cmp.a.text << "\n";
		return "rax";
	}
	if (cmp.a.kind == lowir2cy86::ValueKind::Temp &&
	    post_call_direct_branch_loads_.find(cmp.a.text) !=
	        post_call_direct_branch_loads_.end()) {
		const lowir2cy86::Instruction& load = *definitions_[cmp.a.text];
		out_ << "    load." << load.type.text << " rax, "
		     << frame_temp_mem(fn, cmp.a.text) << "\n";
		return "rax";
	}
	if (cmp.a.kind == lowir2cy86::ValueKind::Temp &&
	    sret_frame_temps_.find(cmp.a.text) !=
	        sret_frame_temps_.end()) {
		out_ << "    load." << cmp.type.text << " rax, "
		     << frame_temp_mem(fn, cmp.a.text) << "\n";
		return "rax";
	}
	if (cmp.a.kind == lowir2cy86::ValueKind::Temp &&
	    direct_branch_loads_.find(cmp.a.text) !=
	        direct_branch_loads_.end()) {
		const lowir2cy86::Instruction& load = *definitions_[cmp.a.text];
		return load_source(fn, load.a);
	}
	return value_reg(fn, cmp.a); }

bool MirDumper::direct_cmp_lhs_is_memory(const lowir2cy86::Instruction& cmp) const {
	return cmp.a.kind == lowir2cy86::ValueKind::Temp &&
	       direct_branch_loads_.find(cmp.a.text) !=
	           direct_branch_loads_.end(); }

string MirDumper::direct_cmp_rhs(const lowir2cy86::Function& fn,
                      const lowir2cy86::Instruction& cmp) {
	if (cmp.b.kind == lowir2cy86::ValueKind::Temp &&
	    post_call_direct_branch_loads_.find(cmp.b.text) !=
	        post_call_direct_branch_loads_.end()) {
		const lowir2cy86::Instruction& load = *definitions_[cmp.b.text];
		out_ << "    load." << load.type.text << " rdx, "
		     << frame_temp_mem(fn, cmp.b.text) << "\n";
		return "rdx";
	}
	if (cmp.b.kind == lowir2cy86::ValueKind::Temp &&
	    sret_frame_temps_.find(cmp.b.text) !=
	        sret_frame_temps_.end()) {
		out_ << "    load." << cmp.type.text << " rdx, "
		     << frame_temp_mem(fn, cmp.b.text) << "\n";
		return "rdx";
	}
	if (cmp.b.kind == lowir2cy86::ValueKind::Temp &&
	    direct_branch_loads_.find(cmp.b.text) !=
	        direct_branch_loads_.end()) {
		const lowir2cy86::Instruction& load = *definitions_[cmp.b.text];
		return load_source(fn, load.a);
	}
	if (direct_cmp_lhs_is_memory(cmp) &&
	    cmp.b.kind == lowir2cy86::ValueKind::Literal)
		return cmp.b.text;
	if (cmp.b.kind == lowir2cy86::ValueKind::Literal &&
	    lowir2cy86::is_integer_type(cmp.type) && cmp.type.bits < 32) {
		out_ << "    mov rdx, " << cmp.b.text << "\n";
		return "rdx";
	}
	return cmp.b.kind == lowir2cy86::ValueKind::Literal
	           ? cmp.b.text
	           : value_reg(fn, cmp.b); }

}  // namespace lowir2native
