#include "lowir2native_mir_dumper.h"

namespace lowir2native {

void MirDumper::dump_store(const lowir2cy86::Function& fn,
                const lowir2cy86::Instruction& ins) {
		if (ins.a.kind == lowir2cy86::ValueKind::Temp &&
		    global_store_addrs_.find(ins.a.text) != global_store_addrs_.end()) {
			dump_global_addr_store(fn, ins);
			return;
		}
		if (ins.a.kind == lowir2cy86::ValueKind::Temp &&
		    store_source_addrs_.find(ins.a.text) != store_source_addrs_.end()) {
			const string dst = store_dest(fn, ins.b);
			const lowir2cy86::Instruction& addr = *definitions_[ins.a.text];
			dump_address_to_reg(fn, addr.a, "rax");
			out_ << "    store." << ins.type.text << " " << dst
			     << ", rax\n";
			return;
		}
		if (mir_is_xmm_type(ins.type)) {
			const string dst = store_dest(fn, ins.b);
			out_ << "    fmov." << ins.type.text << " " << dst
		     << ", " << float_value(fn, ins.a) << "\n";
		return;
	}
	if (lowir2cy86::is_f80_type(ins.type) &&
	    mir_is_xmm_type(mir_lookup_type(fn, ins.a))) {
		const lowir2cy86::Type src_type = mir_lookup_type(fn, ins.a);
		const string dst = store_dest(fn, ins.b);
		out_ << "    fpext." << src_type.text << ".f80 "
		     << dst << ", " << float_value(fn, ins.a)
		     << "\n";
		return;
	}
	if (ins.b.kind == lowir2cy86::ValueKind::Global &&
	    is_thread_local_global(ins.b.text)) {
		if (ins.a.kind == lowir2cy86::ValueKind::Temp &&
		    tls_pressure_frame_temps_.find(ins.a.text) !=
		        tls_pressure_frame_temps_.end()) {
			const string scratch = call_spill_mem(fn, 0);
			out_ << "    load." << ins.type.text << " rax, "
			     << frame_temp_mem(fn, ins.a.text) << "\n";
			out_ << "    store." << ins.type.text << " "
			     << scratch << ", rax\n";
			out_ << "    tls_addr r11, "
			     << tls_wrapper_for_global(ins.b.text) << "\n";
			out_ << "    load." << ins.type.text << " rax, "
			     << scratch << "\n";
			out_ << "    store." << ins.type.text << " [r11], rax\n";
			return;
		}
		string src = value_reg(fn, ins.a);
		if (ins.a.kind == lowir2cy86::ValueKind::Temp &&
		    tls_store_sources_.find(ins.a.text) != tls_store_sources_.end() &&
		    src != "r12") {
			out_ << "    mov r12, " << src << "\n";
			src = "r12";
		}
		out_ << "    tls_addr r11, "
		     << tls_wrapper_for_global(ins.b.text) << "\n";
		out_ << "    store." << ins.type.text << " [r11], "
		     << src << "\n";
		return;
	}
	if (ins.a.kind == lowir2cy86::ValueKind::Literal &&
	    lowir2cy86::is_integer_type(ins.type)) {
		lowir2cy86::Value dst_value = promoted_store_dest(ins.b);
		if (dst_value.kind == lowir2cy86::ValueKind::Temp &&
		    param_index(fn, dst_value.text) >= 0 &&
		    lowir2cy86::is_ptr_type(mir_lookup_type(fn, dst_value))) {
			const string dst = store_dest(fn, ins.b);
			out_ << "    mov rax, " << ins.a.text
			     << debug_suffix(ins) << "\n";
			out_ << "    store." << ins.type.text << " " << dst
			     << ", rax" << debug_suffix(ins) << "\n";
			return;
		}
		const bool preemitted =
		    ins.b.kind == lowir2cy86::ValueKind::Temp &&
		    preemitted_store_literal_addrs_.find(ins.b.text) !=
		        preemitted_store_literal_addrs_.end();
		const lowir2cy86::Instruction* folded_addr =
		    optimized_addr_definition(ins.b);
		if (!preemitted)
			out_ << "    mov rax, " << ins.a.text
			     << debug_suffix(ins) << "\n";
		const string dst = store_dest(fn, ins.b);
		out_ << "    store." << ins.type.text << " " << dst
		     << ", rax" << debug_suffix(ins) << "\n";
		if (!preemitted && folded_addr != nullptr && past_call_in_block_)
			dump_addr(fn, *folded_addr, ins.debug);
		return;
	}
	if (ins.a.kind == lowir2cy86::ValueKind::Literal &&
	    lowir2cy86::is_ptr_type(ins.type)) {
		out_ << "    mov rax, " << ins.a.text << "\n";
		const string dst = store_dest(fn, ins.b);
		out_ << "    store." << ins.type.text << " " << dst
		     << ", rax\n";
		return;
	}
	if (sret_constructor_like(fn) &&
	    ins.a.kind == lowir2cy86::ValueKind::Temp) {
		const lowir2cy86::Type src_type = mir_lookup_type(fn, ins.a);
		if (lowir2cy86::is_integer_type(src_type) &&
		    lowir2cy86::is_integer_type(ins.type) &&
		    src_type.bits < ins.type.bits) {
			map<string, string>::const_iterator fit =
			    fixed_temp_regs_.find(ins.a.text);
			if (fit != fixed_temp_regs_.end() && fit->second == "r15") {
				out_ << "    mov rax, r15\n";
				const string dst = store_dest(fn, ins.b);
				out_ << "    store." << ins.type.text << " " << dst
				     << ", rax\n";
				return;
			}
			const string src = value_reg(fn, ins.a);
			if (src == "r15") {
				const string dst = store_dest(fn, ins.b);
				out_ << "    mov rax, r15\n";
				out_ << "    store." << ins.type.text << " " << dst
				     << ", rax\n";
				return;
			}
			if (is_memory_operand(src))
				out_ << "    load." << src_type.text
				     << " r15, " << src << "\n";
			else
				out_ << "    mov r15, " << src << "\n";
			dump_narrow_extend(src_type, "r15");
			out_ << "    mov rax, r15\n";
			const string dst = store_dest(fn, ins.b);
			out_ << "    store." << ins.type.text << " " << dst
			     << ", rax\n";
			return;
		}
	}
	if (ins.a.kind == lowir2cy86::ValueKind::Temp &&
	    sret_frame_temps_.find(ins.a.text) != sret_frame_temps_.end()) {
		const string dst = store_dest(fn, ins.b);
		out_ << "    load." << ins.type.text << " rax, "
		     << frame_temp_mem(fn, ins.a.text) << "\n";
		out_ << "    store." << ins.type.text << " " << dst
		     << ", rax\n";
		return;
	}
	if (ins.b.kind == lowir2cy86::ValueKind::Temp &&
	    sret_frame_temps_.find(ins.b.text) != sret_frame_temps_.end()) {
		const lowir2cy86::Type src_type = mir_lookup_type(fn, ins.a);
		const bool materialized_source =
		    ins.a.kind == lowir2cy86::ValueKind::Temp &&
		    reference_store_source_temps_.find(ins.a.text) !=
		        reference_store_source_temps_.end() &&
		    fixed_temp_regs_.find(ins.a.text) != fixed_temp_regs_.end();
		string src = value_reg(fn, ins.a);
		if (lowir2cy86::is_integer_type(src_type)) {
			if (is_memory_operand(src))
				out_ << "    load." << src_type.text << " r15, "
				     << src << "\n";
			else if (src != "r15")
				out_ << "    mov r15, " << src << "\n";
			if (src_type.bits < 64 &&
			    !materialized_source &&
			    !(ins.a.kind == lowir2cy86::ValueKind::Temp &&
			      definitions_.find(ins.a.text) != definitions_.end() &&
			      definitions_.find(ins.a.text)->second->kind ==
			          lowir2cy86::InstrKind::Cmp))
				dump_narrow_extend(src_type, "r15");
			out_ << "    mov rax, r15\n";
			src = "rax";
		} else if (is_memory_operand(src)) {
			out_ << "    load." << src_type.text << " rax, "
			     << src << "\n";
			src = "rax";
		} else if (src == "rcx") {
			out_ << "    mov rax, rcx\n";
			src = "rax";
		}
		if (src != "rax") {
			out_ << "    mov rax, " << src << "\n";
			src = "rax";
		}
		const string dst = store_dest(fn, ins.b);
		out_ << "    store." << ins.type.text << " " << dst
		     << ", " << src << "\n";
		return;
	}
	const string dst = store_dest(fn, ins.b);
	string src = value_reg(fn, ins.a);
	const lowir2cy86::Type src_type = mir_lookup_type(fn, ins.a);
	if (lowir2cy86::is_integer_type(src_type) &&
	    lowir2cy86::is_integer_type(ins.type) &&
	    src_type.bits < ins.type.bits) {
		if (is_memory_operand(src))
			out_ << "    load." << src_type.text << " rax, "
			     << src << "\n";
		else
			out_ << "    mov rax, " << src << "\n";
		dump_narrow_extend(src_type, "rax");
		out_ << "    store." << ins.type.text << " " << dst
		     << ", rax\n";
		return;
	}
	if (is_memory_operand(src)) {
		out_ << "    load." << ins.type.text << " rax, "
		     << src << "\n";
		src = "rax";
	}
	out_ << "    store." << ins.type.text << " " << dst
	     << ", " << src << "\n";
	remember_store_literal(fn, ins.a); }

void MirDumper::dump_global_addr_store(const lowir2cy86::Function& fn,
                            const lowir2cy86::Instruction& ins) {
	const lowir2cy86::Instruction& addr = *definitions_[ins.a.text];
	lowir2cy86::Value dst_value = promoted_store_dest(ins.b);
	if (dst_value.kind == lowir2cy86::ValueKind::Slot ||
	    dst_value.kind == lowir2cy86::ValueKind::Global) {
		out_ << "    mov r8, " << value_reg(fn, addr.a) << "\n";
		out_ << "    store." << ins.type.text << " "
		     << value_reg(fn, dst_value) << ", r8\n";
		remember_store_literal(fn, ins.a);
		return;
	}
	const bool dest_in_rbx = dst_value.kind == lowir2cy86::ValueKind::Temp &&
	    entry_param_regs_.find(dst_value.text) != entry_param_regs_.end() &&
	    entry_param_regs_.find(dst_value.text)->second == "rbx";
	const string dst_reg = dest_in_rbx ? "r8" : "r9";
	const string src_reg = dest_in_rbx ? "r9" : "rbx";
	if (dst_value.kind == lowir2cy86::ValueKind::Temp &&
	    pre_call_param_copies_.find(dst_value.text) != pre_call_param_copies_.end() &&
	    entry_param_regs_.find(dst_value.text) == entry_param_regs_.end())
		out_ << "    mov r8, " << value_reg(fn, dst_value) << "\n";
	const string dst_src = value_reg(fn, dst_value);
	if (dst_reg != dst_src)
		out_ << "    mov " << dst_reg << ", " << dst_src << "\n";
	out_ << "    mov " << src_reg << ", " << value_reg(fn, addr.a) << "\n";
	out_ << "    store." << ins.type.text << " [" << dst_reg << "], "
	     << src_reg << "\n"; }

lowir2cy86::Value MirDumper::promoted_store_dest(const lowir2cy86::Value& value) const {
	if (value.kind != lowir2cy86::ValueKind::Temp) return value;
	map<string, string>::const_iterator it = promoted_loads_.find(value.text);
	if (it == promoted_loads_.end()) return value;
	lowir2cy86::Value param;
	param.kind = lowir2cy86::ValueKind::Temp;
	param.text = it->second;
	return param; }

void MirDumper::remember_store_literal(const lowir2cy86::Function& fn,
                            const lowir2cy86::Value& value) {
	if (can_reuse_written_value(value))
		preferred_literal_reg_ = value_reg(fn, value); }

void MirDumper::dump_scalar(const lowir2cy86::Function& fn,
                 const lowir2cy86::Instruction& ins) {
	if (ins.kind == lowir2cy86::InstrKind::Unary)
		dump_unary(fn, ins);
	else if (ins.kind == lowir2cy86::InstrKind::Binary)
		dump_binary(fn, ins);
	else if (ins.kind == lowir2cy86::InstrKind::Cmp)
		dump_cmp_value(fn, ins);
	else
		dump_convert(fn, ins); }

void MirDumper::dump_unary(const lowir2cy86::Function& fn,
                const lowir2cy86::Instruction& ins) {
	if (sret_frame_temps_.find(ins.dest) != sret_frame_temps_.end() &&
	    ins.op == "decay") {
		if (ins.a.kind == lowir2cy86::ValueKind::Temp &&
		    sret_frame_temps_.find(ins.a.text) !=
		        sret_frame_temps_.end())
			out_ << "    load.ptr rax, "
			     << frame_temp_mem(fn, ins.a.text) << "\n";
		else
			out_ << "    mov rax, " << value_reg(fn, ins.a) << "\n";
		out_ << "    store.ptr " << frame_temp_mem(fn, ins.dest)
		     << ", rax\n";
		return;
	}
	const string src = value_reg(fn, ins.a);
	const string dst = is_last_use(ins.a) ? src : temp_reg(ins.dest);
	if (dst != src)
		out_ << "    mov " << dst << ", " << src << "\n";
	if (ins.op == "neg")
		out_ << "    neg " << dst << "\n";
	else if (ins.op == "bitnot")
		out_ << "    not " << dst << "\n";
	else if (ins.op == "bswap") {
		out_ << "    bswap " << dst << "\n";
		if (ins.type.kind == lowir2cy86::TypeKind::UnsignedInt &&
		    ins.type.bits < 64)
			out_ << "    zext.i" << ins.type.bits << " " << dst << "\n"; } else if (ins.op == "not") {
		out_ << "    cmp." << ins.type.text << " " << dst << ", 0\n";
		out_ << "    sete " << dst << "\n";
		out_ << "    movzx " << dst << ", " << dst << "\n";
	}
	if (dst == src && is_last_use(ins.a))
		remember_fixed_temp_reg(ins.dest, dst);
	else
		remember_temp_reg(ins.dest, dst);
}

void MirDumper::dump_convert(const lowir2cy86::Function& fn,
                  const lowir2cy86::Instruction& ins) {
	const string dst = convert_dest(fn, ins);
	if (ins.op == "trunc" &&
	    lowir2cy86::is_signed_integer_type(ins.type) &&
	    ins.type.bits == 32 &&
	    lowir2cy86::is_integer_type(ins.src_type) &&
	    ins.src_type.bits == 64) {
		const string src = convert_source(fn, ins);
		if (src != dst)
			out_ << "    mov " << dst << ", " << src << "\n";
		out_ << "    sext.i32 " << dst << "\n";
		remember_convert_dest(ins, dst);
		return;
	}
	out_ << "    " << ins.op << "." << conversion_type_text(ins.src_type)
	     << "." << conversion_type_text(ins.type) << " " << dst << ", "
	     << convert_source(fn, ins) << "\n";
	remember_convert_dest(ins, dst); }

string MirDumper::conversion_type_text(const lowir2cy86::Type& type) const {
	if (lowir2cy86::is_integer_type(type)) return "i" + to_string(type.bits); return type.text; }

string MirDumper::convert_dest(const lowir2cy86::Function& fn,
                    const lowir2cy86::Instruction& ins) {
	if (lowir2cy86::is_float_type(ins.type) && !lowir2cy86::is_f80_type(ins.type))
		return xmm_reg(ins.dest);
	if (lowir2cy86::is_integer_type(ins.type)) {
		map<string, string>::const_iterator mit =
		    mixed_convert_regs_.find(ins.dest);
		if (mit != mixed_convert_regs_.end())
			return mit->second;
		const string origin = integer_roundtrip_origin(fn, ins);
		if (!origin.empty())
			return origin;
		if (ins.op == "trunc" &&
		    lowir2cy86::is_signed_integer_type(ins.type) &&
		    ins.type.bits == 32 &&
		    lowir2cy86::is_integer_type(ins.src_type) &&
		    ins.src_type.bits == 64)
			return "r9";
	}
	if (lowir2cy86::is_float_type(ins.type)) {
		lowir2cy86::Value dest;
		dest.kind = lowir2cy86::ValueKind::Temp;
		dest.text = ins.dest;
		return mir_f80_value(fn, dest, omitted_slots_);
	} return temp_reg(ins.dest); }

string MirDumper::convert_source(const lowir2cy86::Function& fn,
                      const lowir2cy86::Instruction& ins) {
	if (lowir2cy86::is_float_type(ins.src_type) &&
	    !lowir2cy86::is_f80_type(ins.src_type))
		return float_value(fn, ins.a);
	if (lowir2cy86::is_f80_type(ins.src_type)) return mir_f80_value(fn, ins.a, omitted_slots_);
	if (ins.a.kind == lowir2cy86::ValueKind::Temp &&
	    convert_call_results_.find(ins.a.text) !=
	        convert_call_results_.end())
		return "rax";
	return value_reg(fn, ins.a); }

void MirDumper::remember_convert_dest(const lowir2cy86::Instruction& ins,
                           const string& dst) {
	if (lowir2cy86::is_f80_type(ins.type)) return;
	if (lowir2cy86::is_float_type(ins.type) && !lowir2cy86::is_f80_type(ins.type))
		remember_xmm_reg(ins.dest, dst);
	else
		remember_temp_reg(ins.dest, dst); }

string MirDumper::integer_roundtrip_origin(const lowir2cy86::Function& fn,
                                const lowir2cy86::Instruction& ins) {
	if (ins.a.kind != lowir2cy86::ValueKind::Temp) return "";
	map<string, const lowir2cy86::Instruction*>::const_iterator it =
	    definitions_.find(ins.a.text);
	if (it == definitions_.end() || it->second->kind != lowir2cy86::InstrKind::Convert) return "";
	const lowir2cy86::Instruction& src = *it->second;
	if (src.a.kind != lowir2cy86::ValueKind::Temp) return ""; return value_reg(fn, src.a); }

}  // namespace lowir2native
