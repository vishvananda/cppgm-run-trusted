#include "lowir2native_mir_dumper.h"

namespace lowir2native {

void MirDumper::dump_atomic(const lowir2cy86::Function& fn,
                 const lowir2cy86::Instruction& ins) {
	const string dst = ins.has_dest ? temp_reg(ins.dest) : "rax";
	if (ins.kind == lowir2cy86::InstrKind::AtomicExchange) {
		const string ptr = value_reg(fn, ins.a);
		const string src = value_reg(fn, ins.b);
		out_ << "    mov rax, " << src << "\n";
		out_ << "    xchg." << ins.type.text << " [" << ptr << "], rax\n";
		if (can_reuse_written_value(ins.b))
			remember_reload(ptr, src, true); } else if (ins.kind == lowir2cy86::InstrKind::AtomicAddFetch) {
		out_ << "    mov rcx, " << value_reg(fn, ins.a) << "\n";
		out_ << "    mov rdx, " << value_reg(fn, ins.b) << "\n";
		out_ << "    mov rax, " << value_reg(fn, ins.b) << "\n";
		out_ << "    lock_xadd." << ins.type.text << " [rcx], rax\n";
		out_ << "    add rax, rdx\n"; } else
		dump_atomic_compare_exchange(fn, ins);
	if (ins.has_dest) {
		out_ << "    mov " << dst << ", rax\n";
		if (ins.kind != lowir2cy86::InstrKind::AtomicCompareExchange)
			dump_narrow_extend(ins.type, dst);
		if (ins.kind != lowir2cy86::InstrKind::AtomicCompareExchange)
			prefer_r8_literal_ = true;
		if (ins.kind == lowir2cy86::InstrKind::AtomicCompareExchange)
			prefer_r8_stack_load_ = true;
	} }

void MirDumper::dump_atomic_compare_exchange(const lowir2cy86::Function& fn,
                                  const lowir2cy86::Instruction& ins) {
	const string ptr = value_reg(fn, ins.a);
	out_ << "    mov rcx, " << ptr << "\n";
	dump_expected_pointer(fn, ins.b);
	out_ << "    load." << ins.type.text << " rax, [rdx]\n";
	const string desired = value_reg(fn, ins.c);
	out_ << "    mov rsi, " << desired << "\n";
	out_ << "    lock_cmpxchg." << ins.type.text << " [rcx], rsi\n";
	out_ << "    store." << ins.type.text << " [rdx], rax\n";
	out_ << "    sete rax\n";
	out_ << "    movzx rax, rax\n";
	if (can_reuse_written_value(ins.c))
		remember_reload(ptr, desired, false); }

void MirDumper::dump_expected_pointer(const lowir2cy86::Function& fn,
                           const lowir2cy86::Value& value) {
	const lowir2cy86::Instruction* addr = inline_addr_definition(value);
	if (addr != nullptr) {
		const string op =
		    addr->a.kind == lowir2cy86::ValueKind::Global ? "mov" : "lea";
		out_ << "    " << op << " rdx, " << value_reg(fn, addr->a) << "\n";
		return;
	}
	out_ << "    mov rdx, " << value_reg(fn, value) << "\n"; }

const lowir2cy86::Instruction* MirDumper::inline_addr_definition(
    const lowir2cy86::Value& value) const {
	if (value.kind != lowir2cy86::ValueKind::Temp ||
	    inline_atomic_expected_addrs_.find(value.text) ==
	        inline_atomic_expected_addrs_.end())
		return nullptr;
	map<string, const lowir2cy86::Instruction*>::const_iterator it =
	    definitions_.find(value.text);
	if (it == definitions_.end()) return nullptr; return it->second; }

bool MirDumper::can_reuse_written_value(const lowir2cy86::Value& value) const {
	if (value.kind != lowir2cy86::ValueKind::Temp) return false;
	map<string, int>::const_iterator it = use_counts_.find(value.text); return it == use_counts_.end() || it->second <= 1; }

void MirDumper::dump_switch(const lowir2cy86::Function& fn,
                 const lowir2cy86::Instruction& ins) {
	out_ << "    mov rax, " << value_reg(fn, ins.a) << "\n";
	for (size_t i = 0; i < ins.switch_cases.size(); ++i) {
		out_ << "    mov rcx, " << value_reg(fn, ins.switch_cases[i].value)
		     << "\n";
		out_ << "    cmp.i64 rax, rcx\n";
		out_ << "    je " << ins.switch_cases[i].target << "\n";
	}
	out_ << "    jmp " << ins.target << "\n"; }

void MirDumper::dump_return(const lowir2cy86::Function& fn,
                 const lowir2cy86::Instruction& ins) {
	if (lowir2cy86::is_void_type(ins.type)) {
		out_ << "    ret" << debug_suffix(ins) << "\n";
		return;
	}
	if (lowir2cy86::is_f80_type(ins.type)) {
		out_ << "    fret.f80 " << mir_f80_value(fn, ins.a, omitted_slots_)
		     << debug_suffix(ins) << "\n";
		return;
	}
	if (mir_is_xmm_type(ins.type)) {
		if (lowir2cy86::is_f80_type(mir_lookup_type(fn, ins.a))) {
			out_ << "    fptrunc.f80." << ins.type.text << " xmm0, "
			     << mir_f80_value(fn, ins.a, omitted_slots_) << "\n";
			out_ << "    ret" << debug_suffix(ins) << "\n";
			return;
		}
		const string src = float_value(fn, ins.a);
		out_ << "    fmov." << ins.type.text << " xmm0, " << src
		     << debug_suffix(ins) << "\n";
		out_ << "    ret" << debug_suffix(ins) << "\n";
		return;
	}
	if (lowir2cy86::is_obj_type(ins.type)) {
		const string type = direct_object_chunk_type(ins.type);
		if (!type.empty() &&
		    (ins.a.kind == lowir2cy86::ValueKind::Slot ||
		     inline_addr_definition_for_direct_object(ins.a) != nullptr)) {
			dump_address_value_to_reg(fn, ins.a, "r11");
			out_ << "    load." << type << " rax, [r11]\n";
		} else {
			const string src = value_reg(fn, ins.a);
			if (src != "rax")
				out_ << "    mov rax, " << src << "\n";
		}
		out_ << "    ret" << debug_suffix(ins) << "\n";
		return;
	}
	if (is_param_slot_value(fn, ins.a)) {
		out_ << "    load." << ins.type.text << " rax, "
		     << param_slot_mem(fn, ins.a) << "\n";
		dump_narrow_extend(ins.type, "rax");
		out_ << "    ret rax" << debug_suffix(ins) << "\n";
		return;
	}
	const string src = value_reg(fn, ins.a);
	if (src != "rax")
	{
		if (optimization_level_ >= 1 && !is_memory_operand(src) &&
		    ins.a.kind != lowir2cy86::ValueKind::Literal) {
			out_ << "    ret " << src << debug_suffix(ins) << "\n";
			return;
		}
		out_ << "    mov rax, " << src << debug_suffix(ins) << "\n";
	}
	out_ << "    ret rax" << debug_suffix(ins) << "\n";
}

}  // namespace lowir2native
