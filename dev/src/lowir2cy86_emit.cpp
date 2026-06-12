#include "lowir2cy86.h"
#include "lowir2cy86_emit_helpers.h"
#include "lowir2cy86_runtime_emit.h"
#include <sstream>
#include <stdexcept>
#include <cstdlib>
#include <limits>
using namespace std;
namespace lowir2cy86 {
namespace {
string stack_mem(size_t offset) {
	return "[bp-" + to_string(offset) + "]"; }
string stack_arg_mem(size_t index) {
	return "[bp+" + to_string(16 + index * 8) + "]"; }
string reg_name(const string& base, int width) {
	if (width == 8 || width == 16 || width == 32 || width == 64)
		return base + to_string(width);
	throw runtime_error("invalid register width"); }
string mem_reg(const string& base, int addend) {
	if (addend == 0)
		return "[" + base + "64]";
	if (addend > 0)
		return "[" + base + "64+" + to_string(addend) + "]";
	return "[" + base + "64" + to_string(addend) + "]"; }
string addend_label(const string& label, int addend) {
	if (addend == 0)
		return label;
	if (addend > 0)
		return "(" + label + "+" + to_string(addend) + ")";
	return "(" + label + to_string(addend) + ")"; }
string f80_return_mem() {
	return "[g____cppgm_f80_return]"; }
bool is_scalar_int_like(const Type& type) {
	return is_integer_type(type) || is_ptr_type(type); }
bool is_i128_type(const Type& type) {
	return is_integer_type(type) && type.bits == 128; }
string i128_helper_label(const string& op) {
	return function_label("@__cppgm_i128_" + op); }
int register_value_width_bits(const Type& type, bool direct_abi) {
	if (direct_abi && is_direct_object_abi(type))
		return direct_object_abi_width_bits(type);
	return cy86_width_bits(type); }
size_t abi_gpr_slots(const Type& type, bool direct_abi) {
	if (is_f80_type(type))
		return 0;
	if (direct_abi && is_direct_object_abi(type))
		return direct_object_abi_slots(type);
	return 1; }
struct CyEmitter {
	const Program& program;
	ostringstream out;
	int eh_label_counter;
	bool safe_call_argument_order;
	bool native_output;
	explicit CyEmitter(const Program& p, bool safe_order, bool native)
	    : program(p), eh_label_counter(0),
	      safe_call_argument_order(safe_order), native_output(native) {}
	void line(const string& text) { out << '\t' << text << ";\n"; }
	void label(const string& text) { out << text << ":\n"; }
	string finish() {
		emit_start();
		for (size_t i = 0; i < program.functions.size(); ++i) {
			if (!program.functions[i].declaration)
				emit_function_section(program.functions[i]); }
		if (native_output && needs_i128_runtime())
			out << emit_i128_runtime_cy86();
		if (native_output)
			append_required_abi_runtime_cy86(out, program, eh_label_counter);
		if (program.needs_eh_runtime)
			append_eh_runtime_cy86(out, native_output, eh_label_counter);
		for (size_t i = 0; i < program.globals.size(); ++i) {
			if (!program.globals[i].declaration)
				emit_global_section(program.globals[i]); }
		if (native_output)
			append_external_rtti_vtable_stubs_cy86(out, program);
		if (needs_f80_return_global())
			emit_f80_return_global();
		if (program_needs_allocator_runtime(program))
			append_allocator_runtime_globals_cy86(out);
		if (program.needs_eh_runtime)
			append_eh_runtime_globals_cy86(out, native_output);
		return out.str(); }
	bool needs_i128_runtime() const {
		for (size_t i = 0; i < program.functions.size(); ++i) {
			const Function& fn = program.functions[i];
			for (size_t b = 0; b < fn.blocks.size(); ++b)
				for (size_t j = 0; j < fn.blocks[b].instructions.size(); ++j) {
					const Instruction& ins = fn.blocks[b].instructions[j];
					if ((ins.kind == InstrKind::Binary ||
					     ins.kind == InstrKind::Cmp ||
					     ins.kind == InstrKind::Unary) &&
					    is_i128_type(ins.type))
						return true; } }
		return false; }
	void emit_start() {
		label("start");
		line("move64 bp sp");
		if (!program.init_function.empty())
			line("call " + function_label(program.init_function));
		line("call " + function_label(program.entry_function));
		if (!program.fini_function.empty()) {
			line("isub64 sp sp 8");
			line("move64 [sp] x64");
			line("call " + function_label(program.fini_function));
			line("move64 x64 [sp]");
			line("iadd64 sp sp 8"); }
		line("syscall1 t64 60 x64");
		out << "\n"; }
	void emit_function_section(const Function& fn) {
		label(function_label(fn.name));
		emit_prologue(fn);
		for (size_t i = 0; i < fn.blocks.size(); ++i)
			emit_block(fn, fn.blocks[i]);
		label(function_label(fn.name) + "__epilogue");
		line("move64 sp bp");
		line("move64 bp [sp]");
		line("iadd64 sp sp 8");
		line("ret");
		out << "\n"; }
	void emit_prologue(const Function& fn) {
		line("isub64 sp sp 8");
		line("move64 [sp] bp");
		line("move64 bp sp");
		if (fn.stack_size != 0)
			line("isub64 sp sp " + to_string(fn.stack_size));
		emit_parameter_saves(fn); }
	void emit_parameter_saves(const Function& fn) {
		size_t reg_index = 0;
		size_t f80_index = 0;
		if (fn.hidden_result_offset != 0) {
			line("move64 " + stack_mem(fn.hidden_result_offset) + " x64");
			++reg_index; }
		for (size_t i = 0; i < fn.params.size(); ++i) {
			const string dst = stack_mem(fn.params[i].offset);
			if (is_f80_type(fn.params[i].type)) {
				line("move80 " + dst + " " + stack_arg_mem(f80_index * 2));
				++f80_index;
				continue; }
			if (native_output && is_direct_object_abi(fn.params[i].type)) {
				emit_direct_object_parameter_save(fn.params[i], reg_index);
				reg_index += direct_object_abi_slots(fn.params[i].type);
				continue; }
			const int width = register_value_width_bits(fn.params[i].type,
			                                            native_output);
			if (reg_index < 4)
				line("move" + to_string(width) + " " + dst + " " +
				     reg_name(arg_reg(reg_index), width));
			else {
				line("move64 x64 " + stack_arg_mem(reg_index - 4));
				line("move" + to_string(width) + " " + dst + " " +
				     reg_name("x", width)); }
			++reg_index; } }
	void emit_direct_object_parameter_save(const Parameter& param, size_t reg_index) {
		for (size_t chunk = 0; chunk < direct_object_abi_slots(param.type); ++chunk) {
			const int width = direct_object_abi_chunk_width_bits(param.type, chunk);
			const string dst = stack_mem(param.offset - chunk * 8);
			if (reg_index + chunk < 4) {
				line("move" + to_string(width) + " " + dst + " " +
				     reg_name(arg_reg(reg_index + chunk), width)); }
			else {
				line("move64 x64 " + stack_arg_mem(reg_index + chunk - 4));
				line("move" + to_string(width) + " " + dst + " " +
				     reg_name("x", width)); }
		} }
	void emit_block(const Function& fn, const Block& block) {
		label(function_label(fn.name) + "__" + lowir_symbol_body(block.name));
		for (size_t i = 0; i < block.instructions.size(); ++i)
			emit_instruction(fn, block.instructions[i]); }
	void emit_instruction(const Function& fn, const Instruction& ins) {
		switch (ins.kind) {
		case InstrKind::Const:
			emit_const(fn, ins);
			break;
		case InstrKind::Copy:
			emit_copy(fn, ins);
			break;
		case InstrKind::Addr:
			emit_addr(fn, ins);
			break;
		case InstrKind::Load:
		case InstrKind::AtomicLoad:
			emit_load(fn, ins);
			break;
		case InstrKind::Store:
		case InstrKind::AtomicStore:
			emit_store(fn, ins);
			break;
		case InstrKind::Index:
			emit_index(fn, ins);
			break;
		case InstrKind::CopyObj:
			emit_copyobj(fn, ins);
			break;
		case InstrKind::ZeroInit:
			emit_zeroinit(fn, ins);
			break;
		case InstrKind::Unary:
			emit_unary(fn, ins);
			break;
		case InstrKind::Binary:
			emit_binary(fn, ins);
			break;
		case InstrKind::Cmp:
			emit_cmp(fn, ins);
			break;
		case InstrKind::Convert:
			emit_convert(fn, ins);
			break;
		case InstrKind::Call:
			emit_call(fn, ins);
			break;
		case InstrKind::VaStart:
		case InstrKind::VaArg:
		case InstrKind::VaEnd:
			throw runtime_error("varargs unsupported by cy86 backend");
		case InstrKind::AtomicExchange:
			emit_atomic_exchange(fn, ins);
			break;
		case InstrKind::AtomicAddFetch:
			emit_atomic_add_fetch(fn, ins);
			break;
		case InstrKind::AtomicCompareExchange:
			emit_atomic_compare_exchange(fn, ins);
			break;
		case InstrKind::AtomicThreadFence:
		case InstrKind::AtomicSignalFence:
			break;
		case InstrKind::EhTry:
			emit_eh_push(fn, ins.target);
			break;
		case InstrKind::EhCleanup:
			if (!ins.target.empty())
				emit_eh_push(fn, ins.target);
			break;
		case InstrKind::EhCatch:
			emit_eh_catch(ins);
			break;
		case InstrKind::EhCatchAll:
			emit_eh_catch_all(ins);
			break;
		case InstrKind::EhEnd:
			emit_eh_end();
			break;
		case InstrKind::Throw:
			emit_throw(fn, ins);
			break;
		case InstrKind::Exception:
		case InstrKind::ExceptionSelector:
			emit_exception(fn, ins);
			break;
		case InstrKind::Resume:
			emit_eh_dispatch();
			break;
		case InstrKind::Jump:
			line("jump " + block_label(fn, ins.target));
			break;
		case InstrKind::Branch:
			emit_branch(fn, ins);
			break;
		case InstrKind::Switch:
			emit_switch(fn, ins);
			break;
		case InstrKind::Return:
			emit_return(fn, ins);
			break; } }
	string arg_reg(size_t index) const {
		static const char* const regs[] = {"x", "y", "z", "t"};
		return regs[index]; }
	string block_label(const Function& fn, const string& block) const {
		return function_label(fn.name) + "__" + lowir_symbol_body(block); }
	Type lookup_value_type(const Function& fn, const Value& value) const {
		if (value.kind == ValueKind::Temp) {
			map<string, Type>::const_iterator pit = fn.param_types.find(value.text);
			if (pit != fn.param_types.end())
				return pit->second;
			return fn.temp_types.find(value.text)->second; }
		if (value.kind == ValueKind::Slot)
			return fn.slot_types.find(value.text)->second;
		if (value.kind == ValueKind::Global) {
			map<string, size_t>::const_iterator it = program.global_by_name.find(value.text);
			const Global& global = program.globals[it->second];
			return global.has_type ? global.type : parse_type_text("ptr"); }
		if (value.kind == ValueKind::Function)
			return parse_type_text("ptr");
		return Type(); }
	size_t lookup_offset(const Function& fn, const Value& value) const {
		if (value.kind == ValueKind::Temp) {
			map<string, size_t>::const_iterator pit = fn.param_offsets.find(value.text);
			if (pit != fn.param_offsets.end())
				return pit->second;
			return fn.temp_offsets.find(value.text)->second; }
		return fn.slot_offsets.find(value.text)->second; }
	void emit_const(const Function& fn, const Instruction& ins) {
		if (is_f80_type(ins.type)) {
			line("move80 " + stack_mem(fn.temp_offsets.find(ins.dest)->second) +
			     " " + ins.a.text);
			return; }
		emit_literal_to_reg(ins.type, ins.a.text, "x");
		emit_store_reg_to_temp(fn, ins.dest, ins.type, "x"); }
	void emit_copy(const Function& fn, const Instruction& ins) {
		if (native_output && is_direct_object_abi(ins.type) &&
		    direct_object_abi_slots(ins.type) > 1) {
			emit_direct_object_copy_to_temp(fn, ins.a, ins.dest, ins.type);
			return; }
		emit_value_to_reg(fn, ins.a, ins.type, "x");
		emit_store_reg_to_temp(fn, ins.dest, ins.type, "x"); }
	void emit_addr(const Function& fn, const Instruction& ins) {
		emit_address_to_reg(fn, ins.a, "x");
		emit_store_reg_to_temp(fn, ins.dest, parse_type_text("ptr"), "x"); }
	void emit_load(const Function& fn, const Instruction& ins) {
		if (is_f80_type(ins.type)) {
			emit_f80_load(fn, ins);
			return; }
		if (native_output && is_direct_object_abi(ins.type) &&
		    direct_object_abi_slots(ins.type) > 1) {
			emit_direct_object_load(fn, ins);
			return; }
		if (ins.kind == InstrKind::AtomicLoad) {
			emit_value_to_reg(fn, ins.a, parse_type_text("ptr"), "y");
			emit_load_mem_to_reg(mem_reg("y", 0), ins.type, ins.type, "x");
			emit_store_reg_to_temp(fn, ins.dest, ins.type, "x");
			return; }
		if (ins.a.kind == ValueKind::Global)
			emit_load_mem_to_reg(global_mem(ins.a.text), ins.type, ins.type, "x");
		else if (ins.a.kind == ValueKind::Slot)
			emit_load_mem_to_reg(stack_mem(lookup_offset(fn, ins.a)),
			                     lookup_value_type(fn, ins.a), ins.type, "x");
		else {
			const string base = native_output && is_scalar_int_like(ins.type) &&
			                            cy86_width_bits(ins.type) < 32
			                        ? "y"
			                        : "x";
			emit_value_to_reg(fn, ins.a, parse_type_text("ptr"), base);
			emit_load_mem_to_reg(mem_reg(base, 0), ins.type, ins.type, "x"); }
		emit_store_reg_to_temp(fn, ins.dest, ins.type, "x"); }
	void emit_store(const Function& fn, const Instruction& ins) {
		if (is_f80_type(ins.type)) {
			emit_f80_store(fn, ins);
			return; }
		if (native_output && is_direct_object_abi(ins.type) &&
		    direct_object_abi_slots(ins.type) > 1) {
			emit_direct_object_store(fn, ins);
			return; }
		if (ins.kind == InstrKind::AtomicStore) {
			emit_value_to_reg(fn, ins.b, parse_type_text("ptr"), "y");
			emit_value_to_reg(fn, ins.a, ins.type, "x");
			emit_store_reg_to_mem(mem_reg("y", 0), ins.type, "x");
			return; }
		emit_value_to_reg(fn, ins.a, ins.type, "x");
		if (ins.b.kind == ValueKind::Global)
			emit_store_reg_to_mem(global_mem(ins.b.text), ins.type, "x");
		else if (ins.b.kind == ValueKind::Slot)
			emit_store_reg_to_mem(stack_mem(lookup_offset(fn, ins.b)), ins.type, "x");
		else {
			emit_value_to_reg(fn, ins.b, parse_type_text("ptr"), "y");
			emit_store_reg_to_mem(mem_reg("y", 0), ins.type, "x"); } }
	void emit_direct_object_load(const Function& fn, const Instruction& ins) {
		if (ins.a.kind == ValueKind::Global)
			line("move64 y64 " + global_label(ins.a.text));
		else if (ins.a.kind == ValueKind::Slot)
			emit_address_to_reg(fn, ins.a, "y");
		else
			emit_value_to_reg(fn, ins.a, parse_type_text("ptr"), "y");
		for (size_t chunk = 0; chunk < direct_object_abi_slots(ins.type); ++chunk) {
			const int width = direct_object_abi_chunk_width_bits(ins.type, chunk);
			if (width < 64)
				line("move64 x64 0");
			line("move" + to_string(width) + " " + reg_name("x", width) +
			     " " + mem_reg("y", static_cast<int>(chunk * 8)));
			line("move" + to_string(width) + " " +
			     stack_mem(fn.temp_offsets.find(ins.dest)->second - chunk * 8) +
			     " " + reg_name("x", width)); } }
	void emit_direct_object_store(const Function& fn, const Instruction& ins) {
		if (ins.b.kind == ValueKind::Global)
			line("move64 y64 " + global_label(ins.b.text));
		else if (ins.b.kind == ValueKind::Slot)
			emit_address_to_reg(fn, ins.b, "y");
		else
			emit_value_to_reg(fn, ins.b, parse_type_text("ptr"), "y");
		for (size_t chunk = 0; chunk < direct_object_abi_slots(ins.type); ++chunk) {
			const int width = direct_object_abi_chunk_width_bits(ins.type, chunk);
			emit_direct_object_chunk_to_reg(fn, ins.a, ins.type, chunk, "x");
			line("move" + to_string(width) + " " +
			     mem_reg("y", static_cast<int>(chunk * 8)) + " " +
			     reg_name("x", width)); } }
	void emit_f80_load(const Function& fn, const Instruction& ins) {
		const string dst = stack_mem(fn.temp_offsets.find(ins.dest)->second);
		if (ins.a.kind == ValueKind::Global)
			line("move80 " + dst + " " + global_mem(ins.a.text));
		else if (ins.a.kind == ValueKind::Slot)
			line("move80 " + dst + " " + stack_mem(lookup_offset(fn, ins.a)));
		else {
			emit_value_to_reg(fn, ins.a, parse_type_text("ptr"), "x");
			line("move80 " + dst + " [x64]"); } }
	void emit_f80_store(const Function& fn, const Instruction& ins) {
		const string src = f80_value_mem(fn, ins.a);
		if (ins.b.kind == ValueKind::Global)
			line("move80 " + global_mem(ins.b.text) + " " + src);
		else if (ins.b.kind == ValueKind::Slot)
			line("move80 " + stack_mem(lookup_offset(fn, ins.b)) + " " + src);
		else {
			emit_value_to_reg(fn, ins.b, parse_type_text("ptr"), "x");
			line("move80 [x64] " + src); } }
	void emit_index(const Function& fn, const Instruction& ins) {
		emit_value_to_reg(fn, ins.a, parse_type_text("ptr"), "y");
		emit_value_to_reg(fn, ins.b, parse_type_text("i64"), "x");
		const size_t elem_size = storage_size(ins.type);
		if (elem_size != 1) {
			line("move64 z64 " + to_string(elem_size));
			line("smul64 x64 x64 z64"); }
		line("iadd64 x64 y64 x64");
		emit_store_reg_to_temp(fn, ins.dest, parse_type_text("ptr"), "x"); }
	void emit_copyobj(const Function& fn, const Instruction& ins) {
		emit_pointer_or_slot_destination_to_reg(fn, ins.b, ins.span, "x");
		emit_object_source_to_reg(fn, ins.a, "y");
		emit_copy_qwords(ins.span.bytes, "y", "x"); }
	void emit_zeroinit(const Function& fn, const Instruction& ins) {
		emit_pointer_or_slot_destination_to_reg(fn, ins.a, ins.span, "x");
		line("move64 z64 0");
		if (ins.span.bytes % 8 == 0) {
			for (size_t off = 0; off < ins.span.bytes; off += 8) {
				if (off != 0)
					line("iadd64 x64 x64 8");
				line("move64 [x64] z64"); }
			return; }
		emit_zero_bytes(ins.span.bytes, "x"); }
	void emit_unary(const Function& fn, const Instruction& ins) {
		if (is_i128_type(ins.type)) {
			emit_i128_unary(fn, ins);
			return; }
		if (is_f80_type(ins.type)) {
			if (ins.op != "neg")
				throw runtime_error("unsupported f80 unary op");
			line("fsub80 " + stack_mem(fn.temp_offsets.find(ins.dest)->second) +
			     " 0.0L " + f80_value_mem(fn, ins.a));
			return; }
		emit_value_to_reg(fn, ins.a, ins.type, "x");
		if (ins.op == "neg") {
			line("move64 y64 0");
			line("isub" + to_string(cy86_width_bits(ins.type)) + " " +
			     reg_name("x", cy86_width_bits(ins.type)) + " " +
			     reg_name("y", cy86_width_bits(ins.type)) + " " +
			     reg_name("x", cy86_width_bits(ins.type))); }
		else if (ins.op == "not")
			emit_logical_not(ins.type, "x");
		else if (ins.op == "bitnot")
			line("not" + to_string(cy86_width_bits(ins.type)) + " " +
			     reg_name("x", cy86_width_bits(ins.type)) + " " +
			     reg_name("x", cy86_width_bits(ins.type)));
		else if (ins.op == "bswap")
			line("bswap" + to_string(cy86_width_bits(ins.type)) + " " +
			     reg_name("x", cy86_width_bits(ins.type)) + " " +
			     reg_name("x", cy86_width_bits(ins.type)));
		else if (ins.op != "decay")
			throw runtime_error("unsupported unary op");
		emit_store_reg_to_temp(fn, ins.dest, ins.type, "x"); }
	void emit_i128_unary(const Function& fn, const Instruction& ins) {
		emit_i128_value_to_register_pair(fn, ins.a, ins.type, "x", "y");
		if (ins.op == "neg") {
			line("not64 x64 x64");
			line("not64 y64 y64");
			line("iadd64 x64 x64 1");
			line("ieq64 z8 x64 0");
			line("move64 t64 0");
			line("move8 t8 z8");
			line("iadd64 y64 y64 t64"); }
		else if (ins.op == "bitnot") {
			line("not64 x64 x64");
			line("not64 y64 y64"); }
		else if (ins.op == "decay") { }
		else
			throw runtime_error("unsupported i128 unary op");
		emit_store_direct_object_registers_to_temp(fn, ins.dest, ins.type, 0); }
	void emit_binary(const Function& fn, const Instruction& ins) {
		if (is_i128_type(ins.type)) {
			emit_i128_binary(fn, ins);
			return; }
		if (is_f80_type(ins.type)) {
			line(binary_opcode(ins) + " " +
			     stack_mem(fn.temp_offsets.find(ins.dest)->second) + " " +
			     f80_value_mem(fn, ins.a) + " " + f80_value_mem(fn, ins.b));
			return; }
		emit_value_to_reg(fn, ins.a, ins.type, "y");
		emit_value_to_reg(fn, ins.b, ins.type, "x");
		if (ins.op == "shl" || ins.op == "shr" || ins.op == "ushr") {
			line("move64 z64 x64");
			line("move8 x8 z8"); }
		line(binary_opcode(ins) + " " + reg_name("x", cy86_width_bits(ins.type)) +
		     " " + reg_name("y", cy86_width_bits(ins.type)) + " " +
		     binary_rhs_reg(ins));
		emit_store_reg_to_temp(fn, ins.dest, ins.type, "x"); }
	void emit_i128_binary(const Function& fn, const Instruction& ins) {
		emit_i128_value_to_register_pair(fn, ins.a, ins.type, "x", "y");
		if (ins.op == "shl" || ins.op == "shr" || ins.op == "ushr") {
			emit_i128_chunk_to_reg(fn, ins.b, ins.type, 0, "z");
			line("call " + i128_helper_label(ins.op));
			emit_store_direct_object_registers_to_temp(fn, ins.dest, ins.type, 0);
			return; }
		emit_i128_value_to_register_pair(fn, ins.b, ins.type, "z", "t");
		if (ins.op == "add") {
			line("iadd64 x64 x64 z64");
			line("ult64 z8 x64 z64");
			line("iadd64 y64 y64 t64");
			line("move64 t64 0");
			line("move8 t8 z8");
			line("iadd64 y64 y64 t64"); }
		else if (ins.op == "sub") {
			line("isub64 sp sp 8");
			line("move64 [sp] t64");
			line("ult64 t8 x64 z64");
			line("isub64 x64 x64 z64");
			line("move64 z64 0");
			line("move8 z8 t8");
			line("move64 t64 [sp]");
			line("isub64 y64 y64 t64");
			line("isub64 y64 y64 z64");
			line("iadd64 sp sp 8"); }
		else if (ins.op == "and" || ins.op == "or" || ins.op == "xor") {
			line(ins.op + "64 x64 x64 z64");
			line(ins.op + "64 y64 y64 t64"); }
		else if (ins.op == "mul")
			line("call " + i128_helper_label("mul"));
		else if (ins.op == "udiv" || ins.op == "div")
			line("call " + i128_helper_label("udiv"));
		else if (ins.op == "umod" || ins.op == "mod")
			line("call " + i128_helper_label("umod"));
		else
			throw runtime_error("unsupported i128 binary op");
		emit_store_direct_object_registers_to_temp(fn, ins.dest, ins.type, 0); }
	string binary_rhs_reg(const Instruction& ins) const {
		if (ins.op == "shl" || ins.op == "shr" || ins.op == "ushr")
			return "x8";
		return reg_name("x", cy86_width_bits(ins.type)); }
	string binary_opcode(const Instruction& ins) const {
		const int w = cy86_width_bits(ins.type);
		if (is_float_type(ins.type))
			return string("f") + float_binary_name(ins.op) + to_string(w);
		if (ins.op == "add")
			return "iadd" + to_string(w);
		if (ins.op == "sub")
			return "isub" + to_string(w);
		if (ins.op == "mul")
			return "smul" + to_string(w);
		if (ins.op == "div")
			return "sdiv" + to_string(w);
		if (ins.op == "mod")
			return "smod" + to_string(w);
		if (ins.op == "udiv")
			return "udiv" + to_string(w);
		if (ins.op == "umod")
			return "umod" + to_string(w);
		if (ins.op == "and" || ins.op == "or" || ins.op == "xor")
			return ins.op + to_string(w);
		if (ins.op == "shl")
			return "lshift" + to_string(w);
		if (ins.op == "shr")
			return "srshift" + to_string(w);
		if (ins.op == "ushr")
			return "urshift" + to_string(w);
		throw runtime_error("unsupported binary op"); }
	string float_binary_name(const string& op) const {
		if (op == "add" || op == "sub" || op == "mul" || op == "div")
			return op;
		throw runtime_error("unsupported float binary op"); }
	void emit_cmp(const Function& fn, const Instruction& ins) {
		if (is_i128_type(ins.type)) {
			emit_i128_cmp(fn, ins);
			return; }
		if (is_f80_type(ins.type)) {
			line(cmp_opcode(ins) + " z8 " + f80_value_mem(fn, ins.a) +
			     " " + f80_value_mem(fn, ins.b));
			line("move64 x64 0");
			line("move8 x8 z8");
			emit_store_reg_to_temp(fn, ins.dest, parse_type_text("i64"), "x");
			return; }
		emit_value_to_reg(fn, ins.a, ins.type, "y");
		emit_value_to_reg(fn, ins.b, ins.type, "x");
		line(cmp_opcode(ins) + " z8 " + reg_name("y", cy86_width_bits(ins.type)) +
		     " " + reg_name("x", cy86_width_bits(ins.type)));
		line("move64 x64 0");
		line("move8 x8 z8");
		emit_store_reg_to_temp(fn, ins.dest, ins.type, "x"); }
	void emit_i128_cmp(const Function& fn, const Instruction& ins) {
		const string true_label = next_label("__i128_cmp_true__");
		const string false_label = next_label("__i128_cmp_false__");
		const string done_label = next_label("__i128_cmp_done__");
		emit_i128_value_to_register_pair(fn, ins.a, ins.type, "x", "y");
		line("isub64 sp sp 16");
		line("move64 [sp] x64");
		line("move64 [sp+8] y64");
		emit_i128_value_to_register_pair(fn, ins.b, ins.type, "z", "t");
		if (ins.op == "eq" || ins.op == "ne") {
			line("ieq64 x8 [sp] z64");
			line("ieq64 y8 [sp+8] t64");
			line("move64 z64 0");
			line("move8 z8 x8");
			line("move64 t64 0");
			line("move8 t8 y8");
			line("and64 x64 z64 t64");
			if (ins.op == "ne") {
				line("ieq64 x8 x64 0");
				line("move64 z64 0");
				line("move8 z8 x8");
				line("move64 x64 z64"); }
			line("iadd64 sp sp 16");
			emit_store_reg_to_temp(fn, ins.dest, parse_type_text("i64"), "x");
			return; }
		const bool unsigned_cmp =
		    ins.op == "ult" || ins.op == "ule" || ins.op == "ugt" || ins.op == "uge";
		string op = ins.op;
		if (unsigned_cmp && op.size() > 1 && op[0] == 'u')
			op = op.substr(1);
		const string lt = unsigned_cmp ? "ult64" : "slt64";
		const string gt = unsigned_cmp ? "ugt64" : "sgt64";
		if (op == "lt" || op == "le") {
			line(gt + " x8 [sp+8] t64");
			line("jumpif x8 " + false_label);
			line(lt + " x8 [sp+8] t64");
			line("jumpif x8 " + true_label);
			if (op == "lt")
				line("ult64 x8 [sp] z64");
			else
				line("ule64 x8 [sp] z64");
			line("jumpif x8 " + true_label);
			line("jump " + false_label); }
		else if (op == "gt" || op == "ge") {
			line(lt + " x8 [sp+8] t64");
			line("jumpif x8 " + false_label);
			line(gt + " x8 [sp+8] t64");
			line("jumpif x8 " + true_label);
			if (op == "gt")
				line("ugt64 x8 [sp] z64");
			else
				line("uge64 x8 [sp] z64");
			line("jumpif x8 " + true_label);
			line("jump " + false_label); }
		else
			throw runtime_error("unsupported i128 cmp op");
		label(true_label);
		line("move64 x64 1");
		line("jump " + done_label);
		label(false_label);
		line("move64 x64 0");
		label(done_label);
		line("iadd64 sp sp 16");
		emit_store_reg_to_temp(fn, ins.dest, parse_type_text("i64"), "x"); }
	string cmp_opcode(const Instruction& ins) const {
		const int w = cy86_width_bits(ins.type);
		if (is_float_type(ins.type))
			return "f" + ins.op + to_string(w);
		if (ins.op == "eq")
			return "ieq" + to_string(w);
		if (ins.op == "ne")
			return "ine" + to_string(w);
		if (ins.op == "lt" || ins.op == "le" || ins.op == "gt" || ins.op == "ge")
			return "s" + ins.op + to_string(w);
		if (ins.op == "ult" || ins.op == "ule" || ins.op == "ugt" || ins.op == "uge")
			return ins.op + to_string(w);
		throw runtime_error("unsupported cmp op"); }
	void emit_logical_not(const Type& type, const string& base) {
		line("ieq" + to_string(cy86_width_bits(type)) + " z8 " +
		     reg_name(base, cy86_width_bits(type)) + " 0");
		line("move64 " + base + "64 0");
		line("move8 " + base + "8 z8"); }
	void emit_branch(const Function& fn, const Instruction& ins) {
		emit_value_to_reg(fn, ins.a, parse_type_text("i64"), "x");
		line("ieq64 z8 x64 0");
		line("jumpif z8 " + block_label(fn, ins.target_false));
		line("jump " + block_label(fn, ins.target)); }
	void emit_switch(const Function& fn, const Instruction& ins) {
		emit_value_to_reg(fn, ins.a, parse_type_text("i64"), "x");
		for (size_t i = 0; i < ins.switch_cases.size(); ++i) {
			emit_value_to_reg(fn, ins.switch_cases[i].value, parse_type_text("i64"), "t");
			line("ieq64 z8 x64 t64");
			line("jumpif z8 " + block_label(fn, ins.switch_cases[i].target)); }
		line("jump " + block_label(fn, ins.target)); }
	void emit_return(const Function& fn, const Instruction& ins) {
		if (native_output && is_direct_object_abi(ins.type))
			emit_direct_object_value_to_registers(fn, ins.a, ins.type, 0);
		else if (is_obj_type(ins.type)) {
			emit_object_source_to_reg(fn, ins.a, "x");
			line("move64 y64 " + stack_mem(fn.hidden_result_offset));
			emit_copy_qwords_offset(ins.type.obj_size, "x", "y"); }
		else if (is_f80_type(ins.type))
			line("move80 " + f80_return_mem() + " " + f80_value_mem(fn, ins.a));
		else if (!is_void_type(ins.type))
			emit_value_to_reg(fn, ins.a, ins.type, "x");
		line("jump " + function_label(fn.name) + "__epilogue"); }
	void emit_call(const Function& fn, const Instruction& ins) {
		vector<Value> args = ins.args;
		vector<Type> arg_types = call_arg_types(ins);
		const bool returns_direct_obj =
		    native_output && is_direct_object_abi(ins.type);
		const bool returns_hidden_obj =
		    is_obj_type(ins.type) && !returns_direct_obj;
		const bool returns_f80 = is_f80_type(ins.type);
		const bool indirect = ins.a.kind != ValueKind::Function;
		const size_t f80_stack = f80_call_stack_bytes(arg_types);
		const size_t gpr_slots = call_gpr_slots(fn, args, arg_types, returns_hidden_obj);
		size_t extra_stack = gpr_slots > 4 ? gpr_slots - 4 : 0;
		if (indirect)
			emit_indirect_callee_save(fn, ins.a);
		if (extra_stack != 0 || f80_stack != 0)
			line("isub64 sp sp " + to_string(extra_stack * 8 + f80_stack));
		if (f80_stack != 0)
			emit_f80_call_arguments(fn, args, arg_types, extra_stack * 8);
		emit_call_arguments(fn, ins, args, arg_types, returns_hidden_obj);
		line(string("call ") + (indirect ? indirect_callee_mem(extra_stack * 8 + f80_stack)
		                                  : function_label(ins.a.text)));
		if (extra_stack != 0 || f80_stack != 0 || indirect)
			line("iadd64 sp sp " +
			     to_string(extra_stack * 8 + f80_stack + (indirect ? 8 : 0)));
		if (ins.has_dest && returns_f80)
			line("move80 " + stack_mem(fn.temp_offsets.find(ins.dest)->second) +
			     " " + f80_return_mem());
		else if (ins.has_dest && returns_direct_obj)
			emit_store_direct_object_registers_to_temp(fn, ins.dest, ins.type, 0);
		else if (ins.has_dest && !returns_hidden_obj && !is_void_type(ins.type))
			emit_store_reg_to_temp(fn, ins.dest, ins.type, "x"); }
	size_t call_gpr_slots(const Function& fn,
	                      const vector<Value>& args,
	                      const vector<Type>& arg_types,
	                      bool returns_obj) const {
		size_t slots = returns_obj ? 1 : 0;
		for (size_t i = 0; i < args.size(); ++i) {
			const Type expected =
			    i < arg_types.size() ? arg_types[i] : lookup_value_type(fn, args[i]);
			slots += abi_gpr_slots(expected, native_output); }
		return slots; }
	size_t f80_call_stack_bytes(const vector<Type>& arg_types) const {
		size_t bytes = 0;
		for (size_t i = 0; i < arg_types.size(); ++i)
			if (is_f80_type(arg_types[i]))
				bytes += 16;
		return bytes; }
	void emit_f80_call_arguments(const Function& fn,
	                             const vector<Value>& args,
	                             const vector<Type>& arg_types,
	                             size_t base_offset) {
		size_t offset = base_offset;
		for (size_t i = 0; i < args.size() && i < arg_types.size(); ++i) {
			if (!is_f80_type(arg_types[i]))
				continue;
			const string mem = offset == 0 ? "[sp]" : "[sp+" + to_string(offset) + "]";
			line("move80 " + mem + " " + f80_value_mem(fn, args[i]));
			offset += 16; } }
	void emit_indirect_callee_save(const Function& fn, const Value& callee) {
		emit_value_to_reg(fn, callee, parse_type_text("ptr"), "x");
		line("isub64 sp sp 8");
		line("move64 [sp] x64"); }
	string indirect_callee_mem(size_t offset) const {
		return offset == 0 ? "[sp]" : "[sp+" + to_string(offset) + "]"; }
	vector<Type> call_arg_types(const Instruction& ins) const {
		vector<Type> out;
		if (ins.signature.present) {
			for (size_t i = 0; i < ins.signature.params.size(); ++i)
				out.push_back(ins.signature.params[i].type);
			return out; }
		map<string, size_t>::const_iterator it = program.function_by_name.find(ins.a.text);
		if (it != program.function_by_name.end()) {
			const Function& callee = program.functions[it->second];
			for (size_t i = 0; i < callee.params.size(); ++i)
				out.push_back(callee.params[i].type); }
		return out; }
	void emit_call_arguments(const Function& fn,
	                         const Instruction& ins,
	                         const vector<Value>& args,
	                         const vector<Type>& arg_types,
	                         bool returns_obj) {
		struct ArgItem {
			size_t arg;
			size_t reg;
			Type type;
		};
		vector<ArgItem> items;
		size_t reg_index = 0;
		if (returns_obj) {
			if (!safe_call_argument_order) {
				emit_temp_address_to_reg(fn, ins.dest, "x");
				line("move64 x64 x64"); }
			reg_index = 1; }
		for (size_t i = 0; i < args.size(); ++i) {
			const Type expected =
			    i < arg_types.size() ? arg_types[i] : lookup_value_type(fn, args[i]);
			if (is_f80_type(expected))
				continue;
			ArgItem item;
			item.arg = i;
			item.reg = reg_index;
			item.type = expected;
			if (!safe_call_argument_order)
				emit_call_argument_item(fn, ins, args, item);
			else
				items.push_back(item);
			reg_index += abi_gpr_slots(expected, native_output); }
		if (!safe_call_argument_order)
			return;
		for (size_t i = 0; i < items.size(); ++i)
			if (items[i].reg >= 4)
				emit_call_argument_item(fn, ins, args, items[i]);
		for (size_t i = 0; i < items.size(); ++i)
			if (items[i].reg > 0 && items[i].reg < 4)
				emit_call_argument_item(fn, ins, args, items[i]);
		if (returns_obj) {
			emit_temp_address_to_reg(fn, ins.dest, "x");
			line("move64 x64 x64"); }
		for (size_t i = 0; i < items.size(); ++i)
			if (items[i].reg == 0)
				emit_call_argument_item(fn, ins, args, items[i]); }
	template <class ArgItem>
	void emit_call_argument_item(const Function& fn,
	                             const Instruction& ins,
	                             const vector<Value>& args,
	                             const ArgItem& item) {
		if (native_output && is_direct_object_abi(item.type)) {
			emit_direct_object_call_argument(fn, args[item.arg], item.type, item.reg);
			return; }
		if (item.reg < 4) {
			emit_call_arg_value_to_reg(fn, ins, item.arg, item.type,
			                           arg_reg(item.reg));
			if (item.reg == 0 && args[item.arg].kind == ValueKind::Slot &&
			    is_ptr_type(item.type))
				line("move64 x64 x64");
			return; }
		emit_call_arg_value_to_reg(fn, ins, item.arg, item.type, "x");
		const size_t stack_index = item.reg - 4;
		const string mem = stack_index == 0 ? "[sp]" :
		                   "[sp+" + to_string(stack_index * 8) + "]";
		line("move64 " + mem + " 0");
		line("move64 " + mem + " x64"); }
	void emit_direct_object_call_argument(const Function& fn,
	                                      const Value& arg,
	                                      const Type& type,
	                                      size_t reg_index) {
		for (size_t chunk = 0; chunk < direct_object_abi_slots(type); ++chunk) {
			const int width = direct_object_abi_chunk_width_bits(type, chunk);
			if (reg_index + chunk < 4) {
				emit_direct_object_chunk_to_reg(fn, arg, type, chunk,
				                                arg_reg(reg_index + chunk));
				continue; }
			const size_t stack_index = reg_index + chunk - 4;
			const string mem = stack_index == 0 ? "[sp]" :
			                   "[sp+" + to_string(stack_index * 8) + "]";
			emit_direct_object_chunk_to_reg(fn, arg, type, chunk, "x");
			line("move64 " + mem + " 0");
			line("move" + to_string(width) + " " + mem + " " +
			     reg_name("x", width)); } }
	void emit_call_arg_value_to_reg(const Function& fn,
	                                const Instruction& ins,
	                                size_t index,
	                                const Type& expected,
	                                const string& base) {
		const Value& arg = ins.args[index];
		if (call_arg_needs_address(ins, index)) {
			const Type actual = lookup_value_type(fn, arg);
			if (arg.kind == ValueKind::Temp && !is_ptr_type(actual)) {
				emit_temp_address_to_reg(fn, arg.text, "x");
				if (base != "x")
					line("move64 " + reg_name(base, 64) + " x64");
				return; }
			if (arg.kind == ValueKind::Slot || arg.kind == ValueKind::Global) {
				emit_address_to_reg(fn, arg, "x");
				if (base != "x")
					line("move64 " + reg_name(base, 64) + " x64");
				return; } }
		emit_value_to_reg(fn, arg, expected, base); }
	bool call_arg_needs_address(const Instruction& ins, size_t index) const {
		const Parameter* param = call_param(ins, index);
		if (param == nullptr || !is_ptr_type(param->type))
			return false;
		const string pass = metadata_value(param->metadata, "pass");
		return pass == "reference" || pass == "indirect_result" ||
		       pass == "by_address" || pass == "decay"; }
	const Parameter* call_param(const Instruction& ins, size_t index) const {
		if (ins.signature.present && index < ins.signature.params.size())
			return &ins.signature.params[index];
		if (ins.a.kind != ValueKind::Function)
			return nullptr;
		map<string, size_t>::const_iterator it =
		    program.function_by_name.find(ins.a.text);
		if (it == program.function_by_name.end())
			return nullptr;
		const Function& callee = program.functions[it->second];
		return index < callee.params.size() ? &callee.params[index] : nullptr; }
	void emit_atomic_exchange(const Function& fn, const Instruction& ins) {
		emit_value_to_reg(fn, ins.a, parse_type_text("ptr"), "y");
		emit_value_to_reg(fn, ins.b, ins.type, "x");
		line("move" + to_string(cy86_width_bits(ins.type)) + " t" +
		     to_string(cy86_width_bits(ins.type)) + " [y64]");
		emit_store_reg_to_mem("[y64]", ins.type, "x");
		line("move64 x64 0");
		line("move64 x64 t64");
		emit_store_reg_to_temp(fn, ins.dest, ins.type, "x"); }
	void emit_atomic_add_fetch(const Function& fn, const Instruction& ins) {
		emit_value_to_reg(fn, ins.a, parse_type_text("ptr"), "y");
		line("move" + to_string(cy86_width_bits(ins.type)) + " x" +
		     to_string(cy86_width_bits(ins.type)) + " [y64]");
		emit_value_to_reg(fn, ins.b, ins.type, "z");
		line("iadd" + to_string(cy86_width_bits(ins.type)) + " " +
		     reg_name("x", cy86_width_bits(ins.type)) + " " +
		     reg_name("x", cy86_width_bits(ins.type)) + " " +
		     reg_name("z", cy86_width_bits(ins.type)));
		emit_store_reg_to_mem("[y64]", ins.type, "x");
		emit_store_reg_to_temp(fn, ins.dest, ins.type, "x"); }
	void emit_atomic_compare_exchange(const Function& fn, const Instruction& ins) {
		emit_value_to_reg(fn, ins.a, parse_type_text("ptr"), "y");
		emit_value_to_reg(fn, ins.b, parse_type_text("ptr"), "z");
		line("move64 t64 [y64]");
		line("move64 x64 [z64]");
		line("ieq64 x8 t64 x64");
		const string success = next_label("__atomic_cmpxchg_success__");
		const string end = next_label("__atomic_cmpxchg_end__");
		line("jumpif x8 " + success);
		line("move64 [z64] t64");
		line("move64 x64 0");
		emit_store_reg_to_temp(fn, ins.dest, parse_type_text("i64"), "x");
		line("jump " + end);
		label(success);
		emit_value_to_reg(fn, ins.c, ins.type, "x");
		emit_store_reg_to_mem("[y64]", ins.type, "x");
		line("move64 x64 1");
		emit_store_reg_to_temp(fn, ins.dest, parse_type_text("i64"), "x");
		label(end); }
	string next_label(const string& prefix) {
		return prefix + to_string(eh_label_counter++); }
	bool has_global(const string& name) const {
		return program.global_by_name.find(name) != program.global_by_name.end(); }
	void emit_exception(const Function& fn, const Instruction& ins) {
		const string global = ins.kind == InstrKind::ExceptionSelector
		                          ? "@__cppgm_eh_selector"
		                          : "@__cppgm_eh_value";
		emit_load_mem_to_reg(global_mem(global), ins.type, ins.type, "x");
		emit_store_reg_to_temp(fn, ins.dest, ins.type, "x"); }
	void emit_eh_catch(const Instruction& ins) {
		const string matched = next_label("__eh_catch_matched__");
		const string check_si = next_label("__eh_catch_check_si__");
		const string done = next_label("__eh_catch_done__");
		line("move64 x64 [g____cppgm_eh_selector]");
		line("ine64 z8 x64 0");
		line("jumpif z8 " + done);
		line("move64 x64 [g____cppgm_eh_type]");
		line("move64 y64 " + address_target_label(ins.a.text, 0));
		line("ieq64 z8 x64 y64");
		line("jumpif z8 " + matched);
		label(check_si);
		line("move64 z64 [x64]");
		line("move64 t64 g____external_rtti_vtable____si_class_type_info");
		line("iadd64 t64 t64 16");
		line("ine64 z8 z64 t64");
		line("jumpif z8 " + done);
		line("move64 z64 [x64+16]");
		line("ieq64 z8 z64 y64");
		line("jumpif z8 " + matched);
		line("jump " + done);
		label(matched);
		line("move64 [g____cppgm_eh_selector] " + to_string(ins.order_a));
		label(done); }
	void emit_eh_catch_all(const Instruction& ins) {
		const string done = next_label("__eh_catch_all_done__");
		line("move64 x64 [g____cppgm_eh_selector]");
		line("ine64 z8 x64 0");
		line("jumpif z8 " + done);
		line("move64 [g____cppgm_eh_selector] " + to_string(ins.order_a));
		label(done); }
	void emit_eh_push(const Function& fn, const string& target) {
		line("isub64 sp sp 32");
		line("move64 z64 [g____cppgm_eh_top]");
		line("move64 [sp] z64");
		line("move64 z64 " + block_label(fn, target));
		line("move64 [sp+8] z64");
		line("move64 [sp+16] bp");
		line("move64 z64 sp");
		line("iadd64 z64 z64 32");
		line("move64 [sp+24] z64");
		line("move64 z64 sp");
		line("move64 [g____cppgm_eh_top] z64"); }
	void emit_eh_end() {
		line("move64 x64 [g____cppgm_eh_top]");
		line("move64 y64 [x64]");
		line("move64 [g____cppgm_eh_top] y64");
		line("move64 sp x64");
		line("iadd64 sp sp 32"); }
	void emit_throw(const Function& fn, const Instruction& ins) {
		emit_value_to_reg(fn, ins.a, ins.type, "x");
		line("move64 [g____cppgm_eh_value] x64");
		emit_eh_dispatch(); }
	void emit_eh_dispatch() {
		line("move64 x64 [g____cppgm_eh_top]");
		line("ieq64 z8 x64 0");
		const string handler = next_label("__eh_handler__");
		const string unhandled = next_label("__eh_unhandled__");
		line("jumpif z8 " + unhandled);
		label(handler);
		line("move64 y64 [x64]");
		line("move64 [g____cppgm_eh_top] y64");
		line("move64 z64 [x64+8]");
		line("move64 bp [x64+16]");
		line("move64 sp [x64+24]");
		line("jump z64");
		label(unhandled);
		line("move64 x64 [g____cppgm_eh_value]");
		line("call fn____cppgm_eh_unhandled");
		line("syscall1 t64 60 x64");
		out << "\n"; }
	void emit_f80_return_global() {
		label("g____cppgm_f80_return");
		line("data64 0");
		line("data64 0");
		out << "\n"; }
	bool needs_f80_return_global() const {
		for (size_t i = 0; i < program.functions.size(); ++i) {
			const Function& fn = program.functions[i];
			if (is_f80_type(fn.ret))
				return true;
			for (size_t b = 0; b < fn.blocks.size(); ++b)
				for (size_t j = 0; j < fn.blocks[b].instructions.size(); ++j)
					if (fn.blocks[b].instructions[j].kind == InstrKind::Call &&
					    is_f80_type(fn.blocks[b].instructions[j].type))
						return true; }
		return false; }
	void emit_convert(const Function& fn, const Instruction& ins) {
		if (ins.op == "sext" || ins.op == "zext" || ins.op == "trunc")
			emit_integer_convert(fn, ins);
		else
			emit_float_convert(fn, ins); }
	void emit_integer_convert(const Function& fn, const Instruction& ins) {
		if (is_i128_type(ins.type) && !is_i128_type(ins.src_type)) {
			if (ins.src_type.size > 8)
				throw runtime_error("unsupported i128 extension source");
			const int width = cy86_width_bits(ins.src_type);
			emit_value_to_reg(fn, ins.a, ins.src_type, "x");
			if (width < 64) {
				line("move64 y64 0");
				line("move" + to_string(width) + " y" +
				     to_string(width) + " x" + to_string(width));
				line("move64 x64 y64");
				if (ins.op == "sext")
					emit_sign_extend("x", width, 64); }
			const size_t off = fn.temp_offsets.find(ins.dest)->second;
			line("move64 " + stack_mem(off) + " x64");
			if (ins.op == "sext") {
				line("move64 y64 x64");
				line("move8 t8 63");
				line("srshift64 y64 y64 t8");
				line("move64 " + stack_mem(off - 8) + " y64"); }
			else
				line("move64 " + stack_mem(off - 8) + " 0");
			return; }
		if (!is_i128_type(ins.type) && is_i128_type(ins.src_type)) {
			if (ins.type.size > 8)
				throw runtime_error("unsupported i128 truncation destination");
			emit_direct_object_chunk_to_reg(fn, ins.a, ins.src_type, 0, "x");
			emit_store_reg_to_temp(fn, ins.dest, ins.type, "x");
			return; }
		emit_value_to_reg(fn, ins.a, ins.src_type, "x");
		if (ins.op == "sext")
			emit_sign_extend("x", ins.src_type.bits, ins.type.bits);
		emit_store_reg_to_temp(fn, ins.dest, ins.type, "x"); }
	void emit_float_convert(const Function& fn, const Instruction& ins) {
		const string scratch = stack_mem(fn.convert_scratch_offset);
		if (is_f80_type(ins.type)) {
			emit_to_f80_scratch(fn, ins.op, ins.src_type, ins.a, scratch);
			emit_copy_f80_scratch_to_temp(fn, ins.dest, scratch); }
		else if (is_f80_type(ins.src_type)) {
			emit_f80_value_to_scratch(fn, ins.a, scratch);
			line(f80_to_dest_opcode(ins) + " " +
			     stack_mem(fn.temp_offsets.find(ins.dest)->second) + " " + scratch); }
		else {
			emit_to_f80_scratch(fn, ins.op, ins.src_type, ins.a, scratch);
			line(f80_to_dest_opcode(ins) + " " +
			     stack_mem(fn.temp_offsets.find(ins.dest)->second) + " " + scratch); } }
	string f80_to_dest_opcode(const Instruction& ins) const {
		const string prefix = ins.op == "fptosi" ? "f80convs" :
		                      ins.op == "fptoui" ? "f80convu" : "f80convf";
		return prefix + to_string(cy86_width_bits(ins.type)); }
	void emit_to_f80_scratch(const Function& fn,
	                         const string& op,
	                         const Type& src_type,
	                         const Value& value,
	                         const string& scratch) {
		emit_value_to_reg(fn, value, src_type, "x");
		string opcode;
		if (is_float_type(src_type))
			opcode = "f" + to_string(cy86_width_bits(src_type)) + "convf80";
		else
			opcode = (op == "uitofp" ? "u" : "s") +
			         to_string(cy86_width_bits(src_type)) + "convf80";
		line(opcode + " " + scratch + " " + reg_name("x", cy86_width_bits(src_type)));
		emit_f80_padding(fn); }
	void emit_f80_padding(const Function& fn) {
		const size_t s = fn.convert_scratch_offset;
		line("move64 z64 0");
		line("move32 " + stack_mem(s - 10) + " z32");
		line("move16 " + stack_mem(s - 14) + " z16"); }
	void emit_copy_f80_scratch_to_temp(const Function& fn,
	                                   const string& dest,
	                                   const string& scratch) {
		const size_t off = fn.temp_offsets.find(dest)->second;
		line("move64 z64 " + scratch);
		line("move64 " + stack_mem(off) + " z64");
		line("move64 z64 " + stack_mem(fn.convert_scratch_offset - 8));
		line("move64 " + stack_mem(off - 8) + " z64"); }
	void emit_f80_value_to_scratch(const Function& fn,
	                               const Value& value,
	                               const string& scratch) {
		emit_object_source_to_reg(fn, value, "x");
		line("move64 z64 [x64]");
		line("move64 " + scratch + " z64");
		line("move64 z64 [x64+8]");
		line("move64 " + stack_mem(fn.convert_scratch_offset - 8) + " z64"); }
	void emit_literal_to_reg(const Type& type, const string& literal, const string& base) {
		const string source = native_cy86_literal(type, literal, native_output);
		if (is_float_type(type) && type.bits == 32)
			line("move32 " + reg_name(base, 32) + " " + source);
		else if (is_float_type(type) && type.bits == 64)
			line("move64 " + reg_name(base, 64) + " " + source);
		else
			line("move64 " + reg_name(base, 64) + " " + source); }
	string f80_value_mem(const Function& fn, const Value& value) const {
		if (value.kind == ValueKind::Literal)
			return value.text;
		if (value.kind == ValueKind::Global)
			return global_mem(value.text);
		if (value.kind == ValueKind::Temp || value.kind == ValueKind::Slot)
			return stack_mem(lookup_offset(fn, value));
		throw runtime_error("invalid f80 value"); }
	void emit_value_to_reg(const Function& fn,
	                       const Value& value,
	                       const Type& desired,
	                       const string& base) {
		if (native_output && is_direct_object_abi(desired)) {
			emit_direct_object_value_to_reg(fn, value, desired, base);
			return; }
		if (value.kind == ValueKind::Literal)
			emit_literal_to_reg(desired, value.text, base);
		else if (value.kind == ValueKind::Function)
			line("move64 " + reg_name(base, 64) + " " + function_label(value.text));
		else if (value.kind == ValueKind::Global)
			emit_load_mem_to_reg(global_mem(value.text), lookup_value_type(fn, value),
			                     desired, base);
		else
			emit_load_mem_to_reg(stack_mem(lookup_offset(fn, value)),
			                     lookup_value_type(fn, value), desired, base); }
	void emit_direct_object_value_to_reg(const Function& fn,
	                                     const Value& value,
	                                     const Type& type,
	                                     const string& base) {
		const int width = direct_object_abi_width_bits(type);
		if (value.kind == ValueKind::Global) {
			line("move" + to_string(width) + " " + reg_name(base, width) +
			     " " + global_mem(value.text));
			return; }
		if (value.kind == ValueKind::Temp || value.kind == ValueKind::Slot) {
			line("move" + to_string(width) + " " + reg_name(base, width) +
			     " " + stack_mem(lookup_offset(fn, value)));
			return; }
		throw runtime_error("invalid direct object value"); }
	void emit_direct_object_value_to_registers(const Function& fn,
	                                           const Value& value,
	                                           const Type& type,
	                                           size_t first_reg) {
		for (size_t chunk = 0; chunk < direct_object_abi_slots(type); ++chunk)
			emit_direct_object_chunk_to_reg(fn, value, type, chunk,
			                                arg_reg(first_reg + chunk)); }
	void emit_direct_object_chunk_to_reg(const Function& fn,
	                                     const Value& value,
	                                     const Type& type,
	                                     size_t chunk,
	                                     const string& base) {
		const int width = direct_object_abi_chunk_width_bits(type, chunk);
		if (value.kind == ValueKind::Literal && is_i128_type(type)) {
			const string literal = i128_literal_chunk(value.text, chunk);
			line("move64 " + reg_name(base, 64) + " " + literal);
			return; }
		if (width < 64)
			line("move64 " + reg_name(base, 64) + " 0");
		line("move" + to_string(width) + " " + reg_name(base, width) +
		     " " + direct_object_chunk_mem(fn, value, chunk, base)); }
	string direct_object_chunk_mem(const Function& fn,
	                               const Value& value,
	                               size_t chunk,
	                               const string& base) {
		if (value.kind == ValueKind::Global) {
			const string scratch = base == "t" ? "z" : "t";
			line("move64 " + reg_name(scratch, 64) + " " + global_label(value.text));
			return mem_reg(scratch, static_cast<int>(chunk * 8)); }
		if (value.kind == ValueKind::Temp || value.kind == ValueKind::Slot)
			return stack_mem(lookup_offset(fn, value) - chunk * 8);
		throw runtime_error("invalid direct object value"); }
	void emit_direct_object_copy_to_temp(const Function& fn,
	                                     const Value& value,
	                                     const string& temp,
	                                     const Type& type) {
		for (size_t chunk = 0; chunk < direct_object_abi_slots(type); ++chunk) {
			const int width = direct_object_abi_chunk_width_bits(type, chunk);
			emit_direct_object_chunk_to_reg(fn, value, type, chunk, "x");
			line("move" + to_string(width) + " " +
			     stack_mem(fn.temp_offsets.find(temp)->second - chunk * 8) +
			     " " + reg_name("x", width)); } }
	void emit_pointer_value_to_reg(const Function& fn, const Value& value, const string& base) {
		if (value.kind == ValueKind::Slot && is_obj_type(lookup_value_type(fn, value)))
			emit_address_to_reg(fn, value, base);
		else
			emit_value_to_reg(fn, value, parse_type_text("ptr"), base); }
	void emit_pointer_or_slot_destination_to_reg(const Function& fn,
	                                             const Value& value,
	                                             const Span& span,
	                                             const string& base) {
		const Type type = lookup_value_type(fn, value);
		if (value.kind == ValueKind::Slot && !is_ptr_type(type) &&
		    stack_storage_size(type) >= span.bytes) {
			emit_address_to_reg(fn, value, base);
			return; }
		emit_pointer_value_to_reg(fn, value, base); }
	void emit_object_source_to_reg(const Function& fn, const Value& value, const string& base) {
		const Type type = lookup_value_type(fn, value);
		if ((value.kind == ValueKind::Temp || value.kind == ValueKind::Slot) &&
		    (is_obj_type(type) || is_f80_type(type))) {
			if (value.kind == ValueKind::Temp)
				emit_temp_address_to_reg(fn, value.text, base);
			else
				emit_address_to_reg(fn, value, base); }
		else
			emit_value_to_reg(fn, value, parse_type_text("ptr"), base); }
	void emit_address_to_reg(const Function& fn, const Value& value, const string& base) {
		if (value.kind == ValueKind::Slot)
			line("isub64 " + reg_name(base, 64) + " bp " +
			     to_string(lookup_offset(fn, value)));
		else if (value.kind == ValueKind::Global) {
			if (program.function_by_name.find(value.text) != program.function_by_name.end())
				line("move64 " + reg_name(base, 64) + " " + function_label(value.text));
			else
				line("move64 " + reg_name(base, 64) + " " + global_label(value.text)); }
		else if (value.kind == ValueKind::Function)
			line("move64 " + reg_name(base, 64) + " " + function_label(value.text));
		else
			throw runtime_error("cannot take address"); }
	void emit_temp_address_to_reg(const Function& fn, const string& temp, const string& base) {
		Value value;
		value.kind = ValueKind::Temp;
		value.text = temp;
		line("isub64 " + reg_name(base, 64) + " bp " +
		     to_string(lookup_offset(fn, value))); }
	string global_mem(const string& name) const {
		return "[" + global_label(name) + "]"; }
	void emit_load_mem_to_reg(const string& mem,
	                          const Type& stored,
	                          const Type& desired,
	                          const string& base) {
		const int sw = cy86_width_bits(stored);
		const int dw = cy86_width_bits(desired);
		if (sw == dw) {
			if (sw < 32 && is_scalar_int_like(stored))
				line("move64 " + reg_name(base, 64) + " 0");
			line("move" + to_string(sw) + " " + reg_name(base, sw) + " " + mem);
			return; }
		if (dw == 64 && sw < 64) {
			if (sw < 32)
				line("move64 " + reg_name(base, 64) + " 0");
			line("move" + to_string(sw) + " " + reg_name(base, sw) + " " + mem);
			if (is_signed_integer_type(stored))
				emit_sign_extend(base, sw, 64);
			return; }
		line("move" + to_string(dw) + " " + reg_name(base, dw) + " " + mem); }
	void emit_sign_extend(const string& base, int src_bits, int dst_bits) {
		if (src_bits >= dst_bits)
			return;
		const int shift = dst_bits - src_bits;
		line("move8 t8 " + to_string(shift));
		line("lshift" + to_string(dst_bits) + " " + reg_name(base, dst_bits) +
		     " " + reg_name(base, dst_bits) + " t8");
		line("srshift" + to_string(dst_bits) + " " + reg_name(base, dst_bits) +
			      " " + reg_name(base, dst_bits) + " t8"); }
	void emit_i128_value_to_register_pair(const Function& fn,
	                                      const Value& value,
	                                      const Type& type,
	                                      const string& low,
	                                      const string& high) {
		emit_i128_chunk_to_reg(fn, value, type, 0, low);
		emit_i128_chunk_to_reg(fn, value, type, 1, high); }
	void emit_i128_chunk_to_reg(const Function& fn,
	                            const Value& value,
	                            const Type& type,
	                            size_t chunk,
	                            const string& base) {
		if (value.kind == ValueKind::Literal) {
			const string literal = i128_literal_chunk(value.text, chunk);
			line("move64 " + reg_name(base, 64) + " " + literal);
			return; }
		emit_direct_object_chunk_to_reg(fn, value, type, chunk, base); }
	string i128_literal_chunk(const string& literal, size_t chunk) const {
		if (chunk != 0)
			return !literal.empty() && literal[0] == '-' ? "-1" : "0";
		char* end = NULL;
		const unsigned long long value = strtoull(literal.c_str(), &end, 0);
		if (end != literal.c_str() && *end == '\0' &&
		    value > static_cast<unsigned long long>(numeric_limits<long long>::max()))
			return to_string(static_cast<long long>(value));
		return literal; }
	void emit_store_reg_to_temp(const Function& fn,
	                            const string& temp,
	                            const Type& type,
	                            const string& base) {
		emit_store_reg_to_mem(stack_mem(fn.temp_offsets.find(temp)->second), type, base); }
	void emit_store_direct_object_reg_to_temp(const Function& fn,
	                                          const string& temp,
	                                          const Type& type,
	                                          const string& base) {
		const int width = direct_object_abi_width_bits(type);
		line("move" + to_string(width) + " " +
		     stack_mem(fn.temp_offsets.find(temp)->second) + " " +
		     reg_name(base, width)); }
	void emit_store_direct_object_registers_to_temp(const Function& fn,
	                                                const string& temp,
	                                                const Type& type,
	                                                size_t first_reg) {
		for (size_t chunk = 0; chunk < direct_object_abi_slots(type); ++chunk) {
			const int width = direct_object_abi_chunk_width_bits(type, chunk);
			line("move" + to_string(width) + " " +
			     stack_mem(fn.temp_offsets.find(temp)->second - chunk * 8) +
			     " " + reg_name(arg_reg(first_reg + chunk), width)); } }
	void emit_store_reg_to_mem(const string& mem, const Type& type, const string& base) {
		const int width = register_value_width_bits(type, native_output);
		line("move" + to_string(width) + " " + mem + " " + reg_name(base, width)); }
	void emit_copy_qwords(size_t bytes, const string& src, const string& dst) {
		if (bytes % 8 != 0) {
			emit_copy_bytes(bytes, src, dst);
			return; }
		for (size_t off = 0; off < bytes; off += 8) {
			if (off != 0) {
				line("iadd64 " + dst + "64 " + dst + "64 8");
				line("iadd64 " + src + "64 " + src + "64 8"); }
			line("move64 z64 [" + src + "64]");
			line("move64 [" + dst + "64] z64"); } }
	void emit_copy_qwords_offset(size_t bytes, const string& src, const string& dst) {
		if (bytes % 8 != 0) {
			emit_copy_bytes(bytes, src, dst);
			return; }
		for (size_t off = 0; off < bytes; off += 8) {
			line("move64 z64 " + mem_reg(src, static_cast<int>(off)));
			line("move64 " + mem_reg(dst, static_cast<int>(off)) + " z64"); } }
	void emit_copy_bytes(size_t bytes, const string& src, const string& dst) {
		size_t off = 0;
		while (off < bytes) {
			const size_t width = largest_copy_width(bytes - off);
			line("move" + to_string(width * 8) + " " +
			     reg_name("z", static_cast<int>(width * 8)) + " " +
			     mem_reg(src, static_cast<int>(off)));
			line("move" + to_string(width * 8) + " " +
			     mem_reg(dst, static_cast<int>(off)) + " " +
			     reg_name("z", static_cast<int>(width * 8)));
			off += width; } }
	void emit_zero_bytes(size_t bytes, const string& dst) {
		size_t off = 0;
		while (off < bytes) {
			const size_t width = largest_copy_width(bytes - off);
			line("move" + to_string(width * 8) + " " +
			     mem_reg(dst, static_cast<int>(off)) + " " +
			     reg_name("z", static_cast<int>(width * 8)));
			off += width; } }
	size_t largest_copy_width(size_t bytes) const {
		if (bytes >= 8)
			return 8;
		if (bytes >= 4)
			return 4;
		if (bytes >= 2)
			return 2;
		return 1; }
	void emit_global_section(const Global& global) {
		if (native_output && native_global_alignment(global) >= 16)
			line("align16");
		emit_alias_labels_for_global(global);
		label(global_label(global.name));
		if (global.data.empty())
			emit_scalar_global(global);
		else
			emit_structured_global(global);
		out << "\n"; }
	void emit_alias_labels_for_global(const Global& global) {
		const string object = metadata_value(global.metadata, "object");
		if (object.empty())
			return;
		for (size_t i = 0; i < program.globals.size(); ++i) {
			const Global& decl = program.globals[i];
			if (!decl.declaration || decl.name == global.name)
				continue;
			if (metadata_value(decl.metadata, "object") == object)
				label(global_label(decl.name)); } }
	void emit_scalar_global(const Global& global) {
		if (global.init.kind == "zero")
			line("data" + to_string(cy86_width_bits(global.type)) + " 0");
		else if (global.init.kind == "addr")
		{
			line("data64 " + address_target_label(global.init.target, global.init.addend));
			for (size_t n = 8; n < storage_size(global.type); ++n)
				line("data8 0");
		}
		else
			line("data" + to_string(cy86_width_bits(global.type)) + " " +
			     native_cy86_literal(global.type, global.init.literal,
			                         native_output)); }
	void emit_structured_global(const Global& global) {
		size_t offset = 0;
		for (size_t i = 0; i < global.data.size(); ++i) {
			const GlobalDataItem& item = global.data[i];
			if (item.kind == "zero")
				emit_zero_data(offset, item.zero_bytes);
			else if (item.kind == "addr") {
				emit_padding(offset, 8);
				line("data64 " + address_target_label(item.target, item.addend));
				offset += 8; }
			else {
				emit_padding(offset, item.type.align);
				line("data" + to_string(cy86_width_bits(item.type)) + " " +
				     native_cy86_literal(item.type, item.literal,
				                         native_output));
				offset += storage_size(item.type); }
		} }
	void emit_padding(size_t& offset, size_t align) {
		while (align != 0 && offset % align != 0) {
			line("data8 0");
			++offset; } }
	void emit_zero_data(size_t& offset, size_t bytes) {
		for (size_t i = 0; i < bytes; ++i) {
			line("data8 0");
			++offset; } }
	string address_target_label(const string& target, int addend) const {
		if (program.function_by_name.find(target) != program.function_by_name.end())
			return addend_label(function_label(target), addend);
		return addend_label(global_label(target), addend); }
};
}  // namespace
string finish_cy86_text(const Program& program,
                        bool safe_call_argument_order,
                        bool native_output) {
	CyEmitter emitter(program, safe_call_argument_order, native_output);
	string text = emitter.finish();
	if (text.size() >= 2 && text[text.size() - 1] == '\n' &&
	    text[text.size() - 2] == '\n')
		text.erase(text.size() - 1);
	return text; }
string emit_cy86(const Program& program) {
	return finish_cy86_text(program, false, false); }
string emit_cy86_for_native(const Program& program) {
	return finish_cy86_text(program, true, true); }
}  // namespace lowir2cy86
