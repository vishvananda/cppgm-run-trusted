#include "pa31_host_object_internal.h"

#include <algorithm>
#include <stdexcept>

using namespace std;

namespace pa31 {
namespace host {

namespace {

const int kGpArgRegs[] = {RDI, RSI, RDX, RCX, R8, R9};

struct ArgLoc
{
	Type type;
	bool fp;
	bool object;
	bool stack;
	size_t reg;
	size_t fp_reg;
	size_t stack_offset;
	size_t slots;
	ArgLoc()
		: fp(false), object(false), stack(false), reg(0),
		  fp_reg(0), stack_offset(0), slots(1) {}
};

void choose_arg_location(ArgLoc& loc,
                         size_t& reg_index,
                         size_t& fp_index,
                         size_t& stack_bytes)
{
	loc.fp = lowir2cy86::is_float_type(loc.type) && loc.type.bits <= 64;
	loc.object =
		lowir2cy86::is_obj_type(loc.type) &&
		lowir2cy86::is_direct_object_abi(loc.type);
	if (loc.fp)
	{
		if (fp_index < 8)
			loc.fp_reg = fp_index++;
		else
		{
			loc.stack = true;
			loc.stack_offset = stack_bytes;
			stack_bytes += lowir2cy86::stack_storage_size(loc.type);
		}
	}
	else if (loc.object)
	{
		loc.slots = lowir2cy86::direct_object_abi_slots(loc.type);
		if (reg_index + loc.slots <= 6)
		{
			loc.reg = reg_index;
			reg_index += loc.slots;
		}
		else
		{
			loc.stack = true;
			loc.stack_offset = stack_bytes;
			stack_bytes += loc.slots * 8;
		}
	}
	else if (reg_index < 6)
		loc.reg = reg_index++;
	else
	{
		loc.stack = true;
		loc.stack_offset = stack_bytes;
		stack_bytes += lowir2cy86::stack_storage_size(loc.type);
	}
}

void compute_arg_locations(FuncGen& gen,
                           const Instruction& ins,
                           const vector<Type>& types,
                           vector<ArgLoc>& locs,
                           size_t& fp_index,
                           size_t& stack_bytes)
{
	size_t reg_index = 0;
	fp_index = 0;
	stack_bytes = 0;
	locs.resize(ins.args.size());
	for (size_t i = 0; i < ins.args.size(); ++i)
	{
		ArgLoc loc;
		loc.type = i < types.size() ? types[i] : gen.value_type(ins.args[i]);
		choose_arg_location(loc, reg_index, fp_index, stack_bytes);
		locs[i] = loc;
	}
}

bool call_is_variadic(const Unit& unit, const Instruction& ins)
{
	if (metadata(ins.signature.metadata, "arity") == "variadic")
		return true;
	if (ins.a.kind != ValueKind::Function)
		return false;
	map<string, size_t>::const_iterator f =
		unit.program.function_by_name.find(ins.a.text);
	return f != unit.program.function_by_name.end() &&
	       metadata(unit.program.functions[f->second].metadata, "arity") ==
		       "variadic";
}

bool try_emit_pruned_constructor_call(FuncGen& gen, const Instruction& ins)
{
	if (ins.a.kind != ValueKind::Function)
		return false;
	map<string, size_t>::const_iterator f =
		gen.unit.program.function_by_name.find(ins.a.text);
	if (f == gen.unit.program.function_by_name.end())
		return false;
	const Function& callee = gen.unit.program.functions[f->second];
	if (pruned_noop_constructor_function(callee))
		return true;
	if (!o1_inline_constructor_function(gen.unit, callee))
		return false;
	gen.emit_simple_constructor_inline_call(callee, ins);
	return true;
}

void emit_stack_arg(FuncGen& gen,
                    const Instruction& ins,
                    size_t index,
                    const ArgLoc& loc)
{
	Mem dst(RSP, static_cast<int32_t>(loc.stack_offset));
	const Type& type = loc.type;
	if (loc.fp)
	{
		gen.load_float_value(ins.args[index], type, 15);
		gen.x.sse_mr(type.bits == 32 ? 0xf3 : 0xf2, 0x11, dst, 15);
		return;
	}
	if (loc.object)
	{
		gen.storage_address(ins.args[index], R11);
		for (size_t c = 0; c < loc.slots; ++c)
		{
			const int width =
				lowir2cy86::direct_object_abi_chunk_width_bits(type, c);
			gen.x.mov_rm(width, RAX, Mem(R11, static_cast<int32_t>(c * 8)));
			gen.x.mov_mr(width,
			             Mem(RSP,
			                 static_cast<int32_t>(loc.stack_offset + c * 8)),
			             RAX);
		}
		return;
	}
	gen.load_value(ins.args[index], type, RAX);
	gen.x.mov_mr(width_for(type), dst, RAX);
}

void emit_register_arg(FuncGen& gen,
                       const Instruction& ins,
                       size_t index,
                       const ArgLoc& loc)
{
	const Type& type = loc.type;
	if (loc.fp)
		gen.load_float_value(ins.args[index], type,
		                     static_cast<int>(loc.fp_reg));
	else if (loc.object)
	{
		gen.storage_address(ins.args[index], R11);
		for (size_t c = 0; c < loc.slots; ++c)
		{
			gen.x.mov_rm(
				lowir2cy86::direct_object_abi_chunk_width_bits(type, c),
				kGpArgRegs[loc.reg + c],
				Mem(R11, static_cast<int32_t>(c * 8)));
		}
	}
	else
		gen.load_value(ins.args[index], type, kGpArgRegs[loc.reg]);
}

void emit_call_target(FuncGen& gen, const Instruction& ins)
{
	if (ins.a.kind == ValueKind::Function)
	{
		gen.x.u8(0xe8);
		const size_t off = gen.x.pos();
		gen.x.u32(0);
		gen.unit.obj.reloc(gen.text, off,
		                   target_symbol(gen.unit.program, ins.a.text),
		                   R_X86_64_PLT32, -4);
		return;
	}
	gen.load_value(ins.a, lowir2cy86::parse_type_text("ptr"), R11);
	gen.x.rex(true, 2, 0, R11);
	gen.x.u8(0xff);
	gen.x.modrm(3, 2, R11);
}

void store_call_result(FuncGen& gen, const Instruction& ins)
{
	if (!ins.has_dest || lowir2cy86::is_void_type(ins.type))
		return;
	if (lowir2cy86::is_obj_type(ins.type))
	{
		const size_t off = gen.fn.temp_offsets.find(ins.dest)->second;
		gen.x.mov_mr(lowir2cy86::direct_object_abi_chunk_width_bits(
			             ins.type, 0),
		             frame_object_mem(off, 0), RAX);
		if (lowir2cy86::direct_object_abi_slots(ins.type) == 2)
			gen.x.mov_mr(lowir2cy86::direct_object_abi_chunk_width_bits(
				             ins.type, 1),
			             frame_object_mem(off, 8), RDX);
		return;
	}
	if (lowir2cy86::is_float_type(ins.type))
		gen.store_float_temp(ins.dest, ins.type, 0);
	else
		gen.store_temp(ins.dest, ins.type, RAX);
}

}  // namespace

vector<Type> call_types(const Program& program, const Instruction& ins)
{
	vector<Type> out;
	if (ins.signature.present)
	{
		for (size_t i = 0; i < ins.signature.params.size(); ++i)
			out.push_back(ins.signature.params[i].type);
		return out;
	}
	if (ins.a.kind == ValueKind::Function)
	{
		map<string, size_t>::const_iterator f =
			program.function_by_name.find(ins.a.text);
		if (f != program.function_by_name.end())
			for (size_t i = 0; i < program.functions[f->second].params.size(); ++i)
				out.push_back(program.functions[f->second].params[i].type);
	}
	return out;
}

void advance_sysv_argument(const Type& type,
                           size_t& gp,
                           size_t& fp,
                           size_t& stack)
{
	if (lowir2cy86::is_float_type(type) && type.bits <= 64)
	{
		if (fp < 8) ++fp;
		else stack += lowir2cy86::stack_storage_size(type);
	}
	else if (lowir2cy86::is_obj_type(type) &&
	         lowir2cy86::is_direct_object_abi(type))
	{
		const size_t slots = lowir2cy86::direct_object_abi_slots(type);
		if (gp + slots <= 6) gp += slots;
		else stack += slots * 8;
	}
	else if (gp < 6)
		++gp;
	else
		stack += lowir2cy86::stack_storage_size(type);
}

void fixed_variadic_offsets(const Function& fn,
                            size_t& gp_offset,
                            size_t& fp_offset,
                            size_t& overflow_stack)
{
	size_t gp = 0;
	size_t fp = 0;
	overflow_stack = 16;
	for (size_t i = 0; i < fn.params.size(); ++i)
		advance_sysv_argument(fn.params[i].type, gp, fp, overflow_stack);
	gp_offset = min<size_t>(gp, 6) * 8;
	fp_offset = 48 + min<size_t>(fp, 8) * 16;
}

void patch_local_rel32(Blob& b, size_t at, size_t target)
{
	const int64_t disp = static_cast<int64_t>(target) -
	                     static_cast<int64_t>(at + 4);
	b.patch32(at, static_cast<uint32_t>(disp));
}

void FuncGen::save_variadic_registers()
{
	if (!has_va_start)
		return;
	static const int gp_regs[] = {RDI, RSI, RDX, RCX, R8, R9};
	for (size_t i = 0; i < 6; ++i)
		x.mov_mr(64, frame_object_mem(va_reg_save_off, i * 8), gp_regs[i]);
	for (size_t i = 0; i < 8; ++i)
		x.sse_mr(0, 0x11, frame_object_mem(va_reg_save_off, 48 + i * 16),
		         static_cast<int>(i));
}

void FuncGen::emit_va_start(const Instruction& ins)
{
	size_t gp_offset = 0;
	size_t fp_offset = 48;
	size_t overflow_stack = 16;
	fixed_variadic_offsets(fn, gp_offset, fp_offset, overflow_stack);
	load_value(ins.a, lowir2cy86::parse_type_text("ptr"), R11);
	x.mov_imm(32, RAX, gp_offset);
	x.mov_mr(32, Mem(R11, 0), RAX);
	x.mov_imm(32, RAX, fp_offset);
	x.mov_mr(32, Mem(R11, 4), RAX);
	x.lea(RAX, Mem(RBP, static_cast<int32_t>(overflow_stack)));
	x.mov_mr(64, Mem(R11, 8), RAX);
	x.lea(RAX, frame_object_mem(va_reg_save_off, 0));
	x.mov_mr(64, Mem(R11, 16), RAX);
}

void FuncGen::emit_va_arg(const Instruction& ins)
{
	if (lowir2cy86::is_obj_type(ins.type) ||
	    (lowir2cy86::is_float_type(ins.type) && ins.type.bits > 64))
		throw runtime_error("unsupported host va_arg type");
	load_value(ins.a, lowir2cy86::parse_type_text("ptr"), R11);
	const bool fp_arg = lowir2cy86::is_float_type(ins.type);
	const size_t offset_field = fp_arg ? 4 : 0;
	const size_t limit = fp_arg ? 176 : 48;
	const size_t step = fp_arg ? 16 : 8;
	x.mov_rm(32, RAX, Mem(R11, static_cast<int32_t>(offset_field)));
	x.mov_imm(32, R10, limit);
	x.cmp(32, RAX, R10);
	x.u8(0x0f);
	x.u8(0x83);
	size_t stack_jump = x.pos();
	x.u32(0);
	x.mov_rm(64, R10, Mem(R11, 16));
	x.binary(0x01, 64, R10, RAX);
	if (fp_arg)
	{
		x.sse_rm(ins.type.bits == 32 ? 0xf3 : 0xf2, 0x10, 0, Mem(R10, 0));
		x.mov_imm(32, R10, step);
		x.binary(0x01, 32, RAX, R10);
		x.mov_mr(32, Mem(R11, static_cast<int32_t>(offset_field)), RAX);
		store_float_temp(ins.dest, ins.type, 0);
	}
	else
	{
		x.mov_rm(width_for(ins.type), RAX, Mem(R10, 0));
		store_temp(ins.dest, ins.type, RAX);
		x.mov_rm(32, RAX, Mem(R11, static_cast<int32_t>(offset_field)));
		x.mov_imm(32, R10, step);
		x.binary(0x01, 32, RAX, R10);
		x.mov_mr(32, Mem(R11, static_cast<int32_t>(offset_field)), RAX);
	}
	x.u8(0xe9);
	size_t end_jump = x.pos();
	x.u32(0);
	size_t stack_label = x.pos();
	x.mov_rm(64, R10, Mem(R11, 8));
	if (fp_arg)
	{
		x.sse_rm(ins.type.bits == 32 ? 0xf3 : 0xf2, 0x10, 0, Mem(R10, 0));
		x.mov_imm(64, RAX, lowir2cy86::stack_storage_size(ins.type));
		x.binary(0x01, 64, R10, RAX);
		x.mov_mr(64, Mem(R11, 8), R10);
		store_float_temp(ins.dest, ins.type, 0);
	}
	else
	{
		x.mov_rm(width_for(ins.type), RAX, Mem(R10, 0));
		x.mov_imm(64, RCX, lowir2cy86::stack_storage_size(ins.type));
		x.binary(0x01, 64, R10, RCX);
		x.mov_mr(64, Mem(R11, 8), R10);
		store_temp(ins.dest, ins.type, RAX);
	}
	size_t end_label = x.pos();
	patch_local_rel32(text.bytes, stack_jump, stack_label);
	patch_local_rel32(text.bytes, end_jump, end_label);
}

void FuncGen::emit_simple_constructor_inline_call(const Function& callee,
                                                  const Instruction& ins)
{
	vector<SimpleCtorStore> stores;
	if (ins.args.size() != 1 ||
	    !simple_inline_constructor_function(callee, &stores))
		throw runtime_error("invalid simple constructor inline call");
	load_value(ins.args[0], lowir2cy86::parse_type_text("ptr"), R11);
	for (size_t i = 0; i < stores.size(); ++i)
	{
		const SimpleCtorStore& store = stores[i];
		if (lowir2cy86::is_float_type(store.type))
		{
			load_float_value(store.value, store.type, 0);
			x.sse_mr(store.type.bits == 32 ? 0xf3 : 0xf2, 0x11,
			         Mem(R11, static_cast<int32_t>(store.offset)), 0);
		}
		else
		{
			load_value(store.value, store.type, RAX);
			x.mov_mr(width_for(store.type),
			         Mem(R11, static_cast<int32_t>(store.offset)), RAX);
		}
	}
}

void FuncGen::emit_call(const Instruction& ins)
{
	if (try_emit_pruned_constructor_call(*this, ins))
		return;
	vector<Type> types = call_types(unit.program, ins);
	const bool variadic_call = call_is_variadic(unit, ins);
	size_t fp_index = 0;
	size_t stack_bytes = 0;
	vector<ArgLoc> locs;
	compute_arg_locations(*this, ins, types, locs, fp_index, stack_bytes);
	const size_t call_stack_bytes = align_up(stack_bytes, 16);
	if (call_stack_bytes != 0)
		x.sub_rsp(call_stack_bytes);
	for (size_t i = 0; i < ins.args.size(); ++i)
	{
		if (locs[i].stack)
			emit_stack_arg(*this, ins, i, locs[i]);
		else
			emit_register_arg(*this, ins, i, locs[i]);
	}
	if (variadic_call || ins.args.size() > types.size())
		x.mov_imm(8, RAX, fp_index);
	emit_call_target(*this, ins);
	if (call_stack_bytes != 0)
		x.add_rsp(call_stack_bytes);
	store_call_result(*this, ins);
}

}  // namespace host
}  // namespace pa31
