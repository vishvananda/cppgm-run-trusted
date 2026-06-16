#include "pa31_host_object_internal.h"

namespace pa31 {
namespace host {

bool FuncGen::emit_arithmetic_instruction(const Instruction& ins)
{
	if (ins.kind == InstrKind::Binary)
	{
		if (lowir2cy86::is_float_type(ins.type) && ins.type.bits == 64)
		{
			load_float_value(ins.a, ins.type, 0);
			load_float_value(ins.b, ins.type, 1);
			if (ins.op == "add") x.sse_rr(0xf2, 0x58, 0, 1);
			else if (ins.op == "sub") x.sse_rr(0xf2, 0x5c, 0, 1);
			else if (ins.op == "mul") x.sse_rr(0xf2, 0x59, 0, 1);
			else if (ins.op == "div") x.sse_rr(0xf2, 0x5e, 0, 1);
			else throw runtime_error("unsupported float binary");
			store_float_temp(ins.dest, ins.type, 0);
		}
		else
		{
			load_value(ins.a, ins.type, RAX);
			load_value(ins.b, ins.type, R10);
			if (ins.op == "add") x.binary(0x01, width_for(ins.type), RAX, R10);
			else if (ins.op == "sub") x.binary(0x29, width_for(ins.type), RAX, R10);
			else if (ins.op == "mul") x.imul(width_for(ins.type), RAX, R10);
			else if (ins.op == "and") x.binary(0x21, width_for(ins.type), RAX, R10);
			else if (ins.op == "or") x.binary(0x09, width_for(ins.type), RAX, R10);
			else if (ins.op == "xor") x.binary(0x31, width_for(ins.type), RAX, R10);
			else if (ins.op == "div" || ins.op == "mod")
			{
				x.idiv_reg(width_for(ins.type), R10);
				if (ins.op == "mod")
					x.mov_rr(width_for(ins.type), RAX, RDX);
			}
			else if (ins.op == "udiv" || ins.op == "umod")
			{
				x.div_reg(width_for(ins.type), R10);
				if (ins.op == "umod")
					x.mov_rr(width_for(ins.type), RAX, RDX);
			}
			else if (ins.op == "shl" || ins.op == "shr" || ins.op == "ushr")
			{
				x.mov_rr(64, RCX, R10);
				x.shift_cl(width_for(ins.type),
				           ins.op == "shl" ? 4 : (ins.op == "shr" ? 7 : 5),
				           RAX);
			}
			else throw runtime_error("unsupported binary");
			store_temp(ins.dest, ins.type, RAX);
		}
		return true;
	}
	if (ins.kind == InstrKind::Cmp)
	{
		if (lowir2cy86::is_f80_type(ins.type))
		{
			load_f80_value_to_x87(ins.b);
			load_f80_value_to_x87(ins.a);
			x.x87_fucomip_st1();
			x.x87_fstp_st0();
			uint8_t cc = 0x94;
			if (ins.op == "ne") cc = 0x95;
			else if (ins.op == "lt") cc = 0x92;
			else if (ins.op == "gt") cc = 0x97;
			else if (ins.op == "le") cc = 0x96;
			else if (ins.op == "ge") cc = 0x93;
			else if (ins.op != "eq") throw runtime_error("unsupported float cmp");
			x.setcc(cc);
			x.mov_rr(64, R10, RAX);
			if (ins.op == "ne")
			{
				x.setcc(0x9a);
				x.binary(0x09, 64, RAX, R10);
			}
			else
			{
				x.setcc(0x9b);
				x.binary(0x21, 64, RAX, R10);
			}
		}
		else if (lowir2cy86::is_float_type(ins.type))
		{
			load_float_value(ins.a, ins.type, 0);
			load_float_value(ins.b, ins.type, 1);
			x.sse_rr(ins.type.bits == 32 ? 0 : 0x66, 0x2e, 0, 1);
			uint8_t cc = 0x94;
			if (ins.op == "ne") cc = 0x95;
			else if (ins.op == "lt") cc = 0x92;
			else if (ins.op == "gt") cc = 0x97;
			else if (ins.op == "le") cc = 0x96;
			else if (ins.op == "ge") cc = 0x93;
			else if (ins.op != "eq") throw runtime_error("unsupported float cmp");
			x.setcc(cc);
			x.mov_rr(64, R10, RAX);
			if (ins.op == "ne")
			{
				x.setcc(0x9a);
				x.binary(0x09, 64, RAX, R10);
			}
			else
			{
				x.setcc(0x9b);
				x.binary(0x21, 64, RAX, R10);
			}
		}
		else
		{
			load_value(ins.a, ins.type, RAX);
			load_value(ins.b, ins.type, R10);
			x.cmp(width_for(ins.type), RAX, R10);
			x.setcc(cmp_cc(ins.op));
		}
		store_temp(ins.dest, ins.type, RAX);
		return true;
	}
	if (ins.kind != InstrKind::Convert)
		return false;
	if (ins.op == "sitofp" && lowir2cy86::is_float_type(ins.type))
	{
		load_value(ins.a, ins.src_type, RAX);
		x.cvtsi2sd(width_for(ins.src_type), 0, RAX);
		store_float_temp(ins.dest, ins.type, 0);
	}
	else if (ins.op == "fpext" && ins.src_type.bits == 32 &&
	         ins.type.bits == 64)
	{
		load_float_value(ins.a, ins.src_type, 0);
		x.sse_rr(0xf3, 0x5a, 0, 0);
		store_float_temp(ins.dest, ins.type, 0);
	}
	else
	{
		load_value(ins.a, ins.type, RAX);
		store_temp(ins.dest, ins.type, RAX);
	}
	return true;
}


}  // namespace host
}  // namespace pa31
