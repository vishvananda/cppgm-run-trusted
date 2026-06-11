#include "cy86_x86.h"

#include <algorithm>
#include <cctype>
#include <cerrno>
#include <cstring>
#include <limits>
#include <stdexcept>

using namespace std;

namespace cy86 {
namespace {

const uint64_t kImageBase = 0x400000;
const uint64_t kHeaderSize = 64 + 56;
const uint64_t kCodeBase = kImageBase + kHeaderSize;

enum XReg
{
	RAX = 0, RCX = 1, RDX = 2, RBX = 3,
	RSP = 4, RBP = 5, RSI = 6, RDI = 7,
	R8 = 8, R9 = 9, R10 = 10, R11 = 11,
	RIP = -1
};

struct MemRef
{
	int base;
	int32_t disp;

	MemRef(int b, int32_t d) : base(b), disp(d) {}
};

struct Context
{
	map<string, uint64_t>* labels;
	uint64_t const_2_63;
	uint64_t const_2_64;
	uint64_t instruction_base;
};

struct Emitter
{
	vector<unsigned char> bytes;

	size_t pos() const { return bytes.size(); }
	void u8(uint8_t v) { bytes.push_back(v); }
	void u16(uint16_t v) { u8(v); u8(v >> 8); }
	void u32(uint32_t v)
	{
		for (int i = 0; i < 4; ++i)
			u8(static_cast<uint8_t>(v >> (i * 8)));
	}
	void u64(uint64_t v)
	{
		for (int i = 0; i < 8; ++i)
			u8(static_cast<uint8_t>(v >> (i * 8)));
	}
	void raw(const vector<unsigned char>& data)
	{
		bytes.insert(bytes.end(), data.begin(), data.end());
	}
	void rex(bool w, int r = 0, int x = 0, int b = 0, bool force = false)
	{
		const bool need = force || w || r >= 8 || x >= 8 || b >= 8;
		if (need)
			u8(0x40 | (w ? 8 : 0) | ((r >> 3) << 2) |
			   ((x >> 3) << 1) | (b >> 3));
	}
	void prefix(int width)
	{
		if (width == 16)
			u8(0x66);
	}
	void modrm(int mod, int reg, int rm)
	{
		u8(static_cast<uint8_t>((mod << 6) | ((reg & 7) << 3) | (rm & 7)));
	}
	void sib(int scale, int index, int base)
	{
		u8(static_cast<uint8_t>((scale << 6) | ((index & 7) << 3) | (base & 7)));
	}
	void patch_rel8(size_t where, size_t target)
	{
		const int rel = static_cast<int>(target) - static_cast<int>(where + 1);
		if (rel < -128 || rel > 127)
			throw runtime_error("short branch overflow");
		bytes[where] = static_cast<unsigned char>(rel & 0xff);
	}
};

size_t align_up(size_t value, size_t align)
{
	if (align == 0)
		return value;
	const size_t rem = value % align;
	return rem == 0 ? value : value + align - rem;
}

int width_bytes(int width)
{
	return width == 80 ? 10 : width / 8;
}

uint64_t bytes_to_u64(const vector<unsigned char>& bytes)
{
	uint64_t out = 0;
	const size_t n = min<size_t>(bytes.size(), 8);
	for (size_t i = 0; i < n; ++i)
		out |= static_cast<uint64_t>(bytes[i]) << (i * 8);
	return out;
}

void emit_mem_operand(Emitter& e, int reg_field, const MemRef& mem)
{
	if (mem.base == RIP)
	{
		e.modrm(0, reg_field, 5);
		e.u32(static_cast<uint32_t>(mem.disp));
		return;
	}
	const int base_low = mem.base & 7;
	int mod = 0;
	if (mem.disp == 0 && base_low != 5)
		mod = 0;
	else if (mem.disp >= -128 && mem.disp <= 127)
		mod = 1;
	else
		mod = 2;
	e.modrm(mod, reg_field, base_low == 4 ? 4 : base_low);
	if (base_low == 4)
		e.sib(0, 4, base_low);
	if (mod == 1)
		e.u8(static_cast<uint8_t>(mem.disp));
	else if (mod == 2 || (mod == 0 && base_low == 5))
		e.u32(static_cast<uint32_t>(mem.disp));
}

void emit_reg_reg(Emitter& e, int width, uint8_t opcode, int reg_field, int rm)
{
	e.prefix(width);
	e.rex(width == 64, reg_field, 0, rm, width == 8 && (reg_field >= 4 || rm >= 4));
	e.u8(opcode);
	e.modrm(3, reg_field, rm);
}

void emit_reg_mem(Emitter& e, int width, uint8_t opcode, int reg, const MemRef& mem)
{
	e.prefix(width);
	e.rex(width == 64, reg, 0, mem.base == RIP ? 0 : mem.base,
	      width == 8 && reg >= 4);
	e.u8(opcode);
	emit_mem_operand(e, reg, mem);
}

void emit_x87_mem(Emitter& e, uint8_t opcode, int ext, const MemRef& mem)
{
	e.rex(false, ext, 0, mem.base, false);
	e.u8(opcode);
	emit_mem_operand(e, ext, mem);
}

void emit_mov_imm_reg(Emitter& e, int width, int reg, uint64_t value)
{
	e.prefix(width);
	e.rex(width == 64, 0, 0, reg, width == 8 && reg >= 4);
	if (width == 8)
	{
		e.u8(0xb0 + (reg & 7));
		e.u8(static_cast<uint8_t>(value));
	}
	else
	{
		e.u8(0xb8 + (reg & 7));
		if (width == 16)
			e.u16(static_cast<uint16_t>(value));
		else if (width == 32)
			e.u32(static_cast<uint32_t>(value));
		else
			e.u64(value);
	}
}

void emit_mov_reg_reg(Emitter& e, int width, int dst, int src)
{
	emit_reg_reg(e, width, width == 8 ? 0x8a : 0x8b, dst, src);
}

void emit_mov_reg_mem(Emitter& e, int width, int dst, const MemRef& mem)
{
	emit_reg_mem(e, width, width == 8 ? 0x8a : 0x8b, dst, mem);
}

void emit_mov_mem_reg(Emitter& e, int width, const MemRef& mem, int src)
{
	emit_reg_mem(e, width, width == 8 ? 0x88 : 0x89, src, mem);
}

int32_t rip_disp32(Emitter& e,
                   const Context& ctx,
                   int width,
                   int reg,
                   uint64_t target)
{
	const bool force_rex = width == 8 && reg >= 4;
	const bool need_rex = force_rex || width == 64 || reg >= 8;
	const size_t length = (width == 16 ? 1 : 0) + (need_rex ? 1 : 0) + 6;
	const int64_t next = static_cast<int64_t>(ctx.instruction_base + e.pos() + length);
	const int64_t disp = static_cast<int64_t>(target) - next;
	if (disp < numeric_limits<int32_t>::min() ||
	    disp > numeric_limits<int32_t>::max())
		throw runtime_error("RIP-relative memory address out of range");
	return static_cast<int32_t>(disp);
}

void emit_mov_reg_label_mem(Emitter& e,
                            const Context& ctx,
                            int width,
                            int dst,
                            uint64_t target)
{
	emit_mov_reg_mem(e,
	                 width,
	                 dst,
	                 MemRef(RIP, rip_disp32(e, ctx, width, dst, target)));
}

void emit_mov_label_mem_reg(Emitter& e,
                            const Context& ctx,
                            int width,
                            uint64_t target,
                            int src)
{
	emit_mov_mem_reg(e,
	                 width,
	                 MemRef(RIP, rip_disp32(e, ctx, width, src, target)),
	                 src);
}

void emit_binary_reg_reg(Emitter& e, int width, uint8_t op8, uint8_t op, int dst, int src)
{
	emit_reg_reg(e, width, width == 8 ? op8 : op, src, dst);
}

void emit_add_reg_reg(Emitter& e, int width, int dst, int src)
{
	emit_binary_reg_reg(e, width, 0x00, 0x01, dst, src);
}

void emit_sub_reg_reg(Emitter& e, int width, int dst, int src)
{
	emit_binary_reg_reg(e, width, 0x28, 0x29, dst, src);
}

void emit_and_reg_reg(Emitter& e, int width, int dst, int src)
{
	emit_binary_reg_reg(e, width, 0x20, 0x21, dst, src);
}

void emit_or_reg_reg(Emitter& e, int width, int dst, int src)
{
	emit_binary_reg_reg(e, width, 0x08, 0x09, dst, src);
}

void emit_xor_reg_reg(Emitter& e, int width, int dst, int src)
{
	emit_binary_reg_reg(e, width, 0x30, 0x31, dst, src);
}

void emit_cmp_reg_reg(Emitter& e, int width, int left, int right)
{
	emit_binary_reg_reg(e, width, 0x38, 0x39, left, right);
}

void emit_test_reg_reg(Emitter& e, int width, int left, int right)
{
	emit_binary_reg_reg(e, width, 0x84, 0x85, left, right);
}

void emit_add_imm64(Emitter& e, int reg, uint64_t value)
{
	if (value <= static_cast<uint64_t>(numeric_limits<int32_t>::max()))
	{
		e.rex(true, 0, 0, reg);
		e.u8(0x81);
		e.modrm(3, 0, reg);
		e.u32(static_cast<uint32_t>(value));
		return;
	}
	emit_mov_imm_reg(e, 64, R10, value);
	emit_add_reg_reg(e, 64, reg, R10);
}

void emit_load_x87(Emitter& e, int width, const MemRef& mem)
{
	if (width == 32)
		emit_x87_mem(e, 0xd9, 0, mem);
	else if (width == 64)
		emit_x87_mem(e, 0xdd, 0, mem);
	else
		emit_x87_mem(e, 0xdb, 5, mem);
}

void emit_store_x87(Emitter& e, int width, const MemRef& mem)
{
	if (width == 32)
		emit_x87_mem(e, 0xd9, 3, mem);
	else if (width == 64)
		emit_x87_mem(e, 0xdd, 3, mem);
	else
		emit_x87_mem(e, 0xdb, 7, mem);
}

int cyreg_x86(const RegisterRef& reg)
{
	return register_family_x86_code(reg.base);
}

void require_integral_literal(const LiteralValue& literal)
{
	if (!literal.signed_integral && !literal.unsigned_integral)
		throw runtime_error("expected integral literal");
}

void validate_address(const MemoryAddress& mem)
{
	if (mem.kind == AddressKind::Register && mem.reg.width_bits != 64)
		throw runtime_error("memory address register must be 64-bit");
	if (mem.kind == AddressKind::Label && mem.has_addend)
		require_integral_literal(mem.addend);
}

void validate_operand(const Operand& op, const OperandDesc& desc)
{
	if (desc.immediate_only && op.kind != OperandKind::Immediate)
		throw runtime_error("operand must be immediate");
	if (desc.write && op.kind == OperandKind::Immediate)
		throw runtime_error("write operand may not be immediate");
	if (op.kind == OperandKind::Register && op.reg.width_bits != desc.width_bits)
		throw runtime_error("register width mismatch");
	if (op.kind == OperandKind::Register && desc.width_bits == 80)
		throw runtime_error("no 80-bit CY86 register");
	if (op.kind == OperandKind::Memory)
		validate_address(op.mem);
}

const OpcodeDesc& checked_opcode(const Statement& stmt)
{
	const OpcodeDesc* desc = find_opcode(stmt.opcode);
	if (desc == NULL)
		throw runtime_error("unknown opcode");
	if (desc->operands.size() != stmt.operands.size())
		throw runtime_error("wrong operand count");
	for (size_t i = 0; i < desc->operands.size(); ++i)
		validate_operand(stmt.operands[i], desc->operands[i]);
	return *desc;
}

uint64_t memory_base_value(const MemoryAddress& mem, const Context& ctx)
{
	uint64_t value = 0;
	if (mem.kind == AddressKind::Literal)
		value = literal_to_u64(mem.literal);
	else if (mem.kind == AddressKind::Label)
	{
		map<string, uint64_t>::const_iterator it = ctx.labels->find(mem.label_name);
		if (it == ctx.labels->end())
			throw runtime_error("undefined label");
		value = it->second;
	}
	else
		throw runtime_error("register address has no constant value");
	if (mem.has_addend)
	{
		const uint64_t add = literal_to_u64(mem.addend);
		value += mem.addend_sign < 0 ? -add : add;
	}
	return value;
}

bool memory_label_value(const MemoryAddress& mem, const Context& ctx, uint64_t& value)
{
	if (mem.kind != AddressKind::Label)
		return false;
	value = memory_base_value(mem, ctx);
	return true;
}

void emit_address_to_r11(Emitter& e, const MemoryAddress& mem, const Context& ctx)
{
	if (mem.kind == AddressKind::Register)
	{
		emit_mov_reg_reg(e, 64, R11, cyreg_x86(mem.reg));
		if (mem.has_addend)
		{
			uint64_t add = literal_to_u64(mem.addend);
			if (mem.addend_sign < 0)
				add = -add;
			emit_add_imm64(e, R11, add);
		}
		return;
	}
	emit_mov_imm_reg(e, 64, R11, memory_base_value(mem, ctx));
}

uint64_t operand_immediate_value(const Operand& op, int width, const Context& ctx)
{
	if (op.imm.label)
		return immediate_to_u64(op.imm, *ctx.labels);
	return bytes_to_u64(convert_literal_width(op.imm.literal, width));
}

void emit_load_operand(Emitter& e, const Operand& op, int width, int dst, const Context& ctx)
{
	if (op.kind == OperandKind::Register)
		emit_mov_reg_reg(e, width, dst, cyreg_x86(op.reg));
	else if (op.kind == OperandKind::Immediate)
		emit_mov_imm_reg(e, width, dst, operand_immediate_value(op, width, ctx));
	else
	{
		uint64_t label_address = 0;
		if (memory_label_value(op.mem, ctx, label_address))
		{
			emit_mov_reg_label_mem(e, ctx, width, dst, label_address);
			return;
		}
		emit_address_to_r11(e, op.mem, ctx);
		emit_mov_reg_mem(e, width, dst, MemRef(R11, 0));
	}
}

void emit_store_operand(Emitter& e, const Operand& op, int width, int src, const Context& ctx)
{
	if (op.kind == OperandKind::Register)
		emit_mov_reg_reg(e, width, cyreg_x86(op.reg), src);
	else if (op.kind == OperandKind::Memory)
	{
		uint64_t label_address = 0;
		if (memory_label_value(op.mem, ctx, label_address))
		{
			emit_mov_label_mem_reg(e, ctx, width, label_address, src);
			return;
		}
		emit_address_to_r11(e, op.mem, ctx);
		emit_mov_mem_reg(e, width, MemRef(R11, 0), src);
	}
	else
		throw runtime_error("invalid write operand");
}

void emit_store_literal_bytes(Emitter& e, const MemRef& mem, const vector<unsigned char>& bytes)
{
	size_t pos = 0;
	while (pos < bytes.size())
	{
		const size_t left = bytes.size() - pos;
		if (left >= 8)
		{
			emit_mov_imm_reg(e, 64, RAX, bytes_to_u64(vector<unsigned char>(bytes.begin() + pos, bytes.begin() + pos + 8)));
			emit_mov_mem_reg(e, 64, MemRef(mem.base, mem.disp + static_cast<int32_t>(pos)), RAX);
			pos += 8;
		}
		else if (left >= 2)
		{
			uint16_t v = bytes[pos] | (static_cast<uint16_t>(bytes[pos + 1]) << 8);
			emit_mov_imm_reg(e, 16, RAX, v);
			emit_mov_mem_reg(e, 16, MemRef(mem.base, mem.disp + static_cast<int32_t>(pos)), RAX);
			pos += 2;
		}
		else
		{
			emit_mov_imm_reg(e, 8, RAX, bytes[pos]);
			emit_mov_mem_reg(e, 8, MemRef(mem.base, mem.disp + static_cast<int32_t>(pos)), RAX);
			++pos;
		}
	}
}

void emit_operand_to_temp(Emitter& e, const Operand& op, int width,
                          const MemRef& temp, const Context& ctx)
{
	if (width == 80)
	{
		if (op.kind == OperandKind::Immediate)
			emit_store_literal_bytes(e, temp, convert_literal_width(op.imm.literal, 80));
		else
		{
			emit_address_to_r11(e, op.mem, ctx);
			emit_mov_reg_mem(e, 64, RAX, MemRef(R11, 0));
			emit_mov_mem_reg(e, 64, temp, RAX);
			emit_mov_reg_mem(e, 16, RAX, MemRef(R11, 8));
			emit_mov_mem_reg(e, 16, MemRef(temp.base, temp.disp + 8), RAX);
		}
		return;
	}
	emit_load_operand(e, op, width, RAX, ctx);
	emit_mov_mem_reg(e, width, temp, RAX);
}

void emit_temp_to_operand(Emitter& e, const MemRef& temp, const Operand& op,
                          int width, const Context& ctx)
{
	if (width == 80)
	{
		emit_mov_reg_mem(e, 64, RAX, temp);
		emit_store_operand(e, op, 64, RAX, ctx);
		emit_mov_reg_mem(e, 16, RAX, MemRef(temp.base, temp.disp + 8));
		if (op.kind == OperandKind::Memory)
		{
			emit_address_to_r11(e, op.mem, ctx);
			emit_mov_mem_reg(e, 16, MemRef(R11, 8), RAX);
			return;
		}
		throw runtime_error("invalid 80-bit destination");
	}
	emit_mov_reg_mem(e, width, RAX, temp);
	emit_store_operand(e, op, width, RAX, ctx);
}

void emit_fld_operand(Emitter& e, const Operand& op, int width, int temp_offset, const Context& ctx)
{
	if (op.kind == OperandKind::Memory)
	{
		emit_address_to_r11(e, op.mem, ctx);
		emit_load_x87(e, width, MemRef(R11, 0));
		return;
	}
	MemRef temp(RSP, -temp_offset);
	emit_operand_to_temp(e, op, width, temp, ctx);
	emit_load_x87(e, width, temp);
}

void emit_fstp_operand(Emitter& e, const Operand& op, int width, int temp_offset, const Context& ctx)
{
	if (op.kind == OperandKind::Memory)
	{
		emit_address_to_r11(e, op.mem, ctx);
		emit_store_x87(e, width, MemRef(R11, 0));
		return;
	}
	MemRef temp(RSP, -temp_offset);
	emit_store_x87(e, width, temp);
	emit_temp_to_operand(e, temp, op, width, ctx);
}

void emit_move(Emitter& e, const Statement& stmt, int width, const Context& ctx)
{
	if (width == 80)
	{
		MemRef temp(RSP, -16);
		emit_operand_to_temp(e, stmt.operands[1], 80, temp, ctx);
		emit_temp_to_operand(e, temp, stmt.operands[0], 80, ctx);
		return;
	}
	emit_load_operand(e, stmt.operands[1], width, RAX, ctx);
	emit_store_operand(e, stmt.operands[0], width, RAX, ctx);
}

void emit_not(Emitter& e, const Statement& stmt, int width, const Context& ctx)
{
	emit_load_operand(e, stmt.operands[1], width, RAX, ctx);
	emit_reg_reg(e, width, width == 8 ? 0xf6 : 0xf7, 2, RAX);
	emit_store_operand(e, stmt.operands[0], width, RAX, ctx);
}

void emit_bswap(Emitter& e, const Statement& stmt, int width, const Context& ctx)
{
	emit_load_operand(e, stmt.operands[1], width, RAX, ctx);
	if (width == 16)
	{
		e.u8(0x66);
		e.u8(0xc1);
		e.u8(0xc0);
		e.u8(8);
	}
	else if (width == 32 || width == 64)
	{
		e.rex(width == 64, 0, 0, RAX);
		e.u8(0x0f);
		e.u8(0xc8 + (RAX & 7));
	}
	emit_store_operand(e, stmt.operands[0], width, RAX, ctx);
}

void emit_binary(Emitter& e, const Statement& stmt, int width,
                 void (*op)(Emitter&, int, int, int), const Context& ctx)
{
	emit_load_operand(e, stmt.operands[1], width, RAX, ctx);
	emit_load_operand(e, stmt.operands[2], width, R10, ctx);
	op(e, width, RAX, R10);
	emit_store_operand(e, stmt.operands[0], width, RAX, ctx);
}

void emit_shift(Emitter& e, const Statement& stmt, int width, int ext, const Context& ctx)
{
	emit_load_operand(e, stmt.operands[1], width, RAX, ctx);
	emit_load_operand(e, stmt.operands[2], 8, RCX, ctx);
	emit_reg_reg(e, width, width == 8 ? 0xd2 : 0xd3, ext, RAX);
	emit_store_operand(e, stmt.operands[0], width, RAX, ctx);
}

void emit_mul(Emitter& e, const Statement& stmt, int width, const Context& ctx)
{
	emit_load_operand(e, stmt.operands[1], width, RAX, ctx);
	emit_load_operand(e, stmt.operands[2], width, R10, ctx);
	emit_reg_reg(e, 64, 0x0f, RAX, R10);
	e.bytes.back() = static_cast<unsigned char>((3 << 6) | ((RAX & 7) << 3) | (R10 & 7));
	e.bytes.insert(e.bytes.end() - 1, 0xaf);
	emit_store_operand(e, stmt.operands[0], width, RAX, ctx);
}

void emit_clear_dx(Emitter& e, int width)
{
	if (width == 8)
	{
		e.u8(0x30);
		e.u8(0xe4);
	}
	else if (width == 16)
	{
		e.u8(0x66);
		e.u8(0x31);
		e.u8(0xd2);
	}
	else
		emit_xor_reg_reg(e, 32, RDX, RDX);
}

void emit_sign_extend_dividend(Emitter& e, int width)
{
	if (width == 8)
	{
		e.u8(0x66);
		e.u8(0x98);
	}
	else if (width == 16)
	{
		e.u8(0x66);
		e.u8(0x99);
	}
	else if (width == 32)
		e.u8(0x99);
	else
	{
		e.u8(0x48);
		e.u8(0x99);
	}
}

void emit_divmod(Emitter& e, const Statement& stmt, int width,
                 bool sign, bool mod, const Context& ctx)
{
	emit_load_operand(e, stmt.operands[1], width, RAX, ctx);
	emit_load_operand(e, stmt.operands[2], width, R10, ctx);
	if (sign)
		emit_sign_extend_dividend(e, width);
	else
		emit_clear_dx(e, width);
	emit_reg_reg(e, width, width == 8 ? 0xf6 : 0xf7, sign ? 7 : 6, R10);
	if (mod)
	{
		if (width == 8)
		{
			e.u8(0x88);
			e.u8(0xe0);
		}
		else
			emit_mov_reg_reg(e, width, RAX, RDX);
	}
	emit_store_operand(e, stmt.operands[0], width, RAX, ctx);
}

uint8_t condition_code(const string& op)
{
	if (op == "eq") return 0x94;
	if (op == "ne") return 0x95;
	if (op == "lt") return 0x9c;
	if (op == "gt") return 0x9f;
	if (op == "le") return 0x9e;
	if (op == "ge") return 0x9d;
	throw runtime_error("invalid condition");
}

uint8_t unsigned_condition_code(const string& op)
{
	if (op == "lt") return 0x92;
	if (op == "gt") return 0x97;
	if (op == "le") return 0x96;
	if (op == "ge") return 0x93;
	return condition_code(op);
}

void emit_compare(Emitter& e, const Statement& stmt, int width,
                  uint8_t setcc, const Context& ctx)
{
	emit_load_operand(e, stmt.operands[1], width, RAX, ctx);
	emit_load_operand(e, stmt.operands[2], width, R10, ctx);
	emit_cmp_reg_reg(e, width, RAX, R10);
	e.u8(0x0f);
	e.u8(setcc);
	e.rex(false, 0, 0, RAX, false);
	e.modrm(3, 0, RAX);
	emit_store_operand(e, stmt.operands[0], 8, RAX, ctx);
}

void emit_control(Emitter& e, const Statement& stmt, const Context& ctx)
{
	if (stmt.opcode == "ret")
	{
		e.u8(0xc3);
		return;
	}
	const Operand& target = stmt.opcode == "jumpif" ? stmt.operands[1] : stmt.operands[0];
	Emitter target_code;
	emit_load_operand(target_code, target, 64, RAX, ctx);
	target_code.rex(true, 0, 0, RAX);
	target_code.u8(0xff);
	target_code.modrm(3, stmt.opcode == "call" ? 2 : 4, RAX);
	if (stmt.opcode == "jumpif")
	{
		emit_load_operand(e, stmt.operands[0], 8, RAX, ctx);
		emit_test_reg_reg(e, 8, RAX, RAX);
		e.u8(0x74);
		if (target_code.bytes.size() > 127)
			throw runtime_error("jumpif target sequence too large");
		e.u8(static_cast<uint8_t>(target_code.bytes.size()));
	}
	e.raw(target_code.bytes);
}

void emit_syscall(Emitter& e, const Statement& stmt, const Context& ctx)
{
	static const int arg_regs[] = { RDI, RSI, RDX, R10, R8, R9 };
	const size_t nargs = stmt.operands.size() - 2;
	for (size_t i = 0; i < nargs; ++i)
		emit_load_operand(e, stmt.operands[i + 2], 64, arg_regs[i], ctx);
	emit_load_operand(e, stmt.operands[1], 64, RAX, ctx);
	e.u8(0x0f);
	e.u8(0x05);
	emit_store_operand(e, stmt.operands[0], 64, RAX, ctx);
}

void emit_farith(Emitter& e, const Statement& stmt, int width, uint8_t opcode, const Context& ctx)
{
	emit_fld_operand(e, stmt.operands[1], width, 16, ctx);
	emit_fld_operand(e, stmt.operands[2], width, 32, ctx);
	e.u8(0xde);
	e.u8(opcode);
	emit_fstp_operand(e, stmt.operands[0], width, 16, ctx);
}

void emit_fcompare(Emitter& e, const Statement& stmt, int width,
                   uint8_t setcc, const Context& ctx)
{
	emit_fld_operand(e, stmt.operands[2], width, 16, ctx);
	emit_fld_operand(e, stmt.operands[1], width, 32, ctx);
	e.u8(0xdf);
	e.u8(0xf1);
	e.u8(0xdd);
	e.u8(0xd8);
	e.u8(0x0f);
	e.u8(setcc);
	e.modrm(3, 0, RAX);
	emit_store_operand(e, stmt.operands[0], 8, RAX, ctx);
}

void emit_fild_mem(Emitter& e, int fild_width, const MemRef& mem)
{
	if (fild_width == 16)
		emit_x87_mem(e, 0xdf, 0, mem);
	else if (fild_width == 32)
		emit_x87_mem(e, 0xdb, 0, mem);
	else
		emit_x87_mem(e, 0xdf, 5, mem);
}

void emit_fistp_mem(Emitter& e, int width, const MemRef& mem)
{
	if (width == 16)
		emit_x87_mem(e, 0xdf, 3, mem);
	else if (width == 32)
		emit_x87_mem(e, 0xdb, 3, mem);
	else
		emit_x87_mem(e, 0xdf, 7, mem);
}

void emit_movsx_rax(Emitter& e, int from_width)
{
	if (from_width == 8)
	{
		e.u8(0x0f);
		e.u8(0xbe);
		e.u8(0xc0);
	}
	else if (from_width == 16)
	{
		e.u8(0x0f);
		e.u8(0xbf);
		e.u8(0xc0);
	}
	else if (from_width == 32)
	{
		e.u8(0x48);
		e.u8(0x63);
		e.u8(0xc0);
	}
}

void emit_movzx_rax(Emitter& e, int from_width)
{
	if (from_width == 8)
	{
		e.u8(0x0f);
		e.u8(0xb6);
		e.u8(0xc0);
	}
	else if (from_width == 16)
	{
		e.u8(0x0f);
		e.u8(0xb7);
		e.u8(0xc0);
	}
}

void emit_load_const_tbyte(Emitter& e, uint64_t addr)
{
	emit_mov_imm_reg(e, 64, R11, addr);
	emit_load_x87(e, 80, MemRef(R11, 0));
}

void emit_int_to_f80(Emitter& e, const Statement& stmt, int width,
                     bool unsign, const Context& ctx)
{
	MemRef temp(RSP, -16);
	emit_load_operand(e, stmt.operands[1], width, RAX, ctx);
	if (unsign && width == 64)
	{
		emit_mov_mem_reg(e, 64, temp, RAX);
		emit_fild_mem(e, 64, temp);
		emit_test_reg_reg(e, 64, RAX, RAX);
		e.u8(0x79);
		const size_t patch = e.pos();
		e.u8(0);
		emit_load_const_tbyte(e, ctx.const_2_64);
		e.u8(0xde);
		e.u8(0xc1);
		e.patch_rel8(patch, e.pos());
	}
	else
	{
		int fild_width = width;
		if (!unsign)
			emit_movsx_rax(e, width);
		else if (width < 32)
			emit_movzx_rax(e, width);
		if (width == 8)
			fild_width = 16;
		else if (unsign && width == 16)
			fild_width = 32;
		else if (unsign && width == 32)
			fild_width = 64;
		emit_mov_mem_reg(e, fild_width, temp, RAX);
		emit_fild_mem(e, fild_width, temp);
	}
	emit_fstp_operand(e, stmt.operands[0], 80, 32, ctx);
}

void emit_f80_to_int(Emitter& e, const Statement& stmt, int width,
                     bool unsign, const Context& ctx)
{
	MemRef temp(RSP, -16);
	if (unsign && width == 64)
	{
		emit_fld_operand(e, stmt.operands[1], 80, 32, ctx);
		emit_load_const_tbyte(e, ctx.const_2_63);
		e.u8(0xdf);
		e.u8(0xf1);
		e.u8(0x76);
		const size_t high_patch = e.pos();
		e.u8(0);
		emit_fistp_mem(e, 64, temp);
		e.u8(0xeb);
		const size_t done_patch = e.pos();
		e.u8(0);
		const size_t high = e.pos();
		emit_load_const_tbyte(e, ctx.const_2_63);
		e.u8(0xde);
		e.u8(0xe9);
		emit_fistp_mem(e, 64, temp);
		emit_mov_reg_mem(e, 64, RAX, temp);
		emit_mov_imm_reg(e, 64, R10, 0x8000000000000000ULL);
		emit_or_reg_reg(e, 64, RAX, R10);
		emit_mov_mem_reg(e, 64, temp, RAX);
		const size_t done = e.pos();
		e.patch_rel8(high_patch, high);
		e.patch_rel8(done_patch, done);
	}
	else
	{
		emit_fld_operand(e, stmt.operands[1], 80, 32, ctx);
		const int fist_width = width == 8 ? 16 : (width < 64 ? 64 : 64);
		emit_fistp_mem(e, fist_width, temp);
	}
	emit_temp_to_operand(e, temp, stmt.operands[0], width, ctx);
}

void emit_float_conversion(Emitter& e, const Statement& stmt, const Context& ctx)
{
	const string& op = stmt.opcode;
	if (op[0] == 's' || op[0] == 'u')
	{
		const bool unsign = op[0] == 'u';
		const int width = stoi(op.substr(1, op.find("conv") - 1));
		emit_int_to_f80(e, stmt, width, unsign, ctx);
		return;
	}
	if (op.compare(0, 3, "f80") == 0)
	{
		const bool unsign = op.compare(0, 8, "f80convu") == 0;
		if (op.compare(0, 8, "f80convf") == 0)
		{
			const int width = stoi(op.substr(8));
			emit_fld_operand(e, stmt.operands[1], 80, 32, ctx);
			emit_fstp_operand(e, stmt.operands[0], width, 16, ctx);
		}
		else
		{
			const int width = stoi(op.substr(8));
			emit_f80_to_int(e, stmt, width, unsign, ctx);
		}
		return;
	}
	const int width = stoi(op.substr(1, op.find("conv") - 1));
	emit_fld_operand(e, stmt.operands[1], width, 16, ctx);
	emit_fstp_operand(e, stmt.operands[0], 80, 32, ctx);
}

int opcode_width(const string& op)
{
	size_t pos = op.size();
	while (pos > 0 && isdigit(static_cast<unsigned char>(op[pos - 1])))
		--pos;
	if (pos == op.size())
		return 0;
	return stoi(op.substr(pos));
}

string opcode_core(const string& op)
{
	size_t pos = op.size();
	while (pos > 0 && isdigit(static_cast<unsigned char>(op[pos - 1])))
		--pos;
	return op.substr(0, pos);
}

void emit_instruction(Emitter& e, const Statement& stmt, const Context& ctx)
{
	const string core = opcode_core(stmt.opcode);
	const int width = opcode_width(stmt.opcode);
	if (core == "move") emit_move(e, stmt, width, ctx);
	else if (stmt.opcode == "jump" || stmt.opcode == "jumpif" || stmt.opcode == "call" || stmt.opcode == "ret") emit_control(e, stmt, ctx);
	else if (core == "not") emit_not(e, stmt, width, ctx);
	else if (core == "bswap") emit_bswap(e, stmt, width, ctx);
	else if (core == "and") emit_binary(e, stmt, width, emit_and_reg_reg, ctx);
	else if (core == "or") emit_binary(e, stmt, width, emit_or_reg_reg, ctx);
	else if (core == "xor") emit_binary(e, stmt, width, emit_xor_reg_reg, ctx);
	else if (core == "iadd") emit_binary(e, stmt, width, emit_add_reg_reg, ctx);
	else if (core == "isub") emit_binary(e, stmt, width, emit_sub_reg_reg, ctx);
	else if (core == "lshift") emit_shift(e, stmt, width, 4, ctx);
	else if (core == "srshift") emit_shift(e, stmt, width, 7, ctx);
	else if (core == "urshift") emit_shift(e, stmt, width, 5, ctx);
	else if (core == "smul" || core == "umul") emit_mul(e, stmt, width, ctx);
	else if (core == "sdiv" || core == "udiv") emit_divmod(e, stmt, width, core[0] == 's', false, ctx);
	else if (core == "smod" || core == "umod") emit_divmod(e, stmt, width, core[0] == 's', true, ctx);
	else if (core == "ieq") emit_compare(e, stmt, width, condition_code("eq"), ctx);
	else if (core == "ine") emit_compare(e, stmt, width, condition_code("ne"), ctx);
	else if (core == "slt" || core == "sgt" || core == "sle" || core == "sge") emit_compare(e, stmt, width, condition_code(core.substr(1)), ctx);
	else if (core == "ult" || core == "ugt" || core == "ule" || core == "uge") emit_compare(e, stmt, width, unsigned_condition_code(core.substr(1)), ctx);
	else if (core == "fadd") emit_farith(e, stmt, width, 0xc1, ctx);
	else if (core == "fsub") emit_farith(e, stmt, width, 0xe9, ctx);
	else if (core == "fmul") emit_farith(e, stmt, width, 0xc9, ctx);
	else if (core == "fdiv") emit_farith(e, stmt, width, 0xf9, ctx);
	else if (core == "feq") emit_fcompare(e, stmt, width, 0x94, ctx);
	else if (core == "fne") emit_fcompare(e, stmt, width, 0x95, ctx);
	else if (core == "flt") emit_fcompare(e, stmt, width, 0x92, ctx);
	else if (core == "fgt") emit_fcompare(e, stmt, width, 0x97, ctx);
	else if (core == "fle") emit_fcompare(e, stmt, width, 0x96, ctx);
	else if (core == "fge") emit_fcompare(e, stmt, width, 0x93, ctx);
	else if (stmt.opcode.compare(0, 7, "syscall") == 0) emit_syscall(e, stmt, ctx);
	else if (stmt.opcode.find("convf80") != string::npos || stmt.opcode.find("f80conv") != string::npos) emit_float_conversion(e, stmt, ctx);
	else throw runtime_error("unsupported opcode");
}

vector<unsigned char> data_bytes(const Statement& stmt, const OpcodeDesc* desc,
                                 const Context& ctx)
{
	if (stmt.kind == StatementKind::LiteralData)
		return stmt.literal.bytes;
	const Operand& op = stmt.operands[0];
	if (op.kind != OperandKind::Immediate)
		throw runtime_error("data operand must be immediate");
	if (op.imm.label)
	{
		vector<unsigned char> out;
		uint64_t value = immediate_to_u64(op.imm, *ctx.labels);
		for (int i = 0; i < width_bytes(desc->data_width_bits); ++i)
			out.push_back(static_cast<unsigned char>(value >> (i * 8)));
		return out;
	}
	return convert_literal_width(op.imm.literal, desc->data_width_bits);
}

size_t data_align(const Statement& stmt, const OpcodeDesc* desc)
{
	if (stmt.kind == StatementKind::LiteralData)
		return max<size_t>(1, stmt.literal.alignment);
	return static_cast<size_t>(width_bytes(desc->data_width_bits));
}

size_t statement_payload_size(const Statement& stmt, const OpcodeDesc* desc,
                              map<string, uint64_t>& labels)
{
	if (stmt.kind == StatementKind::LiteralData)
		return stmt.literal.bytes.size();
	if (desc->data_opcode)
		return static_cast<size_t>(width_bytes(desc->data_width_bits));
	Emitter e;
	Context ctx = { &labels, 0, 0, kCodeBase };
	emit_instruction(e, stmt, ctx);
	return e.bytes.size();
}

void collect_labels(Program& program)
{
	for (size_t i = 0; i < program.statements.size(); ++i)
	{
		for (size_t j = 0; j < program.statements[i].labels.size(); ++j)
		{
			const string& label = program.statements[i].labels[j];
			if (is_register_name(label) || is_opcode_name(label))
				throw runtime_error("invalid label name");
			if (program.labels.find(label) != program.labels.end())
				throw runtime_error("duplicate label");
			program.labels[label] = 0;
		}
	}
}

size_t layout_program(Program& program)
{
	collect_labels(program);
	size_t offset = 0;
	for (size_t i = 0; i < program.statements.size(); ++i)
	{
		Statement& stmt = program.statements[i];
		const OpcodeDesc* desc = NULL;
		if (stmt.kind == StatementKind::Instruction)
			desc = &checked_opcode(stmt);
		const bool data = stmt.kind == StatementKind::LiteralData || desc->data_opcode;
		if (data)
			offset = align_up(offset, data_align(stmt, desc));
		stmt.offset = offset;
		for (size_t j = 0; j < stmt.labels.size(); ++j)
			program.labels[stmt.labels[j]] = kCodeBase + stmt.offset;
		stmt.size = statement_payload_size(stmt, desc, program.labels);
		offset += stmt.size;
	}
	return offset;
}

void append_long_double_tbyte(vector<unsigned char>& out, long double value)
{
	unsigned char bytes[sizeof(long double)];
	memcpy(bytes, &value, sizeof(bytes));
	for (int i = 0; i < 10; ++i)
		out.push_back(bytes[i]);
}

void append_hidden_constants(vector<unsigned char>& out)
{
	append_long_double_tbyte(out, 9223372036854775808.0L);
	append_long_double_tbyte(out, 18446744073709551616.0L);
}

void write_elf_header(vector<unsigned char>& out, uint64_t entry, uint64_t filesz)
{
	const unsigned char ident[16] = {
		0x7f, 'E', 'L', 'F', 2, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0
	};
	out.insert(out.end(), ident, ident + 16);
	auto w16 = [&](uint16_t v) { out.push_back(v); out.push_back(v >> 8); };
	auto w32 = [&](uint32_t v) {
		for (int i = 0; i < 4; ++i) out.push_back(v >> (i * 8));
	};
	auto w64 = [&](uint64_t v) {
		for (int i = 0; i < 8; ++i) out.push_back(v >> (i * 8));
	};
	w16(2); w16(0x3e); w32(1); w64(entry); w64(64); w64(0);
	w32(0); w16(64); w16(56); w16(1); w16(0); w16(0); w16(0);
	w32(1); w32(7); w64(0); w64(kImageBase); w64(0);
	w64(filesz); w64(filesz); w64(0x1000);
}

uint64_t entry_address(const Program& program)
{
	map<string, uint64_t>::const_iterator start = program.labels.find("start");
	if (start != program.labels.end())
		return start->second;
	if (!program.statements.empty())
		return kCodeBase + program.statements[0].offset;
	return kCodeBase;
}

}  // namespace

vector<unsigned char> build_elf_image(Program& program)
{
	const size_t program_size = layout_program(program);
	Context ctx = {
		&program.labels,
		kCodeBase + program_size,
		kCodeBase + program_size + 10,
		kCodeBase
	};
	vector<unsigned char> body;
	for (size_t i = 0; i < program.statements.size(); ++i)
	{
		Statement& stmt = program.statements[i];
		const OpcodeDesc* desc = NULL;
		if (stmt.kind == StatementKind::Instruction)
			desc = find_opcode(stmt.opcode);
		const bool data = stmt.kind == StatementKind::LiteralData || desc->data_opcode;
		if (data)
		{
			body.resize(stmt.offset, 0);
			vector<unsigned char> bytes = data_bytes(stmt, desc, ctx);
			body.insert(body.end(), bytes.begin(), bytes.end());
		}
		else
		{
			Emitter e;
			ctx.instruction_base = kCodeBase + stmt.offset;
			emit_instruction(e, stmt, ctx);
			body.insert(body.end(), e.bytes.begin(), e.bytes.end());
		}
	}
	body.resize(program_size, 0);
	append_hidden_constants(body);
	vector<unsigned char> image;
	write_elf_header(image, entry_address(program), kHeaderSize + body.size());
	image.insert(image.end(), body.begin(), body.end());
	return image;
}

}  // namespace cy86
