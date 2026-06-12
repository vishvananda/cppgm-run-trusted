#pragma once

#include "pa31_host_object.h"
#include <algorithm>
#include <cstdint>
#include <cstdlib>
#include <fstream>
#include <map>
#include <set>
#include <stdexcept>
#include <string>
#include <vector>

namespace pa31 {
namespace host {

using namespace std;

using lowir2cy86::Block;
using lowir2cy86::Function;
using lowir2cy86::Global;
using lowir2cy86::GlobalDataItem;
using lowir2cy86::InstrKind;
using lowir2cy86::Instruction;
using lowir2cy86::Parameter;
using lowir2cy86::Program;
using lowir2cy86::Span;
using lowir2cy86::SwitchCase;
using lowir2cy86::Type;
using lowir2cy86::TypeKind;
using lowir2cy86::Value;
using lowir2cy86::ValueKind;
const uint32_t SHT_PROGBITS = 1;
const uint32_t SHT_SYMTAB = 2;
const uint32_t SHT_STRTAB = 3;
const uint32_t SHT_RELA = 4;
const uint32_t SHT_INIT_ARRAY = 14;
const uint32_t SHT_FINI_ARRAY = 15;
const uint32_t SHT_GROUP = 17;
const uint64_t SHF_WRITE = 0x1;
const uint64_t SHF_ALLOC = 0x2;
const uint64_t SHF_EXECINSTR = 0x4;
const uint64_t SHF_GROUP = 0x200;
const uint64_t SHF_TLS = 0x400;
const uint32_t GRP_COMDAT = 1;
const uint32_t R_X86_64_64 = 1;
const uint32_t R_X86_64_PC32 = 2;
const uint32_t R_X86_64_PLT32 = 4;
const uint32_t R_X86_64_TPOFF32 = 23;
struct Blob
{
	vector<unsigned char> data;
	size_t pos() const { return data.size(); }
	void align(size_t n) { while (n > 1 && data.size() % n) data.push_back(0); }
	void u8(uint8_t v) { data.push_back(v); }
	void u16(uint16_t v) { u8(v); u8(v >> 8); }
	void u32(uint32_t v)
	{
		for (int i = 0; i < 4; ++i) u8(static_cast<uint8_t>(v >> (i * 8)));
	}
	void u64(uint64_t v)
	{
		for (int i = 0; i < 8; ++i) u8(static_cast<uint8_t>(v >> (i * 8)));
	}
	void patch32(size_t off, uint32_t v)
	{
		for (int i = 0; i < 4; ++i)
			data[off + i] = static_cast<unsigned char>(v >> (i * 8));
	}
};
struct Reloc
{
	size_t offset;
	string symbol;
	uint32_t type;
	int64_t addend;
};
struct Section
{
	string name;
	uint32_t type;
	uint64_t flags;
	uint64_t align;
	uint64_t entsize;
	uint32_t link;
	uint32_t info;
	Blob bytes;
	vector<Reloc> relocs;
	string group_signature;
	vector<string> group_members;
	bool keep;
	Section() : type(SHT_PROGBITS), flags(0), align(1), entsize(0),
	            link(0), info(0), keep(false) {}
};
struct Symbol
{
	string name;
	uint8_t bind;
	uint8_t type;
	string section;
	uint64_t value;
	uint64_t size;
	bool defined;
};
struct ObjectFile
{
	vector<Section> sections;
	vector<Symbol> symbols;
	map<string, size_t> by_name;
	set<string> dw_refs;
	Section& section(const string& name,
	                 uint32_t type,
	                 uint64_t flags,
	                 uint64_t align)
	{
		map<string, size_t>::iterator it = by_name.find(name);
		if (it != by_name.end())
			return sections[it->second];
		Section sec;
		sec.name = name;
		sec.type = type;
		sec.flags = flags;
		sec.align = align;
		by_name[name] = sections.size();
		sections.push_back(sec);
		return sections.back();
	}
	Section& text()
	{
		return section(".text", SHT_PROGBITS,
		               SHF_ALLOC | SHF_EXECINSTR, 16);
	}
	void add_comdat_group(const string& signature, const string& member)
	{
		Section& group = section(".group." + signature, SHT_GROUP, 0, 4);
		group.keep = true;
		group.entsize = 4;
		group.group_signature = signature;
		if (find(group.group_members.begin(),
		         group.group_members.end(),
		         member) == group.group_members.end())
			group.group_members.push_back(member);
	}
	Section& comdat_text(const string& signature)
	{
		const string name = ".text." + signature;
		add_comdat_group(signature, name);
		Section& sec = section(name, SHT_PROGBITS,
		                       SHF_ALLOC | SHF_EXECINSTR | SHF_GROUP, 16);
		return sec;
	}
	Section& rodata()
	{
		return section(".rodata", SHT_PROGBITS, SHF_ALLOC, 8);
	}
	Section& data()
	{
		return section(".data", SHT_PROGBITS,
		               SHF_ALLOC | SHF_WRITE, 8);
	}
	Section& tdata()
	{
		return section(".tdata", SHT_PROGBITS,
		               SHF_ALLOC | SHF_WRITE | SHF_TLS, 8);
	}
	Section& comdat_data(const string& signature, bool readonly)
	{
		const string name = string(readonly ? ".rodata." : ".data.") + signature;
		add_comdat_group(signature, name);
		Section& sec = section(name, SHT_PROGBITS,
		                       (readonly ? SHF_ALLOC : SHF_ALLOC | SHF_WRITE) |
		                       SHF_GROUP,
		                       8);
		return sec;
	}
	Section& eh_frame()
	{
		return section(".eh_frame", SHT_PROGBITS, SHF_ALLOC, 8);
	}
	Section& gcc_except_table()
	{
		return section(".gcc_except_table", SHT_PROGBITS, SHF_ALLOC, 4);
	}
	Section& init_array()
	{
		Section& sec = section(".init_array", SHT_INIT_ARRAY,
		                       SHF_ALLOC | SHF_WRITE, 8);
		sec.entsize = 8;
		return sec;
	}
	Section& fini_array()
	{
		Section& sec = section(".fini_array", SHT_FINI_ARRAY,
		                       SHF_ALLOC | SHF_WRITE, 8);
		sec.entsize = 8;
		return sec;
	}
	void reloc(Section& sec, size_t off, const string& sym,
	           uint32_t type, int64_t addend)
	{
		Reloc r;
		r.offset = off;
		r.symbol = sym;
		r.type = type;
		r.addend = addend;
		sec.relocs.push_back(r);
	}
	void symbol(const string& name, uint8_t bind, uint8_t type,
	            const string& section, uint64_t value, uint64_t size)
	{
		if (name.empty())
			return;
		for (size_t i = 0; i < symbols.size(); ++i)
			if (symbols[i].name == name)
				return;
		Symbol s;
		s.name = name;
		s.bind = bind;
		s.type = type;
		s.section = section;
		s.value = value;
		s.size = size;
		s.defined = !section.empty();
		symbols.push_back(s);
	}
	string ensure_dw_ref(const string& target)
	{
		const string name = "DW.ref." + target;
		if (dw_refs.insert(name).second)
		{
			Section& d = data();
			d.bytes.align(8);
			const size_t off = d.bytes.pos();
			d.bytes.u64(0);
			symbol(name, 0, 1, ".data", off, 8);
			reloc(d, off, target, R_X86_64_64, 0);
		}
		return name;
	}
	void write(const string& outfile);
};
enum Reg
{
	RAX = 0, RCX = 1, RDX = 2, RBX = 3,
	RSP = 4, RBP = 5, RSI = 6, RDI = 7,
	R8 = 8, R9 = 9, R10 = 10, R11 = 11,
	RIP = -1
};
struct Mem
{
	int base;
	int32_t disp;
	Mem(int b, int32_t d) : base(b), disp(d) {}
};
struct X86
{
	Section& text;
	explicit X86(Section& s) : text(s) {}
	size_t pos() const { return text.bytes.pos(); }
	void u8(uint8_t v) { text.bytes.u8(v); }
	void u32(uint32_t v) { text.bytes.u32(v); }
	void rex(bool w, int r = 0, int x = 0, int b = 0, bool force = false)
	{
		if (force || w || r >= 8 || x >= 8 || b >= 8)
			u8(0x40 | (w ? 8 : 0) | ((r >> 3) << 2) |
			   ((x >> 3) << 1) | (b >> 3));
	}
	void modrm(int mod, int reg, int rm)
	{
		u8(static_cast<uint8_t>((mod << 6) | ((reg & 7) << 3) | (rm & 7)));
	}
	void sib(int scale, int index, int base)
	{
		u8(static_cast<uint8_t>((scale << 6) | ((index & 7) << 3) | (base & 7)));
	}
	void memop(int reg, const Mem& mem)
	{
		if (mem.base == RIP)
		{
			modrm(0, reg, 5);
			u32(static_cast<uint32_t>(mem.disp));
			return;
		}
		const int base = mem.base & 7;
		const int mod = mem.disp == 0 && base != 5 ? 0 :
		                (mem.disp >= -128 && mem.disp <= 127 ? 1 : 2);
		modrm(mod, reg, base == 4 ? 4 : base);
		if (base == 4)
			sib(0, 4, base);
		if (mod == 1)
			u8(static_cast<uint8_t>(mem.disp));
		else if (mod == 2 || (mod == 0 && base == 5))
			u32(static_cast<uint32_t>(mem.disp));
	}
	void reg_mem(int width, uint8_t op, int reg, const Mem& mem)
	{
		rex(width == 64, reg, 0, mem.base == RIP ? 0 : mem.base,
		    width == 8 && reg >= 4);
		u8(op);
		memop(reg, mem);
	}
	void reg_reg(int width, uint8_t op, int reg, int rm)
	{
		rex(width == 64, reg, 0, rm, width == 8 && (reg >= 4 || rm >= 4));
		u8(op);
		modrm(3, reg, rm);
	}
	void mov_imm(int width, int reg, uint64_t value)
	{
		rex(width == 64, 0, 0, reg, width == 8 && reg >= 4);
		u8((width == 8 ? 0xb0 : 0xb8) + (reg & 7));
		if (width == 8) u8(static_cast<uint8_t>(value));
		else if (width == 32) u32(static_cast<uint32_t>(value));
		else text.bytes.u64(value);
	}
	void mov_rr(int width, int dst, int src)
	{
		reg_reg(width, width == 8 ? 0x8a : 0x8b, dst, src);
	}
	void mov_rm(int width, int dst, const Mem& mem)
	{
		reg_mem(width, width == 8 ? 0x8a : 0x8b, dst, mem);
	}
	void mov_mr(int width, const Mem& mem, int src)
	{
		reg_mem(width, width == 8 ? 0x88 : 0x89, src, mem);
	}
	void lea(int dst, const Mem& mem)
	{
		reg_mem(64, 0x8d, dst, mem);
	}
	void binary(uint8_t op, int width, int dst, int src)
	{
		reg_reg(width, op, src, dst);
	}
	void cmp(int width, int left, int right)
	{
		binary(width == 8 ? 0x38 : 0x39, width, left, right);
	}
	void imul(int width, int dst, int src)
	{
		rex(width == 64, dst, 0, src);
		u8(0x0f);
		u8(0xaf);
		modrm(3, dst, src);
	}
	void idiv_reg(int width, int src)
	{
		if (width == 64)
			rex(true);
		u8(0x99);
		rex(width == 64, 0, 0, src);
		u8(0xf7);
		modrm(3, 7, src);
	}
	void shift_cl(int width, int subop, int dst)
	{
		rex(width == 64, subop, 0, dst);
		u8(0xd3);
		modrm(3, subop, dst);
	}
	void imul_imm(int reg, int32_t imm)
	{
		rex(true, reg, 0, reg);
		u8(0x69);
		modrm(3, reg, reg);
		u32(static_cast<uint32_t>(imm));
	}
	void sse_prefix(uint8_t prefix)
	{
		if (prefix)
			u8(prefix);
	}
	void sse_rr(uint8_t prefix, uint8_t op, int dst, int src)
	{
		sse_prefix(prefix);
		rex(false, dst, 0, src);
		u8(0x0f);
		u8(op);
		modrm(3, dst, src);
	}
	void sse_rm(uint8_t prefix, uint8_t op, int dst, const Mem& mem)
	{
		sse_prefix(prefix);
		rex(false, dst, 0, mem.base == RIP ? 0 : mem.base);
		u8(0x0f);
		u8(op);
		memop(dst, mem);
	}
	void sse_mr(uint8_t prefix, uint8_t op, const Mem& mem, int src)
	{
		sse_prefix(prefix);
		rex(false, src, 0, mem.base == RIP ? 0 : mem.base);
		u8(0x0f);
		u8(op);
		memop(src, mem);
	}
	void movd_xmm_from_reg(int bits, int xmm, int reg)
	{
		u8(0x66);
		rex(bits == 64, xmm, 0, reg);
		u8(0x0f);
		u8(0x6e);
		modrm(3, xmm, reg);
	}
	void cvtsi2sd(int bits, int xmm, int reg)
	{
		u8(0xf2);
		rex(bits == 64, xmm, 0, reg);
		u8(0x0f);
		u8(0x2a);
		modrm(3, xmm, reg);
	}
	void setcc(uint8_t cc)
	{
		u8(0x0f);
		u8(cc);
		modrm(3, 0, RAX);
		movzx8(RAX, RAX);
	}
	void movzx8(int dst, int src)
	{
		rex(false, dst, 0, src, dst >= 8 || src >= 4);
		u8(0x0f);
		u8(0xb6);
		modrm(3, dst, src);
	}
	void sub_rsp(size_t bytes)
	{
		if (bytes == 0) return;
		rex(true); u8(bytes <= 127 ? 0x83 : 0x81); modrm(3, 5, RSP);
		if (bytes <= 127) u8(static_cast<uint8_t>(bytes));
		else u32(static_cast<uint32_t>(bytes));
	}
	void add_rsp(size_t bytes)
	{
		if (bytes == 0) return;
		rex(true); u8(bytes <= 127 ? 0x83 : 0x81); modrm(3, 0, RSP);
		if (bytes <= 127) u8(static_cast<uint8_t>(bytes));
		else u32(static_cast<uint32_t>(bytes));
	}
};
struct Patch
{
	size_t at;
	string target;
};
struct EhRange
{
	size_t start;
	size_t end;
	string target;
	bool may_throw;
	EhRange() : start(0), end(0), may_throw(false) {}
};
	struct CatchInfo
	{
		string type_symbol;
		int selector;
		bool catch_all;
		CatchInfo() : selector(0), catch_all(false) {}
	};
struct FunctionInfo
{
	string symbol;
	string section;
	size_t start;
	size_t size;
	bool has_lsda;
	size_t lsda_offset;
	FunctionInfo() : start(0), size(0), has_lsda(false), lsda_offset(0) {}
};
struct SimpleCtorStore
{
	Type type;
	size_t offset;
	Value value;
};
struct Unit
{
	Program& program;
	ObjectFile& obj;
	Options options;
	map<string, string> globals;
	map<string, string> functions;
	vector<FunctionInfo> infos;
	Unit(Program& p, ObjectFile& o, const Options& opts)
		: program(p), obj(o), options(opts) {}
	void prepare_symbols();
	void emit_globals();
	void emit_tls_wrappers();
	void emit_functions();
	void emit_aliases();
	void emit_eh_frame();
	void emit_lifecycle_arrays();
	Section& function_text_section(const Function& fn);
	bool is_thread_local_global(const string& name) const;
	string tls_wrapper_for_global(const string& name) const;
	void emit_tls_wrapper_for_global(const Global& g);
	bool prunes_function(const string& name) const;
	set<string> emitted_tls_wrappers;
};
struct FuncGen
{
	Unit& unit;
	const Function& fn;
	Section& text;
	X86 x;
	map<string, size_t> block_offsets;
	vector<Patch> jumps;
	vector<EhRange> ranges;
	vector<EhRange> active_ranges;
		map<string, vector<CatchInfo> > catches;
		set<string> landing_blocks;
		set<string> cleanup_blocks;
		set<string> cleanup_action_blocks;
	size_t frame_size;
	size_t exc_off;
	size_t sel_off;
	size_t va_reg_save_off;
	bool has_eh;
	bool has_va_start;
	FuncGen(Unit& u, const Function& f)
		: unit(u), fn(f), text(u.function_text_section(f)), x(text), frame_size(0),
		  exc_off(0), sel_off(0), va_reg_save_off(0), has_eh(false),
		  has_va_start(false) {}
	void emit(FunctionInfo& info);
	void emit_instruction(const Instruction& ins, const string& block);
	bool emit_value_instruction(const Instruction& ins);
	bool emit_arithmetic_instruction(const Instruction& ins);
	bool emit_protected_instruction(const Instruction& ins);
	bool emit_eh_instruction(const Instruction& ins, const string& block);
	bool emit_control_instruction(const Instruction& ins);
	void load_value(const Value& v, const Type& target, int reg);
	void load_float_value(const Value& v, const Type& target, int xmm);
	void store_value(const Value& dst, const Type& type, int reg);
	void store_float_value(const Value& dst, const Type& type, int xmm);
	void storage_address(const Value& v, int reg);
	void value_storage_address(const Value& v, int reg);
	void tls_address(const string& name, int reg);
	void copy_bytes(const Value& src, const Value& dst, const Span& span);
	void copy_memory(int src_reg, int dst_reg, size_t bytes);
	void copy_memory_to_frame(int src_reg, size_t dst_off, size_t bytes);
	void zero_memory_tail(int dst_reg, size_t first, size_t bytes);
	void zero_frame_tail(size_t dst_off, size_t first, size_t bytes);
	Type value_type(const Value& v) const;
	Mem frame_mem(size_t off) const { return Mem(RBP, -static_cast<int32_t>(off)); }
	void store_temp(const string& name, const Type& type, int reg);
	void store_float_temp(const string& name, const Type& type, int xmm);
	void save_variadic_registers();
	void emit_va_start(const Instruction& ins);
	void emit_va_arg(const Instruction& ins);
	void emit_stack_alloc(const Instruction& ins);
	void emit_call(const Instruction& ins);
	void emit_simple_constructor_inline_call(const Function& callee,
	                                         const Instruction& ins);
	void emit_return(const Instruction& ins);
	void emit_branch(const Instruction& ins);
	void emit_switch(const Instruction& ins);
	void patch_jumps(size_t base);
	void finish_lsda(FunctionInfo& info, size_t base);
	void save_landing_registers();
};

size_t align_up(size_t value, size_t align);
uint64_t parse_int(const std::string& text);
bool is_identifier(const std::string& text);
bool ends_with(const std::string& text, const std::string& suffix);
std::string metadata(const lowir2cy86::Metadata& items,
                     const std::string& key);
std::string host_global_symbol(const Global& global);
std::string host_function_symbol(const Function& fn);
std::string tls_wrapper_symbol(const std::string& variable_symbol);
std::string target_symbol(const Program& program, const std::string& name);
std::string tls_wrapper_symbol_for_function(const Program& program,
                                            const Function& fn);
void uleb(Blob& b, uint64_t value);
void sleb(Blob& b, int64_t value);
uint64_t parse_f64_bits(const std::string& text);
uint32_t parse_f32_bits(const std::string& text);
uint8_t symbol_bind(const lowir2cy86::Metadata& md);
bool skip_global_definition(const Global& g);
bool pruned_noop_constructor_function(const Function& fn);
bool simple_inline_constructor_function(const Function& fn,
                                        std::vector<SimpleCtorStore>* stores);
bool o1_inline_constructor_function(const Unit& unit, const Function& fn);
void write_integer(Blob& b, const Type& type, uint64_t value);
int width_for(const Type& type);
bool wide_integer_type(const Type& type);
size_t object_offset(const Function& fn, const Value& v);
Mem frame_object_mem(size_t off, size_t pos);
void zero_bytes(X86& x, const Mem& base, size_t bytes);
void emit_rel_jump(X86& x,
                   std::vector<Patch>& patches,
                   uint8_t kind,
                   const std::string& target);
uint8_t cmp_cc(const std::string& op);
std::vector<Type> call_types(const Program& program, const Instruction& ins);
void emit_param_store(X86& x,
                      const Function& fn,
                      size_t index,
                      size_t& reg,
                      size_t& fp,
                      size_t& stack);

}  // namespace host
}  // namespace pa31
