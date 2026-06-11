#include "pa31_host_object.h"
#include <algorithm>
#include <cstdint>
#include <cstdlib>
#include <fstream>
#include <map>
#include <set>
#include <stdexcept>
using namespace std;
namespace pa31 {
namespace {
using lowir2cy86::Block;
using lowir2cy86::Function;
using lowir2cy86::Global;
using lowir2cy86::GlobalDataItem;
using lowir2cy86::InstrKind;
using lowir2cy86::Instruction;
using lowir2cy86::Parameter;
using lowir2cy86::Program;
using lowir2cy86::Span;
using lowir2cy86::Type;
using lowir2cy86::TypeKind;
using lowir2cy86::Value;
using lowir2cy86::ValueKind;
const uint32_t SHT_PROGBITS = 1;
const uint32_t SHT_SYMTAB = 2;
const uint32_t SHT_STRTAB = 3;
const uint32_t SHT_RELA = 4;
const uint64_t SHF_WRITE = 0x1;
const uint64_t SHF_ALLOC = 0x2;
const uint64_t SHF_EXECINSTR = 0x4;
const uint32_t R_X86_64_64 = 1;
const uint32_t R_X86_64_PC32 = 2;
const uint32_t R_X86_64_PLT32 = 4;
size_t align_up(size_t value, size_t align)
{
	if (align <= 1)
		return value;
	const size_t rem = value % align;
	return rem == 0 ? value : value + align - rem;
}
uint64_t parse_int(const string& text)
{
	return static_cast<uint64_t>(strtoll(text.c_str(), NULL, 0));
}
bool is_identifier(const string& text)
{
	if (text.empty() || !(isalpha(text[0]) || text[0] == '_'))
		return false;
	for (size_t i = 1; i < text.size(); ++i)
		if (!(isalnum(text[i]) || text[i] == '_'))
			return false;
	return true;
}
string metadata(const lowir2cy86::Metadata& items, const string& key)
{
	return lowir2cy86::metadata_value(items, key);
}
string host_global_symbol(const Global& global)
{
	const string object = metadata(global.metadata, "object");
	return object.empty() ? lowir2cy86::lowir_symbol_body(global.name) : object;
}
string simple_cpp_function_symbol(const string& body)
{
	return "_Z" + to_string(body.size()) + body + "v";
}
string host_function_symbol(const Function& fn)
{
	const string object = metadata(fn.metadata, "object");
	if (!object.empty())
		return object;
	const string body = lowir2cy86::lowir_symbol_body(fn.name);
	if (body == "main" || metadata(fn.metadata, "linkage") == "c")
		return body;
	if (body.find("__") == string::npos && is_identifier(body))
		return simple_cpp_function_symbol(body);
	return body;
}
string target_symbol(const Program& program, const string& name);
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
void uleb(Blob& b, uint64_t value)
{
	do {
		uint8_t byte = static_cast<uint8_t>(value & 0x7f);
		value >>= 7;
		if (value)
			byte |= 0x80;
		b.u8(byte);
	} while (value);
}
void sleb(Blob& b, int64_t value)
{
	bool more = true;
	while (more)
	{
		uint8_t byte = static_cast<uint8_t>(value & 0x7f);
		const bool sign = (byte & 0x40) != 0;
		value >>= 7;
		more = !((value == 0 && !sign) || (value == -1 && sign));
		if (more)
			byte |= 0x80;
		b.u8(byte);
	}
}
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
	Section& rodata()
	{
		return section(".rodata", SHT_PROGBITS, SHF_ALLOC, 8);
	}
	Section& data()
	{
		return section(".data", SHT_PROGBITS,
		               SHF_ALLOC | SHF_WRITE, 8);
	}
	Section& eh_frame()
	{
		return section(".eh_frame", SHT_PROGBITS, SHF_ALLOC, 8);
	}
	Section& gcc_except_table()
	{
		return section(".gcc_except_table", SHT_PROGBITS, SHF_ALLOC, 4);
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
struct OutSection
{
	Section sec;
	uint64_t offset;
	uint64_t size;
	uint32_t name_off;
};
struct SymOut
{
	Symbol sym;
	uint16_t shndx;
	uint32_t name_off;
};
void append_string(Blob& b, const string& s, uint32_t& off)
{
	off = static_cast<uint32_t>(b.pos());
	for (size_t i = 0; i < s.size(); ++i)
		b.u8(static_cast<uint8_t>(s[i]));
	b.u8(0);
}
uint64_t r_info(uint32_t sym, uint32_t type)
{
	return (static_cast<uint64_t>(sym) << 32) | type;
}
void ObjectFile::write(const string& outfile)
{
	vector<Section> base;
	for (size_t i = 0; i < sections.size(); ++i)
		if (sections[i].keep || !sections[i].bytes.data.empty() ||
		    !sections[i].relocs.empty())
			base.push_back(sections[i]);
	map<string, uint16_t> sec_index;
	for (size_t i = 0; i < base.size(); ++i)
		sec_index[base[i].name] = static_cast<uint16_t>(i + 1);
	vector<Symbol> local_syms;
	vector<Symbol> global_syms;
	for (size_t i = 0; i < base.size(); ++i)
	{
		Symbol s;
		s.name = base[i].name;
		s.bind = 0;
		s.type = 3;
		s.section = base[i].name;
		s.value = 0;
		s.size = 0;
		s.defined = true;
		local_syms.push_back(s);
	}
	set<string> known;
	for (size_t i = 0; i < symbols.size(); ++i)
	{
		if (!symbols[i].defined || sec_index.count(symbols[i].section))
		{
			(symbols[i].bind == 0 ? local_syms : global_syms).push_back(symbols[i]);
			known.insert(symbols[i].name);
		}
	}
	for (size_t i = 0; i < base.size(); ++i)
		for (size_t r = 0; r < base[i].relocs.size(); ++r)
			if (!sec_index.count(base[i].relocs[r].symbol) &&
			    !known.count(base[i].relocs[r].symbol))
			{
				Symbol s;
				s.name = base[i].relocs[r].symbol;
				s.bind = 1;
				s.type = 0;
				s.value = s.size = 0;
				s.defined = false;
				global_syms.push_back(s);
				known.insert(s.name);
			}
	vector<SymOut> symout;
	SymOut nullsym;
	nullsym.sym.name = "";
	nullsym.sym.bind = 0;
	nullsym.sym.type = 0;
	nullsym.sym.value = 0;
	nullsym.sym.size = 0;
	nullsym.sym.defined = false;
	nullsym.shndx = 0;
	nullsym.name_off = 0;
	symout.push_back(nullsym);
	for (size_t i = 0; i < local_syms.size(); ++i)
	{
		SymOut so;
		so.sym = local_syms[i];
		so.shndx = so.sym.defined ? sec_index[so.sym.section] : 0;
		so.name_off = 0;
		symout.push_back(so);
	}
	const uint32_t first_global = static_cast<uint32_t>(symout.size());
	for (size_t i = 0; i < global_syms.size(); ++i)
	{
		SymOut so;
		so.sym = global_syms[i];
		so.shndx = so.sym.defined ? sec_index[so.sym.section] : 0;
		so.name_off = 0;
		symout.push_back(so);
	}
	Blob strtab;
	strtab.u8(0);
	map<string, uint32_t> sym_index;
	for (size_t i = 1; i < symout.size(); ++i)
	{
		append_string(strtab, symout[i].sym.name, symout[i].name_off);
		sym_index[symout[i].sym.name] = static_cast<uint32_t>(i);
	}
	vector<Section> rela_sections;
	const uint32_t rela_count_hint = 0;
	(void)rela_count_hint;
	for (size_t i = 0; i < base.size(); ++i)
	{
		if (base[i].relocs.empty())
			continue;
		Section rela;
		rela.name = ".rela" + base[i].name;
		rela.type = SHT_RELA;
		rela.align = 8;
		rela.entsize = 24;
		rela.info = sec_index[base[i].name];
		for (size_t r = 0; r < base[i].relocs.size(); ++r)
		{
			const Reloc& rel = base[i].relocs[r];
			map<string, uint32_t>::const_iterator sit = sym_index.find(rel.symbol);
			if (sit == sym_index.end())
				throw runtime_error("missing relocation symbol");
			rela.bytes.u64(rel.offset);
			rela.bytes.u64(r_info(sit->second, rel.type));
			rela.bytes.u64(static_cast<uint64_t>(rel.addend));
		}
		rela_sections.push_back(rela);
	}
	const uint16_t symtab_index =
		static_cast<uint16_t>(1 + base.size() + rela_sections.size());
	const uint16_t strtab_index = symtab_index + 1;
	for (size_t i = 0; i < rela_sections.size(); ++i)
		rela_sections[i].link = symtab_index;
	Blob symtab;
	for (size_t i = 0; i < symout.size(); ++i)
	{
		symtab.u32(symout[i].name_off);
		symtab.u8(static_cast<uint8_t>((symout[i].sym.bind << 4) |
		                               (symout[i].sym.type & 0xf)));
		symtab.u8(0);
		symtab.u16(symout[i].shndx);
		symtab.u64(symout[i].sym.value);
		symtab.u64(symout[i].sym.size);
	}
	Section symsec;
	symsec.name = ".symtab";
	symsec.type = SHT_SYMTAB;
	symsec.align = 8;
	symsec.entsize = 24;
	symsec.link = strtab_index;
	symsec.info = first_global;
	symsec.bytes = symtab;
	Section strsec;
	strsec.name = ".strtab";
	strsec.type = SHT_STRTAB;
	strsec.align = 1;
	strsec.bytes = strtab;
	Section shstr;
	shstr.name = ".shstrtab";
	shstr.type = SHT_STRTAB;
	shstr.align = 1;
	shstr.bytes.u8(0);
	vector<OutSection> outsecs;
	for (size_t i = 0; i < base.size(); ++i)
	{
		OutSection os;
		os.sec = base[i];
		append_string(shstr.bytes, os.sec.name, os.name_off);
		outsecs.push_back(os);
	}
	for (size_t i = 0; i < rela_sections.size(); ++i)
	{
		OutSection os;
		os.sec = rela_sections[i];
		append_string(shstr.bytes, os.sec.name, os.name_off);
		outsecs.push_back(os);
	}
	OutSection symos;
	symos.sec = symsec;
	append_string(shstr.bytes, symos.sec.name, symos.name_off);
	outsecs.push_back(symos);
	OutSection stros;
	stros.sec = strsec;
	append_string(shstr.bytes, stros.sec.name, stros.name_off);
	outsecs.push_back(stros);
	OutSection shos;
	append_string(shstr.bytes, shstr.name, shos.name_off);
	shos.sec = shstr;
	outsecs.push_back(shos);
	uint64_t off = 64;
	for (size_t i = 0; i < outsecs.size(); ++i)
	{
		off = align_up(off, outsecs[i].sec.align);
		outsecs[i].offset = off;
		outsecs[i].size = outsecs[i].sec.bytes.data.size();
		off += outsecs[i].size;
	}
	const uint64_t shoff = align_up(off, 8);
	Blob file;
	file.u8(0x7f); file.u8('E'); file.u8('L'); file.u8('F');
	file.u8(2); file.u8(1); file.u8(1); file.u8(0);
	for (int i = 0; i < 8; ++i) file.u8(0);
	file.u16(1);
	file.u16(0x3e);
	file.u32(1);
	file.u64(0);
	file.u64(0);
	file.u64(shoff);
	file.u32(0);
	file.u16(64);
	file.u16(0);
	file.u16(0);
	file.u16(64);
	file.u16(static_cast<uint16_t>(outsecs.size() + 1));
	file.u16(static_cast<uint16_t>(outsecs.size()));
	for (size_t i = 0; i < outsecs.size(); ++i)
	{
		file.align(outsecs[i].sec.align);
		file.data.insert(file.data.end(), outsecs[i].sec.bytes.data.begin(),
		                 outsecs[i].sec.bytes.data.end());
	}
	file.align(8);
	for (int i = 0; i < 64; ++i) file.u8(0);
	for (size_t i = 0; i < outsecs.size(); ++i)
	{
		const Section& s = outsecs[i].sec;
		file.u32(outsecs[i].name_off);
		file.u32(s.type);
		file.u64(s.flags);
		file.u64(0);
		file.u64(outsecs[i].offset);
		file.u64(outsecs[i].size);
		file.u32(s.link);
		file.u32(s.info);
		file.u64(s.align);
		file.u64(s.entsize);
	}
	ofstream out(outfile.c_str(), ios::binary);
	if (!out)
		throw runtime_error("cannot open host object output");
	out.write(reinterpret_cast<const char*>(&file.data[0]),
	          static_cast<streamsize>(file.data.size()));
	if (!out)
		throw runtime_error("cannot write host object");
}
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
	void imul_imm(int reg, int32_t imm)
	{
		rex(true, reg, 0, reg);
		u8(0x69);
		modrm(3, reg, reg);
		u32(static_cast<uint32_t>(imm));
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
	CatchInfo() : selector(0) {}
};
struct FunctionInfo
{
	string symbol;
	size_t start;
	size_t size;
	bool has_lsda;
	size_t lsda_offset;
	FunctionInfo() : start(0), size(0), has_lsda(false), lsda_offset(0) {}
};
struct Unit
{
	Program& program;
	ObjectFile& obj;
	map<string, string> globals;
	map<string, string> functions;
	vector<FunctionInfo> infos;
	Unit(Program& p, ObjectFile& o) : program(p), obj(o) {}
	void prepare_symbols();
	void emit_globals();
	void emit_functions();
	void emit_eh_frame();
};
string target_symbol(const Program& program, const string& name)
{
	map<string, size_t>::const_iterator git = program.global_by_name.find(name);
	if (git != program.global_by_name.end())
		return host_global_symbol(program.globals[git->second]);
	map<string, size_t>::const_iterator fit = program.function_by_name.find(name);
	if (fit != program.function_by_name.end())
		return host_function_symbol(program.functions[fit->second]);
	return lowir2cy86::lowir_symbol_body(name);
}
bool skip_global_definition(const Global& g)
{
	const string obj = metadata(g.metadata, "object");
	return obj == "_ZTIi" || obj == "_ZTSi" ||
	       obj == "_ZTVN10__cxxabiv123__fundamental_type_infoE" ||
	       (!obj.empty() && obj[0] == '@') ||
	       lowir2cy86::lowir_symbol_body(g.name).find("__ehobj_") == 0;
}
uint8_t symbol_bind(const lowir2cy86::Metadata& md)
{
	const string b = metadata(md, "binding");
	if (b == "weak")
		return 2;
	if (b == "internal")
		return 0;
	return 1;
}
void Unit::prepare_symbols()
{
	for (size_t i = 0; i < program.globals.size(); ++i)
		globals[program.globals[i].name] = host_global_symbol(program.globals[i]);
	for (size_t i = 0; i < program.functions.size(); ++i)
		functions[program.functions[i].name] = host_function_symbol(program.functions[i]);
}
void write_integer(Blob& b, const Type& type, uint64_t value)
{
	const size_t n = type.size == 0 ? 8 : type.size;
	for (size_t i = 0; i < n; ++i)
		b.u8(static_cast<uint8_t>(value >> (i * 8)));
}
void emit_global_item(Unit& unit, Section& sec, const GlobalDataItem& item)
{
	if (item.kind == "zero")
	{
		for (size_t i = 0; i < item.zero_bytes; ++i)
			sec.bytes.u8(0);
	}
	else if (item.kind == "addr")
	{
		const size_t off = sec.bytes.pos();
		sec.bytes.u64(0);
		unit.obj.reloc(sec, off, target_symbol(unit.program, item.target),
		               R_X86_64_64, item.has_addend ? item.addend : 0);
	}
	else
		write_integer(sec.bytes, item.type, parse_int(item.literal));
}
void Unit::emit_globals()
{
	for (size_t i = 0; i < program.globals.size(); ++i)
	{
		const Global& g = program.globals[i];
		if (g.declaration || skip_global_definition(g))
			continue;
		const bool readonly = metadata(g.metadata, "storage") == "readonly";
		Section& sec = readonly ? obj.rodata() : obj.data();
		const size_t align = g.has_type ? g.type.align : 1;
		sec.bytes.align(align);
		const size_t off = sec.bytes.pos();
		const string sym = globals[g.name];
		if (g.init.kind == "zero")
			for (size_t n = 0; n < lowir2cy86::storage_size(g.type); ++n)
				sec.bytes.u8(0);
		else if (g.init.kind == "literal")
			write_integer(sec.bytes, g.type, parse_int(g.init.literal));
		else if (g.init.kind == "addr")
		{
			sec.bytes.u64(0);
			obj.reloc(sec, off, target_symbol(program, g.init.target),
			          R_X86_64_64, g.init.has_addend ? g.init.addend : 0);
		}
		else
			for (size_t n = 0; n < g.data.size(); ++n)
				emit_global_item(*this, sec, g.data[n]);
		obj.symbol(sym, symbol_bind(g.metadata), 1, sec.name, off,
		           sec.bytes.pos() - off);
	}
}
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
	map<string, CatchInfo> catches;
	set<string> landing_blocks;
	set<string> cleanup_blocks;
	size_t frame_size;
	size_t exc_off;
	size_t sel_off;
	bool has_eh;
	FuncGen(Unit& u, const Function& f)
		: unit(u), fn(f), text(u.obj.text()), x(text), frame_size(0),
		  exc_off(0), sel_off(0), has_eh(false) {}
	void emit(FunctionInfo& info);
	void emit_instruction(const Instruction& ins, const string& block);
	void load_value(const Value& v, const Type& target, int reg);
	void store_value(const Value& dst, const Type& type, int reg);
	void storage_address(const Value& v, int reg);
	void copy_bytes(const Value& src, const Value& dst, const Span& span);
	Type value_type(const Value& v) const;
	Mem frame_mem(size_t off) const { return Mem(RBP, -static_cast<int32_t>(off)); }
	void store_temp(const string& name, const Type& type, int reg);
	void emit_call(const Instruction& ins);
	void emit_return(const Instruction& ins);
	void emit_branch(const Instruction& ins);
	void patch_jumps(size_t base);
	void finish_lsda(FunctionInfo& info, size_t base);
	void save_landing_registers();
};
Type FuncGen::value_type(const Value& v) const
{
	if (v.kind == ValueKind::Temp)
	{
		map<string, Type>::const_iterator p = fn.param_types.find(v.text);
		if (p != fn.param_types.end()) return p->second;
		map<string, Type>::const_iterator t = fn.temp_types.find(v.text);
		if (t != fn.temp_types.end()) return t->second;
	}
	if (v.kind == ValueKind::Slot)
		return fn.slot_types.find(v.text)->second;
	if (v.kind == ValueKind::Global)
	{
		map<string, size_t>::const_iterator g = unit.program.global_by_name.find(v.text);
		if (g != unit.program.global_by_name.end() &&
		    unit.program.globals[g->second].has_type)
			return unit.program.globals[g->second].type;
		return lowir2cy86::parse_type_text("ptr");
	}
	return Type();
}
Mem frame_object_mem(size_t off, size_t pos)
{
	return Mem(RBP, -static_cast<int32_t>(off) + static_cast<int32_t>(pos));
}
int width_for(const Type& type)
{
	if (lowir2cy86::is_ptr_type(type)) return 64;
	if (lowir2cy86::is_integer_type(type)) return max(8, type.bits);
	return 64;
}
size_t object_offset(const Function& fn, const Value& v)
{
	if (v.kind == ValueKind::Temp)
	{
		map<string, size_t>::const_iterator p = fn.param_offsets.find(v.text);
		if (p != fn.param_offsets.end()) return p->second;
		return fn.temp_offsets.find(v.text)->second;
	}
	return fn.slot_offsets.find(v.text)->second;
}
void FuncGen::store_temp(const string& name, const Type& type, int reg)
{
	map<string, size_t>::const_iterator p = fn.param_offsets.find(name);
	const size_t off = p != fn.param_offsets.end() ? p->second :
	                   fn.temp_offsets.find(name)->second;
	x.mov_mr(width_for(type), frame_mem(off), reg);
}
void FuncGen::load_value(const Value& v, const Type& target, int reg)
{
	if (v.kind == ValueKind::Literal)
	{
		x.mov_imm(width_for(target), reg, parse_int(v.text));
		return;
	}
	if (v.kind == ValueKind::Global)
	{
		Mem mem(RIP, 0);
		x.mov_rm(width_for(target), reg, mem);
		unit.obj.reloc(text, x.pos() - 4, target_symbol(unit.program, v.text),
		               R_X86_64_PC32, -4);
		if (width_for(target) == 8)
			x.movzx8(reg, reg);
		return;
	}
	if (v.kind == ValueKind::Slot || v.kind == ValueKind::Temp)
	{
		const Type src = value_type(v);
		const size_t off = object_offset(fn, v);
		x.mov_rm(width_for(src), reg, frame_mem(off));
		if (width_for(src) == 8)
			x.movzx8(reg, reg);
		if (width_for(target) == 64 && width_for(src) == 32 &&
		    lowir2cy86::is_signed_integer_type(src))
		{
			x.rex(true, reg, 0, reg);
			x.u8(0x63);
			x.modrm(3, reg, reg);
		}
		return;
	}
	throw runtime_error("unsupported value load");
}
void FuncGen::store_value(const Value& dst, const Type& type, int reg)
{
	if (dst.kind == ValueKind::Slot)
		x.mov_mr(width_for(type), frame_mem(fn.slot_offsets.find(dst.text)->second), reg);
	else if (dst.kind == ValueKind::Global)
	{
		Mem mem(RIP, 0);
		x.mov_mr(width_for(type), mem, reg);
		unit.obj.reloc(text, x.pos() - 4, target_symbol(unit.program, dst.text),
		               R_X86_64_PC32, -4);
	}
	else if (dst.kind == ValueKind::Temp)
	{
		load_value(dst, lowir2cy86::parse_type_text("ptr"), R11);
		x.mov_mr(width_for(type), Mem(R11, 0), reg);
	}
	else
		throw runtime_error("unsupported store destination");
}
void FuncGen::storage_address(const Value& v, int reg)
{
	if (v.kind == ValueKind::Slot || (v.kind == ValueKind::Temp &&
	    lowir2cy86::is_obj_type(value_type(v))))
	{
		x.lea(reg, frame_mem(object_offset(fn, v)));
		return;
	}
	if (v.kind == ValueKind::Global)
	{
		x.lea(reg, Mem(RIP, 0));
		unit.obj.reloc(text, x.pos() - 4, target_symbol(unit.program, v.text),
		               R_X86_64_PC32, -4);
		return;
	}
	if (v.kind == ValueKind::Temp)
	{
		load_value(v, lowir2cy86::parse_type_text("ptr"), reg);
		return;
	}
	throw runtime_error("unsupported address source");
}
void FuncGen::copy_bytes(const Value& src, const Value& dst, const Span& span)
{
	storage_address(src, R10);
	storage_address(dst, R11);
	for (size_t pos = 0; pos < span.bytes;)
	{
		const size_t left = span.bytes - pos;
		const int w = left >= 8 ? 64 : (left >= 4 ? 32 : (left >= 2 ? 16 : 8));
		x.mov_rm(w, RAX, Mem(R10, static_cast<int32_t>(pos)));
		x.mov_mr(w, Mem(R11, static_cast<int32_t>(pos)), RAX);
		pos += static_cast<size_t>(w / 8);
	}
}
void zero_bytes(X86& x, const Mem& base, size_t bytes)
{
	x.mov_imm(32, RAX, 0);
	for (size_t pos = 0; pos < bytes;)
	{
		const size_t left = bytes - pos;
		const int w = left >= 8 ? 64 : (left >= 4 ? 32 : (left >= 2 ? 16 : 8));
		x.mov_mr(w, Mem(base.base, base.disp + static_cast<int32_t>(pos)), RAX);
		pos += static_cast<size_t>(w / 8);
	}
}
void FuncGen::save_landing_registers()
{
	if (!has_eh)
		return;
	x.mov_mr(64, frame_mem(exc_off), RAX);
	x.mov_mr(64, frame_mem(sel_off), RDX);
}
void emit_rel_jump(X86& x, vector<Patch>& patches, uint8_t kind, const string& target)
{
	if (kind == 0)
		x.u8(0xe9);
	else
	{
		x.u8(0x0f);
		x.u8(kind);
	}
	const size_t at = x.pos();
	x.u32(0);
	Patch p;
	p.at = at;
	p.target = target;
	patches.push_back(p);
}
void FuncGen::emit_branch(const Instruction& ins)
{
	load_value(ins.a, value_type(ins.a), RAX);
	x.mov_imm(64, R10, 0);
	x.cmp(64, RAX, R10);
	emit_rel_jump(x, jumps, 0x85, ins.target);
	emit_rel_jump(x, jumps, 0, ins.target_false);
}
void FuncGen::emit_return(const Instruction& ins)
{
	if (!lowir2cy86::is_void_type(ins.type))
	{
		if (lowir2cy86::is_obj_type(ins.type))
		{
			storage_address(ins.a, R10);
			x.mov_rm(lowir2cy86::direct_object_abi_chunk_width_bits(ins.type, 0),
			         RAX, Mem(R10, 0));
			if (lowir2cy86::direct_object_abi_slots(ins.type) == 2)
				x.mov_rm(lowir2cy86::direct_object_abi_chunk_width_bits(ins.type, 1),
				         RDX, Mem(R10, 8));
		}
		else
			load_value(ins.a, ins.type, RAX);
	}
	x.u8(0xc9);
	x.u8(0xc3);
}
vector<Type> call_types(const Program& program, const Instruction& ins)
{
	vector<Type> out;
	if (ins.signature.present)
		for (size_t i = 0; i < ins.signature.params.size(); ++i)
			out.push_back(ins.signature.params[i].type);
	else if (ins.a.kind == ValueKind::Function)
	{
		map<string, size_t>::const_iterator f = program.function_by_name.find(ins.a.text);
		if (f != program.function_by_name.end())
			for (size_t i = 0; i < program.functions[f->second].params.size(); ++i)
				out.push_back(program.functions[f->second].params[i].type);
	}
	return out;
}
void FuncGen::emit_call(const Instruction& ins)
{
	static const int regs[] = {RDI, RSI, RDX, RCX, R8, R9};
	vector<Type> types = call_types(unit.program, ins);
	size_t reg_index = 0;
	for (size_t i = 0; i < ins.args.size(); ++i)
	{
		const Type type = i < types.size() ? types[i] : value_type(ins.args[i]);
		if (lowir2cy86::is_obj_type(type) && lowir2cy86::is_direct_object_abi(type))
		{
			storage_address(ins.args[i], R11);
			for (size_t c = 0; c < lowir2cy86::direct_object_abi_slots(type); ++c)
			{
				if (reg_index >= 6) throw runtime_error("stack object args unsupported");
				x.mov_rm(lowir2cy86::direct_object_abi_chunk_width_bits(type, c),
				         regs[reg_index++], Mem(R11, static_cast<int32_t>(c * 8)));
			}
		}
		else
		{
			if (reg_index >= 6) throw runtime_error("stack args unsupported");
			load_value(ins.args[i], type, regs[reg_index++]);
		}
	}
	if (ins.a.kind == ValueKind::Function)
	{
		x.u8(0xe8);
		const size_t off = x.pos();
		x.u32(0);
		unit.obj.reloc(text, off, target_symbol(unit.program, ins.a.text),
		               R_X86_64_PLT32, -4);
	}
	else
	{
		load_value(ins.a, lowir2cy86::parse_type_text("ptr"), R11);
		x.rex(true, 2, 0, R11);
		x.u8(0xff);
		x.modrm(3, 2, R11);
	}
	if (ins.has_dest && !lowir2cy86::is_void_type(ins.type))
	{
		if (lowir2cy86::is_obj_type(ins.type))
		{
			const size_t off = fn.temp_offsets.find(ins.dest)->second;
			x.mov_mr(lowir2cy86::direct_object_abi_chunk_width_bits(ins.type, 0),
			         frame_object_mem(off, 0), RAX);
			if (lowir2cy86::direct_object_abi_slots(ins.type) == 2)
				x.mov_mr(lowir2cy86::direct_object_abi_chunk_width_bits(ins.type, 1),
				         frame_object_mem(off, 8), RDX);
		}
		else
			store_temp(ins.dest, ins.type, RAX);
	}
}
uint8_t cmp_cc(const string& op)
{
	if (op == "eq") return 0x94;
	if (op == "ne") return 0x95;
	if (op == "lt") return 0x9c;
	if (op == "gt") return 0x9f;
	if (op == "le") return 0x9e;
	if (op == "ge") return 0x9d;
	throw runtime_error("unsupported cmp");
}
void FuncGen::emit_instruction(const Instruction& ins, const string& block)
{
	if (ins.kind == InstrKind::Const)
	{ x.mov_imm(width_for(ins.type), RAX, parse_int(ins.a.text)); store_temp(ins.dest, ins.type, RAX); }
	else if (ins.kind == InstrKind::Copy)
	{ load_value(ins.a, ins.type, RAX); store_temp(ins.dest, ins.type, RAX); }
	else if (ins.kind == InstrKind::Addr)
	{ storage_address(ins.a, RAX); store_temp(ins.dest, lowir2cy86::parse_type_text("ptr"), RAX); }
	else if (ins.kind == InstrKind::Load)
	{ storage_address(ins.a, R11); x.mov_rm(width_for(ins.type), RAX, Mem(R11, 0)); store_temp(ins.dest, ins.type, RAX); }
	else if (ins.kind == InstrKind::Store)
	{ load_value(ins.a, ins.type, RAX); store_value(ins.b, ins.type, RAX); }
	else if (ins.kind == InstrKind::Index)
	{
		load_value(ins.a, lowir2cy86::parse_type_text("ptr"), RAX);
		load_value(ins.b, lowir2cy86::parse_type_text("i64"), R10);
		if (ins.op == "array_element" && ins.type.size > 1)
			x.imul_imm(R10, static_cast<int32_t>(ins.type.size));
		x.binary(0x01, 64, RAX, R10);
		store_temp(ins.dest, lowir2cy86::parse_type_text("ptr"), RAX);
	}
	else if (ins.kind == InstrKind::Unary)
	{ load_value(ins.a, ins.type, RAX); store_temp(ins.dest, ins.type, RAX); }
	else if (ins.kind == InstrKind::Binary)
	{
		load_value(ins.a, ins.type, RAX); load_value(ins.b, ins.type, R10);
		if (ins.op == "add") x.binary(0x01, width_for(ins.type), RAX, R10);
		else if (ins.op == "sub") x.binary(0x29, width_for(ins.type), RAX, R10);
		else if (ins.op == "mul") x.imul(width_for(ins.type), RAX, R10);
		else throw runtime_error("unsupported binary");
		store_temp(ins.dest, ins.type, RAX);
	}
	else if (ins.kind == InstrKind::Cmp)
	{
		load_value(ins.a, ins.type, RAX); load_value(ins.b, ins.type, R10);
		x.cmp(width_for(ins.type), RAX, R10); x.setcc(cmp_cc(ins.op));
		store_temp(ins.dest, ins.type, RAX);
	}
	else if (ins.kind == InstrKind::Convert)
	{ load_value(ins.a, ins.type, RAX); store_temp(ins.dest, ins.type, RAX); }
	else if (ins.kind == InstrKind::Call)
	{
		EhRange call_range;
		const bool protected_call = !active_ranges.empty();
		if (protected_call)
		{
			call_range = active_ranges.back();
			call_range.start = x.pos();
		}
		emit_call(ins);
		if (protected_call)
		{
			call_range.end = x.pos();
			if (call_range.end > call_range.start)
				ranges.push_back(call_range);
		}
	}
	else if (ins.kind == InstrKind::CopyObj)
	{
		EhRange copy_range;
		const bool protected_copy = !active_ranges.empty() &&
			cleanup_blocks.count(active_ranges.back().target) != 0;
		if (protected_copy)
		{
			copy_range = active_ranges.back();
			copy_range.start = x.pos();
		}
		copy_bytes(ins.a, ins.b, ins.span);
		if (protected_copy)
		{
			copy_range.end = x.pos();
			if (copy_range.end > copy_range.start)
				ranges.push_back(copy_range);
		}
	}
	else if (ins.kind == InstrKind::ZeroInit)
	{ storage_address(ins.a, R11); zero_bytes(x, Mem(R11, 0), ins.span.bytes); }
	else if (ins.kind == InstrKind::EhTry || ins.kind == InstrKind::EhCleanup)
	{
		if (!ins.target.empty())
		{
			EhRange r; r.start = x.pos(); r.target = ins.target;
			active_ranges.push_back(r); landing_blocks.insert(ins.target);
			if (ins.kind == InstrKind::EhCleanup)
				cleanup_blocks.insert(ins.target);
		}
	}
	else if (ins.kind == InstrKind::EhCatch)
	{ CatchInfo c; c.type_symbol = target_symbol(unit.program, ins.a.text); c.selector = ins.order_a; catches[block] = c; }
	else if (ins.kind == InstrKind::EhEnd)
	{
		if (!active_ranges.empty())
			active_ranges.pop_back();
	}
	else if (ins.kind == InstrKind::Exception)
	{ x.mov_rm(64, RAX, frame_mem(exc_off)); store_temp(ins.dest, ins.type, RAX); }
	else if (ins.kind == InstrKind::ExceptionSelector)
	{ x.mov_rm(64, RAX, frame_mem(sel_off)); store_temp(ins.dest, ins.type, RAX); }
	else if (ins.kind == InstrKind::Resume)
	{
		x.mov_rm(64, RDI, frame_mem(exc_off));
		EhRange resume_range;
		resume_range.start = x.pos();
		resume_range.target = "";
		x.u8(0xe8); size_t off = x.pos(); x.u32(0);
		unit.obj.reloc(text, off, "_Unwind_Resume", R_X86_64_PLT32, -4);
		resume_range.end = x.pos();
		ranges.push_back(resume_range);
		x.u8(0x0f); x.u8(0x0b);
	}
	else if (ins.kind == InstrKind::Jump) emit_rel_jump(x, jumps, 0, ins.target);
	else if (ins.kind == InstrKind::Branch) emit_branch(ins);
	else if (ins.kind == InstrKind::Return) emit_return(ins);
	else
		throw runtime_error("unsupported LowIR instruction for host object");
}
void FuncGen::patch_jumps(size_t base)
{
	for (size_t i = 0; i < jumps.size(); ++i)
	{
		const size_t target = base + block_offsets[jumps[i].target];
		const int64_t disp = static_cast<int64_t>(target) -
		                     static_cast<int64_t>(jumps[i].at + 4);
		text.bytes.patch32(jumps[i].at, static_cast<uint32_t>(disp));
	}
}
void emit_param_store(X86& x, const Function& fn, size_t index, size_t& reg)
{
	static const int regs[] = {RDI, RSI, RDX, RCX, R8, R9};
	const Parameter& p = fn.params[index];
	const size_t off = fn.param_offsets.find(p.name)->second;
	if (lowir2cy86::is_obj_type(p.type) && lowir2cy86::is_direct_object_abi(p.type))
	{
		for (size_t c = 0; c < lowir2cy86::direct_object_abi_slots(p.type); ++c)
			x.mov_mr(lowir2cy86::direct_object_abi_chunk_width_bits(p.type, c),
			         frame_object_mem(off, c * 8), regs[reg++]);
	}
	else
		x.mov_mr(width_for(p.type), Mem(RBP, -static_cast<int32_t>(off)), regs[reg++]);
}
void FuncGen::emit(FunctionInfo& info)
{
	for (size_t b = 0; b < fn.blocks.size(); ++b)
		for (size_t i = 0; i < fn.blocks[b].instructions.size(); ++i)
			if (fn.blocks[b].instructions[i].kind == InstrKind::EhTry ||
			    fn.blocks[b].instructions[i].kind == InstrKind::EhCleanup ||
			    fn.blocks[b].instructions[i].kind == InstrKind::Exception ||
			    fn.blocks[b].instructions[i].kind == InstrKind::Resume)
				has_eh = true;
	frame_size = fn.stack_size;
	if (has_eh)
	{
		frame_size = align_up(frame_size, 8); exc_off = frame_size += 8;
		sel_off = frame_size += 8;
	}
	frame_size = align_up(frame_size, 16);
	text.bytes.align(16);
	const size_t base = x.pos();
	info.start = base;
	info.symbol = host_function_symbol(fn);
	x.u8(0x55);
	x.rex(true); x.u8(0x89); x.modrm(3, RSP, RBP);
	x.sub_rsp(frame_size);
	size_t reg = 0;
	for (size_t i = 0; i < fn.params.size(); ++i)
		emit_param_store(x, fn, i, reg);
	for (size_t b = 0; b < fn.blocks.size(); ++b)
	{
		block_offsets[fn.blocks[b].name] = x.pos() - base;
		if (landing_blocks.count(fn.blocks[b].name))
			save_landing_registers();
		for (size_t i = 0; i < fn.blocks[b].instructions.size(); ++i)
			emit_instruction(fn.blocks[b].instructions[i], fn.blocks[b].name);
	}
	info.size = x.pos() - base;
	unit.obj.symbol(info.symbol, symbol_bind(fn.metadata), 2, ".text", base, info.size);
	patch_jumps(base);
	finish_lsda(info, base);
}
void append_uleb_to(vector<unsigned char>& out, uint64_t value)
{
	Blob b; uleb(b, value); out.insert(out.end(), b.data.begin(), b.data.end());
}
void append_sleb_to(vector<unsigned char>& out, int64_t value)
{
	Blob b; sleb(b, value); out.insert(out.end(), b.data.begin(), b.data.end());
}
void FuncGen::finish_lsda(FunctionInfo& info, size_t base)
{
	if (ranges.empty())
		return;
	sort(ranges.begin(), ranges.end(),
	     [](const EhRange& a, const EhRange& b) { return a.start < b.start; });
	map<string, int> type_index;
	vector<string> types;
	vector<unsigned char> call_table;
	vector<unsigned char> action_table;
	size_t cursor = 0;
	for (size_t i = 0; i < ranges.size(); ++i)
	{
		const size_t range_start = ranges[i].start - base;
		const size_t range_end = ranges[i].end - base + 1;
		if (range_start > cursor)
		{
			append_uleb_to(call_table, cursor);
			append_uleb_to(call_table, range_start - cursor);
			append_uleb_to(call_table, 0);
			append_uleb_to(call_table, 0);
		}
		const size_t lp = ranges[i].target.empty()
			? 0 : block_offsets[ranges[i].target];
		int action = 0;
		map<string, CatchInfo>::const_iterator c = ranges[i].target.empty()
			? catches.end() : catches.find(ranges[i].target);
		if (c != catches.end())
		{
			if (!type_index.count(c->second.type_symbol))
			{
				type_index[c->second.type_symbol] = static_cast<int>(types.size() + 1);
				types.push_back(c->second.type_symbol);
			}
			action = static_cast<int>(action_table.size() + 1);
			append_sleb_to(action_table, type_index[c->second.type_symbol]);
			append_sleb_to(action_table, 0);
		}
		append_uleb_to(call_table, range_start);
		append_uleb_to(call_table, range_end - range_start);
		append_uleb_to(call_table, lp);
		append_uleb_to(call_table, action);
		cursor = max(cursor, range_end);
	}
	Section& lsda = unit.obj.gcc_except_table();
	lsda.bytes.align(4);
	const size_t start = lsda.bytes.pos();
	info.has_lsda = true;
	info.lsda_offset = start;
	lsda.bytes.u8(0xff);
	if (types.empty())
		lsda.bytes.u8(0xff);
	else
	{
		lsda.bytes.u8(0x9b);
		const size_t offset_pos = lsda.bytes.pos();
		uleb(lsda.bytes, 1);
		lsda.bytes.u8(0x01);
		uleb(lsda.bytes, call_table.size());
		for (size_t i = 0; i < call_table.size(); ++i) lsda.bytes.u8(call_table[i]);
		for (size_t i = 0; i < action_table.size(); ++i) lsda.bytes.u8(action_table[i]);
		for (size_t n = 0; n < types.size(); ++n)
		{
			const string& type = types[types.size() - 1 - n];
			const size_t off = lsda.bytes.pos();
			lsda.bytes.u32(0);
			unit.obj.reloc(lsda, off, unit.obj.ensure_dw_ref(type),
			               R_X86_64_PC32, 0);
		}
		const size_t base_pos = lsda.bytes.pos();
		const uint64_t ttype_offset = base_pos - (offset_pos + 1);
		lsda.bytes.data[offset_pos] = static_cast<unsigned char>(ttype_offset);
		return;
	}
	lsda.bytes.u8(0x01);
	uleb(lsda.bytes, call_table.size());
	for (size_t i = 0; i < call_table.size(); ++i) lsda.bytes.u8(call_table[i]);
}
void Unit::emit_functions()
{
	for (size_t i = 0; i < program.functions.size(); ++i)
	{
		const Function& fn = program.functions[i];
		if (fn.declaration)
			continue;
		FunctionInfo info;
		FuncGen gen(*this, fn);
		gen.emit(info);
		infos.push_back(info);
	}
}
void cie_instructions(Blob& b)
{
	b.u8(0x0c); uleb(b, 7); uleb(b, 8);
	b.u8(0x90); uleb(b, 1);
}
size_t write_cie(ObjectFile& obj, bool personality)
{
	Section& eh = obj.eh_frame();
	eh.bytes.align(4);
	const size_t start = eh.bytes.pos();
	eh.bytes.u32(0);
	eh.bytes.u32(0);
	eh.bytes.u8(1);
	const char* aug = personality ? "zPLR" : "zR";
	for (const char* p = aug; *p; ++p) eh.bytes.u8(static_cast<uint8_t>(*p));
	eh.bytes.u8(0);
	uleb(eh.bytes, 1);
	sleb(eh.bytes, -8);
	uleb(eh.bytes, 16);
	if (personality)
	{
		uleb(eh.bytes, 7);
		eh.bytes.u8(0x9b);
		const size_t off = eh.bytes.pos();
		eh.bytes.u32(0);
		obj.reloc(eh, off, obj.ensure_dw_ref("__gxx_personality_v0"),
		          R_X86_64_PC32, 0);
		eh.bytes.u8(0x1b);
		eh.bytes.u8(0x1b);
	}
	else
	{
		uleb(eh.bytes, 1);
		eh.bytes.u8(0x1b);
	}
	cie_instructions(eh.bytes);
	eh.bytes.align(4);
	eh.bytes.patch32(start, static_cast<uint32_t>(eh.bytes.pos() - start - 4));
	return start;
}
void write_fde(ObjectFile& obj, const FunctionInfo& fn, size_t cie)
{
	Section& eh = obj.eh_frame();
	eh.bytes.align(4);
	const size_t start = eh.bytes.pos();
	eh.bytes.u32(0);
	eh.bytes.u32(static_cast<uint32_t>((start + 4) - cie));
	const size_t loc = eh.bytes.pos();
	eh.bytes.u32(0);
	obj.reloc(eh, loc, ".text", R_X86_64_PC32, fn.start);
	eh.bytes.u32(static_cast<uint32_t>(fn.size));
	if (fn.has_lsda)
	{
		uleb(eh.bytes, 4);
		const size_t off = eh.bytes.pos();
		eh.bytes.u32(0);
		obj.reloc(eh, off, ".gcc_except_table", R_X86_64_PC32,
		          fn.lsda_offset);
	}
	else
		uleb(eh.bytes, 0);
	eh.bytes.u8(0x41);
	eh.bytes.u8(0x0e); uleb(eh.bytes, 16);
	eh.bytes.u8(0x86); uleb(eh.bytes, 2);
	eh.bytes.u8(0x43);
	eh.bytes.u8(0x0d); uleb(eh.bytes, 6);
	eh.bytes.align(4);
	eh.bytes.patch32(start, static_cast<uint32_t>(eh.bytes.pos() - start - 4));
}
void Unit::emit_eh_frame()
{
	if (infos.empty())
		return;
	const size_t cie_plain = write_cie(obj, false);
	size_t cie_eh = 0;
	bool made_eh = false;
	for (size_t i = 0; i < infos.size(); ++i)
	{
		if (infos[i].has_lsda && !made_eh)
		{
			cie_eh = write_cie(obj, true);
			made_eh = true;
		}
		write_fde(obj, infos[i], infos[i].has_lsda ? cie_eh : cie_plain);
	}
}
}  // namespace
void write_host_object(lowir2cy86::Program& program, const string& outfile)
{
	if (program.function_by_name.empty())
	{
		bool has_entry = false;
		for (size_t i = 0; i < program.functions.size(); ++i)
			if (metadata(program.functions[i].metadata, "role") == "entry" ||
			    program.functions[i].name == "@main")
				has_entry = true;
		if (!has_entry)
			program.entry_function = "@__pa31_object_without_entry";
	}
	lowir2cy86::validate_and_layout_allow_f80(program);
	ObjectFile obj;
	Unit unit(program, obj);
	unit.prepare_symbols();
	unit.emit_globals();
	unit.emit_functions();
	unit.emit_eh_frame();
	obj.write(outfile);
}
}  // namespace pa31
