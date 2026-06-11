#include "cy86_elf_object.h"
#include <fstream>
#include <limits>
#include <stdexcept>
using namespace std;
namespace cy86 {
namespace {
const uint32_t SHT_PROGBITS = 1;
const uint32_t SHT_SYMTAB = 2;
const uint32_t SHT_STRTAB = 3;
const uint32_t SHT_RELA = 4;
const uint32_t SHT_NOBITS = 8;
const uint64_t SHF_WRITE = 0x1;
const uint64_t SHF_ALLOC = 0x2;
const uint64_t SHF_EXECINSTR = 0x4;
struct SectionHeader {
	uint32_t name;
	uint32_t type;
	uint64_t flags;
	uint64_t offset;
	uint64_t size;
	uint32_t link;
	uint32_t info;
	uint64_t addralign;
	uint64_t entsize;
};
struct SymbolEntry {
	uint32_t name;
	unsigned char info;
	uint16_t shndx;
	uint64_t value;
	uint64_t size;
};
vector<unsigned char> read_file_bytes(const string& path) {
	ifstream in(path.c_str(), ios::binary);
	if (!in)
		throw runtime_error("cannot open object file");
	in.seekg(0, ios::end);
	streamoff size = in.tellg();
	if (size < 0)
		throw runtime_error("cannot size object file");
	in.seekg(0, ios::beg);
	vector<unsigned char> bytes(static_cast<size_t>(size));
	if (!bytes.empty())
		in.read(reinterpret_cast<char*>(&bytes[0]),
		        static_cast<streamsize>(bytes.size()));
	if (!in && !bytes.empty())
		throw runtime_error("cannot read object file");
	return bytes; }
void require_range(const vector<unsigned char>& bytes, uint64_t off, uint64_t size) {
	if (off > bytes.size() || size > bytes.size() - off)
		throw runtime_error("truncated ELF object"); }
uint16_t u16(const vector<unsigned char>& bytes, uint64_t off) {
	require_range(bytes, off, 2);
	return static_cast<uint16_t>(bytes[off]) |
	       (static_cast<uint16_t>(bytes[off + 1]) << 8); }
uint32_t u32(const vector<unsigned char>& bytes, uint64_t off) {
	require_range(bytes, off, 4);
	uint32_t out = 0;
	for (int i = 0; i < 4; ++i)
		out |= static_cast<uint32_t>(bytes[off + i]) << (i * 8);
	return out; }
uint64_t u64(const vector<unsigned char>& bytes, uint64_t off) {
	require_range(bytes, off, 8);
	uint64_t out = 0;
	for (int i = 0; i < 8; ++i)
		out |= static_cast<uint64_t>(bytes[off + i]) << (i * 8);
	return out; }
int64_t s64(const vector<unsigned char>& bytes, uint64_t off) {
	return static_cast<int64_t>(u64(bytes, off)); }
string string_at(const vector<unsigned char>& strings, uint32_t offset) {
	if (offset >= strings.size())
		throw runtime_error("ELF string offset out of range");
	string out;
	for (size_t i = offset; i < strings.size() && strings[i] != 0; ++i)
		out.push_back(static_cast<char>(strings[i]));
	return out; }
vector<unsigned char> section_bytes(const vector<unsigned char>& bytes,
                                    const SectionHeader& sh) {
	if (sh.type == SHT_NOBITS)
		return vector<unsigned char>();
	require_range(bytes, sh.offset, sh.size);
	return vector<unsigned char>(bytes.begin() + static_cast<size_t>(sh.offset),
	                             bytes.begin() + static_cast<size_t>(sh.offset + sh.size)); }
bool include_alloc_section(const string& name, const SectionHeader& sh) {
	if ((sh.flags & SHF_ALLOC) == 0)
		return false;
	if (name == ".eh_frame" || name.find(".eh_frame.") == 0)
		return false;
	return sh.type == SHT_PROGBITS || sh.type == SHT_NOBITS; }
}  // namespace
ExternalObject load_elf64_relocatable(const string& path) {
	vector<unsigned char> bytes = read_file_bytes(path);
	if (bytes.size() < 64 ||
	    bytes[0] != 0x7f || bytes[1] != 'E' ||
	    bytes[2] != 'L' || bytes[3] != 'F' ||
	    bytes[4] != 2 || bytes[5] != 1)
		throw runtime_error("unsupported ELF object");
	if (u16(bytes, 16) != 1 || u16(bytes, 18) != 0x3e)
		throw runtime_error("unsupported ELF object");
	if (u32(bytes, 20) != 1)
		throw runtime_error("unsupported ELF object");
	const uint64_t shoff = u64(bytes, 40);
	const uint16_t shentsize = u16(bytes, 58);
	const uint16_t shnum = u16(bytes, 60);
	const uint16_t shstrndx = u16(bytes, 62);
	if (shentsize < 64 || shstrndx >= shnum)
		throw runtime_error("unsupported ELF section table");
	require_range(bytes, shoff, static_cast<uint64_t>(shentsize) * shnum);
	vector<SectionHeader> shdrs(shnum);
	for (size_t i = 0; i < shnum; ++i) {
		const uint64_t off = shoff + i * shentsize;
		shdrs[i].name = u32(bytes, off + 0);
		shdrs[i].type = u32(bytes, off + 4);
		shdrs[i].flags = u64(bytes, off + 8);
		shdrs[i].offset = u64(bytes, off + 24);
		shdrs[i].size = u64(bytes, off + 32);
		shdrs[i].link = u32(bytes, off + 40);
		shdrs[i].info = u32(bytes, off + 44);
		shdrs[i].addralign = u64(bytes, off + 48);
		shdrs[i].entsize = u64(bytes, off + 56); }
	vector<unsigned char> shstr = section_bytes(bytes, shdrs[shstrndx]);
	vector<string> names(shnum);
	for (size_t i = 0; i < shnum; ++i)
		names[i] = string_at(shstr, shdrs[i].name);
	ExternalObject out;
	vector<size_t> section_map(shnum, static_cast<size_t>(-1));
	for (size_t i = 0; i < shnum; ++i) {
		if (!include_alloc_section(names[i], shdrs[i]))
			continue;
		ExternalSection section;
		section.name = names[i];
		section.data = section_bytes(bytes, shdrs[i]);
		section.size = shdrs[i].size;
		section.align = shdrs[i].addralign == 0 ? 1 : shdrs[i].addralign;
		section.alloc = true;
		section.executable = (shdrs[i].flags & SHF_EXECINSTR) != 0;
		section.writable = (shdrs[i].flags & SHF_WRITE) != 0;
		section.nobits = shdrs[i].type == SHT_NOBITS;
		section.address = 0;
		section_map[i] = out.sections.size();
		out.sections.push_back(section); }
	for (size_t s = 0; s < shnum; ++s) {
		if (shdrs[s].type != SHT_SYMTAB)
			continue;
		if (shdrs[s].entsize == 0 || shdrs[s].link >= shnum)
			throw runtime_error("invalid ELF symbol table");
		vector<unsigned char> strings = section_bytes(bytes, shdrs[shdrs[s].link]);
		const size_t count = static_cast<size_t>(shdrs[s].size / shdrs[s].entsize);
		vector<size_t> symbol_map(count, static_cast<size_t>(-1));
		for (size_t i = 0; i < count; ++i) {
			const uint64_t off = shdrs[s].offset + i * shdrs[s].entsize;
			SymbolEntry sym;
			sym.name = u32(bytes, off + 0);
			sym.info = bytes[off + 4];
			sym.shndx = u16(bytes, off + 6);
			sym.value = u64(bytes, off + 8);
			sym.size = u64(bytes, off + 16);
			ExternalSymbol out_sym;
			out_sym.name = string_at(strings, sym.name);
			out_sym.value = sym.value;
			out_sym.defined = sym.shndx != 0 && sym.shndx < shnum &&
			                  section_map[sym.shndx] != static_cast<size_t>(-1);
			out_sym.section = out_sym.defined ? section_map[sym.shndx]
			                                  : static_cast<size_t>(-1);
			out_sym.global = (sym.info >> 4) != 0;
			out_sym.function = (sym.info & 0xf) == 2;
			symbol_map[i] = out.symbols.size();
			out.symbols.push_back(out_sym); }
		for (size_t rsec = 0; rsec < shnum; ++rsec) {
			if (shdrs[rsec].type != SHT_RELA || shdrs[rsec].link != s)
				continue;
			if (shdrs[rsec].info >= shnum ||
			    section_map[shdrs[rsec].info] == static_cast<size_t>(-1))
				continue;
			if (shdrs[rsec].entsize == 0)
				throw runtime_error("invalid ELF relocation table");
			const size_t rel_count =
				static_cast<size_t>(shdrs[rsec].size / shdrs[rsec].entsize);
			for (size_t i = 0; i < rel_count; ++i) {
				const uint64_t off = shdrs[rsec].offset + i * shdrs[rsec].entsize;
				const uint64_t info = u64(bytes, off + 8);
				const size_t sym_index = static_cast<size_t>(info >> 32);
				if (sym_index >= symbol_map.size())
					throw runtime_error("ELF relocation symbol out of range");
				ExternalRelocation rel;
				rel.section = section_map[shdrs[rsec].info];
				rel.offset = u64(bytes, off + 0);
				rel.type = static_cast<uint32_t>(info & 0xffffffffu);
				rel.symbol = symbol_map[sym_index];
				rel.addend = s64(bytes, off + 16);
				out.relocations.push_back(rel); } }
		break; }
	return out; }
}  // namespace cy86
