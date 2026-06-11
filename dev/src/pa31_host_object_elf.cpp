#include "pa31_host_object_internal.h"

using namespace std;

namespace pa31 {
namespace host {

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
	for (size_t i = 0; i < base.size(); ++i)
	{
		if (base[i].type != SHT_GROUP)
			continue;
		map<string, uint32_t>::const_iterator sig =
			sym_index.find(base[i].group_signature);
		if (sig == sym_index.end())
			throw runtime_error("missing COMDAT signature symbol");
		base[i].bytes.data.clear();
		base[i].bytes.u32(GRP_COMDAT);
		for (size_t m = 0; m < base[i].group_members.size(); ++m)
		{
			map<string, uint16_t>::const_iterator member =
				sec_index.find(base[i].group_members[m]);
			if (member == sec_index.end())
				throw runtime_error("missing COMDAT member section");
			base[i].bytes.u32(member->second);
		}
		base[i].link = 0;
		base[i].info = sig->second;
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
	for (size_t i = 0; i < base.size(); ++i)
		if (base[i].type == SHT_GROUP)
			base[i].link = symtab_index;
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

}  // namespace host
}  // namespace pa31
