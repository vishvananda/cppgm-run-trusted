#include "pa31_host_object_internal.h"

using namespace std;

namespace pa31 {
namespace host {

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
		const bool tls = metadata(g.metadata, "storage") == "thread_local";
		const string sym = globals[g.name];
		const bool weak = symbol_bind(g.metadata) == 2;
		Section& sec = tls ? obj.tdata()
		                    : weak ? obj.comdat_data(sym, readonly)
		                    : (readonly ? obj.rodata() : obj.data());
		const size_t align = g.has_type ? g.type.align : 1;
		sec.bytes.align(align);
		const size_t off = sec.bytes.pos();
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
			for (size_t n = 8; n < lowir2cy86::storage_size(g.type); ++n)
				sec.bytes.u8(0);
		}
		else
			for (size_t n = 0; n < g.data.size(); ++n)
				emit_global_item(*this, sec, g.data[n]);
		obj.symbol(sym, symbol_bind(g.metadata),
		           metadata(g.metadata, "storage") == "thread_local" ? 6 : 1,
		           sec.name, off,
		           sec.bytes.pos() - off);
	}
}
bool Unit::is_thread_local_global(const string& name) const
{
	map<string, size_t>::const_iterator git = program.global_by_name.find(name);
	return git != program.global_by_name.end() &&
	       metadata(program.globals[git->second].metadata, "storage") ==
		       "thread_local";
}
string Unit::tls_wrapper_for_global(const string& name) const
{
	map<string, string>::const_iterator it = globals.find(name);
	if (it != globals.end())
		return tls_wrapper_symbol(it->second);
	return tls_wrapper_symbol(lowir2cy86::lowir_symbol_body(name));
}
void Unit::emit_tls_wrapper_for_global(const Global& g)
{
	const string variable = globals[g.name];
	const string wrapper = tls_wrapper_symbol(variable);
	if (!emitted_tls_wrappers.insert(wrapper).second)
		return;
	if (g.declaration)
		obj.symbol(variable, symbol_bind(g.metadata), 6, "", 0, 0);
	Section& sec = obj.comdat_text(wrapper);
	sec.bytes.align(16);
	X86 x(sec);
	const size_t base = x.pos();
	x.u8(0x55);
	x.rex(true); x.u8(0x89); x.modrm(3, RSP, RBP);
	x.u8(0x64);
	x.rex(true); x.u8(0x8b); x.modrm(0, RAX, 4); x.sib(0, 4, 5); x.u32(0);
	x.rex(true, RAX, 0, RAX); x.u8(0x8d); x.modrm(2, RAX, RAX);
	const size_t off = x.pos();
	x.u32(0);
	obj.reloc(sec, off, variable, R_X86_64_TPOFF32, 0);
	x.u8(0xc9);
	x.u8(0xc3);
	obj.symbol(wrapper, symbol_bind(g.metadata) == 0 ? 0 : 2,
	           2, sec.name, base, x.pos() - base);
}
void Unit::emit_tls_wrappers()
{
	for (size_t i = 0; i < program.globals.size(); ++i)
		if (metadata(program.globals[i].metadata, "storage") == "thread_local")
			emit_tls_wrapper_for_global(program.globals[i]);
}
Section& Unit::function_text_section(const Function& fn)
{
	const string sym = functions[fn.name];
	return symbol_bind(fn.metadata) == 2 ? obj.comdat_text(sym) : obj.text();
}

}  // namespace host
}  // namespace pa31
