#include "pa31_host_object_internal.h"
#include <algorithm>
#include <cstdint>
#include <cstdlib>
#include <cstring>
#include <fstream>
#include <map>
#include <set>
#include <stdexcept>
using namespace std;
namespace pa31 {
namespace host {
size_t align_up(size_t value, size_t align)
{
	if (align <= 1)
		return value;
	const size_t rem = value % align;
	return rem == 0 ? value : value + align - rem;
}
uint64_t parse_int(const string& text)
{
	return static_cast<uint64_t>(strtoull(text.c_str(), NULL, 0));
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
bool ends_with(const string& text, const string& suffix)
{
	return text.size() >= suffix.size() &&
	       text.compare(text.size() - suffix.size(), suffix.size(), suffix) == 0;
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
string simple_cpp_type_code(const Type& type)
{
	if (type.kind == TypeKind::Void)
		return "v";
	if (type.kind == TypeKind::SignedInt)
	{
		if (type.bits == 8) return "a";
		if (type.bits == 16) return "s";
		if (type.bits == 32) return "i";
		if (type.bits == 64) return "l";
		if (type.bits == 128) return "n";
	}
	if (type.kind == TypeKind::UnsignedInt)
	{
		if (type.bits == 8) return "h";
		if (type.bits == 16) return "t";
		if (type.bits == 32) return "j";
		if (type.bits == 64) return "m";
		if (type.bits == 128) return "o";
	}
	if (type.kind == TypeKind::Float)
	{
		if (type.bits == 32) return "f";
		if (type.bits == 64) return "d";
		if (type.bits == 80) return "e";
	}
	if (type.kind == TypeKind::Ptr)
		return "Pv";
	return "";
}
string simple_cpp_function_symbol(const string& body,
                                  const vector<Parameter>& params)
{
	string signature;
	for (size_t i = 0; i < params.size(); ++i)
		signature += simple_cpp_type_code(params[i].type);
	if (signature.empty())
		signature = "v";
	return "_Z" + to_string(body.size()) + body + signature;
}
string tls_wrapper_symbol(const string& variable_symbol)
{
	if (variable_symbol.size() > 2 &&
	    variable_symbol[0] == '_' &&
	    variable_symbol[1] == 'Z')
		return "_ZTW" + variable_symbol.substr(2);
	return "_ZTW" + to_string(variable_symbol.size()) + variable_symbol;
}
string tls_wrapper_lowir_target(const string& function_name)
{
	const string suffix = "__tls_wrapper";
	const string body = lowir2cy86::lowir_symbol_body(function_name);
	if (!ends_with(body, suffix))
		return "";
	return "@" + body.substr(0, body.size() - suffix.size());
}
string host_function_symbol(const Function& fn)
{
	const string object = metadata(fn.metadata, "object");
	if (!object.empty())
		return object;
	const string tls_target = metadata(fn.metadata, "tls_for");
	if (!tls_target.empty())
		return tls_wrapper_symbol(lowir2cy86::lowir_symbol_body(tls_target));
	const string lowir_tls_target = tls_wrapper_lowir_target(fn.name);
	if (!lowir_tls_target.empty())
		return tls_wrapper_symbol(lowir2cy86::lowir_symbol_body(lowir_tls_target));
	const string body = lowir2cy86::lowir_symbol_body(fn.name);
	if (body == "main" || metadata(fn.metadata, "linkage") == "c")
		return body;
	if (body.find("__") == string::npos && is_identifier(body))
		return simple_cpp_function_symbol(body, fn.params);
	return body;
}
string target_symbol(const Program& program, const string& name);
string tls_wrapper_symbol_for_function(const Program& program, const Function& fn)
{
	string target = metadata(fn.metadata, "tls_for");
	if (target.empty())
		target = tls_wrapper_lowir_target(fn.name);
	if (target.empty())
		return "";
	map<string, size_t>::const_iterator git = program.global_by_name.find(target);
	if (git != program.global_by_name.end())
		return tls_wrapper_symbol(host_global_symbol(program.globals[git->second]));
	return tls_wrapper_symbol(lowir2cy86::lowir_symbol_body(target));
}
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
uint64_t parse_f64_bits(const string& text)
{
	if (text == "snan")
		return 0x7ff4000000000000ULL;
	union { double f; uint64_t u; } bits;
	bits.f = strtod(text.c_str(), NULL);
	return bits.u;
}
uint32_t parse_f32_bits(const string& text)
{
	if (text == "snan")
		return 0x7fa00000U;
	union { float f; uint32_t u; } bits;
	bits.f = strtof(text.c_str(), NULL);
	return bits.u;
}
vector<unsigned char> parse_f80_bytes(const string& text)
{
	vector<unsigned char> bytes(16, 0);
	bool negative = !text.empty() && text[0] == '-';
	string body = negative ? text.substr(1) : text;
	if (body == "inf")
	{
		bytes[7] = 0x80;
		bytes[8] = 0xff;
		bytes[9] = negative ? 0xff : 0x7f;
		return bytes;
	}
	if (body == "nan" || body == "snan")
	{
		bytes[7] = body == "snan" ? 0xa0 : 0xc0;
		bytes[8] = 0xff;
		bytes[9] = negative ? 0xff : 0x7f;
		return bytes;
	}
	long double value = strtold(text.c_str(), NULL);
	memcpy(&bytes[0], &value,
	       min(sizeof(value), static_cast<size_t>(10)));
	for (size_t i = 10; i < bytes.size(); ++i)
		bytes[i] = 0;
	return bytes;
}
string target_symbol(const Program& program, const string& name)
{
	map<string, size_t>::const_iterator git = program.global_by_name.find(name);
	if (git != program.global_by_name.end())
		return host_global_symbol(program.globals[git->second]);
	map<string, size_t>::const_iterator fit = program.function_by_name.find(name);
	if (fit != program.function_by_name.end())
	{
		const string wrapper =
			tls_wrapper_symbol_for_function(program, program.functions[fit->second]);
		return wrapper.empty()
			? host_function_symbol(program.functions[fit->second])
			: wrapper;
	}
	return lowir2cy86::lowir_symbol_body(name);
}
uint8_t symbol_bind(const lowir2cy86::Metadata& md);
bool skip_global_definition(const Global& g)
{
	const string obj = metadata(g.metadata, "object");
	return obj == "_ZTIi" || obj == "_ZTSi" ||
	       obj == "_ZTVN10__cxxabiv123__fundamental_type_infoE" ||
	       (!obj.empty() && obj[0] == '@') ||
	       lowir2cy86::lowir_symbol_body(g.name).find("__ehobj_") == 0;
}
bool constructor_object_symbol(const string& object)
{
	return object.find("C1") != string::npos ||
	       object.find("C2") != string::npos;
}
bool noop_constructor_instruction(const Function& fn, const Instruction& ins)
{
	if (ins.kind == InstrKind::Return)
		return true;
	if (ins.kind == InstrKind::Store &&
	    lowir2cy86::is_ptr_type(ins.type) &&
	    ins.a.text == fn.params[0].name &&
	    ins.b.kind == ValueKind::Slot)
		return true;
	if (ins.kind == InstrKind::EhTry ||
	    ins.kind == InstrKind::EhEnd ||
	    ins.kind == InstrKind::EhCatchAll ||
	    ins.kind == InstrKind::EhFilter ||
	    ins.kind == InstrKind::Exception ||
	    ins.kind == InstrKind::Jump)
		return true;
	if (ins.kind == InstrKind::Call &&
	    ins.a.kind == ValueKind::Function &&
	    (ins.a.text == "@cppgm_call_terminate" ||
	     ins.a.text == "cppgm_call_terminate"))
		return true;
	return false;
}
bool pruned_noop_constructor_function(const Function& fn)
{
	if (fn.declaration ||
	    symbol_bind(fn.metadata) != 2 ||
	    (metadata(fn.metadata, "object_root") == "yes" &&
	     metadata(fn.metadata, "generated_default_ctor") != "yes") ||
	    metadata(fn.metadata, "unwind") != "no" ||
	    !constructor_object_symbol(metadata(fn.metadata, "object")) ||
	    !lowir2cy86::is_void_type(fn.ret) ||
	    fn.params.size() != 1 ||
	    !lowir2cy86::is_ptr_type(fn.params[0].type))
		return false;
	for (size_t b = 0; b < fn.blocks.size(); ++b)
	{
		for (size_t i = 0; i < fn.blocks[b].instructions.size(); ++i)
		{
			const Instruction& ins = fn.blocks[b].instructions[i];
			if (noop_constructor_instruction(fn, ins))
				continue;
			return false;
		}
	}
	return true;
}
bool simple_inline_constructor_function(const Function& fn,
                                        vector<SimpleCtorStore>* stores)
{
	if (fn.declaration ||
	    symbol_bind(fn.metadata) != 2 ||
	    !constructor_object_symbol(metadata(fn.metadata, "object")) ||
	    !lowir2cy86::is_void_type(fn.ret) ||
	    fn.params.size() != 1 ||
	    !lowir2cy86::is_ptr_type(fn.params[0].type) ||
	    fn.blocks.size() != 1)
		return false;
	set<string> this_slots;
	set<string> this_temps;
	map<string, size_t> field_temps;
	vector<SimpleCtorStore> found_stores;
	const vector<Instruction>& instructions = fn.blocks[0].instructions;
	for (size_t i = 0; i < instructions.size(); ++i)
	{
		const Instruction& ins = instructions[i];
		if (ins.kind == InstrKind::Return)
			continue;
		if (ins.kind == InstrKind::Store &&
		    lowir2cy86::is_ptr_type(ins.type) &&
		    ins.a.text == fn.params[0].name &&
		    ins.b.kind == ValueKind::Slot)
		{
			this_slots.insert(ins.b.text);
			continue;
		}
		if (ins.kind == InstrKind::Load &&
		    lowir2cy86::is_ptr_type(ins.type) &&
		    ins.a.kind == ValueKind::Slot &&
		    this_slots.count(ins.a.text) != 0)
		{
			this_temps.insert(ins.dest);
			continue;
		}
		if (ins.kind == InstrKind::Index &&
		    (ins.op == "field" || ins.op == "base_subobject" ||
		     ins.op.empty()) &&
		    ins.a.kind == ValueKind::Temp &&
		    this_temps.count(ins.a.text) != 0 &&
		    ins.b.kind == ValueKind::Literal)
		{
			field_temps[ins.dest] =
				static_cast<size_t>(parse_int(ins.b.text));
			continue;
		}
		if (ins.kind == InstrKind::Store &&
		    ins.b.kind == ValueKind::Temp &&
		    field_temps.find(ins.b.text) != field_temps.end() &&
		    ins.a.kind == ValueKind::Literal &&
		    !lowir2cy86::is_obj_type(ins.type) &&
		    !wide_integer_type(ins.type))
		{
			SimpleCtorStore store;
			store.type = ins.type;
			store.offset = field_temps[ins.b.text];
			store.value = ins.a;
			found_stores.push_back(store);
			continue;
		}
		return false;
	}
	if (found_stores.empty())
		return false;
	if (stores != NULL)
		stores->swap(found_stores);
	return true;
}
bool o1_inline_constructor_function(const Unit& unit, const Function& fn)
{
	return unit.options.optimization_level >= 1 &&
	       simple_inline_constructor_function(fn, NULL);
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
	{
		const string wrapper =
			tls_wrapper_symbol_for_function(program, program.functions[i]);
		functions[program.functions[i].name] =
			wrapper.empty() ? host_function_symbol(program.functions[i]) : wrapper;
	}
}
bool Unit::prunes_function(const string& name) const
{
	map<string, size_t>::const_iterator it = program.function_by_name.find(name);
	if (it != program.function_by_name.end())
		return pruned_noop_constructor_function(program.functions[it->second]) ||
		       o1_inline_constructor_function(*this, program.functions[it->second]);
	for (size_t i = 0; i < program.functions.size(); ++i)
		if (program.functions[i].name == name)
			return pruned_noop_constructor_function(program.functions[i]) ||
			       o1_inline_constructor_function(*this,
			                                      program.functions[i]);
	return false;
}
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
	if (lowir2cy86::is_integer_type(type)) return min(64, max(8, type.bits));
	return 64;
}
bool wide_integer_type(const Type& type)
{
	return lowir2cy86::is_integer_type(type) &&
	       lowir2cy86::storage_size(type) > 8;
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
	if (wide_integer_type(type))
		zero_frame_tail(off, 8, lowir2cy86::storage_size(type));
}
void FuncGen::store_float_temp(const string& name, const Type& type, int xmm)
{
	map<string, size_t>::const_iterator p = fn.param_offsets.find(name);
	const size_t off = p != fn.param_offsets.end() ? p->second :
	                   fn.temp_offsets.find(name)->second;
	if (lowir2cy86::is_f80_type(type))
	{
		x.x87_fstpt(frame_mem(off));
		return;
	}
	if (type.bits == 32)
		x.sse_mr(0xf3, 0x11, frame_mem(off), xmm);
	else
		x.sse_mr(0xf2, 0x11, frame_mem(off), xmm);
}
void FuncGen::store_f80_literal_to_frame(const string& text, size_t off)
{
	vector<unsigned char> bytes = parse_f80_bytes(text);
	uint64_t lo = 0;
	for (size_t i = 0; i < 8; ++i)
		lo |= static_cast<uint64_t>(bytes[i]) << (i * 8);
	uint64_t hi = static_cast<uint64_t>(bytes[8]) |
	              (static_cast<uint64_t>(bytes[9]) << 8);
	x.mov_imm(64, RAX, lo);
	x.mov_mr(64, frame_mem(off), RAX);
	x.mov_imm(32, RAX, hi);
	x.mov_mr(32, frame_object_mem(off, 8), RAX);
	zero_frame_tail(off, 12, 16);
}
void FuncGen::store_f80_literal_to_address(const string& text, int reg)
{
	vector<unsigned char> bytes = parse_f80_bytes(text);
	uint64_t lo = 0;
	for (size_t i = 0; i < 8; ++i)
		lo |= static_cast<uint64_t>(bytes[i]) << (i * 8);
	uint64_t hi = static_cast<uint64_t>(bytes[8]) |
	              (static_cast<uint64_t>(bytes[9]) << 8);
	x.mov_imm(64, RAX, lo);
	x.mov_mr(64, Mem(reg, 0), RAX);
	x.mov_imm(32, RAX, hi);
	x.mov_mr(32, Mem(reg, 8), RAX);
	zero_memory_tail(reg, 12, 16);
}
void FuncGen::copy_f80_value_to_frame(const Value& src, size_t off)
{
	if (src.kind == ValueKind::Literal)
	{
		store_f80_literal_to_frame(src.text, off);
		return;
	}
	value_storage_address(src, R11);
	copy_memory_to_frame(R11, off, 16);
}
void FuncGen::copy_f80_value_to_address(const Value& src, int reg)
{
	if (src.kind == ValueKind::Literal)
	{
		store_f80_literal_to_address(src.text, reg);
		return;
	}
	value_storage_address(src, R10);
	copy_memory(R10, reg, 16);
}
	void FuncGen::tls_address(const string& name, int reg)
	{
		x.u8(0xe8);
		const size_t off = x.pos();
	x.u32(0);
	unit.obj.reloc(text, off, unit.tls_wrapper_for_global(name),
	               R_X86_64_PLT32, -4);
		if (reg != RAX)
			x.mov_rr(64, reg, RAX);
	}
	void FuncGen::imported_global_address(const string& name, int reg)
	{
		x.mov_rm(64, reg, Mem(RIP, 0));
		unit.obj.reloc(text, x.pos() - 4, target_symbol(unit.program, name),
		               R_X86_64_GOTPCREL, -4);
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
		if (unit.is_thread_local_global(v.text))
		{
			tls_address(v.text, RAX);
			x.mov_rm(width_for(target), reg, Mem(RAX, 0));
			if (width_for(target) == 8)
				x.movzx8(reg, reg);
			return;
			}
			if (unit.is_imported_global(v.text))
			{
				const int addr_reg = reg == R11 ? R10 : R11;
				imported_global_address(v.text, addr_reg);
				x.mov_rm(width_for(target), reg, Mem(addr_reg, 0));
				if (width_for(target) == 8)
					x.movzx8(reg, reg);
				return;
			}
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
void FuncGen::load_float_value(const Value& v, const Type& target, int xmm)
{
	if (lowir2cy86::is_f80_type(target))
		throw runtime_error("f80 value is loaded through x87");
	if (v.kind == ValueKind::Literal)
	{
		if (target.bits == 32)
		{
			x.mov_imm(32, RAX, parse_f32_bits(v.text));
			x.movd_xmm_from_reg(32, xmm, RAX);
		}
		else
		{
			x.mov_imm(64, RAX, parse_f64_bits(v.text));
			x.movd_xmm_from_reg(64, xmm, RAX);
		}
		return;
	}
	Mem mem(RBP, 0);
	bool have_mem = false;
	if (v.kind == ValueKind::Global)
	{
			if (unit.is_thread_local_global(v.text))
			{
				tls_address(v.text, RAX);
				mem = Mem(RAX, 0);
			}
			else if (unit.is_imported_global(v.text))
			{
				imported_global_address(v.text, R11);
				mem = Mem(R11, 0);
			}
			else
				mem = Mem(RIP, 0);
		have_mem = true;
	}
	else if (v.kind == ValueKind::Slot || v.kind == ValueKind::Temp)
	{
		mem = frame_mem(object_offset(fn, v));
		have_mem = true;
	}
	if (!have_mem)
		throw runtime_error("unsupported float value load");
	if (target.bits == 32)
		x.sse_rm(0xf3, 0x10, xmm, mem);
	else
		x.sse_rm(0xf2, 0x10, xmm, mem);
		if (v.kind == ValueKind::Global &&
		    !unit.is_thread_local_global(v.text) &&
		    !unit.is_imported_global(v.text))
			unit.obj.reloc(text, x.pos() - 4, target_symbol(unit.program, v.text),
			               R_X86_64_PC32, -4);
}
void FuncGen::load_f80_value_to_x87(const Value& v)
{
	if (v.kind == ValueKind::Literal)
	{
		x.sub_rsp(16);
		store_f80_literal_to_address(v.text, RSP);
		x.x87_fldt(Mem(RSP, 0));
		x.add_rsp(16);
		return;
	}
	value_storage_address(v, R11);
	x.x87_fldt(Mem(R11, 0));
}
void FuncGen::store_value(const Value& dst, const Type& type, int reg)
{
	if (dst.kind == ValueKind::Slot)
		x.mov_mr(width_for(type), frame_mem(fn.slot_offsets.find(dst.text)->second), reg);
	else if (dst.kind == ValueKind::Global)
	{
			if (unit.is_thread_local_global(dst.text))
			{
				const int value_reg = reg == RAX ? R10 : reg;
			if (reg == RAX)
				x.mov_rr(64, R10, RAX);
			tls_address(dst.text, R11);
			x.mov_mr(width_for(type), Mem(R11, 0), value_reg);
				return;
			}
			if (unit.is_imported_global(dst.text))
			{
				const int addr_reg = reg == R11 ? R10 : R11;
				imported_global_address(dst.text, addr_reg);
				x.mov_mr(width_for(type), Mem(addr_reg, 0), reg);
				return;
			}
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
void FuncGen::store_float_value(const Value& dst, const Type& type, int xmm)
{
	Mem mem(RBP, 0);
	bool have_mem = false;
	if (dst.kind == ValueKind::Slot)
	{
		mem = frame_mem(fn.slot_offsets.find(dst.text)->second);
		have_mem = true;
	}
	else if (dst.kind == ValueKind::Global)
	{
			if (unit.is_thread_local_global(dst.text))
			{
				tls_address(dst.text, RAX);
				mem = Mem(RAX, 0);
			}
			else if (unit.is_imported_global(dst.text))
			{
				imported_global_address(dst.text, R11);
				mem = Mem(R11, 0);
			}
			else
				mem = Mem(RIP, 0);
		have_mem = true;
	}
	else if (dst.kind == ValueKind::Temp)
	{
		load_value(dst, lowir2cy86::parse_type_text("ptr"), R11);
		mem = Mem(R11, 0);
		have_mem = true;
	}
	if (!have_mem)
		throw runtime_error("unsupported float store destination");
	if (type.bits == 32)
		x.sse_mr(0xf3, 0x11, mem, xmm);
	else
		x.sse_mr(0xf2, 0x11, mem, xmm);
		if (dst.kind == ValueKind::Global &&
		    !unit.is_thread_local_global(dst.text) &&
		    !unit.is_imported_global(dst.text))
			unit.obj.reloc(text, x.pos() - 4, target_symbol(unit.program, dst.text),
			               R_X86_64_PC32, -4);
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
			if (unit.is_thread_local_global(v.text))
			{
				tls_address(v.text, reg);
				return;
			}
			if (unit.is_imported_global(v.text))
			{
				imported_global_address(v.text, reg);
				return;
			}
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
void FuncGen::value_storage_address(const Value& v, int reg)
{
	if (v.kind == ValueKind::Slot || v.kind == ValueKind::Temp)
	{
		x.lea(reg, frame_mem(object_offset(fn, v)));
		return;
	}
	if (v.kind == ValueKind::Global)
	{
			if (unit.is_thread_local_global(v.text))
			{
				tls_address(v.text, reg);
				return;
			}
			if (unit.is_imported_global(v.text))
			{
				imported_global_address(v.text, reg);
				return;
			}
			x.lea(reg, Mem(RIP, 0));
		unit.obj.reloc(text, x.pos() - 4, target_symbol(unit.program, v.text),
		               R_X86_64_PC32, -4);
		return;
	}
	throw runtime_error("unsupported value storage source");
}
void FuncGen::copy_memory(int src_reg, int dst_reg, size_t bytes)
{
	for (size_t pos = 0; pos < bytes;)
	{
		const size_t left = bytes - pos;
		const int w = left >= 8 ? 64 : (left >= 4 ? 32 : (left >= 2 ? 16 : 8));
		x.mov_rm(w, RAX, Mem(src_reg, static_cast<int32_t>(pos)));
		x.mov_mr(w, Mem(dst_reg, static_cast<int32_t>(pos)), RAX);
		pos += static_cast<size_t>(w / 8);
	}
}
void FuncGen::copy_memory_to_frame(int src_reg, size_t dst_off, size_t bytes)
{
	for (size_t pos = 0; pos < bytes;)
	{
		const size_t left = bytes - pos;
		const int w = left >= 8 ? 64 : (left >= 4 ? 32 : (left >= 2 ? 16 : 8));
		x.mov_rm(w, RAX, Mem(src_reg, static_cast<int32_t>(pos)));
		x.mov_mr(w, frame_object_mem(dst_off, pos), RAX);
		pos += static_cast<size_t>(w / 8);
	}
}
void FuncGen::zero_memory_tail(int dst_reg, size_t first, size_t bytes)
{
	if (first >= bytes)
		return;
	x.mov_imm(32, RAX, 0);
	for (size_t pos = first; pos < bytes;)
	{
		const size_t left = bytes - pos;
		const int w = left >= 8 ? 64 : (left >= 4 ? 32 : (left >= 2 ? 16 : 8));
		x.mov_mr(w, Mem(dst_reg, static_cast<int32_t>(pos)), RAX);
		pos += static_cast<size_t>(w / 8);
	}
}
void FuncGen::zero_frame_tail(size_t dst_off, size_t first, size_t bytes)
{
	if (first >= bytes)
		return;
	x.mov_imm(32, RAX, 0);
	for (size_t pos = first; pos < bytes;)
	{
		const size_t left = bytes - pos;
		const int w = left >= 8 ? 64 : (left >= 4 ? 32 : (left >= 2 ? 16 : 8));
		x.mov_mr(w, frame_object_mem(dst_off, pos), RAX);
		pos += static_cast<size_t>(w / 8);
	}
}
void FuncGen::copy_bytes(const Value& src, const Value& dst, const Span& span)
{
	storage_address(src, R10);
	storage_address(dst, R11);
	copy_memory(R10, R11, span.bytes);
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
		const Type type = value_type(ins.a);
		const int width = width_for(type);
		load_value(ins.a, type, RAX);
		x.mov_imm(width, R10, 0);
		x.cmp(width, RAX, R10);
		emit_rel_jump(x, jumps, 0x85, ins.target);
		emit_rel_jump(x, jumps, 0, ins.target_false);
	}
void FuncGen::emit_switch(const Instruction& ins)
{
	const Type type = value_type(ins.a);
	const int width = width_for(type);
	load_value(ins.a, type, RAX);
	for (size_t i = 0; i < ins.switch_cases.size(); ++i)
	{
		const SwitchCase& item = ins.switch_cases[i];
		load_value(item.value, type, R10);
		x.cmp(width, RAX, R10);
		emit_rel_jump(x, jumps, 0x84, item.target);
	}
	emit_rel_jump(x, jumps, 0, ins.target);
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
	else if (lowir2cy86::is_float_type(ins.type))
	{
		if (lowir2cy86::is_f80_type(ins.type))
			load_f80_value_to_x87(ins.a);
		else
			load_float_value(ins.a, ins.type, 0);
	}
	else
		load_value(ins.a, ins.type, RAX);
	}
	x.u8(0xc9);
	x.u8(0xc3);
}
	uint8_t cmp_cc(const string& op)
	{
		if (op == "eq") return 0x94;
		if (op == "ne") return 0x95;
		if (op == "lt") return 0x9c;
		if (op == "gt") return 0x9f;
		if (op == "le") return 0x9e;
		if (op == "ge") return 0x9d;
		if (op == "ult") return 0x92;
		if (op == "ugt") return 0x97;
		if (op == "ule") return 0x96;
		if (op == "uge") return 0x93;
		throw runtime_error("unsupported cmp");
	}
bool FuncGen::emit_const_instruction(const Instruction& ins)
{
	if (lowir2cy86::is_f80_type(ins.type))
		store_f80_literal_to_frame(ins.a.text,
		                           fn.temp_offsets.find(ins.dest)->second);
	else if (lowir2cy86::is_float_type(ins.type))
	{
		load_float_value(ins.a, ins.type, 0);
		store_float_temp(ins.dest, ins.type, 0);
	}
	else
	{
		x.mov_imm(width_for(ins.type), RAX, parse_int(ins.a.text));
		store_temp(ins.dest, ins.type, RAX);
	}
	return true;
}
bool FuncGen::emit_copy_instruction(const Instruction& ins)
{
	if (lowir2cy86::is_f80_type(ins.type))
		copy_f80_value_to_frame(ins.a,
		                        fn.temp_offsets.find(ins.dest)->second);
	else if (lowir2cy86::is_float_type(ins.type))
	{
		load_float_value(ins.a, ins.type, 0);
		store_float_temp(ins.dest, ins.type, 0);
	}
	else if (wide_integer_type(ins.type) && ins.a.kind != ValueKind::Literal)
	{
		value_storage_address(ins.a, R11);
		copy_memory_to_frame(R11,
		                     fn.temp_offsets.find(ins.dest)->second,
		                     lowir2cy86::storage_size(ins.type));
	}
	else
	{
		load_value(ins.a, ins.type, RAX);
		store_temp(ins.dest, ins.type, RAX);
	}
	return true;
}
bool FuncGen::emit_load_instruction(const Instruction& ins)
{
	storage_address(ins.a, R11);
	if (lowir2cy86::is_f80_type(ins.type))
		copy_memory_to_frame(R11,
		                     fn.temp_offsets.find(ins.dest)->second,
		                     lowir2cy86::storage_size(ins.type));
	else if (lowir2cy86::is_float_type(ins.type))
	{
		if (ins.type.bits == 32) x.sse_rm(0xf3, 0x10, 0, Mem(R11, 0));
		else x.sse_rm(0xf2, 0x10, 0, Mem(R11, 0));
		store_float_temp(ins.dest, ins.type, 0);
	}
	else if (wide_integer_type(ins.type))
		copy_memory_to_frame(R11,
		                     fn.temp_offsets.find(ins.dest)->second,
		                     lowir2cy86::storage_size(ins.type));
	else
	{
		x.mov_rm(width_for(ins.type), RAX, Mem(R11, 0));
		store_temp(ins.dest, ins.type, RAX);
	}
	return true;
}
bool FuncGen::emit_store_instruction(const Instruction& ins)
{
	if (lowir2cy86::is_f80_type(ins.type))
	{
		storage_address(ins.b, R11);
		copy_f80_value_to_address(ins.a, R11);
	}
	else if (lowir2cy86::is_float_type(ins.type))
	{
		load_float_value(ins.a, ins.type, 0);
		store_float_value(ins.b, ins.type, 0);
	}
	else if (wide_integer_type(ins.type))
	{
		storage_address(ins.b, R11);
		if (ins.a.kind == ValueKind::Literal)
		{
			x.mov_imm(64, RAX, parse_int(ins.a.text));
			x.mov_mr(64, Mem(R11, 0), RAX);
			zero_memory_tail(R11, 8, lowir2cy86::storage_size(ins.type));
		}
		else
		{
			value_storage_address(ins.a, R10);
			copy_memory(R10, R11, lowir2cy86::storage_size(ins.type));
		}
	}
	else
	{
		load_value(ins.a, ins.type, RAX);
		store_value(ins.b, ins.type, RAX);
	}
	return true;
}
bool FuncGen::emit_index_instruction(const Instruction& ins)
{
	load_value(ins.a, lowir2cy86::parse_type_text("ptr"), RAX);
	load_value(ins.b, lowir2cy86::parse_type_text("i64"), R10);
	if (ins.op == "array_element" && ins.type.size > 1)
		x.imul_imm(R10, static_cast<int32_t>(ins.type.size));
	x.binary(0x01, 64, RAX, R10);
	store_temp(ins.dest, lowir2cy86::parse_type_text("ptr"), RAX);
	return true;
}
bool FuncGen::emit_unary_value_instruction(const Instruction& ins)
{
	if (ins.op == "neg" && lowir2cy86::is_f80_type(ins.type))
	{
		const size_t off = fn.temp_offsets.find(ins.dest)->second;
		copy_f80_value_to_frame(ins.a, off);
		x.mov_rm(8, RAX, frame_object_mem(off, 9));
		x.mov_imm(8, R10, 0x80);
		x.binary(0x31, 8, RAX, R10);
		x.mov_mr(8, frame_object_mem(off, 9), RAX);
		return true;
	}
	if (ins.op == "neg" && lowir2cy86::is_float_type(ins.type))
	{
		const int width = ins.type.bits == 32 ? 32 : 64;
		if (ins.a.kind == ValueKind::Literal)
		{
			uint64_t bits = width == 32
				? parse_f32_bits(ins.a.text)
				: parse_f64_bits(ins.a.text);
			bits ^= width == 32
				? uint64_t(0x80000000U)
				: uint64_t(0x8000000000000000ULL);
			x.mov_imm(width, RAX, bits);
			x.movd_xmm_from_reg(width, 0, RAX);
			store_float_temp(ins.dest, ins.type, 0);
		}
		else
		{
			load_float_value(ins.a, ins.type, 0);
			store_float_temp(ins.dest, ins.type, 0);
			size_t off = fn.temp_offsets.find(ins.dest)->second;
			x.mov_rm(width, RAX, frame_mem(off));
			x.mov_imm(width, R10, width == 32
			          ? uint64_t(0x80000000U)
			          : uint64_t(0x8000000000000000ULL));
			x.binary(0x31, width, RAX, R10);
			x.mov_mr(width, frame_mem(off), RAX);
		}
		return true;
	}
	if ((ins.op == "neg" || ins.op == "bitnot") &&
	    (lowir2cy86::is_integer_type(ins.type) ||
	     lowir2cy86::is_ptr_type(ins.type)))
	{
		const int width = width_for(ins.type);
		const int subop = ins.op == "neg" ? 3 : 2;
		load_value(ins.a, ins.type, RAX);
		x.rex(width == 64, subop, 0, RAX, width == 8 && RAX >= 4);
		x.u8(width == 8 ? 0xf6 : 0xf7);
		x.modrm(3, subop, RAX);
		store_temp(ins.dest, ins.type, RAX);
		return true;
	}
	load_value(ins.a, ins.type, RAX);
	store_temp(ins.dest, ins.type, RAX);
	return true;
}
bool FuncGen::emit_value_instruction(const Instruction& ins)
{
	if (ins.kind == InstrKind::VaStart) { emit_va_start(ins); return true; }
	if (ins.kind == InstrKind::VaEnd) return true;
	if (ins.kind == InstrKind::VaArg) { emit_va_arg(ins); return true; }
	if (ins.kind == InstrKind::StackAlloc) { emit_stack_alloc(ins); return true; }
	if (ins.kind == InstrKind::Const) return emit_const_instruction(ins);
	if (ins.kind == InstrKind::Copy) return emit_copy_instruction(ins);
	if (ins.kind == InstrKind::Addr)
	{
		storage_address(ins.a, RAX);
		store_temp(ins.dest, lowir2cy86::parse_type_text("ptr"), RAX);
		return true;
	}
	if (ins.kind == InstrKind::Load) return emit_load_instruction(ins);
	if (ins.kind == InstrKind::Store) return emit_store_instruction(ins);
	if (ins.kind == InstrKind::Index) return emit_index_instruction(ins);
	if (ins.kind == InstrKind::Unary) return emit_unary_value_instruction(ins);
	return false;
}
void FuncGen::emit_stack_alloc(const Instruction& ins)
{
	if (!lowir2cy86::is_ptr_type(ins.type))
		throw runtime_error("invalid stackalloc destination");
	load_value(ins.a, ins.src_type, RAX);
	x.mov_imm(64, RCX, 15);
	x.binary(0x01, 64, RAX, RCX);
	x.mov_imm(64, RCX, ~static_cast<uint64_t>(15));
	x.binary(0x21, 64, RAX, RCX);
	x.binary(0x29, 64, RSP, RAX);
	x.mov_rr(64, RAX, RSP);
	store_temp(ins.dest, ins.type, RAX);
}
bool FuncGen::emit_protected_instruction(const Instruction& ins)
{
	if (ins.kind == InstrKind::Call)
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
		return true;
	}
	if (ins.kind == InstrKind::CopyObj)
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
		return true;
	}
	if (ins.kind != InstrKind::ZeroInit)
		return false;
	storage_address(ins.a, R11);
	zero_bytes(x, Mem(R11, 0), ins.span.bytes);
	return true;
}
bool FuncGen::emit_eh_instruction(const Instruction& ins, const string& block)
{
	if (ins.kind == InstrKind::EhTry || ins.kind == InstrKind::EhCleanup)
	{
		if (!ins.target.empty())
		{
			EhRange r; r.start = x.pos(); r.target = ins.target;
			active_ranges.push_back(r); landing_blocks.insert(ins.target);
			if (ins.kind == InstrKind::EhCleanup)
				cleanup_blocks.insert(ins.target);
		}
		else if (ins.kind == InstrKind::EhCleanup)
			cleanup_action_blocks.insert(block);
		return true;
	}
	if (ins.kind == InstrKind::EhCatch)
	{
		CatchInfo c; c.type_symbol = target_symbol(unit.program, ins.a.text);
		c.selector = ins.order_a; catches[block].push_back(c);
		return true;
	}
	if (ins.kind == InstrKind::EhCatchAll)
	{
		CatchInfo c; c.selector = ins.order_a; c.catch_all = true;
		catches[block].push_back(c);
		return true;
	}
	if (ins.kind == InstrKind::EhFilter)
	{
		CatchInfo c;
		c.selector = ins.order_a;
		c.exception_spec = true;
		for (size_t i = 0; i < ins.args.size(); ++i)
			c.exception_spec_types.push_back(
				target_symbol(unit.program, ins.args[i].text));
		catches[block].push_back(c);
		return true;
	}
	if (ins.kind == InstrKind::EhEnd)
	{
		if (!active_ranges.empty())
			active_ranges.pop_back();
		return true;
	}
	if (ins.kind == InstrKind::Exception)
	{
		x.mov_rm(64, RAX, frame_mem(exc_off));
		store_temp(ins.dest, ins.type, RAX);
		return true;
	}
	if (ins.kind == InstrKind::ExceptionSelector)
	{
		x.mov_rm(64, RAX, frame_mem(sel_off));
		store_temp(ins.dest, ins.type, RAX);
		return true;
	}
	if (ins.kind != InstrKind::Resume)
		return false;
	x.mov_rm(64, RDI, frame_mem(exc_off));
	EhRange resume_range;
	resume_range.start = x.pos();
	resume_range.target = "";
	x.u8(0xe8); size_t off = x.pos(); x.u32(0);
	unit.obj.reloc(text, off, "_Unwind_Resume", R_X86_64_PLT32, -4);
	resume_range.end = x.pos();
	ranges.push_back(resume_range);
	x.u8(0x0f); x.u8(0x0b);
	return true;
}
bool FuncGen::emit_control_instruction(const Instruction& ins)
{
	if (ins.kind == InstrKind::Jump)
		emit_rel_jump(x, jumps, 0, ins.target);
	else if (ins.kind == InstrKind::Branch)
		emit_branch(ins);
	else if (ins.kind == InstrKind::Switch)
		emit_switch(ins);
	else if (ins.kind == InstrKind::Return)
		emit_return(ins);
	else
		return false;
	return true;
}
void FuncGen::emit_instruction(const Instruction& ins, const string& block)
{
	if (emit_value_instruction(ins) ||
	    emit_arithmetic_instruction(ins) ||
	    emit_protected_instruction(ins) ||
	    emit_eh_instruction(ins, block) ||
	    emit_control_instruction(ins))
		return;
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
void emit_param_store(X86& x, const Function& fn, size_t index,
                      size_t& reg, size_t& fp, size_t& stack)
{
	static const int regs[] = {RDI, RSI, RDX, RCX, R8, R9};
	const Parameter& p = fn.params[index];
	const size_t off = fn.param_offsets.find(p.name)->second;
	if (lowir2cy86::is_f80_type(p.type))
	{
		for (size_t pos = 0; pos < lowir2cy86::storage_size(p.type);)
		{
			const size_t left = lowir2cy86::storage_size(p.type) - pos;
			const int width = left >= 8 ? 64 : (left >= 4 ? 32 : 8);
			x.mov_rm(width, RAX,
			         Mem(RBP, static_cast<int32_t>(stack + pos)));
			x.mov_mr(width, frame_object_mem(off, pos), RAX);
			pos += static_cast<size_t>(width / 8);
		}
		stack += lowir2cy86::stack_storage_size(p.type);
	}
	else if (lowir2cy86::is_float_type(p.type) && p.type.bits <= 64)
	{
		if (fp < 8)
		{
			if (p.type.bits == 32)
				x.sse_mr(0xf3, 0x11, Mem(RBP, -static_cast<int32_t>(off)),
				         static_cast<int>(fp++));
			else
				x.sse_mr(0xf2, 0x11, Mem(RBP, -static_cast<int32_t>(off)),
				         static_cast<int>(fp++));
		}
		else
		{
			const int width = p.type.bits == 32 ? 32 : 64;
			x.mov_rm(width, RAX, Mem(RBP, static_cast<int32_t>(stack)));
			x.mov_mr(width, Mem(RBP, -static_cast<int32_t>(off)), RAX);
			stack += 8;
		}
	}
	else if (lowir2cy86::is_obj_type(p.type) && lowir2cy86::is_direct_object_abi(p.type))
	{
		const size_t slots = lowir2cy86::direct_object_abi_slots(p.type);
		const bool in_registers = reg + slots <= 6;
		for (size_t c = 0; c < slots; ++c)
		{
			const int width =
				lowir2cy86::direct_object_abi_chunk_width_bits(p.type, c);
			if (in_registers)
				x.mov_mr(width, frame_object_mem(off, c * 8), regs[reg + c]);
			else
			{
				x.mov_rm(width, RAX,
				         Mem(RBP, static_cast<int32_t>(stack + c * 8)));
				x.mov_mr(width, frame_object_mem(off, c * 8), RAX);
			}
		}
		if (in_registers)
			reg += slots;
		else
			stack += slots * 8;
	}
	else
	{
		if (reg < 6)
			x.mov_mr(width_for(p.type), Mem(RBP, -static_cast<int32_t>(off)), regs[reg++]);
		else
		{
			x.mov_rm(width_for(p.type), RAX, Mem(RBP, static_cast<int32_t>(stack)));
			x.mov_mr(width_for(p.type), Mem(RBP, -static_cast<int32_t>(off)), RAX);
			stack += 8;
		}
	}
}
void FuncGen::emit(FunctionInfo& info)
{
	for (size_t b = 0; b < fn.blocks.size(); ++b)
		for (size_t i = 0; i < fn.blocks[b].instructions.size(); ++i)
			if (fn.blocks[b].instructions[i].kind == InstrKind::EhTry ||
			    fn.blocks[b].instructions[i].kind == InstrKind::EhCleanup ||
			    fn.blocks[b].instructions[i].kind == InstrKind::EhFilter ||
			    fn.blocks[b].instructions[i].kind == InstrKind::Exception ||
			    fn.blocks[b].instructions[i].kind == InstrKind::Resume)
				has_eh = true;
			else if (fn.blocks[b].instructions[i].kind == InstrKind::VaStart)
				has_va_start = true;
	frame_size = fn.stack_size;
	if (has_eh)
	{
		frame_size = align_up(frame_size, 8); exc_off = frame_size += 8;
		sel_off = frame_size += 8;
	}
	if (has_va_start)
	{
		frame_size = align_up(frame_size, 16);
		va_reg_save_off = frame_size + 176;
		frame_size += 176;
	}
	frame_size = align_up(frame_size, 16);
	text.bytes.align(16);
	const size_t base = x.pos();
	info.start = base;
	info.symbol = host_function_symbol(fn);
	info.section = text.name;
	x.u8(0x55);
	x.rex(true); x.u8(0x89); x.modrm(3, RSP, RBP);
	x.sub_rsp(frame_size);
	save_variadic_registers();
	size_t reg = 0;
	size_t fp = 0;
	size_t stack = 16;
	for (size_t i = 0; i < fn.params.size(); ++i)
		emit_param_store(x, fn, i, reg, fp, stack);
	for (size_t b = 0; b < fn.blocks.size(); ++b)
	{
		block_offsets[fn.blocks[b].name] = x.pos() - base;
		if (landing_blocks.count(fn.blocks[b].name))
			save_landing_registers();
		for (size_t i = 0; i < fn.blocks[b].instructions.size(); ++i)
			emit_instruction(fn.blocks[b].instructions[i], fn.blocks[b].name);
	}
	info.size = x.pos() - base;
	unit.obj.symbol(info.symbol, symbol_bind(fn.metadata), 2, text.name, base, info.size);
	patch_jumps(base);
	finish_lsda(info, base);
}
	void Unit::emit_functions()
	{
		for (size_t i = 0; i < program.functions.size(); ++i)
		{
		const Function& fn = program.functions[i];
		if (fn.declaration)
			continue;
		if (prunes_function(fn.name))
			continue;
		FunctionInfo info;
		FuncGen gen(*this, fn);
		gen.emit(info);
			infos.push_back(info);
		}
	}
	void Unit::emit_lifecycle_arrays()
	{
		for (size_t i = 0; i < program.functions.size(); ++i)
		{
			const Function& fn = program.functions[i];
			const string role = metadata(fn.metadata, "role");
			if (fn.declaration || (role != "init" && role != "fini"))
				continue;
			Section& sec = role == "init" ? obj.init_array() : obj.fini_array();
			sec.bytes.align(8);
			const size_t off = sec.bytes.pos();
			sec.bytes.u64(0);
			obj.reloc(sec, off, target_symbol(program, fn.name), R_X86_64_64, 0);
		}
	}
	const Symbol* find_emitted_symbol(const ObjectFile& obj, const string& name)
	{
		for (size_t i = 0; i < obj.symbols.size(); ++i)
			if (obj.symbols[i].name == name)
				return &obj.symbols[i];
		return NULL;
	}
	void Unit::emit_aliases()
	{
		for (size_t i = 0; i < program.aliases.size(); ++i)
		{
			const string target = target_symbol(program, program.aliases[i].target);
			const Symbol* sym = find_emitted_symbol(obj, target);
			if ((sym == NULL || !sym->defined) &&
			    prunes_function(program.aliases[i].target))
				continue;
			if (sym == NULL || !sym->defined)
				throw runtime_error("object alias target not defined");
			obj.symbol(program.aliases[i].object,
			           sym->bind,
			           sym->type,
			           sym->section,
			           sym->value,
			           sym->size);
		}
	}
}  // namespace host
using namespace host;
void write_host_object(lowir2cy86::Program& program,
                       const string& outfile,
                       const Options& options)
{
	lowir2cy86::validate_and_layout_fragment_allow_f80(program);
	ObjectFile obj;
	Unit unit(program, obj, options);
	unit.prepare_symbols();
	unit.emit_globals();
	unit.emit_tls_wrappers();
	unit.emit_functions();
	unit.emit_lifecycle_arrays();
	unit.emit_aliases();
	unit.emit_eh_frame();
	obj.write(outfile);
}
}  // namespace pa31
