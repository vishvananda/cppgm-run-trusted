#include "lowir2native.h"

#include "cy86_model.h"
#include "lowir2cy86.h"

#include <algorithm>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <cstdint>
#include <fstream>
#include <map>
#include <set>
#include <sstream>
#include <stdexcept>
#include <string>
#include <vector>

using namespace std;

namespace lowir2native {
namespace {

string effective_target(const Options& options)
{
	return options.target.empty() ? "linux" : options.target;
}

string temp_cy86_path(const string& outfile)
{
	return outfile + ".lowir2native.cy86.tmp";
}

void write_text_file(const string& path, const string& text)
{
	ofstream out(path.c_str(), ios::binary);
	if (!out)
		throw runtime_error("cannot open output file");
	out << text;
	out.close();
	if (!out)
		throw runtime_error("cannot write output file");
}

bool token_looks_floating(const string& token)
{
	for (size_t i = 0; i < token.size(); ++i)
	{
		const char c = token[i];
		if (c == '.' || c == 'e' || c == 'E' || c == 'p' || c == 'P')
			return true;
	}
	return false;
}

string strip_float_suffix(string token)
{
	if (!token.empty())
	{
		const char c = token[token.size() - 1];
		if (c == 'f' || c == 'F' || c == 'l' || c == 'L')
			token.erase(token.size() - 1);
	}
	return token;
}

template <class T>
uint64_t float_bits(T value)
{
	uint64_t bits = 0;
	memcpy(&bits, &value, sizeof(value));
	return bits;
}

string signed_bits_literal(uint64_t bits, int width)
{
	if (width == 32)
		return to_string(static_cast<int32_t>(static_cast<uint32_t>(bits)));
	return to_string(static_cast<int64_t>(bits));
}

bool convert_float_token(const string& token, int width, string& out)
{
	if (!token_looks_floating(token))
		return false;
	const string source = strip_float_suffix(token);
	char* end = nullptr;
	if (width == 32)
	{
		const float value = strtof(source.c_str(), &end);
		if (end == source.c_str() || *end != '\0')
			return false;
		out = signed_bits_literal(float_bits(value), 32);
		return true;
	}
	if (width == 64)
	{
		const double value = strtod(source.c_str(), &end);
		if (end == source.c_str() || *end != '\0')
			return false;
		out = signed_bits_literal(float_bits(value), 64);
		return true;
	}
	return false;
}

void sanitize_cy86_line(const vector<string>& parts, string& line);

string sanitize_cy86_floating_literals(const string& text)
{
	istringstream in(text);
	ostringstream out;
	string line;
	while (getline(in, line))
	{
		string body = line;
		const size_t semi = body.find(';');
		if (semi != string::npos)
			body = body.substr(0, semi);
		istringstream words(body);
		vector<string> parts;
		string word;
		while (words >> word)
			parts.push_back(word);
		if (parts.size() >= 2)
			sanitize_cy86_line(parts, line);
		out << line << "\n";
	}
	return out.str();
}

void sanitize_cy86_line(const vector<string>& parts, string& line)
{
	int width = 0;
	if (parts[0] == "move32" || parts[0] == "data32")
		width = 32;
	else if (parts[0] == "move64" || parts[0] == "data64")
		width = 64;
	if (width == 0)
		return;
	string converted;
	if (!convert_float_token(parts.back(), width, converted))
		return;
	const size_t pos = line.rfind(parts.back());
	if (pos != string::npos)
		line.replace(pos, parts.back().size(), converted);
}

void write_native_file(const lowir2cy86::Program& program,
                       const Options& options)
{
	const string tmp = temp_cy86_path(options.outfile);
	write_text_file(tmp,
	                sanitize_cy86_floating_literals(lowir2cy86::emit_cy86(program)));
	cy86::Options cy_options;
	cy_options.target = effective_target(options);
	try
	{
		cy86::compile_to_file(vector<string>(1, tmp), cy_options, options.outfile);
	}
	catch (...)
	{
		remove(tmp.c_str());
		throw;
	}
	remove(tmp.c_str());
}

string storage_suffix(const lowir2cy86::Type& type)
{
	return type.text.empty() ? "void" : type.text;
}

string reg_for_index(size_t index)
{
	static const char* const regs[] = {
		"r8", "r9", "rbx", "r12", "r13", "r14", "r15", "r10", "r11"
	};
	return regs[index % (sizeof(regs) / sizeof(regs[0]))];
}

string abi_gpr(size_t index)
{
	static const char* const regs[] = {"rdi", "rsi", "rdx", "rcx", "r8", "r9"};
	if (index < sizeof(regs) / sizeof(regs[0]))
		return regs[index];
	return "[rbp+" + to_string(16 + (index - 6) * 8) + "]";
}

bool metadata_is(const lowir2cy86::Metadata& md,
                 const string& key,
                 const string& value)
{
	for (size_t i = 0; i < md.size(); ++i)
	{
		if (md[i].key == key && md[i].value == value)
			return true;
	}
	return false;
}

string value_text(const lowir2cy86::Value& value)
{
	return value.text;
}

string mem_for_offset(size_t offset)
{
	return "[rbp-" + to_string(offset) + "]";
}

class MirDumper
{
public:
	MirDumper(const lowir2cy86::Program& program, const string& target)
		: program_(program), target_(target)
	{
	}

	string dump()
	{
		out_ << "machine_ir x86_64 " << target_ << "\n\n";
		dump_startup();
		dump_globals();
		dump_functions();
		return out_.str();
	}

private:
	const lowir2cy86::Program& program_;
	string target_;
	ostringstream out_;
	vector<string> temp_names_;
	vector<string> temp_regs_;
	vector<string> xmm_names_;
	vector<string> xmm_regs_;
	map<string, int> use_counts_;
	map<string, const lowir2cy86::Instruction*> definitions_;
	set<string> direct_branch_cmp_;

	void dump_startup()
	{
		if (program_.entry_function.empty())
			return;
		out_ << "startup\n";
		if (!program_.init_function.empty())
			out_ << "    call " << program_.init_function << "\n";
		out_ << "    call " << program_.entry_function << "\n";
		if (!program_.fini_function.empty())
		{
			out_ << "    mov r12, rax\n";
			out_ << "    call " << program_.fini_function << "\n";
			out_ << "    mov rdi, r12\n";
		}
		else
			out_ << "    mov rdi, rax\n";
		out_ << "    exit\n\n";
	}

	void dump_globals()
	{
		for (size_t i = 0; i < program_.globals.size(); ++i)
		{
			const lowir2cy86::Global& g = program_.globals[i];
			if (g.declaration)
				continue;
			out_ << "global " << g.name;
			if (metadata_is(g.metadata, "storage", "readonly"))
				out_ << " readonly";
			if (metadata_is(g.metadata, "storage", "thread_local"))
				out_ << " thread_local";
			out_ << "\n";
			if (g.has_type)
			{
				out_ << "  storage scalar " << g.type.text << "\n";
				if (g.init.kind == "zero")
					out_ << "  init " << g.type.text << " 0\n";
				else if (g.init.kind == "addr")
					out_ << "  init ptr addr " << g.init.target
					     << addend_text(g.init.has_addend, g.init.addend) << "\n";
				else
					out_ << "  init " << g.type.text << " " << g.init.literal << "\n";
			}
			else
			{
				out_ << "  storage data\n";
				for (size_t j = 0; j < g.data.size(); ++j)
					dump_global_item(g.data[j]);
			}
			out_ << "\n";
		}
	}

	string addend_text(bool has, int addend) const
	{
		if (!has)
			return "";
		return addend >= 0 ? " + " + to_string(addend)
		                   : " - " + to_string(-addend);
	}

	void dump_global_item(const lowir2cy86::GlobalDataItem& item)
	{
		if (item.kind == "zero")
			out_ << "  item zero " << item.zero_bytes << "\n";
		else if (item.kind == "addr")
			out_ << "  item ptr addr " << item.target
			     << addend_text(item.has_addend, item.addend) << "\n";
		else
			out_ << "  item " << item.type.text << " " << item.literal << "\n";
	}

	void dump_functions()
	{
		for (size_t i = 0; i < program_.functions.size(); ++i)
		{
			const lowir2cy86::Function& fn = program_.functions[i];
			if (fn.declaration)
				continue;
			dump_function(fn);
			if (i + 1 != program_.functions.size())
				out_ << "\n";
		}
	}

	void dump_function(const lowir2cy86::Function& fn)
	{
		temp_names_.clear();
		temp_regs_.clear();
		xmm_names_.clear();
		xmm_regs_.clear();
		analyze_function(fn);
		out_ << "function " << fn.name << "\n";
		dump_abi(fn);
		dump_frame(fn);
		out_ << "\n";
		for (size_t i = 0; i < fn.blocks.size(); ++i)
		{
			out_ << "  block " << fn.blocks[i].name << "\n";
			for (size_t j = 0; j < fn.blocks[i].instructions.size(); ++j)
				dump_instruction(fn, fn.blocks[i].instructions[j]);
			if (i + 1 != fn.blocks.size())
				out_ << "\n";
		}
	}

	void analyze_function(const lowir2cy86::Function& fn)
	{
		use_counts_.clear();
		definitions_.clear();
		direct_branch_cmp_.clear();
		for (size_t i = 0; i < fn.blocks.size(); ++i)
		{
			for (size_t j = 0; j < fn.blocks[i].instructions.size(); ++j)
			{
				const lowir2cy86::Instruction& ins = fn.blocks[i].instructions[j];
				if (ins.has_dest)
					definitions_[ins.dest] = &ins;
				count_uses(ins);
			}
		}
		for (size_t i = 0; i < fn.blocks.size(); ++i)
		{
			for (size_t j = 0; j < fn.blocks[i].instructions.size(); ++j)
			{
				const lowir2cy86::Instruction& ins = fn.blocks[i].instructions[j];
				if (ins.kind != lowir2cy86::InstrKind::Branch ||
				    ins.a.kind != lowir2cy86::ValueKind::Temp)
					continue;
				map<string, const lowir2cy86::Instruction*>::const_iterator it =
				    definitions_.find(ins.a.text);
				if (it != definitions_.end() &&
				    it->second->kind == lowir2cy86::InstrKind::Cmp &&
				    use_counts_[ins.a.text] == 1)
					direct_branch_cmp_.insert(ins.a.text);
			}
		}
	}

	void count_uses(const lowir2cy86::Instruction& ins)
	{
		count_use(ins.a);
		count_use(ins.b);
		count_use(ins.c);
		for (size_t i = 0; i < ins.args.size(); ++i)
			count_use(ins.args[i]);
		for (size_t i = 0; i < ins.switch_cases.size(); ++i)
			count_use(ins.switch_cases[i].value);
	}

	void count_use(const lowir2cy86::Value& value)
	{
		if (value.kind == lowir2cy86::ValueKind::Temp)
			++use_counts_[value.text];
	}

	void dump_abi(const lowir2cy86::Function& fn)
	{
		out_ << "  abi\n";
		for (size_t i = 0; i < fn.params.size(); ++i)
			out_ << "    param " << fn.params[i].name << " -> " << abi_gpr(i)
			     << " : " << fn.params[i].type.text << "\n";
		out_ << "    return " << storage_suffix(fn.ret) << " -> "
		     << (lowir2cy86::is_void_type(fn.ret) ? "void" : "rax") << "\n";
	}

	void dump_frame(const lowir2cy86::Function& fn)
	{
		const bool preserve_rbx = estimates_preserve_rbx(fn);
		const bool float_frame = function_uses_float(fn);
		out_ << "  frame\n";
		out_ << "    stack_size "
		     << max(mir_stack_size(fn),
		            max(preserve_rbx ? static_cast<size_t>(16) : static_cast<size_t>(0),
		                float_frame ? static_cast<size_t>(48) : static_cast<size_t>(0)))
		     << "\n";
		out_ << "    scratch_bytes "
		     << (float_frame || fn.needs_convert_scratch ? 48 : 0) << "\n";
		if (preserve_rbx)
			out_ << "    preserve rbx\n";
		for (size_t i = 0; i < fn.slots.size(); ++i)
			out_ << "    slot " << fn.slots[i].name << " -> "
			     << mem_for_offset(fn.slots[i].offset) << " : "
			     << fn.slots[i].type.text << "\n";
	}

	bool function_uses_float(const lowir2cy86::Function& fn) const
	{
		for (size_t i = 0; i < fn.blocks.size(); ++i)
		{
			for (size_t j = 0; j < fn.blocks[i].instructions.size(); ++j)
			{
				const lowir2cy86::Instruction& ins = fn.blocks[i].instructions[j];
				if (lowir2cy86::is_float_type(ins.type) ||
				    lowir2cy86::is_float_type(ins.src_type))
					return true;
			}
		}
		return false;
	}

	bool estimates_preserve_rbx(const lowir2cy86::Function& fn) const
	{
		for (size_t i = 0; i < fn.blocks.size(); ++i)
		{
			for (size_t j = 0; j < fn.blocks[i].instructions.size(); ++j)
			{
				const lowir2cy86::Instruction& ins = fn.blocks[i].instructions[j];
				if (ins.kind == lowir2cy86::InstrKind::Binary &&
				    ins.a.kind == lowir2cy86::ValueKind::Temp)
				{
					if (ins.b.kind == lowir2cy86::ValueKind::Temp &&
					    ins.a.text == ins.b.text)
						continue;
					map<string, int>::const_iterator it = use_counts_.find(ins.a.text);
					if (it != use_counts_.end() && it->second > 1)
						return true;
				}
			}
		}
		return false;
	}

	size_t mir_stack_size(const lowir2cy86::Function& fn) const
	{
		size_t bytes = 0;
		for (size_t i = 0; i < fn.slots.size(); ++i)
		{
			const size_t end = fn.slots[i].offset;
			if (end > bytes)
				bytes = end;
		}
		return align_to(bytes, 16);
	}

	size_t align_to(size_t value, size_t alignment) const
	{
		if (alignment == 0)
			return value;
		const size_t rem = value % alignment;
		return rem == 0 ? value : value + alignment - rem;
	}

	string temp_reg(const string& name)
	{
		for (size_t i = 0; i < temp_names_.size(); ++i)
		{
			if (temp_names_[i] == name)
				return temp_regs_[i];
		}
		temp_names_.push_back(name);
		temp_regs_.push_back(reg_for_index(temp_regs_.size()));
		return temp_regs_.back();
	}

	string xmm_reg(const string& name)
	{
		for (size_t i = 0; i < xmm_names_.size(); ++i)
		{
			if (xmm_names_[i] == name)
				return xmm_regs_[i];
		}
		static const char* const regs[] = {"xmm0", "xmm1", "xmm2", "xmm3"};
		xmm_names_.push_back(name);
		xmm_regs_.push_back(regs[xmm_regs_.size() %
		                         (sizeof(regs) / sizeof(regs[0]))]);
		return xmm_regs_.back();
	}

	void remember_xmm_reg(const string& name, const string& reg)
	{
		for (size_t i = 0; i < xmm_names_.size(); ++i)
		{
			if (xmm_names_[i] == name)
			{
				xmm_regs_[i] = reg;
				return;
			}
		}
		xmm_names_.push_back(name);
		xmm_regs_.push_back(reg);
	}

	lowir2cy86::Type lookup_type(const lowir2cy86::Function& fn,
	                             const lowir2cy86::Value& value) const
	{
		if (value.kind == lowir2cy86::ValueKind::Temp)
		{
			map<string, lowir2cy86::Type>::const_iterator pit =
			    fn.param_types.find(value.text);
			if (pit != fn.param_types.end())
				return pit->second;
			map<string, lowir2cy86::Type>::const_iterator it =
			    fn.temp_types.find(value.text);
			if (it != fn.temp_types.end())
				return it->second;
		}
		if (value.kind == lowir2cy86::ValueKind::Slot)
		{
			map<string, lowir2cy86::Type>::const_iterator it =
			    fn.slot_types.find(value.text);
			if (it != fn.slot_types.end())
				return it->second;
		}
		return lowir2cy86::Type();
	}

	string float_value(const lowir2cy86::Function& fn,
	                   const lowir2cy86::Value& value)
	{
		if (value.kind == lowir2cy86::ValueKind::Temp)
			return xmm_reg(value.text);
		return value_reg(fn, value);
	}

	string value_reg(const lowir2cy86::Function& fn, const lowir2cy86::Value& value)
	{
		if (value.kind == lowir2cy86::ValueKind::Temp)
		{
			for (size_t i = 0; i < fn.params.size(); ++i)
			{
				if (fn.params[i].name == value.text)
					return abi_gpr(i);
			}
			return temp_reg(value.text);
		}
		if (value.kind == lowir2cy86::ValueKind::Literal)
			return value.text;
		if (value.kind == lowir2cy86::ValueKind::Global ||
		    value.kind == lowir2cy86::ValueKind::Function)
			return value.text;
		if (value.kind == lowir2cy86::ValueKind::Slot)
		{
			map<string, size_t>::const_iterator it = fn.slot_offsets.find(value.text);
			if (it != fn.slot_offsets.end())
				return mem_for_offset(it->second);
		}
		return value_text(value);
	}

	void dump_instruction(const lowir2cy86::Function& fn,
	                      const lowir2cy86::Instruction& ins)
	{
		switch (ins.kind)
		{
		case lowir2cy86::InstrKind::Const:
			dump_const(ins);
			break;
		case lowir2cy86::InstrKind::Copy:
			dump_copy(fn, ins);
			break;
		case lowir2cy86::InstrKind::Addr:
			dump_addr(fn, ins);
			break;
		case lowir2cy86::InstrKind::Load:
		case lowir2cy86::InstrKind::AtomicLoad:
			dump_load(fn, ins);
			break;
		case lowir2cy86::InstrKind::Store:
		case lowir2cy86::InstrKind::AtomicStore:
			out_ << "    store." << ins.type.text << " " << store_dest(fn, ins.b)
			     << ", " << value_reg(fn, ins.a) << "\n";
			break;
		case lowir2cy86::InstrKind::Index:
			dump_index(fn, ins);
			break;
		case lowir2cy86::InstrKind::CopyObj:
			out_ << "    copy_bytes " << ins.span.bytes << "x" << ins.span.align
			     << ", " << value_reg(fn, ins.b) << ", "
			     << value_reg(fn, ins.a) << "\n";
			break;
		case lowir2cy86::InstrKind::ZeroInit:
			out_ << "    zero_bytes " << ins.span.bytes << "x" << ins.span.align
			     << ", " << value_reg(fn, ins.a) << "\n";
			break;
		case lowir2cy86::InstrKind::Unary:
		case lowir2cy86::InstrKind::Binary:
		case lowir2cy86::InstrKind::Cmp:
		case lowir2cy86::InstrKind::Convert:
			if (ins.kind != lowir2cy86::InstrKind::Cmp ||
			    direct_branch_cmp_.find(ins.dest) == direct_branch_cmp_.end())
				dump_scalar(fn, ins);
			break;
		case lowir2cy86::InstrKind::Call:
			dump_call(fn, ins);
			break;
		case lowir2cy86::InstrKind::AtomicExchange:
		case lowir2cy86::InstrKind::AtomicCompareExchange:
		case lowir2cy86::InstrKind::AtomicAddFetch:
			dump_atomic(fn, ins);
			break;
		case lowir2cy86::InstrKind::AtomicThreadFence:
		case lowir2cy86::InstrKind::AtomicSignalFence:
			out_ << "    mfence\n";
			break;
		case lowir2cy86::InstrKind::Jump:
			out_ << "    jmp " << ins.target << "\n";
			break;
		case lowir2cy86::InstrKind::Branch:
			dump_branch(fn, ins);
			break;
		case lowir2cy86::InstrKind::Switch:
			dump_switch(fn, ins);
			break;
		case lowir2cy86::InstrKind::Return:
			dump_return(fn, ins);
			break;
		default:
			out_ << "    ; unsupported\n";
			break;
		}
	}

	void dump_const(const lowir2cy86::Instruction& ins)
	{
		if (lowir2cy86::is_float_type(ins.type) && !lowir2cy86::is_f80_type(ins.type))
		{
			out_ << "    fmov." << ins.type.text << " " << xmm_reg(ins.dest)
			     << ", " << ins.a.text << "\n";
			return;
		}
		out_ << "    mov " << temp_reg(ins.dest) << ", " << ins.a.text << "\n";
	}

	void dump_addr(const lowir2cy86::Function& fn,
	               const lowir2cy86::Instruction& ins)
	{
		const string op =
		    ins.a.kind == lowir2cy86::ValueKind::Global ? "mov" : "lea";
		out_ << "    " << op << " " << temp_reg(ins.dest) << ", "
		     << value_reg(fn, ins.a) << "\n";
	}

	void dump_copy(const lowir2cy86::Function& fn,
	               const lowir2cy86::Instruction& ins)
	{
		if (lowir2cy86::is_float_type(ins.type) && !lowir2cy86::is_f80_type(ins.type))
		{
			out_ << "    fmov." << ins.type.text << " " << xmm_reg(ins.dest)
			     << ", " << float_value(fn, ins.a) << "\n";
			return;
		}
		out_ << "    mov " << temp_reg(ins.dest) << ", "
		     << value_reg(fn, ins.a) << "\n";
	}

	void dump_index(const lowir2cy86::Function& fn,
	                const lowir2cy86::Instruction& ins)
	{
		const size_t scale = lowir2cy86::storage_size(ins.type);
		const string dst = temp_reg(ins.dest);
		out_ << "    mov " << dst << ", " << value_reg(fn, ins.a) << "\n";
		if (ins.b.kind == lowir2cy86::ValueKind::Literal)
		{
			const long offset = stol(ins.b.text) * static_cast<long>(scale);
			out_ << "    lea " << dst << ", [" << dst << "+"
			     << offset << "]\n";
		}
		else
			out_ << "    lea " << dst << ", [" << dst << "+"
			     << value_reg(fn, ins.b)
			     << (scale == 1 ? "" : "*" + to_string(scale)) << "]\n";
	}

	string load_source(const lowir2cy86::Function& fn,
	                   const lowir2cy86::Value& value)
	{
		if (value.kind == lowir2cy86::ValueKind::Temp)
			return "[" + value_reg(fn, value) + "]";
		return value_reg(fn, value);
	}

	void dump_load(const lowir2cy86::Function& fn,
	               const lowir2cy86::Instruction& ins)
	{
		const string dst = load_dest_reg(ins);
		out_ << "    load." << ins.type.text << " " << dst << ", "
		     << load_source(fn, ins.a) << "\n";
		remember_temp_reg(ins.dest, dst);
	}

	string load_dest_reg(const lowir2cy86::Instruction& ins)
	{
		if (ins.a.kind == lowir2cy86::ValueKind::Temp)
			return "r8";
		return temp_reg(ins.dest);
	}

	string store_dest(const lowir2cy86::Function& fn,
	                  const lowir2cy86::Value& value)
	{
		if (value.kind == lowir2cy86::ValueKind::Temp)
			return "[" + value_reg(fn, value) + "]";
		return value_reg(fn, value);
	}

	void dump_scalar(const lowir2cy86::Function& fn,
	                 const lowir2cy86::Instruction& ins)
	{
		if (ins.kind == lowir2cy86::InstrKind::Unary)
			dump_unary(fn, ins);
		else if (ins.kind == lowir2cy86::InstrKind::Binary)
			dump_binary(fn, ins);
		else if (ins.kind == lowir2cy86::InstrKind::Cmp)
			dump_cmp_value(fn, ins);
		else
			out_ << "    " << ins.op << "." << ins.src_type.text << "."
			     << ins.type.text << " " << temp_reg(ins.dest) << ", "
			     << value_reg(fn, ins.a) << "\n";
	}

	void dump_unary(const lowir2cy86::Function& fn,
	                const lowir2cy86::Instruction& ins)
	{
		const string dst = temp_reg(ins.dest);
		out_ << "    mov " << dst << ", " << value_reg(fn, ins.a) << "\n";
		if (ins.op == "neg")
			out_ << "    neg " << dst << "\n";
		else if (ins.op == "bitnot")
			out_ << "    not " << dst << "\n";
		else if (ins.op == "bswap")
			out_ << "    bswap " << dst << "\n";
		else if (ins.op == "not")
		{
			out_ << "    cmp." << ins.type.text << " " << dst << ", 0\n";
			out_ << "    sete " << dst << "\n";
			out_ << "    movzx " << dst << ", " << dst << "\n";
		}
	}

	void dump_binary(const lowir2cy86::Function& fn,
	                 const lowir2cy86::Instruction& ins)
	{
		if (lowir2cy86::is_float_type(ins.type) && !lowir2cy86::is_f80_type(ins.type))
		{
			dump_float_binary(fn, ins);
			return;
		}
		const string dst = binary_dest_reg(ins);
		const string left = value_reg(fn, ins.a);
		if (dst != left)
			out_ << "    mov " << dst << ", " << left << "\n";
		if (ins.op == "udiv" || ins.op == "umod")
			dump_divmod(fn, ins, dst, false);
		else if (ins.op == "div" || ins.op == "mod")
			dump_divmod(fn, ins, dst, true);
		else if (ins.op == "ushr")
			out_ << "    shr " << dst << ", " << shift_rhs(fn, ins.b) << "\n";
		else if (ins.op == "shr")
			out_ << "    sar " << dst << ", " << shift_rhs(fn, ins.b) << "\n";
		else if (ins.op == "shl")
			out_ << "    shl " << dst << ", " << shift_rhs(fn, ins.b) << "\n";
		else
		{
			string rhs = value_reg(fn, ins.b);
			if (ins.a.kind == lowir2cy86::ValueKind::Temp &&
			    ins.b.kind == lowir2cy86::ValueKind::Temp &&
			    ins.a.text == ins.b.text && dst != left)
				rhs = dst;
			out_ << "    " << binary_opcode(ins.op) << " " << dst << ", "
			     << rhs << "\n";
		}
		remember_temp_reg(ins.dest, dst);
	}

	void dump_float_binary(const lowir2cy86::Function& fn,
	                       const lowir2cy86::Instruction& ins)
	{
		const string dst = float_binary_dest(ins);
		out_ << "    f" << float_binary_opcode(ins.op) << "." << ins.type.text << " "
		     << dst << ", " << float_value(fn, ins.a) << ", "
		     << float_value(fn, ins.b) << "\n";
		remember_xmm_reg(ins.dest, dst);
	}

	string float_binary_opcode(const string& op) const
	{
		if (op == "add") return "add";
		if (op == "sub") return "sub";
		if (op == "mul") return "mul";
		if (op == "div") return "div";
		return op;
	}

	string float_binary_dest(const lowir2cy86::Instruction& ins)
	{
		if (ins.b.kind == lowir2cy86::ValueKind::Literal)
			return "xmm0";
		return xmm_reg(ins.dest);
	}

	string binary_dest_reg(const lowir2cy86::Instruction& ins)
	{
		if (ins.a.kind == lowir2cy86::ValueKind::Temp &&
		    ins.b.kind == lowir2cy86::ValueKind::Temp &&
		    ins.a.text == ins.b.text)
		{
			if (temp_reg(ins.a.text) == "rax")
				return "r8";
			return temp_reg(ins.a.text);
		}
		if (ins.a.kind == lowir2cy86::ValueKind::Temp &&
		    use_counts_[ins.a.text] == 1)
			return temp_reg(ins.a.text);
		return temp_reg(ins.dest);
	}

	void remember_temp_reg(const string& name, const string& reg)
	{
		for (size_t i = 0; i < temp_names_.size(); ++i)
		{
			if (temp_names_[i] == name)
			{
				temp_regs_[i] = reg;
				return;
			}
		}
		temp_names_.push_back(name);
		temp_regs_.push_back(reg);
	}

	string binary_opcode(const string& op) const
	{
		if (op == "add") return "add";
		if (op == "sub") return "sub";
		if (op == "mul") return "imul";
		if (op == "and") return "and";
		if (op == "or") return "or";
		if (op == "xor") return "xor";
		return op;
	}

	string shift_rhs(const lowir2cy86::Function& fn,
	                 const lowir2cy86::Value& value)
	{
		return value.kind == lowir2cy86::ValueKind::Literal ? value.text : value_reg(fn, value);
	}

	void dump_divmod(const lowir2cy86::Function& fn,
	                 const lowir2cy86::Instruction& ins,
	                 const string& dst,
	                 bool signed_div)
	{
		out_ << "    mov rcx, " << value_reg(fn, ins.b) << "\n";
		out_ << "    mov rax, " << dst << "\n";
		out_ << "    mov rdx, 0\n";
		out_ << "    " << (signed_div ? "idiv" : "div") << " rcx\n";
		if (ins.op == "mod" || ins.op == "umod")
			out_ << "    mov " << dst << ", rdx\n";
		else
			out_ << "    mov " << dst << ", rax\n";
	}

	void dump_cmp_value(const lowir2cy86::Function& fn,
	                    const lowir2cy86::Instruction& ins)
	{
		if (lowir2cy86::is_float_type(ins.type))
		{
			out_ << "    f" << condition_word(ins.op) << "." << ins.type.text
			     << " rax, " << float_value(fn, ins.a) << ", "
			     << float_value(fn, ins.b) << "\n";
			remember_temp_reg(ins.dest, "rax");
			return;
		}
		const string dst = cmp_value_dest_reg(ins);
		const string lhs = value_reg(fn, ins.a);
		if (dst != lhs)
			out_ << "    mov " << dst << ", " << lhs << "\n";
		const string rhs = compare_rhs(fn, ins.b);
		out_ << "    cmp." << ins.type.text << " " << dst << ", " << rhs << "\n";
		out_ << "    set" << condition_suffix(ins.op) << " " << dst << "\n";
		out_ << "    movzx " << dst << ", " << dst << "\n";
		remember_temp_reg(ins.dest, dst);
	}

	string condition_word(const string& op) const
	{
		if (op == "eq") return "eq";
		if (op == "ne") return "ne";
		if (op == "lt" || op == "ult") return "lt";
		if (op == "le" || op == "ule") return "le";
		if (op == "gt" || op == "ugt") return "gt";
		if (op == "ge" || op == "uge") return "ge";
		return op;
	}

	string cmp_value_dest_reg(const lowir2cy86::Instruction& ins)
	{
		if (ins.a.kind == lowir2cy86::ValueKind::Temp &&
		    use_counts_[ins.a.text] == 1)
			return temp_reg(ins.a.text);
		return temp_reg(ins.dest);
	}

	string compare_rhs(const lowir2cy86::Function& fn,
	                   const lowir2cy86::Value& value)
	{
		if (value.kind == lowir2cy86::ValueKind::Literal)
		{
			out_ << "    mov rdx, " << value.text << "\n";
			return "rdx";
		}
		return value_reg(fn, value);
	}

	string condition_suffix(const string& op) const
	{
		if (op == "eq") return "e";
		if (op == "ne") return "ne";
		if (op == "lt") return "l";
		if (op == "le") return "le";
		if (op == "gt") return "g";
		if (op == "ge") return "ge";
		if (op == "ult") return "b";
		if (op == "ule") return "be";
		if (op == "ugt") return "a";
		if (op == "uge") return "ae";
		return op;
	}

	string branch_suffix(const string& op) const
	{
		if (op == "eq") return "e";
		if (op == "ne") return "ne";
		if (op == "lt") return "l";
		if (op == "le") return "le";
		if (op == "gt") return "g";
		if (op == "ge") return "ge";
		if (op == "ult") return "b";
		if (op == "ule") return "be";
		if (op == "ugt") return "a";
		if (op == "uge") return "ae";
		return "ne";
	}

	void dump_branch(const lowir2cy86::Function& fn,
	                 const lowir2cy86::Instruction& ins)
	{
		if (ins.a.kind == lowir2cy86::ValueKind::Temp &&
		    direct_branch_cmp_.find(ins.a.text) != direct_branch_cmp_.end())
		{
			const lowir2cy86::Instruction& cmp = *definitions_[ins.a.text];
			if (lowir2cy86::is_float_type(cmp.type))
			{
				dump_float_branch(fn, cmp, ins.target, ins.target_false);
				return;
			}
			const string lhs = direct_cmp_lhs(fn, cmp);
			const string rhs = direct_cmp_rhs(fn, cmp);
			out_ << "    cmp." << cmp.type.text << " " << lhs << ", "
			     << rhs << "\n";
			out_ << "    j" << branch_suffix(cmp.op) << " " << ins.target << "\n";
			out_ << "    jmp " << ins.target_false << "\n";
			return;
		}
		out_ << "    cmp.i64 " << value_reg(fn, ins.a) << ", 0\n";
		out_ << "    jne " << ins.target << "\n";
		out_ << "    jmp " << ins.target_false << "\n";
	}

	void dump_float_branch(const lowir2cy86::Function& fn,
	                       const lowir2cy86::Instruction& cmp,
	                       const string& target,
	                       const string& target_false)
	{
		out_ << "    fcmp." << cmp.type.text << " " << float_value(fn, cmp.a)
		     << ", " << float_value(fn, cmp.b) << "\n";
		if (cmp.op == "ne")
			out_ << "    jp " << target << "\n";
		else
			out_ << "    jp " << target_false << "\n";
		out_ << "    j" << float_branch_suffix(cmp.op) << " " << target << "\n";
		out_ << "    jmp " << target_false << "\n";
	}

	string float_branch_suffix(const string& op) const
	{
		if (op == "eq") return "e";
		if (op == "ne") return "ne";
		if (op == "lt") return "a";
		if (op == "le") return "ae";
		if (op == "gt") return "b";
		if (op == "ge") return "be";
		return branch_suffix(op);
	}

	string direct_cmp_lhs(const lowir2cy86::Function& fn,
	                      const lowir2cy86::Instruction& cmp)
	{
		if (cmp.a.kind == lowir2cy86::ValueKind::Literal)
		{
			out_ << "    mov rax, " << cmp.a.text << "\n";
			return "rax";
		}
		return value_reg(fn, cmp.a);
	}

	string direct_cmp_rhs(const lowir2cy86::Function& fn,
	                      const lowir2cy86::Instruction& cmp)
	{
		if (cmp.b.kind == lowir2cy86::ValueKind::Literal &&
		    lowir2cy86::is_integer_type(cmp.type) && cmp.type.bits < 32)
		{
			out_ << "    mov rdx, " << cmp.b.text << "\n";
			return "rdx";
		}
		return cmp.b.kind == lowir2cy86::ValueKind::Literal
		           ? cmp.b.text
		           : value_reg(fn, cmp.b);
	}

	void dump_call(const lowir2cy86::Function& fn,
	               const lowir2cy86::Instruction& ins)
	{
		for (size_t i = 0; i < ins.args.size() && i < 6; ++i)
			out_ << "    mov " << abi_gpr(i) << ", "
			     << value_reg(fn, ins.args[i]) << "\n";
		if (ins.a.kind == lowir2cy86::ValueKind::Function)
			out_ << "    call " << ins.a.text << "\n";
		else
			out_ << "    call *" << value_reg(fn, ins.a) << "\n";
		if (ins.has_dest && !lowir2cy86::is_void_type(ins.type))
			out_ << "    mov " << temp_reg(ins.dest) << ", rax\n";
	}

	void dump_atomic(const lowir2cy86::Function& fn,
	                 const lowir2cy86::Instruction& ins)
	{
		const string dst = ins.has_dest ? temp_reg(ins.dest) : "rax";
		if (ins.kind == lowir2cy86::InstrKind::AtomicExchange)
			out_ << "    xchg." << ins.type.text << " ["
			     << value_reg(fn, ins.a) << "], " << value_reg(fn, ins.b) << "\n";
		else if (ins.kind == lowir2cy86::InstrKind::AtomicAddFetch)
			out_ << "    lock_xadd." << ins.type.text << " ["
			     << value_reg(fn, ins.a) << "], " << value_reg(fn, ins.b) << "\n";
		else
			out_ << "    lock_cmpxchg." << ins.type.text << " ["
			     << value_reg(fn, ins.a) << "], " << value_reg(fn, ins.c) << "\n";
		if (ins.has_dest)
			out_ << "    mov " << dst << ", rax\n";
	}

	void dump_switch(const lowir2cy86::Function& fn,
	                 const lowir2cy86::Instruction& ins)
	{
		out_ << "    mov rax, " << value_reg(fn, ins.a) << "\n";
		for (size_t i = 0; i < ins.switch_cases.size(); ++i)
		{
			out_ << "    mov rcx, " << value_reg(fn, ins.switch_cases[i].value)
			     << "\n";
			out_ << "    cmp.i64 rax, rcx\n";
			out_ << "    je " << ins.switch_cases[i].target << "\n";
		}
		out_ << "    jmp " << ins.target << "\n";
	}

	void dump_return(const lowir2cy86::Function& fn,
	                 const lowir2cy86::Instruction& ins)
	{
		if (lowir2cy86::is_void_type(ins.type))
		{
			out_ << "    ret\n";
			return;
		}
		const string src = value_reg(fn, ins.a);
		if (src != "rax")
			out_ << "    mov rax, " << src << "\n";
		out_ << "    ret rax\n";
	}
};

void write_machine_ir_file(const lowir2cy86::Program& program,
                           const Options& options)
{
	MirDumper dumper(program, effective_target(options));
	write_text_file(options.machine_ir_file, dumper.dump());
}

}  // namespace

void compile(const vector<string>& srcfiles, const Options& options)
{
	if (!options.target.empty() && options.target != "linux")
		throw runtime_error("unsupported target");
	lowir2cy86::Program program = lowir2cy86::parse_files(srcfiles);
	lowir2cy86::validate_and_layout(program);
	if (!options.machine_ir_file.empty())
		write_machine_ir_file(program, options);
	if (!options.outfile.empty())
		write_native_file(program, options);
}

}  // namespace lowir2native
