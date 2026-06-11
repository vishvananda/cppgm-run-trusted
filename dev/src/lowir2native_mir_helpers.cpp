#include "lowir2cy86.h"
#include "lowir2native.h"

#include <cstddef>
#include <fstream>
#include <ostream>
#include <stdexcept>
#include <string>

using namespace std;

namespace lowir2native {

bool metadata_is(const lowir2cy86::Metadata& md,
                 const string& key,
                 const string& value);

string effective_target(const Options& options)
{
	return options.target.empty() ? "linux" : options.target;
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

void dump_mir_startup(ostream& out, const lowir2cy86::Program& program)
{
	if (program.entry_function.empty())
		return;
	out << "startup\n";
	if (!program.init_function.empty())
		out << "    call " << program.init_function << "\n";
	out << "    call " << program.entry_function << "\n";
	if (!program.fini_function.empty())
	{
		out << "    mov r12, rax\n";
		out << "    call " << program.fini_function << "\n";
		out << "    mov rdi, r12\n";
	}
	else
		out << "    mov rdi, rax\n";
	out << "    exit\n\n";
}

string addend_text(bool has, int addend)
{
	if (!has)
		return "";
	return addend >= 0 ? " + " + to_string(addend)
	                   : " - " + to_string(-addend);
}

void dump_global_item(ostream& out, const lowir2cy86::GlobalDataItem& item)
{
	if (item.kind == "zero")
		out << "  item zero " << item.zero_bytes << "\n";
	else if (item.kind == "addr")
		out << "  item ptr addr " << item.target
		    << addend_text(item.has_addend, item.addend) << "\n";
	else
		out << "  item " << item.type.text << " " << item.literal << "\n";
}

void dump_mir_globals(ostream& out, const lowir2cy86::Program& program)
{
	for (size_t i = 0; i < program.globals.size(); ++i)
	{
		const lowir2cy86::Global& g = program.globals[i];
		if (g.declaration)
			continue;
		out << "global " << g.name;
		if (metadata_is(g.metadata, "storage", "readonly"))
			out << " readonly";
		if (metadata_is(g.metadata, "storage", "thread_local"))
			out << " thread_local";
		out << "\n";
		if (g.has_type)
		{
			out << "  storage scalar " << g.type.text << "\n";
			if (g.init.kind == "zero")
				out << "  init " << g.type.text << " 0\n";
			else if (g.init.kind == "addr")
				out << "  init ptr addr " << g.init.target
				    << addend_text(g.init.has_addend, g.init.addend) << "\n";
			else
				out << "  init " << g.type.text << " " << g.init.literal << "\n";
		}
		else
		{
			out << "  storage data\n";
			for (size_t j = 0; j < g.data.size(); ++j)
				dump_global_item(out, g.data[j]);
		}
		out << "\n";
	}
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

bool function_uses_float(const lowir2cy86::Function& fn)
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

size_t raw_stack_size(const lowir2cy86::Function& fn)
{
	size_t bytes = 0;
	for (size_t i = 0; i < fn.slots.size(); ++i)
	{
		const size_t end = fn.slots[i].offset;
		if (end > bytes)
			bytes = end;
	}
	return bytes;
}

size_t align_to(size_t value, size_t alignment)
{
	if (alignment == 0)
		return value;
	const size_t rem = value % alignment;
	return rem == 0 ? value : value + alignment - rem;
}

string binary_opcode(const string& op)
{
	if (op == "add") return "add";
	if (op == "sub") return "sub";
	if (op == "mul") return "imul";
	if (op == "and") return "and";
	if (op == "or") return "or";
	if (op == "xor") return "xor";
	return op;
}

string float_binary_opcode(const string& op)
{
	if (op == "add") return "add";
	if (op == "sub") return "sub";
	if (op == "mul") return "mul";
	if (op == "div") return "div";
	return op;
}

string condition_word(const string& op)
{
	if (op == "eq") return "eq";
	if (op == "ne") return "ne";
	if (op == "lt" || op == "ult") return "lt";
	if (op == "le" || op == "ule") return "le";
	if (op == "gt" || op == "ugt") return "gt";
	if (op == "ge" || op == "uge") return "ge";
	return op;
}

string condition_suffix(const string& op)
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

string branch_suffix(const string& op)
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

string float_branch_suffix(const string& op)
{
	if (op == "eq") return "e";
	if (op == "ne") return "ne";
	if (op == "lt") return "a";
	if (op == "le") return "ae";
	if (op == "gt") return "b";
	if (op == "ge") return "be";
	return branch_suffix(op);
}

}  // namespace lowir2native
