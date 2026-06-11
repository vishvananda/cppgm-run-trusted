#include "lowir2cy86.h"
#include "lowir2native.h"

#include <cstddef>
#include <fstream>
#include <stdexcept>
#include <string>

using namespace std;

namespace lowir2native {

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

}  // namespace lowir2native
