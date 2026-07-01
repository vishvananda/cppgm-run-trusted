#include "pa14_lowir_internal.h"

#include <cctype>

namespace pa14 {
namespace internal {

namespace {

bool lowir_symbol_char(char ch)
{
	return std::isalnum(static_cast<unsigned char>(ch)) ||
	       ch == '_' ||
	       ch == '$';
}

bool text_references_symbol(const string& text, const string& name)
{
	string needle = "@" + name;
	size_t pos = 0;
	while ((pos = text.find(needle, pos)) != string::npos)
	{
		size_t after = pos + needle.size();
		if (after == text.size() || !lowir_symbol_char(text[after]))
			return true;
		pos = after;
	}
	return false;
}

void collect_function_reference_symbols(const FunctionOut& fn)
{
	if (fn.reference_symbols_collected)
		return;
	for (size_t b = 0; b < fn.blocks.size(); ++b)
		for (size_t j = 0; j < fn.blocks[b].instrs.size(); ++j)
		{
			const string& instr = fn.blocks[b].instrs[j];
			size_t scan = 0;
			while (scan < instr.size())
			{
				size_t at = instr.find('@', scan);
				if (at == string::npos)
					break;
				size_t begin = at + 1;
				size_t end = begin;
				while (end < instr.size() &&
				       lowir_symbol_char(instr[end]))
					++end;
				if (end > begin)
				{
					fn.referenced_symbols.insert(
						instr.substr(begin, end - begin));
					scan = end;
				}
				else
					scan = begin;
			}
		}
	fn.reference_symbols_collected = true;
}

bool function_references_symbol(const FunctionOut& fn,
                                const string& name)
{
	collect_function_reference_symbols(fn);
	return fn.referenced_symbols.find(name) != fn.referenced_symbols.end();
}

}  // namespace

bool output_references_function(const ProgramLowerer& program,
                                const string& name,
                                size_t self_index)
{
	for (size_t i = 0; i < program.globals.size(); ++i)
		if (text_references_symbol(program.globals[i], name))
			return true;
	for (size_t i = 0; i < program.functions.size(); ++i)
	{
		if (i == self_index)
			continue;
		const FunctionOut& fn = program.functions[i];
		if (function_references_symbol(fn, name))
			return true;
	}
	return false;
}

bool output_references_function_uncached(const ProgramLowerer& program,
                                         const string& name,
                                         size_t self_index)
{
	return output_references_function(program, name, self_index);
}

}  // namespace internal
}  // namespace pa14
