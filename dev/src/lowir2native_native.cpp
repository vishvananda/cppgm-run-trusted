#include "lowir2native.h"

#include "cy86_model.h"
#include "lowir2cy86.h"

#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <cstdint>
#include <algorithm>
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

bool starts_with(const string& text, const string& prefix)
{
	return text.compare(0, prefix.size(), prefix) == 0;
}

string trim_cy86_indent(const string& line)
{
	size_t pos = 0;
	while (pos < line.size() && (line[pos] == '\t' || line[pos] == ' '))
		++pos;
	return line.substr(pos);
}

bool is_x64_zero_line(const string& line)
{
	return trim_cy86_indent(line) == "move64 x64 0;";
}

bool parse_x_narrow_load(const string& line, int& width)
{
	const string body = trim_cy86_indent(line);
	if (body == "move8 x8 [x64];")
	{
		width = 8;
		return true;
	}
	if (body == "move16 x16 [x64];")
	{
		width = 16;
		return true;
	}
	return false;
}

string sanitize_cy86_indirect_narrow_load_aliases(const string& text)
{
	istringstream in(text);
	vector<string> lines;
	string line;
	while (getline(in, line))
		lines.push_back(line);
	ostringstream out;
	for (size_t i = 0; i < lines.size(); ++i)
	{
		int width = 0;
		if (i + 2 < lines.size() &&
		    starts_with(trim_cy86_indent(lines[i]), "move64 x64 ") &&
		    is_x64_zero_line(lines[i + 1]) &&
		    parse_x_narrow_load(lines[i + 2], width))
		{
			const string indent =
			    lines[i].substr(0, lines[i].size() - trim_cy86_indent(lines[i]).size());
			out << lines[i] << "\n";
			out << indent << "move64 y64 0;\n";
			out << indent << "move" << width << " y" << width << " [x64];\n";
			out << indent << "move64 x64 0;\n";
			out << indent << "move" << width << " x" << width << " y" << width << ";\n";
			i += 2;
			continue;
		}
		out << lines[i] << "\n";
	}
	return out.str();
}

void note_temp_use(const lowir2cy86::Value& value, map<string, int>& uses)
{
	if (value.kind == lowir2cy86::ValueKind::Temp)
		++uses[value.text];
}

void count_instruction_temp_uses(const lowir2cy86::Instruction& ins,
                                 map<string, int>& uses)
{
	note_temp_use(ins.a, uses);
	note_temp_use(ins.b, uses);
	note_temp_use(ins.c, uses);
	for (size_t i = 0; i < ins.args.size(); ++i)
		note_temp_use(ins.args[i], uses);
	for (size_t i = 0; i < ins.switch_cases.size(); ++i)
		note_temp_use(ins.switch_cases[i].value, uses);
}

bool is_scalar_ptr_global(const lowir2cy86::Program& program, const string& name)
{
	map<string, size_t>::const_iterator it = program.global_by_name.find(name);
	if (it == program.global_by_name.end())
		return false;
	const lowir2cy86::Global& g = program.globals[it->second];
	return g.has_type && lowir2cy86::is_ptr_type(g.type);
}

size_t zero_data_alignment(size_t bytes)
{
	return bytes >= 16 ? static_cast<size_t>(16) : static_cast<size_t>(1);
}

size_t native_global_alignment(const lowir2cy86::Global& global)
{
	if (global.data.empty())
		return global.has_type ? global.type.align : static_cast<size_t>(1);
	size_t align = 1;
	for (size_t i = 0; i < global.data.size(); ++i)
	{
		const lowir2cy86::GlobalDataItem& item = global.data[i];
		if (item.kind == "zero")
			align = max(align, zero_data_alignment(item.zero_bytes));
		else if (item.kind == "addr")
			align = max<size_t>(align, 8);
		else
			align = max(align, item.type.align);
	}
	return align;
}

string inject_native_global_alignments(const string& text,
                                       const lowir2cy86::Program& program)
{
	map<string, size_t> alignments;
	for (size_t i = 0; i < program.globals.size(); ++i)
	{
		const lowir2cy86::Global& global = program.globals[i];
		if (global.declaration)
			continue;
		const size_t align = native_global_alignment(global);
		if (align >= 16)
			alignments[lowir2cy86::global_label(global.name) + ":"] = align;
	}
	istringstream in(text);
	ostringstream out;
	string line;
	while (getline(in, line))
	{
		if (alignments.find(line) != alignments.end())
			out << "align16;\n";
		out << line << "\n";
	}
	return out.str();
}

void rewrite_indirect_global_pointer_callees(lowir2cy86::Program& program)
{
	const lowir2cy86::Type ptr_type = lowir2cy86::parse_type_text("ptr");
	for (size_t f = 0; f < program.functions.size(); ++f)
	{
		lowir2cy86::Function& fn = program.functions[f];
		map<string, int> uses;
		map<string, lowir2cy86::Instruction*> defs;
		set<string> indirect_callees;
		for (size_t b = 0; b < fn.blocks.size(); ++b)
			for (size_t i = 0; i < fn.blocks[b].instructions.size(); ++i)
			{
				lowir2cy86::Instruction& ins = fn.blocks[b].instructions[i];
				count_instruction_temp_uses(ins, uses);
				if (ins.has_dest)
					defs[ins.dest] = &ins;
				if (ins.kind == lowir2cy86::InstrKind::Call &&
				    ins.a.kind == lowir2cy86::ValueKind::Temp)
					indirect_callees.insert(ins.a.text);
			}
		for (set<string>::const_iterator it = indirect_callees.begin();
		     it != indirect_callees.end(); ++it)
		{
			if (uses[*it] != 1)
				continue;
			map<string, lowir2cy86::Instruction*>::iterator dit = defs.find(*it);
			if (dit == defs.end() || dit->second->kind != lowir2cy86::InstrKind::Addr ||
			    dit->second->a.kind != lowir2cy86::ValueKind::Global ||
			    !is_scalar_ptr_global(program, dit->second->a.text))
				continue;
			dit->second->kind = lowir2cy86::InstrKind::Load;
			dit->second->type = ptr_type;
		}
	}
}

}  // namespace

void write_native_file(const lowir2cy86::Program& program,
                       const Options& options)
{
	lowir2cy86::Program native_program = program;
	rewrite_indirect_global_pointer_callees(native_program);
	const string tmp = temp_cy86_path(options.outfile);
	const string cy86_text =
	    inject_native_global_alignments(lowir2cy86::emit_cy86_for_native(native_program),
	                                    native_program);
	write_text_file(tmp,
	                sanitize_cy86_indirect_narrow_load_aliases(
	                    sanitize_cy86_floating_literals(cy86_text)));
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

}  // namespace lowir2native
