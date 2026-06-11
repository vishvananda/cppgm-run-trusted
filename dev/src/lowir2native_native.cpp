#include "lowir2native.h"

#include "cy86_model.h"
#include "lowir2cy86.h"

#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <cstdint>
#include <fstream>
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

}  // namespace

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

}  // namespace lowir2native
