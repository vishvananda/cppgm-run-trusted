#include "lowir2cy86_emit_helpers.h"

#include <algorithm>
#include <cstdint>
#include <cstdlib>
#include <cstring>

using namespace std;

namespace lowir2cy86 {
namespace {

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
uint64_t raw_float_bits(T value)
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

string native_float_literal_bits(const Type& type, const string& literal)
{
	if (!is_float_type(type) || is_f80_type(type) ||
	    !token_looks_floating(literal))
		return literal;
	const string source = strip_float_suffix(literal);
	char* end = nullptr;
	if (type.bits == 32)
	{
		const float value = strtof(source.c_str(), &end);
		if (end == source.c_str() || *end != '\0')
			return literal;
		return signed_bits_literal(raw_float_bits(value), 32);
	}
	if (type.bits == 64)
	{
		const double value = strtod(source.c_str(), &end);
		if (end == source.c_str() || *end != '\0')
			return literal;
		return signed_bits_literal(raw_float_bits(value), 64);
	}
	return literal;
}

size_t zero_data_alignment(size_t bytes)
{
	return bytes >= 16 ? static_cast<size_t>(16) : static_cast<size_t>(1);
}

}  // namespace

string native_cy86_literal(const Type& type,
                           const string& literal,
                           bool native_output)
{
	return native_output ? native_float_literal_bits(type, literal) : literal;
}

size_t native_global_alignment(const Global& global)
{
	if (global.data.empty())
		return global.has_type ? global.type.align : static_cast<size_t>(1);
	size_t align = 1;
	for (size_t i = 0; i < global.data.size(); ++i)
	{
		const GlobalDataItem& item = global.data[i];
		if (item.kind == "zero")
			align = max(align, zero_data_alignment(item.zero_bytes));
		else if (item.kind == "addr")
			align = max<size_t>(align, 8);
		else
			align = max(align, item.type.align);
	}
	return align;
}

}  // namespace lowir2cy86
