#include "cy86_model.h"

#include <algorithm>
#include <cstring>
#include <limits>
#include <stdexcept>

using namespace std;

namespace cy86 {
namespace {

void append_le(vector<unsigned char>& out, uint64_t value, size_t nbytes)
{
	for (size_t i = 0; i < nbytes; ++i)
		out.push_back(static_cast<unsigned char>((value >> (i * 8)) & 0xff));
}

size_t fundamental_size(EFundamentalType type)
{
	switch (type)
	{
	case FT_SIGNED_CHAR:
	case FT_UNSIGNED_CHAR:
	case FT_CHAR:
	case FT_BOOL:
		return 1;
	case FT_SHORT_INT:
	case FT_UNSIGNED_SHORT_INT:
	case FT_CHAR16_T:
		return 2;
	case FT_INT:
	case FT_UNSIGNED_INT:
	case FT_WCHAR_T:
	case FT_CHAR32_T:
	case FT_FLOAT:
		return 4;
	case FT_LONG_INT:
	case FT_LONG_LONG_INT:
	case FT_UNSIGNED_LONG_INT:
	case FT_UNSIGNED_LONG_LONG_INT:
	case FT_DOUBLE:
		return 8;
	case FT_LONG_DOUBLE:
		return sizeof(long double);
	default:
		throw runtime_error("unsupported literal type");
	}
}

bool is_signed_integral_type(EFundamentalType type)
{
	return type == FT_SIGNED_CHAR || type == FT_SHORT_INT ||
	       type == FT_INT || type == FT_LONG_INT ||
	       type == FT_LONG_LONG_INT || type == FT_CHAR;
}

bool is_unsigned_integral_type(EFundamentalType type)
{
	return type == FT_UNSIGNED_CHAR || type == FT_UNSIGNED_SHORT_INT ||
	       type == FT_UNSIGNED_INT || type == FT_UNSIGNED_LONG_INT ||
	       type == FT_UNSIGNED_LONG_LONG_INT || type == FT_CHAR16_T ||
	       type == FT_CHAR32_T || type == FT_WCHAR_T || type == FT_BOOL;
}

bool source_looks_floating(const string& source)
{
	for (size_t i = 0; i < source.size(); ++i)
	{
		const char c = source[i];
		if (c == '.' || c == 'e' || c == 'E')
			return true;
	}
	return false;
}

EFundamentalType floating_type(const string& source)
{
	if (source.empty())
		return FT_DOUBLE;
	const char c = source[source.size() - 1];
	if (c == 'f' || c == 'F')
		return FT_FLOAT;
	if (c == 'l' || c == 'L')
		return FT_LONG_DOUBLE;
	return FT_DOUBLE;
}

template <class T>
vector<unsigned char> raw_bytes(T value)
{
	vector<unsigned char> out(sizeof(T));
	memcpy(out.data(), &value, sizeof(T));
	return out;
}

LiteralValue make_integer_literal(const string& source,
                                  EFundamentalType type,
                                  uint64_t value)
{
	LiteralValue out;
	out.source = source;
	out.type = type;
	out.alignment = fundamental_size(type);
	out.signed_integral = is_signed_integral_type(type);
	out.unsigned_integral = is_unsigned_integral_type(type);
	out.arithmetic = true;
	append_le(out.bytes, value, fundamental_size(type));
	return out;
}

LiteralValue make_float_literal(const string& source, EFundamentalType type)
{
	LiteralValue out;
	out.source = source;
	out.type = type;
	out.alignment = fundamental_size(type);
	out.floating = true;
	out.arithmetic = true;
	if (type == FT_FLOAT)
		out.bytes = raw_bytes(PA2Decode_float(source));
	else if (type == FT_DOUBLE)
		out.bytes = raw_bytes(PA2Decode_double(source));
	else
		out.bytes = raw_bytes(PA2Decode_long_double(source));
	return out;
}

bool valid_float_suffix(const string& source)
{
	if (source.find('_') != string::npos)
		return false;
	if (source.empty())
		return false;
	const char c = source[source.size() - 1];
	if (isalpha(static_cast<unsigned char>(c)))
		return c == 'f' || c == 'F' || c == 'l' || c == 'L';
	return true;
}

OperandDesc parse_operand_desc(const string& text)
{
	OperandDesc out;
	for (size_t i = 0; i < text.size();)
	{
		const char c = text[i];
		if (isdigit(static_cast<unsigned char>(c)))
		{
			size_t end = i;
			while (end < text.size() && isdigit(static_cast<unsigned char>(text[end])))
				++end;
			out.width_bits = stoi(text.substr(i, end - i));
			i = end;
			continue;
		}
		if (c == 'w')
			out.write = true;
		else if (c == 'r')
			out.read = true;
		else if (c == 'a')
			out.address = true;
		else if (c == 'b')
			out.boolean_value = true;
		else if (c == 'i')
			out.integer = true;
		else if (c == 's')
			out.signed_integer = true;
		else if (c == 'u')
			out.unsigned_integer = true;
		else if (c == 'f')
			out.floating = true;
		else if (c == 'I')
			out.immediate_only = true;
		else
			throw runtime_error("invalid opcode descriptor");
		++i;
	}
	return out;
}

OpcodeDesc make_opcode(const string& line)
{
	size_t pos = line.find(' ');
	OpcodeDesc out;
	out.name = pos == string::npos ? line : line.substr(0, pos);
	while (pos != string::npos)
	{
		while (pos < line.size() && line[pos] == ' ')
			++pos;
		if (pos >= line.size())
			break;
		size_t end = line.find(' ', pos);
		out.operands.push_back(parse_operand_desc(line.substr(pos, end - pos)));
		pos = end;
	}
	if (out.name.size() > 4 && out.name.compare(0, 4, "data") == 0)
	{
		out.data_opcode = true;
		out.data_width_bits = stoi(out.name.substr(4));
	}
	return out;
}

const vector<OpcodeDesc>& opcode_table()
{
	static const char* const lines[] = {
		"data8 rI8", "data16 rI16", "data32 rI32", "data64 rI64",
		"move8 w8 r8", "move16 w16 r16", "move32 w32 r32",
		"move64 w64 r64", "move80 w80 r80",
		"jump ar64", "jumpif br8 ar64", "call ar64", "ret",
		"not8 w8 r8", "not16 w16 r16", "not32 w32 r32", "not64 w64 r64",
		"bswap8 w8 r8", "bswap16 w16 r16", "bswap32 w32 r32", "bswap64 w64 r64",
		"and8 w8 r8 r8", "and16 w16 r16 r16", "and32 w32 r32 r32", "and64 w64 r64 r64",
		"or8 w8 r8 r8", "or16 w16 r16 r16", "or32 w32 r32 r32", "or64 w64 r64 r64",
		"xor8 w8 r8 r8", "xor16 w16 r16 r16", "xor32 w32 r32 r32", "xor64 w64 r64 r64",
		"lshift8 iw8 ir8 ur8", "lshift16 iw16 ir16 ur8", "lshift32 iw32 ir32 ur8", "lshift64 iw64 ir64 ur8",
		"srshift8 sw8 sr8 ur8", "srshift16 sw16 sr16 ur8", "srshift32 sw32 sr32 ur8", "srshift64 sw64 sr64 ur8",
		"urshift8 uw8 ur8 ur8", "urshift16 uw16 ur16 ur8", "urshift32 uw32 ur32 ur8", "urshift64 uw64 ur64 ur8",
		"s8convf80 fw80 sr8", "s16convf80 fw80 sr16", "s32convf80 fw80 sr32", "s64convf80 fw80 sr64",
		"u8convf80 fw80 ur8", "u16convf80 fw80 ur16", "u32convf80 fw80 ur32", "u64convf80 fw80 ur64",
		"f32convf80 fw80 fr32", "f64convf80 fw80 fr64",
		"f80convs8 sw8 fr80", "f80convs16 sw16 fr80", "f80convs32 sw32 fr80", "f80convs64 sw64 fr80",
		"f80convu8 uw8 fr80", "f80convu16 uw16 fr80", "f80convu32 uw32 fr80", "f80convu64 uw64 fr80",
		"f80convf32 fw32 fr80", "f80convf64 fw64 fr80",
		"iadd8 iw8 ir8 ir8", "iadd16 iw16 ir16 ir16", "iadd32 iw32 ir32 ir32", "iadd64 iw64 ir64 ir64",
		"fadd32 fw32 fr32 fr32", "fadd64 fw64 fr64 fr64", "fadd80 fw80 fr80 fr80",
		"isub8 iw8 ir8 ir8", "isub16 iw16 ir16 ir16", "isub32 iw32 ir32 ir32", "isub64 iw64 ir64 ir64",
		"fsub32 fw32 fr32 fr32", "fsub64 fw64 fr64 fr64", "fsub80 fw80 fr80 fr80",
		"smul8 sw8 sr8 sr8", "smul16 sw16 sr16 sr16", "smul32 sw32 sr32 sr32", "smul64 sw64 sr64 sr64",
		"umul8 uw8 ur8 ur8", "umul16 uw16 ur16 ur16", "umul32 uw32 ur32 ur32", "umul64 uw64 ur64 ur64",
		"fmul32 fw32 fr32 fr32", "fmul64 fw64 fr64 fr64", "fmul80 fw80 fr80 fr80",
		"sdiv8 sw8 sr8 sr8", "sdiv16 sw16 sr16 sr16", "sdiv32 sw32 sr32 sr32", "sdiv64 sw64 sr64 sr64",
		"udiv8 uw8 ur8 ur8", "udiv16 uw16 ur16 ur16", "udiv32 uw32 ur32 ur32", "udiv64 uw64 ur64 ur64",
		"fdiv32 fw32 fr32 fr32", "fdiv64 fw64 fr64 fr64", "fdiv80 fw80 fr80 fr80",
		"smod8 sw8 sr8 sr8", "smod16 sw16 sr16 sr16", "smod32 sw32 sr32 sr32", "smod64 sw64 sr64 sr64",
		"umod8 uw8 ur8 ur8", "umod16 uw16 ur16 ur16", "umod32 uw32 ur32 ur32", "umod64 uw64 ur64 ur64",
		"ieq8 wb8 ir8 ir8", "ieq16 wb8 ir16 ir16", "ieq32 wb8 ir32 ir32", "ieq64 wb8 ir64 ir64",
		"feq32 wb8 fr32 fr32", "feq64 wb8 fr64 fr64", "feq80 wb8 fr80 fr80",
		"ine8 wb8 ir8 ir8", "ine16 wb8 ir16 ir16", "ine32 wb8 ir32 ir32", "ine64 wb8 ir64 ir64",
		"fne32 wb8 fr32 fr32", "fne64 wb8 fr64 fr64", "fne80 wb8 fr80 fr80",
		"slt8 wb8 sr8 sr8", "slt16 wb8 sr16 sr16", "slt32 wb8 sr32 sr32", "slt64 wb8 sr64 sr64",
		"ult8 wb8 ur8 ur8", "ult16 wb8 ur16 ur16", "ult32 wb8 ur32 ur32", "ult64 wb8 ur64 ur64",
		"flt32 wb8 fr32 fr32", "flt64 wb8 fr64 fr64", "flt80 wb8 fr80 fr80",
		"sgt8 wb8 sr8 sr8", "sgt16 wb8 sr16 sr16", "sgt32 wb8 sr32 sr32", "sgt64 wb8 sr64 sr64",
		"ugt8 wb8 ur8 ur8", "ugt16 wb8 ur16 ur16", "ugt32 wb8 ur32 ur32", "ugt64 wb8 ur64 ur64",
		"fgt32 wb8 fr32 fr32", "fgt64 wb8 fr64 fr64", "fgt80 wb8 fr80 fr80",
		"sle8 wb8 sr8 sr8", "sle16 wb8 sr16 sr16", "sle32 wb8 sr32 sr32", "sle64 wb8 sr64 sr64",
		"ule8 wb8 ur8 ur8", "ule16 wb8 ur16 ur16", "ule32 wb8 ur32 ur32", "ule64 wb8 ur64 ur64",
		"fle32 wb8 fr32 fr32", "fle64 wb8 fr64 fr64", "fle80 wb8 fr80 fr80",
		"sge8 wb8 sr8 sr8", "sge16 wb8 sr16 sr16", "sge32 wb8 sr32 sr32", "sge64 wb8 sr64 sr64",
		"uge8 wb8 ur8 ur8", "uge16 wb8 ur16 ur16", "uge32 wb8 ur32 ur32", "uge64 wb8 ur64 ur64",
		"fge32 wb8 fr32 fr32", "fge64 wb8 fr64 fr64", "fge80 wb8 fr80 fr80",
		"syscall0 w64 r64", "syscall1 w64 r64 r64", "syscall2 w64 r64 r64 r64",
		"syscall3 w64 r64 r64 r64 r64", "syscall4 w64 r64 r64 r64 r64 r64",
		"syscall5 w64 r64 r64 r64 r64 r64 r64",
		"syscall6 w64 r64 r64 r64 r64 r64 r64 r64"
	};
	static vector<OpcodeDesc> table;
	if (table.empty())
	{
		for (size_t i = 0; i < sizeof(lines) / sizeof(lines[0]); ++i)
			table.push_back(make_opcode(lines[i]));
	}
	return table;
}

}  // namespace

RegisterRef::RegisterRef() : base(RegisterBase::X), width_bits(0) {}

LiteralValue::LiteralValue()
	: type(FT_INT),
	  alignment(1),
	  signed_integral(false),
	  unsigned_integral(false),
	  floating(false),
	  arithmetic(false)
{
}

ImmediateValue::ImmediateValue()
	: label(false), has_addend(false), addend_sign(1)
{
}

MemoryAddress::MemoryAddress()
	: kind(AddressKind::Literal), has_addend(false), addend_sign(1)
{
}

Operand::Operand() : kind(OperandKind::Immediate) {}

Statement::Statement()
	: kind(StatementKind::Instruction), offset(0), size(0)
{
}

OperandDesc::OperandDesc()
	: write(false), read(false), address(false), boolean_value(false),
	  integer(false), signed_integer(false), unsigned_integer(false),
	  floating(false), immediate_only(false), width_bits(0)
{
}

OpcodeDesc::OpcodeDesc() : data_opcode(false), data_width_bits(0) {}

bool parse_register(const string& name, RegisterRef& out)
{
	if (name == "sp" || name == "bp")
	{
		out.name = name;
		out.base = name == "sp" ? RegisterBase::SP : RegisterBase::BP;
		out.width_bits = 64;
		return true;
	}
	if (name.size() < 2)
		return false;
	RegisterBase base;
	if (name[0] == 'x')
		base = RegisterBase::X;
	else if (name[0] == 'y')
		base = RegisterBase::Y;
	else if (name[0] == 'z')
		base = RegisterBase::Z;
	else if (name[0] == 't')
		base = RegisterBase::T;
	else
		return false;
	const string suffix = name.substr(1);
	if (suffix != "8" && suffix != "16" && suffix != "32" && suffix != "64")
		return false;
	out.name = name;
	out.base = base;
	out.width_bits = stoi(suffix);
	return true;
}

bool is_register_name(const string& name)
{
	RegisterRef reg;
	return parse_register(name, reg);
}

int register_family_x86_code(RegisterBase base)
{
	switch (base)
	{
	case RegisterBase::SP: return 4;
	case RegisterBase::BP: return 5;
	case RegisterBase::X: return 12;
	case RegisterBase::Y: return 13;
	case RegisterBase::Z: return 14;
	case RegisterBase::T: return 15;
	}
	return 0;
}

const OpcodeDesc* find_opcode(const string& name)
{
	const vector<OpcodeDesc>& table = opcode_table();
	for (size_t i = 0; i < table.size(); ++i)
	{
		if (table[i].name == name)
			return &table[i];
	}
	return NULL;
}

bool is_opcode_name(const string& name)
{
	return find_opcode(name) != NULL;
}

LiteralValue parse_literal_value(const string& source)
{
	IntegerLiteralInfo int_info;
	if (AnalyzeIntegerLiteral(source, int_info))
	{
		if (int_info.user_defined)
			throw runtime_error("user-defined literal is invalid in CY86");
		return make_integer_literal(source, int_info.type, int_info.value);
	}
	CharacterLiteralInfo char_info;
	if (AnalyzeCharacterLiteral(source, false, char_info))
		return make_integer_literal(source, char_info.type, char_info.code_point);
	StringLiteralInfo string_info;
	if (AnalyzeStringLiteral(source, string_info))
	{
		if (!string_info.ud_suffix.empty())
			throw runtime_error("user-defined literal is invalid in CY86");
		LiteralValue out;
		out.source = source;
		out.type = string_info.type;
		out.alignment = 1;
		out.bytes = string_info.bytes;
		return out;
	}
	if (source_looks_floating(source) && valid_float_suffix(source))
		return make_float_literal(source, floating_type(source));
	throw runtime_error("invalid literal");
}

LiteralValue negate_literal_value(const LiteralValue& value)
{
	if (!value.arithmetic)
		throw runtime_error("cannot negate non-arithmetic literal");
	LiteralValue out = value;
	if (value.floating)
	{
		if (value.type == FT_FLOAT)
			out.bytes = raw_bytes(-PA2Decode_float(value.source));
		else if (value.type == FT_DOUBLE)
			out.bytes = raw_bytes(-PA2Decode_double(value.source));
		else
			out.bytes = raw_bytes(-PA2Decode_long_double(value.source));
		return out;
	}
	const size_t nbytes = value.bytes.size();
	uint64_t v = 0;
	for (size_t i = 0; i < nbytes && i < 8; ++i)
		v |= static_cast<uint64_t>(value.bytes[i]) << (i * 8);
	const int bits = static_cast<int>(nbytes * 8);
	const uint64_t mask = bits >= 64 ? ~0ULL : ((1ULL << bits) - 1);
	out.bytes.clear();
	append_le(out.bytes, (-v) & mask, nbytes);
	return out;
}

vector<unsigned char> convert_literal_width(const LiteralValue& value,
                                            int width_bits)
{
	const size_t nbytes = static_cast<size_t>(width_bits == 80 ? 10 : width_bits / 8);
	vector<unsigned char> out = value.bytes;
	if (out.size() > nbytes)
	{
		out.resize(nbytes);
		return out;
	}
	if (out.size() < nbytes)
	{
		unsigned char ext = 0;
		if (value.signed_integral && !out.empty() &&
		    (out.back() & 0x80) != 0)
			ext = 0xff;
		out.resize(nbytes, ext);
	}
	return out;
}

uint64_t literal_to_u64(const LiteralValue& value)
{
	vector<unsigned char> bytes = convert_literal_width(value, 64);
	uint64_t out = 0;
	for (size_t i = 0; i < bytes.size(); ++i)
		out |= static_cast<uint64_t>(bytes[i]) << (i * 8);
	return out;
}

uint64_t immediate_to_u64(const ImmediateValue& imm,
                          const map<string, uint64_t>& labels)
{
	if (!imm.label)
		return literal_to_u64(imm.literal);
	map<string, uint64_t>::const_iterator it = labels.find(imm.label_name);
	if (it == labels.end())
		throw runtime_error("undefined label");
	uint64_t out = it->second;
	if (imm.has_addend)
	{
		if (!imm.addend.signed_integral && !imm.addend.unsigned_integral)
			throw runtime_error("label addend must be integral");
		uint64_t add = literal_to_u64(imm.addend);
		out += imm.addend_sign < 0 ? -add : add;
	}
	return out;
}

}  // namespace cy86
