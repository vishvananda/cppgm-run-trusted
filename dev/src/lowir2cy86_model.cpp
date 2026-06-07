#include "lowir2cy86.h"

#include <cctype>
#include <cstdlib>
#include <stdexcept>

using namespace std;

namespace lowir2cy86 {
namespace {

size_t checked_positive_size(const string& text)
{
	char* end = nullptr;
	const unsigned long value = strtoul(text.c_str(), &end, 10);
	if (end == text.c_str() || *end != '\0' || value == 0)
		throw runtime_error("invalid positive integer");
	return static_cast<size_t>(value);
}

bool is_power_of_two(size_t value)
{
	return value != 0 && (value & (value - 1)) == 0;
}

Type make_scalar(TypeKind kind,
                 const string& text,
                 int bits,
                 size_t size,
                 size_t align)
{
	Type out;
	out.kind = kind;
	out.text = text;
	out.bits = bits;
	out.size = size;
	out.align = align;
	return out;
}

}  // namespace

Type::Type()
	: kind(TypeKind::Void),
	  bits(0),
	  size(0),
	  align(1),
	  obj_size(0),
	  obj_align(1)
{
}

MetadataItem::MetadataItem() : global_value(false) {}
Span::Span() : bytes(0), align(1) {}
Value::Value() : kind(ValueKind::None) {}
Parameter::Parameter() : offset(0) {}
Slot::Slot() : offset(0) {}
CallSignature::CallSignature() : present(false) {}

Instruction::Instruction()
	: kind(InstrKind::Const),
	  order_a(0),
	  order_b(0),
	  has_dest(false)
{
}

Block::Block() {}

GlobalInit::GlobalInit() : addend(0), has_addend(false) {}

Global::Global() : declaration(false), has_type(false) {}

Function::Function()
	: declaration(false),
	  hidden_result_offset(0),
	  stack_size(0),
	  convert_scratch_offset(0),
	  needs_convert_scratch(false)
{
}

Program::Program() : needs_eh_runtime(false) {}

Type parse_type_text(const string& text)
{
	if (text == "void")
		return Type();
	if (text == "i1")
		return make_scalar(TypeKind::SignedInt, text, 1, 1, 1);
	if (text == "i8")
		return make_scalar(TypeKind::SignedInt, text, 8, 1, 1);
	if (text == "u8")
		return make_scalar(TypeKind::UnsignedInt, text, 8, 1, 1);
	if (text == "i16")
		return make_scalar(TypeKind::SignedInt, text, 16, 2, 2);
	if (text == "u16")
		return make_scalar(TypeKind::UnsignedInt, text, 16, 2, 2);
	if (text == "i32")
		return make_scalar(TypeKind::SignedInt, text, 32, 4, 4);
	if (text == "u32")
		return make_scalar(TypeKind::UnsignedInt, text, 32, 4, 4);
	if (text == "i64")
		return make_scalar(TypeKind::SignedInt, text, 64, 8, 8);
	if (text == "f32")
		return make_scalar(TypeKind::Float, text, 32, 4, 4);
	if (text == "f64")
		return make_scalar(TypeKind::Float, text, 64, 8, 8);
	if (text == "f80")
		return make_scalar(TypeKind::Float, text, 80, 16, 8);
	if (text == "ptr")
		return make_scalar(TypeKind::Ptr, text, 64, 8, 8);
	if (text.size() > 5 && text.compare(0, 4, "obj<") == 0 &&
	    text[text.size() - 1] == '>')
	{
		return object_type(parse_span_text(text.substr(4, text.size() - 5)).bytes,
		                   parse_span_text(text.substr(4, text.size() - 5)).align);
	}
	throw runtime_error("unknown LowIR type");
}

Type object_type(size_t bytes, size_t align)
{
	if (bytes == 0 || !is_power_of_two(align))
		throw runtime_error("invalid object type");
	Type out;
	out.kind = TypeKind::Obj;
	out.text = "obj<" + to_string(bytes) + "x" + to_string(align) + ">";
	out.bits = static_cast<int>(bytes * 8);
	out.size = bytes;
	out.align = align;
	out.obj_size = bytes;
	out.obj_align = align;
	return out;
}

Span parse_span_text(const string& text)
{
	const size_t x = text.find('x');
	if (x == string::npos)
		throw runtime_error("invalid byte span");
	Span out;
	out.bytes = checked_positive_size(text.substr(0, x));
	out.align = checked_positive_size(text.substr(x + 1));
	if (!is_power_of_two(out.align))
		throw runtime_error("invalid byte span alignment");
	return out;
}

bool is_void_type(const Type& type)
{
	return type.kind == TypeKind::Void;
}

bool is_ptr_type(const Type& type)
{
	return type.kind == TypeKind::Ptr;
}

bool is_obj_type(const Type& type)
{
	return type.kind == TypeKind::Obj;
}

bool is_float_type(const Type& type)
{
	return type.kind == TypeKind::Float;
}

bool is_f80_type(const Type& type)
{
	return is_float_type(type) && type.bits == 80;
}

bool is_integer_type(const Type& type)
{
	return type.kind == TypeKind::SignedInt || type.kind == TypeKind::UnsignedInt;
}

bool is_signed_integer_type(const Type& type)
{
	return type.kind == TypeKind::SignedInt;
}

bool is_scalar_runtime_type(const Type& type)
{
	return is_integer_type(type) || is_float_type(type) || is_ptr_type(type);
}

size_t storage_size(const Type& type)
{
	return type.size;
}

size_t stack_storage_size(const Type& type)
{
	if (is_obj_type(type) || is_f80_type(type))
		return type.size;
	return type.size < 8 ? 8 : type.size;
}

int cy86_width_bits(const Type& type)
{
	if (is_ptr_type(type))
		return 64;
	return type.bits;
}

string metadata_value(const Metadata& items, const string& key)
{
	for (size_t i = 0; i < items.size(); ++i)
	{
		if (items[i].key == key)
			return items[i].value;
	}
	return "";
}

bool metadata_has(const Metadata& metadata, const string& key)
{
	return !metadata_value(metadata, key).empty();
}

string lowir_symbol_body(const string& name)
{
	string raw = name;
	if (!raw.empty() &&
	    (raw[0] == '@' || raw[0] == '%' || raw[0] == '$' || raw[0] == '^'))
		raw = raw.substr(1);
	string out;
	for (size_t i = 0; i < raw.size(); ++i)
	{
		const unsigned char c = static_cast<unsigned char>(raw[i]);
		out.push_back(isalnum(c) || raw[i] == '_' ? raw[i] : '_');
	}
	return out;
}

string function_label(const string& name)
{
	return "fn__" + lowir_symbol_body(name);
}

string global_label(const string& name)
{
	return "g__" + lowir_symbol_body(name);
}

}  // namespace lowir2cy86
