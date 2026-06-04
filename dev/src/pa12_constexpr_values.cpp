#include "pa12_internal.h"

namespace pa12 {
namespace internal {
namespace {

bool constexpr_value_is_float_type(TypePtr type)
{
	TypePtr bare = pa11::strip_cv(type);
	return bare->kind == pa11::TypeKind::Fundamental &&
	       (bare->fundamental == FT_FLOAT ||
	        bare->fundamental == FT_DOUBLE ||
	        bare->fundamental == FT_LONG_DOUBLE);
}

bool constexpr_value_is_array_type(TypePtr type)
{
	return type.get() != NULL &&
	       pa11::strip_cv(type)->kind == pa11::TypeKind::Array;
}

bool starts_with(const string& text, const string& prefix)
{
	return text.compare(0, prefix.size(), prefix) == 0;
}

TypePtr constexpr_object_type(TypePtr type)
{
	if (type.get() == NULL)
		return type;
	if (type->kind == pa11::TypeKind::LValueReference ||
	    type->kind == pa11::TypeKind::RValueReference)
		return pa11::strip_cv(type->base);
	return pa11::strip_cv(type);
}

bool integral_type_is_unsigned(TypePtr type)
{
	TypePtr bare = constexpr_object_type(type);
	if (bare.get() == NULL)
		return false;
	if (bare->kind == pa11::TypeKind::Enum)
	{
		switch (bare->enum_underlying)
		{
		case FT_UNSIGNED_CHAR:
		case FT_UNSIGNED_SHORT_INT:
		case FT_UNSIGNED_INT:
		case FT_UNSIGNED_LONG_INT:
		case FT_UNSIGNED_LONG_LONG_INT:
			return true;
		default:
			return false;
		}
	}
	if (bare->kind != pa11::TypeKind::Fundamental)
		return false;
	switch (bare->fundamental)
	{
	case FT_BOOL:
	case FT_UNSIGNED_CHAR:
	case FT_UNSIGNED_SHORT_INT:
	case FT_UNSIGNED_INT:
	case FT_UNSIGNED_LONG_INT:
	case FT_UNSIGNED_LONG_LONG_INT:
	case FT_CHAR16_T:
	case FT_CHAR32_T:
		return true;
	default:
		return false;
	}
}

unsigned integral_type_bits(TypePtr type)
{
	uint64_t bytes = pa11::type_size(constexpr_object_type(type));
	return bytes >= 8 ? 64 : static_cast<unsigned>(bytes * 8);
}

uint64_t integral_mask(unsigned bits)
{
	return bits >= 64 ? ~uint64_t(0) : ((uint64_t(1) << bits) - 1);
}

uint64_t normalized_integral_value(unsigned bits, uint64_t value)
{
	return value & integral_mask(bits);
}

int64_t signed_integral_value(unsigned bits, uint64_t value)
{
	uint64_t normalized = normalized_integral_value(bits, value);
	if (bits >= 64)
		return static_cast<int64_t>(normalized);
	uint64_t sign = uint64_t(1) << (bits - 1);
	if ((normalized & sign) == 0)
		return static_cast<int64_t>(normalized);
	return static_cast<int64_t>(normalized | ~integral_mask(bits));
}

} // namespace

bool constexpr_zero_value_for_type(TypePtr type, ConstexprValue& out)
{
	if (type.get() == NULL || pa11::is_reference_type(type))
		return false;
	TypePtr bare = pa11::strip_cv(type);
	if (bare->kind == pa11::TypeKind::Pointer)
	{
		out = ConstexprValue::pointer(NULL, 0);
		return true;
	}
	if (bare->kind == pa11::TypeKind::Array)
	{
		out = ConstexprValue::object(bare);
		if (!bare->unknown_bound)
		{
			for (uint64_t i = 0; i < bare->bound; ++i)
			{
				ConstexprValue elem;
				if (!constexpr_zero_value_for_type(bare->base, elem))
					return false;
				out.elements.push_back(elem);
			}
		}
		return true;
	}
	if (bare->kind == pa11::TypeKind::Record)
	{
		pa11::layout_record_type(bare);
		out = ConstexprValue::object(bare);
		for (size_t i = 0; i < bare->fields.size(); ++i)
		{
			Binding* field = bare->fields[i];
			if (field == NULL || field->is_static_member)
				continue;
			ConstexprValue field_value;
			if (!constexpr_zero_value_for_type(field->type, field_value))
				return false;
			out.fields[field] = field_value;
		}
		return true;
	}
	if (constexpr_value_is_float_type(bare))
		out = ConstexprValue::floating(0);
	else
		out = ConstexprValue::integer(0);
	return true;
}

bool constexpr_integral_compare(ETokenType op,
                                TypePtr left_type,
                                const ConstexprValue& lhs,
                                const ConstexprValue& rhs,
                                ConstexprValue& out)
{
	if (lhs.is_float || rhs.is_float || lhs.is_pointer || rhs.is_pointer)
		return false;
	unsigned bits = integral_type_bits(left_type);
	if (bits == 0)
		return false;
	uint64_t l = normalized_integral_value(bits, lhs.int_value);
	uint64_t r = normalized_integral_value(bits, rhs.int_value);
	bool unsigned_compare = integral_type_is_unsigned(left_type);
	bool result = false;
	switch (op)
	{
	case OP_EQ: result = l == r; break;
	case OP_NE: result = l != r; break;
	case OP_LT:
		result = unsigned_compare ? l < r :
			signed_integral_value(bits, l) < signed_integral_value(bits, r);
		break;
	case OP_GT:
		result = unsigned_compare ? l > r :
			signed_integral_value(bits, l) > signed_integral_value(bits, r);
		break;
	case OP_LE:
		result = unsigned_compare ? l <= r :
			signed_integral_value(bits, l) <= signed_integral_value(bits, r);
		break;
	case OP_GE:
		result = unsigned_compare ? l >= r :
			signed_integral_value(bits, l) >= signed_integral_value(bits, r);
		break;
	default:
		return false;
	}
	out = ConstexprValue::integer(result ? 1 : 0);
	return true;
}

bool constexpr_string_literal_element(const Node& node,
                                      const ConstexprValue& index,
                                      ConstexprValue& out)
{
	if (!starts_with(node.line, "literal ") ||
	    !constexpr_value_is_array_type(node.type) ||
	    node.token_text.empty() ||
	    index.is_float ||
	    index.is_object ||
	    index.is_pointer)
		return false;
	StringLiteralInfo info;
	if (!AnalyzeStringLiteral(node.token_text, info))
		return false;
	uint64_t element = index.int_value;
	if (element >= info.elements)
		return false;
	uint64_t width = pa11::type_size(pa11::make_fundamental(info.type));
	uint64_t value = 0;
	for (uint64_t i = 0; i < width; ++i)
	{
		uint64_t byte_index = element * width + i;
		if (byte_index < info.bytes.size())
			value |= uint64_t(info.bytes[byte_index]) << (i * 8);
	}
	out = ConstexprValue::integer(value);
	return true;
}

} // namespace internal
} // namespace pa12
