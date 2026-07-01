#include "pa12_internal.h"

using namespace std;

namespace pa12 {
namespace internal {

bool template_name_is(const string& name, const string& unqualified)
{
	if (name == unqualified)
		return true;
	if (name.size() <= unqualified.size() + 2)
		return false;
	size_t offset = name.size() - unqualified.size();
	return name.compare(offset, unqualified.size(), unqualified) == 0 &&
	       offset >= 2 &&
	       name.compare(offset - 2, 2, "::") == 0;
}

bool constexpr_integral_or_bool_type(TypePtr type)
{
	TypePtr bare = type.get() != NULL ? pa11::strip_cv(type) : TypePtr();
	return bare.get() != NULL &&
	       (pa11::is_integral_or_bool_type(bare) ||
	        bare->kind == pa11::TypeKind::Enum);
}

bool constexpr_integral_unsigned(TypePtr type)
{
	TypePtr bare = type.get() != NULL
		? pa11::strip_cv(type) : TypePtr();
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

unsigned constexpr_integral_bits(TypePtr type)
{
	uint64_t bytes = pa11::type_size(pa11::strip_cv(type));
	return bytes >= 8 ? 64 : static_cast<unsigned>(bytes * 8);
}

uint64_t constexpr_integral_mask(unsigned bits)
{
	return bits >= 64 ? ~uint64_t(0) : ((uint64_t(1) << bits) - 1);
}

uint64_t constexpr_normalize_integral(TypePtr type, uint64_t value)
{
	return value & constexpr_integral_mask(constexpr_integral_bits(type));
}

int64_t constexpr_signed_integral(TypePtr type, uint64_t value)
{
	unsigned bits = constexpr_integral_bits(type);
	uint64_t normalized = value & constexpr_integral_mask(bits);
	if (bits >= 64)
		return static_cast<int64_t>(normalized);
	uint64_t sign = uint64_t(1) << (bits - 1);
	if ((normalized & sign) == 0)
		return static_cast<int64_t>(normalized);
	return static_cast<int64_t>(normalized | ~constexpr_integral_mask(bits));
}

uint64_t constexpr_convert_integral(TypePtr source,
                                    TypePtr target,
                                    uint64_t value)
{
	if (source.get() != NULL &&
	    target.get() != NULL &&
	    constexpr_integral_or_bool_type(source) &&
	    constexpr_integral_or_bool_type(target) &&
	    !constexpr_integral_unsigned(source) &&
	    constexpr_integral_bits(target) > constexpr_integral_bits(source))
		return constexpr_normalize_integral(
			target,
			static_cast<uint64_t>(
				constexpr_signed_integral(source, value)));
	return constexpr_normalize_integral(target, value);
}

}  // namespace internal
}  // namespace pa12
