#include "pa11_internal.h"

#include <algorithm>

using namespace std;

namespace pa11 {
namespace {

bool contains_token(const vector<ETokenType>& tokens, ETokenType token)
{ return find(tokens.begin(), tokens.end(), token) != tokens.end(); }

size_t count_token(const vector<ETokenType>& tokens, ETokenType token)
{ return static_cast<size_t>(count(tokens.begin(), tokens.end(), token)); }

}  // namespace

bool is_cv_token(ETokenType type)
{
	return type == KW_CONST || type == KW_VOLATILE;
}

bool is_storage_or_function_specifier(ETokenType type)
{
	return type == KW_EXTERN || type == KW_STATIC ||
	       type == KW_THREAD_LOCAL || type == KW_INLINE ||
	       type == KW_VIRTUAL || type == KW_FRIEND ||
	       type == KW_MUTABLE || type == KW_REGISTER ||
	       type == KW_EXPLICIT;
}

bool is_builtin_type_token(ETokenType type)
{
	switch (type)
	{
	case KW_CHAR: case KW_CHAR16_T: case KW_CHAR32_T: case KW_WCHAR_T:
	case KW_BOOL: case KW_SHORT: case KW_INT: case KW_LONG:
	case KW_SIGNED: case KW_UNSIGNED: case KW_FLOAT: case KW_DOUBLE:
	case KW_VOID:
		return true;
	default:
		return false;
	}
}

EFundamentalType fundamental_from_specs(const vector<ETokenType>& specs)
{
	const bool sign = contains_token(specs, KW_SIGNED);
	const bool unsign = contains_token(specs, KW_UNSIGNED);
	const size_t longs = count_token(specs, KW_LONG);
	if (contains_token(specs, KW_CHAR))
		return unsign ? FT_UNSIGNED_CHAR : (sign ? FT_SIGNED_CHAR : FT_CHAR);
	if (contains_token(specs, KW_CHAR16_T)) return FT_CHAR16_T;
	if (contains_token(specs, KW_CHAR32_T)) return FT_CHAR32_T;
	if (contains_token(specs, KW_WCHAR_T)) return FT_WCHAR_T;
	if (contains_token(specs, KW_BOOL)) return FT_BOOL;
	if (contains_token(specs, KW_FLOAT)) return FT_FLOAT;
	if (contains_token(specs, KW_DOUBLE))
		return longs > 0 ? FT_LONG_DOUBLE : FT_DOUBLE;
	if (contains_token(specs, KW_VOID)) return FT_VOID;
	if (unsign && contains_token(specs, KW_SHORT))
		return FT_UNSIGNED_SHORT_INT;
	if (unsign && longs >= 2) return FT_UNSIGNED_LONG_LONG_INT;
	if (unsign && longs == 1) return FT_UNSIGNED_LONG_INT;
	if (unsign) return FT_UNSIGNED_INT;
	if (contains_token(specs, KW_SHORT)) return FT_SHORT_INT;
	if (longs >= 2) return FT_LONG_LONG_INT;
	if (longs == 1) return FT_LONG_INT;
	return FT_INT;
}

}  // namespace pa11
