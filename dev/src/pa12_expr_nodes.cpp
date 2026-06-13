#include "pa12_internal.h"
#include <algorithm>
#include <stdexcept>
using namespace std; namespace pa12 { namespace internal { namespace {
bool type_is_floating(TypePtr type) { TypePtr bare = pa11::strip_cv(type); return bare->kind == pa11::TypeKind::Fundamental &&
(bare->fundamental == FT_FLOAT || bare->fundamental == FT_DOUBLE || bare->fundamental == FT_LONG_DOUBLE); }
bool type_is_arithmetic(TypePtr type) { return pa11::is_integral_or_bool_type(type) || type_is_floating(type); }
bool type_is_pointer(TypePtr type) { return pa11::strip_cv(type)->kind == pa11::TypeKind::Pointer; }
bool string_ends_with(const string& text, const string& suffix)
{
	return text.size() >= suffix.size() &&
	       text.compare(text.size() - suffix.size(), suffix.size(), suffix) == 0;
}
bool binding_is_function_template_candidate(Binding* binding, const map<Binding*, TemplateDeclaration*>& placeholders,
const map<Binding*, vector<TemplateArgument> >& specializations) { if (binding == NULL) return false; Binding* aliased = binding->aliased_binding != NULL ? binding->aliased_binding : binding;
return placeholders.find(binding) != placeholders.end() || specializations.find(binding) != specializations.end() ||
placeholders.find(aliased) != placeholders.end() || specializations.find(aliased) != specializations.end(); }
bool binding_is_declared_copy_move_assignment_for_record(Binding* binding, TypePtr record,
const map<Binding*, TemplateDeclaration*>& placeholders, const map<Binding*, vector<TemplateArgument> >& specializations)
{ if (binding == NULL || binding->kind != BindingKind::Function || binding->name != "operator=" || binding->is_generated_copy_move_assignment ||
binding_is_function_template_candidate(binding, placeholders, specializations) || binding->type.get() == NULL ||
binding->type->kind != pa11::TypeKind::Function) return false; TypePtr param; if (binding->type->parameters.size() == 2)
param = binding->type->parameters[1]; else if (binding->type->parameters.size() == 1) param = binding->type->parameters[0]; else return false;
TypePtr param_object = pa11::is_reference_type(param) ? param->base : param; return pa11::same_type(pa11::strip_cv(param_object), pa11::strip_cv(record)); }
bool record_has_base_type(TypePtr source, TypePtr target) { if (source.get() == NULL || target.get() == NULL) return false; TypePtr wanted = pa11::strip_cv(target); TypePtr root = pa11::strip_cv(source); vector<TypePtr> pending = pa11::record_direct_bases(root); vector<TypePtr> seen;
while (!pending.empty()) { TypePtr cur = pa11::strip_cv(pending.back()); pending.pop_back(); if (cur.get() == NULL || cur->kind != pa11::TypeKind::Record) continue; bool already = false; for (size_t i = 0; i < seen.size(); ++i) if (pa11::same_type(seen[i], cur)) already = true; if (already) continue; seen.push_back(cur); if (pa11::same_type(cur, wanted)) return true; vector<TypePtr> bases = pa11::record_direct_bases(cur); pending.insert(pending.end(), bases.begin(), bases.end()); } return false; }
bool type_contains_template_parameter_name(TypePtr type, string& name) { if (type.get() == NULL) return false;
type = pa11::strip_cv(type); if (type->kind == pa11::TypeKind::TemplateParameter) { if (!pa11::is_deducible_template_parameter_type(type))
return false; name = type->name; return true; }
if (type->kind == pa11::TypeKind::Pointer || type->kind == pa11::TypeKind::LValueReference || type->kind == pa11::TypeKind::RValueReference || type->kind == pa11::TypeKind::Array)
return type_contains_template_parameter_name(type->base, name); if (type->kind == pa11::TypeKind::Function) { if (type_contains_template_parameter_name(type->base, name))
return true; for (size_t i = 0; i < type->parameters.size(); ++i) if (type_contains_template_parameter_name(type->parameters[i], name))
return true; } if (type->kind == pa11::TypeKind::MemberPointer) return type_contains_template_parameter_name(type->member_class,
name) || type_contains_template_parameter_name(type->base, name); return false; }
bool integral_type_is_unsigned(TypePtr type) { TypePtr bare = pa11::strip_cv(type); if (bare->kind == pa11::TypeKind::Enum)
{ switch (bare->enum_underlying) { case FT_UNSIGNED_CHAR:
case FT_UNSIGNED_SHORT_INT: case FT_UNSIGNED_INT: case FT_UNSIGNED_LONG_INT: case FT_UNSIGNED_LONG_LONG_INT: case FT_UNSIGNED_INT128:
return true; default: return false; }
} if (bare->kind != pa11::TypeKind::Fundamental) return false; switch (bare->fundamental)
{ case FT_BOOL: case FT_UNSIGNED_CHAR: case FT_UNSIGNED_SHORT_INT:
case FT_UNSIGNED_INT: case FT_UNSIGNED_LONG_INT: case FT_UNSIGNED_LONG_LONG_INT: case FT_UNSIGNED_INT128: case FT_CHAR16_T:
case FT_CHAR32_T: return true; default: return false;
} } unsigned integral_type_bits(TypePtr type) {
uint64_t bytes = pa11::type_size(pa11::strip_cv(type)); if (bytes >= 8) return 64; return static_cast<unsigned>(bytes * 8);
} uint64_t mask_for_bits(unsigned bits) { return bits >= 64 ? ~uint64_t(0) : ((uint64_t(1) << bits) - 1);
} uint64_t normalize_integral_value(TypePtr type, uint64_t value) { TypePtr bare = pa11::strip_cv(type);
if (!pa11::is_integral_or_bool_type(bare) && bare->kind != pa11::TypeKind::Enum) return value; return value & mask_for_bits(integral_type_bits(type));
} int64_t signed_integral_value(TypePtr type, uint64_t value) { unsigned bits = integral_type_bits(type);
uint64_t normalized = normalize_integral_value(type, value); if (bits >= 64) return static_cast<int64_t>(normalized); uint64_t sign = uint64_t(1) << (bits - 1);
if ((normalized & sign) == 0) return static_cast<int64_t>(normalized); return static_cast<int64_t>(normalized | ~mask_for_bits(bits)); }
bool constant_binary_value(ETokenType op, TypePtr left_type, uint64_t lhs, TypePtr right_type,
uint64_t rhs, TypePtr result_type, uint64_t& out) {
TypePtr common = result_type; if (op == OP_EQ || op == OP_NE || op == OP_LT || op == OP_GT || op == OP_LE || op == OP_GE || op == OP_LAND || op == OP_LOR) common = left_type;
if (pa11::type_size(pa11::strip_cv(common)) > 8 || pa11::type_size(pa11::strip_cv(result_type)) > 8) return false;
lhs = normalize_integral_value(common, lhs); rhs = normalize_integral_value(common, rhs); const bool unsigned_compare = integral_type_is_unsigned(common); switch (op)
{ case OP_PLUS: out = normalize_integral_value(result_type, lhs + rhs); return true; case OP_MINUS: out = normalize_integral_value(result_type, lhs - rhs); return true; case OP_STAR: out = normalize_integral_value(result_type, lhs * rhs); return true;
case OP_DIV: if (rhs == 0) return false; out = integral_type_is_unsigned(common) ? lhs / rhs
: static_cast<uint64_t>( signed_integral_value(common, lhs) / signed_integral_value(common, rhs)); out = normalize_integral_value(result_type, out);
return true; case OP_MOD: if (rhs == 0) return false; out = integral_type_is_unsigned(common)
? lhs % rhs : static_cast<uint64_t>( signed_integral_value(common, lhs) % signed_integral_value(common, rhs));
out = normalize_integral_value(result_type, out); return true; case OP_XOR: out = normalize_integral_value(result_type, lhs ^ rhs); return true; case OP_AMP: out = normalize_integral_value(result_type, lhs & rhs); return true;
case OP_BOR: out = normalize_integral_value(result_type, lhs | rhs); return true; case OP_LSHIFT: if (rhs >= 64) return false; out = normalize_integral_value(result_type, lhs << rhs);
return true; case OP_RSHIFT: if (rhs >= 64) return false; if (integral_type_is_unsigned(common))
out = lhs >> rhs; else out = static_cast<uint64_t>( signed_integral_value(common, lhs) >> rhs);
out = normalize_integral_value(result_type, out); return true; case OP_EQ: out = unsigned_compare
? (lhs == rhs ? 1 : 0) : (signed_integral_value(common, lhs) == signed_integral_value(common, rhs) ? 1 : 0); return true;
case OP_NE: out = unsigned_compare ? (lhs != rhs ? 1 : 0) : (signed_integral_value(common, lhs) !=
signed_integral_value(common, rhs) ? 1 : 0); return true; case OP_LT: out = unsigned_compare
? (lhs < rhs ? 1 : 0) : (signed_integral_value(common, lhs) < signed_integral_value(common, rhs) ? 1 : 0); return true;
case OP_GT: out = unsigned_compare ? (lhs > rhs ? 1 : 0) : (signed_integral_value(common, lhs) >
signed_integral_value(common, rhs) ? 1 : 0); return true; case OP_LE: out = unsigned_compare
? (lhs <= rhs ? 1 : 0) : (signed_integral_value(common, lhs) <= signed_integral_value(common, rhs) ? 1 : 0); return true;
case OP_GE: out = unsigned_compare ? (lhs >= rhs ? 1 : 0) : (signed_integral_value(common, lhs) >=
signed_integral_value(common, rhs) ? 1 : 0); return true; case OP_LAND: out = (lhs != 0 && rhs != 0) ? 1 : 0; return true; case OP_LOR: out = (lhs != 0 || rhs != 0) ? 1 : 0; return true;
case OP_COMMA: out = normalize_integral_value(result_type, rhs); return true; default: return false; }
} bool top_level_const(TypePtr type) { return type->kind == pa11::TypeKind::Cv &&
(type->cv & pa11::CV_CONST) != 0; } bool type_has_cv_flag(TypePtr type, unsigned flag) {
if (type->kind == pa11::TypeKind::Cv) return (type->cv & flag) != 0 || type_has_cv_flag(type->base, flag); if (type->kind == pa11::TypeKind::Array) return type_has_cv_flag(type->base, flag);
return false; } bool compound_assignment_rhs_viable(ETokenType op, TypePtr lhs, TypePtr rhs) {
TypePtr left = pa11::strip_cv(lhs); TypePtr right = pa11::strip_cv(rhs); if (op == OP_PLUSASS || op == OP_MINUSASS) {
if (left->kind == pa11::TypeKind::Pointer) return pa11::is_integral_or_bool_type(right); return type_is_arithmetic(left) && type_is_arithmetic(right); }
if (op == OP_STARASS || op == OP_DIVASS) return type_is_arithmetic(left) && type_is_arithmetic(right); if (op == OP_MODASS || op == OP_XORASS || op == OP_BANDASS || op == OP_BORASS || op == OP_LSHIFTASS || op == OP_RSHIFTASS)
return pa11::is_integral_or_bool_type(left) && pa11::is_integral_or_bool_type(right); return false; }
bool hosted_libc_math_builtin_core(const string& core)
{
	static const char* names[] = {
		"abs", "labs", "llabs", "free",
		"acos", "acosf", "acosl", "acosh", "acoshf", "acoshl",
		"asin", "asinf", "asinl", "asinh", "asinhf", "asinhl",
		"atan", "atanf", "atanl", "atan2", "atan2f", "atan2l",
		"atanh", "atanhf", "atanhl",
		"cbrt", "cbrtf", "cbrtl", "ceil", "ceilf", "ceill",
		"copysign", "copysignf", "copysignl",
		"cos", "cosf", "cosl", "cosh", "coshf", "coshl",
		"erf", "erff", "erfl", "erfc", "erfcf", "erfcl",
		"exp", "expf", "expl", "exp2", "exp2f", "exp2l",
		"expm1", "expm1f", "expm1l",
		"fabs", "fabsf", "fabsl", "fabsf128",
		"fdim", "fdimf", "fdiml", "floor", "floorf", "floorl",
		"fma", "fmaf", "fmal", "fmax", "fmaxf", "fmaxl",
		"fmin", "fminf", "fminl", "fmod", "fmodf", "fmodl",
		"fpclassify", "frexp", "frexpf", "frexpl",
		"hypot", "hypotf", "hypotl",
		"ilogb", "ilogbf", "ilogbl",
		"isfinite", "isgreater", "isgreaterequal", "isinf",
		"isless", "islessequal", "islessgreater", "isnan",
		"isnormal", "isunordered",
		"ldexp", "ldexpf", "ldexpl",
		"lgamma", "lgammaf", "lgammal",
		"llrint", "llrintf", "llrintl", "llround", "llroundf",
		"llroundl",
		"log", "logf", "logl", "log10", "log10f", "log10l",
		"log1p", "log1pf", "log1pl", "log2", "log2f", "log2l",
		"logb", "logbf", "logbl",
		"lrint", "lrintf", "lrintl", "lround", "lroundf",
		"lroundl",
		"modf", "modff", "modfl", "nearbyint", "nearbyintf",
		"nearbyintl",
		"nextafter", "nextafterf", "nextafterl",
		"nexttoward", "nexttowardf", "nexttowardl",
		"pow", "powf", "powl", "remainder", "remainderf",
		"remainderl", "remquo", "remquof", "remquol",
		"rint", "rintf", "rintl", "round", "roundf", "roundl",
		"scalbln", "scalblnf", "scalblnl",
		"scalbn", "scalbnf", "scalbnl", "signbit",
		"sin", "sinf", "sinl", "sinh", "sinhf", "sinhl",
		"sqrt", "sqrtf", "sqrtl", "tan", "tanf", "tanl",
		"tanh", "tanhf", "tanhl", "tgamma", "tgammaf",
		"tgammal", "trunc", "truncf", "truncl"
	};
	for (size_t i = 0; i < sizeof(names) / sizeof(names[0]); ++i)
		if (core == names[i])
			return true;
	return false;
}
bool hosted_libc_math_builtin_name(const string& name)
{
	return name.compare(0, 10, "__builtin_") == 0 &&
	       hosted_libc_math_builtin_core(name.substr(10));
}
TypePtr hosted_float_builtin_type(const string& core)
{
	if (string_ends_with(core, "f") && !string_ends_with(core, "f128"))
		return pa11::make_fundamental(FT_FLOAT);
	if (string_ends_with(core, "l") || string_ends_with(core, "f128"))
		return pa11::make_fundamental(FT_LONG_DOUBLE);
	return pa11::make_fundamental(FT_DOUBLE);
}
bool hosted_core_starts_with(const string& core, const string& prefix)
{
	return core.compare(0, prefix.size(), prefix) == 0;
}
void classify_hosted_libc_math_builtin(const string& name,
                                       vector<TypePtr>& params,
                                       TypePtr& result)
{
	string core = name.substr(10);
	TypePtr void_type = pa11::make_fundamental(FT_VOID);
	TypePtr void_ptr = pa11::make_pointer(void_type);
	TypePtr int_type = pa11::make_fundamental(FT_INT);
	TypePtr long_type = pa11::make_fundamental(FT_LONG_INT);
	TypePtr long_long_type = pa11::make_fundamental(FT_LONG_LONG_INT);
	if (core == "free")
	{
		params.push_back(void_ptr);
		result = void_type;
		return;
	}
	if (core == "abs" || core == "labs" || core == "llabs")
	{
		result = core == "abs" ? int_type :
		         core == "labs" ? long_type : long_long_type;
		params.push_back(result);
		return;
	}
	TypePtr real = hosted_float_builtin_type(core);
	if (hosted_core_starts_with(core, "llrint") ||
	    hosted_core_starts_with(core, "llround"))
		result = long_long_type;
	else if (hosted_core_starts_with(core, "lrint") ||
	         hosted_core_starts_with(core, "lround"))
		result = long_type;
	else if (hosted_core_starts_with(core, "ilogb") ||
	         core == "isfinite" || core == "isgreater" ||
	         core == "isgreaterequal" || core == "isinf" ||
	         core == "isless" || core == "islessequal" ||
	         core == "islessgreater" || core == "isnan" ||
	         core == "isnormal" || core == "isunordered" ||
	         core == "signbit" || core == "fpclassify")
		result = int_type;
	else
		result = real;
	if (core == "isgreater" || core == "isgreaterequal" ||
	    core == "isless" || core == "islessequal" ||
	    core == "islessgreater" || core == "isunordered")
	{
		params.push_back(pa11::make_fundamental(FT_DOUBLE));
		params.push_back(pa11::make_fundamental(FT_DOUBLE));
		return;
	}
	params.push_back(real);
	if (hosted_core_starts_with(core, "atan2") ||
	    hosted_core_starts_with(core, "copysign") ||
	    hosted_core_starts_with(core, "fdim") ||
	    hosted_core_starts_with(core, "fmax") ||
	    hosted_core_starts_with(core, "fmin") ||
	    hosted_core_starts_with(core, "fmod") ||
	    hosted_core_starts_with(core, "hypot") ||
	    hosted_core_starts_with(core, "nextafter") ||
	    hosted_core_starts_with(core, "nexttoward") ||
	    hosted_core_starts_with(core, "pow") ||
	    hosted_core_starts_with(core, "remainder"))
		params.push_back(real);
	else if (hosted_core_starts_with(core, "fma"))
	{
		params.push_back(real);
		params.push_back(real);
	}
	else if (hosted_core_starts_with(core, "ldexp") ||
	         hosted_core_starts_with(core, "scalbn"))
		params.push_back(int_type);
	else if (hosted_core_starts_with(core, "scalbln"))
		params.push_back(long_type);
	else if (hosted_core_starts_with(core, "frexp"))
		params.push_back(pa11::make_pointer(int_type));
	else if (hosted_core_starts_with(core, "modf"))
		params.push_back(pa11::make_pointer(real));
	else if (hosted_core_starts_with(core, "remquo"))
	{
		params.push_back(real);
		params.push_back(pa11::make_pointer(int_type));
	}
}
bool hosted_builtin_function_name(const string& name) {
	return name == "__builtin_strlen" || name == "__builtin_unreachable" ||
	       name == "__builtin_memcpy" || name == "__builtin_memmove" ||
	       name == "__builtin_memset" ||
	       name == "__builtin_strcmp" || name == "__builtin_memcmp" ||
	       name == "__builtin_memchr" || name == "__builtin_strchr" ||
	       name == "__builtin_bzero" ||
	       name == "__builtin_expect" ||
	       name == "__builtin_is_constant_evaluated" ||
	       name == "__builtin_addressof" ||
	       name == "__builtin_assume_aligned" ||
	       name == "__builtin_FILE" || name == "__builtin_FUNCTION" ||
	       name == "__builtin_LINE" || name == "__builtin_COLUMN" ||
	       name == "__builtin_inf" || name == "__builtin_inff" ||
	       name == "__builtin_infl" ||
	       name == "__builtin_huge_val" ||
	       name == "__builtin_huge_valf" ||
	       name == "__builtin_huge_vall" ||
	       name == "__builtin_nan" || name == "__builtin_nanf" ||
	       name == "__builtin_nanl" || name == "__builtin_nans" ||
	       name == "__builtin_nansf" || name == "__builtin_nansl" ||
	       name == "__builtin_isnan" ||
	       name == "__builtin_flt_rounds" ||
	       name == "__builtin_fpclassify" ||
	       name == "__builtin_prefetch" ||
	       name == "__builtin_operator_new" ||
	       name == "__builtin_operator_delete" ||
	       name == "__builtin_add_overflow" ||
	       name == "__builtin_sub_overflow" ||
	       name == "__builtin_mul_overflow" ||
	       name == "__builtin_invoke" ||
	       name == "__builtin_shuffle" ||
	       name == "__builtin_shufflevector" ||
	       name == "__builtin_vsnprintf" ||
	       name == "__builtin_alloca" || name == "__builtin_va_start" ||
	       name == "__builtin_va_end" || name == "__builtin_bswap16" ||
	       name == "__builtin_bswap32" || name == "__builtin_bswap64" ||
	       name == "__builtin_clz" || name == "__builtin_clzl" ||
	       name == "__builtin_clzll" || name == "__builtin_clzg" ||
	       name == "__builtin_ctz" || name == "__builtin_ctzl" ||
	       name == "__builtin_ctzll" || name == "__builtin_popcount" ||
	       name == "__builtin_popcountl" || name == "__builtin_popcountll" ||
	       name == "__builtin_popcountg" ||
	       name == "__builtin_complex" ||
	       name.compare(0, 15, "__builtin_ia32_") == 0 ||
	       name == "__atomic_load_n" || name == "__atomic_load" ||
	       name == "__atomic_store_n" || name == "__atomic_store" ||
	       name == "__atomic_exchange_n" ||
	       name == "__atomic_compare_exchange" ||
	       name == "__atomic_compare_exchange_n" ||
	       name == "__atomic_fetch_add" ||
	       name == "__atomic_fetch_sub" ||
	       name == "__atomic_fetch_and" ||
	       name == "__atomic_fetch_or" ||
	       name == "__atomic_fetch_xor" ||
	       name == "__atomic_add_fetch" ||
	       name == "__atomic_sub_fetch" ||
	       name == "__atomic_and_fetch" ||
	       name == "__atomic_or_fetch" ||
	       name == "__atomic_xor_fetch" ||
	       name == "__atomic_always_lock_free" ||
	       name == "__atomic_is_lock_free" ||
	       name == "__atomic_thread_fence" ||
	       name == "__atomic_signal_fence" ||
	       name == "__atomic_test_and_set" ||
	       name == "__atomic_clear" ||
	       name == "__sync_lock_test_and_set" ||
	       name == "__sync_lock_release" ||
	       name == "__c11_atomic_load" || name == "__c11_atomic_init" ||
	       name == "__c11_atomic_store" ||
	       name == "__c11_atomic_exchange" ||
	       name == "__c11_atomic_compare_exchange_strong" ||
	       name == "__c11_atomic_compare_exchange_weak" ||
	       name == "__c11_atomic_fetch_add" ||
	       name == "__c11_atomic_fetch_sub" ||
	       name == "__c11_atomic_fetch_and" ||
	       name == "__c11_atomic_fetch_or" ||
	       name == "__c11_atomic_fetch_xor" ||
	       name == "__c11_atomic_is_lock_free" ||
	       name == "__c11_atomic_thread_fence" ||
	       name == "__c11_atomic_signal_fence" ||
	       hosted_libc_math_builtin_name(name);
}
bool function_parameters_match(TypePtr function, const vector<TypePtr>& params) {
if (function.get() == NULL || function->kind != pa11::TypeKind::Function || function->parameters.size() != params.size()) return false;
for (size_t i = 0; i < params.size(); ++i) if (!pa11::same_type(function->parameters[i], params[i])) return false;
return true;
}
}  // namespace
Expr Parser::make_builtin_id_expr(const QualifiedName& name) { if ((name.name == "operatornew" || name.name == "operatornew[]" ||
name.name == "operatordelete" || name.name == "operatordelete[]") && (!name.qualified || name.qualifier == global_scope())) {
TypePtr void_type = pa11::make_fundamental(FT_VOID); TypePtr void_ptr = pa11::make_pointer(void_type);
vector<Binding*> bindings = lookup_unqualified_set(global_scope(), name.name, pa11::LOOKUP_FUNCTION); vector<vector<TypePtr> > wanted; TypePtr result = void_type;
if (name.name == "operatornew" || name.name == "operatornew[]") { vector<TypePtr> ordinary; ordinary.push_back(pa11::make_fundamental(FT_UNSIGNED_LONG_INT)); wanted.push_back(ordinary); vector<TypePtr> placement = ordinary; placement.push_back(void_ptr); wanted.push_back(placement); result = void_ptr; } else { vector<TypePtr> ordinary; ordinary.push_back(void_ptr); wanted.push_back(ordinary); vector<TypePtr> placement = ordinary; placement.push_back(void_ptr); wanted.push_back(placement); }
for (size_t wi = 0; wi < wanted.size(); ++wi) { bool have = false; for (size_t bi = 0; bi < bindings.size(); ++bi) if (function_parameters_match(bindings[bi]->type, wanted[wi])) have = true; if (!have) { Binding* added = add_value(global_scope(), BindingKind::Function, name.name, pa11::make_function(result, wanted[wi], false)); if (name.name == "operatordelete" || name.name == "operatordelete[]") added->unwind_no = true; bindings.push_back(added); } }
Binding* binding = bindings.empty() ? NULL : bindings.front(); Expr out; out.valid = binding != NULL; if (!out.valid) return out;
out.binding = binding; out.type = binding->type; out.category = ValueCategory::LValue; out.overloads = bindings;
string spelling = name.qualified ? name.spelling : binding->name; out.node = Node("id-expression lvalue " + pa11::describe_type(out.type) + " " + spelling); annotate_expr_node(out);
return out; } if (!name.qualified && name.name == "__builtin_constant_p") {
Expr out; out.type = pa11::make_function(pa11::make_fundamental(FT_INT), vector<TypePtr>(1, pa11::make_fundamental(FT_INT)), false);
out.category = ValueCategory::LValue; out.valid = true; out.builtin_constant_p = true; out.node = Node("id-expression lvalue " + pa11::describe_type(out.type) +
" __builtin_constant_p"); annotate_expr_node(out); return out; }
if (!name.qualified && name.name == "__CHAR_BIT__") { Expr out; out.type = pa11::make_fundamental(FT_INT);
out.category = ValueCategory::PRValue; out.valid = true; out.constant_expression = true; out.has_constant_value = true;
out.constant_value = 8; out.node = Node("literal prvalue int 8"); out.node.token_text = "8"; annotate_expr_node(out);
	return out; } if (!name.qualified && hosted_builtin_function_name(name.name)) {
	Binding* binding = pa11::lookup_unqualified(global_scope(), name.name, pa11::LOOKUP_FUNCTION); if (binding == NULL) {
	vector<TypePtr> params; TypePtr result = pa11::make_fundamental(FT_VOID); TypePtr void_ptr = pa11::make_pointer(pa11::make_fundamental(FT_VOID));
	TypePtr const_void_ptr = pa11::make_pointer(pa11::make_cv(pa11::make_fundamental(FT_VOID), pa11::CV_CONST)); TypePtr chr = pa11::make_fundamental(FT_CHAR); TypePtr const_chr = pa11::make_cv(chr, pa11::CV_CONST); TypePtr const_char_ptr = pa11::make_pointer(const_chr); TypePtr char_ptr = pa11::make_pointer(chr); if (name.name == "__builtin_strlen")
	{ TypePtr chr = pa11::make_cv(pa11::make_fundamental(FT_CHAR), pa11::CV_CONST); params.push_back(pa11::make_pointer(chr));
	result = pa11::make_fundamental(FT_UNSIGNED_LONG_INT); } else if (name.name == "__builtin_memcpy" || name.name == "__builtin_memmove")
	{ params.push_back(void_ptr); params.push_back(const_void_ptr); params.push_back(pa11::make_fundamental(FT_UNSIGNED_LONG_INT));
	result = void_ptr; } else if (name.name == "__builtin_memset")
	{ params.push_back(void_ptr); params.push_back(pa11::make_fundamental(FT_INT)); params.push_back(pa11::make_fundamental(FT_UNSIGNED_LONG_INT));
	result = void_ptr; } else if (name.name == "__builtin_strcmp")
	{ params.push_back(const_char_ptr); params.push_back(const_char_ptr); result = pa11::make_fundamental(FT_INT);
	} else if (name.name == "__builtin_memcmp")
	{ params.push_back(const_void_ptr); params.push_back(const_void_ptr); params.push_back(pa11::make_fundamental(FT_UNSIGNED_LONG_INT)); result = pa11::make_fundamental(FT_INT);
	} else if (name.name == "__builtin_memchr")
	{ params.push_back(const_void_ptr); params.push_back(pa11::make_fundamental(FT_INT)); params.push_back(pa11::make_fundamental(FT_UNSIGNED_LONG_INT)); result = void_ptr;
	} else if (name.name == "__builtin_strchr")
	{ params.push_back(const_char_ptr); params.push_back(pa11::make_fundamental(FT_INT)); result = char_ptr;
	} else if (name.name == "__builtin_bzero")
	{ params.push_back(void_ptr); params.push_back(pa11::make_fundamental(FT_UNSIGNED_LONG_INT)); result = pa11::make_fundamental(FT_VOID);
	} else if (name.name == "__builtin_addressof")
	{ result = void_ptr;
	} else if (name.name == "__builtin_assume_aligned")
	{ params.push_back(void_ptr); params.push_back(pa11::make_fundamental(FT_UNSIGNED_LONG_INT)); result = void_ptr;
	} else if (name.name == "__builtin_is_constant_evaluated")
	{ result = pa11::make_fundamental(FT_BOOL);
	} else if (name.name == "__builtin_FILE" || name.name == "__builtin_FUNCTION")
	{ TypePtr chr = pa11::make_cv(pa11::make_fundamental(FT_CHAR), pa11::CV_CONST); result = pa11::make_pointer(chr);
	} else if (name.name == "__builtin_LINE" || name.name == "__builtin_COLUMN")
	{ result = pa11::make_fundamental(FT_INT);
	} else if (name.name == "__builtin_inf" || name.name == "__builtin_huge_val" || name.name == "__builtin_nan" || name.name == "__builtin_nans")
	{ if (name.name == "__builtin_nan" || name.name == "__builtin_nans") params.push_back(const_char_ptr); result = pa11::make_fundamental(FT_DOUBLE);
	} else if (name.name == "__builtin_inff" || name.name == "__builtin_huge_valf" || name.name == "__builtin_nanf" || name.name == "__builtin_nansf")
	{ if (name.name == "__builtin_nanf" || name.name == "__builtin_nansf") params.push_back(const_char_ptr); result = pa11::make_fundamental(FT_FLOAT);
	} else if (name.name == "__builtin_infl" || name.name == "__builtin_huge_vall" || name.name == "__builtin_nansl")
	{ if (name.name == "__builtin_nansl") params.push_back(const_char_ptr); result = pa11::make_fundamental(FT_LONG_DOUBLE);
	} else if (name.name == "__builtin_nanl")
	{ TypePtr chr = pa11::make_cv(pa11::make_fundamental(FT_CHAR), pa11::CV_CONST); params.push_back(pa11::make_pointer(chr));
	result = pa11::make_fundamental(FT_LONG_DOUBLE); } else if (name.name == "__builtin_isnan")
	{ params.push_back(pa11::make_fundamental(FT_LONG_DOUBLE)); result = pa11::make_fundamental(FT_INT); } else if (name.name == "__builtin_alloca")
	{ params.push_back(pa11::make_fundamental(FT_UNSIGNED_LONG_INT)); result = void_ptr; } else if (name.name == "__builtin_va_start")
	{ params.push_back(void_ptr); result = pa11::make_fundamental(FT_VOID); } else if (name.name == "__builtin_va_end")
	{ params.push_back(void_ptr); result = pa11::make_fundamental(FT_VOID); } else if (name.name == "__builtin_bswap16")
	{ result = pa11::make_fundamental(FT_UNSIGNED_SHORT_INT); } else if (name.name == "__builtin_bswap32")
	{ result = pa11::make_fundamental(FT_UNSIGNED_INT); } else if (name.name == "__builtin_bswap64")
	{ result = pa11::make_fundamental(FT_UNSIGNED_LONG_LONG_INT); } else if (name.name == "__builtin_complex")
	{ result = pa11::make_fundamental(FT_LONG_DOUBLE); } else if (name.name == "__builtin_clz" || name.name == "__builtin_clzl" || name.name == "__builtin_clzll" || name.name == "__builtin_clzg" || name.name == "__builtin_ctz" || name.name == "__builtin_ctzl" || name.name == "__builtin_ctzll" || name.name == "__builtin_popcount" || name.name == "__builtin_popcountl" || name.name == "__builtin_popcountll" || name.name == "__builtin_popcountg")
	{ result = pa11::make_fundamental(FT_INT); } else if (name.name == "__builtin_flt_rounds" || name.name == "__builtin_fpclassify")
	{ result = pa11::make_fundamental(FT_INT); } else if (name.name == "__builtin_prefetch" || name.name == "__builtin_operator_delete")
	{ result = pa11::make_fundamental(FT_VOID); } else if (name.name == "__builtin_operator_new")
	{ params.push_back(pa11::make_fundamental(FT_UNSIGNED_LONG_INT)); result = void_ptr; } else if (name.name == "__builtin_add_overflow" || name.name == "__builtin_sub_overflow" || name.name == "__builtin_mul_overflow")
	{ result = pa11::make_fundamental(FT_BOOL); } else if (name.name.compare(0, 15, "__builtin_ia32_") == 0)
	{ result = pa11::make_fundamental(FT_LONG_LONG_INT); } else if (hosted_libc_math_builtin_name(name.name))
	{ classify_hosted_libc_math_builtin(name.name, params, result); } else if (name.name == "__builtin_shuffle" || name.name == "__builtin_shufflevector")
	{ result = pa11::make_fundamental(FT_LONG_LONG_INT); } else if (name.name == "__builtin_invoke")
	{ result = pa11::make_fundamental(FT_INT); } else if (name.name == "__builtin_vsnprintf")
	{ params.push_back(char_ptr); params.push_back(pa11::make_fundamental(FT_UNSIGNED_LONG_INT)); params.push_back(const_char_ptr); params.push_back(void_ptr); result = pa11::make_fundamental(FT_INT); } else if (name.name == "__atomic_always_lock_free" || name.name == "__atomic_is_lock_free" || name.name == "__atomic_test_and_set" || name.name == "__atomic_compare_exchange" || name.name == "__atomic_compare_exchange_n" || name.name == "__c11_atomic_is_lock_free" || name.name == "__c11_atomic_compare_exchange_strong" || name.name == "__c11_atomic_compare_exchange_weak")
	{ result = pa11::make_fundamental(FT_BOOL); } bool variadic_builtin = name.name == "__builtin_va_start" || name.name.compare(0, 5, "__c11") == 0 || name.name.compare(0, 15, "__builtin_ia32_") == 0 || name.name == "__builtin_shuffle" || name.name == "__builtin_shufflevector" || name.name == "__builtin_assume_aligned" || name.name == "__builtin_prefetch" || name.name == "__builtin_operator_new" || name.name == "__builtin_operator_delete" || name.name == "__builtin_add_overflow" || name.name == "__builtin_sub_overflow" || name.name == "__builtin_mul_overflow" || name.name == "__builtin_fpclassify" || name.name == "__builtin_invoke"; TypePtr fn = pa11::make_function(result, params, variadic_builtin); binding = add_value(global_scope(), BindingKind::Function, name.name, fn);
} Expr out; out.valid = true; out.binding = binding;
out.type = binding->type; out.category = ValueCategory::LValue; out.overloads.push_back(binding); out.node = Node("id-expression lvalue " +
pa11::describe_type(out.type) + " " + binding->name); annotate_expr_node(out); return out; }
return Expr(); } Expr Parser::make_binary_expr(ETokenType op, const string& text,
Expr lhs, Expr rhs) { Expr pack; if (make_binary_pack_expr(op, text, lhs, rhs, pack)) return pack; if ((op == OP_EQ || op == OP_NE) && lhs.node.is_typeid_expression && rhs.node.is_typeid_expression)
{ TypePtr left_object = pa11::strip_cv(expression_object_type(lhs.type)); string opname = operator_function_name(op, text);
if (left_object->kind != pa11::TypeKind::Record || left_object->scope == NULL || lookup_qualified_set(left_object->scope, opname, pa11::LOOKUP_FUNCTION).empty())
throw runtime_error("typeid comparison requires declared std::type_info operator");
Expr out; out.type = pa11::make_fundamental(FT_BOOL); out.category = ValueCategory::PRValue; out.valid = true;
out.node = Node("binary-expression prvalue bool " + op_leaf(op, text)); add_child(out.node, lhs.node); add_child(out.node, rhs.node);
out.node.has_op = true; out.node.op = op; out.node.token_text = text; annotate_expr_node(out); return out; }
string delayed_member_pointer_error;
if (op == OP_DOTSTAR || op == OP_ARROWSTAR) {
	TypePtr rhs_type = pa11::strip_cv(expression_object_type(rhs.type));
	bool use_builtin_member_pointer = true;
	if (rhs_type->kind != pa11::TypeKind::MemberPointer)
	{
		if (op == OP_DOTSTAR)
			throw runtime_error("right operand is not member pointer");
		delayed_member_pointer_error = "right operand is not member pointer";
		use_builtin_member_pointer = false;
	}
	TypePtr lhs_object = expression_object_type(lhs.type);
	TypePtr object_record = pa11::strip_cv(lhs_object);
	if (use_builtin_member_pointer && op == OP_ARROWSTAR) {
		if (object_record->kind != pa11::TypeKind::Pointer)
		{
			delayed_member_pointer_error = "left operand is not object pointer";
			use_builtin_member_pointer = false;
		}
		else
			object_record = pa11::strip_cv(object_record->base);
	}
	if (use_builtin_member_pointer) {
		TypePtr member_class = pa11::strip_cv(rhs_type->member_class);
		TypePtr member_type = rhs_type->base;
		bool dependent_member_pointer =
			type_is_template_dependent(object_record) ||
			type_is_template_dependent(member_class) ||
			type_is_template_dependent(member_type);
		if (object_record->kind != pa11::TypeKind::Record &&
		    !dependent_member_pointer)
			throw runtime_error("member pointer object is not record");
		if (!pa11::same_type(object_record, member_class) &&
		    !dependent_member_pointer &&
		    record_base_distance(object_record, member_class) >= 1000000)
			throw runtime_error("member pointer object conversion");
		TypePtr bare_member = pa11::strip_cv(member_type);
		Expr out;
		out.valid = true;
		if (bare_member->kind == pa11::TypeKind::Function) {
			vector<TypePtr> params;
			TypePtr this_object = member_class;
			if (member_type->cv != pa11::CV_NONE)
				this_object = pa11::make_cv(this_object, member_type->cv);
			params.push_back(pa11::make_pointer(this_object));
			for (size_t i = 0; i < member_type->parameters.size(); ++i)
				params.push_back(member_type->parameters[i]);
			TypePtr fn = pa11::make_function(member_type->base,
			                                 params,
			                                 member_type->variadic);
			out.type = pa11::make_pointer(fn);
			out.category = ValueCategory::PRValue;
			out.node = Node("member-pointer-function-expression prvalue " +
			                pa11::describe_type(out.type) + " " +
			                op_leaf(op, text));
		} else {
			if (op == OP_DOTSTAR && pa11::type_has_const(lhs_object))
				member_type = pa11::make_cv(member_type, pa11::CV_CONST);
			else if (op == OP_ARROWSTAR &&
			         pa11::strip_cv(lhs_object)->kind == pa11::TypeKind::Pointer &&
			         pa11::type_has_const(pa11::strip_cv(lhs_object)->base))
				member_type = pa11::make_cv(member_type, pa11::CV_CONST);
			out.type = member_type;
			out.category = ValueCategory::LValue;
			out.node = Node("member-pointer-expression lvalue " +
			                pa11::describe_type(out.type) + " " +
			                op_leaf(op, text));
		}
		add_child(out.node, lhs.node);
		add_child(out.node, rhs.node);
		out.node.has_op = true;
		out.node.op = op;
		out.node.token_text = text;
		annotate_expr_node(out);
		return out;
	}
}
if (op == OP_EQ || op == OP_NE) {
	TypePtr lhs_type = pa11::strip_cv(expression_object_type(lhs.type));
	TypePtr rhs_type = pa11::strip_cv(expression_object_type(rhs.type));
	bool lhs_member_pointer = lhs_type->kind == pa11::TypeKind::MemberPointer;
	bool rhs_member_pointer = rhs_type->kind == pa11::TypeKind::MemberPointer;
	bool lhs_null = lhs.null_pointer_constant ||
		(lhs_type->kind == pa11::TypeKind::Fundamental &&
		 lhs_type->fundamental == FT_NULLPTR_T);
	bool rhs_null = rhs.null_pointer_constant ||
		(rhs_type->kind == pa11::TypeKind::Fundamental &&
		 rhs_type->fundamental == FT_NULLPTR_T);
	if (lhs_member_pointer || rhs_member_pointer) {
		TypePtr target;
		if (lhs_member_pointer && rhs_member_pointer)
			target = lhs.type;
		else if (lhs_member_pointer && rhs_null)
			target = lhs.type;
		else if (rhs_member_pointer && lhs_null)
			target = rhs.type;
		else
			throw runtime_error("invalid member pointer comparison");
		Conversion left = convert_to(lhs, target);
		Conversion right = convert_to(rhs, target);
		if (!left.viable || !right.viable) {
			if (!(lhs_member_pointer && rhs_member_pointer))
				throw runtime_error("invalid member pointer comparison");
			target = rhs.type;
			left = convert_to(lhs, target);
			right = convert_to(rhs, target);
		}
		if (!left.viable || !right.viable)
			throw runtime_error("invalid member pointer comparison");
		Expr out;
		out.type = pa11::make_fundamental(FT_BOOL);
		out.category = ValueCategory::PRValue;
		out.valid = true;
		out.constant_expression =
			left.expr.constant_expression && right.expr.constant_expression;
		out.node = Node("binary-expression prvalue bool " + op_leaf(op, text));
		add_child(out.node, left.expr.node);
		add_child(out.node, right.expr.node);
		out.node.has_op = true;
		out.node.op = op;
		out.node.token_text = text;
		annotate_expr_node(out);
		return out;
	}
}
vector<Binding*> candidates = binary_operator_candidates(op, text, lhs, rhs); Expr builtin_converted; bool have_builtin_converted = make_builtin_converted_binary_expr(op, text, lhs, rhs, builtin_converted); TypePtr left_object = pa11::strip_cv(expression_object_type(lhs.type)); TypePtr right_object = pa11::strip_cv(expression_object_type(rhs.type));
bool enum_operand = left_object->kind == pa11::TypeKind::Enum || right_object->kind == pa11::TypeKind::Enum; bool enum_integral_mix = (left_object->kind == pa11::TypeKind::Enum && right_object->kind != pa11::TypeKind::Enum && pa11::is_integral_or_bool_type(right_object)) || (right_object->kind == pa11::TypeKind::Enum && left_object->kind != pa11::TypeKind::Enum && pa11::is_integral_or_bool_type(left_object)); if (have_builtin_converted && left_object->kind != pa11::TypeKind::Record && right_object->kind != pa11::TypeKind::Record) return builtin_converted; if (left_object->kind != pa11::TypeKind::Record && right_object->kind != pa11::TypeKind::Record && (!enum_operand || enum_integral_mix)) candidates.clear(); bool candidate_accepts_operands = false;
for (size_t i = 0; i < candidates.size(); ++i) if (function_template_placeholders_.find(candidates[i]) != function_template_placeholders_.end() || binary_candidate_accepts_operands(candidates[i], lhs, rhs)) candidate_accepts_operands = true; if (have_builtin_converted && !candidate_accepts_operands) return builtin_converted; if (!candidates.empty()) { Expr callee; callee.valid = true; callee.binding = candidates[0]; callee.type = candidates[0]->type; callee.category = ValueCategory::LValue; callee.overloads = candidates; callee.node = Node("id-expression lvalue " + pa11::describe_type(callee.type) + " " + candidates[0]->name); annotate_expr_node(callee); vector<Expr> args; args.push_back(lhs); args.push_back(rhs); try { return make_call_expr(callee, args); } catch (const runtime_error& err) { if (string(err.what()).compare(0, 28, "cannot resolve call overload") != 0) throw; } }
TypePtr left_record = pa11::strip_cv(expression_object_type(lhs.type)); if (left_record->kind == pa11::TypeKind::Record && left_record->scope != NULL) { string opname = operator_function_name(op, text); vector<Binding*> members = lookup_qualified_set(left_record->scope, opname, pa11::LOOKUP_FUNCTION); if (!members.empty()) { Expr callee = make_member_expr(lhs, opname, "."); vector<Expr> args; args.push_back(rhs); return make_call_expr(callee, args); } } if (have_builtin_converted) return builtin_converted; if (!delayed_member_pointer_error.empty()) throw runtime_error(delayed_member_pointer_error); if (op == OP_LAND || op == OP_LOR) { ++explicit_conversion_context_; Conversion left_bool; Conversion right_bool; try { left_bool = convert_to(lhs, pa11::make_fundamental(FT_BOOL)); right_bool = convert_to(rhs, pa11::make_fundamental(FT_BOOL)); } catch (...) { --explicit_conversion_context_; throw; } --explicit_conversion_context_; if (!left_bool.viable || !right_bool.viable) throw runtime_error("invalid logical conversion"); lhs = left_bool.expr; rhs = right_bool.expr; } else { static const EFundamentalType targets[] = { FT_INT, FT_UNSIGNED_INT, FT_LONG_INT, FT_UNSIGNED_LONG_INT, FT_LONG_LONG_INT, FT_UNSIGNED_LONG_LONG_INT, FT_INT128, FT_UNSIGNED_INT128, FT_SHORT_INT, FT_UNSIGNED_SHORT_INT, FT_CHAR, FT_SIGNED_CHAR, FT_UNSIGNED_CHAR, FT_BOOL, FT_FLOAT, FT_DOUBLE, FT_LONG_DOUBLE }; if (pa11::strip_cv(expression_object_type(lhs.type))->kind == pa11::TypeKind::Record) { for (size_t i = 0; i < sizeof(targets) / sizeof(targets[0]); ++i) { Conversion conv; try { conv = convert_to(lhs, pa11::make_fundamental(targets[i])); } catch (const runtime_error&) { continue; } if (conv.viable) { lhs = conv.expr; break; } } } if (pa11::strip_cv(expression_object_type(rhs.type))->kind == pa11::TypeKind::Record) { for (size_t i = 0; i < sizeof(targets) / sizeof(targets[0]); ++i) { Conversion conv; try { conv = convert_to(rhs, pa11::make_fundamental(targets[i])); } catch (const runtime_error&) { continue; } if (conv.viable) { rhs = conv.expr; break; } } } } TypePtr arithmetic_type = usual_arithmetic_type(lhs.type, rhs.type); TypePtr type = arithmetic_type;
if (op == OP_EQ || op == OP_NE || op == OP_LT || op == OP_GT || op == OP_LE || op == OP_GE || op == OP_LAND || op == OP_LOR) type = pa11::make_fundamental(FT_BOOL); else if ((op == OP_PLUS || op == OP_MINUS) && is_pointer_arithmetic(lhs, rhs)) type = pointer_arithmetic_type(op, lhs, rhs); else if (op == OP_MINUS && is_pointer_difference(lhs, rhs)) type = pa11::make_fundamental(FT_LONG_INT); else if (op == OP_LSHIFT || op == OP_RSHIFT) type = usual_arithmetic_type(lhs.type, lhs.type); else if (op == OP_COMMA) type = rhs.type; Expr out; out.type = type; out.category = op == OP_COMMA ? rhs.category : ValueCategory::PRValue; out.valid = true; out.constant_expression = lhs.constant_expression && rhs.constant_expression; if (lhs.has_constant_value && rhs.has_constant_value)
{ uint64_t value = 0; if (constant_binary_value(op, arithmetic_type, lhs.constant_value, arithmetic_type, rhs.constant_value, type, value)) { out.has_constant_value = true; out.constant_value = value; out.null_pointer_constant = out.constant_value == 0 && pa11::is_integral_or_bool_type(out.type); } } const Expr* dependent_operand = NULL; if (!lhs.dependent_value_name.empty() && parameter_pack_expansion_name(lhs.dependent_value_name)) dependent_operand = &lhs; else if (!rhs.dependent_value_name.empty() && parameter_pack_expansion_name(rhs.dependent_value_name)) dependent_operand = &rhs; else if (!lhs.dependent_value_name.empty()) dependent_operand = &lhs; else if (!rhs.dependent_value_name.empty()) dependent_operand = &rhs; if (dependent_operand != NULL) {
out.dependent_value_name = dependent_operand->dependent_value_name; out.dependent_value_owner_template_name = dependent_operand->dependent_value_owner_template_name; out.dependent_value_member_name = dependent_operand->dependent_value_member_name; out.dependent_value_owner_template_arguments = dependent_operand->dependent_value_owner_template_arguments; out.dependent_value_negated = dependent_operand->dependent_value_negated; } out.node = Node("binary-expression prvalue " + pa11::describe_type(type) + " " + op_leaf(op, text)); add_child(out.node, lhs.node); add_child(out.node, rhs.node); out.node.has_op = true; out.node.op = op; out.node.token_text = text; annotate_expr_node(out); return out; }
bool Parser::binary_candidate_accepts_operands(Binding* fn, const Expr& lhs, const Expr& rhs) const {
if (fn == NULL || fn->type->kind != pa11::TypeKind::Function || fn->type->parameters.size() != 2) return false;
const Expr* args[2] = {&lhs, &rhs}; for (size_t i = 0; i < 2; ++i) { TypePtr param = expression_object_type(fn->type->parameters[i]);
TypePtr arg = expression_object_type(args[i]->type); TypePtr p = pa11::strip_cv(param); TypePtr a = pa11::strip_cv(arg); if (pa11::same_type(p, a))
continue; if (a->kind == pa11::TypeKind::Record) return false; if (scalar_conversion_rank(arg, param) < 1000000)
continue; if (pointer_conversion_viable(arg, param)) continue; return false;
} return true; } bool Parser::make_builtin_converted_binary_expr(ETokenType op,
const string& text, const Expr& lhs, const Expr& rhs, Expr& out)
{ if (op != OP_EQ && op != OP_NE && op != OP_LT && op != OP_GT && op != OP_LE && op != OP_GE) return false;
const Expr* record_side = NULL; const Expr* other_side = NULL; bool record_on_left = false; TypePtr left = pa11::strip_cv(expression_object_type(lhs.type));
TypePtr right = pa11::strip_cv(expression_object_type(rhs.type)); if (left->kind == pa11::TypeKind::Record) { record_side = &lhs;
other_side = &rhs; record_on_left = true; } else if (right->kind == pa11::TypeKind::Record)
{ record_side = &rhs; other_side = &lhs; record_on_left = false;
} else return false; TypePtr record = pa11::strip_cv(expression_object_type(record_side->type));
if (record->scope == NULL) return false; for (map<string, vector<Binding*> >::const_iterator it = record->scope->members.begin();
it != record->scope->members.end(); ++it) { if (it->first.compare(0, 9, "operator ") != 0)
continue; for (size_t i = 0; i < it->second.size(); ++i) { Binding* opfn = it->second[i];
if (opfn->kind != BindingKind::Function || opfn->type->kind != pa11::TypeKind::Function || opfn->type->parameters.size() != 1) continue;
TypePtr target = lvalue_to_rvalue_type(opfn->type->base); TypePtr bare_target = pa11::strip_cv(target); if (bare_target->kind == pa11::TypeKind::Record || pa11::is_void_type(bare_target))
continue; TypePtr this_object = opfn->type->parameters.empty() ? TypePtr() : pa11::strip_cv(opfn->type->parameters[0]);
if (this_object.get() != NULL && this_object->kind == pa11::TypeKind::Pointer) this_object = this_object->base; if (this_object.get() != NULL &&
!type_has_cv_flag(expression_object_type(record_side->type), pa11::CV_VOLATILE) && type_has_cv_flag(this_object, pa11::CV_VOLATILE)) continue;
try { Expr callee; callee.valid = true;
callee.binding = opfn; callee.type = opfn->type; callee.category = ValueCategory::LValue; callee.overloads.push_back(opfn);
callee.node = Node("member-expression lvalue " + pa11::describe_type(callee.type) + " OP_DOT:" + opfn->name); add_child(callee.node, record_side->node);
callee.node.binding = opfn; callee.node.has_op = true; callee.node.op = OP_DOT; callee.node.token_text = opfn->name;
annotate_expr_node(callee); Expr converted_record = make_call_expr(callee, vector<Expr>()); Conversion converted_other = convert_to(*other_side, target); if (!converted_other.viable)
continue; Expr left_expr = record_on_left ? converted_record : converted_other.expr; Expr right_expr = record_on_left
? converted_other.expr : converted_record; out.type = pa11::make_fundamental(FT_BOOL); out.category = ValueCategory::PRValue; out.valid = true;
out.node = Node("binary-expression prvalue bool " + op_leaf(op, text)); add_child(out.node, left_expr.node); add_child(out.node, right_expr.node);
out.node.has_op = true; out.node.op = op; out.node.token_text = text; annotate_expr_node(out);
return true; } catch (const runtime_error&) {
throw; } } }
return false; } void Parser::collect_associated_hidden_friends(TypePtr type, const string& name,
set<Scope*>& seen, vector<Binding*>& out) const { if (type.get() == NULL)
return; TypePtr object = expression_object_type(type); TypePtr bare = pa11::strip_cv(object); if (bare->kind == pa11::TypeKind::Pointer ||
bare->kind == pa11::TypeKind::Array) { collect_associated_hidden_friends(bare->base, name, seen, out); return;
} if (bare->kind != pa11::TypeKind::Record || bare->scope == NULL) return; if (!seen.insert(bare->scope).second)
return; map<Scope*, vector<Binding*> >::const_iterator found = class_friend_functions_.find(bare->scope); if (found != class_friend_functions_.end())
{ for (size_t i = 0; i < found->second.size(); ++i) { Binding* binding = found->second[i];
if (!binding->is_hidden_friend) continue; if (binding->name != name) continue; if (find(out.begin(), out.end(), binding) == out.end()) out.push_back(binding);
} } vector<TypePtr> direct_bases = pa11::record_direct_bases(bare);
for (size_t b = 0; b < direct_bases.size(); ++b) { TypePtr direct_base = direct_bases[b].get() != NULL ? pa11::strip_cv(direct_bases[b]) : TypePtr();
if (direct_base.get() != NULL && direct_base->kind == pa11::TypeKind::Record) collect_associated_hidden_friends(direct_base, name, seen, out); } map<const void*, vector<TemplateArgument> >::const_iterator args =
record_template_arguments_.find(bare.get()); if (args != record_template_arguments_.end()) for (size_t i = 0; i < args->second.size(); ++i) {
vector<TemplateArgument> pending; pending.push_back(args->second[i]); while (!pending.empty()) {
TemplateArgument arg = pending.back(); pending.pop_back(); if (arg.kind == TemplateArgumentKind::Type) collect_associated_hidden_friends(arg.type,
name, seen, out); else if (arg.kind == TemplateArgumentKind::Value)
collect_associated_hidden_friends(arg.type, name, seen, out);
else if (arg.kind == TemplateArgumentKind::Template) ; else for (size_t p = 0; p < arg.pack.size(); ++p)
pending.push_back(arg.pack[p]); } } }
void Parser::collect_associated_namespace_functions(TypePtr type, const string& name, set<Scope*>& seen, vector<Binding*>& out)
{ if (type.get() == NULL) return; TypePtr object = expression_object_type(type);
TypePtr bare = pa11::strip_cv(object); if (bare->kind == pa11::TypeKind::Pointer || bare->kind == pa11::TypeKind::Array) {
collect_associated_namespace_functions(bare->base, name, seen, out); return; } if (bare->kind == pa11::TypeKind::Enum)
{ map<const void*, Scope*>::const_iterator owner = enum_owner_scopes_.find(bare.get()); if (owner == enum_owner_scopes_.end())
	return; for (Scope* scope = owner->second; scope != NULL; scope = scope->parent) { if (scope->kind != ScopeKind::Namespace)
	continue; if (!seen.insert(scope).second) break; bool inline_namespace = scope->is_inline_namespace; vector<Binding*> found =
	lookup_qualified_set(scope, name, pa11::LOOKUP_FUNCTION); QualifiedName template_name; template_name.qualifier = scope; template_name.name = name; template_name.qualified = true; vector<TemplateDeclaration*> templates = find_function_templates(template_name); for (size_t ti = 0; ti < templates.size(); ++ti) if (templates[ti]->placeholder != NULL && find(found.begin(), found.end(), templates[ti]->placeholder) == found.end()) found.push_back(templates[ti]->placeholder); for (size_t i = 0; i < found.size(); ++i) if (find(out.begin(), out.end(), found[i]) == out.end()) out.push_back(found[i]);
	if (!inline_namespace) break; } return; }
if (bare->kind != pa11::TypeKind::Record) return; Scope* owner_scope = NULL; if (bare->scope != NULL) { if (!seen.insert(bare->scope).second) return;
owner_scope = bare->scope->parent; } else { map<const void*, Scope*>::const_iterator owner = record_owner_scopes_.find(bare.get());
if (owner == record_owner_scopes_.end()) return; owner_scope = owner->second; }
	for (Scope* scope = owner_scope; scope != NULL; scope = scope->parent) { if (scope->kind != ScopeKind::Namespace) continue;
	if (!seen.insert(scope).second) break; bool inline_namespace = scope->is_inline_namespace; vector<Binding*> found = lookup_qualified_set(scope, name, pa11::LOOKUP_FUNCTION);
		QualifiedName template_name; template_name.qualifier = scope; template_name.name = name; template_name.qualified = true; vector<TemplateDeclaration*> templates = find_function_templates(template_name); for (size_t ti = 0; ti < templates.size(); ++ti) if (templates[ti]->placeholder != NULL && find(found.begin(), found.end(), templates[ti]->placeholder) == found.end()) found.push_back(templates[ti]->placeholder);
	for (size_t i = 0; i < found.size(); ++i) if (find(out.begin(), out.end(), found[i]) == out.end()) out.push_back(found[i]); if (!inline_namespace) break;
} if (bare->scope == NULL) return; vector<TypePtr> direct_bases = pa11::record_direct_bases(bare); for (size_t b = 0; b < direct_bases.size(); ++b) { TypePtr direct_base = direct_bases[b].get() != NULL ? pa11::strip_cv(direct_bases[b]) : TypePtr(); if (direct_base.get() != NULL &&
direct_base->kind == pa11::TypeKind::Record) collect_associated_namespace_functions(direct_base, name, seen, out); } map<const void*, vector<TemplateArgument> >::const_iterator args = record_template_arguments_.find(bare.get());
if (args != record_template_arguments_.end()) for (size_t i = 0; i < args->second.size(); ++i) { vector<TemplateArgument> pending;
pending.push_back(args->second[i]); while (!pending.empty()) { TemplateArgument arg = pending.back();
pending.pop_back(); if (arg.kind == TemplateArgumentKind::Type) collect_associated_namespace_functions(arg.type, name,
seen, out); else if (arg.kind == TemplateArgumentKind::Value) collect_associated_namespace_functions(arg.type,
name, seen, out); else if (arg.kind == TemplateArgumentKind::Template)
{ TemplateDeclaration* declaration = arg.template_declaration; for (Scope* scope = declaration != NULL
	? declaration->owner : NULL; scope != NULL; scope = scope->parent) {
	if (scope->kind != ScopeKind::Namespace) continue; if (!seen.insert(scope).second) break; bool inline_namespace = scope->is_inline_namespace;
	vector<Binding*> found = lookup_qualified_set(scope, name, pa11::LOOKUP_FUNCTION);
	for (size_t f = 0; f < found.size(); ++f) if (find(out.begin(), out.end(), found[f]) == out.end())
	out.push_back(found[f]); if (!inline_namespace) break; } }
else for (size_t p = 0; p < arg.pack.size(); ++p) pending.push_back(arg.pack[p]); }
} } vector<Binding*> Parser::binary_operator_candidates(ETokenType op, const string& text,
const Expr& lhs, const Expr& rhs) { TypePtr left = pa11::strip_cv(expression_object_type(lhs.type));
TypePtr right = pa11::strip_cv(expression_object_type(rhs.type)); bool overload_operand = left->kind == pa11::TypeKind::Record || right->kind == pa11::TypeKind::Record ||
left->kind == pa11::TypeKind::Enum || right->kind == pa11::TypeKind::Enum; if (!overload_operand) return vector<Binding*>();
string name = operator_function_name(op, text); vector<Binding*> out = lookup_unqualified_set(current_scope(), name, pa11::LOOKUP_FUNCTION); for (size_t i = 0; i < out.size();)
{ if (out[i]->owner != NULL && out[i]->owner->kind == ScopeKind::Class && !out[i]->is_static_member)
out.erase(out.begin() + i); else ++i; }
set<Scope*> seen; collect_associated_hidden_friends(lhs.type, name, seen, out); collect_associated_hidden_friends(rhs.type, name, seen, out); set<Scope*> namespaces;
collect_associated_namespace_functions(lhs.type, name, namespaces, out); collect_associated_namespace_functions(rhs.type, name, namespaces, out); return out; }
Expr Parser::make_overloaded_compound_assignment_expr(ETokenType op, const string& text, Expr lhs, Expr rhs,
TypePtr lhs_bare) { vector<Binding*> candidates = binary_operator_candidates(op, text, lhs, rhs); if (!candidates.empty())
{ Expr callee; callee.valid = true; callee.binding = candidates[0];
callee.type = candidates[0]->type; callee.category = ValueCategory::LValue; callee.overloads = candidates; callee.node = Node("id-expression lvalue " +
pa11::describe_type(callee.type) + " " + candidates[0]->name); annotate_expr_node(callee); vector<Expr> args;
args.push_back(lhs); args.push_back(rhs); try {
return make_call_expr(callee, args); } catch (const runtime_error& err) {
if (string(err.what()).compare(0, 28, "cannot resolve call overload") != 0) throw; }
} if (lhs_bare->kind != pa11::TypeKind::Record || lhs_bare->scope == NULL) return Expr(); string opname = operator_function_name(op, text);
vector<Binding*> members = lookup_qualified_set(lhs_bare->scope, opname, pa11::LOOKUP_FUNCTION); if (members.empty()) return Expr();
Expr callee = make_member_expr(lhs, opname, "."); vector<Expr> args; args.push_back(rhs); return make_call_expr(callee, args);
} Expr Parser::make_record_assignment_expr(Expr lhs, Expr rhs, TypePtr lhs_bare) { bool move_assign = rhs.category != ValueCategory::LValue;
if (rhs.braced_init_list && rhs.type.get() == NULL) { if (!type_is_template_dependent(lhs_bare)) instantiate_member_function_templates(lhs_bare);
vector<Binding*> members = lookup_qualified_set(lhs_bare->scope, "operator=", pa11::LOOKUP_FUNCTION); vector<Binding*> declared_members; for (size_t i = 0; i < members.size(); ++i)
if (!members[i]->is_generated_copy_move_assignment) declared_members.push_back(members[i]); if (!declared_members.empty()) {
Expr callee = make_member_expr(lhs, "operator=", "."); callee.binding = declared_members[0]; callee.type = declared_members[0]->type; callee.overloads = declared_members;
callee.node.binding = declared_members[0]; callee.node.type = declared_members[0]->type; vector<Expr> args; args.push_back(rhs);
try { return make_call_expr(callee, args); }
catch (const runtime_error& err) { if (string(err.what()).compare(0, 28, "cannot resolve call overload") != 0)
throw; } } rhs.type = lhs_bare; rhs.category = ValueCategory::PRValue; rhs.node.type = lhs_bare;
rhs.node.category = rhs.category; if (rhs.node.children.empty()) rhs.node.direct_call = ensure_default_constructor(lhs_bare, true); ensure_default_destructor(lhs_bare);
annotate_expr_node(rhs); }
TypePtr rhs_bare = pa11::strip_cv(expression_object_type(rhs.type)); if (rhs_bare->kind == pa11::TypeKind::Record && pa11::same_type(rhs_bare, lhs_bare)) {
if (!type_is_template_dependent(lhs_bare)) instantiate_member_function_templates(lhs_bare);
vector<Binding*> members = lookup_qualified_set(lhs_bare->scope, "operator=", pa11::LOOKUP_FUNCTION); vector<Binding*> declared_members; bool has_declared_copy_move_assignment = false;
for (size_t i = 0; i < members.size(); ++i) if (!members[i]->is_generated_copy_move_assignment) { declared_members.push_back(members[i]);
if (binding_is_declared_copy_move_assignment_for_record(members[i], lhs_bare, function_template_placeholders_, function_template_specialization_arguments_))
has_declared_copy_move_assignment = true; } if (has_declared_copy_move_assignment && !declared_members.empty()) {
Expr callee = make_member_expr(lhs, "operator=", "."); callee.binding = declared_members[0]; callee.type = declared_members[0]->type; callee.overloads = declared_members;
callee.node.binding = declared_members[0]; callee.node.type = declared_members[0]->type; vector<Expr> args; args.push_back(rhs);
return make_call_expr(callee, args); }
Binding* op_binding = ensure_copy_move_assignment(lhs_bare, move_assign); if (op_binding == NULL && move_assign) op_binding = ensure_copy_move_assignment(lhs_bare, false); if (op_binding == NULL)
throw runtime_error("copy assignment is deleted"); if (deleted_functions_.find(op_binding) != deleted_functions_.end()) throw runtime_error("call to deleted function");
vector<Binding*> candidates; for (size_t i = 0; i < members.size(); ++i)
if (!members[i]->is_generated_copy_move_assignment) candidates.push_back(members[i]); if (find(candidates.begin(), candidates.end(), op_binding) == candidates.end()) candidates.push_back(op_binding);
Expr callee = make_member_expr(lhs, "operator=", "."); callee.binding = candidates[0]; callee.type = candidates[0]->type; callee.overloads = candidates;
callee.node.binding = candidates[0]; callee.node.type = candidates[0]->type; vector<Expr> args; args.push_back(rhs);
return make_call_expr(callee, args); } if (!type_is_template_dependent(lhs_bare)) instantiate_member_function_templates(lhs_bare);
vector<Binding*> members = lookup_qualified_set(lhs_bare->scope, "operator=", pa11::LOOKUP_FUNCTION); vector<Binding*> declared_members; for (size_t i = 0; i < members.size(); ++i)
if (!members[i]->is_generated_copy_move_assignment) declared_members.push_back(members[i]); if (!declared_members.empty()) {
Expr callee = make_member_expr(lhs, "operator=", "."); callee.binding = declared_members[0]; callee.type = declared_members[0]->type; callee.overloads = declared_members;
callee.node.binding = declared_members[0]; callee.node.type = declared_members[0]->type; vector<Expr> args; args.push_back(rhs);
try { return make_call_expr(callee, args); }
catch (const runtime_error& err) { if (string(err.what()).compare(0, 28, "cannot resolve call overload") != 0)
throw; } } Binding* op_binding = ensure_copy_move_assignment(lhs_bare, move_assign);
if (op_binding == NULL && move_assign) op_binding = ensure_copy_move_assignment(lhs_bare, false); if (op_binding == NULL) throw runtime_error("copy assignment is deleted");
Expr callee = make_member_expr(lhs, "operator=", "."); vector<Expr> args; args.push_back(rhs); return make_call_expr(callee, args);
} Expr Parser::make_assignment_expr(ETokenType op, const string& text, Expr lhs,
Expr rhs) { TypePtr lhs_type = expression_object_type(lhs.type); TypePtr lhs_bare = pa11::strip_cv(lhs_type);
	if (op != OP_ASS) {
	Expr overloaded = make_overloaded_compound_assignment_expr(op, text, lhs,
	rhs, lhs_bare); if (overloaded.valid) return overloaded;
	} if (op == OP_ASS && lhs_bare->kind == pa11::TypeKind::Record && lhs_bare->scope != NULL)
	return make_record_assignment_expr(lhs, rhs, lhs_bare); if (lhs.category != ValueCategory::LValue || top_level_const(lhs_type) || (lhs_bare->kind == pa11::TypeKind::Array && !pa11::is_gnu_vector_type(lhs_bare)) ||
	lhs_bare->kind == pa11::TypeKind::Function) throw runtime_error("assignment lhs is not lvalue"); Conversion conv; if (op == OP_ASS)
{ conv = convert_to(rhs, lhs_type); if (!conv.viable) throw runtime_error("invalid assignment conversion");
} else { TypePtr rhs_type = lvalue_to_rvalue_type(rhs.type);
if (!compound_assignment_rhs_viable(op, lvalue_to_rvalue_type(lhs.type), rhs_type)) {
conv = convert_to(rhs, lvalue_to_rvalue_type(lhs.type)); if (!conv.viable || !compound_assignment_rhs_viable( op,
lvalue_to_rvalue_type(lhs.type), lvalue_to_rvalue_type(conv.expr.type))) throw runtime_error("invalid compound assignment conversion"); }
else conv = Conversion(true, 2, rhs); } Expr out;
out.type = lhs_type; out.category = ValueCategory::LValue; out.valid = true; out.node = Node("assignment-expression lvalue " +
pa11::describe_type(out.type) + " " + op_leaf(op, text)); add_child(out.node, lhs.node); add_child(out.node, conv.expr.node); out.node.has_op = true;
out.node.op = op; out.node.token_text = text; annotate_expr_node(out); return out;
} Expr Parser::make_unary_expr(ETokenType op, const string& text, Expr inner) { Expr out;
out.valid = true; TypePtr record = pa11::strip_cv(expression_object_type(inner.type)); if (record->kind == pa11::TypeKind::Record && record->scope != NULL) {
string opname = operator_function_name(op, text); vector<Binding*> members = lookup_qualified_set(record->scope, opname, pa11::LOOKUP_FUNCTION); if (!members.empty())
{ Expr callee = make_member_expr(inner, opname, "."); vector<Expr> args; return make_call_expr(callee, args);
} } if (op == OP_AMP) return make_address_expr(text, inner);
if (op == OP_STAR) return make_deref_expr(text, inner); if ((op == OP_INC || op == OP_DEC) && record->kind == pa11::TypeKind::Record &&
record->scope != NULL) { static const EFundamentalType targets[] = { FT_INT, FT_UNSIGNED_INT, FT_LONG_INT, FT_UNSIGNED_LONG_INT,
FT_LONG_LONG_INT, FT_UNSIGNED_LONG_LONG_INT, FT_INT128, FT_UNSIGNED_INT128, FT_SHORT_INT, FT_UNSIGNED_SHORT_INT, FT_CHAR, FT_SIGNED_CHAR, FT_UNSIGNED_CHAR, FT_BOOL, FT_FLOAT, FT_DOUBLE, FT_LONG_DOUBLE };
for (size_t i = 0; i < sizeof(targets) / sizeof(targets[0]); ++i) { TypePtr ref = pa11::make_lvalue_reference(pa11::make_fundamental(targets[i]));
Conversion conv; try { conv = convert_to(inner, ref);
} catch (const runtime_error&) { continue;
} if (conv.viable) { inner = conv.expr;
record = pa11::strip_cv(expression_object_type(inner.type)); break; } }
} if (op == OP_LNOT && record->kind == pa11::TypeKind::Record && record->scope != NULL) {
++explicit_conversion_context_; Conversion conv; try {
conv = convert_value(inner, pa11::make_fundamental(FT_BOOL)); } catch (...) {
--explicit_conversion_context_; throw; } --explicit_conversion_context_;
if (!conv.viable) throw runtime_error("invalid logical not conversion"); inner = conv.expr; }
if (op == OP_LNOT) out.type = pa11::make_fundamental(FT_BOOL); else if (op == OP_PLUS || op == OP_MINUS || op == OP_COMPL) out.type = usual_arithmetic_type(inner.type, inner.type);
else out.type = expression_object_type(inner.type); out.category = (op == OP_INC || op == OP_DEC) ? ValueCategory::LValue : ValueCategory::PRValue;
out.constant_expression = out.category == ValueCategory::PRValue && inner.constant_expression; if (inner.has_constant_value) {
uint64_t value = inner.constant_value; bool have_value = true; if (op == OP_MINUS) value = uint64_t(0) - value;
else if (op == OP_LNOT) value = value == 0 ? 1 : 0; else if (op == OP_COMPL) value = ~value;
else if (op != OP_PLUS) have_value = false; if (have_value) {
out.has_constant_value = true; out.constant_value = normalize_integral_value(out.type, value); out.null_pointer_constant = value == 0 && pa11::is_integral_or_bool_type(out.type);
} } out.node = Node("unary-expression " + value_category_name(out.category) + " " + pa11::describe_type(out.type) + " " +
op_leaf(op, text)); add_child(out.node, inner.node); out.node.has_op = true; out.node.op = op;
out.node.token_text = text; if ((op == OP_LNOT || op == OP_PLUS || op == OP_MINUS || op == OP_COMPL) && !inner.dependent_value_name.empty()) {
out.dependent_value_name = inner.dependent_value_name; out.dependent_value_owner_template_name = inner.dependent_value_owner_template_name; out.dependent_value_member_name =
inner.dependent_value_member_name; out.dependent_value_owner_template_arguments = inner.dependent_value_owner_template_arguments; out.dependent_value_negated =
(op == OP_MINUS || op == OP_LNOT) ? !inner.dependent_value_negated : inner.dependent_value_negated; }
annotate_expr_node(out); return out; } Expr Parser::make_postfix_expr(ETokenType op, const string& text, Expr inner)
{ if ((op == OP_INC || op == OP_DEC) && pa11::strip_cv(expression_object_type(inner.type))->kind == pa11::TypeKind::Record)
{ static const EFundamentalType targets[] = { FT_INT, FT_UNSIGNED_INT, FT_LONG_INT, FT_UNSIGNED_LONG_INT, FT_LONG_LONG_INT, FT_UNSIGNED_LONG_LONG_INT, FT_INT128, FT_UNSIGNED_INT128, FT_SHORT_INT,
FT_UNSIGNED_SHORT_INT, FT_CHAR, FT_SIGNED_CHAR, FT_UNSIGNED_CHAR, FT_BOOL, FT_FLOAT, FT_DOUBLE, FT_LONG_DOUBLE }; for (size_t i = 0; i < sizeof(targets) / sizeof(targets[0]); ++i)
{ TypePtr ref = pa11::make_lvalue_reference(pa11::make_fundamental(targets[i])); Conversion conv;
try { conv = convert_to(inner, ref); }
catch (const runtime_error&) { continue; }
if (conv.viable) { inner = conv.expr; break;
} } } Expr out;
out.type = expression_object_type(inner.type); out.category = ValueCategory::PRValue; out.valid = true; out.node = Node("postfix-expression prvalue " +
pa11::describe_type(out.type) + " " + op_leaf(op, text)); add_child(out.node, inner.node); out.node.has_op = true; out.node.op = op;
out.node.token_text = text; annotate_expr_node(out); return out; }
Expr Parser::make_record_subscript_expr(TypePtr record, Expr lhs, Expr rhs) { vector<Binding*> members = lookup_qualified_set(record->scope,
"operator[]", pa11::LOOKUP_FUNCTION); if (!members.empty()) {
Expr callee = make_member_expr(lhs, "operator[]", "."); vector<Expr> args; args.push_back(rhs); return make_call_expr(callee, args);
} bool object_const = pa11::type_has_const(expression_object_type(lhs.type)); for (int pass = 0; pass < 2; ++pass)
{ for (map<string, vector<Binding*> >::const_iterator it = record->scope->members.begin(); it != record->scope->members.end();
++it) { if (it->first.compare(0, 9, "operator ") != 0) continue;
for (size_t i = 0; i < it->second.size(); ++i) { Binding* op = it->second[i]; if (op->kind != BindingKind::Function ||
op->type->kind != pa11::TypeKind::Function || op->type->parameters.size() != 1) continue; TypePtr pointer = pa11::strip_cv(op->type->base);
if (pointer->kind != pa11::TypeKind::Pointer) continue; if (!object_const && pass == 0 && pa11::type_has_const(pointer->base))
continue; try { Expr callee;
callee.valid = true; callee.binding = op; callee.type = op->type; callee.category = ValueCategory::LValue;
callee.overloads.push_back(op); callee.node = Node("member-expression lvalue " + pa11::describe_type(callee.type) + " OP_DOT:" + op->name);
add_child(callee.node, lhs.node); callee.node.binding = op; callee.node.has_op = true; callee.node.op = OP_DOT;
callee.node.token_text = op->name; annotate_expr_node(callee); Expr ptr = make_call_expr(callee, vector<Expr>()); return make_subscript_expr(ptr, rhs);
	} catch (const runtime_error&) { }
	} } } throw runtime_error("invalid subscript operands");
} Expr Parser::make_subscript_expr(Expr lhs, Expr rhs) { TypePtr base = pa11::strip_cv(expression_object_type(lhs.type));
if (base->kind == pa11::TypeKind::Array) base = base->base; else if (base->kind == pa11::TypeKind::Pointer) base = base->base;
else { TypePtr rbase = pa11::strip_cv(expression_object_type(rhs.type)); if (rbase->kind == pa11::TypeKind::Array)
base = rbase->base; else if (rbase->kind == pa11::TypeKind::Pointer) base = rbase->base; else if (base->kind == pa11::TypeKind::Record && base->scope != NULL)
	return make_record_subscript_expr(base, lhs, rhs); else if (type_is_template_dependent(lhs.type) || type_is_template_dependent(rhs.type))
	base = pa11::make_dependent_typename_type("__dependent_subscript", false, false, false); else throw runtime_error("invalid subscript operands"); }
Expr out; out.type = base; out.category = ValueCategory::LValue; out.valid = true;
out.node = Node("subscript-expression lvalue " + pa11::describe_type(base)); TypePtr rhs_base = pa11::strip_cv(expression_object_type(rhs.type)); if (rhs_base->kind == pa11::TypeKind::Array || rhs_base->kind == pa11::TypeKind::Pointer)
{ add_child(out.node, rhs.node); add_child(out.node, lhs.node); }
else { add_child(out.node, lhs.node); add_child(out.node, rhs.node);
} annotate_expr_node(out); return out; }
Expr Parser::make_dependent_member_expr(const Expr& object, const string& name, const string& op) {
Expr out; out.valid = true; out.type = pa11::make_dependent_typename_type("__dependent_member", false,
false, false); out.category = ValueCategory::LValue; out.node = Node("member-expression lvalue " +
pa11::describe_type(out.type) + " OP_DOT:" + name); add_child(out.node, object.node); out.node.has_op = true; out.node.op = op == "->" ? OP_ARROW : OP_DOT;
out.node.token_text = name; annotate_expr_node(out); return out; }
Expr Parser::make_member_expr(Expr object, const string& name, const string& op) { TypePtr type = expression_object_type(object.type); if (op == "->")
{ for (int arrow_depth = 0; arrow_depth < 16; ++arrow_depth) { TypePtr arrow_type = pa11::strip_cv(expression_object_type(object.type));
if (arrow_type->kind == pa11::TypeKind::Pointer) { type = arrow_type->base; break; }
if (type_is_template_dependent(arrow_type)) return make_dependent_member_expr(object, name, op);
if (arrow_type->kind != pa11::TypeKind::Record || arrow_type->scope == NULL) throw runtime_error("arrow on non-pointer");
vector<Binding*> ops = lookup_qualified_set(arrow_type->scope, "operator->", pa11::LOOKUP_FUNCTION);
if (ops.empty()) throw runtime_error("arrow on non-pointer");
Expr callee = make_member_expr(object, "operator->", "."); vector<Expr> args; object = make_call_expr(callee, args);
if (arrow_depth == 15) throw runtime_error("recursive operator->"); } } TypePtr bare = pa11::strip_cv(type); if ((bare->kind != pa11::TypeKind::Record || bare->scope == NULL) && type_is_template_dependent(type))
return make_dependent_member_expr(object, name, op); if (bare->kind != pa11::TypeKind::Record || bare->scope == NULL) throw runtime_error("member access on non-record"); if (bare->is_template_specialization && !type_is_template_dependent(bare))
complete_template_record(bare); if (!type_is_template_dependent(bare)) instantiate_member_function_templates(bare); vector<Binding*> found = lookup_qualified_set(bare->scope, name, pa11::LOOKUP_VALUE);
if (found.empty() && (type_is_template_dependent(type) || record_dependent_base_lookup_skips_.count(bare.get()) != 0)) return make_dependent_member_expr(object, name, op);
if (found.empty()) throw runtime_error("member not found: " + name + " in " + pa11::describe_type(bare)); if (!member_access_allowed(found[0], bare))
{ if (found[0]->is_private) throw runtime_error("private member access"); throw runtime_error("protected member access");
} Binding* nonfunction = NULL; for (size_t i = 0; i < found.size(); ++i) { if (found[i]->kind == BindingKind::Function) continue; if (nonfunction == NULL) { nonfunction = found[i]; continue; } if (found[i] != nonfunction && (found[i]->owner != nonfunction->owner || found[i]->name != nonfunction->name || !pa11::same_type(found[i]->type, nonfunction->type))) throw runtime_error("ambiguous member: " + name); }
if (found[0]->kind == BindingKind::Enumerator) { Expr out;
out.binding = found[0]; out.type = found[0]->type; out.category = ValueCategory::PRValue; out.valid = true;
out.constant_expression = true; out.has_constant_value = true; out.constant_value = found[0]->constant_value; out.null_pointer_constant = found[0]->constant_value == 0;
out.node = Node("literal prvalue " + pa11::describe_type(out.type) + " " + to_string(found[0]->constant_value)); out.node.binding = found[0]; out.node.token_text = to_string(found[0]->constant_value);
annotate_expr_node(out); return out; } if (found[0]->kind == BindingKind::Function)
{ vector<Binding*> overloads; bool have_nonstatic = false; for (size_t i = 0; i < found.size(); ++i)
if (found[i]->kind == BindingKind::Function && !found[i]->is_static_member) have_nonstatic = true; for (size_t i = 0; i < found.size(); ++i)
if (found[i]->kind == BindingKind::Function && (!have_nonstatic || !found[i]->is_static_member)) overloads.push_back(found[i]); Binding* first = overloads.empty() ? found[0] : overloads[0];
Expr out; out.valid = true; out.binding = first; out.type = first->type;
out.category = ValueCategory::LValue; out.overloads = overloads; out.node = Node("member-expression lvalue " + pa11::describe_type(out.type) + " OP_DOT:" + name);
add_child(out.node, object.node); out.node.binding = first; out.node.has_op = true; out.node.op = op == "->" ? OP_ARROW : OP_DOT;
out.node.token_text = name; annotate_expr_node(out); return out; }
if (found[0]->is_static_member && found[0]->has_constant) { Expr out; out.type = expression_object_type(found[0]->type);
out.category = ValueCategory::PRValue; out.binding = found[0]; out.valid = true; out.constant_expression = true;
out.has_constant_value = true; out.constant_value = found[0]->constant_value; out.null_pointer_constant = found[0]->constant_value == 0; out.node = Node("literal prvalue " + pa11::describe_type(out.type) +
" " + to_string(found[0]->constant_value)); out.node.binding = found[0]; out.node.token_text = to_string(found[0]->constant_value); annotate_expr_node(out);
return out; } TypePtr member_type = found[0]->type; if (pa11::type_has_const(type) && !found[0]->is_mutable_member)
member_type = pa11::make_cv(member_type, pa11::CV_CONST); Expr out; out.type = member_type; out.category = ValueCategory::LValue;
out.binding = found[0]; out.valid = true; out.node = Node("member-expression lvalue " + pa11::describe_type(member_type) + " OP_DOT:" + name);
add_child(out.node, object.node); out.node.binding = found[0]; out.node.has_op = true; out.node.op = op == "->" ? OP_ARROW : OP_DOT;
out.node.token_text = name; annotate_expr_node(out); return out; }
Expr Parser::make_cast_expr(TypePtr target, const string& op_text, Expr inner, bool suppress_target_pack)
{ if (!at(OP_DOTS) && inner.pack_expansion && inner.pack.size() == 1)
inner = inner.pack[0]; Expr pack; if (make_cast_pack_expr(target, op_text, inner, suppress_target_pack, pack)) return pack;
Expr out; out.type = target; out.category = target->kind == pa11::TypeKind::LValueReference ? ValueCategory::LValue :
target->kind == pa11::TypeKind::RValueReference ? ValueCategory::XValue : ValueCategory::PRValue; out.valid = true;
out.constant_expression = inner.constant_expression; out.has_constant_value = inner.has_constant_value; TypePtr source_object_for_constant = pa11::strip_cv(expression_object_type(inner.type));
TypePtr target_object_for_constant = pa11::strip_cv(target); if (inner.has_constant_value && (pa11::is_integral_or_bool_type(source_object_for_constant) || source_object_for_constant->kind == pa11::TypeKind::Enum) &&
(pa11::is_integral_or_bool_type(target_object_for_constant) || target_object_for_constant->kind == pa11::TypeKind::Enum) && !integral_type_is_unsigned(source_object_for_constant) && integral_type_bits(target_object_for_constant) >
integral_type_bits(source_object_for_constant)) out.constant_value = normalize_integral_value( target, static_cast<uint64_t>(
signed_integral_value(source_object_for_constant, inner.constant_value))); else out.constant_value = normalize_integral_value(target,
inner.constant_value); out.null_pointer_constant = inner.null_pointer_constant && !type_is_pointer(target); if (!inner.dependent_value_name.empty())
{ out.dependent_value_name = inner.dependent_value_name; out.dependent_value_owner_template_name = inner.dependent_value_owner_template_name;
out.dependent_value_member_name = inner.dependent_value_member_name; out.dependent_value_owner_template_arguments = inner.dependent_value_owner_template_arguments;
out.dependent_value_negated = inner.dependent_value_negated; } if (target->kind == pa11::TypeKind::RValueReference && inner.binding != NULL &&
inner.node.line.compare(0, 13, "id-expression") == 0) { out.binding = inner.binding; out.node = Node("id-expression xvalue " + pa11::describe_type(target) +
" " + inner.binding->name); annotate_expr_node(out); return out; }
if ((target->kind == pa11::TypeKind::LValueReference || target->kind == pa11::TypeKind::RValueReference) && target->base.get() != NULL) {
TypePtr target_object = pa11::strip_cv(target->base); TypePtr source_object = pa11::strip_cv(expression_object_type(inner.type)); if (source_object->kind == pa11::TypeKind::Record && target_object->kind == pa11::TypeKind::Record &&
!pa11::same_type(source_object, target_object) && record_has_base_type(source_object, target_object)) { Node base("base-subobject-expression lvalue " +
pa11::describe_type(target_object)); base.type = target_object; base.category = ValueCategory::LValue; add_child(base, inner.node);
inner.node = base; inner.type = target_object; inner.category = ValueCategory::LValue; inner.binding = NULL;
} } TypePtr source_object = pa11::strip_cv(expression_object_type(inner.type)); TypePtr target_object = pa11::strip_cv(target);
if (source_object->kind == pa11::TypeKind::Record && target->kind != pa11::TypeKind::LValueReference && target->kind != pa11::TypeKind::RValueReference && target_object->kind != pa11::TypeKind::Record &&
!pa11::is_void_type(target)) { ++explicit_conversion_context_; Conversion conv;
try { conv = convert_to(inner, target); }
catch (...) { --explicit_conversion_context_; throw;
} --explicit_conversion_context_; if (conv.viable) inner = conv.expr;
	} string line = "cast-expression prvalue " + pa11::describe_type(target); if (!op_text.empty()) line += " " + op_text;
	out.node = Node(line); add_child(out.node, inner.node); out.node.token_text = op_text;
	out.node.is_dynamic_cast_expression = op_text.find("dynamic_cast") != string::npos;
	annotate_expr_node(out);
	return out; } Expr Parser::make_sizeof_expr(uint64_t value) {
Expr out; out.type = pa11::make_fundamental(FT_UNSIGNED_LONG_INT); out.category = ValueCategory::PRValue; out.valid = true;
out.constant_expression = true; out.has_constant_value = true; out.constant_value = value; out.null_pointer_constant = value == 0;
out.node = Node("sizeof-expression prvalue unsigned long int"); out.node.token_text = to_string(value); annotate_expr_node(out); return out;
} Expr Parser::make_dependent_sizeof_expr(ETokenType keyword, TypePtr operand) { Expr out;
out.type = pa11::make_fundamental(FT_UNSIGNED_LONG_INT); out.category = ValueCategory::PRValue; out.valid = true; out.constant_expression = true;
out.has_constant_value = false; out.dependent_value_name = (keyword == KW_SIZEOF ? "sizeof " : "alignof ") + pa11::describe_type(operand);
out.node = Node((keyword == KW_SIZEOF ? "sizeof-expression" : "alignof-expression") + string(" prvalue unsigned long int")); out.node.token_text = out.dependent_value_name;
annotate_expr_node(out); return out; } Expr Parser::make_dependent_sizeof_pack_expr(const string& name)
{ Expr out; out.type = pa11::make_fundamental(FT_UNSIGNED_LONG_INT); out.category = ValueCategory::PRValue;
out.valid = true; out.constant_expression = true; out.has_constant_value = false; out.dependent_value_name = "sizeof...(" + name + ")";
out.node = Node("sizeof-expression prvalue unsigned long int"); out.node.token_text = out.dependent_value_name; annotate_expr_node(out); return out;
}
}  // namespace internal
}  // namespace pa12
