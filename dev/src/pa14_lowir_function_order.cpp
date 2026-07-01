#include "pa14_lowir_function_order_shared.h"
#include <algorithm>
#include <cctype>
namespace pa14 { namespace internal {
namespace {
map<const Binding*, TypePtr>& output_first_this_record_cache()
{
	static map<const Binding*, TypePtr> cache;
	return cache;
}
map<const Binding*, bool>& output_returns_record_cache()
{
	static map<const Binding*, bool> cache;
	return cache;
}
map<const Binding*, bool>& output_returns_pointer_cache()
{
	static map<const Binding*, bool> cache;
	return cache;
}
map<const Binding*, TypePtr>& output_record_result_cache()
{
	static map<const Binding*, TypePtr> cache;
	return cache;
}
map<const Binding*, bool>& output_constructor_like_cache()
{
	static map<const Binding*, bool> cache;
	return cache;
}
map<const Binding*, bool>& output_by_value_record_parameter_cache()
{
	static map<const Binding*, bool> cache;
	return cache;
}
map<const Binding*, TypePtr>& output_first_by_value_record_parameter_cache()
{
	static map<const Binding*, TypePtr> cache;
	return cache;
}
map<pair<const Binding*, bool>, TypePtr>& output_constructor_record_parameter_cache()
{
	static map<pair<const Binding*, bool>, TypePtr> cache;
	return cache;
}
map<pair<const Binding*, const pa11::Type*>, bool>&
output_constructor_has_record_parameter_cache()
{
	static map<pair<const Binding*, const pa11::Type*>, bool> cache;
	return cache;
}
}  // namespace
const string& function_out_name(const FunctionOut& fn)
{ return fn.name; } bool output_function_returns_record(const Binding* binding);
int emitted_function_order_key(const FunctionOut& fn) {
string name = function_out_name(fn); if (name == "main") return 0; if (name.find("operator_lb_rb") != string::npos)
return 30; if (name.find("operator_plus_plus") != string::npos || name.find("operator_minus_minus") != string::npos) return 99;
if (fn.binding != NULL &&
    (fn.binding->name == "operator+" || fn.binding->name == "operator +") &&
    output_function_returns_record(fn.binding))
	return 35;
if (fn.binding != NULL &&
    (fn.binding->name == "operator+=" || fn.binding->name == "operator +="))
	return 45;
if ((name.find("operator_plus") != string::npos || name.find("operator_minus") != string::npos) && name.compare(0, 9, "operator_") != 0) return 40;
if (name.find("operator_lt_lt") != string::npos) return 50; if (name == "operator_plus" || name == "operator_minus") return 60;
if (name.find("operator_lt") != string::npos || name.find("operator_gt") != string::npos || name.find("operator_eq_eq") != string::npos || name.find("operator_bang_eq") != string::npos)
return 70; if (name.find("operator_lp_rp") != string::npos) return 80; if (name.find("operator_star") != string::npos)
return 90; if (name.find("operator_") != string::npos) return name.find("__ov2") != string::npos ? 100 : 99; return 110;
} bool emitted_function_is_operator(const FunctionOut& fn) { return function_out_name(fn).find("operator") != string::npos;
} bool emitted_function_is_strong_entry(const FunctionOut& fn) { string name = function_out_name(fn);
return name == "main" || fn.strong_binding; } TypePtr output_first_this_record(const Binding* binding)
{ map<const Binding*, TypePtr>& cached = output_first_this_record_cache(); map<const Binding*, TypePtr>::const_iterator found = cached.find(binding); if (found != cached.end()) return found->second; if (binding == NULL || binding->type.get() == NULL || binding->type->kind != TypeKind::Function ||
binding->type->parameters.empty()) { cached[binding] = TypePtr(); return TypePtr(); } TypePtr first = pa11::strip_cv(binding->type->parameters[0]); if (first->kind != TypeKind::Pointer)
{ cached[binding] = TypePtr(); return TypePtr(); } TypePtr record = pa11::strip_cv(first->base); TypePtr result = record->kind == TypeKind::Record ? record : TypePtr(); cached[binding] = result; return result; }
bool output_function_returns_record(const Binding* binding) { map<const Binding*, bool>& cached = output_returns_record_cache(); if (binding == NULL) return false; map<const Binding*, bool>::const_iterator found = cached.find(binding); if (found != cached.end()) return found->second; bool result_record = false; if (binding->type.get() != NULL &&
binding->type->kind == TypeKind::Function) { TypePtr result = pa11::strip_cv(binding->type->base); result_record = result.get() != NULL && result->kind == TypeKind::Record; } cached[binding] = result_record; return result_record;
} bool output_function_returns_pointer(const Binding* binding) { map<const Binding*, bool>& cached = output_returns_pointer_cache(); map<const Binding*, bool>::const_iterator found = cached.find(binding); if (found != cached.end()) return found->second; if (binding == NULL ||
binding->type.get() == NULL || binding->type->kind != TypeKind::Function) { cached[binding] = false; return false; } TypePtr result = pa11::strip_cv(binding->type->base);
bool pointer = result.get() != NULL && result->kind == TypeKind::Pointer; cached[binding] = pointer; return pointer; } bool output_function_out_returns_pointer(const FunctionOut& fn) {
return fn.returns_pointer_result; } bool output_function_out_returns_record(const FunctionOut& fn)
{ return fn.returns_record_result; }
bool output_class_owned_pointer_helper(const Binding* binding); TypePtr output_owner_record(const Binding* binding); bool output_same_record(TypePtr left, TypePtr right); bool output_owner_template_specialization(const Binding* binding);
TypePtr output_function_record_result(const Binding* binding) { map<const Binding*, TypePtr>& cached = output_record_result_cache(); if (binding == NULL) return TypePtr(); map<const Binding*, TypePtr>::const_iterator found = cached.find(binding); if (found != cached.end()) return found->second; TypePtr result; if (output_function_returns_record(binding)) result = pa11::strip_cv(binding->type->base); cached[binding] = result; return result; } bool output_function_template_specialization(const Binding* binding) {
return binding != NULL && (!binding->function_specialization_symbol.empty() || (binding->aliased_binding != NULL && !binding->aliased_binding->function_specialization_symbol.empty()));
	} bool output_class_constructor(const Binding* binding); bool output_class_member_of_local_class(const Binding* binding); bool output_constructor_like_binding(const Binding* binding)
	{ map<const Binding*, bool>& cached = output_constructor_like_cache(); map<const Binding*, bool>::const_iterator found = cached.find(binding); if (found != cached.end()) return found->second;
	bool result = false; if (output_class_constructor(binding)) result = true; else if (!(binding == NULL ||
	binding->owner == NULL || binding->owner->kind != ScopeKind::Class || binding->is_static_member || binding->name.empty() ||
	binding->name[0] == '~' || binding->name.compare(0, 8, "operator") == 0 || binding->type.get() == NULL || binding->type->kind != TypeKind::Function ||
	pa11::strip_cv(binding->type->base)->kind != TypeKind::Fundamental || pa11::strip_cv(binding->type->base)->fundamental != FT_VOID)) result = output_first_this_record(binding).get() != NULL; cached[binding] = result; return result;
} bool output_has_by_value_record_parameter(const Binding* binding) { map<const Binding*, bool>& cached = output_by_value_record_parameter_cache(); map<const Binding*, bool>::const_iterator found = cached.find(binding); if (found != cached.end()) return found->second; if (binding == NULL ||
binding->type.get() == NULL || binding->type->kind != TypeKind::Function) { cached[binding] = false; return false; } size_t first = binding->owner != NULL &&
binding->owner->kind == ScopeKind::Class && !binding->is_static_member ? 1 : 0; for (size_t i = first; i < binding->type->parameters.size(); ++i) {
TypePtr param = binding->type->parameters[i]; if (is_reference(param)) continue; param = pa11::strip_cv(param);
if (param.get() != NULL && param->kind == TypeKind::Record) { cached[binding] = true; return true; } } cached[binding] = false; return false;
} TypePtr output_first_by_value_record_parameter(const Binding* binding) { map<const Binding*, TypePtr>& cached = output_first_by_value_record_parameter_cache(); map<const Binding*, TypePtr>::const_iterator found = cached.find(binding); if (found != cached.end()) return found->second; if (binding == NULL ||
binding->type.get() == NULL || binding->type->kind != TypeKind::Function) { cached[binding] = TypePtr(); return TypePtr(); } size_t first = binding->owner != NULL &&
binding->owner->kind == ScopeKind::Class && !binding->is_static_member ? 1 : 0; for (size_t i = first; i < binding->type->parameters.size(); ++i) {
TypePtr param = binding->type->parameters[i]; if (is_reference(param)) continue; param = pa11::strip_cv(param);
if (param.get() != NULL && param->kind == TypeKind::Record) { cached[binding] = param; return param; } } cached[binding] = TypePtr(); return TypePtr();
} bool output_has_reference_parameter(const Binding* binding) { if (binding == NULL ||
binding->type.get() == NULL || binding->type->kind != TypeKind::Function) return false; for (size_t i = 0; i < binding->type->parameters.size(); ++i)
if (is_reference(binding->type->parameters[i])) return true; return false; }
	TypePtr output_constructor_record_parameter(const Binding* binding, bool require_by_value) { map<pair<const Binding*, bool>, TypePtr>& cached = output_constructor_record_parameter_cache(); pair<const Binding*, bool> key = make_pair(binding, require_by_value); map<pair<const Binding*, bool>, TypePtr>::const_iterator found = cached.find(key); if (found != cached.end()) return found->second;
	if (!output_constructor_like_binding(binding) ||
	binding->type.get() == NULL || binding->type->kind != TypeKind::Function) { cached[key] = TypePtr(); return TypePtr(); } for (size_t i = 1; i < binding->type->parameters.size(); ++i)
	{ bool ref = is_reference(binding->type->parameters[i]); if (require_by_value && ref) continue;
	TypePtr param = pa11::strip_cv(object_type(binding->type->parameters[i])); if (param.get() != NULL && param->kind == TypeKind::Record) { cached[key] = param; return param; } }
	cached[key] = TypePtr(); return TypePtr(); } bool output_constructor_has_record_parameter(const Binding* binding, TypePtr record)
	{ record = record.get() != NULL ? pa11::strip_cv(record) : TypePtr(); map<pair<const Binding*, const pa11::Type*>, bool>& cached = output_constructor_has_record_parameter_cache(); pair<const Binding*, const pa11::Type*> key = make_pair(binding, record.get()); map<pair<const Binding*, const pa11::Type*>, bool>::const_iterator found = cached.find(key); if (found != cached.end()) return found->second;
	if (!output_constructor_like_binding(binding) || record.get() == NULL) { cached[key] = false; return false; } for (size_t i = 1; i < binding->type->parameters.size(); ++i)
	{ TypePtr param = pa11::strip_cv(object_type(binding->type->parameters[i])); if (param.get() != NULL && param->kind == TypeKind::Record &&
	pa11::same_type(record, param)) { cached[key] = true; return true; } } cached[key] = false; return false;
} bool emitted_function_is_readable_template_record_member(const string& name)
{ return name.find("_impl_") != string::npos; } bool emitted_function_is_free_operator(const string& name)
{ return name.compare(0, 9, "operator_") == 0; } int emitted_template_member_order_key(const FunctionOut& fn,
bool abi_template_vtable) { if (emitted_function_is_strong_entry(fn)) return 0;
string name = function_out_name(fn); bool template_record = name.compare(0, 5, "type_") == 0 || (abi_template_vtable &&
emitted_function_is_readable_template_record_member(name)); if (template_record && (output_call_operator(fn.binding) || name.find("operator_lp_rp") != string::npos)) return 10; if (template_record && name.find("__deleting_entry") != string::npos)
return 20; if (template_record && name.find("____") != string::npos) return 30; if (emitted_function_is_free_operator(name))
return 40; if (name.find("__print_helper_t_") == string::npos && name.find("__print_helper") != string::npos) return 45;
if (name.find("__operator_lt_lt") != string::npos) return 50; if (name.find("__operator_lp_rp") != string::npos) return 60;
if (name.find("___") != string::npos && name.find("__base_entry") != string::npos) return 70; if (name.find("___") != string::npos &&
name.find("__deleting_entry") != string::npos) return 80; if (name.find("___") != string::npos) return 90;
if (template_record) return 100; if (name.find("__print_helper_t_") != string::npos) return 110;
return 1000; } bool emitted_operator_run_needs_sort(const vector<FunctionOut>& functions, const vector<size_t>& order,
size_t begin, size_t end) { bool subscript_only = end > begin + 1;
bool has_comparison = false; bool has_iterator_step = false; for (size_t i = begin; i < end; ++i) {
string name = function_out_name(functions[order[i]]); if (name.find("___operator") != string::npos) return true; if (name.find("operator_lb_rb") == string::npos)
subscript_only = false; if (name.find("operator_bang_eq") != string::npos || name.find("operator_eq_eq") != string::npos) has_comparison = true;
if (name.find("operator_star") != string::npos || name.find("operator_plus_plus") != string::npos) has_iterator_step = true; }
return subscript_only || (has_comparison && has_iterator_step); }
vector<size_t> ordered_function_indices(const ProgramLowerer& program) { vector<size_t> order; bool has_template_record_function = false;
bool has_abi_template_vtable = false; for (size_t i = 0; i < program.globals.size(); ++i) if (program.globals[i].find("global @__vtable_type_") != string::npos) has_abi_template_vtable = true;
for (size_t i = 0; i < program.functions.size(); ++i) { order.push_back(i); string name = function_out_name(program.functions[i]);
if (name.compare(0, 5, "type_") == 0 || (has_abi_template_vtable && emitted_function_is_readable_template_record_member(name))) has_template_record_function = true;
} if (has_template_record_function) local_stable_sort(order, [&program, has_abi_template_vtable](size_t lhs, size_t rhs) {
int lkey = emitted_template_member_order_key( program.functions[lhs], has_abi_template_vtable); int rkey = emitted_template_member_order_key( program.functions[rhs], has_abi_template_vtable);
return lkey != rkey ? lkey < rkey : lhs < rhs; }); bool has_template_pointer_constructor = false; bool has_template_reference_constructor = false;
bool has_template_record_plus = false; bool has_template_minus = false; for (size_t i = 0; i < order.size(); ++i) {
int key = emitted_template_dependency_order_key( program.functions[order[i]]); if (key == 100) has_template_pointer_constructor = true;
else if (key == 300 || key == 500) has_template_reference_constructor = true; else if (key == 200) has_template_record_plus = true;
else if (key == 400) has_template_minus = true; } bool has_template_dependency_function =
has_template_pointer_constructor && has_template_reference_constructor && has_template_record_plus && has_template_minus;
if (has_template_dependency_function) local_stable_sort(order, [&program](size_t lhs, size_t rhs) { int lkey = emitted_template_dependency_order_key(
program.functions[lhs]); int rkey = emitted_template_dependency_order_key( program.functions[rhs]); return lkey != rkey ? lkey < rkey : lhs < rhs;
}); order_local_template_members_by_rank(program, order); order_outer_class_lifecycle(program.functions, order); order_record_return_before_zero_constructor(program.functions, order);
order_by_value_record_member_before_zero_constructor(program.functions, order); order_record_return_call_operator_before_zero_constructor(program.functions, order); order_zero_constructor_before_namespace_record_return(program.functions, order); order_namespace_record_return_after_zero_constructor(program.functions, order);
order_nonzero_constructor_before_owner_helpers(program.functions, order); order_by_value_constructor_before_record_constructor_dependencies(program.functions, order); order_owner_constructor_before_template_constructor_dependency(program.functions, order); order_scalar_member_after_owner_record_dependencies(program.functions, order);
order_derived_members_before_inherited_constructor_wrappers(program.functions, order); order_base_entries_after_derived_template_users(program.functions, order); order_local_template_call_flow_functions(program.functions, order); order_template_conversion_flow_functions(program.functions, order);
order_same_owner_constructors_by_arity(program.functions, order); order_zero_argument_constructors_before_local_ctors(program.functions, order); order_by_value_conversion_after_parameter_default(program.functions, order); order_record_result_pointer_member_flow(program.functions, order);
order_local_template_call_flow_functions(program.functions, order); order_template_and_lambda_callees_after_callers(program.functions, order); order_pointer_reference_helpers_before_lambda_callers(program.functions, order); order_class_pointer_helpers_before_value_pointer_constructors(program.functions, order);
order_class_pointer_helpers_by_arity(program.functions, order); order_invoked_functor_after_template_invoke(program.functions, order); order_callable_thunk_flow_functions(program.functions, order); order_template_dependency_flow_functions(program.functions, order);
order_operator_functions_by_key(program.functions, order); order_static_template_member_depth_functions(program.functions, order); order_assignment_helper_flow_functions(program.functions, order); order_assignment_operator_before_owner_zero_constructor(program.functions, order);
order_same_owner_constructor_before_assignment_operator(program.functions, order); order_same_owner_call_operator_before_unreferenced_zero_constructor(program.functions, order); order_local_constructor_before_same_owner_call_operator(program.functions, order); order_referenced_zero_constructor_before_foreign_call_operator(program.functions, order); order_static_member_overload_callees_after_callers(program.functions, order); order_static_template_member_callees_after_callers(program.functions, order); order_static_template_owner_callees_after_callers(program.functions, order);
order_template_owner_constructor_callees_after_callers(program.functions, order); order_same_owner_template_member_callees_after_callers(program.functions, order); order_template_owner_member_callees_after_callers(program.functions, order); order_value_template_callees_after_callers(program.functions, order);
order_class_pointer_helpers_before_value_pointer_constructors(program.functions, order); order_template_dependency_flow_functions(program.functions, order); order_by_value_record_member_before_zero_constructor(program.functions, order); order_preemitted_referenced_callees_after_callers(program.functions, order);
order_class_pointer_helpers_before_value_pointer_constructors(program.functions, order); order_class_pointer_helpers_by_arity(program.functions, order); order_assignment_operator_before_owner_zero_constructor(program.functions, order); order_template_scalar_members_before_assignments(program.functions, order);
order_conversion_after_compound_assignment(program.functions, order); order_inherited_conversion_operators_by_owner_depth(program.functions, order); order_template_owner_call_operator_callees_after_callers(program.functions, order); order_template_reference_constructors_before_foreign_call_operators(program.functions, order); order_lambda_call_operators_by_rank(program, order);
order_lambda_callees_after_callers(program.functions, order); order_pointer_reference_helpers_before_lambda_callers(program.functions, order); order_range_for_operator_functions_by_key(program.functions, order); order_template_reference_constructors_before_foreign_call_operators(program.functions, order);
order_assignment_operator_before_owner_zero_constructor(program.functions, order); order_template_dependency_flow_functions(program.functions, order); order_same_owner_constructor_before_assignment_operator(program.functions, order); order_same_owner_call_operator_before_unreferenced_zero_constructor(program.functions, order); order_local_constructor_before_same_owner_call_operator(program.functions, order); order_referenced_zero_constructor_before_foreign_call_operator(program.functions, order); order_value_constructors_after_scalar_template_helpers(program.functions, order); order_template_conversion_flow_functions(program.functions, order);
order_constructors_after_pointer_reference_helpers(program.functions, order);
order_same_owner_constructors_by_arity(program.functions, order);
order_referenced_template_constructors_by_call_position(program.functions, order);
order_local_type_specialization_lifecycle(program.functions, order);
if (has_abi_template_vtable && has_template_record_function)
local_stable_sort(order, [&program, has_abi_template_vtable](size_t lhs, size_t rhs) { int lkey = emitted_template_member_order_key(
program.functions[lhs], has_abi_template_vtable); int rkey = emitted_template_member_order_key( program.functions[rhs],
has_abi_template_vtable); return lkey != rkey ? lkey < rkey : lhs < rhs; }); size_t run = 0;
while (run < order.size()) { if (!emitted_function_is_operator(program.functions[order[run]])) {
++run; continue; } size_t end = run + 1;
while (end < order.size() && emitted_function_is_operator(program.functions[order[end]])) ++end; if (emitted_operator_run_needs_sort(program.functions, order, run, end))
{ bool subscript_only = true; for (size_t i = run; i < end; ++i) if (function_out_name(program.functions[order[i]])
.find("operator_lb_rb") == string::npos) subscript_only = false; local_stable_sort_range(order, run, end, [&program, subscript_only](size_t lhs, size_t rhs) {
int lkey = emitted_function_order_key(program.functions[lhs]); int rkey = emitted_function_order_key(program.functions[rhs]); if (lkey != rkey) return lkey < rkey;
return subscript_only ? function_out_name(program.functions[lhs]) < function_out_name(program.functions[rhs]) : lhs < rhs;
}); } run = end; }
	order_member_template_lambda_breadth_functions(program.functions, order);
	order_lambda_call_operators_by_rank(program, order);
	local_stable_sort(order, [&program](size_t lhs, size_t rhs) {
	const Binding* lb = program.functions[lhs].binding; const Binding* rb = program.functions[rhs].binding;
	bool lgen = lb != NULL && lb->is_generated_aggregate_constructor;
	bool rgen = rb != NULL && rb->is_generated_aggregate_constructor;
	return lgen != rgen ? !lgen : false;
	}); return order; }
void clear_lowir_function_order_caches()
{
	output_first_this_record_cache().clear();
	output_returns_record_cache().clear();
	output_returns_pointer_cache().clear();
	output_record_result_cache().clear();
	output_constructor_like_cache().clear();
	output_by_value_record_parameter_cache().clear();
	output_first_by_value_record_parameter_cache().clear();
	output_constructor_record_parameter_cache().clear();
	output_constructor_has_record_parameter_cache().clear();
}
}  // namespace internal
}  // namespace pa14
