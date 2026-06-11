#include "pa14_lowir_internal.h"
#include <algorithm>
#include <cctype>
namespace pa14 { namespace internal { namespace { string function_out_name(const FunctionOut& fn)
{ return fn.name; } int emitted_function_order_key(const FunctionOut& fn) {
string name = function_out_name(fn); if (name == "main") return 0; if (name.find("operator_lb_rb") != string::npos)
return 30; if (name.find("operator_plus_plus") != string::npos || name.find("operator_minus_minus") != string::npos) return 99;
if ((name.find("operator_plus") != string::npos || name.find("operator_minus") != string::npos) && name.compare(0, 9, "operator_") != 0) return 40;
if (name.find("operator_lt_lt") != string::npos) return 50; if (name == "operator_plus" || name == "operator_minus") return 60;
if (name.find("operator_lt") != string::npos || name.find("operator_gt") != string::npos || name.find("operator_eq_eq") != string::npos || name.find("operator_bang_eq") != string::npos)
return 70; if (name.find("operator_lp_rp") != string::npos) return 80; if (name.find("operator_star") != string::npos)
return 90; if (name.find("operator_") != string::npos) return name.find("__ov2") != string::npos ? 100 : 99; return 110;
} bool emitted_function_is_operator(const FunctionOut& fn) { return function_out_name(fn).find("operator") != string::npos;
} bool emitted_function_is_strong_entry(const FunctionOut& fn) { string name = function_out_name(fn);
return name == "main" || fn.strong_binding; } TypePtr output_first_this_record(const Binding* binding)
{ if (binding == NULL || binding->type.get() == NULL || binding->type->kind != TypeKind::Function ||
binding->type->parameters.empty()) return TypePtr(); TypePtr first = pa11::strip_cv(binding->type->parameters[0]); if (first->kind != TypeKind::Pointer)
return TypePtr(); TypePtr record = pa11::strip_cv(first->base); return record->kind == TypeKind::Record ? record : TypePtr(); }
bool output_function_returns_record(const Binding* binding) { if (binding == NULL || binding->type.get() == NULL ||
binding->type->kind != TypeKind::Function) return false; TypePtr result = pa11::strip_cv(binding->type->base); return result.get() != NULL && result->kind == TypeKind::Record;
} bool output_function_returns_pointer(const Binding* binding) { if (binding == NULL ||
binding->type.get() == NULL || binding->type->kind != TypeKind::Function) return false; TypePtr result = pa11::strip_cv(binding->type->base);
return result.get() != NULL && result->kind == TypeKind::Pointer; } bool output_function_out_returns_pointer(const FunctionOut& fn) {
return fn.returns_pointer_result; } bool output_function_out_returns_record(const FunctionOut& fn)
{ return output_function_returns_record(fn.binding); }
bool output_class_owned_pointer_helper(const Binding* binding); TypePtr output_owner_record(const Binding* binding); bool output_same_record(TypePtr left, TypePtr right); bool output_owner_template_specialization(const Binding* binding);
TypePtr output_function_record_result(const Binding* binding) { if (!output_function_returns_record(binding)) return TypePtr();
return pa11::strip_cv(binding->type->base); } bool output_function_template_specialization(const Binding* binding) {
return binding != NULL && (!binding->function_specialization_symbol.empty() || (binding->aliased_binding != NULL && !binding->aliased_binding->function_specialization_symbol.empty()));
} bool output_class_constructor(const Binding* binding); bool output_class_member_of_local_class(const Binding* binding); bool output_constructor_like_binding(const Binding* binding)
{ if (output_class_constructor(binding)) return true; if (binding == NULL ||
binding->owner == NULL || binding->owner->kind != ScopeKind::Class || binding->is_static_member || binding->name.empty() ||
binding->name[0] == '~' || binding->name.compare(0, 8, "operator") == 0 || binding->type.get() == NULL || binding->type->kind != TypeKind::Function ||
pa11::strip_cv(binding->type->base)->kind != TypeKind::Fundamental || pa11::strip_cv(binding->type->base)->fundamental != FT_VOID) return false; return output_first_this_record(binding).get() != NULL;
} bool output_has_by_value_record_parameter(const Binding* binding) { if (binding == NULL ||
binding->type.get() == NULL || binding->type->kind != TypeKind::Function) return false; size_t first = binding->owner != NULL &&
binding->owner->kind == ScopeKind::Class && !binding->is_static_member ? 1 : 0; for (size_t i = first; i < binding->type->parameters.size(); ++i) {
TypePtr param = binding->type->parameters[i]; if (is_reference(param)) continue; param = pa11::strip_cv(param);
if (param.get() != NULL && param->kind == TypeKind::Record) return true; } return false;
} TypePtr output_first_by_value_record_parameter(const Binding* binding) { if (binding == NULL ||
binding->type.get() == NULL || binding->type->kind != TypeKind::Function) return TypePtr(); size_t first = binding->owner != NULL &&
binding->owner->kind == ScopeKind::Class && !binding->is_static_member ? 1 : 0; for (size_t i = first; i < binding->type->parameters.size(); ++i) {
TypePtr param = binding->type->parameters[i]; if (is_reference(param)) continue; param = pa11::strip_cv(param);
if (param.get() != NULL && param->kind == TypeKind::Record) return param; } return TypePtr();
} bool output_has_reference_parameter(const Binding* binding) { if (binding == NULL ||
binding->type.get() == NULL || binding->type->kind != TypeKind::Function) return false; for (size_t i = 0; i < binding->type->parameters.size(); ++i)
if (is_reference(binding->type->parameters[i])) return true; return false; }
TypePtr output_constructor_record_parameter(const Binding* binding, bool require_by_value) { if (!output_constructor_like_binding(binding) ||
binding->type.get() == NULL || binding->type->kind != TypeKind::Function) return TypePtr(); for (size_t i = 1; i < binding->type->parameters.size(); ++i)
{ bool ref = is_reference(binding->type->parameters[i]); if (require_by_value && ref) continue;
TypePtr param = pa11::strip_cv(object_type(binding->type->parameters[i])); if (param.get() != NULL && param->kind == TypeKind::Record) return param; }
return TypePtr(); } bool output_constructor_has_record_parameter(const Binding* binding, TypePtr record)
{ if (!output_constructor_like_binding(binding) || record.get() == NULL) return false; for (size_t i = 1; i < binding->type->parameters.size(); ++i)
{ TypePtr param = pa11::strip_cv(object_type(binding->type->parameters[i])); if (param.get() != NULL && param->kind == TypeKind::Record &&
pa11::same_type(pa11::strip_cv(record), param)) return true; } return false;
} int output_template_conversion_flow_key(const FunctionOut& fn) { const Binding* binding = fn.binding;
if (binding == NULL || !binding_has_template_specialization_context(binding) || !output_function_template_specialization(binding)) return 0;
if (binding->name.compare(0, 9, "operator ") == 0 && output_function_returns_record(binding)) return 1; if (output_class_constructor(binding) &&
output_has_by_value_record_parameter(binding)) return 2; if (binding->name == "operator=" && output_has_by_value_record_parameter(binding))
return 3; return 0; } void order_template_conversion_flow_functions(const vector<FunctionOut>& functions,
vector<size_t>& order) { bool has_conversion = false; bool has_constructor = false;
bool has_assignment = false; vector<size_t> positions; for (size_t i = 0; i < order.size(); ++i) {
int key = output_template_conversion_flow_key(functions[order[i]]); if (key == 0) continue; positions.push_back(i);
has_conversion = has_conversion || key == 1; has_constructor = has_constructor || key == 2; has_assignment = has_assignment || key == 3; }
if (!has_conversion || !has_constructor || !has_assignment) return; vector<size_t> selected; for (size_t i = 0; i < positions.size(); ++i)
selected.push_back(order[positions[i]]); stable_sort(selected.begin(), selected.end(), [&functions](size_t lhs, size_t rhs) { int lkey = output_template_conversion_flow_key(functions[lhs]);
int rkey = output_template_conversion_flow_key(functions[rhs]); return lkey != rkey ? lkey < rkey : false; }); for (size_t i = 0; i < positions.size(); ++i)
order[positions[i]] = selected[i]; } bool output_inline_definition_rank(const ProgramLowerer& program, const Binding* binding,
size_t& rank) { map<const Binding*, size_t>::const_iterator found = program.inline_definition_ranks.find(binding);
if (found != program.inline_definition_ranks.end()) { rank = found->second; return true;
} if (binding != NULL && binding->aliased_binding != NULL) { found = program.inline_definition_ranks.find(binding->aliased_binding);
if (found != program.inline_definition_ranks.end()) { rank = found->second; return true;
} } return false; }
void order_local_template_members_by_rank(const ProgramLowerer& program, vector<size_t>& order) { vector<size_t> positions;
for (size_t i = 0; i < order.size(); ++i) { const Binding* binding = program.functions[order[i]].binding; size_t rank = 0;
if (binding == NULL || !output_inline_definition_rank(program, binding, rank)) continue; positions.push_back(i);
} if (positions.size() < 2) return; vector<size_t> selected;
for (size_t i = 0; i < positions.size(); ++i) selected.push_back(order[positions[i]]); stable_sort(selected.begin(), selected.end(), [&program](size_t lhs, size_t rhs) {
const Binding* lbind = program.functions[lhs].binding; const Binding* rbind = program.functions[rhs].binding; size_t lrank = 0; size_t rrank = 0;
output_inline_definition_rank(program, lbind, lrank); output_inline_definition_rank(program, rbind, rrank); return lrank != rrank ? lrank < rrank : false; });
for (size_t i = 0; i < positions.size(); ++i) order[positions[i]] = selected[i]; } int emitted_template_dependency_order_key(const FunctionOut& fn)
{ const Binding* binding = fn.binding; if (binding == NULL || emitted_function_is_strong_entry(fn)) return 0;
if (!binding_has_template_specialization_context(binding)) return 10; string name = binding->name; bool op = name.compare(0, 8, "operator") == 0;
if (is_class_constructor_binding(binding) && binding->type.get() != NULL && binding->type->kind == TypeKind::Function && binding->type->parameters.size() >= 2)
{ TypePtr constructed = output_first_this_record(binding); TypePtr param = binding->type->parameters[1]; TypePtr bare_param = pa11::strip_cv(param);
if (bare_param->kind == TypeKind::Pointer) return 100; if (is_reference(param)) {
TypePtr param_record = pa11::strip_cv(object_type(param)); if (constructed.get() != NULL && param_record.get() != NULL && param_record->kind == TypeKind::Record &&
pa11::same_type(pa11::strip_cv(constructed), param_record)) return 500; return 300; }
} if (op && (name == "operator+" || name == "operator +") && output_function_returns_record(binding))
return 200; if (op && (name == "operator-" || name == "operator -")) return 400; if (op)
return 600; return 10; } bool output_template_dependency_sort_candidate(const Binding* binding)
{ if (binding == NULL) return false; if (binding_has_template_specialization_context(binding) ||
output_function_template_specialization(binding)) return true; TypePtr owner = output_owner_record(binding); return owner.get() != NULL && owner->is_template_specialization;
} int output_template_dependency_flow_key(const FunctionOut& fn) { const Binding* binding = fn.binding;
if (binding == NULL || emitted_function_is_strong_entry(fn)) return 0; if (!output_template_dependency_sort_candidate(binding)) return 10;
if (output_class_constructor(binding) && binding->type.get() != NULL && binding->type->kind == TypeKind::Function && binding->type->parameters.size() >= 2)
{ TypePtr constructed = output_first_this_record(binding); TypePtr param = binding->type->parameters[1]; TypePtr bare_param = pa11::strip_cv(param);
if (bare_param.get() != NULL && bare_param->kind == TypeKind::Pointer) return 100; if (is_reference(param)) {
TypePtr param_record = pa11::strip_cv(object_type(param)); if (output_same_record(constructed, param_record)) return 500; return 300;
} } bool op = binding->name.compare(0, 8, "operator") == 0; if (op &&
(binding->name == "operator+" || binding->name == "operator +") && output_function_out_returns_record(fn)) return 200; if (op && (binding->name == "operator-" || binding->name == "operator -"))
return 400; if (op) return 600; return 10;
} void order_template_dependency_flow_functions( const vector<FunctionOut>& functions, vector<size_t>& order) {
bool has_template_pointer_constructor = false; bool has_template_reference_constructor = false; bool has_template_record_plus = false; bool has_template_minus = false;
for (size_t i = 0; i < order.size(); ++i) { int key = output_template_dependency_flow_key(functions[order[i]]); if (key == 100)
has_template_pointer_constructor = true; else if (key == 300 || key == 500) has_template_reference_constructor = true; else if (key == 200)
has_template_record_plus = true; else if (key == 400) has_template_minus = true; }
if (!has_template_pointer_constructor || !has_template_reference_constructor || !has_template_record_plus || !has_template_minus)
return; stable_sort(order.begin(), order.end(), [&functions](size_t lhs, size_t rhs) { int lkey = output_template_dependency_flow_key(
functions[lhs]); int rkey = output_template_dependency_flow_key( functions[rhs]); return lkey != rkey ? lkey < rkey : lhs < rhs;
}); } bool output_class_constructor(const Binding* binding) {
static map<const Binding*, bool> cached; if (binding == NULL) return false; map<const Binding*, bool>::const_iterator found = cached.find(binding);
if (found != cached.end()) return found->second; bool result = false;
if (binding->owner != NULL && binding->owner->kind == ScopeKind::Class && binding->type.get() != NULL &&
binding->type->kind == TypeKind::Function) {
if (binding->name == binding->owner->name) result = true; else {
TypePtr record = pa11::record_type_for_scope(binding->owner); record = record.get() != NULL ? pa11::strip_cv(record) : TypePtr(); if (record.get() != NULL && record->kind == TypeKind::Record) {
if (!record->template_primary_name.empty() && binding->name == record->template_primary_name) result = true; else { string record_name = record->name;
size_t args = record_name.find('<'); if (args != string::npos) record_name = record_name.substr(0, args); result = record->is_template_specialization && binding->name == record_name; } } } }
cached[binding] = result; return result;
} bool output_class_member_of_local_class(const Binding* binding) { if (binding == NULL || binding->owner == NULL)
return false; for (Scope* scope = binding->owner; scope != NULL; scope = scope->parent) { if (scope->kind == ScopeKind::Function)
return true; if (scope->kind == ScopeKind::Namespace) return false; }
return false; } bool output_base_entry_function(const FunctionOut& fn) {
return function_out_name(fn).find("__base_entry") != string::npos; } TypePtr output_owner_record(const Binding* binding) {
if (binding == NULL || binding->owner == NULL || binding->owner->kind != ScopeKind::Class) return TypePtr(); TypePtr record = pa11::record_type_for_scope(binding->owner);
record = record.get() != NULL ? pa11::strip_cv(record) : TypePtr(); return record.get() != NULL && record->kind == TypeKind::Record ? record : TypePtr(); }
bool output_same_record(TypePtr left, TypePtr right) { left = left.get() != NULL ? pa11::strip_cv(left) : TypePtr(); right = right.get() != NULL ? pa11::strip_cv(right) : TypePtr();
return left.get() != NULL && right.get() != NULL && left->kind == TypeKind::Record && right->kind == TypeKind::Record &&
pa11::same_type(left, right); } bool output_same_record_or_template_family(TypePtr left, TypePtr right) {
left = left.get() != NULL ? pa11::strip_cv(left) : TypePtr(); right = right.get() != NULL ? pa11::strip_cv(right) : TypePtr(); if (output_same_record(left, right)) return true;
return left.get() != NULL && right.get() != NULL && left->kind == TypeKind::Record && right->kind == TypeKind::Record &&
!left->template_primary_name.empty() && left->template_primary_name == right->template_primary_name; } bool output_record_vector_contains(const vector<TypePtr>& records, TypePtr record)
{ for (size_t i = 0; i < records.size(); ++i) if (output_same_record(records[i], record)) return true;
return false; } bool output_record_is_local(TypePtr record) {
record = record.get() != NULL ? pa11::strip_cv(record) : TypePtr(); if (record.get() == NULL || record->kind != TypeKind::Record || record->scope == NULL)
return false; for (Scope* scope = record->scope; scope != NULL; scope = scope->parent) { if (scope->kind == ScopeKind::Function)
return true; if (scope->kind == ScopeKind::Namespace) return false; }
return false; } void output_collect_local_records(TypePtr type, vector<TypePtr>& records); void output_collect_local_records_from_template_args(
const vector<pa11::TemplateInstanceArgument>& arguments, vector<TypePtr>& records) { for (size_t i = 0; i < arguments.size(); ++i)
{ const pa11::TemplateInstanceArgument& arg = arguments[i]; if (arg.kind == pa11::TemplateInstanceArgumentKind::Type) output_collect_local_records(arg.type, records);
for (size_t j = 0; j < arg.pack.size(); ++j) { vector<pa11::TemplateInstanceArgument> one; one.push_back(arg.pack[j]);
output_collect_local_records_from_template_args(one, records); } output_collect_local_records_from_template_args( arg.value_owner_template_arguments, records);
} } void output_collect_local_records(TypePtr type, vector<TypePtr>& records) {
type = type.get() != NULL ? pa11::strip_cv(type) : TypePtr(); if (type.get() == NULL) return; if (type->kind == TypeKind::Record)
{ if (output_record_is_local(type) && !output_record_vector_contains(records, type)) records.push_back(type);
output_collect_local_records_from_template_args( type->template_arguments, records); output_collect_local_records(type->base, records); return;
} output_collect_local_records(type->base, records); output_collect_local_records(type->member_class, records); for (size_t i = 0; i < type->parameters.size(); ++i)
output_collect_local_records(type->parameters[i], records); } bool output_type_mentions_record(TypePtr type, TypePtr record) {
type = type.get() != NULL ? pa11::strip_cv(type) : TypePtr(); if (type.get() == NULL || record.get() == NULL) return false; if (type->kind == TypeKind::Record)
{ if (output_same_record(type, record)) return true; for (size_t i = 0; i < type->template_arguments.size(); ++i)
{ const pa11::TemplateInstanceArgument& arg = type->template_arguments[i]; if (arg.kind == pa11::TemplateInstanceArgumentKind::Type &&
output_type_mentions_record(arg.type, record)) return true; for (size_t j = 0; j < arg.pack.size(); ++j) if (arg.pack[j].kind ==
pa11::TemplateInstanceArgumentKind::Type && output_type_mentions_record(arg.pack[j].type, record)) return true; for (size_t j = 0;
j < arg.value_owner_template_arguments.size(); ++j) if (arg.value_owner_template_arguments[j].kind == pa11::TemplateInstanceArgumentKind::Type &&
output_type_mentions_record( arg.value_owner_template_arguments[j].type, record)) return true;
} } if (output_type_mentions_record(type->base, record) || output_type_mentions_record(type->member_class, record))
return true; for (size_t i = 0; i < type->parameters.size(); ++i) if (output_type_mentions_record(type->parameters[i], record)) return true;
return false; } bool output_type_mentions_any_record(TypePtr type, const vector<TypePtr>& records)
{ for (size_t i = 0; i < records.size(); ++i) if (output_type_mentions_record(type, records[i])) return true;
return false; } bool output_binding_related_to_records(const Binding* binding, const vector<TypePtr>& records)
{ if (binding == NULL) return false; return output_type_mentions_any_record(binding->type, records) ||
output_type_mentions_any_record(output_owner_record(binding), records); } bool output_function_mentions_record(const Binding* binding, TypePtr record) {
if (binding == NULL || binding->type.get() == NULL || binding->type->kind != TypeKind::Function || record.get() == NULL)
return false; if (output_same_record(output_first_this_record(binding), record) || output_same_record(output_function_record_result(binding), record)) return true;
for (size_t i = 0; i < binding->type->parameters.size(); ++i) { TypePtr param = pa11::strip_cv(object_type(binding->type->parameters[i])); if (output_same_record(param, record))
return true; } return false; }
bool output_function_has_reference_parameter_record(const Binding* binding, TypePtr record) { if (binding == NULL ||
binding->type.get() == NULL || binding->type->kind != TypeKind::Function || record.get() == NULL) return false;
for (size_t i = 0; i < binding->type->parameters.size(); ++i) { if (!is_reference(binding->type->parameters[i])) continue;
TypePtr param = pa11::strip_cv(object_type(binding->type->parameters[i])); if (output_same_record(param, record)) return true;
} return false; } bool output_local_class_constructor(const FunctionOut& fn)
{ return output_class_constructor(fn.binding) && output_class_member_of_local_class(fn.binding) && !output_base_entry_function(fn);
} bool output_zero_argument_nonlocal_constructor(const FunctionOut& fn) { return output_class_constructor(fn.binding) &&
fn.binding->type->parameters.size() == 1 && !output_class_member_of_local_class(fn.binding) && !output_base_entry_function(fn); }
size_t output_constructor_arity(const FunctionOut& fn) { if (!output_class_constructor(fn.binding) || output_base_entry_function(fn))
return 0; return fn.binding->type->parameters.size(); } string output_constructor_owner_family(const Binding* binding)
{ if (binding == NULL || binding->owner == NULL) return ""; TypePtr record = pa11::record_type_for_scope(binding->owner);
record = record.get() != NULL ? pa11::strip_cv(record) : TypePtr(); if (record.get() == NULL || record->kind != TypeKind::Record) return ""; if (!record->template_primary_name.empty())
return record->template_primary_name; return record->is_template_specialization ? record->name : ""; } bool output_constructors_share_owner_family(const Binding* left,
const Binding* right) { if (left == NULL || right == NULL) return false;
if (left->owner == right->owner) return true; string left_family = output_constructor_owner_family(left); return !left_family.empty() &&
left_family == output_constructor_owner_family(right); } Scope* output_outer_class_scope(const Binding* binding) {
Scope* outer = NULL; for (Scope* scope = binding != NULL ? binding->owner : NULL; scope != NULL; scope = scope->parent)
{ if (scope->kind == ScopeKind::Class) { outer = scope;
continue; } break; }
return outer; } int output_outer_lifecycle_key(const FunctionOut& fn) {
const Binding* binding = fn.binding; Scope* outer = output_outer_class_scope(binding); if (outer == NULL) return 0;
if (binding->owner == outer && output_class_constructor(binding)) return 1; if (binding->owner == outer && is_class_destructor_binding(binding)) return 2;
if (binding->owner != outer) return 3; return 0; }
void order_outer_class_lifecycle(const vector<FunctionOut>& functions, vector<size_t>& order) { bool changed = true;
for (size_t guard = 0; changed && guard < order.size() * order.size() + 1; ++guard) { changed = false; for (size_t i = 0; i < order.size(); ++i)
{ const Binding* left = functions[order[i]].binding; Scope* left_outer = output_outer_class_scope(left); int left_key = output_outer_lifecycle_key(functions[order[i]]);
if (left_outer == NULL || left_key == 0) continue; for (size_t j = i + 1; j < order.size(); ++j) {
const Binding* right = functions[order[j]].binding; if (output_outer_class_scope(right) != left_outer) continue; int right_key =
output_outer_lifecycle_key(functions[order[j]]); if (right_key == 0 || left_key <= right_key) continue; swap(order[i], order[j]);
changed = true; break; } if (changed)
break; } } }
void order_record_return_before_zero_constructor( const vector<FunctionOut>& functions, vector<size_t>& order) { bool changed = true;
for (size_t guard = 0; changed && guard < order.size() * order.size() + 1; ++guard) { changed = false; for (size_t i = 0; i < order.size(); ++i)
{ const Binding* left = functions[order[i]].binding; if (!output_class_constructor(left) || left->type->parameters.size() != 1)
continue; TypePtr constructed = output_first_this_record(left); if (constructed.get() == NULL) continue;
for (size_t j = i + 1; j < order.size(); ++j) { const Binding* right = functions[order[j]].binding; if (right == NULL ||
right->owner == NULL || right->owner->kind != ScopeKind::Class) continue; TypePtr result = output_function_record_result(right);
if (result.get() == NULL || !pa11::same_type(pa11::strip_cv(constructed), pa11::strip_cv(result))) continue;
swap(order[i], order[j]); changed = true; break; }
if (changed) break; } }
} void order_by_value_record_member_before_zero_constructor( const vector<FunctionOut>& functions, vector<size_t>& order) {
bool changed = true; for (size_t guard = 0; changed && guard < order.size() * order.size() + 1; ++guard)
{ changed = false; for (size_t i = 0; i < order.size(); ++i) {
const Binding* ctor = functions[order[i]].binding; if (!output_class_constructor(ctor) || ctor->type->parameters.size() != 1 || output_base_entry_function(functions[order[i]]))
continue; TypePtr constructed = output_first_this_record(ctor); if (constructed.get() == NULL) continue;
for (size_t j = i + 1; j < order.size(); ++j) { const Binding* member = functions[order[j]].binding; if (member == NULL ||
output_constructor_like_binding(member) || (!output_function_template_specialization(member) && !binding_has_template_specialization_context(member) && !output_owner_template_specialization(member) &&
!output_class_member_of_local_class(member))) continue; TypePtr parameter = output_first_by_value_record_parameter(member);
if (!output_same_record_or_template_family( constructed, parameter)) continue; swap(order[i], order[j]);
changed = true; break; } if (changed)
break; } } }
bool output_call_operator(const Binding* binding) { return binding != NULL && (binding->name == "operator()" || binding->name == "operator ()");
} bool output_lambda_related_binding(const Binding* binding) { if (binding == NULL)
return false; if (binding->name.compare(0, 8, "__lambda") == 0) return true; return binding->owner != NULL &&
binding->owner->kind == ScopeKind::Class && binding->owner->name.compare(0, 8, "__lambda") == 0; } bool output_lambda_related_function(const FunctionOut& fn)
{ return output_lambda_related_binding(fn.binding) || function_out_name(fn).compare(0, 8, "__lambda") == 0; }
bool output_lambda_call_operator(const Binding* binding) { return output_lambda_related_binding(binding) && output_call_operator(binding);
} void order_record_return_call_operator_before_zero_constructor( const vector<FunctionOut>& functions, vector<size_t>& order) {
bool changed = true; for (size_t guard = 0; changed && guard < order.size() * order.size() + 1; ++guard) { changed = false;
for (size_t i = 0; i < order.size(); ++i) { const Binding* left = functions[order[i]].binding; if (!output_class_constructor(left) ||
left->type->parameters.size() != 1) continue; for (size_t j = i + 1; j < order.size(); ++j) {
const Binding* right = functions[order[j]].binding; if (right == NULL || right->owner != left->owner || !output_call_operator(right) ||
!output_function_returns_record(right)) continue; swap(order[i], order[j]); changed = true;
break; } if (changed) break;
} } } void order_zero_constructor_before_namespace_record_return(
const vector<FunctionOut>& functions, vector<size_t>& order) { bool changed = true; for (size_t guard = 0; changed && guard < order.size() * order.size() + 1; ++guard)
{ changed = false; for (size_t i = 0; i < order.size(); ++i) {
const Binding* left = functions[order[i]].binding; if (left == NULL || (left->owner != NULL && left->owner->kind != ScopeKind::Namespace)) continue;
TypePtr result = output_function_record_result(left); if (result.get() == NULL) continue; for (size_t j = i + 1; j < order.size(); ++j)
{ const Binding* right = functions[order[j]].binding; if (!output_class_constructor(right) || right->type->parameters.size() != 1)
continue; TypePtr constructed = output_first_this_record(right); if (constructed.get() == NULL || !pa11::same_type(pa11::strip_cv(constructed),
pa11::strip_cv(result))) continue; swap(order[i], order[j]); changed = true;
break; } if (changed) break;
} } } void order_namespace_record_return_after_zero_constructor(
const vector<FunctionOut>& functions, vector<size_t>& order) { for (size_t i = 0; i < order.size(); ++i) {
const Binding* binding = functions[order[i]].binding; if (binding == NULL || (binding->owner != NULL && binding->owner->kind != ScopeKind::Namespace))
continue; TypePtr result = output_function_record_result(binding); if (result.get() == NULL) continue;
size_t ctor_pos = order.size(); for (size_t j = 0; j < order.size(); ++j) { const Binding* candidate = functions[order[j]].binding;
if (!output_class_constructor(candidate) || candidate->type->parameters.size() != 1) continue; TypePtr constructed = output_first_this_record(candidate);
if (constructed.get() != NULL && pa11::same_type(pa11::strip_cv(constructed), pa11::strip_cv(result))) ctor_pos = j;
} if (ctor_pos == order.size() || ctor_pos + 1 >= i) continue; size_t fn_index = order[i];
order.erase(order.begin() + i); order.insert(order.begin() + ctor_pos + 1, fn_index); } }
bool output_same_outer_class(const Binding* left, const Binding* right) { Scope* left_outer = output_outer_class_scope(left); return left_outer != NULL && left_outer == output_outer_class_scope(right);
} void order_nonzero_constructor_before_owner_helpers( const vector<FunctionOut>& functions, vector<size_t>& order) {
for (size_t i = 0; i < order.size(); ++i) { const Binding* ctor = functions[order[i]].binding; if (!output_class_constructor(ctor) ||
ctor->type->parameters.size() <= 1) continue; size_t first_helper = order.size(); size_t after_zero_ctor = 0;
for (size_t j = 0; j < i; ++j) { const Binding* candidate = functions[order[j]].binding; if (output_class_constructor(candidate) &&
candidate->type->parameters.size() == 1) after_zero_ctor = j + 1; if (first_helper == order.size() && candidate != NULL &&
!output_class_constructor(candidate) && !is_class_destructor_binding(candidate) && (candidate->owner == ctor->owner || output_same_outer_class(candidate, ctor)))
first_helper = j; } if (first_helper == order.size()) continue;
size_t insert_pos = first_helper > after_zero_ctor ? first_helper : after_zero_ctor; if (insert_pos >= i) continue;
size_t fn_index = order[i]; order.erase(order.begin() + i); order.insert(order.begin() + insert_pos, fn_index);
} } void order_by_value_constructor_before_record_constructor_dependencies( const vector<FunctionOut>& functions, vector<size_t>& order)
{ bool changed = true; for (size_t guard = 0; changed && guard < order.size() * order.size() + 1; ++guard) {
changed = false; for (size_t i = 0; i < order.size(); ++i) { const Binding* left = functions[order[i]].binding;
if (!output_constructor_like_binding(left)) continue; for (size_t j = i + 1; j < order.size(); ++j) {
const Binding* right = functions[order[j]].binding; TypePtr right_param = output_constructor_record_parameter(right, true); if (right_param.get() == NULL)
continue; TypePtr left_by_value = output_constructor_record_parameter(left, true); if (left_by_value.get() != NULL &&
pa11::same_type(pa11::strip_cv(left_by_value), pa11::strip_cv(right_param))) continue; TypePtr left_record = output_first_this_record(left);
bool left_constructs_param = left_record.get() != NULL && pa11::same_type(pa11::strip_cv(left_record), pa11::strip_cv(right_param));
if (!left_constructs_param && !output_constructor_has_record_parameter(left, right_param)) continue; swap(order[i], order[j]);
changed = true; break; } if (changed)
break; } } }
bool output_constructor_owner_template_specialization(const Binding* binding) { if (!output_constructor_like_binding(binding)) return false;
TypePtr record = output_first_this_record(binding); record = record.get() != NULL ? pa11::strip_cv(record) : TypePtr(); return record.get() != NULL && record->kind == TypeKind::Record &&
record->is_template_specialization; } void order_owner_constructor_before_template_constructor_dependency( const vector<FunctionOut>& functions, vector<size_t>& order)
{ bool changed = true; for (size_t guard = 0; changed && guard < order.size() * order.size() + 1; ++guard) {
changed = false; for (size_t i = 0; i < order.size(); ++i) { const Binding* left = functions[order[i]].binding;
TypePtr left_param = output_constructor_record_parameter(left, false); if (left_param.get() == NULL || output_constructor_record_parameter(left, true).get() != NULL || !output_constructor_owner_template_specialization(left))
continue; for (size_t j = i + 1; j < order.size(); ++j) { const Binding* right = functions[order[j]].binding;
if (!output_constructor_like_binding(right) || output_constructor_owner_template_specialization(right) || !output_constructor_has_record_parameter(right, left_param)) continue;
swap(order[i], order[j]); changed = true; break; }
if (changed) break; } }
} void order_scalar_member_after_owner_record_dependencies( const vector<FunctionOut>& functions, vector<size_t>& order) {
for (size_t i = 0; i < order.size(); ++i) { const Binding* scalar = functions[order[i]].binding; if (scalar == NULL ||
scalar->owner == NULL || scalar->owner->kind != ScopeKind::Class || output_class_constructor(scalar) || is_class_destructor_binding(scalar) ||
output_function_returns_record(scalar)) continue; size_t after = i; for (size_t j = i + 1; j < order.size(); ++j)
{ const Binding* candidate = functions[order[j]].binding; if (candidate == NULL || candidate->owner != scalar->owner) continue;
bool dependency = (output_class_constructor(candidate) && candidate->type->parameters.size() > 1) || output_function_returns_record(candidate);
if (dependency) after = j; } if (after == i)
continue; size_t fn_index = order[i]; order.erase(order.begin() + i); order.insert(order.begin() + after, fn_index);
i = after; } } void order_derived_members_before_inherited_constructor_wrappers(
const vector<FunctionOut>& functions, vector<size_t>& order) { bool changed = true; for (size_t guard = 0; changed && guard < order.size() * order.size() + 1; ++guard)
{ changed = false; for (size_t i = 0; i < order.size(); ++i) {
const Binding* ctor = functions[order[i]].binding; TypePtr record = output_owner_record(ctor); if (!output_class_constructor(ctor) || output_base_entry_function(functions[order[i]]) ||
record.get() == NULL || record->base.get() == NULL || !record->is_template_specialization) continue;
for (size_t j = i + 1; j < order.size(); ++j) { const Binding* member = functions[order[j]].binding; if (member == NULL ||
member->owner != ctor->owner || output_class_constructor(member) || is_class_destructor_binding(member)) continue;
size_t fn_index = order[j]; order.erase(order.begin() + j); order.insert(order.begin() + i, fn_index); changed = true;
break; } if (changed) break;
} } } void order_base_entries_after_derived_template_users(
const vector<FunctionOut>& functions, vector<size_t>& order) { for (size_t i = 0; i < order.size(); ++i) {
const FunctionOut& base_fn = functions[order[i]]; if (!output_base_entry_function(base_fn) || !output_class_constructor(base_fn.binding)) continue;
TypePtr base_record = output_first_this_record(base_fn.binding); base_record = base_record.get() != NULL ? pa11::strip_cv(base_record) : TypePtr(); if (base_record.get() == NULL ||
base_record->kind != TypeKind::Record || !base_record->is_template_specialization) continue; vector<TypePtr> derived_records;
size_t last_related = i; for (size_t j = i + 1; j < order.size(); ++j) { const Binding* candidate = functions[order[j]].binding;
TypePtr owner_record = output_owner_record(candidate); if (owner_record.get() != NULL && record_has_base_subobject(owner_record, base_record)) {
derived_records.push_back(owner_record); last_related = j; continue; }
for (size_t k = 0; k < derived_records.size(); ++k) { if (output_function_mentions_record(candidate, derived_records[k]))
{ last_related = j; break; }
} } if (last_related == i) continue;
size_t fn_index = order[i]; order.erase(order.begin() + i); order.insert(order.begin() + last_related, fn_index); i = last_related;
} } int output_local_template_call_flow_key(const Binding* binding, const Binding* caller)
{ if (binding == NULL) return 0; if (binding == caller)
return 1; if (binding->owner != NULL && binding->owner->kind == ScopeKind::Class && output_constructor_like_binding(binding))
return binding->type->parameters.size() == 1 ? 6 : 3; if (binding->owner == NULL || binding->owner->kind != ScopeKind::Class) {
if (output_function_returns_record(binding) && output_has_by_value_record_parameter(binding)) return 2; return 0;
} if (output_function_returns_record(binding)) return 4; if (!is_class_destructor_binding(binding))
return 5; return 0; } void order_local_template_call_flow_functions(
const vector<FunctionOut>& functions, vector<size_t>& order) { for (size_t pos = 0; pos < order.size(); ++pos) {
const Binding* caller = functions[order[pos]].binding; if (caller == NULL || caller->owner == NULL || caller->owner->kind == ScopeKind::Class ||
!output_function_template_specialization(caller) || output_function_returns_record(caller)) continue; vector<TypePtr> local_records;
output_collect_local_records(caller->type, local_records); if (local_records.empty()) continue; vector<size_t> positions;
bool has_operator = false; bool has_member_record_return = false; for (size_t i = 0; i < order.size(); ++i) {
const Binding* binding = functions[order[i]].binding; if (binding == NULL || !output_binding_related_to_records(binding, local_records)) continue;
int key = output_local_template_call_flow_key(binding, caller); if (key == 0) continue; positions.push_back(i);
has_operator = has_operator || key == 2; has_member_record_return = has_member_record_return || key == 4; } if (positions.size() < 2 ||
!has_operator || !has_member_record_return) continue; vector<size_t> selected;
for (size_t i = 0; i < positions.size(); ++i) selected.push_back(order[positions[i]]); stable_sort(selected.begin(), selected.end(), [&functions, caller](size_t lhs, size_t rhs) {
int lkey = output_local_template_call_flow_key( functions[lhs].binding, caller); int rkey = output_local_template_call_flow_key( functions[rhs].binding, caller);
return lkey != rkey ? lkey < rkey : false; }); for (size_t i = 0; i < positions.size(); ++i) order[positions[i]] = selected[i];
} } void order_by_value_conversion_after_parameter_default( const vector<FunctionOut>& functions, vector<size_t>& order)
{ for (size_t i = 0; i < order.size(); ++i) { const Binding* conversion = functions[order[i]].binding;
TypePtr param = output_constructor_record_parameter(conversion, true); TypePtr owner = output_first_this_record(conversion); if (param.get() == NULL || owner.get() == NULL ||
output_same_record(param, owner)) continue; size_t returned_pos = order.size(); size_t default_pos = order.size();
for (size_t j = 0; j < order.size(); ++j) { const Binding* candidate = functions[order[j]].binding; if (output_same_record(output_function_record_result(candidate),
param)) returned_pos = j; if (output_class_constructor(candidate) && candidate->type->parameters.size() == 1 &&
output_same_record(output_first_this_record(candidate), param)) default_pos = j; }
if (returned_pos == order.size() || default_pos == order.size() || default_pos < i) continue;
size_t fn_index = order[default_pos]; order.erase(order.begin() + default_pos); order.insert(order.begin() + i, fn_index); }
} int output_record_result_flow_key(const FunctionOut& fn, TypePtr record) { const Binding* binding = fn.binding;
if (binding == NULL || record.get() == NULL) return 0; if (output_same_record_or_template_family(output_owner_record(binding), record) &&
output_function_out_returns_pointer(fn)) return 1; if (output_same_record_or_template_family( output_function_record_result(binding), record))
return 2; if (output_constructor_like_binding(binding) && output_same_record_or_template_family( output_first_this_record(binding), record))
return 3; return 0; } void order_record_result_pointer_member_flow(
const vector<FunctionOut>& functions, vector<size_t>& order) { for (size_t i = 0; i < order.size(); ++i) {
TypePtr record = output_function_record_result(functions[order[i]].binding); if (record.get() == NULL) continue;
vector<size_t> positions; bool has_pointer_member = false; bool has_constructor = false; for (size_t j = 0; j < order.size(); ++j)
{ int key = output_record_result_flow_key( functions[order[j]], record); if (key == 0)
continue; positions.push_back(j); has_pointer_member = has_pointer_member || key == 1; has_constructor = has_constructor || key == 3;
} if (positions.size() < 2 || !has_pointer_member || !has_constructor) continue; vector<size_t> selected;
for (size_t j = 0; j < positions.size(); ++j) selected.push_back(order[positions[j]]); stable_sort(selected.begin(), selected.end(), [&functions, record](size_t lhs, size_t rhs) {
int lkey = output_record_result_flow_key( functions[lhs], record); int rkey = output_record_result_flow_key( functions[rhs], record);
return lkey != rkey ? lkey < rkey : false; }); for (size_t j = 0; j < positions.size(); ++j) order[positions[j]] = selected[j];
} } void order_operator_functions_by_key(const vector<FunctionOut>& functions, vector<size_t>& order)
{ bool has_range_for_state = false; for (size_t i = 0; i < functions.size(); ++i) if (functions[i].has_range_for_state) has_range_for_state = true; vector<size_t> positions;
bool needs_sort = false; int last_key = -1; bool has_free_operator = false; Scope* first_member_owner = NULL;
bool same_member_owner = true; for (size_t i = 0; i < order.size(); ++i) { if (!emitted_function_is_operator(functions[order[i]]))
continue; string name = function_out_name(functions[order[i]]); bool free_operator = name.compare(0, 8, "operator") == 0; has_free_operator = has_free_operator || free_operator;
if (!free_operator) { Scope* owner = functions[order[i]].binding != NULL ? functions[order[i]].binding->owner : NULL;
if (first_member_owner == NULL) first_member_owner = owner; else if (owner != first_member_owner) same_member_owner = false;
} int key = emitted_function_order_key(functions[order[i]]); if (last_key > key) needs_sort = true;
last_key = key; positions.push_back(i); } if (!needs_sort || positions.size() < 2)
{ if (has_range_for_state || positions.size() < 2) return; needs_sort = true;
} if (!has_range_for_state && !has_free_operator && !same_member_owner) return; vector<size_t> selected;
for (size_t i = 0; i < positions.size(); ++i) selected.push_back(order[positions[i]]); stable_sort(selected.begin(), selected.end(), [&functions, has_range_for_state](size_t lhs, size_t rhs) {
if (has_range_for_state) { int lkey = emitted_function_order_key(functions[lhs]); int rkey = emitted_function_order_key(functions[rhs]);
return lkey != rkey ? lkey < rkey : false; } string lname = function_out_name(functions[lhs]); string rname = function_out_name(functions[rhs]);
bool lfree = lname.compare(0, 8, "operator") == 0; bool rfree = rname.compare(0, 8, "operator") == 0; if (lfree != rfree) return lfree;
if (lfree) return false; auto member_key = [](const string& name) { if (name.find("operator_x32_pointer") != string::npos)
return name.find("const") != string::npos ? 1 : 2; if (name.find("operator_bang_eq") != string::npos) return 3; if (name.find("operator_eq_eq") != string::npos)
return 4; if (name.find("operator_lp_rp") != string::npos) return 5; if (name.find("operator_star") != string::npos)
return 6; if (name.find("operator_plus_plus") != string::npos || name.find("operator_minus_minus") != string::npos) return 7;
if (name.find("operator_plus_eq") != string::npos || name.find("operator_minus_eq") != string::npos) return 9; if (name.find("operator_plus") != string::npos)
return 8; if (name.find("operator_minus") != string::npos) return 10; return 11;
}; int lkey = member_key(lname); int rkey = member_key(rname); return lkey != rkey ? lkey < rkey : false;
}); for (size_t i = 0; i < positions.size(); ++i) order[positions[i]] = selected[i]; }
bool output_has_range_for_state(const vector<FunctionOut>& functions) { for (size_t i = 0; i < functions.size(); ++i) if (functions[i].has_range_for_state) return true; return false;
} void order_range_for_operator_functions_by_key( const vector<FunctionOut>& functions, vector<size_t>& order) {
if (!output_has_range_for_state(functions)) return; vector<size_t> positions; for (size_t i = 0; i < order.size(); ++i)
if (emitted_function_is_operator(functions[order[i]])) positions.push_back(i); if (positions.size() < 2) return;
vector<size_t> selected; for (size_t i = 0; i < positions.size(); ++i) selected.push_back(order[positions[i]]); stable_sort(selected.begin(), selected.end(),
[&functions](size_t lhs, size_t rhs) { int lkey = emitted_function_order_key(functions[lhs]); int rkey = emitted_function_order_key(functions[rhs]); return lkey != rkey ? lkey < rkey : false;
}); for (size_t i = 0; i < positions.size(); ++i) order[positions[i]] = selected[i]; }
bool output_symbol_reference_matches(const string& instr, const string& symbol) { string needle = "@" + symbol;
size_t pos = instr.find(needle); if (pos == string::npos) return false; size_t end = pos + needle.size();
if (end >= instr.size()) return true; char ch = instr[end]; return !(isalnum(static_cast<unsigned char>(ch)) || ch == '_');
} bool output_function_references_symbol(const FunctionOut& fn, const string& symbol) {
for (size_t i = 0; i < fn.blocks.size(); ++i) for (size_t j = 0; j < fn.blocks[i].instrs.size(); ++j) if (output_symbol_reference_matches(fn.blocks[i].instrs[j], symbol))
return true; return false; } size_t output_function_reference_position(const FunctionOut& fn,
const string& symbol) { size_t ordinal = 0; for (size_t i = 0; i < fn.blocks.size(); ++i)
{ for (size_t j = 0; j < fn.blocks[i].instrs.size(); ++j) { if (output_symbol_reference_matches(fn.blocks[i].instrs[j],
symbol)) return ordinal; ++ordinal; }
} return static_cast<size_t>(-1); } bool output_template_or_local_order_function(const FunctionOut& fn)
{ return output_lambda_related_function(fn) || output_function_template_specialization(fn.binding) || binding_has_template_specialization_context(fn.binding) ||
output_owner_template_specialization(fn.binding) || output_class_member_of_local_class(fn.binding); } bool output_referenced_callee_order_candidate(const FunctionOut& caller,
const FunctionOut& callee) { if (!output_template_or_local_order_function(caller) || !output_template_or_local_order_function(callee))
return false; string caller_name = function_out_name(caller); string callee_name = function_out_name(callee); return !callee_name.empty() &&
caller_name != callee_name && !output_function_references_symbol(callee, caller_name) && output_function_references_symbol(caller, callee_name); }
void order_preemitted_referenced_callees_after_callers( const vector<FunctionOut>& functions, vector<size_t>& order) { bool changed = true;
for (size_t guard = 0; changed && guard < order.size() * order.size() + 1; ++guard) {
changed = false; for (size_t i = 0; i < order.size(); ++i) { size_t caller_index = order[i];
const FunctionOut& caller = functions[order[i]]; vector<size_t> selected; bool has_preemitted = false; for (size_t j = 0; j < order.size(); ++j)
{ if (i == j) continue; const FunctionOut& callee = functions[order[j]];
if (!output_referenced_callee_order_candidate(caller, callee)) continue; selected.push_back(order[j]);
if (j < i) has_preemitted = true; } if (!has_preemitted)
continue; stable_sort(selected.begin(), selected.end(), [&functions, &caller](size_t lhs, size_t rhs) { size_t lpos =
output_function_reference_position( caller, function_out_name(functions[lhs])); size_t rpos =
output_function_reference_position( caller, function_out_name(functions[rhs])); return lpos != rpos ? lpos < rpos : false;
}); for (size_t j = 0; j < selected.size(); ++j) { vector<size_t>::iterator it =
find(order.begin(), order.end(), selected[j]); if (it != order.end()) order.erase(it); }
vector<size_t>::iterator caller_it = find(order.begin(), order.end(), caller_index); size_t insert_pos = caller_it == order.end()
? order.size() : static_cast<size_t>(caller_it - order.begin()) + 1; order.insert(order.begin() + insert_pos, selected.begin(), selected.end());
changed = true; break; } }
} bool output_template_or_lambda_follow_edge(const FunctionOut& caller, const FunctionOut& callee) {
if (output_lambda_related_function(callee) || output_lambda_related_function(caller)) return true; if (callee.binding != NULL &&
callee.binding->owner != NULL && callee.binding->owner->kind == ScopeKind::Class && output_function_returns_pointer(callee.binding) && !output_has_reference_parameter(callee.binding))
return false; if (callee.binding != NULL && output_function_template_specialization(callee.binding)) return true;
return caller.binding != NULL && output_function_template_specialization(caller.binding) && callee.binding != NULL && binding_has_template_specialization_context(callee.binding);
} void order_template_and_lambda_callees_after_callers( const vector<FunctionOut>& functions, vector<size_t>& order) {
bool enabled = false; for (size_t i = 0; i < functions.size(); ++i) { if (output_lambda_related_function(functions[i]) ||
output_class_owned_pointer_helper(functions[i].binding)) { enabled = true; break;
} } if (!enabled) return;
for (size_t i = 0; i < order.size(); ++i) { const FunctionOut& caller = functions[order[i]]; size_t insert_pos = i + 1;
for (size_t j = 0; j < order.size(); ++j) { if (i == j) continue;
const FunctionOut& callee = functions[order[j]]; if (!output_template_or_lambda_follow_edge(caller, callee) || !output_function_references_symbol( caller, function_out_name(callee)))
continue; if (j == insert_pos) { ++insert_pos;
continue; } if (j < i && !output_lambda_related_function(caller) &&
!output_lambda_related_function(callee) && output_function_returns_pointer(callee.binding) && output_has_reference_parameter(callee.binding)) continue;
size_t fn_index = order[j]; order.erase(order.begin() + j); size_t target = j < insert_pos ? insert_pos - 1 : insert_pos; order.insert(order.begin() + target, fn_index);
if (j < i) --i; j = target; insert_pos = target + 1;
} } } void order_pointer_reference_helpers_before_lambda_callers(
const vector<FunctionOut>& functions, vector<size_t>& order) { for (size_t i = 0; i < order.size(); ++i) {
const FunctionOut& lambda = functions[order[i]]; if (!output_lambda_related_function(lambda)) continue; for (size_t j = i + 1; j < order.size(); ++j)
{ const FunctionOut& helper = functions[order[j]]; if (!output_function_out_returns_pointer(helper) || !output_function_references_symbol(
lambda, function_out_name(helper))) continue; size_t fn_index = order[j]; order.erase(order.begin() + j);
order.insert(order.begin() + i, fn_index); ++i; j = i; }
} } bool output_class_owned_pointer_helper(const Binding* binding) {
return binding != NULL && binding->owner != NULL && binding->owner->kind == ScopeKind::Class && binding->name.compare(0, 8, "operator") != 0 &&
output_function_returns_pointer(binding) && !output_has_reference_parameter(binding); } void order_class_pointer_helpers_before_value_pointer_constructors(
const vector<FunctionOut>& functions, vector<size_t>& order) { bool changed = true; for (size_t guard = 0; changed && guard < order.size() * order.size() + 1; ++guard)
{ changed = false; for (size_t i = 0; i < order.size(); ++i) {
const Binding* ctor = functions[order[i]].binding; if (!output_constructor_like_binding(ctor) || output_has_reference_parameter(ctor)) continue;
for (size_t j = i + 1; j < order.size(); ++j) { const Binding* helper = functions[order[j]].binding; if (!output_class_owned_pointer_helper(helper))
continue; size_t fn_index = order[j]; order.erase(order.begin() + j); order.insert(order.begin() + i, fn_index);
changed = true; break; } if (changed)
break; } } }
bool output_scalar_template_helper_for_value_constructor(const FunctionOut& helper,
                                                         const Binding* ctor,
                                                         TypePtr ctor_param)
{
	const Binding* binding = helper.binding;
	if (binding == NULL ||
	    binding->owner == NULL ||
	    binding->owner->kind != ScopeKind::Class ||
	    output_constructor_like_binding(binding) ||
	    is_class_destructor_binding(binding) ||
	    output_function_out_returns_record(helper) ||
	    output_function_out_returns_pointer(helper) ||
	    !output_template_or_local_order_function(helper))
		return false;
	TypePtr result =
		binding->type.get() != NULL && binding->type->kind == TypeKind::Function
		? pa11::strip_cv(binding->type->base) : TypePtr();
	if (result.get() == NULL || result->kind != TypeKind::Fundamental)
		return false;
	TypePtr helper_owner = output_owner_record(binding);
	return output_same_record_or_template_family(helper_owner, ctor_param) ||
	       output_type_mentions_record(binding->type, ctor_param);
}

void order_value_constructors_after_scalar_template_helpers(
	const vector<FunctionOut>& functions,
	vector<size_t>& order)
{
	bool changed = true;
	for (size_t guard = 0; changed && guard < order.size() * order.size() + 1;
	     ++guard)
	{
		changed = false;
		for (size_t i = 0; i < order.size(); ++i)
		{
			const Binding* ctor = functions[order[i]].binding;
			if (!output_constructor_like_binding(ctor) ||
			    output_has_reference_parameter(ctor) ||
			    !output_owner_template_specialization(ctor))
				continue;
			TypePtr ctor_param = output_constructor_record_parameter(ctor, true);
			if (ctor_param.get() == NULL)
				continue;
			for (size_t j = i + 1; j < order.size(); ++j)
			{
				if (!output_scalar_template_helper_for_value_constructor(
					    functions[order[j]], ctor, ctor_param))
					continue;
				size_t fn_index = order[i];
				order.erase(order.begin() + i);
				order.insert(order.begin() + j, fn_index);
				changed = true;
				break;
			}
			if (changed)
				break;
		}
	}
}

size_t output_function_parameter_count(const Binding* binding) { return binding != NULL && binding->type.get() != NULL &&
binding->type->kind == TypeKind::Function ? binding->type->parameters.size() : 0; } void order_class_pointer_helpers_by_arity(const vector<FunctionOut>& functions,
vector<size_t>& order) { vector<size_t> positions; for (size_t i = 0; i < order.size(); ++i)
if (output_class_owned_pointer_helper(functions[order[i]].binding)) positions.push_back(i); if (positions.size() < 2) return;
vector<size_t> selected; for (size_t i = 0; i < positions.size(); ++i) selected.push_back(order[positions[i]]); stable_sort(selected.begin(), selected.end(),
[&functions](size_t lhs, size_t rhs) { size_t lcount = output_function_parameter_count( functions[lhs].binding); size_t rcount = output_function_parameter_count(
functions[rhs].binding); return lcount != rcount ? lcount > rcount : false; }); for (size_t i = 0; i < positions.size(); ++i)
order[positions[i]] = selected[i]; } void order_invoked_functor_after_template_invoke( const vector<FunctionOut>& functions, vector<size_t>& order)
{ for (size_t i = 0; i < order.size(); ++i) { const FunctionOut& caller = functions[order[i]];
if (caller.binding == NULL || !output_function_template_specialization(caller.binding)) continue; for (size_t j = 0; j < order.size(); ++j)
{ if (i == j) continue; const FunctionOut& callee = functions[order[j]];
if (callee.binding == NULL || callee.binding->owner == caller.binding->owner || !output_call_operator(callee.binding) || !output_function_references_symbol(
caller, function_out_name(callee))) continue; size_t fn_index = order[j]; order.erase(order.begin() + j);
size_t target = j < i ? i : i + 1; order.insert(order.begin() + target, fn_index); if (j < i) --i;
break; } } }
int output_callable_thunk_flow_key(const FunctionOut& fn, Scope* owner) { const Binding* binding = fn.binding; if (binding == NULL)
return -1; if (binding->owner == owner) { if (output_class_constructor(binding))
return 0; if (output_call_operator(binding)) return 1; if (binding->name == "assign")
return 2; if (output_function_template_specialization(binding)) return 3; }
if (output_call_operator(binding)) return 4; return -1; }
void order_callable_thunk_flow_functions(const vector<FunctionOut>& functions, vector<size_t>& order) { for (size_t i = 0; i < order.size(); ++i)
{ const FunctionOut& thunk = functions[order[i]]; if (thunk.binding == NULL || thunk.binding->owner == NULL ||
thunk.binding->owner->kind != ScopeKind::Class || !output_function_template_specialization(thunk.binding)) continue; Scope* owner = thunk.binding->owner;
vector<string> external_call_operators; for (size_t j = 0; j < functions.size(); ++j) { const Binding* callee = functions[j].binding;
if (callee == NULL || callee->owner == owner || !output_call_operator(callee) || !output_function_references_symbol(
thunk, function_out_name(functions[j]))) continue; external_call_operators.push_back(function_out_name(functions[j])); }
if (external_call_operators.empty()) continue; vector<size_t> positions; bool has_ctor = false;
bool has_call = false; bool has_assign = false; bool has_thunk = false; bool has_external_call = false;
for (size_t j = 0; j < order.size(); ++j) { const FunctionOut& candidate = functions[order[j]]; int key = output_callable_thunk_flow_key(candidate, owner);
if (key < 0) continue; if (key == 4) {
bool referenced = false; string name = function_out_name(candidate); for (size_t k = 0; k < external_call_operators.size(); ++k) if (external_call_operators[k] == name)
referenced = true; if (!referenced) continue; }
positions.push_back(j); has_ctor = has_ctor || key == 0; has_call = has_call || key == 1; has_assign = has_assign || key == 2;
has_thunk = has_thunk || key == 3; has_external_call = has_external_call || key == 4; } if (positions.size() < 5 ||
!has_ctor || !has_call || !has_assign || !has_thunk ||
!has_external_call) continue; vector<size_t> selected; for (size_t j = 0; j < positions.size(); ++j)
selected.push_back(order[positions[j]]); stable_sort(selected.begin(), selected.end(), [&functions, owner](size_t lhs, size_t rhs) { int lkey = output_callable_thunk_flow_key(
functions[lhs], owner); int rkey = output_callable_thunk_flow_key( functions[rhs], owner); return lkey != rkey ? lkey < rkey : false;
}); for (size_t j = 0; j < positions.size(); ++j) order[positions[j]] = selected[j]; }
} size_t output_type_wrapper_depth(TypePtr type) { if (type.get() == NULL)
return 0; size_t nested = 0; if (type->kind == TypeKind::Cv || type->kind == TypeKind::Pointer ||
type->kind == TypeKind::LValueReference || type->kind == TypeKind::RValueReference || type->kind == TypeKind::Array) nested = 1;
size_t base_depth = output_type_wrapper_depth(type->base); size_t member_depth = output_type_wrapper_depth(type->member_class); for (size_t i = 0; i < type->parameters.size(); ++i) {
size_t param_depth = output_type_wrapper_depth(type->parameters[i]); if (param_depth > base_depth) base_depth = param_depth; }
return nested + (base_depth > member_depth ? base_depth : member_depth); } bool output_static_template_member_depth_candidate(const Binding* binding) {
if (binding == NULL || !binding->is_static_member || binding->owner == NULL || binding->owner->kind != ScopeKind::Class ||
binding->type.get() == NULL || binding->type->kind != TypeKind::Function) return false; TypePtr owner = output_owner_record(binding);
return owner.get() != NULL && owner->is_template_specialization && !owner->template_primary_name.empty() && !owner->template_arguments.empty() &&
owner->template_arguments[0].kind == pa11::TemplateInstanceArgumentKind::Type; } string output_static_template_member_family(const Binding* binding)
{ TypePtr owner = output_owner_record(binding); return owner.get() != NULL ? owner->template_primary_name : ""; }
size_t output_static_template_member_depth(const Binding* binding) { TypePtr owner = output_owner_record(binding); if (owner.get() == NULL ||
owner->template_arguments.empty() || owner->template_arguments[0].kind != pa11::TemplateInstanceArgumentKind::Type) return 0;
return output_type_wrapper_depth(owner->template_arguments[0].type); } int output_static_template_member_depth_key(const Binding* binding) {
size_t depth = output_static_template_member_depth(binding); return depth == 0 ? 0 : 1000 - static_cast<int>(depth); } void order_static_template_member_depth_functions(
const vector<FunctionOut>& functions, vector<size_t>& order) { for (size_t i = 0; i < order.size(); ++i) {
const Binding* seed = functions[order[i]].binding; if (!output_static_template_member_depth_candidate(seed)) continue; string family = output_static_template_member_family(seed);
vector<size_t> positions; bool has_zero_depth = false; size_t max_depth = 0; for (size_t j = 0; j < order.size(); ++j)
{ const Binding* binding = functions[order[j]].binding; if (!output_static_template_member_depth_candidate(binding) || binding->name != seed->name ||
output_static_template_member_family(binding) != family) continue; positions.push_back(j); size_t depth = output_static_template_member_depth(binding);
has_zero_depth = has_zero_depth || depth == 0; if (depth > max_depth) max_depth = depth; }
if (positions.size() < 3 || !has_zero_depth || max_depth < 2) continue; vector<size_t> selected; for (size_t j = 0; j < positions.size(); ++j)
selected.push_back(order[positions[j]]); stable_sort(selected.begin(), selected.end(), [&functions](size_t lhs, size_t rhs) { int lkey = output_static_template_member_depth_key(
functions[lhs].binding); int rkey = output_static_template_member_depth_key( functions[rhs].binding); return lkey != rkey ? lkey < rkey : false;
}); for (size_t j = 0; j < positions.size(); ++j) order[positions[j]] = selected[j]; }
} TypePtr output_assignment_record_parameter(const Binding* binding) { if (binding == NULL ||
binding->name != "operator=" || binding->type.get() == NULL || binding->type->kind != TypeKind::Function) return TypePtr();
for (size_t i = 1; i < binding->type->parameters.size(); ++i) { TypePtr param = pa11::strip_cv(object_type(binding->type->parameters[i])); if (param.get() != NULL && param->kind == TypeKind::Record)
return param; } return TypePtr(); }
int output_assignment_helper_flow_key(const Binding* binding, const Binding* assignment, TypePtr parameter_record) {
if (binding == NULL || assignment == NULL) return 0; if (binding == assignment) return 1;
if (output_class_constructor(binding) && binding->owner == assignment->owner && binding->type->parameters.size() == 1) return 2;
if (output_constructor_like_binding(binding) && output_same_record(output_first_this_record(binding), parameter_record)) return 3; return 0;
} void order_assignment_helper_flow_functions( const vector<FunctionOut>& functions, vector<size_t>& order) {
for (size_t i = 0; i < order.size(); ++i) { const Binding* assignment = functions[order[i]].binding; TypePtr parameter_record = output_assignment_record_parameter(assignment);
if (parameter_record.get() == NULL || (!output_function_template_specialization(assignment) && !binding_has_template_specialization_context(assignment) && !output_owner_template_specialization(assignment)))
continue; vector<size_t> positions; bool has_assignment = false; bool has_owner_ctor = false;
bool has_parameter_ctor = false; for (size_t j = 0; j < order.size(); ++j) { const Binding* candidate = functions[order[j]].binding;
int key = output_assignment_helper_flow_key( candidate, assignment, parameter_record); if (key == 0) continue;
positions.push_back(j); has_assignment = has_assignment || key == 1; has_owner_ctor = has_owner_ctor || key == 2; has_parameter_ctor = has_parameter_ctor || key == 3;
} if (positions.size() < 2 || !has_assignment || (!has_owner_ctor && !has_parameter_ctor))
continue; vector<size_t> selected; for (size_t j = 0; j < positions.size(); ++j) selected.push_back(order[positions[j]]);
stable_sort(selected.begin(), selected.end(), [&functions, assignment, parameter_record]( size_t lhs, size_t rhs) { int lkey = output_assignment_helper_flow_key(
functions[lhs].binding, assignment, parameter_record); int rkey = output_assignment_helper_flow_key(
functions[rhs].binding, assignment, parameter_record); return lkey != rkey ? lkey < rkey : false;
}); for (size_t j = 0; j < positions.size(); ++j) order[positions[j]] = selected[j]; }
} bool output_template_assignment_operator(const Binding* binding) { return binding != NULL &&
binding->name == "operator=" && binding->owner != NULL && binding->owner->kind == ScopeKind::Class; }
void order_assignment_operator_before_owner_zero_constructor( const vector<FunctionOut>& functions, vector<size_t>& order) { bool changed = true;
for (size_t guard = 0; changed && guard < order.size() * order.size() + 1; ++guard) {
changed = false; for (size_t i = 0; i < order.size(); ++i) { const Binding* ctor = functions[order[i]].binding;
if (!output_constructor_like_binding(ctor) || ctor->type->parameters.size() != 1) continue; for (size_t j = i + 1; j < order.size(); ++j)
{ const Binding* assignment = functions[order[j]].binding; if (!output_template_assignment_operator(assignment) || assignment->owner != ctor->owner)
continue; swap(order[i], order[j]); changed = true; break;
} if (changed) break; }
} } void order_same_owner_constructor_before_assignment_operator( const vector<FunctionOut>& functions, vector<size_t>& order)
{ bool changed = true; for (size_t guard = 0; changed && guard < order.size() * order.size() + 1;
++guard) { changed = false; for (size_t i = 0; i < order.size(); ++i)
{ const Binding* assignment = functions[order[i]].binding; if (!output_template_assignment_operator(assignment)) continue;
TypePtr assignment_param = output_first_by_value_record_parameter(assignment); if (assignment_param.get() == NULL) continue;
for (size_t j = i + 1; j < order.size(); ++j) { const Binding* ctor = functions[order[j]].binding; if (!output_constructor_like_binding(ctor) ||
ctor->owner != assignment->owner) continue; TypePtr ctor_param = output_first_by_value_record_parameter(ctor);
if (!output_same_record(assignment_param, ctor_param)) continue; swap(order[i], order[j]); changed = true;
break; } if (changed) break;
} } } bool output_reference_orders_constructor_before_call( const vector<FunctionOut>& functions, const FunctionOut& ctor, const FunctionOut& call)
{ for (size_t i = 0; i < functions.size(); ++i) { size_t ctor_pos = output_function_reference_position(functions[i], function_out_name(ctor));
size_t call_pos = output_function_reference_position(functions[i], function_out_name(call)); if (ctor_pos != static_cast<size_t>(-1) &&
call_pos != static_cast<size_t>(-1) && ctor_pos < call_pos) return true; } return false; }
void order_same_owner_call_operator_before_unreferenced_zero_constructor( const vector<FunctionOut>& functions, vector<size_t>& order)
{ bool changed = true; for (size_t guard = 0; changed && guard < order.size() * order.size() + 1;
++guard) { changed = false; for (size_t i = 0; i < order.size(); ++i)
{ const Binding* ctor = functions[order[i]].binding; if (!output_constructor_like_binding(ctor) || ctor->type->parameters.size() != 1) continue;
for (size_t j = i + 1; j < order.size(); ++j) { const Binding* call = functions[order[j]].binding; if (!output_call_operator(call) ||
call->owner != ctor->owner || !output_function_returns_record(call) || output_reference_orders_constructor_before_call(functions, functions[order[i]], functions[order[j]])) continue; swap(order[i], order[j]); changed = true;
break; } if (changed) break;
} } }
void order_local_constructor_before_same_owner_call_operator( const vector<FunctionOut>& functions, vector<size_t>& order)
{ bool changed = true; for (size_t guard = 0; changed && guard < order.size() * order.size() + 1;
++guard) { changed = false; for (size_t i = 0; i < order.size(); ++i)
{ const Binding* call = functions[order[i]].binding; if (!output_call_operator(call)) continue;
for (size_t j = i + 1; j < order.size(); ++j) { const Binding* ctor = functions[order[j]].binding; if (!output_constructor_like_binding(ctor) ||
ctor->owner != call->owner || (ctor->type->parameters.size() == 1 && output_function_returns_record(call)) ||
!output_reference_orders_constructor_before_call(functions, functions[order[j]], functions[order[i]])) continue; swap(order[i], order[j]); changed = true;
break; } if (changed) break;
} } } bool output_same_static_member_overload(const Binding* left,
const Binding* right) { return left != NULL && right != NULL &&
left != right && left->is_static_member && right->is_static_member && left->owner != NULL &&
left->owner == right->owner && left->name == right->name && left->type.get() != NULL && right->type.get() != NULL &&
left->type->kind == TypeKind::Function && right->type->kind == TypeKind::Function; } void order_static_member_overload_callees_after_callers(
const vector<FunctionOut>& functions, vector<size_t>& order) { for (size_t i = 0; i < order.size(); ++i) {
const FunctionOut& caller = functions[order[i]]; for (size_t j = 0; j < order.size(); ++j) { if (i == j)
continue; const FunctionOut& callee = functions[order[j]]; if (!output_same_static_member_overload(caller.binding, callee.binding) ||
!output_function_references_symbol( caller, function_out_name(callee))) continue; size_t fn_index = order[j];
order.erase(order.begin() + j); size_t target = j < i ? i : i + 1; order.insert(order.begin() + target, fn_index); if (j < i)
--i; break; } }
} bool output_same_static_template_member_family(const Binding* left, const Binding* right) {
if (left == NULL || right == NULL || left == right || !left->is_static_member ||
!right->is_static_member || left->name != right->name) return false; TypePtr lowner = output_owner_record(left);
TypePtr rowner = output_owner_record(right); return lowner.get() != NULL && rowner.get() != NULL && !lowner->template_primary_name.empty() &&
lowner->template_primary_name == rowner->template_primary_name; } void order_static_template_member_callees_after_callers( const vector<FunctionOut>& functions, vector<size_t>& order)
{ for (size_t i = 0; i < order.size(); ++i) { const FunctionOut& caller = functions[order[i]];
for (size_t j = 0; j < order.size(); ++j) { if (i == j) continue;
const FunctionOut& callee = functions[order[j]]; if (!output_same_static_template_member_family( caller.binding, callee.binding) || !output_function_references_symbol(
caller, function_out_name(callee))) continue; size_t fn_index = order[j]; order.erase(order.begin() + j);
size_t target = j < i ? i : i + 1; order.insert(order.begin() + target, fn_index); if (j < i) --i;
break; } } }
void order_static_template_owner_callees_after_callers( const vector<FunctionOut>& functions, vector<size_t>& order) { for (size_t i = 0; i < order.size(); ++i)
{ const FunctionOut& caller = functions[order[i]]; if (caller.binding == NULL || !caller.binding->is_static_member ||
!output_owner_template_specialization(caller.binding)) continue; for (size_t j = 0; j < order.size(); ++j) {
if (i == j) continue; const FunctionOut& callee = functions[order[j]]; if (callee.binding == NULL ||
callee.binding->owner == caller.binding->owner || !output_function_template_specialization(callee.binding) || !output_function_references_symbol( caller, function_out_name(callee)))
continue; size_t fn_index = order[j]; order.erase(order.begin() + j); size_t target = j < i ? i : i + 1;
order.insert(order.begin() + target, fn_index); if (j < i) --i; break;
} } } void order_template_owner_constructor_callees_after_callers(
const vector<FunctionOut>& functions, vector<size_t>& order) { for (size_t i = 0; i < order.size(); ++i) {
const FunctionOut& caller = functions[order[i]]; if (!output_constructor_like_binding(caller.binding) || !output_owner_template_specialization(caller.binding)) continue;
for (size_t j = 0; j < order.size(); ++j) { if (i == j) continue;
const FunctionOut& callee = functions[order[j]]; if (callee.binding == NULL || callee.binding->owner == caller.binding->owner || (!output_function_template_specialization(callee.binding) &&
!binding_has_template_specialization_context(callee.binding)) || !output_function_references_symbol( caller, function_out_name(callee))) continue;
size_t fn_index = order[j]; order.erase(order.begin() + j); size_t target = j < i ? i : i + 1; order.insert(order.begin() + target, fn_index);
if (j < i) --i; break; }
} } void order_template_owner_member_callees_after_callers( const vector<FunctionOut>& functions, vector<size_t>& order)
{ for (size_t i = 0; i < order.size(); ++i) { const FunctionOut& caller = functions[order[i]];
if (caller.binding == NULL || caller.binding->is_static_member || output_constructor_like_binding(caller.binding) || output_call_operator(caller.binding) ||
!output_owner_template_specialization(caller.binding)) continue; for (size_t j = 0; j < order.size(); ++j) {
if (i == j) continue; const FunctionOut& callee = functions[order[j]]; if (callee.binding == NULL ||
callee.binding->owner == caller.binding->owner || (!output_function_template_specialization(callee.binding) && !binding_has_template_specialization_context(callee.binding)) || !output_function_references_symbol(
caller, function_out_name(callee))) continue; size_t fn_index = order[j]; order.erase(order.begin() + j);
size_t target = j < i ? i : i + 1; order.insert(order.begin() + target, fn_index); if (j < i) --i;
break; } } }
void order_same_owner_template_member_callees_after_callers( const vector<FunctionOut>& functions, vector<size_t>& order) { for (size_t i = 0; i < order.size(); ++i)
{ const FunctionOut& caller = functions[order[i]]; if (caller.binding == NULL || caller.binding->owner == NULL ||
caller.binding->owner->kind != ScopeKind::Class || !output_owner_template_specialization(caller.binding)) continue; for (size_t j = 0; j < order.size(); ++j)
{ if (i == j) continue; const FunctionOut& callee = functions[order[j]];
if (callee.binding == NULL || callee.binding->owner != caller.binding->owner || !output_function_template_specialization(callee.binding) || !output_function_references_symbol(
caller, function_out_name(callee))) continue; size_t fn_index = order[j]; order.erase(order.begin() + j);
size_t target = j < i ? i : i + 1; order.insert(order.begin() + target, fn_index); if (j < i) --i;
break; } } }
void order_value_template_callees_after_callers( const vector<FunctionOut>& functions, vector<size_t>& order) { for (size_t i = 0; i < order.size(); ++i)
{ const FunctionOut& caller = functions[order[i]]; if (caller.binding == NULL || !output_function_template_specialization(caller.binding) ||
output_function_out_returns_pointer(caller)) continue; for (size_t j = 0; j < order.size(); ++j) {
if (i == j) continue; const FunctionOut& callee = functions[order[j]]; if (callee.binding == NULL ||
output_function_out_returns_pointer(callee) || (!output_function_template_specialization(callee.binding) && !binding_has_template_specialization_context(callee.binding)) || !output_function_references_symbol(
caller, function_out_name(callee))) continue; size_t fn_index = order[j]; order.erase(order.begin() + j);
size_t target = j < i ? i : i + 1; order.insert(order.begin() + target, fn_index); if (j < i) --i;
break; } } }
int output_template_scalar_assignment_key(const Binding* binding) { if (binding == NULL || binding->type.get() == NULL ||
binding->type->kind != TypeKind::Function || !output_owner_template_specialization(binding)) return 0; if (binding->name == "operator=")
return 2; if (binding->name.compare(0, 8, "operator") == 0 || binding->type->parameters.size() != 1) return 0;
TypePtr result = pa11::strip_cv(binding->type->base); return result.get() != NULL && result->kind == TypeKind::Fundamental ? 1 : 0; }
void order_template_scalar_members_before_assignments( const vector<FunctionOut>& functions, vector<size_t>& order) { vector<size_t> positions;
bool has_scalar = false; bool has_assignment = false; for (size_t i = 0; i < order.size(); ++i) {
int key = output_template_scalar_assignment_key( functions[order[i]].binding); if (key == 0) continue;
positions.push_back(i); has_scalar = has_scalar || key == 1; has_assignment = has_assignment || key == 2; }
if (positions.size() < 2 || !has_scalar || !has_assignment) return; vector<size_t> selected; for (size_t i = 0; i < positions.size(); ++i)
selected.push_back(order[positions[i]]); stable_sort(selected.begin(), selected.end(), [&functions](size_t lhs, size_t rhs) { int lkey = output_template_scalar_assignment_key(
functions[lhs].binding); int rkey = output_template_scalar_assignment_key( functions[rhs].binding); return lkey != rkey ? lkey < rkey : false;
}); for (size_t i = 0; i < positions.size(); ++i) order[positions[i]] = selected[i]; }
bool output_compound_assignment_operator(const Binding* binding) { if (binding == NULL) return false;
return binding->name == "operator+=" || binding->name == "operator +=" || binding->name == "operator-=" || binding->name == "operator -=" ||
binding->name == "operator*=" || binding->name == "operator *=" || binding->name == "operator/=" || binding->name == "operator /=";
} bool output_conversion_operator(const Binding* binding) { return binding != NULL &&
binding->name.compare(0, 9, "operator ") == 0 && !output_call_operator(binding); } void order_conversion_after_compound_assignment(
const vector<FunctionOut>& functions, vector<size_t>& order) { for (size_t i = 0; i < order.size(); ++i) {
const FunctionOut& compound = functions[order[i]]; if (!output_compound_assignment_operator(compound.binding)) continue; for (size_t j = 0; j < i; ++j)
{ const FunctionOut& conversion = functions[order[j]]; if (!output_conversion_operator(conversion.binding) || !output_function_references_symbol(
compound, function_out_name(conversion))) continue; size_t fn_index = order[j]; order.erase(order.begin() + j);
order.insert(order.begin() + i, fn_index); --i; break; }
} } bool output_owner_template_specialization(const Binding* binding) {
TypePtr owner = output_owner_record(binding); return owner.get() != NULL && owner->is_template_specialization; } void order_template_owner_call_operator_callees_after_callers(
const vector<FunctionOut>& functions, vector<size_t>& order) { for (size_t i = 0; i < order.size(); ++i) {
const FunctionOut& caller = functions[order[i]]; if (!output_call_operator(caller.binding) || !output_owner_template_specialization(caller.binding)) continue;
for (size_t j = 0; j < order.size(); ++j) { if (i == j) continue;
const FunctionOut& callee = functions[order[j]]; if (callee.binding == NULL || callee.binding->owner == caller.binding->owner || !output_call_operator(callee.binding) ||
!output_function_references_symbol( caller, function_out_name(callee))) continue; size_t fn_index = order[j];
order.erase(order.begin() + j); size_t target = j < i ? i : i + 1; order.insert(order.begin() + target, fn_index); if (j < i)
--i; break; } }
} void order_template_reference_constructors_before_foreign_call_operators( const vector<FunctionOut>& functions, vector<size_t>& order) {
bool changed = true; for (size_t guard = 0; changed && guard < order.size() * order.size() + 1; ++guard)
{ changed = false; for (size_t i = 0; i < order.size(); ++i) {
const Binding* call = functions[order[i]].binding; if (!output_call_operator(call)) continue; for (size_t j = i + 1; j < order.size(); ++j)
{ const Binding* ctor = functions[order[j]].binding; if (!output_constructor_like_binding(ctor) || !output_has_reference_parameter(ctor) ||
!output_owner_template_specialization(ctor) || call->owner == ctor->owner) continue; TypePtr constructed = output_first_this_record(ctor);
if (!output_function_has_reference_parameter_record( call, constructed)) continue; swap(order[i], order[j]);
changed = true; break; } if (changed)
break; } } }
void order_lambda_call_operators_by_rank(const ProgramLowerer& program, vector<size_t>& order) { vector<size_t> positions;
for (size_t i = 0; i < order.size(); ++i) { const Binding* binding = program.functions[order[i]].binding; size_t rank = 0;
if (!output_lambda_call_operator(binding) || !output_inline_definition_rank(program, binding, rank)) continue; positions.push_back(i);
} if (positions.size() < 2) return; vector<size_t> selected;
for (size_t i = 0; i < positions.size(); ++i) selected.push_back(order[positions[i]]); stable_sort(selected.begin(), selected.end(), [&program](size_t lhs, size_t rhs) {
size_t lrank = 0; size_t rrank = 0; output_inline_definition_rank( program, program.functions[lhs].binding, lrank);
output_inline_definition_rank( program, program.functions[rhs].binding, rrank); return lrank != rrank ? lrank < rrank : false; });
for (size_t i = 0; i < positions.size(); ++i) order[positions[i]] = selected[i]; } void order_lambda_callees_after_callers(const vector<FunctionOut>& functions,
vector<size_t>& order) { for (size_t i = 0; i < order.size(); ++i) {
const FunctionOut& caller = functions[order[i]]; size_t insert_pos = i + 1; for (size_t j = 0; j < order.size(); ++j) {
if (i == j) continue; const FunctionOut& callee = functions[order[j]]; if (!output_lambda_related_function(callee) ||
!output_function_references_symbol( caller, function_out_name(callee))) continue; if (j == insert_pos)
{ ++insert_pos; continue; }
size_t fn_index = order[j]; order.erase(order.begin() + j); size_t target = j < insert_pos ? insert_pos - 1 : insert_pos; order.insert(order.begin() + target, fn_index);
if (j < i) --i; j = target; insert_pos = target + 1;
} } }
bool output_breadth_direct_member(const FunctionOut& fn) {
const Binding* binding = fn.binding; return binding != NULL && binding->owner != NULL &&
binding->owner->kind == ScopeKind::Class && !output_lambda_related_binding(binding) &&
!output_function_template_specialization(binding) && !binding_has_template_specialization_context(binding) &&
!output_constructor_like_binding(binding) && output_function_out_returns_record(fn);
}
bool output_breadth_member_template(const FunctionOut& fn, Scope* owner) {
const Binding* binding = fn.binding; return binding != NULL && binding->owner == owner &&
!output_lambda_related_binding(binding) && !output_constructor_like_binding(binding) &&
output_function_template_specialization(binding) && output_function_out_returns_record(fn);
}
bool output_breadth_free_template(const FunctionOut& fn) {
const Binding* binding = fn.binding; return binding != NULL &&
(binding->owner == NULL || binding->owner->kind == ScopeKind::Namespace) &&
output_function_template_specialization(binding) && output_function_out_returns_record(fn);
}
bool output_scope_vector_contains(const vector<Scope*>& scopes, Scope* scope) {
for (size_t i = 0; i < scopes.size(); ++i) if (scopes[i] == scope) return true; return false;
}
int output_member_template_lambda_breadth_key(const FunctionOut& fn) {
if (output_breadth_direct_member(fn)) return 1;
if (fn.binding != NULL && fn.binding->owner != NULL && fn.binding->owner->kind == ScopeKind::Class &&
!output_lambda_related_binding(fn.binding) && output_function_template_specialization(fn.binding) &&
output_function_out_returns_record(fn)) return 2;
if (output_breadth_free_template(fn)) return 3;
if (output_lambda_call_operator(fn.binding) && output_function_out_returns_record(fn)) return 4;
if (output_lambda_call_operator(fn.binding)) return 5;
return 6;
}
void order_member_template_lambda_breadth_functions(const vector<FunctionOut>& functions, vector<size_t>& order) {
map<Scope*, size_t> direct_counts; vector<Scope*> owners;
for (size_t i = 0; i < functions.size(); ++i) {
if (!output_breadth_direct_member(functions[i]) || functions[i].binding == NULL) continue; Scope* owner = functions[i].binding->owner; bool references_member_template = false;
for (size_t j = 0; j < functions.size(); ++j) if (output_breadth_member_template(functions[j], owner) &&
output_function_references_symbol(functions[i], function_out_name(functions[j]))) { references_member_template = true; break; }
if (!references_member_template) continue; if (++direct_counts[owner] == 2) owners.push_back(owner);
}
if (owners.empty()) return; vector<bool> related(functions.size(), false);
for (size_t i = 0; i < functions.size(); ++i) {
const Binding* binding = functions[i].binding; if (binding == NULL || !output_scope_vector_contains(owners, binding->owner)) continue;
if (output_breadth_direct_member(functions[i])) {
for (size_t j = 0; j < functions.size(); ++j) if (output_breadth_member_template(functions[j], binding->owner) &&
output_function_references_symbol(functions[i], function_out_name(functions[j]))) { related[i] = true; break; }
} else if (output_breadth_member_template(functions[i], binding->owner)) related[i] = true;
}
for (size_t i = 0; i < functions.size(); ++i) {
if (!related[i] || !output_breadth_member_template(functions[i], functions[i].binding->owner)) continue;
for (size_t j = 0; j < functions.size(); ++j) if (output_breadth_free_template(functions[j]) &&
output_function_references_symbol(functions[i], function_out_name(functions[j]))) related[j] = true;
}
for (size_t i = 0; i < functions.size(); ++i) {
if (!related[i] || !output_breadth_free_template(functions[i])) continue;
for (size_t j = 0; j < functions.size(); ++j) if (output_lambda_call_operator(functions[j].binding) &&
output_function_references_symbol(functions[i], function_out_name(functions[j]))) related[j] = true;
}
for (size_t i = 0; i < functions.size(); ++i) {
if (!related[i] || (!output_breadth_free_template(functions[i]) && !output_lambda_call_operator(functions[i].binding))) continue;
for (size_t j = 0; j < functions.size(); ++j) if (output_class_constructor(functions[j].binding) &&
output_function_references_symbol(functions[i], function_out_name(functions[j]))) related[j] = true;
}
vector<size_t> positions; for (size_t i = 0; i < order.size(); ++i) if (related[order[i]]) positions.push_back(i);
if (positions.size() < 2) return; vector<size_t> selected; for (size_t i = 0; i < positions.size(); ++i) selected.push_back(order[positions[i]]);
stable_sort(selected.begin(), selected.end(), [&functions](size_t lhs, size_t rhs) { int lkey = output_member_template_lambda_breadth_key(functions[lhs]);
int rkey = output_member_template_lambda_breadth_key(functions[rhs]); return lkey != rkey ? lkey < rkey : false; });
for (size_t i = 0; i < positions.size(); ++i) order[positions[i]] = selected[i];
}
void order_same_owner_constructors_by_arity(const vector<FunctionOut>& functions,
vector<size_t>& order) { bool changed = true; for (size_t guard = 0; changed && guard < order.size() * order.size() + 1; ++guard)
{ changed = false; for (size_t i = 0; i < order.size(); ++i) {
const Binding* left = functions[order[i]].binding; size_t left_arity = output_constructor_arity(functions[order[i]]); if (left_arity == 0) continue;
for (size_t j = i + 1; j < order.size(); ++j) { const Binding* right = functions[order[j]].binding; size_t right_arity =
output_constructor_arity(functions[order[j]]); if (right_arity == 0 || (output_function_template_specialization(left) && output_function_template_specialization(right)) ||
(output_owner_template_specialization(left) && output_owner_template_specialization(right)) || !output_constructors_share_owner_family(left, right) || left_arity <= right_arity)
continue; swap(order[i], order[j]); changed = true; break;
} if (changed) break; }
} } void order_zero_argument_constructors_before_local_ctors( const vector<FunctionOut>& functions, vector<size_t>& order)
{ size_t i = 0; while (i + 1 < order.size()) {
if (output_local_class_constructor(functions[order[i]]) && output_zero_argument_nonlocal_constructor(functions[order[i + 1]])) { swap(order[i], order[i + 1]);
if (i != 0) --i; continue; }
++i; } } bool emitted_function_is_readable_template_record_member(const string& name)
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
}  // namespace
vector<size_t> ordered_function_indices(const ProgramLowerer& program) { vector<size_t> order; bool has_template_record_function = false;
bool has_abi_template_vtable = false; for (size_t i = 0; i < program.globals.size(); ++i) if (program.globals[i].find("global @__vtable_type_") != string::npos) has_abi_template_vtable = true;
for (size_t i = 0; i < program.functions.size(); ++i) { order.push_back(i); string name = function_out_name(program.functions[i]);
if (name.compare(0, 5, "type_") == 0 || (has_abi_template_vtable && emitted_function_is_readable_template_record_member(name))) has_template_record_function = true;
} if (has_template_record_function) stable_sort(order.begin(), order.end(), [&program, has_abi_template_vtable](size_t lhs, size_t rhs) {
int lkey = emitted_template_member_order_key( program.functions[lhs], has_abi_template_vtable); int rkey = emitted_template_member_order_key( program.functions[rhs], has_abi_template_vtable);
return lkey != rkey ? lkey < rkey : lhs < rhs; }); bool has_template_pointer_constructor = false; bool has_template_reference_constructor = false;
bool has_template_record_plus = false; bool has_template_minus = false; for (size_t i = 0; i < order.size(); ++i) {
int key = emitted_template_dependency_order_key( program.functions[order[i]]); if (key == 100) has_template_pointer_constructor = true;
else if (key == 300 || key == 500) has_template_reference_constructor = true; else if (key == 200) has_template_record_plus = true;
else if (key == 400) has_template_minus = true; } bool has_template_dependency_function =
has_template_pointer_constructor && has_template_reference_constructor && has_template_record_plus && has_template_minus;
if (has_template_dependency_function) stable_sort(order.begin(), order.end(), [&program](size_t lhs, size_t rhs) { int lkey = emitted_template_dependency_order_key(
program.functions[lhs]); int rkey = emitted_template_dependency_order_key( program.functions[rhs]); return lkey != rkey ? lkey < rkey : lhs < rhs;
}); order_local_template_members_by_rank(program, order); order_outer_class_lifecycle(program.functions, order); order_record_return_before_zero_constructor(program.functions, order);
order_by_value_record_member_before_zero_constructor(program.functions, order); order_record_return_call_operator_before_zero_constructor(program.functions, order); order_zero_constructor_before_namespace_record_return(program.functions, order); order_namespace_record_return_after_zero_constructor(program.functions, order);
order_nonzero_constructor_before_owner_helpers(program.functions, order); order_by_value_constructor_before_record_constructor_dependencies(program.functions, order); order_owner_constructor_before_template_constructor_dependency(program.functions, order); order_scalar_member_after_owner_record_dependencies(program.functions, order);
order_derived_members_before_inherited_constructor_wrappers(program.functions, order); order_base_entries_after_derived_template_users(program.functions, order); order_local_template_call_flow_functions(program.functions, order); order_template_conversion_flow_functions(program.functions, order);
order_same_owner_constructors_by_arity(program.functions, order); order_zero_argument_constructors_before_local_ctors(program.functions, order); order_by_value_conversion_after_parameter_default(program.functions, order); order_record_result_pointer_member_flow(program.functions, order);
order_local_template_call_flow_functions(program.functions, order); order_template_and_lambda_callees_after_callers(program.functions, order); order_pointer_reference_helpers_before_lambda_callers(program.functions, order); order_class_pointer_helpers_before_value_pointer_constructors(program.functions, order);
order_class_pointer_helpers_by_arity(program.functions, order); order_invoked_functor_after_template_invoke(program.functions, order); order_callable_thunk_flow_functions(program.functions, order); order_template_dependency_flow_functions(program.functions, order);
order_operator_functions_by_key(program.functions, order); order_static_template_member_depth_functions(program.functions, order); order_assignment_helper_flow_functions(program.functions, order); order_assignment_operator_before_owner_zero_constructor(program.functions, order);
order_same_owner_constructor_before_assignment_operator(program.functions, order); order_same_owner_call_operator_before_unreferenced_zero_constructor(program.functions, order); order_local_constructor_before_same_owner_call_operator(program.functions, order); order_static_member_overload_callees_after_callers(program.functions, order); order_static_template_member_callees_after_callers(program.functions, order); order_static_template_owner_callees_after_callers(program.functions, order);
order_template_owner_constructor_callees_after_callers(program.functions, order); order_same_owner_template_member_callees_after_callers(program.functions, order); order_template_owner_member_callees_after_callers(program.functions, order); order_value_template_callees_after_callers(program.functions, order);
order_class_pointer_helpers_before_value_pointer_constructors(program.functions, order); order_template_dependency_flow_functions(program.functions, order); order_by_value_record_member_before_zero_constructor(program.functions, order); order_preemitted_referenced_callees_after_callers(program.functions, order);
order_class_pointer_helpers_before_value_pointer_constructors(program.functions, order); order_class_pointer_helpers_by_arity(program.functions, order); order_assignment_operator_before_owner_zero_constructor(program.functions, order); order_template_scalar_members_before_assignments(program.functions, order);
order_conversion_after_compound_assignment(program.functions, order); order_template_owner_call_operator_callees_after_callers(program.functions, order); order_template_reference_constructors_before_foreign_call_operators(program.functions, order); order_lambda_call_operators_by_rank(program, order);
order_lambda_callees_after_callers(program.functions, order); order_pointer_reference_helpers_before_lambda_callers(program.functions, order); order_range_for_operator_functions_by_key(program.functions, order); order_template_reference_constructors_before_foreign_call_operators(program.functions, order);
order_assignment_operator_before_owner_zero_constructor(program.functions, order); order_template_dependency_flow_functions(program.functions, order); order_same_owner_constructor_before_assignment_operator(program.functions, order); order_same_owner_call_operator_before_unreferenced_zero_constructor(program.functions, order); order_local_constructor_before_same_owner_call_operator(program.functions, order); order_value_constructors_after_scalar_template_helpers(program.functions, order); if (has_abi_template_vtable && has_template_record_function)
stable_sort(order.begin(), order.end(), [&program, has_abi_template_vtable](size_t lhs, size_t rhs) { int lkey = emitted_template_member_order_key(
program.functions[lhs], has_abi_template_vtable); int rkey = emitted_template_member_order_key( program.functions[rhs],
has_abi_template_vtable); return lkey != rkey ? lkey < rkey : lhs < rhs; }); size_t run = 0;
while (run < order.size()) { if (!emitted_function_is_operator(program.functions[order[run]])) {
++run; continue; } size_t end = run + 1;
while (end < order.size() && emitted_function_is_operator(program.functions[order[end]])) ++end; if (emitted_operator_run_needs_sort(program.functions, order, run, end))
{ bool subscript_only = true; for (size_t i = run; i < end; ++i) if (function_out_name(program.functions[order[i]])
.find("operator_lb_rb") == string::npos) subscript_only = false; stable_sort(order.begin() + run, order.begin() + end, [&program, subscript_only](size_t lhs, size_t rhs) {
int lkey = emitted_function_order_key(program.functions[lhs]); int rkey = emitted_function_order_key(program.functions[rhs]); if (lkey != rkey) return lkey < rkey;
return subscript_only ? function_out_name(program.functions[lhs]) < function_out_name(program.functions[rhs]) : lhs < rhs;
}); } run = end; }
	order_member_template_lambda_breadth_functions(program.functions, order);
	stable_sort(order.begin(), order.end(), [&program](size_t lhs, size_t rhs) {
	const Binding* lb = program.functions[lhs].binding; const Binding* rb = program.functions[rhs].binding;
	bool lgen = lb != NULL && lb->is_generated_aggregate_constructor;
	bool rgen = rb != NULL && rb->is_generated_aggregate_constructor;
	return lgen != rgen ? !lgen : false;
	}); return order; }
}  // namespace internal
}  // namespace pa14
