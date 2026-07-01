#include "pa14_lowir_function_order_shared.h"
#include <algorithm>
#include <cctype>

namespace pa14 {
namespace internal {
namespace {
map<const Binding*, bool>& early_class_constructor_cache()
{
	static map<const Binding*, bool> cache;
	return cache;
}
map<const Binding*, bool>& early_class_member_local_cache()
{
	static map<const Binding*, bool> cache;
	return cache;
}
map<const Binding*, TypePtr>& early_owner_record_cache()
{
	static map<const Binding*, TypePtr> cache;
	return cache;
}
map<pair<const pa11::Type*, const pa11::Type*>, bool>&
early_type_mentions_record_cache()
{
	static map<pair<const pa11::Type*, const pa11::Type*>, bool> cache;
	return cache;
}
map<const Binding*, bool>& early_lambda_related_cache()
{
	static map<const Binding*, bool> cache;
	return cache;
}
}  // namespace
int output_template_conversion_flow_key(const FunctionOut& fn) { const Binding* binding = fn.binding;
if (binding == NULL || !binding_has_template_specialization_context(binding) || !output_function_template_specialization(binding)) return 0;
if (binding->name.compare(0, 9, "operator ") == 0 && output_function_returns_record(binding)) return 1; if (output_class_constructor(binding) &&
output_has_by_value_record_parameter(binding)) return 2; if (binding->name == "operator=" && output_has_by_value_record_parameter(binding))
return 3; return 0; } void order_template_conversion_flow_functions(const vector<FunctionOut>& functions,
vector<size_t>& order) { bool has_conversion = false; bool has_constructor = false;
bool has_assignment = false; vector<size_t> positions; for (size_t i = 0; i < order.size(); ++i) {
int key = output_template_conversion_flow_key(functions[order[i]]); if (key == 0) continue; positions.push_back(i);
has_conversion = has_conversion || key == 1; has_constructor = has_constructor || key == 2; has_assignment = has_assignment || key == 3; }
if (!has_conversion || !has_constructor || !has_assignment) return; vector<size_t> selected; for (size_t i = 0; i < positions.size(); ++i)
selected.push_back(order[positions[i]]); local_stable_sort(selected, [&functions](size_t lhs, size_t rhs) { int lkey = output_template_conversion_flow_key(functions[lhs]);
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
for (size_t i = 0; i < positions.size(); ++i) selected.push_back(order[positions[i]]); local_stable_sort(selected, [&program](size_t lhs, size_t rhs) {
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
	}
void order_template_dependency_flow_functions(const vector<FunctionOut>& functions,
                                              vector<size_t>& order)
{
	vector<int> keys(functions.size(), 0);
	bool has_template_pointer_constructor = false;
	bool has_template_reference_constructor = false;
	bool has_template_record_plus = false;
	bool has_template_minus = false;
	for (size_t i = 0; i < order.size(); ++i)
	{
		size_t index = order[i];
		int key = output_template_dependency_flow_key(functions[index]);
		keys[index] = key;
		if (key == 100)
			has_template_pointer_constructor = true;
		else if (key == 300 || key == 500)
			has_template_reference_constructor = true;
		else if (key == 200)
			has_template_record_plus = true;
		else if (key == 400)
			has_template_minus = true;
	}
	if (!has_template_pointer_constructor ||
	    !has_template_reference_constructor ||
	    !has_template_record_plus ||
	    !has_template_minus)
		return;
	local_stable_sort(order, [&keys](size_t lhs, size_t rhs) {
		int lkey = keys[lhs];
		int rkey = keys[rhs];
		return lkey != rkey ? lkey < rkey : lhs < rhs;
	});
}
bool output_class_constructor(const Binding* binding) {
map<const Binding*, bool>& cached = early_class_constructor_cache(); if (binding == NULL) return false; map<const Binding*, bool>::const_iterator found = cached.find(binding);
if (found != cached.end()) return found->second; bool result = false;
if (binding->owner != NULL && binding->owner->kind == ScopeKind::Class && binding->type.get() != NULL &&
binding->type->kind == TypeKind::Function) {
if (binding->name == binding->owner->name) result = true; else {
TypePtr record = pa11::record_type_for_scope(binding->owner); record = record.get() != NULL ? pa11::strip_cv(record) : TypePtr(); if (record.get() != NULL && record->kind == TypeKind::Record) {
if (!record->template_primary_name.empty() && binding->name == record->template_primary_name) result = true; else { string record_name = record->name;
size_t args = record_name.find('<'); if (args != string::npos) record_name = record_name.substr(0, args); result = record->is_template_specialization && binding->name == record_name; } } } }
cached[binding] = result; return result;
} bool output_class_member_of_local_class(const Binding* binding) { map<const Binding*, bool>& cached = early_class_member_local_cache(); map<const Binding*, bool>::const_iterator found = cached.find(binding); if (found != cached.end()) return found->second; if (binding == NULL || binding->owner == NULL)
{ cached[binding] = false; return false; } for (Scope* scope = binding->owner; scope != NULL; scope = scope->parent) { if (scope->kind == ScopeKind::Function)
{ cached[binding] = true; return true; } if (scope->kind == ScopeKind::Namespace) { cached[binding] = false; return false; } }
cached[binding] = false; return false; } bool output_base_entry_function(const FunctionOut& fn) {
return function_out_name(fn).find("__base_entry") != string::npos; } TypePtr output_owner_record(const Binding* binding) {
map<const Binding*, TypePtr>& cached_owner = early_owner_record_cache(); map<const Binding*, TypePtr>::const_iterator found_owner = cached_owner.find(binding); if (found_owner != cached_owner.end()) return found_owner->second;
if (binding == NULL || binding->owner == NULL || binding->owner->kind != ScopeKind::Class) { cached_owner[binding] = TypePtr(); return TypePtr(); } TypePtr record = pa11::record_type_for_scope(binding->owner);
record = record.get() != NULL ? pa11::strip_cv(record) : TypePtr(); TypePtr owner_record = record.get() != NULL && record->kind == TypeKind::Record ? record : TypePtr(); cached_owner[binding] = owner_record; return owner_record; }
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
output_collect_local_records(type->parameters[i], records); } bool output_type_mentions_record_uncached(TypePtr type, TypePtr record);
bool output_type_mentions_record(TypePtr type, TypePtr record) {
type = type.get() != NULL ? pa11::strip_cv(type) : TypePtr(); record = record.get() != NULL ? pa11::strip_cv(record) : TypePtr();
if (type.get() == NULL || record.get() == NULL) return false; map<pair<const pa11::Type*, const pa11::Type*>, bool>& cached = early_type_mentions_record_cache();
pair<const pa11::Type*, const pa11::Type*> key = make_pair(type.get(), record.get()); map<pair<const pa11::Type*, const pa11::Type*>, bool>::const_iterator found = cached.find(key);
if (found != cached.end()) return found->second; bool result = output_type_mentions_record_uncached(type, record); cached[key] = result; return result; }
bool output_type_mentions_record_uncached(TypePtr type, TypePtr record) {
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
void order_outer_class_lifecycle(const vector<FunctionOut>& functions, vector<size_t>& order) {
map<Scope*, vector<size_t> > positions_by_outer; vector<int> keys(functions.size(), 0);
for (size_t i = 0; i < order.size(); ++i) { size_t fn_index = order[i]; const Binding* binding = functions[fn_index].binding; Scope* outer = output_outer_class_scope(binding); int key = output_outer_lifecycle_key(functions[fn_index]);
if (outer == NULL || key == 0) continue; positions_by_outer[outer].push_back(i); keys[fn_index] = key; }
for (map<Scope*, vector<size_t> >::iterator group = positions_by_outer.begin(); group != positions_by_outer.end(); ++group) {
if (group->second.size() < 2) continue; vector<size_t> selected; selected.reserve(group->second.size());
for (size_t i = 0; i < group->second.size(); ++i) selected.push_back(order[group->second[i]]);
local_stable_sort(selected, [&keys](size_t lhs, size_t rhs) { int lkey = keys[lhs]; int rkey = keys[rhs]; return lkey != rkey ? lkey < rkey : false; });
for (size_t i = 0; i < group->second.size(); ++i) order[group->second[i]] = selected[i]; } }
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
} bool output_lambda_related_binding(const Binding* binding) {
map<const Binding*, bool>& cache = early_lambda_related_cache();
map<const Binding*, bool>::const_iterator found = cache.find(binding);
if (found != cache.end()) return found->second;
bool result = false;
if (binding != NULL) {
if (binding->name.compare(0, 8, "__lambda") == 0) result = true;
else result = binding->owner != NULL &&
binding->owner->kind == ScopeKind::Class && binding->owner->name.compare(0, 8, "__lambda") == 0;
}
cache[binding] = result;
return result;
} bool output_lambda_related_function(const FunctionOut& fn)
{ if (!fn.lambda_related_collected) {
fn.lambda_related_cached = output_lambda_related_binding(fn.binding) || function_out_name(fn).compare(0, 8, "__lambda") == 0;
fn.lambda_related_collected = true;
}
return fn.lambda_related_cached; }
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
{ vector<bool> ctor_like(functions.size(), false); vector<TypePtr> first_this(functions.size()); vector<TypePtr> by_value_param(functions.size()); vector<vector<TypePtr> > record_params(functions.size());
for (size_t f = 0; f < functions.size(); ++f) { const Binding* binding = functions[f].binding; ctor_like[f] = output_constructor_like_binding(binding); if (!ctor_like[f]) continue; first_this[f] = output_first_this_record(binding); by_value_param[f] = output_constructor_record_parameter(binding, true);
if (binding->type.get() != NULL && binding->type->kind == TypeKind::Function) for (size_t p = 1; p < binding->type->parameters.size(); ++p) { TypePtr param = pa11::strip_cv(object_type(binding->type->parameters[p])); if (param.get() != NULL && param->kind == TypeKind::Record) record_params[f].push_back(param); } }
auto constructor_has_param = [&](size_t f, TypePtr record) { if (record.get() == NULL) return false; TypePtr bare_record = pa11::strip_cv(record); for (size_t p = 0; p < record_params[f].size(); ++p) if (pa11::same_type(bare_record, record_params[f][p])) return true; return false; };
bool changed = true; for (size_t guard = 0; changed && guard < order.size() * order.size() + 1; ++guard) {
changed = false; for (size_t i = 0; i < order.size(); ++i) { size_t left_index = order[i]; if (!ctor_like[left_index]) continue; for (size_t j = i + 1; j < order.size(); ++j) {
size_t right_index = order[j]; TypePtr right_param = by_value_param[right_index]; if (right_param.get() == NULL)
continue; TypePtr left_by_value = by_value_param[left_index]; if (left_by_value.get() != NULL &&
pa11::same_type(pa11::strip_cv(left_by_value), pa11::strip_cv(right_param))) continue; TypePtr left_record = first_this[left_index];
bool left_constructs_param = left_record.get() != NULL && pa11::same_type(pa11::strip_cv(left_record), pa11::strip_cv(right_param));
if (!left_constructs_param && !constructor_has_param(left_index, right_param)) continue; swap(order[i], order[j]);
changed = true; break; } if (changed)
break; } } }
bool output_constructor_owner_template_specialization(const Binding* binding) { if (!output_constructor_like_binding(binding)) return false;
TypePtr record = output_first_this_record(binding); record = record.get() != NULL ? pa11::strip_cv(record) : TypePtr(); return record.get() != NULL && record->kind == TypeKind::Record &&
record->is_template_specialization; }

void collect_constructor_record_parameters(const Binding* binding,
                                           vector<TypePtr>& out)
{
	if (binding == NULL ||
	    binding->type.get() == NULL ||
	    binding->type->kind != TypeKind::Function)
		return;
	for (size_t i = 1; i < binding->type->parameters.size(); ++i)
	{
		TypePtr param =
			pa11::strip_cv(object_type(binding->type->parameters[i]));
		if (param.get() != NULL && param->kind == TypeKind::Record)
			out.push_back(param);
	}
}

bool record_list_contains(const vector<TypePtr>& records, TypePtr record)
{
	if (record.get() == NULL)
		return false;
	for (size_t i = 0; i < records.size(); ++i)
		if (output_same_record(records[i], record))
			return true;
	return false;
}

void order_owner_constructor_before_template_constructor_dependency(
	const vector<FunctionOut>& functions,
	vector<size_t>& order)
{
	vector<bool> constructor_like(functions.size(), false);
	vector<bool> owner_template(functions.size(), false);
	vector<bool> has_by_value_record_param(functions.size(), false);
	vector<TypePtr> first_record_param(functions.size());
	vector<vector<TypePtr> > record_params(functions.size());

	for (size_t i = 0; i < functions.size(); ++i)
	{
		const Binding* binding = functions[i].binding;
		constructor_like[i] = output_constructor_like_binding(binding);
		if (!constructor_like[i])
			continue;
		owner_template[i] =
			output_constructor_owner_template_specialization(binding);
		first_record_param[i] =
			output_constructor_record_parameter(binding, false);
		has_by_value_record_param[i] =
			output_constructor_record_parameter(binding, true).get() != NULL;
		collect_constructor_record_parameters(binding, record_params[i]);
	}

	bool changed = true;
	for (size_t guard = 0;
	     changed && guard < order.size() * order.size() + 1;
	     ++guard)
	{
		changed = false;
		for (size_t i = 0; i < order.size(); ++i)
		{
			size_t left_index = order[i];
			TypePtr left_param = first_record_param[left_index];
			if (left_param.get() == NULL ||
			    has_by_value_record_param[left_index] ||
			    !owner_template[left_index])
				continue;
			for (size_t j = i + 1; j < order.size(); ++j)
			{
				size_t right_index = order[j];
				if (!constructor_like[right_index] ||
				    owner_template[right_index] ||
				    !record_list_contains(record_params[right_index],
				                          left_param))
					continue;
				swap(order[i], order[j]);
				changed = true;
				break;
			}
			if (changed)
				break;
		}
	}
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
for (size_t i = 0; i < positions.size(); ++i) selected.push_back(order[positions[i]]); local_stable_sort(selected, [&functions, caller](size_t lhs, size_t rhs) {
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
const vector<FunctionOut>& functions, vector<size_t>& order) { set<const pa11::Type*> seen_records; for (size_t i = 0; i < order.size(); ++i) {
TypePtr record = output_function_record_result(functions[order[i]].binding); if (record.get() == NULL) continue;
if (seen_records.find(record.get()) != seen_records.end()) continue; seen_records.insert(record.get());
vector<size_t> positions; map<size_t, int> keys; bool has_pointer_member = false; bool has_constructor = false; for (size_t j = 0; j < order.size(); ++j)
{ size_t index = order[j]; int key = output_record_result_flow_key( functions[index], record); if (key == 0)
continue; positions.push_back(j); has_pointer_member = has_pointer_member || key == 1; has_constructor = has_constructor || key == 3;
keys[index] = key;
} if (positions.size() < 2 || !has_pointer_member || !has_constructor) continue; vector<size_t> selected;
for (size_t j = 0; j < positions.size(); ++j) selected.push_back(order[positions[j]]); local_stable_sort(selected, [&keys](size_t lhs, size_t rhs) {
int lkey = keys.find(lhs)->second; int rkey = keys.find(rhs)->second;
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
for (size_t i = 0; i < positions.size(); ++i) selected.push_back(order[positions[i]]); local_stable_sort(selected, [&functions, has_range_for_state](size_t lhs, size_t rhs) {
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
vector<size_t> selected; for (size_t i = 0; i < positions.size(); ++i) selected.push_back(order[positions[i]]); local_stable_sort(selected,
[&functions](size_t lhs, size_t rhs) { int lkey = emitted_function_order_key(functions[lhs]); int rkey = emitted_function_order_key(functions[rhs]); return lkey != rkey ? lkey < rkey : false;
}); for (size_t i = 0; i < positions.size(); ++i) order[positions[i]] = selected[i]; }
bool output_symbol_reference_matches(const string& instr, const string& symbol) { string needle = "@" + symbol;
size_t pos = instr.find(needle); if (pos == string::npos) return false; size_t end = pos + needle.size();
if (end >= instr.size()) return true; char ch = instr[end]; return !(isalnum(static_cast<unsigned char>(ch)) || ch == '_' || ch == '$');
} void collect_output_symbol_reference_positions(const FunctionOut& fn) {
if (fn.reference_positions_collected) return; size_t ordinal = 0; for (size_t i = 0; i < fn.blocks.size(); ++i) for (size_t j = 0; j < fn.blocks[i].instrs.size(); ++j) {
const string& instr = fn.blocks[i].instrs[j]; size_t scan = 0; while (scan < instr.size()) { size_t at = instr.find('@', scan); if (at == string::npos) break; size_t begin = at + 1;
size_t end = begin; while (end < instr.size()) { unsigned char ch = static_cast<unsigned char>(instr[end]); if (!isalnum(ch) && instr[end] != '_' && instr[end] != '$') break; ++end; }
if (end > begin) { string symbol = instr.substr(begin, end - begin); fn.referenced_symbols.insert(symbol); if (fn.referenced_symbol_positions.find(symbol) == fn.referenced_symbol_positions.end()) fn.referenced_symbol_positions[symbol] = ordinal; scan = end; } else scan = begin; } ++ordinal; }
fn.reference_symbols_collected = true; fn.reference_positions_collected = true;
} bool output_function_references_symbol(const FunctionOut& fn, const string& symbol) {
collect_output_symbol_reference_positions(fn); return fn.referenced_symbols.find(symbol) != fn.referenced_symbols.end(); } size_t output_function_reference_position(const FunctionOut& fn,
const string& symbol) { collect_output_symbol_reference_positions(fn); map<string, size_t>::const_iterator found = fn.referenced_symbol_positions.find(symbol); return found != fn.referenced_symbol_positions.end() ? found->second : static_cast<size_t>(-1); } void collect_output_symbol_reference_positions(const FunctionOut& fn,
map<string, size_t>& positions) { collect_output_symbol_reference_positions(fn); positions = fn.referenced_symbol_positions; } bool output_referenced_callee_order_candidate_cached(
const vector<bool>& order_functions, const vector<string>& names, const vector<map<string, size_t> >& references,
size_t caller_index, size_t callee_index, size_t& reference_position) { if (!order_functions[caller_index] || !order_functions[callee_index])
return false; const string& caller_name = names[caller_index]; const string& callee_name = names[callee_index];
if (callee_name.empty() || caller_name == callee_name) return false;
if (references[callee_index].find(caller_name) != references[callee_index].end()) return false;
map<string, size_t>::const_iterator found = references[caller_index].find(callee_name); if (found == references[caller_index].end())
return false; reference_position = found->second; return true; } bool output_template_or_local_order_function(const FunctionOut& fn)
{ return output_lambda_related_function(fn) || output_function_template_specialization(fn.binding) || binding_has_template_specialization_context(fn.binding) ||
output_owner_template_specialization(fn.binding) || output_class_member_of_local_class(fn.binding); }
void order_preemitted_referenced_callees_after_callers( const vector<FunctionOut>& functions, vector<size_t>& order) {
vector<string> names(functions.size()); vector<bool> order_functions(functions.size(), false);
vector<map<string, size_t> > references(functions.size()); for (size_t i = 0; i < functions.size(); ++i)
{ names[i] = function_out_name(functions[i]); order_functions[i] = output_template_or_local_order_function(functions[i]);
if (order_functions[i]) collect_output_symbol_reference_positions(functions[i], references[i]); }
map<string, vector<size_t> > symbol_indices; for (size_t i = 0; i < names.size(); ++i)
if (!names[i].empty()) symbol_indices[names[i]].push_back(i);
vector<vector<pair<size_t, size_t> > > referenced_callees(functions.size());
for (size_t caller = 0; caller < functions.size(); ++caller) {
if (!order_functions[caller]) continue; const string& caller_name = names[caller];
for (map<string, size_t>::const_iterator ref = references[caller].begin(); ref != references[caller].end(); ++ref) {
map<string, vector<size_t> >::const_iterator found = symbol_indices.find(ref->first); if (found == symbol_indices.end()) continue;
for (size_t ci = 0; ci < found->second.size(); ++ci) { size_t callee = found->second[ci];
if (callee == caller || !order_functions[callee]) continue;
if (references[callee].find(caller_name) != references[callee].end()) continue;
referenced_callees[caller].push_back(make_pair(callee, ref->second)); } } }
vector<size_t> current_position(functions.size(), static_cast<size_t>(-1));
for (size_t guard = 0; guard < order.size(); ++guard) {
bool changed = false;
fill(current_position.begin(), current_position.end(), static_cast<size_t>(-1));
for (size_t i = 0; i < order.size(); ++i) current_position[order[i]] = i;
for (size_t i = 0; i < order.size(); ++i) { size_t caller_index = order[i];
const vector<pair<size_t, size_t> >& edges = referenced_callees[caller_index]; if (edges.empty()) continue;
vector<size_t> selected; map<size_t, size_t> selected_positions; bool has_preemitted = false;
for (size_t e = 0; e < edges.size(); ++e) { size_t callee = edges[e].first; size_t pos = current_position[callee];
if (pos == static_cast<size_t>(-1)) continue; selected.push_back(callee); selected_positions[callee] = edges[e].second;
if (pos < i) has_preemitted = true; } if (!has_preemitted) continue;
local_stable_sort(selected, [&selected_positions, &current_position](size_t lhs, size_t rhs) {
size_t lpos = selected_positions.find(lhs)->second; size_t rpos = selected_positions.find(rhs)->second;
if (lpos != rpos) return lpos < rpos; return current_position[lhs] < current_position[rhs]; });
vector<bool> selected_function(functions.size(), false); for (size_t j = 0; j < selected.size(); ++j) selected_function[selected[j]] = true;
vector<size_t> rebuilt; rebuilt.reserve(order.size()); size_t insert_pos = static_cast<size_t>(-1);
for (size_t j = 0; j < order.size(); ++j) { size_t fn = order[j]; if (selected_function[fn]) continue;
rebuilt.push_back(fn); if (fn == caller_index) insert_pos = rebuilt.size(); }
if (insert_pos == static_cast<size_t>(-1)) insert_pos = rebuilt.size();
rebuilt.insert(rebuilt.begin() + insert_pos, selected.begin(), selected.end()); order.swap(rebuilt);
changed = true; break; } if (!changed) break; }
}
void order_referenced_template_constructors_by_call_position(
	const vector<FunctionOut>& functions,
	vector<size_t>& order)
{
	vector<string> names(functions.size());
	vector<bool> order_functions(functions.size(), false);
	vector<map<string, size_t> > references(functions.size());
	vector<string> constructor_families(functions.size());
	map<string, vector<size_t> > symbol_indices;
	for (size_t i = 0; i < functions.size(); ++i)
	{
		names[i] = function_out_name(functions[i]);
		if (!names[i].empty())
			symbol_indices[names[i]].push_back(i);
		order_functions[i] = output_template_or_local_order_function(
			functions[i]);
		if (order_functions[i])
			collect_output_symbol_reference_positions(functions[i],
			                                          references[i]);
		if (order_functions[i] &&
		    output_constructor_like_binding(functions[i].binding))
			constructor_families[i] =
				output_constructor_owner_family(functions[i].binding);
	}
	vector<size_t> current_position(functions.size(),
	                                static_cast<size_t>(-1));
	for (size_t caller_pos = 0; caller_pos < order.size(); ++caller_pos)
	{
		fill(current_position.begin(),
		     current_position.end(),
		     static_cast<size_t>(-1));
		for (size_t i = 0; i < order.size(); ++i)
			current_position[order[i]] = i;
		size_t caller_index = order[caller_pos];
		if (!order_functions[caller_index] ||
		    references[caller_index].empty())
			continue;
		map<string, vector<pair<size_t, size_t> > > callees_by_family;
		for (map<string, size_t>::const_iterator ref =
			     references[caller_index].begin();
		     ref != references[caller_index].end();
		     ++ref)
		{
			map<string, vector<size_t> >::const_iterator found =
				symbol_indices.find(ref->first);
			if (found == symbol_indices.end())
				continue;
			for (size_t i = 0; i < found->second.size(); ++i)
			{
				size_t callee = found->second[i];
				if (callee == caller_index ||
				    constructor_families[callee].empty() ||
				    current_position[callee] ==
					    static_cast<size_t>(-1) ||
				    references[callee].find(names[caller_index]) !=
					    references[callee].end())
					continue;
				callees_by_family[constructor_families[callee]]
					.push_back(make_pair(callee, ref->second));
			}
		}
		for (map<string, vector<pair<size_t, size_t> > >::iterator group =
			     callees_by_family.begin();
		     group != callees_by_family.end();
		     ++group)
		{
			vector<pair<size_t, size_t> >& selected = group->second;
			if (selected.size() < 2)
				continue;
			local_stable_sort(selected,
			            [](const pair<size_t, size_t>& lhs,
			               const pair<size_t, size_t>& rhs) {
				            return lhs.second != rhs.second
				                   ? lhs.second < rhs.second
				                   : false;
			            });
			vector<size_t> positions;
			for (size_t i = 0; i < selected.size(); ++i)
				positions.push_back(current_position[selected[i].first]);
			local_stable_sort(positions, [](size_t lhs, size_t rhs) { return lhs < rhs; });
			bool same = true;
			for (size_t i = 0; i < selected.size(); ++i)
				if (order[positions[i]] != selected[i].first)
				{
					same = false;
					break;
				}
			if (same)
				continue;
			for (size_t i = 0; i < selected.size(); ++i)
				order[positions[i]] = selected[i].first;
			break;
		}
	}
}
bool output_template_or_lambda_follow_edge(const FunctionOut& caller, const FunctionOut& callee) {
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

void clear_lowir_function_order_early_caches()
{
	early_class_constructor_cache().clear();
	early_class_member_local_cache().clear();
	early_owner_record_cache().clear();
	early_type_mentions_record_cache().clear();
	early_lambda_related_cache().clear();
}

}  // namespace internal
}  // namespace pa14
