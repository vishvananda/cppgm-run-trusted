#include "pa14_lowir_function_order_shared.h"
#include <algorithm>
#include <cctype>

namespace pa14 {
namespace internal {
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

bool output_pointer_reference_template_helper(const FunctionOut& fn)
{
	const Binding* binding = fn.binding;
	return binding != NULL &&
	       !output_constructor_like_binding(binding) &&
	       !is_class_destructor_binding(binding) &&
	       output_function_out_returns_pointer(fn) &&
	       output_has_reference_parameter(binding) &&
	       output_template_or_local_order_function(fn);
}

bool output_constructor_should_follow_pointer_helper(const FunctionOut& ctor_fn,
                                                     const FunctionOut& helper)
{
	const Binding* ctor = ctor_fn.binding;
	const Binding* helper_binding = helper.binding;
	if (!output_constructor_like_binding(ctor) ||
	    output_base_entry_function(ctor_fn) ||
	    !output_pointer_reference_template_helper(helper))
		return false;
	bool local_constructor = output_local_class_constructor(ctor_fn);
	bool reference_constructor = output_has_reference_parameter(ctor);
	if (!local_constructor && !reference_constructor)
		return false;
	string helper_name = function_out_name(helper);
	if (!helper_name.empty() &&
	    output_function_references_symbol(ctor_fn, helper_name))
		return true;
	TypePtr owner = output_owner_record(ctor);
	if (local_constructor &&
	    output_function_mentions_record(helper_binding, owner))
		return true;
	if (reference_constructor)
	{
		TypePtr param = output_constructor_record_parameter(ctor, false);
		if (output_function_mentions_record(helper_binding, param))
			return true;
	}
	return false;
}

void order_constructors_after_pointer_reference_helpers(
	const vector<FunctionOut>& functions,
	vector<size_t>& order)
{
	vector<bool> pointer_reference_helper(functions.size(), false);
	vector<string> helper_names(functions.size());
	for (size_t i = 0; i < functions.size(); ++i)
	{
		pointer_reference_helper[i] =
			output_pointer_reference_template_helper(functions[i]);
		if (pointer_reference_helper[i])
			helper_names[i] = function_out_name(functions[i]);
	}
	vector<vector<size_t> > follow_helpers(functions.size());
	for (size_t i = 0; i < functions.size(); ++i)
	{
		const FunctionOut& ctor_fn = functions[i];
		const Binding* ctor = ctor_fn.binding;
		if (!output_constructor_like_binding(ctor) ||
		    output_base_entry_function(ctor_fn))
			continue;
		bool local_constructor = output_local_class_constructor(ctor_fn);
		bool reference_constructor = output_has_reference_parameter(ctor);
		if (!local_constructor && !reference_constructor)
			continue;
		TypePtr owner =
			local_constructor ? output_owner_record(ctor) : TypePtr();
		TypePtr param =
			reference_constructor
			? output_constructor_record_parameter(ctor, false)
			: TypePtr();
		for (size_t j = 0; j < functions.size(); ++j)
		{
			if (i == j || !pointer_reference_helper[j])
				continue;
			const Binding* helper_binding = functions[j].binding;
			if (!helper_names[j].empty() &&
			    output_function_references_symbol(ctor_fn,
			                                      helper_names[j]))
			{
				follow_helpers[i].push_back(j);
				continue;
			}
			if (local_constructor &&
			    output_function_mentions_record(helper_binding, owner))
			{
				follow_helpers[i].push_back(j);
				continue;
			}
			if (reference_constructor &&
			    output_function_mentions_record(helper_binding, param))
				follow_helpers[i].push_back(j);
		}
	}
	vector<size_t> current_position(functions.size(),
	                                static_cast<size_t>(-1));
	bool changed = true;
	for (size_t guard = 0; changed && guard < order.size() * order.size() + 1;
	     ++guard)
	{
		changed = false;
		fill(current_position.begin(),
		     current_position.end(),
		     static_cast<size_t>(-1));
		for (size_t i = 0; i < order.size(); ++i)
			current_position[order[i]] = i;
		for (size_t i = 0; i < order.size(); ++i)
		{
			size_t fn_index = order[i];
			const vector<size_t>& helpers = follow_helpers[fn_index];
			size_t move_after_position = i;
			bool should_move = false;
			for (size_t j = 0; j < helpers.size(); ++j)
			{
				size_t helper_position = current_position[helpers[j]];
				if (helper_position == static_cast<size_t>(-1) ||
				    helper_position <= move_after_position)
					continue;
				move_after_position = helper_position;
				should_move = true;
			}
			if (!should_move)
				continue;
			order.erase(order.begin() + i);
			order.insert(order.begin() + move_after_position, fn_index);
			changed = true;
			if (changed)
				break;
		}
	}
}

size_t output_function_parameter_count(const Binding* binding) { return binding != NULL && binding->type.get() != NULL &&
binding->type->kind == TypeKind::Function ? binding->type->parameters.size() : 0; } void order_class_pointer_helpers_by_arity(const vector<FunctionOut>& functions,
vector<size_t>& order) { vector<size_t> positions; for (size_t i = 0; i < order.size(); ++i)
if (output_class_owned_pointer_helper(functions[order[i]].binding)) positions.push_back(i); if (positions.size() < 2) return;
vector<size_t> selected; for (size_t i = 0; i < positions.size(); ++i) selected.push_back(order[positions[i]]); local_stable_sort(selected,
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
selected.push_back(order[positions[j]]); local_stable_sort(selected, [&functions, owner](size_t lhs, size_t rhs) { int lkey = output_callable_thunk_flow_key(
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
selected.push_back(order[positions[j]]); local_stable_sort(selected, [&functions](size_t lhs, size_t rhs) { int lkey = output_static_template_member_depth_key(
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
local_stable_sort(selected, [&functions, assignment, parameter_record]( size_t lhs, size_t rhs) { int lkey = output_assignment_helper_flow_key(
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
const Binding* right);
void order_referenced_zero_constructor_before_foreign_call_operator(
	const vector<FunctionOut>& functions,
	vector<size_t>& order)
{ bool changed = true; for (size_t guard = 0; changed && guard < order.size() * order.size() + 1; ++guard) {
changed = false; for (size_t i = 0; i < order.size(); ++i) { const Binding* call = functions[order[i]].binding; if (!output_call_operator(call)) continue;
for (size_t j = i + 1; j < order.size(); ++j) { const Binding* ctor = functions[order[j]].binding; if (!output_constructor_like_binding(ctor) ||
ctor->type.get() == NULL || ctor->type->kind != TypeKind::Function || ctor->type->parameters.size() != 1 || ctor->owner == call->owner ||
!output_reference_orders_constructor_before_call(functions, functions[order[j]], functions[order[i]])) continue; swap(order[i], order[j]); changed = true; break; }
if (changed) break; } } }
bool output_same_static_member_overload(const Binding* left,
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
void move_ordered_callee_after_caller(vector<size_t>& order,
                                      size_t& caller_position,
                                      size_t callee_position)
{
	size_t fn_index = order[callee_position];
	order.erase(order.begin() + callee_position);
	size_t target =
		callee_position < caller_position ? caller_position
		                                  : caller_position + 1;
	order.insert(order.begin() + target, fn_index);
	if (callee_position < caller_position)
		--caller_position;
}

void order_static_template_owner_callees_after_callers(
	const vector<FunctionOut>& functions,
	vector<size_t>& order)
{
	vector<string> names(functions.size());
	vector<bool> caller_candidate(functions.size(), false);
	vector<bool> callee_candidate(functions.size(), false);
	for (size_t i = 0; i < functions.size(); ++i)
	{
		const Binding* binding = functions[i].binding;
		names[i] = function_out_name(functions[i]);
		caller_candidate[i] =
			binding != NULL &&
			binding->is_static_member &&
			output_owner_template_specialization(binding);
		callee_candidate[i] =
			binding != NULL &&
			output_function_template_specialization(binding);
	}
	for (size_t i = 0; i < order.size(); ++i)
	{
		size_t caller_index = order[i];
		const FunctionOut& caller = functions[caller_index];
		if (!caller_candidate[caller_index])
			continue;
		for (size_t j = 0; j < order.size(); ++j)
		{
			size_t callee_index = order[j];
			const Binding* callee = functions[callee_index].binding;
			if (i == j ||
			    !callee_candidate[callee_index] ||
			    callee->owner == caller.binding->owner ||
			    !output_function_references_symbol(caller,
			                                      names[callee_index]))
				continue;
			move_ordered_callee_after_caller(order, i, j);
			break;
		}
	}
}

void order_template_owner_constructor_callees_after_callers(
	const vector<FunctionOut>& functions,
	vector<size_t>& order)
{
	vector<string> names(functions.size());
	vector<bool> caller_candidate(functions.size(), false);
	vector<bool> callee_candidate(functions.size(), false);
	for (size_t i = 0; i < functions.size(); ++i)
	{
		const Binding* binding = functions[i].binding;
		names[i] = function_out_name(functions[i]);
		caller_candidate[i] =
			output_constructor_like_binding(binding) &&
			output_owner_template_specialization(binding);
		callee_candidate[i] =
			binding != NULL &&
			(output_function_template_specialization(binding) ||
			 binding_has_template_specialization_context(binding));
	}
	for (size_t i = 0; i < order.size(); ++i)
	{
		size_t caller_index = order[i];
		const FunctionOut& caller = functions[caller_index];
		if (!caller_candidate[caller_index])
			continue;
		for (size_t j = 0; j < order.size(); ++j)
		{
			size_t callee_index = order[j];
			const Binding* callee = functions[callee_index].binding;
			if (i == j ||
			    !callee_candidate[callee_index] ||
			    callee->owner == caller.binding->owner ||
			    !output_function_references_symbol(caller,
			                                      names[callee_index]))
				continue;
			move_ordered_callee_after_caller(order, i, j);
			break;
		}
	}
}

void order_template_owner_member_callees_after_callers(
	const vector<FunctionOut>& functions,
	vector<size_t>& order)
{
	vector<string> names(functions.size());
	vector<bool> caller_candidate(functions.size(), false);
	vector<bool> callee_candidate(functions.size(), false);
	for (size_t i = 0; i < functions.size(); ++i)
	{
		const Binding* binding = functions[i].binding;
		names[i] = function_out_name(functions[i]);
		caller_candidate[i] =
			binding != NULL &&
			!binding->is_static_member &&
			!output_constructor_like_binding(binding) &&
			!output_call_operator(binding) &&
			output_owner_template_specialization(binding);
		callee_candidate[i] =
			binding != NULL &&
			(output_function_template_specialization(binding) ||
			 binding_has_template_specialization_context(binding));
	}
	for (size_t i = 0; i < order.size(); ++i)
	{
		size_t caller_index = order[i];
		const FunctionOut& caller = functions[caller_index];
		if (!caller_candidate[caller_index])
			continue;
		for (size_t j = 0; j < order.size(); ++j)
		{
			size_t callee_index = order[j];
			const Binding* callee = functions[callee_index].binding;
			if (i == j ||
			    !callee_candidate[callee_index] ||
			    callee->owner == caller.binding->owner ||
			    !output_function_references_symbol(caller,
			                                      names[callee_index]))
				continue;
			move_ordered_callee_after_caller(order, i, j);
			break;
		}
	}
}

void order_same_owner_template_member_callees_after_callers(
	const vector<FunctionOut>& functions,
	vector<size_t>& order)
{
	vector<string> names(functions.size());
	vector<bool> caller_candidate(functions.size(), false);
	vector<bool> callee_candidate(functions.size(), false);
	for (size_t i = 0; i < functions.size(); ++i)
	{
		const Binding* binding = functions[i].binding;
		names[i] = function_out_name(functions[i]);
		caller_candidate[i] =
			binding != NULL &&
			binding->owner != NULL &&
			binding->owner->kind == ScopeKind::Class &&
			output_owner_template_specialization(binding);
		callee_candidate[i] =
			binding != NULL &&
			output_function_template_specialization(binding);
	}
	for (size_t i = 0; i < order.size(); ++i)
	{
		size_t caller_index = order[i];
		const FunctionOut& caller = functions[caller_index];
		if (!caller_candidate[caller_index])
			continue;
		for (size_t j = 0; j < order.size(); ++j)
		{
			size_t callee_index = order[j];
			const Binding* callee = functions[callee_index].binding;
			if (i == j ||
			    !callee_candidate[callee_index] ||
			    callee->owner != caller.binding->owner ||
			    !output_function_references_symbol(caller,
			                                      names[callee_index]))
				continue;
			move_ordered_callee_after_caller(order, i, j);
			break;
		}
	}
}
void order_value_template_callees_after_callers(
	const vector<FunctionOut>& functions,
	vector<size_t>& order)
{
	vector<bool> caller_candidate(functions.size(), false);
	vector<bool> callee_candidate(functions.size(), false);
	vector<string> names(functions.size());
	for (size_t i = 0; i < functions.size(); ++i)
	{
		const FunctionOut& fn = functions[i];
		names[i] = function_out_name(fn);
		caller_candidate[i] =
			fn.binding != NULL &&
			output_function_template_specialization(fn.binding) &&
			!output_function_out_returns_pointer(fn);
		callee_candidate[i] =
			fn.binding != NULL &&
			!output_function_out_returns_pointer(fn) &&
			(output_function_template_specialization(fn.binding) ||
			 binding_has_template_specialization_context(fn.binding));
	}
	for (size_t i = 0; i < order.size(); ++i)
	{
		size_t caller_index = order[i];
		const FunctionOut& caller = functions[caller_index];
		if (!caller_candidate[caller_index])
			continue;
		for (size_t j = 0; j < order.size(); ++j)
		{
			size_t callee_index = order[j];
			if (i == j ||
			    !callee_candidate[callee_index] ||
			    !output_function_references_symbol(caller,
			                                      names[callee_index]))
				continue;
			size_t fn_index = order[j];
			order.erase(order.begin() + j);
			size_t target = j < i ? i : i + 1;
			order.insert(order.begin() + target, fn_index);
			if (j < i)
				--i;
			break;
		}
	}
}
int output_template_scalar_assignment_key(const Binding* binding) { if (binding == NULL || binding->type.get() == NULL ||
binding->type->kind != TypeKind::Function || !output_owner_template_specialization(binding)) return 0; if (binding->name == "operator=")
return 2; if (binding->name.compare(0, 8, "operator") == 0 || binding->type->parameters.size() != 1) return 0;
TypePtr result = pa11::strip_cv(binding->type->base); return result.get() != NULL && result->kind == TypeKind::Fundamental ? 1 : 0; }
void order_template_scalar_members_before_assignments( const vector<FunctionOut>& functions, vector<size_t>& order) { vector<size_t> positions;
bool has_scalar = false; bool has_assignment = false; for (size_t i = 0; i < order.size(); ++i) {
int key = output_template_scalar_assignment_key( functions[order[i]].binding); if (key == 0) continue;
positions.push_back(i); has_scalar = has_scalar || key == 1; has_assignment = has_assignment || key == 2; }
if (positions.size() < 2 || !has_scalar || !has_assignment) return; vector<size_t> selected; for (size_t i = 0; i < positions.size(); ++i)
selected.push_back(order[positions[i]]); local_stable_sort(selected, [&functions](size_t lhs, size_t rhs) { int lkey = output_template_scalar_assignment_key(
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
} } void order_inherited_conversion_operators_by_owner_depth(
const vector<FunctionOut>& functions, vector<size_t>& order)
{ bool changed = true; for (size_t guard = 0; changed && guard < order.size() * order.size() + 1; ++guard)
{ changed = false; for (size_t i = 0; i < order.size(); ++i) {
const Binding* left = functions[order[i]].binding; if (!output_conversion_operator(left) || !output_owner_template_specialization(left))
continue; TypePtr left_owner = output_owner_record(left);
for (size_t j = i + 1; j < order.size(); ++j) { const Binding* right = functions[order[j]].binding;
if (!output_conversion_operator(right) || !output_owner_template_specialization(right)) continue; TypePtr right_owner =
output_owner_record(right); if (left_owner.get() == NULL || right_owner.get() == NULL || !record_has_base_subobject(right_owner, left_owner))
continue; swap(order[i], order[j]); changed = true; break; }
if (changed) break; } }
} bool output_owner_template_specialization(const Binding* binding) {
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
bool output_lambda_source_order_key(const string& name,
                                    string& context,
                                    size_t& source)
{
	if (name.find("__lambda") == string::npos)
		return false;
	size_t op = name.rfind("__operator__");
	if (op == string::npos)
		return false;
	size_t marker = name.rfind("_t", op);
	if (marker == string::npos || marker + 2 >= op ||
	    !isdigit(static_cast<unsigned char>(name[marker + 2])))
		return false;
	size_t pos = marker + 2;
	source = 0;
	while (pos < op && isdigit(static_cast<unsigned char>(name[pos])))
	{
		source = source * 10 + static_cast<size_t>(name[pos] - '0');
		++pos;
	}
	if (pos >= op || name[pos] != '_')
		return false;
	context = name.substr(0, marker);
	return true;
}
void order_lambda_call_operators_by_rank(const ProgramLowerer& program, vector<size_t>& order) { vector<size_t> positions;
for (size_t i = 0; i < order.size(); ++i) { const Binding* binding = program.functions[order[i]].binding; size_t rank = 0; string context; size_t source = 0;
string name = function_out_name(program.functions[order[i]]);
bool lambda_call = output_lambda_call_operator(binding) ||
	(name.find("__lambda") != string::npos &&
	 name.find("__operator__") != string::npos);
if (!lambda_call) continue; if (!output_inline_definition_rank(program, binding, rank) &&
!output_lambda_source_order_key(name, context, source)) continue; positions.push_back(i);
} if (positions.size() < 2) return; vector<size_t> selected;
for (size_t i = 0; i < positions.size(); ++i) selected.push_back(order[positions[i]]); local_stable_sort(selected, [&program](size_t lhs, size_t rhs) {
size_t lrank = 0; size_t rrank = 0; output_inline_definition_rank( program, program.functions[lhs].binding, lrank);
output_inline_definition_rank( program, program.functions[rhs].binding, rrank); string lcontext; string rcontext; size_t lsource = 0; size_t rsource = 0;
bool lsource_key = output_lambda_source_order_key(function_out_name(program.functions[lhs]), lcontext, lsource);
bool rsource_key = output_lambda_source_order_key(function_out_name(program.functions[rhs]), rcontext, rsource);
if (lsource_key && rsource_key) {
if (lcontext != rcontext) return lcontext < rcontext;
if (lsource != rsource) return lsource < rsource;
}
return lrank != rrank ? lrank < rrank : false; });
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
local_stable_sort(selected, [&functions](size_t lhs, size_t rhs) { int lkey = output_member_template_lambda_breadth_key(functions[lhs]);
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
++i; } }
size_t output_local_type_ordinal_from_name(const string& name)
{
	const string marker = "local_type";
	size_t pos = name.find(marker);
	while (pos != string::npos)
	{
		pos += marker.size();
		size_t value = 0;
		bool any_digit = false;
		while (pos < name.size() &&
		       isdigit(static_cast<unsigned char>(name[pos])))
		{
			any_digit = true;
			value = value * 10 + static_cast<size_t>(name[pos] - '0');
			++pos;
		}
		if (any_digit)
			return value;
		pos = name.find(marker, pos);
	}
	return 0;
}

size_t output_local_record_ordinal(TypePtr record)
{
	record = record.get() != NULL ? pa11::strip_cv(record) : TypePtr();
	if (record.get() == NULL || record->kind != TypeKind::Record)
		return 0;
	size_t ordinal = output_local_type_ordinal_from_name(record->name);
	if (ordinal != 0)
		return ordinal;
	if (record->scope != NULL)
		return output_local_type_ordinal_from_name(record->scope->name);
	return 0;
}

size_t output_function_local_type_ordinal(const FunctionOut& fn)
{
	size_t ordinal = output_local_type_ordinal_from_name(function_out_name(fn));
	if (ordinal != 0)
		return ordinal;
	if (fn.binding != NULL)
	{
		ordinal = output_local_record_ordinal(output_owner_record(fn.binding));
		if (ordinal != 0)
			return ordinal;
	}
	return 0;
}

int output_local_type_lifecycle_key(const FunctionOut& fn)
{
	const Binding* binding = fn.binding;
	if (binding == NULL)
		return 0;
	if (output_class_constructor(binding) &&
	    binding->type.get() != NULL &&
	    binding->type->kind == TypeKind::Function &&
	    binding->type->parameters.size() == 1 &&
	    !output_base_entry_function(fn))
		return 1;
	if (is_class_destructor_binding(binding))
		return 2;
	if (output_class_constructor(binding) &&
	    !output_base_entry_function(fn))
		return 3;
	if (output_call_operator(binding))
		return 4;
	return 0;
}

void order_local_type_specialization_lifecycle(
	const vector<FunctionOut>& functions,
	vector<size_t>& order)
{
	vector<size_t> ordinals(functions.size(), 0);
	vector<int> keys(functions.size(), 0);
	for (size_t i = 0; i < functions.size(); ++i)
	{
		ordinals[i] = output_function_local_type_ordinal(functions[i]);
		keys[i] = output_local_type_lifecycle_key(functions[i]);
	}
	bool changed = true;
	for (size_t guard = 0; changed && guard < order.size() * order.size() + 1;
	     ++guard)
	{
		changed = false;
		for (size_t i = 0; i < order.size(); ++i)
		{
			size_t ctor_index = order[i];
			if (keys[ctor_index] != 1 || ordinals[ctor_index] == 0)
				continue;
			size_t insert_after = i;
			for (size_t j = i + 1; j < order.size(); ++j)
			{
				size_t candidate = order[j];
				if (ordinals[candidate] == 0 ||
				    ordinals[candidate] >= ordinals[ctor_index] ||
				    keys[candidate] <= 1)
					continue;
				insert_after = j;
			}
			if (insert_after == i)
				continue;
			size_t fn_index = order[i];
			order.erase(order.begin() + i);
			--insert_after;
			order.insert(order.begin() + insert_after + 1, fn_index);
			changed = true;
			break;
		}
	}
}
}  // namespace internal
}  // namespace pa14
