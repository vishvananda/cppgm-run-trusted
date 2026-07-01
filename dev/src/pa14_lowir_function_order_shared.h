#pragma once
#include "pa14_lowir_internal.h"

namespace pa14 {
namespace internal {

template<typename T, typename Compare>
void local_stable_sort(vector<T>& values, Compare compare)
{
	for (size_t i = 1; i < values.size(); ++i)
	{
		T current = values[i];
		size_t j = i;
		while (j > 0 && compare(current, values[j - 1]))
		{
			values[j] = values[j - 1];
			--j;
		}
		values[j] = current;
	}
}

template<typename Compare>
void local_stable_sort_range(vector<size_t>& values,
                             size_t begin,
                             size_t end,
                             Compare compare)
{
	for (size_t i = begin + 1; i < end; ++i)
	{
		size_t current = values[i];
		size_t j = i;
		while (j > begin && compare(current, values[j - 1]))
		{
			values[j] = values[j - 1];
			--j;
		}
		values[j] = current;
	}
}

const string& function_out_name(const FunctionOut& fn);
int emitted_function_order_key(const FunctionOut& fn);
bool emitted_function_is_operator(const FunctionOut& fn);
bool emitted_function_is_strong_entry(const FunctionOut& fn);
int emitted_template_dependency_order_key(const FunctionOut& fn);
TypePtr output_first_this_record(const Binding* binding);
bool output_function_returns_record(const Binding* binding);
bool output_function_returns_pointer(const Binding* binding);
bool output_function_out_returns_pointer(const FunctionOut& fn);
bool output_function_out_returns_record(const FunctionOut& fn);
TypePtr output_function_record_result(const Binding* binding);
bool output_function_template_specialization(const Binding* binding);
bool output_class_constructor(const Binding* binding);
bool output_class_member_of_local_class(const Binding* binding);
bool output_constructor_like_binding(const Binding* binding);
bool output_has_by_value_record_parameter(const Binding* binding);
TypePtr output_first_by_value_record_parameter(const Binding* binding);
bool output_has_reference_parameter(const Binding* binding);
TypePtr output_constructor_record_parameter(const Binding* binding,
                                            bool require_by_value);
bool output_constructor_has_record_parameter(const Binding* binding,
                                             TypePtr record);
bool output_base_entry_function(const FunctionOut& fn);
TypePtr output_owner_record(const Binding* binding);
bool output_same_record(TypePtr left, TypePtr right);
bool output_same_record_or_template_family(TypePtr left, TypePtr right);
bool output_type_mentions_record(TypePtr type, TypePtr record);
bool output_function_mentions_record(const Binding* binding, TypePtr record);
bool output_function_has_reference_parameter_record(const Binding* binding,
                                                    TypePtr record);
bool output_local_class_constructor(const FunctionOut& fn);
bool output_zero_argument_nonlocal_constructor(const FunctionOut& fn);
size_t output_constructor_arity(const FunctionOut& fn);
string output_constructor_owner_family(const Binding* binding);
bool output_constructors_share_owner_family(const Binding* left,
                                            const Binding* right);
bool output_call_operator(const Binding* binding);
bool output_lambda_related_binding(const Binding* binding);
bool output_lambda_related_function(const FunctionOut& fn);
bool output_lambda_call_operator(const Binding* binding);
bool output_class_owned_pointer_helper(const Binding* binding);
bool output_owner_template_specialization(const Binding* binding);
bool output_function_references_symbol(const FunctionOut& fn,
                                       const string& symbol);
size_t output_function_reference_position(const FunctionOut& fn,
                                          const string& symbol);
bool output_template_or_local_order_function(const FunctionOut& fn);
bool output_inline_definition_rank(const ProgramLowerer& program,
                                   const Binding* binding,
                                   size_t& rank);

void order_template_conversion_flow_functions(
	const vector<FunctionOut>& functions,
	vector<size_t>& order);
void order_local_template_members_by_rank(const ProgramLowerer& program,
                                          vector<size_t>& order);
void order_template_dependency_flow_functions(
	const vector<FunctionOut>& functions,
	vector<size_t>& order);
void order_outer_class_lifecycle(const vector<FunctionOut>& functions,
                                 vector<size_t>& order);
void order_record_return_before_zero_constructor(
	const vector<FunctionOut>& functions,
	vector<size_t>& order);
void order_by_value_record_member_before_zero_constructor(
	const vector<FunctionOut>& functions,
	vector<size_t>& order);
void order_record_return_call_operator_before_zero_constructor(
	const vector<FunctionOut>& functions,
	vector<size_t>& order);
void order_zero_constructor_before_namespace_record_return(
	const vector<FunctionOut>& functions,
	vector<size_t>& order);
void order_namespace_record_return_after_zero_constructor(
	const vector<FunctionOut>& functions,
	vector<size_t>& order);
void order_nonzero_constructor_before_owner_helpers(
	const vector<FunctionOut>& functions,
	vector<size_t>& order);
void order_by_value_constructor_before_record_constructor_dependencies(
	const vector<FunctionOut>& functions,
	vector<size_t>& order);
void order_owner_constructor_before_template_constructor_dependency(
	const vector<FunctionOut>& functions,
	vector<size_t>& order);
void order_scalar_member_after_owner_record_dependencies(
	const vector<FunctionOut>& functions,
	vector<size_t>& order);
void order_derived_members_before_inherited_constructor_wrappers(
	const vector<FunctionOut>& functions,
	vector<size_t>& order);
void order_base_entries_after_derived_template_users(
	const vector<FunctionOut>& functions,
	vector<size_t>& order);
void order_local_template_call_flow_functions(
	const vector<FunctionOut>& functions,
	vector<size_t>& order);
void order_by_value_conversion_after_parameter_default(
	const vector<FunctionOut>& functions,
	vector<size_t>& order);
void order_record_result_pointer_member_flow(
	const vector<FunctionOut>& functions,
	vector<size_t>& order);
void order_template_and_lambda_callees_after_callers(
	const vector<FunctionOut>& functions,
	vector<size_t>& order);
void order_pointer_reference_helpers_before_lambda_callers(
	const vector<FunctionOut>& functions,
	vector<size_t>& order);
void order_class_pointer_helpers_before_value_pointer_constructors(
	const vector<FunctionOut>& functions,
	vector<size_t>& order);
void order_operator_functions_by_key(const vector<FunctionOut>& functions,
                                     vector<size_t>& order);
void order_range_for_operator_functions_by_key(
	const vector<FunctionOut>& functions,
	vector<size_t>& order);
void order_preemitted_referenced_callees_after_callers(
	const vector<FunctionOut>& functions,
	vector<size_t>& order);

void order_class_pointer_helpers_by_arity(const vector<FunctionOut>& functions,
                                          vector<size_t>& order);
void order_same_owner_constructors_by_arity(
	const vector<FunctionOut>& functions,
	vector<size_t>& order);
void order_zero_argument_constructors_before_local_ctors(
	const vector<FunctionOut>& functions,
	vector<size_t>& order);
void order_invoked_functor_after_template_invoke(
	const vector<FunctionOut>& functions,
	vector<size_t>& order);
void order_callable_thunk_flow_functions(const vector<FunctionOut>& functions,
                                         vector<size_t>& order);
void order_static_template_member_depth_functions(
	const vector<FunctionOut>& functions,
	vector<size_t>& order);
void order_assignment_helper_flow_functions(
	const vector<FunctionOut>& functions,
	vector<size_t>& order);
void order_assignment_operator_before_owner_zero_constructor(
	const vector<FunctionOut>& functions,
	vector<size_t>& order);
void order_same_owner_constructor_before_assignment_operator(
	const vector<FunctionOut>& functions,
	vector<size_t>& order);
void order_same_owner_call_operator_before_unreferenced_zero_constructor(
	const vector<FunctionOut>& functions,
	vector<size_t>& order);
void order_local_constructor_before_same_owner_call_operator(
	const vector<FunctionOut>& functions,
	vector<size_t>& order);
void order_referenced_zero_constructor_before_foreign_call_operator(
	const vector<FunctionOut>& functions,
	vector<size_t>& order);
void order_static_member_overload_callees_after_callers(
	const vector<FunctionOut>& functions,
	vector<size_t>& order);
void order_static_template_member_callees_after_callers(
	const vector<FunctionOut>& functions,
	vector<size_t>& order);
void order_static_template_owner_callees_after_callers(
	const vector<FunctionOut>& functions,
	vector<size_t>& order);
void order_template_owner_constructor_callees_after_callers(
	const vector<FunctionOut>& functions,
	vector<size_t>& order);
void order_same_owner_template_member_callees_after_callers(
	const vector<FunctionOut>& functions,
	vector<size_t>& order);
void order_template_owner_member_callees_after_callers(
	const vector<FunctionOut>& functions,
	vector<size_t>& order);
void order_value_template_callees_after_callers(
	const vector<FunctionOut>& functions,
	vector<size_t>& order);
void order_template_scalar_members_before_assignments(
	const vector<FunctionOut>& functions,
	vector<size_t>& order);
void order_conversion_after_compound_assignment(
	const vector<FunctionOut>& functions,
	vector<size_t>& order);
void order_inherited_conversion_operators_by_owner_depth(
	const vector<FunctionOut>& functions,
	vector<size_t>& order);
void order_template_owner_call_operator_callees_after_callers(
	const vector<FunctionOut>& functions,
	vector<size_t>& order);
void order_template_reference_constructors_before_foreign_call_operators(
	const vector<FunctionOut>& functions,
	vector<size_t>& order);
void order_lambda_call_operators_by_rank(const ProgramLowerer& program,
                                         vector<size_t>& order);
void order_lambda_callees_after_callers(const vector<FunctionOut>& functions,
                                        vector<size_t>& order);
void order_member_template_lambda_breadth_functions(
	const vector<FunctionOut>& functions,
	vector<size_t>& order);
void order_value_constructors_after_scalar_template_helpers(
	const vector<FunctionOut>& functions,
	vector<size_t>& order);
void order_constructors_after_pointer_reference_helpers(
	const vector<FunctionOut>& functions,
	vector<size_t>& order);
void order_referenced_template_constructors_by_call_position(
	const vector<FunctionOut>& functions,
	vector<size_t>& order);
void order_local_type_specialization_lifecycle(
	const vector<FunctionOut>& functions,
	vector<size_t>& order);

}  // namespace internal
}  // namespace pa14
