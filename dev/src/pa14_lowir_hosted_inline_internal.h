#pragma once
#include "pa14_lowir_internal.h"
#include "pa14_lowir_function_internal.h"

namespace pa14 {
namespace internal {

bool hosted_deque_iterator_difference_binding(const Binding* binding,
                                              TypePtr* element_out);
bool hosted_deque_iterator_order_binding(const Binding* binding);
bool hosted_deque_iterator_plus_binding(const Binding* binding,
                                        TypePtr* element_out,
                                        size_t* n_index_out,
                                        size_t* iterator_index_out);
bool hosted_deque_iterator_minus_n_binding(const Binding* binding,
                                           TypePtr* element_out);
bool hosted_bit_iterator_base_comparison_binding(const Binding* binding);
bool hosted_bit_iterator_base_difference_binding(const Binding* binding);
bool hosted_bit_iterator_plus_binding(const Binding* binding,
                                      size_t* iterator_index_out,
                                      size_t* n_index_out);
bool hosted_bit_const_iterator_deref_binding(const Binding* binding);
bool hosted_bit_const_iterator_preincrement_binding(const Binding* binding);
bool hosted_allocator_comparison_binding(const Binding* binding);
bool hosted_allocator_rebind_constructor_binding(const Binding* binding);
bool hosted_allocator_destroy_binding(const Binding* binding,
                                      TypePtr* object_out,
                                      size_t* pointer_index_out);
bool hosted_iterator_comparison_binding(const Binding* binding);
bool hosted_vector_bool_s_nword_binding(const Binding* binding);

bool binding_in_namespace(const Binding* binding, const string& name);
bool record_in_namespace(TypePtr record, const string& name);
bool pointer_object_type(TypePtr type);
string hosted_record_primary(TypePtr record);
bool hosted_to_address_binding(const Binding* binding);
bool std_type_info_record(TypePtr record);
bool type_info_reference(TypePtr type);
bool hosted_type_info_comparison_binding(const Binding* binding);
bool hosted_basic_string_record(TypePtr record);
TypePtr hosted_equal_iterator_string_record(TypePtr type);
bool hosted_equal_aux_basic_string_binding(const Binding* binding);
bool hosted_int_object_type(TypePtr type);
TypePtr hosted_int_iterator_value_type(TypePtr type);
bool hosted_lexicographical_compare_int_binding(const Binding* binding);
bool hosted_uninitialized_default_n_trivial_binding(const Binding* binding);
bool hosted_default_allocator_record(TypePtr allocator, TypePtr element);
bool hosted_vector_base_record(TypePtr record, TypePtr* element_out);
bool hosted_vector_record(TypePtr record, TypePtr* element_out);
TypePtr hosted_guard_alloc_vector_record(TypePtr guard_record);
Binding* basic_string_guarded_field(TypePtr record);
bool hosted_basic_string_guard_destructor_binding(const Binding* binding);
bool hosted_uninit_destroy_guard_record(TypePtr record, TypePtr* iterator_out);
bool hosted_uninit_destroy_guard_destructor_binding(const Binding* binding);
bool hosted_vector_base_deallocate_binding(const Binding* binding);
bool hosted_vector_impl_move_constructor_binding(const Binding* binding);
bool hosted_vector_guard_alloc_record(TypePtr record);
bool hosted_vector_guard_alloc_destructor_binding(const Binding* binding);
bool hosted_pair_record(TypePtr record);
Binding* hosted_pair_field(TypePtr record, const string& name, size_t fallback);
TypePtr hosted_pair_argument(TypePtr record, size_t index);
uint64_t hosted_pair_align_up(uint64_t value, uint64_t align);
TypePtr hosted_member_owner_record(const Binding* binding);
Binding* hosted_field_named(TypePtr record, const string& name);
uint64_t hosted_field_offset_or_zero(TypePtr record, const string& name);
bool hosted_tuple_storage_record(TypePtr record);
bool hosted_tuple_storage_default_constructor_binding(const Binding* binding);
bool hosted_tuple_storage_head_binding(const Binding* binding);
bool hosted_unique_ptr_impl_record(TypePtr record);
bool hosted_unique_ptr_record(TypePtr record);
bool hosted_default_delete_record(TypePtr record);
bool hosted_unique_ptr_destructor_binding(const Binding* binding,
                                          TypePtr* element_out);
bool hosted_unique_ptr_impl_pointer_constructor_binding(const Binding* binding);
bool hosted_unique_ptr_impl_move_constructor_binding(const Binding* binding);
bool hosted_unique_ptr_impl_move_assignment_binding(const Binding* binding);
bool hosted_unique_ptr_impl_constructor_binding(const Binding* binding);
bool hosted_iter_equals_val_constructor_binding(const Binding* binding);
bool hosted_normal_iterator_record(TypePtr record, TypePtr* iterator_out);
bool hosted_normal_iterator_member_binding(const Binding* binding);
bool hosted_normal_iterator_difference_binding(const Binding* binding,
                                               TypePtr* element_out);
bool hosted_ops_compare_record(TypePtr record);
bool hosted_ops_compare_constructor_binding(const Binding* binding);
bool hosted_uninit_destroy_guard_constructor_binding(const Binding* binding);
bool hosted_uninit_destroy_guard_release_binding(const Binding* binding);
bool hosted_tuple_record(TypePtr record);
bool hosted_single_type_template_argument(
	const vector<pa11::TemplateInstanceArgument>& args,
	TypePtr* type_out);
bool hosted_tuple_reference_constructor_binding(const Binding* binding,
                                                TypePtr* element_out);
bool hosted_forward_as_tuple_binding(const Binding* binding);
bool hosted_index_tuple_record(TypePtr record);
bool hosted_pair_piecewise_constructor_symbol(const Binding* binding);
bool hosted_pair_piecewise_index_constructor_binding(const Binding* binding);
bool hosted_pair_constructor_binding(const Binding* binding);
bool hosted_pair_default_constructor_binding(const Binding* binding);
bool hosted_pair_assignment_binding(const Binding* binding);
bool hosted_alloc_traits_propagate_on_move_assign_binding(
	const Binding* binding);
bool hosted_rbtree_assignment_binding(const Binding* binding);
bool hosted_rbtree_copy_constructor_binding(const Binding* binding);
bool hosted_rbtree_const_iterator_node_constructor_binding(
	const Binding* binding);
bool hosted_tree_container_default_record(TypePtr record);
bool hosted_temporary_buffer_constructor_binding(const Binding* binding);
bool hosted_sp_counted_base_record(TypePtr record);
bool hosted_sp_counted_ptr_record(TypePtr record);
bool hosted_sp_counted_base_constructor_binding(const Binding* binding);
bool hosted_sp_counted_base_destructor_binding(const Binding* binding);
bool hosted_sp_counted_base_add_ref_binding(const Binding* binding);
bool hosted_sp_counted_base_release_binding(const Binding* binding);
bool hosted_sp_counted_base_destroy_binding(const Binding* binding);
bool hosted_sp_counted_ptr_virtual_binding(const Binding* binding);
bool hosted_sp_counted_ptr_destructor_binding(const Binding* binding);
bool hosted_sp_counted_control_binding(const Binding* binding);
Binding* hosted_sp_counted_base_member_function(TypePtr record,
                                                const string& name);
bool hosted_record_has_parent_primary(TypePtr record, const string& primary);
bool hosted_vector_guard_elts_record(TypePtr record, TypePtr* element_out);
bool hosted_vector_guard_elts_destructor_binding(const Binding* binding);
bool hosted_hashtable_local_guard_destructor_binding(const Binding* binding);
bool hosted_hashtable_ebo_helper_record(TypePtr record);
bool hosted_same_record_reference(TypePtr type, TypePtr record);
bool hosted_hashtable_ebo_helper_copy_constructor_binding(
	const Binding* binding);
bool hosted_hashtable_allocator_move_constructor_binding(
	const Binding* binding);
bool hosted_shared_count_member_symbol(const Binding* binding);
bool hosted_shared_count_copy_constructor_binding(const Binding* binding);
bool hosted_shared_count_assignment_binding(const Binding* binding);
bool hosted_shared_ptr_assignment_binding(const Binding* binding);
Binding* hosted_shared_ptr_count_field(TypePtr record);
TypePtr hosted_shared_count_control_record_from_type(TypePtr count);
Binding* hosted_shared_control_function_from_record(TypePtr control,
                                                    const string& name);
TypePtr hosted_shared_count_control_record(const Binding* binding);
Binding* hosted_shared_count_control_function(const Binding* binding,
                                             const string& name);
bool hosted_exception_ptr_record(TypePtr record);
bool hosted_make_exception_ptr_binding(const Binding* binding);
TypePtr stoa_conversion_function_type(const Binding* binding);
bool hosted_stoa_binding(const Binding* binding);
Binding* hosted_exception_ptr_void_constructor(TypePtr record);
void ensure_make_exception_ptr_runtime_declarations(ProgramLowerer& program);
void ensure_stoa_runtime_declarations(ProgramLowerer& program);
void ensure_hosted_operator_delete_declaration(ProgramLowerer& program);
void ensure_hosted_operator_new_declaration(ProgramLowerer& program);
void ensure_hosted_rbtree_runtime_declarations(ProgramLowerer& program);
Binding* hosted_basic_string_release_function(TypePtr string_record);
Node make_hosted_parameter_node(const Binding* binding,
                                size_t index,
                                const string& name);
Node make_empty_hosted_function_node(const Binding* binding,
                                     const vector<string>& names);
string parameter_name(const FunctionOut& out,
                      size_t index,
                      const string& fallback);

}  // namespace internal
}  // namespace pa14
