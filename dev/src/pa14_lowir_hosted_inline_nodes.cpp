#include "pa14_lowir_hosted_inline_internal.h"
#include "pa12_templates_function_support.h"

namespace pa14 {
namespace internal {

bool lowir_synthesizable_hosted_inline_body(const Binding* binding)
{
	if (binding == NULL ||
	    !pa12::internal::substituted_type_is_valid(binding->type))
		return false;
	return lowir_synthesizable_hosted_hashtable_count_constructor(binding) ||
	       lowir_synthesizable_hosted_hashtable_range_constructor(binding) ||
	       lowir_synthesizable_hosted_hash_code_base_hash_code(binding) ||
	       lowir_synthesizable_hosted_vector_copy_constructor(binding) ||
	       lowir_synthesizable_hosted_vector_copy_assignment(binding) ||
	       lowir_synthesizable_hosted_vector_range_insert(binding) ||
	       lowir_synthesizable_hosted_vector_realloc_insert(binding) ||
	       lowir_synthesizable_hosted_vector_initializer_realloc_insert(binding) ||
	       lowir_synthesizable_hosted_vector_relocate(binding) ||
	       lowir_synthesizable_hosted_initializer_list_allocator_construct(binding) ||
	       lowir_synthesizable_hosted_unique_ptr_allocator_copy_construct(binding) ||
	       lowir_synthesizable_hosted_unique_ptr_copy_helper(binding) ||
	       hosted_to_address_binding(binding) ||
	       hosted_type_info_comparison_binding(binding) ||
	       hosted_iterator_comparison_binding(binding) ||
	       hosted_vector_bool_s_nword_binding(binding) ||
	       hosted_normal_iterator_difference_binding(binding, NULL) ||
	       hosted_deque_iterator_difference_binding(binding, NULL) ||
	       hosted_deque_iterator_order_binding(binding) ||
	       hosted_deque_iterator_plus_binding(binding, NULL, NULL, NULL) ||
	       hosted_deque_iterator_minus_n_binding(binding, NULL) ||
	       hosted_bit_iterator_base_comparison_binding(binding) ||
	       hosted_bit_iterator_base_difference_binding(binding) ||
	       hosted_bit_iterator_plus_binding(binding, NULL, NULL) ||
	       hosted_bit_const_iterator_deref_binding(binding) ||
	       hosted_bit_const_iterator_preincrement_binding(binding) ||
	       hosted_equal_aux_basic_string_binding(binding) ||
	       hosted_lexicographical_compare_int_binding(binding) ||
	       hosted_uninitialized_default_n_trivial_binding(binding) ||
	       hosted_allocator_comparison_binding(binding) ||
	       hosted_allocator_rebind_constructor_binding(binding) ||
	       hosted_allocator_destroy_binding(binding, NULL, NULL) ||
	       hosted_basic_string_guard_destructor_binding(binding) ||
	       hosted_uninit_destroy_guard_destructor_binding(binding) ||
	       hosted_vector_guard_elts_destructor_binding(binding) ||
	       hosted_vector_base_deallocate_binding(binding) ||
	       hosted_vector_impl_move_constructor_binding(binding) ||
	       hosted_std_function_swap_binding(binding) ||
	       hosted_rbtree_assignment_binding(binding) ||
	       hosted_rbtree_const_iterator_node_constructor_binding(binding) ||
	       hosted_tuple_storage_default_constructor_binding(binding) ||
	       hosted_tuple_storage_head_binding(binding) ||
	       hosted_tuple_reference_constructor_binding(binding, NULL) ||
	       hosted_unique_ptr_destructor_binding(binding, NULL) ||
	       hosted_unique_ptr_impl_constructor_binding(binding) ||
	       hosted_unique_ptr_impl_move_assignment_binding(binding) ||
	       hosted_iter_equals_val_constructor_binding(binding) ||
	       hosted_normal_iterator_member_binding(binding) ||
	       hosted_ops_compare_constructor_binding(binding) ||
	       hosted_uninit_destroy_guard_constructor_binding(binding) ||
	       hosted_uninit_destroy_guard_release_binding(binding) ||
	       hosted_vector_guard_alloc_destructor_binding(binding) ||
	       hosted_alloc_traits_propagate_on_move_assign_binding(binding) ||
	       hosted_pair_default_constructor_binding(binding) ||
	       hosted_pair_piecewise_index_constructor_binding(binding) ||
	       hosted_pair_constructor_binding(binding) ||
	       hosted_pair_assignment_binding(binding) ||
	       hosted_rbtree_copy_constructor_binding(binding) ||
	       hosted_temporary_buffer_constructor_binding(binding) ||
	       hosted_sp_counted_control_binding(binding) ||
	       hosted_hashtable_local_guard_destructor_binding(binding) ||
	       hosted_hashtable_ebo_helper_copy_constructor_binding(binding) ||
	       hosted_hashtable_allocator_move_constructor_binding(binding) ||
	       hosted_shared_count_copy_constructor_binding(binding) ||
	       hosted_shared_count_assignment_binding(binding) ||
	       hosted_shared_ptr_assignment_binding(binding) ||
	       hosted_make_exception_ptr_binding(binding) ||
	       hosted_stoa_binding(binding);
}

Node lowir_make_hosted_inline_body_node(const Binding* binding)
{
	if (lowir_synthesizable_hosted_hashtable_count_constructor(binding))
		return lowir_make_hosted_hashtable_count_constructor_node(binding);
	if (lowir_synthesizable_hosted_hashtable_range_constructor(binding))
		return make_empty_hosted_function_node(
			binding,
			{"this", "__f", "__l", "__bkt_count_hint",
			 "__h", "__eq", "__a", "__true_type"});
	if (lowir_synthesizable_hosted_hash_code_base_hash_code(binding))
		return make_empty_hosted_function_node(binding,
		                                       {"this", "__k"});
	if (lowir_synthesizable_hosted_vector_copy_constructor(binding))
		return make_empty_hosted_function_node(binding,
		                                       {"this", "__x"});
	if (lowir_synthesizable_hosted_vector_copy_assignment(binding))
		return make_empty_hosted_function_node(binding,
		                                       {"this", "__x"});
	if (lowir_synthesizable_hosted_vector_range_insert(binding))
		return lowir_make_hosted_vector_range_insert_node(binding);
	if (lowir_synthesizable_hosted_vector_realloc_insert(binding))
		return make_empty_hosted_function_node(
			binding, {"this", "__position", "__args"});
	if (lowir_synthesizable_hosted_vector_initializer_realloc_insert(binding))
		return make_empty_hosted_function_node(
			binding, {"this", "__position", "__args"});
	if (lowir_synthesizable_hosted_vector_relocate(binding))
		return make_empty_hosted_function_node(
			binding, {"__first", "__last", "__result", "__alloc"});
	if (lowir_synthesizable_hosted_initializer_list_allocator_construct(binding))
		return make_empty_hosted_function_node(
			binding, {"this", "__p", "__args"});
	if (lowir_synthesizable_hosted_unique_ptr_allocator_copy_construct(binding))
		return make_empty_hosted_function_node(
			binding, {"this", "__p", "__args"});
	if (lowir_synthesizable_hosted_unique_ptr_copy_helper(binding))
		return make_empty_hosted_function_node(
			binding, {"__first", "__last", "__value"});
	if (hosted_std_function_swap_binding(binding))
		return make_empty_hosted_function_node(binding, {"this", "__x"});
	if (hosted_rbtree_assignment_binding(binding))
		return make_empty_hosted_function_node(binding, {"this", "__x"});
	if (hosted_rbtree_const_iterator_node_constructor_binding(binding))
		return make_empty_hosted_function_node(binding,
		                                       {"this", "__node"});
	if (hosted_to_address_binding(binding))
		return make_empty_hosted_function_node(binding, {"__ptr"});
	if (hosted_type_info_comparison_binding(binding))
		return make_empty_hosted_function_node(binding, {"this", "__rhs"});
	if (hosted_iterator_comparison_binding(binding))
		return make_empty_hosted_function_node(binding, {"__lhs", "__rhs"});
	if (hosted_vector_bool_s_nword_binding(binding))
		return make_empty_hosted_function_node(binding, {"__n"});
	if (hosted_normal_iterator_difference_binding(binding, NULL))
		return make_empty_hosted_function_node(binding, {"__lhs", "__rhs"});
	if (hosted_deque_iterator_difference_binding(binding, NULL))
		return make_empty_hosted_function_node(binding, {"__lhs", "__rhs"});
	if (hosted_deque_iterator_order_binding(binding))
		return make_empty_hosted_function_node(binding, {"__lhs", "__rhs"});
	size_t n_index = 0;
	size_t iterator_index = 0;
	if (hosted_deque_iterator_plus_binding(
		    binding, NULL, &n_index, &iterator_index))
	{
		vector<string> names(2);
		names[n_index] = "__n";
		names[iterator_index] = "__x";
		return make_empty_hosted_function_node(binding, names);
	}
	if (hosted_deque_iterator_minus_n_binding(binding, NULL))
		return make_empty_hosted_function_node(binding, {"__x", "__n"});
	if (hosted_bit_iterator_base_comparison_binding(binding) ||
	    hosted_bit_iterator_base_difference_binding(binding))
		return make_empty_hosted_function_node(binding, {"__lhs", "__rhs"});
	size_t bit_iterator_index = 0;
	size_t bit_n_index = 0;
	if (hosted_bit_iterator_plus_binding(
		    binding, &bit_iterator_index, &bit_n_index))
	{
		vector<string> names(2);
		names[bit_iterator_index] = "__x";
		names[bit_n_index] = "__n";
		return make_empty_hosted_function_node(binding, names);
	}
	if (hosted_bit_const_iterator_deref_binding(binding) ||
	    hosted_bit_const_iterator_preincrement_binding(binding))
		return make_empty_hosted_function_node(binding, {"this"});
	if (hosted_equal_aux_basic_string_binding(binding))
		return make_empty_hosted_function_node(
			binding, {"__first1", "__last1", "__first2"});
	if (hosted_lexicographical_compare_int_binding(binding))
		return make_empty_hosted_function_node(
			binding, {"__first1", "__last1", "__first2", "__last2"});
	if (hosted_uninitialized_default_n_trivial_binding(binding))
		return make_empty_hosted_function_node(
			binding, {"__first", "__n"});
	if (hosted_allocator_comparison_binding(binding))
		return make_empty_hosted_function_node(binding, {"__lhs", "__rhs"});
	if (hosted_allocator_rebind_constructor_binding(binding))
		return make_empty_hosted_function_node(binding, {"this", "__param1"});
	size_t destroy_pointer_index = 0;
	if (hosted_allocator_destroy_binding(binding, NULL,
	                                     &destroy_pointer_index))
	{
		vector<string> names(binding->type->parameters.size());
		for (size_t i = 0; i < names.size(); ++i)
			names[i] = "__param" + to_string(i);
		if (!names.empty())
			names[0] = "this";
		if (destroy_pointer_index < names.size())
			names[destroy_pointer_index] = "__p";
		return make_empty_hosted_function_node(binding, names);
	}
	if (hosted_basic_string_guard_destructor_binding(binding))
		return make_empty_hosted_function_node(binding, {"this"});
	if (hosted_uninit_destroy_guard_destructor_binding(binding))
		return make_empty_hosted_function_node(binding, {"this"});
	if (hosted_vector_guard_elts_destructor_binding(binding))
		return make_empty_hosted_function_node(binding, {"this"});
	if (hosted_vector_base_deallocate_binding(binding))
		return make_empty_hosted_function_node(
			binding, {"this", "__p", "__n"});
	if (hosted_vector_impl_move_constructor_binding(binding))
		return make_empty_hosted_function_node(binding, {"this", "__x"});
	if (hosted_tuple_storage_default_constructor_binding(binding))
		return make_empty_hosted_function_node(binding, {"this"});
	if (hosted_tuple_storage_head_binding(binding))
		return make_empty_hosted_function_node(binding, {"__t"});
	if (hosted_tuple_reference_constructor_binding(binding, NULL))
		return make_empty_hosted_function_node(binding,
		                                       {"this", "__value"});
	if (hosted_unique_ptr_destructor_binding(binding, NULL))
		return make_empty_hosted_function_node(binding, {"this"});
	if (hosted_unique_ptr_impl_pointer_constructor_binding(binding))
		return make_empty_hosted_function_node(binding, {"this", "__p"});
	if (hosted_unique_ptr_impl_move_constructor_binding(binding))
		return make_empty_hosted_function_node(binding, {"this", "__u"});
	if (hosted_unique_ptr_impl_move_assignment_binding(binding))
		return make_empty_hosted_function_node(binding, {"this", "__u"});
	if (hosted_iter_equals_val_constructor_binding(binding))
		return make_empty_hosted_function_node(binding, {"this", "__value"});
	if (hosted_normal_iterator_member_binding(binding))
	{
		if (binding->name == "operator+" ||
		    binding->name == "operator-")
			return make_empty_hosted_function_node(binding,
			                                       {"this", "__n"});
		return make_empty_hosted_function_node(binding, {"this"});
	}
	if (hosted_ops_compare_constructor_binding(binding))
		return make_empty_hosted_function_node(binding, {"this", "__comp"});
	if (hosted_uninit_destroy_guard_constructor_binding(binding))
		return make_empty_hosted_function_node(binding, {"this", "__first"});
	if (hosted_uninit_destroy_guard_release_binding(binding))
		return make_empty_hosted_function_node(binding, {"this"});
	if (hosted_vector_guard_alloc_destructor_binding(binding))
		return make_empty_hosted_function_node(binding, {"this"});
	if (hosted_alloc_traits_propagate_on_move_assign_binding(binding))
		return make_empty_hosted_function_node(binding, {});
	if (hosted_pair_default_constructor_binding(binding))
		return make_empty_hosted_function_node(binding, {"this"});
	if (hosted_pair_piecewise_index_constructor_binding(binding))
	{
		if (binding->type.get() != NULL &&
		    binding->type->kind == TypeKind::Function &&
		    binding->type->parameters.size() == 4)
			return make_empty_hosted_function_node(
				binding,
				{"this", "__piecewise", "__tuple1", "__tuple2"});
		return make_empty_hosted_function_node(
			binding,
			{"this", "__tuple1", "__tuple2", "__indexes1", "__indexes2"});
	}
	if (hosted_sp_counted_control_binding(binding))
	{
		if (binding->name == pa11::abi_private_name("M_get_deleter"))
			return make_empty_hosted_function_node(binding,
			                                       {"this", "__ti"});
		return make_empty_hosted_function_node(binding, {"this"});
	}
	if (hosted_pair_constructor_binding(binding))
	{
		TypePtr record = class_record_for_member(binding);
		Binding* first = hosted_pair_field(record, "first", 0);
		Binding* second = hosted_pair_field(record, "second", 1);
		if (first == NULL || second == NULL)
			throw runtime_error("unsupported hosted pair constructor");
		Scope* function_scope =
			pa11::create_child_scope(binding->owner,
			                         ScopeKind::Function,
			                         binding->name);
		static const char* names[] = {"this", "__first", "__second"};
		vector<Binding*> params;
		Node fn("function-definition");
		fn.binding = const_cast<Binding*>(binding);
		fn.type = binding->type;
		for (size_t i = 0; i < binding->type->parameters.size(); ++i)
		{
			Binding* param_binding =
				pa11::add_binding(function_scope,
				                  BindingKind::Parameter,
				                  names[i],
				                  binding->type->parameters[i]);
			params.push_back(param_binding);
			Node param(string("parameter ") + names[i]);
			param.binding = param_binding;
			param.type = binding->type->parameters[i];
			fn.children.push_back(param);
		}
		Node body("compound-statement");
		Binding* fields[] = {first, second};
		for (size_t i = 0; i < 2; ++i)
		{
			TypePtr expr_type = object_type(params[i + 1]->type);
			Node arg(string("id-expression lvalue ") +
			         pa11::describe_type(expr_type) +
			         " " + names[i + 1]);
			arg.binding = params[i + 1];
			arg.type = expr_type;
			arg.category = ValueCategory::LValue;
			Node action(string("member-init-action ") + fields[i]->name);
			action.binding = fields[i];
			action.type = fields[i]->type;
			pa12::internal::add_child(action, arg);
			pa12::internal::add_child(body, action);
		}
		fn.children.push_back(body);
		return fn;
	}
	if (hosted_pair_assignment_binding(binding))
		return make_empty_hosted_function_node(binding, {"this", "__x"});
	if (hosted_rbtree_copy_constructor_binding(binding))
		return make_empty_hosted_function_node(binding, {"this", "__x"});
	if (hosted_temporary_buffer_constructor_binding(binding))
		return make_empty_hosted_function_node(
			binding, {"this", "__seed", "__original_len"});
	if (hosted_hashtable_local_guard_destructor_binding(binding))
		return make_empty_hosted_function_node(binding, {"this"});
	if (hosted_hashtable_ebo_helper_copy_constructor_binding(binding))
		return make_empty_hosted_function_node(binding, {"this", "__x"});
	if (hosted_hashtable_allocator_move_constructor_binding(binding))
		return make_empty_hosted_function_node(
			binding, {"this", "__ht", "__alloc", "__true_type"});
	if (hosted_shared_count_copy_constructor_binding(binding))
		return make_empty_hosted_function_node(binding, {"this", "__r"});
	if (hosted_shared_count_assignment_binding(binding))
		return make_empty_hosted_function_node(binding, {"this", "__r"});
	if (hosted_shared_ptr_assignment_binding(binding))
		return make_empty_hosted_function_node(binding, {"this", "__r"});
	if (hosted_make_exception_ptr_binding(binding))
		return make_empty_hosted_function_node(binding, {"__ex"});
	if (hosted_stoa_binding(binding))
	{
		vector<string> names;
		names.push_back("__convf");
		names.push_back("__name");
		names.push_back("__str");
		names.push_back("__idx");
		for (size_t i = 4; i < binding->type->parameters.size(); ++i)
			names.push_back("__base" + to_string(i - 4));
		return make_empty_hosted_function_node(binding, names);
	}
	throw runtime_error("unsupported hosted inline body");
}

}  // namespace internal
}  // namespace pa14
