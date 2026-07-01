#pragma once
#include "pa14_lowir_internal.h"
namespace pa14 {
namespace internal {
	bool hosted_vector_temporary_value_destructor(const Binding* binding);
	struct ActiveCatchContext
	{
		string rtti;
			bool catch_all;
			string entry;
			int selector;
			size_t cleanup_depth;
			ActiveCatchContext()
				: catch_all(false), selector(1), cleanup_depth(0)
			{
			}
		};
	class FunctionLowerer
	{
public:
	FunctionLowerer(ProgramLowerer& program,
	                const Node& fn,
	                bool destructor_base_entry = false);
	FunctionOut lower();
	FunctionOut lower_deleting_destructor_entry(const string& name,
	                                            const string& header);
private:
	struct CallEmissionState
	{
		const Node* expr;
		Binding* direct;
		size_t arg_start;
		string callee;
		TypePtr callee_type;
		bool virtual_call;
		int virtual_slot_index;
		bool delay_direct_demand;
		string ret;
		string preallocated_call_slot;
		vector<string> args;
		vector<TypePtr> arg_types;
			vector<pair<Value, TypePtr> > temp_cleanups;
			bool setup_may_create_temp_cleanup;
			bool setup_contains_call;
			bool setup_object_contains_call;
			bool protect_setup_only;
			bool protected_setup;
		string protected_dispatch;
		bool protected_define_dispatch;
		bool temp_cleanup_region_open;
		string temp_cleanup_dispatch;
		string temp_cleanup_end;
		string call_text;
		string tmp;
		bool cleanup_temps_in_call;
		CallEmissionState()
			: expr(NULL),
			  direct(NULL),
			  arg_start(1),
			  virtual_call(false),
				  virtual_slot_index(-1),
				  delay_direct_demand(false),
				  setup_may_create_temp_cleanup(false),
				  setup_contains_call(false),
				  setup_object_contains_call(false),
				  protect_setup_only(false),
			  protected_setup(false),
			  protected_define_dispatch(false),
			  temp_cleanup_region_open(false),
			  cleanup_temps_in_call(false)
		{
		}
	};
	ProgramLowerer& program_;
	const Node& fn_;
	bool destructor_base_entry_;
	FunctionOut out_;
	vector<unique_ptr<Block> > blocks_;
	Block* current_;
	map<const Binding*, string> slots_;
	map<string, int> slot_names_;
	vector<string> break_targets_;
	vector<string> continue_targets_;
	vector<size_t> break_cleanup_depths_;
	vector<size_t> continue_cleanup_depths_;
	vector<vector<Cleanup> > cleanups_;
	set<const Binding*> by_address_parameters_;
	set<const Binding*> return_slot_variables_;
		set<uint64_t> initialized_bitfield_storage_;
		vector<pair<Value, TypePtr> > pending_temp_cleanups_;
		map<string, string> labels_;
		map<string, size_t> label_cleanup_depths_;
		map<const Node*, string> switch_labels_;
	int temp_counter_;
	int block_counter_;
	int aux_slot_counter_;
	int eh_try_depth_;
	int call_temp_cleanup_defer_depth_;
	string logical_call_result_slot_;
	TypePtr logical_call_result_type_;
	const Node* logical_call_result_expr_;
	bool logical_call_result_consumed_;
	string call_result_store_slot_;
	string call_result_store_addr_;
	TypePtr call_result_store_type_;
	const Node* call_result_store_expr_;
	bool call_result_store_consumed_;
	string record_return_slot_;
	bool lowering_record_return_object_;
	bool lowering_array_subobject_init_;
		bool constructor_destination_before_protected_try_;
			vector<const Node*> constructor_unwind_actions_;
			string active_unwind_dispatch_;
			size_t active_unwind_cleanup_depth_;
			vector<ActiveCatchContext> active_catches_;
	void add_slot(const string& name, const string& type);
	string slot_for(const Binding* binding);
	string this_slot_name();
	string fresh_temp();
	string fresh_block(const string& prefix);
	string fresh_aux_slot(const string& prefix, const string& type);
		void start_block(const string& name);
		void instr(const string& text);
		void terminate(const string& text);
		void collect_label_cleanup_depths(const Node& node, size_t depth);
		void emit_goto_cleanups(const string& label);
		void emit_control_transfer_cleanups(size_t target_depth);
		bool initialize_function_header(Binding* binding, TypePtr fn_type);
		void lower_params();
	void lower_param_stores();
	bool lower_defaulted_storage_special_member();
	bool lower_hosted_vector_bool_move_body();
	bool lower_hosted_hashtable_count_constructor_body();
	bool lower_hosted_hashtable_range_constructor_body();
	bool lower_hosted_hash_code_base_hash_code_body();
	bool lower_hosted_vector_range_insert_body();
	bool lower_hosted_vector_realloc_insert_body();
	bool lower_hosted_vector_relocate_body();
	void store_hosted_vector_bool_empty(const string& object);
	void emit_hosted_vector_bool_copy_from(const string& object,
	                                       const string& source_object,
	                                       const string& next_block);
	void emit_hosted_vector_copy_construct_loop(const string& src_begin,
	                                            const string& src_end,
	                                            const string& dst_begin,
	                                            TypePtr element,
	                                            Binding* copy_ctor,
	                                            const string& label);
	void emit_hosted_vector_copy_assign_loop(const string& src_begin,
	                                         const string& src_end,
	                                         const string& dst_begin,
	                                         TypePtr element,
	                                         Binding* copy_assign,
	                                         const string& label);
	void emit_hosted_vector_destroy_loop(const string& begin,
	                                     const string& end,
	                                     TypePtr element,
	                                     const string& label);
	void emit_hosted_vector_assignment_grow(const string& object,
	                                        const string& start,
	                                        const string& finish,
	                                        const string& source_start,
	                                        const string& source_finish,
	                                        const string& source_bytes,
	                                        const string& finish_addr,
	                                        const string& end_storage_addr,
	                                        TypePtr element,
	                                        Binding* copy_ctor,
	                                        const string& done_block);
	void emit_hosted_vector_assignment_fit(const string& start,
	                                       const string& finish,
	                                       const string& source_start,
	                                       const string& source_finish,
	                                       const string& source_bytes,
	                                       const string& old_size_bytes,
	                                       const string& finish_addr,
	                                       TypePtr element,
	                                       Binding* copy_ctor,
	                                       Binding* copy_assign,
	                                       const string& done_block);
	bool lower_hosted_vector_copy_constructor_body();
	bool lower_hosted_vector_copy_assignment_body();
	bool lower_hosted_vector_bool_copy_assignment_body();
	bool lower_hosted_vector_impl_move_constructor_body();
	bool lower_hosted_std_function_swap_body();
	bool lower_hosted_rbtree_assignment_body();
	bool lower_hosted_rbtree_const_iterator_node_constructor_body();
	bool lower_hosted_tuple_storage_default_constructor_body();
	bool lower_hosted_tuple_storage_head_body();
	bool lower_hosted_tuple_reference_constructor_body();
	bool lower_hosted_forward_as_tuple_body();
	bool lower_hosted_unique_ptr_destructor_body();
	bool lower_hosted_unique_ptr_impl_constructor_body();
	bool lower_hosted_unique_ptr_impl_assignment_body();
	bool lower_hosted_iter_equals_val_constructor_body();
	bool lower_hosted_normal_iterator_member_body();
	bool lower_hosted_normal_iterator_difference_body();
	bool lower_hosted_ops_compare_constructor_body();
	bool lower_hosted_uninit_destroy_guard_constructor_body();
	bool lower_hosted_uninit_destroy_guard_release_body();
	bool lower_hosted_to_address_body();
	bool lower_hosted_type_info_comparison_body();
	bool lower_hosted_vector_bool_s_nword_body();
	bool lower_hosted_deque_iterator_difference_body();
	bool lower_hosted_deque_iterator_order_body();
	bool lower_hosted_deque_iterator_plus_body();
	bool lower_hosted_bit_iterator_base_comparison_body();
	bool lower_hosted_bit_iterator_base_difference_body();
	bool lower_hosted_bit_iterator_plus_body();
	bool lower_hosted_bit_const_iterator_deref_body();
	bool lower_hosted_bit_const_iterator_preincrement_body();
	bool lower_hosted_equal_aux1_basic_string_body();
	bool lower_hosted_lexicographical_compare_int_body();
	bool lower_hosted_uninitialized_default_n_trivial_body();
	bool lower_hosted_allocator_comparison_body();
	bool lower_hosted_allocator_destroy_body();
	bool lower_hosted_alloc_traits_propagate_body();
	bool lower_hosted_pair_default_constructor_body();
	bool lower_hosted_pair_piecewise_index_constructor_body();
	bool lower_hosted_pair_assignment_body();
	bool lower_hosted_rbtree_copy_constructor_body();
	bool lower_hosted_temporary_buffer_constructor_body();
	bool lower_hosted_shared_control_body();
	bool lower_hosted_basic_string_guard_destructor_body();
	bool lower_hosted_uninit_destroy_guard_destructor_body();
	bool lower_hosted_vector_guard_elts_destructor_body();
	bool lower_hosted_vector_base_deallocate_body(), lower_hosted_vector_guard_alloc_destructor_body(), lower_hosted_iterator_comparison_body();
	bool lower_hosted_shared_count_copy_body(), lower_hosted_shared_count_assignment_body(), lower_hosted_shared_ptr_assignment_body();
	bool lower_hosted_make_exception_ptr_body();
	bool lower_hosted_stoa_body();
	string emit_hosted_stoa_conversion_call(Binding* binding, TypePtr conv_fn, const string& convf, const string& str, const string& end_addr, const string& conv_ret_type);
	void lower_stmt(const Node& node);
	void lower_compound(const Node& node);
	void lower_deleting_destructor_compound(const Node& node);
	void lower_deleting_destructor_nonvirtual_bases(TypePtr record);
	void lower_decl_stmt(const Node& node);
		void lower_variable_decl(const Node& var);
		bool lower_braced_variable_init(const Node& var, TypePtr type);
		void lower_global_variable_init(const Node& var);
		bool lower_constructor_action_global_init(const Node& var);
		bool lower_generated_aggregate_global_init(const Node& var,
		                                           const Node& init);
		bool lower_function_pointer_global_init(const Node& var,
		                                        const Node& init);
		bool lower_static_member_storage_global_init(const Node& var,
		                                             const Node& init);
		function<Value()> global_storage_addr_for(const Node& var);
		function<Value()> global_variable_addr_for(const Node& var);
		void lower_local_static_array_global_init(
			const function<Value()>& addr_for,
			TypePtr bare,
			const Node& init);
		bool lower_local_static_global_init(const Node& var,
		                                    const function<Value()>& addr_for,
		                                    TypePtr bare,
		                                    const Node& init);
		void lower_thread_local_variable_init(const Node& node);
	void lower_global_variable_fini(const Node& var);
	void lower_local_static_decl(const Node& var);
	void lower_destructor_for_object(const function<Value()>& addr_for,
	                                 TypePtr type);
	bool type_needs_cleanup(TypePtr type) const;
		void lower_scope_destructor_for_object(const function<Value()>& addr_for,
		                                       TypePtr type);
		void emit_active_catch_clause(const ActiveCatchContext& ctx);
		void emit_unwind_object_cleanups();
		void emit_rethrow_object_cleanups();
	void lower_member_fini(const Node& node);
	void lower_base_fini(const Node& node);
	void lower_member_init(const Node& node);
	bool lower_direct_member_constructor_init(
		const Node& node,
		const function<Value()>& member_addr);
	void lower_scalar_member_init(const Node& node,
	                              const function<Value()>& member_addr);
	void lower_delegating_init(const Node& node);
	void lower_storage_copy_action(const Node& node);
	void lower_bitfield_member_init(const Node& node,
	                                Value value,
	                                const function<Value()>& member_addr);
	void lower_base_init(const Node& node);
	bool lower_defaulted_assignment_fields(TypePtr record,
	                                       bool move,
	                                       const string& other_name);
	bool lower_defaulted_constructor_fields(TypePtr record,
	                                        bool move,
	                                        const string& other_name);
	Value emit_base_subobject_addr(Value object, TypePtr source, TypePtr target);
	const Binding* hidden_virtual_base_parameter_binding(
		const Node& expr) const;
	bool hidden_virtual_base_argument_for_parameter(
		const Binding* binding,
		TypePtr target,
		string& hidden_base,
		TypePtr& hidden_base_record);
	Value emit_hidden_virtual_base_addr_for_lvalue(const Node& expr,
	                                              TypePtr target,
	                                              bool& found,
	                                              TypePtr* hidden_record = NULL);
	void lower_aggregate_init(const function<Value()>& addr_for,
	                          TypePtr type,
	                          const Node& init);
	void lower_direct_array_init(Value base, TypePtr type, const Node& init);
	Value direct_array_element_addr(Value base, TypePtr elem, size_t index);
		void lower_aggregate_elements(const function<Value()>& addr_for,
		                              TypePtr type,
		                              const vector<Node>& clauses,
		                              size_t& index);
		void lower_union_aggregate_elements(const function<Value()>& addr_for, TypePtr bare, const vector<Node>& clauses, size_t& index);
			void lower_record_base_aggregate_elements(const function<Value()>& addr_for, TypePtr bare, const vector<Node>& clauses, size_t& index);
			void lower_record_field_aggregate_elements(const function<Value()>& addr_for, TypePtr bare, const vector<Node>& clauses, size_t& index);
			void lower_record_field_aggregate_element(const function<Value()>& addr_for, Binding* field, const vector<Node>& clauses, size_t& index);
			void lower_bitfield_aggregate_field(const function<Value()>& field_addr, Binding* field, const Node& child);
			void lower_array_aggregate_elements(const function<Value()>& addr_for, TypePtr bare, TypePtr type, const vector<Node>& clauses, size_t& index);
		void lower_object_init(const function<Value()>& addr_for,
		                       TypePtr type,
		                       const Node& init);
		void lower_record_object_init(const function<Value()>& addr_for,
		                              TypePtr type,
		                              const Node& init);
		bool lower_record_base_cast_init(const function<Value()>& addr_for,
		                                 TypePtr type,
		                                 const Node& init);
		bool lower_hosted_normal_iterator_conversion_init(
			const function<Value()>& addr_for,
			TypePtr type,
			const Node& init);
		bool lower_known_record_conversion_init(
			const function<Value()>& addr_for,
			TypePtr type,
			const Node& init);
		bool lower_same_storage_record_conversion_init(
			const function<Value()>& addr_for,
			TypePtr type,
			const Node& init);
		bool lower_known_char_pointer_record_init(
			const function<Value()>& addr_for,
			TypePtr type,
			const Node& init);
		bool lower_record_conditional_init(const function<Value()>& addr_for,
		                                   TypePtr type,
		                                   const Node& init);
			bool lower_record_same_type_init(const function<Value()>& addr_for,
			                                 TypePtr type,
			                                 const Node& init);
			bool lower_value_constructor_prvalue_same_type_init(
				const function<Value()>& addr_for,
				TypePtr type,
				const Node& init,
				bool returned_prvalue);
			bool lower_reference_prvalue_same_type_init(
				const function<Value()>& addr_for,
				const Node& init,
				bool returned_prvalue);
			bool lower_operator_plus_same_type_init(
				const function<Value()>& addr_for,
				TypePtr type,
				const Node& init,
				bool returned_prvalue);
			Binding* same_type_copy_move_constructor(
				TypePtr type,
				TypePtr src_record,
				TypePtr dst_record,
				const Node& init,
				bool& enum_return_copy_move);
			bool lower_copy_move_same_type_init(
				const function<Value()>& addr_for,
				TypePtr type,
				TypePtr src_record,
				TypePtr dst_record,
				const Node& init);
			bool lower_direct_same_type_storage_init(
				const function<Value()>& addr_for,
				TypePtr type,
				const Node& init,
				bool returned_prvalue);
			void lower_scalar_object_init(const function<Value()>& addr_for,
			                              TypePtr type,
			                              const Node& init);
		bool lower_braced_object_init(const function<Value()>& addr_for,
		                              TypePtr type,
		                              const Node& init);
		bool lower_initializer_list_init(const function<Value()>& addr_for,
		                                 TypePtr type,
		                                 const Node& init);
		bool lower_braced_direct_constructor_init(
			const function<Value()>& addr_for,
			TypePtr type,
			const Node& init);
		bool lower_braced_copy_constructor_init(
			const function<Value()>& addr_for,
			TypePtr type,
			const Node& init);
		bool lower_braced_record_constructor_init(
			const function<Value()>& addr_for,
			TypePtr type,
			const Node& init);
		void lower_base_zero_init(const function<Value()>& addr_for,
	                          TypePtr source,
	                          TypePtr base);
	void lower_zero_init(const function<Value()>& addr_for, TypePtr type);
	bool lower_hosted_tree_container_default_init(
		const function<Value()>& addr_for,
		TypePtr type);
	bool lower_hosted_vector_default_init(
		const function<Value()>& addr_for,
		TypePtr type);
	void lower_default_init(const function<Value()>& addr_for, TypePtr type);
	void lower_storage_zero(Value addr, uint64_t size);
		void lower_constructor_call(const function<Value()>& addr_for,
		                            Binding* ctor,
		                            const vector<const Node*>& args,
		                            bool base_entry = false);
		bool lower_hosted_shared_ptr_constructor(
			const function<Value()>& addr_for,
			Binding* ctor,
			const vector<const Node*>& args);
		bool lower_hosted_vector_initializer_list_constructor(
			const function<Value()>& addr_for,
			Binding* ctor,
			const vector<const Node*>& args);
		bool lower_hosted_vector_bool_move_constructor(
			const function<Value()>& addr_for,
			Binding* ctor,
			const vector<const Node*>& args);
		void append_constructor_hidden_parameter_args(
			Binding* ctor,
			const vector<const Node*>& args,
			vector<string>& lowered);
		void append_constructor_base_entry_hidden_args(Binding* ctor,
		                                              vector<string>& lowered);
		void lower_record_reference_constructor_argument(
		const Node& arg,
		TypePtr param,
		vector<string>& lowered,
		vector<pair<Value, TypePtr> >& temp_cleanups,
		vector<PendingConstructorConversion>& pending_conversions,
		bool force_refcall_slot = false);
	void emit_constructor_call_with_cleanups(
		Binding* ctor,
		vector<string>& lowered,
		const vector<pair<Value, TypePtr> >& temp_cleanups,
		const vector<PendingConstructorConversion>& pending_conversions,
		bool base_entry = false);
	void emit_temporary_cleanups(const vector<pair<Value, TypePtr> >& temps);
	void lower_temporary_init_with_unwind(const function<Value()>& addr_for,
	                                      TypePtr type,
	                                      const Node& init);
	bool lower_string_array_init(const function<Value()>& addr_for,
	                             TypePtr type,
	                             const Node& init);
	void lower_if(const Node& node);
	void lower_while(const Node& node);
	void lower_do(const Node& node);
	void lower_for(const Node& node);
	void lower_range_for(const Node& node);
	void lower_try(const Node& node);
	void lower_catch_binding(const Node& catch_clause,
	                         const string& caught);
	bool compound_has_constructor_init_action(const Node& node) const;
	bool constructor_init_action_needs_cleanup(const Node& node) const;
	void emit_constructor_unwind_cleanups();
	void lower_return(const Node& node);
	void register_cleanup(Binding* binding, TypePtr type);
		void emit_scope_cleanups(vector<Cleanup>& scope);
		void emit_all_cleanups();
		void emit_active_catch_clauses();
		void terminate_unwind_or_active_catch();
		void emit_shared_unwind_dispatch_body();
		void lower_vptr_store(TypePtr record);
	void maybe_lower_constructor_vptr(size_t index, size_t total);
	void maybe_lower_destructor_epilogue(bool& emitted);
	bool has_active_cleanups() const;
	bool has_active_call_protection_cleanups() const;
	bool cleanup_scope_affects_unwind(const vector<Cleanup>& scope) const;
	void clear_active_unwind_dispatch();
	void emit_unwind_cleanups_to_depth(size_t cleanup_depth);
	void emit_unwind_cleanups();
	void add_pending_temp_cleanup(Value addr, TypePtr type);
	bool has_pending_temp_cleanups() const;
	bool node_may_create_temp_cleanup(const Node& node) const;
	void emit_pending_temp_cleanups();
	void terminate_with_pending_temp_cleanups(const string& prefix,
	                                         const string& yes,
	                                         const string& no);
	void lower_expr_stmt(const Node& node);
	void lower_discarded_expr(const Node& expr);
	void lower_switch(const Node& node);
	void lower_switch_items(const Node& node,
	                        vector<pair<string, const Node*> >& cases,
	                        const Node*& default_node);
		Value emit_rvalue(const Node& expr);
		Value emit_statement_expression(const Node& expr);
		Value emit_member_pointer_function_rvalue(const Node& expr);
		Value emit_call_rvalue(const Node& expr);
		Value emit_new_expression(const Node& expr);
		Value emit_array_new_expression(const Node& expr, TypePtr object);
		Value emit_scalar_new_expression(const Node& expr, TypePtr object);
		Value emit_delete_expression(const Node& expr);
		Value emit_pseudo_destructor_rvalue(const Node& expr);
		void emit_builtin_va_start(const Node& expr);
	Value emit_builtin_va_arg(const Node& expr);
	Value emit_builtin_alloca(const Node& expr);
	Value emit_c11_atomic_builtin(const Node& expr);
	Value emit_gnu_atomic_builtin(const Node& expr);
	Value emit_builtin_bit_count(const Node& expr);
	Value emit_builtin_assume_aligned(const Node& expr);
	Value emit_builtin_prefetch(const Node& expr);
	Value emit_builtin_operator_new_delete(const Node& expr);
	Value emit_builtin_overflow(const Node& expr);
	Value emit_builtin_flt_rounds(const Node& expr);
		Value emit_builtin_fpclassify(const Node& expr);
		Value emit_builtin_fp_test(const Node& expr);
		Value emit_builtin_float_constant(const Node& expr);
		Value emit_initializer_list_accessor_call(const Node& expr,
		                                          bool& handled);
		Value emit_hosted_vector_accessor_call(const Node& expr,
		                                       bool& handled);
		Value emit_lvalue_addr(const Node& expr);
	Value hosted_hash_node_object_addr(const Node& object,
	                                   TypePtr object_expr_type);
	Value emit_hosted_hash_node_next_call(const Node& expr, bool& handled);
	Value emit_member_lvalue_addr(const Node& expr);
	Value emit_literal(const Node& expr);
	Value emit_id_rvalue(const Node& expr);
	Value emit_binary(const Node& expr);
	Value emit_logical_binary(const Node& expr);
	Value emit_pointer_index_binary(const Node& expr,
	                                Value lhs,
	                                Value rhs,
	                                TypePtr lhs_type,
	                                TypePtr rhs_type);
		Value emit_pointer_difference(const Node& expr,
		                              Value lhs,
		                              Value rhs,
		                              TypePtr lhs_type);
		Value emit_assignment(const Node& expr);
		Value emit_record_assignment(const Node& expr);
		void finish_assignment_protection(bool wrap,
		                                  bool define_dispatch,
		                                  const string& dispatch);
		Value emit_member_assignment(const Node& expr);
		Value emit_compound_assignment(const Node& expr, TypePtr lhs_type);
		Value emit_plain_assignment(const Node& expr, TypePtr lhs_type);
		Value emit_unary(const Node& expr);
	Value emit_postfix(const Node& expr);
		Value emit_call(const Node& expr);
		void init_call_target(const Node& expr, CallEmissionState& call);
		void init_direct_call_target(const Node& expr, CallEmissionState& call); void init_indirect_call_target(const Node& expr, CallEmissionState& call); void validate_call_target(const Node& expr, CallEmissionState& call);
		void preallocate_call_result_slot(const Node& expr,
	                                  CallEmissionState& call);
	void prepare_call_setup_protection(const Node& expr,
	                                   CallEmissionState& call);
	void lower_call_arguments(const Node& expr, CallEmissionState& call);
	bool lower_variadic_record_call_argument(const Node& arg,
	                                         CallEmissionState& call);
	bool append_hidden_member_object_argument(const Node& object_arg,
	                                          TypePtr owner_record,
	                                          CallEmissionState& call);
	bool append_hidden_member_object_lvalue_argument(
		const Node& hidden_lookup_arg,
		TypePtr owner_record,
		CallEmissionState& call);
	bool append_hidden_member_cast_argument(const Node& hidden_lookup_arg,
	                                        TypePtr owner_record,
	                                        CallEmissionState& call);
	void find_hidden_member_this_argument(TypePtr owner_record,
	                                      string& hidden_base,
	                                      TypePtr& hidden_base_record);
	void find_hidden_member_parameter_argument(const Node& hidden_lookup_arg,
	                                           TypePtr owner_record,
	                                           string& hidden_base,
	                                           TypePtr& hidden_base_record);
	void maybe_open_call_temp_cleanup_region(CallEmissionState& call);
	void append_hidden_call_arguments(const Node& expr,
	                                  CallEmissionState& call);
	string hidden_parameter_pvb_from_existing_parameter(const Node& arg,
	                                                   TypePtr vbase);
	string hidden_parameter_pvb_from_explicit_record(
		const Node* arg,
		const string& explicit_record_arg,
		TypePtr context,
		TypePtr vbase);
	string hidden_parameter_pvb_from_argument_value(
		const Node* arg,
		const string& explicit_record_arg,
		TypePtr context,
		TypePtr vbase);
	bool call_temp_cleanup_region_is_cleanup_only(
		const CallEmissionState& call) const;
	void append_hidden_parameter_call_arguments(const Node& expr,
	                                            CallEmissionState& call,
	                                            bool member_this_param);
	string hidden_this_call_argument(const Node* object_arg,
	                                 const string& explicit_arg,
	                                 bool object_arg_is_this,
	                                 TypePtr this_record,
	                                 TypePtr vbase,
	                                 size_t vbase_index);
	void append_hidden_this_call_arguments(const Node& expr,
	                                       CallEmissionState& call,
	                                       bool member_this_param);
		void finish_setup_only_protection(CallEmissionState& call);
		void resolve_call_callee(const Node& expr, CallEmissionState& call);
		void emit_record_return_open_cleanup_region(
			CallEmissionState& call,
			const string& call_text);
			void emit_record_return_temp_cleanup_call(
				CallEmissionState& call,
				const string& call_text);
			bool emit_record_return_call(CallEmissionState& call, Value& out);
			void build_scalar_call(CallEmissionState& call);
			Value scalar_call_result_for_store(const CallEmissionState& call,
			                                   const string& loaded);
		bool emit_protected_setup_scalar_call(CallEmissionState& call,
		                                      Value& out);
	bool emit_temp_cleanup_scalar_call(CallEmissionState& call,
	                                   Value& out);
	bool emit_active_cleanup_scalar_call(CallEmissionState& call,
	                                     Value& out);
	bool emit_hosted_vector_bool_insert_aux(CallEmissionState& call);
	bool emit_hosted_vector_range_insert(CallEmissionState& call,
	                                     Value& out);
	bool emit_packed_bit_insert_aux(CallEmissionState& call);
	bool emit_contiguous_range_insert(CallEmissionState& call, Value& out);
	void emit_contiguous_insert_fit(const string& position, const string& first, const string& tail_bytes, const string& insert_bytes, const string& new_finish, const string& finish_addr, const string& result_slot, const string& done_block);
	void emit_contiguous_insert_grow(const string& object, const string& start, const string& finish, const string& position, const string& first, const string& insert_bytes, const string& tail_bytes, const string& end_storage_addr, const string& finish_addr, const string& result_slot, const string& done_block);
	Value emit_plain_scalar_call(CallEmissionState& call);
	bool lower_indirect_record_call(const function<Value()>& addr_for,
	                                const Node& expr);
	bool lower_known_heap_factory_call(const function<Value()>& addr_for,
	                                   const Node& expr);
	bool lower_heap_object_factory_call(const function<Value()>& addr_for,
	                                    const Node& expr,
	                                    TypePtr object);
	bool lower_hosted_basic_string_cstr_init(
		const function<Value()>& addr_for,
		TypePtr type,
		const Node& arg);
	bool lower_char_pointer_record_constructor_init(
		const function<Value()>& addr_for,
		Binding* ctor,
		TypePtr allocator,
		const Node& arg);
			void lower_call_argument(const Node& arg, TypePtr param, vector<string>& args, vector<pair<Value, TypePtr> >* temp_cleanups = NULL, bool preserve_no_storage_lvalue = false);
			void lower_reference_call_argument(const Node& arg, TypePtr param, vector<string>& args, vector<pair<Value, TypePtr> >* temp_cleanups = NULL);
			void lower_record_reference_temp_argument(const Node& init, TypePtr object, TypePtr target, const string& prefix, vector<string>& args, vector<pair<Value, TypePtr> >* temp_cleanups);
			void lower_value_call_argument(const Node& arg, TypePtr param, vector<string>& args, vector<pair<Value, TypePtr> >* temp_cleanups = NULL, bool preserve_no_storage_lvalue = false);
	bool lower_temporary_record_pointer_argument(const Node& arg,
	                                             TypePtr param,
	                                             vector<string>& args,
	                                             vector<pair<Value, TypePtr> >* temp_cleanups = NULL);
	bool call_argument_may_create_temp_cleanup(const Node& arg,
	                                           TypePtr param) const;
		bool call_setup_can_use_outer_eh(const Node& expr, TypePtr callee_type, size_t arg_start) const;
		void lower_record_value_argument(const Node& arg, TypePtr param, vector<string>& args, bool preserve_no_storage_lvalue = false);
	Value emit_subscript_addr(const Node& expr);
	Value emit_cast(const Node& expr);
	Value emit_dynamic_cast(const Node& expr, bool reference_result);
	Value emit_throw(const Node& expr);
	void ensure_throw_runtime_declarations();
	void ensure_rethrow_runtime_declaration();
	void ensure_noexcept_terminate_helper();
	void ensure_unexpected_runtime_declaration();
	void emit_rethrow();
	void emit_dynamic_exception_filter(const Binding* binding);
		void emit_noexcept_terminate_landing(TypePtr ret, bool indirect_result);
		void emit_unexpected_landing(TypePtr ret, bool indirect_result);
	string ensure_exception_object_global(TypePtr object);
	string emit_exception_allocation(TypePtr object,
	                                 bool protect_throw,
	                                 string& throw_dispatch);
	void lower_throw_operand(Value allocation,
	                         TypePtr object,
	                         const Node& operand);
	string throw_destructor_argument(TypePtr object);
	void emit_throw_runtime_call(const string& allocation,
	                             const string& rtti,
	                             TypePtr object,
	                             bool protect_throw,
	                             const string& throw_dispatch);
	Value emit_typeid_lvalue_addr(const Node& expr);
	Value emit_conditional(const Node& expr);
	Value emit_conditional_value(const Node& expr);
			Value convert_value(Value value, TypePtr from, TypePtr to, bool fold_literals = true);
		Value convert_member_pointer_value(Value value,
		                                   TypePtr from,
		                                   TypePtr to,
		                                   const string& dst,
		                                   const string& src);
		Value convert_same_lowir_value(Value value,
		                               TypePtr from,
		                               TypePtr to,
		                               const string& dst);
		Value convert_binary_value(Value value, TypePtr from, TypePtr to);
	Value bool_value(Value value, TypePtr type);
	Value ensure_pointer(Value storage);
	void branch_logical_operand(const Node& expr, const string& yes, const string& no);
	void branch_with_unwind_cleanups(const Node& expr, const string& yes, const string& no);
	void branch_on(const Node& expr, const string& yes, const string& no);
};
}  // namespace internal
}  // namespace pa14
