#pragma once

#include "pa14_lowir.h"

#include "pa12_internal.h"

#include <map>
#include <functional>
#include <memory>
#include <set>
#include <sstream>
#include <stdexcept>
#include <string>
#include <vector>

using namespace std;

namespace pa14 {
namespace internal {

using pa11::Binding;
using pa11::BindingKind;
using pa11::Scope;
using pa11::ScopeKind;
using pa11::TypeKind;
using pa11::TypePtr;
using pa12::internal::Node;
using pa12::internal::ValueCategory;

struct Value
{
	string type;
	string text;

	Value() {}
	Value(const string& t, const string& v) : type(t), text(v) {}
};

struct Block
{
	string name;
	vector<string> instrs;
	bool terminated;

	explicit Block(const string& n) : name(n), terminated(false) {}
};

struct FunctionOut
{
	const Binding* binding;
	string name;
	string header;
	bool has_range_for_state;
	bool strong_binding;
	bool returns_pointer_result;
	vector<string> slots;
	vector<Block> blocks;

	FunctionOut()
		: binding(NULL),
		  has_range_for_state(false),
		  strong_binding(false),
		  returns_pointer_result(false) {}
};
FunctionOut make_constructor_base_entry(const FunctionOut& lowered,
                                        const string& name);

struct InitAction
{
	string target;
	string kind;
	string symbol;

	InitAction() {}
	InitAction(const string& t, const string& k, const string& s)
		: target(t), kind(k), symbol(s) {}
};

struct Cleanup
{
	Binding* binding;
	TypePtr type;
	string addr;
	string instruction;
	bool force_destructor_call;

	Cleanup() : binding(NULL), force_destructor_call(false) {}
	Cleanup(Binding* b, TypePtr t, bool force = false)
		: binding(b), type(t), force_destructor_call(force) {}
	Cleanup(const string& a, TypePtr t, bool force = false)
		: binding(NULL), type(t), addr(a), force_destructor_call(force) {}
	explicit Cleanup(const string& instr)
		: binding(NULL), instruction(instr), force_destructor_call(false) {}
};

struct PendingConstructorConversion
{
	size_t index;
	Value value;
	TypePtr from;
	TypePtr to;
};

bool starts_with(const string& text, const string& prefix);
TypePtr object_type(TypePtr type);
TypePtr strip_for_value(TypePtr type);
bool is_reference(TypePtr type);
bool is_float_type(TypePtr type);
bool is_unsigned_type(TypePtr type);
string scalar_lowir_type(TypePtr type);
int lowir_arithmetic_rank(TypePtr type);
TypePtr lowir_integral_promotion(TypePtr type);
TypePtr lowir_common_type(TypePtr left, TypePtr right);
string slot_lowir_type(TypePtr type);
bool record_pass_by_address(TypePtr type);
bool record_return_by_address(TypePtr type);
bool record_has_nontrivial_value_transfer(TypePtr type);
bool record_has_storage_copy(TypePtr type);
string lowir_literal(TypePtr type, const Node& node);
string lowir_parameter(TypePtr type);
string metadata_suffix(const vector<string>& items);
vector<string> qualified_parts(const Binding* binding);
string source_symbol_base(const Binding* binding);
string global_object_symbol(const Binding* binding);
bool node_contains_call_expression(const Node& node);
bool record_has_default_constructor_for_array(TypePtr type);
bool record_has_base_subobject(TypePtr source, TypePtr target);
uint64_t base_subobject_offset(TypePtr source, TypePtr target);
Binding* find_constructor(TypePtr type, size_t arg_count);
const Node* record_prvalue_child_for_xvalue(const Node& arg);
bool defaulted_copy_move_constructor_needs_helper(Binding* binding, TypePtr type);
Binding* find_any_copy_move_constructor(TypePtr type, bool move);
Binding* find_copy_move_constructor(TypePtr type, bool move);
bool inline_defaulted_copy_move_storage_constructor(Binding* binding,
                                                   TypePtr type,
                                                   const Node& init);
Binding* find_destructor(TypePtr type);
bool type_needs_destructor(TypePtr type);
bool default_init_no_op(TypePtr type);
bool no_op_generated_default_constructor(Binding* ctor, TypePtr type);
bool has_inline_constructor(TypePtr type);
bool is_brace_elision_aggregate(TypePtr type);
bool is_string_literal_node(const Node& node);
bool zero_init_has_store(TypePtr type);
bool type_has_reference_subobject(TypePtr type);
bool record_has_user_assignment_operator(TypePtr type);
string zero_integer_type(uint64_t size);
bool same_record_initializer(const Node& init, TypePtr type);
bool record_has_base(TypePtr source, TypePtr target);
bool is_class_constructor_binding(const Binding* binding);
bool is_class_destructor_binding(const Binding* binding);
TypePtr class_record_for_member(const Binding* binding);
bool record_is_template_specialization(TypePtr record);
bool binding_has_template_specialization_context(const Binding* binding);
bool template_static_member_definition_matches(const Binding* use,
                                               const Binding* definition);
string record_lowir_name(TypePtr record);
bool template_record_uses_abi_global_symbol(TypePtr record);
string template_record_global_symbol_part(TypePtr record);
string vtable_symbol_for_record(TypePtr record);
string rtti_symbol_for_record(TypePtr record);

struct ProgramLowerer
{
	vector<string> declares;
	vector<string> global_declares;
	vector<string> globals;
	vector<FunctionOut> functions;
	vector<FunctionOut> pending_synthetic_assignment_functions;
	map<const Binding*, string> symbols;
	map<string, int> used_symbols;
	map<string, string> function_symbols;
	set<string> defined_functions;
	set<string> declared_functions;
	set<string> defined_globals;
	set<string> declared_globals;
	vector<const Binding*> global_definition_bindings;
	map<const Binding*, Node> global_definition_nodes;
	map<string, string> string_literals;
	map<string, string> string_literal_types;
		vector<pair<string, vector<uint32_t> > > string_defs;
	map<const Binding*, const Node*> inline_definitions;
	map<const Binding*, Node> synthetic_inline_definitions;
	map<const Binding*, Node> deferred_global_definitions;
		map<const Binding*, size_t> inline_definition_ranks;
	map<const Binding*, string> function_declarations_by_binding;
	set<const Binding*> demanded_inline_complete_entries;
	set<const Binding*> demanded_constructor_base_entries;
	set<const Binding*> demanded_destructor_base_entries;
	set<const void*> emitted_vtables;
	set<const void*> emitted_rtti;
	set<string> declared_pure_virtual_signatures;
	set<const Binding*> emitted_deleting_destructors;
	map<const void*, Binding*> implicit_copy_assignments;
	map<const void*, Binding*> implicit_move_assignments;
	vector<const Binding*> pending_inline_definitions;
	vector<InitAction> init_actions;
	vector<Node> global_init_variables;
	vector<Node> thread_local_init_variables;
	vector<Node> global_fini_variables;
	vector<unique_ptr<Binding> > synthetic_bindings;
	const Binding* active_inline_definition;
	size_t active_inline_dependency_insert_count;
	bool needs_empty_init_function;
	bool needs_eh_declarations;
		int generated_assignment_emit_depth;

		typedef vector<const Binding*>::iterator PendingInlineIterator;

		ProgramLowerer();
	string symbol_for(const Binding* binding);
	string constructor_symbol_for(const Binding* binding, bool base_entry);
	string destructor_symbol_for(const Binding* binding, bool base_entry);
	string string_symbol(const string& token_text);
	void demand_vtable(TypePtr record);
	void emit_rtti(TypePtr record);
	void emit_typeinfo(TypePtr type);
	string catch_rtti_symbol(TypePtr type);
	void emit_deleting_destructor_entry(const Binding* dtor);
	void register_inline_definition(const Node& node);
	void register_function_declaration(const Node& node);
	void demand_function_declaration(const Binding* binding);
	void demand_global_declaration(const Binding* binding);
	bool demand_deferred_global_definition(const Binding* binding);
	bool template_static_member_constant_load_required(
		const Binding* binding) const;
	string ensure_local_static_guard(const Binding* binding);
	void ensure_thread_local_wrapper(const string& global_name);
	void ensure_eh_declarations();
	Binding* demand_implicit_copy_assignment(TypePtr type, bool move);
	void queue_synthetic_assignment_function(Binding* binding,
	                                         TypePtr record,
	                                         bool move,
	                                         const string& name);
	void emit_pending_generated_aggregate_constructors();
		void demand_move_assignment_copy_dependency(const Binding* binding);
		void insert_pending_inline_definition(const Binding* binding);
		void place_lvalue_assignment_before_rvalue_assignment(
			const Binding* binding, PendingInlineIterator& pos);
		void place_user_assignment_before_owner_members(
			const Binding* binding, PendingInlineIterator& pos);
		void place_record_return_before_matching_constructor(
			const Binding* binding, PendingInlineIterator& pos);
		void place_record_return_before_owner_scalar_member(
			const Binding* binding, PendingInlineIterator& pos);
		void place_record_return_before_pending_operator(
			const Binding* binding, PendingInlineIterator& pos);
		void place_constructor_after_pending_record_operator(
			const Binding* binding, PendingInlineIterator& pos);
		void place_local_constructor_after_shorter_overload(
			const Binding* binding, PendingInlineIterator& pos);
		void place_constructor_inline_definition(
			const Binding* binding, PendingInlineIterator& pos);
		void place_destructor_inline_definition(
			const Binding* binding, PendingInlineIterator& pos);
		void place_const_conversion_before_mutable_conversion(
			const Binding* binding, PendingInlineIterator& pos);
		void place_specialized_conversion_before_base_conversion(
			const Binding* binding, PendingInlineIterator& pos);
		void place_ranked_template_operator(
			const Binding* binding, PendingInlineIterator& pos);
		void place_ranked_owner_member(
			const Binding* binding, PendingInlineIterator& pos);
		void place_subscript_before_pending_operators(
			const Binding* binding, PendingInlineIterator& pos);
		void place_before_late_operator_or_generated_assignment(
			const Binding* binding, PendingInlineIterator& pos);
		void place_before_generated_default_constructor(
			const Binding* binding, PendingInlineIterator& pos);
		void place_active_destructor_dependency(
			const Binding* binding, PendingInlineIterator& pos);
		void place_active_record_return_dependency(
			const Binding* binding, PendingInlineIterator& pos);
		void place_before_pending_captureless_lambda_helper(
			const Binding* binding, PendingInlineIterator& pos);
		void place_after_pending_reference_constructor(
			const Binding* binding, PendingInlineIterator& pos);
		void place_scalar_helper_after_record_returns(
			const Binding* binding, PendingInlineIterator& pos);
		void place_value_constructor_after_scalar_helpers(
			const Binding* binding, PendingInlineIterator& pos);
		void place_scalar_helper_before_value_constructor(
			const Binding* binding, PendingInlineIterator& pos);
		void place_static_template_member_after_pending_scalar_templates(
			const Binding* binding, PendingInlineIterator& pos);
		void place_static_member_before_later_owner_static_member(
			const Binding* binding, PendingInlineIterator& pos);
		void place_constructor_destructor_pair(
			const Binding* binding, PendingInlineIterator& pos);
		void place_constructor_after_record_return_dependency(
			const Binding* binding, PendingInlineIterator& pos);
		void emit_pending_synthetic_assignment_functions();
	void demand_inline_function(const Binding* binding,
	                            bool complete_entry = true);
	void emit_pending_inline_definitions();
	void emit_global_lifecycle_functions();
	void collect_translation_unit(const Node& root);
	void collect_node(const Node& node);
	void emit_global(const Node& node);
	void demand_initializer_calls(const Node& node);
	void demand_initializer_type_calls(TypePtr type, const Node& node);
	string global_scalar_initializer(TypePtr type, const Node& init);
	string global_data_item(TypePtr elem, const Node& init);
	void write_global_data_items(ostringstream& out, TypePtr elem, const Node& init);
	void write_global_zero_items(ostringstream& out, TypePtr elem);
	void write(const string& outfile) const;
};

vector<size_t> ordered_function_indices(const ProgramLowerer& program);

class FunctionLowerer
{
public:
	FunctionLowerer(ProgramLowerer& program, const Node& fn);

	FunctionOut lower();

private:
	ProgramLowerer& program_;
	const Node& fn_;
	FunctionOut out_;
	vector<unique_ptr<Block> > blocks_;
	Block* current_;
	map<const Binding*, string> slots_;
	map<string, int> slot_names_;
	vector<string> break_targets_;
	vector<string> continue_targets_;
	vector<vector<Cleanup> > cleanups_;
	set<const Binding*> by_address_parameters_;
	set<const Binding*> return_slot_variables_;
	set<uint64_t> initialized_bitfield_storage_;
	vector<pair<Value, TypePtr> > pending_temp_cleanups_;
	map<string, string> labels_;
	map<const Node*, string> switch_labels_;
	int temp_counter_;
	int block_counter_;
	int aux_slot_counter_;
	int eh_try_depth_;
	int call_temp_cleanup_defer_depth_;
	string logical_call_result_slot_;
	TypePtr logical_call_result_type_;
	bool logical_call_result_consumed_;
	string call_result_store_slot_;
	TypePtr call_result_store_type_;
	bool call_result_store_consumed_;
	string record_return_slot_;
	bool lowering_record_return_object_;
	bool lowering_array_subobject_init_;
	bool constructor_destination_before_protected_try_;
	string active_unwind_dispatch_;

	void add_slot(const string& name, const string& type);
	string slot_for(const Binding* binding);
	string fresh_temp();
	string fresh_block(const string& prefix);
	string fresh_aux_slot(const string& prefix, const string& type);
	void start_block(const string& name);
	void instr(const string& text);
	void terminate(const string& text);

	void lower_params();
	void lower_param_stores();
	bool lower_defaulted_storage_special_member();
	void lower_stmt(const Node& node);
	void lower_compound(const Node& node);
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
	Value emit_base_subobject_addr(Value object, TypePtr source, TypePtr target);
	void lower_aggregate_init(const function<Value()>& addr_for,
	                          TypePtr type,
	                          const Node& init);
	void lower_direct_array_init(Value base, TypePtr type, const Node& init);
	Value direct_array_element_addr(Value base, TypePtr elem, size_t index);
	void lower_aggregate_elements(const function<Value()>& addr_for,
	                              TypePtr type,
	                              const vector<Node>& clauses,
	                              size_t& index);
		void lower_object_init(const function<Value()>& addr_for,
		                       TypePtr type,
		                       const Node& init);
		bool lower_braced_object_init(const function<Value()>& addr_for,
		                              TypePtr type,
		                              const Node& init);
		bool lower_braced_direct_constructor_init(
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
	void lower_default_init(const function<Value()>& addr_for, TypePtr type);
	void lower_storage_zero(Value addr, uint64_t size);
	void lower_constructor_call(const function<Value()>& addr_for,
	                            Binding* ctor,
	                            const vector<const Node*>& args,
	                            bool base_entry = false);
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
	void lower_return(const Node& node);
	void register_cleanup(Binding* binding, TypePtr type);
	void emit_scope_cleanups(vector<Cleanup>& scope);
	void emit_all_cleanups();
	void lower_vptr_store(TypePtr record);
	void maybe_lower_constructor_vptr(size_t index, size_t total);
	void maybe_lower_destructor_epilogue(bool& emitted);
	bool has_active_cleanups() const;
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
	Value emit_lvalue_addr(const Node& expr);
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
	Value emit_unary(const Node& expr);
	Value emit_postfix(const Node& expr);
	Value emit_call(const Node& expr);
	bool lower_indirect_record_call(const function<Value()>& addr_for,
	                                const Node& expr);
	void lower_call_argument(const Node& arg,
	                         TypePtr param,
	                         vector<string>& args,
	                         vector<pair<Value, TypePtr> >* temp_cleanups = NULL);
	void lower_reference_call_argument(const Node& arg,
	                                   TypePtr param,
	                                   vector<string>& args,
	                                   vector<pair<Value, TypePtr> >* temp_cleanups = NULL);
	void lower_value_call_argument(const Node& arg,
	                               TypePtr param,
	                               vector<string>& args,
	                               vector<pair<Value, TypePtr> >* temp_cleanups = NULL);
	bool lower_temporary_record_pointer_argument(const Node& arg,
	                                             TypePtr param,
	                                             vector<string>& args,
	                                             vector<pair<Value, TypePtr> >* temp_cleanups = NULL);
	bool call_argument_may_create_temp_cleanup(const Node& arg,
	                                           TypePtr param) const;
	bool call_setup_can_use_outer_eh(const Node& expr,
	                                 TypePtr callee_type,
	                                 size_t arg_start) const;
	void lower_record_value_argument(const Node& arg,
	                                 TypePtr param,
	                                 vector<string>& args);
	Value emit_subscript_addr(const Node& expr);
	Value emit_cast(const Node& expr);
	Value emit_conditional(const Node& expr);
	Value emit_conditional_value(const Node& expr);
	Value convert_value(Value value,
	                    TypePtr from,
	                    TypePtr to,
	                    bool fold_literals = true);
	Value convert_binary_value(Value value, TypePtr from, TypePtr to);
	Value bool_value(Value value, TypePtr type);
	Value ensure_pointer(Value storage);
	void branch_logical_operand(const Node& expr, const string& yes, const string& no);
	void branch_with_unwind_cleanups(const Node& expr,
	                                 const string& yes,
	                                 const string& no);
	void branch_on(const Node& expr, const string& yes, const string& no);
};


}  // namespace internal
}  // namespace pa14
