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
#include <unordered_set>
#include <vector>
using namespace std;
namespace pa14 {
namespace internal {
using pa11::Binding; using pa11::BindingKind;
using pa11::Scope; using pa11::ScopeKind;
using pa11::TypeKind; using pa11::TypePtr;
using pa12::internal::Node; using pa12::internal::ValueCategory;
struct ProgramLowerer;
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
	vector<string> parameter_names;
	bool has_range_for_state; bool strong_binding; bool returns_pointer_result;
	bool returns_record_result;
	vector<string> slots;
	vector<Block> blocks;
	vector<pair<string, string> > constructor_base_entry_arg_rewrites;
	mutable bool reference_symbols_collected;
	mutable bool reference_positions_collected;
	mutable bool lambda_related_collected;
	mutable bool lambda_related_cached;
	mutable unordered_set<string> referenced_symbols;
	mutable map<string, size_t> referenced_symbol_positions;
	FunctionOut()
		: binding(NULL),
		  has_range_for_state(false),
		  strong_binding(false),
		  returns_pointer_result(false),
		  returns_record_result(false),
		  reference_symbols_collected(false),
		  reference_positions_collected(false),
		  lambda_related_collected(false),
		  lambda_related_cached(false) {}
	FunctionOut(const FunctionOut& other);
	FunctionOut& operator=(const FunctionOut& other);
};
class NativeLifecycleDemandScope
{
public:
	explicit NativeLifecycleDemandScope(bool enabled);
	~NativeLifecycleDemandScope();
private:
	bool previous_;
};
FunctionOut make_constructor_base_entry(const FunctionOut& lowered, const string& name);
FunctionOut make_destructor_base_entry(const FunctionOut& lowered, const string& name, bool native_lowering = false);
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
	bool starts_with(const string& text, const string& prefix); TypePtr object_type(TypePtr type);
	TypePtr strip_for_value(TypePtr type); TypePtr substituted_expression_type(const Node& expr);
	bool is_reference(TypePtr type); bool is_float_type(TypePtr type); bool is_unsigned_type(TypePtr type);
	bool is_initializer_list_type(TypePtr type, TypePtr* element = NULL);
string scalar_lowir_type(TypePtr type);
int lowir_arithmetic_rank(TypePtr type);
TypePtr lowir_integral_promotion(TypePtr type);
TypePtr lowir_common_type(TypePtr left, TypePtr right);
string slot_lowir_type(TypePtr type);
bool record_pass_by_address(TypePtr type);
bool record_return_by_address(TypePtr type);
bool record_has_nontrivial_value_transfer(TypePtr type);
bool record_has_storage_copy(TypePtr type);
bool hosted_shared_ptr_record(TypePtr type);
bool function_signature_has_unresolved_storage(const Binding* binding);
bool node_tree_has_unresolved_storage(const Node& node);
string lowir_literal(TypePtr type, const Node& node);
string lowir_parameter(TypePtr type);
string metadata_suffix(const vector<string>& items);
vector<string> qualified_parts(const Binding* binding);
string source_symbol_base(const Binding* binding);
string global_object_symbol(const Binding* binding);
void clear_global_object_symbol_cache();
void clear_same_binding_or_alias_cache();
void clear_lowir_emit_caches();
void clear_lowir_emit_root_caches();
void clear_lowir_function_order_caches();
void clear_lowir_function_order_early_caches();
void clear_lowir_inline_order_caches();
void clear_lowir_inline_order_ranked_caches();
bool binding_has_internal_linkage(const Binding* binding);
bool node_contains_call_expression(const Node& node);
void append_assignment_dependency_members(TypePtr record, vector<Binding*>& members);
bool record_has_default_constructor_for_array(TypePtr type);
bool record_has_base_subobject(TypePtr source, TypePtr target);
uint64_t base_subobject_offset(TypePtr source, TypePtr target);
Binding* find_record_copy_move_assignment(TypePtr type, bool move);
Binding* canonical_constructor_binding(Binding* binding);
const Binding* canonical_constructor_binding(const Binding* binding);
Binding* find_constructor(TypePtr type, size_t arg_count);
const Node* record_prvalue_child_for_xvalue(const Node& arg);
bool defaulted_copy_move_constructor_needs_helper(Binding* binding, TypePtr type);
Binding* find_any_copy_move_constructor(TypePtr type, bool move);
Binding* find_copy_move_constructor(TypePtr type, bool move);
bool inline_defaulted_copy_move_storage_constructor(Binding* binding, TypePtr type, const Node& init);
bool same_record_copy_move_constructor(Binding* binding, TypePtr type, const Node& init);
Binding* find_destructor(TypePtr type);
bool type_needs_destructor(TypePtr type);
bool type_has_generated_noop_destructor(TypePtr type);
bool temp_cleanups_are_generated_noop_destructors(const vector<pair<Value, TypePtr> >& temps);
bool default_init_no_op(TypePtr type);
bool default_constructor_needs_subobject_work(TypePtr type);
bool generated_default_constructor_body_has_work(const ProgramLowerer& program, Binding* ctor, TypePtr type);
bool no_op_generated_default_constructor(Binding* ctor, TypePtr type);
void demand_suppressed_default_init_subobjects(ProgramLowerer& program, TypePtr type);
bool has_inline_constructor(TypePtr type);
bool is_brace_elision_aggregate(TypePtr type);
bool is_string_literal_node(const Node& node);
bool zero_init_has_store(TypePtr type);
bool type_has_reference_subobject(TypePtr type);
bool record_has_user_assignment_operator(TypePtr type);
string zero_integer_type(uint64_t size);
bool same_record_initializer(const Node& init, TypePtr type);
bool record_has_base(TypePtr source, TypePtr target);
bool hosted_exception_record(TypePtr record); bool record_uses_hosted_external_stream_vtable(TypePtr record);
bool hosted_external_stream_function_binding(const Binding* binding);
bool is_class_constructor_binding(const Binding* binding);
bool is_class_destructor_binding(const Binding* binding);
TypePtr class_record_for_member(const Binding* binding);
bool lowir_synthesizable_noop_constructor(const Binding* binding);
bool lowir_synthesizable_defaulted_storage_copy_constructor(const Binding* binding);
bool implicit_copy_constructor_synthesizable_record(TypePtr type, bool move);
bool lowir_hosted_tree_copy_move_constructor(const Binding* binding);
bool lowir_synthesizable_hosted_hashtable_count_constructor(const Binding* binding);
bool lowir_synthesizable_hosted_hashtable_range_constructor(const Binding* binding);
bool lowir_synthesizable_hosted_hash_code_base_hash_code(const Binding* binding);
bool lowir_synthesizable_hosted_vector_copy_assignment(const Binding* binding);
bool lowir_synthesizable_hosted_vector_copy_constructor(const Binding* binding);
bool lowir_synthesizable_hosted_vector_range_insert(const Binding* binding);
bool lowir_synthesizable_hosted_vector_realloc_insert(const Binding* binding);
bool lowir_synthesizable_hosted_vector_initializer_realloc_insert(const Binding* binding);
bool lowir_synthesizable_hosted_vector_relocate(const Binding* binding);
bool lowir_synthesizable_hosted_initializer_list_allocator_construct(const Binding* binding);
bool lowir_synthesizable_hosted_unique_ptr_allocator_copy_construct(const Binding* binding);
bool lowir_synthesizable_hosted_unique_ptr_copy_helper(const Binding* binding);
bool lowir_synthesizable_hosted_inline_body(const Binding* binding);
Node lowir_make_defaulted_storage_copy_constructor_node(const Binding* binding);
Node lowir_make_hosted_hashtable_count_constructor_node(const Binding* binding);
Node lowir_make_hosted_vector_range_insert_node(const Binding* binding);
Node lowir_make_hosted_inline_body_node(const Binding* binding);
bool lowir_extern_template_class_external_binding(const Binding* binding);
bool suppress_noop_generated_constructor_call(const Node& node); void collect_hosted_streambuf_virtual_body_demands(const vector<Node>& extra, set<const Binding*>& out);
bool hosted_library_binding(const Binding* binding);
bool hosted_library_body_candidate(const Binding* binding);
bool hosted_unordered_map_body_root(const Binding* binding);
bool hosted_std_function_swap_binding(const Binding* binding);
const Binding* hosted_map_base_lvalue_operator_index_alias(const Binding* binding);
Binding* anonymous_storage_member_target(Binding* binding);
bool record_is_template_specialization(TypePtr record);
bool binding_has_template_specialization_context(const Binding* binding);
bool binding_has_function_template_specialization_symbol(const Binding* binding);
bool hosted_basic_string_external_member(const Binding* binding);
bool template_static_member_definition_matches(const Binding* use, const Binding* definition);
string record_lowir_name(TypePtr record);
string rtti_record_symbol_part(TypePtr record);
bool template_record_uses_abi_global_symbol(TypePtr record);
string template_record_global_symbol_part(TypePtr record);
bool type_contains_template_symbol_pattern(TypePtr type);
string vtable_symbol_for_record(TypePtr record);
string vtable_view_symbol_for_record(TypePtr record, TypePtr view_base, uint64_t offset);
uint64_t vtable_address_point_offset(TypePtr record);
string vtt_symbol_for_record(TypePtr record);
string construction_vtable_symbol_for_record(TypePtr record, TypePtr constructed, uint64_t offset, size_t slice);
bool record_uses_virtual_base_vtt(TypePtr record);
vector<pair<TypePtr, uint64_t> > vtt_ordered_vtable_views(TypePtr record);
size_t construction_vtt_group_size(TypePtr record);
size_t construction_vtt_slot_for_direct_base(TypePtr record, TypePtr direct_base);
size_t construction_vtt_slot_for_view(TypePtr record, TypePtr view_base, uint64_t offset);
string rtti_symbol_for_record(TypePtr record);
vector<pair<TypePtr, uint64_t> > polymorphic_vtable_views(TypePtr record);
TypePtr hidden_virtual_base_context_record(TypePtr type);
vector<TypePtr> hidden_virtual_bases_for_record(TypePtr record);
vector<TypePtr> hidden_virtual_bases_for_parameter(TypePtr type);
struct ProgramLowerer;
const Binding* inline_alias_lookup_binding(ProgramLowerer& program,
                                           const string& name,
                                           const string& object);
const vector<const Binding*>* inline_alias_member_candidates(
	const ProgramLowerer& program,
	const string& name);
void rank_inline_definition(ProgramLowerer& program, const Binding* binding);
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
	map<string, string> function_symbols_by_object;
	set<string> reserved_class_member_overload_symbol_bases;
		set<string> defined_functions; set<string> declared_functions;
		set<string> defined_globals; set<string> declared_globals;
		set<const Binding*> function_definition_bindings; vector<const Binding*> global_definition_bindings;
	map<const Binding*, Node> global_definition_nodes;
	map<string, string> string_literals;
	map<string, string> string_literal_types;
		vector<pair<string, vector<uint32_t> > > string_defs;
	map<const Binding*, const Node*> inline_definitions;
	map<const Binding*, Node> synthetic_inline_definitions;
	mutable map<const Binding*, bool> recorded_inline_body_shape_cache;
	mutable size_t inline_definition_lookup_cache_size;
	mutable map<string, const Binding*> inline_definition_lookup_by_name;
	mutable map<string, const Binding*> inline_definition_lookup_by_object;
	mutable size_t inline_definition_member_lookup_cache_size;
	mutable map<string, vector<const Binding*> > inline_definition_members_by_name;
	map<const Binding*, Node> deferred_global_definitions;
	set<const Binding*> pending_deferred_global_definition_demands; map<const Binding*, size_t> inline_definition_ranks;
	map<pair<const Binding*, size_t>, vector<TypePtr> > hidden_parameter_virtual_bases;
	map<const Binding*, string> function_declarations_by_binding;
	set<const Binding*> demanded_inline_complete_entries;
	set<const Binding*> demanded_constructor_base_entries;
	set<const Binding*> demanded_destructor_base_entries;
	set<const Binding*> referenced_constructor_base_entries;
	set<const Binding*> constructor_base_entry_only_references;
	set<const void*> static_downcast_source_records;
	set<const void*> emitted_vtables;
	set<const void*> emitted_rtti;
	set<string> declared_pure_virtual_signatures;
	set<const Binding*> emitted_deleting_destructors;
	map<const void*, Binding*> implicit_copy_assignments;
	map<const void*, Binding*> implicit_move_assignments;
	map<const void*, Binding*> implicit_copy_constructors;
	map<const void*, Binding*> implicit_move_constructors;
	vector<FunctionOut> pending_synthetic_constructor_functions;
	vector<const Binding*> pending_inline_definitions;
	vector<InitAction> init_actions;
	vector<Node> global_init_variables;
	vector<Node> thread_local_init_variables;
	vector<Node> global_fini_variables;
	vector<unique_ptr<Binding> > synthetic_bindings;
	bool emitting_inline_definitions; const Binding* active_inline_definition;
	size_t active_inline_dependency_insert_count;
	bool native_lowering; bool host_object_lowering;
	bool needs_empty_init_function; bool needs_eh_declarations;
		int generated_assignment_emit_depth; typedef vector<const Binding*>::iterator PendingInlineIterator;
		ProgramLowerer(bool native = false, bool host_object = false);
	string symbol_for(const Binding* binding);
	string constructor_symbol_for(const Binding* binding, bool base_entry);
	string destructor_symbol_for(const Binding* binding, bool base_entry);
	string string_symbol(const string& token_text);
	void demand_vtable(TypePtr record, bool include_bases = true);
	void emit_rtti(TypePtr record);
	void emit_typeinfo(TypePtr type);
	string typeid_rtti_symbol(TypePtr type);
	string catch_rtti_symbol(TypePtr type);
	void emit_deleting_destructor_entry(const Binding* dtor);
	void register_inline_definition(const Node& node);
	vector<TypePtr> hidden_virtual_bases_for_function_parameter(const Binding* binding, size_t parameter_index, TypePtr type);
	void register_function_declaration(const Node& node);
	void mark_static_downcast_source_record(TypePtr record);
	bool is_static_downcast_source_record(TypePtr record) const;
	void emit_generated_empty_constructor(const Binding* binding, const string& name);
	void emit_referenced_allocator_noop_constructors();
	void emit_referenced_noop_constructor_base_entries();
	void demand_function_declaration(const Binding* binding);
	void demand_lifecycle_base_entry_declaration(const Binding* binding);
	void demand_global_declaration(const Binding* binding);
	bool demand_deferred_global_definition(const Binding* binding);
	bool deferred_global_definition_demanded(const Binding* binding) const;
	bool template_static_member_constant_load_required(const Binding* binding) const;
	void demand_template_static_member_definitions_for_function(const Binding* binding);
	string ensure_local_static_guard(const Binding* binding);
	void ensure_thread_local_wrapper(const string& global_name);
	void ensure_atexit_declaration();
	void ensure_eh_declarations();
	Binding* demand_implicit_copy_constructor(TypePtr type, bool move);
	Binding* demand_implicit_copy_assignment(TypePtr type, bool move);
	void queue_synthetic_constructor_function(Binding* binding, TypePtr record, bool move, const string& name);
	void queue_synthetic_assignment_function(Binding* binding, TypePtr record, bool move, const string& name);
	void emit_pending_generated_aggregate_constructors();
		void demand_move_assignment_copy_dependency(const Binding* binding);
		void insert_pending_inline_definition(const Binding* binding);
		void place_lvalue_assignment_before_rvalue_assignment(const Binding* binding, PendingInlineIterator& pos);
		void place_user_assignment_before_owner_members(const Binding* binding, PendingInlineIterator& pos);
		void place_record_return_before_matching_constructor(const Binding* binding, PendingInlineIterator& pos);
		void place_record_return_before_owner_scalar_member(const Binding* binding, PendingInlineIterator& pos);
		void place_record_return_before_pending_operator(const Binding* binding, PendingInlineIterator& pos);
		void place_constructor_after_pending_record_operator(const Binding* binding, PendingInlineIterator& pos);
		void place_operator_before_pending_constructor(
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
			void append_lowered_inline_definition_outputs(
				const Binding* binding,
				const string& name,
				bool class_ctor,
				bool class_dtor,
				bool need_base,
				bool need_complete,
				const FunctionOut& lowered,
				const FunctionOut& destructor_base_lowered);
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
}  // namespace internal
}  // namespace pa14
