#ifndef LOWIR2NATIVE_MIR_DUMPER_H
#define LOWIR2NATIVE_MIR_DUMPER_H

#include "lowir2cy86.h"
#include "lowir2native.h"
#include "lowir2native_mir_helpers.h"

#include <algorithm>
#include <cstdlib>
#include <map>
#include <ostream>
#include <set>
#include <sstream>
#include <stdexcept>
#include <string>
#include <vector>

using namespace std;

namespace lowir2native {

class MirDumper {
public:
	MirDumper(const lowir2cy86::Program& program, const string& target,
	          int optimization_level);
	string dump();
private:
	const lowir2cy86::Program& program_;
	string target_;
	int optimization_level_;
	ostringstream out_;
	vector<string> temp_names_;
	vector<string> temp_regs_;
	map<string, string> fixed_temp_regs_;
	vector<string> xmm_names_;
	vector<string> xmm_regs_;
	map<string, int> use_counts_;
	map<string, int> remaining_uses_;
	map<string, int> current_param_index_;
	map<string, const lowir2cy86::Instruction*> definitions_;
	map<string, string> entry_param_regs_;
	set<string> delayed_entry_param_regs_;
	set<string> copy_only_entry_param_regs_;
	set<string> pre_call_abi_params_;
	map<string, string> promoted_slot_params_;
	map<string, string> promoted_loads_;
	map<string, string> promoted_addr_params_;
	map<string, string> slot_param_sources_;
	map<string, string> entry_branch_param_loads_;
	set<string> entry_branch_param_indexes_;
	set<string> entry_branch_param_value_loads_;
	map<string, string> mixed_convert_regs_;
	map<string, string> call_arg_addr_regs_;
	map<string, string> call_arg_index_regs_;
	vector<string> call_arg_index_base_params_;
	map<string, string> direct_branch_addr_regs_;
	set<string> direct_branch_cmp_;
	set<string> direct_branch_loads_;
	set<string> materialized_branch_loads_;
	set<string> direct_branch_not_;
	set<string> direct_branch_value_operands_;
		set<string> post_call_direct_branch_loads_;
		set<string> direct_return_values_;
		set<string> branch_call_results_;
		set<string> call_arg_results_;
		set<string> convert_call_results_;
		map<string, string> copy_alias_call_args_;
		set<string> branch_cmp_call_results_;
	set<string> rematerialized_binary_immediates_;
	set<string> optimized_addr_load_temps_;
	map<string, const lowir2cy86::Instruction*> optimized_literal_stores_by_addr_;
	set<string> store_source_loads_;
	set<string> store_source_addrs_;
	set<string> global_store_addrs_;
	set<string> reference_store_source_params_;
	set<string> reference_store_source_temps_;
	set<string> reference_store_cmp_sources_;
	set<string> reference_store_dest_params_;
	set<string> indirect_callee_loads_;
	set<string> indirect_callee_base_loads_;
	set<string> full_gpr_indirect_callee_loads_;
	set<string> late_indirect_arg_temps_;
	set<string> pre_call_param_copies_;
	set<string> param_store_dests_;
	set<string> param_base_loads_;
	map<string, string> param_base_load_params_;
	set<string> tls_store_sources_;
	set<string> tls_pressure_frame_temps_;
	set<string> tls_accumulator_temps_;
	set<string> sret_frame_temps_;
	set<string> stack_call_arg_temps_;
	set<string> stack_call_index_args_;
	set<string> stack_call_result_arg_temps_;
	set<string> stack_call_result_temps_;
	set<string> inline_call_arg_addrs_;
	set<string> inline_copy_addrs_;
	set<string> direct_object_copy_addrs_;
	set<string> direct_param_copy_loads_;
	set<string> inline_zero_addrs_;
	set<string> inline_atomic_expected_addrs_;
	set<string> frame_temps_;
	set<string> omitted_slots_;
	set<string> used_preserves_;
	set<string> live_across_calls_;
	set<string> preemitted_store_literal_addrs_;
	string preferred_load_ptr_;
	string preferred_load_reg_;
	string preferred_literal_reg_;
	size_t live_reg_alloc_;
	size_t forced_preserve_count_;
	size_t current_block_index_;
	bool call_arg_result_frame_preserve_;
	bool branch_cmp_call_result_frame_preserve_;
	bool preferred_load_sets_literal_;
	bool prefer_r8_stack_load_;
	bool fixed_load_dest_;
	bool fixed_const_dest_;
	bool prefer_r8_literal_;
	bool folded_branch_call_preserve_;
	bool large_slot_frame_;
	bool past_call_in_block_;
	bool past_stack_call_in_block_;
	bool force_entry_param_reg_;
	string current_fallthrough_block_;
	map<string, size_t> stack_call_index_arg_spills_;
	map<string, size_t> stack_call_result_arg_spills_;
	set<size_t> prehomed_stack_call_reg_args_;
	void dump_functions();
	void dump_function(const lowir2cy86::Function& fn);
	vector<size_t> optimized_block_order(const lowir2cy86::Function& fn) const;
	string fallthrough_for_order(const lowir2cy86::Function& fn,
	                             const vector<size_t>& order,
	                             size_t order_index) const;
	string debug_suffix(const lowir2cy86::Instruction& ins) const;
	string debug_suffix(const string& debug) const;
	void reset_function_state();
	void analyze_function(const lowir2cy86::Function& fn);
	void reset_analysis_state(const lowir2cy86::Function& fn);
	void collect_function_definitions(const lowir2cy86::Function& fn);
	void analyze_function_structure(const lowir2cy86::Function& fn);
	void analyze_instruction_features(const lowir2cy86::Function& fn);
	void analyze_instruction_feature(const lowir2cy86::Function& fn,
	                                 size_t block_index,
	                                 size_t instruction_index);
	void analyze_call_instruction_feature(const lowir2cy86::Function& fn,
	                                      const lowir2cy86::Instruction& ins);
	void analyze_binary_instruction_feature(
	    const lowir2cy86::Instruction& ins);
	void analyze_optimized_addr_use(const lowir2cy86::Instruction& ins);
	void analyze_store_instruction_feature(const lowir2cy86::Instruction& ins);
	void analyze_branch_instruction_feature(const lowir2cy86::Function& fn,
	                                        size_t block_index,
	                                        size_t instruction_index);
	void count_uses(const lowir2cy86::Instruction& ins);
	void count_use(const lowir2cy86::Value& value);
	void analyze_slot_param_sources(const lowir2cy86::Function& fn);
	void analyze_entry_branch_param_loads(const lowir2cy86::Function& fn);
	string temp_origin_param(const lowir2cy86::Function& fn,
	                         const string& name) const;
	string temp_origin_param(const lowir2cy86::Function& fn,
	                         const string& name,
	                         set<string>& seen) const;
	bool temp_origin_is_reference_param(const lowir2cy86::Function& fn,
	                                    const string& name) const;
	void materialize_frame_temp(const string& name);
	void collect_reference_address_frame_chain(
	    const lowir2cy86::Function& fn, const string& name);
	void collect_stack_call_load_frame_chain(
	    const lowir2cy86::Function& fn, const string& name,
	    bool include_address_chain);
	void note_inline_copy_addr(const lowir2cy86::Value& value);
	void note_direct_object_copy_addr(const lowir2cy86::Function& fn,
	                                  const lowir2cy86::Instruction& ins);
	void note_direct_param_copy_loads(const lowir2cy86::Function& fn,
	                                  const lowir2cy86::Instruction& ins);
	string direct_param_copy_load_param(const lowir2cy86::Function& fn,
	                                    const lowir2cy86::Value& value) const;
	bool param_only_feeds_direct_param_copy(
	    const lowir2cy86::Function& fn, const string& name) const;
	bool value_is_temp(const lowir2cy86::Value& value,
	                   const string& name) const;
	void note_inline_zero_addr(const lowir2cy86::Function& fn,
	                           const lowir2cy86::Value& value);
	bool addr_temp_only_zero_and_index(const lowir2cy86::Function& fn,
	                                   const string& name) const;
	bool temp_value_named(const lowir2cy86::Value& value,
	                      const string& name) const;
	void note_direct_branch_load(const lowir2cy86::Instruction& cmp);
	void note_direct_branch_operands(const lowir2cy86::Instruction& cmp);
	void note_post_call_direct_branch_load(const lowir2cy86::Block& block,
	                                       size_t branch_index,
	                                       const lowir2cy86::Instruction& cmp);
	void note_post_call_direct_branch_call_result(
	    const lowir2cy86::Block& block, size_t branch_index,
	    const lowir2cy86::Instruction& cmp);
	void note_direct_branch_call_result_value(const lowir2cy86::Value& value);
	void note_post_call_direct_branch_load_value(const lowir2cy86::Value& value,
	                                             const lowir2cy86::Type& cmp_type);
	void note_direct_branch_operand(const lowir2cy86::Value& value,
	                                const string& addr_reg);
	bool direct_branch_slot_load_temp(const string& name,
	                                  const lowir2cy86::Type& type) const;
	bool temp_is_const_integer_literal(const string& name,
	                                   string& literal) const;
	bool value_is_const_integer_literal(const lowir2cy86::Value& value,
	                                    string& literal) const;
	bool binary_supports_immediate_rhs(
	    const lowir2cy86::Instruction& ins) const;
	void analyze_entry_param_regs(const lowir2cy86::Function& fn);
	void assign_sret_constructor_entry_param_regs(const lowir2cy86::Function& fn);
	void assign_entry_branch_reference_param_regs(
	    const lowir2cy86::Function& fn);
	void assign_reference_store_source_param_regs(const lowir2cy86::Function& fn);
	void assign_pointer_store_param_regs(const lowir2cy86::Function& fn);
	void assign_global_store_param_regs(const lowir2cy86::Function& fn);
	void analyze_call_arg_addr_regs(const lowir2cy86::Function& fn);
	void analyze_call_arg_index_regs(const lowir2cy86::Function& fn);
	bool index_base_is_reference_param(const lowir2cy86::Function& fn,
	                                   const lowir2cy86::Value& base) const;
	void assign_call_arg_index_base_regs(const lowir2cy86::Function& fn);
	void assign_promoted_load_param_copies(const lowir2cy86::Function& fn);
	void assign_copy_alias_param_regs(const lowir2cy86::Function& fn);
	void assign_promoted_call_arg_copy(const lowir2cy86::Function& fn,
	                                   const lowir2cy86::Value& arg);
	bool assign_promoted_branch_copy(const lowir2cy86::Function& fn,
	                                 const lowir2cy86::Value& value);
	void assign_forwarded_call_param_regs(const lowir2cy86::Function& fn);
	void assign_switch_case_param_regs(const lowir2cy86::Function& fn);
	bool entry_reg_in_use(const string& reg) const;
	void assign_param_base_load_regs(const lowir2cy86::Function& fn);
	void assign_indirect_promoted_call_entry_copies(const lowir2cy86::Function& fn);
	void assign_promoted_call_entry_copies(const lowir2cy86::Function& fn);
	bool call_has_indexed_promoted_arg(const lowir2cy86::Instruction& ins) const;
	void note_promoted_call_arg_param(const lowir2cy86::Value& arg,
	                                  set<string>& params) const;
	void assign_branch_edge_param_regs(const lowir2cy86::Function& fn);
	size_t entry_preserve_reg_count() const;
	bool param_needs_branch_edge_copy(const lowir2cy86::Function& fn,
	                                  const string& name) const;
	bool param_copy_delays_entry_use(const lowir2cy86::Function& fn,
	                                 const string& name) const;
	bool param_used_after_entry(const lowir2cy86::Function& fn,
	                            const string& name) const;
	bool param_copy_used_after_entry(const lowir2cy86::Function& fn,
	                                 const string& name) const;
	bool temp_used_after_entry(const lowir2cy86::Function& fn,
	                           const string& name) const;
	bool param_used_only_after_entry(const lowir2cy86::Function& fn,
	                                 const string& name) const;
	bool instruction_uses_temp(const lowir2cy86::Instruction& ins,
	                           const string& name) const;
	bool dense_integer_params(const lowir2cy86::Function& fn) const;
	bool has_integer_or_pointer_binary(const lowir2cy86::Function& fn) const;
	void analyze_dense_integer_param_regs(const lowir2cy86::Function& fn);
	void analyze_full_gpr_indirect_call_temps(const lowir2cy86::Function& fn);
	void analyze_direct_object_call_arg_temps(const lowir2cy86::Function& fn);
	void analyze_pre_call_param_copies(const lowir2cy86::Function& fn);
	void analyze_copy_alias_call_args(const lowir2cy86::Function& fn);
	void analyze_tls_store_sources(const lowir2cy86::Function& fn);
	void analyze_tls_pressure_temps(const lowir2cy86::Function& fn,
	                                int store_pos,
	                                const map<string, int>& def_pos);
	bool temp_used_after_position(const lowir2cy86::Function& fn,
	                              const string& name,
	                              int after_pos) const;
	void analyze_stack_arg_call_homes(const lowir2cy86::Function& fn);
		size_t first_preserved_stack_call_reg_arg(
		    const lowir2cy86::Instruction& ins) const;
	void analyze_reference_store_dest_frame_temps(const lowir2cy86::Function& fn);
	void analyze_param_store_dests(const lowir2cy86::Function& fn);
	void analyze_param_base_loads(const lowir2cy86::Function& fn);
	void analyze_sret_frame_temps(const lowir2cy86::Function& fn);
	string index_chain_root_param(const string& name) const;
	void collect_sret_frame_chain(const string& name);
	string param_for_projected_load_base(const lowir2cy86::Function& fn,
	                                     const string& temp) const;
	bool load_result_used_as_index_base(const lowir2cy86::Function& fn,
	                                    const string& name) const;
	void analyze_promoted_addr_params(const lowir2cy86::Function& fn);
	void analyze_object_result_field_params(const lowir2cy86::Function& fn);
	bool mixed_gpr_xmm_abi_shape(const lowir2cy86::Function& fn) const;
	void analyze_mixed_gpr_xmm_abi(const lowir2cy86::Function& fn);
	string preserve_reg(size_t index) const;
	bool param_pass_is(const lowir2cy86::Function& fn,
	                   size_t index, const string& pass) const;
	bool param_is_index_base(const lowir2cy86::Function& fn,
	                         const string& name) const;
	void analyze_live_across_calls(const lowir2cy86::Function& fn);
	bool branch_cmp_needs_post_call_preserve(
	    const lowir2cy86::Instruction& cmp) const;
	bool branch_cmp_value_needs_post_call_preserve(
	    const lowir2cy86::Value& value) const;
	bool address_chain_root_is_stable(const string& name) const;
	bool address_chain_root_is_stable(const string& name,
	                                  set<string>& seen) const;
	void note_live_use(const lowir2cy86::Value& value, int pos,
	                   map<string, int>& last_use);
	int param_index_for_name(const string& name) const;
	vector<string> frame_preserves(const lowir2cy86::Function& fn);
	bool loads_through_preserved_pointer_param(const lowir2cy86::Function& fn) const;
	vector<string> ordered_preserves() const;
	string temp_reg(const string& name);
	string large_frame_scratch_reg(size_t index) const;
	string live_preserve_reg();
	void note_temp_reg(const string& reg);
	string xmm_reg(const string& name);
	void remember_xmm_reg(const string& name, const string& reg);
	string float_value(const lowir2cy86::Function& fn,
	                   const lowir2cy86::Value& value);
	string value_reg(const lowir2cy86::Function& fn, const lowir2cy86::Value& value);
	bool entry_param_reg_available(const string& name) const;
	bool entry_param_can_use_abi_before_call(const string& name) const;
	int param_index(const lowir2cy86::Function& fn, const string& name) const;
	bool is_param_slot_value(const lowir2cy86::Function& fn,
	                         const lowir2cy86::Value& value) const;
	string param_slot_mem(const lowir2cy86::Function& fn,
	                      const lowir2cy86::Value& value) const;
	string frame_temp_mem(const lowir2cy86::Function& fn,
	                      const string& name) const;
	void dump_param_saves(const lowir2cy86::Function& fn);
	void dump_reference_store_source_param_copies(
	    const lowir2cy86::Function& fn,
	    set<string>& emitted_entry_params);
	bool dump_sret_constructor_entry_param_moves(
	    const lowir2cy86::Function& fn,
	    set<string>& emitted_entry_params);
	void dump_entry_param_move_if_mapped(const lowir2cy86::Function& fn,
	                                     size_t index,
	                                     set<string>& emitted_entry_params);
	void dump_entry_pre_call_param_copies(const lowir2cy86::Function& fn,
	                                      set<string>& emitted_entry_params);
	void dump_multiuse_promoted_param_copies(const lowir2cy86::Function& fn);
	bool materialize_sret_widened_promoted_load(
	    const lowir2cy86::Function& fn,
	    const lowir2cy86::Instruction& ins,
	    bool emit);
	bool materialize_reference_store_source_promoted_load(
	    const lowir2cy86::Function& fn,
	    const lowir2cy86::Instruction& ins,
	    bool emit);
	bool sret_widened_store_source(const lowir2cy86::Function& fn,
	                               const string& name) const;
	void dump_instruction(const lowir2cy86::Function& fn,
	                      const lowir2cy86::Instruction& ins);
	void simulate_instruction(const lowir2cy86::Function& fn,
	                          const lowir2cy86::Instruction& ins);
	bool simulate_f80_instruction(const lowir2cy86::Function& fn,
	                              const lowir2cy86::Instruction& ins);
	void consume_instruction_uses(const lowir2cy86::Instruction& ins);
	void consume_value(const lowir2cy86::Value& value);
	void release_dead_temps();
	bool temp_is_live(const string& name) const;
	bool reg_is_live(const string& reg) const;
	bool is_last_use(const lowir2cy86::Value& value) const;
	void simulate_atomic(const lowir2cy86::Function& fn,
	                     const lowir2cy86::Instruction& ins);
	void simulate_call(const lowir2cy86::Function& fn,
	                   const lowir2cy86::Instruction& ins);
	void simulate_expected_pointer(const lowir2cy86::Function& fn,
	                               const lowir2cy86::Value& value);
	void simulate_binary(const lowir2cy86::Function& fn,
	                     const lowir2cy86::Instruction& ins);
	void simulate_cmp(const lowir2cy86::Function& fn,
	                  const lowir2cy86::Instruction& ins);
	void dump_const(const lowir2cy86::Function& fn,
	                const lowir2cy86::Instruction& ins);
	string const_dest_reg(const lowir2cy86::Instruction& ins);
	void remember_const_dest(const string& name, const string& reg);
		void dump_addr(const lowir2cy86::Function& fn,
		               const lowir2cy86::Instruction& ins,
		               const string& debug);
		string fixed_addr_dest_reg(const lowir2cy86::Instruction& ins) const;
	void dump_copy(const lowir2cy86::Function& fn,
	               const lowir2cy86::Instruction& ins);
		bool large_frame_pointer_literal_copy(
		    const lowir2cy86::Instruction& ins) const;
	bool copy_can_forward(const lowir2cy86::Function& fn,
	                      const lowir2cy86::Instruction& ins) const;
	bool copy_is_integer_narrow(const lowir2cy86::Function& fn,
	                            const lowir2cy86::Instruction& ins) const;
	bool copy_can_narrow_in_place(const lowir2cy86::Function& fn,
	                              const lowir2cy86::Instruction& ins) const;
	bool addr_prefers_rcx(const lowir2cy86::Instruction& ins) const;
	bool optimized_addr_temp_feeds_load(const string& name) const;
	const lowir2cy86::Instruction* optimized_addr_definition(
	    const lowir2cy86::Value& value) const;
	const lowir2cy86::Instruction* optimized_literal_store_for_addr(
	    const string& name) const;
	bool has_large_slot_frame(const lowir2cy86::Function& fn) const;
	void dump_copyobj(const lowir2cy86::Function& fn,
	                  const lowir2cy86::Instruction& ins);
	bool copyobj_uses_direct_param_loads(
	    const lowir2cy86::Instruction& ins) const;
	bool copyobj_source_is_direct_object(const lowir2cy86::Function& fn,
	                                     const lowir2cy86::Instruction& ins) const;
	void dump_direct_object_copy(const lowir2cy86::Function& fn,
	                             const lowir2cy86::Instruction& ins);
	void simulate_direct_object_copy(const lowir2cy86::Function& fn,
	                                 const lowir2cy86::Instruction& ins);
	string direct_object_chunk_type(const lowir2cy86::Type& type) const;
	bool is_memory_operand(const string& text) const;
	const lowir2cy86::Instruction* inline_addr_definition_for_direct_object(
	    const lowir2cy86::Value& value) const;
	void dump_copy_addr_or_move(const lowir2cy86::Function& fn,
	                            const lowir2cy86::Value& value,
	                            const string& reg);
	void dump_zeroinit(const lowir2cy86::Function& fn,
	                   const lowir2cy86::Instruction& ins);
	void remember_copied_object_load(const lowir2cy86::Function& fn,
	                                 const lowir2cy86::Instruction& ins);
	string direct_addr_target(const lowir2cy86::Function& fn,
	                          const lowir2cy86::Value& value);
	void dump_address_to_reg(const lowir2cy86::Function& fn,
	                         const lowir2cy86::Value& value,
	                         const string& reg);
	void dump_address_value_to_reg(const lowir2cy86::Function& fn,
	                               const lowir2cy86::Value& value,
	                               const string& reg);
	void dump_index(const lowir2cy86::Function& fn,
	                const lowir2cy86::Instruction& ins);
	void dump_sret_frame_index(const lowir2cy86::Function& fn,
	                           const lowir2cy86::Instruction& ins);
	const lowir2cy86::Instruction* inline_zero_addr_definition(
	    const lowir2cy86::Value& value) const;
	string index_dest_reg(const lowir2cy86::Function& fn,
	                      const lowir2cy86::Instruction& ins);
	bool index_is_single_param_store_dest(const lowir2cy86::Function& fn,
	                                      const lowir2cy86::Instruction& ins) const;
	const lowir2cy86::Instruction* unique_store_to_temp(
	    const lowir2cy86::Function& fn, const string& name) const;
	bool store_source_is_load(const lowir2cy86::Value& value) const;
	bool index_feeds_stack_call_arg_load(const lowir2cy86::Function& fn,
	                                     const string& name) const;
	bool load_result_feeds_pre_stack_call_index(
	    const lowir2cy86::Function& fn, const string& name) const;
	bool load_result_feeds_store_source_load(
	    const lowir2cy86::Function& fn, const string& name) const;
	bool load_result_feeds_store_source_load(
	    const lowir2cy86::Function& fn, const string& name,
	    set<string>& seen) const;
	bool load_result_feeds_post_stack_value_load(
	    const lowir2cy86::Function& fn, const string& name) const;
	bool load_result_feeds_post_stack_value_load(
	    const lowir2cy86::Function& fn, const string& name,
	    set<string>& seen) const;
	bool promoted_load_feeds_direct_call_index(
	    const lowir2cy86::Function& fn, const string& name) const;
	bool temp_used_only_as_store_dest(const lowir2cy86::Function& fn,
	                                  const string& name) const;
	long index_literal_offset(const lowir2cy86::Instruction& ins) const;
	string load_source(const lowir2cy86::Function& fn,
	                   const lowir2cy86::Value& value);
	bool is_thread_local_global(const string& name) const;
	string tls_wrapper_for_global(const string& name) const;
	void dump_load(const lowir2cy86::Function& fn,
	               const lowir2cy86::Instruction& ins);
	string pointer_load_base_reg(const lowir2cy86::Function& fn,
	                             const lowir2cy86::Value& value,
	                             bool promoted) const;
	string load_dest_reg(const lowir2cy86::Function& fn,
	                     const lowir2cy86::Instruction& ins);
	string atomic_load_dest_reg(const lowir2cy86::Function& fn,
	                            const lowir2cy86::Instruction& ins);
	string store_source_load_dest_reg(const lowir2cy86::Function& fn,
	                                  const lowir2cy86::Instruction& ins);
	string indirect_result_load_dest_reg(const lowir2cy86::Function& fn,
	                                     const lowir2cy86::Instruction& ins);
	string fixed_analysis_load_dest_reg(const lowir2cy86::Function& fn,
	                                    const lowir2cy86::Instruction& ins);
	string fallback_load_dest_reg(const lowir2cy86::Function& fn,
	                              const lowir2cy86::Instruction& ins);
	bool store_source_feeds_reference_param_dest(
	    const lowir2cy86::Function& fn, const string& name) const;
	string reference_store_dest_base_reg(
	    const lowir2cy86::Function& fn, const string& name) const;
	bool temp_used_as_direct_call_arg(const lowir2cy86::Function& fn,
	                                  const string& name) const;
	bool function_has_float(const lowir2cy86::Function& fn) const;
	void remember_load_dest(const string& name, const string& reg);
	void dump_atomic_store(const lowir2cy86::Function& fn,
	                       const lowir2cy86::Instruction& ins);
	void remember_store_reload(const lowir2cy86::Function& fn,
	                           const lowir2cy86::Value& ptr_value,
	                           const lowir2cy86::Value& src_value);
	void remember_reload(const string& ptr, const string& reg, bool prefer_literal);
	void dump_narrow_extend(const lowir2cy86::Type& type, const string& reg,
	                        const string& debug = "");
	string store_dest(const lowir2cy86::Function& fn,
	                  const lowir2cy86::Value& value);
	void dump_store(const lowir2cy86::Function& fn,
	                const lowir2cy86::Instruction& ins);
	void dump_global_addr_store(const lowir2cy86::Function& fn,
	                            const lowir2cy86::Instruction& ins);
	lowir2cy86::Value promoted_store_dest(const lowir2cy86::Value& value) const;
	void remember_store_literal(const lowir2cy86::Function& fn,
	                            const lowir2cy86::Value& value);
	void dump_scalar(const lowir2cy86::Function& fn,
	                 const lowir2cy86::Instruction& ins);
	void dump_unary(const lowir2cy86::Function& fn,
	                const lowir2cy86::Instruction& ins);
	void dump_convert(const lowir2cy86::Function& fn,
	                  const lowir2cy86::Instruction& ins);
	string conversion_type_text(const lowir2cy86::Type& type) const;
	string convert_dest(const lowir2cy86::Function& fn,
	                    const lowir2cy86::Instruction& ins);
	string convert_source(const lowir2cy86::Function& fn,
	                      const lowir2cy86::Instruction& ins);
	void remember_convert_dest(const lowir2cy86::Instruction& ins,
	                           const string& dst);
	string integer_roundtrip_origin(const lowir2cy86::Function& fn,
	                                const lowir2cy86::Instruction& ins);
	void dump_binary(const lowir2cy86::Function& fn,
	                 const lowir2cy86::Instruction& ins);
	void dump_float_binary(const lowir2cy86::Function& fn,
	                       const lowir2cy86::Instruction& ins);
	string float_binary_dest(const lowir2cy86::Instruction& ins);
	bool literal_needs_reg(const string& text) const;
	bool binary_literal_prefers_reg(const lowir2cy86::Instruction& ins) const;
	string binary_dest_reg(const lowir2cy86::Function& fn,
	                       const lowir2cy86::Instruction& ins);
	void remember_temp_reg(const string& name, const string& reg);
	void remember_fixed_temp_reg(const string& name, const string& reg);
	string shift_rhs(const lowir2cy86::Function& fn,
	                 const lowir2cy86::Value& value);
	void dump_divmod(const lowir2cy86::Function& fn,
	                 const lowir2cy86::Instruction& ins,
	                 const string& dst,
	                 bool signed_div);
	void dump_cmp_value(const lowir2cy86::Function& fn,
	                    const lowir2cy86::Instruction& ins);
	bool cmp_result_stays_in_rax(const string& name) const;
	void dump_rax_condition_result(const string& name);
	string cmp_value_dest_reg(const lowir2cy86::Function& fn,
	                          const lowir2cy86::Instruction& ins);
	string compare_rhs(const lowir2cy86::Function& fn,
	                   const lowir2cy86::Value& value);
	void dump_branch(const lowir2cy86::Function& fn,
	                 const lowir2cy86::Instruction& ins);
	string inverse_branch_suffix(const string& suffix) const;
	void dump_conditional_branch(const string& suffix,
	                             const string& true_target,
	                             const string& false_target,
	                             const string& debug);
	bool branch_uses_fresh_call_result(const lowir2cy86::Value& value) const;
	void dump_float_branch(const lowir2cy86::Function& fn,
	                       const lowir2cy86::Instruction& cmp,
	                       const string& target,
	                       const string& target_false);
	string direct_cmp_lhs(const lowir2cy86::Function& fn,
	                      const lowir2cy86::Instruction& cmp);
	bool direct_cmp_lhs_is_memory(const lowir2cy86::Instruction& cmp) const;
	string direct_cmp_rhs(const lowir2cy86::Function& fn,
	                      const lowir2cy86::Instruction& cmp);
	void dump_call(const lowir2cy86::Function& fn,
	               const lowir2cy86::Instruction& ins);
	bool indirect_reference_first_arg_needs_preserve(
	    const lowir2cy86::Function& fn,
	    const lowir2cy86::Instruction& ins) const;
	bool full_gpr_first_arg_needs_home(
	    const lowir2cy86::Instruction& ins) const;
	bool full_gpr_indirect_call_placeholder(
	    const lowir2cy86::Instruction& ins) const;
	void dump_stack_call_pre_homes(const lowir2cy86::Function& fn,
	                               const lowir2cy86::Instruction& ins);
	bool call_has_reference_stack_index_arg(
	    const lowir2cy86::Instruction& ins) const;
	string call_spill_mem(const lowir2cy86::Function& fn, size_t index) const;
	size_t frame_temps_end_offset(const lowir2cy86::Function& fn) const;
	string call_result_reg(const lowir2cy86::Function& fn,
	                       const lowir2cy86::Instruction& ins) const;
	bool call_has_xmm_arg(const lowir2cy86::Function& fn,
	                      const lowir2cy86::Instruction& ins) const;
	bool call_has_temp_arg(const lowir2cy86::Instruction& ins) const;
	bool call_arg_needs_temp_home(const lowir2cy86::Function& fn,
	                              const lowir2cy86::Instruction& ins,
	                              size_t index) const;
	bool full_gpr_indirect_call(const lowir2cy86::Function& fn,
	                            const lowir2cy86::Instruction& ins) const;
	bool call_uses_full_gpr_args(const lowir2cy86::Function& fn,
	                             const lowir2cy86::Instruction& ins) const;
	bool function_has_call_or_multiple_blocks(const lowir2cy86::Function& fn) const;
	bool has_indirect_result_param(const lowir2cy86::Function& fn) const;
	bool sret_constructor_like(const lowir2cy86::Function& fn) const;
	void dump_full_gpr_first_arg_home(const lowir2cy86::Function& fn,
	                                  const lowir2cy86::Instruction& ins);
	void dump_call_arg_temp_home(const lowir2cy86::Function& fn,
	                             const lowir2cy86::Instruction& ins,
	                             size_t index);
	bool call_result_stays_in_rax(const string& name) const;
	void dump_indirect_callee(const lowir2cy86::Function& fn,
	                          const lowir2cy86::Value& value);
	const lowir2cy86::Instruction* inline_addr_definition_for_call(
	    const lowir2cy86::Value& value) const;
	void dump_call_arg(const lowir2cy86::Function& fn,
	                   const lowir2cy86::Instruction& ins, size_t index, const string& reg);
	bool single_use_temp(const string& name) const;
	bool is_dead_dest(const string& name) const;
	void dump_late_indirect_arg_homes(const lowir2cy86::Function& fn,
	                                  const lowir2cy86::Instruction& ins);
	string late_indirect_arg_mem(const lowir2cy86::Function& fn,
	                             const lowir2cy86::Instruction& ins,
	                             size_t index) const;
	size_t late_indirect_arg_spill_index(const lowir2cy86::Instruction& ins,
	                                     size_t index) const;
	void dump_stack_call_arg(const lowir2cy86::Function& fn,
	                         const lowir2cy86::Instruction& ins, size_t index);
	void dump_stack_index_call_arg(const lowir2cy86::Function& fn,
	                               const lowir2cy86::Value& arg,
	                               const lowir2cy86::Type& type,
	                               const string& dst);
	void dump_atomic(const lowir2cy86::Function& fn,
	                 const lowir2cy86::Instruction& ins);
	void dump_atomic_compare_exchange(const lowir2cy86::Function& fn,
	                                  const lowir2cy86::Instruction& ins);
	void dump_expected_pointer(const lowir2cy86::Function& fn,
	                           const lowir2cy86::Value& value);
	const lowir2cy86::Instruction* inline_addr_definition(
	    const lowir2cy86::Value& value) const;
	bool can_reuse_written_value(const lowir2cy86::Value& value) const;
	void dump_switch(const lowir2cy86::Function& fn,
	                 const lowir2cy86::Instruction& ins);
	void dump_return(const lowir2cy86::Function& fn,
	                 const lowir2cy86::Instruction& ins);
};

}  // namespace lowir2native

#endif
