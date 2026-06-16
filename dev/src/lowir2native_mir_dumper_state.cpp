#include "lowir2native_mir_dumper.h"

namespace lowir2native {

MirDumper::MirDumper(const lowir2cy86::Program& program, const string& target,
                     int optimization_level)
	: program_(program), target_(target),
	  optimization_level_(optimization_level) { }

string MirDumper::dump() {
	out_ << "machine_ir x86_64 " << target_ << "\n\n";
	dump_mir_startup(out_, program_);
	dump_mir_globals(out_, program_);
	dump_functions();
	return out_.str();
}

void MirDumper::dump_functions() {
	for (size_t i = 0; i < program_.functions.size(); ++i) {
		const lowir2cy86::Function& fn = program_.functions[i];
		if (fn.declaration)
			continue;
		dump_function(fn);
		if (i + 1 != program_.functions.size())
			out_ << "\n";
	} }

void MirDumper::dump_function(const lowir2cy86::Function& fn) {
	analyze_function(fn);
	const vector<string> preserves = frame_preserves(fn);
	const vector<size_t> order = optimized_block_order(fn);
	reset_function_state();
	out_ << "function " << fn.name << "\n";
	dump_mir_abi(out_, fn);
	dump_mir_frame(out_, program_, fn, preserves, omitted_slots_);
	dump_mir_frame_temps(out_, fn, frame_temps_, omitted_slots_);
	out_ << "\n";
	for (size_t i = 0; i < order.size(); ++i) {
		current_block_index_ = order[i];
		current_fallthrough_block_ = fallthrough_for_order(fn, order, i);
		past_call_in_block_ = false;
		past_stack_call_in_block_ = false;
		release_dead_temps();
		const lowir2cy86::Block& block = fn.blocks[order[i]];
		out_ << "  block " << block.name << "\n";
		if (order[i] == 0)
			dump_param_saves(fn);
		for (size_t j = 0; j < block.instructions.size(); ++j)
			dump_instruction(fn, block.instructions[j]);
		if (i + 1 != order.size())
			out_ << "\n";
	} }

vector<size_t> MirDumper::optimized_block_order(
    const lowir2cy86::Function& fn) const {
	vector<size_t> order;
	vector<bool> seen(fn.blocks.size(), false);
	if (optimization_level_ < 2) {
		for (size_t i = 0; i < fn.blocks.size(); ++i)
			order.push_back(i);
		return order;
	}
	for (size_t start = 0; start < fn.blocks.size(); ++start) {
		size_t current = start;
		while (current < fn.blocks.size() && !seen[current]) {
			seen[current] = true;
			order.push_back(current);
			const lowir2cy86::Block& block = fn.blocks[current];
			if (block.instructions.empty())
				break;
			const lowir2cy86::Instruction& last = block.instructions.back();
			if (last.kind != lowir2cy86::InstrKind::Jump)
				break;
			const size_t next = block_index_by_name(fn, last.target);
			if (next >= fn.blocks.size() || seen[next])
				break;
			current = next;
		}
	}
	return order;
}

size_t MirDumper::block_index_by_name(const lowir2cy86::Function& fn,
                                      const string& name) const {
	for (size_t i = 0; i < fn.blocks.size(); ++i)
		if (fn.blocks[i].name == name)
			return i;
	return fn.blocks.size();
}

string MirDumper::fallthrough_for_order(const lowir2cy86::Function& fn,
                                        const vector<size_t>& order,
                                        size_t order_index) const {
	if (order_index + 1 >= order.size())
		return "";
	return fn.blocks[order[order_index + 1]].name;
}

string MirDumper::debug_suffix(const lowir2cy86::Instruction& ins) const {
	return debug_suffix(ins.debug);
}

string MirDumper::debug_suffix(const string& debug) const {
	return debug.empty() ? "" : " " + debug;
}

void MirDumper::reset_function_state() {
	temp_names_.clear();
	temp_regs_.clear();
	fixed_temp_regs_.clear();
	xmm_names_.clear();
	xmm_regs_.clear();
	remaining_uses_ = use_counts_;
	used_preserves_.clear();
	preemitted_store_literal_addrs_.clear();
	live_reg_alloc_ = 0;
	current_block_index_ = 0;
	stack_call_index_arg_spills_.clear();
	stack_call_result_arg_spills_.clear();
	prehomed_stack_call_reg_args_.clear();
	preferred_load_ptr_.clear();
	preferred_load_reg_.clear();
	preferred_literal_reg_.clear();
	preferred_load_sets_literal_ = false;
	prefer_r8_stack_load_ = false;
	fixed_load_dest_ = false;
	fixed_const_dest_ = false;
	prefer_r8_literal_ = false;
	past_call_in_block_ = false;
	past_stack_call_in_block_ = false;
	force_entry_param_reg_ = false;
	current_fallthrough_block_.clear();
}

void MirDumper::analyze_function(const lowir2cy86::Function& fn) {
	reset_analysis_state(fn);
	collect_function_definitions(fn);
	analyze_function_structure(fn);
	analyze_instruction_features(fn);
	analyze_entry_param_regs(fn);
	analyze_mixed_gpr_xmm_abi(fn);
}

void MirDumper::reset_analysis_state(const lowir2cy86::Function& fn) {
	use_counts_.clear();
	definitions_.clear();
	current_param_index_.clear();
	entry_param_regs_.clear();
	delayed_entry_param_regs_.clear();
	copy_only_entry_param_regs_.clear();
	pre_call_abi_params_.clear();
	promoted_slot_params_.clear();
	promoted_loads_.clear();
	promoted_addr_params_.clear();
	mixed_convert_regs_.clear();
	call_arg_addr_regs_.clear();
	call_arg_index_regs_.clear();
	call_arg_index_base_params_.clear();
	direct_branch_addr_regs_.clear();
	direct_branch_cmp_.clear();
	direct_branch_loads_.clear();
	materialized_branch_loads_.clear();
	direct_branch_not_.clear();
	direct_branch_value_operands_.clear();
	post_call_direct_branch_loads_.clear();
	direct_return_values_.clear();
	branch_call_results_.clear();
	call_arg_results_.clear();
	convert_call_results_.clear();
	copy_alias_call_args_.clear();
	branch_cmp_call_results_.clear();
	rematerialized_binary_immediates_.clear();
	store_source_loads_.clear();
	store_source_addrs_.clear();
	global_store_addrs_.clear();
	reference_store_source_params_.clear();
	reference_store_source_temps_.clear();
	reference_store_cmp_sources_.clear();
	reference_store_dest_params_.clear();
	indirect_callee_loads_.clear();
	indirect_callee_base_loads_.clear();
	full_gpr_indirect_callee_loads_.clear();
	late_indirect_arg_temps_.clear();
	pre_call_param_copies_.clear();
	param_store_dests_.clear();
	param_base_loads_.clear();
	param_base_load_params_.clear();
	tls_store_sources_.clear();
	tls_pressure_frame_temps_.clear();
	tls_accumulator_temps_.clear();
	sret_frame_temps_.clear();
	stack_call_arg_temps_.clear();
	stack_call_index_args_.clear();
	stack_call_result_arg_temps_.clear();
	stack_call_result_temps_.clear();
	inline_call_arg_addrs_.clear();
	inline_copy_addrs_.clear();
	direct_object_copy_addrs_.clear();
	direct_param_copy_loads_.clear();
	inline_zero_addrs_.clear();
	inline_atomic_expected_addrs_.clear();
	frame_temps_.clear();
	omitted_slots_.clear();
	live_across_calls_.clear();
	slot_param_sources_.clear();
	entry_branch_param_loads_.clear();
	entry_branch_param_indexes_.clear();
	entry_branch_param_value_loads_.clear();
	forced_preserve_count_ = 0;
	current_block_index_ = 0;
	call_arg_result_frame_preserve_ = false;
	branch_cmp_call_result_frame_preserve_ = false;
	folded_branch_call_preserve_ = false;
	large_slot_frame_ = has_large_slot_frame(fn);
	past_call_in_block_ = false;
	past_stack_call_in_block_ = false;
	force_entry_param_reg_ = false;
	for (size_t i = 0; i < fn.params.size(); ++i)
		current_param_index_[fn.params[i].name] = static_cast<int>(i);
}

void MirDumper::collect_function_definitions(const lowir2cy86::Function& fn) {
	for (size_t i = 0; i < fn.blocks.size(); ++i) {
		for (size_t j = 0; j < fn.blocks[i].instructions.size(); ++j) {
			const lowir2cy86::Instruction& ins = fn.blocks[i].instructions[j];
			if (ins.has_dest)
				definitions_[ins.dest] = &ins;
			count_uses(ins);
		}
	}
}

void MirDumper::analyze_function_structure(const lowir2cy86::Function& fn) {
	analyze_slot_param_sources(fn);
	analyze_entry_branch_param_loads(fn);
	analyze_mir_promoted_slots(fn, promoted_slot_params_, promoted_loads_, omitted_slots_);
	if (large_slot_frame_) {
		promoted_slot_params_.clear();
		promoted_loads_.clear();
		omitted_slots_.clear();
	}
	analyze_promoted_addr_params(fn);
	analyze_mir_frame_temps(program_, fn, frame_temps_);
	analyze_live_across_calls(fn);
	analyze_sret_frame_temps(fn);
	analyze_tls_store_sources(fn);
	analyze_stack_arg_call_homes(fn);
	analyze_reference_store_dest_frame_temps(fn);
	analyze_param_store_dests(fn);
	analyze_param_base_loads(fn);
	analyze_full_gpr_indirect_call_temps(fn);
	analyze_direct_object_call_arg_temps(fn);
	analyze_pre_call_param_copies(fn);
	analyze_copy_alias_call_args(fn);
	analyze_call_arg_addr_regs(fn);
	analyze_call_arg_index_regs(fn);
}

void MirDumper::analyze_instruction_features(const lowir2cy86::Function& fn) {
	for (size_t i = 0; i < fn.blocks.size(); ++i)
		for (size_t j = 0; j < fn.blocks[i].instructions.size(); ++j)
			analyze_instruction_feature(fn, i, j);
}

void MirDumper::analyze_instruction_feature(const lowir2cy86::Function& fn,
                                            size_t block_index,
                                            size_t instruction_index) {
	const lowir2cy86::Instruction& ins =
	    fn.blocks[block_index].instructions[instruction_index];
	if (ins.kind == lowir2cy86::InstrKind::AtomicCompareExchange &&
	    ins.b.kind == lowir2cy86::ValueKind::Temp &&
	    use_counts_[ins.b.text] == 1) {
		map<string, const lowir2cy86::Instruction*>::const_iterator ait =
		    definitions_.find(ins.b.text);
		if (ait != definitions_.end() &&
		    ait->second->kind == lowir2cy86::InstrKind::Addr)
			inline_atomic_expected_addrs_.insert(ins.b.text);
	}
	if (ins.kind == lowir2cy86::InstrKind::Return &&
	    ins.a.kind == lowir2cy86::ValueKind::Temp &&
	    use_counts_[ins.a.text] == 1)
		direct_return_values_.insert(ins.a.text);
	if (ins.kind == lowir2cy86::InstrKind::Call)
		analyze_call_instruction_feature(fn, ins);
	if (ins.kind == lowir2cy86::InstrKind::Binary)
		analyze_binary_instruction_feature(ins);
	if (ins.kind == lowir2cy86::InstrKind::Convert && ins.op == "trunc" &&
	    lowir2cy86::is_signed_integer_type(ins.type) && ins.type.bits == 32 &&
	    lowir2cy86::is_integer_type(ins.src_type) && ins.src_type.bits == 64 &&
	    ins.a.kind == lowir2cy86::ValueKind::Temp &&
	    use_counts_[ins.a.text] == 1) {
		map<string, const lowir2cy86::Instruction*>::const_iterator cit =
		    definitions_.find(ins.a.text);
		if (cit != definitions_.end() &&
		    cit->second->kind == lowir2cy86::InstrKind::Call)
			convert_call_results_.insert(ins.a.text);
	}
	if (ins.kind == lowir2cy86::InstrKind::CopyObj) {
		note_inline_copy_addr(ins.b);
		note_direct_object_copy_addr(fn, ins);
		note_direct_param_copy_loads(fn, ins);
	}
	if (ins.kind == lowir2cy86::InstrKind::Store)
		analyze_store_instruction_feature(ins);
	if (ins.kind == lowir2cy86::InstrKind::ZeroInit)
		note_inline_zero_addr(fn, ins.a);
	if (ins.kind == lowir2cy86::InstrKind::Branch)
		analyze_branch_instruction_feature(fn, block_index, instruction_index);
}

void MirDumper::analyze_call_instruction_feature(
    const lowir2cy86::Function& fn, const lowir2cy86::Instruction& ins) {
	for (size_t a = 0; a < ins.args.size(); ++a) {
		if (ins.args[a].kind == lowir2cy86::ValueKind::Temp &&
		    use_counts_[ins.args[a].text] == 1) {
			map<string, const lowir2cy86::Instruction*>::const_iterator cit =
			    definitions_.find(ins.args[a].text);
			if (cit != definitions_.end()) {
				if (cit->second->kind == lowir2cy86::InstrKind::Call) {
					branch_call_results_.insert(ins.args[a].text);
					call_arg_results_.insert(ins.args[a].text);
				if (call_uses_full_gpr_args(fn, ins))
					call_arg_result_frame_preserve_ = true;
			} else if (cit->second->kind == lowir2cy86::InstrKind::Addr &&
			           cit->second->a.kind == lowir2cy86::ValueKind::Slot)
				inline_call_arg_addrs_.insert(ins.args[a].text);
			}
		}
	}
	if (ins.a.kind == lowir2cy86::ValueKind::Temp) {
		map<string, const lowir2cy86::Instruction*>::const_iterator lit =
		    definitions_.find(ins.a.text);
		if (lit != definitions_.end() &&
		    lit->second->kind == lowir2cy86::InstrKind::Load &&
		    lit->second->a.kind == lowir2cy86::ValueKind::Temp) {
			indirect_callee_loads_.insert(ins.a.text);
			indirect_callee_base_loads_.insert(lit->second->a.text);
		}
	}
}

void MirDumper::analyze_binary_instruction_feature(
    const lowir2cy86::Instruction& ins) {
	if (optimization_level_ < 1 || !binary_supports_immediate_rhs(ins) ||
	    ins.b.kind != lowir2cy86::ValueKind::Temp ||
	    use_counts_[ins.b.text] != 1)
		return;
	string literal;
	if (temp_is_const_integer_literal(ins.b.text, literal))
		rematerialized_binary_immediates_.insert(ins.b.text);
}

void MirDumper::analyze_store_instruction_feature(
    const lowir2cy86::Instruction& ins) {
	if (!(optimization_level_ >= 1 &&
	      ins.b.kind == lowir2cy86::ValueKind::Temp &&
	      optimized_addr_definition(ins.b) != nullptr))
		note_inline_copy_addr(ins.b);
	if (ins.a.kind != lowir2cy86::ValueKind::Temp)
		return;
	map<string, const lowir2cy86::Instruction*>::const_iterator it =
	    definitions_.find(ins.a.text);
	if (it != definitions_.end() &&
	    it->second->kind == lowir2cy86::InstrKind::Addr &&
	    it->second->a.kind == lowir2cy86::ValueKind::Global &&
	    use_counts_[ins.a.text] == 1)
		global_store_addrs_.insert(ins.a.text);
	if (use_counts_[ins.a.text] != 1)
		return;
	if (it != definitions_.end() &&
	    it->second->kind == lowir2cy86::InstrKind::Load)
		store_source_loads_.insert(ins.a.text);
	if (it != definitions_.end() &&
	    it->second->kind == lowir2cy86::InstrKind::Addr &&
	    it->second->a.kind == lowir2cy86::ValueKind::Slot &&
	    ins.b.kind == lowir2cy86::ValueKind::Temp)
		store_source_addrs_.insert(ins.a.text);
}

void MirDumper::analyze_branch_instruction_feature(
    const lowir2cy86::Function& fn, size_t block_index,
    size_t instruction_index) {
	const lowir2cy86::Instruction& ins =
	    fn.blocks[block_index].instructions[instruction_index];
	if (ins.a.kind != lowir2cy86::ValueKind::Temp)
		return;
	if (optimization_level_ >= 1)
		direct_branch_value_operands_.insert(ins.a.text);
	map<string, const lowir2cy86::Instruction*>::const_iterator it =
	    definitions_.find(ins.a.text);
	if (block_index != 0 && it != definitions_.end() &&
	    it->second->kind == lowir2cy86::InstrKind::Call)
		branch_call_results_.insert(ins.a.text);
	if (it != definitions_.end() &&
	    it->second->kind == lowir2cy86::InstrKind::Unary &&
	    it->second->op == "not" && use_counts_[ins.a.text] == 1) {
		direct_branch_not_.insert(ins.a.text);
		if (it->second->a.kind == lowir2cy86::ValueKind::Temp) {
			map<string, const lowir2cy86::Instruction*>::const_iterator uit =
			    definitions_.find(it->second->a.text);
			if (uit != definitions_.end() &&
			    uit->second->kind == lowir2cy86::InstrKind::Call)
				branch_call_results_.insert(it->second->a.text);
		}
	}
	if (it != definitions_.end() &&
	    it->second->kind == lowir2cy86::InstrKind::Cmp &&
	    use_counts_[ins.a.text] == 1) {
		direct_branch_cmp_.insert(ins.a.text);
		note_direct_branch_operands(*it->second);
		note_direct_branch_load(*it->second);
		note_post_call_direct_branch_load(fn.blocks[block_index], instruction_index,
		                                  *it->second);
	}
}

}  // namespace lowir2native
