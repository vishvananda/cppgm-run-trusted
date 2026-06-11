#include "lowir2native_mir_dumper.h"

namespace lowir2native {

vector<string> MirDumper::frame_preserves(const lowir2cy86::Function& fn) {
	reset_function_state();
	for (size_t i = 0; i < fn.blocks.size(); ++i) {
		current_block_index_ = i;
		past_call_in_block_ = false;
		past_stack_call_in_block_ = false;
		release_dead_temps();
		for (size_t j = 0; j < fn.blocks[i].instructions.size(); ++j)
			simulate_instruction(fn, fn.blocks[i].instructions[j]);
	}
	if (folded_branch_call_preserve_ || !indirect_callee_loads_.empty())
		used_preserves_.insert("r12");
	if (branch_cmp_call_result_frame_preserve_)
		used_preserves_.insert("r12");
	if (call_arg_result_frame_preserve_)
		used_preserves_.insert("rbx");
	if (loads_through_preserved_pointer_param(fn))
		used_preserves_.insert("rbx");
	if (!materialized_branch_loads_.empty())
		used_preserves_.insert("rbx");
	if (!post_call_direct_branch_loads_.empty())
		used_preserves_.insert("rbx");
	for (size_t i = 0; i < forced_preserve_count_; ++i)
		used_preserves_.insert(preserve_reg(i));
	return ordered_preserves(); }

bool MirDumper::loads_through_preserved_pointer_param(const lowir2cy86::Function& fn) const {
	for (size_t b = 0; b < fn.blocks.size(); ++b)
		for (size_t i = 0; i < fn.blocks[b].instructions.size(); ++i) {
			const lowir2cy86::Instruction& ins = fn.blocks[b].instructions[i];
			if (ins.kind != lowir2cy86::InstrKind::Load ||
			    ins.a.kind != lowir2cy86::ValueKind::Temp)
				continue;
			const string projected =
			    param_for_projected_load_base(fn, ins.a.text);
			if (!projected.empty()) {
				const int index = param_index(fn, projected);
				if (index >= 0 && param_pass_is(fn, index, "reference"))
					return true;
			}
			lowir2cy86::Value src = promoted_store_dest(ins.a);
			if (src.kind != lowir2cy86::ValueKind::Temp)
				continue;
			const int index = param_index(fn, src.text);
			if (index < 0 ||
			    !lowir2cy86::is_ptr_type(mir_lookup_type(fn, src)))
				continue;
			if (src.text != ins.a.text || param_pass_is(fn, index, "reference"))
				return true;
		}
	return false;
}

vector<string> MirDumper::ordered_preserves() const {
	static const char* const order[] = {"rbx", "r12", "r13", "r14", "r15"};
	vector<string> regs;
	for (size_t i = 0; i < sizeof(order) / sizeof(order[0]); ++i) {
		if (used_preserves_.find(order[i]) != used_preserves_.end())
			regs.push_back(order[i]);
	} return regs; }

string MirDumper::temp_reg(const string& name) {
	if (temp_regs_.size() < temp_names_.size())
		temp_names_.resize(temp_regs_.size());
	for (size_t i = 0; i < temp_names_.size(); ++i) {
		if (temp_names_[i] == name) {
			note_temp_reg(temp_regs_[i]);
			return temp_regs_[i];
		}
	}
	const string reg =
	    live_across_calls_.find(name) != live_across_calls_.end()
	        ? live_preserve_reg()
	        : large_slot_frame_
	              ? large_frame_scratch_reg(temp_regs_.size())
	              : reg_for_index(temp_regs_.size());
	temp_names_.push_back(name);
	temp_regs_.push_back(reg);
	note_temp_reg(reg); return reg; }

string MirDumper::large_frame_scratch_reg(size_t index) const {
	static const char* const regs[] = {"r8", "r9"};
	return regs[index % (sizeof(regs) / sizeof(regs[0]))];
}

string MirDumper::live_preserve_reg() {
	string reg = preserve_reg(live_reg_alloc_);
	while ((reg == "rbx" && reg_is_live(reg)) ||
	       (reg == "r12" && branch_cmp_call_result_frame_preserve_)) {
		++live_reg_alloc_;
		reg = preserve_reg(live_reg_alloc_);
	}
	++live_reg_alloc_; return reg; }

void MirDumper::note_temp_reg(const string& reg) {
	if (reg == "rbx" || reg == "r12" || reg == "r13" ||
	    reg == "r14" || reg == "r15")
		used_preserves_.insert(reg); }

string MirDumper::xmm_reg(const string& name) {
	for (size_t i = 0; i < xmm_names_.size(); ++i) {
		if (xmm_names_[i] == name)
			return xmm_regs_[i];
	}
	static const char* const regs[] = {"xmm0", "xmm1", "xmm2", "xmm3"};
	for (size_t i = 0; i < xmm_names_.size(); ++i) {
		if (!temp_is_live(xmm_names_[i])) {
			xmm_names_[i] = name;
			return xmm_regs_[i];
		}
	}
	xmm_names_.push_back(name);
	xmm_regs_.push_back(regs[xmm_regs_.size() %
	                         (sizeof(regs) / sizeof(regs[0]))]); return xmm_regs_.back(); }

void MirDumper::remember_xmm_reg(const string& name, const string& reg) {
	for (size_t i = 0; i < xmm_names_.size(); ++i) {
		if (xmm_names_[i] == name) {
			xmm_regs_[i] = reg;
			return;
		}
	}
	xmm_names_.push_back(name);
	xmm_regs_.push_back(reg); }

string MirDumper::float_value(const lowir2cy86::Function& fn,
                   const lowir2cy86::Value& value) {
	if (value.kind == lowir2cy86::ValueKind::Temp) {
		const int index = param_index(fn, value.text);
		if (index >= 0 && mir_param_needs_slot(fn, index))
			return mem_for_offset(mir_param_slot_offset(fn, index));
		return xmm_reg(value.text);
	} return value_reg(fn, value); }

string MirDumper::value_reg(const lowir2cy86::Function& fn, const lowir2cy86::Value& value) {
	if (value.kind == lowir2cy86::ValueKind::Temp) {
		map<string, string>::const_iterator source_fit =
		    fixed_temp_regs_.find(value.text);
		if (source_fit != fixed_temp_regs_.end() &&
		    reference_store_source_temps_.find(value.text) !=
		        reference_store_source_temps_.end())
			return source_fit->second;
		map<string, string>::const_iterator ait = promoted_loads_.find(value.text);
		if (ait != promoted_loads_.end()) {
			lowir2cy86::Value param;
			param.kind = lowir2cy86::ValueKind::Temp;
			param.text = ait->second;
			return value_reg(fn, param);
		}
		map<string, string>::const_iterator eit = entry_param_regs_.find(value.text);
		if (eit != entry_param_regs_.end() &&
		    entry_param_reg_available(value.text)) {
			if (entry_param_can_use_abi_before_call(value.text))
				return mir_abi_param_location(
				    fn, static_cast<size_t>(param_index(fn, value.text)));
			note_temp_reg(eit->second);
			return eit->second;
		}
		for (size_t i = 0; i < fn.params.size(); ++i) {
			if (fn.params[i].name == value.text) {
				if (mir_param_needs_slot(fn, i))
					return mem_for_offset(mir_param_slot_offset(fn, i));
				return mir_abi_param_location(fn, i);
			}
		}
		map<string, string>::const_iterator fit = fixed_temp_regs_.find(value.text);
		if (fit != fixed_temp_regs_.end())
			return fit->second;
		return temp_reg(value.text);
	}
	if (value.kind == lowir2cy86::ValueKind::Literal) return value.text;
	if (value.kind == lowir2cy86::ValueKind::Global ||
	    value.kind == lowir2cy86::ValueKind::Function)
		return value.text;
	if (value.kind == lowir2cy86::ValueKind::Slot) return mem_for_offset(mir_slot_offset(fn, value.text, omitted_slots_)); return value_text(value); }

bool MirDumper::entry_param_reg_available(const string& name) const {
	if (copy_only_entry_param_regs_.find(name) !=
	    copy_only_entry_param_regs_.end())
		return false;
	return delayed_entry_param_regs_.find(name) ==
	           delayed_entry_param_regs_.end() ||
	       current_block_index_ != 0;
}

bool MirDumper::entry_param_can_use_abi_before_call(const string& name) const {
	return current_block_index_ == 0 &&
	       !past_call_in_block_ &&
	       !force_entry_param_reg_ &&
	       pre_call_abi_params_.find(name) != pre_call_abi_params_.end();
}

int MirDumper::param_index(const lowir2cy86::Function& fn, const string& name) const {
	for (size_t i = 0; i < fn.params.size(); ++i)
		if (fn.params[i].name == name)
			return static_cast<int>(i); return -1; }

bool MirDumper::is_param_slot_value(const lowir2cy86::Function& fn,
                         const lowir2cy86::Value& value) const {
	if (value.kind != lowir2cy86::ValueKind::Temp) return false;
	const int index = param_index(fn, value.text); return index >= 0 && mir_param_needs_slot(fn, index); }

string MirDumper::param_slot_mem(const lowir2cy86::Function& fn,
                      const lowir2cy86::Value& value) const {
	const int index = param_index(fn, value.text);
	return index >= 0 ? mem_for_offset(mir_param_slot_offset(fn, index))
	                  : mem_for_offset(fn.param_offsets.find(value.text)->second);
}

string MirDumper::frame_temp_mem(const lowir2cy86::Function& fn,
                      const string& name) const {
	size_t bytes = 0;
	for (size_t i = 0; i < fn.params.size(); ++i)
		if (mir_param_needs_slot(fn, i))
			bytes = max(bytes, mir_param_slot_offset(fn, i));
	for (size_t i = 0; i < fn.slots.size(); ++i)
		bytes = max(bytes, mir_slot_offset(fn, fn.slots[i].name, omitted_slots_));
	for (size_t i = 0; i < fn.temp_order.size(); ++i) {
		const string& temp = fn.temp_order[i];
		if (frame_temps_.find(temp) == frame_temps_.end())
			continue;
		const lowir2cy86::Type& type = fn.temp_types.find(temp)->second;
		const size_t align = lowir2cy86::is_obj_type(type)
		                         ? type.align
		                         : lowir2cy86::storage_size(type);
		bytes = align_to(bytes, align);
		bytes += lowir2cy86::is_obj_type(type)
		             ? lowir2cy86::stack_storage_size(type)
		             : lowir2cy86::storage_size(type);
		if (temp == name)
			return mem_for_offset(bytes);
	}
	return mem_for_offset(fn.temp_offsets.find(name)->second); }

void MirDumper::dump_param_saves(const lowir2cy86::Function& fn) {
	for (size_t i = 0; i < fn.params.size(); ++i) {
		if (!mir_param_needs_slot(fn, i))
			continue;
		const string dst = mem_for_offset(mir_param_slot_offset(fn, i));
		const string src = mir_abi_param_location(fn, i);
		if (mir_is_xmm_type(fn.params[i].type))
			out_ << "    fmov." << fn.params[i].type.text << " "
			     << dst << ", " << src << "\n";
		else if (lowir2cy86::is_f80_type(fn.params[i].type))
			;
		else if (src.find("[rbp+") != 0) {
			const string type = direct_object_chunk_type(fn.params[i].type).empty()
			    ? fn.params[i].type.text
			    : direct_object_chunk_type(fn.params[i].type);
			out_ << "    store." << type
			     << " " << dst << ", " << src << "\n";
		}
		else {
			const string type = direct_object_chunk_type(fn.params[i].type).empty()
			    ? fn.params[i].type.text
			    : direct_object_chunk_type(fn.params[i].type);
			out_ << "    load." << type
			     << " rax, " << src << "\n";
			out_ << "    store." << type
			     << " " << dst << ", rax\n";
		}
	}
	dump_mir_f80_param_saves(out_, fn);
	set<string> emitted_entry_params;
	if (dump_sret_constructor_entry_param_moves(fn, emitted_entry_params)) {
		dump_multiuse_promoted_param_copies(fn);
		return;
	}
	dump_entry_pre_call_param_copies(fn, emitted_entry_params);
	dump_reference_store_source_param_copies(fn, emitted_entry_params);
	if (dense_integer_params(fn)) {
		static const size_t order[] = {2, 3, 4, 5, 1, 0};
		for (size_t p = 0; p < sizeof(order) / sizeof(order[0]); ++p) {
			if (order[p] >= fn.params.size())
				continue;
			map<string, string>::const_iterator it =
			    entry_param_regs_.find(fn.params[order[p]].name);
			if (it == entry_param_regs_.end())
				continue;
			const string src = mir_abi_param_location(fn, order[p]);
			if (src != it->second)
				out_ << "    mov " << it->second << ", " << src << "\n";
			emitted_entry_params.insert(fn.params[order[p]].name);
		}
	}
	for (size_t i = 0; i < fn.params.size(); ++i) {
		if (emitted_entry_params.find(fn.params[i].name) !=
		    emitted_entry_params.end())
			continue;
		map<string, string>::const_iterator it =
		    entry_param_regs_.find(fn.params[i].name);
		if (it == entry_param_regs_.end())
			continue;
		const string src = mir_abi_param_location(fn, i);
		if (src != it->second)
			out_ << "    mov " << it->second << ", " << src << "\n";
	}
	dump_multiuse_promoted_param_copies(fn); }

void MirDumper::dump_reference_store_source_param_copies(
    const lowir2cy86::Function& fn,
    set<string>& emitted_entry_params) {
	for (int pass = 0; pass < 2; ++pass) {
		for (size_t i = 0; i < fn.params.size(); ++i) {
			const string& name = fn.params[i].name;
			if (emitted_entry_params.find(name) !=
			    emitted_entry_params.end())
				continue;
			if (reference_store_source_params_.find(name) ==
			    reference_store_source_params_.end())
				continue;
			map<string, string>::const_iterator it =
			    entry_param_regs_.find(name);
			if (it == entry_param_regs_.end())
				continue;
			const bool writes_r8 = it->second == "r8";
			if ((pass == 0 && writes_r8) ||
			    (pass == 1 && !writes_r8))
				continue;
			const string src = mir_abi_param_location(fn, i);
			if (src != it->second)
				out_ << "    mov " << it->second << ", " << src << "\n";
			emitted_entry_params.insert(name);
		}
	}
}

bool MirDumper::dump_sret_constructor_entry_param_moves(
    const lowir2cy86::Function& fn,
    set<string>& emitted_entry_params) {
	if (!sret_constructor_like(fn))
		return false;
	dump_entry_param_move_if_mapped(fn, 0, emitted_entry_params);
	for (size_t i = 1; i < fn.params.size(); ++i)
		if (entry_param_regs_.find(fn.params[i].name) !=
		        entry_param_regs_.end() &&
		    entry_param_regs_.find(fn.params[i].name)->second == "r13")
			dump_entry_param_move_if_mapped(fn, i, emitted_entry_params);
	for (size_t i = 1; i < fn.params.size(); ++i)
		if (entry_param_regs_.find(fn.params[i].name) !=
		        entry_param_regs_.end() &&
		    entry_param_regs_.find(fn.params[i].name)->second == "rbx")
			dump_entry_param_move_if_mapped(fn, i, emitted_entry_params);
	for (size_t i = 1; i < fn.params.size(); ++i)
		if (entry_param_regs_.find(fn.params[i].name) !=
		        entry_param_regs_.end() &&
		    entry_param_regs_.find(fn.params[i].name)->second == "r12")
			dump_entry_param_move_if_mapped(fn, i, emitted_entry_params);
	for (size_t i = 1; i < fn.params.size(); ++i) {
		const string src = mir_abi_param_location(fn, i);
		if (src == "r8") {
			out_ << "    mov r9, r8\n";
			break;
		}
	}
	for (size_t i = 1; i < fn.params.size(); ++i) {
		const string src = mir_abi_param_location(fn, i);
		if (src == "rcx") {
			out_ << "    mov r8, rcx\n";
			break;
		}
	}
	return true;
}

void MirDumper::dump_entry_param_move_if_mapped(const lowir2cy86::Function& fn,
                                     size_t index,
                                     set<string>& emitted_entry_params) {
	if (index >= fn.params.size())
		return;
	map<string, string>::const_iterator it =
	    entry_param_regs_.find(fn.params[index].name);
	if (it == entry_param_regs_.end())
		return;
	const string src = mir_abi_param_location(fn, index);
	if (src != it->second)
		out_ << "    mov " << it->second << ", " << src << "\n";
	emitted_entry_params.insert(fn.params[index].name);
}

void MirDumper::dump_entry_pre_call_param_copies(const lowir2cy86::Function& fn,
                                      set<string>& emitted_entry_params) {
	if (!pre_call_param_copies_.empty()) {
		for (size_t i = 0; i < fn.params.size(); ++i) {
			const string& name = fn.params[i].name;
			if (pre_call_param_copies_.find(name) !=
			        pre_call_param_copies_.end() ||
			    copy_only_entry_param_regs_.find(name) ==
			        copy_only_entry_param_regs_.end())
				continue;
			map<string, string>::const_iterator eit =
			    entry_param_regs_.find(name);
			if (eit == entry_param_regs_.end())
				continue;
			const string src = mir_abi_param_location(fn, i);
			if (src != eit->second)
				out_ << "    mov " << eit->second << ", " << src << "\n";
			emitted_entry_params.insert(name);
		}
	}
	for (set<string>::const_iterator it = pre_call_param_copies_.begin();
	     it != pre_call_param_copies_.end(); ++it) {
		if (entry_param_regs_.find(*it) == entry_param_regs_.end())
			continue;
		const int index = param_index(fn, *it);
		if (index < 0)
			continue;
		out_ << "    mov r8, " << mir_abi_param_location(fn, index) << "\n";
	}
}

void MirDumper::dump_multiuse_promoted_param_copies(const lowir2cy86::Function& fn) {
	set<string> emitted;
	for (map<string, string>::const_iterator it = promoted_loads_.begin();
	     it != promoted_loads_.end(); ++it) {
		if (emitted.find(it->second) != emitted.end() ||
		    pre_call_param_copies_.find(it->second) != pre_call_param_copies_.end() ||
		    entry_param_regs_.find(it->second) != entry_param_regs_.end())
			continue;
		map<string, int>::const_iterator uit = use_counts_.find(it->first);
		if (uit == use_counts_.end() || uit->second <= 1)
			continue;
		const int index = param_index(fn, it->second);
		if (index < 0)
			continue;
		out_ << "    mov r8, " << mir_abi_param_location(fn, index) << "\n";
		emitted.insert(it->second);
	} }

bool MirDumper::materialize_sret_widened_promoted_load(
    const lowir2cy86::Function& fn,
    const lowir2cy86::Instruction& ins,
    bool emit) {
	if (!sret_constructor_like(fn) ||
	    ins.kind != lowir2cy86::InstrKind::Load ||
	    ins.a.kind != lowir2cy86::ValueKind::Slot ||
	    !sret_widened_store_source(fn, ins.dest))
		return false;
	map<string, string>::const_iterator pit =
	    promoted_slot_params_.find(ins.a.text);
	if (pit == promoted_slot_params_.end())
		return false;
	lowir2cy86::Value param;
	param.kind = lowir2cy86::ValueKind::Temp;
	param.text = pit->second;
	const string src = value_reg(fn, param);
	if (emit) {
		if (is_memory_operand(src))
			out_ << "    load." << ins.type.text << " r15, "
			     << src << "\n";
		else
			out_ << "    mov r15, " << src << "\n";
		dump_narrow_extend(ins.type, "r15");
	}
	remember_fixed_temp_reg(ins.dest, "r15");
	return true;
}

bool MirDumper::materialize_reference_store_source_promoted_load(
    const lowir2cy86::Function& fn,
    const lowir2cy86::Instruction& ins,
    bool emit) {
	if (ins.kind != lowir2cy86::InstrKind::Load ||
	    ins.a.kind != lowir2cy86::ValueKind::Slot ||
	    reference_store_source_temps_.find(ins.dest) ==
	        reference_store_source_temps_.end())
		return false;
	map<string, string>::const_iterator pit =
	    promoted_slot_params_.find(ins.a.text);
	if (pit == promoted_slot_params_.end() ||
	    reference_store_source_params_.find(pit->second) ==
	        reference_store_source_params_.end())
		return false;
	lowir2cy86::Value param;
	param.kind = lowir2cy86::ValueKind::Temp;
	param.text = pit->second;
	const string src = value_reg(fn, param);
	if (emit) {
		if (is_memory_operand(src))
			out_ << "    load." << ins.type.text << " r15, "
			     << src << "\n";
		else if (src != "r15")
			out_ << "    mov r15, " << src << "\n";
		dump_narrow_extend(ins.type, "r15");
	}
	remember_fixed_temp_reg(ins.dest, "r15");
	return true;
}

}  // namespace lowir2native
