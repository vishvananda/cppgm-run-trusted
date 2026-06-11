#include "lowir2native_mir_dumper.h"

namespace lowir2native {

void MirDumper::analyze_entry_param_regs(const lowir2cy86::Function& fn) {
	if (tls_pressure_frame_temps_.empty() && dense_integer_params(fn))
		analyze_dense_integer_param_regs(fn);
	assign_switch_case_param_regs(fn);
	size_t preserve = 0;
	for (size_t i = 0; i < fn.params.size(); ++i) {
		const string& name = fn.params[i].name;
		if (live_across_calls_.find(name) != live_across_calls_.end() &&
		    entry_param_regs_.find(name) == entry_param_regs_.end() &&
		    !mir_param_needs_slot(fn, i) &&
		    preserve < 5) {
			entry_param_regs_[name] = preserve_reg(preserve++);
			pre_call_abi_params_.insert(name);
		}
	}
	assign_forwarded_call_param_regs(fn);
	assign_call_arg_index_base_regs(fn);
	assign_pointer_store_param_regs(fn);
	assign_global_store_param_regs(fn);
	assign_param_base_load_regs(fn);
	assign_promoted_load_param_copies(fn);
	assign_copy_alias_param_regs(fn);
	assign_indirect_promoted_call_entry_copies(fn);
	assign_promoted_call_entry_copies(fn);
	assign_entry_branch_reference_param_regs(fn);
	assign_branch_edge_param_regs(fn);
	assign_reference_store_source_param_regs(fn);
	assign_sret_constructor_entry_param_regs(fn);
	for (size_t i = 0; i < fn.params.size(); ++i) {
		const string& name = fn.params[i].name;
		if (!lowir2cy86::is_ptr_type(fn.params[i].type) ||
		    entry_param_regs_.find(name) != entry_param_regs_.end())
			continue;
		if (name == "%ret" && param_is_index_base(fn, name))
			entry_param_regs_[name] = "rbx";
		else if (param_pass_is(fn, i, "indirect_result"))
			entry_param_regs_[name] = "r8";
		else if (param_pass_is(fn, i, "reference") &&
		         use_counts_.find(name) != use_counts_.end() &&
		         use_counts_.find(name)->second != 0 &&
		         !param_only_feeds_direct_param_copy(fn, name) &&
		         reference_store_dest_params_.find(name) ==
		             reference_store_dest_params_.end())
			entry_param_regs_[name] = "r9";
	}
	analyze_object_result_field_params(fn); }

void MirDumper::assign_sret_constructor_entry_param_regs(const lowir2cy86::Function& fn) {
	if (!sret_constructor_like(fn))
		return;
	if (!fn.params.empty())
		entry_param_regs_[fn.params[0].name] = "r14";
	size_t live_scalar = 0;
	for (size_t i = 1; i < fn.params.size(); ++i) {
		const string& name = fn.params[i].name;
		if (live_across_calls_.find(name) == live_across_calls_.end())
			continue;
		if (param_pass_is(fn, i, "reference") &&
		    lowir2cy86::is_ptr_type(fn.params[i].type)) {
			entry_param_regs_[name] = "r12";
			continue;
		}
		if (mir_param_needs_slot(fn, i) ||
		    !lowir2cy86::is_integer_type(fn.params[i].type))
			continue;
		if (live_scalar == 0)
			entry_param_regs_[name] = "r13";
		else if (live_scalar == 1)
			entry_param_regs_[name] = "rbx";
		++live_scalar;
	}
	forced_preserve_count_ =
	    max(forced_preserve_count_, static_cast<size_t>(5));
}

void MirDumper::assign_entry_branch_reference_param_regs(
    const lowir2cy86::Function& fn) {
	if (entry_branch_param_loads_.empty() ||
	    fn.params.empty() ||
	    fn.params[0].name != "%ret" ||
	    !param_pass_is(fn, 0, "indirect_result"))
		return;
	set<string> refs;
	for (map<string, string>::const_iterator it =
	         entry_branch_param_loads_.begin();
	     it != entry_branch_param_loads_.end(); ++it)
		refs.insert(it->second);
	for (size_t i = 1; i < fn.params.size(); ++i) {
		const string& name = fn.params[i].name;
		if (entry_param_regs_.find(name) != entry_param_regs_.end())
			continue;
		if (refs.find(name) != refs.end()) {
			entry_param_regs_[name] = "r8";
			continue;
		}
		if (lowir2cy86::is_ptr_type(fn.params[i].type) &&
		    lowir2cy86::metadata_value(fn.params[i].metadata,
		                               "pass").empty()) {
			entry_param_regs_[name] = "r9";
			pre_call_abi_params_.insert(name);
		}
	}
}

void MirDumper::assign_reference_store_source_param_regs(const lowir2cy86::Function& fn) {
	for (set<string>::const_iterator it =
	         reference_store_source_params_.begin();
	     it != reference_store_source_params_.end(); ++it) {
		if (entry_param_regs_.find(*it) != entry_param_regs_.end())
			continue;
		const int index = param_index(fn, *it);
		if (index < 0 || mir_param_needs_slot(fn, index))
			continue;
		const string abi = mir_abi_param_location(fn, index);
		if (abi == "rdx") {
			entry_param_regs_[*it] = "r8";
		} else if (abi == "rcx") {
			entry_param_regs_[*it] = "rbx";
		} else if (abi == "r8") {
			entry_param_regs_[*it] = "r13";
		}
	}
	if (!reference_store_source_params_.empty())
		forced_preserve_count_ =
		    max(forced_preserve_count_, static_cast<size_t>(5));
}

void MirDumper::assign_pointer_store_param_regs(const lowir2cy86::Function& fn) {
	static const char* const regs[] = {"r8", "r9"};
	const bool single_param = fn.params.size() == 1;
	size_t next = 0;
	for (size_t i = 0; i < fn.params.size(); ++i) {
		const string& name = fn.params[i].name;
		if (param_store_dests_.find(name) == param_store_dests_.end() ||
		    entry_param_regs_.find(name) != entry_param_regs_.end() ||
		    name == "%ret" ||
		    !lowir2cy86::metadata_value(fn.params[i].metadata, "pass").empty() ||
		    next >= sizeof(regs) / sizeof(regs[0]))
			continue;
		entry_param_regs_[name] = single_param ? "r9" : regs[next++];
	}
}

void MirDumper::assign_global_store_param_regs(const lowir2cy86::Function& fn) {
	size_t global_stores = 0;
	for (size_t b = 0; b < fn.blocks.size(); ++b)
		for (size_t i = 0; i < fn.blocks[b].instructions.size(); ++i) {
			const lowir2cy86::Instruction& ins = fn.blocks[b].instructions[i];
			if (ins.kind == lowir2cy86::InstrKind::Store &&
			    ins.b.kind == lowir2cy86::ValueKind::Global &&
			    !is_thread_local_global(ins.b.text))
				++global_stores;
		}
	if (global_stores < 2)
		return;
	for (size_t b = 0; b < fn.blocks.size(); ++b)
		for (size_t i = 0; i < fn.blocks[b].instructions.size(); ++i) {
			const lowir2cy86::Instruction& ins = fn.blocks[b].instructions[i];
			if (ins.kind != lowir2cy86::InstrKind::Store ||
			    ins.b.kind != lowir2cy86::ValueKind::Global ||
			    ins.a.kind != lowir2cy86::ValueKind::Temp ||
			    entry_param_regs_.find(ins.a.text) != entry_param_regs_.end())
				continue;
			const int index = param_index(fn, ins.a.text);
			if (index < 0 ||
			    mir_abi_param_location(fn, index) != "rcx" ||
			    !lowir2cy86::is_integer_type(fn.params[index].type) ||
			    fn.params[index].type.bits >= 64)
				continue;
			entry_param_regs_[ins.a.text] = "rbx";
		}
}

void MirDumper::analyze_call_arg_addr_regs(const lowir2cy86::Function& fn) {
	for (size_t b = 0; b < fn.blocks.size(); ++b)
		for (size_t i = 0; i < fn.blocks[b].instructions.size(); ++i) {
			const lowir2cy86::Instruction& ins = fn.blocks[b].instructions[i];
			if (ins.kind != lowir2cy86::InstrKind::Call)
				continue;
			for (size_t a = 0; a < ins.args.size(); ++a) {
				const lowir2cy86::Value& arg = ins.args[a];
				if (arg.kind != lowir2cy86::ValueKind::Temp ||
				    use_counts_[arg.text] != 1 ||
				    live_across_calls_.find(arg.text) !=
				        live_across_calls_.end())
					continue;
				if (mir_call_arg_register(program_, fn, ins, a).empty())
					continue;
				map<string, const lowir2cy86::Instruction*>::const_iterator it =
				    definitions_.find(arg.text);
				if (it == definitions_.end() ||
				    it->second->kind != lowir2cy86::InstrKind::Addr)
					continue;
				call_arg_addr_regs_[arg.text] = "r8";
			}
		}
}

void MirDumper::analyze_call_arg_index_regs(const lowir2cy86::Function& fn) {
	for (size_t b = 0; b < fn.blocks.size(); ++b)
		for (size_t i = 0; i < fn.blocks[b].instructions.size(); ++i) {
			const lowir2cy86::Instruction& ins = fn.blocks[b].instructions[i];
			if (ins.kind != lowir2cy86::InstrKind::Call)
				continue;
			for (size_t a = 0; a < ins.args.size(); ++a) {
				const lowir2cy86::Value& arg = ins.args[a];
				if (arg.kind != lowir2cy86::ValueKind::Temp ||
				    use_counts_[arg.text] != 1)
					continue;
				map<string, const lowir2cy86::Instruction*>::const_iterator it =
				    definitions_.find(arg.text);
				if (it == definitions_.end() ||
				    it->second->kind != lowir2cy86::InstrKind::Index)
					continue;
				if (index_base_is_reference_param(fn, it->second->a) &&
				    !fn.params.empty() &&
				    fn.params[0].name == "%ret" &&
				    param_pass_is(fn, 0, "indirect_result"))
					continue;
				const string reg = mir_call_arg_register(program_, fn, ins, a);
				if (reg.empty())
					continue;
				const lowir2cy86::Type type =
				    mir_call_param_type(program_, fn, ins, a);
				if (mir_is_xmm_type(type))
					continue;
				call_arg_index_regs_[arg.text] = reg;
				const lowir2cy86::Value& base = it->second->a;
				if (base.kind == lowir2cy86::ValueKind::Temp &&
				    param_index(fn, base.text) >= 0 &&
				    find(call_arg_index_base_params_.begin(),
				         call_arg_index_base_params_.end(),
				         base.text) == call_arg_index_base_params_.end())
					call_arg_index_base_params_.push_back(base.text);
			}
		}
}

bool MirDumper::index_base_is_reference_param(const lowir2cy86::Function& fn,
                                   const lowir2cy86::Value& base) const {
	if (base.kind != lowir2cy86::ValueKind::Temp)
		return false;
	return temp_origin_is_reference_param(fn, base.text);
}

void MirDumper::assign_call_arg_index_base_regs(const lowir2cy86::Function& fn) {
	static const char* const regs[] = {"r8", "r9"};
	size_t next = 0;
	for (size_t i = 0; i < call_arg_index_base_params_.size(); ++i) {
		const string& name = call_arg_index_base_params_[i];
		if (entry_param_regs_.find(name) != entry_param_regs_.end())
			continue;
		if (param_index(fn, name) < 0)
			continue;
		while (next < sizeof(regs) / sizeof(regs[0]) &&
		       entry_reg_in_use(regs[next]))
			++next;
		if (next >= sizeof(regs) / sizeof(regs[0]))
			return;
		entry_param_regs_[name] = regs[next++];
	}
}

void MirDumper::assign_promoted_load_param_copies(const lowir2cy86::Function& fn) {
	bool promoted_branch_after_call = false;
	for (size_t b = 0; b < fn.blocks.size(); ++b) {
		bool saw_call = false;
		for (size_t i = 0; i < fn.blocks[b].instructions.size(); ++i) {
			const lowir2cy86::Instruction& ins = fn.blocks[b].instructions[i];
			if (ins.kind == lowir2cy86::InstrKind::Call) {
				if (ins.a.kind == lowir2cy86::ValueKind::Function) {
					for (size_t a = 0; a < ins.args.size(); ++a)
						assign_promoted_call_arg_copy(fn, ins.args[a]);
				}
				saw_call = true;
			}
			if (!saw_call || ins.kind != lowir2cy86::InstrKind::Branch ||
			    ins.a.kind != lowir2cy86::ValueKind::Temp)
				continue;
			map<string, const lowir2cy86::Instruction*>::const_iterator it =
			    definitions_.find(ins.a.text);
			if (it == definitions_.end() ||
			    it->second->kind != lowir2cy86::InstrKind::Cmp)
				continue;
			if (assign_promoted_branch_copy(fn, it->second->a) ||
			    assign_promoted_branch_copy(fn, it->second->b))
				promoted_branch_after_call = true;
		}
	}
	if (promoted_branch_after_call)
		branch_cmp_call_result_frame_preserve_ = true;
	if (promoted_branch_after_call)
		forced_preserve_count_ =
		    max(forced_preserve_count_, static_cast<size_t>(3));
}

void MirDumper::assign_copy_alias_param_regs(const lowir2cy86::Function& fn) {
	bool assigned = false;
	for (map<string, string>::const_iterator it =
	         copy_alias_call_args_.begin();
	     it != copy_alias_call_args_.end(); ++it) {
		if (param_index(fn, it->second) < 0 ||
		    entry_param_regs_.find(it->second) != entry_param_regs_.end())
			continue;
		entry_param_regs_[it->second] = "r9";
		copy_only_entry_param_regs_.insert(it->second);
		assigned = true;
	}
	if (assigned)
		forced_preserve_count_ =
		    max(forced_preserve_count_, static_cast<size_t>(1));
}

void MirDumper::assign_promoted_call_arg_copy(const lowir2cy86::Function& fn,
                                   const lowir2cy86::Value& arg) {
	if (arg.kind != lowir2cy86::ValueKind::Temp)
		return;
	map<string, string>::const_iterator pit = promoted_loads_.find(arg.text);
	if (pit == promoted_loads_.end() ||
	    entry_param_regs_.find(pit->second) != entry_param_regs_.end())
		return;
	map<string, lowir2cy86::Type>::const_iterator tit =
	    fn.param_types.find(pit->second);
	if (tit == fn.param_types.end() || !lowir2cy86::is_ptr_type(tit->second))
		return;
	entry_param_regs_[pit->second] = "r9";
	copy_only_entry_param_regs_.insert(pit->second);
}

bool MirDumper::assign_promoted_branch_copy(const lowir2cy86::Function& fn,
                                 const lowir2cy86::Value& value) {
	if (value.kind != lowir2cy86::ValueKind::Temp)
		return false;
	map<string, string>::const_iterator pit = promoted_loads_.find(value.text);
	if (pit == promoted_loads_.end())
		return false;
	map<string, lowir2cy86::Type>::const_iterator tit =
	    fn.param_types.find(pit->second);
	if (tit == fn.param_types.end() ||
	    lowir2cy86::is_ptr_type(tit->second))
		return false;
	pre_call_param_copies_.insert(pit->second);
	return true;
}

void MirDumper::assign_forwarded_call_param_regs(const lowir2cy86::Function& fn) {
	if (entry_param_regs_.empty())
		return;
	static const char* const regs[] = {"r8", "r9"};
	size_t next = 0;
	for (size_t b = 0; b < fn.blocks.size(); ++b)
		for (size_t i = 0; i < fn.blocks[b].instructions.size(); ++i) {
			const lowir2cy86::Instruction& ins = fn.blocks[b].instructions[i];
			if (ins.kind != lowir2cy86::InstrKind::Call)
				continue;
			bool forwards_preserved = false;
			for (size_t a = 0; a < ins.args.size(); ++a)
				if (ins.args[a].kind == lowir2cy86::ValueKind::Temp &&
				    entry_param_regs_.find(ins.args[a].text) !=
				        entry_param_regs_.end())
					forwards_preserved = true;
			if (!forwards_preserved)
				continue;
			for (size_t a = 0; a < ins.args.size(); ++a) {
				if (ins.args[a].kind != lowir2cy86::ValueKind::Temp ||
				    param_index(fn, ins.args[a].text) < 0 ||
				    entry_param_regs_.find(ins.args[a].text) !=
				        entry_param_regs_.end())
					continue;
				while (next < sizeof(regs) / sizeof(regs[0]) &&
				       entry_reg_in_use(regs[next]))
					++next;
				if (next >= sizeof(regs) / sizeof(regs[0]))
					return;
				entry_param_regs_[ins.args[a].text] = regs[next++];
			}
		}
}

void MirDumper::assign_switch_case_param_regs(const lowir2cy86::Function& fn) {
	bool has_switch = false;
	for (size_t i = 0; i < fn.blocks.size(); ++i)
		for (size_t j = 0; j < fn.blocks[i].instructions.size(); ++j)
			if (fn.blocks[i].instructions[j].kind ==
			    lowir2cy86::InstrKind::Switch) {
				has_switch = true;
				const lowir2cy86::Value& selector =
				    fn.blocks[i].instructions[j].a;
				if (selector.kind == lowir2cy86::ValueKind::Temp &&
				    param_index(fn, selector.text) >= 0) {
					entry_param_regs_[selector.text] = "r9";
					copy_only_entry_param_regs_.insert(selector.text);
				}
			}
	if (!has_switch)
		return;
	size_t preserve = 0;
	for (size_t b = 1; b < fn.blocks.size(); ++b)
		for (size_t i = 0; i < fn.blocks[b].instructions.size(); ++i) {
			const lowir2cy86::Instruction& ins = fn.blocks[b].instructions[i];
			if (ins.kind != lowir2cy86::InstrKind::Call)
				continue;
			for (size_t a = ins.args.size(); a > 0; --a) {
				const lowir2cy86::Value& arg = ins.args[a - 1];
				if (arg.kind != lowir2cy86::ValueKind::Temp ||
				    param_index(fn, arg.text) < 0 ||
				    live_across_calls_.find(arg.text) ==
				        live_across_calls_.end() ||
				    entry_param_regs_.find(arg.text) !=
				        entry_param_regs_.end())
					continue;
				entry_param_regs_[arg.text] = preserve_reg(preserve++);
			}
		}
}

bool MirDumper::entry_reg_in_use(const string& reg) const {
	for (map<string, string>::const_iterator it = entry_param_regs_.begin();
	     it != entry_param_regs_.end(); ++it)
		if (it->second == reg)
			return true;
	return false;
}

void MirDumper::assign_param_base_load_regs(const lowir2cy86::Function& fn) {
	for (map<string, string>::const_iterator pit = param_base_load_params_.begin();
	     pit != param_base_load_params_.end(); ++pit) {
		const int index = param_index(fn, pit->second);
		if (index < 0 ||
		    entry_param_regs_.find(pit->second) != entry_param_regs_.end())
			continue;
		entry_param_regs_[pit->second] = preserve_reg(0);
		forced_preserve_count_ = max(forced_preserve_count_, static_cast<size_t>(2));
	}
}

void MirDumper::assign_indirect_promoted_call_entry_copies(const lowir2cy86::Function& fn) {
	static const char* const regs[] = {"r9", "r8"};
	size_t next = 0;
	set<string> params;
	for (size_t b = 0; b < fn.blocks.size(); ++b)
		for (size_t i = 0; i < fn.blocks[b].instructions.size(); ++i) {
			const lowir2cy86::Instruction& ins = fn.blocks[b].instructions[i];
			if (ins.kind != lowir2cy86::InstrKind::Call ||
			    ins.a.kind == lowir2cy86::ValueKind::Function)
				continue;
			note_promoted_call_arg_param(ins.a, params);
			for (size_t a = 0; a < ins.args.size(); ++a)
				if (mir_call_arg_needs_address(program_, ins, a))
					note_promoted_call_arg_param(ins.args[a], params);
		}
	for (size_t i = 0; i < fn.params.size(); ++i) {
		if (params.find(fn.params[i].name) == params.end() ||
		    entry_param_regs_.find(fn.params[i].name) != entry_param_regs_.end())
			continue;
		if (next >= sizeof(regs) / sizeof(regs[0]))
			break;
		entry_param_regs_[fn.params[i].name] = regs[next++];
		delayed_entry_param_regs_.insert(fn.params[i].name);
	}
	if (!params.empty())
		forced_preserve_count_ =
		    max(forced_preserve_count_, static_cast<size_t>(3));
}

void MirDumper::assign_promoted_call_entry_copies(const lowir2cy86::Function& fn) {
	set<string> params;
	for (size_t b = 0; b < fn.blocks.size(); ++b)
		for (size_t i = 0; i < fn.blocks[b].instructions.size(); ++i) {
			const lowir2cy86::Instruction& ins = fn.blocks[b].instructions[i];
			if (ins.kind != lowir2cy86::InstrKind::Call ||
			    ins.a.kind != lowir2cy86::ValueKind::Function ||
			    mir_call_stack_arg_bytes(program_, fn, ins) != 0)
				continue;
			if (!call_has_indexed_promoted_arg(ins))
				continue;
			for (size_t a = 0; a < ins.args.size(); ++a)
				note_promoted_call_arg_param(ins.args[a], params);
		}
	bool assigned = false;
	for (set<string>::const_iterator it = params.begin();
	     it != params.end(); ++it) {
		if (entry_param_regs_.find(*it) != entry_param_regs_.end())
			continue;
		const lowir2cy86::Type type = fn.param_types.find(*it)->second;
		entry_param_regs_[*it] = lowir2cy86::is_ptr_type(type) ? "r9" : "r8";
		copy_only_entry_param_regs_.insert(*it);
		assigned = true;
	}
	if (assigned)
		forced_preserve_count_ =
		    max(forced_preserve_count_, static_cast<size_t>(3));
}

bool MirDumper::call_has_indexed_promoted_arg(const lowir2cy86::Instruction& ins) const {
	for (size_t a = 0; a < ins.args.size(); ++a) {
		if (ins.args[a].kind != lowir2cy86::ValueKind::Temp)
			continue;
		map<string, const lowir2cy86::Instruction*>::const_iterator it =
		    definitions_.find(ins.args[a].text);
		if (it == definitions_.end() ||
		    it->second->kind != lowir2cy86::InstrKind::Index ||
		    it->second->a.kind != lowir2cy86::ValueKind::Temp)
			continue;
		if (promoted_loads_.find(it->second->a.text) !=
		    promoted_loads_.end())
			return true;
	}
	return false;
}

void MirDumper::note_promoted_call_arg_param(const lowir2cy86::Value& arg,
                                  set<string>& params) const {
	if (arg.kind != lowir2cy86::ValueKind::Temp)
		return;
	map<string, string>::const_iterator pit = promoted_loads_.find(arg.text);
	if (pit != promoted_loads_.end()) {
		params.insert(pit->second);
		return;
	}
	map<string, const lowir2cy86::Instruction*>::const_iterator it =
	    definitions_.find(arg.text);
	if (it == definitions_.end() ||
	    it->second->kind != lowir2cy86::InstrKind::Index ||
	    it->second->a.kind != lowir2cy86::ValueKind::Temp)
		return;
	pit = promoted_loads_.find(it->second->a.text);
	if (pit != promoted_loads_.end())
		params.insert(pit->second);
}

void MirDumper::assign_branch_edge_param_regs(const lowir2cy86::Function& fn) {
	static const char* const regs[] = {"r8", "r9"};
	size_t next = 0;
	for (size_t i = 0; i < fn.params.size(); ++i)
		if (entry_param_regs_.find(fn.params[i].name) != entry_param_regs_.end())
			++next;
	for (size_t i = 0; i < fn.params.size(); ++i) {
		const string& name = fn.params[i].name;
		if (entry_param_regs_.find(name) != entry_param_regs_.end())
			continue;
		if (!param_needs_branch_edge_copy(fn, name))
			continue;
		const bool delayed = param_copy_delays_entry_use(fn, name);
		const string reg = delayed &&
		                   entry_param_regs_.empty() ? "r9" :
		    next < sizeof(regs) / sizeof(regs[0])
		        ? regs[next]
		        : preserve_reg(next - 2);
		entry_param_regs_[name] = reg;
		if (delayed)
			delayed_entry_param_regs_.insert(name);
		++next;
	}
	if (!entry_param_regs_.empty() && fn.blocks.size() > 1)
		forced_preserve_count_ =
		    max(forced_preserve_count_, entry_preserve_reg_count());
}

size_t MirDumper::entry_preserve_reg_count() const {
	size_t count = 0;
	for (map<string, string>::const_iterator it = entry_param_regs_.begin();
	     it != entry_param_regs_.end(); ++it)
		if (copy_only_entry_param_regs_.find(it->first) ==
		    copy_only_entry_param_regs_.end())
			++count;
	return count;
}

bool MirDumper::param_needs_branch_edge_copy(const lowir2cy86::Function& fn,
                                  const string& name) const {
	if (fn.blocks.size() <= 1)
		return false;
	if (param_used_after_entry(fn, name))
		return true;
	if (param_copy_used_after_entry(fn, name))
		return true;
	for (size_t b = 0; b < fn.blocks.size(); ++b)
		for (size_t i = 0; i < fn.blocks[b].instructions.size(); ++i) {
			const lowir2cy86::Instruction& ins = fn.blocks[b].instructions[i];
			if (ins.kind == lowir2cy86::InstrKind::Branch &&
			    ins.a.kind == lowir2cy86::ValueKind::Temp) {
				map<string, const lowir2cy86::Instruction*>::const_iterator it =
				    definitions_.find(ins.a.text);
				if (it != definitions_.end() &&
				    it->second->kind == lowir2cy86::InstrKind::Cmp &&
				    (temp_value_named(it->second->a, name) ||
				     temp_value_named(it->second->b, name)))
					return true;
			}
		}
	return false;
}

bool MirDumper::param_copy_delays_entry_use(const lowir2cy86::Function& fn,
                                 const string& name) const {
	map<string, lowir2cy86::Type>::const_iterator it =
	    fn.param_types.find(name);
	return it != fn.param_types.end() &&
	       lowir2cy86::is_ptr_type(it->second) &&
	       param_used_after_entry(fn, name) &&
	       !param_copy_used_after_entry(fn, name);
}

bool MirDumper::param_used_after_entry(const lowir2cy86::Function& fn,
                            const string& name) const {
	for (size_t b = 1; b < fn.blocks.size(); ++b)
		for (size_t i = 0; i < fn.blocks[b].instructions.size(); ++i)
			if (instruction_uses_temp(fn.blocks[b].instructions[i], name))
				return true;
	return false;
}

bool MirDumper::param_copy_used_after_entry(const lowir2cy86::Function& fn,
                                 const string& name) const {
	set<string> copies;
	for (size_t i = 0; i < fn.blocks.size(); ++i)
		for (size_t j = 0; j < fn.blocks[i].instructions.size(); ++j) {
			const lowir2cy86::Instruction& ins = fn.blocks[i].instructions[j];
			if (ins.kind == lowir2cy86::InstrKind::Copy &&
			    ins.a.kind == lowir2cy86::ValueKind::Temp &&
			    ins.a.text == name)
				copies.insert(ins.dest);
		}
	for (set<string>::const_iterator it = copies.begin();
	     it != copies.end(); ++it)
		if (temp_used_after_entry(fn, *it))
			return true;
	return false;
}

bool MirDumper::temp_used_after_entry(const lowir2cy86::Function& fn,
                           const string& name) const {
	for (size_t b = 1; b < fn.blocks.size(); ++b)
		for (size_t i = 0; i < fn.blocks[b].instructions.size(); ++i)
			if (instruction_uses_temp(fn.blocks[b].instructions[i], name))
				return true;
	return false;
}

bool MirDumper::param_used_only_after_entry(const lowir2cy86::Function& fn,
                                 const string& name) const {
	bool used_after = false;
	bool used_entry = false;
	for (size_t b = 0; b < fn.blocks.size(); ++b)
		for (size_t i = 0; i < fn.blocks[b].instructions.size(); ++i) {
			const lowir2cy86::Instruction& ins = fn.blocks[b].instructions[i];
			if (!instruction_uses_temp(ins, name))
				continue;
			if (b == 0)
				used_entry = true;
			else
				used_after = true;
		}
	return used_after && !used_entry;
}

bool MirDumper::instruction_uses_temp(const lowir2cy86::Instruction& ins,
                           const string& name) const {
	if (temp_value_named(ins.a, name) || temp_value_named(ins.b, name) ||
	    temp_value_named(ins.c, name))
		return true;
	for (size_t i = 0; i < ins.args.size(); ++i)
		if (temp_value_named(ins.args[i], name))
			return true;
	for (size_t i = 0; i < ins.switch_cases.size(); ++i)
		if (temp_value_named(ins.switch_cases[i].value, name))
			return true;
	return false;
}

bool MirDumper::dense_integer_params(const lowir2cy86::Function& fn) const {
	if (fn.params.size() < 6)
		return false;
	for (size_t i = 0; i < fn.params.size(); ++i)
		if (!lowir2cy86::is_integer_type(fn.params[i].type) &&
		    !lowir2cy86::is_ptr_type(fn.params[i].type))
			return false;
	return has_integer_or_pointer_binary(fn); }

bool MirDumper::has_integer_or_pointer_binary(const lowir2cy86::Function& fn) const {
	for (size_t b = 0; b < fn.blocks.size(); ++b)
		for (size_t i = 0; i < fn.blocks[b].instructions.size(); ++i) {
			const lowir2cy86::Instruction& ins = fn.blocks[b].instructions[i];
			if (ins.kind == lowir2cy86::InstrKind::Binary &&
			    (lowir2cy86::is_integer_type(ins.type) ||
			     lowir2cy86::is_ptr_type(ins.type)))
				return true;
		}
	return false; }

void MirDumper::analyze_dense_integer_param_regs(const lowir2cy86::Function& fn) {
	static const char* const regs[] = {"r15", "r9", "rbx", "r12", "r13", "r14"};
	const size_t n = fn.params.size() < 6 ? fn.params.size() : 6;
	for (size_t i = 0; i < n; ++i)
		entry_param_regs_[fn.params[i].name] = regs[i]; }

}  // namespace lowir2native
