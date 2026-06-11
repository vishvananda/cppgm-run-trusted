#include "lowir2native_mir_dumper.h"

namespace lowir2native {

void MirDumper::analyze_full_gpr_indirect_call_temps(const lowir2cy86::Function& fn) {
	for (size_t b = 0; b < fn.blocks.size(); ++b)
		for (size_t i = 0; i < fn.blocks[b].instructions.size(); ++i) {
			const lowir2cy86::Instruction& ins = fn.blocks[b].instructions[i];
			if (!full_gpr_indirect_call(fn, ins))
				continue;
			if (ins.has_dest)
				frame_temps_.insert(ins.dest);
			if (ins.a.kind == lowir2cy86::ValueKind::Temp) {
				map<string, const lowir2cy86::Instruction*>::const_iterator it =
				    definitions_.find(ins.a.text);
				if (it != definitions_.end() &&
				    it->second->kind == lowir2cy86::InstrKind::Load &&
				    it->second->a.kind == lowir2cy86::ValueKind::Temp)
					full_gpr_indirect_callee_loads_.insert(ins.a.text);
			}
			for (size_t a = 0; a < ins.args.size(); ++a) {
				if (ins.args[a].kind != lowir2cy86::ValueKind::Temp)
					continue;
				map<string, const lowir2cy86::Instruction*>::const_iterator it =
				    definitions_.find(ins.args[a].text);
				if (it != definitions_.end() &&
				    it->second->kind == lowir2cy86::InstrKind::Call) {
					late_indirect_arg_temps_.insert(ins.args[a].text);
				}
			}
		} }

void MirDumper::analyze_direct_object_call_arg_temps(const lowir2cy86::Function& fn) {
	for (size_t b = 0; b < fn.blocks.size(); ++b)
		for (size_t i = 0; i < fn.blocks[b].instructions.size(); ++i) {
			const lowir2cy86::Instruction& ins = fn.blocks[b].instructions[i];
			if (ins.kind != lowir2cy86::InstrKind::Call)
				continue;
			for (size_t a = 0; a < ins.args.size(); ++a) {
				if (ins.args[a].kind != lowir2cy86::ValueKind::Temp ||
				    !lowir2cy86::is_obj_type(
				        mir_call_param_type(program_, fn, ins, a)))
					continue;
				map<string, const lowir2cy86::Instruction*>::const_iterator it =
				    definitions_.find(ins.args[a].text);
				if (it != definitions_.end() &&
				    it->second->kind == lowir2cy86::InstrKind::Call &&
				    lowir2cy86::is_obj_type(it->second->type))
					frame_temps_.insert(ins.args[a].text);
			}
		} }

void MirDumper::analyze_pre_call_param_copies(const lowir2cy86::Function& fn) {
	set<string> stored_global_params;
	for (size_t b = 0; b < fn.blocks.size(); ++b)
		for (size_t i = 0; i < fn.blocks[b].instructions.size(); ++i) {
			const lowir2cy86::Instruction& ins = fn.blocks[b].instructions[i];
			if (ins.kind == lowir2cy86::InstrKind::Store &&
			    ins.a.kind == lowir2cy86::ValueKind::Temp) {
				map<string, const lowir2cy86::Instruction*>::const_iterator git =
				    definitions_.find(ins.a.text);
				if (git == definitions_.end() ||
				    git->second->kind != lowir2cy86::InstrKind::Addr ||
				    git->second->a.kind != lowir2cy86::ValueKind::Global)
					continue;
				lowir2cy86::Value dst = promoted_store_dest(ins.b);
				if (dst.kind == lowir2cy86::ValueKind::Temp &&
				    param_index(fn, dst.text) >= 0)
					stored_global_params.insert(dst.text);
			}
			if (ins.kind != lowir2cy86::InstrKind::Call)
				continue;
			for (size_t a = 0; a < ins.args.size(); ++a) {
				if (ins.args[a].kind != lowir2cy86::ValueKind::Temp)
					continue;
				map<string, string>::const_iterator pit =
				    promoted_loads_.find(ins.args[a].text);
				if (pit != promoted_loads_.end() &&
				    stored_global_params.find(pit->second) != stored_global_params.end())
					pre_call_param_copies_.insert(pit->second);
			}
		} }

void MirDumper::analyze_copy_alias_call_args(const lowir2cy86::Function& fn) {
	map<string, string> copy_source_param;
	set<string> copied_after_aliasing_object;
	for (size_t b = 0; b < fn.blocks.size(); ++b)
		for (size_t i = 0; i < fn.blocks[b].instructions.size(); ++i) {
			const lowir2cy86::Instruction& ins = fn.blocks[b].instructions[i];
			if (ins.kind == lowir2cy86::InstrKind::Copy &&
			    ins.a.kind == lowir2cy86::ValueKind::Temp &&
			    param_index(fn, ins.a.text) >= 0) {
				copy_source_param[ins.dest] = ins.a.text;
				continue;
			}
			if (ins.kind == lowir2cy86::InstrKind::CopyObj &&
			    ins.a.kind == lowir2cy86::ValueKind::Temp) {
				for (map<string, string>::const_iterator it =
				         copy_source_param.begin();
				     it != copy_source_param.end(); ++it)
					if (it->second == ins.a.text)
						copied_after_aliasing_object.insert(it->first);
				continue;
			}
			if (ins.kind != lowir2cy86::InstrKind::Call)
				continue;
			for (size_t a = 0; a < ins.args.size(); ++a) {
				if (ins.args[a].kind != lowir2cy86::ValueKind::Temp ||
				    copied_after_aliasing_object.find(ins.args[a].text) ==
				        copied_after_aliasing_object.end())
					continue;
				copy_alias_call_args_[ins.args[a].text] =
				    copy_source_param[ins.args[a].text];
			}
		}
}

void MirDumper::analyze_tls_store_sources(const lowir2cy86::Function& fn) {
	map<string, int> def_pos;
	int pos = 0;
	for (size_t b = 0; b < fn.blocks.size(); ++b)
		for (size_t i = 0; i < fn.blocks[b].instructions.size(); ++i, ++pos)
			if (fn.blocks[b].instructions[i].has_dest)
				def_pos[fn.blocks[b].instructions[i].dest] = pos;
	pos = 0;
	for (size_t b = 0; b < fn.blocks.size(); ++b)
		for (size_t i = 0; i < fn.blocks[b].instructions.size(); ++i, ++pos) {
			const lowir2cy86::Instruction& ins = fn.blocks[b].instructions[i];
			if (ins.kind == lowir2cy86::InstrKind::Store &&
			    ins.a.kind == lowir2cy86::ValueKind::Temp &&
			    ins.b.kind == lowir2cy86::ValueKind::Global &&
			    is_thread_local_global(ins.b.text)) {
				tls_store_sources_.insert(ins.a.text);
				live_across_calls_.insert(ins.a.text);
				analyze_tls_pressure_temps(fn, pos, def_pos);
			}
		} }

void MirDumper::analyze_tls_pressure_temps(const lowir2cy86::Function& fn,
                                int store_pos,
                                const map<string, int>& def_pos) {
	vector<string> live;
	for (size_t t = 0; t < fn.temp_order.size(); ++t) {
		const string& name = fn.temp_order[t];
		map<string, int>::const_iterator dit = def_pos.find(name);
		map<string, lowir2cy86::Type>::const_iterator tit =
		    fn.temp_types.find(name);
		if (dit == def_pos.end() || dit->second >= store_pos ||
		    tit == fn.temp_types.end() ||
		    (!lowir2cy86::is_integer_type(tit->second) &&
		     !lowir2cy86::is_ptr_type(tit->second)) ||
		    !temp_used_after_position(fn, name, store_pos))
			continue;
		live.push_back(name);
	}
	if (live.empty())
		return;
	tls_accumulator_temps_.insert(live[0]);
	for (size_t i = 1; i < live.size(); ++i) {
		tls_pressure_frame_temps_.insert(live[i]);
		frame_temps_.insert(live[i]);
	}
	forced_preserve_count_ =
	    max(forced_preserve_count_, static_cast<size_t>(5));
}

bool MirDumper::temp_used_after_position(const lowir2cy86::Function& fn,
                              const string& name,
                              int after_pos) const {
	int pos = 0;
	for (size_t b = 0; b < fn.blocks.size(); ++b)
		for (size_t i = 0; i < fn.blocks[b].instructions.size(); ++i, ++pos)
			if (pos > after_pos &&
			    instruction_uses_temp(fn.blocks[b].instructions[i], name))
				return true;
	return false;
}

void MirDumper::analyze_stack_arg_call_homes(const lowir2cy86::Function& fn) {
	for (size_t b = 0; b < fn.blocks.size(); ++b)
		for (size_t i = 0; i < fn.blocks[b].instructions.size(); ++i) {
			const lowir2cy86::Instruction& ins = fn.blocks[b].instructions[i];
			if (ins.kind != lowir2cy86::InstrKind::Call ||
			    lowir2cy86::is_f80_type(ins.type) ||
			    mir_call_has_f80_arg(fn, ins) ||
			    mir_call_stack_arg_bytes(program_, fn, ins) == 0)
				continue;
				bool saw_reference_index_stack_arg = false;
				for (size_t a = 0; a < ins.args.size(); ++a) {
					if (mir_call_arg_register(program_, fn, ins, a).empty() &&
					    ins.args[a].kind == lowir2cy86::ValueKind::Temp) {
						const string& arg_name = ins.args[a].text;
						const bool reference_arg =
						    temp_origin_is_reference_param(fn, arg_name);
						map<string, const lowir2cy86::Instruction*>::const_iterator dit =
						    definitions_.find(arg_name);
						const bool call_result_arg =
						    dit != definitions_.end() &&
						    dit->second->kind == lowir2cy86::InstrKind::Call;
						if (mir_call_stack_arg_offset(program_, fn, ins, a) == 0 &&
						    !reference_arg && !call_result_arg)
							continue;
						const bool reference_index_arg =
						    dit != definitions_.end() &&
						    dit->second->kind == lowir2cy86::InstrKind::Index &&
						    reference_arg;
						if (reference_index_arg) {
							stack_call_index_args_.insert(arg_name);
							saw_reference_index_stack_arg = true;
						} else {
							stack_call_arg_temps_.insert(arg_name);
							frame_temps_.insert(arg_name);
							if (call_result_arg) {
								stack_call_result_arg_temps_.insert(arg_name);
								frame_temps_.erase(arg_name);
								stack_call_arg_temps_.erase(arg_name);
							}
							if (reference_arg)
								collect_stack_call_load_frame_chain(
								    fn, arg_name,
								    saw_reference_index_stack_arg);
						}
					}
					if (!mir_call_arg_register(program_, fn, ins, a).empty() &&
					    a >= first_preserved_stack_call_reg_arg(ins) &&
					    ins.args[a].kind == lowir2cy86::ValueKind::Temp &&
					    !mir_is_xmm_type(mir_call_param_type(program_, fn, ins, a)) &&
					    !mir_call_arg_needs_address(program_, ins, a))
						live_across_calls_.insert(ins.args[a].text);
				}
				if (ins.has_dest && !lowir2cy86::is_void_type(ins.type)) {
					stack_call_result_temps_.insert(ins.dest);
					frame_temps_.insert(ins.dest);
				}
			} }

	size_t MirDumper::first_preserved_stack_call_reg_arg(
	    const lowir2cy86::Instruction& ins) const {
		return mir_call_arg_needs_address(program_, ins, 0) ? 1 : 2;
	}

void MirDumper::analyze_reference_store_dest_frame_temps(const lowir2cy86::Function& fn) {
	if (fn.blocks.size() <= 1 || fn.blocks.empty())
		return;
	const lowir2cy86::Block& entry = fn.blocks[0];
	for (size_t i = 0; i < entry.instructions.size(); ++i) {
		const lowir2cy86::Instruction& ins = entry.instructions[i];
		if (ins.kind == lowir2cy86::InstrKind::Branch ||
		    ins.kind == lowir2cy86::InstrKind::Jump ||
		    ins.kind == lowir2cy86::InstrKind::Switch ||
		    ins.kind == lowir2cy86::InstrKind::Return)
			break;
		if (ins.kind != lowir2cy86::InstrKind::Store ||
		    ins.b.kind != lowir2cy86::ValueKind::Temp)
			continue;
		const string dst_param = temp_origin_param(fn, ins.b.text);
		const int dst_index = param_index(fn, dst_param);
		if (dst_index < 0 || !param_pass_is(fn, dst_index, "reference"))
			continue;
		reference_store_dest_params_.insert(dst_param);
		if (ins.a.kind == lowir2cy86::ValueKind::Temp) {
			reference_store_source_temps_.insert(ins.a.text);
			map<string, const lowir2cy86::Instruction*>::const_iterator dit =
			    definitions_.find(ins.a.text);
			if (dit != definitions_.end() &&
			    dit->second->kind == lowir2cy86::InstrKind::Cmp &&
			    dit->second->a.kind == lowir2cy86::ValueKind::Temp)
				reference_store_cmp_sources_.insert(dit->second->a.text);
			const string src_param = temp_origin_param(fn, ins.a.text);
			if (param_index(fn, src_param) >= 0)
				reference_store_source_params_.insert(src_param);
		}
		collect_reference_address_frame_chain(fn, ins.b.text);
	}
}

void MirDumper::analyze_param_store_dests(const lowir2cy86::Function& fn) {
	for (size_t b = 0; b < fn.blocks.size(); ++b)
		for (size_t i = 0; i < fn.blocks[b].instructions.size(); ++i) {
			const lowir2cy86::Instruction& ins = fn.blocks[b].instructions[i];
			if (ins.kind != lowir2cy86::InstrKind::Store)
				continue;
			lowir2cy86::Value dst = promoted_store_dest(ins.b);
			if (dst.kind == lowir2cy86::ValueKind::Temp &&
			    param_index(fn, dst.text) >= 0 &&
			    lowir2cy86::is_ptr_type(mir_lookup_type(fn, dst)))
				param_store_dests_.insert(dst.text);
		}
}

void MirDumper::analyze_param_base_loads(const lowir2cy86::Function& fn) {
	for (size_t b = 0; b < fn.blocks.size(); ++b)
		for (size_t i = 0; i < fn.blocks[b].instructions.size(); ++i) {
			const lowir2cy86::Instruction& ins = fn.blocks[b].instructions[i];
			if (ins.kind != lowir2cy86::InstrKind::Load ||
			    ins.a.kind != lowir2cy86::ValueKind::Temp)
				continue;
			const string param = param_for_projected_load_base(fn, ins.a.text);
			if (param.empty())
				continue;
			if (load_result_used_as_index_base(fn, ins.dest)) {
				param_base_loads_.insert(ins.dest);
				param_base_load_params_[ins.dest] = param;
			}
		}
}

void MirDumper::analyze_sret_frame_temps(const lowir2cy86::Function& fn) {
	if (fn.params.empty() ||
	    fn.params[0].name != "%ret" ||
	    !param_pass_is(fn, 0, "indirect_result") ||
	    !function_has_call_or_multiple_blocks(fn))
		return;
	for (size_t b = 0; b < fn.blocks.size(); ++b)
		for (size_t i = 0; i < fn.blocks[b].instructions.size(); ++i) {
			const lowir2cy86::Instruction& ins = fn.blocks[b].instructions[i];
			if (ins.kind == lowir2cy86::InstrKind::Store &&
			    ins.b.kind == lowir2cy86::ValueKind::Temp &&
			    lowir2cy86::is_integer_type(ins.type) &&
			    ins.type.bits == 64 &&
			    index_chain_root_param(ins.b.text) == "%ret")
				collect_sret_frame_chain(ins.b.text);
			if (ins.kind == lowir2cy86::InstrKind::Load &&
			    ins.has_dest &&
			    lowir2cy86::is_ptr_type(ins.type) &&
			    ins.a.kind == lowir2cy86::ValueKind::Temp) {
				const string param =
				    param_for_projected_load_base(fn, ins.a.text);
				const int index = param.empty() ? -1 : param_index(fn, param);
				if (index >= 0 && param_pass_is(fn, index, "reference")) {
					sret_frame_temps_.insert(ins.dest);
					frame_temps_.insert(ins.dest);
				}
			}
		}
}

string MirDumper::index_chain_root_param(const string& name) const {
	map<string, const lowir2cy86::Instruction*>::const_iterator it =
	    definitions_.find(name);
	if (it == definitions_.end())
		return "";
	const lowir2cy86::Instruction& ins = *it->second;
	if ((ins.kind == lowir2cy86::InstrKind::Index ||
	     (ins.kind == lowir2cy86::InstrKind::Unary &&
	      ins.op == "decay")) &&
	    ins.a.kind == lowir2cy86::ValueKind::Temp) {
		if (param_index_for_name(ins.a.text) >= 0)
			return ins.a.text;
		return index_chain_root_param(ins.a.text);
	}
	return "";
}

void MirDumper::collect_sret_frame_chain(const string& name) {
	map<string, const lowir2cy86::Instruction*>::const_iterator it =
	    definitions_.find(name);
	if (it == definitions_.end())
		return;
	const lowir2cy86::Instruction& ins = *it->second;
	if (ins.kind != lowir2cy86::InstrKind::Index &&
	    !(ins.kind == lowir2cy86::InstrKind::Unary &&
	      ins.op == "decay"))
		return;
	sret_frame_temps_.insert(name);
	frame_temps_.insert(name);
	if (ins.a.kind == lowir2cy86::ValueKind::Temp &&
	    param_index_for_name(ins.a.text) < 0)
		collect_sret_frame_chain(ins.a.text);
}

string MirDumper::param_for_projected_load_base(const lowir2cy86::Function& fn,
                                     const string& temp) const {
	lowir2cy86::Value src;
	src.kind = lowir2cy86::ValueKind::Temp;
	src.text = temp;
	src = promoted_store_dest(src);
	if (src.kind == lowir2cy86::ValueKind::Temp &&
	    param_index(fn, src.text) >= 0 &&
	    lowir2cy86::is_ptr_type(mir_lookup_type(fn, src)))
		return src.text;
	map<string, const lowir2cy86::Instruction*>::const_iterator it =
	    definitions_.find(temp);
	if (it == definitions_.end() ||
	    it->second->kind != lowir2cy86::InstrKind::Index ||
	    it->second->a.kind != lowir2cy86::ValueKind::Temp)
		return "";
	return param_for_projected_load_base(fn, it->second->a.text);
}

bool MirDumper::load_result_used_as_index_base(const lowir2cy86::Function& fn,
                                    const string& name) const {
	for (size_t bb = 0; bb < fn.blocks.size(); ++bb)
		for (size_t ii = 0; ii < fn.blocks[bb].instructions.size(); ++ii) {
			const lowir2cy86::Instruction& use = fn.blocks[bb].instructions[ii];
			if (use.kind == lowir2cy86::InstrKind::Index &&
			    use.a.kind == lowir2cy86::ValueKind::Temp &&
			    use.a.text == name)
				return true;
		}
	return false;
}

void MirDumper::analyze_promoted_addr_params(const lowir2cy86::Function& fn) {
	for (size_t b = 0; b < fn.blocks.size(); ++b)
		for (size_t i = 0; i < fn.blocks[b].instructions.size(); ++i) {
			const lowir2cy86::Instruction& ins = fn.blocks[b].instructions[i];
			if (ins.kind != lowir2cy86::InstrKind::Addr ||
			    ins.a.kind != lowir2cy86::ValueKind::Slot)
				continue;
			map<string, string>::const_iterator pit =
			    promoted_slot_params_.find(ins.a.text);
			if (pit != promoted_slot_params_.end())
				promoted_addr_params_[ins.dest] = pit->second;
		} }

void MirDumper::analyze_object_result_field_params(const lowir2cy86::Function& fn) {
	if (entry_param_regs_.find("%ret") == entry_param_regs_.end())
		return;
	for (size_t b = 0; b < fn.blocks.size(); ++b)
		for (size_t i = 0; i < fn.blocks[b].instructions.size(); ++i) {
			const lowir2cy86::Instruction& ins = fn.blocks[b].instructions[i];
			if (ins.kind != lowir2cy86::InstrKind::Store ||
			    ins.a.kind != lowir2cy86::ValueKind::Temp ||
			    param_index(fn, ins.a.text) < 0 ||
			    ins.b.kind != lowir2cy86::ValueKind::Temp)
				continue;
			map<string, const lowir2cy86::Instruction*>::const_iterator dit =
			    definitions_.find(ins.b.text);
			if (dit != definitions_.end() &&
			    dit->second->kind == lowir2cy86::InstrKind::Index &&
			    dit->second->a.kind == lowir2cy86::ValueKind::Temp &&
			    dit->second->a.text == "%ret")
				entry_param_regs_[ins.a.text] = "r9";
		} }

bool MirDumper::mixed_gpr_xmm_abi_shape(const lowir2cy86::Function& fn) const {
	return fn.params.size() == 4 &&
	       !lowir2cy86::is_float_type(fn.params[0].type) &&
	       mir_is_xmm_type(fn.params[1].type) &&
	       !lowir2cy86::is_float_type(fn.params[2].type) &&
	       mir_is_xmm_type(fn.params[3].type);
}

void MirDumper::analyze_mixed_gpr_xmm_abi(const lowir2cy86::Function& fn) {
	if (!mixed_gpr_xmm_abi_shape(fn))
		return;
	entry_param_regs_[fn.params[2].name] = "rbx";
	size_t float_convert = 0;
	for (size_t b = 0; b < fn.blocks.size(); ++b)
		for (size_t i = 0; i < fn.blocks[b].instructions.size(); ++i) {
			const lowir2cy86::Instruction& ins = fn.blocks[b].instructions[i];
			if (ins.kind != lowir2cy86::InstrKind::Convert ||
			    ins.op != "fptosi" ||
			    ins.a.kind != lowir2cy86::ValueKind::Temp ||
			    !mir_is_xmm_type(ins.src_type))
				continue;
			const int p = param_index(fn, ins.a.text);
			if (p < 0)
				continue;
			mixed_convert_regs_[ins.dest] =
			    float_convert == 0 ? "r9" : "r12";
			++float_convert;
		}
}

string MirDumper::preserve_reg(size_t index) const {
	static const char* const regs[] = {"rbx", "r12", "r13", "r14", "r15"};
	return regs[index % (sizeof(regs) / sizeof(regs[0]))]; }

bool MirDumper::param_pass_is(const lowir2cy86::Function& fn,
                   size_t index, const string& pass) const {
	return index < fn.params.size() &&
	       lowir2cy86::metadata_value(fn.params[index].metadata, "pass") == pass; }

bool MirDumper::param_is_index_base(const lowir2cy86::Function& fn,
                         const string& name) const {
	for (size_t i = 0; i < fn.blocks.size(); ++i)
		for (size_t j = 0; j < fn.blocks[i].instructions.size(); ++j) {
			const lowir2cy86::Instruction& ins = fn.blocks[i].instructions[j];
			if (ins.kind == lowir2cy86::InstrKind::Index &&
			    ins.a.kind == lowir2cy86::ValueKind::Temp &&
			    ins.a.text == name)
				return true;
		}
	return false; }

void MirDumper::analyze_live_across_calls(const lowir2cy86::Function& fn) {
	map<string, int> def_pos;
	map<string, int> last_use;
	vector<int> calls;
	for (size_t i = 0; i < fn.params.size(); ++i)
		def_pos[fn.params[i].name] = -1;
	int pos = 0;
	for (size_t i = 0; i < fn.blocks.size(); ++i)
		for (size_t j = 0; j < fn.blocks[i].instructions.size(); ++j, ++pos) {
			const lowir2cy86::Instruction& ins = fn.blocks[i].instructions[j];
			note_live_use(ins.a, pos, last_use);
			note_live_use(ins.b, pos, last_use);
			note_live_use(ins.c, pos, last_use);
			for (size_t a = 0; a < ins.args.size(); ++a)
				note_live_use(ins.args[a], pos, last_use);
			for (size_t s = 0; s < ins.switch_cases.size(); ++s)
				note_live_use(ins.switch_cases[s].value, pos, last_use);
			if (ins.kind == lowir2cy86::InstrKind::Branch &&
			    ins.a.kind == lowir2cy86::ValueKind::Temp) {
				map<string, const lowir2cy86::Instruction*>::const_iterator it =
				    definitions_.find(ins.a.text);
				if (it != definitions_.end() &&
				    it->second->kind == lowir2cy86::InstrKind::Cmp &&
				    use_counts_[ins.a.text] == 1) {
					note_live_use(it->second->a, pos, last_use);
					note_live_use(it->second->b, pos, last_use);
					if (!calls.empty() &&
					    !lowir2cy86::is_float_type(it->second->type) &&
					    branch_cmp_needs_post_call_preserve(*it->second))
						folded_branch_call_preserve_ = true;
				}
			}
			if (ins.kind == lowir2cy86::InstrKind::Call)
				calls.push_back(pos);
			if (ins.has_dest)
				def_pos[ins.dest] = pos;
		}
	for (size_t c = 0; c < calls.size(); ++c)
		for (map<string, int>::const_iterator it = last_use.begin();
		     it != last_use.end(); ++it) {
			map<string, int>::const_iterator dit = def_pos.find(it->first);
			if (dit != def_pos.end() && dit->second < calls[c] && calls[c] < it->second)
				live_across_calls_.insert(it->first);
		} }

bool MirDumper::branch_cmp_needs_post_call_preserve(
    const lowir2cy86::Instruction& cmp) const {
	return branch_cmp_value_needs_post_call_preserve(cmp.a) ||
	       branch_cmp_value_needs_post_call_preserve(cmp.b);
}

bool MirDumper::branch_cmp_value_needs_post_call_preserve(
    const lowir2cy86::Value& value) const {
	if (value.kind != lowir2cy86::ValueKind::Temp)
		return false;
	map<string, const lowir2cy86::Instruction*>::const_iterator it =
	    definitions_.find(value.text);
	if (it == definitions_.end())
		return true;
	if (address_chain_root_is_stable(value.text))
		return false;
	if (it->second->kind == lowir2cy86::InstrKind::Call)
		return false;
	if (it->second->kind != lowir2cy86::InstrKind::Load)
		return true;
	if (it->second->a.kind == lowir2cy86::ValueKind::Temp &&
	    address_chain_root_is_stable(it->second->a.text))
		return false;
	return it->second->a.kind != lowir2cy86::ValueKind::Global &&
	       it->second->a.kind != lowir2cy86::ValueKind::Slot;
}

bool MirDumper::address_chain_root_is_stable(const string& name) const {
	set<string> seen;
	return address_chain_root_is_stable(name, seen);
}

bool MirDumper::address_chain_root_is_stable(const string& name,
                                  set<string>& seen) const {
	if (!seen.insert(name).second)
		return false;
	map<string, const lowir2cy86::Instruction*>::const_iterator it =
	    definitions_.find(name);
	if (it == definitions_.end())
		return false;
	const lowir2cy86::Instruction& ins = *it->second;
	if (ins.kind == lowir2cy86::InstrKind::Addr)
		return ins.a.kind == lowir2cy86::ValueKind::Slot ||
		       ins.a.kind == lowir2cy86::ValueKind::Global;
	if ((ins.kind == lowir2cy86::InstrKind::Index ||
	     (ins.kind == lowir2cy86::InstrKind::Unary &&
	      ins.op == "decay") ||
	     ins.kind == lowir2cy86::InstrKind::Copy) &&
	    ins.a.kind == lowir2cy86::ValueKind::Temp)
		return address_chain_root_is_stable(ins.a.text, seen);
	return false;
}

void MirDumper::note_live_use(const lowir2cy86::Value& value, int pos,
                   map<string, int>& last_use) {
	if (value.kind != lowir2cy86::ValueKind::Temp) return;
	last_use[value.text] = pos;
	map<string, string>::const_iterator it =
	    promoted_loads_.find(value.text);
	if (it != promoted_loads_.end())
		last_use[it->second] = pos;
	map<string, const lowir2cy86::Instruction*>::const_iterator dit =
	    definitions_.find(value.text);
	if (dit != definitions_.end() &&
	    dit->second->kind == lowir2cy86::InstrKind::Index &&
	    dit->second->a.kind == lowir2cy86::ValueKind::Temp &&
	    param_index_for_name(dit->second->a.text) >= 0)
		last_use[dit->second->a.text] = pos;
}

int MirDumper::param_index_for_name(const string& name) const {
	return current_param_index_.find(name) == current_param_index_.end()
	           ? -1
	           : current_param_index_.find(name)->second;
}

}  // namespace lowir2native
