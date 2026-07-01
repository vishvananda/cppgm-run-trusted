#include "lowir2native_mir_dumper.h"

namespace lowir2native {

bool MirDumper::sret_widened_store_source(const lowir2cy86::Function& fn,
                               const string& name) const {
	for (size_t b = 0; b < fn.blocks.size(); ++b)
		for (size_t i = 0; i < fn.blocks[b].instructions.size(); ++i) {
			const lowir2cy86::Instruction& ins = fn.blocks[b].instructions[i];
			if (ins.kind != lowir2cy86::InstrKind::Store ||
			    ins.a.kind != lowir2cy86::ValueKind::Temp ||
			    ins.a.text != name)
				continue;
			const lowir2cy86::Type src = mir_lookup_type(fn, ins.a);
			return lowir2cy86::is_integer_type(src) &&
			       lowir2cy86::is_integer_type(ins.type) &&
			       src.bits < ins.type.bits;
		}
	return false;
}

void MirDumper::dump_instruction(const lowir2cy86::Function& fn,
                      const lowir2cy86::Instruction& ins) {
		if (mir_skip_promoted_slot_instruction(ins, omitted_slots_, promoted_slot_params_)) {
			if (materialize_reference_store_source_promoted_load(fn, ins, true)) {
				consume_instruction_uses(ins);
				return;
			}
			if (materialize_sret_widened_promoted_load(fn, ins, true)) {
				consume_instruction_uses(ins);
				return;
			}
			if (ins.kind == lowir2cy86::InstrKind::Load &&
			    promoted_load_feeds_direct_call_index(fn, ins.dest)) {
				lowir2cy86::Value param;
				param.kind = lowir2cy86::ValueKind::Temp;
				param.text = promoted_loads_.find(ins.dest)->second;
				out_ << "    mov r8, " << value_reg(fn, param) << "\n";
			}
			consume_instruction_uses(ins);
			return;
		}
	switch (ins.kind) {
	case lowir2cy86::InstrKind::Const:
		dump_const(fn, ins);
		break;
	case lowir2cy86::InstrKind::Copy:
		dump_copy(fn, ins);
		break;
		case lowir2cy86::InstrKind::Addr: {
			const lowir2cy86::Instruction* store =
			    optimized_literal_store_for_addr(ins.dest);
			if (store != nullptr) {
				if (!past_call_in_block_) {
					out_ << "    mov rax, " << store->a.text
					     << debug_suffix(store->debug) << "\n";
					dump_addr(fn, ins, store->debug);
					preemitted_store_literal_addrs_.insert(ins.dest);
				}
				break;
			}
			if (optimized_addr_temp_feeds_load(ins.dest))
				break;
			if (is_dead_dest(ins.dest) ||
			    global_store_addrs_.find(ins.dest) != global_store_addrs_.end() ||
			    store_source_addrs_.find(ins.dest) != store_source_addrs_.end() ||
			    inline_call_arg_addrs_.find(ins.dest) != inline_call_arg_addrs_.end() ||
		    inline_copy_addrs_.find(ins.dest) != inline_copy_addrs_.end() ||
		    promoted_addr_params_.find(ins.dest) !=
		        promoted_addr_params_.end() ||
		    direct_object_copy_addrs_.find(ins.dest) !=
		        direct_object_copy_addrs_.end() ||
		    inline_zero_addrs_.find(ins.dest) != inline_zero_addrs_.end())
			break;
		if (inline_atomic_expected_addrs_.find(ins.dest) !=
		    inline_atomic_expected_addrs_.end())
			break;
		dump_addr(fn, ins, ins.debug);
		break; }
	case lowir2cy86::InstrKind::Load:
		if (direct_param_copy_loads_.find(ins.dest) !=
		    direct_param_copy_loads_.end())
			break;
		if (direct_branch_loads_.find(ins.dest) !=
		    direct_branch_loads_.end())
			break;
		dump_load(fn, ins);
		break;
	case lowir2cy86::InstrKind::AtomicLoad:
		dump_load(fn, ins);
		break;
	case lowir2cy86::InstrKind::Store:
		dump_store(fn, ins);
		break;
	case lowir2cy86::InstrKind::AtomicStore:
		dump_atomic_store(fn, ins);
		break;
	case lowir2cy86::InstrKind::Index:
		if (stack_call_index_args_.find(ins.dest) !=
		    stack_call_index_args_.end())
			break;
		dump_index(fn, ins);
		break;
	case lowir2cy86::InstrKind::CopyObj:
		if (ins.b.kind == lowir2cy86::ValueKind::Temp &&
		    promoted_addr_params_.find(ins.b.text) !=
		        promoted_addr_params_.end() &&
		    promoted_addr_params_.find(ins.b.text)->second != "%ret")
			break;
		dump_copyobj(fn, ins);
		break;
	case lowir2cy86::InstrKind::ZeroInit:
		dump_zeroinit(fn, ins);
		break;
	case lowir2cy86::InstrKind::Unary:
		if (direct_branch_not_.find(ins.dest) != direct_branch_not_.end())
			break;
		dump_unary(fn, ins);
		break;
	case lowir2cy86::InstrKind::Binary:
	case lowir2cy86::InstrKind::Cmp:
	case lowir2cy86::InstrKind::Convert:
		if (ins.kind != lowir2cy86::InstrKind::Cmp ||
		    direct_branch_cmp_.find(ins.dest) == direct_branch_cmp_.end())
			dump_scalar(fn, ins);
		break;
	case lowir2cy86::InstrKind::Call:
		dump_call(fn, ins);
		past_call_in_block_ = true;
		if (mir_call_stack_arg_bytes(program_, fn, ins) != 0)
			past_stack_call_in_block_ = true;
		break;
	case lowir2cy86::InstrKind::AtomicExchange:
	case lowir2cy86::InstrKind::AtomicCompareExchange:
	case lowir2cy86::InstrKind::AtomicAddFetch:
		dump_atomic(fn, ins);
		break;
	case lowir2cy86::InstrKind::AtomicThreadFence:
		out_ << "    mfence\n";
		break;
	case lowir2cy86::InstrKind::AtomicSignalFence:
		break;
	case lowir2cy86::InstrKind::Jump:
		if (optimization_level_ >= 1 && ins.target == current_fallthrough_block_)
			break;
		out_ << "    jmp " << ins.target << "\n";
		break;
	case lowir2cy86::InstrKind::Branch:
		dump_branch(fn, ins);
		break;
	case lowir2cy86::InstrKind::Switch:
		dump_switch(fn, ins);
		break;
	case lowir2cy86::InstrKind::Return:
		dump_return(fn, ins);
		break;
	default:
		throw runtime_error("unsupported LowIR instruction for machine IR");
	}
		consume_instruction_uses(ins); }

void MirDumper::simulate_instruction(const lowir2cy86::Function& fn,
                          const lowir2cy86::Instruction& ins) {
		if (mir_skip_promoted_slot_instruction(ins, omitted_slots_, promoted_slot_params_)) {
			if (materialize_reference_store_source_promoted_load(fn, ins, false)) {
				consume_instruction_uses(ins);
				return;
			}
			if (materialize_sret_widened_promoted_load(fn, ins, false)) {
				consume_instruction_uses(ins);
				return;
			}
			consume_instruction_uses(ins);
			return;
		}
		if (simulate_f80_instruction(fn, ins)) {
			consume_instruction_uses(ins);
			return;
		}
	switch (ins.kind) {
	case lowir2cy86::InstrKind::Const:
		if (lowir2cy86::is_float_type(ins.type) &&
		    !lowir2cy86::is_f80_type(ins.type))
			xmm_reg(ins.dest);
		else
			remember_const_dest(ins.dest, const_dest_reg(ins));
		break;
		case lowir2cy86::InstrKind::Copy:
			if (lowir2cy86::is_float_type(ins.type) &&
			    !lowir2cy86::is_f80_type(ins.type)) {
				float_value(fn, ins.a);
				xmm_reg(ins.dest); } else {
				if (large_frame_pointer_literal_copy(ins))
					remember_fixed_temp_reg(ins.dest, "r8");
				else
				if (copy_can_forward(fn, ins))
					remember_fixed_temp_reg(ins.dest, value_reg(fn, ins.a));
				else if (copy_can_narrow_in_place(fn, ins))
					remember_fixed_temp_reg(ins.dest, value_reg(fn, ins.a));
				else {
				temp_reg(ins.dest);
				value_reg(fn, ins.a);
			}
		}
		break;
	case lowir2cy86::InstrKind::Addr:
		if (is_dead_dest(ins.dest)) {
			if (ins.a.kind == lowir2cy86::ValueKind::Slot)
				used_preserves_.insert("rbx");
			break;
		}
		if (inline_call_arg_addrs_.find(ins.dest) != inline_call_arg_addrs_.end())
			break;
		if (store_source_addrs_.find(ins.dest) != store_source_addrs_.end())
			break;
		if (inline_copy_addrs_.find(ins.dest) != inline_copy_addrs_.end())
			break;
		if (promoted_addr_params_.find(ins.dest) !=
		    promoted_addr_params_.end())
			break;
		if (direct_object_copy_addrs_.find(ins.dest) !=
		    direct_object_copy_addrs_.end())
			break;
		if (inline_zero_addrs_.find(ins.dest) != inline_zero_addrs_.end())
			break;
		if (inline_atomic_expected_addrs_.find(ins.dest) !=
		    inline_atomic_expected_addrs_.end())
			break;
		if (direct_branch_addr_regs_.find(ins.dest) !=
		    direct_branch_addr_regs_.end())
			remember_fixed_temp_reg(
			    ins.dest, direct_branch_addr_regs_.find(ins.dest)->second);
		else if (!fixed_addr_dest_reg(ins).empty())
			remember_fixed_temp_reg(ins.dest, fixed_addr_dest_reg(ins));
		else if (addr_prefers_rcx(ins))
			remember_fixed_temp_reg(ins.dest, "rcx");
		else
			temp_reg(ins.dest);
		value_reg(fn, ins.a);
		break;
	case lowir2cy86::InstrKind::Load:
	case lowir2cy86::InstrKind::AtomicLoad: {
		map<string, string>::const_iterator ebit =
		    entry_branch_param_loads_.find(ins.dest);
		if (ebit != entry_branch_param_loads_.end()) {
			map<string, string>::const_iterator eit =
			    entry_param_regs_.find(ebit->second);
			if (eit != entry_param_regs_.end()) {
				remember_fixed_temp_reg(ins.dest, eit->second);
				break;
			}
		}
		if (direct_param_copy_loads_.find(ins.dest) !=
		    direct_param_copy_loads_.end())
			break;
		if (direct_branch_loads_.find(ins.dest) !=
		    direct_branch_loads_.end())
			break;
		if (ins.a.kind == lowir2cy86::ValueKind::Temp &&
		    direct_object_copy_addrs_.find(ins.a.text) !=
		        direct_object_copy_addrs_.end()) {
			const lowir2cy86::Instruction& addr = *definitions_[ins.a.text];
			const string dst = load_dest_reg(fn, ins);
			value_reg(fn, addr.a);
			remember_load_dest(ins.dest, dst);
			break;
		}
		if (ins.a.kind == lowir2cy86::ValueKind::Temp &&
		    promoted_addr_params_.find(ins.a.text) !=
		        promoted_addr_params_.end()) {
			const string dst = load_dest_reg(fn, ins);
			lowir2cy86::Value param;
			param.kind = lowir2cy86::ValueKind::Temp;
			param.text = promoted_addr_params_[ins.a.text];
			param_slot_mem(fn, param);
			remember_load_dest(ins.dest, dst);
			break;
		}
		lowir2cy86::Value src_value = promoted_store_dest(ins.a);
		if (src_value.kind == lowir2cy86::ValueKind::Temp &&
		    param_index(fn, src_value.text) >= 0 &&
		    lowir2cy86::is_ptr_type(mir_lookup_type(fn, src_value)) &&
		    function_has_call_or_multiple_blocks(fn))
			used_preserves_.insert("rbx");
		const string dst = load_dest_reg(fn, ins);
		load_source(fn, ins.a);
		remember_load_dest(ins.dest, dst);
		break;
	}
	case lowir2cy86::InstrKind::Store:
		if (ins.a.kind == lowir2cy86::ValueKind::Temp &&
		    global_store_addrs_.find(ins.a.text) != global_store_addrs_.end()) {
			lowir2cy86::Value dst_value = promoted_store_dest(ins.b);
			if (dst_value.kind == lowir2cy86::ValueKind::Temp)
				used_preserves_.insert("rbx");
			value_reg(fn, dst_value);
			break;
		}
		if (ins.b.kind == lowir2cy86::ValueKind::Global &&
		    is_thread_local_global(ins.b.text)) {
			value_reg(fn, ins.a);
			if (ins.a.kind == lowir2cy86::ValueKind::Temp &&
			    tls_store_sources_.find(ins.a.text) !=
			        tls_store_sources_.end())
				used_preserves_.insert("r12");
			break;
		}
		value_reg(fn, ins.a);
		if (ins.b.kind == lowir2cy86::ValueKind::Temp &&
		    inline_copy_addrs_.find(ins.b.text) != inline_copy_addrs_.end()) {
			const lowir2cy86::Instruction& addr = *definitions_[ins.b.text];
			value_reg(fn, addr.a);
		} else
			value_reg(fn, ins.b);
		remember_store_literal(fn, ins.a);
		break;
	case lowir2cy86::InstrKind::AtomicStore:
		remember_store_reload(fn, ins.b, ins.a);
		break;
	case lowir2cy86::InstrKind::Index: {
		if (stack_call_index_args_.find(ins.dest) !=
		    stack_call_index_args_.end())
			break;
		const bool saved_force_entry_param_reg =
		    force_entry_param_reg_;
		if (call_arg_index_regs_.find(ins.dest) !=
		    call_arg_index_regs_.end())
			force_entry_param_reg_ = true;
		const string dst = index_dest_reg(fn, ins);
		value_reg(fn, ins.a);
		if (ins.b.kind != lowir2cy86::ValueKind::Literal)
			value_reg(fn, ins.b);
		if (temp_used_only_as_store_dest(fn, ins.dest))
			remember_fixed_temp_reg(ins.dest, dst);
		else if (dst == value_reg(fn, ins.a))
			remember_fixed_temp_reg(ins.dest, dst);
		else
			remember_temp_reg(ins.dest, dst);
		force_entry_param_reg_ = saved_force_entry_param_reg;
		break;
	}
	case lowir2cy86::InstrKind::CopyObj:
		if (ins.b.kind == lowir2cy86::ValueKind::Temp &&
		    promoted_addr_params_.find(ins.b.text) !=
		        promoted_addr_params_.end() &&
		    promoted_addr_params_.find(ins.b.text)->second != "%ret")
			break;
		if (copyobj_uses_direct_param_loads(ins))
			break;
		if (copyobj_source_is_direct_object(fn, ins)) {
			simulate_direct_object_copy(fn, ins);
			break;
		}
		value_reg(fn, ins.b);
		value_reg(fn, ins.a);
		remember_copied_object_load(fn, ins);
		break;
	case lowir2cy86::InstrKind::ZeroInit:
		value_reg(fn, ins.a);
		break;
	case lowir2cy86::InstrKind::Unary:
		if (direct_branch_not_.find(ins.dest) != direct_branch_not_.end()) {
			value_reg(fn, ins.a);
			break;
		}
		if (is_last_use(ins.a)) {
			const string src = value_reg(fn, ins.a);
			remember_fixed_temp_reg(ins.dest, src);
		} else
			temp_reg(ins.dest);
		value_reg(fn, ins.a);
		break;
	case lowir2cy86::InstrKind::Binary:
		simulate_binary(fn, ins);
		break;
	case lowir2cy86::InstrKind::Cmp:
		if (direct_branch_cmp_.find(ins.dest) == direct_branch_cmp_.end())
			simulate_cmp(fn, ins);
		break;
	case lowir2cy86::InstrKind::Convert: {
		const string dst = convert_dest(fn, ins);
		convert_source(fn, ins);
		remember_convert_dest(ins, dst);
		break;
	}
	case lowir2cy86::InstrKind::Call:
		simulate_call(fn, ins);
		past_call_in_block_ = true;
		if (mir_call_stack_arg_bytes(program_, fn, ins) != 0)
			past_stack_call_in_block_ = true;
		break;
	case lowir2cy86::InstrKind::AtomicExchange:
	case lowir2cy86::InstrKind::AtomicCompareExchange:
	case lowir2cy86::InstrKind::AtomicAddFetch:
		simulate_atomic(fn, ins);
		break;
	case lowir2cy86::InstrKind::AtomicThreadFence:
	case lowir2cy86::InstrKind::AtomicSignalFence:
	case lowir2cy86::InstrKind::Jump:
		break;
	case lowir2cy86::InstrKind::Branch:
		if (ins.a.kind == lowir2cy86::ValueKind::Temp &&
		    direct_branch_cmp_.find(ins.a.text) != direct_branch_cmp_.end()) {
			const lowir2cy86::Instruction& cmp = *definitions_[ins.a.text];
			value_reg(fn, cmp.a);
			if (cmp.b.kind != lowir2cy86::ValueKind::Literal)
				value_reg(fn, cmp.b); } else if (ins.a.kind == lowir2cy86::ValueKind::Temp &&
		    direct_branch_not_.find(ins.a.text) != direct_branch_not_.end()) {
			const lowir2cy86::Instruction& un = *definitions_[ins.a.text];
			value_reg(fn, un.a); } else
			value_reg(fn, ins.a);
		break;
	case lowir2cy86::InstrKind::Switch:
		value_reg(fn, ins.a);
		for (size_t i = 0; i < ins.switch_cases.size(); ++i)
			value_reg(fn, ins.switch_cases[i].value);
		break;
	case lowir2cy86::InstrKind::Return:
		value_reg(fn, ins.a);
		break;
	default:
		throw runtime_error("unsupported LowIR instruction for machine IR");
	}
		consume_instruction_uses(ins); }

bool MirDumper::simulate_f80_instruction(const lowir2cy86::Function& fn,
                              const lowir2cy86::Instruction& ins) {
	if (ins.kind == lowir2cy86::InstrKind::Const ||
	    ins.kind == lowir2cy86::InstrKind::Load ||
	    ins.kind == lowir2cy86::InstrKind::Binary ||
	    ins.kind == lowir2cy86::InstrKind::Call)
		return lowir2cy86::is_f80_type(ins.type) ||
		       (ins.kind == lowir2cy86::InstrKind::Call &&
		        mir_call_has_f80_arg(fn, ins));
	if (ins.kind == lowir2cy86::InstrKind::Cmp &&
	    lowir2cy86::is_f80_type(ins.type)) {
		remember_temp_reg(ins.dest, "rax");
		return true;
	} return false; }

void MirDumper::consume_instruction_uses(const lowir2cy86::Instruction& ins) {
	consume_value(ins.a);
	consume_value(ins.b);
	consume_value(ins.c);
	for (size_t i = 0; i < ins.args.size(); ++i)
		consume_value(ins.args[i]);
	for (size_t i = 0; i < ins.switch_cases.size(); ++i)
		consume_value(ins.switch_cases[i].value); }

void MirDumper::consume_value(const lowir2cy86::Value& value) {
	if (value.kind != lowir2cy86::ValueKind::Temp) return;
	map<string, int>::iterator it = remaining_uses_.find(value.text);
	if (it != remaining_uses_.end() && it->second > 0)
		--it->second; }

void MirDumper::release_dead_temps() {
	while (!temp_names_.empty() && !temp_is_live(temp_names_.back())) {
		temp_names_.pop_back();
		temp_regs_.pop_back(); } for (map<string, string>::iterator it = fixed_temp_regs_.begin();
	     it != fixed_temp_regs_.end(); ) {
		if (!temp_is_live(it->first))
			fixed_temp_regs_.erase(it++);
		else
			++it;
	} }

bool MirDumper::temp_is_live(const string& name) const {
	map<string, int>::const_iterator it = remaining_uses_.find(name); return it != remaining_uses_.end() && it->second > 0; }

bool MirDumper::reg_is_live(const string& reg) const {
	for (size_t i = 0; i < temp_names_.size(); ++i) {
		if (temp_regs_[i] == reg && temp_is_live(temp_names_[i]))
			return true;
	}
	for (map<string, string>::const_iterator it = fixed_temp_regs_.begin();
	     it != fixed_temp_regs_.end(); ++it) {
		if (it->second == reg && temp_is_live(it->first))
			return true;
	}
	for (map<string, string>::const_iterator it = entry_param_regs_.begin();
	     it != entry_param_regs_.end(); ++it) {
		if (it->second == reg && entry_param_reg_available(it->first) &&
		    temp_is_live(it->first))
			return true;
	}
	for (map<string, string>::const_iterator it = promoted_loads_.begin();
	     it != promoted_loads_.end(); ++it) {
		map<string, string>::const_iterator eit =
		    entry_param_regs_.find(it->second);
		if (eit != entry_param_regs_.end() && eit->second == reg &&
		    temp_is_live(it->first))
			return true;
	}
	return false; }

bool MirDumper::is_last_use(const lowir2cy86::Value& value) const {
	if (value.kind != lowir2cy86::ValueKind::Temp) return false;
	map<string, int>::const_iterator it = remaining_uses_.find(value.text); return it == remaining_uses_.end() || it->second <= 1; }

void MirDumper::simulate_atomic(const lowir2cy86::Function& fn,
                     const lowir2cy86::Instruction& ins) {
	if (ins.has_dest)
		temp_reg(ins.dest);
	if (ins.kind == lowir2cy86::InstrKind::AtomicExchange) {
		const string ptr = value_reg(fn, ins.a);
		const string src = value_reg(fn, ins.b);
		if (can_reuse_written_value(ins.b))
			remember_reload(ptr, src, true); } else if (ins.kind == lowir2cy86::InstrKind::AtomicCompareExchange) {
		const string ptr = value_reg(fn, ins.a);
		simulate_expected_pointer(fn, ins.b);
		const string desired = value_reg(fn, ins.c);
		if (can_reuse_written_value(ins.c))
			remember_reload(ptr, desired, false);
		prefer_r8_stack_load_ = true; } else {
		value_reg(fn, ins.a);
		value_reg(fn, ins.b);
		value_reg(fn, ins.c);
	}
	if (ins.has_dest &&
	    ins.kind != lowir2cy86::InstrKind::AtomicCompareExchange)
		prefer_r8_literal_ = true; }

void MirDumper::simulate_call(const lowir2cy86::Function& fn,
                   const lowir2cy86::Instruction& ins) {
	if (lowir2cy86::is_f80_type(ins.type) || mir_call_has_f80_arg(fn, ins)) return;
	for (size_t i = 0; i < ins.args.size(); ++i) {
		const lowir2cy86::Type type =
		    mir_call_param_type(program_, fn, ins, i);
		const bool saved_force_entry_param_reg =
		    force_entry_param_reg_;
		force_entry_param_reg_ = true;
		if (mir_is_xmm_type(type))
			float_value(fn, ins.args[i]);
		else if (ins.args[i].kind == lowir2cy86::ValueKind::Temp &&
		         inline_call_arg_addrs_.find(ins.args[i].text) != inline_call_arg_addrs_.end()) {
			const lowir2cy86::Instruction& addr = *definitions_[ins.args[i].text];
			value_reg(fn, addr.a);
		} else
			value_reg(fn, ins.args[i]);
		force_entry_param_reg_ = saved_force_entry_param_reg;
	}
	if (ins.a.kind != lowir2cy86::ValueKind::Function)
		value_reg(fn, ins.a);
	if (ins.has_dest && !lowir2cy86::is_void_type(ins.type)) {
		if (lowir2cy86::is_obj_type(ins.type))
			remember_fixed_temp_reg(ins.dest, "rax");
		else if (mir_is_xmm_type(ins.type))
			remember_xmm_reg(ins.dest, "xmm0");
		else if (live_across_calls_.find(ins.dest) != live_across_calls_.end())
			temp_reg(ins.dest);
		else if (call_result_stays_in_rax(ins.dest)) {
			remember_fixed_temp_reg(ins.dest, "rax");
		}
		else
			remember_fixed_temp_reg(ins.dest, call_result_reg(fn, ins));
	} }

void MirDumper::simulate_expected_pointer(const lowir2cy86::Function& fn,
                               const lowir2cy86::Value& value) {
	const lowir2cy86::Instruction* addr = inline_addr_definition(value);
	if (addr != nullptr) {
		if (addr->a.kind == lowir2cy86::ValueKind::Temp)
			value_reg(fn, addr->a);
		return;
	}
	value_reg(fn, value); }

void MirDumper::simulate_binary(const lowir2cy86::Function& fn,
                     const lowir2cy86::Instruction& ins) {
	if (lowir2cy86::is_f80_type(ins.type)) return;
	if (lowir2cy86::is_float_type(ins.type) &&
	    !lowir2cy86::is_f80_type(ins.type)) {
		float_binary_dest(ins);
		float_value(fn, ins.a);
		float_value(fn, ins.b);
		return;
	}
	const string dst = binary_dest_reg(fn, ins);
	value_reg(fn, ins.a);
	if (ins.b.kind != lowir2cy86::ValueKind::Literal &&
	    !(ins.b.kind == lowir2cy86::ValueKind::Temp &&
	      tls_pressure_frame_temps_.find(ins.b.text) !=
	          tls_pressure_frame_temps_.end()))
		value_reg(fn, ins.b);
	if (tls_pressure_frame_temps_.find(ins.dest) !=
	    tls_pressure_frame_temps_.end())
		return;
	remember_temp_reg(ins.dest, dst); }

void MirDumper::simulate_cmp(const lowir2cy86::Function& fn,
                  const lowir2cy86::Instruction& ins) {
	if (lowir2cy86::is_f80_type(ins.type)) {
		if (cmp_result_stays_in_rax(ins.dest))
			remember_fixed_temp_reg(ins.dest, "rax");
		else
			temp_reg(ins.dest);
		return;
	}
	if (lowir2cy86::is_float_type(ins.type)) {
		float_value(fn, ins.a);
		float_value(fn, ins.b);
		if (cmp_result_stays_in_rax(ins.dest))
			remember_fixed_temp_reg(ins.dest, "rax");
		else
			temp_reg(ins.dest);
		return;
	}
	const string dst = cmp_value_dest_reg(fn, ins);
	const string lhs = value_reg(fn, ins.a);
	if (ins.b.kind != lowir2cy86::ValueKind::Literal)
		value_reg(fn, ins.b);
	if (dst == lhs && is_last_use(ins.a))
		remember_fixed_temp_reg(ins.dest, dst);
	else
		remember_temp_reg(ins.dest, dst); }

}  // namespace lowir2native
