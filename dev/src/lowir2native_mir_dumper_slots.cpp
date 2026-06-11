#include "lowir2native_mir_dumper.h"

namespace lowir2native {

void MirDumper::count_uses(const lowir2cy86::Instruction& ins) {
	count_use(ins.a);
	count_use(ins.b);
	count_use(ins.c);
	for (size_t i = 0; i < ins.args.size(); ++i)
		count_use(ins.args[i]);
	for (size_t i = 0; i < ins.switch_cases.size(); ++i)
		count_use(ins.switch_cases[i].value); }

void MirDumper::count_use(const lowir2cy86::Value& value) {
	if (value.kind == lowir2cy86::ValueKind::Temp)
		++use_counts_[value.text]; }

void MirDumper::analyze_slot_param_sources(const lowir2cy86::Function& fn) {
	for (size_t b = 0; b < fn.blocks.size(); ++b)
		for (size_t i = 0; i < fn.blocks[b].instructions.size(); ++i) {
			const lowir2cy86::Instruction& ins = fn.blocks[b].instructions[i];
			if (ins.kind != lowir2cy86::InstrKind::Store ||
			    ins.a.kind != lowir2cy86::ValueKind::Temp ||
			    ins.b.kind != lowir2cy86::ValueKind::Slot)
				continue;
			const int index = param_index(fn, ins.a.text);
			if (index < 0)
				continue;
			map<string, lowir2cy86::Type>::const_iterator sit =
			    fn.slot_types.find(ins.b.text);
			if (sit == fn.slot_types.end() ||
			    sit->second.text != fn.params[index].type.text)
				continue;
			slot_param_sources_[ins.b.text] = ins.a.text;
		}
}

void MirDumper::analyze_entry_branch_param_loads(const lowir2cy86::Function& fn) {
	if (fn.params.empty() ||
	    fn.params[0].name != "%ret" ||
	    !param_pass_is(fn, 0, "indirect_result") ||
	    fn.blocks.empty())
		return;
	const lowir2cy86::Block& entry = fn.blocks[0];
	for (size_t i = 0; i < entry.instructions.size(); ++i) {
		const lowir2cy86::Instruction& ins = entry.instructions[i];
		if (ins.kind == lowir2cy86::InstrKind::Branch ||
		    ins.kind == lowir2cy86::InstrKind::Jump ||
		    ins.kind == lowir2cy86::InstrKind::Switch ||
		    ins.kind == lowir2cy86::InstrKind::Return)
			break;
		if (ins.kind == lowir2cy86::InstrKind::Load &&
		    ins.a.kind == lowir2cy86::ValueKind::Slot) {
			map<string, string>::const_iterator sit =
			    slot_param_sources_.find(ins.a.text);
			if (sit != slot_param_sources_.end()) {
				const int index = param_index(fn, sit->second);
				if (index >= 0 && param_pass_is(fn, index, "reference"))
					entry_branch_param_loads_[ins.dest] = sit->second;
			}
		}
		if (ins.kind == lowir2cy86::InstrKind::Index &&
		    ins.a.kind == lowir2cy86::ValueKind::Temp &&
		    entry_branch_param_loads_.find(ins.a.text) !=
		        entry_branch_param_loads_.end())
			entry_branch_param_indexes_.insert(ins.dest);
		if (ins.kind == lowir2cy86::InstrKind::Load &&
		    ins.a.kind == lowir2cy86::ValueKind::Temp &&
		    entry_branch_param_indexes_.find(ins.a.text) !=
		        entry_branch_param_indexes_.end())
			entry_branch_param_value_loads_.insert(ins.dest);
	}
}

string MirDumper::temp_origin_param(const lowir2cy86::Function& fn,
                         const string& name) const {
	set<string> seen;
	return temp_origin_param(fn, name, seen);
}

string MirDumper::temp_origin_param(const lowir2cy86::Function& fn,
                         const string& name,
                         set<string>& seen) const {
	if (!seen.insert(name).second)
		return "";
	if (param_index(fn, name) >= 0)
		return name;
	map<string, string>::const_iterator pit = promoted_loads_.find(name);
	if (pit != promoted_loads_.end())
		return pit->second;
	map<string, const lowir2cy86::Instruction*>::const_iterator it =
	    definitions_.find(name);
	if (it == definitions_.end())
		return "";
	const lowir2cy86::Instruction& ins = *it->second;
	if (ins.kind == lowir2cy86::InstrKind::Load) {
		if (ins.a.kind == lowir2cy86::ValueKind::Slot) {
			map<string, string>::const_iterator sit =
			    slot_param_sources_.find(ins.a.text);
			return sit == slot_param_sources_.end() ? "" : sit->second;
		}
		if (ins.a.kind == lowir2cy86::ValueKind::Temp)
			return temp_origin_param(fn, ins.a.text, seen);
	}
	if ((ins.kind == lowir2cy86::InstrKind::Index ||
	     ins.kind == lowir2cy86::InstrKind::Copy ||
	     (ins.kind == lowir2cy86::InstrKind::Unary && ins.op == "decay")) &&
	    ins.a.kind == lowir2cy86::ValueKind::Temp)
		return temp_origin_param(fn, ins.a.text, seen);
	return "";
}

bool MirDumper::temp_origin_is_reference_param(const lowir2cy86::Function& fn,
                                    const string& name) const {
	const string param = temp_origin_param(fn, name);
	const int index = param.empty() ? -1 : param_index(fn, param);
	return index >= 0 && param_pass_is(fn, index, "reference");
}

void MirDumper::materialize_frame_temp(const string& name) {
	sret_frame_temps_.insert(name);
	frame_temps_.insert(name);
}

void MirDumper::collect_reference_address_frame_chain(
    const lowir2cy86::Function& fn, const string& name) {
	map<string, const lowir2cy86::Instruction*>::const_iterator it =
	    definitions_.find(name);
	if (it == definitions_.end())
		return;
	const lowir2cy86::Instruction& ins = *it->second;
	if (ins.kind == lowir2cy86::InstrKind::Load &&
	    ins.a.kind == lowir2cy86::ValueKind::Slot &&
	    temp_origin_is_reference_param(fn, name)) {
		materialize_frame_temp(name);
		return;
	}
	if ((ins.kind == lowir2cy86::InstrKind::Index ||
	     (ins.kind == lowir2cy86::InstrKind::Unary && ins.op == "decay")) &&
	    ins.a.kind == lowir2cy86::ValueKind::Temp) {
		collect_reference_address_frame_chain(fn, ins.a.text);
		materialize_frame_temp(name);
	}
}

void MirDumper::collect_stack_call_load_frame_chain(
    const lowir2cy86::Function& fn, const string& name,
    bool include_address_chain) {
	map<string, const lowir2cy86::Instruction*>::const_iterator it =
	    definitions_.find(name);
	if (it == definitions_.end())
		return;
	const lowir2cy86::Instruction& ins = *it->second;
	if (include_address_chain &&
	    ins.kind == lowir2cy86::InstrKind::Load &&
	    ins.a.kind == lowir2cy86::ValueKind::Temp)
		collect_reference_address_frame_chain(fn, ins.a.text);
	materialize_frame_temp(name);
}

void MirDumper::note_inline_copy_addr(const lowir2cy86::Value& value) {
	if (value.kind != lowir2cy86::ValueKind::Temp ||
	    use_counts_[value.text] != 1) return;
	map<string, const lowir2cy86::Instruction*>::const_iterator it =
	    definitions_.find(value.text);
	if (it != definitions_.end() && it->second->kind == lowir2cy86::InstrKind::Addr)
		inline_copy_addrs_.insert(value.text); }

void MirDumper::note_direct_object_copy_addr(const lowir2cy86::Function& fn,
                                  const lowir2cy86::Instruction& ins) {
	if (!copyobj_source_is_direct_object(fn, ins) ||
	    ins.b.kind != lowir2cy86::ValueKind::Temp)
		return;
	map<string, const lowir2cy86::Instruction*>::const_iterator it =
	    definitions_.find(ins.b.text);
	if (it != definitions_.end() &&
	    it->second->kind == lowir2cy86::InstrKind::Addr)
		direct_object_copy_addrs_.insert(ins.b.text); }

void MirDumper::note_direct_param_copy_loads(const lowir2cy86::Function& fn,
                                  const lowir2cy86::Instruction& ins) {
	string src = direct_param_copy_load_param(fn, ins.a);
	string dst = direct_param_copy_load_param(fn, ins.b);
	if (src.empty() || dst.empty())
		return;
	const int src_index = param_index(fn, src);
	const int dst_index = param_index(fn, dst);
	if (src_index < 0 || dst_index < 0 ||
	    mir_abi_param_location(fn, src_index) != "rsi" ||
	    mir_abi_param_location(fn, dst_index) != "rdi")
		return;
	direct_param_copy_loads_.insert(ins.a.text);
	direct_param_copy_loads_.insert(ins.b.text);
	forced_preserve_count_ =
	    max(forced_preserve_count_, static_cast<size_t>(2));
}

string MirDumper::direct_param_copy_load_param(const lowir2cy86::Function& fn,
                                    const lowir2cy86::Value& value) const {
	if (value.kind != lowir2cy86::ValueKind::Temp)
		return "";
	map<string, const lowir2cy86::Instruction*>::const_iterator it =
	    definitions_.find(value.text);
	if (it == definitions_.end() ||
	    it->second->kind != lowir2cy86::InstrKind::Load ||
	    it->second->a.kind != lowir2cy86::ValueKind::Slot)
		return "";
	map<string, string>::const_iterator sit =
	    slot_param_sources_.find(it->second->a.text);
	return sit == slot_param_sources_.end() ? "" : sit->second;
}

bool MirDumper::param_only_feeds_direct_param_copy(
    const lowir2cy86::Function& fn, const string& name) const {
	string slot;
	for (map<string, string>::const_iterator it =
	         slot_param_sources_.begin();
	     it != slot_param_sources_.end(); ++it) {
		if (it->second == name) {
			slot = it->first;
			break;
		}
	}
	if (slot.empty())
		return false;
	bool saw_copy_load = false;
	for (size_t b = 0; b < fn.blocks.size(); ++b)
		for (size_t i = 0; i < fn.blocks[b].instructions.size(); ++i) {
			const lowir2cy86::Instruction& ins =
			    fn.blocks[b].instructions[i];
			const bool store_to_slot =
			    ins.kind == lowir2cy86::InstrKind::Store &&
			    value_is_temp(ins.a, name) &&
			    ins.b.kind == lowir2cy86::ValueKind::Slot &&
			    ins.b.text == slot;
			if (!store_to_slot &&
			    (value_is_temp(ins.a, name) ||
			     value_is_temp(ins.b, name) ||
			     value_is_temp(ins.c, name)))
				return false;
			for (size_t a = 0; a < ins.args.size(); ++a)
				if (value_is_temp(ins.args[a], name))
					return false;
			for (size_t s = 0; s < ins.switch_cases.size(); ++s)
				if (value_is_temp(ins.switch_cases[s].value, name))
					return false;
			if (ins.kind != lowir2cy86::InstrKind::Load ||
			    ins.a.kind != lowir2cy86::ValueKind::Slot ||
			    ins.a.text != slot)
				continue;
			if (direct_param_copy_loads_.find(ins.dest) ==
			    direct_param_copy_loads_.end())
				return false;
			saw_copy_load = true;
		}
	return saw_copy_load;
}

bool MirDumper::value_is_temp(const lowir2cy86::Value& value,
                   const string& name) const {
	return value.kind == lowir2cy86::ValueKind::Temp &&
	       value.text == name;
}

void MirDumper::note_inline_zero_addr(const lowir2cy86::Function& fn,
                           const lowir2cy86::Value& value) {
	if (value.kind != lowir2cy86::ValueKind::Temp)
		return;
	map<string, const lowir2cy86::Instruction*>::const_iterator it =
	    definitions_.find(value.text);
	if (it == definitions_.end() ||
	    it->second->kind != lowir2cy86::InstrKind::Addr ||
	    it->second->a.kind != lowir2cy86::ValueKind::Slot)
		return;
	if (addr_temp_only_zero_and_index(fn, value.text))
		inline_zero_addrs_.insert(value.text); }

bool MirDumper::addr_temp_only_zero_and_index(const lowir2cy86::Function& fn,
                                   const string& name) const {
	bool saw_zero = false;
	for (size_t b = 0; b < fn.blocks.size(); ++b) {
		for (size_t i = 0; i < fn.blocks[b].instructions.size(); ++i) {
			const lowir2cy86::Instruction& ins = fn.blocks[b].instructions[i];
			const bool a = temp_value_named(ins.a, name);
			const bool bval = temp_value_named(ins.b, name);
			const bool c = temp_value_named(ins.c, name);
			bool arg = false;
			for (size_t n = 0; n < ins.args.size(); ++n)
				arg = arg || temp_value_named(ins.args[n], name);
			for (size_t n = 0; n < ins.switch_cases.size(); ++n)
				arg = arg || temp_value_named(ins.switch_cases[n].value, name);
			if (!a && !bval && !c && !arg)
				continue;
			if (ins.kind == lowir2cy86::InstrKind::ZeroInit && a &&
			    !bval && !c && !arg) {
				saw_zero = true;
				continue;
			}
			if (ins.kind == lowir2cy86::InstrKind::Index && a &&
			    !bval && !c && !arg)
				continue;
			return false;
		}
	}
	return saw_zero; }

bool MirDumper::temp_value_named(const lowir2cy86::Value& value,
                      const string& name) const {
	return value.kind == lowir2cy86::ValueKind::Temp &&
	       value.text == name; }

void MirDumper::note_direct_branch_load(const lowir2cy86::Instruction& cmp) {
    if (cmp.b.kind == lowir2cy86::ValueKind::Temp &&
	    direct_branch_slot_load_temp(cmp.b.text, cmp.type)) {
		direct_branch_loads_.insert(cmp.b.text);
		if (cmp.a.kind == lowir2cy86::ValueKind::Temp &&
		    direct_branch_slot_load_temp(cmp.a.text, cmp.type))
			materialized_branch_loads_.insert(cmp.a.text);
		return;
	}
	if (cmp.a.kind != lowir2cy86::ValueKind::Temp)
		return;
	if (!direct_branch_slot_load_temp(cmp.a.text, cmp.type))
		return;
	direct_branch_loads_.insert(cmp.a.text); }

void MirDumper::note_direct_branch_operands(const lowir2cy86::Instruction& cmp) {
	note_direct_branch_operand(cmp.a, "rax");
	note_direct_branch_operand(cmp.b, "rdx"); }

void MirDumper::note_post_call_direct_branch_load(const lowir2cy86::Block& block,
                                       size_t branch_index,
                                       const lowir2cy86::Instruction& cmp) {
	bool saw_call = false;
	for (size_t i = 0; i < branch_index; ++i)
		if (block.instructions[i].kind == lowir2cy86::InstrKind::Call)
			saw_call = true;
	if (!saw_call)
		return;
	note_post_call_direct_branch_load_value(cmp.a, cmp.type);
	note_post_call_direct_branch_load_value(cmp.b, cmp.type);
	note_post_call_direct_branch_call_result(block, branch_index, cmp);
}

void MirDumper::note_post_call_direct_branch_call_result(
    const lowir2cy86::Block& block, size_t branch_index,
    const lowir2cy86::Instruction& cmp) {
	size_t cmp_index = branch_index;
	for (size_t i = 0; i < branch_index; ++i)
		if (&block.instructions[i] == &cmp) {
			cmp_index = i;
			break;
		}
	if (cmp_index == branch_index)
		return;
	bool saw_call_after_cmp = false;
	for (size_t i = cmp_index + 1; i < branch_index; ++i)
		if (block.instructions[i].kind == lowir2cy86::InstrKind::Call)
			saw_call_after_cmp = true;
	if (!saw_call_after_cmp)
		return;
	note_direct_branch_call_result_value(cmp.a);
	note_direct_branch_call_result_value(cmp.b);
}

void MirDumper::note_direct_branch_call_result_value(const lowir2cy86::Value& value) {
	if (value.kind != lowir2cy86::ValueKind::Temp)
		return;
	map<string, const lowir2cy86::Instruction*>::const_iterator it =
	    definitions_.find(value.text);
	if (it != definitions_.end() &&
	    it->second->kind == lowir2cy86::InstrKind::Call)
		branch_cmp_call_result_frame_preserve_ = true;
}

void MirDumper::note_post_call_direct_branch_load_value(const lowir2cy86::Value& value,
                                             const lowir2cy86::Type& cmp_type) {
	if (value.kind != lowir2cy86::ValueKind::Temp)
		return;
	map<string, const lowir2cy86::Instruction*>::const_iterator it =
	    definitions_.find(value.text);
	if (it != definitions_.end() &&
	    it->second->kind == lowir2cy86::InstrKind::Load &&
	    it->second->a.kind == lowir2cy86::ValueKind::Slot &&
	    lowir2cy86::is_integer_type(it->second->type) &&
	    lowir2cy86::is_integer_type(cmp_type) &&
	    it->second->type.bits < cmp_type.bits) {
		post_call_direct_branch_loads_.insert(value.text);
		frame_temps_.insert(value.text);
	}
}

void MirDumper::note_direct_branch_operand(const lowir2cy86::Value& value,
                                const string& addr_reg) {
	if (value.kind != lowir2cy86::ValueKind::Temp)
		return;
	direct_branch_value_operands_.insert(value.text);
	map<string, const lowir2cy86::Instruction*>::const_iterator it =
	    definitions_.find(value.text);
	if (it == definitions_.end())
		return;
	if (it->second->kind == lowir2cy86::InstrKind::Addr) {
		if (it->second->a.kind != lowir2cy86::ValueKind::Global)
			direct_branch_addr_regs_[value.text] = addr_reg;
	}
	else if (it->second->kind == lowir2cy86::InstrKind::Call &&
	         !lowir2cy86::is_float_type(it->second->type)) {
		branch_cmp_call_results_.insert(value.text);
		live_across_calls_.insert(value.text);
	}
}

bool MirDumper::direct_branch_slot_load_temp(const string& name,
                                  const lowir2cy86::Type& type) const {
	map<string, int>::const_iterator uit = use_counts_.find(name);
	if (uit == use_counts_.end() || uit->second != 1)
		return false;
	map<string, const lowir2cy86::Instruction*>::const_iterator it =
	    definitions_.find(name);
	return it != definitions_.end() &&
	       it->second->kind == lowir2cy86::InstrKind::Load &&
	       (it->second->a.kind == lowir2cy86::ValueKind::Slot ||
	        it->second->a.kind == lowir2cy86::ValueKind::Global) &&
	       promoted_loads_.find(name) == promoted_loads_.end() &&
	       it->second->type.text == type.text; }

}  // namespace lowir2native
