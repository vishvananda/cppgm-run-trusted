#include "pa14_lowir_hosted_inline_internal.h"
#include "pa12_templates_function_support.h"

namespace pa14 {
namespace internal {

bool FunctionLowerer::lower_hosted_shared_control_body()
{
	Binding* binding = fn_.binding;
	if (!hosted_sp_counted_control_binding(binding))
		return false;
	string this_name = parameter_name(out_, 0, "this");
	string self = fresh_temp();
	instr(self + " = load ptr $" + this_name);
	if (hosted_sp_counted_base_constructor_binding(binding))
	{
		TypePtr record = hosted_member_owner_record(binding);
		Binding* use_count = hosted_pair_field(
			record, pa11::abi_private_name("M_use_count"), 0);
		Binding* weak_count = hosted_pair_field(
			record, pa11::abi_private_name("M_weak_count"), 1);
		if (use_count == NULL || weak_count == NULL)
			return false;
		Binding* counts[] = {use_count, weak_count};
		for (size_t i = 0; i < 2; ++i)
		{
			string addr = self;
			if (counts[i]->member_offset != 0)
			{
				addr = fresh_temp();
				instr(addr + " = index i8 [projection=field] " +
				      self + ", " +
				      to_string(counts[i]->member_offset));
			}
			instr("store " + scalar_lowir_type(counts[i]->type) +
			      " 1, " + addr);
		}
		terminate("return void");
		return true;
	}
	if (hosted_sp_counted_base_add_ref_binding(binding))
	{
		TypePtr record = hosted_member_owner_record(binding);
		Binding* use_count = hosted_pair_field(
			record, pa11::abi_private_name("M_use_count"), 0);
		if (use_count == NULL)
			return false;
		string addr = self;
		if (use_count->member_offset != 0)
		{
			addr = fresh_temp();
			instr(addr + " = index i8 [projection=field] " + self +
			      ", " + to_string(use_count->member_offset));
		}
		string low_type = scalar_lowir_type(use_count->type);
		string old_count = fresh_temp();
		instr(old_count + " = load " + low_type + " " + addr);
		string new_count = fresh_temp();
		instr(new_count + " = binary add " + low_type + " " +
		      old_count + ", 1");
		instr("store " + low_type + " " + new_count + ", " + addr);
		terminate("return void");
		return true;
	}
	auto emit_virtual_void_call =
		[this](Binding* target, const string& object)
	{
		if (target == NULL)
			return false;
		program_.demand_function_declaration(target);
		if (target->virtual_slot_index >= 0)
		{
			string vptr = fresh_temp();
			instr(vptr + " = load ptr " + object);
			string slot_addr = vptr;
			if (target->virtual_slot_index > 0)
			{
				slot_addr = fresh_temp();
				instr(slot_addr + " = index i8 " + vptr + ", " +
				      to_string(target->virtual_slot_index * 8));
			}
			string fnptr = fresh_temp();
			instr(fnptr + " = load ptr " + slot_addr);
			instr("call void " + fnptr + "(" + object +
			      ") as (%arg0 : ptr) -> void");
			return true;
		}
		instr("call void @" + program_.symbol_for(target) +
		      "(" + object + ")");
		return true;
	};
	if (hosted_sp_counted_base_destroy_binding(binding) ||
	    binding->name == pa11::abi_private_name("M_destroy"))
	{
		ensure_hosted_operator_delete_declaration(program_);
		instr("call void @operator_delete(" + self + ")");
		terminate("return void");
		return true;
	}
	if (hosted_sp_counted_base_release_binding(binding))
	{
		TypePtr record = hosted_member_owner_record(binding);
		Binding* use_count = hosted_pair_field(
			record, pa11::abi_private_name("M_use_count"), 0);
		Binding* weak_count = hosted_pair_field(
			record, pa11::abi_private_name("M_weak_count"), 1);
		if (use_count == NULL || weak_count == NULL)
			return false;
		string use_addr = self;
		if (use_count->member_offset != 0)
		{
			use_addr = fresh_temp();
			instr(use_addr + " = index i8 [projection=field] " +
			      self + ", " + to_string(use_count->member_offset));
		}
		string weak_addr = self;
		if (weak_count->member_offset != 0)
		{
			weak_addr = fresh_temp();
			instr(weak_addr + " = index i8 [projection=field] " +
			      self + ", " + to_string(weak_count->member_offset));
		}
		string low_type = scalar_lowir_type(use_count->type);
		if (binding->name == pa11::abi_private_name("M_release"))
		{
			Binding* cold = hosted_sp_counted_base_member_function(
				record, pa11::abi_private_name("M_release_last_use_cold"));
			if (cold == NULL)
				cold = hosted_sp_counted_base_member_function(
					record, pa11::abi_private_name("M_release_last_use"));
			if (cold == NULL)
				return false;
			program_.demand_function_declaration(cold);
			program_.demand_inline_function(cold);
			string old_count = fresh_temp();
			instr(old_count + " = load " + low_type + " " + use_addr);
			string new_count = fresh_temp();
			instr(new_count + " = binary sub " + low_type + " " +
			      old_count + ", 1");
			instr("store " + low_type + " " + new_count + ", " +
			      use_addr);
			string last = fresh_temp();
			instr(last + " = cmp eq " + low_type + " " +
			      old_count + ", 1");
			string release_last = fresh_block("sp_release_last");
			string done = fresh_block("sp_release_done");
			terminate("branch " + last + ", ^" + release_last +
			          ", ^" + done);
			start_block(release_last);
			instr("call void @" + program_.symbol_for(cold) +
			      "(" + self + ")");
			terminate("jump ^" + done);
			start_block(done);
			terminate("return void");
			return true;
		}
		Binding* dispose = hosted_sp_counted_base_member_function(
			record, pa11::abi_private_name("M_dispose"));
		Binding* destroy = hosted_sp_counted_base_member_function(
			record, pa11::abi_private_name("M_destroy"));
		if (dispose == NULL || destroy == NULL)
			return false;
		if (!emit_virtual_void_call(dispose, self))
			return false;
		string old_weak = fresh_temp();
		instr(old_weak + " = load " + low_type + " " + weak_addr);
		string new_weak = fresh_temp();
		instr(new_weak + " = binary sub " + low_type + " " +
		      old_weak + ", 1");
		instr("store " + low_type + " " + new_weak + ", " + weak_addr);
		string last_weak = fresh_temp();
		instr(last_weak + " = cmp eq " + low_type + " " +
		      old_weak + ", 1");
		string destroy_block = fresh_block("sp_release_destroy");
		string done = fresh_block("sp_release_last_done");
		terminate("branch " + last_weak + ", ^" + destroy_block +
		          ", ^" + done);
		start_block(destroy_block);
		if (!emit_virtual_void_call(destroy, self))
			return false;
		terminate("jump ^" + done);
		start_block(done);
		terminate("return void");
		return true;
	}
	if (binding->name == pa11::abi_private_name("M_get_deleter"))
	{
		terminate("return " + scalar_lowir_type(binding->type->base) +
		          " 0");
		return true;
	}
	terminate("return void");
	return true;
}

bool FunctionLowerer::lower_hosted_shared_count_copy_body()
{
	Binding* binding = fn_.binding;
	if (!hosted_shared_count_copy_constructor_binding(binding))
		return false;
	Binding* add_ref = hosted_shared_count_control_function(
		binding, pa11::abi_private_name("M_add_ref_copy"));
	if (add_ref == NULL)
		return false;
	program_.demand_function_declaration(add_ref);
	program_.demand_inline_function(add_ref);
	string self_name = parameter_name(out_, 0, "this");
	string other_name = parameter_name(out_, 1, "__r");
	string self = fresh_temp();
	instr(self + " = load ptr $" + self_name);
	string other = fresh_temp();
	instr(other + " = load ptr $" + other_name);
	string other_pi = fresh_temp();
	instr(other_pi + " = load ptr " + other);
	instr("store ptr " + other_pi + ", " + self);
	string has_pi = fresh_temp();
	instr(has_pi + " = cmp ne ptr " + other_pi + ", 0");
	string retain = fresh_block("shared_count_retain");
	string done = fresh_block("shared_count_done");
	terminate("branch " + has_pi + ", ^" + retain + ", ^" + done);
	start_block(retain);
	instr("call void @" + program_.symbol_for(add_ref) + "(" + other_pi + ")");
	terminate("jump ^" + done);
	start_block(done);
	terminate("return void");
	return true;
}

bool FunctionLowerer::lower_hosted_shared_count_assignment_body()
{
	Binding* binding = fn_.binding;
	if (!hosted_shared_count_assignment_binding(binding))
		return false;
	Binding* add_ref = hosted_shared_count_control_function(
		binding, pa11::abi_private_name("M_add_ref_copy"));
	Binding* release = hosted_shared_count_control_function(
		binding, pa11::abi_private_name("M_release"));
	if (add_ref == NULL || release == NULL)
		return false;
	program_.demand_function_declaration(add_ref);
	program_.demand_function_declaration(release);
	program_.demand_inline_function(add_ref);
	program_.demand_inline_function(release);
	string self_name = parameter_name(out_, 0, "this");
	string other_name = parameter_name(out_, 1, "__r");
	string self = fresh_temp();
	instr(self + " = load ptr $" + self_name);
	string other = fresh_temp();
	instr(other + " = load ptr $" + other_name);
	string other_pi = fresh_temp();
	instr(other_pi + " = load ptr " + other);
	string self_pi = fresh_temp();
	instr(self_pi + " = load ptr " + self);
	string same = fresh_temp();
	instr(same + " = cmp eq ptr " + other_pi + ", " + self_pi);
	string done = fresh_block("shared_count_assign_done");
	string retain_check = fresh_block("shared_count_assign_retain_check");
	terminate("branch " + same + ", ^" + done + ", ^" + retain_check);
	start_block(retain_check);
	string has_other = fresh_temp();
	instr(has_other + " = cmp ne ptr " + other_pi + ", 0");
	string retain = fresh_block("shared_count_assign_retain");
	string release_check = fresh_block("shared_count_assign_release_check");
	terminate("branch " + has_other + ", ^" + retain + ", ^" + release_check);
	start_block(retain);
	instr("call void @" + program_.symbol_for(add_ref) + "(" + other_pi + ")");
	terminate("jump ^" + release_check);
	start_block(release_check);
	string has_self = fresh_temp();
	instr(has_self + " = cmp ne ptr " + self_pi + ", 0");
	string release_block = fresh_block("shared_count_assign_release");
	string store = fresh_block("shared_count_assign_store");
	terminate("branch " + has_self + ", ^" + release_block + ", ^" + store);
	start_block(release_block);
	instr("call void @" + program_.symbol_for(release) + "(" + self_pi + ")");
	terminate("jump ^" + store);
	start_block(store);
	instr("store ptr " + other_pi + ", " + self);
	terminate("jump ^" + done);
	start_block(done);
	terminate("return ptr " + self);
	return true;
}

bool FunctionLowerer::lower_hosted_shared_ptr_assignment_body()
{
	Binding* binding = fn_.binding;
	if (!hosted_shared_ptr_assignment_binding(binding))
		return false;
	TypePtr record = class_record_for_member(binding);
	record = record.get() != NULL ? pa11::strip_cv(record) : TypePtr();
	Binding* count_field = hosted_shared_ptr_count_field(record);
	if (count_field == NULL)
		return false;
	bool move = binding->type->parameters[1]->kind == TypeKind::RValueReference;
	string self_name = parameter_name(out_, 0, "this");
	string other_name = parameter_name(out_, 1, "__r");
	string self = fresh_temp();
	instr(self + " = load ptr $" + self_name);
	string other = fresh_temp();
	instr(other + " = load ptr $" + other_name);
	string same = fresh_temp();
	instr(same + " = cmp eq ptr " + self + ", " + other);
	string done = fresh_block("shared_ptr_assign_done");
	string assign = fresh_block("shared_ptr_assign");
	terminate("branch " + same + ", ^" + done + ", ^" + assign);
	start_block(assign);
	if (move)
	{
		TypePtr control = hosted_shared_count_control_record_from_type(
			count_field->type);
		Binding* release = hosted_shared_control_function_from_record(
			control, pa11::abi_private_name("M_release"));
		if (release == NULL)
			return false;
		program_.demand_function_declaration(release);
		program_.demand_inline_function(release);
		string self_count = fresh_temp();
		instr(self_count + " = index i8 [projection=field] " +
		      self + ", 8");
		string self_pi = fresh_temp();
		instr(self_pi + " = load ptr " + self_count);
		string has_self = fresh_temp();
		instr(has_self + " = cmp ne ptr " + self_pi + ", 0");
		string release_block = fresh_block("shared_ptr_assign_release");
		string steal = fresh_block("shared_ptr_assign_steal");
		terminate("branch " + has_self + ", ^" + release_block +
		          ", ^" + steal);
		start_block(release_block);
		instr("call void @" + program_.symbol_for(release) +
		      "(" + self_pi + ")");
		terminate("jump ^" + steal);
		start_block(steal);
		instr("copyobj " + to_string(pa11::type_size(record)) + "x" +
		      to_string(pa11::type_align(record)) + " " +
		      other + ", " + self);
		lower_storage_zero(Value("ptr", other), pa11::type_size(record));
		terminate("jump ^" + done);
	}
	else
	{
		Binding* count_assign =
			program_.demand_implicit_copy_assignment(
				count_field->type, false);
		program_.demand_function_declaration(count_assign);
		if (count_assign->is_inline_definition)
			program_.demand_inline_function(count_assign);
		string other_ptr = fresh_temp();
		instr(other_ptr + " = load ptr " + other);
		instr("store ptr " + other_ptr + ", " + self);
		string self_count = fresh_temp();
		instr(self_count + " = index i8 [projection=field] " +
		      self + ", 8");
		string other_count = fresh_temp();
		instr(other_count + " = index i8 [projection=field] " +
		      other + ", 8");
		string ignored = fresh_temp();
		instr(ignored + " = call ptr @" +
		      program_.symbol_for(count_assign) + "(" +
		      self_count + ", " + other_count + ")");
		terminate("jump ^" + done);
	}
	start_block(done);
	terminate("return ptr " + self);
	return true;
}

}  // namespace internal
}  // namespace pa14
