#include "pa14_lowir_hosted_inline_internal.h"
#include "pa12_templates_function_support.h"

namespace pa14 {
namespace internal {

bool FunctionLowerer::lower_hosted_basic_string_guard_destructor_body()
{
	Binding* binding = fn_.binding;
	if (!hosted_basic_string_guard_destructor_binding(binding))
		return false;
	TypePtr guard_record = class_record_for_member(binding);
	Binding* guarded_field = basic_string_guarded_field(guard_record);
	if (guarded_field == NULL)
		return false;
	TypePtr string_ptr = pa11::strip_cv(guarded_field->type);
	TypePtr string_record = string_ptr->base;
	Binding* dispose = hosted_basic_string_release_function(string_record);
	if (dispose == NULL)
		return false;
	program_.demand_function_declaration(dispose);
	program_.demand_inline_function(dispose);
	string this_name = parameter_name(out_, 0, "this");
	string self = fresh_temp();
	instr(self + " = load ptr $" + this_name);
	string field_addr = self;
	if (guarded_field->member_offset != 0)
	{
		field_addr = fresh_temp();
		instr(field_addr + " = index i8 [projection=field] " +
		      self + ", " + to_string(guarded_field->member_offset));
	}
	string guarded = fresh_temp();
	instr(guarded + " = load ptr " + field_addr);
	string has_guarded = fresh_temp();
	instr(has_guarded + " = cmp ne ptr " + guarded + ", 0");
	string dispose_block = fresh_block("guard_dispose");
	string done_block = fresh_block("guard_done");
	terminate("branch " + has_guarded + ", ^" +
	          dispose_block + ", ^" + done_block);
	start_block(dispose_block);
	instr("call void @" + program_.symbol_for(dispose) +
	      "(" + guarded + ")");
	terminate("jump ^" + done_block);
	start_block(done_block);
	terminate("return void");
	return true;
}

bool FunctionLowerer::lower_hosted_vector_base_deallocate_body()
{
	Binding* binding = fn_.binding;
	if (!hosted_vector_base_deallocate_binding(binding))
		return false;
	ensure_hosted_operator_delete_declaration(program_);
	string pointer_name = parameter_name(out_, 1, "__p");
	string pointer = fresh_temp();
	instr(pointer + " = load ptr $" + pointer_name);
	string has_pointer = fresh_temp();
	instr(has_pointer + " = cmp ne ptr " + pointer + ", 0");
	string deallocate_block = fresh_block("vector_deallocate");
	string done_block = fresh_block("vector_deallocate_done");
	terminate("branch " + has_pointer + ", ^" +
	          deallocate_block + ", ^" + done_block);
	start_block(deallocate_block);
	instr("call void @operator_delete(" + pointer + ")");
	terminate("jump ^" + done_block);
	start_block(done_block);
	terminate("return void");
	return true;
}

bool FunctionLowerer::lower_hosted_vector_impl_move_constructor_body()
{
	Binding* binding = fn_.binding;
	if (!hosted_vector_impl_move_constructor_binding(binding))
		return false;
	TypePtr record = class_record_for_member(binding);
	record = record.get() != NULL ? pa11::strip_cv(record) : TypePtr();
	if (record.get() == NULL || record->kind != TypeKind::Record)
		return false;
	string this_name = parameter_name(out_, 0, "this");
	string other_name = parameter_name(out_, 1, "__x");
	string self = fresh_temp();
	instr(self + " = load ptr $" + this_name);
	string other = fresh_temp();
	instr(other + " = load ptr $" + other_name);
	uint64_t size = pa11::type_size(record);
	uint64_t align = pa11::type_align(record);
	instr("copyobj " + to_string(size) + "x" + to_string(align) +
	      " " + other + ", " + self);
	instr("zeroinit " + to_string(size) + "x" + to_string(align) +
	      " " + other);
	terminate("return void");
	return true;
}

bool FunctionLowerer::lower_hosted_std_function_swap_body()
{
	Binding* binding = fn_.binding;
	if (!hosted_std_function_swap_binding(binding))
		return false;
	TypePtr record = class_record_for_member(binding);
	record = record.get() != NULL ? pa11::strip_cv(record) : TypePtr();
	if (record.get() == NULL || record->kind != TypeKind::Record)
		return false;
	string this_name = parameter_name(out_, 0, "this");
	string other_name = parameter_name(out_, 1, "__x");
	string self = fresh_temp();
	instr(self + " = load ptr $" + this_name);
	string other = fresh_temp();
	instr(other + " = load ptr $" + other_name);
	uint64_t size = pa11::type_size(record);
	uint64_t align = pa11::type_align(record);
	string tmp = fresh_aux_slot("function_swap", slot_lowir_type(record));
	instr("copyobj " + to_string(size) + "x" + to_string(align) +
	      " " + self + ", $" + tmp);
	instr("copyobj " + to_string(size) + "x" + to_string(align) +
	      " " + other + ", " + self);
	instr("copyobj " + to_string(size) + "x" + to_string(align) +
	      " $" + tmp + ", " + other);
	terminate("return void");
	return true;
}

bool FunctionLowerer::lower_hosted_rbtree_assignment_body()
{
	Binding* binding = fn_.binding;
	if (!hosted_rbtree_assignment_binding(binding))
		return false;
	TypePtr record = hosted_member_owner_record(binding);
	record = record.get() != NULL ? pa11::strip_cv(record) : TypePtr();
	if (record.get() == NULL || record->kind != TypeKind::Record)
		return false;
	if (record->template_arguments.size() < 2 ||
	    record->template_arguments[1].kind !=
		    pa11::TemplateInstanceArgumentKind::Type)
		return false;
	TypePtr value_type = pa11::strip_cv(record->template_arguments[1].type);
	if (value_type.get() == NULL)
		return false;
	uint64_t value_align = pa11::type_align(value_type);
	uint64_t value_size = pa11::type_size(value_type);
	uint64_t node_align = max<uint64_t>(uint64_t(8), value_align);
	uint64_t value_offset =
		(uint64_t(32) + value_align - 1) & ~(value_align - 1);
	uint64_t node_size =
		(value_offset + value_size + node_align - 1) &
		~(node_align - 1);
	ensure_hosted_operator_new_declaration(program_);
	ensure_hosted_rbtree_runtime_declarations(program_);
	string this_name = parameter_name(out_, 0, "this");
	string other_name = parameter_name(out_, 1, "__x");
	string self = fresh_temp();
	instr(self + " = load ptr $" + this_name);
	string other = fresh_temp();
	instr(other + " = load ptr $" + other_name);
	string same = fresh_temp();
	instr(same + " = cmp eq ptr " + self + ", " + other);
	string assign_block = fresh_block("rbtree_assign");
	string done_block = fresh_block("rbtree_assign_done");
	terminate("branch " + same + ", ^" + done_block + ", ^" +
	          assign_block);
	start_block(assign_block);
	lower_destructor_for_object([self]() { return Value("ptr", self); },
	                            record);

	auto header_addr = [this](const string& tree) -> string {
		string impl = fresh_temp();
		instr(impl + " = index i8 [projection=field] " + tree +
		      ", 0");
		string header_base = fresh_temp();
		instr(header_base + " = index i8 [projection=base_subobject] " +
		      impl + ", 8");
		string header = fresh_temp();
		instr(header + " = index i8 [projection=field] " +
		      header_base + ", 0");
		return header;
	};
	auto field_addr = [this](const string& base, uint64_t offset) -> string {
		string addr = fresh_temp();
		instr(addr + " = index i8 [projection=field] " + base +
		      ", " + to_string(offset));
		return addr;
	};
	auto copy_object = [this](TypePtr type, const string& dst,
	                          const string& src) -> bool {
		TypePtr bare = pa11::strip_cv(type);
		if (bare.get() == NULL)
			return false;
		if (bare->kind == TypeKind::Record)
		{
			Binding* ctor = find_copy_move_constructor(bare, false);
			if (ctor != NULL)
			{
				program_.demand_function_declaration(ctor);
				program_.demand_inline_function(ctor);
				instr("call void @" + program_.symbol_for(ctor) +
				      "(" + dst + ", " + src + ")");
				return true;
			}
			if (!record_has_storage_copy(bare))
				return false;
			instr("copyobj " + to_string(pa11::type_size(bare)) +
			      "x" + to_string(pa11::type_align(bare)) +
			      " " + src + ", " + dst);
			return true;
		}
		if (is_reference(type))
		{
			string value = fresh_temp();
			instr(value + " = load ptr " + src);
			instr("store ptr " + value + ", " + dst);
			return true;
		}
		string low_type = scalar_lowir_type(type);
		string value = fresh_temp();
		instr(value + " = load " + low_type + " " + src);
		instr("store " + low_type + " " + value + ", " + dst);
		return true;
	};

	instr("copyobj 8x8 " + other + ", " + self);
	string self_header = header_addr(self);
	string other_header = header_addr(other);
	string self_parent_addr = field_addr(self_header, 8);
	instr("store ptr 0, " + self_parent_addr);
	string self_left_addr = field_addr(self_header, 16);
	instr("store ptr " + self_header + ", " + self_left_addr);
	string self_right_addr = field_addr(self_header, 24);
	instr("store ptr " + self_header + ", " + self_right_addr);
	string self_count_addr = field_addr(self_header, 32);
	instr("store i64 0, " + self_count_addr);

	string source_left_addr = field_addr(other_header, 16);
	string source_cur_slot = fresh_aux_slot("rbtree_copy_cur", "ptr");
	string source_cur_init = fresh_temp();
	instr(source_cur_init + " = load ptr " + source_left_addr);
	instr("store ptr " + source_cur_init + ", $" + source_cur_slot);
	string copy_check = fresh_block("rbtree_copy_check");
	string copy_body = fresh_block("rbtree_copy_body");
	terminate("jump ^" + copy_check);
	start_block(copy_check);
	string source_cur = fresh_temp();
	instr(source_cur + " = load ptr $" + source_cur_slot);
	string copy_done = fresh_temp();
	instr(copy_done + " = cmp eq ptr " + source_cur + ", " +
	      other_header);
	terminate("branch " + copy_done + ", ^" + done_block + ", ^" +
	          copy_body);
	start_block(copy_body);
	string node = fresh_temp();
	instr(node + " = call ptr @operator_new(" + to_string(node_size) + ")");
	string dst_value = fresh_temp();
	instr(dst_value + " = index i8 " + node + ", " +
	      to_string(value_offset));
	string src_value = fresh_temp();
	instr(src_value + " = index i8 " + source_cur + ", " +
	      to_string(value_offset));
	if (!copy_object(value_type, dst_value, src_value))
		return false;
	string parent = fresh_temp();
	instr(parent + " = load ptr " + self_right_addr);
	string insert_left = fresh_temp();
	instr(insert_left + " = cmp eq ptr " + parent + ", " +
	      self_header);
	instr("call void @std___Rb_tree_insert_and_rebalance(" +
	      insert_left + ", " + node + ", " + parent + ", " +
	      self_header + ")");
	string count = fresh_temp();
	instr(count + " = load i64 " + self_count_addr);
	string next_count = fresh_temp();
	instr(next_count + " = binary add i64 " + count + ", 1");
	instr("store i64 " + next_count + ", " + self_count_addr);
	string next_source = fresh_temp();
	instr(next_source + " = call ptr @std___Rb_tree_increment(" +
	      source_cur + ")");
	instr("store ptr " + next_source + ", $" + source_cur_slot);
	terminate("jump ^" + copy_check);
	start_block(done_block);
	terminate("return " + scalar_lowir_type(binding->type->base) +
	          " " + self);
	return true;
}

bool FunctionLowerer::lower_hosted_rbtree_copy_constructor_body()
{
	Binding* binding = fn_.binding;
	if (!hosted_rbtree_copy_constructor_binding(binding))
		return false;
	TypePtr record = hosted_member_owner_record(binding);
	record = record.get() != NULL ? pa11::strip_cv(record) : TypePtr();
	if (record.get() == NULL || record->kind != TypeKind::Record)
		return false;
	Binding* assign = find_record_copy_move_assignment(record, false);
	if (assign == NULL)
		return false;
	program_.demand_function_declaration(assign);
	program_.demand_inline_function(assign);
	string this_name = parameter_name(out_, 0, "this");
	string other_name = parameter_name(out_, 1, "__x");
	string self = fresh_temp();
	instr(self + " = load ptr $" + this_name);
	function<Value()> self_addr = [self]() { return Value("ptr", self); };
	lower_zero_init(self_addr, record);
	string other = fresh_temp();
	instr(other + " = load ptr $" + other_name);
	instr("call " + scalar_lowir_type(assign->type->base) +
	      " @" + program_.symbol_for(assign) + "(" + self + ", " +
	      other + ")");
	terminate("return void");
	return true;
}

bool FunctionLowerer::lower_hosted_rbtree_const_iterator_node_constructor_body()
{
	Binding* binding = fn_.binding;
	if (!hosted_rbtree_const_iterator_node_constructor_binding(binding))
		return false;
	TypePtr record = hosted_member_owner_record(binding);
	record = record.get() != NULL ? pa11::strip_cv(record) : TypePtr();
	if (record.get() == NULL || record->kind != TypeKind::Record)
		return false;
	string this_name = parameter_name(out_, 0, "this");
	string node_name = parameter_name(out_, 1, "__node");
	string self = fresh_temp();
	instr(self + " = load ptr $" + this_name);
	string node = fresh_temp();
	instr(node + " = load ptr $" + node_name);
	uint64_t node_offset = hosted_field_offset_or_zero(
		record, pa11::abi_private_name("M_node"));
	string node_addr = self;
	if (node_offset != 0)
	{
		node_addr = fresh_temp();
		instr(node_addr + " = index i8 [projection=field] " +
		      self + ", " + to_string(node_offset));
	}
	instr("store ptr " + node + ", " + node_addr);
	terminate("return void");
	return true;
}

bool FunctionLowerer::lower_hosted_temporary_buffer_constructor_body()
{
	Binding* binding = fn_.binding;
	if (!hosted_temporary_buffer_constructor_binding(binding))
		return false;
	TypePtr record = hosted_member_owner_record(binding);
	record = record.get() != NULL ? pa11::strip_cv(record) : TypePtr();
	if (record.get() == NULL || record->kind != TypeKind::Record)
		return false;
	Binding* original =
		hosted_field_named(record, pa11::abi_private_name("M_original_len"));
	if (original == NULL && !record->fields.empty())
		original = record->fields[0];
	Binding* impl =
		hosted_field_named(record, pa11::abi_private_name("M_impl"));
	if (impl == NULL && record->fields.size() > 1)
		impl = record->fields[1];
	if (original == NULL || impl == NULL)
		return false;
	TypePtr impl_record = pa11::strip_cv(impl->type);
	if (impl_record.get() == NULL || impl_record->kind != TypeKind::Record)
		return false;
	Binding* len = hosted_field_named(
		impl_record, pa11::abi_private_name("M_len"));
	if (len == NULL && !impl_record->fields.empty())
		len = impl_record->fields[0];
	Binding* buffer = hosted_field_named(
		impl_record, pa11::abi_private_name("M_buffer"));
	if (buffer == NULL && impl_record->fields.size() > 1)
		buffer = impl_record->fields[1];
	if (len == NULL || buffer == NULL)
		return false;
	string this_name = parameter_name(out_, 0, "this");
	string len_name = parameter_name(out_, 2, "__original_len");
	string self = fresh_temp();
	instr(self + " = load ptr $" + this_name);
	string requested = fresh_temp();
	string requested_type = scalar_lowir_type(binding->type->parameters[2]);
	instr(requested + " = load " + requested_type + " $" + len_name);
	string original_addr = self;
	if (original->member_offset != 0)
	{
		original_addr = fresh_temp();
		instr(original_addr + " = index i8 [projection=field] " +
		      self + ", " + to_string(original->member_offset));
	}
	instr("store " + requested_type + " " + requested + ", " +
	      original_addr);
	string impl_addr = self;
	if (impl->member_offset != 0)
	{
		impl_addr = fresh_temp();
		instr(impl_addr + " = index i8 [projection=field] " +
		      self + ", " + to_string(impl->member_offset));
	}
	string len_addr = impl_addr;
	if (len->member_offset != 0)
	{
		len_addr = fresh_temp();
		instr(len_addr + " = index i8 [projection=field] " +
		      impl_addr + ", " + to_string(len->member_offset));
	}
	instr("store " + scalar_lowir_type(len->type) + " 0, " + len_addr);
	string buffer_addr = impl_addr;
	if (buffer->member_offset != 0)
	{
		buffer_addr = fresh_temp();
		instr(buffer_addr + " = index i8 [projection=field] " +
		      impl_addr + ", " + to_string(buffer->member_offset));
	}
	instr("store ptr 0, " + buffer_addr);
	terminate("return void");
	return true;
}

bool FunctionLowerer::lower_hosted_tuple_storage_default_constructor_body()
{
	Binding* binding = fn_.binding;
	if (!hosted_tuple_storage_default_constructor_binding(binding))
		return false;
	TypePtr record = hosted_member_owner_record(binding);
	record = record.get() != NULL ? pa11::strip_cv(record) : TypePtr();
	if (record.get() == NULL || record->kind != TypeKind::Record)
		return false;
	string this_name = parameter_name(out_, 0, "this");
	string self = fresh_temp();
	instr(self + " = load ptr $" + this_name);
	lower_storage_zero(Value("ptr", self), pa11::type_size(record));
	terminate("return void");
	return true;
}

bool FunctionLowerer::lower_hosted_tuple_storage_head_body()
{
	Binding* binding = fn_.binding;
	if (!hosted_tuple_storage_head_binding(binding))
		return false;
	TypePtr record = hosted_member_owner_record(binding);
	record = record.get() != NULL ? pa11::strip_cv(record) : TypePtr();
	if (record.get() == NULL || record->kind != TypeKind::Record)
		return false;
	string tuple_name = parameter_name(out_, 0, "__t");
	string object = fresh_temp();
	instr(object + " = load ptr $" + tuple_name);
	uint64_t offset = hosted_field_offset_or_zero(
		record, pa11::abi_private_name("M_head_impl"));
	string result = object;
	if (offset != 0)
	{
		result = fresh_temp();
		instr(result + " = index i8 [projection=field] " +
		      object + ", " + to_string(offset));
	}
	terminate("return " + scalar_lowir_type(binding->type->base) +
	          " " + result);
	return true;
}

bool FunctionLowerer::lower_hosted_tuple_reference_constructor_body()
{
	Binding* binding = fn_.binding;
	if (!hosted_tuple_reference_constructor_binding(binding, NULL))
		return false;
	TypePtr record = hosted_member_owner_record(binding);
	record = record.get() != NULL ? pa11::strip_cv(record) : TypePtr();
	if (record.get() == NULL || record->kind != TypeKind::Record)
		return false;
	string this_name = parameter_name(out_, 0, "this");
	string value_name = parameter_name(out_, 1, "__value");
	string self = fresh_temp();
	instr(self + " = load ptr $" + this_name);
	lower_storage_zero(Value("ptr", self), pa11::type_size(record));
	uint64_t offset = hosted_field_offset_or_zero(
		record, pa11::abi_private_name("M_head_impl"));
	string target = self;
	if (offset != 0)
	{
		target = fresh_temp();
		instr(target + " = index i8 [projection=field] " +
		      self + ", " + to_string(offset));
	}
	instr("store ptr $" + value_name + ", " + target);
	terminate("return void");
	return true;
}

bool hosted_forward_as_tuple_binding(const Binding* binding)
{
	if (binding == NULL ||
	    binding->name != "forward_as_tuple" ||
	    !binding_in_namespace(binding, "std") ||
	    binding->type.get() == NULL ||
	    binding->type->kind != TypeKind::Function)
		return false;
	TypePtr result = pa11::strip_cv(binding->type->base);
	if (!hosted_tuple_record(result))
		return false;
	for (size_t i = 0; i < binding->type->parameters.size(); ++i)
		if (!is_reference(binding->type->parameters[i]))
			return false;
	return true;
}

bool FunctionLowerer::lower_hosted_forward_as_tuple_body()
{
	Binding* binding = fn_.binding;
	if (!hosted_forward_as_tuple_binding(binding))
		return false;
	TypePtr result = pa11::strip_cv(binding->type->base);
	pa11::layout_record_type(result);
	Value tuple_addr;
	bool indirect_result = record_return_by_address(result);
	if (indirect_result)
		tuple_addr = Value("ptr", "%ret");
	else
	{
		if (record_return_slot_.empty())
			record_return_slot_ = fresh_aux_slot("retobj",
			                                     slot_lowir_type(result));
		string addr = fresh_temp();
		instr(addr + " = addr $" + record_return_slot_);
		tuple_addr = Value("ptr", addr);
	}
	lower_storage_zero(tuple_addr, pa11::type_size(result));
	for (size_t i = 0; i < binding->type->parameters.size(); ++i)
	{
		string target = tuple_addr.text;
		uint64_t offset = i * 8;
		if (offset != 0)
		{
			target = fresh_temp();
			instr(target + " = index i8 [projection=field] " +
			      tuple_addr.text + ", " + to_string(offset));
		}
		string pname = parameter_name(out_, i, "__arg" + to_string(i));
		instr("store ptr $" + pname + ", " + target);
	}
	emit_pending_temp_cleanups();
	emit_all_cleanups();
	if (indirect_result)
		terminate("return void");
	else
		terminate("return " + scalar_lowir_type(result) +
		          " $" + record_return_slot_);
	return true;
}

bool FunctionLowerer::lower_hosted_unique_ptr_destructor_body()
{
	Binding* binding = fn_.binding;
	TypePtr element;
	if (!hosted_unique_ptr_destructor_binding(binding, &element))
		return false;
	TypePtr record = hosted_member_owner_record(binding);
	record = record.get() != NULL ? pa11::strip_cv(record) : TypePtr();
	if (record.get() == NULL || record->kind != TypeKind::Record)
		return false;
	string this_name = parameter_name(out_, 0, "this");
	string self = fresh_temp();
	instr(self + " = load ptr $" + this_name);
	uint64_t pointer_offset = hosted_field_offset_or_zero(
		record, pa11::abi_private_name("M_t"));
	string pointer_addr = self;
	if (pointer_offset != 0)
	{
		pointer_addr = fresh_temp();
		instr(pointer_addr + " = index i8 [projection=field] " +
		      self + ", " + to_string(pointer_offset));
	}
	string pointer = fresh_temp();
	instr(pointer + " = load ptr " + pointer_addr);
	string has_pointer = fresh_temp();
	instr(has_pointer + " = cmp ne ptr " + pointer + ", 0");
	string delete_block = fresh_block("unique_ptr_delete");
	string done_block = fresh_block("unique_ptr_done");
	terminate("branch " + has_pointer + ", ^" + delete_block +
	          ", ^" + done_block);
	start_block(delete_block);
	lower_destructor_for_object([pointer]() { return Value("ptr", pointer); },
	                            element);
	ensure_hosted_operator_delete_declaration(program_);
	instr("call void @operator_delete(" + pointer + ")");
	terminate("jump ^" + done_block);
	start_block(done_block);
	instr("store ptr 0, " + pointer_addr);
	terminate("return void");
	return true;
}

bool FunctionLowerer::lower_hosted_unique_ptr_impl_constructor_body()
{
	Binding* binding = fn_.binding;
	if (!hosted_unique_ptr_impl_constructor_binding(binding))
		return false;
	TypePtr record = hosted_member_owner_record(binding);
	record = record.get() != NULL ? pa11::strip_cv(record) : TypePtr();
	if (record.get() == NULL || record->kind != TypeKind::Record)
		return false;
	string this_name = parameter_name(out_, 0, "this");
	string self = fresh_temp();
	instr(self + " = load ptr $" + this_name);
	uint64_t pointer_offset = hosted_field_offset_or_zero(
		record, pa11::abi_private_name("M_t"));
	auto pointer_addr = [this, pointer_offset](const string& object) -> string
	{
		if (pointer_offset == 0)
			return object;
		string addr = fresh_temp();
		instr(addr + " = index i8 [projection=field] " +
		      object + ", " + to_string(pointer_offset));
		return addr;
	};
	if (hosted_unique_ptr_impl_pointer_constructor_binding(binding))
	{
		lower_storage_zero(Value("ptr", self), pa11::type_size(record));
		string pointer_name = parameter_name(out_, 1, "__p");
		string pointer = fresh_temp();
		instr(pointer + " = load ptr $" + pointer_name);
		instr("store ptr " + pointer + ", " + pointer_addr(self));
		terminate("return void");
		return true;
	}
	string other_name = parameter_name(out_, 1, "__u");
	string other = fresh_temp();
	instr(other + " = load ptr $" + other_name);
	uint64_t size = pa11::type_size(record);
	uint64_t align = pa11::type_align(record);
	instr("copyobj " + to_string(size) + "x" + to_string(align) +
	      " " + other + ", " + self);
	instr("store ptr 0, " + pointer_addr(other));
	terminate("return void");
	return true;
}

bool FunctionLowerer::lower_hosted_unique_ptr_impl_assignment_body()
{
	Binding* binding = fn_.binding;
	if (!hosted_unique_ptr_impl_move_assignment_binding(binding))
		return false;
	TypePtr record = hosted_member_owner_record(binding);
	record = record.get() != NULL ? pa11::strip_cv(record) : TypePtr();
	if (record.get() == NULL || record->kind != TypeKind::Record)
		return false;
	TypePtr element;
	if (!record->template_arguments.empty() &&
	    record->template_arguments[0].kind ==
		    pa11::TemplateInstanceArgumentKind::Type)
		element = pa11::strip_cv(record->template_arguments[0].type);
	string this_name = parameter_name(out_, 0, "this");
	string other_name = parameter_name(out_, 1, "__u");
	string self = fresh_temp();
	instr(self + " = load ptr $" + this_name);
	string other = fresh_temp();
	instr(other + " = load ptr $" + other_name);
	uint64_t pointer_offset = hosted_field_offset_or_zero(
		record, pa11::abi_private_name("M_t"));
	auto pointer_addr = [this, pointer_offset](const string& object) -> string
	{
		if (pointer_offset == 0)
			return object;
		string addr = fresh_temp();
		instr(addr + " = index i8 [projection=field] " +
		      object + ", " + to_string(pointer_offset));
		return addr;
	};
	string self_ptr_addr = pointer_addr(self);
	string old_ptr = fresh_temp();
	instr(old_ptr + " = load ptr " + self_ptr_addr);
	string other_ptr_addr = pointer_addr(other);
	string new_ptr = fresh_temp();
	instr(new_ptr + " = load ptr " + other_ptr_addr);
	string same = fresh_temp();
	instr(same + " = cmp eq ptr " + old_ptr + ", " + new_ptr);
	string done_delete = fresh_block("unique_impl_assign_done_delete");
	string delete_check = fresh_block("unique_impl_assign_delete_check");
	terminate("branch " + same + ", ^" + done_delete + ", ^" +
	          delete_check);
	start_block(delete_check);
	string has_old = fresh_temp();
	instr(has_old + " = cmp ne ptr " + old_ptr + ", 0");
	string delete_block = fresh_block("unique_impl_assign_delete");
	terminate("branch " + has_old + ", ^" + delete_block + ", ^" +
	          done_delete);
	start_block(delete_block);
	if (element.get() != NULL)
		lower_destructor_for_object([old_ptr]() { return Value("ptr", old_ptr); },
		                            element);
	ensure_hosted_operator_delete_declaration(program_);
	instr("call void @operator_delete(" + old_ptr + ")");
	terminate("jump ^" + done_delete);
	start_block(done_delete);
	instr("store ptr " + new_ptr + ", " + self_ptr_addr);
	instr("store ptr 0, " + other_ptr_addr);
	terminate("return " + scalar_lowir_type(binding->type->base) +
	          " " + self);
	return true;
}

bool FunctionLowerer::lower_hosted_iter_equals_val_constructor_body()
{
	Binding* binding = fn_.binding;
	if (!hosted_iter_equals_val_constructor_binding(binding))
		return false;
	TypePtr record = hosted_member_owner_record(binding);
	record = record.get() != NULL ? pa11::strip_cv(record) : TypePtr();
	if (record.get() == NULL || record->kind != TypeKind::Record)
		return false;
	string this_name = parameter_name(out_, 0, "this");
	string value_name = parameter_name(out_, 1, "__value");
	string self = fresh_temp();
	instr(self + " = load ptr $" + this_name);
	lower_storage_zero(Value("ptr", self), pa11::type_size(record));
	string value = fresh_temp();
	instr(value + " = load ptr $" + value_name);
	uint64_t offset = hosted_field_offset_or_zero(
		record, pa11::abi_private_name("M_value"));
	string target = self;
	if (offset != 0)
	{
		target = fresh_temp();
		instr(target + " = index i8 [projection=field] " +
		      self + ", " + to_string(offset));
	}
	instr("store ptr " + value + ", " + target);
	terminate("return void");
	return true;
}

bool FunctionLowerer::lower_hosted_normal_iterator_member_body()
{
	Binding* binding = fn_.binding;
	TypePtr iterator;
	if (!hosted_normal_iterator_member_binding(binding) ||
	    !hosted_normal_iterator_record(hosted_member_owner_record(binding),
	                                   &iterator))
		return false;
	TypePtr element = pa11::strip_cv(iterator->base);
	if (element.get() == NULL)
		return false;
	uint64_t element_size = pa11::type_size(element);
	uint64_t current_offset = hosted_field_offset_or_zero(
		hosted_member_owner_record(binding),
		pa11::abi_private_name("M_current"));
	string this_name = parameter_name(out_, 0, "this");
	string self = fresh_temp();
	instr(self + " = load ptr $" + this_name);
	string current_addr = self;
	if (current_offset != 0)
	{
		current_addr = fresh_temp();
		instr(current_addr + " = index i8 [projection=field] " +
		      self + ", " + to_string(current_offset));
	}
	if (binding->name == "base")
	{
		terminate("return " + scalar_lowir_type(binding->type->base) +
		          " " + current_addr);
		return true;
	}
	string current = fresh_temp();
	instr(current + " = load ptr " + current_addr);
	if (binding->name == "operator*")
	{
		terminate("return " + scalar_lowir_type(binding->type->base) +
		          " " + current);
		return true;
	}
	if (binding->name == "operator++" ||
	    binding->name == "operator--")
	{
		string next = fresh_temp();
		string offset = binding->name == "operator--"
			? "-" + to_string(element_size)
			: to_string(element_size);
		instr(next + " = index i8 " + current + ", " + offset);
		instr("store ptr " + next + ", " + current_addr);
		terminate("return " + scalar_lowir_type(binding->type->base) +
		          " " + self);
		return true;
	}
	string n_name = parameter_name(out_, 1, "__n");
	TypePtr n_type = binding->type->parameters[1];
	string n_lowir_type = scalar_lowir_type(n_type);
	string n = fresh_temp();
	instr(n + " = load " + n_lowir_type + " $" + n_name);
	if (n_lowir_type != "i64")
	{
		string converted = fresh_temp();
		instr(converted + " = convert " +
		      string(is_unsigned_type(n_type) ? "zext" : "sext") +
		      " i64 " + n_lowir_type + " " + n);
		n = converted;
	}
	string bytes = fresh_temp();
	instr(bytes + " = binary mul i64 " + n + ", " +
	      to_string(element_size));
	if (binding->name == "operator-")
	{
		string negated = fresh_temp();
		instr(negated + " = binary sub i64 0, " + bytes);
		bytes = negated;
	}
	string result = fresh_temp();
	instr(result + " = index i8 " + current + ", " + bytes);
	if (record_return_by_address(binding->type->base))
	{
		instr("store ptr " + result + ", %ret");
		terminate("return void");
	}
	else
	{
		string result_slot =
			fresh_aux_slot("normal_iterator_result",
			               slot_lowir_type(binding->type->base));
		string result_addr = "$" + result_slot;
		if (current_offset != 0)
		{
			result_addr = fresh_temp();
			instr(result_addr + " = index i8 [projection=field] $" +
			      result_slot + ", " + to_string(current_offset));
		}
		instr("store ptr " + result + ", " + result_addr);
		terminate("return " + scalar_lowir_type(binding->type->base) +
		          " $" + result_slot);
	}
	return true;
}

bool FunctionLowerer::lower_hosted_normal_iterator_difference_body()
{
	Binding* binding = fn_.binding;
	TypePtr element;
	if (!hosted_normal_iterator_difference_binding(binding, &element))
		return false;
	uint64_t element_size = pa11::type_size(element);
	if (element_size == 0)
		return false;
	TypePtr lhs_record = binding->type->parameters[0];
	if (is_reference(lhs_record))
		lhs_record = lhs_record->base;
	lhs_record = pa11::strip_cv(lhs_record);
	uint64_t current_offset = hosted_field_offset_or_zero(
		lhs_record, pa11::abi_private_name("M_current"));
	string lhs_name = parameter_name(out_, 0, "__lhs");
	string rhs_name = parameter_name(out_, 1, "__rhs");
	string lhs_object = fresh_temp();
	instr(lhs_object + " = load ptr $" + lhs_name);
	string rhs_object = fresh_temp();
	instr(rhs_object + " = load ptr $" + rhs_name);
	string lhs_current_addr = lhs_object;
	string rhs_current_addr = rhs_object;
	if (current_offset != 0)
	{
		lhs_current_addr = fresh_temp();
		instr(lhs_current_addr + " = index i8 [projection=field] " +
		      lhs_object + ", " + to_string(current_offset));
		rhs_current_addr = fresh_temp();
		instr(rhs_current_addr + " = index i8 [projection=field] " +
		      rhs_object + ", " + to_string(current_offset));
	}
	string lhs_current = fresh_temp();
	instr(lhs_current + " = load ptr " + lhs_current_addr);
	string rhs_current = fresh_temp();
	instr(rhs_current + " = load ptr " + rhs_current_addr);
	string bytes = fresh_temp();
	instr(bytes + " = binary sub ptr " + lhs_current + ", " +
	      rhs_current);
	string distance = bytes;
	if (element_size != 1)
	{
		distance = fresh_temp();
		instr(distance + " = binary div i64 " + bytes + ", " +
		      to_string(element_size));
	}
	string ret_type = scalar_lowir_type(binding->type->base);
	if (ret_type != "i64")
	{
		string converted = fresh_temp();
		instr(converted + " = convert trunc " + ret_type +
		      " i64 " + distance);
		distance = converted;
	}
	terminate("return " + ret_type + " " + distance);
	return true;
}

bool FunctionLowerer::lower_hosted_ops_compare_constructor_body()
{
	Binding* binding = fn_.binding;
	if (!hosted_ops_compare_constructor_binding(binding))
		return false;
	TypePtr record = hosted_member_owner_record(binding);
	record = record.get() != NULL ? pa11::strip_cv(record) : TypePtr();
	if (record.get() == NULL || record->kind != TypeKind::Record)
		return false;
	string this_name = parameter_name(out_, 0, "this");
	string comp_name = parameter_name(out_, 1, "__comp");
	string self = fresh_temp();
	instr(self + " = load ptr $" + this_name);
	lower_storage_zero(Value("ptr", self), pa11::type_size(record));
	uint64_t offset = hosted_field_offset_or_zero(
		record, pa11::abi_private_name("M_comp"));
	string target = self;
	if (offset != 0)
	{
		target = fresh_temp();
		instr(target + " = index i8 [projection=field] " +
		      self + ", " + to_string(offset));
	}
	TypePtr arg = binding->type->parameters[1];
	TypePtr arg_record = is_reference(arg)
		? pa11::strip_cv(arg->base) : TypePtr();
	string value_type = "ptr";
	string value = fresh_temp();
	if (arg_record.get() != NULL &&
	    arg_record->kind == TypeKind::Record &&
	    hosted_ops_compare_record(arg_record))
	{
		string source = fresh_temp();
		instr(source + " = load ptr $" + comp_name);
		uint64_t source_offset = hosted_field_offset_or_zero(
			arg_record, pa11::abi_private_name("M_comp"));
		string source_field = source;
		if (source_offset != 0)
		{
			source_field = fresh_temp();
			instr(source_field + " = index i8 [projection=field] " +
			      source + ", " + to_string(source_offset));
		}
		instr(value + " = load ptr " + source_field);
	}
	else
	{
		value_type = scalar_lowir_type(arg);
		instr(value + " = load " + value_type + " $" + comp_name);
	}
	instr("store " + value_type + " " + value + ", " + target);
	terminate("return void");
	return true;
}

bool FunctionLowerer::lower_hosted_uninit_destroy_guard_constructor_body()
{
	Binding* binding = fn_.binding;
	TypePtr iterator;
	if (!hosted_uninit_destroy_guard_constructor_binding(binding) ||
	    !hosted_uninit_destroy_guard_record(
		    hosted_member_owner_record(binding), &iterator))
		return false;
	TypePtr record = hosted_member_owner_record(binding);
	record = record.get() != NULL ? pa11::strip_cv(record) : TypePtr();
	if (record.get() == NULL || record->kind != TypeKind::Record)
		return false;
	uint64_t iterator_size = max<uint64_t>(
		uint64_t(1), pa11::type_size(iterator));
	uint64_t cur_offset = (iterator_size + 7) & ~uint64_t(7);
	string this_name = parameter_name(out_, 0, "this");
	string first_name = parameter_name(out_, 1, "__first");
	string self = fresh_temp();
	instr(self + " = load ptr $" + this_name);
	lower_storage_zero(Value("ptr", self), pa11::type_size(record));
	string first_ref = fresh_temp();
	instr(first_ref + " = load ptr $" + first_name);
	string first = fresh_temp();
	instr(first + " = load ptr " + first_ref);
	instr("store ptr " + first + ", " + self);
	if (cur_offset < pa11::type_size(record))
	{
		string cur_addr = fresh_temp();
		instr(cur_addr + " = index i8 [projection=field] " +
		      self + ", " + to_string(cur_offset));
		instr("store ptr " + first_ref + ", " + cur_addr);
	}
	terminate("return void");
	return true;
}

bool FunctionLowerer::lower_hosted_uninit_destroy_guard_release_body()
{
	Binding* binding = fn_.binding;
	TypePtr iterator;
	if (!hosted_uninit_destroy_guard_release_binding(binding) ||
	    !hosted_uninit_destroy_guard_record(
		    hosted_member_owner_record(binding), &iterator))
		return false;
	TypePtr record = hosted_member_owner_record(binding);
	record = record.get() != NULL ? pa11::strip_cv(record) : TypePtr();
	if (record.get() == NULL || record->kind != TypeKind::Record)
		return false;
	uint64_t iterator_size = max<uint64_t>(
		uint64_t(1), pa11::type_size(iterator));
	uint64_t cur_offset = (iterator_size + 7) & ~uint64_t(7);
	string this_name = parameter_name(out_, 0, "this");
	string self = fresh_temp();
	instr(self + " = load ptr $" + this_name);
	if (cur_offset < pa11::type_size(record))
	{
		string cur_addr = fresh_temp();
		instr(cur_addr + " = index i8 [projection=field] " +
		      self + ", " + to_string(cur_offset));
		instr("store ptr 0, " + cur_addr);
	}
	terminate("return void");
	return true;
}

bool FunctionLowerer::lower_hosted_vector_guard_alloc_destructor_body()
{
	Binding* binding = fn_.binding;
	if (!hosted_vector_guard_alloc_destructor_binding(binding))
		return false;
	ensure_hosted_operator_delete_declaration(program_);
	string this_name = parameter_name(out_, 0, "this");
	string self = fresh_temp();
	instr(self + " = load ptr $" + this_name);
	string storage = fresh_temp();
	instr(storage + " = load ptr " + self);
	string has_storage = fresh_temp();
	instr(has_storage + " = cmp ne ptr " + storage + ", 0");
	string deallocate_block = fresh_block("guard_alloc_deallocate");
	string done_block = fresh_block("guard_alloc_done");
	terminate("branch " + has_storage + ", ^" +
	          deallocate_block + ", ^" + done_block);
	start_block(deallocate_block);
	instr("call void @operator_delete(" + storage + ")");
	terminate("jump ^" + done_block);
	start_block(done_block);
	terminate("return void");
	return true;
}

bool FunctionLowerer::lower_hosted_vector_guard_elts_destructor_body()
{
	Binding* binding = fn_.binding;
	TypePtr element;
	if (!hosted_vector_guard_elts_destructor_binding(binding) ||
	    !hosted_vector_guard_elts_record(class_record_for_member(binding),
	                                     &element))
		return false;
	if (element.get() == NULL)
		return false;
	if (!type_needs_destructor(element))
	{
		terminate("return void");
		return true;
	}
	string this_name = parameter_name(out_, 0, "this");
	string self = fresh_temp();
	instr(self + " = load ptr $" + this_name);
	string first_addr = fresh_temp();
	instr(first_addr + " = index i8 [projection=field] " +
	      self + ", 0");
	string first = fresh_temp();
	instr(first + " = load ptr " + first_addr);
	string last_addr = fresh_temp();
	instr(last_addr + " = index i8 [projection=field] " +
	      self + ", 8");
	string last = fresh_temp();
	instr(last + " = load ptr " + last_addr);
	string cur_slot = fresh_aux_slot("guard_elts_cur", "ptr");
	instr("store ptr " + first + ", $" + cur_slot);
	string check_block = fresh_block("guard_elts_check");
	string body_block = fresh_block("guard_elts_body");
	string done_block = fresh_block("guard_elts_done");
	terminate("jump ^" + check_block);
	start_block(check_block);
	string cur = fresh_temp();
	instr(cur + " = load ptr $" + cur_slot);
	string more = fresh_temp();
	instr(more + " = cmp ne ptr " + cur + ", " + last);
	terminate("branch " + more + ", ^" +
	          body_block + ", ^" + done_block);
	start_block(body_block);
	lower_destructor_for_object([cur]() { return Value("ptr", cur); },
	                            element);
	string next = fresh_temp();
	instr(next + " = index i8 " + cur + ", " +
	      to_string(pa11::type_size(element)));
	instr("store ptr " + next + ", $" + cur_slot);
	terminate("jump ^" + check_block);
	start_block(done_block);
	terminate("return void");
	return true;
}

bool FunctionLowerer::lower_hosted_uninit_destroy_guard_destructor_body()
{
	Binding* binding = fn_.binding;
	TypePtr iterator;
	if (!hosted_uninit_destroy_guard_destructor_binding(binding) ||
	    !hosted_uninit_destroy_guard_record(
		    class_record_for_member(binding), &iterator))
		return false;
	TypePtr iterator_bare = pa11::strip_cv(iterator);
	if (iterator_bare.get() == NULL ||
	    iterator_bare->kind != TypeKind::Pointer)
		return false;
	TypePtr element = pa11::strip_cv(iterator_bare->base);
	if (element.get() == NULL)
		return false;
	if (!type_needs_destructor(element))
	{
		terminate("return void");
		return true;
	}
	uint64_t iterator_size = max<uint64_t>(
		uint64_t(1), pa11::type_size(iterator));
	uint64_t cur_offset = (iterator_size + 7) & ~uint64_t(7);
	string this_name = parameter_name(out_, 0, "this");
	string self = fresh_temp();
	instr(self + " = load ptr $" + this_name);
	string cur_addr = fresh_temp();
	instr(cur_addr + " = index i8 [projection=field] " +
	      self + ", " + to_string(cur_offset));
	string cur_slot = fresh_temp();
	instr(cur_slot + " = load ptr " + cur_addr);
	string has_cur = fresh_temp();
	instr(has_cur + " = cmp ne ptr " + cur_slot + ", 0");
	string destroy_block = fresh_block("uninit_guard_destroy");
	string done_block = fresh_block("uninit_guard_done");
	terminate("branch " + has_cur + ", ^" +
	          destroy_block + ", ^" + done_block);
	start_block(destroy_block);
	string first = fresh_temp();
	instr(first + " = load ptr " + self);
	string finish = fresh_temp();
	instr(finish + " = load ptr " + cur_slot);
	string cur_storage = fresh_aux_slot("uninit_guard_cur", "ptr");
	instr("store ptr " + first + ", $" + cur_storage);
	string check_block = fresh_block("uninit_guard_check");
	string body_block = fresh_block("uninit_guard_body");
	terminate("jump ^" + check_block);
	start_block(check_block);
	string cur = fresh_temp();
	instr(cur + " = load ptr $" + cur_storage);
	string more = fresh_temp();
	instr(more + " = cmp ne ptr " + cur + ", " + finish);
	terminate("branch " + more + ", ^" +
	          body_block + ", ^" + done_block);
	start_block(body_block);
	lower_destructor_for_object([cur]() { return Value("ptr", cur); },
	                            element);
	string next = fresh_temp();
	instr(next + " = index i8 " + cur + ", " +
	      to_string(pa11::type_size(element)));
	instr("store ptr " + next + ", $" + cur_storage);
	terminate("jump ^" + check_block);
	start_block(done_block);
	terminate("return void");
	return true;
}

bool FunctionLowerer::lower_hosted_make_exception_ptr_body()
{
	Binding* binding = fn_.binding;
	if (!hosted_make_exception_ptr_binding(binding))
		return false;
	TypePtr object = pa11::strip_cv(object_type(binding->type->parameters[0]));
	if (object.get() == NULL)
		return false;
	program_.emit_typeinfo(object);
	string rtti = program_.typeid_rtti_symbol(object);
	if (rtti.empty())
		rtti = program_.catch_rtti_symbol(object);
	if (rtti.empty())
		return false;
	Binding* wrapper_ctor =
		hosted_exception_ptr_void_constructor(binding->type->base);
	ensure_throw_runtime_declarations();
	ensure_make_exception_ptr_runtime_declarations(program_);
	if (wrapper_ctor != NULL)
		program_.demand_function_declaration(wrapper_ctor);
	string allocation = fresh_temp();
	instr(allocation +
	      " = call ptr @__external_runtime____cxa_allocate_exception(" +
	      to_string(pa11::type_size(object)) + ")");
	string rtti_addr = fresh_temp();
	instr(rtti_addr + " = addr @" + rtti);
	string dtor_arg = throw_destructor_argument(object);
	string ignored = fresh_temp();
	instr(ignored +
	      " = call ptr @__external_runtime____cxa_init_primary_exception(" +
	      allocation + ", " + rtti_addr + ", " + dtor_arg + ")");
	string param_name = parameter_name(out_, 0, "__ex");
	if (object->kind == TypeKind::Record)
	{
		Binding* copy_ctor = find_copy_move_constructor(object, false);
		if (copy_ctor != NULL)
		{
			program_.demand_function_declaration(copy_ctor);
			program_.demand_inline_function(copy_ctor);
			string source = record_pass_by_address(binding->type->parameters[0])
				? "%" + param_name : "$" + param_name;
			instr("call void @" + program_.symbol_for(copy_ctor) +
			      "(" + allocation + ", " + source + ")");
		}
		else
		{
			string source = record_pass_by_address(binding->type->parameters[0])
				? "%" + param_name : "$" + param_name;
			instr("copyobj " + to_string(pa11::type_size(object)) +
			      "x" + to_string(pa11::type_align(object)) + " " +
			      source + ", " + allocation);
		}
	}
	else
	{
		string value = fresh_temp();
		instr(value + " = load " + scalar_lowir_type(object) +
		      " $" + param_name);
		instr("store " + scalar_lowir_type(object) + " " + value +
		      ", " + allocation);
	}
	if (wrapper_ctor != NULL)
		instr("call void @" + program_.symbol_for(wrapper_ctor) +
		      "(%ret, " + allocation + ")");
	else
		instr("store ptr " + allocation + ", %ret");
	terminate("return void");
	return true;
}


}  // namespace internal
}  // namespace pa14
