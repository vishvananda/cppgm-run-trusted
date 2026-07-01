#include "pa14_lowir_hosted_inline_internal.h"
#include "pa12_templates_function_support.h"

namespace pa14 {
namespace internal {

bool FunctionLowerer::lower_hosted_pair_default_constructor_body()
{
	Binding* binding = fn_.binding;
	if (!hosted_pair_default_constructor_binding(binding))
		return false;
	TypePtr record = hosted_member_owner_record(binding);
	record = record.get() != NULL ? pa11::strip_cv(record) : TypePtr();
	Binding* first = hosted_pair_field(record, "first", 0);
	Binding* second = hosted_pair_field(record, "second", 1);
	if (record.get() == NULL || first == NULL || second == NULL)
		return false;
	string this_name = parameter_name(out_, 0, "this");
	string self = fresh_temp();
	instr(self + " = load ptr $" + this_name);
	Binding* fields[] = {first, second};
	for (size_t i = 0; i < 2; ++i)
	{
		Binding* field = fields[i];
		function<Value()> field_addr = [this, self, field]() {
			string addr = self;
			if (field->member_offset != 0)
			{
				addr = fresh_temp();
				instr(addr + " = index i8 [projection=field] " +
				      self + ", " +
				      to_string(field->member_offset));
			}
			return Value("ptr", addr);
		};
		lower_zero_init(field_addr, field->type);
	}
	terminate("return void");
	return true;
}

bool FunctionLowerer::lower_hosted_tree_container_default_init(
	const function<Value()>& addr_for,
	TypePtr type)
{
	TypePtr record = type.get() != NULL ? pa11::strip_cv(type) : TypePtr();
	if (!hosted_tree_container_default_record(record))
		return false;
	pa11::layout_record_type(record);
	string primary = hosted_record_primary(record);
	uint64_t header_offset = 0;
	if (primary == "set" ||
	    primary == "multiset" ||
	    primary == "map" ||
	    primary == "multimap" ||
	    primary == pa11::abi_private_name("Rb_tree") ||
	    primary == pa11::abi_private_name("Rb_tree_impl"))
		header_offset = 8;
	else if (primary != pa11::abi_private_name("Rb_tree_header"))
		return false;

	Value object = addr_for();
	lower_storage_zero(object, pa11::type_size(record));
	string header = object.text;
	if (header_offset != 0)
	{
		header = fresh_temp();
		instr(header + " = index i8 [projection=field] " +
		      object.text + ", " + to_string(header_offset));
	}
	auto field_addr = [this, header](uint64_t offset) -> string {
		if (offset == 0)
			return header;
		string addr = fresh_temp();
		instr(addr + " = index i8 [projection=field] " +
		      header + ", " + to_string(offset));
		return addr;
	};
	instr("store i32 0, " + field_addr(0));
	instr("store ptr 0, " + field_addr(8));
	instr("store ptr " + header + ", " + field_addr(16));
	instr("store ptr " + header + ", " + field_addr(24));
	instr("store i64 0, " + field_addr(32));
	return true;
}

bool FunctionLowerer::lower_hosted_pair_piecewise_index_constructor_body()
{
	Binding* binding = fn_.binding;
	if (!hosted_pair_piecewise_index_constructor_binding(binding))
		return false;
	TypePtr record = hosted_member_owner_record(binding);
	record = record.get() != NULL ? pa11::strip_cv(record) : TypePtr();
	Binding* first = hosted_pair_field(record, "first", 0);
	Binding* second = hosted_pair_field(record, "second", 1);
	TypePtr first_member_type =
		first != NULL ? first->type : hosted_pair_argument(record, 0);
	TypePtr second_member_type =
		second != NULL ? second->type : hosted_pair_argument(record, 1);
	if (record.get() == NULL ||
	    first_member_type.get() == NULL ||
	    second_member_type.get() == NULL)
		return false;
	uint64_t first_offset = first != NULL ? first->member_offset : 0;
	uint64_t second_offset = second != NULL
		? second->member_offset
		: hosted_pair_align_up(pa11::type_size(first_member_type),
		                       pa11::type_align(second_member_type));
	bool public_piecewise = binding->type->parameters.size() == 4;
	size_t tuple1_index = public_piecewise ? 2 : 1;
	TypePtr tuple1_type = object_type(binding->type->parameters[tuple1_index]);
	tuple1_type = tuple1_type.get() != NULL
		? pa11::strip_cv(tuple1_type) : TypePtr();
	bool tuple_stores_reference = true;
	if (hosted_tuple_record(tuple1_type) &&
	    !tuple1_type->template_arguments.empty() &&
	    tuple1_type->template_arguments[0].kind ==
		    pa11::TemplateInstanceArgumentKind::Type)
	{
		TypePtr tuple_element =
			tuple1_type->template_arguments[0].type;
		tuple_stores_reference = is_reference(tuple_element);
	}

	string this_name = parameter_name(out_, 0, "this");
	string tuple1_name = parameter_name(out_, tuple1_index, "__tuple1");
	string self = fresh_temp();
	instr(self + " = load ptr $" + this_name);
	auto field_addr = [this, self](uint64_t offset) -> string {
		if (offset == 0)
			return self;
		string addr = fresh_temp();
		instr(addr + " = index i8 [projection=field] " + self +
		      ", " + to_string(offset));
		return addr;
	};

	string first_addr = field_addr(first_offset);
	string tuple1;
	if (public_piecewise)
		tuple1 = "%" + tuple1_name;
	else
	{
		tuple1 = fresh_temp();
		instr(tuple1 + " = load ptr $" + tuple1_name);
	}
	string source_addr = tuple1;
	if (tuple_stores_reference)
	{
		source_addr = fresh_temp();
		instr(source_addr + " = load ptr " + tuple1);
	}

	TypePtr first_type = pa11::strip_cv(first_member_type);
	if (first_type.get() != NULL &&
	    first_type->kind == TypeKind::Record)
	{
		Binding* ctor = find_copy_move_constructor(first_type, false);
		if (ctor == NULL)
		{
			if (!record_has_storage_copy(first_type))
				return false;
			instr("copyobj " + to_string(pa11::type_size(first_type)) +
			      "x" + to_string(pa11::type_align(first_type)) +
			      " " + source_addr + ", " + first_addr);
		}
		else
		{
			program_.demand_function_declaration(ctor);
			program_.demand_inline_function(ctor);
			instr("call void @" + program_.symbol_for(ctor) +
			      "(" + first_addr + ", " + source_addr + ")");
		}
	}
	else if (is_reference(first_member_type))
	{
		string stored = tuple_stores_reference ? source_addr : fresh_temp();
		if (!tuple_stores_reference)
			instr(stored + " = load ptr " + source_addr);
		instr("store ptr " + stored + ", " + first_addr);
	}
	else
	{
		string low_type = scalar_lowir_type(first_member_type);
		string value = fresh_temp();
		instr(value + " = load " + low_type + " " + source_addr);
		instr("store " + low_type + " " + value + ", " + first_addr);
	}

	string second_addr_text = field_addr(second_offset);
	Value second_value("ptr", second_addr_text);
	TypePtr second_type = pa11::strip_cv(second_member_type);
	function<Value()> second_addr = [second_value]() {
		return second_value;
	};
	if (second_type.get() != NULL && second_type->kind == TypeKind::Record)
	{
		if (lower_hosted_vector_default_init(second_addr,
		                                      second_member_type))
		{
		}
		else if (lower_hosted_tree_container_default_init(second_addr,
		                                             second_member_type))
		{
		}
		else if (Binding* ctor = find_constructor(second_member_type, 0))
		{
			if (record_in_namespace(second_type, "std"))
			{
				vector<const Node*> args;
				lower_constructor_call(second_addr, ctor, args);
			}
			else
			{
				lower_storage_zero(second_value,
				                   pa11::type_size(second_member_type));
				lower_zero_init(second_addr, second_member_type);
			}
		}
		else
		{
			lower_storage_zero(second_value,
			                   pa11::type_size(second_member_type));
			lower_zero_init(second_addr, second_member_type);
		}
	}
	else
		lower_zero_init(second_addr, second_member_type);
	terminate("return void");
	return true;
}

bool FunctionLowerer::lower_hosted_pair_assignment_body()
{
	Binding* binding = fn_.binding;
	if (!hosted_pair_assignment_binding(binding))
		return false;
	TypePtr record = hosted_member_owner_record(binding);
	record = record.get() != NULL ? pa11::strip_cv(record) : TypePtr();
	Binding* first = hosted_pair_field(record, "first", 0);
	Binding* second = hosted_pair_field(record, "second", 1);
	if (record.get() == NULL || first == NULL || second == NULL)
		return false;
	string this_name = parameter_name(out_, 0, "this");
	string other_name = parameter_name(out_, 1, "__x");
	string self = fresh_temp();
	instr(self + " = load ptr $" + this_name);
	string other = fresh_temp();
	instr(other + " = load ptr $" + other_name);
	Binding* fields[] = {first, second};
	for (size_t i = 0; i < 2; ++i)
	{
		Binding* field = fields[i];
		string dst = self;
		string src = other;
		if (field->member_offset != 0)
		{
			dst = fresh_temp();
			instr(dst + " = index i8 [projection=field] " +
			      self + ", " + to_string(field->member_offset));
			src = fresh_temp();
			instr(src + " = index i8 [projection=field] " +
			      other + ", " + to_string(field->member_offset));
		}
		TypePtr field_type = pa11::strip_cv(field->type);
		if (field_type.get() != NULL &&
		    field_type->kind == TypeKind::Record)
		{
			Binding* assign =
				find_record_copy_move_assignment(field_type, false);
			if (assign != NULL)
			{
				program_.demand_function_declaration(assign);
				program_.demand_inline_function(assign);
				instr("call " + scalar_lowir_type(assign->type->base) +
				      " @" + program_.symbol_for(assign) +
				      "(" + dst + ", " + src + ")");
			}
			else if (record_has_storage_copy(field_type))
			{
				instr("copyobj " +
				      to_string(pa11::type_size(field_type)) +
				      "x" +
				      to_string(pa11::type_align(field_type)) +
				      " " + src + ", " + dst);
			}
			else
				return false;
			continue;
		}
		if (is_reference(field->type))
		{
			string value = fresh_temp();
			instr(value + " = load ptr " + src);
			instr("store ptr " + value + ", " + dst);
			continue;
		}
		string low_type = scalar_lowir_type(field->type);
		string value = fresh_temp();
		instr(value + " = load " + low_type + " " + src);
		instr("store " + low_type + " " + value + ", " + dst);
	}
	terminate("return " + scalar_lowir_type(binding->type->base) +
	          " " + self);
	return true;
}

}  // namespace internal
}  // namespace pa14
