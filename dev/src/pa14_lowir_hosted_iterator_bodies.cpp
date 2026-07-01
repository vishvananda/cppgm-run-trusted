#include "pa14_lowir_internal.h"
#include "pa14_lowir_function_internal.h"

namespace pa14 {
namespace internal {
namespace {

bool binding_in_namespace(const Binding* binding, const string& name)
{
	for (const Scope* scope = binding != NULL ? binding->owner : NULL;
	     scope != NULL;
	     scope = scope->parent)
		if (scope->kind == ScopeKind::Namespace && scope->name == name)
			return true;
	return false;
}

bool record_in_namespace(TypePtr record, const string& name)
{
	TypePtr bare = record.get() != NULL ? pa11::strip_cv(record) : TypePtr();
	for (const Scope* scope = bare.get() != NULL ? bare->scope : NULL;
	     scope != NULL;
	     scope = scope->parent)
		if (scope->kind == ScopeKind::Namespace && scope->name == name)
			return true;
	return false;
}

string hosted_record_primary(TypePtr record)
{
	TypePtr bare = record.get() != NULL ? pa11::strip_cv(record) : TypePtr();
	if (bare.get() == NULL)
		return "";
	string primary = bare->template_primary_name.empty()
		? bare->name : bare->template_primary_name;
	size_t args = primary.find('<');
	if (args != string::npos)
		primary = primary.substr(0, args);
	size_t pos = primary.rfind("::");
	if (pos != string::npos)
		primary = primary.substr(pos + 2);
	return primary;
}

bool hosted_iterator_comparison_record(TypePtr record)
{
	TypePtr bare = record.get() != NULL ? pa11::strip_cv(record) : TypePtr();
	if (bare.get() == NULL ||
	    bare->kind != TypeKind::Record ||
	    !record_in_namespace(bare, "std"))
		return false;
	string primary = hosted_record_primary(bare);
	return primary == pa11::abi_private_name("Rb_tree_iterator") ||
	       primary == pa11::abi_private_name("Rb_tree_const_iterator") ||
	       primary == "_Deque_iterator" ||
	       primary == "_Node_iterator" ||
	       primary == "_Node_const_iterator";
}

string parameter_name(const FunctionOut& out, size_t index,
                      const string& fallback)
{
	return index < out.parameter_names.size()
		? out.parameter_names[index] : fallback;
}

}  // namespace

bool hosted_deque_iterator_record(TypePtr record, TypePtr* element_out)
{
	TypePtr bare = record.get() != NULL ? pa11::strip_cv(record) : TypePtr();
	if (bare.get() == NULL ||
	    bare->kind != TypeKind::Record ||
	    !record_in_namespace(bare, "std") ||
	    hosted_record_primary(bare) != "_Deque_iterator" ||
	    bare->template_arguments.empty() ||
	    bare->template_arguments[0].kind !=
		    pa11::TemplateInstanceArgumentKind::Type)
		return false;
	if (element_out != NULL)
		*element_out = pa11::strip_cv(bare->template_arguments[0].type);
	return true;
}

bool hosted_allocator_comparison_binding(const Binding* binding)
{
	if (binding == NULL ||
	    (binding->name != "operator==" && binding->name != "operator!=") ||
	    binding->type.get() == NULL ||
	    binding->type->kind != TypeKind::Function ||
	    binding->type->parameters.size() != 2 ||
	    !pa11::same_type(pa11::strip_cv(binding->type->base),
	                     pa11::make_fundamental(FT_BOOL)) ||
	    !binding_in_namespace(binding, "std"))
		return false;
	TypePtr lhs = binding->type->parameters[0];
	TypePtr rhs = binding->type->parameters[1];
	if (is_reference(lhs))
		lhs = lhs->base;
	if (is_reference(rhs))
		rhs = rhs->base;
	lhs = pa11::strip_cv(lhs);
	rhs = pa11::strip_cv(rhs);
	return hosted_record_primary(lhs) == "allocator" &&
	       hosted_record_primary(rhs) == "allocator";
}

bool hosted_iterator_comparison_binding(const Binding* binding)
{
	if (binding == NULL ||
	    (binding->name != "operator==" && binding->name != "operator!=") ||
	    binding->type.get() == NULL ||
	    binding->type->kind != TypeKind::Function ||
	    binding->type->parameters.size() != 2 ||
	    !pa11::same_type(pa11::strip_cv(binding->type->base),
	                     pa11::make_fundamental(FT_BOOL)) ||
	    !binding_in_namespace(binding, "std"))
		return false;
	TypePtr lhs = binding->type->parameters[0];
	TypePtr rhs = binding->type->parameters[1];
	if (is_reference(lhs))
		lhs = lhs->base;
	if (is_reference(rhs))
		rhs = rhs->base;
	lhs = pa11::strip_cv(lhs);
	rhs = pa11::strip_cv(rhs);
	return hosted_iterator_comparison_record(lhs) &&
	       hosted_iterator_comparison_record(rhs) &&
	       pa11::same_type(lhs, rhs);
}

bool hosted_deque_iterator_difference_binding(const Binding* binding,
                                              TypePtr* element_out)
{
	if (binding == NULL ||
	    binding->type.get() == NULL ||
	    binding->type->kind != TypeKind::Function ||
	    binding->type->parameters.size() != 2 ||
	    !pa11::is_integral_or_bool_type(binding->type->base) ||
	    !binding_in_namespace(binding, "std"))
		return false;
	string object = global_object_symbol(binding);
	if (binding->name != "operator-" &&
	    object.compare(0, 24, "_ZStmiRKSt15_Deque_iterator") != 0)
		return false;
	TypePtr lhs = binding->type->parameters[0];
	TypePtr rhs = binding->type->parameters[1];
	if (is_reference(lhs))
		lhs = lhs->base;
	if (is_reference(rhs))
		rhs = rhs->base;
	lhs = pa11::strip_cv(lhs);
	rhs = pa11::strip_cv(rhs);
	TypePtr element;
	if (!hosted_deque_iterator_record(lhs, &element) ||
	    !hosted_deque_iterator_record(rhs, NULL) ||
	    !pa11::same_type(lhs, rhs))
		return false;
	if (element_out != NULL)
		*element_out = element;
	return true;
}

bool hosted_deque_iterator_order_binding(const Binding* binding)
{
	if (binding == NULL ||
	    binding->type.get() == NULL ||
	    binding->type->kind != TypeKind::Function ||
	    binding->type->parameters.size() != 2 ||
	    !pa11::same_type(pa11::strip_cv(binding->type->base),
	                     pa11::make_fundamental(FT_BOOL)) ||
	    !binding_in_namespace(binding, "std"))
		return false;
	if (binding->name != "operator<" &&
	    binding->name != "operator<=" &&
	    binding->name != "operator>" &&
	    binding->name != "operator>=")
		return false;
	TypePtr lhs = binding->type->parameters[0];
	TypePtr rhs = binding->type->parameters[1];
	if (is_reference(lhs))
		lhs = lhs->base;
	if (is_reference(rhs))
		rhs = rhs->base;
	lhs = pa11::strip_cv(lhs);
	rhs = pa11::strip_cv(rhs);
	return hosted_deque_iterator_record(lhs, NULL) &&
	       hosted_deque_iterator_record(rhs, NULL) &&
	       pa11::same_type(lhs, rhs);
}

bool hosted_deque_iterator_plus_binding(const Binding* binding,
                                        TypePtr* element_out,
                                        size_t* n_index_out,
                                        size_t* iterator_index_out)
{
	if (binding == NULL ||
	    (binding->name != "operator+" && binding->name != "operator-") ||
	    binding->type.get() == NULL ||
	    binding->type->kind != TypeKind::Function ||
	    binding->type->parameters.size() != 2 ||
	    !record_return_by_address(binding->type->base) ||
	    !binding_in_namespace(binding, "std"))
		return false;
	TypePtr result = pa11::strip_cv(binding->type->base);
	if (!hosted_deque_iterator_record(result, NULL))
		return false;
	for (size_t i = 0; i < 2; ++i)
	{
		size_t other = i == 0 ? 1 : 0;
		TypePtr ntype = pa11::strip_cv(binding->type->parameters[i]);
		TypePtr iterator = binding->type->parameters[other];
		if (is_reference(iterator))
			iterator = iterator->base;
		iterator = pa11::strip_cv(iterator);
		TypePtr element;
		if (!pa11::is_integral_or_bool_type(ntype) ||
		    !hosted_deque_iterator_record(iterator, &element) ||
		    !pa11::same_type(iterator, result))
			continue;
		if (element_out != NULL)
			*element_out = element;
		if (n_index_out != NULL)
			*n_index_out = i;
		if (iterator_index_out != NULL)
			*iterator_index_out = other;
		return true;
	}
	return false;
}

bool hosted_deque_iterator_minus_n_binding(const Binding* binding,
                                           TypePtr* element_out)
{
	if (binding == NULL ||
	    binding->name != "operator-" ||
	    binding->type.get() == NULL ||
	    binding->type->kind != TypeKind::Function ||
	    binding->type->parameters.size() != 2 ||
	    !record_return_by_address(binding->type->base) ||
	    !binding_in_namespace(binding, "std"))
		return false;
	TypePtr result = pa11::strip_cv(binding->type->base);
	if (!hosted_deque_iterator_record(result, NULL))
		return false;
	TypePtr iterator = binding->type->parameters[0];
	if (is_reference(iterator))
		iterator = iterator->base;
	iterator = pa11::strip_cv(iterator);
	TypePtr ntype = pa11::strip_cv(binding->type->parameters[1]);
	TypePtr element;
	if (!hosted_deque_iterator_record(iterator, &element) ||
	    !pa11::same_type(iterator, result) ||
	    !pa11::is_integral_or_bool_type(ntype))
		return false;
	if (element_out != NULL)
		*element_out = element;
	return true;
}

bool hosted_bit_iterator_base_record(TypePtr record)
{
	TypePtr bare = record.get() != NULL ? pa11::strip_cv(record) : TypePtr();
	if (bare.get() == NULL ||
	    bare->kind != TypeKind::Record ||
	    !record_in_namespace(bare, "std"))
		return false;
	try
	{
		pa11::layout_record_type(bare);
	}
	catch (const runtime_error&)
	{
		return false;
	}
	if (bare->fields.size() < 2 || pa11::type_size(bare) != 16)
		return false;
	TypePtr word = pa11::strip_cv(bare->fields[0]->type);
	TypePtr offset = pa11::strip_cv(bare->fields[1]->type);
	return word.get() != NULL &&
	       word->kind == TypeKind::Pointer &&
	       pa11::is_integral_or_bool_type(offset) &&
	       pa11::type_size(offset) == 4;
}

bool hosted_bit_iterator_record(TypePtr record)
{
	TypePtr bare = record.get() != NULL ? pa11::strip_cv(record) : TypePtr();
	if (bare.get() == NULL ||
	    bare->kind != TypeKind::Record ||
	    !record_in_namespace(bare, "std"))
		return false;
	vector<TypePtr> bases = pa11::record_direct_bases(bare);
	for (size_t i = 0; i < bases.size(); ++i)
		if (hosted_bit_iterator_base_record(bases[i]))
			return true;
	return false;
}

bool hosted_bit_const_iterator_record(TypePtr record)
{
	TypePtr bare = record.get() != NULL ? pa11::strip_cv(record) : TypePtr();
	return bare.get() != NULL &&
	       bare->kind == TypeKind::Record &&
	       record_in_namespace(bare, "std") &&
	       hosted_bit_iterator_record(bare);
}

bool hosted_bit_const_iterator_deref_binding(const Binding* binding)
{
	if (binding == NULL ||
	    binding->name != "operator*" ||
	    binding->type.get() == NULL ||
	    binding->type->kind != TypeKind::Function ||
	    binding->type->parameters.size() != 1 ||
	    !pa11::same_type(pa11::strip_cv(binding->type->base),
	                     pa11::make_fundamental(FT_BOOL)))
		return false;
	return hosted_bit_const_iterator_record(class_record_for_member(binding));
}

bool hosted_bit_const_iterator_preincrement_binding(const Binding* binding)
{
	if (binding == NULL ||
	    binding->name != "operator++" ||
	    binding->type.get() == NULL ||
	    binding->type->kind != TypeKind::Function ||
	    binding->type->parameters.size() != 1 ||
	    binding->type->base.get() == NULL ||
	    binding->type->base->kind != TypeKind::LValueReference)
		return false;
	TypePtr record = class_record_for_member(binding);
	return hosted_bit_const_iterator_record(record) &&
	       pa11::same_type(pa11::strip_cv(binding->type->base->base),
	                       pa11::strip_cv(record));
}

bool hosted_bit_iterator_base_comparison_binding(const Binding* binding)
{
	if (binding == NULL ||
	    (binding->name != "operator==" && binding->name != "operator!=") ||
	    binding->type.get() == NULL ||
	    binding->type->kind != TypeKind::Function ||
	    binding->type->parameters.size() != 2 ||
	    !pa11::same_type(pa11::strip_cv(binding->type->base),
	                     pa11::make_fundamental(FT_BOOL)) ||
	    !binding_in_namespace(binding, "std"))
		return false;
	TypePtr lhs = binding->type->parameters[0];
	TypePtr rhs = binding->type->parameters[1];
	if (is_reference(lhs))
		lhs = lhs->base;
	if (is_reference(rhs))
		rhs = rhs->base;
	lhs = pa11::strip_cv(lhs);
	rhs = pa11::strip_cv(rhs);
	return hosted_bit_iterator_base_record(lhs) &&
	       hosted_bit_iterator_base_record(rhs);
}

bool hosted_bit_iterator_base_difference_binding(const Binding* binding)
{
	if (binding == NULL ||
	    binding->name != "operator-" ||
	    binding->type.get() == NULL ||
	    binding->type->kind != TypeKind::Function ||
	    binding->type->parameters.size() != 2 ||
	    !pa11::is_integral_or_bool_type(binding->type->base) ||
	    !binding_in_namespace(binding, "std"))
		return false;
	TypePtr lhs = binding->type->parameters[0];
	TypePtr rhs = binding->type->parameters[1];
	if (is_reference(lhs))
		lhs = lhs->base;
	if (is_reference(rhs))
		rhs = rhs->base;
	lhs = pa11::strip_cv(lhs);
	rhs = pa11::strip_cv(rhs);
	return hosted_bit_iterator_base_record(lhs) &&
	       hosted_bit_iterator_base_record(rhs);
}

bool hosted_bit_iterator_plus_binding(const Binding* binding,
                                      size_t* iterator_index_out,
                                      size_t* n_index_out)
{
	if (binding == NULL ||
	    (binding->name != "operator+" && binding->name != "operator-") ||
	    binding->type.get() == NULL ||
	    binding->type->kind != TypeKind::Function ||
	    binding->type->parameters.size() != 2 ||
	    !hosted_bit_iterator_record(binding->type->base) ||
	    !binding_in_namespace(binding, "std"))
		return false;
	for (size_t i = 0; i < 2; ++i)
	{
		size_t other = i == 0 ? 1 : 0;
		if (binding->name == "operator-" && i != 0)
			continue;
		TypePtr iterator = binding->type->parameters[i];
		if (is_reference(iterator))
			iterator = iterator->base;
		iterator = pa11::strip_cv(iterator);
		TypePtr ntype = pa11::strip_cv(binding->type->parameters[other]);
		if (!hosted_bit_iterator_record(iterator) ||
		    !pa11::is_integral_or_bool_type(ntype))
			continue;
		if (iterator_index_out != NULL)
			*iterator_index_out = i;
		if (n_index_out != NULL)
			*n_index_out = other;
		return true;
	}
	return false;
}
bool FunctionLowerer::lower_hosted_deque_iterator_difference_body()
{
	Binding* binding = fn_.binding;
	TypePtr element;
	if (!hosted_deque_iterator_difference_binding(binding, &element))
		return false;
	size_t element_size = pa11::type_size(element);
	if (element_size == 0)
		return false;
	size_t buffer_size = element_size < 512 ? 512 / element_size : 1;
	string lhs_name = parameter_name(out_, 0, "__lhs");
	string rhs_name = parameter_name(out_, 1, "__rhs");
	string lhs_object = fresh_temp();
	instr(lhs_object + " = load ptr $" + lhs_name);
	string rhs_object = fresh_temp();
	instr(rhs_object + " = load ptr $" + rhs_name);
	string lhs_cur = fresh_temp();
	instr(lhs_cur + " = load ptr " + lhs_object);
	string rhs_cur = fresh_temp();
	instr(rhs_cur + " = load ptr " + rhs_object);
	string lhs_first_addr = fresh_temp();
	instr(lhs_first_addr + " = index i8 [projection=field] " +
	      lhs_object + ", 8");
	string lhs_first = fresh_temp();
	instr(lhs_first + " = load ptr " + lhs_first_addr);
	string rhs_last_addr = fresh_temp();
	instr(rhs_last_addr + " = index i8 [projection=field] " +
	      rhs_object + ", 16");
	string rhs_last = fresh_temp();
	instr(rhs_last + " = load ptr " + rhs_last_addr);
	string lhs_node_addr = fresh_temp();
	instr(lhs_node_addr + " = index i8 [projection=field] " +
	      lhs_object + ", 24");
	string lhs_node = fresh_temp();
	instr(lhs_node + " = load ptr " + lhs_node_addr);
	string rhs_node_addr = fresh_temp();
	instr(rhs_node_addr + " = index i8 [projection=field] " +
	      rhs_object + ", 24");
	string rhs_node = fresh_temp();
	instr(rhs_node + " = load ptr " + rhs_node_addr);
	string node_bytes = fresh_temp();
	instr(node_bytes + " = binary sub ptr " + lhs_node + ", " + rhs_node);
	string node_count = fresh_temp();
	instr(node_count + " = binary div i64 " + node_bytes + ", 8");
	string between_nodes = fresh_temp();
	instr(between_nodes + " = binary sub i64 " + node_count + ", 1");
	string middle = fresh_temp();
	instr(middle + " = binary mul i64 " + between_nodes + ", " +
	      to_string(buffer_size));
	string lhs_bytes = fresh_temp();
	instr(lhs_bytes + " = binary sub ptr " + lhs_cur + ", " + lhs_first);
	string lhs_offset = fresh_temp();
	instr(lhs_offset + " = binary div i64 " + lhs_bytes + ", " +
	      to_string(element_size));
	string rhs_bytes = fresh_temp();
	instr(rhs_bytes + " = binary sub ptr " + rhs_last + ", " + rhs_cur);
	string rhs_tail = fresh_temp();
	instr(rhs_tail + " = binary div i64 " + rhs_bytes + ", " +
	      to_string(element_size));
	string with_lhs = fresh_temp();
	instr(with_lhs + " = binary add i64 " + middle + ", " + lhs_offset);
	string total = fresh_temp();
	instr(total + " = binary add i64 " + with_lhs + ", " + rhs_tail);
	string ret_type = scalar_lowir_type(binding->type->base);
	if (ret_type != "i64")
	{
		string converted = fresh_temp();
		instr(converted + " = convert trunc " + ret_type + " i64 " +
		      total);
		total = converted;
	}
	terminate("return " + ret_type + " " + total);
	return true;
}

bool FunctionLowerer::lower_hosted_deque_iterator_order_body()
{
	Binding* binding = fn_.binding;
	if (!hosted_deque_iterator_order_binding(binding))
		return false;
	string lhs_name = parameter_name(out_, 0, "__lhs");
	string rhs_name = parameter_name(out_, 1, "__rhs");
	string lhs_object = fresh_temp();
	instr(lhs_object + " = load ptr $" + lhs_name);
	string rhs_object = fresh_temp();
	instr(rhs_object + " = load ptr $" + rhs_name);
	string lhs_cur = fresh_temp();
	instr(lhs_cur + " = load ptr " + lhs_object);
	string rhs_cur = fresh_temp();
	instr(rhs_cur + " = load ptr " + rhs_object);
	string lhs_node_addr = fresh_temp();
	instr(lhs_node_addr + " = index i8 [projection=field] " +
	      lhs_object + ", 24");
	string lhs_node = fresh_temp();
	instr(lhs_node + " = load ptr " + lhs_node_addr);
	string rhs_node_addr = fresh_temp();
	instr(rhs_node_addr + " = index i8 [projection=field] " +
	      rhs_object + ", 24");
	string rhs_node = fresh_temp();
	instr(rhs_node + " = load ptr " + rhs_node_addr);
	string same_node = fresh_temp();
	instr(same_node + " = cmp eq ptr " + lhs_node + ", " + rhs_node);
	string same_block = fresh_block("deque_cmp_same_node");
	string other_block = fresh_block("deque_cmp_other_node");
	string done_block = fresh_block("deque_cmp_done");
	string result_slot = fresh_aux_slot("deque_cmp_result", "u8");
	terminate("branch " + same_node + ", ^" + same_block + ", ^" +
	          other_block);
	start_block(same_block);
	string cur_cmp = fresh_temp();
	string same_op = "ult";
	if (binding->name == "operator<=")
		same_op = "ule";
	else if (binding->name == "operator>")
		same_op = "ugt";
	else if (binding->name == "operator>=")
		same_op = "uge";
	instr(cur_cmp + " = cmp " + same_op + " ptr " + lhs_cur + ", " +
	      rhs_cur);
	instr("store u8 " + cur_cmp + ", $" + result_slot);
	terminate("jump ^" + done_block);
	start_block(other_block);
	string node_cmp = fresh_temp();
	string node_op = (binding->name == "operator>" ||
	                  binding->name == "operator>=") ? "ugt" : "ult";
	instr(node_cmp + " = cmp " + node_op + " ptr " + lhs_node + ", " +
	      rhs_node);
	instr("store u8 " + node_cmp + ", $" + result_slot);
	terminate("jump ^" + done_block);
	start_block(done_block);
	string result = fresh_temp();
	instr(result + " = load u8 $" + result_slot);
	terminate("return " + scalar_lowir_type(binding->type->base) +
	          " " + result);
	return true;
}

bool FunctionLowerer::lower_hosted_deque_iterator_plus_body()
{
	Binding* binding = fn_.binding;
	TypePtr element;
	size_t n_index = 0;
	size_t iterator_index = 0;
	if (!hosted_deque_iterator_plus_binding(
		    binding, &element, &n_index, &iterator_index))
		return false;
	size_t element_size = pa11::type_size(element);
	if (element_size == 0)
		return false;
	size_t buffer_size = element_size < 512 ? 512 / element_size : 1;
	string n_name = parameter_name(out_, n_index, "__n");
	string iterator_name = parameter_name(out_, iterator_index, "__x");
	TypePtr n_type = binding->type->parameters[n_index];
	string n_lowir_type = scalar_lowir_type(n_type);
	string n_value = fresh_temp();
	instr(n_value + " = load " + n_lowir_type + " $" + n_name);
	if (n_lowir_type != "i64")
	{
		string converted = fresh_temp();
		instr(converted + " = convert " +
		      string(is_unsigned_type(n_type) ? "zext" : "sext") +
		      " i64 " + n_lowir_type + " " + n_value);
		n_value = converted;
	}
	if (binding->name == "operator-")
	{
		string negated = fresh_temp();
		instr(negated + " = binary sub i64 0, " + n_value);
		n_value = negated;
	}
	string source = fresh_temp();
	instr(source + " = load ptr $" + iterator_name);
	string cur = fresh_temp();
	instr(cur + " = load ptr " + source);
	string first_addr = fresh_temp();
	instr(first_addr + " = index i8 [projection=field] " + source + ", 8");
	string first = fresh_temp();
	instr(first + " = load ptr " + first_addr);
	string last_addr = fresh_temp();
	instr(last_addr + " = index i8 [projection=field] " + source + ", 16");
	string last = fresh_temp();
	instr(last + " = load ptr " + last_addr);
	string node_addr = fresh_temp();
	instr(node_addr + " = index i8 [projection=field] " + source + ", 24");
	string node = fresh_temp();
	instr(node + " = load ptr " + node_addr);
	string cur_bytes = fresh_temp();
	instr(cur_bytes + " = binary sub ptr " + cur + ", " + first);
	string cur_offset = fresh_temp();
	instr(cur_offset + " = binary div i64 " + cur_bytes + ", " +
	      to_string(element_size));
	string offset = fresh_temp();
	instr(offset + " = binary add i64 " + n_value + ", " + cur_offset);
	string nonnegative = fresh_temp();
	instr(nonnegative + " = cmp ge i64 " + offset + ", 0");
	string check_high = fresh_block("deque_plus_check_high");
	string same_node = fresh_block("deque_plus_same_node");
	string far_node = fresh_block("deque_plus_far_node");
	terminate("branch " + nonnegative + ", ^" + check_high + ", ^" +
	          far_node);
	start_block(check_high);
	string in_buffer = fresh_temp();
	instr(in_buffer + " = cmp lt i64 " + offset + ", " +
	      to_string(buffer_size));
	terminate("branch " + in_buffer + ", ^" + same_node + ", ^" +
	          far_node);
	auto store_result = [this](const string& result_cur,
	                          const string& result_first,
	                          const string& result_last,
	                          const string& result_node)
	{
		instr("store ptr " + result_cur + ", %ret");
		string first_field = fresh_temp();
		instr(first_field + " = index i8 [projection=field] %ret, 8");
		instr("store ptr " + result_first + ", " + first_field);
		string last_field = fresh_temp();
		instr(last_field + " = index i8 [projection=field] %ret, 16");
		instr("store ptr " + result_last + ", " + last_field);
		string node_field = fresh_temp();
		instr(node_field + " = index i8 [projection=field] %ret, 24");
		instr("store ptr " + result_node + ", " + node_field);
	};
	start_block(same_node);
	string delta_bytes = fresh_temp();
	instr(delta_bytes + " = binary mul i64 " + n_value + ", " +
	      to_string(element_size));
	string same_cur = fresh_temp();
	instr(same_cur + " = index i8 " + cur + ", " + delta_bytes);
	store_result(same_cur, first, last, node);
	terminate("return void");
	start_block(far_node);
	string positive_offset = fresh_temp();
	instr(positive_offset + " = cmp gt i64 " + offset + ", 0");
	string positive_node = fresh_block("deque_plus_positive_node");
	string negative_node = fresh_block("deque_plus_negative_node");
	string have_node_offset = fresh_block("deque_plus_have_node_offset");
	string node_offset_slot = fresh_aux_slot("deque_node_offset", "i64");
	terminate("branch " + positive_offset + ", ^" + positive_node + ", ^" +
	          negative_node);
	start_block(positive_node);
	string positive_node_offset = fresh_temp();
	instr(positive_node_offset + " = binary div i64 " + offset + ", " +
	      to_string(buffer_size));
	instr("store i64 " + positive_node_offset + ", $" + node_offset_slot);
	terminate("jump ^" + have_node_offset);
	start_block(negative_node);
	string negated = fresh_temp();
	instr(negated + " = binary sub i64 0, " + offset);
	string adjusted = fresh_temp();
	instr(adjusted + " = binary sub i64 " + negated + ", 1");
	string divided = fresh_temp();
	instr(divided + " = binary div i64 " + adjusted + ", " +
	      to_string(buffer_size));
	string neg_divided = fresh_temp();
	instr(neg_divided + " = binary sub i64 0, " + divided);
	string negative_node_offset = fresh_temp();
	instr(negative_node_offset + " = binary sub i64 " + neg_divided +
	      ", 1");
	instr("store i64 " + negative_node_offset + ", $" + node_offset_slot);
	terminate("jump ^" + have_node_offset);
	start_block(have_node_offset);
	string node_offset = fresh_temp();
	instr(node_offset + " = load i64 $" + node_offset_slot);
	string node_offset_bytes = fresh_temp();
	instr(node_offset_bytes + " = binary mul i64 " + node_offset + ", 8");
	string new_node = fresh_temp();
	instr(new_node + " = index i8 " + node + ", " + node_offset_bytes);
	string new_first = fresh_temp();
	instr(new_first + " = load ptr " + new_node);
	string new_last = fresh_temp();
	instr(new_last + " = index i8 " + new_first + ", " +
	      to_string(buffer_size * element_size));
	string consumed = fresh_temp();
	instr(consumed + " = binary mul i64 " + node_offset + ", " +
	      to_string(buffer_size));
	string new_offset = fresh_temp();
	instr(new_offset + " = binary sub i64 " + offset + ", " + consumed);
	string new_cur_bytes = fresh_temp();
	instr(new_cur_bytes + " = binary mul i64 " + new_offset + ", " +
	      to_string(element_size));
	string new_cur = fresh_temp();
	instr(new_cur + " = index i8 " + new_first + ", " + new_cur_bytes);
	store_result(new_cur, new_first, new_last, new_node);
	terminate("return void");
	return true;
}

bool FunctionLowerer::lower_hosted_bit_iterator_base_comparison_body()
{
	Binding* binding = fn_.binding;
	if (!hosted_bit_iterator_base_comparison_binding(binding))
		return false;
	string lhs_name = parameter_name(out_, 0, "__lhs");
	string rhs_name = parameter_name(out_, 1, "__rhs");
	string lhs_object = fresh_temp();
	instr(lhs_object + " = load ptr $" + lhs_name);
	string rhs_object = fresh_temp();
	instr(rhs_object + " = load ptr $" + rhs_name);
	string lhs_word = fresh_temp();
	instr(lhs_word + " = load ptr " + lhs_object);
	string rhs_word = fresh_temp();
	instr(rhs_word + " = load ptr " + rhs_object);
	string word_cmp = fresh_temp();
	string word_op = binding->name == "operator!=" ? "ne" : "eq";
	instr(word_cmp + " = cmp " + word_op + " ptr " + lhs_word + ", " +
	      rhs_word);
	string result_slot = fresh_aux_slot("bit_cmp_result", "u8");
	string offset_block = fresh_block("bit_cmp_offset");
	string done_block = fresh_block("bit_cmp_done");
	if (binding->name == "operator!=")
	{
		string word_same = fresh_temp();
		instr(word_same + " = cmp eq ptr " + lhs_word + ", " + rhs_word);
		string word_diff = fresh_block("bit_cmp_word_diff");
		terminate("branch " + word_same + ", ^" + offset_block + ", ^" +
		          word_diff);
		start_block(word_diff);
		instr("store u8 1, $" + result_slot);
		terminate("jump ^" + done_block);
	}
	else
	{
		string word_diff = fresh_block("bit_cmp_word_diff");
		terminate("branch " + word_cmp + ", ^" + offset_block + ", ^" +
		          word_diff);
		start_block(word_diff);
		instr("store u8 0, $" + result_slot);
		terminate("jump ^" + done_block);
	}
	start_block(offset_block);
	string lhs_offset_addr = fresh_temp();
	instr(lhs_offset_addr + " = index i8 [projection=field] " +
	      lhs_object + ", 8");
	string rhs_offset_addr = fresh_temp();
	instr(rhs_offset_addr + " = index i8 [projection=field] " +
	      rhs_object + ", 8");
	string lhs_offset = fresh_temp();
	instr(lhs_offset + " = load u32 " + lhs_offset_addr);
	string rhs_offset = fresh_temp();
	instr(rhs_offset + " = load u32 " + rhs_offset_addr);
	string offset_cmp = fresh_temp();
	string offset_op = binding->name == "operator!=" ? "ne" : "eq";
	instr(offset_cmp + " = cmp " + offset_op + " u32 " + lhs_offset +
	      ", " + rhs_offset);
	instr("store u8 " + offset_cmp + ", $" + result_slot);
	terminate("jump ^" + done_block);
	start_block(done_block);
	string result = fresh_temp();
	instr(result + " = load u8 $" + result_slot);
	terminate("return " + scalar_lowir_type(binding->type->base) +
	          " " + result);
	return true;
}

bool FunctionLowerer::lower_hosted_bit_const_iterator_deref_body()
{
	Binding* binding = fn_.binding;
	if (!hosted_bit_const_iterator_deref_binding(binding))
		return false;
	string this_name = parameter_name(out_, 0, "this");
	string self = fresh_temp();
	instr(self + " = load ptr $" + this_name);
	string word_ptr = fresh_temp();
	instr(word_ptr + " = load ptr " + self);
	string word = fresh_temp();
	instr(word + " = load i64 " + word_ptr);
	string offset_addr = fresh_temp();
	instr(offset_addr + " = index i8 [projection=field] " + self + ", 8");
	string offset32 = fresh_temp();
	instr(offset32 + " = load u32 " + offset_addr);
	string offset = fresh_temp();
	instr(offset + " = convert zext i64 u32 " + offset32);
	string mask = fresh_temp();
	instr(mask + " = binary shl i64 1, " + offset);
	string masked = fresh_temp();
	instr(masked + " = binary and i64 " + word + ", " + mask);
	string result = fresh_temp();
	instr(result + " = cmp ne i64 " + masked + ", 0");
	terminate("return " + scalar_lowir_type(binding->type->base) +
	          " " + result);
	return true;
}

bool FunctionLowerer::lower_hosted_bit_const_iterator_preincrement_body()
{
	Binding* binding = fn_.binding;
	if (!hosted_bit_const_iterator_preincrement_binding(binding))
		return false;
	string this_name = parameter_name(out_, 0, "this");
	string self = fresh_temp();
	instr(self + " = load ptr $" + this_name);
	string offset_addr = fresh_temp();
	instr(offset_addr + " = index i8 [projection=field] " + self + ", 8");
	string offset = fresh_temp();
	instr(offset + " = load u32 " + offset_addr);
	string at_last_bit = fresh_temp();
	instr(at_last_bit + " = cmp eq u32 " + offset + ", 63");
	string next_word = fresh_block("bit_const_iter_next_word");
	string same_word = fresh_block("bit_const_iter_same_word");
	string done = fresh_block("bit_const_iter_done");
	terminate("branch " + at_last_bit + ", ^" + next_word + ", ^" +
	          same_word);
	start_block(next_word);
	string word_ptr = fresh_temp();
	instr(word_ptr + " = load ptr " + self);
	string advanced_word = fresh_temp();
	instr(advanced_word + " = index i8 " + word_ptr + ", 8");
	instr("store ptr " + advanced_word + ", " + self);
	instr("store u32 0, " + offset_addr);
	terminate("jump ^" + done);
	start_block(same_word);
	string incremented = fresh_temp();
	instr(incremented + " = binary add u32 " + offset + ", 1");
	instr("store u32 " + incremented + ", " + offset_addr);
	terminate("jump ^" + done);
	start_block(done);
	terminate("return " + scalar_lowir_type(binding->type->base) +
	          " " + self);
	return true;
}

bool FunctionLowerer::lower_hosted_bit_iterator_base_difference_body()
{
	Binding* binding = fn_.binding;
	if (!hosted_bit_iterator_base_difference_binding(binding))
		return false;
	string lhs_name = parameter_name(out_, 0, "__lhs");
	string rhs_name = parameter_name(out_, 1, "__rhs");
	string lhs_object = fresh_temp();
	instr(lhs_object + " = load ptr $" + lhs_name);
	string rhs_object = fresh_temp();
	instr(rhs_object + " = load ptr $" + rhs_name);
	string lhs_word = fresh_temp();
	instr(lhs_word + " = load ptr " + lhs_object);
	string rhs_word = fresh_temp();
	instr(rhs_word + " = load ptr " + rhs_object);
	string word_bytes = fresh_temp();
	instr(word_bytes + " = binary sub ptr " + lhs_word + ", " + rhs_word);
	string word_count = fresh_temp();
	instr(word_count + " = binary div i64 " + word_bytes + ", 8");
	string bit_words = fresh_temp();
	instr(bit_words + " = binary mul i64 " + word_count + ", 64");
	string lhs_offset_addr = fresh_temp();
	instr(lhs_offset_addr + " = index i8 [projection=field] " +
	      lhs_object + ", 8");
	string rhs_offset_addr = fresh_temp();
	instr(rhs_offset_addr + " = index i8 [projection=field] " +
	      rhs_object + ", 8");
	string lhs_offset32 = fresh_temp();
	instr(lhs_offset32 + " = load u32 " + lhs_offset_addr);
	string rhs_offset32 = fresh_temp();
	instr(rhs_offset32 + " = load u32 " + rhs_offset_addr);
	string lhs_offset = fresh_temp();
	instr(lhs_offset + " = convert zext i64 u32 " + lhs_offset32);
	string rhs_offset = fresh_temp();
	instr(rhs_offset + " = convert zext i64 u32 " + rhs_offset32);
	string offset_delta = fresh_temp();
	instr(offset_delta + " = binary sub i64 " + lhs_offset + ", " +
	      rhs_offset);
	string total = fresh_temp();
	instr(total + " = binary add i64 " + bit_words + ", " + offset_delta);
	string ret_type = scalar_lowir_type(binding->type->base);
	if (ret_type != "i64")
	{
		string converted = fresh_temp();
		instr(converted + " = convert trunc " + ret_type + " i64 " +
		      total);
		total = converted;
	}
	terminate("return " + ret_type + " " + total);
	return true;
}

bool FunctionLowerer::lower_hosted_bit_iterator_plus_body()
{
	Binding* binding = fn_.binding;
	size_t iterator_index = 0;
	size_t n_index = 0;
	if (!hosted_bit_iterator_plus_binding(binding, &iterator_index, &n_index))
		return false;
	string iterator_name = parameter_name(out_, iterator_index, "__x");
	string n_name = parameter_name(out_, n_index, "__n");
	TypePtr iterator_param = binding->type->parameters[iterator_index];
	TypePtr n_type = binding->type->parameters[n_index];
	string source;
	if (is_reference(iterator_param) || record_pass_by_address(iterator_param))
	{
		source = fresh_temp();
		instr(source + " = load ptr $" + iterator_name);
	}
	else
		source = "$" + iterator_name;
	string word = fresh_temp();
	instr(word + " = load ptr " + source);
	string offset_addr = fresh_temp();
	instr(offset_addr + " = index i8 [projection=field] " + source + ", 8");
	string offset32 = fresh_temp();
	instr(offset32 + " = load u32 " + offset_addr);
	string offset64 = fresh_temp();
	instr(offset64 + " = convert zext i64 u32 " + offset32);
	string n_lowir_type = scalar_lowir_type(n_type);
	string n_value = fresh_temp();
	instr(n_value + " = load " + n_lowir_type + " $" + n_name);
	if (n_lowir_type != "i64")
	{
		string converted = fresh_temp();
		instr(converted + " = convert " +
		      string(is_unsigned_type(n_type) ? "zext" : "sext") +
		      " i64 " + n_lowir_type + " " + n_value);
		n_value = converted;
	}
	if (binding->name == "operator-")
	{
		string negated = fresh_temp();
		instr(negated + " = binary sub i64 0, " + n_value);
		n_value = negated;
	}
	string bit_index = fresh_temp();
	instr(bit_index + " = binary add i64 " + offset64 + ", " + n_value);
	string word_offset = fresh_temp();
	instr(word_offset + " = binary div i64 " + bit_index + ", 64");
	string bit_offset = fresh_temp();
	instr(bit_offset + " = binary mod i64 " + bit_index + ", 64");
	string negative = fresh_temp();
	instr(negative + " = cmp lt i64 " + bit_offset + ", 0");
	string adjust_block = fresh_block("bit_plus_adjust");
	string unadjusted_block = fresh_block("bit_plus_unadjusted");
	string have_offsets = fresh_block("bit_plus_have_offsets");
	string word_offset_slot = fresh_aux_slot("bit_word_offset", "i64");
	string bit_offset_slot = fresh_aux_slot("bit_offset", "i64");
	terminate("branch " + negative + ", ^" + adjust_block + ", ^" +
	          unadjusted_block);
	start_block(adjust_block);
	string adjusted_bit = fresh_temp();
	instr(adjusted_bit + " = binary add i64 " + bit_offset + ", 64");
	string adjusted_word = fresh_temp();
	instr(adjusted_word + " = binary sub i64 " + word_offset + ", 1");
	instr("store i64 " + adjusted_word + ", $" + word_offset_slot);
	instr("store i64 " + adjusted_bit + ", $" + bit_offset_slot);
	terminate("jump ^" + have_offsets);
	start_block(unadjusted_block);
	instr("store i64 " + word_offset + ", $" + word_offset_slot);
	instr("store i64 " + bit_offset + ", $" + bit_offset_slot);
	terminate("jump ^" + have_offsets);
	start_block(have_offsets);
	string final_word_offset = fresh_temp();
	instr(final_word_offset + " = load i64 $" + word_offset_slot);
	string final_bit_offset = fresh_temp();
	instr(final_bit_offset + " = load i64 $" + bit_offset_slot);
	string word_bytes = fresh_temp();
	instr(word_bytes + " = binary mul i64 " + final_word_offset + ", 8");
	string result_word = fresh_temp();
	instr(result_word + " = index i8 " + word + ", " + word_bytes);
	string result_offset32 = fresh_temp();
	instr(result_offset32 + " = convert trunc u32 i64 " +
	      final_bit_offset);
	bool indirect_result = record_return_by_address(binding->type->base);
	string result_slot;
	string result_addr = "%ret";
	if (!indirect_result)
	{
		result_slot = fresh_aux_slot(
			"bit_iter_ret", slot_lowir_type(binding->type->base));
		result_addr = "$" + result_slot;
	}
	instr("store ptr " + result_word + ", " + result_addr);
	string result_offset_addr = fresh_temp();
	instr(result_offset_addr + " = index i8 [projection=field] " +
	      result_addr + ", 8");
	instr("store u32 " + result_offset32 + ", " + result_offset_addr);
	if (indirect_result)
		terminate("return void");
	else
		terminate("return " + scalar_lowir_type(binding->type->base) +
		          " $" + result_slot);
	return true;
}

}  // namespace internal
}  // namespace pa14
