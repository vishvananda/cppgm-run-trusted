#include "pa14_lowir_hosted_inline_internal.h"
#include "pa12_templates_function_support.h"

namespace pa14 {
namespace internal {

string FunctionLowerer::emit_hosted_stoa_conversion_call(
	Binding* binding,
	TypePtr conv_fn,
	const string& convf,
	const string& str,
	const string& end_addr,
	const string& conv_ret_type)
{
	vector<string> args;
	args.push_back(str);
	args.push_back(end_addr);
	for (size_t i = 4; i < binding->type->parameters.size(); ++i)
	{
		string pname = parameter_name(out_, i, "__base" + to_string(i - 4));
		string value = fresh_temp();
		instr(value + " = load " +
		      scalar_lowir_type(binding->type->parameters[i]) +
		      " $" + pname);
		args.push_back(value);
	}
	string converted = fresh_temp();
	ostringstream call;
	call << converted << " = call " << conv_ret_type << " " << convf << "(";
	for (size_t i = 0; i < args.size(); ++i)
	{
		if (i != 0)
			call << ", ";
		call << args[i];
	}
	call << ") as (";
	for (size_t i = 0; i < conv_fn->parameters.size(); ++i)
	{
		if (i != 0)
			call << ", ";
		call << "%arg" << i << " : " <<
			lowir_parameter(conv_fn->parameters[i]);
	}
	call << ") -> " << conv_ret_type;
	instr(call.str());
	return converted;
}

bool FunctionLowerer::lower_hosted_equal_aux1_basic_string_body()
{
	Binding* binding = fn_.binding;
	if (!hosted_equal_aux_basic_string_binding(binding))
		return false;
	TypePtr string_record = hosted_equal_iterator_string_record(
		binding->type->parameters[0]);
	size_t string_size = pa11::type_size(string_record);
	auto iterator_pointer = [this, binding](size_t index,
	                                        const string& fallback)
	{
		string name = parameter_name(out_, index, fallback);
		TypePtr type = pa11::strip_cv(binding->type->parameters[index]);
		if (type.get() != NULL && type->kind == TypeKind::Pointer)
		{
			string value = fresh_temp();
			instr(value + " = load ptr $" + name);
			return value;
		}
		string addr = fresh_temp();
		instr(addr + " = addr $" + name);
		string value = fresh_temp();
		instr(value + " = load ptr " + addr);
		return value;
	};
	string first = iterator_pointer(0, "__first1");
	string last = iterator_pointer(1, "__last1");
	string second = iterator_pointer(2, "__first2");
	string first_slot = fresh_aux_slot("equal_first", "ptr");
	string second_slot = fresh_aux_slot("equal_second", "ptr");
	instr("store ptr " + first + ", $" + first_slot);
	instr("store ptr " + second + ", $" + second_slot);
	string loop = fresh_block("equal_loop");
	string compare = fresh_block("equal_compare");
	string success = fresh_block("equal_success");
	string failure = fresh_block("equal_failure");
	terminate("jump ^" + loop);
	start_block(loop);
	string cur_first = fresh_temp();
	instr(cur_first + " = load ptr $" + first_slot);
	string more = fresh_temp();
	instr(more + " = cmp ne ptr " + cur_first + ", " + last);
	terminate("branch " + more + ", ^" + compare + ", ^" + success);
	start_block(compare);
	string cur_second = fresh_temp();
	instr(cur_second + " = load ptr $" + second_slot);
	string len1_addr = fresh_temp();
	instr(len1_addr + " = index i8 [projection=field] " +
	      cur_first + ", 8");
	string len2_addr = fresh_temp();
	instr(len2_addr + " = index i8 [projection=field] " +
	      cur_second + ", 8");
	string len1 = fresh_temp();
	instr(len1 + " = load i64 " + len1_addr);
	string len2 = fresh_temp();
	instr(len2 + " = load i64 " + len2_addr);
	string same_len = fresh_temp();
	instr(same_len + " = cmp eq i64 " + len1 + ", " + len2);
	string bytes_init = fresh_block("equal_bytes_init");
	terminate("branch " + same_len + ", ^" + bytes_init + ", ^" +
	          failure);
	start_block(bytes_init);
	string data1 = fresh_temp();
	instr(data1 + " = load ptr " + cur_first);
	string data2 = fresh_temp();
	instr(data2 + " = load ptr " + cur_second);
	string index_slot = fresh_aux_slot("equal_index", "i64");
	instr("store i64 0, $" + index_slot);
	string byte_loop = fresh_block("equal_byte_loop");
	string byte_compare = fresh_block("equal_byte_compare");
	string advance = fresh_block("equal_advance");
	terminate("jump ^" + byte_loop);
	start_block(byte_loop);
	string index = fresh_temp();
	instr(index + " = load i64 $" + index_slot);
	string bytes_done = fresh_temp();
	instr(bytes_done + " = cmp eq i64 " + index + ", " + len1);
	terminate("branch " + bytes_done + ", ^" + advance + ", ^" +
	          byte_compare);
	start_block(byte_compare);
	string byte1_addr = fresh_temp();
	instr(byte1_addr + " = index i8 " + data1 + ", " + index);
	string byte2_addr = fresh_temp();
	instr(byte2_addr + " = index i8 " + data2 + ", " + index);
	string byte1 = fresh_temp();
	instr(byte1 + " = load u8 " + byte1_addr);
	string byte2 = fresh_temp();
	instr(byte2 + " = load u8 " + byte2_addr);
	string same_byte = fresh_temp();
	instr(same_byte + " = cmp eq u8 " + byte1 + ", " + byte2);
	string next_byte = fresh_block("equal_next_byte");
	terminate("branch " + same_byte + ", ^" + next_byte + ", ^" +
	          failure);
	start_block(next_byte);
	string next_index = fresh_temp();
	instr(next_index + " = binary add i64 " + index + ", 1");
	instr("store i64 " + next_index + ", $" + index_slot);
	terminate("jump ^" + byte_loop);
	start_block(advance);
	string next_first = fresh_temp();
	instr(next_first + " = index i8 " + cur_first + ", " +
	      to_string(string_size));
	string next_second = fresh_temp();
	instr(next_second + " = index i8 " + cur_second + ", " +
	      to_string(string_size));
	instr("store ptr " + next_first + ", $" + first_slot);
	instr("store ptr " + next_second + ", $" + second_slot);
	terminate("jump ^" + loop);
	start_block(failure);
	terminate("return " + scalar_lowir_type(binding->type->base) + " 0");
	start_block(success);
	terminate("return " + scalar_lowir_type(binding->type->base) + " 1");
	return true;
}

bool FunctionLowerer::lower_hosted_lexicographical_compare_int_body()
{
	Binding* binding = fn_.binding;
	if (!hosted_lexicographical_compare_int_binding(binding))
		return false;
	auto iterator_pointer = [this, binding](size_t index,
	                                        const string& fallback)
	{
		string name = parameter_name(out_, index, fallback);
		TypePtr type = pa11::strip_cv(binding->type->parameters[index]);
		if (type.get() != NULL && type->kind == TypeKind::Pointer)
		{
			string value = fresh_temp();
			instr(value + " = load ptr $" + name);
			return value;
		}
		string addr = fresh_temp();
		instr(addr + " = addr $" + name);
		string value = fresh_temp();
		instr(value + " = load ptr " + addr);
		return value;
	};
	string first1 = iterator_pointer(0, "__first1");
	string last1 = iterator_pointer(1, "__last1");
	string first2 = iterator_pointer(2, "__first2");
	string last2 = iterator_pointer(3, "__last2");
	string first1_slot = fresh_aux_slot("lex_first1", "ptr");
	string first2_slot = fresh_aux_slot("lex_first2", "ptr");
	instr("store ptr " + first1 + ", $" + first1_slot);
	instr("store ptr " + first2 + ", $" + first2_slot);
	string ret_type = scalar_lowir_type(binding->type->base);
	string loop = fresh_block("lex_loop");
	string first2_done_check = fresh_block("lex_first2_done_check");
	string compare = fresh_block("lex_compare");
	string less = fresh_block("lex_less");
	string greater_or_equal = fresh_block("lex_greater_or_equal");
	string greater = fresh_block("lex_greater");
	string advance = fresh_block("lex_advance");
	string first1_done = fresh_block("lex_first1_done");
	string failure = fresh_block("lex_failure");
	terminate("jump ^" + loop);
	start_block(loop);
	string cur1 = fresh_temp();
	instr(cur1 + " = load ptr $" + first1_slot);
	string done1 = fresh_temp();
	instr(done1 + " = cmp eq ptr " + cur1 + ", " + last1);
	terminate("branch " + done1 + ", ^" + first1_done + ", ^" +
	          first2_done_check);
	start_block(first1_done);
	string cur2_for_done = fresh_temp();
	instr(cur2_for_done + " = load ptr $" + first2_slot);
	string second_has_tail = fresh_temp();
	instr(second_has_tail + " = cmp ne ptr " + cur2_for_done + ", " +
	      last2);
	terminate("return " + ret_type + " " + second_has_tail);
	start_block(first2_done_check);
	string cur2 = fresh_temp();
	instr(cur2 + " = load ptr $" + first2_slot);
	string done2 = fresh_temp();
	instr(done2 + " = cmp eq ptr " + cur2 + ", " + last2);
	terminate("branch " + done2 + ", ^" + failure + ", ^" + compare);
	start_block(compare);
	string value1 = fresh_temp();
	instr(value1 + " = load i32 " + cur1);
	string value2 = fresh_temp();
	instr(value2 + " = load i32 " + cur2);
	string first_less = fresh_temp();
	instr(first_less + " = cmp lt i32 " + value1 + ", " + value2);
	terminate("branch " + first_less + ", ^" + less + ", ^" +
	          greater_or_equal);
	start_block(greater_or_equal);
	string second_less = fresh_temp();
	instr(second_less + " = cmp lt i32 " + value2 + ", " + value1);
	terminate("branch " + second_less + ", ^" + greater + ", ^" +
	          advance);
	start_block(less);
	terminate("return " + ret_type + " 1");
	start_block(greater);
	terminate("return " + ret_type + " 0");
	start_block(advance);
	string next1 = fresh_temp();
	instr(next1 + " = index i8 " + cur1 + ", 4");
	string next2 = fresh_temp();
	instr(next2 + " = index i8 " + cur2 + ", 4");
	instr("store ptr " + next1 + ", $" + first1_slot);
	instr("store ptr " + next2 + ", $" + first2_slot);
	terminate("jump ^" + loop);
	start_block(failure);
	terminate("return " + ret_type + " 0");
	return true;
}

bool FunctionLowerer::lower_hosted_uninitialized_default_n_trivial_body()
{
	Binding* binding = fn_.binding;
	if (!hosted_uninitialized_default_n_trivial_binding(binding))
		return false;
	TypePtr first_type = pa11::strip_cv(binding->type->parameters[0]);
	TypePtr element = pa11::strip_cv(first_type->base);
	uint64_t size = pa11::type_size(element);
	string first_name = parameter_name(out_, 0, "__first");
	string n_name = parameter_name(out_, 1, "__n");
	string first = fresh_temp();
	instr(first + " = load ptr $" + first_name);
	string n = fresh_temp();
	string n_type = scalar_lowir_type(binding->type->parameters[1]);
	instr(n + " = load " + n_type + " $" + n_name);
	if (n_type != "i64")
	{
		string widened = fresh_temp();
		instr(widened + " = convert zext i64 " + n_type + " " + n);
		n = widened;
	}
	string cur_slot = fresh_aux_slot("uninit_default_cur", "ptr");
	string index_slot = fresh_aux_slot("uninit_default_index", "i64");
	instr("store ptr " + first + ", $" + cur_slot);
	instr("store i64 0, $" + index_slot);
	string loop = fresh_block("uninit_default_loop");
	string body = fresh_block("uninit_default_body");
	string done = fresh_block("uninit_default_done");
	terminate("jump ^" + loop);
	start_block(loop);
	string index = fresh_temp();
	instr(index + " = load i64 $" + index_slot);
	string more = fresh_temp();
	instr(more + " = cmp ult i64 " + index + ", " + n);
	terminate("branch " + more + ", ^" + body + ", ^" + done);
	start_block(body);
	string cur = fresh_temp();
	instr(cur + " = load ptr $" + cur_slot);
	lower_storage_zero(Value("ptr", cur), size);
	string next_cur = fresh_temp();
	instr(next_cur + " = index i8 " + cur + ", " + to_string(size));
	string next_index = fresh_temp();
	instr(next_index + " = binary add i64 " + index + ", 1");
	instr("store ptr " + next_cur + ", $" + cur_slot);
	instr("store i64 " + next_index + ", $" + index_slot);
	terminate("jump ^" + loop);
	start_block(done);
	string ret = fresh_temp();
	instr(ret + " = load ptr $" + cur_slot);
	terminate("return ptr " + ret);
	return true;
}

bool FunctionLowerer::lower_hosted_stoa_body()
{
	Binding* binding = fn_.binding;
	if (!hosted_stoa_binding(binding))
		return false;
	TypePtr conv_fn = stoa_conversion_function_type(binding);
	if (conv_fn.get() == NULL)
		return false;
	ensure_stoa_runtime_declarations(program_);
	string ret_type = scalar_lowir_type(binding->type->base);
	string conv_ret_type = scalar_lowir_type(conv_fn->base);
	string convf_name = parameter_name(out_, 0, "__convf");
	string name_name = parameter_name(out_, 1, "__name");
	string str_name = parameter_name(out_, 2, "__str");
	string idx_name = parameter_name(out_, 3, "__idx");
	string convf = fresh_temp();
	instr(convf + " = load ptr $" + convf_name);
	string name = fresh_temp();
	instr(name + " = load ptr $" + name_name);
	string str = fresh_temp();
	instr(str + " = load ptr $" + str_name);
	string errno_ptr = fresh_temp();
	instr(errno_ptr +
	      " = call ptr @__external_runtime___errno_location()");
	string old_errno = fresh_temp();
	instr(old_errno + " = load i32 " + errno_ptr);
	instr("store i32 0, " + errno_ptr);
	string end_slot = fresh_aux_slot("stoa_endptr", "ptr");
	string end_addr = fresh_temp();
	instr(end_addr + " = addr $" + end_slot);
	string converted = emit_hosted_stoa_conversion_call(
		binding, conv_fn, convf, str, end_addr, conv_ret_type);
	string endptr = fresh_temp();
	instr(endptr + " = load ptr $" + end_slot);
	string errno_value = fresh_temp();
	instr(errno_value + " = load i32 " + errno_ptr);
	string errno_zero = fresh_temp();
	instr(errno_zero + " = cmp eq i32 " + errno_value + ", 0");
	string restore_errno = fresh_block("stoa_restore_errno");
	string check_digits = fresh_block("stoa_check_digits");
	terminate("branch " + errno_zero + ", ^" + restore_errno + ", ^" +
	          check_digits);
	start_block(restore_errno);
	instr("store i32 " + old_errno + ", " + errno_ptr);
	terminate("jump ^" + check_digits);
	start_block(check_digits);
	string no_digits = fresh_temp();
	instr(no_digits + " = cmp eq ptr " + endptr + ", " + str);
	string invalid = fresh_block("stoa_invalid");
	string check_range = fresh_block("stoa_check_range");
	terminate("branch " + no_digits + ", ^" + invalid + ", ^" +
	          check_range);
	start_block(invalid);
	instr("call void @__external_std___throw_invalid_argument(" + name + ")");
	terminate("return " + ret_type + " 0");
	start_block(check_range);
	string erange = fresh_temp();
	instr(erange + " = cmp eq i32 " + errno_value + ", 34");
	string out_of_range = fresh_block("stoa_out_of_range");
	string assign_value = fresh_block("stoa_assign");
	terminate("branch " + erange + ", ^" + out_of_range + ", ^" +
	          assign_value);
	bool needs_int_range =
		ret_type == "i32" &&
		conv_ret_type == "i64" &&
		!is_unsigned_type(binding->type->base);
	if (needs_int_range)
	{
		start_block(assign_value);
		string too_low = fresh_temp();
		instr(too_low + " = cmp lt " + conv_ret_type + " " +
		      converted + ", -2147483648");
		string check_high = fresh_block("stoa_check_high");
		terminate("branch " + too_low + ", ^" + out_of_range + ", ^" +
		          check_high);
		start_block(check_high);
		string too_high = fresh_temp();
		instr(too_high + " = cmp gt " + conv_ret_type + " " +
		      converted + ", 2147483647");
		assign_value = fresh_block("stoa_assign_int");
		terminate("branch " + too_high + ", ^" + out_of_range + ", ^" +
		          assign_value);
	}
	start_block(assign_value);
	string result = converted;
	if (ret_type != conv_ret_type)
	{
		result = fresh_temp();
		instr(result + " = convert trunc " + ret_type + " " +
		      conv_ret_type + " " + converted);
	}
	string idx = fresh_temp();
	instr(idx + " = load ptr $" + idx_name);
	string has_idx = fresh_temp();
	instr(has_idx + " = cmp ne ptr " + idx + ", 0");
	string store_idx = fresh_block("stoa_store_idx");
	string done = fresh_block("stoa_done");
	terminate("branch " + has_idx + ", ^" + store_idx + ", ^" + done);
	start_block(store_idx);
	string consumed = fresh_temp();
	instr(consumed + " = binary sub ptr " + endptr + ", " + str);
	instr("store i64 " + consumed + ", " + idx);
	terminate("jump ^" + done);
	start_block(out_of_range);
	instr("call void @__external_std___throw_out_of_range(" + name + ")");
	terminate("return " + ret_type + " 0");
	start_block(done);
	terminate("return " + ret_type + " " + result);
	return true;
}

bool FunctionLowerer::lower_hosted_to_address_body()
{
	Binding* binding = fn_.binding;
	if (!hosted_to_address_binding(binding))
		return false;
	string param_name = parameter_name(out_, 0, "__ptr");
	TypePtr param = binding->type->parameters[0];
	if (is_reference(param))
	{
		string ref = fresh_temp();
		instr(ref + " = load ptr $" + param_name);
		string value = fresh_temp();
		instr(value + " = load ptr " + ref);
		terminate("return ptr " + value);
		return true;
	}
	string value = fresh_temp();
	instr(value + " = load ptr $" + param_name);
	terminate("return ptr " + value);
	return true;
}

bool FunctionLowerer::lower_hosted_type_info_comparison_body()
{
	Binding* binding = fn_.binding;
	if (!hosted_type_info_comparison_binding(binding))
		return false;
	string this_name = parameter_name(out_, 0, "this");
	string rhs_name = parameter_name(out_, 1, "__rhs");
	string self = fresh_temp();
	instr(self + " = load ptr $" + this_name);
	string rhs = fresh_temp();
	instr(rhs + " = load ptr $" + rhs_name);
	string self_name_addr = fresh_temp();
	instr(self_name_addr + " = index i8 [projection=field] " +
	      self + ", 8");
	string rhs_name_addr = fresh_temp();
	instr(rhs_name_addr + " = index i8 [projection=field] " +
	      rhs + ", 8");
	string self_name = fresh_temp();
	instr(self_name + " = load ptr " + self_name_addr);
	string rhs_type_name = fresh_temp();
	instr(rhs_type_name + " = load ptr " + rhs_name_addr);
	string result = fresh_temp();
	string object = global_object_symbol(binding);
	string op = (binding->name == "operator!=" ||
	             object == "_ZNKSt9type_infoneERKS_") ? "ne" : "eq";
	instr(result + " = cmp " + op + " ptr " + self_name + ", " +
	      rhs_type_name);
	terminate("return " + scalar_lowir_type(binding->type->base) +
	          " " + result);
	return true;
}

bool FunctionLowerer::lower_hosted_iterator_comparison_body()
{
	Binding* binding = fn_.binding;
	if (!hosted_iterator_comparison_binding(binding))
		return false;
	string lhs_name = parameter_name(out_, 0, "__lhs");
	string rhs_name = parameter_name(out_, 1, "__rhs");
	string lhs_object = fresh_temp();
	instr(lhs_object + " = load ptr $" + lhs_name);
	string rhs_object = fresh_temp();
	instr(rhs_object + " = load ptr $" + rhs_name);
	string lhs_node = fresh_temp();
	instr(lhs_node + " = load ptr " + lhs_object);
	string rhs_node = fresh_temp();
	instr(rhs_node + " = load ptr " + rhs_object);
	string result = fresh_temp();
	string op = binding->name == "operator!=" ? "ne" : "eq";
	instr(result + " = cmp " + op + " ptr " + lhs_node + ", " + rhs_node);
	terminate("return " + scalar_lowir_type(binding->type->base) +
	          " " + result);
	return true;
}

bool FunctionLowerer::lower_hosted_vector_bool_s_nword_body()
{
	Binding* binding = fn_.binding;
	if (!hosted_vector_bool_s_nword_binding(binding))
		return false;
	string n_name = parameter_name(out_, 0, "__n");
	TypePtr n_type = binding->type->parameters[0];
	string lowir_type = scalar_lowir_type(n_type);
	string value = fresh_temp();
	instr(value + " = load " + lowir_type + " $" + n_name);
	if (lowir_type != "i64")
	{
		string converted = fresh_temp();
		instr(converted + " = convert " +
		      string(is_unsigned_type(n_type) ? "zext" : "sext") +
		      " i64 " + lowir_type + " " + value);
		value = converted;
	}
	string biased = fresh_temp();
	instr(biased + " = binary add i64 " + value + ", 63");
	string words = fresh_temp();
	instr(words + " = binary udiv i64 " + biased + ", 64");
	string ret_type = scalar_lowir_type(binding->type->base);
	if (ret_type != "i64")
	{
		string converted = fresh_temp();
		instr(converted + " = convert trunc " + ret_type +
		      " i64 " + words);
		words = converted;
	}
	terminate("return " + ret_type + " " + words);
	return true;
}

bool FunctionLowerer::lower_hosted_allocator_comparison_body()
{
	Binding* binding = fn_.binding;
	if (!hosted_allocator_comparison_binding(binding))
		return false;
	string result = binding->name == "operator!=" ? "0" : "1";
	terminate("return " + scalar_lowir_type(binding->type->base) +
	          " " + result);
	return true;
}

bool FunctionLowerer::lower_hosted_allocator_destroy_body()
{
	Binding* binding = fn_.binding;
	TypePtr object;
	size_t pointer_index = 0;
	if (!hosted_allocator_destroy_binding(binding, &object, &pointer_index))
		return false;
	if (type_needs_destructor(object))
	{
		string pointer_name = parameter_name(out_, pointer_index, "__p");
		string pointer = fresh_temp();
		instr(pointer + " = load ptr $" + pointer_name);
		lower_destructor_for_object(
			[pointer]() { return Value("ptr", pointer); }, object);
	}
	terminate("return void");
	return true;
}

bool FunctionLowerer::lower_hosted_alloc_traits_propagate_body()
{
	Binding* binding = fn_.binding;
	if (!hosted_alloc_traits_propagate_on_move_assign_binding(binding))
		return false;
	string result = binding->name == pa11::abi_private_name("S_always_equal")
		? "1" : "0";
	terminate("return " + scalar_lowir_type(binding->type->base) +
	          " " + result);
	return true;
}

}  // namespace internal
}  // namespace pa14
