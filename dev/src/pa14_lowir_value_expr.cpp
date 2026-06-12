#include "pa14_lowir_internal.h"
namespace pa14 {
namespace internal {

void FunctionLowerer::emit_builtin_va_start(const Node& expr)
{
	if (expr.children.size() < 3)
		throw runtime_error("invalid __builtin_va_start");
	Value list_addr = ensure_pointer(emit_lvalue_addr(expr.children[1]));
	string tag_slot = fresh_aux_slot("va_list", "obj<24x8>");
	string tag_addr = fresh_temp();
	instr(tag_addr + " = addr $" + tag_slot);
	instr("store ptr " + tag_addr + ", " + list_addr.text);
	instr("va_start " + tag_addr);
}

Value FunctionLowerer::emit_builtin_va_arg(const Node& expr)
{
	if (expr.children.size() != 1)
		throw runtime_error("invalid __builtin_va_arg");
	Value list = convert_value(emit_rvalue(expr.children[0]),
	                           expr.children[0].type,
	                           pa11::make_pointer(
		                           pa11::make_fundamental(FT_VOID)));
	string out = fresh_temp();
	instr(out + " = va_arg " + scalar_lowir_type(expr.type) + " " +
	      list.text);
	return Value(scalar_lowir_type(expr.type), out);
}

Value FunctionLowerer::emit_builtin_alloca(const Node& expr)
{
	if (expr.children.size() < 2)
		throw runtime_error("invalid __builtin_alloca");
	Value raw_size = emit_rvalue(expr.children[1]);
	Value size = convert_value(raw_size,
	                           expr.children[1].type,
	                           pa11::make_fundamental(FT_UNSIGNED_LONG_INT));
	string out = fresh_temp();
	instr(out + " = stackalloc i64 " + size.text);
	return Value("ptr", out);
}

Value FunctionLowerer::emit_c11_atomic_builtin(const Node& expr)
{
	if (expr.direct_call == NULL)
		throw runtime_error("invalid atomic builtin");
	const string& name = expr.direct_call->name;
	if (name == "__c11_atomic_thread_fence" ||
	    name == "__c11_atomic_signal_fence")
		return Value("void", "");
	if (name == "__c11_atomic_is_lock_free")
		return Value(scalar_lowir_type(expr.type), "1");
	if (expr.children.size() < 2)
		throw runtime_error("invalid atomic builtin");
	Value ptr = ensure_pointer(emit_rvalue(expr.children[1]));
	TypePtr ptr_type = pa11::strip_cv(expr.children[1].type);
	if (ptr_type->kind != TypeKind::Pointer)
		throw runtime_error("invalid atomic pointer");
	TypePtr object = pa11::strip_cv(ptr_type->base);
	string low_type = scalar_lowir_type(object);
	if (name == "__c11_atomic_load")
	{
		string loaded = fresh_temp();
		instr(loaded + " = load " + low_type + " " + ptr.text);
		return Value(low_type, loaded);
	}
	if (name == "__c11_atomic_init" || name == "__c11_atomic_store")
	{
		if (expr.children.size() < 3)
			throw runtime_error("invalid atomic store");
		Value raw = emit_rvalue(expr.children[2]);
		Value value = convert_value(raw, expr.children[2].type, object);
		instr("store " + low_type + " " + value.text + ", " + ptr.text);
		return Value("void", "");
	}
	if (name == "__c11_atomic_exchange")
	{
		if (expr.children.size() < 3)
			throw runtime_error("invalid atomic exchange");
		string oldv = fresh_temp();
		instr(oldv + " = load " + low_type + " " + ptr.text);
		Value raw = emit_rvalue(expr.children[2]);
		Value value = convert_value(raw, expr.children[2].type, object);
		instr("store " + low_type + " " + value.text + ", " + ptr.text);
		return Value(low_type, oldv);
	}
	if (name == "__c11_atomic_fetch_add" ||
	    name == "__c11_atomic_fetch_sub" ||
	    name == "__c11_atomic_fetch_and" ||
	    name == "__c11_atomic_fetch_or" ||
	    name == "__c11_atomic_fetch_xor")
	{
		if (expr.children.size() < 3)
			throw runtime_error("invalid atomic fetch");
		string oldv = fresh_temp();
		instr(oldv + " = load " + low_type + " " + ptr.text);
		Value raw = emit_rvalue(expr.children[2]);
		Value rhs = convert_value(raw, expr.children[2].type, object);
		string op = name == "__c11_atomic_fetch_add" ? "add" :
		            name == "__c11_atomic_fetch_sub" ? "sub" :
		            name == "__c11_atomic_fetch_and" ? "and" :
		            name == "__c11_atomic_fetch_or" ? "or" : "xor";
		string next = fresh_temp();
		instr(next + " = binary " + op + " " + low_type + " " +
		      oldv + ", " + rhs.text);
		instr("store " + low_type + " " + next + ", " + ptr.text);
		return Value(low_type, oldv);
	}
	if (name == "__c11_atomic_compare_exchange_strong" ||
	    name == "__c11_atomic_compare_exchange_weak")
	{
		if (expr.children.size() < 4)
			throw runtime_error("invalid atomic compare exchange");
		Value expected_ptr = ensure_pointer(emit_rvalue(expr.children[2]));
		string cur = fresh_temp();
		instr(cur + " = load " + low_type + " " + ptr.text);
		string expected = fresh_temp();
		instr(expected + " = load " + low_type + " " + expected_ptr.text);
		string ok = fresh_temp();
		instr(ok + " = cmp eq " + low_type + " " + cur + ", " + expected);
		Value desired_raw = emit_rvalue(expr.children[3]);
		Value desired = convert_value(desired_raw,
		                              expr.children[3].type,
		                              object);
		string success = fresh_block("atomic_cas_success");
		string failure = fresh_block("atomic_cas_failure");
		string end = fresh_block("atomic_cas_end");
		string slot = fresh_aux_slot("atomic_cas", scalar_lowir_type(expr.type));
		terminate("branch " + ok + ", ^" + success + ", ^" + failure);
		start_block(success);
		instr("store " + low_type + " " + desired.text + ", " + ptr.text);
		instr("store " + scalar_lowir_type(expr.type) + " 1, $" + slot);
		terminate("jump ^" + end);
		start_block(failure);
		instr("store " + low_type + " " + cur + ", " + expected_ptr.text);
		instr("store " + scalar_lowir_type(expr.type) + " 0, $" + slot);
		terminate("jump ^" + end);
		start_block(end);
		string result = fresh_temp();
		instr(result + " = load " + scalar_lowir_type(expr.type) +
		      " $" + slot);
		return Value(scalar_lowir_type(expr.type), result);
	}
	throw runtime_error("unsupported atomic builtin");
}

Value FunctionLowerer::emit_gnu_atomic_builtin(const Node& expr)
{
	if (expr.direct_call == NULL)
		throw runtime_error("invalid atomic builtin");
	const string& name = expr.direct_call->name;
	if (name == "__atomic_always_lock_free" ||
	    name == "__atomic_is_lock_free")
		return Value(scalar_lowir_type(expr.type), "1");
	if (expr.children.size() < 2)
		throw runtime_error("invalid atomic builtin");
	Value ptr = ensure_pointer(emit_rvalue(expr.children[1]));
	TypePtr ptr_type = pa11::strip_cv(expr.children[1].type);
	if (ptr_type->kind != TypeKind::Pointer)
		throw runtime_error("invalid atomic pointer");
	TypePtr object = pa11::strip_cv(ptr_type->base);
	string low_type = scalar_lowir_type(object);
	if (name == "__atomic_load_n")
	{
		string loaded = fresh_temp();
		instr(loaded + " = load " + low_type + " " + ptr.text);
		return Value(low_type, loaded);
	}
	if (name == "__atomic_load")
	{
		if (expr.children.size() < 3)
			throw runtime_error("invalid atomic load");
		Value out_ptr = ensure_pointer(emit_rvalue(expr.children[2]));
		string loaded = fresh_temp();
		instr(loaded + " = load " + low_type + " " + ptr.text);
		instr("store " + low_type + " " + loaded + ", " + out_ptr.text);
		return Value("void", "");
	}
	if (name == "__atomic_store_n")
	{
		if (expr.children.size() < 3)
			throw runtime_error("invalid atomic store");
		Value raw = emit_rvalue(expr.children[2]);
		Value value = convert_value(raw, expr.children[2].type, object);
		instr("store " + low_type + " " + value.text + ", " + ptr.text);
		return Value("void", "");
	}
	if (name == "__atomic_store")
	{
		if (expr.children.size() < 3)
			throw runtime_error("invalid atomic store");
		Value value_ptr = ensure_pointer(emit_rvalue(expr.children[2]));
		string loaded = fresh_temp();
		instr(loaded + " = load " + low_type + " " + value_ptr.text);
		instr("store " + low_type + " " + loaded + ", " + ptr.text);
		return Value("void", "");
	}
	if (name == "__sync_lock_release")
	{
		instr("store " + low_type + " 0, " + ptr.text);
		return Value("void", "");
	}
	if (name == "__atomic_exchange_n" ||
	    name == "__sync_lock_test_and_set")
	{
		if (expr.children.size() < 3)
			throw runtime_error("invalid atomic exchange");
		string oldv = fresh_temp();
		instr(oldv + " = load " + low_type + " " + ptr.text);
		Value raw = emit_rvalue(expr.children[2]);
		Value value = convert_value(raw, expr.children[2].type, object);
		instr("store " + low_type + " " + value.text + ", " + ptr.text);
		return Value(low_type, oldv);
	}
	if (name == "__atomic_fetch_add" ||
	    name == "__atomic_fetch_sub" ||
	    name == "__atomic_fetch_and" ||
	    name == "__atomic_fetch_or" ||
	    name == "__atomic_fetch_xor" ||
	    name == "__atomic_add_fetch" ||
	    name == "__atomic_sub_fetch" ||
	    name == "__atomic_and_fetch" ||
	    name == "__atomic_or_fetch" ||
	    name == "__atomic_xor_fetch")
	{
		if (expr.children.size() < 3)
			throw runtime_error("invalid atomic fetch");
		string oldv = fresh_temp();
		instr(oldv + " = load " + low_type + " " + ptr.text);
		Value raw = emit_rvalue(expr.children[2]);
		Value rhs = convert_value(raw, expr.children[2].type, object);
		string op;
		if (name.find("_add") != string::npos ||
		    name.find("add_") != string::npos)
			op = "add";
		else if (name.find("_sub") != string::npos ||
		         name.find("sub_") != string::npos)
			op = "sub";
		else if (name.find("_and") != string::npos ||
		         name.find("and_") != string::npos)
			op = "and";
		else if (name.find("_or") != string::npos ||
		         name.find("or_") != string::npos)
			op = "or";
		else
			op = "xor";
		string next = fresh_temp();
		instr(next + " = binary " + op + " " + low_type + " " +
		      oldv + ", " + rhs.text);
		instr("store " + low_type + " " + next + ", " + ptr.text);
		if (name.find("_fetch") != string::npos &&
		    name.find("fetch_") == string::npos)
			return Value(low_type, next);
		return Value(low_type, oldv);
	}
	throw runtime_error("unsupported atomic builtin");
}

Value FunctionLowerer::emit_builtin_bit_count(const Node& expr)
{
	if (expr.direct_call == NULL || expr.children.size() < 2)
		throw runtime_error("invalid bit builtin");
	const string& name = expr.direct_call->name;
	Value raw = emit_rvalue(expr.children[1]);
	TypePtr arg_type = pa11::strip_cv(strip_for_value(expr.children[1].type));
	string low_type = scalar_lowir_type(arg_type);
	string result_type = scalar_lowir_type(expr.type);
	unsigned width = static_cast<unsigned>(pa11::type_size(arg_type) * 8);
	Value fallback;
	if (name == "__builtin_clzg" && expr.children.size() >= 3)
		fallback = convert_value(emit_rvalue(expr.children[2]),
		                         expr.children[2].type,
		                         expr.type);
	string value_slot = fresh_aux_slot("bit_count_value", low_type);
	string count_slot = fresh_aux_slot("bit_count_result", result_type);
	instr("store " + low_type + " " + raw.text + ", $" + value_slot);
	instr("store " + result_type + " 0, $" + count_slot);
	string value = fresh_temp();
	instr(value + " = load " + low_type + " $" + value_slot);
	if (name.find("popcount") != string::npos)
	{
		string loop = fresh_block("popcount_loop");
		string body = fresh_block("popcount_body");
		string end = fresh_block("popcount_end");
		terminate("jump ^" + loop);
		start_block(loop);
		string cur = fresh_temp();
		instr(cur + " = load " + low_type + " $" + value_slot);
		string more = fresh_temp();
		instr(more + " = cmp ne " + low_type + " " + cur + ", 0");
		terminate("branch " + more + ", ^" + body + ", ^" + end);
		start_block(body);
		string bit = fresh_temp();
		instr(bit + " = binary and " + low_type + " " + cur + ", 1");
		Value bit_value = convert_value(Value(low_type, bit),
		                                expr.children[1].type,
		                                expr.type);
		string count = fresh_temp();
		instr(count + " = load " + result_type + " $" + count_slot);
		string next_count = fresh_temp();
		instr(next_count + " = binary add " + result_type + " " +
		      count + ", " + bit_value.text);
		instr("store " + result_type + " " + next_count +
		      ", $" + count_slot);
		string shifted = fresh_temp();
		instr(shifted + " = binary ushr " + low_type + " " + cur + ", 1");
		instr("store " + low_type + " " + shifted + ", $" + value_slot);
		terminate("jump ^" + loop);
		start_block(end);
		string result = fresh_temp();
		instr(result + " = load " + result_type + " $" + count_slot);
		return Value(result_type, result);
	}
	string zero = fresh_temp();
	instr(zero + " = cmp eq " + low_type + " " + value + ", 0");
	string zero_block = fresh_block("bit_count_zero");
	string loop = fresh_block("bit_count_loop");
	string body = fresh_block("bit_count_body");
	string end = fresh_block("bit_count_end");
	terminate("branch " + zero + ", ^" + zero_block + ", ^" + loop);
	start_block(zero_block);
	if (name == "__builtin_clzg" && !fallback.text.empty())
		instr("store " + result_type + " " + fallback.text +
		      ", $" + count_slot);
	else
		instr("store " + result_type + " " + to_string(width) +
		      ", $" + count_slot);
	terminate("jump ^" + end);
	start_block(loop);
	string cur = fresh_temp();
	instr(cur + " = load " + low_type + " $" + value_slot);
	string probe = fresh_temp();
	if (name.find("ctz") != string::npos)
		instr(probe + " = binary and " + low_type + " " + cur + ", 1");
	else
		instr(probe + " = binary and " + low_type + " " + cur + ", " +
		      to_string(uint64_t(1) << (width - 1)));
	string done = fresh_temp();
	instr(done + " = cmp ne " + low_type + " " + probe + ", 0");
	terminate("branch " + done + ", ^" + end + ", ^" + body);
	start_block(body);
	string count = fresh_temp();
	instr(count + " = load " + result_type + " $" + count_slot);
	string next_count = fresh_temp();
	instr(next_count + " = binary add " + result_type + " " +
	      count + ", 1");
	instr("store " + result_type + " " + next_count + ", $" + count_slot);
	string shifted = fresh_temp();
	if (name.find("ctz") != string::npos)
		instr(shifted + " = binary ushr " + low_type + " " + cur + ", 1");
	else
		instr(shifted + " = binary shl " + low_type + " " + cur + ", 1");
	instr("store " + low_type + " " + shifted + ", $" + value_slot);
	terminate("jump ^" + loop);
	start_block(end);
	string result = fresh_temp();
	instr(result + " = load " + result_type + " $" + count_slot);
	return Value(result_type, result);
}

Value FunctionLowerer::emit_builtin_assume_aligned(const Node& expr)
{
	if (expr.children.size() < 3)
		throw runtime_error("invalid __builtin_assume_aligned");
	Value pointer = emit_rvalue(expr.children[1]);
	for (size_t i = 2; i < expr.children.size(); ++i)
		emit_rvalue(expr.children[i]);
	return convert_value(pointer, expr.children[1].type, expr.type);
}

Value FunctionLowerer::emit_builtin_prefetch(const Node& expr)
{
	for (size_t i = 1; i < expr.children.size(); ++i)
		emit_rvalue(expr.children[i]);
	return Value("void", "");
}

Value FunctionLowerer::emit_builtin_operator_new_delete(const Node& expr)
{
	if (expr.direct_call == NULL || expr.children.size() < 2)
		throw runtime_error("invalid builtin operator new/delete");
	const string& name = expr.direct_call->name;
	if (name == "__builtin_operator_new")
	{
		if (program_.declared_functions.insert("operator_new").second)
			program_.declares.push_back(
				"declare function @operator_new(%arg0 : i64) -> ptr "
				"[binding=strong, object=" +
				string(program_.native_lowering
				       ? "_Znwm"
				       : "cppgm_builtin_operator_new") + "]");
		Value raw_size = emit_rvalue(expr.children[1]);
		Value size = convert_value(raw_size,
		                           expr.children[1].type,
		                           pa11::make_fundamental(
			                           FT_UNSIGNED_LONG_INT));
		for (size_t i = 2; i < expr.children.size(); ++i)
			emit_rvalue(expr.children[i]);
		string out = fresh_temp();
		instr(out + " = call ptr @operator_new(" + size.text + ")");
		return Value("ptr", out);
	}
	if (program_.declared_functions.insert("operator_delete").second)
		program_.declares.push_back(
			"declare function @operator_delete(%arg0 : ptr) -> void "
			"[unwind=no, binding=strong, object=" +
			string(program_.native_lowering
			       ? "_ZdlPv"
			       : "cppgm_builtin_operator_delete") + "]");
	Value raw_pointer = emit_rvalue(expr.children[1]);
	Value pointer = convert_value(
		raw_pointer,
		expr.children[1].type,
		pa11::make_pointer(pa11::make_fundamental(FT_VOID)));
	for (size_t i = 2; i < expr.children.size(); ++i)
		emit_rvalue(expr.children[i]);
	instr("call void @operator_delete(" + pointer.text + ")");
	return Value("void", "");
}

Value FunctionLowerer::emit_builtin_overflow(const Node& expr)
{
	if (expr.direct_call == NULL || expr.children.size() != 4)
		throw runtime_error("invalid overflow builtin");
	TypePtr out_ptr = pa11::strip_cv(strip_for_value(expr.children[3].type));
	if (out_ptr->kind != TypeKind::Pointer)
		throw runtime_error("overflow result is not pointer");
	TypePtr result_type = pa11::strip_cv(out_ptr->base);
	string low_type = scalar_lowir_type(result_type);
	Value lhs_raw = emit_rvalue(expr.children[1]);
	Value rhs_raw = emit_rvalue(expr.children[2]);
	Value out_raw = ensure_pointer(emit_rvalue(expr.children[3]));
	string out_slot = fresh_aux_slot("overflow_out", "ptr");
	instr("store ptr " + out_raw.text + ", $" + out_slot);
	Value lhs = convert_value(lhs_raw, expr.children[1].type, result_type);
	Value rhs = convert_value(rhs_raw, expr.children[2].type, result_type);
	string op = expr.direct_call->name == "__builtin_sub_overflow"
		? "sub"
		: expr.direct_call->name == "__builtin_mul_overflow" ? "mul" : "add";
	string result = fresh_temp();
	instr(result + " = binary " + op + " " + low_type + " " +
	      lhs.text + ", " + rhs.text);
	string result_slot = fresh_aux_slot("overflow_result", low_type);
	instr("store " + low_type + " " + result + ", $" + result_slot);
	string out_addr = fresh_temp();
	instr(out_addr + " = load ptr $" + out_slot);
	instr("store " + low_type + " $" + result_slot + ", " + out_addr);
	string overflow = fresh_temp();
	if (op == "mul" && is_unsigned_type(result_type))
	{
		string rhs_zero = fresh_temp();
		instr(rhs_zero + " = cmp eq " + low_type + " " + rhs.text + ", 0");
		string zero = fresh_block("overflow_mul_zero");
		string check = fresh_block("overflow_mul_check");
		string end = fresh_block("overflow_mul_end");
		string slot = fresh_aux_slot("overflow", "u8");
		terminate("branch " + rhs_zero + ", ^" + zero + ", ^" + check);
		start_block(zero);
		instr("store u8 0, $" + slot);
		terminate("jump ^" + end);
		start_block(check);
		string div = fresh_temp();
		instr(div + " = binary udiv " + low_type + " " + result +
		      ", " + rhs.text);
		string cmp = fresh_temp();
		instr(cmp + " = cmp ne " + low_type + " " + div + ", " +
		      lhs.text);
		instr("store u8 " + cmp + ", $" + slot);
		terminate("jump ^" + end);
		start_block(end);
		string loaded = fresh_temp();
		instr(loaded + " = load u8 $" + slot);
		return Value("u8", loaded);
	}
	if (op == "add" && is_unsigned_type(result_type))
		instr(overflow + " = cmp ult " + low_type + " " + result +
		      ", " + lhs.text);
	else if (op == "sub" && is_unsigned_type(result_type))
		instr(overflow + " = cmp ult " + low_type + " " + lhs.text +
		      ", " + rhs.text);
	else if (op == "add" || op == "sub")
	{
		string x1 = fresh_temp();
		string x2 = fresh_temp();
		string both = fresh_temp();
		if (op == "add")
		{
			instr(x1 + " = binary xor " + low_type + " " +
			      lhs.text + ", " + result);
			instr(x2 + " = binary xor " + low_type + " " +
			      rhs.text + ", " + result);
		}
		else
		{
			instr(x1 + " = binary xor " + low_type + " " +
			      lhs.text + ", " + rhs.text);
			instr(x2 + " = binary xor " + low_type + " " +
			      lhs.text + ", " + result);
		}
		instr(both + " = binary and " + low_type + " " + x1 +
		      ", " + x2);
		instr(overflow + " = cmp lt " + low_type + " " + both +
		      ", 0");
	}
	else
		instr(overflow + " = cmp ne " + low_type + " " + result +
		      ", " + result);
	return Value("u8", overflow);
}

Value FunctionLowerer::emit_builtin_flt_rounds(const Node& expr)
{
	(void)expr;
	return Value("i32", "1");
}

Value FunctionLowerer::emit_builtin_fpclassify(const Node& expr)
{
	if (expr.children.size() != 7)
		throw runtime_error("invalid __builtin_fpclassify");
	vector<Value> classes;
	for (size_t i = 1; i <= 5; ++i)
		classes.push_back(convert_value(emit_rvalue(expr.children[i]),
		                                expr.children[i].type,
		                                expr.type));
	Value value = emit_rvalue(expr.children[6]);
	string value_type = scalar_lowir_type(expr.children[6].type);
	string slot = fresh_aux_slot("fpclassify", scalar_lowir_type(expr.type));
	string is_zero = fresh_temp();
	instr(is_zero + " = cmp eq " + value_type + " " + value.text +
	      ", 0.0");
	string zero_block = fresh_block("fpclassify_zero");
	string nonzero_block = fresh_block("fpclassify_nonzero");
	string normal_block = fresh_block("fpclassify_normal");
	string nan_block = fresh_block("fpclassify_nan");
	string end = fresh_block("fpclassify_end");
	terminate("branch " + is_zero + ", ^" + zero_block + ", ^" +
	          nonzero_block);
	start_block(zero_block);
	instr("store " + scalar_lowir_type(expr.type) + " " +
	      classes[4].text + ", $" + slot);
	terminate("jump ^" + end);
	start_block(nonzero_block);
	string ordered = fresh_temp();
	instr(ordered + " = cmp eq " + value_type + " " + value.text +
	      ", " + value.text);
	terminate("branch " + ordered + ", ^" + normal_block + ", ^" +
	          nan_block);
	start_block(normal_block);
	instr("store " + scalar_lowir_type(expr.type) + " " +
	      classes[2].text + ", $" + slot);
	terminate("jump ^" + end);
	start_block(nan_block);
	instr("store " + scalar_lowir_type(expr.type) + " " +
	      classes[0].text + ", $" + slot);
	terminate("jump ^" + end);
	start_block(end);
	string result = fresh_temp();
	instr(result + " = load " + scalar_lowir_type(expr.type) +
	      " $" + slot);
	return Value(scalar_lowir_type(expr.type), result);
}

Value FunctionLowerer::emit_builtin_float_constant(const Node& expr)
{
	if (expr.direct_call == NULL)
		throw runtime_error("invalid floating builtin");
	for (size_t i = 1; i < expr.children.size(); ++i)
		emit_rvalue(expr.children[i]);
	string type = scalar_lowir_type(expr.type);
	string name = expr.direct_call->name;
	bool nan = name.find("nan") != string::npos;
	return Value(type, nan ? "nan" : "inf");
}

Value FunctionLowerer::convert_member_pointer_value(Value value,
                                                    TypePtr from,
                                                    TypePtr to,
                                                    const string& dst,
                                                    const string& src) {
	TypePtr from_bare = pa11::strip_cv(strip_for_value(from));
	TypePtr to_bare = pa11::strip_cv(strip_for_value(to));
	TypePtr member_type = pa11::strip_cv(from_bare->base);
	if (member_type->kind != TypeKind::Function &&
	    !pa11::same_type(pa11::strip_cv(from_bare->member_class),
	                     pa11::strip_cv(to_bare->member_class)) &&
	    record_has_base_subobject(to_bare->member_class, from_bare->member_class)) {
		uint64_t offset = base_subobject_offset(to_bare->member_class,
		                                        from_bare->member_class);
		if (offset != 0) {
			string slot = fresh_aux_slot("memptrconv", "i64");
			string is_null = fresh_temp();
			instr(is_null + " = cmp eq i64 " + value.text + ", 0");
			string null_block = fresh_block("memptr_null");
			string value_block = fresh_block("memptr_value");
			string end_block = fresh_block("memptr_end");
			terminate("branch " + is_null + ", ^" + null_block + ", ^" +
			          value_block);
			start_block(null_block);
			instr("store i64 0, $" + slot);
			terminate("jump ^" + end_block);
			start_block(value_block);
			string adjusted = fresh_temp();
			instr(adjusted + " = binary add i64 " + value.text + ", " +
			      to_string(offset));
			instr("store i64 " + adjusted + ", $" + slot);
			terminate("jump ^" + end_block);
			start_block(end_block);
			string loaded = fresh_temp();
			instr(loaded + " = load i64 $" + slot);
			return Value("i64", loaded); } }
	if (dst == src)
		return Value(dst, value.text);
	string tmp = fresh_temp();
	instr(tmp + " = copy " + dst + " " + value.text);
	return Value(dst, tmp); }

Value FunctionLowerer::convert_same_lowir_value(Value value,
                                                TypePtr from,
                                                TypePtr to,
                                                const string& dst) {
	TypePtr from_bare = pa11::strip_cv(strip_for_value(from));
	TypePtr to_bare = pa11::strip_cv(strip_for_value(to));
	if (from_bare->kind == TypeKind::Pointer &&
	    to_bare->kind == TypeKind::Pointer) {
		TypePtr from_pointee = pa11::strip_cv(from_bare->base);
		TypePtr to_pointee = pa11::strip_cv(to_bare->base);
		if (from_pointee->kind == TypeKind::Record &&
		    to_pointee->kind == TypeKind::Record &&
		    record_has_base_subobject(from_pointee, to_pointee))
			return emit_base_subobject_addr(value, from_pointee, to_pointee);
		if (from_pointee->kind == TypeKind::Record &&
		    to_pointee->kind == TypeKind::Record &&
		    record_has_base_subobject(to_pointee, from_pointee)) {
			program_.mark_static_downcast_source_record(from_pointee);
			uint64_t offset = base_subobject_offset(to_pointee, from_pointee);
			if (offset == 0)
				return value;
			string slot = fresh_aux_slot("basecast", "ptr");
			string is_null = fresh_temp();
			instr(is_null + " = cmp eq ptr " + value.text + ", 0");
			string null_block = fresh_block("basecast_null");
			string adjust_block = fresh_block("basecast_adjust");
			string end_block = fresh_block("basecast_end");
			terminate("branch " + is_null + ", ^" + null_block + ", ^" +
			          adjust_block);
			start_block(null_block);
			instr("store ptr 0, $" + slot);
			terminate("jump ^" + end_block);
			start_block(adjust_block);
			string adjusted = fresh_temp();
			instr(adjusted + " = index i8 [projection=base_subobject] " +
			      value.text + ", -" + to_string(offset));
			instr("store ptr " + adjusted + ", $" + slot);
			terminate("jump ^" + end_block);
			start_block(end_block);
			string loaded = fresh_temp();
			instr(loaded + " = load ptr $" + slot);
			return Value("ptr", loaded); } }
	return Value(dst, value.text); }

Value FunctionLowerer::convert_value(Value value, TypePtr from, TypePtr to, bool fold_literals) {
	string dst = scalar_lowir_type(to);
	string src = scalar_lowir_type(strip_for_value(from));
	TypePtr from_bare = pa11::strip_cv(strip_for_value(from));
	TypePtr to_bare = pa11::strip_cv(strip_for_value(to));
	if (from_bare->kind == TypeKind::Fundamental && from_bare->fundamental == FT_NULLPTR_T && to_bare->kind == TypeKind::Pointer) {
		string tmp = fresh_temp();
		instr(tmp + " = copy ptr " + value.text);
		return Value(dst, tmp); }
	if (from_bare->kind == TypeKind::Fundamental && from_bare->fundamental == FT_NULLPTR_T && to_bare->kind == TypeKind::MemberPointer) {
		if (fold_literals && value.text != "" && value.text[0] != '%' && value.text[0] != '$' && value.text[0] != '@')
			return Value(dst, value.text);
		string tmp = fresh_temp();
		if (dst == src)
			instr(tmp + " = copy " + dst + " " + value.text);
		else
			instr(tmp + " = convert zext " + dst + " " + src + " " + value.text);
		return Value(dst, tmp); }
	if (from_bare->kind == TypeKind::Pointer && to_bare->kind == TypeKind::Fundamental && to_bare->fundamental == FT_BOOL) {
		string cmp = fresh_temp();
		instr(cmp + " = cmp ne ptr " + value.text + ", 0");
		string tmp = fresh_temp();
		instr(tmp + " = copy u8 " + cmp);
		return Value("u8", tmp); }
	if (from_bare->kind == TypeKind::MemberPointer && to_bare->kind == TypeKind::Fundamental && to_bare->fundamental == FT_BOOL) {
		string type = scalar_lowir_type(from);
		if (from_bare->base.get() != NULL && from_bare->base->kind == TypeKind::Function && type == "i128")
			type = "i64";
		string cmp = fresh_temp();
		instr(cmp + " = cmp ne " + type + " " + value.text + ", 0");
		string tmp = fresh_temp();
		instr(tmp + " = copy u8 " + cmp);
		return Value("u8", tmp); }
	if (program_.native_lowering && to_bare->kind == TypeKind::Fundamental && to_bare->fundamental == FT_BOOL && (from_bare->kind == TypeKind::Fundamental || from_bare->kind == TypeKind::Enum))
		return bool_value(value, from);
	if (from_bare->kind == TypeKind::MemberPointer &&
	    to_bare->kind == TypeKind::MemberPointer)
		return convert_member_pointer_value(value, from, to, dst, src);
	if (dst == src)
		return convert_same_lowir_value(value, from, to, dst);
	if (fold_literals && value.text != "" && value.text[0] != '%' && value.text[0] != '$' && value.text[0] != '@' && !is_float_type(from) && !is_float_type(to) && (value.text == "0" || (dst != "ptr" && src != "ptr")))
		return Value(dst, value.text);
	string op = "copy";
	if (dst == "ptr" || src == "ptr")
		op = "copy";
	else if (starts_with(dst, "f") && starts_with(src, "f"))
		op = pa11::type_size(to) > pa11::type_size(from) ? "fpext" : "fptrunc";
	else if (starts_with(dst, "f")) {
		bool literal_zero = value.text == "0" && value.text[0] != '%' && value.text[0] != '$' && value.text[0] != '@';
		if (pa11::is_integral_or_bool_type(from) && pa11::type_size(from_bare) < 8 && !literal_zero) {
			int shift = (8 - pa11::type_size(from_bare)) * 8;
			string shifted = fresh_temp();
			instr(shifted + " = binary shl i64 " + value.text + ", " + to_string(shift));
			string normalized = fresh_temp();
			instr(normalized + " = binary " + string(is_unsigned_type(from) ? "ushr" : "shr") + " i64 " + shifted + ", " + to_string(shift));
			value = Value(value.type, normalized); }
		op = is_unsigned_type(from) ? "uitofp" : "sitofp"; }
	else if (starts_with(src, "f"))
		op = is_unsigned_type(to) ? "fptoui" : "fptosi";
	else if ((is_reference(from) ? pa11::type_size(strip_for_value(from))
	                             : pa11::type_size(from)) == (is_reference(to) ? pa11::type_size(strip_for_value(to))
	                           : pa11::type_size(to)))
		op = "copy";
	else if ((is_reference(to) ? pa11::type_size(strip_for_value(to))
	                           : pa11::type_size(to)) <
	         (is_reference(from) ? pa11::type_size(strip_for_value(from))
	                             : pa11::type_size(from)))
		op = "trunc";
	else
		op = is_unsigned_type(from) ? "zext" : "sext";
	string tmp = fresh_temp();
	if (op == "copy")
		instr(tmp + " = copy " + dst + " " + value.text);
	else
		instr(tmp + " = convert " + op + " " + dst + " " + src + " " + value.text);
	return Value(dst, tmp); }
Value FunctionLowerer::convert_binary_value(Value value, TypePtr from, TypePtr to) {
	string dst = scalar_lowir_type(to);
	string src = scalar_lowir_type(strip_for_value(from));
	if (dst == "i64" && src != dst && is_unsigned_type(to) && value.text != "" && value.text[0] != '%' && value.text[0] != '$' && value.text[0] != '@' && !is_float_type(from) && !is_float_type(to)) {
		string tmp = fresh_temp();
		instr(tmp + " = convert " + string(is_unsigned_type(from) ? "zext" : "sext") + " i64 " + src + " " + value.text);
		return Value("i64", tmp); }
	return convert_value(value, from, to); }
Value FunctionLowerer::bool_value(Value value, TypePtr type) {
	TypePtr bare = strip_cv(strip_for_value(type));
	if (bare->kind == TypeKind::MemberPointer && bare->base.get() != NULL && bare->base->kind == TypeKind::Function && value.type == "i128")
		value = Value("i64", value.text);
	string src = scalar_lowir_type(strip_for_value(type));
	if (value.type == "i64" && src == "i128")
		src = "i64";
	string cmp_type = (!is_float_type(type) && src != "ptr" && src != "i128")
		? "i64" : src;
	string tmp = fresh_temp();
	string zero = is_float_type(type) ? "0.0" : "0";
	instr(tmp + " = cmp ne " + cmp_type + " " + value.text + ", " + zero);
	return Value("u8", tmp); }
Value FunctionLowerer::ensure_pointer(Value storage) {
	if (storage.text.empty())
		return storage;
	if (storage.text[0] != '$' && storage.text[0] != '@')
		return storage;
	string tmp = fresh_temp();
	instr(tmp + " = addr " + storage.text);
	return Value("ptr", tmp); }
void FunctionLowerer::branch_logical_operand(const Node& expr, const string& yes, const string& no) {
	if (starts_with(expr.line, "binary-expression") && expr.has_op && (expr.op == OP_LAND || expr.op == OP_LOR)) {
		Value value = emit_rvalue(expr);
		terminate_with_pending_temp_cleanups(value.text, yes, no);
		return; }
	branch_on(expr, yes, no); }
void FunctionLowerer::branch_with_unwind_cleanups(const Node& expr, const string& yes, const string& no) {
	string dispatch = active_unwind_dispatch_.empty()
		? fresh_block("call_unwind_dispatch") : active_unwind_dispatch_;
	bool define_dispatch = active_unwind_dispatch_.empty();
	instr("eh_try ^" + dispatch);
	++eh_try_depth_;
	Value cond = emit_rvalue(expr);
	if (is_float_type(expr.type))
		cond = bool_value(cond, expr.type);
	--eh_try_depth_;
	instr("eh_end");
	if (define_dispatch) {
		string end = fresh_block("call_unwind_end");
		terminate("jump ^" + end);
		active_unwind_dispatch_ = dispatch;
		start_block(dispatch);
		emit_unwind_cleanups();
		terminate("resume");
		start_block(end); }
	terminate_with_pending_temp_cleanups(cond.text, yes, no); }
Value FunctionLowerer::emit_binary(const Node& expr) {
	if (expr.has_op && expr.op == OP_COMMA) {
		emit_rvalue(expr.children[0]);
		return emit_rvalue(expr.children[1]); }
	if (expr.has_op && (expr.op == OP_EQ || expr.op == OP_NE) && expr.children.size() == 2 && expr.children[0].is_typeid_expression && expr.children[1].is_typeid_expression) {
		Value lhs = emit_lvalue_addr(expr.children[0]);
		Value rhs = emit_lvalue_addr(expr.children[1]);
		string tmp = fresh_temp();
		instr(tmp + " = cmp " + string(expr.op == OP_EQ ? "eq" : "ne") + " ptr " + lhs.text + ", " + rhs.text);
		return Value("u8", tmp); }
	if (expr.has_op && (expr.op == OP_LAND || expr.op == OP_LOR))
		return emit_logical_binary(expr);
	bool wrap_lhs_materialized_member = eh_try_depth_ == 0 && has_active_cleanups() && starts_with(expr.children[0].line, "member-expression") && node_contains_call_expression(expr.children[0]) && expr.children[0].category == ValueCategory::LValue && scalar_lowir_type(expr.children[0].type).compare(0, 4, "obj<") != 0;
	string dispatch;
	bool define_dispatch = false;
	Value lhs;
	if (wrap_lhs_materialized_member) {
		Value lhs_addr;
		if (!expr.children[0].children.empty() && starts_with(expr.children[0].children[0].line, "call-expression") && expr.children[0].binding != NULL) {
			const Node& member_expr = expr.children[0];
			TypePtr object_record = pa11::strip_cv(object_type(member_expr.children[0].type));
			string slot = fresh_aux_slot("tmpobj", scalar_lowir_type(object_record));
			string object_addr_name = fresh_temp();
			instr(object_addr_name + " = addr $" + slot);
			Value object_addr("ptr", object_addr_name);
			function<Value()> object_addr_for = [object_addr]() {
				return object_addr;
			};
			lower_object_init(object_addr_for, object_record, member_expr.children[0]);
			dispatch = active_unwind_dispatch_.empty()
				? fresh_block("call_unwind_dispatch") : active_unwind_dispatch_;
			define_dispatch = active_unwind_dispatch_.empty();
			instr("eh_try ^" + dispatch);
			++eh_try_depth_;
			Binding* member = member_expr.binding;
			TypePtr owner_record = pa11::record_type_for_scope(member->owner);
			Value projected_base = object_addr;
			if (owner_record.get() != NULL && object_record.get() != NULL && object_record->kind == TypeKind::Record && owner_record->kind == TypeKind::Record && !pa11::same_type(object_record, owner_record))
				projected_base = emit_base_subobject_addr(object_addr, object_record, owner_record);
			string field_addr = fresh_temp();
			instr(field_addr + " = index i8 [projection=field] " + projected_base.text + ", " + to_string(member->member_offset));
			lhs_addr = Value("ptr", field_addr); }
		else {
			lhs_addr = ensure_pointer(emit_lvalue_addr(expr.children[0]));
			dispatch = active_unwind_dispatch_.empty()
				? fresh_block("call_unwind_dispatch") : active_unwind_dispatch_;
			define_dispatch = active_unwind_dispatch_.empty();
			instr("eh_try ^" + dispatch);
			++eh_try_depth_; }
		string loaded = fresh_temp();
		instr(loaded + " = load " + scalar_lowir_type(expr.children[0].type) + " " + lhs_addr.text);
		lhs = Value(scalar_lowir_type(expr.children[0].type), loaded); }
	else
		lhs = emit_rvalue(expr.children[0]);
	Value rhs = emit_rvalue(expr.children[1]);
	TypePtr lhs_type = strip_for_value(expr.children[0].type);
	TypePtr rhs_type = strip_for_value(expr.children[1].type);
	if ((expr.op == OP_PLUS || expr.op == OP_MINUS) && scalar_lowir_type(expr.type) == "ptr")
		return emit_pointer_index_binary(expr, lhs, rhs, lhs_type, rhs_type);
	if (expr.op == OP_MINUS && pa11::strip_cv(lhs_type)->kind == TypeKind::Pointer && pa11::strip_cv(rhs_type)->kind == TypeKind::Pointer)
		return emit_pointer_difference(expr, lhs, rhs, lhs_type);
	string op;
	bool cmp = false;
	switch (expr.op) {
	case OP_PLUS: op = "add"; break;
	case OP_MINUS: op = "sub"; break;
	case OP_STAR: op = "mul"; break;
	case OP_DIV: op = is_unsigned_type(expr.children[0].type) ? "udiv" : "div"; break;
	case OP_MOD: op = is_unsigned_type(expr.children[0].type) ? "umod" : "mod"; break;
	case OP_AMP: op = "and"; break;
	case OP_BOR: op = "or"; break;
	case OP_XOR: op = "xor"; break;
	case OP_LSHIFT: op = "shl"; break;
	case OP_RSHIFT: op = is_unsigned_type(expr.children[0].type) ? "ushr" : "shr"; break;
	case OP_EQ: op = "eq"; cmp = true; break;
	case OP_NE: op = "ne"; cmp = true; break;
	case OP_LT: op = is_unsigned_type(expr.children[0].type) ? "ult" : "lt"; cmp = true; break;
	case OP_LE: op = is_unsigned_type(expr.children[0].type) ? "ule" : "le"; cmp = true; break;
	case OP_GT: op = is_unsigned_type(expr.children[0].type) ? "ugt" : "gt"; cmp = true; break;
	case OP_GE: op = is_unsigned_type(expr.children[0].type) ? "uge" : "ge"; cmp = true; break;
	default: throw runtime_error("unsupported binary operator"); }
	TypePtr op_type = cmp ? lowir_common_type(expr.children[0].type, expr.children[1].type)
	                     : expr.type;
	if (expr.op == OP_DIV)
		op = is_unsigned_type(op_type) ? "udiv" : "div";
	else if (expr.op == OP_MOD)
		op = is_unsigned_type(op_type) ? "umod" : "mod";
	else if (expr.op == OP_RSHIFT)
		op = is_unsigned_type(op_type) ? "ushr" : "shr";
	else if (expr.op == OP_LT)
		op = is_unsigned_type(op_type) ? "ult" : "lt";
	else if (expr.op == OP_LE)
		op = is_unsigned_type(op_type) ? "ule" : "le";
	else if (expr.op == OP_GT)
		op = is_unsigned_type(op_type) ? "ugt" : "gt";
	else if (expr.op == OP_GE)
		op = is_unsigned_type(op_type) ? "uge" : "ge";
	if (cmp && scalar_lowir_type(op_type) == "ptr") {
		if (scalar_lowir_type(strip_for_value(expr.children[0].type)) != "ptr")
			lhs = convert_binary_value(lhs, expr.children[0].type, op_type);
		if (scalar_lowir_type(strip_for_value(expr.children[1].type)) != "ptr")
			rhs = convert_binary_value(rhs, expr.children[1].type, op_type); }
	else {
		lhs = convert_binary_value(lhs, expr.children[0].type, op_type);
		rhs = convert_binary_value(rhs, expr.children[1].type, op_type); }
	string type = scalar_lowir_type(op_type);
	string tmp = fresh_temp();
	instr(tmp + " = " + string(cmp ? "cmp " : "binary ") + op + " " + type + " " + lhs.text + ", " + rhs.text);
	if (wrap_lhs_materialized_member) {
		--eh_try_depth_;
		instr("eh_end");
		if (define_dispatch) {
			string end = fresh_block("call_unwind_end");
			terminate("jump ^" + end);
			active_unwind_dispatch_ = dispatch;
			start_block(dispatch);
			emit_unwind_cleanups();
			terminate("resume");
			start_block(end); } }
	return Value(cmp ? "u8" : scalar_lowir_type(expr.type), tmp); }
Value FunctionLowerer::emit_record_assignment(const Node& expr) {
	TypePtr lhs_type = object_type(expr.children[0].type);
	bool move_assign = expr.children[1].category != ValueCategory::LValue;
	bool wrap = eh_try_depth_ == 0 && has_active_cleanups();
	string dispatch;
	bool define_dispatch = false;
	if (wrap) {
		dispatch = active_unwind_dispatch_.empty()
			? fresh_block("call_unwind_dispatch")
			: active_unwind_dispatch_;
		define_dispatch = active_unwind_dispatch_.empty();
		instr("eh_try ^" + dispatch);
		++eh_try_depth_; }
	Value target = ensure_pointer(emit_lvalue_addr(expr.children[0]));
	TypePtr rhs_type = object_type(expr.children[1].type);
	Value source;
	if (expr.children[1].category == ValueCategory::LValue ||
	    expr.children[1].category == ValueCategory::XValue)
		source = ensure_pointer(emit_lvalue_addr(expr.children[1]));
	else {
		TypePtr object = pa11::strip_cv(rhs_type);
		string slot = fresh_aux_slot("assignarg", scalar_lowir_type(object));
		string addr = fresh_temp();
		instr(addr + " = addr $" + slot);
		source = Value("ptr", addr);
		function<Value()> source_addr = [source]() { return source; };
		lower_object_init(source_addr, object, expr.children[1]); }
	Binding* assign = program_.demand_implicit_copy_assignment(lhs_type, move_assign);
	string tmp = fresh_temp();
	instr(tmp + " = call ptr @" + program_.symbol_for(assign) + "(" +
	      target.text + ", " + source.text + ")");
	finish_assignment_protection(wrap, define_dispatch, dispatch);
	return Value("ptr", tmp); }

void FunctionLowerer::finish_assignment_protection(bool wrap,
                                                   bool define_dispatch,
                                                   const string& dispatch) {
	if (!wrap)
		return;
	--eh_try_depth_;
	instr("eh_end");
	if (define_dispatch) {
		string end = fresh_block("call_unwind_end");
		terminate("jump ^" + end);
		active_unwind_dispatch_ = dispatch;
		start_block(dispatch);
		emit_unwind_cleanups();
		terminate("resume");
		start_block(end); } }

Value FunctionLowerer::emit_member_assignment(const Node& expr) {
	TypePtr lhs_type = object_type(expr.children[0].type);
	bool wrap = eh_try_depth_ == 0 && has_active_cleanups() &&
		node_contains_call_expression(expr.children[0]);
	string dispatch;
	bool define_dispatch = false;
	if (wrap) {
		dispatch = active_unwind_dispatch_.empty()
			? fresh_block("call_unwind_dispatch")
			: active_unwind_dispatch_;
		define_dispatch = active_unwind_dispatch_.empty();
		instr("eh_try ^" + dispatch);
		++eh_try_depth_; }
	Value rhs = emit_rvalue(expr.children[1]);
	rhs = convert_binary_value(rhs, expr.children[1].type, lhs_type);
	Value addr = emit_lvalue_addr(expr.children[0]);
	if (expr.children[0].binding != NULL && expr.children[0].binding->is_bit_field) {
		Binding* field = expr.children[0].binding;
		string low_type = scalar_lowir_type(lhs_type);
		uint64_t mask = field->bit_width >= 64
			? ~uint64_t(0) : ((uint64_t(1) << field->bit_width) - 1);
		string masked = fresh_temp();
		instr(masked + " = binary and " + low_type + " " + rhs.text +
		      ", " + to_string(mask));
		string shifted = masked;
		uint64_t storage_mask = mask << field->bit_offset;
		if (field->bit_offset != 0) {
			shifted = fresh_temp();
			instr(shifted + " = binary shl " + low_type + " " +
			      masked + ", " + to_string(field->bit_offset)); }
		string oldv = fresh_temp();
		instr(oldv + " = load " + low_type + " " + addr.text);
		string cleared = fresh_temp();
		instr(cleared + " = binary and " + low_type + " " + oldv +
		      ", " + to_string(~storage_mask));
		string merged = fresh_temp();
		instr(merged + " = binary or " + low_type + " " + cleared +
		      ", " + shifted);
		instr("store " + low_type + " " + merged + ", " + addr.text);
		finish_assignment_protection(wrap, define_dispatch, dispatch);
		return rhs; }
	instr("store " + scalar_lowir_type(lhs_type) + " " + rhs.text +
	      ", " + addr.text);
	finish_assignment_protection(wrap, define_dispatch, dispatch);
	return rhs; }

Value FunctionLowerer::emit_compound_assignment(const Node& expr, TypePtr lhs_type) {
	Value oldv = emit_rvalue(expr.children[0]);
	Value rhs = emit_rvalue(expr.children[1]);
	if (scalar_lowir_type(lhs_type) == "ptr" &&
	    (expr.op == OP_PLUSASS || expr.op == OP_MINUSASS)) {
		TypePtr ptr = pa11::strip_cv(strip_for_value(lhs_type));
		uint64_t scale = pa11::type_size(ptr->base);
		string offset = rhs.text;
		if (scale != 1) {
			string mul = fresh_temp();
			instr(mul + " = binary mul i64 " + offset + ", " + to_string(scale));
			offset = mul; }
		if (expr.op == OP_MINUSASS) {
			string neg = fresh_temp();
			instr(neg + " = binary sub i64 0, " + offset);
			offset = neg; }
		string tmp = fresh_temp();
		instr(tmp + " = index i8 " + oldv.text + ", " + offset);
		Value addr = emit_lvalue_addr(expr.children[0]);
		instr("store ptr " + tmp + ", " + addr.text);
		return Value("ptr", tmp); }
	TypePtr arithmetic_type = lowir_common_type(expr.children[0].type,
	                                           expr.children[1].type);
	oldv = convert_binary_value(oldv, expr.children[0].type, arithmetic_type);
	rhs = convert_value(rhs, expr.children[1].type, arithmetic_type);
	ETokenType op = expr.op == OP_PLUSASS ? OP_PLUS : expr.op == OP_MINUSASS ? OP_MINUS : expr.op == OP_STARASS ? OP_STAR : expr.op == OP_DIVASS ? OP_DIV : expr.op == OP_MODASS ? OP_MOD : OP_PLUS;
	string op_name = op == OP_MINUS ? "sub" : op == OP_STAR ? "mul" : op == OP_DIV ? (is_unsigned_type(arithmetic_type) ? "udiv" : "div") : op == OP_MOD ? (is_unsigned_type(arithmetic_type) ? "umod" : "mod") : "add";
	string tmp = fresh_temp();
	instr(tmp + " = binary " + op_name + " " +
	      scalar_lowir_type(arithmetic_type) + " " + oldv.text + ", " + rhs.text);
	rhs = convert_value(Value(scalar_lowir_type(arithmetic_type), tmp),
	                    arithmetic_type,
	                    lhs_type);
	Value addr = emit_lvalue_addr(expr.children[0]);
	instr("store " + scalar_lowir_type(lhs_type) + " " + rhs.text +
	      ", " + addr.text);
	return rhs; }

Value FunctionLowerer::emit_plain_assignment(const Node& expr, TypePtr lhs_type) {
	Binding* lhs_binding = expr.children[0].binding;
	map<const Binding*, string>::const_iterator slot_it = lhs_binding != NULL
		? slots_.find(lhs_binding) : slots_.end();
	if (starts_with(expr.children[1].line, "call-expression") && slot_it != slots_.end()) {
		call_result_store_slot_ = slot_it->second;
		call_result_store_type_ = lhs_type;
		call_result_store_consumed_ = false; }
	Value rhs = emit_rvalue(expr.children[1]);
	if (!call_result_store_consumed_) {
		rhs = convert_binary_value(rhs, expr.children[1].type, lhs_type);
		Value addr = emit_lvalue_addr(expr.children[0]);
		instr("store " + scalar_lowir_type(lhs_type) + " " + rhs.text +
		      ", " + addr.text); }
	call_result_store_slot_.clear();
	call_result_store_type_.reset();
	call_result_store_consumed_ = false;
	return rhs; }

Value FunctionLowerer::emit_assignment(const Node& expr) {
	if (expr.op == OP_ASS && expr.children.size() == 2 &&
	    pa11::strip_cv(object_type(expr.children[0].type))->kind == TypeKind::Record)
		return emit_record_assignment(expr);
	if (expr.op == OP_ASS && starts_with(expr.children[0].line, "member-expression"))
		return emit_member_assignment(expr);
	TypePtr lhs_type = object_type(expr.children[0].type);
	if (expr.op != OP_ASS)
		return emit_compound_assignment(expr, lhs_type);
	return emit_plain_assignment(expr, lhs_type); }
Value FunctionLowerer::emit_unary(const Node& expr) {
	if (expr.op == OP_AMP) {
		TypePtr result_bare = pa11::strip_cv(expr.type);
		if (result_bare->kind == TypeKind::MemberPointer) {
			if (expr.children.empty() || expr.children[0].binding == NULL)
				throw runtime_error("member pointer address missing member");
			Binding* member = expr.children[0].binding->aliased_binding != NULL && expr.children[0].binding->target_scope != NULL
				? expr.children[0].binding->aliased_binding
				: expr.children[0].binding;
			if (member->kind == BindingKind::Function) {
				if (member->is_inline_definition)
					program_.demand_inline_function(member);
				if (!program_.native_lowering) {
					program_.demand_function_declaration(member);
					string addr = fresh_temp();
					instr(addr + " = addr @" + program_.symbol_for(member));
					string bits = fresh_temp();
					instr(bits + " = copy i64 " + addr);
					string wide = fresh_temp();
					instr(wide + " = convert zext i128 i64 " + bits);
					return Value("i128", wide); }
				string bits = fresh_temp();
				if (member->virtual_slot_index >= 0) {
					TypePtr owner = pa11::record_type_for_scope(member->owner);
					if (owner.get() != NULL)
						program_.demand_vtable(owner);
					string slot = fresh_aux_slot("memptr_lit", "i128");
					string addr = fresh_temp();
					instr(addr + " = addr $" + slot);
					instr("store i64 " + to_string(member->virtual_slot_index * 8) + ", " + addr);
					string flag_addr = fresh_temp();
					instr(flag_addr + " = index i8 " + addr + ", 8");
					instr("store i64 1, " + flag_addr);
					instr(bits + " = load i128 $" + slot);
					return Value("i128", bits); }
				else {
					program_.demand_function_declaration(member);
					string addr = fresh_temp();
					instr(addr + " = addr @" + program_.symbol_for(member));
					instr(bits + " = copy i64 " + addr); }
				string wide = fresh_temp();
				instr(wide + " = convert zext i128 i64 " + bits);
				return Value("i128", wide); }
			TypePtr owner = pa11::record_type_for_scope(member->owner);
			if (owner.get() != NULL)
				pa11::layout_record_type(pa11::strip_cv(owner));
			string tmp = fresh_temp();
			instr(tmp + " = const i64 " + to_string(member->member_offset + 1));
			return Value("i64", tmp); }
		if (!expr.children.empty() && expr.children[0].binding != NULL && expr.children[0].binding->kind == BindingKind::Function) {
			if (expr.children[0].binding->is_inline_definition)
				program_.demand_inline_function(expr.children[0].binding);
			program_.demand_function_declaration(expr.children[0].binding);
			string addr = fresh_temp();
			instr(addr + " = addr @" + program_.symbol_for(expr.children[0].binding));
			return Value("ptr", addr); }
		return ensure_pointer(emit_lvalue_addr(expr.children[0])); }
	if (expr.op == OP_STAR) {
		Value addr = emit_lvalue_addr(expr);
		string tmp = fresh_temp();
		instr(tmp + " = load " + scalar_lowir_type(expr.type) + " " + addr.text);
		return Value(scalar_lowir_type(expr.type), tmp); }
	if (expr.op == OP_INC || expr.op == OP_DEC) {
		Value addr = emit_lvalue_addr(expr.children[0]);
		TypePtr value_type = strip_for_value(expr.children[0].type);
		string oldtmp = fresh_temp();
		instr(oldtmp + " = load " + scalar_lowir_type(value_type) + " " + addr.text);
		Value oldv(scalar_lowir_type(value_type), oldtmp);
		string one = "1";
		string tmp;
		if (oldv.type == "ptr") {
			TypePtr ptr = pa11::strip_cv(strip_for_value(expr.type));
			uint64_t scale = pa11::type_size(ptr->base);
			if (expr.op == OP_DEC && scale == 1)
				one = "-1";
			else if (expr.op == OP_DEC) {
				string mul = fresh_temp();
				instr(mul + " = binary mul i64 1, " + to_string(scale));
				string neg = fresh_temp();
				instr(neg + " = binary sub i64 0, " + mul);
				one = neg; }
			else if (scale != 1) {
				string mul = fresh_temp();
				instr(mul + " = binary mul i64 1, " + to_string(scale));
				one = mul; }
			tmp = fresh_temp();
			instr(tmp + " = index i8 " + oldv.text + ", " + one); }
		else {
			tmp = fresh_temp();
			instr(tmp + " = binary " + string(expr.op == OP_INC ? "add" : "sub") + " " + scalar_lowir_type(expr.type) + " " + oldv.text + ", " + one); }
		instr("store " + scalar_lowir_type(expr.type) + " " + tmp + ", " + addr.text);
		return Value(scalar_lowir_type(expr.type), tmp); }
	Value inner = emit_rvalue(expr.children[0]);
	if (expr.op == OP_PLUS)
		return inner;
	string op = expr.op == OP_MINUS ? "neg" : expr.op == OP_COMPL ? "bitnot" : "not";
	if (expr.op == OP_LNOT) {
		string tmp = fresh_temp();
		TypePtr bare = strip_cv(strip_for_value(expr.children[0].type));
		if (bare->kind == TypeKind::MemberPointer && bare->base.get() != NULL && bare->base->kind == TypeKind::Function && inner.type == "i128")
			inner = Value("i64", inner.text);
		string cmp_type = (!is_float_type(expr.children[0].type) && inner.type != "ptr" && inner.type != "i128") ? "i64" : inner.type;
			string zero = is_float_type(expr.children[0].type) ? "0.0" : "0";
		instr(tmp + " = cmp eq " + cmp_type + " " + inner.text + ", " + zero);
		return Value("u8", tmp); }
	string tmp = fresh_temp();
	instr(tmp + " = unary " + op + " " + inner.type + " " + inner.text);
	return Value(inner.type, tmp); }
Value FunctionLowerer::emit_postfix(const Node& expr) {
	Value addr = emit_lvalue_addr(expr.children[0]);
	bool refetch_store_addr = starts_with(expr.children[0].line, "call-expression") && is_reference(expr.children[0].type);
	TypePtr value_type = strip_for_value(expr.children[0].type);
	string oldtmp = fresh_temp();
	instr(oldtmp + " = load " + scalar_lowir_type(value_type) + " " + addr.text);
	Value oldv(scalar_lowir_type(value_type), oldtmp);
	string one = "1";
	string tmp;
	if (oldv.type == "ptr") {
		TypePtr ptr = pa11::strip_cv(strip_for_value(expr.type));
		uint64_t scale = pa11::type_size(ptr->base);
		if (expr.op == OP_DEC && scale == 1)
			one = "-1";
		else if (expr.op == OP_DEC) {
			string mul = fresh_temp();
			instr(mul + " = binary mul i64 1, " + to_string(scale));
			string neg = fresh_temp();
			instr(neg + " = binary sub i64 0, " + mul);
			one = neg; }
		else if (scale != 1) {
			string mul = fresh_temp();
			instr(mul + " = binary mul i64 1, " + to_string(scale));
			one = mul; }
		tmp = fresh_temp();
		instr(tmp + " = index i8 " + oldv.text + ", " + one); }
	else {
		tmp = fresh_temp();
		instr(tmp + " = binary " + string(expr.op == OP_INC ? "add" : "sub") + " " + oldv.type + " " + oldv.text + ", 1"); }
	Value store_addr = refetch_store_addr ? emit_lvalue_addr(expr.children[0]) : addr;
	instr("store " + oldv.type + " " + tmp + ", " + store_addr.text);
	return oldv; }
Value FunctionLowerer::emit_cast(const Node& expr) {
	if (expr.is_dynamic_cast_expression)
		return emit_dynamic_cast(expr, is_reference(expr.type));
	if (pa11::is_void_type(expr.type)) {
		if (expr.children[0].category == ValueCategory::LValue && pa11::strip_cv(object_type(expr.children[0].type))->kind == TypeKind::Record)
			ensure_pointer(emit_lvalue_addr(expr.children[0]));
		else
			lower_discarded_expr(expr.children[0]);
		return Value("void", ""); }
	if (is_reference(expr.type))
		return emit_rvalue(expr.children[0]);
	TypePtr cast_source = pa11::strip_cv(strip_for_value(expr.children[0].type));
	TypePtr cast_target = pa11::strip_cv(strip_for_value(expr.type));
	if (cast_source->kind == TypeKind::Enum && cast_source->enum_underlying != FT_INT && cast_target->kind == TypeKind::Fundamental && scalar_lowir_type(expr.children[0].type) == scalar_lowir_type(expr.type)) {
		Value raw = emit_rvalue(expr.children[0]);
		string tmp = fresh_temp();
		instr(tmp + " = copy " + scalar_lowir_type(expr.type) + " " + raw.text);
		return Value(scalar_lowir_type(expr.type), tmp); }
	if (cast_source->kind == TypeKind::Fundamental && cast_target->kind == TypeKind::Enum && cast_target->enum_underlying != FT_INT && scalar_lowir_type(expr.children[0].type) == scalar_lowir_type(expr.type)) {
		Value raw = emit_rvalue(expr.children[0]);
		string tmp = fresh_temp();
		instr(tmp + " = copy " + scalar_lowir_type(expr.type) + " " + raw.text);
		return Value(scalar_lowir_type(expr.type), tmp); }
	if (cast_source->kind == TypeKind::Fundamental && cast_target->kind == TypeKind::Fundamental && cast_source->fundamental == FT_LONG_INT && cast_target->fundamental == FT_UNSIGNED_LONG_INT && scalar_lowir_type(expr.children[0].type) == scalar_lowir_type(expr.type)) {
		Value raw = emit_rvalue(expr.children[0]);
		string tmp = fresh_temp();
		instr(tmp + " = copy " + scalar_lowir_type(expr.type) + " " + raw.text);
		return Value(scalar_lowir_type(expr.type), tmp); }
	if (cast_source->kind == TypeKind::Pointer && cast_target->kind == TypeKind::Pointer && expr.children[0].binding != NULL && expr.children[0].binding->kind == BindingKind::Parameter && expr.children[0].binding->name == "this") {
		TypePtr source_record = pa11::strip_cv(cast_source->base);
		TypePtr target_record = pa11::strip_cv(cast_target->base);
		if (source_record->kind == TypeKind::Record && target_record->kind == TypeKind::Record && record_has_base_subobject(target_record, source_record)) {
			program_.mark_static_downcast_source_record(source_record);
			Value raw = emit_rvalue(expr.children[0]);
			uint64_t offset = base_subobject_offset(target_record, source_record);
			if (offset == 0)
				return raw;
			string tmp = fresh_temp();
			instr(tmp + " = index i8 [projection=base_subobject] " + raw.text + ", -" + to_string(offset));
			return Value("ptr", tmp); } }
	return convert_value(emit_rvalue(expr.children[0]), expr.children[0].type, expr.type); }
void FunctionLowerer::branch_on(const Node& expr, const string& yes, const string& no) {
	if (starts_with(expr.line, "condition-declaration")) {
		if (expr.children.empty())
			throw runtime_error("empty condition declaration");
		lower_variable_decl(expr.children[0]);
		const Node& cond_node = expr.children.size() > 1 ? expr.children[1] : expr.children[0];
		Value cond = emit_rvalue(cond_node);
		if (is_float_type(cond_node.type))
			cond = bool_value(cond, cond_node.type);
		terminate_with_pending_temp_cleanups(cond.text, yes, no);
		return; }
	if (starts_with(expr.line, "binary-expression") && expr.has_op && expr.op == OP_LOR) {
		string rhs = fresh_block("lor_rhs");
		branch_on(expr.children[0], yes, rhs);
		start_block(rhs);
		branch_on(expr.children[1], yes, no);
		return; }
	if (starts_with(expr.line, "binary-expression") && expr.has_op && expr.op == OP_LAND) {
		string rhs = fresh_block("land_rhs");
		branch_on(expr.children[0], rhs, no);
		start_block(rhs);
		branch_on(expr.children[1], yes, no);
		return; }
	if (eh_try_depth_ == 0 && has_active_cleanups() && node_contains_call_expression(expr)) {
		branch_with_unwind_cleanups(expr, yes, no);
		return; }
	Value cond = emit_rvalue(expr);
	if (is_float_type(expr.type))
		cond = bool_value(cond, expr.type);
	terminate_with_pending_temp_cleanups(cond.text, yes, no); }
}  // namespace internal
}  // namespace pa14
