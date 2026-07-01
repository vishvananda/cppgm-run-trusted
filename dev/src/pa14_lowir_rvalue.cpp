#include "pa14_lowir_internal.h"
#include "pa14_lowir_function_internal.h"

namespace pa14 {
namespace internal {

namespace {

bool direct_call_named(const Node& expr, const string& name)
{
	return expr.direct_call != NULL && expr.direct_call->name == name;
}

bool direct_call_float_constant(const Node& expr)
{
	if (expr.direct_call == NULL)
		return false;
	const string& name = expr.direct_call->name;
	return name == "__builtin_inf" ||
	       name == "__builtin_inff" ||
	       name == "__builtin_infl" ||
	       name == "__builtin_huge_val" ||
	       name == "__builtin_huge_valf" ||
	       name == "__builtin_huge_vall" ||
	       name == "__builtin_nan" ||
	       name == "__builtin_nanf" ||
	       name == "__builtin_nanl" ||
	       name == "__builtin_nans" ||
	       name == "__builtin_nansf" ||
	       name == "__builtin_nansl";
}

bool direct_call_bit_count(const Node& expr)
{
	if (expr.direct_call == NULL)
		return false;
	const string& name = expr.direct_call->name;
	return name == "__builtin_clz" ||
	       name == "__builtin_clzl" ||
	       name == "__builtin_clzll" ||
	       name == "__builtin_clzg" ||
	       name == "__builtin_ctz" ||
	       name == "__builtin_ctzl" ||
	       name == "__builtin_ctzll" ||
	       name == "__builtin_popcount" ||
	       name == "__builtin_popcountl" ||
	       name == "__builtin_popcountll" ||
	       name == "__builtin_popcountg";
}

bool direct_call_fp_test(const Node& expr)
{
	if (expr.direct_call == NULL)
		return false;
	const string& name = expr.direct_call->name;
	return name == "__builtin_isfinite" ||
	       name == "__builtin_isinf" ||
	       name == "__builtin_isnan" ||
	       name == "__builtin_isnormal" ||
	       name == "__builtin_signbit";
}

bool gnu_atomic_builtin_name(const string& name)
{
	return name == "__atomic_load_n" ||
	       name == "__atomic_load" ||
	       name == "__atomic_store_n" ||
	       name == "__atomic_store" ||
	       name == "__atomic_exchange_n" ||
	       name == "__atomic_compare_exchange" ||
	       name == "__atomic_compare_exchange_n" ||
	       name == "__atomic_fetch_add" ||
	       name == "__atomic_fetch_sub" ||
	       name == "__atomic_fetch_and" ||
	       name == "__atomic_fetch_or" ||
	       name == "__atomic_fetch_xor" ||
	       name == "__atomic_add_fetch" ||
	       name == "__atomic_sub_fetch" ||
	       name == "__atomic_and_fetch" ||
	       name == "__atomic_or_fetch" ||
	       name == "__atomic_xor_fetch" ||
	       name == "__atomic_always_lock_free" ||
	       name == "__atomic_is_lock_free" ||
	       name == "__atomic_thread_fence" ||
	       name == "__atomic_signal_fence" ||
	       name == "__atomic_test_and_set" ||
	       name == "__atomic_clear" ||
	       name == "__sync_lock_test_and_set" ||
	       name == "__sync_lock_release";
}

bool c11_atomic_builtin_name(const string& name)
{
	return name == "__c11_atomic_load" ||
	       name == "__c11_atomic_init" ||
	       name == "__c11_atomic_store" ||
	       name == "__c11_atomic_exchange" ||
	       name == "__c11_atomic_compare_exchange_strong" ||
	       name == "__c11_atomic_compare_exchange_weak" ||
	       name == "__c11_atomic_fetch_add" ||
	       name == "__c11_atomic_fetch_sub" ||
	       name == "__c11_atomic_fetch_and" ||
	       name == "__c11_atomic_fetch_or" ||
	       name == "__c11_atomic_fetch_xor" ||
	       name == "__c11_atomic_is_lock_free" ||
	       name == "__c11_atomic_thread_fence" ||
	       name == "__c11_atomic_signal_fence";
}

}  // namespace

Value FunctionLowerer::emit_statement_expression(const Node& expr)
{
	if (expr.children.empty())
		return Value("void", "");
	const Node& body = expr.children[0];
	cleanups_.push_back(vector<Cleanup>());
	Value result("void", "");
	size_t result_index = body.children.size();
	if (!body.children.empty() &&
	    starts_with(body.children.back().line, "expression-statement") &&
	    !body.children.back().children.empty())
		result_index = body.children.size() - 1;
	for (size_t i = 0; i < result_index; ++i)
		lower_stmt(body.children[i]);
	if (result_index < body.children.size())
		result = emit_rvalue(body.children[result_index].children[0]);
	if (current_ != NULL && !current_->terminated)
		emit_scope_cleanups(cleanups_.back());
	cleanups_.pop_back();
	return result;
}

Value FunctionLowerer::emit_member_pointer_function_rvalue(const Node& expr)
{
	if (expr.children.size() < 2)
		throw runtime_error("member pointer function missing operand");
	if (!program_.native_lowering)
	{
		const Node& member_expr = expr.children[1];
		if (starts_with(member_expr.line, "unary-expression") &&
		    member_expr.has_op && member_expr.op == OP_AMP &&
		    !member_expr.children.empty() &&
		    member_expr.children[0].binding != NULL &&
		    member_expr.children[0].binding->kind == BindingKind::Function)
		{
			Binding* fn = member_expr.children[0].binding;
			if (fn->is_inline_definition)
				program_.demand_inline_function(fn);
			program_.demand_function_declaration(fn);
			string addr = fresh_temp();
			instr(addr + " = addr @" + program_.symbol_for(fn));
			return Value("ptr", addr);
		}
		Value member = emit_rvalue(expr.children[1]);
		string bits = fresh_temp();
		instr(bits + " = convert trunc i64 i128 " + member.text);
		string fn = fresh_temp();
		instr(fn + " = copy ptr " + bits);
		return Value("ptr", fn);
	}
	Value base;
	if (expr.has_op && expr.op == OP_ARROWSTAR)
		base = emit_rvalue(expr.children[0]);
	else if (expr.children[0].category == ValueCategory::LValue ||
	         expr.children[0].category == ValueCategory::XValue)
		base = emit_lvalue_addr(expr.children[0]);
	else
	{
		TypePtr object_record = pa11::strip_cv(object_type(expr.children[0].type));
		if (object_record->kind != TypeKind::Record)
			throw runtime_error("unsupported member pointer object");
		string slot = fresh_aux_slot("tmpobj", scalar_lowir_type(object_record));
		string addr = fresh_temp();
		instr(addr + " = addr $" + slot);
		base = Value("ptr", addr);
		function<Value()> object_addr = [base]() { return base; };
		lower_object_init(object_addr, object_record, expr.children[0]);
	}
	base = ensure_pointer(base);
	TypePtr object_record = expr.has_op && expr.op == OP_ARROWSTAR
		? pa11::strip_cv(strip_for_value(expr.children[0].type))
		: pa11::strip_cv(object_type(expr.children[0].type));
	if (object_record.get() != NULL && object_record->kind == TypeKind::Pointer)
		object_record = pa11::strip_cv(object_record->base);
	TypePtr member_pointer = pa11::strip_cv(object_type(expr.children[1].type));
	if (member_pointer->kind != TypeKind::MemberPointer)
		throw runtime_error("member pointer function operand type missing");
	TypePtr owner_record = pa11::strip_cv(member_pointer->member_class);
	if (object_record.get() != NULL && object_record->kind == TypeKind::Record &&
	    owner_record.get() != NULL && !pa11::same_type(object_record, owner_record) &&
	    record_has_base_subobject(object_record, owner_record))
		base = emit_base_subobject_addr(base, object_record, owner_record);
	Value member = emit_rvalue(expr.children[1]);
	string bits_slot = fresh_aux_slot("memptr_bits", "i128");
	instr("store i128 " + member.text + ", $" + bits_slot);
	string bits_addr = fresh_temp();
	instr(bits_addr + " = addr $" + bits_slot);
	string bits = fresh_temp();
	instr(bits + " = load i64 " + bits_addr);
	string flag_addr = fresh_temp();
	instr(flag_addr + " = index i8 " + bits_addr + ", 8");
	string is_virtual = fresh_temp();
	instr(is_virtual + " = load i64 " + flag_addr);
	string indirect = fresh_block("memptr_virtual");
	string direct = fresh_block("memptr_direct");
	string end = fresh_block("memptr_end");
	string slot = fresh_aux_slot("memptr_fn", "ptr");
	terminate("branch " + is_virtual + ", ^" + indirect + ", ^" + direct);
	start_block(indirect);
	string offset_slot = fresh_aux_slot("memptr_offset", "i64");
	instr("store i64 " + bits + ", $" + offset_slot);
	string vptr = fresh_temp();
	instr(vptr + " = load ptr " + base.text);
	string slot_addr = fresh_temp();
	instr(slot_addr + " = index i8 " + vptr + ", $" + offset_slot);
	string vfn = fresh_temp();
	instr(vfn + " = load ptr " + slot_addr);
	instr("store ptr " + vfn + ", $" + slot);
	terminate("jump ^" + end);
	start_block(direct);
	string fn = fresh_temp();
	instr(fn + " = copy ptr " + bits);
	instr("store ptr " + fn + ", $" + slot);
	terminate("jump ^" + end);
	start_block(end);
	string loaded = fresh_temp();
	instr(loaded + " = load ptr $" + slot);
	return Value("ptr", loaded);
}

Value FunctionLowerer::emit_call_rvalue(const Node& expr)
{
	if (expr.direct_call != NULL &&
	    (expr.direct_call->name == "__builtin_va_start" ||
	     expr.direct_call->name == "__builtin_va_end"))
	{
		if (expr.direct_call->name == "__builtin_va_start")
			emit_builtin_va_start(expr);
		return Value("void", "");
	}
	if (direct_call_named(expr, "__builtin_alloca"))
		return emit_builtin_alloca(expr);
	if (direct_call_named(expr, "__builtin_assume_aligned"))
		return emit_builtin_assume_aligned(expr);
	if (direct_call_named(expr, "__builtin_prefetch"))
		return emit_builtin_prefetch(expr);
	if (direct_call_named(expr, "__builtin_operator_new") ||
	    direct_call_named(expr, "__builtin_operator_delete"))
		return emit_builtin_operator_new_delete(expr);
	if (direct_call_named(expr, "__builtin_add_overflow") ||
	    direct_call_named(expr, "__builtin_sub_overflow") ||
	    direct_call_named(expr, "__builtin_mul_overflow"))
		return emit_builtin_overflow(expr);
	if (direct_call_named(expr, "__builtin_flt_rounds"))
		return emit_builtin_flt_rounds(expr);
	if (direct_call_named(expr, "__builtin_fpclassify"))
		return emit_builtin_fpclassify(expr);
	if (direct_call_fp_test(expr))
		return emit_builtin_fp_test(expr);
	if (direct_call_float_constant(expr))
		return emit_builtin_float_constant(expr);
	if (direct_call_named(expr, "__builtin_complex"))
	{
		Value real = emit_rvalue(expr.children[1]);
		emit_rvalue(expr.children[2]);
		return convert_value(real, expr.children[1].type, expr.type);
	}
	if (direct_call_bit_count(expr))
		return emit_builtin_bit_count(expr);
	if (expr.direct_call != NULL &&
	    gnu_atomic_builtin_name(expr.direct_call->name))
		return emit_gnu_atomic_builtin(expr);
	if (expr.direct_call != NULL &&
	    c11_atomic_builtin_name(expr.direct_call->name))
		return emit_c11_atomic_builtin(expr);
	bool handled_hash_next = false;
	Value hash_next = emit_hosted_hash_node_next_call(expr,
	                                                  handled_hash_next);
	if (handled_hash_next)
		return hash_next;
	Value value = emit_call(expr);
	if (!is_reference(expr.type))
		return value;
	TypePtr value_type = object_type(expr.type);
	while (is_reference(value_type))
		value_type = object_type(value_type);
	string tmp = fresh_temp();
	instr(tmp + " = load " + scalar_lowir_type(value_type) + " " + value.text);
	return Value(scalar_lowir_type(value_type), tmp);
}

Value FunctionLowerer::emit_array_new_expression(const Node& expr, TypePtr object)
{
	if (expr.children.empty())
		throw runtime_error("array new missing bound");
	if (program_.declared_functions.insert("operator_new__").second)
		program_.declares.push_back(
			"declare function @operator_new__(%arg0 : i64) -> ptr "
			"[binding=strong, object=" +
			string(program_.native_lowering
			       ? "_Znam" : "cppgm_builtin_operator_new_array") + "]");
	bool record_array = object->kind == TypeKind::Record;
	bool constant_record_bound = record_array && expr.children[0].has_constant_value;
	uint64_t constant_count = expr.children[0].constant_value;
	Value raw_count;
	Value count;
	bool u32_record_size =
		record_array && scalar_lowir_type(expr.children[0].type) == "u32";
	string alloc_size;
	string size_slot;
	if (constant_record_bound)
	{
		uint64_t total = constant_count * pa11::type_size(object) + 8;
		alloc_size = fresh_temp();
		instr(alloc_size + " = convert sext i64 i32 " + to_string(total));
	}
	else
	{
		raw_count = emit_rvalue(expr.children[0]);
		count = raw_count;
		if (!u32_record_size)
			count = convert_value(raw_count,
			                      expr.children[0].type,
			                      pa11::make_fundamental(FT_UNSIGNED_LONG_INT));
		string bytes = u32_record_size ? raw_count.text : count.text;
		if (pa11::type_size(object) != 1)
		{
			if (u32_record_size)
			{
				bytes = fresh_temp();
				instr(bytes + " = binary mul u32 " + raw_count.text + ", " +
				      to_string(pa11::type_size(object)));
			}
			else
			{
				string size_tmp = fresh_temp();
				instr(size_tmp + " = convert sext i64 i32 " +
				      to_string(pa11::type_size(object)));
				bytes = fresh_temp();
				instr(bytes + " = binary mul i64 " + count.text + ", " + size_tmp);
			}
		}
		alloc_size = bytes;
		if (record_array && u32_record_size)
		{
			string total32 = fresh_temp();
			instr(total32 + " = binary add u32 " + bytes + ", 8");
			alloc_size = fresh_temp();
			instr(alloc_size + " = convert zext i64 u32 " + total32);
		}
		else if (record_array)
		{
			string total = fresh_temp();
			instr(total + " = binary add i64 " + bytes + ", 8");
			alloc_size = total;
		}
		size_slot = fresh_aux_slot("array_new_size", "i64");
		instr("store i64 " + alloc_size + ", $" + size_slot);
	}
	string call_tmp = fresh_temp();
	instr(call_tmp + " = call ptr @operator_new__(" + alloc_size + ")");
	string result_ptr = call_tmp;
	if (record_array)
	{
		string cookie_count;
		if (constant_record_bound)
		{
			result_ptr = fresh_temp();
			instr(result_ptr + " = index i8 " + call_tmp + ", 8");
			cookie_count = fresh_temp();
			instr(cookie_count + " = const i64 " + to_string(constant_count));
		}
		else
		{
			string stored_size = fresh_temp();
			instr(stored_size + " = load i64 $" + size_slot);
			result_ptr = fresh_temp();
			instr(result_ptr + " = index i8 " + call_tmp + ", 8");
			string payload_size = fresh_temp();
			instr(payload_size + " = binary sub i64 " + stored_size + ", 8");
			cookie_count = fresh_temp();
			instr(cookie_count + " = binary udiv i64 " + payload_size + ", " +
			      to_string(pa11::type_size(object)));
		}
		instr("store i64 " + cookie_count + ", " + call_tmp);
	}
	if (record_array && record_has_default_constructor_for_array(object))
	{
		string index_slot = fresh_aux_slot("array_new_index", "i64");
		string cond_block = fresh_block("array_new_ctor_cond");
		string body_block = fresh_block("array_new_ctor_body");
		string end_block = fresh_block("array_new_ctor_end");
		string constant_bound;
		if (constant_record_bound)
		{
			constant_bound = fresh_temp();
			instr(constant_bound + " = const i64 " + to_string(constant_count));
		}
		instr("store i64 0, $" + index_slot);
		terminate("jump ^" + cond_block);
		start_block(cond_block);
		string idx = fresh_temp();
		instr(idx + " = load i64 $" + index_slot);
		string more = fresh_temp();
		string bound = constant_bound.empty() ? count.text : constant_bound;
		if (!constant_record_bound && u32_record_size)
		{
			bound = fresh_temp();
			instr(bound + " = convert zext i64 u32 " + raw_count.text);
		}
		instr(more + " = cmp ult i64 " + idx + ", " + bound);
		terminate("branch " + more + ", ^" + body_block + ", ^" + end_block);
		start_block(body_block);
		string offset = fresh_temp();
		instr(offset + " = binary mul i64 " + idx + ", " +
		      to_string(pa11::type_size(object)));
		string elem = fresh_temp();
		instr(elem + " = index i8 " + result_ptr + ", " + offset);
		Value elem_addr("ptr", elem);
		function<Value()> addr_for = [elem_addr]() { return elem_addr; };
		lower_default_init(addr_for, object);
		string next = fresh_temp();
		instr(next + " = binary add i64 " + idx + ", 1");
		instr("store i64 " + next + ", $" + index_slot);
		terminate("jump ^" + cond_block);
		start_block(end_block);
	}
	else if (!record_array && expr.token_text == "paren-init")
	{
		string index_slot = fresh_aux_slot("zeroinit_offset", "i64");
		string cond_block = fresh_block("zeroinit_cond");
		string body_block = fresh_block("zeroinit_body");
		string end_block = fresh_block("zeroinit_end");
		string bound = fresh_temp();
		instr(bound + " = load i64 $" + size_slot);
		instr("store i64 0, $" + index_slot);
		terminate("jump ^" + cond_block);
		start_block(cond_block);
		string idx = fresh_temp();
		instr(idx + " = load i64 $" + index_slot);
		string more = fresh_temp();
		instr(more + " = cmp ult i64 " + idx + ", " + bound);
		terminate("branch " + more + ", ^" + body_block + ", ^" + end_block);
		start_block(body_block);
		string elem = fresh_temp();
		instr(elem + " = index i8 " + result_ptr + ", " + idx);
		instr("store i8 0, " + elem);
		string next = fresh_temp();
		instr(next + " = binary add i64 " + idx + ", 1");
		instr("store i64 " + next + ", $" + index_slot);
		terminate("jump ^" + cond_block);
		start_block(end_block);
	}
	return convert_value(Value("ptr", result_ptr), pa11::make_pointer(object), expr.type);
}

Value FunctionLowerer::emit_scalar_new_expression(const Node& expr, TypePtr object)
{
	bool placement = !expr.children.empty() && expr.binding != NULL;
	Value storage;
	size_t arg_start = 0;
	TypePtr placement_param;
	if (placement)
	{
		string size_tmp = fresh_temp();
		instr(size_tmp + " = convert sext i64 i32 " +
		      to_string(pa11::type_size(object)));
		Value size_value("i64", size_tmp);
		program_.demand_function_declaration(expr.binding);
		vector<string> new_args;
		new_args.push_back(size_value.text);
		placement_param = expr.binding->type->parameters.size() > 1
			? expr.binding->type->parameters[1] : expr.children[0].type;
		lower_call_argument(expr.children[0], placement_param, new_args);
		string call_tmp = fresh_temp();
		ostringstream call;
		call << call_tmp << " = call ptr @" << program_.symbol_for(expr.binding) << "(";
		for (size_t i = 0; i < new_args.size(); ++i)
			call << (i != 0 ? ", " : "") << new_args[i];
		call << ")";
		instr(call.str());
		storage = Value("ptr", call_tmp);
		arg_start = 1;
	}
	else
	{
		if (program_.declared_functions.insert("operator_new").second)
			program_.declares.push_back(
				"declare function @operator_new(%arg0 : i64) -> ptr "
				"[binding=strong, object=" +
				string(program_.native_lowering
				       ? "_Znwm" : "cppgm_builtin_operator_new") + "]");
		string size_tmp = fresh_temp();
		instr(size_tmp + " = convert sext i64 i32 " +
		      to_string(pa11::type_size(object)));
		string call_tmp = fresh_temp();
		instr(call_tmp + " = call ptr @operator_new(" + size_tmp + ")");
		storage = Value("ptr", call_tmp);
	}
	Binding* ctor = expr.direct_call;
	if (ctor != NULL)
	{
		bool guard_null = placement && placement_param.get() != NULL &&
			pa11::strip_cv(strip_for_value(placement_param))->kind != TypeKind::Pointer;
		string end_block;
		if (guard_null)
		{
			string init_block = fresh_block("new_init");
			end_block = fresh_block("new_end");
			string nonnull = fresh_temp();
			instr(nonnull + " = cmp ne ptr " + storage.text + ", 0");
			terminate("branch " + nonnull + ", ^" + init_block + ", ^" + end_block);
			start_block(init_block);
		}
		program_.demand_function_declaration(ctor);
		program_.demand_inline_function(ctor);
		vector<string> lowered;
		lowered.push_back(storage.text);
		for (size_t i = arg_start; i < expr.children.size(); ++i)
			lower_call_argument(
				expr.children[i], ctor->type->parameters[i - arg_start + 1], lowered);
		ostringstream call;
		call << "call void @" << program_.symbol_for(ctor) << "(";
		for (size_t i = 0; i < lowered.size(); ++i)
			call << (i != 0 ? ", " : "") << lowered[i];
		call << ")";
		instr(call.str());
		if (guard_null)
		{
			terminate("jump ^" + end_block);
			start_block(end_block);
		}
	}
	else if (arg_start < expr.children.size())
	{
		Value value = convert_value(emit_rvalue(expr.children[arg_start]),
		                            expr.children[arg_start].type,
		                            object);
		instr("store " + scalar_lowir_type(object) + " " + value.text +
		      ", " + storage.text);
	}
	return convert_value(storage, pa11::make_pointer(object), expr.type);
}

Value FunctionLowerer::emit_new_expression(const Node& expr)
{
	TypePtr object = pa11::strip_cv(pa11::strip_cv(expr.type)->base);
	if (expr.line.find(" array") != string::npos)
		return emit_array_new_expression(expr, object);
	return emit_scalar_new_expression(expr, object);
}

Value FunctionLowerer::emit_delete_expression(const Node& expr)
{
	if (expr.children.empty() || expr.binding == NULL)
		return Value("void", "");
	Value pointer = ensure_pointer(emit_rvalue(expr.children[0]));
	TypePtr ptr_type = pa11::strip_cv(strip_for_value(expr.children[0].type));
	TypePtr object = ptr_type->kind == TypeKind::Pointer
		? pa11::strip_cv(ptr_type->base) : TypePtr();
	program_.demand_function_declaration(expr.binding);
	bool array_delete = expr.line.find(" array") != string::npos;
	if (array_delete && object.get() != NULL && object->kind == TypeKind::Record)
	{
		string nonnull = fresh_block("array_delete_nonnull");
		string end = fresh_block("array_delete_end");
		string cond = fresh_temp();
		instr(cond + " = cmp ne ptr " + pointer.text + ", 0");
		terminate("branch " + cond + ", ^" + nonnull + ", ^" + end);
		start_block(nonnull);
		string base = fresh_temp();
		instr(base + " = index i8 " + pointer.text + ", -8");
		string count = fresh_temp();
		instr(count + " = load i64 " + base);
		if (type_needs_cleanup(object))
		{
			string index_slot = fresh_aux_slot("array_delete_index", "i64");
			string dtor_cond = fresh_block("array_delete_dtor_cond");
			string dtor_body = fresh_block("array_delete_dtor_body");
			string dtor_end = fresh_block("array_delete_dtor_end");
			instr("store i64 " + count + ", $" + index_slot);
			terminate("jump ^" + dtor_cond);
			start_block(dtor_cond);
			string idx = fresh_temp();
			instr(idx + " = load i64 $" + index_slot);
			string more = fresh_temp();
			instr(more + " = cmp ne i64 " + idx + ", 0");
			terminate("branch " + more + ", ^" + dtor_body + ", ^" + dtor_end);
			start_block(dtor_body);
			string prev = fresh_temp();
			instr(prev + " = binary sub i64 " + idx + ", 1");
			instr("store i64 " + prev + ", $" + index_slot);
			string offset = fresh_temp();
			instr(offset + " = binary mul i64 " + prev + ", " +
			      to_string(pa11::type_size(object)));
			string elem = fresh_temp();
			instr(elem + " = index i8 " + pointer.text + ", " + offset);
			Value elem_addr("ptr", elem);
			function<Value()> addr_for = [elem_addr]() { return elem_addr; };
			lower_destructor_for_object(addr_for, object);
			terminate("jump ^" + dtor_cond);
			start_block(dtor_end);
		}
		instr("call void @" + program_.symbol_for(expr.binding) + "(" + base + ")");
		terminate("jump ^" + end);
		start_block(end);
		return Value("void", "");
	}
	if (array_delete || object.get() == NULL || object->kind != TypeKind::Record)
	{
		instr("call void @" + program_.symbol_for(expr.binding) + "(" +
		      pointer.text + ")");
		return Value("void", "");
	}
	string nonnull = fresh_block("delete_nonnull");
	string end = fresh_block("delete_end");
	string cond = fresh_temp();
	instr(cond + " = cmp ne ptr " + pointer.text + ", 0");
	terminate("branch " + cond + ", ^" + nonnull + ", ^" + end);
	start_block(nonnull);
	Binding* vdtor = find_destructor(object);
	if (vdtor != NULL && vdtor->is_virtual && vdtor->virtual_slot_index >= 0)
	{
		program_.demand_vtable(object);
		string vptr = fresh_temp();
		instr(vptr + " = load ptr " + pointer.text);
		int deleting_slot = vdtor->virtual_slot_index + 1;
		string slot_addr = vptr;
		if (deleting_slot > 0)
		{
			slot_addr = fresh_temp();
			instr(slot_addr + " = index i8 " + vptr + ", " +
			      to_string(deleting_slot * 8));
		}
		string fnptr = fresh_temp();
		instr(fnptr + " = load ptr " + slot_addr);
		instr("call void " + fnptr + "(" + pointer.text +
		      ") as (%arg0 : ptr) -> void");
		terminate("jump ^" + end);
		start_block(end);
		return Value("void", "");
	}
	function<Value()> addr_for = [pointer]() { return pointer; };
	lower_destructor_for_object(addr_for, object);
	instr("call void @" + program_.symbol_for(expr.binding) + "(" +
	      pointer.text + ")");
	terminate("jump ^" + end);
	start_block(end);
	return Value("void", "");
}

Value FunctionLowerer::emit_pseudo_destructor_rvalue(const Node& expr)
{
	if (expr.direct_call != NULL && !expr.children.empty())
	{
		program_.demand_function_declaration(expr.direct_call);
		program_.demand_inline_function(expr.direct_call);
		Value addr = expr.has_op && expr.op == OP_ARROW
			? emit_rvalue(expr.children[0])
			: emit_lvalue_addr(expr.children[0]);
		addr = ensure_pointer(addr);
		instr("call void @" + program_.symbol_for(expr.direct_call) + "(" +
		      addr.text + ")");
	}
	else if (!expr.children.empty())
		emit_rvalue(expr.children[0]);
	return Value("void", "");
}

Value FunctionLowerer::emit_rvalue(const Node& expr)
{
	if (starts_with(expr.line, "literal "))
		return emit_literal(expr);
	if (starts_with(expr.line, "statement-expression"))
		return emit_statement_expression(expr);
	if (starts_with(expr.line, "member-pointer-function-expression"))
		return emit_member_pointer_function_rvalue(expr);
	if (starts_with(expr.line, "id-expression") ||
	    starts_with(expr.line, "member-expression") ||
	    starts_with(expr.line, "variable "))
		return emit_id_rvalue(expr);
	if (starts_with(expr.line, "binary-expression"))
		return emit_binary(expr);
	if (starts_with(expr.line, "assignment-expression"))
		return emit_assignment(expr);
	if (starts_with(expr.line, "throw-expression"))
		return emit_throw(expr);
	if (starts_with(expr.line, "builtin-va-arg-expression"))
		return emit_builtin_va_arg(expr);
	if (starts_with(expr.line, "unary-expression"))
		return emit_unary(expr);
	if (starts_with(expr.line, "postfix-expression"))
		return emit_postfix(expr);
	if (starts_with(expr.line, "call-expression"))
		return emit_call_rvalue(expr);
	if (starts_with(expr.line, "new-expression"))
		return emit_new_expression(expr);
	if (starts_with(expr.line, "delete-expression"))
		return emit_delete_expression(expr);
	if (starts_with(expr.line, "braced-init-list") ||
	    starts_with(expr.line, "initializer-list-object"))
	{
		TypePtr bare = expr.type.get() != NULL
			? pa11::strip_cv(expr.type) : TypePtr();
		if (bare.get() != NULL &&
		    (bare->kind == TypeKind::Record ||
		     bare->kind == TypeKind::Array))
		{
			string slot = fresh_aux_slot("braced",
			                             slot_lowir_type(expr.type));
			string addr_name = fresh_temp();
			instr(addr_name + " = addr $" + slot);
			Value addr("ptr", addr_name);
			function<Value()> addr_for = [addr]() { return addr; };
			if (starts_with(expr.line, "initializer-list-object"))
				lower_initializer_list_init(addr_for, expr.type, expr);
			else
				lower_object_init(addr_for, expr.type, expr);
			return addr;
		}
		if (expr.children.size() == 1)
			return convert_value(emit_rvalue(expr.children[0]),
			                     expr.children[0].type,
			                     expr.type);
		if (bare.get() != NULL &&
		    bare->kind == TypeKind::Fundamental)
			return Value(scalar_lowir_type(expr.type), "0");
	}
	if (starts_with(expr.line, "subscript-expression") ||
	    starts_with(expr.line, "member-pointer-expression"))
	{
		Value addr = starts_with(expr.line, "subscript-expression")
			? emit_subscript_addr(expr) : emit_lvalue_addr(expr);
		string tmp = fresh_temp();
		instr(tmp + " = load " + scalar_lowir_type(expr.type) + " " + addr.text);
		return Value(scalar_lowir_type(expr.type), tmp);
	}
	if (starts_with(expr.line, "cast-expression") ||
	    starts_with(expr.line, "id-expression xvalue"))
		return emit_cast(expr);
	if (starts_with(expr.line, "conditional-expression"))
		return expr.category == ValueCategory::LValue
			? emit_conditional_value(expr) : emit_conditional(expr);
	if (starts_with(expr.line, "sizeof-expression"))
	{
		string tmp = fresh_temp();
		string value = expr.has_constant_value
			? to_string(expr.constant_value) : expr.token_text;
		instr(tmp + " = const i64 " + value);
		return Value("i64", tmp);
	}
	if (starts_with(expr.line, "pseudo-destructor-expression"))
		return emit_pseudo_destructor_rvalue(expr);
	throw runtime_error("unsupported rvalue expression: " + expr.line);
}

}  // namespace internal
}  // namespace pa14
