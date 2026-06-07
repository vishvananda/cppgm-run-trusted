#include "pa14_lowir_internal.h"

namespace pa14 {
namespace internal {

Value FunctionLowerer::emit_rvalue(const Node& expr)
{
	if (starts_with(expr.line, "literal "))
		return emit_literal(expr);
	if (starts_with(expr.line, "id-expression") ||
	    starts_with(expr.line, "member-expression") ||
	    starts_with(expr.line, "variable "))
		return emit_id_rvalue(expr);
	if (starts_with(expr.line, "binary-expression"))
		return emit_binary(expr);
	if (starts_with(expr.line, "assignment-expression"))
		return emit_assignment(expr);
	if (starts_with(expr.line, "unary-expression"))
		return emit_unary(expr);
	if (starts_with(expr.line, "postfix-expression"))
		return emit_postfix(expr);
	if (starts_with(expr.line, "call-expression"))
	{
		Value value = emit_call(expr);
		if (is_reference(expr.type))
		{
			TypePtr value_type = object_type(expr.type);
			while (is_reference(value_type))
				value_type = object_type(value_type);
			string tmp = fresh_temp();
			instr(tmp + " = load " + scalar_lowir_type(value_type) +
			      " " + value.text);
			return Value(scalar_lowir_type(value_type), tmp);
		}
		return value;
	}
	if (starts_with(expr.line, "new-expression"))
	{
		TypePtr object = pa11::strip_cv(pa11::strip_cv(expr.type)->base);
		bool array_new = expr.line.find(" array") != string::npos;
		if (array_new)
		{
			if (expr.children.empty())
				throw runtime_error("array new missing bound");
			if (program_.declared_functions.insert("operator_new__").second)
				program_.declares.push_back(
					"declare function @operator_new__(%arg0 : i64) -> ptr "
					"[binding=strong, object=cppgm_builtin_operator_new_array]");
			bool record_array = object->kind == TypeKind::Record;
			bool constant_record_bound =
				record_array && expr.children[0].has_constant_value;
			uint64_t constant_count = expr.children[0].constant_value;
			Value raw_count;
			Value count;
			bool u32_record_size =
				record_array &&
				scalar_lowir_type(expr.children[0].type) == "u32";
			string alloc_size;
			string size_slot;
			if (constant_record_bound)
			{
				uint64_t total =
					constant_count * pa11::type_size(object) + 8;
				alloc_size = fresh_temp();
				instr(alloc_size + " = convert sext i64 i32 " +
				      to_string(total));
			}
			else
			{
				raw_count = emit_rvalue(expr.children[0]);
				count = raw_count;
				if (!u32_record_size)
					count = convert_value(
						raw_count,
						expr.children[0].type,
						pa11::make_fundamental(FT_UNSIGNED_LONG_INT));
				string bytes = u32_record_size ? raw_count.text : count.text;
				if (pa11::type_size(object) != 1)
				{
					if (u32_record_size)
					{
						bytes = fresh_temp();
						instr(bytes + " = binary mul u32 " +
						      raw_count.text + ", " +
						      to_string(pa11::type_size(object)));
					}
					else
					{
						string size_tmp = fresh_temp();
						instr(size_tmp +
						      " = convert sext i64 i32 " +
						      to_string(pa11::type_size(object)));
						bytes = fresh_temp();
						instr(bytes + " = binary mul i64 " +
						      count.text + ", " + size_tmp);
					}
				}
				alloc_size = bytes;
				if (record_array && u32_record_size)
				{
					string total32 = fresh_temp();
					instr(total32 + " = binary add u32 " + bytes + ", 8");
					alloc_size = fresh_temp();
					instr(alloc_size + " = convert zext i64 u32 " +
					      total32);
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
				if (constant_record_bound)
				{
					result_ptr = fresh_temp();
					instr(result_ptr + " = index i8 " + call_tmp + ", 8");
					string cookie_count = fresh_temp();
					instr(cookie_count + " = const i64 " +
					      to_string(constant_count));
					instr("store i64 " + cookie_count + ", " + call_tmp);
				}
				else
				{
					string stored_size = fresh_temp();
					instr(stored_size + " = load i64 $" + size_slot);
					result_ptr = fresh_temp();
					instr(result_ptr + " = index i8 " + call_tmp + ", 8");
					string payload_size = fresh_temp();
					instr(payload_size + " = binary sub i64 " +
					      stored_size + ", 8");
					string cookie_count = fresh_temp();
					instr(cookie_count + " = binary udiv i64 " +
					      payload_size + ", " +
					      to_string(pa11::type_size(object)));
					instr("store i64 " + cookie_count + ", " + call_tmp);
				}
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
					instr(constant_bound + " = const i64 " +
					      to_string(constant_count));
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
				terminate("branch " + more + ", ^" + body_block +
				          ", ^" + end_block);
				start_block(body_block);
				string offset = fresh_temp();
				instr(offset + " = binary mul i64 " + idx + ", " +
				      to_string(pa11::type_size(object)));
				string elem = fresh_temp();
				instr(elem + " = index i8 " + result_ptr + ", " + offset);
				Value elem_addr("ptr", elem);
				function<Value()> addr_for = [elem_addr]() {
					return elem_addr;
				};
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
				terminate("branch " + more + ", ^" + body_block +
				          ", ^" + end_block);
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
			return convert_value(Value("ptr", result_ptr),
			                     pa11::make_pointer(object),
			                     expr.type);
		}
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
			call << call_tmp << " = call ptr @" << program_.symbol_for(expr.binding)
			     << "(";
			for (size_t i = 0; i < new_args.size(); ++i)
			{
				if (i != 0)
					call << ", ";
				call << new_args[i];
			}
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
					"[binding=strong, object=cppgm_builtin_operator_new]");
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
			bool guard_null = placement &&
				placement_param.get() != NULL &&
				pa11::strip_cv(strip_for_value(placement_param))->kind !=
				TypeKind::Pointer;
			string end_block;
			if (guard_null)
			{
				string init_block = fresh_block("new_init");
				end_block = fresh_block("new_end");
				string nonnull = fresh_temp();
				instr(nonnull + " = cmp ne ptr " + storage.text + ", 0");
				terminate("branch " + nonnull + ", ^" + init_block +
				          ", ^" + end_block);
				start_block(init_block);
			}
			program_.demand_function_declaration(ctor);
			program_.demand_inline_function(ctor);
			vector<string> lowered;
			lowered.push_back(storage.text);
				for (size_t i = arg_start; i < expr.children.size(); ++i)
				{
					TypePtr param = ctor->type->parameters[i - arg_start + 1];
					lower_call_argument(expr.children[i], param, lowered);
				}
			ostringstream call;
			call << "call void @" << program_.symbol_for(ctor) << "(";
			for (size_t i = 0; i < lowered.size(); ++i)
			{
				if (i != 0)
					call << ", ";
				call << lowered[i];
			}
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
			instr("store " + scalar_lowir_type(object) + " " +
			      value.text + ", " + storage.text);
		}
		return convert_value(storage,
		                     pa11::make_pointer(object),
		                     expr.type);
	}
	if (starts_with(expr.line, "delete-expression"))
	{
		if (expr.children.empty() || expr.binding == NULL)
			return Value("void", "");
		Value pointer = ensure_pointer(emit_rvalue(expr.children[0]));
		TypePtr ptr_type =
			pa11::strip_cv(strip_for_value(expr.children[0].type));
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
				terminate("branch " + more + ", ^" + dtor_body +
				          ", ^" + dtor_end);
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
				function<Value()> addr_for = [elem_addr]() {
					return elem_addr;
				};
				lower_destructor_for_object(addr_for, object);
				terminate("jump ^" + dtor_cond);
				start_block(dtor_end);
			}
			instr("call void @" + program_.symbol_for(expr.binding) +
			      "(" + base + ")");
			terminate("jump ^" + end);
			start_block(end);
			return Value("void", "");
		}
		if (array_delete ||
		    object.get() == NULL ||
		    object->kind != TypeKind::Record)
		{
			instr("call void @" + program_.symbol_for(expr.binding) +
			      "(" + pointer.text + ")");
			return Value("void", "");
		}
		string nonnull = fresh_block("delete_nonnull");
		string end = fresh_block("delete_end");
		string cond = fresh_temp();
		instr(cond + " = cmp ne ptr " + pointer.text + ", 0");
		terminate("branch " + cond + ", ^" + nonnull + ", ^" + end);
		start_block(nonnull);
		Binding* vdtor = find_destructor(object);
		if (vdtor != NULL && vdtor->is_virtual &&
		    vdtor->virtual_slot_index >= 0)
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
		function<Value()> addr_for = [pointer]() {
			return pointer;
		};
		lower_destructor_for_object(addr_for, object);
		instr("call void @" + program_.symbol_for(expr.binding) +
		      "(" + pointer.text + ")");
		terminate("jump ^" + end);
		start_block(end);
		return Value("void", "");
	}
	if (starts_with(expr.line, "subscript-expression"))
	{
		Value addr = emit_subscript_addr(expr);
		string tmp = fresh_temp();
		instr(tmp + " = load " + scalar_lowir_type(expr.type) + " " + addr.text);
		return Value(scalar_lowir_type(expr.type), tmp);
	}
	if (starts_with(expr.line, "cast-expression") ||
	    starts_with(expr.line, "id-expression xvalue"))
		return emit_cast(expr);
	if (starts_with(expr.line, "conditional-expression"))
	{
		if (expr.category == ValueCategory::LValue)
			return emit_conditional_value(expr);
		return emit_conditional(expr);
	}
	if (starts_with(expr.line, "sizeof-expression"))
	{
		string tmp = fresh_temp();
		instr(tmp + " = const i64 " + expr.token_text);
		return Value("i64", tmp);
	}
	if (starts_with(expr.line, "pseudo-destructor-expression"))
	{
		if (expr.direct_call != NULL && !expr.children.empty())
		{
			program_.demand_function_declaration(expr.direct_call);
			program_.demand_inline_function(expr.direct_call);
			Value addr = expr.has_op && expr.op == OP_ARROW
				? emit_rvalue(expr.children[0])
				: emit_lvalue_addr(expr.children[0]);
			addr = ensure_pointer(addr);
			instr("call void @" + program_.symbol_for(expr.direct_call) +
			      "(" + addr.text + ")");
		}
		else if (!expr.children.empty())
			emit_rvalue(expr.children[0]);
		return Value("void", "");
	}
	throw runtime_error("unsupported rvalue expression: " + expr.line);
}

Value FunctionLowerer::convert_value(Value value,
                                     TypePtr from,
                                     TypePtr to,
                                     bool fold_literals)
{
	string dst = scalar_lowir_type(to);
	string src = scalar_lowir_type(strip_for_value(from));
	TypePtr from_bare = pa11::strip_cv(strip_for_value(from));
	TypePtr to_bare = pa11::strip_cv(strip_for_value(to));
	if (from_bare->kind == TypeKind::Fundamental &&
	    from_bare->fundamental == FT_NULLPTR_T &&
	    to_bare->kind == TypeKind::Pointer)
	{
		string tmp = fresh_temp();
		instr(tmp + " = copy ptr " + value.text);
		return Value(dst, tmp);
	}
	if (from_bare->kind == TypeKind::Pointer &&
	    to_bare->kind == TypeKind::Fundamental &&
	    to_bare->fundamental == FT_BOOL)
	{
		string cmp = fresh_temp();
		instr(cmp + " = cmp ne ptr " + value.text + ", 0");
		string tmp = fresh_temp();
		instr(tmp + " = copy u8 " + cmp);
		return Value("u8", tmp);
	}
	if (dst == src)
	{
		if (from_bare->kind == TypeKind::Pointer &&
		    to_bare->kind == TypeKind::Pointer)
		{
			TypePtr from_pointee = pa11::strip_cv(from_bare->base);
			TypePtr to_pointee = pa11::strip_cv(to_bare->base);
			if (from_pointee->kind == TypeKind::Record &&
			    to_pointee->kind == TypeKind::Record &&
			    record_has_base_subobject(from_pointee, to_pointee))
			{
				return emit_base_subobject_addr(value,
				                                from_pointee,
				                                to_pointee);
			}
		}
		return Value(dst, value.text);
	}
	if (fold_literals &&
	    value.text != "" && value.text[0] != '%' &&
	    value.text[0] != '$' && value.text[0] != '@' &&
	    !is_float_type(from) && !is_float_type(to) &&
	    (value.text == "0" || (dst != "ptr" && src != "ptr")))
		return Value(dst, value.text);
	string op = "copy";
	if (dst == "ptr" || src == "ptr")
		op = "copy";
	else if (starts_with(dst, "f") && starts_with(src, "f"))
		op = pa11::type_size(to) > pa11::type_size(from) ? "fpext" : "fptrunc";
	else if (starts_with(dst, "f"))
	{
		bool literal_zero =
			value.text == "0" &&
			value.text[0] != '%' &&
			value.text[0] != '$' &&
			value.text[0] != '@';
		if (pa11::is_integral_or_bool_type(from) &&
		    pa11::type_size(from_bare) < 8 &&
		    !literal_zero)
		{
			int shift = (8 - pa11::type_size(from_bare)) * 8;
			string shifted = fresh_temp();
			instr(shifted + " = binary shl i64 " + value.text +
			      ", " + to_string(shift));
			string normalized = fresh_temp();
			instr(normalized + " = binary " +
			      string(is_unsigned_type(from) ? "ushr" : "shr") +
			      " i64 " + shifted + ", " + to_string(shift));
			value = Value(value.type, normalized);
		}
		op = is_unsigned_type(from) ? "uitofp" : "sitofp";
	}
	else if (starts_with(src, "f"))
		op = is_unsigned_type(to) ? "fptoui" : "fptosi";
	else if ((is_reference(from) ? pa11::type_size(strip_for_value(from))
	                             : pa11::type_size(from)) ==
	         (is_reference(to) ? pa11::type_size(strip_for_value(to))
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
		instr(tmp + " = convert " + op + " " + dst + " " + src + " " +
		      value.text);
	return Value(dst, tmp);
}

Value FunctionLowerer::convert_binary_value(Value value, TypePtr from, TypePtr to)
{
	string dst = scalar_lowir_type(to);
	string src = scalar_lowir_type(strip_for_value(from));
	if (dst == "i64" && src != dst && is_unsigned_type(to) &&
	    value.text != "" &&
	    value.text[0] != '%' && value.text[0] != '$' &&
	    value.text[0] != '@' && !is_float_type(from) && !is_float_type(to))
	{
		string tmp = fresh_temp();
		instr(tmp + " = convert " + string(is_unsigned_type(from) ? "zext" : "sext") +
		      " i64 " + src + " " + value.text);
		return Value("i64", tmp);
	}
	return convert_value(value, from, to);
}

Value FunctionLowerer::bool_value(Value value, TypePtr type)
{
	string src = scalar_lowir_type(strip_for_value(type));
	string cmp_type = (!is_float_type(type) && src != "ptr") ? "i64" : src;
	string tmp = fresh_temp();
	string zero = is_float_type(type) ? "0.0" : "0";
	instr(tmp + " = cmp ne " + cmp_type + " " + value.text + ", " + zero);
	return Value("u8", tmp);
}

Value FunctionLowerer::ensure_pointer(Value storage)
{
	if (storage.text.empty())
		return storage;
	if (storage.text[0] != '$' && storage.text[0] != '@')
		return storage;
	string tmp = fresh_temp();
	instr(tmp + " = addr " + storage.text);
	return Value("ptr", tmp);
}

void FunctionLowerer::branch_logical_operand(const Node& expr,
                                             const string& yes,
                                             const string& no)
{
	if (starts_with(expr.line, "binary-expression") && expr.has_op &&
	    (expr.op == OP_LAND || expr.op == OP_LOR))
	{
		Value value = emit_rvalue(expr);
		terminate_with_pending_temp_cleanups(value.text, yes, no);
		return;
	}
	branch_on(expr, yes, no);
}

void FunctionLowerer::branch_with_unwind_cleanups(const Node& expr,
                                                  const string& yes,
                                                  const string& no)
{
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
	if (define_dispatch)
	{
		string end = fresh_block("call_unwind_end");
		terminate("jump ^" + end);
		active_unwind_dispatch_ = dispatch;
		start_block(dispatch);
		emit_unwind_cleanups();
		terminate("resume");
		start_block(end);
	}
	terminate_with_pending_temp_cleanups(cond.text, yes, no);
}

Value FunctionLowerer::emit_binary(const Node& expr)
{
	if (expr.has_op && expr.op == OP_COMMA)
	{
		emit_rvalue(expr.children[0]);
		return emit_rvalue(expr.children[1]);
	}
	if (expr.has_op && (expr.op == OP_LAND || expr.op == OP_LOR))
		return emit_logical_binary(expr);
	Value lhs = emit_rvalue(expr.children[0]);
	Value rhs = emit_rvalue(expr.children[1]);
	TypePtr lhs_type = strip_for_value(expr.children[0].type);
	TypePtr rhs_type = strip_for_value(expr.children[1].type);
	if ((expr.op == OP_PLUS || expr.op == OP_MINUS) &&
	    scalar_lowir_type(expr.type) == "ptr")
		return emit_pointer_index_binary(expr, lhs, rhs, lhs_type, rhs_type);
	if (expr.op == OP_MINUS &&
	    pa11::strip_cv(lhs_type)->kind == TypeKind::Pointer &&
	    pa11::strip_cv(rhs_type)->kind == TypeKind::Pointer)
		return emit_pointer_difference(expr, lhs, rhs, lhs_type);
	string op;
	bool cmp = false;
	switch (expr.op)
	{
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
	default: throw runtime_error("unsupported binary operator");
	}
	TypePtr op_type = cmp ? lowir_common_type(expr.children[0].type,
	                                          expr.children[1].type)
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
	if (cmp && scalar_lowir_type(op_type) == "ptr")
	{
		if (scalar_lowir_type(strip_for_value(expr.children[0].type)) != "ptr")
			lhs = convert_binary_value(lhs, expr.children[0].type, op_type);
		if (scalar_lowir_type(strip_for_value(expr.children[1].type)) != "ptr")
			rhs = convert_binary_value(rhs, expr.children[1].type, op_type);
	}
	else
	{
		lhs = convert_binary_value(lhs, expr.children[0].type, op_type);
		rhs = convert_binary_value(rhs, expr.children[1].type, op_type);
	}
	string type = scalar_lowir_type(op_type);
	string tmp = fresh_temp();
	instr(tmp + " = " + string(cmp ? "cmp " : "binary ") + op + " " +
	      type + " " + lhs.text + ", " + rhs.text);
	return Value(cmp ? "u8" : scalar_lowir_type(expr.type), tmp);
}

Value FunctionLowerer::emit_assignment(const Node& expr)
{
	if (expr.op == OP_ASS && expr.children.size() == 2 &&
	    pa11::strip_cv(object_type(expr.children[0].type))->kind ==
	    TypeKind::Record)
	{
		TypePtr lhs_type = object_type(expr.children[0].type);
		bool move_assign = expr.children[1].category != ValueCategory::LValue;
		Binding* assign =
			program_.demand_implicit_copy_assignment(lhs_type, move_assign);
		bool wrap = eh_try_depth_ == 0 && has_active_cleanups();
		string dispatch;
		bool define_dispatch = false;
		if (wrap)
		{
			dispatch = active_unwind_dispatch_.empty()
				? fresh_block("call_unwind_dispatch")
				: active_unwind_dispatch_;
			define_dispatch = active_unwind_dispatch_.empty();
			instr("eh_try ^" + dispatch);
			++eh_try_depth_;
		}
		Value target = ensure_pointer(emit_lvalue_addr(expr.children[0]));
		TypePtr rhs_type = object_type(expr.children[1].type);
		Value source;
		if (expr.children[1].category == ValueCategory::LValue ||
		    expr.children[1].category == ValueCategory::XValue)
			source = ensure_pointer(emit_lvalue_addr(expr.children[1]));
		else
		{
			TypePtr object = pa11::strip_cv(rhs_type);
			string slot = fresh_aux_slot("assignarg", scalar_lowir_type(object));
			string addr = fresh_temp();
			instr(addr + " = addr $" + slot);
			source = Value("ptr", addr);
			function<Value()> source_addr = [source]() {
				return source;
			};
			lower_object_init(source_addr, object, expr.children[1]);
		}
		string tmp = fresh_temp();
		instr(tmp + " = call ptr @" + program_.symbol_for(assign) +
		      "(" + target.text + ", " + source.text + ")");
		if (wrap)
		{
			--eh_try_depth_;
			instr("eh_end");
			if (define_dispatch)
			{
				string end = fresh_block("call_unwind_end");
				terminate("jump ^" + end);
				active_unwind_dispatch_ = dispatch;
				start_block(dispatch);
				emit_unwind_cleanups();
				terminate("resume");
				start_block(end);
			}
		}
		return Value("ptr", tmp);
	}
	if (expr.op == OP_ASS &&
	    starts_with(expr.children[0].line, "member-expression"))
	{
		TypePtr lhs_type = object_type(expr.children[0].type);
		Value rhs = emit_rvalue(expr.children[1]);
		rhs = convert_binary_value(rhs, expr.children[1].type, lhs_type);
		Value addr = emit_lvalue_addr(expr.children[0]);
		if (expr.children[0].binding != NULL &&
		    expr.children[0].binding->is_bit_field)
		{
			Binding* field = expr.children[0].binding;
			string low_type = scalar_lowir_type(lhs_type);
			uint64_t mask = field->bit_width >= 64
				? ~uint64_t(0) : ((uint64_t(1) << field->bit_width) - 1);
			string masked = fresh_temp();
			instr(masked + " = binary and " + low_type + " " +
			      rhs.text + ", " + to_string(mask));
			string shifted = masked;
			uint64_t storage_mask = mask << field->bit_offset;
			if (field->bit_offset != 0)
			{
				shifted = fresh_temp();
				instr(shifted + " = binary shl " + low_type + " " +
				      masked + ", " + to_string(field->bit_offset));
			}
			string oldv = fresh_temp();
			instr(oldv + " = load " + low_type + " " + addr.text);
			string cleared = fresh_temp();
			instr(cleared + " = binary and " + low_type + " " + oldv +
			      ", " + to_string(~storage_mask));
			string merged = fresh_temp();
			instr(merged + " = binary or " + low_type + " " + cleared +
			      ", " + shifted);
			instr("store " + low_type + " " + merged + ", " + addr.text);
			return rhs;
		}
		instr("store " + scalar_lowir_type(lhs_type) + " " + rhs.text +
		      ", " + addr.text);
		return rhs;
	}
	TypePtr lhs_type = object_type(expr.children[0].type);
	if (expr.op != OP_ASS)
	{
		Value oldv = emit_rvalue(expr.children[0]);
		Value rhs = emit_rvalue(expr.children[1]);
		if (scalar_lowir_type(lhs_type) == "ptr" &&
		    (expr.op == OP_PLUSASS || expr.op == OP_MINUSASS))
		{
			TypePtr ptr = pa11::strip_cv(strip_for_value(lhs_type));
			uint64_t scale = pa11::type_size(ptr->base);
			string offset = rhs.text;
			if (scale != 1)
			{
				string mul = fresh_temp();
				instr(mul + " = binary mul i64 " + offset + ", " +
				      to_string(scale));
				offset = mul;
			}
			if (expr.op == OP_MINUSASS)
			{
				string neg = fresh_temp();
				instr(neg + " = binary sub i64 0, " + offset);
				offset = neg;
			}
			string tmp = fresh_temp();
			instr(tmp + " = index i8 " + oldv.text + ", " + offset);
			Value addr = emit_lvalue_addr(expr.children[0]);
			instr("store ptr " + tmp + ", " + addr.text);
			return Value("ptr", tmp);
		}
		rhs = convert_value(rhs, expr.children[1].type, lhs_type);
		ETokenType op = expr.op == OP_PLUSASS ? OP_PLUS :
		                expr.op == OP_MINUSASS ? OP_MINUS :
		                expr.op == OP_STARASS ? OP_STAR :
		                expr.op == OP_DIVASS ? OP_DIV : OP_PLUS;
		string tmp = fresh_temp();
		instr(tmp + " = binary " + string(op == OP_MINUS ? "sub" :
		      op == OP_STAR ? "mul" : op == OP_DIV ? "div" : "add") + " " +
		      scalar_lowir_type(lhs_type) + " " + oldv.text + ", " + rhs.text);
		rhs = Value(scalar_lowir_type(lhs_type), tmp);
		Value addr = emit_lvalue_addr(expr.children[0]);
		instr("store " + scalar_lowir_type(lhs_type) + " " +
		      rhs.text + ", " + addr.text);
		return rhs;
	}
	Value rhs = emit_rvalue(expr.children[1]);
	rhs = convert_binary_value(rhs, expr.children[1].type, lhs_type);
	Value addr = emit_lvalue_addr(expr.children[0]);
	instr("store " + scalar_lowir_type(lhs_type) + " " + rhs.text + ", " + addr.text);
	return rhs;
}

Value FunctionLowerer::emit_unary(const Node& expr)
{
	if (expr.op == OP_AMP)
	{
		if (!expr.children.empty() &&
		    expr.children[0].binding != NULL &&
		    expr.children[0].binding->kind == BindingKind::Function)
		{
			if (expr.children[0].binding->is_inline_definition)
				program_.demand_inline_function(expr.children[0].binding);
			string addr = fresh_temp();
			instr(addr + " = addr @" +
			      program_.symbol_for(expr.children[0].binding));
			return Value("ptr", addr);
		}
		return ensure_pointer(emit_lvalue_addr(expr.children[0]));
	}
	if (expr.op == OP_STAR)
	{
		Value addr = emit_lvalue_addr(expr);
		string tmp = fresh_temp();
		instr(tmp + " = load " + scalar_lowir_type(expr.type) + " " + addr.text);
		return Value(scalar_lowir_type(expr.type), tmp);
	}
	if (expr.op == OP_INC || expr.op == OP_DEC)
	{
		Value addr = emit_lvalue_addr(expr.children[0]);
		TypePtr value_type = strip_for_value(expr.children[0].type);
		string oldtmp = fresh_temp();
		instr(oldtmp + " = load " + scalar_lowir_type(value_type) + " " +
		      addr.text);
		Value oldv(scalar_lowir_type(value_type), oldtmp);
		string one = "1";
		string tmp;
		if (oldv.type == "ptr")
		{
			TypePtr ptr = pa11::strip_cv(strip_for_value(expr.type));
			uint64_t scale = pa11::type_size(ptr->base);
			if (expr.op == OP_DEC && scale == 1)
				one = "-1";
			else if (expr.op == OP_DEC)
			{
				string mul = fresh_temp();
				instr(mul + " = binary mul i64 1, " + to_string(scale));
				string neg = fresh_temp();
				instr(neg + " = binary sub i64 0, " + mul);
				one = neg;
			}
			else if (scale != 1)
			{
				string mul = fresh_temp();
				instr(mul + " = binary mul i64 1, " + to_string(scale));
				one = mul;
			}
			tmp = fresh_temp();
			instr(tmp + " = index i8 " + oldv.text + ", " + one);
		}
		else
		{
			tmp = fresh_temp();
			instr(tmp + " = binary " + string(expr.op == OP_INC ? "add" : "sub") +
			      " " + scalar_lowir_type(expr.type) + " " + oldv.text + ", " + one);
		}
		instr("store " + scalar_lowir_type(expr.type) + " " + tmp + ", " + addr.text);
		return Value(scalar_lowir_type(expr.type), tmp);
	}
	Value inner = emit_rvalue(expr.children[0]);
	if (expr.op == OP_PLUS)
		return inner;
	string op = expr.op == OP_MINUS ? "neg" :
	            expr.op == OP_COMPL ? "bitnot" : "not";
	if (expr.op == OP_LNOT)
	{
		string tmp = fresh_temp();
		string cmp_type = (!is_float_type(expr.children[0].type) &&
		                   inner.type != "ptr") ? "i64" : inner.type;
			string zero = is_float_type(expr.children[0].type) ? "0.0" : "0";
		instr(tmp + " = cmp eq " + cmp_type + " " + inner.text + ", " + zero);
		return Value("u8", tmp);
	}
	string tmp = fresh_temp();
	instr(tmp + " = unary " + op + " " + inner.type + " " + inner.text);
	return Value(inner.type, tmp);
}

Value FunctionLowerer::emit_postfix(const Node& expr)
{
	Value addr = emit_lvalue_addr(expr.children[0]);
	TypePtr value_type = strip_for_value(expr.children[0].type);
	string oldtmp = fresh_temp();
	instr(oldtmp + " = load " + scalar_lowir_type(value_type) + " " + addr.text);
	Value oldv(scalar_lowir_type(value_type), oldtmp);
	string one = "1";
	string tmp;
	if (oldv.type == "ptr")
	{
		TypePtr ptr = pa11::strip_cv(strip_for_value(expr.type));
		uint64_t scale = pa11::type_size(ptr->base);
		if (expr.op == OP_DEC && scale == 1)
			one = "-1";
		else if (expr.op == OP_DEC)
		{
			string mul = fresh_temp();
			instr(mul + " = binary mul i64 1, " + to_string(scale));
			string neg = fresh_temp();
			instr(neg + " = binary sub i64 0, " + mul);
			one = neg;
		}
		else if (scale != 1)
		{
			string mul = fresh_temp();
			instr(mul + " = binary mul i64 1, " + to_string(scale));
			one = mul;
		}
		tmp = fresh_temp();
		instr(tmp + " = index i8 " + oldv.text + ", " + one);
	}
	else
	{
		tmp = fresh_temp();
		instr(tmp + " = binary " + string(expr.op == OP_INC ? "add" : "sub") +
		      " " + oldv.type + " " + oldv.text + ", 1");
	}
	instr("store " + oldv.type + " " + tmp + ", " + addr.text);
	return oldv;
}

Value FunctionLowerer::emit_cast(const Node& expr)
{
	if (pa11::is_void_type(expr.type))
	{
		if (expr.children[0].category == ValueCategory::LValue &&
		    pa11::strip_cv(object_type(expr.children[0].type))->kind ==
		    TypeKind::Record)
			ensure_pointer(emit_lvalue_addr(expr.children[0]));
		else
			lower_discarded_expr(expr.children[0]);
		return Value("void", "");
	}
	if (is_reference(expr.type))
		return emit_rvalue(expr.children[0]);
	TypePtr cast_source = pa11::strip_cv(strip_for_value(expr.children[0].type));
	TypePtr cast_target = pa11::strip_cv(strip_for_value(expr.type));
	if (cast_source->kind == TypeKind::Enum &&
	    cast_source->enum_underlying != FT_INT &&
	    cast_target->kind == TypeKind::Fundamental &&
	    scalar_lowir_type(expr.children[0].type) == scalar_lowir_type(expr.type))
	{
		Value raw = emit_rvalue(expr.children[0]);
		string tmp = fresh_temp();
		instr(tmp + " = copy " + scalar_lowir_type(expr.type) + " " +
		      raw.text);
		return Value(scalar_lowir_type(expr.type), tmp);
	}
	if (cast_source->kind == TypeKind::Fundamental &&
	    cast_target->kind == TypeKind::Fundamental &&
	    cast_source->fundamental == FT_LONG_INT &&
	    cast_target->fundamental == FT_UNSIGNED_LONG_INT &&
	    scalar_lowir_type(expr.children[0].type) == scalar_lowir_type(expr.type))
	{
		Value raw = emit_rvalue(expr.children[0]);
		string tmp = fresh_temp();
		instr(tmp + " = copy " + scalar_lowir_type(expr.type) + " " +
		      raw.text);
		return Value(scalar_lowir_type(expr.type), tmp);
	}
	return convert_value(emit_rvalue(expr.children[0]),
	                     expr.children[0].type,
	                     expr.type);
}

Value FunctionLowerer::emit_conditional(const Node& expr)
{
	string type = expr.category == ValueCategory::LValue ? "ptr" :
	              scalar_lowir_type(expr.type);
	string slot = fresh_aux_slot(expr.category == ValueCategory::LValue ?
	                             "condaddr" : "cond", type);
	string yes = fresh_block(expr.category == ValueCategory::LValue ?
	                         "condaddr_then" : "cond_then");
	string no = fresh_block(expr.category == ValueCategory::LValue ?
	                        "condaddr_else" : "cond_else");
	string end = fresh_block(expr.category == ValueCategory::LValue ?
	                         "condaddr_end" : "cond_end");
	if (eh_try_depth_ == 0 && has_active_cleanups() &&
	    node_contains_call_expression(expr.children[0]))
		branch_with_unwind_cleanups(expr.children[0], yes, no);
	else
	{
		Value cond = emit_rvalue(expr.children[0]);
		if (is_float_type(expr.children[0].type))
			cond = bool_value(cond, expr.children[0].type);
		terminate_with_pending_temp_cleanups(cond.text, yes, no);
	}
	start_block(yes);
	Value yv;
	if (expr.category == ValueCategory::LValue)
		yv = ensure_pointer(emit_lvalue_addr(expr.children[1]));
	else
	{
		if (starts_with(expr.children[1].line, "call-expression"))
		{
			call_result_store_slot_ = slot;
			call_result_store_type_ = expr.type;
			call_result_store_consumed_ = false;
		}
		yv = emit_rvalue(expr.children[1]);
		if (!call_result_store_consumed_)
			yv = convert_value(yv, expr.children[1].type, expr.type);
	}
	if (expr.category == ValueCategory::LValue)
		yv = convert_value(yv,
		                   pa11::make_pointer(object_type(expr.children[1].type)),
		                   pa11::make_pointer(expr.type));
	if (!call_result_store_consumed_)
		instr("store " + type + " " + yv.text + ", $" + slot);
	call_result_store_slot_.clear();
	call_result_store_type_.reset();
	call_result_store_consumed_ = false;
	emit_pending_temp_cleanups();
	terminate("jump ^" + end);
	start_block(no);
	Value nv;
	if (expr.category == ValueCategory::LValue)
		nv = ensure_pointer(emit_lvalue_addr(expr.children[2]));
	else
	{
		if (starts_with(expr.children[2].line, "call-expression"))
		{
			call_result_store_slot_ = slot;
			call_result_store_type_ = expr.type;
			call_result_store_consumed_ = false;
		}
		nv = emit_rvalue(expr.children[2]);
		if (!call_result_store_consumed_)
			nv = convert_value(nv, expr.children[2].type, expr.type);
	}
	if (expr.category == ValueCategory::LValue)
		nv = convert_value(nv,
		                   pa11::make_pointer(object_type(expr.children[2].type)),
		                   pa11::make_pointer(expr.type));
	if (!call_result_store_consumed_)
		instr("store " + type + " " + nv.text + ", $" + slot);
	call_result_store_slot_.clear();
	call_result_store_type_.reset();
	call_result_store_consumed_ = false;
	emit_pending_temp_cleanups();
	terminate("jump ^" + end);
	start_block(end);
	string tmp = fresh_temp();
	instr(tmp + " = load " + type + " $" + slot);
	return Value(type, tmp);
}

Value FunctionLowerer::emit_conditional_value(const Node& expr)
{
	string type = scalar_lowir_type(expr.type);
	string slot = fresh_aux_slot("cond", type);
	string yes = fresh_block("cond_then");
	string no = fresh_block("cond_else");
	string end = fresh_block("cond_end");
	if (eh_try_depth_ == 0 && has_active_cleanups() &&
	    node_contains_call_expression(expr.children[0]))
		branch_with_unwind_cleanups(expr.children[0], yes, no);
	else
	{
		Value cond = emit_rvalue(expr.children[0]);
		if (is_float_type(expr.children[0].type))
			cond = bool_value(cond, expr.children[0].type);
		terminate_with_pending_temp_cleanups(cond.text, yes, no);
	}
	start_block(yes);
	if (starts_with(expr.children[1].line, "call-expression"))
	{
		call_result_store_slot_ = slot;
		call_result_store_type_ = expr.type;
		call_result_store_consumed_ = false;
	}
	Value yv = emit_rvalue(expr.children[1]);
	if (!call_result_store_consumed_)
	{
		yv = convert_value(yv, expr.children[1].type, expr.type);
		instr("store " + type + " " + yv.text + ", $" + slot);
	}
	call_result_store_slot_.clear();
	call_result_store_type_.reset();
	call_result_store_consumed_ = false;
	emit_pending_temp_cleanups();
	terminate("jump ^" + end);
	start_block(no);
	if (starts_with(expr.children[2].line, "call-expression"))
	{
		call_result_store_slot_ = slot;
		call_result_store_type_ = expr.type;
		call_result_store_consumed_ = false;
	}
	Value nv = emit_rvalue(expr.children[2]);
	if (!call_result_store_consumed_)
	{
		nv = convert_value(nv, expr.children[2].type, expr.type);
		instr("store " + type + " " + nv.text + ", $" + slot);
	}
	call_result_store_slot_.clear();
	call_result_store_type_.reset();
	call_result_store_consumed_ = false;
	emit_pending_temp_cleanups();
	terminate("jump ^" + end);
	start_block(end);
	string tmp = fresh_temp();
	instr(tmp + " = load " + type + " $" + slot);
	return Value(type, tmp);
}

void FunctionLowerer::branch_on(const Node& expr, const string& yes, const string& no)
{
	if (starts_with(expr.line, "condition-declaration"))
	{
		if (expr.children.empty())
			throw runtime_error("empty condition declaration");
		lower_variable_decl(expr.children[0]);
		const Node& cond_node =
			expr.children.size() > 1 ? expr.children[1] : expr.children[0];
		Value cond = emit_rvalue(cond_node);
		if (is_float_type(cond_node.type))
			cond = bool_value(cond, cond_node.type);
		terminate_with_pending_temp_cleanups(cond.text, yes, no);
		return;
	}
	if (starts_with(expr.line, "binary-expression") && expr.has_op &&
	    expr.op == OP_LOR)
	{
		string rhs = fresh_block("lor_rhs");
		branch_on(expr.children[0], yes, rhs);
		start_block(rhs);
		branch_on(expr.children[1], yes, no);
		return;
	}
	if (starts_with(expr.line, "binary-expression") && expr.has_op &&
	    expr.op == OP_LAND)
	{
		string rhs = fresh_block("land_rhs");
		branch_on(expr.children[0], rhs, no);
		start_block(rhs);
		branch_on(expr.children[1], yes, no);
		return;
	}
	if (eh_try_depth_ == 0 && has_active_cleanups() &&
	    node_contains_call_expression(expr))
	{
		branch_with_unwind_cleanups(expr, yes, no);
		return;
	}
	Value cond = emit_rvalue(expr);
	if (is_float_type(expr.type))
		cond = bool_value(cond, expr.type);
	terminate_with_pending_temp_cleanups(cond.text, yes, no);
}


}  // namespace internal
}  // namespace pa14
