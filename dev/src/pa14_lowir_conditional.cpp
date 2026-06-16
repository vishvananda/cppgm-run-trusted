#include "pa14_lowir_internal.h"

namespace pa14 {
namespace internal {

Value FunctionLowerer::emit_conditional(const Node& expr)
{
	if (expr.category != ValueCategory::LValue && pa11::is_void_type(expr.type))
	{
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
		emit_rvalue(expr.children[1]);
		emit_pending_temp_cleanups();
		terminate("jump ^" + end);
		start_block(no);
		emit_rvalue(expr.children[2]);
		emit_pending_temp_cleanups();
		terminate("jump ^" + end);
		start_block(end);
		return Value("void", "");
	}
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
	if (pa11::is_void_type(expr.type))
	{
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
		emit_rvalue(expr.children[1]);
		emit_pending_temp_cleanups();
		terminate("jump ^" + end);
		start_block(no);
		emit_rvalue(expr.children[2]);
		emit_pending_temp_cleanups();
		terminate("jump ^" + end);
		start_block(end);
		return Value("void", "");
	}
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

bool FunctionLowerer::lower_record_conditional_init(
	const function<Value()>& addr_for,
	TypePtr type,
	const Node& init)
{
	if (!starts_with(init.line, "conditional-expression") ||
	    init.children.size() != 3)
		return false;
	Binding* copy = find_copy_move_constructor(type, false);
	if (copy == NULL && !type_needs_cleanup(type))
	{
		Value target = addr_for();
		function<Value()> target_addr = [target]() { return target; };
		string yes = fresh_block("condobj_then");
		string no = fresh_block("condobj_else");
		string end = fresh_block("condobj_end");
		Value cond = emit_rvalue(init.children[0]);
		if (is_float_type(init.children[0].type))
			cond = bool_value(cond, init.children[0].type);
		terminate("branch " + cond.text + ", ^" + yes + ", ^" + no);
		start_block(yes);
		lower_object_init(target_addr, type, init.children[1]);
		terminate("jump ^" + end);
		start_block(no);
		lower_object_init(target_addr, type, init.children[2]);
		terminate("jump ^" + end);
		start_block(end);
		return true;
	}
	Value target = addr_for();
	string slot = fresh_aux_slot("arg", slot_lowir_type(type));
	string temp_name = fresh_temp();
	instr(temp_name + " = addr $" + slot);
	Value temp_addr("ptr", temp_name);
	function<Value()> result_addr = [temp_addr]() { return temp_addr; };
	string yes = fresh_block("condobj_then");
	string no = fresh_block("condobj_else");
	string end = fresh_block("condobj_end");
	Value cond = emit_rvalue(init.children[0]);
	if (is_float_type(init.children[0].type))
		cond = bool_value(cond, init.children[0].type);
	terminate("branch " + cond.text + ", ^" + yes + ", ^" + no);
	start_block(yes);
	lower_object_init(result_addr, type, init.children[1]);
	terminate("jump ^" + end);
	start_block(no);
	lower_object_init(result_addr, type, init.children[2]);
	terminate("jump ^" + end);
	start_block(end);
	Binding* temp_dtor = find_destructor(type);
	bool call_temp_dtor =
		temp_dtor != NULL && !temp_dtor->is_generated_default_destructor;
	function<void()> destroy_result = [this, result_addr, type,
	                                  temp_dtor, call_temp_dtor]() {
		if (call_temp_dtor)
		{
			program_.demand_function_declaration(temp_dtor);
			program_.demand_inline_function(temp_dtor);
			Value target = result_addr();
			string arg = target.text;
			if (!arg.empty() && (arg[0] == '@' || arg[0] == '$'))
			{
				string tmp = fresh_temp();
				instr(tmp + " = addr " + arg);
				arg = tmp;
			}
			instr("call void @" + program_.symbol_for(temp_dtor) +
			      "(" + arg + ")");
		}
		else if (type_needs_cleanup(type))
			lower_destructor_for_object(result_addr, type);
	};
	if (copy != NULL)
	{
		program_.demand_function_declaration(copy);
		program_.demand_inline_function(copy);
		string dispatch = fresh_block("call_unwind_dispatch");
		string done = fresh_block("call_unwind_end");
		instr("eh_try ^" + dispatch);
		++eh_try_depth_;
		instr("call void @" + program_.symbol_for(copy) +
		      "(" + target.text + ", " + temp_addr.text + ")");
		destroy_result();
		--eh_try_depth_;
		instr("eh_end");
		terminate("jump ^" + done);
		start_block(dispatch);
		destroy_result();
		emit_unwind_cleanups();
		terminate("resume");
		start_block(done);
		return true;
	}
	if (record_has_storage_copy(type))
		instr("copyobj " + to_string(pa11::type_size(type)) + "x" +
		      to_string(pa11::type_align(type)) + " " + temp_addr.text +
		      ", " + target.text);
	destroy_result();
	return true;
}

}  // namespace internal
}  // namespace pa14
