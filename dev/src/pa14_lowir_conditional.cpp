#include "pa14_lowir_internal.h"

namespace pa14 {
namespace internal {

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

}  // namespace internal
}  // namespace pa14
