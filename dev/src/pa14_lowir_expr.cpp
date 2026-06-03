#include "pa14_lowir_internal.h"

namespace pa14 {
namespace internal {

Value FunctionLowerer::emit_logical_binary(const Node& expr)
{
	string slot = fresh_aux_slot(expr.op == OP_LAND ? "land" : "lor", "i64");
	string rhs = fresh_block(expr.op == OP_LAND ? "land_rhs" : "lor_rhs");
	string sh = fresh_block(expr.op == OP_LAND ? "land_short" : "lor_short");
	string end = fresh_block(expr.op == OP_LAND ? "land_end" : "lor_end");
	if (expr.op == OP_LAND)
		branch_logical_operand(expr.children[0], rhs, sh);
	else
		branch_logical_operand(expr.children[0], sh, rhs);
	start_block(rhs);
	Value rv = bool_value(emit_rvalue(expr.children[1]), expr.children[1].type);
	instr("store i64 " + rv.text + ", $" + slot);
	terminate("jump ^" + end);
	start_block(sh);
	instr("store i64 " + string(expr.op == OP_LAND ? "0" : "1") + ", $" +
	      slot);
	terminate("jump ^" + end);
	start_block(end);
	string tmp = fresh_temp();
	instr(tmp + " = load i64 $" + slot);
	return Value("i64", tmp);
}

Value FunctionLowerer::emit_pointer_index_binary(const Node& expr,
                                                 Value lhs,
                                                 Value rhs,
                                                 TypePtr lhs_type,
                                                 TypePtr rhs_type)
{
	const bool left_ptr = pa11::strip_cv(lhs_type)->kind == TypeKind::Pointer;
	Value base = left_ptr ? lhs : rhs;
	Value offset = left_ptr ? rhs : lhs;
	TypePtr ptr_type = left_ptr ? lhs_type : rhs_type;
	uint64_t scale = pa11::type_size(pa11::strip_cv(ptr_type)->base);
	if (scale != 1)
	{
		string mul = fresh_temp();
		instr(mul + " = binary mul i64 " + offset.text + ", " +
		      to_string(scale));
		offset = Value("i64", mul);
	}
	if (expr.op == OP_MINUS)
	{
		string neg = fresh_temp();
		instr(neg + " = binary sub i64 0, " + offset.text);
		offset = Value("i64", neg);
	}
	string tmp = fresh_temp();
	instr(tmp + " = index i8 " + base.text + ", " + offset.text);
	return Value("ptr", tmp);
}

Value FunctionLowerer::emit_pointer_difference(const Node& expr,
                                               Value lhs,
                                               Value rhs,
                                               TypePtr lhs_type)
{
	(void)expr;
	string diff = fresh_temp();
	instr(diff + " = binary sub ptr " + lhs.text + ", " + rhs.text);
	string tmp = fresh_temp();
	uint64_t scale = pa11::type_size(pa11::strip_cv(lhs_type)->base);
	instr(tmp + " = binary div i64 " + diff + ", " + to_string(scale));
	return Value("i64", tmp);
}

}  // namespace internal
}  // namespace pa14
