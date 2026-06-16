#include "pa14_lowir_internal.h"
#include "pa12_templates_function_support.h"

namespace pa14 {
namespace internal {

Value FunctionLowerer::emit_binary(const Node& expr)
{
	if (expr.has_op && expr.op == OP_COMMA) {
		emit_rvalue(expr.children[0]);
		return emit_rvalue(expr.children[1]); }
	if (expr.has_op && (expr.op == OP_EQ || expr.op == OP_NE) &&
	    expr.children.size() == 2 &&
	    expr.children[0].is_typeid_expression &&
	    expr.children[1].is_typeid_expression) {
		Value lhs = emit_lvalue_addr(expr.children[0]);
		Value rhs = emit_lvalue_addr(expr.children[1]);
		string tmp = fresh_temp();
		instr(tmp + " = cmp " + string(expr.op == OP_EQ ? "eq" : "ne") +
		      " ptr " + lhs.text + ", " + rhs.text);
		return Value("u8", tmp); }
	if (expr.has_op && (expr.op == OP_LAND || expr.op == OP_LOR))
		return emit_logical_binary(expr);
	TypePtr lhs_expr_type = substituted_expression_type(expr.children[0]);
	TypePtr rhs_expr_type = substituted_expression_type(expr.children[1]);
	TypePtr result_expr_type = substituted_expression_type(expr);
	if (!pa12::internal::substituted_type_is_valid(result_expr_type))
		result_expr_type = lowir_common_type(lhs_expr_type, rhs_expr_type);
	bool wrap_lhs_materialized_member =
		eh_try_depth_ == 0 &&
		has_active_cleanups() &&
		starts_with(expr.children[0].line, "member-expression") &&
		node_contains_call_expression(expr.children[0]) &&
		expr.children[0].category == ValueCategory::LValue &&
		scalar_lowir_type(lhs_expr_type).compare(0, 4, "obj<") != 0;
	string dispatch;
	bool define_dispatch = false;
	Value lhs;
	if (wrap_lhs_materialized_member) {
		Value lhs_addr;
		if (!expr.children[0].children.empty() &&
		    starts_with(expr.children[0].children[0].line,
		                "call-expression") &&
		    expr.children[0].binding != NULL) {
			const Node& member_expr = expr.children[0];
			TypePtr object_record =
				pa11::strip_cv(object_type(member_expr.children[0].type));
			string slot =
				fresh_aux_slot("tmpobj", scalar_lowir_type(object_record));
			string object_addr_name = fresh_temp();
			instr(object_addr_name + " = addr $" + slot);
			Value object_addr("ptr", object_addr_name);
			function<Value()> object_addr_for = [object_addr]() {
				return object_addr;
			};
			lower_object_init(object_addr_for,
			                  object_record,
			                  member_expr.children[0]);
			dispatch = active_unwind_dispatch_.empty()
				? fresh_block("call_unwind_dispatch") : active_unwind_dispatch_;
			define_dispatch = active_unwind_dispatch_.empty();
			instr("eh_try ^" + dispatch);
			++eh_try_depth_;
			Binding* member = member_expr.binding;
			TypePtr owner_record = pa11::record_type_for_scope(member->owner);
			Value projected_base = object_addr;
			if (owner_record.get() != NULL &&
			    object_record.get() != NULL &&
			    object_record->kind == TypeKind::Record &&
			    owner_record->kind == TypeKind::Record &&
			    !pa11::same_type(object_record, owner_record))
				projected_base =
					emit_base_subobject_addr(object_addr,
					                         object_record,
					                         owner_record);
			string field_addr = fresh_temp();
			instr(field_addr + " = index i8 [projection=field] " +
			      projected_base.text + ", " +
			      to_string(member->member_offset));
			lhs_addr = Value("ptr", field_addr); }
		else {
			lhs_addr = ensure_pointer(emit_lvalue_addr(expr.children[0]));
			dispatch = active_unwind_dispatch_.empty()
				? fresh_block("call_unwind_dispatch") : active_unwind_dispatch_;
			define_dispatch = active_unwind_dispatch_.empty();
			instr("eh_try ^" + dispatch);
			++eh_try_depth_; }
		string loaded = fresh_temp();
		instr(loaded + " = load " + scalar_lowir_type(lhs_expr_type) +
		      " " + lhs_addr.text);
		lhs = Value(scalar_lowir_type(lhs_expr_type), loaded); }
	else
		lhs = emit_rvalue(expr.children[0]);
	Value rhs = emit_rvalue(expr.children[1]);
	TypePtr lhs_type = strip_for_value(lhs_expr_type);
	TypePtr rhs_type = strip_for_value(rhs_expr_type);
	if ((expr.op == OP_PLUS || expr.op == OP_MINUS) &&
	    scalar_lowir_type(result_expr_type) == "ptr")
		return emit_pointer_index_binary(expr, lhs, rhs, lhs_type, rhs_type);
	if (expr.op == OP_MINUS &&
	    pa11::strip_cv(lhs_type)->kind == TypeKind::Pointer &&
	    pa11::strip_cv(rhs_type)->kind == TypeKind::Pointer)
		return emit_pointer_difference(expr, lhs, rhs, lhs_type);
	string op;
	bool cmp = false;
	switch (expr.op) {
	case OP_PLUS: op = "add"; break;
	case OP_MINUS: op = "sub"; break;
	case OP_STAR: op = "mul"; break;
	case OP_DIV: op = is_unsigned_type(lhs_expr_type) ? "udiv" : "div"; break;
	case OP_MOD: op = is_unsigned_type(lhs_expr_type) ? "umod" : "mod"; break;
	case OP_AMP: op = "and"; break;
	case OP_BOR: op = "or"; break;
	case OP_XOR: op = "xor"; break;
	case OP_LSHIFT: op = "shl"; break;
	case OP_RSHIFT: op = is_unsigned_type(lhs_expr_type) ? "ushr" : "shr"; break;
	case OP_EQ: op = "eq"; cmp = true; break;
	case OP_NE: op = "ne"; cmp = true; break;
	case OP_LT: op = is_unsigned_type(lhs_expr_type) ? "ult" : "lt"; cmp = true; break;
	case OP_LE: op = is_unsigned_type(lhs_expr_type) ? "ule" : "le"; cmp = true; break;
	case OP_GT: op = is_unsigned_type(lhs_expr_type) ? "ugt" : "gt"; cmp = true; break;
	case OP_GE: op = is_unsigned_type(lhs_expr_type) ? "uge" : "ge"; cmp = true; break;
	default: throw runtime_error("unsupported binary operator"); }
	TypePtr op_type = cmp ? lowir_common_type(lhs_expr_type, rhs_expr_type)
	                     : result_expr_type;
	if (!pa12::internal::substituted_type_is_valid(op_type))
		op_type = lowir_common_type(lhs_expr_type, rhs_expr_type);
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
		if (scalar_lowir_type(strip_for_value(lhs_expr_type)) != "ptr")
			lhs = convert_binary_value(lhs, lhs_expr_type, op_type);
		if (scalar_lowir_type(strip_for_value(rhs_expr_type)) != "ptr")
			rhs = convert_binary_value(rhs, rhs_expr_type, op_type); }
	else {
		lhs = convert_binary_value(lhs, lhs_expr_type, op_type);
		rhs = convert_binary_value(rhs, rhs_expr_type, op_type); }
	string type = scalar_lowir_type(op_type);
	string tmp = fresh_temp();
	instr(tmp + " = " + string(cmp ? "cmp " : "binary ") + op + " " +
	      type + " " + lhs.text + ", " + rhs.text);
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
	return Value(cmp ? "u8" : scalar_lowir_type(op_type), tmp);
}

}  // namespace internal
}  // namespace pa14
