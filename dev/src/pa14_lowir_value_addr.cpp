#include "pa14_lowir_internal.h"

namespace pa14 {
namespace internal {

Value FunctionLowerer::emit_literal(const Node& expr)
{
	if (expr.token_text.size() > 0 &&
	    expr.token_text[expr.token_text.size() - 1] == '"')
	{
		string sym = program_.string_symbol(expr.token_text);
		string tmp = fresh_temp();
		instr(tmp + " = addr @" + sym);
		return Value("ptr", tmp);
	}
	return Value(scalar_lowir_type(expr.type), lowir_literal(expr.type, expr));
}

Value FunctionLowerer::emit_id_rvalue(const Node& expr)
{
	if (expr.binding == NULL)
		return emit_literal(expr);
	if (expr.binding->kind == BindingKind::Function)
	{
		string addr = fresh_temp();
		instr(addr + " = addr @" + program_.symbol_for(expr.binding));
		string decay = fresh_temp();
		instr(decay + " = unary decay ptr " + addr);
		return Value("ptr", decay);
	}
	TypePtr object = object_type(expr.type);
	if (object->kind == TypeKind::Array &&
	    expr.binding->owner != NULL &&
	    (expr.binding->owner->kind == ScopeKind::Namespace ||
	     expr.binding->is_static_member))
	{
		program_.demand_global_declaration(expr.binding);
		string addr = fresh_temp();
		instr(addr + " = addr @" + program_.symbol_for(expr.binding));
		string decay = fresh_temp();
		instr(decay + " = unary decay ptr " + addr);
		return Value("ptr", decay);
	}
	Value addr = emit_lvalue_addr(expr);
	TypePtr value_type = strip_for_value(expr.type);
	if (pa11::strip_cv(object_type(expr.type))->kind == TypeKind::Array)
	{
		addr = ensure_pointer(addr);
		string tmp = fresh_temp();
		instr(tmp + " = unary decay ptr " + addr.text);
		return Value("ptr", tmp);
	}
	if (pa11::strip_cv(object_type(expr.type))->kind == TypeKind::Function)
	{
		string tmp = fresh_temp();
		instr(tmp + " = unary decay ptr " + addr.text);
		return Value("ptr", tmp);
	}
	string value_low_type = scalar_lowir_type(value_type);
	if (expr.binding != NULL && expr.binding->is_bit_field)
		value_low_type = "i" + to_string(pa11::type_size(value_type) * 8);
	string tmp = fresh_temp();
	instr(tmp + " = load " + value_low_type + " " + addr.text);
	if (expr.binding != NULL && expr.binding->is_bit_field)
	{
		string value = tmp;
		if (expr.binding->bit_offset != 0)
		{
			string shifted = fresh_temp();
			instr(shifted + " = binary ushr " + value_low_type +
			      " " + value + ", " + to_string(expr.binding->bit_offset));
			value = shifted;
		}
		uint64_t mask = expr.binding->bit_width >= 64
			? ~uint64_t(0) : ((uint64_t(1) << expr.binding->bit_width) - 1);
		string masked = fresh_temp();
		instr(masked + " = binary and " + value_low_type +
		      " " + value + ", " + to_string(mask));
		tmp = masked;
	}
	return Value(scalar_lowir_type(value_type), tmp);
}

Value FunctionLowerer::emit_lvalue_addr(const Node& expr)
{
	if (starts_with(expr.line, "id-expression") && expr.binding != NULL)
	{
		if (expr.binding->kind == BindingKind::Function)
		{
			string tmp = fresh_temp();
			instr(tmp + " = addr @" + program_.symbol_for(expr.binding));
			return Value("ptr", tmp);
		}
		if (expr.binding->owner != NULL &&
		    expr.binding->owner->kind == ScopeKind::Class &&
		    !expr.binding->is_static_member)
		{
			string this_ptr = fresh_temp();
			instr(this_ptr + " = load ptr $this");
			Value base("ptr", this_ptr);
			TypePtr object_record = fn_.binding != NULL &&
			                        fn_.binding->owner != NULL
				? pa11::record_type_for_scope(fn_.binding->owner) : TypePtr();
			TypePtr owner_record = pa11::record_type_for_scope(expr.binding->owner);
			if (object_record.get() != NULL &&
			    owner_record.get() != NULL &&
			    !pa11::same_type(pa11::strip_cv(object_record),
			                     pa11::strip_cv(owner_record)))
			{
				TypePtr direct_base = object_record->base.get() != NULL
					? pa11::strip_cv(object_record->base) : TypePtr();
				if (direct_base.get() != NULL &&
				    pa11::same_type(direct_base,
				                    pa11::strip_cv(owner_record)))
				{
					string base_tmp = fresh_temp();
					instr(base_tmp + " = index i8 [projection=base_subobject] " +
					      base.text + ", 0");
					base = Value("ptr", base_tmp);
				}
			}
			string tmp = fresh_temp();
			instr(tmp + " = index i8 [projection=field] " + base.text +
			      ", " + to_string(expr.binding->member_offset));
			if (is_reference(expr.binding->type))
			{
				string ref = fresh_temp();
				instr(ref + " = load ptr " + tmp);
				return Value("ptr", ref);
			}
			return Value("ptr", tmp);
		}
		if (return_slot_variables_.find(expr.binding) !=
		    return_slot_variables_.end())
			return Value("ptr", "%ret");
		if (by_address_parameters_.find(expr.binding) !=
		    by_address_parameters_.end())
			return Value("ptr", "%" + slot_for(expr.binding));
		if (is_reference(expr.binding->type))
		{
			string tmp = fresh_temp();
			if (expr.binding->is_static_member ||
			    (expr.binding->owner != NULL &&
			     expr.binding->owner->kind == ScopeKind::Namespace))
			{
				program_.demand_global_declaration(expr.binding);
				instr(tmp + " = load ptr @" + program_.symbol_for(expr.binding));
			}
			else
				instr(tmp + " = load ptr $" + slot_for(expr.binding));
			return Value("ptr", tmp);
		}
		if (expr.binding->is_static_member ||
		    (expr.binding->owner != NULL &&
		     expr.binding->owner->kind == ScopeKind::Namespace))
		{
			program_.demand_global_declaration(expr.binding);
			return Value("ptr", "@" + program_.symbol_for(expr.binding));
		}
		string slot = slot_for(expr.binding);
		return Value("ptr", "$" + slot);
	}
	if (starts_with(expr.line, "variable ") && expr.binding != NULL)
	{
		if (return_slot_variables_.find(expr.binding) !=
		    return_slot_variables_.end())
			return Value("ptr", "%ret");
		return Value("ptr", "$" + slot_for(expr.binding));
	}
	if (starts_with(expr.line, "member-expression") && expr.binding != NULL)
		return emit_member_lvalue_addr(expr);
	if (starts_with(expr.line, "base-subobject-expression"))
	{
		if (expr.children.empty())
			throw runtime_error("base subobject missing object");
		Value base = ensure_pointer(emit_lvalue_addr(expr.children[0]));
		string tmp = fresh_temp();
		instr(tmp + " = index i8 [projection=base_subobject] " +
		      base.text + ", 0");
		return Value("ptr", tmp);
	}
	if (starts_with(expr.line, "unary-expression") && expr.has_op &&
	    expr.op == OP_STAR)
		return emit_rvalue(expr.children[0]);
	if (starts_with(expr.line, "unary-expression") && expr.has_op &&
	    expr.op == OP_AMP)
		return emit_lvalue_addr(expr.children[0]);
	if (starts_with(expr.line, "unary-expression") && expr.has_op &&
	    (expr.op == OP_INC || expr.op == OP_DEC))
	{
		emit_unary(expr);
		return emit_lvalue_addr(expr.children[0]);
	}
	if (starts_with(expr.line, "postfix-expression") && expr.has_op)
	{
		emit_postfix(expr);
		return emit_lvalue_addr(expr.children[0]);
	}
	if (starts_with(expr.line, "binary-expression") && expr.has_op &&
	    expr.op == OP_COMMA)
	{
		emit_rvalue(expr.children[0]);
		return emit_lvalue_addr(expr.children[1]);
	}
	if (starts_with(expr.line, "subscript-expression"))
		return emit_subscript_addr(expr);
	if (starts_with(expr.line, "conditional-expression"))
		return emit_conditional(expr);
	if (starts_with(expr.line, "call-expression") && is_reference(expr.type))
		return emit_call(expr);
	if (starts_with(expr.line, "assignment-expression") &&
	    expr.has_op && (expr.op == OP_INC || expr.op == OP_DEC))
		return emit_lvalue_addr(expr.children[0]);
	if (starts_with(expr.line, "literal lvalue"))
		return emit_literal(expr);
	if (starts_with(expr.line, "cast-expression") &&
	    is_reference(expr.type) && !expr.children.empty())
	{
		TypePtr target = pa11::strip_cv(expr.type->base);
		TypePtr source = pa11::strip_cv(object_type(expr.children[0].type));
		if (target->kind == TypeKind::Record &&
		    source->kind == TypeKind::Record &&
		    !pa11::same_type(target, source) &&
		    !record_has_base_subobject(source, target))
		{
			string slot = fresh_aux_slot("tmpobj", slot_lowir_type(target));
			string addr_name = fresh_temp();
			instr(addr_name + " = addr $" + slot);
			Value temp_addr("ptr", addr_name);
			function<Value()> addr_for = [temp_addr]() {
				return temp_addr;
			};
			lower_object_init(addr_for, target, expr.children[0]);
			if (type_needs_cleanup(target))
				add_pending_temp_cleanup(temp_addr, target);
			return temp_addr;
		}
	}
	if (starts_with(expr.line, "cast-expression") ||
	    starts_with(expr.line, "id-expression xvalue"))
		return emit_lvalue_addr(expr.children.empty() ? expr : expr.children[0]);
	throw runtime_error("unsupported lvalue expression");
}

Value FunctionLowerer::emit_member_lvalue_addr(const Node& expr)
{
	if (expr.binding->is_static_member)
	{
		program_.demand_global_declaration(expr.binding);
		return Value("ptr", "@" + program_.symbol_for(expr.binding));
	}
	if (expr.children.empty())
		throw runtime_error("member expression missing object");
	Value base;
	if (expr.has_op && expr.op == OP_ARROW)
		base = emit_rvalue(expr.children[0]);
	else if (expr.children[0].category == ValueCategory::LValue ||
	         expr.children[0].category == ValueCategory::XValue)
		base = emit_lvalue_addr(expr.children[0]);
	else
	{
		TypePtr object_record =
			pa11::strip_cv(object_type(expr.children[0].type));
		if (object_record->kind != TypeKind::Record)
			throw runtime_error("unsupported member object expression");
		string slot = fresh_aux_slot("tmpobj", scalar_lowir_type(object_record));
		string addr = fresh_temp();
		instr(addr + " = addr $" + slot);
		base = Value("ptr", addr);
		function<Value()> object_addr = [base]() {
			return base;
		};
		lower_object_init(object_addr, object_record, expr.children[0]);
	}
	base = ensure_pointer(base);
	TypePtr object_record = expr.has_op && expr.op == OP_ARROW
		? pa11::strip_cv(strip_for_value(expr.children[0].type))
		: pa11::strip_cv(object_type(expr.children[0].type));
	if (object_record.get() != NULL &&
	    object_record->kind == TypeKind::Pointer)
		object_record = pa11::strip_cv(object_record->base);
	TypePtr owner_record = pa11::record_type_for_scope(expr.binding->owner);
	if (object_record.get() != NULL &&
	    object_record->kind == TypeKind::Record &&
	    owner_record.get() != NULL &&
	    !pa11::same_type(object_record, owner_record))
	{
		TypePtr direct_base = object_record->base.get() != NULL
			? pa11::strip_cv(object_record->base) : TypePtr();
		if (direct_base.get() != NULL &&
		    pa11::same_type(direct_base, owner_record))
		{
			string base_tmp = fresh_temp();
			instr(base_tmp + " = index i8 [projection=base_subobject] " +
			      base.text + ", 0");
			base = Value("ptr", base_tmp);
		}
	}
	string tmp = fresh_temp();
	instr(tmp + " = index i8 [projection=field] " + base.text +
	      ", " + to_string(expr.binding->member_offset));
	if (is_reference(expr.binding->type))
	{
		string ref = fresh_temp();
		instr(ref + " = load ptr " + tmp);
		return Value("ptr", ref);
	}
	return Value("ptr", tmp);
}

Value FunctionLowerer::emit_subscript_addr(const Node& expr)
{
	Value base;
	if (starts_with(expr.children[0].line, "conditional-expression") &&
	    expr.children[0].category == ValueCategory::LValue &&
	    pa11::strip_cv(object_type(expr.children[0].type))->kind == TypeKind::Array)
		base = emit_lvalue_addr(expr.children[0]);
	else
		base = emit_rvalue(expr.children[0]);
	base = ensure_pointer(base);
	Value index = emit_rvalue(expr.children[1]);
	TypePtr object = pa11::strip_cv(object_type(expr.type));
	if (object->kind == TypeKind::Record)
	{
		string scaled = fresh_temp();
		instr(scaled + " = binary mul i64 " + index.text + ", " +
		      to_string(pa11::type_size(object)));
		string tmp = fresh_temp();
		instr(tmp + " = index i8 [projection=array_element] " + base.text +
		      ", " + scaled);
		return Value("ptr", tmp);
	}
	string tmp = fresh_temp();
	string elem = scalar_lowir_type(expr.type);
	instr(tmp + " = index " + elem +
	      " [projection=array_element] " + base.text + ", " + index.text);
	return Value("ptr", tmp);
}


}  // namespace internal
}  // namespace pa14
