#include "pa14_lowir_internal.h"

namespace pa14 {
namespace internal {

void FunctionLowerer::lower_reference_call_argument(const Node& arg,
                                                    TypePtr param,
                                                    vector<string>& args)
{
	if (arg.category == ValueCategory::LValue)
	{
		Value addr = ensure_pointer(emit_lvalue_addr(arg));
		TypePtr from_ptr = pa11::make_pointer(object_type(arg.type));
		TypePtr to_ptr = pa11::make_pointer(param->base);
		args.push_back(convert_value(addr, from_ptr, to_ptr).text);
		return;
	}
	if (pa11::strip_cv(param->base)->kind == TypeKind::Record &&
	    pa11::strip_cv(object_type(arg.type))->kind == TypeKind::Record)
	{
		TypePtr object = pa11::strip_cv(object_type(arg.type));
		TypePtr target = pa11::strip_cv(param->base);
		string prefix = pa11::same_type(object, target) ? "arg" : "tmpobj";
		string slot = fresh_aux_slot(prefix, scalar_lowir_type(object));
		string addr_name = fresh_temp();
		instr(addr_name + " = addr $" + slot);
		Value temp_addr("ptr", addr_name);
		function<Value()> addr_for = [temp_addr]() {
			return temp_addr;
		};
		lower_object_init(addr_for, object, arg);
		args.push_back(convert_value(temp_addr,
		                             pa11::make_pointer(object),
		                             pa11::make_pointer(param->base)).text);
		return;
	}
	string slot = fresh_aux_slot("refarg", scalar_lowir_type(param->base));
	Value value = convert_value(emit_rvalue(arg), arg.type, param->base);
	instr("store " + scalar_lowir_type(param->base) + " " +
	      value.text + ", $" + slot);
	string addr = fresh_temp();
	instr(addr + " = addr $" + slot);
	args.push_back(addr);
}

bool FunctionLowerer::lower_temporary_record_pointer_argument(const Node& arg,
                                                              TypePtr param,
                                                              vector<string>& args)
{
	if (pa11::strip_cv(param)->kind != TypeKind::Pointer ||
	    pa11::strip_cv(pa11::strip_cv(param)->base)->kind != TypeKind::Record ||
	    !starts_with(arg.line, "unary-expression") ||
	    !arg.has_op || arg.op != OP_AMP || arg.children.empty() ||
	    arg.children[0].category == ValueCategory::LValue ||
	    pa11::strip_cv(object_type(arg.children[0].type))->kind != TypeKind::Record)
		return false;
	TypePtr object = pa11::strip_cv(object_type(arg.children[0].type));
	string slot = fresh_aux_slot("tmpobj", scalar_lowir_type(object));
	string addr_name = fresh_temp();
	instr(addr_name + " = addr $" + slot);
	Value temp_addr("ptr", addr_name);
	function<Value()> addr_for = [temp_addr]() {
		return temp_addr;
	};
	lower_object_init(addr_for, object, arg.children[0]);
	args.push_back(convert_value(temp_addr, pa11::make_pointer(object), param).text);
	return true;
}

void FunctionLowerer::lower_record_value_argument(const Node& arg,
                                                  TypePtr param,
                                                  vector<string>& args)
{
	string slot = fresh_aux_slot("argobj", slot_lowir_type(param));
	string addr_name = fresh_temp();
	instr(addr_name + " = addr $" + slot);
	Value target_addr("ptr", addr_name);
	if (arg.category == ValueCategory::LValue)
	{
		Value source = ensure_pointer(emit_lvalue_addr(arg));
		if (pa11::type_size(param) > 1)
		{
			string tmp = fresh_temp();
			instr(tmp + " = load " + scalar_lowir_type(param) +
			      " " + source.text);
			instr("store " + scalar_lowir_type(param) + " " +
			      tmp + ", " + target_addr.text);
		}
	}
	else
	{
		function<Value()> addr_for = [target_addr]() {
			return target_addr;
		};
		lower_object_init(addr_for, param, arg);
	}
	args.push_back("$" + slot);
}

void FunctionLowerer::lower_value_call_argument(const Node& arg,
                                                TypePtr param,
                                                vector<string>& args)
{
	if (lower_temporary_record_pointer_argument(arg, param, args))
		return;
	if (pa11::strip_cv(param)->kind == TypeKind::Record)
	{
		lower_record_value_argument(arg, param, args);
		return;
	}
	Value raw = emit_rvalue(arg);
	string src = scalar_lowir_type(strip_for_value(arg.type));
	string dst = scalar_lowir_type(param);
	if (src != dst && !raw.text.empty() &&
	    raw.text[0] != '%' && raw.text[0] != '$' && raw.text[0] != '@' &&
	    pa11::type_size(param) != pa11::type_size(arg.type) &&
	    pa11::is_integral_or_bool_type(arg.type) &&
	    pa11::is_integral_or_bool_type(param))
	{
		string tmp = fresh_temp();
		string op = pa11::type_size(param) < pa11::type_size(arg.type)
			? "trunc" : is_unsigned_type(arg.type) ? "zext" : "sext";
		instr(tmp + " = convert " + op + " " + dst + " " + src + " " +
		      raw.text);
		args.push_back(tmp);
		return;
	}
	args.push_back(convert_value(raw, arg.type, param).text);
}

void FunctionLowerer::lower_call_argument(const Node& arg,
                                          TypePtr param,
                                          vector<string>& args)
{
	if (is_reference(param))
		lower_reference_call_argument(arg, param, args);
	else
		lower_value_call_argument(arg, param, args);
}

Value FunctionLowerer::emit_call(const Node& expr)
{
	Binding* direct = expr.direct_call;
	size_t arg_start = direct != NULL ? 1 : 1;
	string callee;
	TypePtr callee_type;
	bool delay_direct_demand = direct != NULL && direct->name == "operator=";
	if (direct != NULL)
	{
		callee_type = direct->type;
		if (!delay_direct_demand)
		{
			program_.demand_function_declaration(direct);
			program_.demand_inline_function(direct);
			callee = "@" + program_.symbol_for(direct);
		}
	}
	else
	{
		callee_type = strip_for_value(expr.children[0].type);
		if (pa11::strip_cv(callee_type)->kind == TypeKind::Pointer)
			callee_type = pa11::strip_cv(callee_type)->base;
	}
	vector<string> args;
	for (size_t i = arg_start; i < expr.children.size(); ++i)
	{
		bool variadic_extra = i - arg_start >= callee_type->parameters.size();
		TypePtr param = !variadic_extra
			? callee_type->parameters[i - arg_start] : expr.children[i].type;
		if (variadic_extra && scalar_lowir_type(expr.children[i].type) == "f32")
			param = pa11::make_fundamental(FT_DOUBLE);
		lower_call_argument(expr.children[i], param, args);
	}
	if (direct != NULL && delay_direct_demand)
	{
		program_.demand_function_declaration(direct);
		program_.demand_inline_function(direct);
		callee = "@" + program_.symbol_for(direct);
	}
	else if (direct == NULL)
		callee = emit_rvalue(expr.children[0]).text;
	ostringstream call;
	string ret = scalar_lowir_type(callee_type->base);
	string tmp;
	if (ret == "void")
		call << "call void ";
	else
	{
		tmp = fresh_temp();
		call << tmp << " = call " << ret << " ";
	}
	call << callee << "(";
	for (size_t i = 0; i < args.size(); ++i)
	{
		if (i != 0)
			call << ", ";
		call << args[i];
	}
	call << ")";
	if (direct == NULL)
	{
		call << " as (";
		for (size_t i = 0; i < callee_type->parameters.size(); ++i)
		{
			if (i != 0)
				call << ", ";
			call << "%arg" << i << " : " <<
				lowir_parameter(callee_type->parameters[i]);
		}
		call << ") -> " << ret;
	}
	instr(call.str());
	if (eh_try_depth_ > 0 && ret != "void")
	{
		string slot = fresh_aux_slot("call", ret);
		instr("store " + ret + " " + tmp + ", $" + slot);
		string loaded = fresh_temp();
		instr(loaded + " = load " + ret + " $" + slot);
		return Value(ret, loaded);
	}
	return Value(ret, tmp);
}

}  // namespace internal
}  // namespace pa14
