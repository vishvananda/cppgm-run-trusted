#include "pa14_lowir_internal.h"

namespace pa14 {
namespace internal {

namespace {

void demand_record_return_calls(ProgramLowerer& program, const Node& node)
{
	if (node.direct_call != NULL &&
	    node.direct_call->type.get() != NULL &&
	    node.direct_call->type->kind == TypeKind::Function &&
	    pa11::strip_cv(node.direct_call->type->base)->kind ==
		    TypeKind::Record)
	{
		program.demand_function_declaration(node.direct_call);
		program.demand_inline_function(node.direct_call);
	}
	for (size_t i = 0; i < node.children.size(); ++i)
		demand_record_return_calls(program, node.children[i]);
}

bool call_binding_has_template_cleanup_context(const Binding* binding)
{
	return binding != NULL &&
	       (!binding->function_specialization_symbol.empty() ||
	        binding_has_template_specialization_context(binding));
}

bool assignment_parameter_is_copy_move(const Binding* binding)
{
	if (binding == NULL || binding->owner == NULL ||
	    binding->owner->kind != ScopeKind::Class ||
	    binding->type.get() == NULL ||
	    binding->type->kind != TypeKind::Function ||
	    binding->type->parameters.size() != 2 ||
	    !is_reference(binding->type->parameters[1]))
		return false;
	TypePtr record = pa11::record_type_for_scope(binding->owner);
	if (record.get() == NULL)
		return false;
	TypePtr param_record = pa11::strip_cv(binding->type->parameters[1]->base);
	return param_record->kind == TypeKind::Record &&
	       pa11::same_type(param_record, pa11::strip_cv(record));
}

}  // namespace

void FunctionLowerer::lower_reference_call_argument(const Node& arg,
                                                    TypePtr param,
                                                    vector<string>& args,
                                                    vector<pair<Value, TypePtr> >* temp_cleanups)
{
	demand_record_return_calls(program_, arg);
	const Node* materialized = record_prvalue_child_for_xvalue(arg);
	if (materialized != NULL &&
	    pa11::strip_cv(param->base)->kind == TypeKind::Record)
	{
		TypePtr object = pa11::strip_cv(object_type(materialized->type));
		TypePtr target = pa11::strip_cv(param->base);
		bool indirect_call_result =
			starts_with(materialized->line, "call-expression") &&
			record_return_by_address(materialized->type);
		string prefix = indirect_call_result ? "refcall" :
		                (pa11::same_type(object, target) ? "arg" : "tmpobj");
		string slot = fresh_aux_slot(prefix, scalar_lowir_type(object));
		string addr_name = fresh_temp();
		Value temp_addr("ptr", addr_name);
		shared_ptr<bool> emitted(new bool(false));
		function<Value()> addr_for = [this, slot, temp_addr, emitted]() {
			if (!*emitted)
			{
				*emitted = true;
				instr(temp_addr.text + " = addr $" + slot);
			}
			return temp_addr;
		};
		lower_temporary_init_with_unwind(addr_for, object, *materialized);
		addr_for();
		if (temp_cleanups != NULL && type_needs_cleanup(object))
			temp_cleanups->push_back(make_pair(temp_addr, object));
		args.push_back(convert_value(temp_addr,
		                             pa11::make_pointer(object),
		                             pa11::make_pointer(param->base)).text);
		return;
	}
	if (arg.category == ValueCategory::PRValue &&
	    starts_with(arg.line, "braced-init-list") &&
	    pa11::strip_cv(param->base)->kind == TypeKind::Array)
	{
		string slot = fresh_aux_slot("argarr", slot_lowir_type(param->base));
		string addr_name = fresh_temp();
		instr(addr_name + " = addr $" + slot);
		Value temp_addr("ptr", addr_name);
		lower_direct_array_init(temp_addr, param->base, arg);
		args.push_back(convert_value(temp_addr,
		                             pa11::make_pointer(param->base),
		                             pa11::make_pointer(param->base)).text);
		return;
	}
	if (arg.category == ValueCategory::LValue ||
	    arg.category == ValueCategory::XValue)
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
		Value temp_addr("ptr", addr_name);
		shared_ptr<bool> emitted(new bool(false));
		function<Value()> addr_for = [this, slot, temp_addr, emitted]() {
			if (!*emitted)
			{
				*emitted = true;
				instr(temp_addr.text + " = addr $" + slot);
			}
			return temp_addr;
		};
		lower_temporary_init_with_unwind(addr_for, object, arg);
		addr_for();
		if (temp_cleanups != NULL && type_needs_cleanup(object))
			temp_cleanups->push_back(make_pair(temp_addr, object));
		args.push_back(convert_value(temp_addr,
		                             pa11::make_pointer(object),
		                             pa11::make_pointer(param->base)).text);
		return;
	}
	string slot = fresh_aux_slot("refarg", scalar_lowir_type(param->base));
	Value raw =
		arg.binding != NULL && arg.binding->kind == BindingKind::Function
		? ensure_pointer(emit_lvalue_addr(arg))
		: emit_rvalue(arg);
	Value value = convert_value(raw, arg.type, param->base);
	instr("store " + scalar_lowir_type(param->base) + " " +
	      value.text + ", $" + slot);
	string addr = fresh_temp();
	instr(addr + " = addr $" + slot);
	args.push_back(addr);
}

bool FunctionLowerer::lower_temporary_record_pointer_argument(const Node& arg,
                                                              TypePtr param,
                                                              vector<string>& args,
                                                              vector<pair<Value, TypePtr> >* temp_cleanups)
{
	if (pa11::strip_cv(param)->kind != TypeKind::Pointer ||
	    pa11::strip_cv(pa11::strip_cv(param)->base)->kind != TypeKind::Record ||
	    !starts_with(arg.line, "unary-expression") ||
	    !arg.has_op || arg.op != OP_AMP || arg.children.empty() ||
	    arg.children[0].category == ValueCategory::LValue ||
	    arg.children[0].category == ValueCategory::XValue ||
	    pa11::strip_cv(object_type(arg.children[0].type))->kind != TypeKind::Record)
		return false;
	TypePtr object = pa11::strip_cv(object_type(arg.children[0].type));
	string slot = fresh_aux_slot("tmpobj", scalar_lowir_type(object));
	string addr_name = fresh_temp();
	Value temp_addr("ptr", addr_name);
	shared_ptr<bool> emitted(new bool(false));
	function<Value()> addr_for = [this, slot, temp_addr, emitted]() {
		if (!*emitted)
		{
			*emitted = true;
			instr(temp_addr.text + " = addr $" + slot);
		}
		return temp_addr;
	};
	lower_temporary_init_with_unwind(addr_for, object, arg.children[0]);
	addr_for();
	if (temp_cleanups != NULL && object->is_polymorphic &&
	    type_needs_cleanup(object))
		temp_cleanups->push_back(make_pair(temp_addr, object));
	args.push_back(convert_value(temp_addr, pa11::make_pointer(object), param).text);
	return true;
}

bool FunctionLowerer::call_argument_may_create_temp_cleanup(const Node& arg,
                                                            TypePtr param) const
{
	if (node_contains_call_expression(arg))
		return true;
	TypePtr bare_param = pa11::strip_cv(param);
	if (is_reference(param))
	{
		const Node* materialized = record_prvalue_child_for_xvalue(arg);
		if (materialized != NULL &&
		    pa11::strip_cv(param->base)->kind == TypeKind::Record &&
		    type_needs_cleanup(object_type(materialized->type)))
			return true;
		if (arg.category == ValueCategory::PRValue &&
		    pa11::strip_cv(param->base)->kind == TypeKind::Record &&
		    pa11::strip_cv(object_type(arg.type))->kind == TypeKind::Record &&
		    type_needs_cleanup(object_type(arg.type)))
			return true;
	}
	if (bare_param->kind == TypeKind::Pointer &&
	    starts_with(arg.line, "unary-expression") &&
	    arg.has_op && arg.op == OP_AMP && !arg.children.empty() &&
	    arg.children[0].category != ValueCategory::LValue &&
	    pa11::strip_cv(object_type(arg.children[0].type))->kind ==
	    TypeKind::Record &&
	    type_needs_cleanup(object_type(arg.children[0].type)))
		return true;
	return false;
}

bool call_argument_needs_setup_cleanup_protection(const Node& arg,
                                                  TypePtr param)
{
	TypePtr bare_param = pa11::strip_cv(param);
	if (is_reference(param))
	{
		const Node* materialized = record_prvalue_child_for_xvalue(arg);
		if (materialized != NULL &&
		    pa11::strip_cv(param->base)->kind == TypeKind::Record &&
		    type_needs_destructor(object_type(materialized->type)))
			return true;
		if (arg.category == ValueCategory::PRValue &&
		    pa11::strip_cv(param->base)->kind == TypeKind::Record &&
		    pa11::strip_cv(object_type(arg.type))->kind == TypeKind::Record &&
		    type_needs_destructor(object_type(arg.type)))
			return true;
	}
	if (bare_param->kind == TypeKind::Record &&
	    arg.category == ValueCategory::PRValue &&
	    pa11::strip_cv(object_type(arg.type))->kind == TypeKind::Record &&
	    type_needs_destructor(object_type(arg.type)))
		return true;
	if (bare_param->kind == TypeKind::Pointer &&
	    starts_with(arg.line, "unary-expression") &&
	    arg.has_op && arg.op == OP_AMP && !arg.children.empty() &&
	    arg.children[0].category != ValueCategory::LValue &&
	    pa11::strip_cv(object_type(arg.children[0].type))->kind ==
	    TypeKind::Record &&
	    type_needs_destructor(object_type(arg.children[0].type)))
	{
		TypePtr object = pa11::strip_cv(object_type(arg.children[0].type));
		return !object->is_polymorphic;
	}
	return false;
}

bool FunctionLowerer::call_setup_can_use_outer_eh(const Node& expr,
                                                  TypePtr callee_type,
                                                  size_t arg_start) const
{
	if (is_class_constructor_binding(expr.direct_call) ||
	    pa11::strip_cv(callee_type->base)->kind == TypeKind::Record ||
	    call_temp_cleanup_defer_depth_ > 0)
		return false;
	for (size_t i = arg_start; i < expr.children.size(); ++i)
	{
		bool variadic_extra = i - arg_start >= callee_type->parameters.size();
		TypePtr param = !variadic_extra
			? callee_type->parameters[i - arg_start]
			: expr.children[i].type;
		if (variadic_extra && scalar_lowir_type(expr.children[i].type) == "f32")
			param = pa11::make_fundamental(FT_DOUBLE);
		if (call_argument_needs_setup_cleanup_protection(expr.children[i],
		                                                 param))
			return false;
	}
	return true;
}

void FunctionLowerer::lower_record_value_argument(const Node& arg,
                                                  TypePtr param,
                                                  vector<string>& args)
{
	bool by_address = record_pass_by_address(param);
	string slot = fresh_aux_slot(by_address ? "arg" : "argobj",
	                             slot_lowir_type(param));
	string addr_name = fresh_temp();
	instr(addr_name + " = addr $" + slot);
	Value target_addr("ptr", addr_name);
	function<Value()> addr_for = [target_addr]() {
		return target_addr;
	};
	if (arg.direct_call != NULL &&
	    arg.children.empty() &&
	    (arg.direct_call->is_generated_default_constructor ||
	     arg.direct_call->is_defaulted) &&
	    no_op_generated_default_constructor(arg.direct_call, param) &&
	    zero_init_has_store(param))
		lower_storage_zero(target_addr, pa11::type_size(param));
	lower_object_init(addr_for, param, arg);
	args.push_back(by_address ? target_addr.text : "$" + slot);
}

void FunctionLowerer::lower_value_call_argument(const Node& arg,
                                                TypePtr param,
                                                vector<string>& args,
                                                vector<pair<Value, TypePtr> >* temp_cleanups)
{
	if (lower_temporary_record_pointer_argument(arg, param, args, temp_cleanups))
		return;
	if (pa11::strip_cv(param)->kind == TypeKind::Record)
	{
		lower_record_value_argument(arg, param, args);
		return;
		}
		Value raw = emit_rvalue(arg);
		Value converted = convert_binary_value(raw, arg.type, param);
		if (converted.type == "ptr" && converted.text == "0" &&
		    arg.token_text == "nullptr")
			converted.text = "nullptr";
		args.push_back(converted.text);
	}

void FunctionLowerer::lower_call_argument(const Node& arg,
                                          TypePtr param,
                                          vector<string>& args,
                                          vector<pair<Value, TypePtr> >* temp_cleanups)
{
	if (is_reference(param))
		lower_reference_call_argument(arg, param, args, temp_cleanups);
	else
		lower_value_call_argument(arg, param, args, temp_cleanups);
}

bool FunctionLowerer::lower_indirect_record_call(const function<Value()>& addr_for,
                                                 const Node& expr)
{
	if (!starts_with(expr.line, "call-expression") ||
	    pa11::strip_cv(expr.type)->kind != TypeKind::Record ||
	    !record_return_by_address(expr.type))
		return false;
	Binding* direct = expr.direct_call;
	TypePtr callee_type;
	string callee;
	if (direct != NULL)
	{
		callee_type = direct->type;
		program_.demand_function_declaration(direct);
		program_.demand_inline_function(direct);
		callee = "@" + program_.symbol_for(direct);
	}
	else
	{
		callee_type = strip_for_value(expr.children[0].type);
		if (pa11::strip_cv(callee_type)->kind == TypeKind::Pointer)
			callee_type = pa11::strip_cv(callee_type)->base;
		callee = emit_rvalue(expr.children[0]).text;
	}
	vector<string> args;
	args.push_back(addr_for().text);
	for (size_t i = 1; i < expr.children.size(); ++i)
	{
		bool variadic_extra = i - 1 >= callee_type->parameters.size();
		TypePtr param = !variadic_extra
			? callee_type->parameters[i - 1] : expr.children[i].type;
		if (variadic_extra && scalar_lowir_type(expr.children[i].type) == "f32")
			param = pa11::make_fundamental(FT_DOUBLE);
		lower_call_argument(expr.children[i], param, args);
	}
	ostringstream call;
	call << "call void " << callee << "(";
	for (size_t i = 0; i < args.size(); ++i)
	{
		if (i != 0)
			call << ", ";
		call << args[i];
	}
	call << ")";
	if (direct == NULL)
	{
		call << " as (%ret : ptr [pass=indirect_result]";
		for (size_t i = 0; i < callee_type->parameters.size(); ++i)
			call << ", %arg" << i << " : " <<
				lowir_parameter(callee_type->parameters[i]);
		call << ") -> void";
	}
	instr(call.str());
	return true;
}

void FunctionLowerer::init_call_target(const Node& expr,
                                       CallEmissionState& call)
{
	call.direct = expr.direct_call;
	call.arg_start = 1;
	call.virtual_call = call.direct != NULL && expr.virtual_dispatch &&
	                    call.direct->virtual_slot_index >= 0;
	call.delay_direct_demand =
		call.direct != NULL && call.direct->name == "operator=";
	if (call.direct != NULL)
	{
		call.callee_type = call.direct->type;
		if (!call.delay_direct_demand && !call.virtual_call &&
		    call.direct->owner != NULL &&
		    call.direct->owner->kind == ScopeKind::Class &&
		    !call.direct->is_static_member &&
		    call.direct->name == "operator()")
			call.delay_direct_demand = true;
		if (!call.delay_direct_demand && !call.virtual_call &&
		    call.direct->owner != NULL &&
		    call.direct->owner->kind == ScopeKind::Class &&
		    !call.direct->is_static_member && !expr.children.empty())
		{
			const Node& object_arg = expr.children[0];
			TypePtr object = object_arg.type.get() != NULL
				? pa11::strip_cv(object_type(object_arg.type))
				: TypePtr();
			if (object_arg.category != ValueCategory::LValue &&
			    object.get() != NULL && object->kind == TypeKind::Record)
				call.delay_direct_demand = true;
		}
		if (!call.delay_direct_demand && !call.virtual_call)
		{
			TypePtr result_record =
				pa11::strip_cv(call.callee_type->base);
			if (result_record->kind == TypeKind::Record &&
			    result_record->is_polymorphic)
				program_.demand_vtable(result_record);
			program_.demand_function_declaration(call.direct);
			program_.demand_inline_function(call.direct);
			call.callee = "@" + program_.symbol_for(call.direct);
		}
	}
	else
	{
		call.callee_type = strip_for_value(expr.children[0].type);
		if (pa11::strip_cv(call.callee_type)->kind == TypeKind::Pointer)
			call.callee_type = pa11::strip_cv(call.callee_type)->base;
	}
	call.ret = scalar_lowir_type(call.callee_type->base);
}

void FunctionLowerer::preallocate_call_result_slot(
	const Node& expr,
	CallEmissionState& call)
{
	if (call.ret == "void" || call.ret.compare(0, 4, "obj<") == 0)
		return;
	if (eh_try_depth_ == 0 && has_active_cleanups())
		call.preallocated_call_slot = fresh_aux_slot("call", call.ret);
	for (size_t i = call.arg_start; i < expr.children.size(); ++i)
	{
		bool variadic_extra =
			i - call.arg_start >= call.callee_type->parameters.size();
		if (variadic_extra)
			continue;
		TypePtr param = call.callee_type->parameters[i - call.arg_start];
		const Node& arg = expr.children[i];
		bool cleanup_arg = false;
		if (is_reference(param) && arg.category == ValueCategory::PRValue &&
		    pa11::strip_cv(param->base)->kind == TypeKind::Record &&
		    pa11::strip_cv(object_type(arg.type))->kind == TypeKind::Record &&
		    type_needs_cleanup(object_type(arg.type)))
			cleanup_arg = true;
		TypePtr bare_param = pa11::strip_cv(param);
		if (!cleanup_arg && bare_param->kind == TypeKind::Pointer &&
		    starts_with(arg.line, "unary-expression") && arg.has_op &&
		    arg.op == OP_AMP && !arg.children.empty() &&
		    arg.children[0].category != ValueCategory::LValue)
		{
			TypePtr object =
				pa11::strip_cv(object_type(arg.children[0].type));
			if (object->kind == TypeKind::Record && object->is_polymorphic &&
			    type_needs_cleanup(object))
				cleanup_arg = true;
		}
		if (cleanup_arg)
		{
			if (call.preallocated_call_slot.empty())
				call.preallocated_call_slot =
					fresh_aux_slot("call", call.ret);
			break;
		}
	}
}

void FunctionLowerer::prepare_call_setup_protection(
	const Node& expr,
	CallEmissionState& call)
{
	if (call_binding_has_template_cleanup_context(call.direct) ||
	    (call.direct != NULL && call.direct->name == "operator="))
		for (size_t i = call.arg_start; i < expr.children.size(); ++i)
		{
			bool variadic_extra =
				i - call.arg_start >= call.callee_type->parameters.size();
			TypePtr param = !variadic_extra
				? call.callee_type->parameters[i - call.arg_start]
				: expr.children[i].type;
			if (variadic_extra &&
			    scalar_lowir_type(expr.children[i].type) == "f32")
				param = pa11::make_fundamental(FT_DOUBLE);
			if (call_argument_needs_setup_cleanup_protection(
				    expr.children[i], param))
			{
				call.setup_may_create_temp_cleanup = true;
				break;
			}
		}
	call.protect_setup_only =
		eh_try_depth_ == 0 && has_active_cleanups() &&
		call.setup_may_create_temp_cleanup &&
		!call_setup_can_use_outer_eh(expr, call.callee_type,
		                             call.arg_start);
	call.protected_setup =
		eh_try_depth_ == 0 && !call.protect_setup_only &&
		((has_active_cleanups() &&
		  call_setup_can_use_outer_eh(expr, call.callee_type,
		                              call.arg_start)) ||
		 (!has_active_cleanups() && call.setup_may_create_temp_cleanup));
	if (call.protected_setup || call.protect_setup_only)
	{
		call.protected_dispatch = active_unwind_dispatch_.empty()
			? fresh_block("call_unwind_dispatch")
			: active_unwind_dispatch_;
		call.protected_define_dispatch = active_unwind_dispatch_.empty();
		instr("eh_try ^" + call.protected_dispatch);
		++eh_try_depth_;
	}
}

void FunctionLowerer::lower_call_arguments(const Node& expr,
                                           CallEmissionState& call)
{
	for (size_t i = call.arg_start; i < expr.children.size(); ++i)
	{
		bool variadic_extra =
			i - call.arg_start >= call.callee_type->parameters.size();
		if (variadic_extra &&
		    pa11::strip_cv(object_type(expr.children[i].type))->kind ==
			    TypeKind::Record)
		{
			const Node& arg = expr.children[i];
			if (arg.category == ValueCategory::LValue ||
			    arg.category == ValueCategory::XValue)
				call.args.push_back(
					ensure_pointer(emit_lvalue_addr(arg)).text);
			else
			{
				TypePtr record = object_type(arg.type);
				string slot =
					fresh_aux_slot("arg", slot_lowir_type(record));
				string addr_name = fresh_temp();
				instr(addr_name + " = addr $" + slot);
				Value target_addr("ptr", addr_name);
				function<Value()> addr_for = [target_addr]() {
					return target_addr;
				};
				lower_object_init(addr_for, record, arg);
				call.args.push_back(target_addr.text);
			}
			continue;
		}
		TypePtr param = !variadic_extra
			? call.callee_type->parameters[i - call.arg_start]
			: expr.children[i].type;
		if (variadic_extra && scalar_lowir_type(expr.children[i].type) == "f32")
			param = pa11::make_fundamental(FT_DOUBLE);
		lower_call_argument(expr.children[i], param, call.args,
		                    &call.temp_cleanups);
		if (!call.temp_cleanup_region_open && !call.temp_cleanups.empty() &&
		    !call.protected_setup && !call.protect_setup_only &&
		    call_temp_cleanup_defer_depth_ == 0 && eh_try_depth_ == 0)
		{
			call.temp_cleanup_dispatch =
				fresh_block("call_unwind_dispatch");
			call.temp_cleanup_end = fresh_block("call_unwind_end");
			instr("eh_try ^" + call.temp_cleanup_dispatch);
			++eh_try_depth_;
			call.temp_cleanup_region_open = true;
		}
	}
}

void FunctionLowerer::finish_setup_only_protection(CallEmissionState& call)
{
	if (!call.protect_setup_only)
		return;
	--eh_try_depth_;
	instr("eh_end");
	if (!call.protected_define_dispatch)
		return;
	string end = fresh_block("call_unwind_end");
	terminate("jump ^" + end);
	active_unwind_dispatch_ = call.protected_dispatch;
	start_block(call.protected_dispatch);
	emit_unwind_cleanups();
	terminate("resume");
	start_block(end);
}

void FunctionLowerer::resolve_call_callee(const Node& expr,
                                          CallEmissionState& call)
{
	if (call.direct != NULL && call.delay_direct_demand)
	{
		bool function_template_assignment =
			!call.direct->function_specialization_symbol.empty() ||
			(call.direct->aliased_binding != NULL &&
			 !call.direct->aliased_binding->function_specialization_symbol.empty());
		if (call.direct->name == "operator=" &&
		    call.direct->is_generated_copy_move_assignment &&
		    call.direct->owner != NULL &&
		    call.direct->owner->kind == ScopeKind::Class)
		{
			TypePtr record = pa11::record_type_for_scope(call.direct->owner);
			if (record.get() != NULL)
			{
				bool move = call.direct->type.get() != NULL &&
				            call.direct->type->kind == TypeKind::Function &&
				            call.direct->type->parameters.size() > 1 &&
				            call.direct->type->parameters[1]->kind ==
					            TypeKind::RValueReference;
				call.direct =
					program_.demand_implicit_copy_assignment(record, move);
				call.callee_type = call.direct->type;
			}
		}
		else if (call.direct->name == "operator=" &&
		         !call.direct->is_defaulted &&
		         !call.direct->is_inline_definition &&
		         !function_template_assignment &&
		         assignment_parameter_is_copy_move(call.direct) &&
		         call.direct->owner != NULL &&
		         call.direct->owner->kind == ScopeKind::Class)
		{
			TypePtr record = pa11::record_type_for_scope(call.direct->owner);
			if (record.get() != NULL)
			{
				bool move = call.direct->type.get() != NULL &&
				            call.direct->type->kind == TypeKind::Function &&
				            call.direct->type->parameters.size() > 1 &&
				            call.direct->type->parameters[1]->kind ==
					            TypeKind::RValueReference;
				call.direct =
					program_.demand_implicit_copy_assignment(record, move);
				call.callee_type = call.direct->type;
			}
		}
		program_.demand_function_declaration(call.direct);
		program_.demand_inline_function(call.direct);
		call.callee = "@" + program_.symbol_for(call.direct);
	}
	else if (call.direct == NULL)
		call.callee = emit_rvalue(expr.children[0]).text;
	if (!call.virtual_call)
		return;
	if (call.args.empty())
		throw runtime_error("virtual call missing object argument");
	string vptr = fresh_temp();
	instr(vptr + " = load ptr " + call.args[0]);
	string slot_addr = vptr;
	if (call.direct->virtual_slot_index > 0)
	{
		slot_addr = fresh_temp();
		instr(slot_addr + " = index i8 " + vptr + ", " +
		      to_string(call.direct->virtual_slot_index * 8));
	}
	string fnptr = fresh_temp();
	instr(fnptr + " = load ptr " + slot_addr);
	call.callee = fnptr;
}

bool FunctionLowerer::emit_record_return_call(CallEmissionState& call,
                                              Value& out)
{
	if (pa11::strip_cv(call.callee_type->base)->kind != TypeKind::Record ||
	    !record_return_by_address(call.callee_type->base))
		return false;
	string slot = fresh_aux_slot("callret",
	                             slot_lowir_type(call.callee_type->base));
	string addr = fresh_temp();
	instr(addr + " = addr $" + slot);
	vector<string> indirect_args;
	indirect_args.push_back(addr);
	indirect_args.insert(indirect_args.end(), call.args.begin(),
	                     call.args.end());
	ostringstream indirect_call;
	indirect_call << "call void " << call.callee << "(";
	for (size_t i = 0; i < indirect_args.size(); ++i)
	{
		if (i != 0)
			indirect_call << ", ";
		indirect_call << indirect_args[i];
	}
	indirect_call << ")";
	if (call.direct == NULL || call.virtual_call)
	{
		indirect_call << " as (%ret : ptr [pass=indirect_result]";
		for (size_t i = 0; i < call.callee_type->parameters.size(); ++i)
			indirect_call << ", %arg" << i << " : "
			              << lowir_parameter(call.callee_type->parameters[i]);
		indirect_call << ") -> void";
	}
	if (call.temp_cleanups.empty() || call_temp_cleanup_defer_depth_ > 0)
	{
		instr(indirect_call.str());
		for (size_t i = 0; i < call.temp_cleanups.size(); ++i)
			add_pending_temp_cleanup(call.temp_cleanups[i].first,
			                         call.temp_cleanups[i].second);
	}
	else
	{
		string dispatch = fresh_block("call_unwind_dispatch");
		string end = fresh_block("call_unwind_end");
		instr("eh_try ^" + dispatch);
		++eh_try_depth_;
		instr(indirect_call.str());
		--eh_try_depth_;
		instr("eh_end");
		terminate("jump ^" + end);
		start_block(dispatch);
		emit_temporary_cleanups(call.temp_cleanups);
		emit_unwind_cleanups();
		terminate("resume");
		start_block(end);
		for (size_t i = 0; i < call.temp_cleanups.size(); ++i)
			add_pending_temp_cleanup(call.temp_cleanups[i].first,
			                         call.temp_cleanups[i].second);
	}
	out = Value(scalar_lowir_type(call.callee_type->base), "$" + slot);
	return true;
}

void FunctionLowerer::build_scalar_call(CallEmissionState& call)
{
	ostringstream out;
	if (call.ret == "void")
		out << "call void ";
	else
	{
		call.tmp = fresh_temp();
		out << call.tmp << " = call " << call.ret << " ";
	}
	out << call.callee << "(";
	for (size_t i = 0; i < call.args.size(); ++i)
	{
		if (i != 0)
			out << ", ";
		out << call.args[i];
	}
	out << ")";
	if (call.direct == NULL || call.virtual_call)
	{
		out << " as (";
		for (size_t i = 0; i < call.callee_type->parameters.size(); ++i)
		{
			if (i != 0)
				out << ", ";
			out << "%arg" << i << " : "
			    << lowir_parameter(call.callee_type->parameters[i]);
		}
		out << ") -> " << call.ret;
	}
	call.call_text = out.str();
	call.cleanup_temps_in_call =
		call_binding_has_template_cleanup_context(call.direct) ||
		(call.direct != NULL && call.direct->name == "operator=");
}

bool FunctionLowerer::emit_protected_setup_scalar_call(
	CallEmissionState& call,
	Value& out)
{
	if (!call.protected_setup)
		return false;
	bool spill_result =
		call.ret != "void" && call.ret.compare(0, 4, "obj<") != 0;
	bool consume_store = spill_result && !call_result_store_slot_.empty();
	bool normal_temp_cleanup =
		!call.temp_cleanups.empty() &&
		(call.cleanup_temps_in_call || consume_store);
	string slot = call.preallocated_call_slot;
	string loaded;
	instr(call.call_text);
	if (spill_result)
	{
		if (slot.empty())
			slot = fresh_aux_slot("call", call.ret);
		instr("store " + call.ret + " " + call.tmp + ", $" + slot);
		loaded = fresh_temp();
		instr(loaded + " = load " + call.ret + " $" + slot);
	}
	if (consume_store)
	{
		Value stored = convert_value(Value(call.ret, loaded),
		                             call.callee_type->base,
		                             call_result_store_type_);
		instr("store " + scalar_lowir_type(call_result_store_type_) +
		      " " + stored.text + ", $" + call_result_store_slot_);
		call_result_store_consumed_ = true;
	}
	if (normal_temp_cleanup)
		emit_temporary_cleanups(call.temp_cleanups);
	--eh_try_depth_;
	instr("eh_end");
	if (!normal_temp_cleanup)
		for (size_t i = 0; i < call.temp_cleanups.size(); ++i)
			add_pending_temp_cleanup(call.temp_cleanups[i].first,
			                         call.temp_cleanups[i].second);
	if (!call.protected_define_dispatch)
	{
		out = spill_result ? Value(call.ret, loaded)
		                   : Value(call.ret, call.tmp);
		return true;
	}
	string end = fresh_block("call_unwind_end");
	terminate("jump ^" + end);
	active_unwind_dispatch_ = call.protected_dispatch;
	start_block(call.protected_dispatch);
	if (!call.temp_cleanups.empty())
		emit_temporary_cleanups(call.temp_cleanups);
	emit_unwind_cleanups();
	terminate("resume");
	start_block(end);
	out = spill_result ? Value(call.ret, loaded) : Value(call.ret, call.tmp);
	return true;
}

bool FunctionLowerer::emit_temp_cleanup_scalar_call(CallEmissionState& call,
                                                    Value& out)
{
	if (call.temp_cleanups.empty() || call_temp_cleanup_defer_depth_ > 0)
		return false;
	string slot;
	bool spill_result =
		call.ret != "void" && call.ret.compare(0, 4, "obj<") != 0;
	bool consume_logical = spill_result && !logical_call_result_slot_.empty();
	bool consume_store = spill_result && !call_result_store_slot_.empty();
	bool normal_temp_cleanup = call.cleanup_temps_in_call;
	if (spill_result)
		slot = call.preallocated_call_slot.empty()
			? fresh_aux_slot("call", call.ret)
			: call.preallocated_call_slot;
	string loaded;
	string dispatch = call.temp_cleanup_region_open
		? call.temp_cleanup_dispatch : fresh_block("call_unwind_dispatch");
	string end = call.temp_cleanup_region_open
		? call.temp_cleanup_end : fresh_block("call_unwind_end");
	if (!call.temp_cleanup_region_open)
	{
		instr("eh_try ^" + dispatch);
		++eh_try_depth_;
	}
	instr(call.call_text);
	if (spill_result)
	{
		instr("store " + call.ret + " " + call.tmp + ", $" + slot);
		loaded = fresh_temp();
		instr(loaded + " = load " + call.ret + " $" + slot);
	}
	if (consume_logical)
	{
		Value rv = bool_value(Value(call.ret, loaded),
		                      logical_call_result_type_);
		instr("store i64 " + rv.text + ", $" + logical_call_result_slot_);
		emit_temporary_cleanups(call.temp_cleanups);
		normal_temp_cleanup = true;
		logical_call_result_consumed_ = true;
	}
	else if (consume_store)
	{
		Value stored = convert_value(Value(call.ret, loaded),
		                             call.callee_type->base,
		                             call_result_store_type_);
		instr("store " + scalar_lowir_type(call_result_store_type_) + " " +
		      stored.text + ", $" + call_result_store_slot_);
		call_result_store_consumed_ = true;
		emit_temporary_cleanups(call.temp_cleanups);
		normal_temp_cleanup = true;
	}
	else if (normal_temp_cleanup)
		emit_temporary_cleanups(call.temp_cleanups);
	--eh_try_depth_;
	instr("eh_end");
	terminate("jump ^" + end);
	start_block(dispatch);
	emit_temporary_cleanups(call.temp_cleanups);
	emit_unwind_cleanups();
	terminate("resume");
	start_block(end);
	if (!normal_temp_cleanup)
		for (size_t i = 0; i < call.temp_cleanups.size(); ++i)
			add_pending_temp_cleanup(call.temp_cleanups[i].first,
			                         call.temp_cleanups[i].second);
	out = spill_result ? Value(call.ret, loaded) : Value(call.ret, call.tmp);
	return true;
}

bool FunctionLowerer::emit_active_cleanup_scalar_call(CallEmissionState& call,
                                                      Value& out)
{
	if (!call.temp_cleanups.empty() || eh_try_depth_ != 0 ||
	    !has_active_cleanups())
		return false;
	bool spill_result =
		call.ret != "void" && call.ret.compare(0, 4, "obj<") != 0;
	string slot = call.preallocated_call_slot;
	string loaded;
	string dispatch = active_unwind_dispatch_.empty()
		? fresh_block("call_unwind_dispatch") : active_unwind_dispatch_;
	bool define_dispatch = active_unwind_dispatch_.empty();
	instr("eh_try ^" + dispatch);
	++eh_try_depth_;
	instr(call.call_text);
	if (spill_result)
	{
		if (slot.empty())
			slot = fresh_aux_slot("call", call.ret);
		instr("store " + call.ret + " " + call.tmp + ", $" + slot);
		loaded = fresh_temp();
		instr(loaded + " = load " + call.ret + " $" + slot);
	}
	if (spill_result && !call_result_store_slot_.empty())
	{
		Value stored = convert_value(Value(call.ret, loaded),
		                             call.callee_type->base,
		                             call_result_store_type_);
		instr("store " + scalar_lowir_type(call_result_store_type_) + " " +
		      stored.text + ", $" + call_result_store_slot_);
		call_result_store_consumed_ = true;
	}
	--eh_try_depth_;
	instr("eh_end");
	if (!define_dispatch)
	{
		out = spill_result ? Value(call.ret, loaded)
		                   : Value(call.ret, call.tmp);
		return true;
	}
	string end = fresh_block("call_unwind_end");
	terminate("jump ^" + end);
	active_unwind_dispatch_ = dispatch;
	start_block(dispatch);
	emit_unwind_cleanups();
	terminate("resume");
	start_block(end);
	out = spill_result ? Value(call.ret, loaded) : Value(call.ret, call.tmp);
	return true;
}

Value FunctionLowerer::emit_plain_scalar_call(CallEmissionState& call)
{
	instr(call.call_text);
	for (size_t i = 0; i < call.temp_cleanups.size(); ++i)
		add_pending_temp_cleanup(call.temp_cleanups[i].first,
		                         call.temp_cleanups[i].second);
	if (eh_try_depth_ > 0 && has_active_cleanups() && call.ret != "void" &&
	    call.ret.compare(0, 4, "obj<") != 0)
	{
		string slot = fresh_aux_slot("call", call.ret);
		instr("store " + call.ret + " " + call.tmp + ", $" + slot);
		string loaded = fresh_temp();
		instr(loaded + " = load " + call.ret + " $" + slot);
		return Value(call.ret, loaded);
	}
	return Value(call.ret, call.tmp);
}

Value FunctionLowerer::emit_call(const Node& expr)
{
	CallEmissionState call;
	init_call_target(expr, call);
	preallocate_call_result_slot(expr, call);
	prepare_call_setup_protection(expr, call);
	lower_call_arguments(expr, call);
	finish_setup_only_protection(call);
	resolve_call_callee(expr, call);
	Value out;
	if (emit_record_return_call(call, out))
		return out;
	build_scalar_call(call);
	if (emit_protected_setup_scalar_call(call, out))
		return out;
	if (emit_temp_cleanup_scalar_call(call, out))
		return out;
	if (emit_active_cleanup_scalar_call(call, out))
		return out;
	return emit_plain_scalar_call(call);
}

}  // namespace internal
}  // namespace pa14
