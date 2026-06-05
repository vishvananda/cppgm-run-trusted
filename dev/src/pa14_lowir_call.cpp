#include "pa14_lowir_internal.h"

namespace pa14 {
namespace internal {

namespace {

void demand_record_return_calls(ProgramLowerer& program, const Node& node)
{
	if (starts_with(node.line, "call-expression") &&
	    node.direct_call != NULL &&
	    pa11::strip_cv(node.type)->kind == TypeKind::Record)
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
		if (temp_cleanups != NULL && type_needs_cleanup(object))
			temp_cleanups->push_back(make_pair(temp_addr, object));
		args.push_back(convert_value(temp_addr,
		                             pa11::make_pointer(object),
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
		if (temp_cleanups != NULL && type_needs_cleanup(object))
			temp_cleanups->push_back(make_pair(temp_addr, object));
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
		return true;
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
		TypePtr param_bare = pa11::strip_cv(param);
		bool pointer_to_void =
			param_bare->kind == TypeKind::Pointer &&
			pa11::is_void_type(pa11::strip_cv(param_bare->base));
		if (converted.type == "ptr" && converted.text == "0" &&
		    (arg.token_text == "nullptr" || pointer_to_void))
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

Value FunctionLowerer::emit_call(const Node& expr)
{
	Binding* direct = expr.direct_call;
	size_t arg_start = direct != NULL ? 1 : 1;
	string callee;
	TypePtr callee_type;
	bool virtual_call =
		direct != NULL && expr.virtual_dispatch &&
		direct->virtual_slot_index >= 0;
	bool delay_direct_demand = direct != NULL && direct->name == "operator=";
	if (direct != NULL)
	{
		callee_type = direct->type;
			if (!delay_direct_demand && !virtual_call &&
			    direct->owner != NULL &&
			    direct->owner->kind == ScopeKind::Class &&
			    !direct->is_static_member &&
			    direct->name == "operator()")
				delay_direct_demand = true;
			if (!delay_direct_demand && !virtual_call &&
			    direct->owner != NULL &&
			    direct->owner->kind == ScopeKind::Class &&
			    !direct->is_static_member &&
			    !expr.children.empty())
			{
				const Node& object_arg = expr.children[0];
				TypePtr object = object_arg.type.get() != NULL
					? pa11::strip_cv(object_type(object_arg.type))
					: TypePtr();
				if (object_arg.category != ValueCategory::LValue &&
				    object.get() != NULL &&
				    object->kind == TypeKind::Record)
					delay_direct_demand = true;
			}
		if (!delay_direct_demand && !virtual_call)
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
	string ret = scalar_lowir_type(callee_type->base);
	string preallocated_call_slot;
	if (ret != "void" && ret.compare(0, 4, "obj<") != 0)
	{
		if (eh_try_depth_ == 0 && has_active_cleanups())
			preallocated_call_slot = fresh_aux_slot("call", ret);
		for (size_t i = arg_start; i < expr.children.size(); ++i)
		{
			bool variadic_extra = i - arg_start >= callee_type->parameters.size();
			if (variadic_extra)
				continue;
			TypePtr param = callee_type->parameters[i - arg_start];
			const Node& arg = expr.children[i];
			bool cleanup_arg = false;
			if (is_reference(param) &&
			    arg.category == ValueCategory::PRValue &&
			    pa11::strip_cv(param->base)->kind == TypeKind::Record &&
			    pa11::strip_cv(object_type(arg.type))->kind == TypeKind::Record &&
			    type_needs_cleanup(object_type(arg.type)))
				cleanup_arg = true;
			if (cleanup_arg)
			{
				preallocated_call_slot = fresh_aux_slot("call", ret);
				break;
			}
		}
	}
	vector<string> args;
	vector<pair<Value, TypePtr> > temp_cleanups;
	bool setup_may_create_temp_cleanup = false;
	if (call_binding_has_template_cleanup_context(direct))
		for (size_t i = arg_start; i < expr.children.size(); ++i)
		{
			bool variadic_extra =
				i - arg_start >= callee_type->parameters.size();
			TypePtr param = !variadic_extra
				? callee_type->parameters[i - arg_start]
				: expr.children[i].type;
			if (variadic_extra &&
			    scalar_lowir_type(expr.children[i].type) == "f32")
				param = pa11::make_fundamental(FT_DOUBLE);
			if (call_argument_needs_setup_cleanup_protection(expr.children[i],
			                                                 param))
			{
				setup_may_create_temp_cleanup = true;
				break;
			}
		}
	bool protect_setup_only =
		eh_try_depth_ == 0 &&
		has_active_cleanups() &&
		setup_may_create_temp_cleanup &&
		!call_setup_can_use_outer_eh(expr, callee_type, arg_start);
	bool protected_setup =
		eh_try_depth_ == 0 &&
		!protect_setup_only &&
		((has_active_cleanups() &&
		  call_setup_can_use_outer_eh(expr, callee_type, arg_start)) ||
		 (!has_active_cleanups() && setup_may_create_temp_cleanup));
	string protected_dispatch;
	bool protected_define_dispatch = false;
	if (protected_setup || protect_setup_only)
	{
		protected_dispatch = active_unwind_dispatch_.empty()
			? fresh_block("call_unwind_dispatch") : active_unwind_dispatch_;
		protected_define_dispatch = active_unwind_dispatch_.empty();
		instr("eh_try ^" + protected_dispatch);
		++eh_try_depth_;
	}
	for (size_t i = arg_start; i < expr.children.size(); ++i)
	{
		bool variadic_extra = i - arg_start >= callee_type->parameters.size();
		if (variadic_extra &&
		    pa11::strip_cv(object_type(expr.children[i].type))->kind ==
			    TypeKind::Record)
		{
			const Node& arg = expr.children[i];
			if (arg.category == ValueCategory::LValue ||
			    arg.category == ValueCategory::XValue)
				args.push_back(ensure_pointer(emit_lvalue_addr(arg)).text);
			else
			{
				TypePtr record = object_type(arg.type);
				string slot = fresh_aux_slot("arg", slot_lowir_type(record));
				string addr_name = fresh_temp();
				instr(addr_name + " = addr $" + slot);
				Value target_addr("ptr", addr_name);
				function<Value()> addr_for = [target_addr]() {
					return target_addr;
				};
				lower_object_init(addr_for, record, arg);
				args.push_back(target_addr.text);
			}
			continue;
		}
		TypePtr param = !variadic_extra
			? callee_type->parameters[i - arg_start] : expr.children[i].type;
		if (variadic_extra && scalar_lowir_type(expr.children[i].type) == "f32")
			param = pa11::make_fundamental(FT_DOUBLE);
		lower_call_argument(expr.children[i], param, args, &temp_cleanups);
	}
	if (protect_setup_only)
	{
		--eh_try_depth_;
		instr("eh_end");
		if (protected_define_dispatch)
		{
			string end = fresh_block("call_unwind_end");
			terminate("jump ^" + end);
			active_unwind_dispatch_ = protected_dispatch;
			start_block(protected_dispatch);
			emit_unwind_cleanups();
			terminate("resume");
			start_block(end);
		}
	}
		if (direct != NULL && delay_direct_demand)
		{
			if (direct->name == "operator=" &&
			    !direct->is_defaulted &&
			    !direct->is_inline_definition &&
			    direct->owner != NULL &&
			    direct->owner->kind == ScopeKind::Class)
		{
			TypePtr record = pa11::record_type_for_scope(direct->owner);
			if (record.get() != NULL)
			{
				direct = program_.demand_implicit_copy_assignment(record, false);
				callee_type = direct->type;
			}
		}
		program_.demand_function_declaration(direct);
		program_.demand_inline_function(direct);
		callee = "@" + program_.symbol_for(direct);
	}
	else if (direct == NULL)
		callee = emit_rvalue(expr.children[0]).text;
	if (virtual_call)
	{
		if (args.empty())
			throw runtime_error("virtual call missing object argument");
		string vptr = fresh_temp();
		instr(vptr + " = load ptr " + args[0]);
		string slot_addr = vptr;
		if (direct->virtual_slot_index > 0)
		{
			slot_addr = fresh_temp();
			instr(slot_addr + " = index i8 " + vptr + ", " +
			      to_string(direct->virtual_slot_index * 8));
		}
		string fnptr = fresh_temp();
		instr(fnptr + " = load ptr " + slot_addr);
		callee = fnptr;
	}
	if (pa11::strip_cv(callee_type->base)->kind == TypeKind::Record &&
	    record_return_by_address(callee_type->base))
	{
		string slot = fresh_aux_slot("callret", slot_lowir_type(callee_type->base));
		string addr = fresh_temp();
		instr(addr + " = addr $" + slot);
		vector<string> indirect_args;
		indirect_args.push_back(addr);
		indirect_args.insert(indirect_args.end(), args.begin(), args.end());
		ostringstream indirect_call;
		indirect_call << "call void " << callee << "(";
		for (size_t i = 0; i < indirect_args.size(); ++i)
		{
			if (i != 0)
				indirect_call << ", ";
			indirect_call << indirect_args[i];
		}
		indirect_call << ")";
		if (direct == NULL || virtual_call)
		{
			indirect_call << " as (%ret : ptr [pass=indirect_result]";
			for (size_t i = 0; i < callee_type->parameters.size(); ++i)
				indirect_call << ", %arg" << i << " : " <<
					lowir_parameter(callee_type->parameters[i]);
			indirect_call << ") -> void";
		}
		if (temp_cleanups.empty() || call_temp_cleanup_defer_depth_ > 0)
		{
			instr(indirect_call.str());
			for (size_t i = 0; i < temp_cleanups.size(); ++i)
				add_pending_temp_cleanup(temp_cleanups[i].first,
				                         temp_cleanups[i].second);
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
			emit_temporary_cleanups(temp_cleanups);
			emit_unwind_cleanups();
			terminate("resume");
			start_block(end);
			for (size_t i = 0; i < temp_cleanups.size(); ++i)
				add_pending_temp_cleanup(temp_cleanups[i].first,
				                         temp_cleanups[i].second);
		}
		return Value(scalar_lowir_type(callee_type->base), "$" + slot);
	}
	ostringstream call;
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
	if (direct == NULL || virtual_call)
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
	bool cleanup_temps_in_call =
		call_binding_has_template_cleanup_context(direct);
	if (protected_setup)
	{
		bool spill_result = ret != "void" &&
		                    ret.compare(0, 4, "obj<") != 0;
		bool consume_store = spill_result &&
		                     !call_result_store_slot_.empty();
		bool normal_temp_cleanup =
			!temp_cleanups.empty() &&
			(cleanup_temps_in_call || consume_store);
		string slot = preallocated_call_slot;
		string loaded;
		instr(call.str());
		if (spill_result)
		{
			if (slot.empty())
				slot = fresh_aux_slot("call", ret);
			instr("store " + ret + " " + tmp + ", $" + slot);
			loaded = fresh_temp();
			instr(loaded + " = load " + ret + " $" + slot);
			}
		if (consume_store)
		{
			Value stored = convert_value(Value(ret, loaded),
			                             callee_type->base,
			                             call_result_store_type_);
			instr("store " + scalar_lowir_type(call_result_store_type_) +
		      " " + stored.text + ", $" + call_result_store_slot_);
			call_result_store_consumed_ = true;
		}
		if (normal_temp_cleanup)
			emit_temporary_cleanups(temp_cleanups);
		--eh_try_depth_;
		instr("eh_end");
		if (!normal_temp_cleanup)
			for (size_t i = 0; i < temp_cleanups.size(); ++i)
				add_pending_temp_cleanup(temp_cleanups[i].first,
				                         temp_cleanups[i].second);
		if (!protected_define_dispatch)
			return spill_result ? Value(ret, loaded) : Value(ret, tmp);
		string end = fresh_block("call_unwind_end");
		terminate("jump ^" + end);
		active_unwind_dispatch_ = protected_dispatch;
		start_block(protected_dispatch);
		if (!temp_cleanups.empty())
			emit_temporary_cleanups(temp_cleanups);
		emit_unwind_cleanups();
		terminate("resume");
		start_block(end);
		return spill_result ? Value(ret, loaded) : Value(ret, tmp);
	}
	if (!temp_cleanups.empty() && call_temp_cleanup_defer_depth_ == 0)
	{
		string slot;
		bool spill_result = ret != "void" &&
		                    ret.compare(0, 4, "obj<") != 0;
			bool consume_logical = spill_result &&
			                       !logical_call_result_slot_.empty();
			bool consume_store = spill_result &&
			                     !call_result_store_slot_.empty();
			bool normal_temp_cleanup = cleanup_temps_in_call;
			if (spill_result)
				slot = preallocated_call_slot.empty()
					? fresh_aux_slot("call", ret)
				: preallocated_call_slot;
		string loaded;
		string dispatch = fresh_block("call_unwind_dispatch");
		string end = fresh_block("call_unwind_end");
		instr("eh_try ^" + dispatch);
		++eh_try_depth_;
		instr(call.str());
		if (spill_result)
		{
			instr("store " + ret + " " + tmp + ", $" + slot);
			loaded = fresh_temp();
			instr(loaded + " = load " + ret + " $" + slot);
		}
		if (consume_logical)
		{
			Value rv = bool_value(Value(ret, loaded),
			                      logical_call_result_type_);
				instr("store i64 " + rv.text + ", $" +
				      logical_call_result_slot_);
				emit_temporary_cleanups(temp_cleanups);
				normal_temp_cleanup = true;
				logical_call_result_consumed_ = true;
			}
			else if (consume_store)
		{
			Value stored = convert_value(Value(ret, loaded),
			                             callee_type->base,
			                             call_result_store_type_);
			instr("store " + scalar_lowir_type(call_result_store_type_) +
			      " " + stored.text + ", $" + call_result_store_slot_);
				call_result_store_consumed_ = true;
				emit_temporary_cleanups(temp_cleanups);
				normal_temp_cleanup = true;
			}
			else if (normal_temp_cleanup)
				emit_temporary_cleanups(temp_cleanups);
			--eh_try_depth_;
			instr("eh_end");
		terminate("jump ^" + end);
		start_block(dispatch);
		emit_temporary_cleanups(temp_cleanups);
			emit_unwind_cleanups();
			terminate("resume");
			start_block(end);
			if (!normal_temp_cleanup)
				for (size_t i = 0; i < temp_cleanups.size(); ++i)
					add_pending_temp_cleanup(temp_cleanups[i].first,
					                         temp_cleanups[i].second);
			if (spill_result)
				return Value(ret, loaded);
			return Value(ret, tmp);
	}
	if (temp_cleanups.empty() && eh_try_depth_ == 0 && has_active_cleanups())
	{
		bool spill_result = ret != "void" &&
		                    ret.compare(0, 4, "obj<") != 0;
		string slot = preallocated_call_slot;
		string loaded;
		string dispatch = active_unwind_dispatch_.empty()
			? fresh_block("call_unwind_dispatch") : active_unwind_dispatch_;
		bool define_dispatch = active_unwind_dispatch_.empty();
		instr("eh_try ^" + dispatch);
		++eh_try_depth_;
		instr(call.str());
		if (spill_result)
		{
			if (slot.empty())
				slot = fresh_aux_slot("call", ret);
			instr("store " + ret + " " + tmp + ", $" + slot);
			loaded = fresh_temp();
			instr(loaded + " = load " + ret + " $" + slot);
		}
		if (spill_result && !call_result_store_slot_.empty())
		{
			Value stored = convert_value(Value(ret, loaded),
			                             callee_type->base,
			                             call_result_store_type_);
			instr("store " + scalar_lowir_type(call_result_store_type_) +
			      " " + stored.text + ", $" + call_result_store_slot_);
			call_result_store_consumed_ = true;
		}
		--eh_try_depth_;
		instr("eh_end");
		if (!define_dispatch)
			return spill_result ? Value(ret, loaded) : Value(ret, tmp);
		string end = fresh_block("call_unwind_end");
		terminate("jump ^" + end);
		if (define_dispatch)
		{
			active_unwind_dispatch_ = dispatch;
			start_block(dispatch);
			emit_unwind_cleanups();
			terminate("resume");
		}
		start_block(end);
		return spill_result ? Value(ret, loaded) : Value(ret, tmp);
	}
	instr(call.str());
	for (size_t i = 0; i < temp_cleanups.size(); ++i)
		add_pending_temp_cleanup(temp_cleanups[i].first,
		                         temp_cleanups[i].second);
	if (eh_try_depth_ > 0 && ret != "void" &&
	    ret.compare(0, 4, "obj<") != 0)
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
