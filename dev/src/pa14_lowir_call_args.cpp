#include "pa14_lowir_internal.h"
#include "pa14_lowir_function_internal.h"

namespace pa14 {
namespace internal {
namespace {

bool call_object_arg_is_this(const Node* object_arg)
{
	return object_arg != NULL &&
	       object_arg->binding != NULL &&
	       (object_arg->binding->name == "__this" ||
	        object_arg->binding->name == "this") &&
	       (starts_with(object_arg->line, "member-expression") ||
	        starts_with(object_arg->line, "id-expression"));
}

bool hosted_external_stream_member(const Binding* binding)
{
	if (hosted_external_stream_function_binding(binding))
		return true;
	if (binding == NULL ||
	    binding->owner == NULL ||
	    binding->owner->kind != ScopeKind::Namespace ||
	    (binding->owner->name != "std" &&
	     binding->owner->name != "__gnu_cxx") ||
	    binding->type.get() == NULL ||
	    binding->type->kind != TypeKind::Function)
		return false;
	for (size_t i = 0; i < binding->type->parameters.size(); ++i)
	{
		TypePtr param = pa11::strip_cv(binding->type->parameters[i]);
		if (param.get() != NULL &&
		    (param->kind == TypeKind::LValueReference ||
		     param->kind == TypeKind::RValueReference))
			param = pa11::strip_cv(param->base);
		if (record_uses_hosted_external_stream_vtable(param))
			return true;
	}
	return false;
}

}  // namespace

bool FunctionLowerer::lower_variadic_record_call_argument(
	const Node& arg,
	CallEmissionState& call)
{
	if (arg.category == ValueCategory::LValue ||
	    arg.category == ValueCategory::XValue)
	{
		call.args.push_back(ensure_pointer(emit_lvalue_addr(arg)).text);
		return true;
	}
	TypePtr record = object_type(arg.type);
	string slot = fresh_aux_slot("arg", slot_lowir_type(record));
	string addr_name = fresh_temp();
	instr(addr_name + " = addr $" + slot);
	Value target_addr("ptr", addr_name);
	function<Value()> addr_for = [target_addr]() {
		return target_addr;
	};
	lower_object_init(addr_for, record, arg);
	call.args.push_back(target_addr.text);
	return true;
}

bool FunctionLowerer::append_hidden_member_object_lvalue_argument(
	const Node& hidden_lookup_arg,
	TypePtr owner_record,
	CallEmissionState& call)
{
	bool found_hidden = false;
	TypePtr helper_hidden_record;
	Value hidden =
		emit_hidden_virtual_base_addr_for_lvalue(hidden_lookup_arg,
		                                         owner_record,
		                                         found_hidden,
		                                         &helper_hidden_record);
	if (!found_hidden)
		return false;
	if (pa11::same_type(pa11::strip_cv(helper_hidden_record),
	                    pa11::strip_cv(owner_record)))
		hidden = emit_base_subobject_addr(hidden,
		                                  owner_record,
		                                  owner_record);
	call.args.push_back(hidden.text);
	return true;
}

bool FunctionLowerer::append_hidden_member_cast_argument(
	const Node& hidden_lookup_arg,
	TypePtr owner_record,
	CallEmissionState& call)
{
	if (!starts_with(hidden_lookup_arg.line, "cast-expression") ||
	    fn_.binding->owner == NULL ||
	    fn_.binding->owner->kind != ScopeKind::Class ||
	    fn_.binding->is_static_member ||
	    is_class_constructor_binding(fn_.binding) ||
	    is_class_destructor_binding(fn_.binding))
		return false;
	string hidden_base;
	TypePtr hidden_base_record;
	for (size_t p = 0; p < fn_.children.size(); ++p)
		if (starts_with(fn_.children[p].line, "parameter "))
		{
			if (hidden_virtual_base_argument_for_parameter(
				    fn_.children[p].binding,
				    owner_record,
				    hidden_base,
				    hidden_base_record))
			{
				call.args.push_back(
					emit_base_subobject_addr(Value("ptr", hidden_base),
					                         hidden_base_record,
					                         owner_record).text);
				return true;
			}
			break;
		}
	return false;
}

void FunctionLowerer::find_hidden_member_this_argument(
	TypePtr owner_record,
	string& hidden_base,
	TypePtr& hidden_base_record)
{
	vector<TypePtr> this_vbases =
		hidden_virtual_bases_for_record(class_record_for_member(fn_.binding));
	for (size_t v = 0; v < this_vbases.size(); ++v)
	{
		TypePtr hidden_record = pa11::strip_cv(this_vbases[v]);
		if (pa11::same_type(hidden_record, pa11::strip_cv(owner_record)) ||
		    record_has_base_subobject(hidden_record, owner_record))
		{
			hidden_base = "%__vbptr" + to_string(v);
			hidden_base_record = hidden_record;
			return;
		}
	}
}

void FunctionLowerer::find_hidden_member_parameter_argument(
	const Node& hidden_lookup_arg,
	TypePtr owner_record,
	string& hidden_base,
	TypePtr& hidden_base_record)
{
	if (!starts_with(hidden_lookup_arg.line, "id-expression") ||
	    hidden_lookup_arg.binding == NULL ||
	    hidden_lookup_arg.binding->kind != BindingKind::Parameter)
		return;
	Binding* param_binding = hidden_lookup_arg.binding;
	size_t hidden_index = 0;
	for (size_t pi = 0; pi < fn_.children.size(); ++pi)
	{
		if (!starts_with(fn_.children[pi].line, "parameter "))
			continue;
		Binding* candidate = fn_.children[pi].binding;
		if (candidate == NULL)
			continue;
		bool member_this_param =
			fn_.binding->owner != NULL &&
			fn_.binding->owner->kind == ScopeKind::Class &&
			!fn_.binding->is_static_member &&
			pi == 0;
		if (member_this_param)
			continue;
		TypePtr ptype = candidate->type;
		vector<TypePtr> vbases = hidden_virtual_bases_for_parameter(ptype);
		for (size_t v = 0; v < vbases.size(); ++v)
		{
			TypePtr hidden_record = pa11::strip_cv(vbases[v]);
			if (candidate == param_binding &&
			    (pa11::same_type(hidden_record,
			                    pa11::strip_cv(owner_record)) ||
			     record_has_base_subobject(hidden_record, owner_record)))
			{
				TypePtr pbare = pa11::strip_cv(ptype);
				if ((pbare->kind == TypeKind::LValueReference ||
				     pbare->kind == TypeKind::RValueReference) &&
				    pa11::strip_cv(pbare->base)->kind == TypeKind::Record)
				{
					hidden_base = fresh_temp();
					instr(hidden_base + " = load ptr $" +
					      slot_for(param_binding) + "__pvb" +
					      to_string(v));
				}
				else
					hidden_base = "%__pvbptr" + to_string(hidden_index);
				hidden_base_record = hidden_record;
				return;
			}
			++hidden_index;
		}
	}
}

bool FunctionLowerer::append_hidden_member_object_argument(
	const Node& object_arg,
	TypePtr owner_record,
	CallEmissionState& call)
{
	if (owner_record.get() == NULL)
		return false;
	const Node* hidden_lookup_arg = &object_arg;
	if (starts_with(object_arg.line, "unary-expression") &&
	    object_arg.has_op &&
	    object_arg.op == OP_AMP &&
	    !object_arg.children.empty())
		hidden_lookup_arg = &object_arg.children[0];
	if ((object_arg.category == ValueCategory::LValue ||
	     object_arg.category == ValueCategory::XValue) &&
	    append_hidden_member_object_lvalue_argument(*hidden_lookup_arg,
	                                                owner_record,
	                                                call))
		return true;
	if (append_hidden_member_cast_argument(*hidden_lookup_arg,
	                                       owner_record,
	                                       call))
		return true;
	string hidden_base;
	TypePtr hidden_base_record;
	bool object_is_this = call_object_arg_is_this(hidden_lookup_arg);
	if (object_is_this &&
	    !is_class_constructor_binding(fn_.binding) &&
	    !is_class_destructor_binding(fn_.binding))
		find_hidden_member_this_argument(owner_record,
		                                 hidden_base,
		                                 hidden_base_record);
	if (hidden_base.empty())
		find_hidden_member_parameter_argument(*hidden_lookup_arg,
		                                      owner_record,
		                                      hidden_base,
		                                      hidden_base_record);
	if (hidden_base.empty())
		return false;
	call.args.push_back(
		emit_base_subobject_addr(Value("ptr", hidden_base),
		                         hidden_base_record,
		                         owner_record).text);
	return true;
}

void FunctionLowerer::maybe_open_call_temp_cleanup_region(
	CallEmissionState& call)
{
	if (call.temp_cleanup_region_open ||
	    call.temp_cleanups.empty() ||
	    call.protected_setup ||
	    call.protect_setup_only ||
	    call_temp_cleanup_defer_depth_ != 0 ||
	    eh_try_depth_ != 0)
		return;
	call.temp_cleanup_dispatch = fresh_block("call_unwind_dispatch");
	call.temp_cleanup_end = fresh_block("call_unwind_end");
	instr((call_temp_cleanup_region_is_cleanup_only(call)
	       ? "eh_cleanup ^" : "eh_try ^") +
	      call.temp_cleanup_dispatch);
	++eh_try_depth_;
	call.temp_cleanup_region_open = true;
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
			lower_variadic_record_call_argument(expr.children[i], call);
			continue;
		}
		TypePtr param = !variadic_extra
			? call.callee_type->parameters[i - call.arg_start]
			: expr.children[i].type;
		if (variadic_extra && scalar_lowir_type(expr.children[i].type) == "f32")
			param = pa11::make_fundamental(FT_DOUBLE);
		if (!variadic_extra &&
		    i == call.arg_start &&
		    call.direct != NULL &&
		    call.direct->owner != NULL &&
		    call.direct->owner->kind == ScopeKind::Class &&
		    !call.direct->is_static_member &&
		    !hosted_external_stream_member(call.direct))
		{
			TypePtr owner_record = class_record_for_member(call.direct);
			if (append_hidden_member_object_argument(expr.children[i],
			                                         owner_record,
			                                         call))
				continue;
		}
		TypePtr result = pa11::strip_cv(call.callee_type->base);
		TypePtr bare_param = pa11::strip_cv(param);
		bool function_template_callee =
			call.direct != NULL &&
			binding_has_function_template_specialization_symbol(call.direct);
		bool preserve_no_storage_lvalue =
			!variadic_extra &&
			function_template_callee &&
			result->kind == TypeKind::Record &&
			bare_param->kind == TypeKind::Record;
		lower_call_argument(expr.children[i], param, call.args,
		                    &call.temp_cleanups,
		                    preserve_no_storage_lvalue);
		call.arg_types.push_back(param);
		maybe_open_call_temp_cleanup_region(call);
	}
}

string FunctionLowerer::hidden_parameter_pvb_from_existing_parameter(
	const Node& arg,
	TypePtr vbase)
{
	if (!starts_with(arg.line, "id-expression") ||
	    arg.binding == NULL ||
	    arg.binding->kind != BindingKind::Parameter)
		return "";
	vector<TypePtr> arg_vbases =
		hidden_virtual_bases_for_parameter(arg.binding->type);
	for (size_t av = 0; av < arg_vbases.size(); ++av)
		if (pa11::same_type(pa11::strip_cv(arg_vbases[av]),
		                    pa11::strip_cv(vbase)))
		{
			TypePtr arg_type = pa11::strip_cv(arg.binding->type);
			if ((arg_type->kind == TypeKind::LValueReference ||
			     arg_type->kind == TypeKind::RValueReference) &&
			    pa11::strip_cv(arg_type->base)->kind == TypeKind::Record)
			{
				string loaded = fresh_temp();
				instr(loaded + " = load ptr $" +
				      slot_for(arg.binding) + "__pvb" +
				      to_string(av));
				return loaded;
			}
			return "%__pvbptr" + to_string(av);
		}
	return "";
}

string FunctionLowerer::hidden_parameter_pvb_from_explicit_record(
	const Node* arg,
	const string& explicit_record_arg,
	TypePtr context,
	TypePtr vbase)
{
	if (arg == NULL || explicit_record_arg.empty())
		return "";
	TypePtr source_context = hidden_virtual_base_context_record(arg->type);
	if (source_context.get() == NULL ||
	    context.get() == NULL ||
	    !pa11::same_type(pa11::strip_cv(source_context),
	                     pa11::strip_cv(context)) ||
	    !record_has_base_subobject(context, vbase))
		return "";
	return emit_base_subobject_addr(Value("ptr", explicit_record_arg),
	                                context,
	                                vbase).text;
}

string FunctionLowerer::hidden_parameter_pvb_from_argument_value(
	const Node* arg,
	const string& explicit_record_arg,
	TypePtr context,
	TypePtr vbase)
{
	TypePtr source;
	Value base;
	if (arg != NULL &&
	    (arg->category == ValueCategory::LValue ||
	     arg->category == ValueCategory::XValue))
	{
		base = ensure_pointer(emit_lvalue_addr(*arg));
		source = pa11::strip_cv(object_type(arg->type));
	}
	else if (arg != NULL)
	{
		base = emit_rvalue(*arg);
		source = pa11::strip_cv(strip_for_value(arg->type));
		if (source.get() != NULL && source->kind == TypeKind::Pointer)
			source = pa11::strip_cv(source->base);
	}
	if (source.get() != NULL &&
	    source->kind == TypeKind::Record &&
	    record_has_base_subobject(source, vbase))
		return emit_base_subobject_addr(base, source, vbase).text;
	if (!explicit_record_arg.empty())
		return emit_base_subobject_addr(Value("ptr", explicit_record_arg),
		                                context,
		                                vbase).text;
	return "";
}

void FunctionLowerer::append_hidden_parameter_call_arguments(
	const Node& expr,
	CallEmissionState& call,
	bool member_this_param)
{
	if (hosted_external_stream_member(call.direct))
		return;
	for (size_t p = member_this_param ? 1 : 0;
	     p < call.callee_type->parameters.size();
	     ++p)
	{
		size_t arg_index = call.arg_start + p;
		TypePtr context =
			hidden_virtual_base_context_record(call.callee_type->parameters[p]);
		vector<TypePtr> vbases = call.direct != NULL
			? program_.hidden_virtual_bases_for_function_parameter(
				call.direct, p, call.callee_type->parameters[p])
			: hidden_virtual_bases_for_parameter(
				call.callee_type->parameters[p]);
		if (vbases.empty())
			continue;
		const Node* arg = arg_index < expr.children.size()
			? &expr.children[arg_index] : NULL;
		string explicit_arg =
			arg_index >= call.arg_start &&
			arg_index - call.arg_start < call.args.size()
			? call.args[arg_index - call.arg_start] : string();
		string explicit_record_arg = explicit_arg;
		TypePtr param_bare = pa11::strip_cv(call.callee_type->parameters[p]);
		bool ref_pointer =
			(param_bare->kind == TypeKind::LValueReference ||
			 param_bare->kind == TypeKind::RValueReference) &&
			pa11::strip_cv(param_bare->base)->kind == TypeKind::Pointer;
		if (!explicit_record_arg.empty() && ref_pointer)
		{
			string loaded = fresh_temp();
			instr(loaded + " = load ptr " + explicit_record_arg);
			explicit_record_arg = loaded;
		}
		for (size_t v = 0; v < vbases.size(); ++v)
		{
			string hidden = arg != NULL
				? hidden_parameter_pvb_from_existing_parameter(*arg,
				                                               vbases[v])
				: string();
			if (hidden.empty())
				hidden = hidden_parameter_pvb_from_explicit_record(
					arg, explicit_record_arg, context, vbases[v]);
			if (hidden.empty())
				hidden = hidden_parameter_pvb_from_argument_value(
					arg, explicit_record_arg, context, vbases[v]);
			call.args.push_back(hidden.empty() ? "0" : hidden);
		}
	}
}

string FunctionLowerer::hidden_this_call_argument(
	const Node* object_arg,
	const string& explicit_arg,
	bool object_arg_is_this,
	TypePtr this_record,
	TypePtr vbase,
	size_t vbase_index)
{
	if (object_arg_is_this &&
	    !is_class_constructor_binding(fn_.binding) &&
	    !is_class_destructor_binding(fn_.binding))
		return "%__vbptr" + to_string(vbase_index);
	if (object_arg != NULL && !object_arg_is_this)
	{
		TypePtr source;
		Value base;
		if (object_arg->category == ValueCategory::LValue ||
		    object_arg->category == ValueCategory::XValue)
		{
			base = ensure_pointer(emit_lvalue_addr(*object_arg));
			source = pa11::strip_cv(object_type(object_arg->type));
		}
		else
		{
			base = emit_rvalue(*object_arg);
			source = pa11::strip_cv(strip_for_value(object_arg->type));
			if (source.get() != NULL && source->kind == TypeKind::Pointer)
				source = pa11::strip_cv(source->base);
		}
		if (source.get() != NULL &&
		    source->kind == TypeKind::Record &&
		    record_has_base_subobject(source, vbase))
			return emit_base_subobject_addr(base, source, vbase).text;
	}
	if (explicit_arg.empty())
		return "";
	if (object_arg_is_this)
	{
		string this_ptr = fresh_temp();
		instr(this_ptr + " = load ptr $this");
		return emit_base_subobject_addr(Value("ptr", this_ptr),
		                                this_record,
		                                vbase).text;
	}
	return emit_base_subobject_addr(Value("ptr", explicit_arg),
	                                this_record,
	                                vbase).text;
}

void FunctionLowerer::append_hidden_this_call_arguments(
	const Node& expr,
	CallEmissionState& call,
	bool member_this_param)
{
	if (!member_this_param ||
	    call.direct == NULL ||
	    hosted_external_stream_member(call.direct) ||
	    is_class_constructor_binding(call.direct) ||
	    is_class_destructor_binding(call.direct))
		return;
	TypePtr this_record = class_record_for_member(call.direct);
	vector<TypePtr> vbases = call.direct->is_virtual
		? program_.hidden_virtual_bases_for_function_parameter(
			call.direct, 0, call.callee_type->parameters[0])
		: hidden_virtual_bases_for_record(this_record);
	const Node* object_arg =
		call.arg_start < expr.children.size()
		? &expr.children[call.arg_start] : NULL;
	string explicit_arg = !call.args.empty() ? call.args[0] : string();
	bool object_arg_is_this = call_object_arg_is_this(object_arg);
	for (size_t v = 0; v < vbases.size(); ++v)
	{
		string hidden = hidden_this_call_argument(object_arg,
		                                         explicit_arg,
		                                         object_arg_is_this,
		                                         this_record,
		                                         vbases[v],
		                                         v);
		call.args.push_back(hidden.empty() ? "0" : hidden);
	}
}

void FunctionLowerer::append_hidden_call_arguments(const Node& expr,
                                                   CallEmissionState& call)
{
	bool member_this_param =
		call.direct != NULL &&
		call.direct->owner != NULL &&
		call.direct->owner->kind == ScopeKind::Class &&
		!call.direct->is_static_member &&
		!call.callee_type->parameters.empty();
	append_hidden_parameter_call_arguments(expr, call, member_this_param);
	append_hidden_this_call_arguments(expr, call, member_this_param);
}

}  // namespace internal
}  // namespace pa14
