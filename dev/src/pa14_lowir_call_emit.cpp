#include "pa14_lowir_internal.h"
#include "pa14_lowir_function_internal.h"
#include "pa12_templates_function_support.h"

namespace pa14 {
namespace internal {

namespace {

bool call_binding_has_template_cleanup_context(const Binding* binding)
{
	return binding != NULL &&
	       (binding_has_function_template_specialization_symbol(binding) ||
	        binding_has_template_specialization_context(binding));
}

bool hosted_std_namespace_scope(const Scope* scope)
{
	for (const Scope* cur = scope; cur != NULL; cur = cur->parent)
		if (cur->kind == ScopeKind::Namespace && cur->name == "std")
			return true;
	return false;
}

bool scope_has_namespace_name(const Scope* scope, const string& name)
{
	for (const Scope* cur = scope; cur != NULL; cur = cur->parent)
		if (cur->kind == ScopeKind::Namespace && cur->name == name)
			return true;
	return false;
}

bool hosted_std_forwarding_binding(const Binding* binding)
{
	return binding != NULL &&
	       binding->owner != NULL &&
	       binding->owner->kind == ScopeKind::Namespace &&
	       scope_has_namespace_name(binding->owner, "std") &&
	       (binding->name == "move" || binding->name == "forward");
}

Binding* unresolved_direct_function_callee(const Node& expr)
{
	if (!starts_with(expr.line, "call-expression") ||
	    expr.children.empty())
		return NULL;
	const Node& callee = expr.children[0];
	if (callee.binding != NULL &&
	    callee.binding->kind == BindingKind::Function)
		return callee.binding;
	if ((starts_with(callee.line, "unary-expression") ||
	     starts_with(callee.line, "cast-expression")) &&
	    callee.children.size() == 1 &&
	    callee.children[0].binding != NULL &&
	    callee.children[0].binding->kind == BindingKind::Function)
		return callee.children[0].binding;
	return NULL;
}

Binding* hosted_std_forwarding_call_binding(const Node& expr)
{
	if (hosted_std_forwarding_binding(expr.direct_call))
		return expr.direct_call;
	Binding* callee = unresolved_direct_function_callee(expr);
	return hosted_std_forwarding_binding(callee) ? callee : NULL;
}

string unqualified_template_primary_name(TypePtr type)
{
	TypePtr bare = type.get() != NULL ? pa11::strip_cv(type) : TypePtr();
	if (bare.get() == NULL)
		return "";
	string primary = bare->template_primary_name.empty()
		? bare->name : bare->template_primary_name;
	size_t pos = primary.rfind("::");
	return pos == string::npos ? primary : primary.substr(pos + 2);
}

bool hosted_vector_bool_record(TypePtr type)
{
	TypePtr bare = type.get() != NULL ? pa11::strip_cv(type) : TypePtr();
	if (bare.get() == NULL ||
	    bare->kind != TypeKind::Record ||
	    !bare->is_template_specialization ||
	    bare->scope == NULL ||
	    unqualified_template_primary_name(bare) != "vector" ||
	    bare->template_arguments.empty() ||
	    bare->template_arguments[0].kind !=
		    pa11::TemplateInstanceArgumentKind::Type)
		return false;
	TypePtr element = pa11::strip_cv(bare->template_arguments[0].type);
	return element.get() != NULL &&
	       element->kind == TypeKind::Fundamental &&
	       element->fundamental == FT_BOOL &&
	       hosted_std_namespace_scope(bare->scope);
}

bool template_instance_type_argument(TypePtr record, size_t index, TypePtr& out)
{
	TypePtr bare = record.get() != NULL ? pa11::strip_cv(record) : TypePtr();
	if (bare.get() == NULL || index >= bare->template_arguments.size())
		return false;
	const pa11::TemplateInstanceArgument& arg =
		bare->template_arguments[index];
	if (arg.kind != pa11::TemplateInstanceArgumentKind::Type)
		return false;
	out = arg.type;
	return out.get() != NULL;
}

bool hosted_vector_record(TypePtr type, TypePtr& element)
{
	TypePtr bare = type.get() != NULL ? pa11::strip_cv(type) : TypePtr();
	if (bare.get() == NULL ||
	    bare->kind != TypeKind::Record ||
	    !bare->is_template_specialization ||
	    bare->scope == NULL ||
	    unqualified_template_primary_name(bare) != "vector" ||
	    !hosted_std_namespace_scope(bare->scope) ||
	    !template_instance_type_argument(bare, 0, element))
		return false;
	element = pa11::strip_cv(element);
	return element.get() != NULL;
}

bool hosted_normal_iterator_record(TypePtr type,
                                   TypePtr& iterator,
                                   TypePtr& container)
{
	TypePtr bare = type.get() != NULL ? pa11::strip_cv(type) : TypePtr();
	if (bare.get() == NULL ||
	    bare->kind != TypeKind::Record ||
	    !bare->is_template_specialization ||
	    unqualified_template_primary_name(bare) != pa11::abi_private_name("_normal_iterator") ||
	    !scope_has_namespace_name(bare->scope, "__gnu_cxx") ||
	    !template_instance_type_argument(bare, 0, iterator) ||
	    !template_instance_type_argument(bare, 1, container))
		return false;
	iterator = pa11::strip_cv(iterator);
	container = pa11::strip_cv(container);
	return iterator.get() != NULL && container.get() != NULL;
}

bool hosted_vector_bool_insert_aux_binding(const Binding* binding)
{
	return binding != NULL &&
	       binding->name == pa11::abi_private_name("M_insert_aux") &&
	       hosted_vector_bool_record(class_record_for_member(binding));
}

bool hosted_vector_range_insert_binding(const Binding* binding,
                                        TypePtr& element)
{
	if (binding == NULL ||
	    binding->name != "insert" ||
	    binding->type.get() == NULL ||
	    binding->type->kind != TypeKind::Function ||
	    binding->type->parameters.size() != 4 ||
	    !hosted_vector_record(class_record_for_member(binding), element))
		return false;
	TypePtr bare = pa11::strip_cv(element);
	return bare.get() != NULL &&
	       bare->kind != TypeKind::Record &&
	       bare->kind != TypeKind::Array;
}

void declare_hosted_operator_new(ProgramLowerer& program)
{
	if (program.declared_functions.insert("operator_new").second)
		program.declares.push_back(
			"declare function @operator_new(%arg0 : i64) -> ptr "
			"[binding=strong, object=" +
			string(program.native_lowering
			       ? "_Znwm" : "cppgm_builtin_operator_new") + "]");
}

void declare_hosted_operator_delete(ProgramLowerer& program)
{
	if (program.declared_functions.insert("operator_delete").second)
		program.declares.push_back(
			"declare function @operator_delete(%arg0 : ptr) -> void "
			"[unwind=no, binding=strong, object=" +
			string(program.native_lowering
			       ? "_ZdlPv" : "cppgm_builtin_operator_delete") + "]");
}

void declare_hosted_memmove(ProgramLowerer& program)
{
	if (program.declared_functions.insert("__builtin_memmove").second)
		program.declares.push_back(
			"declare function @__builtin_memmove(%arg0 : ptr "
			"[capture=nocapture, access=readwrite], "
			"%arg1 : ptr [capture=nocapture, access=read], "
			"%arg2 : i64) -> ptr [effects=readwrite, unwind=no, "
			"linkage=c, binding=strong, object=memmove]");
}

bool assignment_parameter_is_copy_move(const Binding* binding)
{
	if (binding == NULL ||
	    binding->type.get() == NULL ||
	    binding->type->kind != TypeKind::Function ||
	    binding->type->parameters.size() != 2 ||
	    !is_reference(binding->type->parameters[1]))
		return false;
	TypePtr record = class_record_for_member(binding);
	record = record.get() != NULL ? pa11::strip_cv(record) : TypePtr();
	TypePtr param = pa11::strip_cv(binding->type->parameters[1]->base);
	return record.get() != NULL &&
	       param.get() != NULL &&
	       record->kind == TypeKind::Record &&
	       param->kind == TypeKind::Record &&
	       pa11::same_type(record, param);
}

}  // namespace

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
		program_.demand_inline_function(call.direct, true);
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
	if (call.virtual_slot_index > 0)
	{
		slot_addr = fresh_temp();
		instr(slot_addr + " = index i8 " + vptr + ", " +
		      to_string(call.virtual_slot_index * 8));
	}
	string fnptr = fresh_temp();
	instr(fnptr + " = load ptr " + slot_addr);
	call.callee = fnptr;
	}

bool FunctionLowerer::call_temp_cleanup_region_is_cleanup_only(
	const CallEmissionState& call) const
{
	return active_catches_.empty() &&
	       temp_cleanups_are_generated_noop_destructors(call.temp_cleanups);
}

void FunctionLowerer::emit_record_return_open_cleanup_region(
	CallEmissionState& call,
	const string& call_text)
{
	string dispatch = call.protected_setup
		? call.protected_dispatch : call.temp_cleanup_dispatch;
	string end = call.protected_setup
		? fresh_block("call_unwind_end") : call.temp_cleanup_end;
	bool cleanup_only =
		call.temp_cleanup_region_open &&
		call_temp_cleanup_region_is_cleanup_only(call);
	instr(call_text);
	--eh_try_depth_;
	instr("eh_end");
	terminate("jump ^" + end);
	start_block(dispatch);
	if (!cleanup_only)
	{
		emit_active_catch_clauses();
		if (program_.native_lowering || !active_catches_.empty())
			instr("eh_cleanup");
	}
	emit_temporary_cleanups(call.temp_cleanups);
	emit_unwind_cleanups();
	if (cleanup_only)
		terminate("resume");
	else
		terminate_unwind_or_active_catch();
	start_block(end);
	for (size_t i = 0; i < call.temp_cleanups.size(); ++i)
		add_pending_temp_cleanup(call.temp_cleanups[i].first,
		                         call.temp_cleanups[i].second);
}

void FunctionLowerer::emit_record_return_temp_cleanup_call(
	CallEmissionState& call,
	const string& call_text)
{
	string dispatch = fresh_block("call_unwind_dispatch");
	string end = fresh_block("call_unwind_end");
	bool cleanup_only =
		call_temp_cleanup_region_is_cleanup_only(call);
	instr((cleanup_only ? "eh_cleanup ^" : "eh_try ^") + dispatch);
	++eh_try_depth_;
	instr(call_text);
	--eh_try_depth_;
	instr("eh_end");
	terminate("jump ^" + end);
	start_block(dispatch);
	if (!cleanup_only)
	{
		emit_active_catch_clauses();
		if (program_.native_lowering || !active_catches_.empty())
			instr("eh_cleanup");
	}
	emit_temporary_cleanups(call.temp_cleanups);
	emit_unwind_cleanups();
	if (cleanup_only)
		terminate("resume");
	else
		terminate_unwind_or_active_catch();
	start_block(end);
	for (size_t i = 0; i < call.temp_cleanups.size(); ++i)
		add_pending_temp_cleanup(call.temp_cleanups[i].first,
		                         call.temp_cleanups[i].second);
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
		size_t hidden = 0;
		bool member_this_param =
			call.direct != NULL &&
			call.direct->owner != NULL &&
			call.direct->owner->kind == ScopeKind::Class &&
			!call.direct->is_static_member &&
			!call.callee_type->parameters.empty();
		for (size_t i = member_this_param ? 1 : 0;
		     i < call.callee_type->parameters.size();
		     ++i)
		{
			vector<TypePtr> vbases = call.direct != NULL
				? program_.hidden_virtual_bases_for_function_parameter(
					call.direct, i, call.callee_type->parameters[i])
				: hidden_virtual_bases_for_parameter(
					call.callee_type->parameters[i]);
			for (size_t v = 0; v < vbases.size(); ++v)
				indirect_call << ", %__pvbptr" << hidden++ << " : ptr";
		}
		if (member_this_param &&
		    call.direct != NULL &&
		    !is_class_constructor_binding(call.direct) &&
		    !is_class_destructor_binding(call.direct))
		{
			vector<TypePtr> vbases = call.direct->is_virtual
				? program_.hidden_virtual_bases_for_function_parameter(
					call.direct, 0, call.callee_type->parameters[0])
				: hidden_virtual_bases_for_record(
					class_record_for_member(call.direct));
			for (size_t v = 0; v < vbases.size(); ++v)
				indirect_call << ", %__vbptr" << v << " : ptr";
		}
			indirect_call << ") -> void";
		}
		if (call.protected_setup || call.temp_cleanup_region_open)
		{
			emit_record_return_open_cleanup_region(call,
			                                       indirect_call.str());
			out = Value(scalar_lowir_type(call.callee_type->base), "$" + slot);
			return true;
		}
		if (call.temp_cleanups.empty() || call_temp_cleanup_defer_depth_ > 0)
		{
			instr(indirect_call.str());
		if (call.protected_setup)
		{
			--eh_try_depth_;
			instr("eh_end");
			if (call.protected_define_dispatch)
			{
				string end = fresh_block("call_unwind_end");
				terminate("jump ^" + end);
				active_unwind_dispatch_ = call.protected_dispatch;
				active_unwind_cleanup_depth_ = cleanups_.size();
				start_block(call.protected_dispatch);
				emit_active_catch_clauses();
				if (program_.native_lowering || !active_catches_.empty())
					instr("eh_cleanup");
				emit_unwind_cleanups();
				terminate_unwind_or_active_catch();
				start_block(end);
			}
		}
		for (size_t i = 0; i < call.temp_cleanups.size(); ++i)
			add_pending_temp_cleanup(call.temp_cleanups[i].first,
			                         call.temp_cleanups[i].second);
	}
	else
	{
		emit_record_return_temp_cleanup_call(call, indirect_call.str());
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
	bool direct_variadic_signature =
		program_.native_lowering &&
		call.direct != NULL &&
		!call.virtual_call &&
		call.callee_type->variadic &&
		call.arg_types.size() == call.args.size();
	if (call.direct == NULL || call.virtual_call || direct_variadic_signature)
	{
		out << " as (";
		if (direct_variadic_signature)
		{
			for (size_t i = 0; i < call.arg_types.size(); ++i)
			{
				if (i != 0)
					out << ", ";
				out << "%arg" << i << " : "
				    << lowir_parameter(call.arg_types[i]);
			}
		}
		else
		{
			for (size_t i = 0; i < call.callee_type->parameters.size(); ++i)
			{
				if (i != 0)
					out << ", ";
				out << "%arg" << i << " : "
				    << lowir_parameter(call.callee_type->parameters[i]);
			}
			size_t hidden = 0;
			bool member_this_param =
				call.direct != NULL &&
				call.direct->owner != NULL &&
				call.direct->owner->kind == ScopeKind::Class &&
				!call.direct->is_static_member &&
				!call.callee_type->parameters.empty();
			for (size_t i = member_this_param ? 1 : 0;
			     i < call.callee_type->parameters.size();
			     ++i)
			{
				vector<TypePtr> vbases = call.direct != NULL
					? program_.hidden_virtual_bases_for_function_parameter(
						call.direct, i, call.callee_type->parameters[i])
					: hidden_virtual_bases_for_parameter(
						call.callee_type->parameters[i]);
				for (size_t v = 0; v < vbases.size(); ++v)
				{
					if (hidden != 0 || !call.callee_type->parameters.empty())
						out << ", ";
					out << "%__pvbptr" << hidden++ << " : ptr";
				}
			}
			if (member_this_param &&
			    call.direct != NULL &&
			    !is_class_constructor_binding(call.direct) &&
			    !is_class_destructor_binding(call.direct))
			{
				vector<TypePtr> vbases = call.direct->is_virtual
					? program_.hidden_virtual_bases_for_function_parameter(
						call.direct, 0, call.callee_type->parameters[0])
					: hidden_virtual_bases_for_record(
						class_record_for_member(call.direct));
				for (size_t v = 0; v < vbases.size(); ++v)
				{
					if (hidden != 0 ||
					    !call.callee_type->parameters.empty() ||
					    v != 0)
						out << ", ";
					out << "%__vbptr" << v << " : ptr";
				}
			}
		}
		out << ") -> " << call.ret;
		if (direct_variadic_signature)
			out << " [arity=variadic]";
	}
	call.call_text = out.str();
	call.cleanup_temps_in_call =
		call_binding_has_template_cleanup_context(call.direct) ||
		(call.direct != NULL &&
		 (call.direct->name == "operator=" ||
		  is_class_constructor_binding(call.direct)));
}

Value FunctionLowerer::scalar_call_result_for_store(
	const CallEmissionState& call,
	const string& loaded)
{
	TypePtr source = call.callee_type->base;
	Value value(call.ret, loaded);
	if (is_reference(source))
	{
		TypePtr object = object_type(source);
		while (is_reference(object))
			object = object_type(object);
		string deref = fresh_temp();
		instr(deref + " = load " + scalar_lowir_type(object) + " " +
		      loaded);
		source = object;
		value = Value(scalar_lowir_type(object), deref);
	}
	return convert_value(value, source, call_result_store_type_);
}

bool FunctionLowerer::emit_protected_setup_scalar_call(
	CallEmissionState& call,
	Value& out)
{
	if (!call.protected_setup)
		return false;
		bool spill_result =
			call.ret != "void" && call.ret.compare(0, 4, "obj<") != 0;
		bool record_result = call.ret.compare(0, 4, "obj<") == 0;
		bool consume_record_store =
			record_result && !call_result_store_addr_.empty() &&
			call_result_store_type_.get() != NULL &&
			call_result_store_expr_ == call.expr;
		bool consume_store =
			spill_result &&
			!call_result_store_slot_.empty() &&
			call_result_store_type_.get() != NULL &&
			call_result_store_expr_ == call.expr &&
			call.callee_type.get() != NULL &&
			call.callee_type->kind == TypeKind::Function &&
			call.callee_type->base.get() != NULL;
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
			Value stored = scalar_call_result_for_store(call, loaded);
			instr("store " + scalar_lowir_type(call_result_store_type_) +
			      " " + stored.text + ", $" + call_result_store_slot_);
			call_result_store_consumed_ = true;
		}
		else if (consume_record_store)
		{
			instr("copyobj " + to_string(pa11::type_size(call_result_store_type_)) +
			      "x" + to_string(pa11::type_align(call_result_store_type_)) +
			      " " + call.tmp + ", " + call_result_store_addr_);
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
			active_unwind_cleanup_depth_ = cleanups_.size();
			start_block(call.protected_dispatch);
		emit_active_catch_clauses();
		if (program_.native_lowering || !active_catches_.empty())
			instr("eh_cleanup");
		if (!call.temp_cleanups.empty())
		emit_temporary_cleanups(call.temp_cleanups);
	emit_unwind_cleanups();
	terminate_unwind_or_active_catch();
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
	bool consume_logical =
		spill_result &&
		!logical_call_result_slot_.empty() &&
		logical_call_result_expr_ == call.expr;
	bool consume_store =
		spill_result &&
		!call_result_store_slot_.empty() &&
		call_result_store_type_.get() != NULL &&
		call_result_store_expr_ == call.expr &&
		call.callee_type.get() != NULL &&
		call.callee_type->kind == TypeKind::Function &&
		call.callee_type->base.get() != NULL;
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
	bool cleanup_only =
		call_temp_cleanup_region_is_cleanup_only(call);
	if (!call.temp_cleanup_region_open)
	{
		instr((cleanup_only ? "eh_cleanup ^" : "eh_try ^") + dispatch);
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
		Value stored = scalar_call_result_for_store(call, loaded);
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
	if (!cleanup_only)
	{
		emit_active_catch_clauses();
		if (program_.native_lowering || !active_catches_.empty())
			instr("eh_cleanup");
	}
		emit_temporary_cleanups(call.temp_cleanups);
	emit_unwind_cleanups();
	if (cleanup_only)
		terminate("resume");
	else
		terminate_unwind_or_active_catch();
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
	    !has_active_call_protection_cleanups())
		return false;
		bool spill_result =
			call.ret != "void" && call.ret.compare(0, 4, "obj<") != 0;
		bool record_result = call.ret.compare(0, 4, "obj<") == 0;
		bool consume_record_store =
			record_result && !call_result_store_addr_.empty() &&
			call_result_store_type_.get() != NULL &&
			call_result_store_expr_ == call.expr;
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
		if (spill_result &&
		    !call_result_store_slot_.empty() &&
		    call_result_store_type_.get() != NULL &&
		    call_result_store_expr_ == call.expr &&
		    call.callee_type.get() != NULL &&
		    call.callee_type->kind == TypeKind::Function &&
		    call.callee_type->base.get() != NULL)
		{
			Value stored = scalar_call_result_for_store(call, loaded);
			instr("store " + scalar_lowir_type(call_result_store_type_) + " " +
			      stored.text + ", $" + call_result_store_slot_);
			call_result_store_consumed_ = true;
		}
		else if (consume_record_store)
		{
			instr("copyobj " + to_string(pa11::type_size(call_result_store_type_)) +
			      "x" + to_string(pa11::type_align(call_result_store_type_)) +
			      " " + call.tmp + ", " + call_result_store_addr_);
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
			active_unwind_cleanup_depth_ = cleanups_.size();
			start_block(dispatch);
		emit_active_catch_clauses();
		if (program_.native_lowering || !active_catches_.empty())
			instr("eh_cleanup");
		emit_unwind_cleanups();
	terminate_unwind_or_active_catch();
	start_block(end);
	out = spill_result ? Value(call.ret, loaded) : Value(call.ret, call.tmp);
	return true;
}

bool FunctionLowerer::emit_hosted_vector_bool_insert_aux(
	CallEmissionState& call)
{
	if (!hosted_vector_bool_insert_aux_binding(call.direct) ||
	    call.args.size() < 3)
		return false;
	return emit_packed_bit_insert_aux(call);
}

bool FunctionLowerer::emit_packed_bit_insert_aux(CallEmissionState& call)
{
	if (program_.declared_functions.insert("operator_new").second)
		program_.declares.push_back(
			"declare function @operator_new(%arg0 : i64) -> ptr "
			"[binding=strong, object=" +
			string(program_.native_lowering
			       ? "_Znwm" : "cppgm_builtin_operator_new") + "]");
	string size_tmp = fresh_temp();
	instr(size_tmp + " = convert sext i64 i32 8");
	string word = fresh_temp();
	instr(word + " = call ptr @operator_new(" + size_tmp + ")");
	string bit = fresh_temp();
	instr(bit + " = convert zext i64 u8 " + call.args[2]);
	instr("store i64 " + bit + ", " + word);
	const string& object = call.args[0];
	string start_offset = fresh_temp();
	instr(start_offset + " = index i8 [projection=field] " +
	      object + ", 8");
	instr("store u32 0, " + start_offset);
	string finish_ptr = fresh_temp();
	instr(finish_ptr + " = index i8 [projection=field] " +
	      object + ", 16");
	string finish_offset = fresh_temp();
	instr(finish_offset + " = index i8 [projection=field] " +
	      object + ", 24");
	string end_storage = fresh_temp();
	instr(end_storage + " = index i8 " + word + ", 8");
	string end_storage_field = fresh_temp();
	instr(end_storage_field + " = index i8 [projection=field] " +
	      object + ", 32");
	instr("store ptr " + word + ", " + object);
	instr("store ptr " + word + ", " + finish_ptr);
	instr("store u32 1, " + finish_offset);
	instr("store ptr " + end_storage + ", " + end_storage_field);
	if (call.protected_setup)
	{
		--eh_try_depth_;
		instr("eh_end");
		if (call.protected_define_dispatch)
		{
			string end = fresh_block("call_unwind_end");
			terminate("jump ^" + end);
			active_unwind_dispatch_ = call.protected_dispatch;
			active_unwind_cleanup_depth_ = cleanups_.size();
			start_block(call.protected_dispatch);
			emit_active_catch_clauses();
			if (program_.native_lowering || !active_catches_.empty())
				instr("eh_cleanup");
			if (!call.temp_cleanups.empty())
				emit_temporary_cleanups(call.temp_cleanups);
			emit_unwind_cleanups();
			terminate_unwind_or_active_catch();
			start_block(end);
		}
		for (size_t i = 0; i < call.temp_cleanups.size(); ++i)
			add_pending_temp_cleanup(call.temp_cleanups[i].first,
			                         call.temp_cleanups[i].second);
		return true;
	}
	if (call.temp_cleanup_region_open)
	{
		bool cleanup_only =
			call_temp_cleanup_region_is_cleanup_only(call);
		--eh_try_depth_;
		instr("eh_end");
		terminate("jump ^" + call.temp_cleanup_end);
		start_block(call.temp_cleanup_dispatch);
		if (!cleanup_only)
		{
			emit_active_catch_clauses();
			if (program_.native_lowering || !active_catches_.empty())
				instr("eh_cleanup");
		}
		emit_temporary_cleanups(call.temp_cleanups);
		emit_unwind_cleanups();
		if (cleanup_only)
			terminate("resume");
		else
			terminate_unwind_or_active_catch();
		start_block(call.temp_cleanup_end);
		for (size_t i = 0; i < call.temp_cleanups.size(); ++i)
			add_pending_temp_cleanup(call.temp_cleanups[i].first,
			                         call.temp_cleanups[i].second);
		return true;
	}
	for (size_t i = 0; i < call.temp_cleanups.size(); ++i)
		add_pending_temp_cleanup(call.temp_cleanups[i].first,
		                         call.temp_cleanups[i].second);
	return true;
}

bool FunctionLowerer::emit_hosted_vector_range_insert(CallEmissionState& call,
                                                      Value& out)
{
	TypePtr element;
	if (!hosted_vector_range_insert_binding(call.direct, element) ||
	    call.args.size() < 4 ||
	    call.direct->type.get() == NULL ||
	    call.direct->type->kind != TypeKind::Function)
		return false;
	TypePtr position_iterator;
	TypePtr position_container;
	TypePtr first_iterator;
	TypePtr first_container;
	TypePtr last_iterator;
	TypePtr last_container;
	if (!hosted_normal_iterator_record(call.direct->type->parameters[1],
	                                   position_iterator,
	                                   position_container) ||
	    !hosted_normal_iterator_record(call.direct->type->parameters[2],
	                                   first_iterator,
	                                   first_container) ||
	    !hosted_normal_iterator_record(call.direct->type->parameters[3],
	                                   last_iterator,
	                                   last_container) ||
	    !pa11::same_type(first_container, last_container))
		return false;
	return emit_contiguous_range_insert(call, out);
}

void FunctionLowerer::emit_contiguous_insert_fit(const string& position,
                                                 const string& first,
                                                 const string& tail_bytes,
                                                 const string& insert_bytes,
                                                 const string& new_finish,
                                                 const string& finish_addr,
                                                 const string& result_slot,
                                                 const string& done_block)
{
	string tail_dest = fresh_temp();
	instr(tail_dest + " = index i8 " + position + ", " + insert_bytes);
	string ignored_tail = fresh_temp();
	instr(ignored_tail + " = call ptr @__builtin_memmove(" + tail_dest +
	      ", " + position + ", " + tail_bytes + ")");
	string ignored_insert = fresh_temp();
	instr(ignored_insert + " = call ptr @__builtin_memmove(" + position +
	      ", " + first + ", " + insert_bytes + ")");
	instr("store ptr " + new_finish + ", " + finish_addr);
	instr("store ptr " + position + ", $" + result_slot);
	terminate("jump ^" + done_block);
}

void FunctionLowerer::emit_contiguous_insert_grow(
	const string& object,
	const string& start,
	const string& finish,
	const string& position,
	const string& first,
	const string& insert_bytes,
	const string& tail_bytes,
	const string& end_storage_addr,
	const string& finish_addr,
	const string& result_slot,
	const string& done_block)
{
	string old_size_bytes = fresh_temp();
	instr(old_size_bytes + " = binary sub ptr " + finish + ", " + start);
	string prefix_bytes = fresh_temp();
	instr(prefix_bytes + " = binary sub ptr " + position + ", " + start);
	string new_size_bytes = fresh_temp();
	instr(new_size_bytes + " = binary add i64 " + old_size_bytes + ", " +
	      insert_bytes);
	string doubled_old = fresh_temp();
	instr(doubled_old + " = binary mul i64 " + old_size_bytes + ", 2");
	string grow_to_exact = fresh_temp();
	instr(grow_to_exact + " = cmp ult i64 " + doubled_old + ", " +
	      new_size_bytes);
	string exact_block = fresh_block("range_insert_exact");
	string doubled_block = fresh_block("range_insert_doubled");
	string alloc_block = fresh_block("range_insert_alloc");
	string alloc_slot = fresh_aux_slot("insert_alloc_bytes", "i64");
	terminate("branch " + grow_to_exact + ", ^" + exact_block + ", ^" +
	          doubled_block);
	start_block(exact_block);
	instr("store i64 " + new_size_bytes + ", $" + alloc_slot);
	terminate("jump ^" + alloc_block);
	start_block(doubled_block);
	instr("store i64 " + doubled_old + ", $" + alloc_slot);
	terminate("jump ^" + alloc_block);
	start_block(alloc_block);
	string alloc_bytes = fresh_temp();
	instr(alloc_bytes + " = load i64 $" + alloc_slot);
	string storage = fresh_temp();
	instr(storage + " = call ptr @operator_new(" + alloc_bytes + ")");
	string ignored_prefix = fresh_temp();
	instr(ignored_prefix + " = call ptr @__builtin_memmove(" + storage +
	      ", " + start + ", " + prefix_bytes + ")");
	string insert_dest = fresh_temp();
	instr(insert_dest + " = index i8 " + storage + ", " + prefix_bytes);
	string ignored_new = fresh_temp();
	instr(ignored_new + " = call ptr @__builtin_memmove(" + insert_dest +
	      ", " + first + ", " + insert_bytes + ")");
	string new_tail_dest = fresh_temp();
	instr(new_tail_dest + " = index i8 " + insert_dest + ", " +
	      insert_bytes);
	string ignored_new_tail = fresh_temp();
	instr(ignored_new_tail + " = call ptr @__builtin_memmove(" +
	      new_tail_dest + ", " + position + ", " + tail_bytes + ")");
	string grown_finish = fresh_temp();
	instr(grown_finish + " = index i8 " + storage + ", " +
	      new_size_bytes);
	string grown_end_storage = fresh_temp();
	instr(grown_end_storage + " = index i8 " + storage + ", " + alloc_bytes);
	instr("store ptr " + storage + ", " + object);
	instr("store ptr " + grown_finish + ", " + finish_addr);
	instr("store ptr " + grown_end_storage + ", " + end_storage_addr);
	string has_old_storage = fresh_temp();
	instr(has_old_storage + " = cmp ne ptr " + start + ", 0");
	string delete_block = fresh_block("range_insert_delete_old");
	string skip_delete_block = fresh_block("range_insert_skip_delete");
	terminate("branch " + has_old_storage + ", ^" + delete_block + ", ^" +
	          skip_delete_block);
	start_block(delete_block);
	instr("call void @operator_delete(" + start + ")");
	terminate("jump ^" + skip_delete_block);
	start_block(skip_delete_block);
	instr("store ptr " + insert_dest + ", $" + result_slot);
	terminate("jump ^" + done_block);
}

bool FunctionLowerer::emit_contiguous_range_insert(CallEmissionState& call,
                                                   Value& out)
{
	declare_hosted_memmove(program_);
	declare_hosted_operator_new(program_);
	declare_hosted_operator_delete(program_);
	const string& object = call.args[0];
	string position = fresh_temp();
	instr(position + " = load ptr " + call.args[1]);
	string first = fresh_temp();
	instr(first + " = load ptr " + call.args[2]);
	string last = fresh_temp();
	instr(last + " = load ptr " + call.args[3]);
	string finish_addr = fresh_temp();
	instr(finish_addr + " = index i8 [projection=field] " +
	      object + ", 8");
	string end_storage_addr = fresh_temp();
	instr(end_storage_addr + " = index i8 [projection=field] " +
	      object + ", 16");
	string start = fresh_temp();
	instr(start + " = load ptr " + object);
	string finish = fresh_temp();
	instr(finish + " = load ptr " + finish_addr);
	string end_storage = fresh_temp();
	instr(end_storage + " = load ptr " + end_storage_addr);
	string insert_bytes = fresh_temp();
	instr(insert_bytes + " = binary sub ptr " + last + ", " + first);
	string tail_bytes = fresh_temp();
	instr(tail_bytes + " = binary sub ptr " + finish + ", " + position);
	string new_finish = fresh_temp();
	instr(new_finish + " = index i8 " + finish + ", " + insert_bytes);
	string available_bytes = fresh_temp();
	instr(available_bytes + " = binary sub ptr " + end_storage + ", " +
	      finish);
	string needs_grow = fresh_temp();
	instr(needs_grow + " = cmp ult i64 " + available_bytes + ", " +
	      insert_bytes);
	string result_slot = fresh_aux_slot("insert_result", "ptr");
	string grow_block = fresh_block("range_insert_grow");
	string fit_block = fresh_block("range_insert_fit");
	string done_block = fresh_block("range_insert_done");
	terminate("branch " + needs_grow + ", ^" + grow_block + ", ^" +
	          fit_block);
	start_block(fit_block);
	emit_contiguous_insert_fit(position,
	                           first,
	                           tail_bytes,
	                           insert_bytes,
	                           new_finish,
	                           finish_addr,
	                           result_slot,
	                           done_block);
	start_block(grow_block);
	emit_contiguous_insert_grow(object,
	                            start,
	                            finish,
	                            position,
	                            first,
	                            insert_bytes,
	                            tail_bytes,
	                            end_storage_addr,
	                            finish_addr,
	                            result_slot,
	                            done_block);
	start_block(done_block);
	string result_ptr = fresh_temp();
	instr(result_ptr + " = load ptr $" + result_slot);
	string ret_slot = fresh_aux_slot("insert_ret", call.ret);
	instr("store ptr " + result_ptr + ", $" + ret_slot);
	Value result(call.ret, "$" + ret_slot);
	if (call.protected_setup)
	{
		--eh_try_depth_;
		instr("eh_end");
		for (size_t i = 0; i < call.temp_cleanups.size(); ++i)
			add_pending_temp_cleanup(call.temp_cleanups[i].first,
			                         call.temp_cleanups[i].second);
		if (call.protected_define_dispatch)
		{
			string end = fresh_block("call_unwind_end");
			terminate("jump ^" + end);
			active_unwind_dispatch_ = call.protected_dispatch;
			active_unwind_cleanup_depth_ = cleanups_.size();
			start_block(call.protected_dispatch);
			emit_active_catch_clauses();
			if (program_.native_lowering || !active_catches_.empty())
				instr("eh_cleanup");
			if (!call.temp_cleanups.empty())
				emit_temporary_cleanups(call.temp_cleanups);
			emit_unwind_cleanups();
			terminate_unwind_or_active_catch();
			start_block(end);
		}
		out = result;
		return true;
	}
	for (size_t i = 0; i < call.temp_cleanups.size(); ++i)
		add_pending_temp_cleanup(call.temp_cleanups[i].first,
		                         call.temp_cleanups[i].second);
	out = result;
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

Value FunctionLowerer::emit_initializer_list_accessor_call(const Node& expr,
                                                           bool& handled)
{
	handled = false;
	Binding* binding = expr.direct_call;
	if (binding == NULL ||
	    (binding->name != "begin" &&
	     binding->name != "end" &&
	     binding->name != "size") ||
	    binding->type.get() == NULL ||
	    binding->type->kind != TypeKind::Function ||
	    binding->type->parameters.size() != 1 ||
	    expr.children.size() != 2)
		return Value();
	TypePtr record = class_record_for_member(binding);
	TypePtr element;
	if (!is_initializer_list_type(record, &element))
		return Value();
	Value this_value = emit_rvalue(expr.children[1]);
	if (this_value.type != "ptr")
		this_value = ensure_pointer(emit_lvalue_addr(expr.children[1]));
	string begin_addr = fresh_temp();
	instr(begin_addr + " = index i8 [projection=field] " +
	      this_value.text + ", 0");
	if (binding->name == "size")
	{
		string size_addr = fresh_temp();
		instr(size_addr + " = index i8 [projection=field] " +
		      this_value.text + ", 8");
		string size_value = fresh_temp();
		instr(size_value + " = load i64 " + size_addr);
		handled = true;
		return Value("i64", size_value);
	}
	string begin_value = fresh_temp();
	instr(begin_value + " = load ptr " + begin_addr);
	if (binding->name == "begin")
	{
		handled = true;
		return Value("ptr", begin_value);
	}
	string size_addr = fresh_temp();
	instr(size_addr + " = index i8 [projection=field] " +
	      this_value.text + ", 8");
	string size_value = fresh_temp();
	instr(size_value + " = load i64 " + size_addr);
	string byte_count = fresh_temp();
	instr(byte_count + " = binary mul i64 " + size_value + ", " +
	      to_string(pa11::type_size(element)));
	string end_value = fresh_temp();
	instr(end_value + " = index i8 " + begin_value + ", " + byte_count);
	handled = true;
	return Value("ptr", end_value);
}

Value FunctionLowerer::emit_hosted_vector_accessor_call(const Node& expr,
                                                        bool& handled)
{
	handled = false;
	Binding* binding = expr.direct_call;
	if (binding == NULL ||
	    (binding->name != "size" &&
	     binding->name != "empty" &&
	     binding->name != "operator[]") ||
	    binding->type.get() == NULL ||
	    binding->type->kind != TypeKind::Function)
		return Value();
	const bool index_call = binding->name == "operator[]";
	if ((!index_call && (binding->type->parameters.size() != 1 ||
	                     expr.children.size() != 2)) ||
	    (index_call && (binding->type->parameters.size() != 2 ||
	                    expr.children.size() != 3)))
		return Value();
	TypePtr element;
	if (!hosted_vector_record(class_record_for_member(binding), element))
		return Value();
	TypePtr bare_element = pa11::strip_cv(element);
	if (bare_element.get() == NULL ||
	    (bare_element->kind == TypeKind::Fundamental &&
	     bare_element->fundamental == FT_BOOL))
		return Value();
	Value this_value = emit_rvalue(expr.children[1]);
	if (this_value.type != "ptr")
		this_value = ensure_pointer(emit_lvalue_addr(expr.children[1]));
	string start_addr = fresh_temp();
	instr(start_addr + " = index i8 [projection=field] " +
	      this_value.text + ", 0");
	string start = fresh_temp();
	instr(start + " = load ptr " + start_addr);
	if (index_call)
	{
		Value index = emit_rvalue(expr.children[2]);
		if (index.type != "i64")
			index = convert_value(index,
			                      expr.children[2].type,
			                      pa11::make_fundamental(
				                      FT_UNSIGNED_LONG_INT));
		string offset = fresh_temp();
		instr(offset + " = binary mul i64 " + index.text + ", " +
		      to_string(pa11::type_size(bare_element)));
		string elem = fresh_temp();
		instr(elem + " = index i8 [projection=array_element] " +
		      start + ", " + offset);
		handled = true;
		return Value("ptr", elem);
	}
	string finish_addr = fresh_temp();
	instr(finish_addr + " = index i8 [projection=field] " +
	      this_value.text + ", 8");
	string finish = fresh_temp();
	instr(finish + " = load ptr " + finish_addr);
	string bytes = fresh_temp();
	instr(bytes + " = binary sub ptr " + finish + ", " + start);
	string count = fresh_temp();
	instr(count + " = binary div i64 " + bytes + ", " +
	      to_string(pa11::type_size(bare_element)));
	handled = true;
	if (binding->name == "size")
		return Value("i64", count);
	string empty = fresh_temp();
	instr(empty + " = cmp eq i64 " + count + ", 0");
	return Value("u8", empty);
}

Value FunctionLowerer::emit_call(const Node& expr)
{
	if (program_.native_lowering)
	{
		bool initializer_list_accessor = false;
		Value accessor =
			emit_initializer_list_accessor_call(expr, initializer_list_accessor);
		if (initializer_list_accessor)
			return accessor;
		bool vector_accessor = false;
		accessor =
			emit_hosted_vector_accessor_call(expr, vector_accessor);
		if (vector_accessor)
			return accessor;
	}

	if (program_.native_lowering &&
	    hosted_std_forwarding_call_binding(expr) != NULL &&
	    expr.children.size() == 2)
		return emit_rvalue(expr.children[1]);

	CallEmissionState call;
	call.expr = &expr;
	init_call_target(expr, call);
	preallocate_call_result_slot(expr, call);
	prepare_call_setup_protection(expr, call);
	lower_call_arguments(expr, call);
	append_hidden_call_arguments(expr, call);
	finish_setup_only_protection(call);
	maybe_open_call_temp_cleanup_region(call);
	resolve_call_callee(expr, call);
	Value out;
	if (emit_hosted_vector_range_insert(call, out))
		return out;
	if (emit_record_return_call(call, out))
		return out;
	if (emit_hosted_vector_bool_insert_aux(call))
		return Value("void", "");
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
