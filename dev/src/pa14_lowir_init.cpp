#include "pa14_lowir_internal.h"

namespace pa14 {
namespace internal {

Binding* find_constructor(TypePtr type, size_t arg_count)
{
	TypePtr bare = pa11::strip_cv(type);
	if (bare->kind != TypeKind::Record || bare->scope == NULL)
		return NULL;
	map<string, vector<Binding*> >::const_iterator found =
		bare->scope->members.find(bare->scope->name);
	if (found == bare->scope->members.end())
		return NULL;
	for (size_t i = 0; i < found->second.size(); ++i)
	{
		Binding* binding = found->second[i];
		if (binding->kind == BindingKind::Function &&
		    binding->type->kind == TypeKind::Function &&
		    binding->type->parameters.size() == arg_count + 1)
			return binding;
	}
	return NULL;
}

const Node* record_prvalue_child_for_xvalue(const Node& arg)
{
	if (arg.category != ValueCategory::XValue || arg.children.empty())
		return NULL;
	if (!starts_with(arg.line, "cast-expression"))
		return NULL;
	const Node& child = arg.children[0];
	if (child.category == ValueCategory::LValue ||
	    child.category == ValueCategory::XValue)
		return NULL;
	if (pa11::strip_cv(object_type(child.type))->kind != TypeKind::Record)
		return NULL;
	return &child;
}

Binding* find_any_copy_move_constructor(TypePtr type, bool move)
{
	TypePtr bare = pa11::strip_cv(type);
	if (bare->kind != TypeKind::Record || bare->scope == NULL)
		return NULL;
	map<string, vector<Binding*> >::const_iterator found =
		bare->scope->members.find(bare->scope->name);
	if (found == bare->scope->members.end())
		return NULL;
	for (size_t i = 0; i < found->second.size(); ++i)
	{
		Binding* binding = found->second[i];
		if (binding->kind != BindingKind::Function ||
		    binding->type->kind != TypeKind::Function ||
		    binding->type->parameters.size() != 2)
			continue;
		TypePtr param = binding->type->parameters[1];
		if (move)
		{
			if (param->kind != TypeKind::RValueReference)
				continue;
		}
		else if (param->kind != TypeKind::LValueReference)
			continue;
		TypePtr param_record = pa11::strip_cv(param->base);
		if (param_record->kind == TypeKind::Record &&
		    pa11::same_type(param_record, bare))
			return binding;
	}
	return NULL;
}

bool type_needs_defaulted_copy_move_helper(TypePtr type, bool move);

bool record_needs_defaulted_copy_move_helper(TypePtr type, bool move)
{
	TypePtr bare = pa11::strip_cv(type);
	if (bare->kind != TypeKind::Record)
		return false;
	Binding* exact = find_any_copy_move_constructor(bare, move);
	if (exact != NULL && !exact->is_defaulted)
		return true;
	if (exact == NULL && move)
	{
		Binding* copy = find_any_copy_move_constructor(bare, false);
		if (copy != NULL && !copy->is_defaulted)
			return true;
	}
	pa11::layout_record_type(bare);
	if (bare->base.get() != NULL &&
	    type_needs_defaulted_copy_move_helper(bare->base, move))
		return true;
	for (size_t i = 0; i < bare->fields.size(); ++i)
		if (type_needs_defaulted_copy_move_helper(bare->fields[i]->type, move))
			return true;
	return false;
}

bool type_needs_defaulted_copy_move_helper(TypePtr type, bool move)
{
	TypePtr bare = pa11::strip_cv(type);
	if (bare->kind == TypeKind::Array)
		return type_needs_defaulted_copy_move_helper(bare->base, move);
	if (bare->kind != TypeKind::Record)
		return false;
	return record_needs_defaulted_copy_move_helper(bare, move);
}

bool defaulted_copy_move_constructor_needs_helper(Binding* binding, TypePtr type)
{
	if (binding == NULL ||
	    binding->type->kind != TypeKind::Function ||
	    binding->type->parameters.size() != 2 ||
	    !is_reference(binding->type->parameters[1]))
		return false;
	return type_needs_defaulted_copy_move_helper(
		type,
		binding->type->parameters[1]->kind == TypeKind::RValueReference);
}

Binding* find_copy_move_constructor(TypePtr type, bool move)
{
	TypePtr bare = pa11::strip_cv(type);
	if (bare->kind != TypeKind::Record || bare->scope == NULL)
		return NULL;
	map<string, vector<Binding*> >::const_iterator found =
		bare->scope->members.find(bare->scope->name);
	if (found == bare->scope->members.end())
		return NULL;
	for (size_t i = 0; i < found->second.size(); ++i)
	{
		Binding* binding = found->second[i];
		if (binding->kind != BindingKind::Function ||
		    binding->type->kind != TypeKind::Function ||
		    binding->type->parameters.size() != 2)
			continue;
		if (binding->is_defaulted &&
		    !defaulted_copy_move_constructor_needs_helper(binding, bare))
			continue;
		TypePtr param = binding->type->parameters[1];
		if (move)
		{
			if (param->kind != TypeKind::RValueReference)
				continue;
		}
		else if (param->kind != TypeKind::LValueReference)
			continue;
		TypePtr param_record = pa11::strip_cv(param->base);
		if (param_record->kind == TypeKind::Record &&
		    pa11::same_type(param_record, bare))
			return binding;
	}
	return NULL;
}

bool inline_defaulted_copy_move_storage_constructor(Binding* binding,
                                                   TypePtr type,
                                                   const Node& init)
{
	if (binding == NULL ||
	    !binding->is_defaulted ||
	    !binding->is_inline_definition ||
	    binding->type->kind != TypeKind::Function ||
	    binding->type->parameters.size() != 2 ||
	    !is_reference(binding->type->parameters[1]) ||
	    init.children.size() != 1 ||
	    defaulted_copy_move_constructor_needs_helper(binding, type) ||
	    !record_has_storage_copy(type))
		return false;
	TypePtr param_record = pa11::strip_cv(binding->type->parameters[1]->base);
	TypePtr target_record = pa11::strip_cv(type);
	return param_record->kind == TypeKind::Record &&
	       target_record->kind == TypeKind::Record &&
	       pa11::same_type(param_record, target_record);
}

bool same_record_copy_move_constructor(Binding* binding,
                                       TypePtr type,
                                       const Node& init)
{
	if (binding == NULL ||
	    binding->type->kind != TypeKind::Function ||
	    binding->type->parameters.size() != 2 ||
	    !is_reference(binding->type->parameters[1]) ||
	    init.children.size() != 1)
		return false;
	TypePtr param_record = pa11::strip_cv(binding->type->parameters[1]->base);
	TypePtr target_record = pa11::strip_cv(type);
	return param_record->kind == TypeKind::Record &&
	       target_record->kind == TypeKind::Record &&
	       pa11::same_type(param_record, target_record);
}

Binding* find_destructor(TypePtr type)
{
	TypePtr bare = pa11::strip_cv(type);
	if (bare->kind != TypeKind::Record || bare->scope == NULL)
		return NULL;
	string name = "~" + bare->scope->name;
	map<string, vector<Binding*> >::const_iterator found =
		bare->scope->members.find(name);
	if (found == bare->scope->members.end())
		return NULL;
	for (size_t i = 0; i < found->second.size(); ++i)
	{
		Binding* binding = found->second[i];
		if (binding->kind == BindingKind::Function &&
		    binding->type->kind == TypeKind::Function)
			return binding;
	}
	return NULL;
}

bool type_needs_destructor(TypePtr type)
{
	TypePtr bare = pa11::strip_cv(type);
	if (bare->kind == TypeKind::Array)
		return type_needs_destructor(bare->base);
	if (bare->kind != TypeKind::Record)
		return false;
	Binding* dtor = find_destructor(bare);
	if (dtor != NULL && !dtor->is_noop_destructor)
		return true;
	pa11::layout_record_type(bare);
	if (bare->base.get() != NULL && type_needs_destructor(bare->base))
		return true;
	for (size_t i = 0; i < bare->fields.size(); ++i)
		if (type_needs_destructor(bare->fields[i]->type))
			return true;
	return false;
}

bool type_contains_record(TypePtr type)
{
	TypePtr bare = pa11::strip_cv(type);
	if (bare->kind == TypeKind::Record)
		return true;
	if (bare->kind == TypeKind::Array)
		return type_contains_record(bare->base);
	return false;
}

bool default_init_no_op(TypePtr type)
{
	TypePtr bare = pa11::strip_cv(type);
	if (bare->kind == TypeKind::Array)
		return default_init_no_op(bare->base);
	if (bare->kind != TypeKind::Record)
		return false;
	Binding* ctor = find_constructor(bare, 0);
	if (ctor != NULL && !ctor->is_generated_default_constructor)
		return false;
	pa11::layout_record_type(bare);
	if (bare->base.get() != NULL && !default_init_no_op(bare->base))
		return false;
	for (size_t i = 0; i < bare->fields.size(); ++i)
		if (!default_init_no_op(bare->fields[i]->type))
			return false;
	return true;
}

bool no_op_generated_default_constructor(Binding* ctor, TypePtr type)
{
	if (ctor == NULL || !ctor->is_generated_default_constructor)
		return false;
	TypePtr bare = pa11::strip_cv(type);
	if (bare->kind == TypeKind::Record && bare->is_polymorphic)
		return false;
	return ctor->unwind_no || default_init_no_op(type);
}

bool has_inline_constructor(TypePtr type)
{
	TypePtr bare = pa11::strip_cv(type);
	if (bare->kind != TypeKind::Record || bare->scope == NULL)
		return false;
	map<string, vector<Binding*> >::const_iterator found =
		bare->scope->members.find(bare->scope->name);
	if (found == bare->scope->members.end())
		return false;
	for (size_t i = 0; i < found->second.size(); ++i)
		if (found->second[i]->kind == BindingKind::Function &&
		    found->second[i]->type->kind == TypeKind::Function &&
		    found->second[i]->is_inline_definition)
			return true;
	return false;
}

bool aggregate_blocking_constructor(Binding* binding)
{
	if (binding->kind != BindingKind::Function ||
	    binding->type->kind != TypeKind::Function)
		return false;
	if (binding->is_generated_default_constructor ||
	    binding->is_generated_aggregate_constructor ||
	    binding->is_generated_copy_move_constructor)
		return false;
	if (binding->is_defaulted && binding->type->parameters.size() == 1)
		return false;
	return true;
}

bool record_has_aggregate_blocking_constructor(TypePtr type)
{
	TypePtr bare = pa11::strip_cv(type);
	if (bare->kind != TypeKind::Record || bare->scope == NULL)
		return false;
	map<string, vector<Binding*> >::const_iterator found =
		bare->scope->members.find(bare->scope->name);
	if (found == bare->scope->members.end())
		return false;
	for (size_t i = 0; i < found->second.size(); ++i)
		if (aggregate_blocking_constructor(found->second[i]))
			return true;
	return false;
}

bool record_has_nonpublic_field(TypePtr type)
{
	TypePtr bare = pa11::strip_cv(type);
	if (bare->kind != TypeKind::Record)
		return false;
	pa11::layout_record_type(bare);
	for (size_t i = 0; i < bare->fields.size(); ++i)
		if (bare->fields[i]->is_private ||
		    bare->fields[i]->is_protected_member)
			return true;
	return false;
}

bool record_has_real_inline_constructor(TypePtr type)
{
	TypePtr bare = pa11::strip_cv(type);
	if (bare->kind != TypeKind::Record || bare->scope == NULL)
		return false;
	map<string, vector<Binding*> >::const_iterator found =
		bare->scope->members.find(bare->scope->name);
	if (found == bare->scope->members.end())
		return false;
	for (size_t i = 0; i < found->second.size(); ++i)
		if (found->second[i]->kind == BindingKind::Function &&
		    found->second[i]->type->kind == TypeKind::Function &&
		    found->second[i]->is_inline_definition &&
		    aggregate_blocking_constructor(found->second[i]))
			return true;
	return false;
}

bool record_has_ordinary_member_function_for_aggregate(TypePtr type)
{
	TypePtr bare = pa11::strip_cv(type);
	if (bare->kind != TypeKind::Record || bare->scope == NULL)
		return false;
	for (map<string, vector<Binding*> >::const_iterator it =
	     bare->scope->members.begin();
	     it != bare->scope->members.end();
	     ++it)
	{
		if (it->first == bare->scope->name ||
		    it->first == "~" + bare->scope->name)
			continue;
		for (size_t i = 0; i < it->second.size(); ++i)
			if (it->second[i]->kind == BindingKind::Function)
				return true;
	}
	return false;
}

bool is_brace_elision_aggregate(TypePtr type)
{
	TypePtr bare = pa11::strip_cv(type);
	if (bare->kind == TypeKind::Array)
		return true;
	if (bare->kind != TypeKind::Record)
		return false;
	return !record_has_aggregate_blocking_constructor(type) &&
	       !record_has_nonpublic_field(type);
}

bool is_string_literal_node(const Node& node)
{
	return !node.token_text.empty() &&
	       node.token_text[node.token_text.size() - 1] == '"';
}

bool zero_init_has_store(TypePtr type)
{
	TypePtr bare = pa11::strip_cv(type);
	if (bare->kind == TypeKind::Array)
		return !bare->unknown_bound && bare->bound != 0 &&
		       zero_init_has_store(bare->base);
	if (bare->kind != TypeKind::Record)
		return true;
	pa11::layout_record_type(bare);
	if (bare->base.get() != NULL && zero_init_has_store(bare->base))
		return true;
	for (size_t i = 0; i < bare->fields.size(); ++i)
		if (zero_init_has_store(bare->fields[i]->type))
			return true;
	return false;
}

bool type_has_reference_subobject(TypePtr type)
{
	TypePtr bare = pa11::strip_cv(type);
	if (bare->kind == TypeKind::Array)
		return type_has_reference_subobject(bare->base);
	if (bare->kind != TypeKind::Record)
		return false;
	pa11::layout_record_type(bare);
	if (bare->base.get() != NULL &&
	    type_has_reference_subobject(bare->base))
		return true;
	for (size_t i = 0; i < bare->fields.size(); ++i)
	{
		if (is_reference(bare->fields[i]->type) ||
		    type_has_reference_subobject(bare->fields[i]->type))
			return true;
	}
	return false;
}

bool record_has_user_assignment_operator(TypePtr type)
{
	TypePtr bare = pa11::strip_cv(type);
	if (bare->kind != TypeKind::Record || bare->scope == NULL)
		return false;
	map<string, vector<Binding*> >::const_iterator found =
		bare->scope->members.find("operator=");
	if (found == bare->scope->members.end())
		return false;
	for (size_t i = 0; i < found->second.size(); ++i)
		if (found->second[i]->kind == BindingKind::Function &&
		    !found->second[i]->is_generated_copy_move_assignment)
			return true;
	return false;
}

string zero_integer_type(uint64_t size)
{
	switch (size)
	{
	case 1: return "i8";
	case 2: return "i16";
	case 4: return "i32";
	case 8: return "i64";
	default: return "";
	}
}

bool same_record_initializer(const Node& init, TypePtr type)
{
	if (init.type.get() == NULL || type.get() == NULL)
		return false;
	TypePtr dst = pa11::strip_cv(type);
	TypePtr src = pa11::strip_cv(object_type(init.type));
	return dst->kind == TypeKind::Record &&
	       src->kind == TypeKind::Record &&
	       pa11::same_type(src, dst);
}

bool record_has_base(TypePtr source, TypePtr target)
{
	TypePtr dst = pa11::strip_cv(target);
	for (TypePtr cur = pa11::strip_cv(source);
	     cur.get() != NULL && cur->kind == TypeKind::Record;
	     cur = cur->base.get() != NULL ? pa11::strip_cv(cur->base) : TypePtr())
	{
		if (pa11::same_type(cur, dst))
			return true;
	}
	return false;
}

bool FunctionLowerer::lower_braced_variable_init(const Node& var, TypePtr type)
{
	TypePtr bare = pa11::strip_cv(type);
	Value direct_base;
	if (bare->kind == TypeKind::Array)
		direct_base = ensure_pointer(emit_lvalue_addr(var));
	shared_ptr<Value> cached_base(new Value(direct_base));
	function<Value()> addr_for = [this, &var, cached_base]() {
		if (cached_base->text.empty())
			*cached_base = ensure_pointer(emit_lvalue_addr(var));
		return *cached_base;
	};
	if (bare->kind == TypeKind::Array)
	{
		direct_base = *cached_base;
		lower_direct_array_init(direct_base, type, var.children[0]);
	}
	else
	{
		if (!record_has_real_inline_constructor(type) &&
		    !record_has_ordinary_member_function_for_aggregate(type) &&
		    var.children[0].direct_call == NULL)
		{
			ensure_pointer(emit_lvalue_addr(var));
			function<Value()> aggregate_addr_for = [this, &var]() {
				return ensure_pointer(emit_lvalue_addr(var));
			};
			lower_aggregate_init(aggregate_addr_for, type, var.children[0]);
			emit_pending_temp_cleanups();
			register_cleanup(var.binding, type);
			return true;
		}
		bool generated_aggregate_init =
			var.children[0].direct_call != NULL &&
			var.children[0].direct_call->is_generated_aggregate_constructor;
		Binding* init_ctor = var.children[0].direct_call;
		if (init_ctor == NULL)
			init_ctor = find_constructor(type, var.children[0].children.size());
		if (!generated_aggregate_init)
			generated_aggregate_init =
				init_ctor != NULL &&
				init_ctor->is_generated_aggregate_constructor;
		bool aggregate_storage_init =
			is_brace_elision_aggregate(type) || generated_aggregate_init;
		bool copy_move_init =
			same_record_copy_move_constructor(init_ctor, type, var.children[0]);
		bool const_zero_init =
			pa11::type_has_const(type) &&
			var.children[0].children.empty() &&
			zero_init_has_store(type);
		if (aggregate_storage_init &&
		    (!var.children[0].children.empty() || zero_init_has_store(type)))
			addr_for();
		if (aggregate_storage_init &&
		    !copy_move_init &&
		    (!pa11::type_has_const(type) || const_zero_init) &&
		    !type_has_reference_subobject(type) &&
		    !record_has_user_assignment_operator(type))
		{
			function<Value()> aggregate_addr_for = [this, &var]() {
				return ensure_pointer(emit_lvalue_addr(var));
			};
			lower_object_init(aggregate_addr_for, type, var.children[0]);
		}
		else
			lower_object_init(addr_for, type, var.children[0]);
	}
	emit_pending_temp_cleanups();
	register_cleanup(var.binding, type);
	return true;
}

void FunctionLowerer::lower_variable_decl(const Node& var)
{
	if (!starts_with(var.line, "variable ") || var.binding == NULL)
		return;
	string slot = return_slot_variables_.find(var.binding) ==
	              return_slot_variables_.end()
		? slot_for(var.binding) : string();
	if (var.children.empty())
	{
		TypePtr bare = pa11::strip_cv(var.binding->type);
		if (type_contains_record(var.binding->type))
		{
			if (bare->kind != TypeKind::Array)
				ensure_pointer(emit_lvalue_addr(var));
			function<Value()> addr_for = [this, &var]() {
				return ensure_pointer(emit_lvalue_addr(var));
			};
			lower_default_init(addr_for, var.binding->type);
			register_cleanup(var.binding, var.binding->type);
		}
		return;
	}
	TypePtr type = var.binding->type;
	if (starts_with(var.children[0].line, "constructor-action"))
	{
		Binding* ctor = !var.children[0].children.empty()
			? var.children[0].children[0].direct_call : NULL;
		if (no_op_generated_default_constructor(ctor, var.binding->type))
		{
			ensure_pointer(emit_lvalue_addr(var));
			emit_pending_temp_cleanups();
			register_cleanup(var.binding, var.binding->type);
			return;
		}
		if (!var.children[0].children.empty())
			emit_rvalue(var.children[0].children[0]);
		emit_pending_temp_cleanups();
		register_cleanup(var.binding, var.binding->type);
		return;
	}
	TypePtr bare = pa11::strip_cv(type);
	if ((bare->kind == TypeKind::Record || bare->kind == TypeKind::Array) &&
	    starts_with(var.children[0].line, "braced-init-list"))
	{
		lower_braced_variable_init(var, type);
		return;
	}
	if (bare->kind == TypeKind::Record)
	{
		Value base = ensure_pointer(emit_lvalue_addr(var));
		function<Value()> addr_for = [base]() {
			return base;
		};
		lower_object_init(addr_for, type, var.children[0]);
		emit_pending_temp_cleanups();
		register_cleanup(var.binding, type);
		return;
	}
	if (is_reference(type))
	{
		Value source = ensure_pointer(emit_lvalue_addr(var.children[0]));
		TypePtr from_ptr = pa11::make_pointer(object_type(var.children[0].type));
		TypePtr to_ptr = pa11::make_pointer(type->base);
		Value converted = convert_value(source, from_ptr, to_ptr);
		instr("store ptr " + converted.text + ", $" + slot);
	}
	else
	{
		if (starts_with(var.children[0].line, "call-expression"))
		{
			call_result_store_slot_ = slot;
			call_result_store_type_ = type;
			call_result_store_consumed_ = false;
		}
			Value init = emit_rvalue(var.children[0]);
			if (!call_result_store_consumed_)
			{
				TypePtr init_bare =
					pa11::strip_cv(strip_for_value(var.children[0].type));
				TypePtr target_bare = pa11::strip_cv(strip_for_value(type));
				bool literal_value = !init.text.empty() &&
				                     init.text[0] != '%' &&
				                     init.text[0] != '$' &&
				                     init.text[0] != '@';
				bool materialize_widening_literal =
					literal_value &&
					pa11::is_integral_or_bool_type(init_bare) &&
					pa11::is_integral_or_bool_type(target_bare) &&
					pa11::type_size(target_bare) > pa11::type_size(init_bare);
				init = convert_value(init,
				                     var.children[0].type,
				                     type,
				                     !materialize_widening_literal);
				instr("store " + scalar_lowir_type(type) + " " +
				      init.text + ", $" + slot);
			}
		call_result_store_slot_.clear();
		call_result_store_type_.reset();
		call_result_store_consumed_ = false;
	}
	emit_pending_temp_cleanups();
}

void FunctionLowerer::register_cleanup(Binding* binding, TypePtr type)
{
	if (cleanups_.empty() || binding == NULL)
		return;
	TypePtr bare = pa11::strip_cv(type);
	if (bare->kind != TypeKind::Record && bare->kind != TypeKind::Array)
		return;
	if (!type_needs_destructor(type))
		return;
	program_.ensure_eh_declarations();
	TypePtr cleanup_type = bare;
	while (cleanup_type->kind == TypeKind::Array)
		cleanup_type = pa11::strip_cv(cleanup_type->base);
	if (cleanup_type->kind == TypeKind::Record)
	{
		Binding* dtor = find_destructor(cleanup_type);
		if (dtor != NULL && !dtor->is_noop_destructor)
			program_.demand_inline_function(dtor);
	}
	cleanups_.back().push_back(Cleanup(binding, type));
}

void FunctionLowerer::emit_scope_cleanups(vector<Cleanup>& scope)
{
	for (size_t n = 0; n < scope.size(); ++n)
	{
		size_t i = scope.size() - 1 - n;
		Binding* binding = scope[i].binding;
		TypePtr type = scope[i].type;
		string cleanup_addr = scope[i].addr;
		function<Value()> addr_for = [this, binding, cleanup_addr]() {
			if (!cleanup_addr.empty())
				return Value("ptr", cleanup_addr);
			return ensure_pointer(Value("ptr", "$" + slot_for(binding)));
		};
		if (scope[i].force_destructor_call)
		{
			TypePtr bare = pa11::strip_cv(type);
			Binding* dtor = bare->kind == TypeKind::Record
				? find_destructor(bare) : NULL;
			if (dtor != NULL)
			{
				program_.demand_function_declaration(dtor);
				program_.demand_inline_function(dtor);
				Value target = addr_for();
				string arg = target.text;
				if (!arg.empty() && (arg[0] == '@' || arg[0] == '$'))
				{
					string tmp = fresh_temp();
					instr(tmp + " = addr " + arg);
					arg = tmp;
				}
				instr("call void @" + program_.symbol_for(dtor) +
				      "(" + arg + ")");
				continue;
			}
		}
		lower_scope_destructor_for_object(addr_for, type);
	}
}

void FunctionLowerer::emit_all_cleanups()
{
	for (size_t n = 0; n < cleanups_.size(); ++n)
	{
		size_t i = cleanups_.size() - 1 - n;
		emit_scope_cleanups(cleanups_[i]);
	}
}

bool FunctionLowerer::has_active_cleanups() const
{
	for (size_t i = 0; i < cleanups_.size(); ++i)
		if (!cleanups_[i].empty())
			return true;
	return false;
}

void FunctionLowerer::emit_unwind_cleanups()
{
	for (size_t n = 0; n < cleanups_.size(); ++n)
	{
		size_t i = cleanups_.size() - 1 - n;
		emit_scope_cleanups(cleanups_[i]);
	}
}

void FunctionLowerer::lower_global_variable_init(const Node& var)
{
	if (!starts_with(var.line, "variable ") || var.binding == NULL ||
	    var.children.empty())
		return;
	if (starts_with(var.children[0].line, "constructor-action"))
	{
			if (!var.children[0].children.empty() &&
			    var.children[0].children[0].direct_call != NULL &&
			    no_op_generated_default_constructor(
				    var.children[0].children[0].direct_call,
				    var.binding->type))
				return;
			if (!var.children[0].children.empty() &&
			    var.children[0].children[0].direct_call != NULL &&
			    var.children[0].children[0].direct_call->
				    is_generated_aggregate_constructor)
			{
				function<Value()> addr_for = [this, &var]() {
					program_.demand_global_declaration(var.binding);
					string tmp = fresh_temp();
					instr(tmp + " = addr @" + program_.symbol_for(var.binding));
					return Value("ptr", tmp);
				};
				lower_aggregate_init(addr_for,
				                     var.binding->type,
				                     var.children[0].children[0]);
				return;
			}
			if (!var.children[0].children.empty())
				emit_rvalue(var.children[0].children[0]);
			return;
	}
	if (var.children[0].direct_call != NULL &&
	    no_op_generated_default_constructor(var.children[0].direct_call,
	                                        var.binding->type))
		return;
	Binding* aggregate_ctor = NULL;
	if (starts_with(var.children[0].line, "braced-init-list"))
	{
		aggregate_ctor = var.children[0].direct_call;
		if (aggregate_ctor == NULL)
			aggregate_ctor = find_constructor(var.binding->type,
			                                  var.children[0].children.size());
	}
	if (aggregate_ctor != NULL &&
	    aggregate_ctor->is_generated_aggregate_constructor)
	{
		function<Value()> addr_for = [this, &var]() {
			program_.demand_global_declaration(var.binding);
			string tmp = fresh_temp();
			instr(tmp + " = addr @" + program_.symbol_for(var.binding));
			return Value("ptr", tmp);
		};
		lower_aggregate_init(addr_for, var.binding->type, var.children[0]);
		return;
	}
	if (default_init_no_op(var.binding->type))
		return;
	if (starts_with(var.children[0].line, "unary-expression") &&
	    var.children[0].has_op &&
	    var.children[0].op == OP_AMP &&
	    !var.children[0].children.empty() &&
	    var.children[0].children[0].binding != NULL &&
	    var.children[0].children[0].binding->kind == BindingKind::Function)
	{
		Binding* fn = var.children[0].children[0].binding;
		if (fn->is_inline_definition)
			program_.demand_inline_function(fn);
		string tmp = fresh_temp();
		instr(tmp + " = addr @" + program_.symbol_for(fn));
		program_.demand_global_declaration(var.binding);
		instr("store ptr " + tmp + ", @" + program_.symbol_for(var.binding));
		return;
	}
	if (starts_with(var.children[0].line, "id-expression") &&
	    var.children[0].binding != NULL &&
	    var.children[0].binding->kind == BindingKind::Function &&
	    pa11::strip_cv(var.binding->type)->kind == TypeKind::Pointer &&
	    pa11::strip_cv(var.binding->type)->base.get() != NULL &&
	    pa11::strip_cv(var.binding->type)->base->kind == TypeKind::Function)
	{
		Binding* fn = var.children[0].binding;
		if (fn->is_inline_definition)
			program_.demand_inline_function(fn);
		string tmp = fresh_temp();
		instr(tmp + " = addr @" + program_.symbol_for(fn));
		program_.demand_global_declaration(var.binding);
		instr("store ptr " + tmp + ", @" + program_.symbol_for(var.binding));
		return;
	}
	function<Value()> addr_for = [this, &var]() {
		program_.demand_global_declaration(var.binding);
		TypePtr bare = pa11::strip_cv(var.binding->type);
		if (bare->kind == TypeKind::Record || bare->kind == TypeKind::Array)
		{
			string tmp = fresh_temp();
			instr(tmp + " = addr @" + program_.symbol_for(var.binding));
			return Value("ptr", tmp);
		}
		return Value("ptr", "@" + program_.symbol_for(var.binding));
	};
	lower_object_init(addr_for, var.binding->type, var.children[0]);
}

void FunctionLowerer::lower_thread_local_variable_init(const Node& node)
{
	if (node.children.empty() || node.token_text.empty())
		return;
	string run_block = fresh_block("local_static_ctor_run");
	string done_block = fresh_block("local_static_ctor_done");
	string loaded = fresh_temp();
	instr(loaded + " = load i64 @" + node.token_text);
	string initialized = fresh_temp();
	instr(initialized + " = cmp ne i64 " + loaded + ", 0");
	terminate("branch " + initialized + ", ^" + done_block +
	          ", ^" + run_block);
	start_block(run_block);
	lower_global_variable_init(node.children[0]);
	instr("store i64 1, @" + node.token_text);
	terminate("jump ^" + done_block);
	start_block(done_block);
}

void FunctionLowerer::lower_global_variable_fini(const Node& var)
{
	if (!starts_with(var.line, "variable ") || var.binding == NULL)
		return;
	function<Value()> addr_for = [this, &var]() {
		program_.demand_global_declaration(var.binding);
		return Value("ptr", "@" + program_.symbol_for(var.binding));
	};
	lower_destructor_for_object(addr_for, var.binding->type);
}

void FunctionLowerer::lower_destructor_for_object(
	const function<Value()>& addr_for,
	TypePtr type)
{
	TypePtr bare = pa11::strip_cv(type);
	if (bare->kind == TypeKind::Array)
	{
		TypePtr elem = bare->base;
		uint64_t count = bare->unknown_bound ? 0 : bare->bound;
		for (uint64_t n = 0; n < count; ++n)
		{
			uint64_t i = count - 1 - n;
			function<Value()> elem_addr = [this, addr_for, elem, i]() {
				Value base = addr_for();
				string decay = fresh_temp();
				instr(decay + " = unary decay ptr " + base.text);
				string scaled = to_string(i);
				if (pa11::type_size(elem) != 1)
				{
					scaled = fresh_temp();
					instr(scaled + " = binary mul i64 " + to_string(i) +
					      ", " + to_string(pa11::type_size(elem)));
				}
				string addr = fresh_temp();
				instr(addr + " = index i8 [projection=array_element] " +
				      decay + ", " + scaled);
				return Value("ptr", addr);
			};
			lower_destructor_for_object(elem_addr, elem);
		}
		return;
	}
	if (bare->kind != TypeKind::Record)
		return;
	Binding* dtor = find_destructor(bare);
	if (dtor != NULL && !dtor->is_noop_destructor)
	{
		program_.demand_function_declaration(dtor);
		program_.demand_inline_function(dtor);
		Value target = addr_for();
		string arg = target.text;
		if (!arg.empty() && (arg[0] == '@' || arg[0] == '$'))
		{
			string tmp = fresh_temp();
			instr(tmp + " = addr " + arg);
			arg = tmp;
		}
		instr("call void @" + program_.symbol_for(dtor) + "(" +
		      arg + ")");
		return;
	}
	pa11::layout_record_type(bare);
	for (size_t n = 0; n < bare->fields.size(); ++n)
	{
		size_t i = bare->fields.size() - 1 - n;
		Binding* field = bare->fields[i];
		function<Value()> field_addr = [this, addr_for, field]() {
			Value base = addr_for();
			string addr = fresh_temp();
			instr(addr + " = index i8 [projection=field] " + base.text +
			      ", " + to_string(field->member_offset));
			return Value("ptr", addr);
		};
		lower_destructor_for_object(field_addr, field->type);
	}
	if (bare->base.get() != NULL)
	{
		function<Value()> base_addr = [this, addr_for, bare]() {
			Value base = addr_for();
			return emit_base_subobject_addr(base, bare, bare->base);
		};
		lower_destructor_for_object(base_addr, bare->base);
	}
}

void FunctionLowerer::lower_scope_destructor_for_object(
	const function<Value()>& addr_for,
	TypePtr type)
{
	TypePtr bare = pa11::strip_cv(type);
	if (bare->kind != TypeKind::Array)
	{
		lower_destructor_for_object(addr_for, type);
		return;
	}
	TypePtr elem = bare->base;
	uint64_t count = bare->unknown_bound ? 0 : bare->bound;
	for (uint64_t i = 0; i < count; ++i)
	{
		function<Value()> elem_addr = [this, addr_for, elem, i]() {
			Value base = addr_for();
			string decay = fresh_temp();
			instr(decay + " = unary decay ptr " + base.text);
			string scaled = to_string(i);
			if (pa11::type_size(elem) != 1)
			{
				scaled = fresh_temp();
				instr(scaled + " = binary mul i64 " + to_string(i) +
				      ", " + to_string(pa11::type_size(elem)));
			}
			string addr = fresh_temp();
			instr(addr + " = index i8 [projection=array_element] " +
			      decay + ", " + scaled);
			return Value("ptr", addr);
		};
		lower_destructor_for_object(elem_addr, elem);
	}
}

void FunctionLowerer::lower_member_fini(const Node& node)
{
	if (node.binding == NULL)
		return;
	function<Value()> member_addr = [this, &node]() {
		string this_ptr = fresh_temp();
		instr(this_ptr + " = load ptr $this");
		string addr = fresh_temp();
		instr(addr + " = index i8 [projection=field] " + this_ptr +
		      ", " + to_string(node.binding->member_offset));
		return Value("ptr", addr);
	};
	lower_destructor_for_object(member_addr, node.binding->type);
}

void FunctionLowerer::lower_base_fini(const Node& node)
{
	if (node.type.get() == NULL)
		return;
	TypePtr source = class_record_for_member(fn_.binding);
	function<Value()> base_addr = [this, source, &node]() {
		string this_ptr = fresh_temp();
		instr(this_ptr + " = load ptr $this");
		return emit_base_subobject_addr(Value("ptr", this_ptr),
		                                source,
		                                node.type);
	};
	Binding* dtor = find_destructor(node.type);
	if (dtor != NULL && dtor->is_virtual)
	{
		program_.demand_function_declaration(dtor);
		string callee = program_.destructor_symbol_for(dtor, true);
		program_.demand_inline_function(dtor, false);
		Value target = base_addr();
		instr("call void @" + callee + "(" + target.text + ")");
		return;
	}
	lower_destructor_for_object(base_addr, node.type);
}


}  // namespace internal
}  // namespace pa14
