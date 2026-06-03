#include "pa14_lowir_internal.h"

namespace pa14 {
namespace internal {

namespace {

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
	if (find_destructor(bare) != NULL)
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
	return default_init_no_op(type);
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

bool is_brace_elision_aggregate(TypePtr type)
{
	TypePtr bare = pa11::strip_cv(type);
	if (bare->kind == TypeKind::Array)
		return true;
	if (bare->kind != TypeKind::Record)
		return false;
	return !has_inline_constructor(type);
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

}  // namespace

void FunctionLowerer::lower_variable_decl(const Node& var)
{
	if (!starts_with(var.line, "variable ") || var.binding == NULL)
		return;
	string slot = slot_for(var.binding);
	if (var.children.empty())
	{
		TypePtr bare = pa11::strip_cv(var.binding->type);
		if (type_contains_record(var.binding->type))
		{
			Value base = ensure_pointer(emit_lvalue_addr(var));
			shared_ptr<bool> used(new bool(false));
			function<Value()> addr_for = [this, &var, base, used]() {
				if (!*used)
				{
					*used = true;
					return base;
				}
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
			register_cleanup(var.binding, var.binding->type);
			return;
		}
		if (!var.children[0].children.empty())
			emit_rvalue(var.children[0].children[0]);
		register_cleanup(var.binding, var.binding->type);
		return;
	}
	TypePtr bare = pa11::strip_cv(type);
	if ((bare->kind == TypeKind::Record || bare->kind == TypeKind::Array) &&
	    starts_with(var.children[0].line, "braced-init-list"))
	{
		Value direct_base;
		if (bare->kind == TypeKind::Array)
			direct_base = ensure_pointer(emit_lvalue_addr(var));
		function<Value()> addr_for = [this, &var, direct_base]() {
			if (!direct_base.text.empty())
				return direct_base;
			return ensure_pointer(emit_lvalue_addr(var));
		};
		if (bare->kind == TypeKind::Array)
			lower_direct_array_init(direct_base, type, var.children[0]);
		else
		{
			if (is_brace_elision_aggregate(type) &&
			    (!var.children[0].children.empty() ||
			     zero_init_has_store(type)))
				ensure_pointer(emit_lvalue_addr(var));
			lower_object_init(addr_for, type, var.children[0]);
		}
		register_cleanup(var.binding, type);
		return;
	}
	if (bare->kind == TypeKind::Record)
	{
		function<Value()> addr_for = [this, &var]() {
			return ensure_pointer(emit_lvalue_addr(var));
		};
		lower_object_init(addr_for, type, var.children[0]);
		register_cleanup(var.binding, type);
		return;
	}
	if (is_reference(type))
		instr("store ptr " + ensure_pointer(emit_lvalue_addr(var.children[0])).text +
		      ", $" + slot);
	else
	{
		Value init = emit_rvalue(var.children[0]);
		init = convert_value(init, var.children[0].type, type);
		instr("store " + scalar_lowir_type(type) + " " + init.text + ", $" + slot);
	}
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
	cleanups_.back().push_back(Cleanup(binding, type));
}

void FunctionLowerer::emit_scope_cleanups(vector<Cleanup>& scope)
{
	for (size_t n = 0; n < scope.size(); ++n)
	{
		size_t i = scope.size() - 1 - n;
		Binding* binding = scope[i].binding;
		TypePtr type = scope[i].type;
		function<Value()> addr_for = [this, binding]() {
			return ensure_pointer(Value("ptr", "$" + slot_for(binding)));
		};
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
		if (!var.children[0].children.empty())
			emit_rvalue(var.children[0].children[0]);
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
		function<Value()> base_addr = [this, addr_for]() {
			Value base = addr_for();
			string addr = fresh_temp();
			instr(addr + " = index i8 [projection=base_subobject] " +
			      base.text + ", 0");
			return Value("ptr", addr);
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
	function<Value()> base_addr = [this]() {
		string this_ptr = fresh_temp();
		instr(this_ptr + " = load ptr $this");
		string addr = fresh_temp();
		instr(addr + " = index i8 [projection=base_subobject] " +
		      this_ptr + ", 0");
		return Value("ptr", addr);
	};
	lower_destructor_for_object(base_addr, node.type);
}

void FunctionLowerer::lower_aggregate_init(const function<Value()>& addr_for,
                                           TypePtr type,
                                           const Node& init)
{
	size_t index = 0;
	lower_aggregate_elements(addr_for, type, init.children, index);
}

Value FunctionLowerer::direct_array_element_addr(Value base,
                                                 TypePtr elem,
                                                 size_t index)
{
	uint64_t offset = index * pa11::type_size(elem);
	if (offset == 0)
		return base;
	string addr = fresh_temp();
	instr(addr + " = index i8 [projection=array_element] " + base.text + ", " +
	      to_string(offset));
	return Value("ptr", addr);
}

void FunctionLowerer::lower_direct_array_init(Value base,
                                              TypePtr type,
                                              const Node& init)
{
	TypePtr bare = pa11::strip_cv(type);
	if (bare->kind != TypeKind::Array)
		return;
	function<Value()> base_addr = [base]() {
		return base;
	};
	if (!init.children.empty() &&
	    lower_string_array_init(base_addr, type, init.children[0]))
		return;
	TypePtr elem = bare->base;
	uint64_t count = bare->unknown_bound ? init.children.size() : bare->bound;
	size_t clause = 0;
	for (size_t i = 0; i < count; ++i)
	{
		function<Value()> elem_addr = [this, base, elem, i]() {
			return direct_array_element_addr(base, elem, i);
		};
		if (clause >= init.children.size())
		{
			lower_zero_init(elem_addr, elem);
			continue;
		}
		const Node& child = init.children[clause];
		if (is_brace_elision_aggregate(elem) &&
		    !starts_with(child.line, "braced-init-list"))
			lower_aggregate_elements(elem_addr, elem, init.children, clause);
		else
			lower_object_init(elem_addr, elem, init.children[clause++]);
	}
}

void FunctionLowerer::lower_aggregate_elements(const function<Value()>& addr_for,
                                               TypePtr type,
                                               const vector<Node>& clauses,
                                               size_t& index)
{
	TypePtr bare = pa11::strip_cv(type);
	if (bare->kind == TypeKind::Record)
	{
		pa11::layout_record_type(bare);
		if (bare->base.get() != NULL)
		{
			function<Value()> base_addr = [this, addr_for]() {
				Value base = addr_for();
				string addr = fresh_temp();
				instr(addr + " = index i8 [projection=base_subobject] " +
				      base.text + ", 0");
				return Value("ptr", addr);
				};
				if (index >= clauses.size())
					lower_base_zero_init(addr_for, bare->base);
				else
				{
				const Node& child = clauses[index];
				if (is_brace_elision_aggregate(bare->base) &&
				    !starts_with(child.line, "braced-init-list"))
					lower_aggregate_elements(base_addr, bare->base, clauses, index);
				else
					lower_object_init(base_addr, bare->base, clauses[index++]);
			}
		}
		for (size_t i = 0; i < bare->fields.size(); ++i)
		{
			Binding* field = bare->fields[i];
			function<Value()> field_addr = [this, addr_for, field]() {
				Value base = addr_for();
				string addr = fresh_temp();
				instr(addr + " = index i8 [projection=field] " + base.text +
				      ", " + to_string(field->member_offset));
				return Value("ptr", addr);
			};
			if (index >= clauses.size())
			{
				lower_zero_init(field_addr, field->type);
				continue;
			}
			const Node& child = clauses[index];
			if (is_brace_elision_aggregate(field->type) &&
			    !starts_with(child.line, "braced-init-list"))
				lower_aggregate_elements(field_addr, field->type, clauses, index);
			else if (field->is_bit_field)
			{
				Value value = convert_value(emit_rvalue(child),
				                            child.type,
				                            field->type);
				string low_type = scalar_lowir_type(field->type);
				uint64_t mask = field->bit_width >= 64
					? ~uint64_t(0) : ((uint64_t(1) << field->bit_width) - 1);
				string masked = fresh_temp();
				instr(masked + " = binary and " + low_type + " " +
				      to_string(mask) + ", " + value.text);
				if (field->bit_offset != 0)
				{
					string shifted = fresh_temp();
					instr(shifted + " = binary shl " + low_type + " " +
					      masked + ", " + to_string(field->bit_offset));
					masked = shifted;
				}
				Value target = field_addr();
				instr("store " + low_type + " " + masked + ", " + target.text);
				++index;
			}
			else
				lower_object_init(field_addr, field->type, clauses[index++]);
		}
		return;
	}
	if (bare->kind != TypeKind::Array)
		return;
	if (index < clauses.size() &&
	    lower_string_array_init(addr_for, type, clauses[index]))
	{
		++index;
		return;
	}
	TypePtr elem = bare->base;
	uint64_t count = bare->unknown_bound ? clauses.size() - index : bare->bound;
		for (size_t i = 0; i < count; ++i)
		{
			function<Value()> elem_addr = [this, addr_for, elem, i]() {
				Value base = addr_for();
				string decay = fresh_temp();
				instr(decay + " = unary decay ptr " + base.text);
				if (pa11::strip_cv(elem)->kind == TypeKind::Record)
				{
					string scaled = fresh_temp();
					instr(scaled + " = binary mul i64 " + to_string(i) +
					      ", " + to_string(pa11::type_size(elem)));
					string addr = fresh_temp();
					instr(addr + " = index i8 [projection=array_element] " +
				      decay + ", " + scaled);
					return Value("ptr", addr);
				}
				string addr = fresh_temp();
				instr(addr + " = index " + scalar_lowir_type(elem) +
				      " [projection=array_element] " + decay + ", " +
				      to_string(i));
				return Value("ptr", addr);
			};
		if (index >= clauses.size())
		{
			lower_zero_init(elem_addr, elem);
			continue;
		}
		const Node& child = clauses[index];
		if (is_brace_elision_aggregate(elem) &&
		    !starts_with(child.line, "braced-init-list"))
			lower_aggregate_elements(elem_addr, elem, clauses, index);
		else
			lower_object_init(elem_addr, elem, clauses[index++]);
	}
}

void FunctionLowerer::lower_object_init(const function<Value()>& addr_for,
                                        TypePtr type,
                                        const Node& init)
{
	if (starts_with(init.line, "braced-init-list"))
	{
		if (init.direct_call != NULL)
		{
			vector<const Node*> args;
			for (size_t i = 0; i < init.children.size(); ++i)
				args.push_back(&init.children[i]);
			lower_constructor_call(addr_for, init.direct_call, args);
			return;
			}
			if (pa11::strip_cv(type)->kind == TypeKind::Record)
			{
				Binding* ctor = find_constructor(type, init.children.size());
				if (ctor != NULL && !init.children.empty())
				{
					vector<const Node*> args;
					for (size_t i = 0; i < init.children.size(); ++i)
						args.push_back(&init.children[i]);
					lower_constructor_call(addr_for, ctor, args);
					return;
				}
			}
			if (is_brace_elision_aggregate(type))
			{
				lower_aggregate_init(addr_for, type, init);
				return;
			}
			if (pa11::strip_cv(type)->kind == TypeKind::Record)
			{
				throw runtime_error("no matching constructor");
			}
		if (init.children.empty())
		{
			lower_zero_init(addr_for, type);
			return;
		}
		lower_object_init(addr_for, type, init.children[0]);
		return;
	}
	if (is_reference(type))
	{
		Value target = ensure_pointer(emit_lvalue_addr(init));
		Value addr = addr_for();
		instr("store ptr " + target.text + ", " + addr.text);
		return;
	}
	if (pa11::strip_cv(type)->kind == TypeKind::Record)
	{
		if (starts_with(init.line, "cast-expression") &&
		    pa11::same_type(pa11::strip_cv(type), pa11::strip_cv(init.type)) &&
		    init.children.size() == 1)
		{
			Binding* ctor = find_constructor(type, 1);
			if (ctor == NULL)
				throw runtime_error("no matching constructor");
			vector<const Node*> args;
			args.push_back(&init.children[0]);
			lower_constructor_call(addr_for, ctor, args);
			return;
		}
		Binding* ctor = find_constructor(type, 1);
		if (ctor == NULL)
			throw runtime_error("no matching constructor");
		vector<const Node*> args;
		args.push_back(&init);
		lower_constructor_call(addr_for, ctor, args);
		return;
	}
	Value addr = addr_for();
	Value value = convert_value(emit_rvalue(init), init.type, type);
	instr("store " + scalar_lowir_type(type) + " " +
	      value.text + ", " + addr.text);
}

void FunctionLowerer::lower_storage_zero(Value addr, uint64_t size)
{
	string type = zero_integer_type(size);
	if (!type.empty())
	{
		instr("store " + type + " 0, " + addr.text);
		return;
	}
	for (uint64_t i = 0; i < size; ++i)
	{
		string target = addr.text;
		if (i != 0)
		{
			target = fresh_temp();
			instr(target + " = index i8 " + addr.text + ", " + to_string(i));
		}
		instr("store i8 0, " + target);
	}
}

void FunctionLowerer::lower_base_zero_init(const function<Value()>& addr_for,
                                           TypePtr type)
{
	TypePtr bare = pa11::strip_cv(type);
	if (bare->kind != TypeKind::Record)
	{
		lower_zero_init(addr_for, type);
		return;
	}
	Binding* ctor = find_constructor(type, 0);
	if (ctor != NULL)
	{
		if (no_op_generated_default_constructor(ctor, type))
			return;
		vector<const Node*> args;
		lower_constructor_call(addr_for, ctor, args);
		return;
	}
	if (has_inline_constructor(type))
		throw runtime_error("no default constructor");
	pa11::layout_record_type(bare);
	if (bare->base.get() != NULL)
		lower_base_zero_init(addr_for, bare->base);
	for (size_t i = 0; i < bare->fields.size(); ++i)
	{
		Binding* field = bare->fields[i];
		function<Value()> field_addr = [this, addr_for, field]() {
			Value base = addr_for();
			if (field->member_offset == 0)
				return base;
			string addr = fresh_temp();
			instr(addr + " = index i8 [projection=field] " + base.text +
			      ", " + to_string(field->member_offset));
			return Value("ptr", addr);
		};
		lower_zero_init(field_addr, field->type);
	}
}

void FunctionLowerer::lower_zero_init(const function<Value()>& addr_for, TypePtr type)
{
	TypePtr bare = pa11::strip_cv(type);
	if (bare->kind == TypeKind::Record)
	{
		Binding* ctor = find_constructor(type, 0);
		if (ctor != NULL)
		{
			if (no_op_generated_default_constructor(ctor, type))
				return;
			vector<const Node*> args;
			lower_constructor_call(addr_for, ctor, args);
			return;
		}
		if (has_inline_constructor(type))
			throw runtime_error("no default constructor");
		pa11::layout_record_type(bare);
			if (bare->base.get() != NULL)
				lower_base_zero_init(addr_for, bare->base);
		for (size_t i = 0; i < bare->fields.size(); ++i)
		{
			Binding* field = bare->fields[i];
			function<Value()> field_addr = [this, addr_for, field]() {
				Value base = addr_for();
				string addr = fresh_temp();
				instr(addr + " = index i8 [projection=field] " + base.text +
				      ", " + to_string(field->member_offset));
				return Value("ptr", addr);
			};
			lower_zero_init(field_addr, field->type);
		}
		return;
	}
	if (bare->kind == TypeKind::Array)
	{
		TypePtr elem = bare->base;
		uint64_t count = bare->unknown_bound ? 0 : bare->bound;
		for (size_t i = 0; i < count; ++i)
		{
			function<Value()> elem_addr = [this, addr_for, elem, i]() {
				Value base = addr_for();
				string decay = fresh_temp();
				instr(decay + " = unary decay ptr " + base.text);
				if (pa11::strip_cv(elem)->kind == TypeKind::Record)
				{
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
				}
				string addr = fresh_temp();
				instr(addr + " = index " + scalar_lowir_type(elem) +
				      " [projection=array_element] " + decay + ", " +
				      to_string(i));
				return Value("ptr", addr);
			};
			lower_zero_init(elem_addr, elem);
		}
		return;
	}
	if (is_reference(type))
		return;
	Value addr = addr_for();
	instr("store " + scalar_lowir_type(type) + " 0, " + addr.text);
}

void FunctionLowerer::lower_default_init(const function<Value()>& addr_for,
                                         TypePtr type)
{
	TypePtr bare = pa11::strip_cv(type);
	if (bare->kind == TypeKind::Record)
	{
		Binding* ctor = find_constructor(type, 0);
		if (ctor != NULL)
		{
			vector<const Node*> args;
			lower_constructor_call(addr_for, ctor, args);
			return;
		}
		return;
	}
	if (bare->kind == TypeKind::Array)
	{
		TypePtr elem = bare->base;
		uint64_t count = bare->unknown_bound ? 0 : bare->bound;
		for (size_t i = 0; i < count; ++i)
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
			lower_default_init(elem_addr, elem);
		}
	}
}

void FunctionLowerer::emit_temporary_cleanups(
	const vector<pair<Value, TypePtr> >& temps)
{
	for (size_t n = 0; n < temps.size(); ++n)
	{
		size_t i = temps.size() - 1 - n;
		Value addr = temps[i].first;
		TypePtr type = temps[i].second;
		function<Value()> addr_for = [addr]() {
			return addr;
		};
		lower_destructor_for_object(addr_for, type);
	}
}

void FunctionLowerer::lower_record_reference_constructor_argument(
	const Node& arg,
	TypePtr param,
	vector<string>& lowered,
	vector<pair<Value, TypePtr> >& temp_cleanups,
	vector<PendingConstructorConversion>& pending_conversions)
{
	TypePtr object = pa11::strip_cv(object_type(arg.type));
	TypePtr target = pa11::strip_cv(param->base);
	string prefix = pa11::same_type(object, target) ? "arg" : "tmpobj";
	string slot = fresh_aux_slot(prefix, scalar_lowir_type(object));
	string addr_name = fresh_temp();
	Value temp_addr("ptr", addr_name);
	function<Value()> temp_addr_for = [temp_addr]() {
		return temp_addr;
	};
	if (find_destructor(object) != NULL)
	{
		string dispatch = fresh_block("call_unwind_dispatch");
		string end = fresh_block("call_unwind_end");
		instr("eh_try ^" + dispatch);
		++eh_try_depth_;
		instr(addr_name + " = addr $" + slot);
		lower_object_init(temp_addr_for, object, arg);
		--eh_try_depth_;
		instr("eh_end");
		terminate("jump ^" + end);
		start_block(dispatch);
		emit_temporary_cleanups(temp_cleanups);
		terminate("resume");
		start_block(end);
		temp_cleanups.push_back(make_pair(temp_addr, object));
		PendingConstructorConversion pending;
		pending.index = lowered.size();
		pending.value = temp_addr;
		pending.from = pa11::make_pointer(object);
		pending.to = pa11::make_pointer(param->base);
		pending_conversions.push_back(pending);
		lowered.push_back(temp_addr.text);
		return;
	}
	instr(addr_name + " = addr $" + slot);
	lower_object_init(temp_addr_for, object, arg);
	lowered.push_back(convert_value(temp_addr,
	                                pa11::make_pointer(object),
	                                pa11::make_pointer(param->base)).text);
}

void FunctionLowerer::emit_constructor_call_with_cleanups(
	Binding* ctor,
	vector<string>& lowered,
	const vector<pair<Value, TypePtr> >& temp_cleanups,
	const vector<PendingConstructorConversion>& pending_conversions)
{
	program_.demand_function_declaration(ctor);
	program_.demand_inline_function(ctor);
	function<string()> call_text = [this, ctor, &lowered]() {
		ostringstream call;
		call << "call void @" << program_.symbol_for(ctor) << "(";
		for (size_t i = 0; i < lowered.size(); ++i)
		{
			if (i != 0)
				call << ", ";
			call << lowered[i];
		}
		call << ")";
		return call.str();
	};
	if (temp_cleanups.empty())
	{
		for (size_t i = 0; i < pending_conversions.size(); ++i)
			lowered[pending_conversions[i].index] =
				convert_value(pending_conversions[i].value,
				              pending_conversions[i].from,
				              pending_conversions[i].to).text;
		instr(call_text());
		return;
	}
	string dispatch = fresh_block("call_unwind_dispatch");
	string end = fresh_block("call_unwind_end");
	instr("eh_try ^" + dispatch);
	++eh_try_depth_;
	for (size_t i = 0; i < pending_conversions.size(); ++i)
		lowered[pending_conversions[i].index] =
			convert_value(pending_conversions[i].value,
			              pending_conversions[i].from,
			              pending_conversions[i].to).text;
	instr(call_text());
	emit_temporary_cleanups(temp_cleanups);
	--eh_try_depth_;
	instr("eh_end");
	terminate("jump ^" + end);
	start_block(dispatch);
	emit_temporary_cleanups(temp_cleanups);
	terminate("resume");
	start_block(end);
}

void FunctionLowerer::lower_constructor_call(const function<Value()>& addr_for,
                                             Binding* ctor,
                                             const vector<const Node*>& args)
{
	if (ctor == NULL)
		throw runtime_error("missing constructor");
	vector<string> lowered;
	vector<pair<Value, TypePtr> > temp_cleanups;
	vector<PendingConstructorConversion> pending_conversions;
	lowered.push_back(addr_for().text);
	for (size_t i = 0; i < args.size(); ++i)
	{
		TypePtr param = ctor->type->parameters[i + 1];
		const Node& arg = *args[i];
		if (is_reference(param))
		{
			if (arg.category == ValueCategory::LValue)
			{
				Value addr = ensure_pointer(emit_lvalue_addr(arg));
				TypePtr from_ptr = pa11::make_pointer(object_type(arg.type));
				TypePtr to_ptr = pa11::make_pointer(param->base);
				lowered.push_back(convert_value(addr, from_ptr, to_ptr).text);
			}
				else if (pa11::strip_cv(param->base)->kind == TypeKind::Record &&
				         pa11::strip_cv(object_type(arg.type))->kind == TypeKind::Record)
					lower_record_reference_constructor_argument(
						arg,
						param,
						lowered,
						temp_cleanups,
						pending_conversions);
			else
			{
				string slot = fresh_aux_slot("refarg",
				                             scalar_lowir_type(param->base));
				Value value = convert_value(emit_rvalue(arg),
				                            arg.type,
				                            param->base);
				instr("store " + scalar_lowir_type(param->base) + " " +
				      value.text + ", $" + slot);
				string addr = fresh_temp();
				instr(addr + " = addr $" + slot);
				lowered.push_back(addr);
			}
		}
		else
		{
			if (pa11::strip_cv(param)->kind == TypeKind::Record)
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
					function<Value()> arg_addr = [target_addr]() {
						return target_addr;
					};
					lower_object_init(arg_addr, param, arg);
				}
				lowered.push_back("$" + slot);
			}
			else
				lowered.push_back(convert_value(emit_rvalue(arg),
				                                arg.type,
				                                param).text);
		}
	}
	emit_constructor_call_with_cleanups(ctor,
	                                    lowered,
	                                    temp_cleanups,
	                                    pending_conversions);
}

bool FunctionLowerer::lower_string_array_init(const function<Value()>& addr_for,
                                              TypePtr type,
                                              const Node& init)
{
	TypePtr bare = pa11::strip_cv(type);
	if (bare->kind != TypeKind::Array || !is_string_literal_node(init))
		return false;
	TypePtr elem = pa11::strip_cv(bare->base);
	if (elem->kind != TypeKind::Fundamental || pa11::type_size(elem) != 1)
		return false;
	StringLiteralInfo info;
	if (!AnalyzeStringLiteral(init.token_text, info) || !info.ud_suffix.empty())
		return false;
	uint64_t count = bare->unknown_bound ? info.bytes.size() : bare->bound;
	for (size_t i = 0; i < count; ++i)
	{
		Value base = addr_for();
		string decay = fresh_temp();
		instr(decay + " = unary decay ptr " + base.text);
		string addr = fresh_temp();
		instr(addr + " = index " + scalar_lowir_type(bare->base) +
		      " [projection=array_element] " + decay + ", " + to_string(i));
		uint64_t value = i < info.bytes.size() ? info.bytes[i] : 0;
		instr("store " + scalar_lowir_type(bare->base) + " " +
		      to_string(value) + ", " + addr);
	}
	return true;
}

void FunctionLowerer::lower_base_init(const Node& node)
{
	if (node.type.get() == NULL)
		return;
	function<Value()> base_addr = [this]() {
		string this_ptr = fresh_temp();
		instr(this_ptr + " = load ptr $this");
		string addr = fresh_temp();
		instr(addr + " = index i8 [projection=base_subobject] " +
		      this_ptr + ", 0");
		return Value("ptr", addr);
	};
	if (node.children.empty())
		lower_zero_init(base_addr, node.type);
	else
		lower_object_init(base_addr, node.type, node.children[0]);
}

void FunctionLowerer::lower_member_init(const Node& node)
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
	if (!node.children.empty() &&
	    starts_with(node.children[0].line, "braced-init-list"))
		{
			if (node.direct_call != NULL)
			{
				if (no_op_generated_default_constructor(node.direct_call,
				                                        node.binding->type))
					return;
				Value addr = member_addr();
				if (node.direct_call->is_generated_default_constructor)
					lower_storage_zero(addr, pa11::type_size(node.binding->type));
			function<Value()> same_addr = [addr]() {
				return addr;
			};
			vector<const Node*> args;
			for (size_t i = 0; i < node.children[0].children.size(); ++i)
				args.push_back(&node.children[0].children[i]);
			lower_constructor_call(same_addr, node.direct_call, args);
			return;
		}
		lower_object_init(member_addr, node.binding->type, node.children[0]);
		return;
	}
	if (node.direct_call != NULL)
	{
		if (no_op_generated_default_constructor(node.direct_call,
		                                        node.binding->type))
			return;
		program_.demand_function_declaration(node.direct_call);
		program_.demand_inline_function(node.direct_call);
		vector<string> args;
		args.push_back(member_addr().text);
		for (size_t i = 0; i < node.children.size(); ++i)
		{
			if (i == 0 &&
			    starts_with(node.children[i].line, "literal prvalue " +
			                pa11::describe_type(node.binding->type)))
				continue;
			args.push_back(emit_rvalue(node.children[i]).text);
		}
		ostringstream call;
		call << "call void @" << program_.symbol_for(node.direct_call) << "(";
		for (size_t i = 0; i < args.size(); ++i)
		{
			if (i != 0)
				call << ", ";
			call << args[i];
		}
		call << ")";
		instr(call.str());
		return;
		}
		if (node.children.empty())
		{
			if (pa11::strip_cv(node.binding->type)->kind == TypeKind::Array)
				lower_default_init(member_addr, node.binding->type);
			return;
		}
		if (is_reference(node.binding->type))
	{
		Value target = ensure_pointer(emit_lvalue_addr(node.children[0]));
		instr("store ptr " + target.text + ", " + member_addr().text);
	}
	else
	{
		Value value = convert_value(emit_rvalue(node.children[0]),
		                            node.children[0].type,
		                            node.binding->type);
		if (node.binding->is_bit_field)
		{
			lower_bitfield_member_init(node, value, member_addr);
			return;
		}
		Value target = member_addr();
		instr("store " + scalar_lowir_type(node.binding->type) + " " +
		      value.text + ", " + target.text);
	}
}

void FunctionLowerer::lower_bitfield_member_init(
	const Node& node,
	Value value,
	const function<Value()>& member_addr)
{
	string low_type = scalar_lowir_type(node.binding->type);
	uint64_t mask = node.binding->bit_width >= 64
		? ~uint64_t(0) : ((uint64_t(1) << node.binding->bit_width) - 1);
	uint64_t storage_key = node.binding->member_offset;
	bool merge = initialized_bitfield_storage_.find(storage_key) !=
	             initialized_bitfield_storage_.end();
	if (merge)
	{
		Value target = member_addr();
		string oldv = fresh_temp();
		instr(oldv + " = load " + low_type + " " + target.text);
		uint64_t storage_mask = mask << node.binding->bit_offset;
		uint64_t storage_bits = pa11::type_size(node.binding->type) * 8;
		uint64_t clear_mask = ~storage_mask;
		if (storage_bits < 64)
			clear_mask &= (uint64_t(1) << storage_bits) - 1;
		string cleared = fresh_temp();
		instr(cleared + " = binary and " + low_type + " " + oldv +
		      ", " + to_string(clear_mask));
		string masked = fresh_temp();
		instr(masked + " = binary and " + low_type + " " +
		      to_string(mask) + ", " + value.text);
		if (node.binding->bit_offset != 0)
		{
			string shifted = fresh_temp();
			instr(shifted + " = binary shl " + low_type + " " +
			      masked + ", " + to_string(node.binding->bit_offset));
			masked = shifted;
		}
		string merged = fresh_temp();
		instr(merged + " = binary or " + low_type + " " + cleared +
		      ", " + masked);
		Value store_target = member_addr();
		instr("store " + low_type + " " + merged + ", " + store_target.text);
		initialized_bitfield_storage_.insert(storage_key);
		return;
	}
	string masked = fresh_temp();
	instr(masked + " = binary and " + low_type + " " +
	      to_string(mask) + ", " + value.text);
	if (node.binding->bit_offset != 0)
	{
		string shifted = fresh_temp();
		instr(shifted + " = binary shl " + low_type + " " + masked +
		      ", " + to_string(node.binding->bit_offset));
		masked = shifted;
	}
	Value target = member_addr();
	instr("store " + low_type + " " + masked + ", " + target.text);
	initialized_bitfield_storage_.insert(storage_key);
}

}  // namespace internal
}  // namespace pa14
