#include "pa14_lowir_internal.h"

namespace pa14 {
namespace internal {

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
		if (bare->tag == "union")
		{
			if (bare->fields.empty())
				return;
			Binding* field = bare->fields[0];
			function<Value()> field_addr = [this, addr_for, field]() {
				Value base = addr_for();
				string addr = fresh_temp();
				instr(addr + " = index i8 [projection=field] " + base.text +
				      ", " + to_string(field->member_offset));
				return Value("ptr", addr);
			};
			if (index >= clauses.size())
				lower_zero_init(field_addr, field->type);
			else
				lower_object_init(field_addr, field->type, clauses[index++]);
			return;
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
			if (index >= clauses.size())
				lower_base_zero_init(addr_for, bare->base);
			else
			{
				const Node& child = clauses[index];
				if (same_record_initializer(child, bare->base))
					lower_object_init(base_addr, bare->base, clauses[index++]);
				else if (is_brace_elision_aggregate(bare->base) &&
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
			if (same_record_initializer(child, field->type))
				lower_object_init(field_addr, field->type, clauses[index++]);
			else if (is_brace_elision_aggregate(field->type) &&
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
			if (init.direct_call->is_generated_aggregate_constructor &&
			    !pa11::type_has_const(type) &&
			    !type_has_reference_subobject(type) &&
			    !record_has_user_assignment_operator(type))
			{
				lower_aggregate_init(addr_for, type, init);
				return;
			}
			if (inline_defaulted_copy_move_storage_constructor(init.direct_call,
			                                                   type,
			                                                   init))
			{
				const Node& source_node = init.children[0];
				TypePtr source_object = object_type(source_node.type);
				Value target = addr_for();
				Value source;
				if (source_node.category == ValueCategory::LValue ||
				    source_node.category == ValueCategory::XValue)
					source = ensure_pointer(emit_lvalue_addr(source_node));
				else
				{
					string slot =
						fresh_aux_slot("tmpobj",
						               scalar_lowir_type(source_object));
					string addr = fresh_temp();
					instr(addr + " = addr $" + slot);
					source = Value("ptr", addr);
					function<Value()> source_addr = [source]() {
						return source;
					};
					lower_object_init(source_addr, source_object, source_node);
				}
				Value converted =
					convert_value(source,
					              pa11::make_pointer(source_object),
					              pa11::make_pointer(type));
				instr("copyobj " + to_string(pa11::type_size(type)) +
				      "x" + to_string(pa11::type_align(type)) + " " +
				      converted.text + ", " + target.text);
				return;
			}
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
				if (ctor->is_generated_aggregate_constructor &&
				    !pa11::type_has_const(type) &&
				    !type_has_reference_subobject(type) &&
				    !record_has_user_assignment_operator(type))
				{
					lower_aggregate_init(addr_for, type, init);
					return;
				}
				vector<const Node*> args;
				for (size_t i = 0; i < init.children.size(); ++i)
					args.push_back(&init.children[i]);
				lower_constructor_call(addr_for, ctor, args);
				return;
			}
			if (ctor != NULL && init.children.empty() &&
			    (ctor->is_generated_default_constructor || ctor->is_defaulted))
			{
				Value addr = addr_for();
				lower_storage_zero(addr, pa11::type_size(type));
				function<Value()> same_addr = [addr]() {
					return addr;
				};
				vector<const Node*> args;
				lower_constructor_call(same_addr, ctor, args);
				return;
			}
		}
		if (is_brace_elision_aggregate(type))
		{
			lower_aggregate_init(addr_for, type, init);
			return;
		}
		if (pa11::strip_cv(type)->kind == TypeKind::Record)
			throw runtime_error("no matching constructor");
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
		    init.children.size() == 1)
		{
			TypePtr src_record =
				pa11::strip_cv(object_type(init.children[0].type));
			TypePtr dst_record = pa11::strip_cv(type);
			if (src_record->kind == TypeKind::Record &&
			    dst_record->kind == TypeKind::Record &&
			    !pa11::same_type(src_record, dst_record) &&
			    record_has_base(src_record, dst_record))
			{
				Value target = addr_for();
				Value source;
				if (init.children[0].category == ValueCategory::LValue ||
				    init.children[0].category == ValueCategory::XValue)
					source = ensure_pointer(emit_lvalue_addr(init.children[0]));
				else
				{
					string slot = fresh_aux_slot("tmpobj",
					                             scalar_lowir_type(src_record));
					string addr_name = fresh_temp();
					instr(addr_name + " = addr $" + slot);
					source = Value("ptr", addr_name);
					function<Value()> source_addr = [source]() {
						return source;
					};
					lower_object_init(source_addr,
					                  src_record,
					                  init.children[0]);
				}
				string base = fresh_temp();
				instr(base + " = index i8 [projection=base_subobject] " +
				      source.text + ", 0");
				if (record_has_storage_copy(type))
					instr("copyobj " + to_string(pa11::type_size(type)) +
					      "x" + to_string(pa11::type_align(type)) + " " +
					      base + ", " + target.text);
				return;
			}
		}
		if (starts_with(init.line, "conditional-expression") &&
		    init.children.size() == 3)
		{
			Binding* copy = find_copy_move_constructor(type, false);
			if (copy == NULL && !type_needs_cleanup(type))
			{
				Value target = addr_for();
				function<Value()> target_addr = [target]() {
					return target;
				};
				string yes = fresh_block("condobj_then");
				string no = fresh_block("condobj_else");
				string end = fresh_block("condobj_end");
				Value cond = emit_rvalue(init.children[0]);
				if (is_float_type(init.children[0].type))
					cond = bool_value(cond, init.children[0].type);
				terminate("branch " + cond.text + ", ^" + yes + ", ^" + no);
				start_block(yes);
				lower_object_init(target_addr, type, init.children[1]);
				terminate("jump ^" + end);
				start_block(no);
				lower_object_init(target_addr, type, init.children[2]);
				terminate("jump ^" + end);
				start_block(end);
				return;
			}
			Value target = addr_for();
			string slot = fresh_aux_slot("arg", slot_lowir_type(type));
			string temp_name = fresh_temp();
			instr(temp_name + " = addr $" + slot);
			Value temp_addr("ptr", temp_name);
			function<Value()> result_addr = [temp_addr]() {
				return temp_addr;
			};
			string yes = fresh_block("condobj_then");
			string no = fresh_block("condobj_else");
			string end = fresh_block("condobj_end");
			Value cond = emit_rvalue(init.children[0]);
			if (is_float_type(init.children[0].type))
				cond = bool_value(cond, init.children[0].type);
			terminate("branch " + cond.text + ", ^" + yes + ", ^" + no);
			start_block(yes);
			lower_object_init(result_addr, type, init.children[1]);
			terminate("jump ^" + end);
			start_block(no);
			lower_object_init(result_addr, type, init.children[2]);
			terminate("jump ^" + end);
			start_block(end);
			Binding* temp_dtor = find_destructor(type);
			bool call_temp_dtor =
				temp_dtor != NULL && !temp_dtor->is_generated_default_destructor;
			function<void()> destroy_result = [this, result_addr, type,
			                                  temp_dtor, call_temp_dtor]() {
				if (call_temp_dtor)
				{
					program_.demand_function_declaration(temp_dtor);
					program_.demand_inline_function(temp_dtor);
					Value target = result_addr();
					string arg = target.text;
					if (!arg.empty() && (arg[0] == '@' || arg[0] == '$'))
					{
						string tmp = fresh_temp();
						instr(tmp + " = addr " + arg);
						arg = tmp;
					}
					instr("call void @" + program_.symbol_for(temp_dtor) +
					      "(" + arg + ")");
				}
				else if (type_needs_cleanup(type))
					lower_destructor_for_object(result_addr, type);
			};
			if (copy != NULL)
			{
				program_.demand_function_declaration(copy);
				program_.demand_inline_function(copy);
				string dispatch = fresh_block("call_unwind_dispatch");
				string done = fresh_block("call_unwind_end");
				instr("eh_try ^" + dispatch);
				++eh_try_depth_;
				instr("call void @" + program_.symbol_for(copy) +
				      "(" + target.text + ", " + temp_addr.text + ")");
				destroy_result();
				--eh_try_depth_;
				instr("eh_end");
				terminate("jump ^" + done);
				start_block(dispatch);
				destroy_result();
				emit_unwind_cleanups();
				terminate("resume");
				start_block(done);
				return;
			}
			if (record_has_storage_copy(type))
				instr("copyobj " + to_string(pa11::type_size(type)) +
				      "x" + to_string(pa11::type_align(type)) + " " +
				      temp_addr.text + ", " + target.text);
			destroy_result();
			return;
		}
		if (lower_indirect_record_call(addr_for, init))
			return;
		if (starts_with(init.line, "cast-expression") &&
		    pa11::same_type(pa11::strip_cv(type), pa11::strip_cv(init.type)) &&
		    init.children.size() == 1)
		{
			TypePtr child_record =
				pa11::strip_cv(object_type(init.children[0].type));
			if (child_record->kind != TypeKind::Record ||
			    !pa11::same_type(child_record, pa11::strip_cv(type)))
			{
				Binding* ctor = find_constructor(type, 1);
				if (ctor == NULL)
					throw runtime_error("no matching constructor");
				vector<const Node*> args;
				args.push_back(&init.children[0]);
				lower_constructor_call(addr_for, ctor, args);
				return;
			}
		}
		TypePtr src_record = pa11::strip_cv(object_type(init.type));
		TypePtr dst_record = pa11::strip_cv(type);
		if (src_record->kind == TypeKind::Record &&
		    pa11::same_type(src_record, dst_record))
		{
			Binding* copy_move =
				(init.category == ValueCategory::LValue ||
				 init.category == ValueCategory::XValue)
				? find_copy_move_constructor(
					type,
					init.category == ValueCategory::XValue)
				: NULL;
			if (copy_move == NULL && init.category == ValueCategory::XValue)
				copy_move = find_copy_move_constructor(type, false);
			if (copy_move != NULL)
			{
				vector<const Node*> args;
				args.push_back(&init);
				lower_constructor_call(addr_for, copy_move, args);
				return;
			}
			Value target = addr_for();
			string source = (init.category == ValueCategory::LValue ||
			                 init.category == ValueCategory::XValue)
				? ensure_pointer(emit_lvalue_addr(init)).text
				: emit_rvalue(init).text;
			if (record_has_storage_copy(type))
				instr("copyobj " + to_string(pa11::type_size(type)) +
				      "x" + to_string(pa11::type_align(type)) + " " +
				      source + ", " + target.text);
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
	Value raw = emit_rvalue(init);
	Value value = convert_value(raw, init.type, type);
	bool unsigned_i64_widen =
		scalar_lowir_type(type) == "i64" &&
		is_unsigned_type(type) &&
		pa11::type_size(init.type) < pa11::type_size(type);
	if (value.text == raw.text &&
	    !raw.text.empty() && raw.text[0] != '%' &&
	    raw.text[0] != '$' && raw.text[0] != '@' &&
	    pa11::is_integral_or_bool_type(init.type) &&
	    pa11::is_integral_or_bool_type(type) &&
	    unsigned_i64_widen)
	{
		string src = scalar_lowir_type(strip_for_value(init.type));
		string dst = scalar_lowir_type(type);
		string tmp = fresh_temp();
		string op = is_unsigned_type(init.type) ? "zext" : "sext";
		instr(tmp + " = convert " + op + " " + dst + " " + src + " " +
		      raw.text);
		value = Value(dst, tmp);
	}
	Value addr = addr_for();
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


}  // namespace internal
}  // namespace pa14
