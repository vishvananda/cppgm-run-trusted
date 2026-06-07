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

void demand_string_literals(ProgramLowerer& program, const Node& node)
{
	if (starts_with(node.line, "literal lvalue") &&
	    !node.token_text.empty() &&
	    node.token_text[node.token_text.size() - 1] == '"')
		program.string_symbol(node.token_text);
	for (size_t i = 0; i < node.children.size(); ++i)
		demand_string_literals(program, node.children[i]);
}

bool is_no_op_generated_default_prvalue(const Node& node, TypePtr type)
{
	if (type.get() == NULL || node.type.get() == NULL)
		return false;
	TypePtr target = pa11::strip_cv(type);
	TypePtr source = pa11::strip_cv(object_type(node.type));
	return node.category == ValueCategory::PRValue &&
	       target->kind == TypeKind::Record &&
	       source.get() != NULL &&
	       pa11::same_type(target, source) &&
	       no_op_generated_default_constructor(node.direct_call, type);
}

bool type_contains_enum(TypePtr type)
{
	TypePtr bare = type.get() != NULL ? pa11::strip_cv(type) : TypePtr();
	if (bare.get() == NULL)
		return false;
	if (bare->kind == TypeKind::Array)
		return type_contains_enum(bare->base);
	if (bare->kind == TypeKind::Enum)
		return true;
	if (bare->kind != TypeKind::Record)
		return false;
	pa11::layout_record_type(bare);
	if (bare->base.get() != NULL && type_contains_enum(bare->base))
		return true;
	for (size_t i = 0; i < bare->fields.size(); ++i)
		if (type_contains_enum(bare->fields[i]->type))
			return true;
	return false;
}

string template_family_name(TypePtr record)
{
	TypePtr bare = record.get() != NULL ? pa11::strip_cv(record) : TypePtr();
	if (bare.get() == NULL)
		return "";
	return bare->template_primary_name.empty()
		? bare->name : bare->template_primary_name;
}

bool same_template_family(TypePtr left, TypePtr right)
{
	TypePtr l = left.get() != NULL ? pa11::strip_cv(left) : TypePtr();
	TypePtr r = right.get() != NULL ? pa11::strip_cv(right) : TypePtr();
	return l.get() != NULL &&
	       r.get() != NULL &&
	       l->kind == TypeKind::Record &&
	       r->kind == TypeKind::Record &&
	       l->is_template_specialization &&
	       r->is_template_specialization &&
	       template_family_name(l) == template_family_name(r);
}

bool function_template_specialization_binding(const Binding* binding)
{
	return binding != NULL &&
	       (!binding->function_specialization_symbol.empty() ||
	        (binding->aliased_binding != NULL &&
	         !binding->aliased_binding->function_specialization_symbol.empty()));
}

Binding* find_existing_template_family_constructor(ProgramLowerer& program,
                                                   TypePtr target,
                                                   TypePtr source,
                                                   bool move)
{
	TypePtr target_record = pa11::strip_cv(target);
	TypePtr source_record = pa11::strip_cv(source);
	Binding* best = NULL;
	size_t best_rank = static_cast<size_t>(-1);
	for (map<const Binding*, const Node*>::const_iterator it =
		     program.inline_definitions.begin();
	     it != program.inline_definitions.end();
	     ++it)
	{
		const Binding* binding = it->first;
		if (!function_template_specialization_binding(binding) ||
		    binding->kind != BindingKind::Function ||
		    binding->type.get() == NULL ||
		    binding->type->kind != TypeKind::Function ||
		    binding->type->parameters.size() != 2 ||
		    binding->is_generated_copy_move_constructor)
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
		TypePtr owner_record = class_record_for_member(binding);
		if (param_record->kind != TypeKind::Record ||
		    !pa11::same_type(param_record, source_record) ||
		    !same_template_family(owner_record, target_record))
			continue;
		map<const Binding*, size_t>::const_iterator rank_it =
			program.inline_definition_ranks.find(binding);
		size_t rank = rank_it == program.inline_definition_ranks.end()
			? static_cast<size_t>(-1) : rank_it->second;
		if (best == NULL || rank < best_rank)
		{
			best = const_cast<Binding*>(binding);
			best_rank = rank;
		}
	}
	return best;
}

}  // namespace

void FunctionLowerer::lower_aggregate_init(const function<Value()>& addr_for,
                                           TypePtr type,
                                           const Node& init)
{
	TypePtr closure_record = pa11::strip_cv(type);
	bool lambda_closure_type =
		closure_record.get() != NULL &&
		closure_record->kind == TypeKind::Record &&
		closure_record->scope != NULL &&
		closure_record->scope->name.compare(0, 8, "__lambda") == 0;
	if (init.token_text == "lambda-closure" || lambda_closure_type)
	{
		TypePtr bare = closure_record;
		if (bare->kind == TypeKind::Record)
		{
			pa11::layout_record_type(bare);
			for (size_t i = 0; i < bare->fields.size(); ++i)
			{
				Binding* field = bare->fields[i];
				function<Value()> field_addr = [this, addr_for, field]() {
					Value base = addr_for();
					if (field->member_offset == 0)
						return base;
					string addr = fresh_temp();
					instr(addr + " = index i8 [projection=field] " +
					      base.text + ", " +
					      to_string(field->member_offset));
					return Value("ptr", addr);
				};
				if (i < init.children.size())
				{
					(void)field_addr();
					lower_object_init(field_addr,
					                  field->type,
					                  init.children[i]);
				}
				else
					lower_zero_init(field_addr, field->type);
			}
			return;
		}
	}
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
		Value target = elem_addr();
		function<Value()> target_addr = [target]() {
			return target;
		};
		if (is_brace_elision_aggregate(elem) &&
		    !starts_with(child.line, "braced-init-list"))
			lower_aggregate_elements(target_addr, elem, init.children, clause);
		else
			lower_object_init(target_addr, elem, init.children[clause++]);
	}
}

void FunctionLowerer::lower_aggregate_elements(const function<Value()>& addr_for,
                                               TypePtr type,
                                               const vector<Node>& clauses,
                                               size_t& index)
{
	TypePtr bare = pa11::strip_cv(type);
	struct DestinationFlagGuard
	{
		FunctionLowerer* self;
		bool saved;
		explicit DestinationFlagGuard(FunctionLowerer* s)
			: self(s), saved(s->constructor_destination_before_protected_try_)
		{
			self->constructor_destination_before_protected_try_ = false;
		}
		~DestinationFlagGuard()
		{
			self->constructor_destination_before_protected_try_ = saved;
		}
	} destination_guard(this);
	if (bare->kind == TypeKind::Record)
{ pa11::layout_record_type(bare); if (bare->tag == "union") { if (bare->fields.empty()) return; Binding* field = bare->fields[0]; function<Value()> field_addr = [this, addr_for, field]() { Value base = addr_for();
string addr = fresh_temp(); instr(addr + " = index i8 [projection=field] " + base.text + ", " + to_string(field->member_offset)); return Value("ptr", addr); }; if (index >= clauses.size())
lower_zero_init(field_addr, field->type); else { bool saved_array_subobject = lowering_array_subobject_init_; if (pa11::strip_cv(field->type)->kind == TypeKind::Array) lowering_array_subobject_init_ = true;
lower_object_init(field_addr, field->type, clauses[index++]); lowering_array_subobject_init_ = saved_array_subobject; } return; } if (bare->base.get() != NULL) { function<Value()> base_addr = [this, addr_for, bare]() {
Value base = addr_for(); return emit_base_subobject_addr(base, bare, bare->base); }; if (index >= clauses.size()) lower_base_zero_init(addr_for, bare, bare->base); else { const Node& child = clauses[index];
if (same_record_initializer(child, bare->base)) lower_object_init(base_addr, bare->base, clauses[index++]); else if (is_brace_elision_aggregate(bare->base) && !starts_with(child.line, "braced-init-list"))
lower_aggregate_elements(base_addr, bare->base, clauses, index); else lower_object_init(base_addr, bare->base, clauses[index++]); } } for (size_t i = 0; i < bare->fields.size(); ++i) { Binding* field = bare->fields[i];
	function<Value()> field_addr = [this, addr_for, field]() { Value base = addr_for(); string addr = fresh_temp(); instr(addr + " = index i8 [projection=field] " + base.text + ", " + to_string(field->member_offset));
return Value("ptr", addr); }; if (index >= clauses.size()) { lower_zero_init(field_addr, field->type); continue; } const Node& child = clauses[index]; if (same_record_initializer(child, field->type)) {
if (is_no_op_generated_default_prvalue(child, field->type)) { ++index; continue; } Binding* copy_move = NULL; if (child.category == ValueCategory::LValue || child.category == ValueCategory::XValue) {
copy_move = find_copy_move_constructor(field->type, child.category == ValueCategory::XValue); if (copy_move == NULL && child.category == ValueCategory::XValue) copy_move = find_copy_move_constructor(field->type, false); }
if (!record_has_storage_copy(field->type) && (child.category == ValueCategory::LValue || child.category == ValueCategory::XValue) && copy_move == NULL) {
(void)field_addr(); ++index; continue; } lower_object_init(field_addr, field->type, clauses[index++]); } else if (is_brace_elision_aggregate(field->type) && !starts_with(child.line, "braced-init-list")) {
bool saved_array_subobject = lowering_array_subobject_init_; if (pa11::strip_cv(field->type)->kind == TypeKind::Array) lowering_array_subobject_init_ = true;
lower_aggregate_elements(field_addr, field->type, clauses, index); lowering_array_subobject_init_ = saved_array_subobject; } else if (field->is_bit_field) { Value value = convert_value(emit_rvalue(child), child.type,
field->type); string low_type = scalar_lowir_type(field->type); uint64_t mask = field->bit_width >= 64 ? ~uint64_t(0) : ((uint64_t(1) << field->bit_width) - 1); string masked = fresh_temp();
instr(masked + " = binary and " + low_type + " " + to_string(mask) + ", " + value.text); if (field->bit_offset != 0) { string shifted = fresh_temp(); instr(shifted + " = binary shl " + low_type + " " +
masked + ", " + to_string(field->bit_offset)); masked = shifted; } Value target = field_addr(); instr("store " + low_type + " " + masked + ", " + target.text); ++index; } else {
if (is_no_op_generated_default_prvalue(child, field->type)) { ++index; continue; } bool saved_array_subobject = lowering_array_subobject_init_; if (pa11::strip_cv(field->type)->kind == TypeKind::Array)
lowering_array_subobject_init_ = true; lower_object_init(field_addr, field->type, clauses[index++]); lowering_array_subobject_init_ = saved_array_subobject; } } return; }
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

bool FunctionLowerer::lower_braced_direct_constructor_init(
	const function<Value()>& addr_for,
	TypePtr type,
	const Node& init)
{
	if (init.direct_call == NULL)
		return false;
	if (init.direct_call->is_generated_aggregate_constructor &&
	    init.token_text != "force-constructor" &&
	    !pa11::type_has_const(type) &&
	    !type_has_reference_subobject(type) &&
	    !record_has_user_assignment_operator(type) &&
	    !binding_has_template_specialization_context(init.direct_call))
	{
		lower_aggregate_init(addr_for, type, init);
		return true;
	}
		if (inline_defaulted_copy_move_storage_constructor(init.direct_call,
		                                                   type,
		                                                   init))
		{
			if (binding_has_template_specialization_context(fn_.binding) &&
			    !init.direct_call->is_generated_copy_move_constructor)
				program_.demand_inline_function(init.direct_call);
			const Node& source_node = init.children[0];
			TypePtr source_object = object_type(source_node.type);
			Value target = addr_for();
		Value source;
		if (source_node.category == ValueCategory::LValue ||
		    source_node.category == ValueCategory::XValue)
			source = ensure_pointer(emit_lvalue_addr(source_node));
		else
		{
			string slot = fresh_aux_slot("tmpobj", scalar_lowir_type(source_object));
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
		return true;
	}
	if (init.children.empty() &&
	    (init.direct_call->is_generated_default_constructor ||
	     init.direct_call->is_defaulted))
	{
		Value addr = addr_for();
		if (init.direct_call->is_generated_default_constructor &&
		    !no_op_generated_default_constructor(init.direct_call, type) &&
		    zero_init_has_store(type))
			lower_storage_zero(addr, pa11::type_size(type));
		function<Value()> same_addr = [addr]() {
			return addr;
		};
		vector<const Node*> args;
		lower_constructor_call(same_addr, init.direct_call, args);
		return true;
	}
	for (size_t i = 0; i < init.children.size(); ++i)
		demand_record_return_calls(program_, init.children[i]);
	vector<const Node*> args;
	for (size_t i = 0; i < init.children.size(); ++i)
		args.push_back(&init.children[i]);
	lower_constructor_call(addr_for, init.direct_call, args);
	return true;
}

bool FunctionLowerer::lower_braced_record_constructor_init(
	const function<Value()>& addr_for,
	TypePtr type,
	const Node& init)
{
	if (pa11::strip_cv(type)->kind != TypeKind::Record)
		return false;
	Binding* ctor = find_constructor(type, init.children.size());
	if (ctor != NULL && !init.children.empty())
	{
		if (ctor->is_generated_aggregate_constructor &&
		    !pa11::type_has_const(type) &&
		    (!lowering_record_return_object_ ||
		     !type_has_reference_subobject(type)) &&
		    !record_has_user_assignment_operator(type))
		{
			lower_aggregate_init(addr_for, type, init);
			return true;
		}
		vector<const Node*> args;
		for (size_t i = 0; i < init.children.size(); ++i)
			args.push_back(&init.children[i]);
		lower_constructor_call(addr_for, ctor, args);
		return true;
	}
	if (ctor != NULL && init.children.empty() &&
	    (ctor->is_generated_default_constructor || ctor->is_defaulted))
	{
		Value addr = addr_for();
		if (ctor->is_generated_default_constructor &&
		    !no_op_generated_default_constructor(ctor, type) &&
		    zero_init_has_store(type))
			lower_storage_zero(addr, pa11::type_size(type));
		function<Value()> same_addr = [addr]() {
			return addr;
		};
		vector<const Node*> args;
		lower_constructor_call(same_addr, ctor, args);
		return true;
	}
	if (ctor != NULL && init.children.empty())
	{
		vector<const Node*> args;
		lower_constructor_call(addr_for, ctor, args);
		return true;
	}
	return false;
}

bool FunctionLowerer::lower_braced_object_init(const function<Value()>& addr_for,
                                               TypePtr type,
                                               const Node& init)
{
	if (lower_braced_direct_constructor_init(addr_for, type, init))
		return true;
	if (lower_braced_record_constructor_init(addr_for, type, init))
		return true;
	if (is_brace_elision_aggregate(type))
	{
		lower_aggregate_init(addr_for, type, init);
		return true;
	}
	if (pa11::strip_cv(type)->kind == TypeKind::Record)
		throw runtime_error("no matching constructor for " +
		                    pa11::describe_type(type) + " from " +
		                    init.line);
	if (init.children.empty())
	{
		lower_zero_init(addr_for, type);
		return true;
	}
	lower_object_init(addr_for, type, init.children[0]);
	return true;
}

void FunctionLowerer::lower_object_init(const function<Value()>& addr_for,
                                        TypePtr type,
                                        const Node& init)
{
	if (starts_with(init.line, "braced-init-list"))
	{
		lower_braced_object_init(addr_for, type, init);
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
				string base =
					emit_base_subobject_addr(source,
					                         src_record,
					                         dst_record).text;
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
					throw runtime_error("no matching constructor for " +
					                    pa11::describe_type(type) +
					                    " from " + init.line);
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
			bool returned_prvalue =
				init.category == ValueCategory::PRValue &&
				starts_with(init.line, "call-expression");
			if (!record_has_storage_copy(type) &&
			    returned_prvalue &&
			    !type_needs_cleanup(type) &&
			    init.direct_call != NULL &&
			    init.direct_call->name == "operator+")
			{
				demand_record_return_calls(program_, init);
				demand_string_literals(program_, init);
				addr_for();
				return;
			}
			Binding* copy_move =
				(init.category == ValueCategory::LValue ||
				 init.category == ValueCategory::XValue)
				? find_copy_move_constructor(
					type,
					init.category == ValueCategory::XValue)
				: NULL;
			if (copy_move == NULL && init.category == ValueCategory::XValue)
				copy_move = find_copy_move_constructor(type, false);
			if (copy_move == NULL &&
			    dst_record->is_template_specialization &&
			    init.category == ValueCategory::LValue)
				copy_move =
					find_existing_template_family_constructor(program_,
					                                          type,
					                                          init.type,
					                                          false);
			if (copy_move == NULL &&
			    dst_record->is_template_specialization &&
			    init.category == ValueCategory::LValue)
			{
				Binding* any = find_any_copy_move_constructor(type, false);
				if (any != NULL && !any->is_defaulted)
					copy_move = any;
			}
			if (copy_move == NULL &&
			    lowering_record_return_object_ &&
			    init.category == ValueCategory::XValue &&
			    type_contains_enum(type))
				copy_move = find_any_copy_move_constructor(type, true);
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
				if (record_has_storage_copy(type) || returned_prvalue)
					instr("copyobj " + to_string(pa11::type_size(type)) +
					      "x" + to_string(pa11::type_align(type)) + " " +
					      source + ", " + target.text);
				return;
			}
		Binding* ctor = find_constructor(type, 1);
		if (ctor == NULL)
			throw runtime_error("no matching constructor for " +
			                    pa11::describe_type(type) + " from " +
			                    init.line);
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
                                           TypePtr source,
                                           TypePtr type)
{
	TypePtr bare = pa11::strip_cv(type);
	function<Value()> base_addr = [this, addr_for, source, type]() {
		Value object = addr_for();
		uint64_t offset = base_subobject_offset(source, type);
		if (offset == 0)
			return object;
		string addr = fresh_temp();
		instr(addr + " = index i8 [projection=base_subobject] " +
		      object.text + ", " + to_string(offset));
		return Value("ptr", addr);
	};
	if (bare->kind != TypeKind::Record)
	{
		lower_zero_init(base_addr, type);
		return;
	}
	Binding* ctor = find_constructor(type, 0);
	if (ctor != NULL)
	{
		if (no_op_generated_default_constructor(ctor, type))
		{
			if (record_is_template_specialization(bare))
				base_addr();
			return;
		}
		vector<const Node*> args;
		lower_constructor_call(base_addr, ctor, args);
		return;
	}
	if (has_inline_constructor(type))
		throw runtime_error("no default constructor");
	pa11::layout_record_type(bare);
	if (bare->base.get() != NULL)
		lower_base_zero_init(base_addr, bare, bare->base);
	for (size_t i = 0; i < bare->fields.size(); ++i)
	{
		Binding* field = bare->fields[i];
		function<Value()> field_addr = [this, base_addr, field]() {
			Value base = base_addr();
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
			{
				if (record_is_template_specialization(bare))
					addr_for();
				return;
			}
			vector<const Node*> args;
			lower_constructor_call(addr_for, ctor, args);
			return;
		}
		if (has_inline_constructor(type))
			throw runtime_error("no default constructor");
		pa11::layout_record_type(bare);
		if (bare->base.get() != NULL)
			lower_base_zero_init(addr_for, bare, bare->base);
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
