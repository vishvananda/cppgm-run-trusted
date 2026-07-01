#include "pa14_lowir_internal.h"
#include "pa14_lowir_function_internal.h"
#include "pa12_expr_semantics_support.h"
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
bool zero_argument_constructor_prvalue(const Node& node)
{
	if (node.direct_call == NULL ||
	    !is_class_constructor_binding(node.direct_call))
		return false;
	if (node.children.empty())
		return true;
	return node.children.size() == 1 &&
	       starts_with(node.children[0].line, "callee ");
}
bool should_zero_before_value_constructor(Binding* ctor,
                                          TypePtr type,
                                          bool lowering_record_return_object)
{
	if (ctor == NULL)
		return false;
	const bool noop_generated =
		ctor->is_generated_default_constructor &&
		no_op_generated_default_constructor(ctor, type);
	if ((ctor->is_generated_default_constructor && !noop_generated) ||
	    ctor->is_defaulted)
		return true;
	if (!noop_generated || lowering_record_return_object)
		return false;
	TypePtr bare = type.get() != NULL ? pa11::strip_cv(type) : TypePtr();
	return bare.get() != NULL && bare->kind == TypeKind::Record;
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
	vector<TypePtr> bases = pa11::record_direct_bases(bare);
	for (size_t i = 0; i < bases.size(); ++i)
		if (type_contains_enum(bases[i]))
			return true;
	for (size_t i = 0; i < bare->fields.size(); ++i)
		if (type_contains_enum(bare->fields[i]->type))
			return true;
	return false;
}
string template_family_name(TypePtr record)
{
	TypePtr bare = record.get() != NULL ? pa11::strip_cv(record) : TypePtr();
	return bare.get() == NULL
		? ""
		: (bare->template_primary_name.empty()
		   ? bare->name
		   : bare->template_primary_name);
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
bool same_record_object_type(TypePtr left, TypePtr right)
{
	TypePtr l = left.get() != NULL ? pa11::strip_cv(left) : TypePtr();
	TypePtr r = right.get() != NULL ? pa11::strip_cv(right) : TypePtr();
	return l.get() != NULL &&
	       r.get() != NULL &&
	       l->kind == TypeKind::Record &&
	       r->kind == TypeKind::Record &&
	       (pa11::same_type(l, r) ||
	        pa12::internal::same_template_specialization_record(l, r));
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
		    !is_class_constructor_binding(binding) ||
		    binding->type.get() == NULL ||
		    binding->type->kind != TypeKind::Function ||
		    binding->type->parameters.size() != 2 ||
		    binding->is_generated_copy_move_constructor ||
		    function_signature_has_unresolved_storage(binding) ||
		    type_contains_template_symbol_pattern(binding->type) ||
		    type_contains_template_symbol_pattern(
			    class_record_for_member(binding)))
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

bool FunctionLowerer::lower_value_constructor_prvalue_same_type_init(
	const function<Value()>& addr_for,
	TypePtr type,
	const Node& init,
	bool returned_prvalue)
{
	if (!returned_prvalue ||
	    !zero_argument_constructor_prvalue(init) ||
	    (!init.direct_call->is_generated_default_constructor &&
	     !init.direct_call->is_defaulted))
		return false;
	Value target = addr_for();
	const bool noop_generated =
		init.direct_call->is_generated_default_constructor &&
		no_op_generated_default_constructor(init.direct_call, type);
	if (should_zero_before_value_constructor(
		    init.direct_call,
		    type,
		    lowering_record_return_object_) &&
	    zero_init_has_store(type))
		lower_storage_zero(target, pa11::type_size(type));
	if (noop_generated)
		demand_suppressed_default_init_subobjects(program_, type);
	function<Value()> same_addr = [target]() {
		return target;
	};
	vector<const Node*> args;
	lower_constructor_call(same_addr, init.direct_call, args);
	return true;
}

bool FunctionLowerer::lower_reference_prvalue_same_type_init(
	const function<Value()>& addr_for,
	const Node& init,
	bool returned_prvalue)
{
	if (!returned_prvalue ||
	    !is_reference(init.type) ||
	    init.direct_call == NULL ||
	    !is_class_constructor_binding(init.direct_call))
		return false;
	vector<const Node*> args;
	size_t first_arg = 0;
	if (!init.children.empty() && starts_with(init.children[0].line, "callee"))
		first_arg = 1;
	for (size_t i = first_arg; i < init.children.size(); ++i)
		args.push_back(&init.children[i]);
	lower_constructor_call(addr_for, init.direct_call, args);
	return true;
}

bool FunctionLowerer::lower_operator_plus_same_type_init(
	const function<Value()>& addr_for,
	TypePtr type,
	const Node& init,
	bool returned_prvalue)
{
	if (record_has_storage_copy(type) ||
	    !returned_prvalue ||
	    type_needs_cleanup(type) ||
	    init.direct_call == NULL ||
	    init.direct_call->name != "operator+")
		return false;
	demand_record_return_calls(program_, init);
	demand_string_literals(program_, init);
	addr_for();
	return true;
}

Binding* FunctionLowerer::same_type_copy_move_constructor(
	TypePtr type,
	TypePtr src_record,
	TypePtr dst_record,
	const Node& init,
	bool& enum_return_copy_move)
{
	enum_return_copy_move = false;
	Binding* copy_move =
		(init.category == ValueCategory::LValue ||
		 init.category == ValueCategory::XValue)
		? find_copy_move_constructor(type,
		                             init.category == ValueCategory::XValue)
		: NULL;
	if (copy_move == NULL && init.category == ValueCategory::XValue)
		copy_move = find_copy_move_constructor(type, false);
	if (copy_move == NULL && dst_record->is_template_specialization &&
	    init.category == ValueCategory::LValue)
		copy_move = find_existing_template_family_constructor(program_, type,
		                                                      init.type,
		                                                      false);
	if (copy_move == NULL && dst_record->is_template_specialization &&
	    init.category == ValueCategory::LValue)
	{
		Binding* any = find_any_copy_move_constructor(type, false);
		if (any != NULL && !any->is_defaulted)
			copy_move = any;
	}
	if (copy_move == NULL && lowering_record_return_object_ &&
	    init.category == ValueCategory::XValue && type_contains_enum(type))
	{
		copy_move = find_any_copy_move_constructor(type, true);
		enum_return_copy_move = copy_move != NULL;
	}
	if (copy_move != NULL &&
	    (!program_.host_object_lowering || lowering_record_return_object_) &&
	    record_has_storage_copy(type) &&
	    !enum_return_copy_move &&
	    ((same_record_object_type(src_record, dst_record) &&
	      !record_has_nontrivial_value_transfer(type)) ||
	     function_signature_has_unresolved_storage(copy_move) ||
	     type_contains_template_symbol_pattern(copy_move->type) ||
	     type_contains_template_symbol_pattern(class_record_for_member(copy_move))))
		copy_move = NULL;
	return copy_move;
}

bool FunctionLowerer::lower_copy_move_same_type_init(
	const function<Value()>& addr_for,
	TypePtr type,
	TypePtr src_record,
	TypePtr dst_record,
	const Node& init)
{
	bool enum_return_copy_move = false;
	Binding* copy_move = same_type_copy_move_constructor(type,
	                                                     src_record,
	                                                     dst_record,
	                                                     init,
	                                                     enum_return_copy_move);
	if (copy_move == NULL)
		return false;
	vector<const Node*> args;
	args.push_back(&init);
	lower_constructor_call(addr_for, copy_move, args);
	return true;
}

bool FunctionLowerer::lower_direct_same_type_storage_init(
	const function<Value()>& addr_for,
	TypePtr type,
	const Node& init,
	bool returned_prvalue)
{
	Value target = addr_for();
	bool saved_call_result_store_consumed = call_result_store_consumed_;
	if (returned_prvalue)
		call_result_store_consumed_ = false;
	bool protect_call =
		returned_prvalue &&
		eh_try_depth_ == 0 &&
		has_active_call_protection_cleanups() &&
		starts_with(init.line, "call-expression");
	if (protect_call)
	{
		call_result_store_addr_ = target.text;
		call_result_store_type_ = type;
		call_result_store_expr_ = &init;
		call_result_store_consumed_ = false;
	}
	string protected_dispatch;
	string protected_done;
	bool protected_define_dispatch = false;
	if (protect_call)
	{
		protected_dispatch = active_unwind_dispatch_.empty()
			? fresh_block("call_unwind_dispatch")
			: active_unwind_dispatch_;
		protected_define_dispatch = active_unwind_dispatch_.empty();
		instr("eh_try ^" + protected_dispatch);
		++eh_try_depth_;
	}
		string source = (init.category == ValueCategory::LValue ||
		                 init.category == ValueCategory::XValue)
			? ensure_pointer(emit_lvalue_addr(init)).text
			: emit_rvalue(init).text;
		if (!call_result_store_consumed_ &&
		    (record_has_storage_copy(type) || returned_prvalue))
		{
			instr("copyobj " + to_string(pa11::type_size(type)) + "x" +
			      to_string(pa11::type_align(type)) + " " + source + ", " +
			      target.text);
			call_result_store_consumed_ = true;
		}
		if (protect_call && current_ != NULL && !current_->terminated)
		{
			--eh_try_depth_;
		instr("eh_end");
		if (protected_define_dispatch)
		{
			protected_done = fresh_block("call_unwind_end");
				terminate("jump ^" + protected_done);
				active_unwind_dispatch_ = protected_dispatch;
				active_unwind_cleanup_depth_ = cleanups_.size();
				start_block(protected_dispatch);
			emit_shared_unwind_dispatch_body();
			start_block(protected_done);
		}
	}
	if (protect_call)
	{
		call_result_store_addr_.clear();
		call_result_store_type_.reset();
		call_result_store_expr_ = NULL;
	}
	call_result_store_consumed_ = saved_call_result_store_consumed;
	return true;
}

bool FunctionLowerer::lower_record_same_type_init(
	const function<Value()>& addr_for,
	TypePtr type,
	const Node& init)
{
	if (init.type.get() == NULL)
		return false;
	TypePtr src_record = pa11::strip_cv(object_type(init.type));
	TypePtr dst_record = pa11::strip_cv(type);
	bool returned_prvalue =
		init.category == ValueCategory::PRValue &&
		starts_with(init.line, "call-expression");
	bool unresolved_direct_copy =
		init.direct_call != NULL &&
		(function_signature_has_unresolved_storage(init.direct_call) ||
		 type_contains_template_symbol_pattern(init.direct_call->type) ||
		 type_contains_template_symbol_pattern(
			 class_record_for_member(init.direct_call)));
	bool compatible_template_family_copy =
		same_template_family(src_record, dst_record) &&
		pa11::type_size(src_record) == pa11::type_size(dst_record) &&
		pa11::type_align(src_record) == pa11::type_align(dst_record) &&
		(unresolved_direct_copy ||
		 (!program_.host_object_lowering && returned_prvalue));
	if (!same_record_object_type(src_record, dst_record) &&
	    !compatible_template_family_copy)
		return false;
	if (lower_value_constructor_prvalue_same_type_init(
		    addr_for, type, init, returned_prvalue))
		return true;
	if (lower_reference_prvalue_same_type_init(addr_for, init, returned_prvalue))
		return true;
	if (lower_operator_plus_same_type_init(
		    addr_for, type, init, returned_prvalue))
		return true;
	if (lower_copy_move_same_type_init(
		    addr_for, type, src_record, dst_record, init))
		return true;
	return lower_direct_same_type_storage_init(
		addr_for, type, init, returned_prvalue);
}

}  // namespace internal
}  // namespace pa14
