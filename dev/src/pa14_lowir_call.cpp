#include "pa14_lowir_internal.h"
#include "pa12_templates_function_support.h"

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

string function_template_specialization_symbol(const Binding* binding)
{
	if (binding == NULL)
		return string();
	if (!binding->function_specialization_symbol.empty())
		return binding->function_specialization_symbol;
	if (binding->aliased_binding != NULL)
		return binding->aliased_binding->function_specialization_symbol;
	return string();
}

bool function_template_specialization_call(const Binding* binding)
{
	return !function_template_specialization_symbol(binding).empty();
}

bool hosted_std_namespace_scope(const Scope* scope)
{
	for (const Scope* cur = scope; cur != NULL; cur = cur->parent)
		if (cur->kind == ScopeKind::Namespace && cur->name == "std")
			return true;
	return false;
}

bool hosted_make_shared_binding(const Binding* binding)
{
	return binding != NULL &&
	       binding->name == "make_shared" &&
	       binding->owner != NULL &&
	       hosted_std_namespace_scope(binding->owner);
}

bool hosted_shared_ptr_element(TypePtr type, TypePtr& element)
{
	TypePtr bare = type.get() != NULL ? pa11::strip_cv(type) : TypePtr();
	if (!hosted_shared_ptr_record(bare) ||
	    bare->template_arguments.empty() ||
	    bare->template_arguments[0].kind !=
		    pa11::TemplateInstanceArgumentKind::Type)
		return false;
	element = bare->template_arguments[0].type;
	return element.get() != NULL;
}

TypePtr normalized_value_type(TypePtr type)
{
	return type.get() != NULL ? pa11::strip_cv(strip_for_value(type)) :
		TypePtr();
}

bool same_unqualified_type(TypePtr left, TypePtr right)
{
	return left.get() != NULL &&
	       right.get() != NULL &&
	       pa11::same_type(pa11::strip_cv(left), pa11::strip_cv(right));
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

bool hosted_basic_string_record(TypePtr type)
{
	TypePtr bare = type.get() != NULL ? pa11::strip_cv(type) : TypePtr();
	if (bare.get() == NULL ||
	    bare->kind != TypeKind::Record ||
	    !bare->is_template_specialization ||
	    bare->scope == NULL ||
	    unqualified_template_primary_name(bare) != "basic_string")
		return false;
	return hosted_std_namespace_scope(bare->scope);
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

bool hosted_vector_bool_insert_aux_binding(const Binding* binding)
{
	return binding != NULL &&
	       binding->name == "_M_insert_aux" &&
	       hosted_vector_bool_record(class_record_for_member(binding));
}

bool literal_char_pointer_argument(const Node& arg)
{
	return !arg.token_text.empty() &&
	       arg.token_text[arg.token_text.size() - 1] == '"';
}

bool char_pointer_value_type(TypePtr type)
{
	TypePtr value = normalized_value_type(type);
	TypePtr pointee = value.get() != NULL &&
	                  value->kind == TypeKind::Pointer
		? pa11::strip_cv(value->base) : TypePtr();
	return pointee.get() != NULL &&
	       pointee->kind == TypeKind::Fundamental &&
	       pointee->fundamental == FT_CHAR;
}

Binding* find_basic_string_cstr_constructor(TypePtr type,
                                            TypePtr& allocator)
{
	TypePtr bare = type.get() != NULL ? pa11::strip_cv(type) : TypePtr();
	if (!hosted_basic_string_record(bare) ||
	    bare->scope == NULL ||
	    bare->template_arguments.size() < 3 ||
	    bare->template_arguments[2].kind !=
		    pa11::TemplateInstanceArgumentKind::Type)
		return NULL;
	TypePtr alloc_arg = bare->template_arguments[2].type;
	map<string, vector<Binding*> >::const_iterator found =
		bare->scope->members.find(bare->scope->name);
	if (found == bare->scope->members.end())
		return NULL;
	for (size_t i = 0; i < found->second.size(); ++i)
	{
		Binding* binding = found->second[i];
		if (binding == NULL ||
		    binding->kind != BindingKind::Function ||
		    binding->type.get() == NULL ||
		    binding->type->kind != TypeKind::Function ||
		    binding->type->parameters.size() != 3 ||
		    !char_pointer_value_type(binding->type->parameters[1]) ||
		    !is_reference(binding->type->parameters[2]))
			continue;
		TypePtr param_alloc =
			pa11::strip_cv(binding->type->parameters[2]->base);
		if (!same_unqualified_type(param_alloc, alloc_arg))
			continue;
		allocator = param_alloc;
		return canonical_constructor_binding(binding);
	}
	return NULL;
}

int constructor_parameter_score(TypePtr param, const Node& arg)
{
	TypePtr arg_type = substituted_expression_type(arg);
	TypePtr param_value =
		normalized_value_type(is_reference(param) ? param->base : param);
	TypePtr arg_value = normalized_value_type(arg_type);
	if (param_value.get() == NULL || arg_value.get() == NULL)
		return -1;
	if (same_unqualified_type(param_value, arg_value))
		return 100;
	if (param_value->kind == TypeKind::Pointer &&
	    arg_value->kind == TypeKind::Pointer &&
	    same_unqualified_type(param_value->base, arg_value->base))
		return 90;
	if (is_reference(param))
	{
		TypePtr param_object = pa11::strip_cv(param->base);
		TypePtr arg_object = pa11::strip_cv(object_type(arg_type));
		if (param_object.get() != NULL &&
		    arg_object.get() != NULL &&
		    param_object->kind == TypeKind::Record &&
		    arg_object->kind == TypeKind::Record &&
		    same_unqualified_type(param_object, arg_object))
			return 80;
		return -1;
	}
	return -1;
}

Binding* find_constructor_for_arguments(TypePtr type,
                                        const vector<const Node*>& args)
{
	TypePtr bare = type.get() != NULL ? pa11::strip_cv(type) : TypePtr();
	if (bare.get() == NULL ||
	    bare->kind != TypeKind::Record ||
	    bare->scope == NULL)
		return NULL;
	map<string, vector<Binding*> >::const_iterator found =
		bare->scope->members.find(bare->scope->name);
	if (found == bare->scope->members.end())
		return NULL;
	Binding* best = NULL;
	int best_score = -1;
	for (size_t i = 0; i < found->second.size(); ++i)
	{
		Binding* binding = found->second[i];
		if (binding == NULL ||
		    binding->kind != BindingKind::Function ||
		    binding->type.get() == NULL ||
		    binding->type->kind != TypeKind::Function ||
		    binding->type->parameters.size() != args.size() + 1)
			continue;
		int score = 0;
		bool viable = true;
		for (size_t j = 0; j < args.size(); ++j)
		{
			int part = constructor_parameter_score(
				binding->type->parameters[j + 1], *args[j]);
			if (part < 0)
			{
				viable = false;
				break;
			}
			score += part;
		}
		if (viable && score > best_score)
		{
			best = binding;
			best_score = score;
		}
	}
	return best != NULL ? canonical_constructor_binding(best) : NULL;
}

bool same_function_parameter_signature(TypePtr left, TypePtr right)
{
	if (left.get() == NULL || right.get() == NULL ||
	    left->kind != TypeKind::Function ||
	    right->kind != TypeKind::Function ||
	    left->parameters.size() != right->parameters.size() ||
	    left->variadic != right->variadic)
		return false;
	for (size_t i = 0; i < left->parameters.size(); ++i)
		if (!pa11::same_type(left->parameters[i], right->parameters[i]))
			return false;
	return true;
}

bool active_template_specialization_body_call(const ProgramLowerer& program,
                                              const Binding* direct)
{
	const Binding* active = program.active_inline_definition;
	if (active == NULL || direct == NULL)
		return false;
	if (active == direct ||
	    active->aliased_binding == direct ||
	    direct->aliased_binding == active)
		return true;
	string active_symbol = function_template_specialization_symbol(active);
	string direct_symbol = function_template_specialization_symbol(direct);
	return !active_symbol.empty() && active_symbol == direct_symbol;
}

Binding* retarget_template_self_call_to_ordinary_overload(
	const ProgramLowerer& program,
	Binding* direct)
{
	if (!active_template_specialization_body_call(program, direct) ||
	    !function_template_specialization_call(direct) ||
	    direct->owner == NULL ||
	    direct->owner->kind != ScopeKind::Class ||
	    direct->type.get() == NULL ||
	    direct->type->kind != TypeKind::Function)
		return direct;
	map<string, vector<Binding*> >::const_iterator found =
		direct->owner->members.find(direct->name);
	if (found == direct->owner->members.end())
		return direct;
	for (size_t i = 0; i < found->second.size(); ++i)
	{
		Binding* candidate = found->second[i];
		if (candidate == NULL ||
		    candidate == direct ||
		    candidate->kind != BindingKind::Function ||
		    function_template_specialization_call(candidate) ||
		    candidate->type.get() == NULL ||
		    candidate->type->kind != TypeKind::Function ||
		    !same_function_parameter_signature(candidate->type,
		                                       direct->type))
			continue;
		return candidate;
	}
	return direct;
}

TypePtr call_type_from_expression(const Node& expr, size_t arg_start)
{
	if (expr.type.get() == NULL || expr.children.size() < arg_start)
		return TypePtr();
	vector<TypePtr> params;
	for (size_t i = arg_start; i < expr.children.size(); ++i)
	{
		if (expr.children[i].type.get() == NULL)
			return TypePtr();
		params.push_back(expr.children[i].type);
	}
	return pa11::make_function(expr.type, params, false);
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

bool type_contains_template_parameter(TypePtr type)
{
	if (type.get() == NULL)
		return false;
	TypePtr bare = pa11::strip_cv(type);
	if (bare->kind == TypeKind::TemplateParameter ||
	    bare->kind == TypeKind::TemplateTemplateParameter ||
	    bare->is_dependent_typename)
		return true;
	if (bare->kind == TypeKind::Pointer ||
	    bare->kind == TypeKind::LValueReference ||
	    bare->kind == TypeKind::RValueReference ||
	    bare->kind == TypeKind::Array)
		return type_contains_template_parameter(bare->base);
	if (bare->kind == TypeKind::MemberPointer)
		return type_contains_template_parameter(bare->member_class) ||
		       type_contains_template_parameter(bare->base);
	if (bare->kind == TypeKind::Function)
	{
		if (type_contains_template_parameter(bare->base))
			return true;
		for (size_t i = 0; i < bare->parameters.size(); ++i)
			if (type_contains_template_parameter(bare->parameters[i]))
				return true;
	}
	if (bare->kind == TypeKind::Record && bare->is_template_specialization)
		for (size_t i = 0; i < bare->template_arguments.size(); ++i)
		{
			const pa11::TemplateInstanceArgument& arg =
				bare->template_arguments[i];
			if (arg.kind == pa11::TemplateInstanceArgumentKind::Type &&
			    type_contains_template_parameter(arg.type))
				return true;
			if (arg.kind == pa11::TemplateInstanceArgumentKind::Pack)
				for (size_t j = 0; j < arg.pack.size(); ++j)
					if (arg.pack[j].kind ==
						    pa11::TemplateInstanceArgumentKind::Type &&
					    type_contains_template_parameter(arg.pack[j].type))
						return true;
		}
	return false;
}

TypePtr member_this_record_from_argument(const Node& arg)
{
	TypePtr type = substituted_expression_type(arg);
	TypePtr bare = type.get() != NULL ? pa11::strip_cv(type) : TypePtr();
	if (bare.get() != NULL && bare->kind == TypeKind::Pointer)
		bare = pa11::strip_cv(bare->base);
	else
		bare = pa11::strip_cv(object_type(type));
	return bare.get() != NULL && bare->kind == TypeKind::Record
		? bare : TypePtr();
}

	bool candidate_parameters_match_call(Binding* candidate, const Node& expr)
	{
	if (candidate == NULL ||
	    candidate->type.get() == NULL ||
	    candidate->type->kind != TypeKind::Function ||
	    candidate->type->parameters.size() + 1 != expr.children.size())
		return false;
	for (size_t i = 1; i < candidate->type->parameters.size(); ++i)
	{
		TypePtr param = object_type(candidate->type->parameters[i]);
		TypePtr arg = object_type(substituted_expression_type(expr.children[i + 1]));
		if (param.get() == NULL || arg.get() == NULL)
			return false;
		if (!pa11::same_type(pa11::strip_cv(param), pa11::strip_cv(arg)))
			return false;
	}
		return true;
	}

	bool call_operator_parameters_match(Binding* candidate, const Node& expr)
	{
		if (candidate == NULL ||
		    candidate->type.get() == NULL ||
		    candidate->type->kind != TypeKind::Function ||
		    candidate->type->parameters.size() != expr.children.size())
			return false;
		for (size_t i = 1; i < candidate->type->parameters.size(); ++i)
		{
			TypePtr param = object_type(candidate->type->parameters[i]);
			TypePtr arg = object_type(substituted_expression_type(expr.children[i]));
			if (param.get() == NULL || arg.get() == NULL)
				return false;
			if (!pa11::same_type(pa11::strip_cv(param), pa11::strip_cv(arg)))
				return false;
		}
		return true;
	}

	Binding* find_record_call_operator(TypePtr record, const Node& expr)
	{
		TypePtr bare = record.get() != NULL ? pa11::strip_cv(record) : TypePtr();
		if (bare.get() == NULL ||
		    bare->kind != TypeKind::Record ||
		    bare->scope == NULL)
			return NULL;
		map<string, vector<Binding*> >::const_iterator found =
			bare->scope->members.find("operator()");
		if (found == bare->scope->members.end())
			return NULL;
		Binding* best = NULL;
		int best_score = -1;
		for (size_t i = 0; i < found->second.size(); ++i)
		{
			Binding* candidate = found->second[i];
			if (candidate == NULL ||
			    candidate->kind != BindingKind::Function ||
			    candidate->is_static_member ||
			    !call_operator_parameters_match(candidate, expr))
				continue;
			int score = candidate->is_inline_definition ? 1 : 0;
			if (best == NULL || score > best_score)
			{
				best = candidate;
				best_score = score;
			}
		}
		return best;
	}

	Binding* addressed_function_callee(const Node& callee)
	{
		if (!callee.dependent_value_name.empty())
			return NULL;
		if (callee.binding != NULL &&
		    callee.binding->kind == BindingKind::Function)
			return callee.binding;
		if ((starts_with(callee.line, "unary-expression") ||
		     starts_with(callee.line, "cast-expression")) &&
		    callee.children.size() == 1)
			return addressed_function_callee(callee.children[0]);
		return NULL;
	}

	Binding* retarget_concrete_member_call(const Node& expr, Binding* direct)
	{
	if (direct == NULL ||
	    direct->owner == NULL ||
	    direct->owner->kind != ScopeKind::Class ||
	    direct->is_static_member ||
	    expr.children.size() < 2)
		return direct;
	TypePtr object_record = member_this_record_from_argument(expr.children[1]);
	if (object_record.get() == NULL ||
	    object_record->scope == NULL ||
	    type_contains_template_parameter(object_record))
		return direct;
	TypePtr direct_record = class_record_for_member(direct);
	direct_record = direct_record.get() != NULL
		? pa11::strip_cv(direct_record) : TypePtr();
	if (direct_record.get() != NULL &&
	    pa11::same_type(direct_record, object_record) &&
	    !type_contains_template_parameter(direct->type))
		return direct;
	map<string, vector<Binding*> >::iterator found =
		object_record->scope->members.find(direct->name);
	if (found == object_record->scope->members.end())
		return direct;
	Binding* best = direct;
	int best_score = -1;
	for (size_t i = 0; i < found->second.size(); ++i)
	{
		Binding* candidate = found->second[i];
		if (candidate == NULL ||
		    candidate->kind != BindingKind::Function ||
		    candidate->is_static_member ||
		    candidate->name != direct->name ||
		    !candidate_parameters_match_call(candidate, expr))
			continue;
		int score = 0;
		if (!type_contains_template_parameter(candidate->type))
			score += 100;
		if (!candidate->function_specialization_symbol.empty())
			score += 50;
		if (candidate->is_inline_definition)
			score += 10;
		if (candidate == direct)
			score += 1;
		if (score > best_score)
		{
			best = candidate;
			best_score = score;
		}
	}
	if (best != NULL &&
	    best != direct &&
	    best_score >= 100 &&
	    best->aliased_binding == NULL)
	{
		Binding* alias = direct->aliased_binding != NULL
			? direct->aliased_binding : direct;
		if (alias != NULL &&
		    (alias->is_inline_definition || direct->is_inline_definition))
		{
			best->aliased_binding = alias;
			best->is_inline_definition = true;
		}
	}
	return best_score >= 100 ? best : direct;
}

bool virtual_call_signature_matches(Binding* wanted, Binding* candidate)
{
	if (wanted == NULL || candidate == NULL ||
	    wanted->type.get() == NULL || candidate->type.get() == NULL ||
	    wanted->type->kind != TypeKind::Function ||
	    candidate->type->kind != TypeKind::Function ||
	    wanted->name != candidate->name ||
	    wanted->type->parameters.size() != candidate->type->parameters.size())
		return false;
	for (size_t i = 0; i < wanted->type->parameters.size(); ++i)
		if (!pa11::same_type(pa11::strip_cv(wanted->type->parameters[i]),
		                     pa11::strip_cv(candidate->type->parameters[i])))
			return false;
	return true;
}

int resolved_virtual_slot_index(Binding* binding)
{
	if (binding == NULL)
		return -1;
	if (binding->virtual_slot_index >= 0)
		return binding->virtual_slot_index;
	if (!binding->is_virtual)
		return -1;
	TypePtr record = class_record_for_member(binding);
	record = record.get() != NULL ? pa11::strip_cv(record) : TypePtr();
	if (record.get() == NULL || record->kind != TypeKind::Record)
		return -1;
	pa11::layout_record_type(record);
	for (size_t i = 0; i < record->virtual_entries.size(); ++i)
	{
		Binding* candidate = record->virtual_entries[i].function;
		if (candidate == binding ||
		    virtual_call_signature_matches(binding, candidate))
			return static_cast<int>(i);
	}
	return -1;
}

bool is_string_literal_node(const Node& arg)
{
	return !arg.token_text.empty() &&
	       arg.token_text[arg.token_text.size() - 1] == '"';
}

bool can_emit_contextual_scalar_literal(const Node& arg,
                                        TypePtr arg_type,
                                        TypePtr target_type)
{
	if (!starts_with(arg.line, "literal ") || is_string_literal_node(arg))
		return false;
	if (pa12::internal::substituted_type_is_valid(arg_type))
		return false;
	return pa12::internal::substituted_type_is_valid(target_type);
}

Value contextual_scalar_literal_value(TypePtr target_type, const Node& arg)
{
	return Value(scalar_lowir_type(target_type),
	             lowir_literal(target_type, arg));
}

}  // namespace

void FunctionLowerer::lower_reference_call_argument(const Node& arg,
                                                    TypePtr param,
                                                    vector<string>& args,
                                                    vector<pair<Value, TypePtr> >* temp_cleanups)
{
	demand_record_return_calls(program_, arg);
	TypePtr arg_type = substituted_expression_type(arg);
	const Node* materialized = record_prvalue_child_for_xvalue(arg);
	if (materialized != NULL &&
	    pa11::strip_cv(param->base)->kind == TypeKind::Record)
	{
		TypePtr materialized_type = substituted_expression_type(*materialized);
		TypePtr object = pa11::strip_cv(object_type(materialized_type));
		TypePtr target = pa11::strip_cv(param->base);
		bool indirect_call_result =
			starts_with(materialized->line, "call-expression") &&
			record_return_by_address(materialized_type);
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
		if (temp_cleanups != NULL &&
		    (type_needs_cleanup(object) ||
		     (program_.native_lowering &&
		      type_has_generated_noop_destructor(object))))
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
		TypePtr from_ptr = pa11::make_pointer(object_type(arg_type));
		TypePtr to_ptr = pa11::make_pointer(param->base);
		args.push_back(convert_value(addr, from_ptr, to_ptr).text);
		return;
	}
	if (pa11::strip_cv(param->base)->kind == TypeKind::Record &&
	    pa11::strip_cv(object_type(arg_type))->kind == TypeKind::Record)
	{
		TypePtr object = pa11::strip_cv(object_type(arg_type));
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
		if (temp_cleanups != NULL &&
		    (type_needs_cleanup(object) ||
		     (program_.native_lowering &&
		      type_has_generated_noop_destructor(object))))
			temp_cleanups->push_back(make_pair(temp_addr, object));
		args.push_back(convert_value(temp_addr,
		                             pa11::make_pointer(object),
		                             pa11::make_pointer(param->base)).text);
		return;
	}
	string slot = fresh_aux_slot("refarg", scalar_lowir_type(param->base));
	Value raw;
	if (arg.binding != NULL && arg.binding->kind == BindingKind::Function)
		raw = ensure_pointer(emit_lvalue_addr(arg));
	else if (can_emit_contextual_scalar_literal(arg, arg_type, param->base))
		raw = contextual_scalar_literal_value(param->base, arg);
	else
		raw = emit_rvalue(arg);
	Value value = convert_value(raw, arg_type, param->base);
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
	if (temp_cleanups != NULL &&
	    ((object->is_polymorphic && type_needs_cleanup(object)) ||
	     (program_.native_lowering &&
	      type_has_generated_noop_destructor(object))))
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
		    (type_needs_cleanup(object_type(materialized->type)) ||
		     (program_.native_lowering &&
		      type_has_generated_noop_destructor(
			      object_type(materialized->type)))))
			return true;
		if (arg.category == ValueCategory::PRValue &&
		    pa11::strip_cv(param->base)->kind == TypeKind::Record &&
		    pa11::strip_cv(object_type(arg.type))->kind == TypeKind::Record &&
		    (type_needs_cleanup(object_type(arg.type)) ||
		     (program_.native_lowering &&
		      type_has_generated_noop_destructor(object_type(arg.type)))))
			return true;
	}
	if (bare_param->kind == TypeKind::Pointer &&
	    starts_with(arg.line, "unary-expression") &&
	    arg.has_op && arg.op == OP_AMP && !arg.children.empty() &&
	    arg.children[0].category != ValueCategory::LValue &&
	    pa11::strip_cv(object_type(arg.children[0].type))->kind ==
	    TypeKind::Record &&
	    (type_needs_cleanup(object_type(arg.children[0].type)) ||
	     (program_.native_lowering &&
	      type_has_generated_noop_destructor(
		      object_type(arg.children[0].type)))))
		return true;
	return false;
}

bool call_argument_needs_setup_cleanup_protection(const Node& arg,
                                                  TypePtr param,
                                                  bool include_generated_noop)
{
	TypePtr bare_param = pa11::strip_cv(param);
	if (is_reference(param))
	{
		const Node* materialized = record_prvalue_child_for_xvalue(arg);
		if (materialized != NULL &&
		    pa11::strip_cv(param->base)->kind == TypeKind::Record &&
		    (type_needs_destructor(object_type(materialized->type)) ||
		     (include_generated_noop &&
		      type_has_generated_noop_destructor(
			      object_type(materialized->type)))))
			return true;
		if (arg.category == ValueCategory::PRValue &&
		    pa11::strip_cv(param->base)->kind == TypeKind::Record &&
		    pa11::strip_cv(object_type(arg.type))->kind == TypeKind::Record &&
		    (type_needs_destructor(object_type(arg.type)) ||
		     (include_generated_noop &&
		      type_has_generated_noop_destructor(object_type(arg.type)))))
			return true;
	}
	if (bare_param->kind == TypeKind::Record &&
	    arg.category == ValueCategory::PRValue &&
	    pa11::strip_cv(object_type(arg.type))->kind == TypeKind::Record &&
	    (type_needs_destructor(object_type(arg.type)) ||
	     (include_generated_noop &&
	      type_has_generated_noop_destructor(object_type(arg.type)))))
		return true;
	if (bare_param->kind == TypeKind::Pointer &&
	    starts_with(arg.line, "unary-expression") &&
	    arg.has_op && arg.op == OP_AMP && !arg.children.empty() &&
	    arg.children[0].category != ValueCategory::LValue &&
	    pa11::strip_cv(object_type(arg.children[0].type))->kind ==
	    TypeKind::Record &&
	    (type_needs_destructor(object_type(arg.children[0].type)) ||
	     (include_generated_noop &&
	      type_has_generated_noop_destructor(
		      object_type(arg.children[0].type)))))
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
		if (call_argument_needs_setup_cleanup_protection(
			    expr.children[i],
			    param,
			    program_.native_lowering))
			return false;
	}
	return true;
}

void FunctionLowerer::lower_record_value_argument(const Node& arg,
                                                  TypePtr param,
                                                  vector<string>& args,
                                                  bool preserve_no_storage_lvalue)
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
	if (preserve_no_storage_lvalue &&
	    !record_has_storage_copy(param) &&
	    (arg.category == ValueCategory::LValue ||
	     arg.category == ValueCategory::XValue))
		ensure_pointer(emit_lvalue_addr(arg));
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
                                                vector<pair<Value, TypePtr> >* temp_cleanups,
                                                bool preserve_no_storage_lvalue)
{
	if (lower_temporary_record_pointer_argument(arg, param, args, temp_cleanups))
		return;
	TypePtr arg_type = substituted_expression_type(arg);
	if (pa11::strip_cv(param)->kind == TypeKind::Record)
	{
		lower_record_value_argument(arg,
		                            param,
		                            args,
		                            preserve_no_storage_lvalue);
		return;
		}
		TypePtr param_bare = pa11::strip_cv(param);
		if (param_bare->kind == TypeKind::Pointer &&
		    pa11::strip_cv(param_bare->base)->kind == TypeKind::Record &&
		    starts_with(arg.line, "unary-expression") &&
		    arg.has_op && arg.op == OP_AMP &&
		    !arg.children.empty())
		{
			TypePtr target = pa11::strip_cv(param_bare->base);
			TypePtr source = pa11::strip_cv(object_type(
				substituted_expression_type(arg.children[0])));
			if (source.get() != NULL &&
			    source->kind == TypeKind::Record &&
			    !pa11::same_type(source, target) &&
			    record_has_base_subobject(source, target))
			{
				bool found_hidden = false;
				TypePtr hidden_record;
				Value hidden =
					emit_hidden_virtual_base_addr_for_lvalue(
						arg.children[0], target, found_hidden,
						&hidden_record);
				if (found_hidden)
				{
					if (!pa11::same_type(pa11::strip_cv(hidden_record),
					                    target))
						hidden = emit_base_subobject_addr(hidden,
						                                  target,
						                                  target);
					args.push_back(hidden.text);
					return;
				}
			}
		}
		Value raw = can_emit_contextual_scalar_literal(arg, arg_type, param)
			? contextual_scalar_literal_value(param, arg)
			: emit_rvalue(arg);
		TypePtr arg_bare = pa11::strip_cv(arg_type);
		TypePtr arg_decl_bare = arg.binding != NULL
			? pa11::strip_cv(arg.binding->type) : arg_bare;
		if ((arg_decl_bare->kind == TypeKind::LValueReference ||
		     arg_decl_bare->kind == TypeKind::RValueReference) &&
		    pa11::strip_cv(arg_decl_bare->base)->kind == TypeKind::Pointer &&
		    param_bare->kind == TypeKind::Pointer)
		{
			TypePtr source_pointer = pa11::strip_cv(arg_decl_bare->base);
			TypePtr from_pointee = pa11::strip_cv(source_pointer->base);
			TypePtr to_pointee = pa11::strip_cv(param_bare->base);
			if (from_pointee->kind == TypeKind::Record &&
			    to_pointee->kind == TypeKind::Record &&
			    record_has_base_subobject(from_pointee, to_pointee))
			{
				uint64_t offset =
					base_subobject_offset(from_pointee, to_pointee);
				if (offset != 0)
				{
					string slot = fresh_aux_slot("basecast", "ptr");
					string is_null = fresh_temp();
					instr(is_null + " = cmp eq ptr " + raw.text + ", 0");
					string null_block = fresh_block("basecast_null");
					string adjust_block = fresh_block("basecast_adjust");
					string end_block = fresh_block("basecast_end");
					terminate("branch " + is_null + ", ^" + null_block +
					          ", ^" + adjust_block);
					start_block(null_block);
					instr("store ptr 0, $" + slot);
					terminate("jump ^" + end_block);
					start_block(adjust_block);
					string adjusted = fresh_temp();
					instr(adjusted + " = index i8 " + raw.text + ", " +
					      to_string(offset));
					instr("store ptr " + adjusted + ", $" + slot);
					terminate("jump ^" + end_block);
					start_block(end_block);
					string loaded = fresh_temp();
					instr(loaded + " = load ptr $" + slot);
					args.push_back(loaded);
					return;
				}
			}
		}
		Value converted = convert_binary_value(raw, arg_type, param);
		if (converted.type == "ptr" && converted.text == "0" &&
		    arg.token_text == "nullptr")
			converted.text = "nullptr";
		args.push_back(converted.text);
	}

void FunctionLowerer::lower_call_argument(const Node& arg,
                                          TypePtr param,
                                          vector<string>& args,
                                          vector<pair<Value, TypePtr> >* temp_cleanups,
                                          bool preserve_no_storage_lvalue)
{
	if (is_reference(param))
		lower_reference_call_argument(arg, param, args, temp_cleanups);
	else
		lower_value_call_argument(arg,
		                          param,
		                          args,
		                          temp_cleanups,
		                          preserve_no_storage_lvalue);
}

bool FunctionLowerer::lower_hosted_basic_string_cstr_init(
	const function<Value()>& addr_for,
	TypePtr type,
	const Node& arg)
{
	const Node* source = &arg;
	if (starts_with(arg.line, "cast-expression") &&
	    arg.children.size() == 1 &&
	    literal_char_pointer_argument(arg.children[0]))
		source = &arg.children[0];
	if (!literal_char_pointer_argument(*source))
		return false;
	TypePtr allocator;
	Binding* ctor = find_basic_string_cstr_constructor(type, allocator);
	if (ctor == NULL)
		return false;
	Value target = addr_for();
	string allocator_slot = fresh_aux_slot("stralloc",
	                                      slot_lowir_type(allocator));
	string allocator_addr_name = fresh_temp();
	instr(allocator_addr_name + " = addr $" + allocator_slot);
	Value allocator_addr("ptr", allocator_addr_name);
	function<Value()> allocator_addr_for = [allocator_addr]() {
		return allocator_addr;
	};
	lower_default_init(allocator_addr_for, allocator);
	vector<string> lowered;
	lowered.push_back(target.text);
	lower_call_argument(*source, ctor->type->parameters[1], lowered);
	lowered.push_back(allocator_addr.text);
	program_.demand_function_declaration(ctor);
	string callee = program_.symbol_for(ctor);
	ostringstream call;
	call << "call void @" << callee << "(";
	for (size_t i = 0; i < lowered.size(); ++i)
	{
		if (i != 0)
			call << ", ";
		call << lowered[i];
	}
	call << ")";
	instr(call.str());
	return true;
}

bool FunctionLowerer::lower_hosted_make_shared_call(
	const function<Value()>& addr_for,
	const Node& expr)
{
	TypePtr object;
	if (!starts_with(expr.line, "call-expression") ||
	    !hosted_make_shared_binding(expr.direct_call) ||
	    !hosted_shared_ptr_element(expr.type, object))
		return false;
	object = pa11::strip_cv(object);
	if (object.get() == NULL)
		return false;
	if (program_.declared_functions.insert("operator_new").second)
		program_.declares.push_back(
			"declare function @operator_new(%arg0 : i64) -> ptr "
			"[binding=strong, object=" +
			string(program_.native_lowering
			       ? "_Znwm" : "cppgm_builtin_operator_new") + "]");
	string size_tmp = fresh_temp();
	instr(size_tmp + " = convert sext i64 i32 " +
	      to_string(pa11::type_size(object)));
	string object_tmp = fresh_temp();
	instr(object_tmp + " = call ptr @operator_new(" + size_tmp + ")");
	Value object_addr("ptr", object_tmp);
	function<Value()> object_addr_for = [object_addr]() {
		return object_addr;
	};
	size_t argc = expr.children.empty() ? 0 : expr.children.size() - 1;
	if (object->kind == TypeKind::Record)
	{
		if (argc == 0)
			lower_default_init(object_addr_for, object);
		else if (argc == 1 &&
		         lower_hosted_basic_string_cstr_init(
			         object_addr_for, object, expr.children[1]))
		{
		}
		else
		{
			vector<const Node*> args;
			for (size_t i = 1; i < expr.children.size(); ++i)
				args.push_back(&expr.children[i]);
			Binding* ctor = find_constructor_for_arguments(object, args);
			if (ctor != NULL)
				lower_constructor_call(object_addr_for, ctor, args);
			else if (argc == 1)
				lower_object_init(object_addr_for, object,
				                  expr.children[1]);
			else
				throw runtime_error("no matching make_shared constructor");
		}
	}
	else
	{
		if (argc == 0)
			lower_zero_init(object_addr_for, object);
		else if (argc == 1)
			lower_scalar_object_init(object_addr_for, object,
			                         expr.children[1]);
		else
			throw runtime_error("too many make_shared scalar arguments");
	}
	Value target = addr_for();
	instr("store ptr " + object_addr.text + ", " + target.text);
	string control = fresh_temp();
	instr(control + " = index i8 [projection=field] " +
	      target.text + ", 8");
	instr("store ptr 0, " + control);
	return true;
}

bool FunctionLowerer::lower_indirect_record_call(const function<Value()>& addr_for,
                                                 const Node& expr)
{
	if (!starts_with(expr.line, "call-expression") ||
	    pa11::strip_cv(expr.type)->kind != TypeKind::Record)
		return false;
	if (lower_hosted_make_shared_call(addr_for, expr))
		return true;
	if (!record_return_by_address(expr.type))
		return false;
	CallEmissionState call_state;
	init_call_target(expr, call_state);
	string result_addr = addr_for().text;
	for (size_t i = 1; i < expr.children.size(); ++i)
	{
		bool variadic_extra =
			i - 1 >= call_state.callee_type->parameters.size();
		TypePtr param = !variadic_extra
			? call_state.callee_type->parameters[i - 1] : expr.children[i].type;
		if (variadic_extra && scalar_lowir_type(expr.children[i].type) == "f32")
			param = pa11::make_fundamental(FT_DOUBLE);
		lower_call_argument(expr.children[i], param, call_state.args);
	}
	append_hidden_call_arguments(expr, call_state);
	resolve_call_callee(expr, call_state);
	vector<string> args;
	args.push_back(result_addr);
	args.insert(args.end(), call_state.args.begin(), call_state.args.end());
	ostringstream call;
	call << "call void " << call_state.callee << "(";
	for (size_t i = 0; i < args.size(); ++i)
	{
		if (i != 0)
			call << ", ";
		call << args[i];
	}
	call << ")";
	if (call_state.direct == NULL || call_state.virtual_call)
	{
		call << " as (%ret : ptr [pass=indirect_result]";
		for (size_t i = 0; i < call_state.callee_type->parameters.size(); ++i)
			call << ", %arg" << i << " : " <<
				lowir_parameter(call_state.callee_type->parameters[i]);
		call << ") -> void";
	}
	instr(call.str());
	return true;
}

void FunctionLowerer::init_call_target(const Node& expr,
                                       CallEmissionState& call)
{
	call.direct = expr.direct_call;
	bool lambda_helper_call =
		call.direct != NULL &&
		call.direct->kind == BindingKind::Function &&
		call.direct->name.compare(0, 8, "__lambda") == 0;
	if (!lambda_helper_call && call.direct == NULL && !expr.children.empty())
	{
		call.direct = addressed_function_callee(expr.children[0]);
		lambda_helper_call =
			call.direct != NULL &&
			call.direct->kind == BindingKind::Function &&
			call.direct->name.compare(0, 8, "__lambda") == 0;
	}
	if (lambda_helper_call &&
	    !expr.children.empty() &&
	    expr.children[0].type.get() != NULL)
		call.direct = NULL;
	call.arg_start = 1;
	call.virtual_slot_index = resolved_virtual_slot_index(call.direct);
	bool inferred_virtual_call =
		call.direct != NULL &&
		call.virtual_slot_index >= 0 &&
		call.direct->owner != NULL &&
		call.direct->owner->kind == ScopeKind::Class &&
		!call.direct->is_static_member &&
		!is_class_constructor_binding(call.direct) &&
		!is_class_destructor_binding(call.direct) &&
		!expr.suppress_virtual_dispatch &&
		expr.children.size() > 1;
	call.virtual_call = call.direct != NULL &&
	                    (expr.virtual_dispatch || inferred_virtual_call) &&
	                    call.virtual_slot_index >= 0;
	call.delay_direct_demand =
		call.direct != NULL && call.direct->name == "operator=";
	if (call.direct != NULL)
		init_direct_call_target(expr, call);
	else
		init_indirect_call_target(expr, call);
	validate_call_target(expr, call);
	call.ret = scalar_lowir_type(call.callee_type->base);
}

void FunctionLowerer::init_direct_call_target(const Node& expr,
                                              CallEmissionState& call)
{
	call.direct = retarget_concrete_member_call(expr, call.direct);
	call.direct =
		retarget_template_self_call_to_ordinary_overload(program_,
		                                                 call.direct);
	call.callee_type = call.direct->type;
	if ((call.callee_type.get() == NULL ||
	     call.callee_type->kind != TypeKind::Function) &&
	    !expr.children.empty())
		call.callee_type = strip_for_value(expr.children[0].type);
	if (call.callee_type.get() == NULL ||
	    call.callee_type->kind != TypeKind::Function)
		call.callee_type = call_type_from_expression(expr, call.arg_start);
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
			? pa11::strip_cv(object_type(object_arg.type)) : TypePtr();
		if (object_arg.category != ValueCategory::LValue &&
		    object.get() != NULL && object->kind == TypeKind::Record)
			call.delay_direct_demand = true;
	}
	if (call.delay_direct_demand || call.virtual_call)
		return;
	TypePtr result_record =
		call.callee_type.get() != NULL &&
		call.callee_type->kind == TypeKind::Function &&
		call.callee_type->base.get() != NULL
		? pa11::strip_cv(call.callee_type->base) : TypePtr();
	if (result_record.get() != NULL &&
	    result_record->kind == TypeKind::Record &&
	    result_record->is_polymorphic)
		program_.demand_vtable(result_record);
	program_.demand_function_declaration(call.direct);
	program_.demand_inline_function(call.direct, true);
	call.callee = "@" + program_.symbol_for(call.direct);
}

void FunctionLowerer::init_indirect_call_target(const Node& expr,
                                                CallEmissionState& call)
{
	TypePtr callee_expr_type = !expr.children.empty()
		? substituted_expression_type(expr.children[0]) : TypePtr();
	TypePtr callee_object = callee_expr_type.get() != NULL
		? pa11::strip_cv(object_type(callee_expr_type)) : TypePtr();
	if (callee_object.get() != NULL && callee_object->kind == TypeKind::Record)
	{
		call.direct = find_record_call_operator(callee_object, expr);
		if (call.direct != NULL)
		{
			call.arg_start = 0;
			call.virtual_slot_index = resolved_virtual_slot_index(call.direct);
			call.virtual_call = false;
			call.delay_direct_demand = true;
			call.callee_type = call.direct->type;
		}
	}
	if (call.direct != NULL)
		return;
	call.callee_type = !expr.children.empty() &&
		expr.children[0].type.get() != NULL
		? strip_for_value(expr.children[0].type) : TypePtr();
	if (call.callee_type.get() != NULL &&
	    pa11::strip_cv(call.callee_type)->kind == TypeKind::Pointer)
		call.callee_type = pa11::strip_cv(call.callee_type)->base;
}

void FunctionLowerer::validate_call_target(const Node& expr,
                                           CallEmissionState& call)
{
	if (call.callee_type.get() != NULL &&
	    call.callee_type->kind == TypeKind::Function &&
	    call.callee_type->base.get() != NULL)
		return;
	string detail = expr.line;
	if (call.direct != NULL)
		detail += " direct " + call.direct->name;
	if (call.callee_type.get() != NULL)
		detail += " type " + pa11::describe_type(call.callee_type);
	for (size_t i = 0; i < expr.children.size(); ++i)
		detail += " child " + expr.children[i].line;
	throw runtime_error("invalid call target type: " + detail);
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
		    (type_needs_cleanup(object_type(arg.type)) ||
		     (program_.native_lowering &&
		      type_has_generated_noop_destructor(object_type(arg.type)))))
			cleanup_arg = true;
		TypePtr bare_param = pa11::strip_cv(param);
		if (!cleanup_arg && bare_param->kind == TypeKind::Pointer &&
		    starts_with(arg.line, "unary-expression") && arg.has_op &&
		    arg.op == OP_AMP && !arg.children.empty() &&
		    arg.children[0].category != ValueCategory::LValue)
		{
			TypePtr object =
				pa11::strip_cv(object_type(arg.children[0].type));
			if (object->kind == TypeKind::Record &&
			    ((object->is_polymorphic && type_needs_cleanup(object)) ||
			     (program_.native_lowering &&
			      type_has_generated_noop_destructor(object))))
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
				    expr.children[i],
				    param,
				    program_.native_lowering))
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
		bool protect_virtual_record_result =
			eh_try_depth_ == 0 && has_active_cleanups() &&
			call.virtual_call &&
			call.ret.compare(0, 4, "obj<") == 0 &&
			!call_result_store_addr_.empty();
		call.protected_setup =
			eh_try_depth_ == 0 && !call.protect_setup_only &&
			(protect_virtual_record_result ||
			 (has_active_cleanups() &&
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
		emit_active_catch_clauses();
		if (program_.native_lowering || !active_catches_.empty())
			instr("eh_cleanup");
		emit_unwind_cleanups();
	terminate_unwind_or_active_catch();
	start_block(end);
}



}  // namespace internal
}  // namespace pa14
