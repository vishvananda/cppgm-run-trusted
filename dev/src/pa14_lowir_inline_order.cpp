#include "pa14_lowir_internal.h"

#include <algorithm>

namespace pa14 {
namespace internal {
namespace {

bool function_definition_body_empty(const Node& node)
{
	return !node.children.empty() &&
	       starts_with(node.children.back().line, "compound-statement") &&
	       node.children.back().children.empty();
}

bool is_class_constructor(const Binding* binding)
{
	return binding != NULL &&
	       binding->owner != NULL &&
	       binding->owner->kind == ScopeKind::Class &&
	       binding->name == binding->owner->name;
}

bool is_lambda_related_function(const Binding* binding)
{
	if (binding == NULL)
		return false;
	if (binding->name.compare(0, 8, "__lambda") == 0)
		return true;
	return binding->owner != NULL &&
	       binding->owner->kind == ScopeKind::Class &&
	       binding->owner->name.compare(0, 8, "__lambda") == 0;
}

bool is_captureless_lambda_helper_function(const Binding* binding)
{
	return binding != NULL &&
	       binding->name.compare(0, 8, "__lambda") == 0;
}

bool is_lambda_call_operator_function(const Binding* binding)
{
	return binding != NULL &&
	       binding->owner != NULL &&
	       binding->owner->kind == ScopeKind::Class &&
	       binding->owner->name.compare(0, 8, "__lambda") == 0;
}

bool constructor_has_reference_parameter(const Binding* binding)
{
	if (!is_class_constructor(binding) ||
	    binding->type.get() == NULL ||
	    binding->type->kind != TypeKind::Function)
		return false;
	for (size_t i = 1; i < binding->type->parameters.size(); ++i)
		if (is_reference(binding->type->parameters[i]))
			return true;
	return false;
}

TypePtr function_record_result(const Binding* binding)
{
	if (binding == NULL ||
	    binding->type.get() == NULL ||
	    binding->type->kind != TypeKind::Function)
		return TypePtr();
	TypePtr result = pa11::strip_cv(binding->type->base);
	return result.get() != NULL && result->kind == TypeKind::Record
		? result
		: TypePtr();
}

bool function_returns_record(const Binding* binding)
{
	return function_record_result(binding).get() != NULL;
}

bool function_template_specialization_binding(const Binding* binding)
{
	return binding != NULL &&
	       (!binding->function_specialization_symbol.empty() ||
	        (binding->aliased_binding != NULL &&
	         !binding->aliased_binding->function_specialization_symbol.empty()));
}

bool template_argument_mentions_type(const pa11::TemplateInstanceArgument& argument,
                                     TypePtr type)
{
	type = type.get() != NULL ? pa11::strip_cv(type) : TypePtr();
	if (type.get() == NULL)
		return false;
	if (argument.kind == pa11::TemplateInstanceArgumentKind::Type)
	{
		TypePtr argument_type = argument.type.get() != NULL
			? pa11::strip_cv(argument.type) : TypePtr();
		return argument_type.get() != NULL &&
		       pa11::same_type(argument_type, type);
	}
	if (argument.kind == pa11::TemplateInstanceArgumentKind::Pack)
		for (size_t i = 0; i < argument.pack.size(); ++i)
			if (template_argument_mentions_type(argument.pack[i], type))
				return true;
	return false;
}

bool template_arguments_mention_type(
	const vector<pa11::TemplateInstanceArgument>& arguments, TypePtr type)
{
	for (size_t i = 0; i < arguments.size(); ++i)
		if (template_argument_mentions_type(arguments[i], type))
			return true;
	return false;
}

const Binding* first_base_default_constructor(const Binding* binding)
{
	if (binding == NULL || binding->name.empty() || binding->name[0] != '~' ||
	    binding->owner == NULL)
		return NULL;
	TypePtr record = pa11::record_type_for_scope(binding->owner);
	if (record.get() == NULL)
		return NULL;
	pa11::layout_record_type(record);
	if (!record->fields.empty())
		return NULL;
	for (TypePtr base = record->base; base.get() != NULL;
	     base = pa11::strip_cv(base)->base)
	{
		TypePtr bare = pa11::strip_cv(base);
		if (bare->kind != TypeKind::Record || bare->scope == NULL)
			return NULL;
		map<string, vector<Binding*> >::const_iterator found =
			bare->scope->members.find(bare->scope->name);
		if (found != bare->scope->members.end())
			for (size_t i = 0; i < found->second.size(); ++i)
				if (found->second[i]->kind == BindingKind::Function &&
				    found->second[i]->type->kind == TypeKind::Function &&
				    found->second[i]->type->parameters.size() == 1)
					return found->second[i];
	}
	return NULL;
}

bool constructor_has_no_explicit_parameters(const Binding* binding)
{
	return is_class_constructor(binding) &&
	       binding->type.get() != NULL &&
	       binding->type->kind == TypeKind::Function &&
	       binding->type->parameters.size() == 1;
}

bool constructor_has_record_parameter(TypePtr record, const Binding* binding)
{
	if (record.get() == NULL ||
	    !is_class_constructor(binding) ||
	    binding->type.get() == NULL ||
	    binding->type->kind != TypeKind::Function)
		return false;
	for (size_t i = 1; i < binding->type->parameters.size(); ++i)
	{
		TypePtr param = binding->type->parameters[i];
		if (param->kind == TypeKind::LValueReference ||
		    param->kind == TypeKind::RValueReference)
			param = param->base;
		param = pa11::strip_cv(param);
		if (param.get() != NULL &&
		    param->kind == TypeKind::Record &&
		    pa11::same_type(param, record))
			return true;
	}
	return false;
}

bool constructor_parameter_wraps_pending_parameter(TypePtr candidate,
                                                   TypePtr pending)
{
	candidate = pa11::strip_cv(object_type(candidate));
	pending = pa11::strip_cv(object_type(pending));
	if (candidate.get() == NULL ||
	    pending.get() == NULL ||
	    candidate->kind != TypeKind::Record ||
	    !candidate->is_template_specialization ||
	    pa11::same_type(candidate, pending))
		return false;
	return template_arguments_mention_type(candidate->template_arguments,
	                                       pending);
}

bool constructor_specialization_more_specific_than_pending(
	const Binding* binding, const Binding* pending)
{
	if (!is_class_constructor(binding) ||
	    !is_class_constructor(pending) ||
	    binding->owner != pending->owner ||
	    !function_template_specialization_binding(binding) ||
	    !function_template_specialization_binding(pending) ||
	    binding->type.get() == NULL ||
	    pending->type.get() == NULL ||
	    binding->type->kind != TypeKind::Function ||
	    pending->type->kind != TypeKind::Function ||
	    binding->type->parameters.size() != pending->type->parameters.size())
		return false;
	bool more_specific = false;
	for (size_t i = 1; i < binding->type->parameters.size(); ++i)
	{
		TypePtr candidate = pa11::strip_cv(
			object_type(binding->type->parameters[i]));
		TypePtr pending_param = pa11::strip_cv(
			object_type(pending->type->parameters[i]));
		if (candidate.get() != NULL &&
		    pending_param.get() != NULL &&
		    pa11::same_type(candidate, pending_param))
			continue;
		if (!constructor_parameter_wraps_pending_parameter(
			    binding->type->parameters[i], pending->type->parameters[i]))
			return false;
		more_specific = true;
	}
	return more_specific;
}

bool function_has_by_value_record_parameter(const Binding* binding,
                                            TypePtr record)
{
	if (binding == NULL ||
	    binding->type.get() == NULL ||
	    binding->type->kind != TypeKind::Function ||
	    record.get() == NULL)
		return false;
	for (size_t i = 0; i < binding->type->parameters.size(); ++i)
	{
		TypePtr param = pa11::strip_cv(binding->type->parameters[i]);
		if (param.get() != NULL &&
		    param->kind == TypeKind::Record &&
		    pa11::same_type(param, record))
			return true;
	}
	return false;
}

string record_template_family_name(TypePtr record)
{
	TypePtr bare = record.get() != NULL ? pa11::strip_cv(record) : TypePtr();
	if (bare.get() == NULL || bare->kind != TypeKind::Record)
		return "";
	return bare->template_primary_name.empty()
		? bare->name : bare->template_primary_name;
}

bool same_record_or_template_family(TypePtr left, TypePtr right)
{
	TypePtr l = left.get() != NULL ? pa11::strip_cv(left) : TypePtr();
	TypePtr r = right.get() != NULL ? pa11::strip_cv(right) : TypePtr();
	if (l.get() == NULL || r.get() == NULL ||
	    l->kind != TypeKind::Record || r->kind != TypeKind::Record)
		return false;
	if (pa11::same_type(l, r))
		return true;
	if (!l->is_template_specialization || !r->is_template_specialization)
		return false;
	string left_family = record_template_family_name(l);
	return !left_family.empty() &&
	       left_family == record_template_family_name(r);
}

bool function_has_by_value_record_family_parameter(const Binding* binding,
                                                   TypePtr record)
{
	if (binding == NULL ||
	    binding->type.get() == NULL ||
	    binding->type->kind != TypeKind::Function ||
	    record.get() == NULL)
		return false;
	for (size_t i = 0; i < binding->type->parameters.size(); ++i)
	{
		TypePtr param = pa11::strip_cv(binding->type->parameters[i]);
		if (param.get() != NULL &&
		    param->kind == TypeKind::Record &&
		    same_record_or_template_family(param, record))
			return true;
	}
	return false;
}

bool pending_record_return_feeds_constructor(
	const Binding* binding,
	const vector<const Binding*>& pending_inline_definitions)
{
	if (!is_class_constructor(binding))
		return false;
	for (size_t i = 0; i < pending_inline_definitions.size(); ++i)
	{
		TypePtr result = function_record_result(pending_inline_definitions[i]);
		if (constructor_has_record_parameter(result, binding))
			return true;
	}
	return false;
}

TypePtr first_this_record(const Binding* binding)
{
	if (binding == NULL ||
	    binding->type.get() == NULL ||
	    binding->type->kind != TypeKind::Function ||
	    binding->type->parameters.empty())
		return TypePtr();
	TypePtr first = pa11::strip_cv(binding->type->parameters[0]);
	if (first->kind != TypeKind::Pointer)
		return TypePtr();
	TypePtr record = pa11::strip_cv(first->base);
	return record->kind == TypeKind::Record ? record : TypePtr();
}

bool same_this_record(const Binding* left, const Binding* right)
{
	TypePtr left_record = first_this_record(left);
	TypePtr right_record = first_this_record(right);
	return left_record.get() != NULL &&
	       right_record.get() != NULL &&
	       pa11::same_type(left_record, right_record);
}

bool class_static_member_function_like(const Binding* binding)
{
	return binding != NULL &&
	       binding->kind == BindingKind::Function &&
	       binding->owner != NULL &&
	       binding->owner->kind == ScopeKind::Class &&
	       !is_class_constructor(binding) &&
	       !is_class_destructor_binding(binding) &&
	       (binding->is_static_member || first_this_record(binding).get() == NULL);
}

size_t binding_order_index(const Binding* binding)
{
	if (binding == NULL || binding->owner == NULL)
		return static_cast<size_t>(-1);
	const vector<Binding*>& order = binding->owner->binding_order;
	for (size_t i = 0; i < order.size(); ++i)
	{
		const Binding* current = order[i];
		if (current == binding ||
		    current->aliased_binding == binding ||
		    binding->aliased_binding == current)
			return i;
	}
	return static_cast<size_t>(-1);
}

bool class_member_of_local_class(const Binding* binding)
{
	if (binding == NULL || binding->owner == NULL)
		return false;
	for (Scope* scope = binding->owner; scope != NULL; scope = scope->parent)
	{
		if (scope->kind == ScopeKind::Function)
			return true;
		if (scope->kind == ScopeKind::Namespace)
			return false;
	}
	return false;
}

bool pending_local_class_constructor(
	const vector<const Binding*>& pending_inline_definitions)
{
	for (size_t i = 0; i < pending_inline_definitions.size(); ++i)
		if (is_class_constructor(pending_inline_definitions[i]) &&
		    class_member_of_local_class(pending_inline_definitions[i]))
			return true;
	return false;
}

bool function_touches_record(const Binding* binding, TypePtr record)
{
	if (binding == NULL ||
	    binding->type.get() == NULL ||
	    binding->type->kind != TypeKind::Function ||
	    record.get() == NULL)
		return false;
	for (size_t i = 0; i < binding->type->parameters.size(); ++i)
	{
		TypePtr param = pa11::strip_cv(binding->type->parameters[i]);
		if (param->kind == TypeKind::Pointer ||
		    param->kind == TypeKind::LValueReference ||
		    param->kind == TypeKind::RValueReference)
			param = pa11::strip_cv(param->base);
		if (param->kind == TypeKind::Record &&
		    pa11::same_type(param, record))
			return true;
	}
	return false;
}

}  // namespace

void ProgramLowerer::demand_move_assignment_copy_dependency(
	const Binding* binding)
{
	if (binding == NULL ||
	    !binding->is_generated_copy_move_assignment ||
	    binding->type->kind != TypeKind::Function ||
	    binding->type->parameters.size() != 2 ||
	    binding->type->parameters[1]->kind != TypeKind::RValueReference ||
	    binding->owner == NULL)
		return;
	map<string, vector<Binding*> >::const_iterator found =
		binding->owner->members.find("operator=");
	if (found == binding->owner->members.end())
		return;
	for (size_t i = 0; i < found->second.size(); ++i)
	{
		Binding* candidate = found->second[i];
		if (candidate->is_generated_copy_move_assignment &&
		    candidate->type->kind == TypeKind::Function &&
		    candidate->type->parameters.size() == 2 &&
		    candidate->type->parameters[1]->kind == TypeKind::LValueReference)
		{
			demand_inline_function(candidate);
			break;
		}
	}
}

void ProgramLowerer::place_lvalue_assignment_before_rvalue_assignment(
	const Binding* binding, ProgramLowerer::PendingInlineIterator& pos)
{
	if (!binding->is_generated_copy_move_assignment ||
	    binding->type->kind != TypeKind::Function ||
	    binding->type->parameters.size() != 2 ||
	    binding->type->parameters[1]->kind != TypeKind::LValueReference)
		return;
	for (PendingInlineIterator it = pending_inline_definitions.begin();
	     it != pending_inline_definitions.end(); ++it)
		if ((*it)->is_generated_copy_move_assignment &&
		    (*it)->type->kind == TypeKind::Function &&
		    (*it)->type->parameters.size() == 2 &&
		    (*it)->type->parameters[1]->kind == TypeKind::RValueReference)
		{
			pos = it;
			break;
		}
}

void ProgramLowerer::place_user_assignment_before_owner_members(
	const Binding* binding, ProgramLowerer::PendingInlineIterator& pos)
{
	if (binding->name != "operator=" ||
	    binding->is_generated_copy_move_assignment ||
	    binding->owner == NULL ||
	    function_template_specialization_binding(binding))
		return;
	for (PendingInlineIterator it = pending_inline_definitions.begin();
	     it != pending_inline_definitions.end(); ++it)
		if ((*it)->owner == binding->owner &&
		    (*it)->name != binding->owner->name)
		{
			pos = it;
			break;
		}
	if (pos == pending_inline_definitions.end())
	{
		for (PendingInlineIterator it = pending_inline_definitions.begin();
		     it != pending_inline_definitions.end(); ++it)
			if (constructor_has_no_explicit_parameters(*it) &&
			    !class_member_of_local_class(*it))
			{
				pos = it;
				break;
			}
	}
}

void ProgramLowerer::place_record_return_before_matching_constructor(
	const Binding* binding, ProgramLowerer::PendingInlineIterator& pos)
{
	if (!function_returns_record(binding))
		return;
	TypePtr result = function_record_result(binding);
	for (PendingInlineIterator it = pending_inline_definitions.begin();
	     it != pending_inline_definitions.end(); ++it)
	{
		const Binding* pending = *it;
		if (!is_class_constructor(pending) ||
		    pending->type.get() == NULL ||
		    pending->type->kind != TypeKind::Function ||
		    pending->type->parameters.size() < 2)
			continue;
		TypePtr param = pa11::strip_cv(
			object_type(pending->type->parameters[1]));
		if (param.get() != NULL &&
		    param->kind == TypeKind::Record &&
		    pa11::same_type(param, result))
		{
			pos = it;
			break;
		}
	}
}

void ProgramLowerer::place_record_return_before_owner_scalar_member(
	const Binding* binding, ProgramLowerer::PendingInlineIterator& pos)
{
	if (!function_returns_record(binding) ||
	    binding->owner == NULL ||
	    !binding_has_template_specialization_context(binding))
		return;
	for (PendingInlineIterator it = pending_inline_definitions.begin();
	     it != pending_inline_definitions.end(); ++it)
	{
		const Binding* pending = *it;
		bool pending_operator =
			pending->name.compare(0, 8, "operator") == 0 ||
			pending->name.compare(0, 9, "operator ") == 0;
		if (pending->owner == binding->owner &&
		    !is_class_constructor(pending) &&
		    !pending_operator &&
		    !function_returns_record(pending))
		{
			pos = it;
			break;
		}
	}
}

void ProgramLowerer::place_record_return_before_pending_operator(
	const Binding* binding, ProgramLowerer::PendingInlineIterator& pos)
{
	if (!function_returns_record(binding) ||
	    binding->name.compare(0, 8, "operator") == 0)
		return;
	TypePtr result = function_record_result(binding);
	for (PendingInlineIterator it = pending_inline_definitions.begin();
	     it != pending_inline_definitions.end(); ++it)
	{
		if ((*it)->name.compare(0, 8, "operator") != 0)
			continue;
		TypePtr pending_record = first_this_record(*it);
		if (result.get() != NULL &&
		    pending_record.get() != NULL &&
		    pa11::same_type(pa11::strip_cv(result),
		                    pa11::strip_cv(pending_record)))
		{
			if (pos == pending_inline_definitions.end() || it < pos)
				pos = it;
			break;
		}
	}
}

void ProgramLowerer::place_constructor_after_pending_record_operator(
	const Binding* binding, ProgramLowerer::PendingInlineIterator& pos)
{
	if (!is_class_constructor(binding) ||
	    binding->type.get() == NULL ||
	    binding->type->kind != TypeKind::Function ||
	    binding->type->parameters.size() < 2)
		return;
	TypePtr param_record = pa11::strip_cv(
		object_type(binding->type->parameters[1]));
	if (param_record.get() == NULL || param_record->kind != TypeKind::Record)
		return;
	for (PendingInlineIterator it = pending_inline_definitions.begin();
	     it != pending_inline_definitions.end(); ++it)
	{
		if (pos != pending_inline_definitions.end() && !(it < pos))
			break;
		if ((*it)->name.compare(0, 8, "operator") != 0)
			continue;
		TypePtr pending_record = first_this_record(*it);
		TypePtr pending_result = function_record_result(*it);
		bool same_owner =
			pending_record.get() != NULL &&
			pa11::same_type(pa11::strip_cv(pending_record), param_record);
		bool same_result =
			pending_result.get() != NULL &&
			pa11::same_type(pa11::strip_cv(pending_result), param_record);
		if (same_owner || same_result)
			pos = it + 1;
	}
}

void ProgramLowerer::place_local_constructor_after_shorter_overload(
	const Binding* binding, ProgramLowerer::PendingInlineIterator& pos)
{
	if (!is_class_constructor(binding) ||
	    !class_member_of_local_class(binding) ||
	    binding->owner == NULL ||
	    binding->type.get() == NULL ||
	    binding->type->kind != TypeKind::Function)
		return;
	size_t arity = binding->type->parameters.size();
	for (PendingInlineIterator it = pending_inline_definitions.begin();
	     it != pending_inline_definitions.end(); ++it)
	{
		if ((*it)->owner != binding->owner ||
		    !is_class_constructor(*it) ||
		    (*it)->type.get() == NULL ||
		    (*it)->type->kind != TypeKind::Function ||
		    (*it)->type->parameters.size() >= arity)
			continue;
		PendingInlineIterator after = it + 1;
		if (pos == pending_inline_definitions.end() || pos < after)
			pos = after;
	}
}

void ProgramLowerer::place_constructor_inline_definition(
	const Binding* binding, ProgramLowerer::PendingInlineIterator& pos)
{ if (binding->owner == NULL || binding->name != binding->owner->name) return; if (!binding->is_generated_default_constructor) for (PendingInlineIterator it = pending_inline_definitions.begin();
it != pending_inline_definitions.end(); ++it) { bool pending_ctor = (*it)->owner != NULL && (*it)->owner->kind == ScopeKind::Class && (*it)->name == (*it)->owner->name; if (pending_ctor && binding->type.get() != NULL &&
(*it)->type.get() != NULL && binding->type->kind == TypeKind::Function && (*it)->type->kind == TypeKind::Function && binding->type->parameters.size() < (*it)->type->parameters.size()) { pos = it; break; } }
if (pos == pending_inline_definitions.end()) { TypePtr constructed_record = first_this_record(binding); for (PendingInlineIterator it = pending_inline_definitions.begin(); it != pending_inline_definitions.end(); ++it) {
TypePtr pending_record = first_this_record(*it); bool same_owner_destructor = is_class_destructor_binding(*it) && (*it)->owner == binding->owner;
if (is_class_destructor_binding(*it) && (same_owner_destructor || (constructed_record.get() != NULL && pending_record.get() != NULL && pa11::same_type(constructed_record, pending_record)))) {
	pos = it; break; } } } if (pos == pending_inline_definitions.end() && binding->is_generated_default_constructor) { for (PendingInlineIterator it = pending_inline_definitions.begin();
	it != pending_inline_definitions.end(); ++it) if (!is_class_constructor(*it) && same_this_record(binding, *it)) { pos = it + 1; } } if (pos == pending_inline_definitions.end()) { for (PendingInlineIterator it = pending_inline_definitions.begin();
	it != pending_inline_definitions.end(); ++it) if (constructor_specialization_more_specific_than_pending(binding, *it)) { pos = it; break; } } if (pos == pending_inline_definitions.end() &&
	binding_has_template_specialization_context(binding)) { for (PendingInlineIterator it = pending_inline_definitions.begin(); it != pending_inline_definitions.end(); ++it) { const Binding* pending = *it;
bool pending_operator = pending->name.compare(0, 8, "operator") == 0 || pending->name.compare(0, 9, "operator ") == 0; if (pending->owner == binding->owner && !is_class_constructor(pending) && !pending_operator) {
pos = it; break; } } } if (pos == pending_inline_definitions.end() && constructor_has_no_explicit_parameters(binding)) { TypePtr record = first_this_record(binding);
for (PendingInlineIterator it = pending_inline_definitions.begin(); it != pending_inline_definitions.end(); ++it) if (function_returns_record(*it) && function_has_by_value_record_parameter(*it, record)) { pos = it;
break; } } if (pos == pending_inline_definitions.end()) { for (PendingInlineIterator it = pending_inline_definitions.begin(); it != pending_inline_definitions.end(); ++it) { TypePtr result = function_record_result(*it);
if (constructor_has_record_parameter(result, binding)) { pos = it + 1; break; } } } if (!binding->is_generated_default_constructor &&
binding->type.get() != NULL && binding->type->kind == TypeKind::Function && !function_template_specialization_binding(binding)) { bool has_reference_parameter = false; for (size_t i = 1; i < binding->type->parameters.size(); ++i)
if (is_reference(binding->type->parameters[i])) has_reference_parameter = true; if (has_reference_parameter) for (PendingInlineIterator it = pending_inline_definitions.begin();
it != pending_inline_definitions.end(); ++it) if (!is_class_constructor(*it)) { if (pos == pending_inline_definitions.end() || it < pos) pos = it; break; } } if (pos == pending_inline_definitions.end() && !binding->is_generated_default_constructor &&
!binding_has_template_specialization_context(binding) && !pending_record_return_feeds_constructor( binding, pending_inline_definitions)) for (PendingInlineIterator it = pending_inline_definitions.begin();
it != pending_inline_definitions.end(); ++it) if ((*it)->owner != NULL && (*it)->owner->kind == ScopeKind::Namespace) { pos = it; break; } bool zero_argument_ctor_before_local =
constructor_has_no_explicit_parameters(binding) && !class_member_of_local_class(binding) && pending_local_class_constructor(pending_inline_definitions); if (!binding->is_generated_default_constructor &&
!zero_argument_ctor_before_local) for (PendingInlineIterator it = pending_inline_definitions.begin(); it != pending_inline_definitions.end() && pos == pending_inline_definitions.end(); ++it)
if ((*it)->owner == binding->owner && ((*it)->name == "operator=" || (*it)->name.compare(0, 9, "operator ") == 0)) { pos = it; break; } if (active_inline_definition != NULL &&
is_class_constructor(active_inline_definition) && binding_has_template_specialization_context(active_inline_definition)) { TypePtr active_record = first_this_record(active_inline_definition);
for (PendingInlineIterator it = pending_inline_definitions.begin(); it != pending_inline_definitions.end() && pos == pending_inline_definitions.end(); ++it) { if (!is_class_constructor(*it)) continue;
TypePtr pending_record = first_this_record(*it); if (active_record.get() != NULL && pending_record.get() != NULL && record_has_base(active_record, pending_record)) continue; pos = it; break; } }
if (pos == pending_inline_definitions.end() && constructor_has_no_explicit_parameters(binding) && !class_member_of_local_class(binding)) { for (PendingInlineIterator it = pending_inline_definitions.begin();
it != pending_inline_definitions.end(); ++it) if (is_class_constructor(*it) && class_member_of_local_class(*it)) { pos = it; break; } } }

void ProgramLowerer::place_destructor_inline_definition(
	const Binding* binding, ProgramLowerer::PendingInlineIterator& pos)
{
	if (binding->name.empty() || binding->name[0] != '~' ||
	    binding->owner == NULL)
		return;

	TypePtr destroyed_record = first_this_record(binding);
	for (PendingInlineIterator it = pending_inline_definitions.begin();
	     it != pending_inline_definitions.end(); ++it)
	{
		TypePtr pending_this = first_this_record(*it);
		bool pending_destroyed_record_ctor =
			binding_has_template_specialization_context(binding) &&
			is_class_constructor(*it) &&
			((*it)->owner == binding->owner ||
			 (pending_this.get() != NULL &&
			  destroyed_record.get() != NULL &&
			  pa11::same_type(pending_this, destroyed_record)));
		if (((*it)->owner == binding->owner &&
		     (*it)->name != binding->owner->name) ||
		    (!pending_destroyed_record_ctor &&
		     function_touches_record(*it, destroyed_record)))
		{
			pos = it;
			break;
		}
	}
}

void ProgramLowerer::place_const_conversion_before_mutable_conversion(
	const Binding* binding, ProgramLowerer::PendingInlineIterator& pos)
{
	bool binding_const_conversion =
		binding->name.compare(0, 9, "operator ") == 0 &&
		binding->type->kind == TypeKind::Function &&
		!binding->type->parameters.empty() &&
		pa11::strip_cv(binding->type->parameters[0])->kind ==
			TypeKind::Pointer &&
		(pa11::strip_cv(binding->type->parameters[0])->base->cv &
		 pa11::CV_CONST) != 0;
	if (!binding_const_conversion || binding->owner == NULL)
		return;

	for (PendingInlineIterator it = pending_inline_definitions.begin();
	     it != pending_inline_definitions.end(); ++it)
	{
		bool pending_conversion =
			(*it)->name.compare(0, 9, "operator ") == 0 &&
			(*it)->type->kind == TypeKind::Function &&
			!(*it)->type->parameters.empty() &&
			pa11::strip_cv((*it)->type->parameters[0])->kind ==
				TypeKind::Pointer;
		bool pending_const =
			pending_conversion &&
			(pa11::strip_cv((*it)->type->parameters[0])->base->cv &
			 pa11::CV_CONST) != 0;
		if ((*it)->owner == binding->owner &&
		    pending_conversion && !pending_const)
		{
			pos = it;
			break;
		}
	}
}

void ProgramLowerer::place_specialized_conversion_before_base_conversion(
	const Binding* binding, ProgramLowerer::PendingInlineIterator& pos)
{
	if (binding->name.compare(0, 9, "operator ") == 0 &&
	    binding->owner != NULL &&
	    binding_has_template_specialization_context(binding))
	{
		TypePtr owner_record = class_record_for_member(binding);
		for (PendingInlineIterator it = pending_inline_definitions.begin();
		     it != pending_inline_definitions.end() &&
		     pos == pending_inline_definitions.end(); ++it)
		{
			if ((*it)->name.compare(0, 9, "operator ") != 0 ||
			    (*it)->owner == NULL)
				continue;
			TypePtr pending_record = class_record_for_member(*it);
			if (owner_record.get() != NULL &&
			    pending_record.get() != NULL &&
			    record_has_base(owner_record, pending_record))
			{
				pos = it;
				break;
			}
		}
	}
}

void ProgramLowerer::place_ranked_template_operator(
	const Binding* binding, ProgramLowerer::PendingInlineIterator& pos)
{
	if (pos != pending_inline_definitions.end())
		return;
	bool operator_function = binding->name.compare(0, 8, "operator") == 0;
	if (!operator_function)
		return;
	if (function_returns_record(binding))
	{
		TypePtr result = function_record_result(binding);
		for (PendingInlineIterator it = pending_inline_definitions.begin();
		     it != pending_inline_definitions.end(); ++it)
		{
			if ((*it)->name.compare(0, 8, "operator") == 0 ||
			    !function_returns_record(*it))
				continue;
			TypePtr pending_result = function_record_result(*it);
			if (result.get() != NULL &&
			    pending_result.get() != NULL &&
			    pa11::same_type(pa11::strip_cv(result),
			                    pa11::strip_cv(pending_result)))
			{
				pos = it;
				return;
			}
		}
		for (PendingInlineIterator it = pending_inline_definitions.begin();
		     it != pending_inline_definitions.end(); ++it)
		{
			if ((*it)->name.compare(0, 8, "operator") == 0 ||
			    function_returns_record(*it))
				continue;
			if (function_has_by_value_record_family_parameter(*it, result))
			{
				pos = it;
				return;
			}
		}
	}
	bool function_template_specialization =
		!binding->function_specialization_symbol.empty() ||
		(binding->aliased_binding != NULL &&
		 !binding->aliased_binding->function_specialization_symbol.empty());
	if (!binding_has_template_specialization_context(binding) &&
	    !function_template_specialization)
		return;
	for (PendingInlineIterator it = pending_inline_definitions.begin();
	     it != pending_inline_definitions.end(); ++it)
		if (((*it)->owner == binding->owner || same_this_record(*it, binding)) &&
		    is_class_constructor(*it) &&
		    (*it)->is_generated_default_constructor)
		{
			pos = it;
			return;
		}
	if (active_inline_definition != NULL &&
	    !is_class_constructor(active_inline_definition))
		for (PendingInlineIterator it = pending_inline_definitions.begin();
		     it != pending_inline_definitions.end(); ++it)
			if (is_class_constructor(*it) &&
			    !(*it)->is_generated_default_constructor &&
			    binding_has_template_specialization_context(*it))
			{
				pos = it;
				return;
			}
	map<const Binding*, size_t>::const_iterator binding_rank =
		inline_definition_ranks.find(binding);
	if (binding_rank == inline_definition_ranks.end())
		return;
	bool active_record_return_assignment =
		active_inline_definition != NULL &&
		function_returns_record(active_inline_definition) &&
		binding->name == "operator=";
	for (PendingInlineIterator it = pending_inline_definitions.begin();
	     it != pending_inline_definitions.end(); ++it)
	{
		bool pending_operator = (*it)->name.compare(0, 8, "operator") == 0;
		if (!pending_operator)
			continue;
		if ((*it)->is_generated_default_constructor)
			continue;
		if (active_record_return_assignment &&
		    !function_returns_record(*it))
			continue;
		map<const Binding*, size_t>::const_iterator pending_rank =
			inline_definition_ranks.find(*it);
		bool pending_function_template =
			!(*it)->function_specialization_symbol.empty() ||
			((*it)->aliased_binding != NULL &&
			 !(*it)->aliased_binding->function_specialization_symbol.empty());
		if (pending_rank != inline_definition_ranks.end() &&
		    (binding_has_template_specialization_context(*it) ||
		     pending_function_template) &&
		    pending_rank->second > binding_rank->second)
		{
			pos = it;
			break;
		}
	}
}

void ProgramLowerer::place_ranked_owner_member(
	const Binding* binding, ProgramLowerer::PendingInlineIterator& pos)
{
	if (is_class_constructor(binding) &&
	    pos != pending_inline_definitions.end() &&
	    is_class_destructor_binding(*pos) &&
	    same_this_record(binding, *pos))
		return;
	map<const Binding*, size_t>::const_iterator binding_rank =
		inline_definition_ranks.find(binding);
	bool operator_function = binding->name.compare(0, 8, "operator") == 0;
	if (pos == pending_inline_definitions.end() &&
	    binding_rank != inline_definition_ranks.end() &&
	    binding->owner != NULL &&
	    !binding->is_generated_default_constructor &&
	    !binding->is_generated_copy_move_assignment &&
	    !operator_function)
	{
		for (PendingInlineIterator it = pending_inline_definitions.begin();
		     it != pending_inline_definitions.end(); ++it)
		{
			map<const Binding*, size_t>::const_iterator pending_rank =
				inline_definition_ranks.find(*it);
			if (pending_rank != inline_definition_ranks.end() &&
			    (*it)->owner == binding->owner &&
			    !(*it)->is_generated_copy_move_assignment &&
			    !(is_class_destructor_binding(binding) &&
			      is_class_constructor(*it) &&
			      same_this_record(binding, *it)) &&
			    pending_rank->second > binding_rank->second)
			{
				pos = it;
				break;
			}
		}
	}
	if (pos == pending_inline_definitions.end() &&
	    binding_rank != inline_definition_ranks.end() &&
	    binding->owner != NULL &&
	    binding_has_template_specialization_context(binding) &&
	    !binding->is_generated_default_constructor &&
	    !binding->is_generated_copy_move_assignment &&
	    !operator_function)
	{
		for (PendingInlineIterator it = pending_inline_definitions.begin();
		     it != pending_inline_definitions.end(); ++it)
		{
			map<const Binding*, size_t>::const_iterator pending_rank =
				inline_definition_ranks.find(*it);
			bool pending_function_template =
				!(*it)->function_specialization_symbol.empty() ||
				((*it)->aliased_binding != NULL &&
				 !(*it)->aliased_binding->function_specialization_symbol.empty());
			if (pending_rank != inline_definition_ranks.end() &&
			    pending_function_template &&
			    function_returns_record(*it) &&
			    pending_rank->second > binding_rank->second)
			{
				pos = it;
				break;
			}
		}
	}
}

void ProgramLowerer::place_before_late_operator_or_generated_assignment(
	const Binding* binding, ProgramLowerer::PendingInlineIterator& pos)
{
	if (binding->name != "operator[]" &&
	    (binding->name.empty() || binding->name[0] != '~'))
		for (PendingInlineIterator it = pending_inline_definitions.begin();
		     it != pending_inline_definitions.end(); ++it)
			if ((*it)->name == "operator[]" ||
			    (generated_assignment_emit_depth == 0 &&
			     (*it)->is_generated_copy_move_assignment))
			{
				pos = it;
				break;
	}
}

void ProgramLowerer::place_before_generated_default_constructor(
	const Binding* binding, ProgramLowerer::PendingInlineIterator& pos)
{
	if (pos != pending_inline_definitions.end() ||
	    binding->is_generated_default_constructor)
		return;
	if (is_class_constructor(binding) && class_member_of_local_class(binding))
		return;
	TypePtr binding_record = first_this_record(binding);
	if (binding_has_template_specialization_context(binding) &&
	    binding_record.get() != NULL)
	{
		for (PendingInlineIterator it = pending_inline_definitions.begin();
		     it != pending_inline_definitions.end(); ++it)
			if ((*it)->is_generated_default_constructor)
			{
				TypePtr pending_record = first_this_record(*it);
				pending_record = pending_record.get() != NULL
					? pa11::strip_cv(pending_record)
					: TypePtr();
				if (pending_record.get() != NULL &&
				    pending_record->is_template_specialization &&
				    !same_this_record(binding, *it))
					continue;
				pos = it;
				break;
			}
		return;
	}
	for (PendingInlineIterator it = pending_inline_definitions.begin();
	     it != pending_inline_definitions.end(); ++it)
		if ((*it)->is_generated_default_constructor)
		{
			pos = it;
			break;
		}
}

void ProgramLowerer::place_subscript_before_pending_operators(
	const Binding* binding,
	ProgramLowerer::PendingInlineIterator& pos)
{
	if (binding->name != "operator[]")
		return;
	for (PendingInlineIterator it = pending_inline_definitions.begin();
	     it != pending_inline_definitions.end(); ++it)
		if ((*it)->name.compare(0, 8, "operator") == 0)
		{
			pos = it;
			break;
		}
}

void ProgramLowerer::place_active_destructor_dependency(
	const Binding* binding, ProgramLowerer::PendingInlineIterator& pos)
{
	if (active_inline_definition != NULL &&
	    active_inline_definition->name.size() > 0 &&
	    active_inline_definition->name[0] == '~' &&
	    binding != active_inline_definition &&
	    binding_has_template_specialization_context(active_inline_definition))
	{
		size_t index = active_inline_dependency_insert_count;
		if (index > pending_inline_definitions.size())
			index = pending_inline_definitions.size();
		pos = pending_inline_definitions.begin() + index;
		++active_inline_dependency_insert_count;
	}
}

void ProgramLowerer::place_active_record_return_dependency(
	const Binding* binding, ProgramLowerer::PendingInlineIterator& pos)
{
	if (active_inline_definition == NULL ||
	    binding == active_inline_definition ||
	    is_lambda_related_function(active_inline_definition) ||
	    !function_returns_record(active_inline_definition) ||
	    !is_class_constructor(binding))
		return;
	if (constructor_has_no_explicit_parameters(binding))
		return;
	TypePtr result = function_record_result(active_inline_definition);
	bool record_parameter = constructor_has_record_parameter(result, binding);
	if (pos != pending_inline_definitions.end() && record_parameter)
		return;
	if (!record_parameter)
	{
		TypePtr constructed = first_this_record(binding);
		if (constructed.get() == NULL ||
		    result.get() == NULL ||
		    !pa11::same_type(pa11::strip_cv(constructed),
		                     pa11::strip_cv(result)))
			return;
	}
	size_t index = active_inline_dependency_insert_count;
	if (index > pending_inline_definitions.size())
		index = pending_inline_definitions.size();
	PendingInlineIterator active_pos =
		pending_inline_definitions.begin() + index;
	if (pos == pending_inline_definitions.end() || active_pos < pos)
		pos = active_pos;
	++active_inline_dependency_insert_count;
}

void ProgramLowerer::place_before_pending_captureless_lambda_helper(
	const Binding* binding, ProgramLowerer::PendingInlineIterator& pos)
{
	if (is_captureless_lambda_helper_function(binding))
		return;
	if (!is_lambda_call_operator_function(binding) &&
	    is_lambda_related_function(binding))
		return;
	for (PendingInlineIterator it = pending_inline_definitions.begin();
	     it != pending_inline_definitions.end(); ++it)
	{
		if (!is_captureless_lambda_helper_function(*it))
			continue;
		if (pos == pending_inline_definitions.end() || it < pos)
			pos = it;
		break;
	}
}

void ProgramLowerer::place_after_pending_reference_constructor(
	const Binding* binding, ProgramLowerer::PendingInlineIterator& pos)
{
	if (is_class_constructor(binding))
		return;
	if (function_returns_record(binding) &&
	    (binding->owner == NULL || binding->owner->kind != ScopeKind::Class))
		return;
	for (PendingInlineIterator it = pending_inline_definitions.begin();
	     it != pending_inline_definitions.end(); ++it)
	{
		if (!constructor_has_reference_parameter(*it))
			continue;
		if (pos != pending_inline_definitions.end() && !(it < pos))
			continue;
		pos = it + 1;
		break;
	}
}

void ProgramLowerer::place_scalar_helper_after_record_returns(
	const Binding* binding, ProgramLowerer::PendingInlineIterator& pos)
{
	if (is_class_constructor(binding) || function_returns_record(binding))
		return;
	for (PendingInlineIterator it = pending_inline_definitions.begin();
	     it != pending_inline_definitions.end(); ++it)
	{
		if (!function_returns_record(*it))
			continue;
		PendingInlineIterator after = it + 1;
		if (pos == pending_inline_definitions.end() || !(pos > it))
			pos = after;
	}
}

void ProgramLowerer::place_value_constructor_after_scalar_helpers(
	const Binding* binding, ProgramLowerer::PendingInlineIterator& pos)
{
	if (!is_class_constructor(binding) ||
	    constructor_has_reference_parameter(binding) ||
	    binding->is_generated_default_constructor)
		return;
	for (PendingInlineIterator it = pending_inline_definitions.begin();
	     it != pending_inline_definitions.end(); ++it)
	{
		if (is_class_constructor(*it) || function_returns_record(*it))
			continue;
		if (pos == pending_inline_definitions.end() || !(pos > it))
			pos = it + 1;
	}
}

void ProgramLowerer::place_scalar_helper_before_value_constructor(
	const Binding* binding, ProgramLowerer::PendingInlineIterator& pos)
{
	if (is_class_constructor(binding) || function_returns_record(binding))
		return;
	for (PendingInlineIterator it = pending_inline_definitions.begin();
	     it != pending_inline_definitions.end(); ++it)
	{
		if (!is_class_constructor(*it) ||
		    constructor_has_reference_parameter(*it))
			continue;
		if (pos == pending_inline_definitions.end() || it < pos)
			pos = it;
		break;
	}
}

void ProgramLowerer::place_static_template_member_after_pending_scalar_templates(
	const Binding* binding, ProgramLowerer::PendingInlineIterator& pos)
{
	if (active_inline_definition == NULL ||
	    binding == active_inline_definition ||
	    !class_static_member_function_like(binding) ||
	    function_returns_record(binding) ||
	    !binding_has_template_specialization_context(binding) ||
	    is_class_constructor(active_inline_definition) ||
	    function_returns_record(active_inline_definition) ||
	    !function_template_specialization_binding(active_inline_definition))
		return;
	for (PendingInlineIterator it = pending_inline_definitions.begin();
	     it != pending_inline_definitions.end(); ++it)
	{
		if (is_class_constructor(*it) ||
		    function_returns_record(*it) ||
		    !function_template_specialization_binding(*it) ||
		    ((*it)->owner != NULL && (*it)->owner->kind == ScopeKind::Class))
			continue;
		PendingInlineIterator after = it + 1;
		if (pos == pending_inline_definitions.end() || after > pos)
			pos = after;
	}
}

void ProgramLowerer::place_static_member_before_later_owner_static_member(
	const Binding* binding, ProgramLowerer::PendingInlineIterator& pos)
{
	if (!class_static_member_function_like(binding))
		return;
	size_t binding_index = binding_order_index(binding);
	if (binding_index == static_cast<size_t>(-1))
		return;
	for (PendingInlineIterator it = pending_inline_definitions.begin();
	     it != pending_inline_definitions.end(); ++it)
	{
		if ((*it)->owner != binding->owner ||
		    !class_static_member_function_like(*it))
			continue;
		size_t pending_index = binding_order_index(*it);
		if (pending_index == static_cast<size_t>(-1) ||
		    !(binding_index < pending_index))
			continue;
		if (pos == pending_inline_definitions.end() || it < pos)
			pos = it;
		break;
	}
}

void ProgramLowerer::place_constructor_destructor_pair(
	const Binding* binding, ProgramLowerer::PendingInlineIterator& pos)
{
	if (is_class_constructor(binding))
	{
		for (PendingInlineIterator it = pending_inline_definitions.begin();
		     it != pending_inline_definitions.end(); ++it)
		{
			if (!is_class_destructor_binding(*it))
				continue;
			bool same_owner =
				binding->owner != NULL && (*it)->owner == binding->owner;
			if (!same_owner && !same_this_record(binding, *it))
				continue;
			if (pos == pending_inline_definitions.end() || it < pos)
				pos = it;
			break;
		}
		return;
	}
	if (!is_class_destructor_binding(binding))
		return;
	for (PendingInlineIterator it = pending_inline_definitions.begin();
	     it != pending_inline_definitions.end(); ++it)
	{
		if (!is_class_constructor(*it))
			continue;
		bool same_owner =
			binding->owner != NULL && (*it)->owner == binding->owner;
		if (!same_owner && !same_this_record(binding, *it))
			continue;
		PendingInlineIterator after = it + 1;
		if (pos == pending_inline_definitions.end() || pos < after)
			pos = after;
		break;
	}
}

void ProgramLowerer::place_constructor_after_record_return_dependency(
	const Binding* binding, ProgramLowerer::PendingInlineIterator& pos)
{
	if (!is_class_constructor(binding) ||
	    binding->type.get() == NULL ||
	    binding->type->kind != TypeKind::Function ||
	    binding->type->parameters.size() < 2)
		return;
	TypePtr constructed = first_this_record(binding);
	for (size_t i = 1; i < binding->type->parameters.size(); ++i)
	{
		bool reference_param = is_reference(binding->type->parameters[i]);
		if (reference_param &&
		    !same_record_or_template_family(
			    object_type(binding->type->parameters[i]), constructed))
			continue;
		TypePtr param = pa11::strip_cv(object_type(binding->type->parameters[i]));
		if (param.get() == NULL || param->kind != TypeKind::Record)
			continue;
		for (PendingInlineIterator it = pending_inline_definitions.begin();
		     it != pending_inline_definitions.end(); ++it)
		{
			if (reference_param &&
			    (*it)->owner != NULL &&
			    (*it)->owner->kind == ScopeKind::Class)
				continue;
			TypePtr result = function_record_result(*it);
			if (result.get() == NULL ||
			    !pa11::same_type(pa11::strip_cv(result), param))
				continue;
			PendingInlineIterator after = it + 1;
			if (pos == pending_inline_definitions.end() || pos < after)
				pos = after;
		}
	}
}

void ProgramLowerer::insert_pending_inline_definition(const Binding* binding)
{
	PendingInlineIterator pos = pending_inline_definitions.end();
	place_lvalue_assignment_before_rvalue_assignment(binding, pos);
	place_user_assignment_before_owner_members(binding, pos);
	place_record_return_before_matching_constructor(binding, pos);
	place_record_return_before_owner_scalar_member(binding, pos);
	place_record_return_before_pending_operator(binding, pos);
	place_constructor_after_pending_record_operator(binding, pos);
	place_local_constructor_after_shorter_overload(binding, pos);
	place_constructor_inline_definition(binding, pos);
	place_destructor_inline_definition(binding, pos);
	place_const_conversion_before_mutable_conversion(binding, pos);
	place_specialized_conversion_before_base_conversion(binding, pos);
	place_ranked_template_operator(binding, pos);
	place_ranked_owner_member(binding, pos);
	place_subscript_before_pending_operators(binding, pos);
	place_before_late_operator_or_generated_assignment(binding, pos);
	place_before_generated_default_constructor(binding, pos);
	place_active_destructor_dependency(binding, pos);
	place_active_record_return_dependency(binding, pos);
	place_before_pending_captureless_lambda_helper(binding, pos);
	place_scalar_helper_after_record_returns(binding, pos);
	place_after_pending_reference_constructor(binding, pos);
	place_value_constructor_after_scalar_helpers(binding, pos);
	place_scalar_helper_before_value_constructor(binding, pos);
	place_static_template_member_after_pending_scalar_templates(binding, pos);
	place_static_member_before_later_owner_static_member(binding, pos);
	place_constructor_destructor_pair(binding, pos);
	place_constructor_after_record_return_dependency(binding, pos);
	pending_inline_definitions.insert(pos, binding);
}

void ProgramLowerer::emit_pending_generated_aggregate_constructors()
{
	if (pending_inline_definitions.empty())
		return;
	vector<const Binding*> selected;
	vector<const Binding*> rest;
	for (size_t i = 0; i < pending_inline_definitions.size(); ++i)
	{
		const Binding* binding = pending_inline_definitions[i];
		if (binding != NULL && binding->is_generated_aggregate_constructor)
			selected.push_back(binding);
		else
			rest.push_back(binding);
	}
	if (selected.empty())
		return;
	pending_inline_definitions.swap(selected);
	emit_pending_inline_definitions();
	pending_inline_definitions.insert(pending_inline_definitions.end(),
	                                  rest.begin(), rest.end());
}

void ProgramLowerer::emit_pending_inline_definitions()
{ while (!pending_inline_definitions.empty()) { const Binding* binding = pending_inline_definitions.front(); pending_inline_definitions.erase(pending_inline_definitions.begin());
map<const Binding*, const Node*>::const_iterator found = inline_definitions.find(binding); if (found == inline_definitions.end()) continue; const Binding* base_ctor = first_base_default_constructor(binding);
string base_ctor_name; bool base_ctor_complete = false; if (base_ctor != NULL) { base_ctor_complete = !base_ctor->is_generated_default_constructor; base_ctor_name = base_ctor_complete ? symbol_for(base_ctor)
: constructor_symbol_for(base_ctor, true); } if (base_ctor != NULL && defined_functions.find(base_ctor_name) == defined_functions.end() && inline_definitions.find(base_ctor) != inline_definitions.end()) {
demand_inline_function(base_ctor, base_ctor_complete); vector<const Binding*>::iterator retry = find(pending_inline_definitions.begin(), pending_inline_definitions.end(), base_ctor);
if (retry != pending_inline_definitions.end()) ++retry; else retry = pending_inline_definitions.begin(); pending_inline_definitions.insert(retry, binding); continue; } string name = symbol_for(binding);
bool class_ctor = is_class_constructor(binding); bool class_dtor = is_class_destructor_binding(binding); bool need_complete = !class_ctor || demanded_inline_complete_entries.find(binding) !=
demanded_inline_complete_entries.end(); bool need_base = (class_ctor && demanded_constructor_base_entries.find(binding) != demanded_constructor_base_entries.end()) || (class_dtor &&
demanded_destructor_base_entries.find(binding) != demanded_destructor_base_entries.end()); bool ctor_owner_polymorphic = false; if (class_ctor) { TypePtr owner_record = class_record_for_member(binding);
owner_record = owner_record.get() != NULL ? pa11::strip_cv(owner_record) : TypePtr(); ctor_owner_polymorphic = owner_record.get() != NULL && owner_record->is_polymorphic; }
if (defined_functions.find(name) != defined_functions.end()) need_complete = false; if (defined_functions.find(name + "__base_entry") != defined_functions.end()) need_base = false; bool has_function_type =
binding->type.get() != NULL && binding->type->kind == TypeKind::Function; bool multi_parameter_ctor = has_function_type && binding->type->parameters.size() > 1; bool ctor_has_record_parameter = false;
bool ctor_has_reference_record_parameter = false; if (has_function_type) for (size_t i = 1; i < binding->type->parameters.size(); ++i) { TypePtr param = binding->type->parameters[i]; bool reference_param =
param->kind == TypeKind::LValueReference || param->kind == TypeKind::RValueReference; if (reference_param) param = param->base; param = pa11::strip_cv(param); if (param.get() != NULL && param->kind == TypeKind::Record) {
ctor_has_record_parameter = true; if (reference_param) ctor_has_reference_record_parameter = true; } } bool template_specialization_ctor = binding_has_template_specialization_context(binding) &&
!binding->is_generated_default_constructor && !binding->is_generated_aggregate_constructor && !binding->is_generated_copy_move_constructor && function_definition_body_empty(*found->second);
if (class_ctor && need_base && !need_complete && !binding->is_generated_default_constructor && ((ctor_owner_polymorphic && multi_parameter_ctor) || (template_specialization_ctor && (!ctor_has_record_parameter ||
ctor_has_reference_record_parameter))) && has_function_type && defined_functions.find(name) == defined_functions.end()) need_complete = true; if (!need_complete && !need_base) continue; if (need_complete)
defined_functions.insert(name); if (need_base) defined_functions.insert(name + "__base_entry"); const Binding* saved_active = active_inline_definition; size_t saved_dependency_insert_count =
active_inline_dependency_insert_count; active_inline_definition = binding; active_inline_dependency_insert_count = 0; FunctionLowerer lowerer(*this, *found->second); if (binding->is_generated_copy_move_assignment)
++generated_assignment_emit_depth; FunctionOut lowered = lowerer.lower(); if (binding->is_generated_copy_move_assignment) --generated_assignment_emit_depth; active_inline_definition = saved_active;
active_inline_dependency_insert_count = saved_dependency_insert_count; if (!binding->name.empty() && binding->name[0] == '~' && !binding_has_template_specialization_context(binding)) emit_pending_inline_definitions();
if (class_ctor && need_complete) { TypePtr active_record = first_this_record(binding); bool emit_member_ctor_dependencies = false; for (PendingInlineIterator it = pending_inline_definitions.begin(); it != pending_inline_definitions.end(); ++it) { if (!is_class_constructor(*it)) continue; TypePtr pending_record = first_this_record(*it); if (active_record.get() != NULL && pending_record.get() != NULL && record_has_base(active_record, pending_record)) continue; emit_member_ctor_dependencies = true; break; } if (emit_member_ctor_dependencies) emit_pending_inline_definitions(); }
if (need_base) functions.push_back(make_constructor_base_entry(lowered, name)); if (need_complete) { bool inserted = false; if (class_ctor && constructor_has_no_explicit_parameters(binding) && class_member_of_local_class(binding)) { for (vector<FunctionOut>::iterator it = functions.begin(); it != functions.end(); ++it) { const Binding* pending = it->binding; if (pending != NULL && pending->owner == binding->owner && is_class_constructor(pending) && pending->type.get() != NULL && pending->type->kind == TypeKind::Function && pending->type->parameters.size() > binding->type->parameters.size()) { functions.insert(it, lowered); inserted = true; break; } } } if (!inserted) functions.push_back(lowered); } emit_pending_synthetic_assignment_functions(); } }

}  // namespace internal

}  // namespace pa14
