#include "pa14_lowir_internal.h"
namespace pa14 {
namespace internal {
namespace {
map<const Binding*, TypePtr>& ranked_function_record_result_cache()
{
	static map<const Binding*, TypePtr> cache;
	return cache;
}
bool is_class_constructor(const Binding* binding)
{
	return binding != NULL &&
	       binding->owner != NULL &&
	       binding->owner->kind == ScopeKind::Class &&
	       binding->name == binding->owner->name;
}
TypePtr function_record_result(const Binding* binding)
{
	map<const Binding*, TypePtr>& cache =
		ranked_function_record_result_cache();
	map<const Binding*, TypePtr>::const_iterator found = cache.find(binding);
	if (found != cache.end())
		return found->second;
	if (binding == NULL ||
	    binding->type.get() == NULL ||
	    binding->type->kind != TypeKind::Function)
	{
		cache[binding] = TypePtr();
		return TypePtr();
	}
	TypePtr result = pa11::strip_cv(binding->type->base);
	TypePtr record = result.get() != NULL && result->kind == TypeKind::Record
		? result : TypePtr();
	cache[binding] = record;
	return record;
}
bool function_returns_record(const Binding* binding)
{
	return function_record_result(binding).get() != NULL;
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
bool function_has_by_value_record_parameter(const Binding* binding,
                                            TypePtr record)
{
	if (binding == NULL ||
	    binding->type.get() == NULL ||
	    binding->type->kind != TypeKind::Function)
		return false;
	for (size_t i = 0; i < binding->type->parameters.size(); ++i)
	{
		TypePtr param = binding->type->parameters[i];
		if (param.get() == NULL || is_reference(param))
			continue;
		param = pa11::strip_cv(param);
		if (param.get() != NULL &&
		    param->kind == TypeKind::Record &&
		    pa11::same_type(param, record))
			return true;
	}
	return false;
}
string record_template_family_name(TypePtr record)
{
	record = record.get() != NULL ? pa11::strip_cv(record) : TypePtr();
	if (record.get() == NULL || record->kind != TypeKind::Record)
		return string();
	string family = record->template_primary_name;
	if (family.empty() && record->scope != NULL)
		family = record->scope->name;
	return family;
}
bool same_record_or_template_family(TypePtr left, TypePtr right)
{
	left = left.get() != NULL ? pa11::strip_cv(left) : TypePtr();
	right = right.get() != NULL ? pa11::strip_cv(right) : TypePtr();
	if (left.get() == NULL || right.get() == NULL ||
	    left->kind != TypeKind::Record || right->kind != TypeKind::Record)
		return false;
	if (pa11::same_type(left, right))
		return true;
	string left_family = record_template_family_name(left);
	string right_family = record_template_family_name(right);
	if (left_family.empty() || left_family != right_family)
		return false;
	return template_arguments_mention_type(left->template_arguments, right) ||
	       template_arguments_mention_type(right->template_arguments, left);
}
bool function_has_by_value_record_family_parameter(const Binding* binding,
                                                   TypePtr record)
{
	if (function_has_by_value_record_parameter(binding, record))
		return true;
	if (binding == NULL ||
	    binding->type.get() == NULL ||
	    binding->type->kind != TypeKind::Function)
		return false;
	for (size_t i = 0; i < binding->type->parameters.size(); ++i)
	{
		TypePtr param = binding->type->parameters[i];
		if (param.get() == NULL || is_reference(param))
			continue;
		param = pa11::strip_cv(param);
		if (param.get() != NULL &&
		    param->kind == TypeKind::Record &&
		    same_record_or_template_family(param, record))
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
	return pa11::strip_cv(object_type(binding->type->parameters[0]));
}
bool same_this_record(const Binding* left, const Binding* right)
{
	TypePtr lhs = first_this_record(left);
	TypePtr rhs = first_this_record(right);
	return lhs.get() != NULL &&
	       rhs.get() != NULL &&
	       pa11::same_type(pa11::strip_cv(lhs), pa11::strip_cv(rhs));
}
}  // namespace

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
		if (active_record_return_assignment && !function_returns_record(*it))
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

void clear_lowir_inline_order_ranked_caches()
{
	ranked_function_record_result_cache().clear();
}

}  // namespace internal
}  // namespace pa14
