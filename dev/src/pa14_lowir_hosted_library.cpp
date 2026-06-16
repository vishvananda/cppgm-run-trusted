#include "pa14_lowir_internal.h"

namespace pa14 {
namespace internal {

namespace {

bool hosted_vector_initializer_list_constructor_binding(const Binding* binding)
{
	if (!is_class_constructor_binding(binding) ||
	    binding->type.get() == NULL ||
	    binding->type->kind != TypeKind::Function ||
	    binding->type->parameters.size() < 2)
		return false;
	TypePtr record = class_record_for_member(binding);
	record = record.get() != NULL ? pa11::strip_cv(record) : TypePtr();
	if (record.get() == NULL ||
	    record->kind != TypeKind::Record ||
	    !record->is_template_specialization)
		return false;
	string primary = record->template_primary_name.empty()
		? record->name : record->template_primary_name;
	size_t scope = primary.rfind("::");
	if (scope != string::npos)
		primary = primary.substr(scope + 2);
	if (primary != "vector")
		return false;
	TypePtr param = binding->type->parameters[1];
	if (is_reference(param))
		param = param->base;
	return is_initializer_list_type(pa11::strip_cv(param), NULL);
}

}  // namespace

bool hosted_library_binding(const Binding* binding)
{
	if (binding == NULL)
		return false;
	if (binding->name.compare(0, 10, "__builtin_") == 0)
		return true;
	if (binding->name == "sched_yield" ||
	    binding->name.compare(0, 8, "pthread_") == 0 ||
	    binding->name.compare(0, 10, "__gthread_") == 0)
		return true;
	for (Scope* scope = binding->owner; scope != NULL; scope = scope->parent)
	{
		if (scope->kind != ScopeKind::Namespace)
			continue;
		if (scope->name == "std" || scope->name == "__gnu_cxx")
			return true;
	}
	return false;
}

bool hosted_library_body_candidate(const Binding* binding)
{
	if (binding == NULL || !hosted_library_binding(binding))
		return true;
	TypePtr record = class_record_for_member(binding);
	record = record.get() != NULL ? pa11::strip_cv(record) : TypePtr();
	string primary = record.get() != NULL && record->kind == TypeKind::Record
		? (record->template_primary_name.empty()
		   ? record->name : record->template_primary_name)
		: string();
	size_t scope = primary.rfind("::");
	if (scope != string::npos)
		primary = primary.substr(scope + 2);
	if (hosted_external_stream_function_binding(binding))
		return false;
	if (function_signature_has_unresolved_storage(binding))
		return false;
	if (primary == "basic_string" &&
	    (is_class_constructor_binding(binding) ||
	     is_class_destructor_binding(binding) ||
	     binding->name == "operator="))
		return false;
	if (primary == "vector" &&
	    hosted_vector_initializer_list_constructor_binding(binding))
		return false;
	if (primary == "vector" &&
	    binding->name.compare(0, 3, "_M_") == 0)
		return true;
	if (binding->is_inline_definition ||
	    binding->is_generated_copy_move_constructor ||
	    binding->is_generated_copy_move_assignment ||
	    binding->is_generated_default_constructor ||
	    binding->is_generated_default_destructor ||
	    binding_has_template_specialization_context(binding))
		return true;
	const Binding* alias = binding->aliased_binding;
	if (function_signature_has_unresolved_storage(alias))
		return false;
	return alias != NULL &&
	       (alias->is_inline_definition ||
	        alias->is_generated_copy_move_constructor ||
	        alias->is_generated_copy_move_assignment ||
	        alias->is_generated_default_constructor ||
	        alias->is_generated_default_destructor ||
	        binding_has_template_specialization_context(alias));
}

}  // namespace internal
}  // namespace pa14
