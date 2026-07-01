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

bool record_is_in_std_namespace(TypePtr record)
{
	record = record.get() != NULL ? pa11::strip_cv(record) : TypePtr();
	Scope* scope = record.get() != NULL ? record->scope : NULL;
	for (Scope* cur = scope; cur != NULL; cur = cur->parent)
		if (cur->kind == ScopeKind::Namespace && cur->name == "std")
			return true;
	return false;
}

string hosted_unqualified_primary(TypePtr record)
{
	record = record.get() != NULL ? pa11::strip_cv(record) : TypePtr();
	if (record.get() == NULL || record->kind != TypeKind::Record)
		return "";
	string primary = record->template_primary_name.empty()
		? record->name : record->template_primary_name;
	size_t args = primary.find('<');
	if (args != string::npos)
		primary = primary.substr(0, args);
	size_t scope = primary.rfind("::");
	if (scope != string::npos)
		primary = primary.substr(scope + 2);
	return primary;
}

bool hosted_map_base_operator_index_binding(const Binding* binding)
{
	if (binding == NULL ||
	    binding->name != "operator[]" ||
	    binding->type.get() == NULL ||
	    binding->type->kind != TypeKind::Function ||
	    binding->type->parameters.size() < 2)
		return false;
	TypePtr record = class_record_for_member(binding);
	record = record.get() != NULL ? pa11::strip_cv(record) : TypePtr();
	return record.get() != NULL &&
	       record->kind == TypeKind::Record &&
	       record_is_in_std_namespace(record) &&
	       hosted_unqualified_primary(record) ==
		       pa11::abi_private_name("Map_base");
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

bool hosted_std_function_swap_binding(const Binding* binding)
{
	if (binding == NULL ||
	    binding->name != "swap" ||
	    binding->type.get() == NULL ||
	    binding->type->kind != TypeKind::Function)
		return false;
	TypePtr record = class_record_for_member(binding);
	record = record.get() != NULL ? pa11::strip_cv(record) : TypePtr();
	return record.get() != NULL &&
	       record->kind == TypeKind::Record &&
	       record_is_in_std_namespace(record) &&
	       hosted_unqualified_primary(record) == "function";
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
	if (hosted_std_function_swap_binding(binding))
		return true;
	if (function_signature_has_unresolved_storage(binding))
		return false;
	if (primary == "basic_string" &&
	    (is_class_constructor_binding(binding) ||
	     is_class_destructor_binding(binding) ||
	     binding->name == "operator=") &&
	    (!binding_has_function_template_specialization_symbol(binding) ||
	     hosted_basic_string_external_member(binding)))
		return false;
	if (primary == "vector" &&
	    hosted_vector_initializer_list_constructor_binding(binding))
		return false;
	if (primary == "vector" &&
	    binding->name.compare(0, pa11::abi_private_member_prefix().size(),
	                          pa11::abi_private_member_prefix()) == 0)
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

	const Binding* hosted_map_base_lvalue_operator_index_alias(
		const Binding* binding)
	{
		if (!hosted_map_base_operator_index_binding(binding) ||
		    binding->owner == NULL)
			return NULL;
		string object = global_object_symbol(binding);
		bool rvalue_object = object.find("ixEO") != string::npos;
		bool rvalue_type =
			binding->type->parameters[1].get() != NULL &&
			binding->type->parameters[1]->kind ==
				TypeKind::RValueReference;
		if (!rvalue_object && !rvalue_type)
			return NULL;
		map<string, vector<Binding*> >::const_iterator overloads =
			binding->owner->members.find(binding->name);
		if (overloads == binding->owner->members.end())
			return NULL;
		for (size_t i = 0; i < overloads->second.size(); ++i)
		{
			Binding* candidate = overloads->second[i];
			if (candidate == NULL ||
			    candidate == binding ||
			    !hosted_map_base_operator_index_binding(candidate) ||
			    candidate->type->parameters[1].get() == NULL ||
			    candidate->type->parameters[1]->kind !=
				    TypeKind::LValueReference)
				continue;
			return candidate;
		}
		return NULL;
	}

	bool hosted_unordered_map_body_root(const Binding* binding)
	{
		if (binding == NULL ||
		    binding->type.get() == NULL ||
		    binding->type->kind != TypeKind::Function ||
		    binding->type->parameters.size() < 2)
			return false;
		if (hosted_map_base_lvalue_operator_index_alias(binding) != NULL)
			return true;
		string object = global_object_symbol(binding);
		string map_base_prefix = "_ZNSt8__detail9_Map_base";
		if (object.compare(0, map_base_prefix.size(),
		                   map_base_prefix) == 0 &&
		    object.find("ixE") != string::npos)
			return true;
		TypePtr record = class_record_for_member(binding);
		record = record.get() != NULL ? pa11::strip_cv(record) : TypePtr();
		if (record.get() == NULL ||
		    record->kind != TypeKind::Record ||
		    !record_is_in_std_namespace(record))
			return false;
		string primary = hosted_unqualified_primary(record);
		if (binding->name == "insert")
			return primary == "unordered_map";
		if (binding->name == "operator[]")
			return primary == "unordered_map" ||
			       primary == pa11::abi_private_name("Map_base");
		return false;
	}

	}  // namespace internal
	}  // namespace pa14
