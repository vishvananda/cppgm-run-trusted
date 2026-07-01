#include "pa14_lowir_function_internal.h"

namespace pa14 {
namespace internal {
namespace {

string destructor_epilogue_record_primary(TypePtr record)
{
	TypePtr bare = record.get() != NULL ? pa11::strip_cv(record) : TypePtr();
	if (bare.get() == NULL)
		return "";
	string primary = bare->template_primary_name.empty()
		? bare->name : bare->template_primary_name;
	size_t args = primary.find('<');
	if (args != string::npos)
		primary = primary.substr(0, args);
	size_t scope = primary.rfind("::");
	if (scope != string::npos)
		primary = primary.substr(scope + 2);
	return primary;
}

bool destructor_epilogue_record_in_std(TypePtr record)
{
	TypePtr bare = record.get() != NULL ? pa11::strip_cv(record) : TypePtr();
	for (Scope* scope = bare.get() != NULL ? bare->scope : NULL;
	     scope != NULL;
	     scope = scope->parent)
		if (scope->kind == ScopeKind::Namespace && scope->name == "std")
			return true;
	return false;
}

}  // namespace

bool hosted_vector_temporary_value_destructor(const Binding* binding)
{
	if (!is_class_destructor_binding(binding))
		return false;
	TypePtr record = class_record_for_member(binding);
	record = record.get() != NULL ? pa11::strip_cv(record) : TypePtr();
	if (record.get() == NULL ||
	    record->kind != TypeKind::Record ||
	    !destructor_epilogue_record_in_std(record) ||
	    destructor_epilogue_record_primary(record) != "_Temporary_value")
		return false;
	for (Scope* scope = record->scope != NULL ? record->scope->parent : NULL;
	     scope != NULL;
	     scope = scope->parent)
	{
		if (scope->kind != ScopeKind::Class)
			continue;
		TypePtr owner = pa11::record_type_for_scope(scope);
		if (destructor_epilogue_record_primary(owner) == "vector")
			return true;
	}
	return false;
}

}  // namespace internal
}  // namespace pa14
