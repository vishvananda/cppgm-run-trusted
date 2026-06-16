#include "pa14_lowir_internal.h"

#include <stdexcept>

using namespace std;

namespace pa14 {
namespace internal {
namespace {

bool hosted_namespace_scope(const Scope* scope)
{
	for (const Scope* current = scope;
	     current != NULL;
	     current = current->parent)
		if (current->kind == ScopeKind::Namespace &&
		    (current->name == "std" || current->name == "__gnu_cxx"))
			return true;
	return false;
}

bool hosted_library_record(TypePtr type)
{
	TypePtr bare = type.get() != NULL ? pa11::strip_cv(type) : TypePtr();
	return bare.get() != NULL &&
	       bare->kind == TypeKind::Record &&
	       hosted_namespace_scope(bare->scope);
}

bool type_contains_hosted_library_record(TypePtr type,
                                         set<const pa11::Type*>& seen)
{
	if (type.get() == NULL)
		return false;
	TypePtr bare = pa11::strip_cv(type);
	if (bare->kind == TypeKind::Array)
		return type_contains_hosted_library_record(bare->base, seen);
	if (bare->kind != TypeKind::Record)
		return false;
	if (hosted_library_record(bare))
		return true;
	if (!seen.insert(bare.get()).second)
		return false;
	try
	{
		pa11::layout_record_type(bare);
	}
	catch (const runtime_error&)
	{
		return false;
	}
	vector<TypePtr> bases = pa11::record_direct_bases(bare);
	for (size_t i = 0; i < bases.size(); ++i)
		if (type_contains_hosted_library_record(bases[i], seen))
			return true;
	for (size_t i = 0; i < bare->fields.size(); ++i)
		if (type_contains_hosted_library_record(bare->fields[i]->type,
		                                        seen))
			return true;
	return false;
}

}

bool constructor_record_contains_hosted_subobject(const Binding* binding)
{
	if (!is_class_constructor_binding(binding))
		return false;
	TypePtr record = class_record_for_member(binding);
	set<const pa11::Type*> seen;
	return type_contains_hosted_library_record(record, seen);
}

}
}
