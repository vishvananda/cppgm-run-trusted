#include "pa14_lowir_internal.h"

namespace pa14 {
namespace internal {
namespace {

bool copy_move_constructor_binding(const Binding* binding)
{
	if (binding == NULL ||
	    !is_class_constructor_binding(binding) ||
	    binding->type.get() == NULL ||
	    binding->type->kind != TypeKind::Function ||
	    binding->type->parameters.size() != 2 ||
	    !is_reference(binding->type->parameters[1]))
		return false;
	TypePtr record = class_record_for_member(binding);
	record = record.get() != NULL ? pa11::strip_cv(record) : TypePtr();
	TypePtr source = pa11::strip_cv(binding->type->parameters[1]->base);
	return record.get() != NULL &&
	       record->kind == TypeKind::Record &&
	       source.get() != NULL &&
	       source->kind == TypeKind::Record &&
	       pa11::same_type(record, source);
}

bool extern_template_class_binding(const Binding* binding)
{
	if (binding == NULL)
		return false;
	for (Scope* scope = binding->owner; scope != NULL; scope = scope->parent)
	{
		if (scope->kind != ScopeKind::Class)
			continue;
		TypePtr record = pa11::record_type_for_scope(scope);
		record = record.get() != NULL ? pa11::strip_cv(record) : TypePtr();
		if (record.get() != NULL &&
		    record->kind == TypeKind::Record &&
		    record->is_extern_template_instantiation)
			return true;
	}
	return false;
}

string unqualified_template_primary(TypePtr type)
{
	TypePtr bare = type.get() != NULL ? pa11::strip_cv(type) : TypePtr();
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

bool record_is_in_std_namespace(TypePtr record)
{
	record = record.get() != NULL ? pa11::strip_cv(record) : TypePtr();
	Scope* scope = record.get() != NULL ? record->scope : NULL;
	for (Scope* cur = scope; cur != NULL; cur = cur->parent)
		if (cur->kind == ScopeKind::Namespace && cur->name == "std")
			return true;
	return false;
}

}  // namespace

bool lowir_synthesizable_noop_constructor(const Binding* binding)
{
	if (binding == NULL ||
	    !is_class_constructor_binding(binding) ||
	    binding->type.get() == NULL ||
	    binding->type->kind != TypeKind::Function ||
	    binding->type->parameters.empty())
		return false;
	TypePtr record = class_record_for_member(binding);
	record = record.get() != NULL ? pa11::strip_cv(record) : TypePtr();
	if (record.get() == NULL || record->kind != TypeKind::Record)
		return false;
	if (binding->is_generated_default_constructor &&
	    binding->is_noop_constructor &&
	    !binding->is_object_root)
		return false;
	string primary = record->template_primary_name.empty()
		? (record->scope != NULL ? record->scope->name : record->name)
		: record->template_primary_name;
	size_t qpos = primary.rfind("::");
	if (qpos != string::npos)
		primary = primary.substr(qpos + 2);
	bool hosted_allocator_ctor =
		primary == "allocator" &&
		(binding->type->parameters.size() == 1 ||
		 binding->type->parameters.size() == 2);
	if (!hosted_allocator_ctor)
		return false;
	return !record->is_polymorphic &&
	       pa11::record_virtual_bases(record).empty();
}

bool lowir_synthesizable_defaulted_storage_copy_constructor(
	const Binding* binding)
{
	if (binding == NULL ||
	    !binding->is_generated_copy_move_constructor ||
	    !binding->is_defaulted ||
	    !binding->is_inline_definition ||
	    binding->type.get() == NULL ||
	    binding->type->kind != TypeKind::Function ||
	    binding->type->parameters.size() != 2 ||
	    !is_reference(binding->type->parameters[1]))
		return false;
	TypePtr record = class_record_for_member(binding);
	record = record.get() != NULL ? pa11::strip_cv(record) : TypePtr();
	if (record.get() == NULL ||
	    record->kind != TypeKind::Record ||
	    !record_has_storage_copy(record))
		return false;
	TypePtr source = pa11::strip_cv(binding->type->parameters[1]->base);
	if (!pa11::same_type(source, record))
		return false;
	return !defaulted_copy_move_constructor_needs_helper(
		const_cast<Binding*>(binding), record);
}

bool lowir_hosted_tree_copy_move_constructor(const Binding* binding)
{
	if (!copy_move_constructor_binding(binding))
		return false;
	TypePtr record = class_record_for_member(binding);
	record = record.get() != NULL ? pa11::strip_cv(record) : TypePtr();
	return record.get() != NULL &&
	       record->kind == TypeKind::Record &&
	       record->scope != NULL &&
	       record->scope->name == "_Rb_tree";
}

Node lowir_make_defaulted_storage_copy_constructor_node(
	const Binding* binding)
{
	Node fn("function-definition");
	fn.binding = const_cast<Binding*>(binding);
	fn.type = binding->type;
	Node this_param("parameter this");
	this_param.type = binding->type->parameters[0];
	fn.children.push_back(this_param);
	Node other_param("parameter other");
	other_param.type = binding->type->parameters[1];
	fn.children.push_back(other_param);
	fn.children.push_back(Node("compound-statement"));
	return fn;
}

bool lowir_extern_template_class_external_binding(const Binding* binding)
{
	TypePtr record = class_record_for_member(binding);
	record = record.get() != NULL ? pa11::strip_cv(record) : TypePtr();
	if (record.get() == NULL)
		return false;
	bool hosted_string =
		unqualified_template_primary(record) == "basic_string" &&
		record_is_in_std_namespace(record);
	if (hosted_string)
		return is_class_constructor_binding(binding) ||
		       is_class_destructor_binding(binding) ||
		       binding->name == "operator=";
	if (!extern_template_class_binding(binding))
		return false;
	return record_uses_hosted_external_stream_vtable(record);
}

}  // namespace internal
}  // namespace pa14
