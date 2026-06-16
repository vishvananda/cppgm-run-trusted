#include "pa14_lowir_internal.h"
#include "pa12_types_support.h"

#include <set>

namespace pa11 {
bool complete_hosted_record_layout(TypePtr type);
}

namespace pa14 {
namespace internal {

bool function_signature_has_unresolved_storage(const Binding* binding);

namespace {

bool value_storage_unresolved(TypePtr type,
                              set<const void*>& seen,
                              bool allow_unknown_bound_array = false);
bool node_tree_storage_unresolved(const Node& node,
                                  bool generated_lifecycle_body);

bool generated_lifecycle_binding(const Binding* binding)
{
	return binding != NULL &&
	       (binding->is_generated_default_constructor ||
	        binding->is_generated_aggregate_constructor ||
	        binding->is_generated_copy_move_constructor ||
	        binding->is_generated_copy_move_assignment ||
	        binding->is_generated_default_destructor);
}

bool concrete_replayed_function_binding(const Binding* binding)
{
	if (binding == NULL || function_signature_has_unresolved_storage(binding))
		return false;
	if (!binding->function_specialization_symbol.empty())
		return true;
	TypePtr owner = class_record_for_member(binding);
	owner = owner.get() != NULL ? pa11::strip_cv(owner) : TypePtr();
	return owner.get() != NULL &&
	       owner->kind == TypeKind::Record &&
	       owner->is_template_specialization;
}

bool dependent_type_storage(TypePtr type)
{
	TypePtr bare = type.get() != NULL ? pa11::strip_cv(type) : TypePtr();
	return bare.get() != NULL &&
	       (bare->is_dependent_typename ||
	        bare->kind == TypeKind::TemplateParameter ||
	        bare->kind == TypeKind::TemplateTemplateParameter);
}

bool record_member_storage_unresolved(TypePtr record,
                                      set<const void*>& seen)
{
	TypePtr bare = pa11::strip_cv(record);
	if (bare->scope == NULL)
		return false;
	for (size_t i = 0; i < bare->scope->binding_order.size(); ++i)
	{
		Binding* member = bare->scope->binding_order[i];
		if (member->kind != BindingKind::Variable ||
		    member->is_static_member ||
		    member->aliased_binding != NULL)
			continue;
		if (value_storage_unresolved(member->type, seen))
			return true;
	}
	return false;
}

bool record_existing_field_storage_unresolved(TypePtr record,
                                             set<const void*>& seen)
{
	TypePtr bare = pa11::strip_cv(record);
	for (size_t i = 0; i < bare->fields.size(); ++i)
		if (bare->fields[i] != NULL &&
		    value_storage_unresolved(bare->fields[i]->type, seen))
			return true;
	return false;
}

bool record_base_storage_unresolved(TypePtr record, set<const void*>& seen)
{
	TypePtr bare = pa11::strip_cv(record);
	vector<TypePtr> bases = bare->direct_bases;
	if (bases.empty() && bare->base.get() != NULL)
		bases.push_back(bare->base);
	for (size_t i = 0; i < bases.size(); ++i)
		if (value_storage_unresolved(bases[i], seen))
			return true;
	for (size_t i = 0; i < bare->virtual_bases.size(); ++i)
		if (value_storage_unresolved(bare->virtual_bases[i], seen))
			return true;
	return false;
}

bool record_storage_unresolved(TypePtr record, set<const void*>& seen)
{
	TypePtr bare = pa11::strip_cv(record);
	if (!seen.insert(bare.get()).second)
		return false;
	if (pa12::internal::type_structurally_dependent(bare))
		return true;
	if (!bare->complete && !pa11::complete_hosted_record_layout(bare))
		return true;
	return record_base_storage_unresolved(bare, seen) ||
	       record_member_storage_unresolved(bare, seen) ||
	       record_existing_field_storage_unresolved(bare, seen);
}

bool value_storage_unresolved(TypePtr type,
                              set<const void*>& seen,
                              bool allow_unknown_bound_array)
{
	TypePtr bare = type.get() != NULL ? pa11::strip_cv(type) : TypePtr();
	if (bare.get() == NULL)
		return false;
	if (dependent_type_storage(bare))
		return true;
	if (bare->kind == TypeKind::Array)
		return (!allow_unknown_bound_array && bare->unknown_bound) ||
		       value_storage_unresolved(bare->base, seen);
	if (bare->kind == TypeKind::Record)
		return record_storage_unresolved(bare, seen);
	return false;
}

bool node_allows_unknown_bound_array_reference(const Node& node,
                                               bool generated_context)
{
	if (!generated_context)
		return false;
	return !starts_with(node.line, "variable ") &&
	       !starts_with(node.line, "parameter ") &&
	       !starts_with(node.line, "field ");
}

bool node_tree_storage_unresolved(const Node& node,
                                  bool generated_lifecycle_body)
{
	set<const void*> seen;
	bool generated_context =
		generated_lifecycle_body ||
		generated_lifecycle_binding(node.binding) ||
		concrete_replayed_function_binding(node.binding);
	if (!generated_context &&
	    pa12::internal::expr_node_structurally_dependent(node))
		return true;
		bool allow_unknown_bound_array =
			node_allows_unknown_bound_array_reference(node,
			                                          generated_context);
		if (value_storage_unresolved(node.type,
		                             seen,
		                             allow_unknown_bound_array))
			return true;
		if (node.binding != NULL &&
	    (function_signature_has_unresolved_storage(node.binding) ||
	     value_storage_unresolved(
		     node.binding->type,
		     seen,
		     allow_unknown_bound_array &&
		     node.binding->kind == BindingKind::Variable &&
		     node.binding->is_static_member)))
			return true;
	if (function_signature_has_unresolved_storage(node.direct_call))
		return true;
	for (size_t i = 0; i < node.children.size(); ++i)
		if (node_tree_storage_unresolved(node.children[i],
		                                 generated_context))
			return true;
	return false;
}

}  // namespace

bool function_signature_has_unresolved_storage(const Binding* binding)
{
	if (binding == NULL ||
	    binding->type.get() == NULL ||
	    binding->type->kind != TypeKind::Function)
		return false;
	set<const void*> seen;
	if (value_storage_unresolved(binding->type->base, seen))
		return true;
	for (size_t i = 0; i < binding->type->parameters.size(); ++i)
		if (value_storage_unresolved(binding->type->parameters[i], seen))
			return true;
	return false;
}

bool node_tree_has_unresolved_storage(const Node& node)
{
	return node_tree_storage_unresolved(node, false);
}

}  // namespace internal
}  // namespace pa14
