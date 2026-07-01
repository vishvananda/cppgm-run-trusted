#include "pa12_internal.h"

namespace pa12 {
namespace internal {
namespace {
bool defaulted_default_constructor_binding(Binding* function)
{
	return function != NULL &&
	       function->owner != NULL &&
	       function->owner->kind == ScopeKind::Class &&
	       function->type.get() != NULL &&
	       function->type->kind == pa11::TypeKind::Function &&
	       function->type->parameters.size() == 1 &&
	       function->name == function->owner->name;
}
}

bool Parser::can_demand_lowir_function_body(Binding* function) const
{
	return !defer_hosted_function_body(function);
}

	bool Parser::demand_lowir_function_body(Binding* function)
	{
		if (function == NULL || function_template_candidate_instantiation_depth_ != 0)
			return false;
	if (function->is_extern_template_instantiation)
		return false;
	if (defaulted_default_constructor_binding(function))
	{
		TypePtr owner_record = pa11::record_type_for_scope(function->owner);
		if (owner_record.get() != NULL)
			ensure_default_constructor(owner_record);
	}
	if (function->owner != NULL && function->owner->kind == ScopeKind::Class)
	{
		TypePtr owner_record = pa11::record_type_for_scope(function->owner);
		owner_record = owner_record.get() != NULL ? pa11::strip_cv(owner_record) : TypePtr();
		if (owner_record.get() != NULL &&
		    owner_record->kind == pa11::TypeKind::Record &&
		    owner_record->is_template_specialization &&
		    !(hosted_compatibility_ &&
		      hosted_library_function(function)))
			instantiate_member_function_templates(owner_record,
			                                      function->is_object_root);
	}
	auto demand_function_template_specialization_body = [this](Binding* target) {
		if (target == NULL ||
		    function_bodies_.find(target) != function_bodies_.end())
			return;
		map<Binding*, TemplateDeclaration*>::iterator declaration =
			function_template_placeholders_.find(target);
		map<Binding*, vector<TemplateArgument> >::iterator args =
			function_template_specialization_arguments_.find(target);
		TemplateDeclaration* source =
			declaration != function_template_placeholders_.end()
			? replacement_function_template_definition(declaration->second)
			: NULL;
		if (declaration == function_template_placeholders_.end() ||
		    source == NULL ||
		    !source->has_definition ||
		    args == function_template_specialization_arguments_.end())
			return;
		function_template_placeholders_[target] = source;
		instantiate_function_template(source, args->second);
	};
	demand_function_template_specialization_body(function);
	if (function->aliased_binding != NULL)
		demand_function_template_specialization_body(function->aliased_binding);
		size_t before = extra_lowir_nodes_.size();
		parse_pending_function_body(function);
		parse_pending_member_body(function);
	if (function->aliased_binding != NULL)
	{
		parse_pending_function_body(function->aliased_binding);
		parse_pending_member_body(function->aliased_binding);
	}
	ensure_function_body_extra_node(function, true);
		if (function->aliased_binding != NULL)
			ensure_function_body_extra_node(function->aliased_binding, true);
		return extra_lowir_nodes_.size() != before;
	}

}  // namespace internal
}  // namespace pa12
