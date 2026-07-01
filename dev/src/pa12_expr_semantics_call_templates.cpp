#include "pa12_expr_semantics_call_template_instantiator.h"
#include "pa12_expr_semantics_support.h"
#include "pa12_templates_function_support.h"
#include "pa12_types_support.h"

#include <algorithm>
#include <cstdint>
#include <stdexcept>

using namespace std;

namespace pa12 {
namespace internal {

size_t dependent_cache_hash_combine(size_t seed, size_t value);
size_t dependent_cache_template_argument_identity(
	const TemplateArgument& argument,
	int depth);
size_t dependent_cache_type_identity(TypePtr type);


bool TemplateCallCandidateInstantiator::cached_function_type_dependent()
{
	return cached_binding_type_dependent(fn);
}

bool TemplateCallCandidateInstantiator::cached_binding_type_dependent(
	Binding* binding)
{
	if (binding == NULL || binding->type.get() == NULL)
		return false;
	pair<Binding*, const void*> key(binding, binding->type.get());
	map<pair<Binding*, const void*>, bool>::iterator found =
		p.function_template_type_dependency_cache_.find(key);
	if (found != p.function_template_type_dependency_cache_.end())
		return found->second;
	bool dependent = p.type_is_template_dependent(binding->type);
	p.function_template_type_dependency_cache_[key] = dependent;
	return dependent;
}

bool TemplateCallCandidateInstantiator::member_call_owner_matches(
	Binding* binding) const
{
	if (binding == NULL ||
	    binding->owner == NULL ||
	    binding->owner->kind != ScopeKind::Class ||
	    binding->is_static_member ||
	    binding->type.get() == NULL ||
	    binding->type->kind != pa11::TypeKind::Function ||
	    binding->type->parameters.empty() ||
	    args.empty())
		return true;
	TypePtr this_param = pa11::strip_cv(binding->type->parameters[0]);
	if (this_param.get() == NULL ||
	    this_param->kind != pa11::TypeKind::Pointer)
		return true;
	TypePtr this_record = this_param->base.get() != NULL
		? pa11::strip_cv(this_param->base) : TypePtr();
	TypePtr object_type = p.expression_object_type(args[0].type);
	object_type = object_type.get() != NULL
		? pa11::strip_cv(object_type) : TypePtr();
	if (object_type.get() != NULL &&
	    object_type->kind == pa11::TypeKind::Pointer)
		object_type = object_type->base.get() != NULL
			? pa11::strip_cv(object_type->base) : TypePtr();
	TypePtr object_record = object_type.get() != NULL
		? pa11::strip_cv(object_type) : TypePtr();
	if (this_record.get() == NULL ||
	    object_record.get() == NULL ||
	    this_record->kind != pa11::TypeKind::Record ||
	    object_record->kind != pa11::TypeKind::Record)
		return true;
	if (object_record->is_template_specialization &&
	    this_record->is_template_specialization &&
	    !object_record->template_primary_name.empty() &&
	    object_record->template_primary_name ==
		    this_record->template_primary_name)
		return pa11::same_type(object_record, this_record);
	if (pa11::same_type(object_record, this_record) ||
	    same_template_signature_type(object_record, this_record))
		return true;
	return p.record_base_distance(object_record, this_record) < 1000000;
}

Binding* TemplateCallCandidateInstantiator::canonical_call_binding(
	Binding* binding) const
{
	Binding* canonical = canonical_function_binding(binding);
	if (canonical != binding && !member_call_owner_matches(canonical))
		return binding;
	return canonical;
}

bool TemplateCallCandidateInstantiator::load_template_declaration()
{
	map<Binding*, TemplateDeclaration*>::iterator template_it =
		p.function_template_placeholders_.find(fn);
	if (template_it == p.function_template_placeholders_.end() &&
	    fn->aliased_binding != NULL)
	{
		placeholder = fn->aliased_binding;
		template_it = p.function_template_placeholders_.find(placeholder);
	}
	if (template_it == p.function_template_placeholders_.end())
		return false;
	fn_type_dependent = cached_function_type_dependent();
	bool call_has_explicit_args =
		explicit_template_arguments.find(fn) != explicit_template_arguments.end() ||
		(placeholder != fn &&
		 explicit_template_arguments.find(placeholder) != explicit_template_arguments.end());
	if (p.function_template_specialization_arguments_.find(fn) !=
	        p.function_template_specialization_arguments_.end() &&
	    !fn_type_dependent && !call_has_explicit_args)
		return false;
	original_declaration = template_it->second;
	placeholder_candidate = original_declaration->placeholder == placeholder;
	specialization_candidate = original_declaration->placeholder != NULL &&
		original_declaration->placeholder != fn;
	if (!placeholder_candidate && !specialization_candidate)
		return false;
	declaration = original_declaration;
	return true;
}

void TemplateCallCandidateInstantiator::choose_declaration_with_body()
{
	if (template_declaration_has_body(p.tokens_, declaration))
		return;
	map<Scope*, map<string, vector<TemplateDeclaration*> > >::iterator sit =
		p.function_templates_.find(declaration->owner);
	if (sit == p.function_templates_.end())
		return;
	map<string, vector<TemplateDeclaration*> >::iterator it =
		sit->second.find(declaration->name);
	if (it == sit->second.end())
		return;
	for (size_t i = 0; i < it->second.size(); ++i)
	{
		TemplateDeclaration* candidate = it->second[i];
		if (candidate == declaration ||
		    !template_declaration_has_body(p.tokens_, candidate) ||
		    candidate->generic_function_type.get() == NULL ||
		    !same_template_signature_type(candidate->generic_function_type,
		                                  declaration->generic_function_type) ||
		    !expr_template_parameter_lists_match(candidate->parameters,
		                                         declaration->parameters))
			continue;
		declaration = candidate;
		break;
	}
}

}  // namespace internal
}  // namespace pa12
