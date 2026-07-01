#include "pa12_templates_type_substitution_engine.h"
#include "pa12_types_support.h"

#include <algorithm>

using namespace std;

namespace pa12 {
namespace internal {

Binding* TypeSubstitutionEngine::member_record_binding(Scope* owner,
                                                       const TypePtr& type) const
{
	if (owner == NULL || type.get() == NULL)
		return NULL;
	string member_name = type->scope != NULL ? type->scope->name : string();
	if (!member_name.empty())
	{
		Binding* found =
			pa11::find_owned_binding(owner, member_name, BindingKind::Type);
		if (found != NULL &&
		    found->type.get() != NULL &&
		    pa11::strip_cv(found->type).get() == type.get())
			return found;
	}
	for (size_t i = 0; i < owner->binding_order.size(); ++i)
	{
		Binding* binding = owner->binding_order[i];
		if (binding == NULL ||
		    binding->kind != BindingKind::Type ||
		    binding->type.get() == NULL)
			continue;
		if (pa11::strip_cv(binding->type).get() == type.get())
			return binding;
	}
	return NULL;
}

TypeSubstitutionResult
TypeSubstitutionEngine::substitute_member_record_owner(const TypePtr& type) const
{
	if (type->kind != pa11::TypeKind::Record)
		return TypeSubstitutionResult::none();
	Scope* owner_scope = NULL;
	map<const void*, Scope*>::const_iterator owner =
		p.record_owner_scopes_.find(type.get());
	if (owner != p.record_owner_scopes_.end())
		owner_scope = owner->second;
	else if (type->scope != NULL)
		owner_scope = type->scope->parent;
	if (owner_scope == NULL || owner_scope->kind != ScopeKind::Class)
		return TypeSubstitutionResult::none();
	TypePtr owner_record = pa11::record_type_for_scope(owner_scope);
	owner_record = owner_record.get() != NULL
		? pa11::strip_cv(owner_record) : TypePtr();
	if (owner_record.get() == NULL ||
	    owner_record->kind != pa11::TypeKind::Record)
		return TypeSubstitutionResult::none();
	TypePtr substituted_owner = p.substitute_template_type(owner_record);
	substituted_owner = substituted_owner.get() != NULL
		? pa11::strip_cv(substituted_owner) : TypePtr();
	if (substituted_owner.get() == NULL ||
	    substituted_owner->kind != pa11::TypeKind::Record ||
	    substituted_owner->scope == NULL ||
	    substituted_owner->scope == owner_scope)
		return TypeSubstitutionResult::none();
	Binding* binding = member_record_binding(owner_scope, type);
	if (binding == NULL)
		return TypeSubstitutionResult::none();
	Binding* rebound =
		const_cast<Parser*>(&p)->complete_member_class_template_record(
			binding,
			substituted_owner->scope);
	if (rebound == NULL || rebound->type.get() == NULL)
		return TypeSubstitutionResult::none();
	TypePtr rebound_bare = pa11::strip_cv(rebound->type);
	if (rebound_bare.get() == type.get())
		return TypeSubstitutionResult::none();
	return TypeSubstitutionResult::done(rebound->type);
}

TypeSubstitutionResult TypeSubstitutionEngine::substitute_record(
	const TypePtr& type) const
{
	if (type->kind != pa11::TypeKind::Record ||
	    !type->is_template_specialization)
		return TypeSubstitutionResult::none();
	if (!type_structurally_dependent(type) &&
	    !record_arguments_are_still_dependent(type))
		return TypeSubstitutionResult::done(type);
	string primary_name = record_primary_name(type);
	TypeSubstitutionResult templ =
		substitute_template_template_record(type, primary_name);
	if (templ.handled)
		return templ;
	vector<TemplateArgument> fallback_args;
	const vector<TemplateArgument>* source_args = NULL;
	record_source_arguments(type, fallback_args, source_args);
	TemplateDeclaration* record_decl =
		find_record_declaration(type, primary_name, source_args);
	if (record_decl != NULL &&
	    find(p.completing_class_template_arguments_.begin(),
	         p.completing_class_template_arguments_.end(),
	         record_decl) != p.completing_class_template_arguments_.end())
		return TypeSubstitutionResult::done(type);
	TypeSubstitutionResult pack =
		substitute_primary_pack_record(type, record_decl);
	if (pack.handled)
		return pack;
	if (record_decl != NULL && source_args != NULL)
		return instantiate_substituted_record(type, record_decl, *source_args);
	return TypeSubstitutionResult::done(type);
}

}  // namespace internal
}  // namespace pa12
