#include "pa12_expr_semantics_support.h"
#include "pa12_templates_function_support.h"
#include "pa12_templates_instance_support.h"
#include <algorithm>
#include <cstdint>
#include <sstream>
#include <stdexcept>
#include <utility>
#include "posttoken_pipeline.h"
#include "pp_token.h"
using namespace std;
namespace pa12 {
namespace internal {
bool member_parameter_names_have_non_this(const vector<string>& names);
TypePtr remap_template_parameter_names(TypePtr type, const map<string, string>& names);
map<string, string> template_parameter_name_map(const vector<TemplateParameterInfo>& from, const vector<TemplateParameterInfo>& to);
void build_owner_template_substitutions(const vector<TemplateArgument>& owner_arguments, TemplateDeclaration* owner_declaration, map<string, TypePtr>& subst, map<string, TemplateArgument>& value_subst, set<string>& pack_subst);
void copy_member_template_placeholder_state(Binding* placeholder, Binding* source, map<Binding*, vector<string> >& function_parameter_names, map<Binding*, vector<Expr> >& default_arguments, bool copy_static_member);
void assign_member_template_alias_state(Binding* alias, Binding* source);
void merge_member_template_alias_state(Binding* concrete, Binding* source);
bool ordinary_member_definition_matches_placeholder(const TemplateDeclaration* declaration, Binding* function, const vector<Token>& tokens);
TypePtr rebind_nested_constructor_self_type(TypePtr type, TypePtr current);
bool class_constructor_binding_name(const Binding* binding)
{
	return binding != NULL &&
	       binding->owner != NULL &&
	       binding->owner->kind == ScopeKind::Class &&
	       binding->name == binding->owner->name;
}
bool class_destructor_binding_name(const Binding* binding)
{
	return binding != NULL &&
	       binding->owner != NULL &&
	       binding->owner->kind == ScopeKind::Class &&
	       binding->name == "~" + binding->owner->name;
}
bool special_member_alias_mismatch(const Binding* left, const Binding* right)
{
	bool left_ctor = class_constructor_binding_name(left);
	bool right_ctor = class_constructor_binding_name(right);
	bool left_dtor = class_destructor_binding_name(left);
	bool right_dtor = class_destructor_binding_name(right);
	if (!(left_ctor || right_ctor || left_dtor || right_dtor))
		return false;
	return left_ctor != right_ctor || left_dtor != right_dtor;
}
struct ActiveMemberInstantiationGuard
{
	set<pair<const void*, bool> >& active;
	pair<const void*, bool> key;
	ActiveMemberInstantiationGuard(set<pair<const void*, bool> >& active_records,
	                               pair<const void*, bool> active_key)
		: active(active_records), key(active_key) {}
	~ActiveMemberInstantiationGuard() { active.erase(key); }
};
void Parser::instantiate_member_function_templates(TypePtr type, bool object_root)
{
	TypePtr bare = pa11::strip_cv(type);
	if (bare->kind != pa11::TypeKind::Record)
		return;
	pair<const void*, bool> cache_key(bare.get(), object_root);
	map<pair<const void*, bool>, size_t>::iterator completed = completed_member_function_template_records_.find(cache_key);
	if ((completed != completed_member_function_template_records_.end() &&
	     completed->second == member_function_template_generation_) ||
	    active_member_function_template_records_.count(cache_key) != 0)
		return;
	size_t save_pos = pos_;
	vector<Scope*> save_scopes = scopes_;
	map<const void*, TemplateDeclaration*>::iterator outer = record_template_declarations_.find(bare.get());
	TemplateDeclaration* owner_declaration = outer != record_template_declarations_.end()
		? outer->second : NULL;
	map<const void*, vector<TemplateArgument> >::iterator args_it = record_template_arguments_.find(bare.get());
	vector<TemplateArgument> owner_arguments;
	if (args_it != record_template_arguments_.end())
		owner_arguments = args_it->second;
	else if (!bare->template_arguments.empty())
		for (size_t i = 0; i < bare->template_arguments.size(); ++i)
			owner_arguments.push_back(template_argument_from_instance_argument(bare->template_arguments[i]));
	vector<TemplateArgument> primary_owner_arguments;
	if (!bare->template_arguments.empty())
		for (size_t i = 0; i < bare->template_arguments.size(); ++i)
			primary_owner_arguments.push_back(template_argument_from_instance_argument(bare->template_arguments[i]));
	if (primary_owner_arguments.empty())
		primary_owner_arguments = owner_arguments;
	bool owner_arguments_still_dependent = false;
	for (size_t i = 0; i < owner_arguments.size(); ++i)
		if (template_argument_has_template_parameter(owner_arguments[i], record_template_arguments_))
			owner_arguments_still_dependent = true;
	if (owner_arguments_still_dependent &&
	    (owner_declaration == NULL ||
	     !owner_declaration->class_specialization) &&
	    !primary_owner_arguments.empty())
		owner_arguments = primary_owner_arguments;
	if (owner_declaration == NULL &&
	    bare->is_template_specialization &&
	    !bare->template_primary_name.empty())
	{
		owner_declaration = find_class_template(NULL, bare->template_primary_name);
		if (owner_declaration != NULL)
		{
			for (size_t i = 0; i < bare->template_arguments.size(); ++i)
				owner_arguments.push_back(template_argument_from_instance_argument(bare->template_arguments[i]));
			record_template_declarations_[bare.get()] = owner_declaration;
			record_template_arguments_[bare.get()] = owner_arguments;
		}
	}
	TemplateDeclaration* primary_owner_declaration = owner_declaration;
	if (owner_declaration != NULL &&
	    owner_declaration->class_specialization &&
	    bare->is_template_specialization &&
	    !bare->template_primary_name.empty())
	{
		TemplateDeclaration* primary = find_class_template(owner_declaration->owner, bare->template_primary_name);
		if (primary != NULL)
			primary_owner_declaration = primary;
	}
	if (owner_declaration == NULL ||
	    (owner_arguments.empty() && !owner_declaration->parameters.empty()))
		return;
	active_member_function_template_records_.insert(cache_key);
	ActiveMemberInstantiationGuard active_guard(
		active_member_function_template_records_, cache_key);
	for (map<pair<TemplateDeclaration*, string>, vector<TemplateDeclaration*> >::iterator it = member_function_templates_.begin(); it != member_function_templates_.end(); ++it)
	{
		if (it->first.first != owner_declaration &&
		    it->first.first != primary_owner_declaration)
			continue;
		bool have_matching_member_class_specialization = member_template_set_has_class_specialization(this, primary_owner_declaration, it->second, primary_owner_arguments, record_template_arguments_);
		for (size_t i = 0; i < it->second.size(); ++i)
		{
			TemplateDeclaration* declaration = it->second[i];
			if (!declaration->class_specialization &&
			    have_matching_member_class_specialization)
				continue;
			bool matching_owner_definition = member_template_definition_matches_owner(this, it->first.first, owner_declaration, primary_owner_declaration, declaration, primary_owner_arguments, record_template_arguments_);
			if (!matching_owner_definition)
				continue;
			if (rebind_out_of_class_member_template_definition(
				    bare, object_root, owner_declaration, owner_arguments, declaration))
				continue;
			if (clone_out_of_class_member_constructor_template(
				    bare, owner_declaration, owner_arguments, declaration))
				continue;
			if (clone_class_template_member_template(
				    bare, owner_declaration, owner_arguments, declaration))
				continue;
			instantiate_member_function_template_specialization(
				bare, object_root, owner_declaration, owner_arguments, declaration);
		}
	}
	scopes_ = save_scopes;
	pos_ = save_pos;
	completed_member_function_template_records_[cache_key] =
		member_function_template_generation_;
}
}  // namespace internal
}  // namespace pa12
