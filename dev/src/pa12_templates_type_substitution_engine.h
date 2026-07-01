#pragma once

#include <string>
#include <vector>

#include "pa12_internal.h"

namespace pa12 {
namespace internal {

struct TypeSubstitutionResult
{
	bool handled;
	TypePtr type;
	static TypeSubstitutionResult none()
	{
		TypeSubstitutionResult result;
		result.handled = false;
		return result;
	}
	static TypeSubstitutionResult done(TypePtr type)
	{
		TypeSubstitutionResult result;
		result.handled = true;
		result.type = type;
		return result;
	}
};

struct ActiveDependentTypeSubstitution
{
	vector<size_t>& keys;
	vector<size_t>& types;
	ActiveDependentTypeSubstitution(vector<size_t>& k,
	                                 vector<size_t>& t,
	                                 size_t key,
	                                 const void* type)
	  : keys(k), types(t)
	{
		keys.push_back(key);
		types.push_back(reinterpret_cast<size_t>(type));
	}
	~ActiveDependentTypeSubstitution()
	{
		keys.pop_back();
		types.pop_back();
	}
};

struct TypeSubstitutionEngine
{
	const Parser& p;
	explicit TypeSubstitutionEngine(const Parser& parser) : p(parser) {}
	TypePtr substitute(const TypePtr& type) const;
	bool preserves_self_reference(const TypePtr& type) const;
	bool self_substitution_can_change(const TypePtr& type) const;
	TypeSubstitutionResult substitute_plain_dependent(const TypePtr& type) const;
	size_t active_dependent_key(const TypePtr& type) const;
	bool active_dependent_substitution(const TypePtr& type) const;
	bool concrete_substitution_context() const;
	bool has_template_substitution_name(const string& name) const;
	bool unresolved_foreign_decltype_template_argument(
		const TypePtr& type,
		const string& message) const;
	bool dependent_decltype_has_unsubstituted_template_argument(
		const TypePtr& type,
		const vector<Token>& tokens) const;
	TypeSubstitutionResult substitute_dependent_decltype(
		const TypePtr& type,
		bool replay_errors_are_hard) const;
	TypeSubstitutionResult substitute_dependent_arguments(
		const TypePtr& type,
		bool concrete_context) const;
	TypeSubstitutionResult substitute_dependent_builtin(const TypePtr& type) const;
	bool split_dependent_root(const TypePtr& type,
	                          string& root_name,
	                          string& suffix) const;
	bool find_dependent_root_substitution(const TypePtr& type,
	                                      const string& root_name,
	                                      TypePtr& root_subst) const;
	TypeSubstitutionResult substitute_dependent_qualified_root(
		const TypePtr& type,
		bool concrete_context) const;
	bool dependent_root_still_dependent(const TypePtr& type) const;
	bool dependent_primary_still_dependent(const TypePtr& type) const;
	bool dependent_arguments_still_dependent(const TypePtr& type) const;
	bool dependent_typename_still_dependent(const TypePtr& type) const;
	TypePtr substitute_dependent_typename(const TypePtr& type) const;
	TypeSubstitutionResult substitute_simple(const TypePtr& type) const;
	bool record_arguments_are_still_dependent(const TypePtr& type) const;
	string record_primary_name(const TypePtr& type) const;
	bool argument_count_too_large(TemplateDeclaration* declaration,
	                              const vector<TemplateArgument>& args) const;
	bool argument_count_too_small(TemplateDeclaration* declaration,
	                              const vector<TemplateArgument>& args) const;
	TypeSubstitutionResult substitute_template_template_record(
		const TypePtr& type,
		const string& primary_name) const;
	void record_source_arguments(const TypePtr& type,
	                             vector<TemplateArgument>& fallback_args,
	                             const vector<TemplateArgument>*& source_args) const;
	TemplateDeclaration* find_record_declaration(
		const TypePtr& type,
		const string& primary_name,
		const vector<TemplateArgument>* source_args) const;
	TypeSubstitutionResult substitute_primary_pack_record(
		const TypePtr& type,
		TemplateDeclaration* record_decl) const;
	vector<TemplateArgument> expand_substituted_record_argument(
		TemplateDeclaration* record_decl,
		const vector<TemplateArgument>& source_args,
		size_t& index) const;
	vector<TemplateArgument> substitute_record_arguments(
		TemplateDeclaration* record_decl,
		const vector<TemplateArgument>& source_args) const;
	TypeSubstitutionResult instantiate_substituted_record(
		const TypePtr& type,
		TemplateDeclaration* record_decl,
		const vector<TemplateArgument>& source_args) const;
	Binding* member_record_binding(Scope* owner, const TypePtr& type) const;
	TypeSubstitutionResult substitute_member_record_owner(const TypePtr& type) const;
	TypeSubstitutionResult substitute_record(const TypePtr& type) const;
};

}  // namespace internal
}  // namespace pa12
