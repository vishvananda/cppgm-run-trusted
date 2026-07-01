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

namespace {
pa11::TemplateInstanceArgument normalize_recovered_template_parameter(
	const pa11::TemplateInstanceArgument& argument,
	const set<string>& names,
	set<const void*>& active);

bool recovered_template_parameter_name_in_argument(
	const pa11::TemplateInstanceArgument& argument,
	const set<string>& names,
	set<const void*>& active);

bool recovered_template_parameter_name_in_type(TypePtr type,
                                               const set<string>& names,
                                               set<const void*>& active)
{
	if (type.get() == NULL || names.empty())
		return false;
	type = pa11::strip_cv(type);
	if (!active.insert(type.get()).second)
		return false;
	if ((type->kind == pa11::TypeKind::TemplateParameter ||
	     type->kind == pa11::TypeKind::TemplateTemplateParameter) &&
	    names.count(type->name) != 0)
		return true;
	if (type->base.get() != NULL &&
	    recovered_template_parameter_name_in_type(type->base, names, active))
		return true;
	if (type->member_class.get() != NULL &&
	    recovered_template_parameter_name_in_type(type->member_class,
	                                             names,
	                                             active))
		return true;
	for (size_t i = 0; i < type->parameters.size(); ++i)
		if (recovered_template_parameter_name_in_type(type->parameters[i],
		                                              names,
		                                              active))
			return true;
	for (size_t i = 0; i < type->template_arguments.size(); ++i)
		if (recovered_template_parameter_name_in_argument(
			    type->template_arguments[i],
			    names,
			    active))
			return true;
	for (size_t i = 0;
	     i < type->dependent_typename_template_argument_lists.size();
	     ++i)
		for (size_t j = 0;
		     j < type->dependent_typename_template_argument_lists[i].size();
		     ++j)
			if (recovered_template_parameter_name_in_argument(
				    type->dependent_typename_template_argument_lists[i][j],
				    names,
				    active))
				return true;
	return false;
}

bool recovered_template_parameter_name_in_type(TypePtr type,
                                               const set<string>& names)
{
	set<const void*> active;
	return recovered_template_parameter_name_in_type(type, names, active);
}

bool recovered_template_parameter_name_in_argument(
	const pa11::TemplateInstanceArgument& argument,
	const set<string>& names,
	set<const void*>& active)
{
	if (argument.kind == pa11::TemplateInstanceArgumentKind::Type)
		return recovered_template_parameter_name_in_type(argument.type,
		                                                 names,
		                                                 active);
	if (argument.kind == pa11::TemplateInstanceArgumentKind::Value)
	{
		if (names.count(argument.value_name) != 0 ||
		    names.count(argument.value_owner_template_name) != 0)
			return true;
		if (recovered_template_parameter_name_in_type(argument.type,
		                                              names,
		                                              active))
			return true;
		for (size_t i = 0;
		     i < argument.value_owner_template_arguments.size();
		     ++i)
			if (recovered_template_parameter_name_in_argument(
				    argument.value_owner_template_arguments[i],
				    names,
				    active))
				return true;
		return false;
	}
	if (argument.kind == pa11::TemplateInstanceArgumentKind::Template)
		return names.count(argument.template_name) != 0 ||
		       names.count(argument.value_name) != 0;
	for (size_t i = 0; i < argument.pack.size(); ++i)
		if (recovered_template_parameter_name_in_argument(argument.pack[i],
		                                                  names,
		                                                  active))
			return true;
	return false;
}

TypePtr normalize_recovered_template_parameter(TypePtr type,
                                               const set<string>& names,
                                               set<const void*>& active)
{
	if (type.get() == NULL || names.empty())
		return type;
	if (type->kind == pa11::TypeKind::Record &&
	    type->is_template_specialization &&
	    !recovered_template_parameter_name_in_type(type, names))
		return type;
	if (!active.insert(type.get()).second)
		return type;
	TypePtr out(new pa11::Type(*type));
	if (out->kind == pa11::TypeKind::TemplateParameter &&
	    names.count(out->name) != 0 &&
	    out->is_dependent_typename &&
	    !out->dependent_typename_qualified &&
	    !out->dependent_typename_template_id &&
	    !out->dependent_typename_decltype)
	{
		out->is_dependent_typename = false;
	}
	if (out->base.get() != NULL)
		out->base =
			normalize_recovered_template_parameter(out->base,
			                                       names,
			                                       active);
	if (out->member_class.get() != NULL)
		out->member_class =
			normalize_recovered_template_parameter(out->member_class,
			                                       names,
			                                       active);
	for (size_t i = 0; i < out->parameters.size(); ++i)
		out->parameters[i] =
			normalize_recovered_template_parameter(out->parameters[i],
			                                       names,
			                                       active);
	for (size_t i = 0; i < out->template_arguments.size(); ++i)
		out->template_arguments[i] =
			normalize_recovered_template_parameter(out->template_arguments[i],
			                                       names,
			                                       active);
	for (size_t i = 0;
	     i < out->dependent_typename_template_argument_lists.size();
	     ++i)
		for (size_t j = 0;
		     j < out->dependent_typename_template_argument_lists[i].size();
		     ++j)
			out->dependent_typename_template_argument_lists[i][j] =
				normalize_recovered_template_parameter(
					out->dependent_typename_template_argument_lists[i][j],
					names,
					active);
	active.erase(type.get());
	return out;
}

pa11::TemplateInstanceArgument normalize_recovered_template_parameter(
	const pa11::TemplateInstanceArgument& argument,
	const set<string>& names,
	set<const void*>& active)
{
	if (names.empty())
		return argument;
	pa11::TemplateInstanceArgument out = argument;
	if (out.kind == pa11::TemplateInstanceArgumentKind::Type)
		out.type =
			normalize_recovered_template_parameter(out.type,
			                                       names,
			                                       active);
	else if (out.kind == pa11::TemplateInstanceArgumentKind::Value)
	{
		out.type =
			normalize_recovered_template_parameter(out.type,
			                                       names,
			                                       active);
		for (size_t i = 0; i < out.value_owner_template_arguments.size(); ++i)
			out.value_owner_template_arguments[i] =
				normalize_recovered_template_parameter(
					out.value_owner_template_arguments[i],
					names,
					active);
	}
	else if (out.kind == pa11::TemplateInstanceArgumentKind::Pack)
	{
		for (size_t i = 0; i < out.pack.size(); ++i)
			out.pack[i] =
				normalize_recovered_template_parameter(out.pack[i],
				                                       names,
				                                       active);
	}
	return out;
}

TypePtr normalize_recovered_template_parameter(TypePtr type,
                                               const set<string>& names)
{
	set<const void*> active;
	return normalize_recovered_template_parameter(type, names, active);
}

void collect_direct_function_template_parameters(
	TypePtr function_type,
	const vector<TemplateParameterInfo>& existing_parameters,
	vector<TemplateParameterInfo>& recovered_parameters)
{
	if (function_type.get() == NULL ||
	    function_type->kind != pa11::TypeKind::Function)
		return;
	for (size_t pi = 0; pi < function_type->parameters.size(); ++pi)
	{
		TypePtr pattern = pa11::strip_cv(function_type->parameters[pi]);
		while (pattern.get() != NULL &&
		       (pattern->kind == pa11::TypeKind::LValueReference ||
		        pattern->kind == pa11::TypeKind::RValueReference ||
		        pattern->kind == pa11::TypeKind::Pointer ||
		        pattern->kind == pa11::TypeKind::Array))
			pattern = pa11::strip_cv(pattern->base);
		if (pattern.get() == NULL ||
		    pattern->kind != pa11::TypeKind::TemplateParameter ||
		    pattern->name.empty())
			continue;
		bool direct_dependent_parameter =
			pattern->is_dependent_typename &&
			!pattern->dependent_typename_qualified &&
			!pattern->dependent_typename_template_id &&
			!pattern->dependent_typename_decltype;
		if (!pa11::is_deducible_template_parameter_type(pattern) &&
		    !direct_dependent_parameter)
			continue;
		const TemplateParameterInfo* declared_parameter = NULL;
		for (size_t di = 0; di < existing_parameters.size(); ++di)
			if (existing_parameters[di].name == pattern->name)
				declared_parameter = &existing_parameters[di];
		bool already_recovered = false;
		for (size_t ri = 0; ri < recovered_parameters.size(); ++ri)
			if (recovered_parameters[ri].name == pattern->name)
				already_recovered = true;
		if (!already_recovered)
		{
			if (declared_parameter != NULL)
				recovered_parameters.push_back(*declared_parameter);
			else
			{
				TemplateParameterInfo parameter;
				parameter.kind = TemplateParameterKind::Type;
				parameter.name = pattern->name;
				recovered_parameters.push_back(parameter);
			}
		}
	}
}

}  // namespace

void TemplateCallCandidateInstantiator::recover_effective_declaration()
{
	if (declaration->generic_function_type.get() == NULL ||
	    declaration->generic_function_type->kind != pa11::TypeKind::Function)
		return;
	vector<TemplateParameterInfo> recovered_parameters;
	TypePtr recovered_function_type = declaration->generic_function_type;
	collect_direct_function_template_parameters(
		declaration->generic_function_type, declaration->parameters,
		recovered_parameters);
	if (recovered_parameters.empty() && fn != NULL &&
	    fn->type.get() != NULL && fn->type->kind == pa11::TypeKind::Function)
	{
		collect_direct_function_template_parameters(
			fn->type, declaration->parameters, recovered_parameters);
		if (!recovered_parameters.empty())
			recovered_function_type = fn->type;
	}
	if (recovered_parameters.empty())
		return;
	pair<TemplateDeclaration*, const void*> cache_key(
		original_declaration,
		recovered_function_type.get());
	map<pair<TemplateDeclaration*, const void*>, TemplateDeclaration*>::
		iterator cached =
			p.recovered_function_template_declarations_.find(cache_key);
	if (cached != p.recovered_function_template_declarations_.end())
	{
		declaration = cached->second;
		recovered_effective_declaration = true;
		return;
	}
	bool only_declared = !declaration->parameters.empty();
	for (size_t ri = 0; ri < recovered_parameters.size(); ++ri)
	{
		bool declared = false;
		for (size_t di = 0; di < declaration->parameters.size(); ++di)
			if (declaration->parameters[di].name ==
			    recovered_parameters[ri].name)
				declared = true;
		if (!declared)
			only_declared = false;
	}
	unique_ptr<TemplateDeclaration> effective(new TemplateDeclaration(*declaration));
	effective->parameters = only_declared ? declaration->parameters : recovered_parameters;
	set<string> recovered_names;
	for (size_t ri = 0; ri < recovered_parameters.size(); ++ri)
		recovered_names.insert(recovered_parameters[ri].name);
	effective->generic_function_type =
		normalize_recovered_template_parameter(recovered_function_type,
		                                       recovered_names);
	effective->function_specializations.clear();
	effective->completing_specializations.clear();
	declaration = effective.get();
	p.template_declarations_.push_back(std::move(effective));
	p.recovered_function_template_declarations_[cache_key] = declaration;
	recovered_effective_declaration = true;
}

}  // namespace internal
}  // namespace pa12
