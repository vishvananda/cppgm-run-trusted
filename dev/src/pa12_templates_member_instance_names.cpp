#include "pa12_templates_instance_support.h"

#include <algorithm>
#include <map>
#include <set>
#include <string>
#include <vector>

using namespace std;

namespace pa12 {
namespace internal {

bool member_parameter_names_have_non_this(const vector<string>& names)
{
	for (size_t i = 0; i < names.size(); ++i)
		if (!names[i].empty() && names[i] != "this")
			return true;
	return false;
}

pa11::TemplateInstanceArgument remap_template_parameter_names(
	const pa11::TemplateInstanceArgument& argument,
	const map<string, string>& names);

bool remap_name_matches(const string& name, const map<string, string>& names)
{
	return !name.empty() && names.find(name) != names.end();
}

bool type_uses_remapped_parameter_name(TypePtr type,
                                       const map<string, string>& names);

bool instance_argument_uses_remapped_parameter_name(
	const pa11::TemplateInstanceArgument& argument,
	const map<string, string>& names)
{
	if (names.empty())
		return false;
	if (type_uses_remapped_parameter_name(argument.type, names))
		return true;
	if (remap_name_matches(argument.value_name, names) ||
	    remap_name_matches(argument.template_name, names) ||
	    remap_name_matches(argument.value_owner_template_name, names))
		return true;
	for (size_t i = 0; i < argument.pack.size(); ++i)
		if (instance_argument_uses_remapped_parameter_name(argument.pack[i],
		                                                   names))
			return true;
	for (size_t i = 0; i < argument.value_owner_template_arguments.size(); ++i)
		if (instance_argument_uses_remapped_parameter_name(
			    argument.value_owner_template_arguments[i],
			    names))
			return true;
	return false;
}

bool type_uses_remapped_parameter_name(TypePtr type,
                                       const map<string, string>& names)
{
	if (type.get() == NULL || names.empty())
		return false;
	if ((type->kind == pa11::TypeKind::TemplateParameter ||
	     type->kind == pa11::TypeKind::TemplateTemplateParameter) &&
	    remap_name_matches(type->name, names))
		return true;
	if (remap_name_matches(type->template_primary_name, names))
		return true;
	if (type_uses_remapped_parameter_name(type->base, names) ||
	    type_uses_remapped_parameter_name(type->member_class, names))
		return true;
	for (size_t i = 0; i < type->parameters.size(); ++i)
		if (type_uses_remapped_parameter_name(type->parameters[i], names))
			return true;
	for (size_t i = 0; i < type->template_arguments.size(); ++i)
		if (instance_argument_uses_remapped_parameter_name(
			    type->template_arguments[i],
			    names))
			return true;
	for (size_t i = 0;
	     i < type->dependent_typename_template_argument_lists.size();
	     ++i)
		for (size_t j = 0;
		     j < type->dependent_typename_template_argument_lists[i].size();
		     ++j)
			if (instance_argument_uses_remapped_parameter_name(
				    type->dependent_typename_template_argument_lists[i][j],
				    names))
				return true;
	return false;
}

TypePtr remap_template_parameter_names(TypePtr type,
                                       const map<string, string>& names)
{
	if (type.get() == NULL || names.empty() ||
	    !type_uses_remapped_parameter_name(type, names))
		return type;
	TypePtr out(new pa11::Type(*type));
	map<string, string>::const_iterator found = names.find(out->name);
	if ((out->kind == pa11::TypeKind::TemplateParameter ||
	     out->kind == pa11::TypeKind::TemplateTemplateParameter) &&
	    found != names.end())
		out->name = found->second;
	found = names.find(out->template_primary_name);
	if (found != names.end())
		out->template_primary_name = found->second;
	if (out->base.get() != NULL)
		out->base = remap_template_parameter_names(out->base, names);
	if (out->member_class.get() != NULL)
		out->member_class =
			remap_template_parameter_names(out->member_class, names);
	for (size_t i = 0; i < out->parameters.size(); ++i)
		out->parameters[i] =
			remap_template_parameter_names(out->parameters[i], names);
	for (size_t i = 0; i < out->template_arguments.size(); ++i)
		out->template_arguments[i] =
			remap_template_parameter_names(out->template_arguments[i],
			                               names);
	for (size_t i = 0;
	     i < out->dependent_typename_template_argument_lists.size();
	     ++i)
		for (size_t j = 0;
		     j < out->dependent_typename_template_argument_lists[i].size();
		     ++j)
			out->dependent_typename_template_argument_lists[i][j] =
				remap_template_parameter_names(
					out->dependent_typename_template_argument_lists[i][j],
					names);
	return out;
}

pa11::TemplateInstanceArgument remap_template_parameter_names(
	const pa11::TemplateInstanceArgument& argument,
	const map<string, string>& names)
{
	if (names.empty() ||
	    !instance_argument_uses_remapped_parameter_name(argument, names))
		return argument;
	pa11::TemplateInstanceArgument out = argument;
	if (out.kind == pa11::TemplateInstanceArgumentKind::Type)
		out.type = remap_template_parameter_names(out.type, names);
	else if (out.kind == pa11::TemplateInstanceArgumentKind::Value) {
		out.type = remap_template_parameter_names(out.type, names);
		map<string, string>::const_iterator found =
			names.find(out.value_name);
		if (found != names.end())
			out.value_name = found->second;
		for (size_t i = 0; i < out.value_owner_template_arguments.size(); ++i)
			out.value_owner_template_arguments[i] =
				remap_template_parameter_names(
					out.value_owner_template_arguments[i],
					names);
	} else if (out.kind == pa11::TemplateInstanceArgumentKind::Template) {
		map<string, string>::const_iterator found =
			names.find(out.template_name);
		if (found != names.end())
			out.template_name = found->second;
	} else {
		for (size_t i = 0; i < out.pack.size(); ++i)
			out.pack[i] = remap_template_parameter_names(out.pack[i],
			                                             names);
	}
	return out;
}

map<string, string> template_parameter_name_map(
	const vector<TemplateParameterInfo>& from,
	const vector<TemplateParameterInfo>& to)
{
	map<string, string> names;
	size_t count = min(from.size(), to.size());
	for (size_t i = 0; i < count; ++i)
		if (!from[i].name.empty() &&
		    !to[i].name.empty() &&
		    from[i].name != to[i].name)
			names[from[i].name] = to[i].name;
	return names;
}

void build_owner_template_substitutions(
	const vector<TemplateArgument>& owner_arguments,
	TemplateDeclaration* owner_declaration,
	map<string, TypePtr>& subst,
	map<string, TemplateArgument>& value_subst,
	set<string>& pack_subst)
{
	if (owner_declaration == NULL)
		return;
	for (size_t k = 0;
	     k < owner_arguments.size() &&
	     k < owner_declaration->parameters.size();
	     ++k) {
		const TemplateParameterInfo& parameter =
			owner_declaration->parameters[k];
		if (parameter.name.empty())
			continue;
		if (parameter.kind == TemplateParameterKind::Type) {
			if (parameter.is_pack) {
				subst[parameter.name] =
					template_parameter_placeholder_type(parameter);
				value_subst[parameter.name] = owner_arguments[k];
				pack_subst.insert(parameter.name);
			} else {
				subst[parameter.name] = owner_arguments[k].type;
			}
		} else {
			value_subst[parameter.name] = owner_arguments[k];
		}
	}
}

void Parser::add_member_function_template(
	vector<TemplateDeclaration*>& members,
	TemplateDeclaration* declaration)
{
	if (find(members.begin(), members.end(), declaration) != members.end())
		return;
	members.push_back(declaration);
	++member_function_template_generation_;
}

}  // namespace internal
}  // namespace pa12
