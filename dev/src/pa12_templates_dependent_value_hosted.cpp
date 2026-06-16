#include "pa12_templates_instance_support.h"
#include "pa12_types_support.h"

#include <stdexcept>

using namespace std;

namespace pa12 {
namespace internal {

TypePtr Parser::hosted_dependent_value_traits_record(
	const string& owner_parameter) const
{
	TypePtr traits_type;
	find_template_type_substitution(owner_parameter, traits_type);
	try
	{
		if (traits_type.get() != NULL)
			traits_type = substitute_template_type(traits_type);
		else
			traits_type = substitute_template_type(
				pa11::make_template_parameter_type(owner_parameter));
	}
	catch (const runtime_error&)
	{
	}
	TypePtr traits_record = traits_type.get() != NULL
		? pa11::strip_cv(traits_type) : TypePtr();
	if (traits_record.get() == NULL ||
	    traits_record->is_dependent_typename ||
	    traits_record->kind == pa11::TypeKind::TemplateParameter)
	{
		for (size_t ai = active_class_instantiations_.size();
		     ai > 0 && (traits_record.get() == NULL ||
			        traits_record->is_dependent_typename ||
			        traits_record->kind == pa11::TypeKind::TemplateParameter);
		     --ai)
		{
			const ActiveClassInstantiation& active =
				active_class_instantiations_[ai - 1];
			if (active.declaration == NULL)
				continue;
			size_t param_index = active.declaration->parameters.size();
			for (size_t pi = 0;
			     pi < active.declaration->parameters.size();
			     ++pi)
				if (active.declaration->parameters[pi].name ==
				    owner_parameter)
				{
					param_index = pi;
					break;
				}
			if (param_index == active.declaration->parameters.size())
				continue;
			TypePtr active_record = active.type.get() != NULL
				? pa11::strip_cv(active.type) : TypePtr();
			if (active_record.get() == NULL ||
			    active_record->kind != pa11::TypeKind::Record)
				continue;
			vector<TemplateArgument> active_args;
			map<const void*, vector<TemplateArgument> >::const_iterator
				active_stored =
					record_template_arguments_.find(active_record.get());
			if (active_stored != record_template_arguments_.end())
				active_args = active_stored->second;
			else
				for (size_t ti = 0;
				     ti < active_record->template_arguments.size();
				     ++ti)
					active_args.push_back(
						template_argument_from_instance_argument(
							active_record->template_arguments[ti]));
			active_args = flatten_template_argument_packs(active_args);
			if (param_index < active_args.size() &&
			    active_args[param_index].kind == TemplateArgumentKind::Type)
			{
				TypePtr candidate =
					pa11::strip_cv(active_args[param_index].type);
				if (candidate.get() != NULL &&
				    !candidate->is_dependent_typename &&
				    candidate->kind != pa11::TypeKind::TemplateParameter)
					traits_record = candidate;
			}
		}
	}
	string primary = traits_record.get() != NULL
		? (traits_record->template_primary_name.empty()
		   ? traits_record->name
		   : traits_record->template_primary_name)
		: string();
	size_t primary_sep = primary.rfind("::");
	if (primary_sep != string::npos)
		primary = primary.substr(primary_sep + 2);
	size_t primary_args = primary.find('<');
	if (primary_args != string::npos)
		primary = primary.substr(0, primary_args);
	return traits_record.get() != NULL &&
	       traits_record->kind == pa11::TypeKind::Record &&
	       primary == "_Hashtable_traits"
		? traits_record : TypePtr();
}

bool Parser::resolve_hosted_dependent_value_member_argument(
	const TemplateArgument& arg,
	TemplateArgument& out) const
{
	if (!hosted_compatibility_ ||
	    (arg.value_member_name != "value" &&
	     arg.value_member_name != "__value"))
		return false;
	size_t owner_sep = arg.value_owner_template_name.rfind("::");
	if (owner_sep == string::npos)
		return false;
	string owner_parameter =
		arg.value_owner_template_name.substr(0, owner_sep);
	string trait_member =
		arg.value_owner_template_name.substr(owner_sep + 2);
	int trait_index = -1;
	if (trait_member == "__hash_cached")
		trait_index = 0;
	else if (trait_member == "__constant_iterators")
		trait_index = 1;
	else if (trait_member == "__unique_keys")
		trait_index = 2;
	if (trait_index < 0)
		return false;
	TypePtr traits_record =
		hosted_dependent_value_traits_record(owner_parameter);
	if (traits_record.get() != NULL)
	{
		vector<TemplateArgument> trait_args;
		map<const void*, vector<TemplateArgument> >::const_iterator stored =
			record_template_arguments_.find(traits_record.get());
		if (stored != record_template_arguments_.end())
			trait_args = stored->second;
		else
			for (size_t i = 0;
			     i < traits_record->template_arguments.size();
			     ++i)
				trait_args.push_back(
					template_argument_from_instance_argument(
						traits_record->template_arguments[i]));
		trait_args = flatten_template_argument_packs(trait_args);
		if (static_cast<size_t>(trait_index) < trait_args.size() &&
		    trait_args[trait_index].kind == TemplateArgumentKind::Value &&
		    !trait_args[trait_index].dependent)
		{
			bool value = trait_args[trait_index].value != 0;
			TemplateArgument result = TemplateArgument::value_arg(
				pa11::make_fundamental(FT_BOOL),
				arg.value_negated ? (value ? 0 : 1)
				                  : (value ? 1 : 0));
			result.value_name = arg.value_name;
			out = result;
			return true;
		}
	}
	out = arg;
	return true;
}

}  // namespace internal
}  // namespace pa12
