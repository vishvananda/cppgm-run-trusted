#include "pa12_templates_function_support.h"

#include <algorithm>
#include <functional>
#include <stdexcept>

using namespace std;

namespace pa12 {
namespace internal {

bool Parser::deduce_function_template_target_type(
	TemplateDeclaration* declaration,
	TypePtr target,
	const vector<TemplateArgument>& explicit_arguments,
	vector<TemplateArgument>& out)
{
	if (declaration->generic_function_type.get() == NULL ||
	    declaration->generic_function_type->kind != pa11::TypeKind::Function)
		return false;
	if (target.get() == NULL ||
	    pa11::strip_cv(target)->kind != pa11::TypeKind::Function ||
	    explicit_arguments.size() > declaration->parameters.size())
		return false;
	map<string, TypePtr> deduced;
	map<string, TypePtr> fixed;
	map<string, TemplateArgument> deduced_arguments;
	map<string, vector<TemplateArgument> > deduced_packs;
	for (size_t i = 0; i < explicit_arguments.size(); ++i)
	{
		const string& pname = declaration->parameters[i].name;
		if (pname.empty())
			return false;
		if (declaration->parameters[i].kind ==
		    TemplateParameterKind::Type)
		{
			if (explicit_arguments[i].kind != TemplateArgumentKind::Type)
				return false;
			deduced[pname] = explicit_arguments[i].type;
			fixed[pname] = explicit_arguments[i].type;
		}
		else if (declaration->parameters[i].kind ==
		         TemplateParameterKind::NonType)
		{
			if (explicit_arguments[i].kind != TemplateArgumentKind::Value)
				return false;
			deduced_arguments[pname] = explicit_arguments[i];
		}
		else if (declaration->parameters[i].kind ==
		         TemplateParameterKind::TemplateTemplate)
		{
			if (explicit_arguments[i].kind != TemplateArgumentKind::Template)
				return false;
			deduced_arguments[pname] = explicit_arguments[i];
		}
	}
	TypePtr pattern_fn = declaration->generic_function_type;
	if (!declaration->outer_type_substitutions.empty() ||
	    !declaration->outer_value_substitutions.empty())
	{
		vector<map<string, TypePtr> > save_subst =
			template_type_substitutions_;
		vector<map<string, TemplateArgument> > save_value_subst =
			template_value_substitutions_;
		try
		{
			template_type_substitutions_.insert(
				template_type_substitutions_.end(),
				declaration->outer_type_substitutions.begin(),
				declaration->outer_type_substitutions.end());
			template_value_substitutions_.insert(
				template_value_substitutions_.end(),
				declaration->outer_value_substitutions.begin(),
				declaration->outer_value_substitutions.end());
			pattern_fn =
				substitute_function_template_type(declaration,
				                                  pattern_fn);
		}
		catch (const runtime_error&)
		{
			template_type_substitutions_ = save_subst;
			template_value_substitutions_ = save_value_subst;
			return false;
		}
		template_type_substitutions_ = save_subst;
		template_value_substitutions_ = save_value_subst;
	}
	TypePtr target_fn = pa11::strip_cv(target);
	TypePtr pattern_result = pattern_fn->base;
	for (map<string, TypePtr>::const_iterator fit = fixed.begin();
	     fit != fixed.end(); ++fit)
		pattern_result = substitute_template_type_parameter(
			pattern_result,
			fit->first,
			fit->second);
	if (!deduce_template_type(pattern_result,
	                          target_fn->base,
	                          deduced,
	                          &fixed,
	                          &deduced_arguments))
		return false;
	size_t target_index = 0;
	for (size_t i = 0; i < pattern_fn->parameters.size(); ++i)
	{
		TypePtr pattern = pattern_fn->parameters[i];
		for (map<string, TypePtr>::const_iterator fit = fixed.begin();
		     fit != fixed.end(); ++fit)
			pattern = substitute_template_type_parameter(pattern,
			                                             fit->first,
			                                             fit->second);
		string pack_name;
		bool parameter_pack =
			function_parameter_pack_name(declaration, pattern, pack_name);
		size_t remaining_function_parameters =
			pattern_fn->parameters.size() - i - 1;
		if (parameter_pack)
		{
			if (target_index + remaining_function_parameters >
			    target_fn->parameters.size())
				return false;
			size_t take = target_fn->parameters.size() -
			              target_index -
			              remaining_function_parameters;
			vector<TemplateArgument> pack;
			for (size_t j = 0; j < take; ++j)
			{
				map<string, TypePtr> one;
				if (!deduce_template_type(pattern,
				                          target_fn->parameters[target_index + j],
				                          one,
				                          &fixed,
				                          &deduced_arguments))
					return false;
				map<string, TypePtr>::iterator found =
					one.find(pack_name);
				if (found == one.end())
					return false;
				pack.push_back(TemplateArgument::type_arg(found->second));
			}
			deduced_packs[pack_name] = pack;
			target_index += take;
			continue;
		}
		if (target_index >= target_fn->parameters.size())
			return false;
		if (!deduce_template_type(pattern,
		                          target_fn->parameters[target_index],
		                          deduced,
		                          &fixed,
		                          &deduced_arguments))
			return false;
		++target_index;
	}
	if (target_index != target_fn->parameters.size())
		return false;
	vector<TemplateArgument> full_args;
	for (size_t i = 0; i < declaration->parameters.size(); ++i)
	{
		const string& pname = declaration->parameters[i].name;
		if (declaration->parameters[i].kind == TemplateParameterKind::Type &&
		    declaration->parameters[i].is_pack)
		{
			map<string, vector<TemplateArgument> >::iterator found =
				deduced_packs.find(pname);
			map<string, TypePtr>::iterator scalar = deduced.find(pname);
			if (found == deduced_packs.end() &&
			    scalar != deduced.end())
			{
				vector<TemplateArgument> pack;
				pack.push_back(TemplateArgument::type_arg(
					scalar->second));
				full_args.push_back(TemplateArgument::pack_arg(pack));
				continue;
			}
			full_args.push_back(
				TemplateArgument::pack_arg(
					found == deduced_packs.end()
					? vector<TemplateArgument>()
					: found->second));
			continue;
		}
		if (declaration->parameters[i].kind == TemplateParameterKind::Type)
		{
			map<string, TypePtr>::iterator found = deduced.find(pname);
			if (found == deduced.end())
				break;
			full_args.push_back(TemplateArgument::type_arg(found->second));
			continue;
		}
		map<string, TemplateArgument>::iterator found =
			deduced_arguments.find(pname);
		if (found == deduced_arguments.end())
			break;
		full_args.push_back(found->second);
	}
	try
	{
		out = complete_template_arguments(declaration, full_args);
	}
	catch (const runtime_error&)
	{
		return false;
	}
	if (out.size() != declaration->parameters.size())
		return false;
	return true;
}

}  // namespace internal
}  // namespace pa12
