#include "pa12_templates_instance_support.h"
#include <algorithm>
#include <cstdint>
#include <functional>
#include <set>
#include <sstream>
#include <stdexcept>
#include <utility>
#include "posttoken_pipeline.h"
#include "pp_token.h"
using namespace std;
namespace pa12 {
namespace internal {
bool same_template_record_type(TypePtr left, TypePtr right)
{
	TypePtr l = left.get() != NULL ? pa11::strip_cv(left) : TypePtr();
	TypePtr r = right.get() != NULL ? pa11::strip_cv(right) : TypePtr();
	if (l.get() == NULL || r.get() == NULL)
		return false;
	if (pa11::same_type(l, r))
		return true;
	return l->kind == pa11::TypeKind::Record &&
	       r->kind == pa11::TypeKind::Record &&
	       l->is_template_specialization &&
	       r->is_template_specialization &&
	       l->template_primary_name == r->template_primary_name &&
	       l->name == r->name;
}
bool template_record_owner_name_match(TypePtr left, TypePtr right)
{
	TypePtr l = left.get() != NULL ? pa11::strip_cv(left) : TypePtr();
	TypePtr r = right.get() != NULL ? pa11::strip_cv(right) : TypePtr();
	if (l.get() == NULL ||
	    r.get() == NULL ||
	    l->kind != pa11::TypeKind::Record ||
	    r->kind != pa11::TypeKind::Record ||
	    l->name != r->name)
		return false;
	string l_primary = !l->template_primary_name.empty()
		? l->template_primary_name : l->name;
	string r_primary = !r->template_primary_name.empty()
		? r->template_primary_name : r->name;
	return l_primary == r_primary &&
	       (l->is_template_specialization || r->is_template_specialization);
}
bool template_instance_argument_contains_parameter_name(
	const pa11::TemplateInstanceArgument& argument,
	const string& name,
	const map<const void*, vector<TemplateArgument> >& record_arguments,
	map<const void*, int>& type_memo,
	map<const void*, int>& instance_memo,
	map<const void*, int>& argument_memo);
bool template_argument_contains_parameter_name(
	const TemplateArgument& argument,
	const string& name,
	const map<const void*, vector<TemplateArgument> >& record_arguments,
	map<const void*, int>& type_memo,
	map<const void*, int>& instance_memo,
	map<const void*, int>& argument_memo);
void collect_type_parameter_names_impl(
	TypePtr type,
	const map<const void*, vector<TemplateArgument> >& record_arguments,
	set<string>& names,
	map<const void*, int>& type_memo,
	map<const void*, int>& instance_memo,
	map<const void*, int>& argument_memo);
void collect_instance_argument_parameter_names(
	const pa11::TemplateInstanceArgument& argument,
	const map<const void*, vector<TemplateArgument> >& record_arguments,
	set<string>& names,
	map<const void*, int>& type_memo,
	map<const void*, int>& instance_memo,
	map<const void*, int>& argument_memo);
void collect_template_argument_parameter_names(
	const TemplateArgument& argument,
	const map<const void*, vector<TemplateArgument> >& record_arguments,
	set<string>& names,
	map<const void*, int>& type_memo,
	map<const void*, int>& instance_memo,
	map<const void*, int>& argument_memo);
bool dependent_template_parameter_contains_parameter_name(
	TypePtr type,
	const string& name,
	const map<const void*, vector<TemplateArgument> >& record_arguments,
	map<const void*, int>& type_memo,
	map<const void*, int>& instance_memo,
	map<const void*, int>& argument_memo)
{
	bool result = false;
	for (size_t i = 0; i < type->template_arguments.size(); ++i)
		if (template_instance_argument_contains_parameter_name(
			    type->template_arguments[i],
			    name,
			    record_arguments,
			    type_memo,
			    instance_memo,
			    argument_memo))
			result = true;
	for (size_t i = 0;
	     !result && i < type->dependent_typename_template_argument_lists.size();
	     ++i)
		for (size_t j = 0;
		     !result && j < type->dependent_typename_template_argument_lists[i].size();
		     ++j)
			if (template_instance_argument_contains_parameter_name(
				    type->dependent_typename_template_argument_lists[i][j],
				    name,
				    record_arguments,
				    type_memo,
				    instance_memo,
				    argument_memo))
				result = true;
	return result;
}
bool type_contains_parameter_name_impl(
	TypePtr type,
	const string& name,
	const map<const void*, vector<TemplateArgument> >& record_arguments,
	map<const void*, int>& type_memo,
	map<const void*, int>& instance_memo,
	map<const void*, int>& argument_memo)
{
	if (type.get() == NULL)
		return false;
	type = pa11::strip_cv(type);
	map<const void*, int>::const_iterator cached = type_memo.find(type.get());
	if (cached != type_memo.end())
		return cached->second > 0;
	type_memo[type.get()] = -1;
	bool result = false;
	if (type->kind == pa11::TypeKind::TemplateParameter)
	{
		if (type->is_dependent_typename)
			result = dependent_template_parameter_contains_parameter_name(
				type,
				name,
				record_arguments,
				type_memo,
				instance_memo,
				argument_memo);
		if (!result)
			result = pa11::is_deducible_template_parameter_type(type) &&
			         type->name == name;
		type_memo[type.get()] = result ? 1 : 0;
		return result;
	}
	if (type->kind == pa11::TypeKind::Pointer ||
	    type->kind == pa11::TypeKind::LValueReference ||
	    type->kind == pa11::TypeKind::RValueReference)
		result = type_contains_parameter_name_impl(type->base,
		                                           name,
		                                           record_arguments,
		                                           type_memo,
		                                           instance_memo,
		                                           argument_memo);
	if (type->kind == pa11::TypeKind::Array)
	{
		if (type->unknown_bound && type->name == name)
			result = true;
		else
			result = type_contains_parameter_name_impl(type->base,
			                                           name,
			                                           record_arguments,
			                                           type_memo,
			                                           instance_memo,
			                                           argument_memo);
		type_memo[type.get()] = result ? 1 : 0;
		return result;
	}
	if (type->kind == pa11::TypeKind::Function)
	{
		if (type_contains_parameter_name_impl(type->base,
		                                      name,
		                                      record_arguments,
		                                      type_memo,
		                                      instance_memo,
		                                      argument_memo))
			result = true;
		for (size_t i = 0; i < type->parameters.size(); ++i)
			if (!result &&
				    type_contains_parameter_name_impl(type->parameters[i],
				                                      name,
				                                      record_arguments,
				                                      type_memo,
				                                      instance_memo,
				                                      argument_memo))
					result = true;
		type_memo[type.get()] = result ? 1 : 0;
		return result;
	}
	if (type->kind == pa11::TypeKind::MemberPointer)
	{
		result = type_contains_parameter_name_impl(type->member_class,
		                                           name,
		                                           record_arguments,
		                                           type_memo,
		                                           instance_memo,
		                                           argument_memo) ||
		         type_contains_parameter_name_impl(type->base,
		                                           name,
		                                           record_arguments,
		                                           type_memo,
		                                           instance_memo,
		                                           argument_memo);
		type_memo[type.get()] = result ? 1 : 0;
		return result;
	}
	if (type->is_template_specialization)
	{
		if (type->is_dependent_typename &&
		    type->dependent_typename_template_id &&
		    type->template_primary_name == name)
			result = true;
		for (size_t i = 0; i < type->template_arguments.size(); ++i)
			if (!result &&
				    template_instance_argument_contains_parameter_name(
					    type->template_arguments[i],
					    name,
					    record_arguments,
					    type_memo,
					    instance_memo,
					    argument_memo))
					result = true;
		map<const void*, vector<TemplateArgument> >::const_iterator found =
			record_arguments.find(type.get());
		if (found != record_arguments.end())
			for (size_t i = 0; i < found->second.size(); ++i)
				if (!result &&
					    template_argument_contains_parameter_name(
						    found->second[i],
						    name,
						    record_arguments,
						    type_memo,
						    instance_memo,
						    argument_memo))
						result = true;
	}
	type_memo[type.get()] = result ? 1 : 0;
	return result;
}
bool type_contains_parameter_name(
	TypePtr type,
	const string& name,
	const map<const void*, vector<TemplateArgument> >& record_arguments)
{
	map<const void*, int> type_memo;
	map<const void*, int> instance_memo;
	map<const void*, int> argument_memo;
	return type_contains_parameter_name_impl(type,
	                                         name,
	                                         record_arguments,
	                                         type_memo,
	                                         instance_memo,
	                                         argument_memo);
}
bool template_instance_argument_contains_parameter_name(
	const pa11::TemplateInstanceArgument& argument,
	const string& name,
	const map<const void*, vector<TemplateArgument> >& record_arguments,
	map<const void*, int>& type_memo,
	map<const void*, int>& instance_memo,
	map<const void*, int>& argument_memo)
{
	const void* memo_key = &argument;
	map<const void*, int>::const_iterator cached =
		instance_memo.find(memo_key);
	if (cached != instance_memo.end())
		return cached->second > 0;
	instance_memo[memo_key] = -1;
	bool result = false;
	if (argument.kind == pa11::TemplateInstanceArgumentKind::Type)
		result = type_contains_parameter_name_impl(argument.type,
		                                          name,
		                                          record_arguments,
		                                          type_memo,
		                                          instance_memo,
		                                          argument_memo);
	if (argument.kind == pa11::TemplateInstanceArgumentKind::Value)
	{
		for (size_t i = 0;
		     i < argument.value_owner_template_arguments.size();
		     ++i)
			if (template_instance_argument_contains_parameter_name(
				    argument.value_owner_template_arguments[i],
				    name,
				    record_arguments,
				    type_memo,
				    instance_memo,
				    argument_memo))
				result = true;
		if (!result)
			result = argument.value_owner_template_name == name ||
			         (argument.dependent && argument.value_name == name) ||
			         type_contains_parameter_name_impl(argument.type,
			                                           name,
			                                           record_arguments,
			                                           type_memo,
			                                           instance_memo,
			                                           argument_memo);
	}
	if (argument.kind == pa11::TemplateInstanceArgumentKind::Pack)
		for (size_t i = 0; i < argument.pack.size(); ++i)
			if (template_instance_argument_contains_parameter_name(
				    argument.pack[i],
				    name,
				    record_arguments,
				    type_memo,
				    instance_memo,
				    argument_memo))
				result = true;
	instance_memo[memo_key] = result ? 1 : 0;
	return result;
}
bool template_argument_contains_parameter_name(
	const TemplateArgument& argument,
	const string& name,
	const map<const void*, vector<TemplateArgument> >& record_arguments,
	map<const void*, int>& type_memo,
	map<const void*, int>& instance_memo,
	map<const void*, int>& argument_memo)
{
	const void* memo_key = &argument;
	map<const void*, int>::const_iterator cached =
		argument_memo.find(memo_key);
	if (cached != argument_memo.end())
		return cached->second > 0;
	argument_memo[memo_key] = -1;
	bool result = false;
	if (argument.kind == TemplateArgumentKind::Type)
		result = type_contains_parameter_name_impl(argument.type,
		                                          name,
		                                          record_arguments,
		                                          type_memo,
		                                          instance_memo,
		                                          argument_memo);
	if (argument.kind == TemplateArgumentKind::Value)
	{
		for (size_t i = 0;
		     i < argument.value_owner_template_arguments.size();
		     ++i)
			if (template_instance_argument_contains_parameter_name(
				    argument.value_owner_template_arguments[i],
				    name,
				    record_arguments,
				    type_memo,
				    instance_memo,
				    argument_memo))
				result = true;
		if (!result)
			result = argument.value_owner_template_name == name ||
			         (argument.dependent && argument.value_name == name) ||
			         type_contains_parameter_name_impl(argument.type,
			                                           name,
			                                           record_arguments,
			                                           type_memo,
			                                           instance_memo,
			                                           argument_memo);
	}
	if (argument.kind == TemplateArgumentKind::Pack)
		for (size_t i = 0; i < argument.pack.size(); ++i)
			if (template_argument_contains_parameter_name(
				    argument.pack[i],
				    name,
				    record_arguments,
				    type_memo,
				    instance_memo,
				    argument_memo))
				result = true;
	if (argument.kind == TemplateArgumentKind::Template)
		result = argument.template_declaration == NULL &&
		         argument.value_name == name;
	argument_memo[memo_key] = result ? 1 : 0;
	return result;
}
void collect_type_parameter_names(
	TypePtr type,
	const map<const void*, vector<TemplateArgument> >& record_arguments,
	set<string>& names)
{
	map<const void*, int> type_memo;
	map<const void*, int> instance_memo;
	map<const void*, int> argument_memo;
	collect_type_parameter_names_impl(type,
	                                  record_arguments,
	                                  names,
	                                  type_memo,
	                                  instance_memo,
	                                  argument_memo);
}
void collect_type_parameter_names_impl(
	TypePtr type,
	const map<const void*, vector<TemplateArgument> >& record_arguments,
	set<string>& names,
	map<const void*, int>& type_memo,
	map<const void*, int>& instance_memo,
	map<const void*, int>& argument_memo)
{
	if (type.get() == NULL)
		return;
	type = pa11::strip_cv(type);
	if (type_memo.find(type.get()) != type_memo.end())
		return;
	type_memo[type.get()] = 1;
	if (type->kind == pa11::TypeKind::TemplateParameter)
	{
		if (type->is_dependent_typename)
		{
			for (size_t i = 0; i < type->template_arguments.size(); ++i)
				collect_instance_argument_parameter_names(
					type->template_arguments[i],
					record_arguments,
					names,
					type_memo,
					instance_memo,
					argument_memo);
			for (size_t i = 0;
			     i < type->dependent_typename_template_argument_lists.size();
			     ++i)
				for (size_t j = 0;
				     j < type->dependent_typename_template_argument_lists[i].size();
				     ++j)
					collect_instance_argument_parameter_names(
						type->dependent_typename_template_argument_lists[i][j],
						record_arguments,
						names,
						type_memo,
						instance_memo,
						argument_memo);
		}
		if (pa11::is_deducible_template_parameter_type(type))
			names.insert(type->name);
		return;
	}
	if (type->kind == pa11::TypeKind::Pointer ||
	    type->kind == pa11::TypeKind::LValueReference ||
	    type->kind == pa11::TypeKind::RValueReference)
	{
		collect_type_parameter_names_impl(type->base,
		                                  record_arguments,
		                                  names,
		                                  type_memo,
		                                  instance_memo,
		                                  argument_memo);
		return;
	}
	if (type->kind == pa11::TypeKind::Array)
	{
		if (type->unknown_bound && !type->name.empty())
			names.insert(type->name);
		else
			collect_type_parameter_names_impl(type->base,
			                                  record_arguments,
			                                  names,
			                                  type_memo,
			                                  instance_memo,
			                                  argument_memo);
		return;
	}
	if (type->kind == pa11::TypeKind::Function)
	{
		collect_type_parameter_names_impl(type->base,
		                                  record_arguments,
		                                  names,
		                                  type_memo,
		                                  instance_memo,
		                                  argument_memo);
		for (size_t i = 0; i < type->parameters.size(); ++i)
			collect_type_parameter_names_impl(type->parameters[i],
			                                  record_arguments,
			                                  names,
			                                  type_memo,
			                                  instance_memo,
			                                  argument_memo);
		return;
	}
	if (type->kind == pa11::TypeKind::MemberPointer)
	{
		collect_type_parameter_names_impl(type->member_class,
		                                  record_arguments,
		                                  names,
		                                  type_memo,
		                                  instance_memo,
		                                  argument_memo);
		collect_type_parameter_names_impl(type->base,
		                                  record_arguments,
		                                  names,
		                                  type_memo,
		                                  instance_memo,
		                                  argument_memo);
		return;
	}
	if (!type->is_template_specialization)
		return;
	if (type->is_dependent_typename &&
	    type->dependent_typename_template_id &&
	    !type->template_primary_name.empty())
		names.insert(type->template_primary_name);
	for (size_t i = 0; i < type->template_arguments.size(); ++i)
		collect_instance_argument_parameter_names(
			type->template_arguments[i],
			record_arguments,
			names,
			type_memo,
			instance_memo,
			argument_memo);
	map<const void*, vector<TemplateArgument> >::const_iterator found =
		record_arguments.find(type.get());
	if (found != record_arguments.end())
		for (size_t i = 0; i < found->second.size(); ++i)
			collect_template_argument_parameter_names(found->second[i],
			                                          record_arguments,
			                                          names,
			                                          type_memo,
			                                          instance_memo,
			                                          argument_memo);
}
void collect_instance_argument_parameter_names(
	const pa11::TemplateInstanceArgument& argument,
	const map<const void*, vector<TemplateArgument> >& record_arguments,
	set<string>& names,
	map<const void*, int>& type_memo,
	map<const void*, int>& instance_memo,
	map<const void*, int>& argument_memo)
{
	const void* memo_key = &argument;
	if (instance_memo.find(memo_key) != instance_memo.end())
		return;
	instance_memo[memo_key] = 1;
	if (argument.kind == pa11::TemplateInstanceArgumentKind::Type)
	{
		collect_type_parameter_names_impl(argument.type,
		                                  record_arguments,
		                                  names,
		                                  type_memo,
		                                  instance_memo,
		                                  argument_memo);
		return;
	}
	if (argument.kind == pa11::TemplateInstanceArgumentKind::Value)
	{
		for (size_t i = 0;
		     i < argument.value_owner_template_arguments.size();
		     ++i)
			collect_instance_argument_parameter_names(
				argument.value_owner_template_arguments[i],
				record_arguments,
				names,
				type_memo,
				instance_memo,
				argument_memo);
		if (!argument.value_owner_template_name.empty())
			names.insert(argument.value_owner_template_name);
		if (argument.dependent && !argument.value_name.empty())
			names.insert(argument.value_name);
		collect_type_parameter_names_impl(argument.type,
		                                  record_arguments,
		                                  names,
		                                  type_memo,
		                                  instance_memo,
		                                  argument_memo);
		return;
	}
	if (argument.kind == pa11::TemplateInstanceArgumentKind::Pack)
		for (size_t i = 0; i < argument.pack.size(); ++i)
			collect_instance_argument_parameter_names(argument.pack[i],
			                                          record_arguments,
			                                          names,
			                                          type_memo,
			                                          instance_memo,
			                                          argument_memo);
}
void collect_template_argument_parameter_names(
	const TemplateArgument& argument,
	const map<const void*, vector<TemplateArgument> >& record_arguments,
	set<string>& names,
	map<const void*, int>& type_memo,
	map<const void*, int>& instance_memo,
	map<const void*, int>& argument_memo)
{
	const void* memo_key = &argument;
	if (argument_memo.find(memo_key) != argument_memo.end())
		return;
	argument_memo[memo_key] = 1;
	if (argument.kind == TemplateArgumentKind::Type)
	{
		collect_type_parameter_names_impl(argument.type,
		                                  record_arguments,
		                                  names,
		                                  type_memo,
		                                  instance_memo,
		                                  argument_memo);
		return;
	}
	if (argument.kind == TemplateArgumentKind::Value)
	{
		for (size_t i = 0;
		     i < argument.value_owner_template_arguments.size();
		     ++i)
			collect_instance_argument_parameter_names(
				argument.value_owner_template_arguments[i],
				record_arguments,
				names,
				type_memo,
				instance_memo,
				argument_memo);
		if (!argument.value_owner_template_name.empty())
			names.insert(argument.value_owner_template_name);
		if (argument.dependent && !argument.value_name.empty())
			names.insert(argument.value_name);
		collect_type_parameter_names_impl(argument.type,
		                                  record_arguments,
		                                  names,
		                                  type_memo,
		                                  instance_memo,
		                                  argument_memo);
		return;
	}
	if (argument.kind == TemplateArgumentKind::Pack)
	{
		for (size_t i = 0; i < argument.pack.size(); ++i)
			collect_template_argument_parameter_names(argument.pack[i],
			                                          record_arguments,
			                                          names,
			                                          type_memo,
			                                          instance_memo,
			                                          argument_memo);
		return;
	}
	if (argument.kind == TemplateArgumentKind::Template &&
	    argument.template_declaration == NULL &&
	    !argument.value_name.empty())
		names.insert(argument.value_name);
}

}  // namespace internal
}  // namespace pa12
