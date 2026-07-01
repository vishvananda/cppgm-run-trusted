#include "pa12_internal.h"

using namespace std;

namespace pa12 {
namespace internal {
size_t dependent_cache_hash_combine(size_t seed, size_t value);
size_t dependent_cache_template_argument_identity(
	const TemplateArgument& argument,
	int depth);
size_t dependent_cache_string_hash(const string& value);
namespace {

bool template_type_has_template_parameter_impl(
	TypePtr type,
	const map<const void*, vector<TemplateArgument> >& record_template_arguments,
	map<const void*, int>& type_memo);

bool template_instance_argument_has_template_parameter_impl(
	const pa11::TemplateInstanceArgument& argument,
	const map<const void*, vector<TemplateArgument> >& record_template_arguments,
	map<const void*, int>& type_memo);

bool template_argument_has_template_parameter_impl(
	const TemplateArgument& arg,
	const map<const void*, vector<TemplateArgument> >& record_template_arguments,
	map<const void*, int>& type_memo);

size_t cheap_template_instance_dependency_key(
	const pa11::TemplateInstanceArgument& argument,
	int depth);

size_t cheap_template_argument_dependency_key(
	const TemplateArgument& argument,
	int depth);

}  // namespace

bool template_instance_argument_has_template_parameter_name(
	const pa11::TemplateInstanceArgument& argument,
	string& name);
bool template_instance_argument_has_template_parameter(
	const pa11::TemplateInstanceArgument& argument,
	const map<const void*, vector<TemplateArgument> >& record_template_arguments);

bool template_argument_has_template_parameter(
	const TemplateArgument& arg,
	const map<const void*, vector<TemplateArgument> >& record_template_arguments)
{
	map<const void*, int> type_memo;
	return template_argument_has_template_parameter_impl(
		arg,
		record_template_arguments,
		type_memo);
}

namespace {

size_t cheap_type_dependency_key(TypePtr type)
{
	TypePtr bare = type.get() != NULL ? pa11::strip_cv(type) : TypePtr();
	return reinterpret_cast<uintptr_t>(bare.get());
}

size_t cheap_template_instance_dependency_key(
	const pa11::TemplateInstanceArgument& argument,
	int depth)
{
	size_t key = dependent_cache_hash_combine(
		0x9a71,
		static_cast<size_t>(argument.kind));
	if (argument.kind == pa11::TemplateInstanceArgumentKind::Type ||
	    argument.kind == pa11::TemplateInstanceArgumentKind::Value)
		key = dependent_cache_hash_combine(
			key,
			cheap_type_dependency_key(argument.type));
	if (argument.kind == pa11::TemplateInstanceArgumentKind::Value)
	{
		key = dependent_cache_hash_combine(key, argument.dependent);
		key = dependent_cache_hash_combine(key, argument.value);
		key = dependent_cache_hash_combine(key,
			dependent_cache_string_hash(argument.value_name));
		key = dependent_cache_hash_combine(key,
			dependent_cache_string_hash(argument.value_owner_template_name));
		key = dependent_cache_hash_combine(key,
			dependent_cache_string_hash(argument.value_member_name));
	}
	if (argument.kind == pa11::TemplateInstanceArgumentKind::Template)
	{
		key = dependent_cache_hash_combine(key, argument.dependent);
		key = dependent_cache_hash_combine(
			key,
			dependent_cache_string_hash(argument.template_name));
	}
	if (argument.kind == pa11::TemplateInstanceArgumentKind::Pack &&
	    depth < 2)
	{
		key = dependent_cache_hash_combine(key, argument.pack.size());
		for (size_t i = 0; i < argument.pack.size(); ++i)
			key = dependent_cache_hash_combine(
				key,
				cheap_template_instance_dependency_key(
					argument.pack[i],
					depth + 1));
	}
	return key;
}

size_t cheap_template_argument_dependency_key(
	const TemplateArgument& argument,
	int depth)
{
	size_t key = dependent_cache_hash_combine(
		0x4d33,
		static_cast<size_t>(argument.kind));
	if (argument.kind == TemplateArgumentKind::Type ||
	    argument.kind == TemplateArgumentKind::Value)
		key = dependent_cache_hash_combine(
			key,
			cheap_type_dependency_key(argument.type));
	if (argument.kind == TemplateArgumentKind::Value)
	{
		key = dependent_cache_hash_combine(key, argument.dependent);
		key = dependent_cache_hash_combine(key, argument.value);
		key = dependent_cache_hash_combine(key,
			dependent_cache_string_hash(argument.value_name));
		key = dependent_cache_hash_combine(key,
			dependent_cache_string_hash(argument.value_owner_template_name));
		key = dependent_cache_hash_combine(key,
			dependent_cache_string_hash(argument.value_member_name));
		if (depth < 2)
		{
			key = dependent_cache_hash_combine(
				key,
				argument.value_owner_template_arguments.size());
			for (size_t i = 0;
			     i < argument.value_owner_template_arguments.size();
			     ++i)
				key = dependent_cache_hash_combine(
					key,
					cheap_template_instance_dependency_key(
						argument.value_owner_template_arguments[i],
						depth + 1));
		}
	}
	if (argument.kind == TemplateArgumentKind::Template)
	{
		key = dependent_cache_hash_combine(
			key,
			reinterpret_cast<uintptr_t>(argument.template_declaration));
		key = dependent_cache_hash_combine(key,
			dependent_cache_string_hash(argument.value_name));
	}
	if (argument.kind == TemplateArgumentKind::Pack && depth < 2)
	{
		key = dependent_cache_hash_combine(key, argument.pack.size());
		for (size_t i = 0; i < argument.pack.size(); ++i)
			key = dependent_cache_hash_combine(
				key,
				cheap_template_argument_dependency_key(
					argument.pack[i],
					depth + 1));
	}
	return key;
}

}  // namespace

bool Parser::template_argument_dependent_cached(
	const TemplateArgument& argument) const
{
	size_t key = dependent_cache_hash_combine(
		0xa9d3f17u,
		cheap_template_argument_dependency_key(argument, 0));
	key = dependent_cache_hash_combine(key,
	                                   record_template_arguments_.size());
	key = dependent_cache_hash_combine(key,
	                                   active_class_instantiations_.size());
	key = dependent_cache_hash_combine(key,
	                                   validating_template_definition_);
	map<size_t, bool>::const_iterator cached =
		template_dependent_type_cache_.find(key);
	if (cached != template_dependent_type_cache_.end())
		return cached->second;
	bool dependent =
		template_argument_has_template_parameter(argument,
		                                         record_template_arguments_);
	template_dependent_type_cache_[key] = dependent;
	return dependent;
}

namespace {

bool template_argument_has_template_parameter_impl(
	const TemplateArgument& arg,
	const map<const void*, vector<TemplateArgument> >& record_template_arguments,
	map<const void*, int>& type_memo)
{
	if (arg.kind == TemplateArgumentKind::Type)
		return template_type_has_template_parameter_impl(
			arg.type,
			record_template_arguments,
			type_memo);
	if (arg.kind == TemplateArgumentKind::Value)
	{
		if (arg.dependent &&
		    !arg.value_owner_template_arguments.empty())
		{
			for (size_t i = 0;
			     i < arg.value_owner_template_arguments.size();
			     ++i)
				if (template_instance_argument_has_template_parameter_impl(
					    arg.value_owner_template_arguments[i],
					    record_template_arguments,
					    type_memo))
					return true;
			return false;
		}
		return arg.dependent ||
		       template_type_has_template_parameter_impl(
			       arg.type,
			       record_template_arguments,
			       type_memo);
	}
	if (arg.kind == TemplateArgumentKind::Template)
		return arg.template_declaration == NULL;
	for (size_t i = 0; i < arg.pack.size(); ++i)
		if (template_argument_has_template_parameter_impl(
			    arg.pack[i],
			    record_template_arguments,
			    type_memo))
			return true;
	return false;
}

}  // namespace

bool template_type_has_template_parameter_name(TypePtr type, string& name)
{
	if (type.get() == NULL)
		return false;
	type = pa11::strip_cv(type);
	if (type->kind == pa11::TypeKind::TemplateParameter)
	{
		if (type->is_dependent_typename)
		{
			for (size_t i = 0; i < type->template_arguments.size(); ++i)
				if (template_instance_argument_has_template_parameter_name(
					    type->template_arguments[i],
					    name))
					return true;
			for (size_t i = 0;
			     i < type->dependent_typename_template_argument_lists.size();
			     ++i)
				for (size_t j = 0;
				     j < type->dependent_typename_template_argument_lists[i].size();
				     ++j)
					if (template_instance_argument_has_template_parameter_name(
						    type->dependent_typename_template_argument_lists[i][j],
						    name))
						return true;
		}
		if (!pa11::is_deducible_template_parameter_type(type))
			return false;
		name = type->name;
		return true;
	}
	if (type->kind == pa11::TypeKind::Pointer ||
	    type->kind == pa11::TypeKind::LValueReference ||
	    type->kind == pa11::TypeKind::RValueReference)
		return template_type_has_template_parameter_name(type->base, name);
	if (type->kind == pa11::TypeKind::Array)
	{
		if (type->unknown_bound && !type->name.empty())
		{
			name = type->name;
			return true;
		}
		return template_type_has_template_parameter_name(type->base, name);
	}
	if (type->kind == pa11::TypeKind::Function)
	{
		if (template_type_has_template_parameter_name(type->base, name))
			return true;
		for (size_t i = 0; i < type->parameters.size(); ++i)
			if (template_type_has_template_parameter_name(
				    type->parameters[i],
				    name))
				return true;
	}
	if (type->kind == pa11::TypeKind::MemberPointer)
		return template_type_has_template_parameter_name(type->member_class,
		                                                name) ||
		       template_type_has_template_parameter_name(type->base, name);
	if (type->is_dependent_typename &&
	    type->dependent_typename_template_id &&
	    !type->template_primary_name.empty())
	{
		name = type->template_primary_name;
		return true;
	}
	if (type->is_template_specialization)
		for (size_t i = 0; i < type->template_arguments.size(); ++i)
			if (template_instance_argument_has_template_parameter_name(
				    type->template_arguments[i],
				    name))
				return true;
	return false;
}

bool template_instance_argument_has_template_parameter_name(
	const pa11::TemplateInstanceArgument& argument,
	string& name)
{
	if (argument.kind == pa11::TemplateInstanceArgumentKind::Type)
		return template_type_has_template_parameter_name(argument.type, name);
	if (argument.kind == pa11::TemplateInstanceArgumentKind::Value)
	{
		for (size_t i = 0;
		     i < argument.value_owner_template_arguments.size();
		     ++i)
			if (template_instance_argument_has_template_parameter_name(
				    argument.value_owner_template_arguments[i],
				    name))
				return true;
		if (!argument.value_owner_template_name.empty())
		{
			name = argument.value_owner_template_name;
			return true;
		}
		if (argument.dependent)
		{
			if (!argument.value_name.empty())
			{
				name = argument.value_name;
				return true;
			}
		}
		return template_type_has_template_parameter_name(argument.type, name);
	}
	if (argument.kind == pa11::TemplateInstanceArgumentKind::Pack)
	{
		if (!argument.value_name.empty())
		{
			name = argument.value_name;
			return true;
		}
		if (!argument.template_name.empty())
		{
			name = argument.template_name;
			return true;
		}
		for (size_t i = 0; i < argument.pack.size(); ++i)
			if (template_instance_argument_has_template_parameter_name(
				    argument.pack[i],
				    name))
				return true;
	}
	return false;
}

bool template_instance_argument_has_template_parameter(
	const pa11::TemplateInstanceArgument& argument,
	const map<const void*, vector<TemplateArgument> >& record_template_arguments)
{
	map<const void*, int> type_memo;
	return template_instance_argument_has_template_parameter_impl(
		argument,
		record_template_arguments,
		type_memo);
}

namespace {

bool template_instance_argument_has_template_parameter_impl(
	const pa11::TemplateInstanceArgument& argument,
	const map<const void*, vector<TemplateArgument> >& record_template_arguments,
	map<const void*, int>& type_memo)
{
	if (argument.kind == pa11::TemplateInstanceArgumentKind::Type)
		return template_type_has_template_parameter_impl(
			argument.type,
			record_template_arguments,
			type_memo);
	if (argument.kind == pa11::TemplateInstanceArgumentKind::Value)
	{
		if (argument.dependent &&
		    !argument.value_owner_template_arguments.empty())
		{
			for (size_t i = 0;
			     i < argument.value_owner_template_arguments.size();
			     ++i)
				if (template_instance_argument_has_template_parameter_impl(
					    argument.value_owner_template_arguments[i],
					    record_template_arguments,
					    type_memo))
					return true;
			return false;
		}
		return argument.dependent ||
		       template_type_has_template_parameter_impl(
			       argument.type,
			       record_template_arguments,
			       type_memo);
	}
	if (argument.kind == pa11::TemplateInstanceArgumentKind::Template)
		return argument.dependent;
	if (argument.kind == pa11::TemplateInstanceArgumentKind::Pack)
		for (size_t i = 0; i < argument.pack.size(); ++i)
			if (template_instance_argument_has_template_parameter_impl(
				    argument.pack[i],
				    record_template_arguments,
				    type_memo))
				return true;
	return false;
}

}  // namespace

bool template_type_has_template_parameter(
	TypePtr type,
	const map<const void*, vector<TemplateArgument> >& record_template_arguments)
{
	map<const void*, int> type_memo;
	return template_type_has_template_parameter_impl(
		type,
		record_template_arguments,
		type_memo);
}

namespace {

bool template_type_has_template_parameter_impl(
	TypePtr type,
	const map<const void*, vector<TemplateArgument> >& record_template_arguments,
	map<const void*, int>& type_memo)
{
	if (type.get() == NULL)
		return false;
	type = pa11::strip_cv(type);
	const void* type_key = type.get();
	map<const void*, int>::const_iterator memo = type_memo.find(type_key);
	if (memo != type_memo.end())
		return memo->second > 0;
	type_memo[type_key] = -1;
	bool result = false;
	if (type->is_dependent_typename &&
	    (!type->template_arguments.empty() ||
	     !type->dependent_typename_template_argument_lists.empty()))
	{
		if (type->kind == pa11::TypeKind::Record &&
		    type->is_template_specialization &&
		    type->scope == NULL &&
		    !type->template_primary_name.empty())
			result = true;
		for (size_t i = 0; i < type->template_arguments.size(); ++i)
			if (!result &&
			    template_instance_argument_has_template_parameter_impl(
				    type->template_arguments[i],
				    record_template_arguments,
				    type_memo))
				result = true;
		for (size_t i = 0;
		     !result &&
		     i < type->dependent_typename_template_argument_lists.size();
		     ++i)
			for (size_t j = 0;
			     !result &&
			     j < type->dependent_typename_template_argument_lists[i].size();
			     ++j)
				if (template_instance_argument_has_template_parameter_impl(
					    type->dependent_typename_template_argument_lists[i][j],
					    record_template_arguments,
					    type_memo))
					result = true;
			type_memo[type_key] = 1;
			return true;
		}
	if (type->is_dependent_typename)
		result = true;
	if (type->kind == pa11::TypeKind::TemplateParameter)
		result = true;
	if (!result &&
	    (type->kind == pa11::TypeKind::Pointer ||
	     type->kind == pa11::TypeKind::LValueReference ||
	     type->kind == pa11::TypeKind::RValueReference))
		result = template_type_has_template_parameter_impl(
			type->base,
			record_template_arguments,
			type_memo);
	if (!result && type->kind == pa11::TypeKind::Array)
	{
		if (type->unknown_bound && !type->name.empty())
			result = true;
		else
			result = template_type_has_template_parameter_impl(
				type->base,
				record_template_arguments,
				type_memo);
	}
	if (!result && type->kind == pa11::TypeKind::Function)
	{
		if (template_type_has_template_parameter_impl(
			    type->base,
			    record_template_arguments,
			    type_memo))
			result = true;
		for (size_t i = 0; i < type->parameters.size(); ++i)
			if (!result &&
			    template_type_has_template_parameter_impl(
				    type->parameters[i],
				    record_template_arguments,
				    type_memo))
				result = true;
	}
	if (!result && type->kind == pa11::TypeKind::MemberPointer)
		result = template_type_has_template_parameter_impl(
			       type->member_class,
			       record_template_arguments,
			       type_memo) ||
		       template_type_has_template_parameter_impl(
			       type->base,
			       record_template_arguments,
			       type_memo);
	if (!result && type->kind == pa11::TypeKind::Record)
	{
		if (type->is_template_specialization &&
		    type->scope == NULL &&
		    !type->template_primary_name.empty())
			result = true;
		if (type->is_template_specialization ||
		    type->is_dependent_typename)
		{
			map<const void*, vector<TemplateArgument> >::const_iterator found =
				record_template_arguments.find(type.get());
			if (found != record_template_arguments.end())
				for (size_t i = 0; i < found->second.size(); ++i)
					if (!result &&
					    template_argument_has_template_parameter_impl(
						    found->second[i],
						    record_template_arguments,
						    type_memo))
						result = true;
		}
		if (type->is_template_specialization)
			for (size_t i = 0; i < type->template_arguments.size(); ++i)
				if (!result &&
				    template_instance_argument_has_template_parameter_impl(
					    type->template_arguments[i],
					    record_template_arguments,
					    type_memo))
					result = true;
	}
	type_memo[type_key] = result ? 1 : 0;
	return result;
}

}  // namespace

bool Parser::template_arguments_dependent(
	const vector<TemplateArgument>& arguments) const
{
	const bool allow_complete_record =
		active_class_instantiations_.empty() &&
		!validating_template_definition_;
	for (size_t i = 0; i < arguments.size(); ++i)
	{
		bool dependent =
			template_argument_dependent_cached(arguments[i]);
		if (dependent &&
		    arguments[i].kind == TemplateArgumentKind::Pack)
		{
			dependent = false;
			for (size_t p = 0; p < arguments[i].pack.size(); ++p)
			{
				bool element_dependent =
					template_argument_dependent_cached(
						arguments[i].pack[p]);
				if (element_dependent &&
				    allow_complete_record &&
				    arguments[i].pack[p].kind ==
					    TemplateArgumentKind::Type)
				{
					TypePtr bare =
						arguments[i].pack[p].type.get() != NULL
						? pa11::strip_cv(arguments[i].pack[p].type)
						: TypePtr();
					if (bare.get() != NULL &&
					    bare->kind == pa11::TypeKind::Record &&
					    bare->scope != NULL &&
					    !bare->is_dependent_typename)
						element_dependent = false;
				}
				if (element_dependent)
				{
					dependent = true;
					break;
				}
			}
		}
		if (dependent &&
		    arguments[i].kind == TemplateArgumentKind::Type)
		{
			TypePtr bare = arguments[i].type.get() != NULL
				? pa11::strip_cv(arguments[i].type) : TypePtr();
			if (bare.get() != NULL &&
			    bare->kind == pa11::TypeKind::Record &&
			    bare->scope != NULL &&
			    !bare->is_dependent_typename &&
			    allow_complete_record)
				dependent = false;
		}
		if (dependent)
			return true;
	}
	return false;
}

bool Parser::active_class_instantiation_dependent() const
{
	if (active_class_instantiations_.empty())
		return false;
	TypePtr active = pa11::strip_cv(active_class_instantiations_.back().type);
	map<const void*, vector<TemplateArgument> >::const_iterator found =
		record_template_arguments_.find(active.get());
	if (found == record_template_arguments_.end())
		return type_is_template_dependent(active);
	return template_arguments_dependent(found->second);
}

}  // namespace internal
}  // namespace pa12
