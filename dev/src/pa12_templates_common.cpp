#include "pa12_internal.h"

using namespace std;

namespace pa12 {
namespace internal {

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
	if (arg.kind == TemplateArgumentKind::Type)
		return template_type_has_template_parameter(
			arg.type,
			record_template_arguments);
	if (arg.kind == TemplateArgumentKind::Value)
	{
		if (arg.dependent &&
		    !arg.value_owner_template_arguments.empty())
		{
			for (size_t i = 0;
			     i < arg.value_owner_template_arguments.size();
			     ++i)
				if (template_instance_argument_has_template_parameter(
					    arg.value_owner_template_arguments[i],
					    record_template_arguments))
					return true;
			return false;
		}
		return arg.dependent ||
		       template_type_has_template_parameter(
			       arg.type,
			       record_template_arguments);
	}
	if (arg.kind == TemplateArgumentKind::Template)
		return arg.template_declaration == NULL;
	for (size_t i = 0; i < arg.pack.size(); ++i)
		if (template_argument_has_template_parameter(
			    arg.pack[i],
			    record_template_arguments))
			return true;
	return false;
}

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
	    type->kind == pa11::TypeKind::RValueReference ||
	    type->kind == pa11::TypeKind::Array)
		return template_type_has_template_parameter_name(type->base, name);
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
		for (size_t i = 0; i < argument.pack.size(); ++i)
			if (template_instance_argument_has_template_parameter_name(
				    argument.pack[i],
				    name))
				return true;
	return false;
}

bool template_instance_argument_has_template_parameter(
	const pa11::TemplateInstanceArgument& argument,
	const map<const void*, vector<TemplateArgument> >& record_template_arguments)
{
	if (argument.kind == pa11::TemplateInstanceArgumentKind::Type)
		return template_type_has_template_parameter(argument.type,
		                                           record_template_arguments);
	if (argument.kind == pa11::TemplateInstanceArgumentKind::Value)
	{
		if (argument.dependent &&
		    !argument.value_owner_template_arguments.empty())
		{
			for (size_t i = 0;
			     i < argument.value_owner_template_arguments.size();
			     ++i)
				if (template_instance_argument_has_template_parameter(
					    argument.value_owner_template_arguments[i],
					    record_template_arguments))
					return true;
			return false;
		}
		return argument.dependent ||
		       template_type_has_template_parameter(
			       argument.type,
			       record_template_arguments);
	}
	if (argument.kind == pa11::TemplateInstanceArgumentKind::Template)
		return argument.dependent;
	if (argument.kind == pa11::TemplateInstanceArgumentKind::Pack)
		for (size_t i = 0; i < argument.pack.size(); ++i)
			if (template_instance_argument_has_template_parameter(
				    argument.pack[i],
				    record_template_arguments))
				return true;
	return false;
}

bool template_type_has_template_parameter(
	TypePtr type,
	const map<const void*, vector<TemplateArgument> >& record_template_arguments)
{
	if (type.get() == NULL)
		return false;
	type = pa11::strip_cv(type);
	if (type->is_dependent_typename &&
	    (!type->template_arguments.empty() ||
	     !type->dependent_typename_template_argument_lists.empty()))
	{
		if (type->kind == pa11::TypeKind::Record &&
		    type->is_template_specialization &&
		    type->scope == NULL &&
		    !type->template_primary_name.empty())
			return true;
		for (size_t i = 0; i < type->template_arguments.size(); ++i)
			if (template_instance_argument_has_template_parameter(
				    type->template_arguments[i],
				    record_template_arguments))
				return true;
		for (size_t i = 0;
		     i < type->dependent_typename_template_argument_lists.size();
		     ++i)
			for (size_t j = 0;
			     j < type->dependent_typename_template_argument_lists[i].size();
			     ++j)
				if (template_instance_argument_has_template_parameter(
					    type->dependent_typename_template_argument_lists[i][j],
					    record_template_arguments))
					return true;
		return true;
	}
	if (type->is_dependent_typename)
		return true;
	if (type->kind == pa11::TypeKind::TemplateParameter)
		return true;
	if (type->kind == pa11::TypeKind::Pointer ||
	    type->kind == pa11::TypeKind::LValueReference ||
	    type->kind == pa11::TypeKind::RValueReference ||
	    type->kind == pa11::TypeKind::Array)
		return template_type_has_template_parameter(
			type->base,
			record_template_arguments);
	if (type->kind == pa11::TypeKind::Function)
	{
		if (template_type_has_template_parameter(type->base,
		                                        record_template_arguments))
			return true;
		for (size_t i = 0; i < type->parameters.size(); ++i)
			if (template_type_has_template_parameter(
				    type->parameters[i],
				    record_template_arguments))
				return true;
	}
	if (type->kind == pa11::TypeKind::MemberPointer)
		return template_type_has_template_parameter(
			       type->member_class,
			       record_template_arguments) ||
		       template_type_has_template_parameter(type->base,
		                                           record_template_arguments);
	if (type->kind == pa11::TypeKind::Record)
	{
		if (type->is_template_specialization &&
		    type->scope == NULL &&
		    !type->template_primary_name.empty())
			return true;
		if (type->is_template_specialization ||
		    type->is_dependent_typename)
		{
			map<const void*, vector<TemplateArgument> >::const_iterator found =
				record_template_arguments.find(type.get());
			if (found != record_template_arguments.end())
				for (size_t i = 0; i < found->second.size(); ++i)
					if (template_argument_has_template_parameter(
						    found->second[i],
						    record_template_arguments))
						return true;
		}
		if (type->is_template_specialization)
			for (size_t i = 0; i < type->template_arguments.size(); ++i)
				if (template_instance_argument_has_template_parameter(
					    type->template_arguments[i],
					    record_template_arguments))
					return true;
	}
	return false;
}

bool Parser::template_arguments_dependent(
	const vector<TemplateArgument>& arguments) const
{
	const bool allow_complete_record =
		active_class_instantiations_.empty() &&
		!validating_template_definition_;
	for (size_t i = 0; i < arguments.size(); ++i)
	{
		bool dependent =
			template_argument_has_template_parameter(
				arguments[i],
				record_template_arguments_);
		if (dependent &&
		    arguments[i].kind == TemplateArgumentKind::Pack)
		{
			dependent = false;
			for (size_t p = 0; p < arguments[i].pack.size(); ++p)
			{
				bool element_dependent =
					template_argument_has_template_parameter(
						arguments[i].pack[p],
						record_template_arguments_);
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
