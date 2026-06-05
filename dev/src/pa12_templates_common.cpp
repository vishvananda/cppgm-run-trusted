#include "pa12_internal.h"

using namespace std;

namespace pa12 {
namespace internal {

bool template_argument_has_template_parameter(
	const TemplateArgument& arg,
	const map<const void*, vector<TemplateArgument> >& record_template_arguments)
{
	if (arg.kind == TemplateArgumentKind::Type)
		return template_type_has_template_parameter(
			arg.type,
			record_template_arguments);
	if (arg.kind == TemplateArgumentKind::Value)
		return arg.dependent ||
		       template_type_has_template_parameter(
			       arg.type,
			       record_template_arguments);
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
	return false;
}

bool template_type_has_template_parameter(
	TypePtr type,
	const map<const void*, vector<TemplateArgument> >& record_template_arguments)
{
	if (type.get() == NULL)
		return false;
	type = pa11::strip_cv(type);
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
		map<const void*, vector<TemplateArgument> >::const_iterator found =
			record_template_arguments.find(type.get());
		if (found != record_template_arguments.end())
			for (size_t i = 0; i < found->second.size(); ++i)
				if (template_argument_has_template_parameter(
					    found->second[i],
					    record_template_arguments))
					return true;
	}
	return false;
}

bool Parser::template_arguments_dependent(
	const vector<TemplateArgument>& arguments) const
{
	for (size_t i = 0; i < arguments.size(); ++i)
		if (template_argument_has_template_parameter(
			    arguments[i],
			    record_template_arguments_))
			return true;
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
