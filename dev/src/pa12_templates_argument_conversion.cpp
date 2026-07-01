#include "pa12_internal.h"
#include "pa12_templates_function_support.h"
#include "pa12_templates_instance_support.h"

#include <stdexcept>

using namespace std;

namespace pa12 {
namespace internal {
size_t dependent_cache_string_hash(const string& value);
size_t dependent_cache_type_identity(TypePtr type);
size_t dependent_cache_template_argument_identity(
	const TemplateArgument& argument,
	int depth);

pa11::TemplateInstanceArgument completed_instance_argument(
	const TemplateArgument& argument)
{
	if (argument.pack_expansion && argument.kind != TemplateArgumentKind::Pack)
	{
		TemplateArgument element = argument;
		element.pack_expansion = false;
		vector<pa11::TemplateInstanceArgument> pack;
		pack.push_back(completed_instance_argument(element));
		return pa11::TemplateInstanceArgument::pack_arg(pack);
	}
	if (argument.kind == TemplateArgumentKind::Type)
		return pa11::TemplateInstanceArgument::type_arg(argument.type);
	if (argument.kind == TemplateArgumentKind::Value)
	{
		pa11::TemplateInstanceArgument out = argument.dependent
			? pa11::TemplateInstanceArgument::dependent_value_arg(argument.type)
			: pa11::TemplateInstanceArgument::value_arg(argument.type,
			                                            argument.value);
		out.value_name = argument.value_name;
		out.value_negated = argument.value_negated;
		out.value_owner_template_name =
			argument.value_owner_template_name;
		out.value_member_name = argument.value_member_name;
		out.value_owner_template_arguments =
			argument.value_owner_template_arguments;
		out.value_expr_begin = argument.value_expr_begin;
		out.value_expr_end = argument.value_expr_end;
		return out;
	}
	if (argument.kind == TemplateArgumentKind::Template)
	{
		pa11::TemplateInstanceArgument out =
			pa11::TemplateInstanceArgument::template_arg(
				argument.template_declaration != NULL
				? qualified_template_declaration_name(
					argument.template_declaration)
				: argument.value_name);
		out.dependent = argument.template_declaration == NULL;
		return out;
	}
	vector<pa11::TemplateInstanceArgument> pack;
	for (size_t i = 0; i < argument.pack.size(); ++i)
	{
		TemplateArgument element = argument.pack[i];
		if (element.kind == TemplateArgumentKind::Value &&
		    !element.dependent)
			element.pack_expansion = false;
		pack.push_back(completed_instance_argument(element));
	}
	pa11::TemplateInstanceArgument out =
		pa11::TemplateInstanceArgument::pack_arg(pack);
	out.value_name = argument.value_name;
	out.template_name = argument.value_name;
	return out;
}

bool template_argument_kind_matches_parameter(
	const TemplateArgument& argument,
	const TemplateParameterInfo& parameter)
{
	if (parameter.kind == TemplateParameterKind::Type)
		return argument.kind == TemplateArgumentKind::Type;
	if (parameter.kind == TemplateParameterKind::NonType)
		return argument.kind == TemplateArgumentKind::Value;
	if (argument.kind != TemplateArgumentKind::Template)
		return false;
	if (argument.template_declaration == NULL)
		return true;
	if (argument.template_declaration->kind == TemplateDeclarationKind::Alias)
		return true;
	const vector<TemplateParameterInfo>& params =
		argument.template_declaration->parameters;
	if (parameter.template_parameters.size() == 1 &&
	    parameter.template_parameters[0].kind == TemplateParameterKind::Type)
	{
		size_t required = 0;
		for (size_t i = 0; i < params.size(); ++i)
		{
			if (params[i].kind != TemplateParameterKind::Type)
				return false;
			if (!params[i].has_default && !params[i].is_pack)
				++required;
		}
		return required <= 1;
	}
	size_t actual = 0;
	for (size_t expected = 0;
	     expected < parameter.template_parameters.size();
	     ++expected)
	{
		const TemplateParameterInfo& expected_param =
			parameter.template_parameters[expected];
		if (expected_param.is_pack)
		{
			for (; actual < params.size(); ++actual)
				if (params[actual].kind != expected_param.kind)
					return false;
			return true;
		}
		if (actual >= params.size())
			return false;
		if (params[actual].kind != expected_param.kind ||
		    params[actual].is_pack != expected_param.is_pack)
			return false;
		++actual;
	}
	return actual == params.size();
}

bool unsigned_integral_template_parameter(TypePtr type)
{
	TypePtr bare = type.get() != NULL ? pa11::strip_cv(type) : TypePtr();
	if (bare.get() == NULL)
		return false;
	if (bare->kind == pa11::TypeKind::Enum)
	{
		switch (bare->enum_underlying)
		{
		case FT_UNSIGNED_CHAR:
		case FT_UNSIGNED_SHORT_INT:
		case FT_UNSIGNED_INT:
		case FT_UNSIGNED_LONG_INT:
		case FT_UNSIGNED_LONG_LONG_INT:
			return true;
		default:
			return false;
		}
	}
	if (bare->kind != pa11::TypeKind::Fundamental)
		return false;
	switch (bare->fundamental)
	{
	case FT_BOOL:
	case FT_UNSIGNED_CHAR:
	case FT_UNSIGNED_SHORT_INT:
	case FT_UNSIGNED_INT:
	case FT_UNSIGNED_LONG_INT:
	case FT_UNSIGNED_LONG_LONG_INT:
	case FT_CHAR16_T:
	case FT_CHAR32_T:
		return true;
	default:
		return false;
	}
}

TemplateArgument convert_non_type_template_argument(
	TemplateArgument argument,
	TypePtr parameter_type)
{
	if (argument.kind != TemplateArgumentKind::Value ||
	    parameter_type.get() == NULL)
		return argument;
	if (argument.value_binding != NULL)
	{
		TypePtr parameter_bare = pa11::strip_cv(parameter_type);
		TypePtr argument_bare = argument.type.get() != NULL
			? pa11::strip_cv(argument.type) : TypePtr();
		if (parameter_bare->kind == pa11::TypeKind::LValueReference ||
		    parameter_bare->kind == pa11::TypeKind::RValueReference)
		{
			TypePtr target = pa11::strip_cv(parameter_bare->base);
			TypePtr source = argument.value_binding->type.get() != NULL
				? pa11::strip_cv(argument.value_binding->type)
				: TypePtr();
			if (source.get() == NULL || !pa11::same_type(target, source))
				throw runtime_error("invalid non-type template argument");
			argument.type = parameter_type;
			return argument;
		}
		if (argument.value_binding->kind == BindingKind::Function &&
		    (pa11::same_type(argument.type, parameter_type) ||
		     (parameter_bare->kind == pa11::TypeKind::Function &&
		      argument_bare.get() != NULL &&
		      argument_bare->kind == pa11::TypeKind::Pointer &&
		      pa11::same_type(argument_bare->base, parameter_bare))))
		{
			argument.type = parameter_type;
			return argument;
		}
		if (parameter_bare->kind == pa11::TypeKind::MemberPointer &&
		    argument_bare.get() != NULL &&
		    argument_bare->kind == pa11::TypeKind::MemberPointer &&
		    pa11::same_type(argument_bare, parameter_bare))
		{
			argument.type = parameter_type;
			return argument;
		}
		throw runtime_error("invalid non-type template argument");
	}
	TypePtr bare = pa11::strip_cv(parameter_type);
	if (bare->kind == pa11::TypeKind::Fundamental &&
	    bare->fundamental == FT_BOOL)
		argument.value = argument.value != 0 ? 1 : 0;
	else
	{
		size_t size = 0;
		try
		{
			size = pa11::type_size(parameter_type);
		}
		catch (const runtime_error&)
		{
			size = 0;
		}
		if (size > 0 && size < 8)
		{
			uint64_t mask = (uint64_t(1) << (size * 8)) - 1;
			argument.value &= mask;
			if (!unsigned_integral_template_parameter(parameter_type))
			{
				uint64_t sign = uint64_t(1) << (size * 8 - 1);
				if ((argument.value & sign) != 0)
					argument.value |= ~mask;
			}
		}
	}
	argument.type = parameter_type;
	return argument;
}

	bool dependent_typename_condition_false(TypePtr type)
	{
		if (type.get() == NULL || type->template_arguments.empty())
			return false;
		const pa11::TemplateInstanceArgument& condition =
			type->template_arguments[0];
		if (condition.kind != pa11::TemplateInstanceArgumentKind::Value)
			return false;
		return !condition.dependent && condition.value == 0;
	}

}  // namespace internal
}  // namespace pa12
