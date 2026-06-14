#include "pa12_templates_instance_support.h"
#include "pa12_types_support.h"

#include <algorithm>
#include <cstdint>
#include <functional>
#include <sstream>
#include <stdexcept>
#include <utility>

#include "posttoken_pipeline.h"
#include "pp_token.h"

using namespace std;

namespace pa12 {
namespace internal {
size_t dependent_cache_hash_combine(size_t seed, size_t value)
{
	return seed ^ (value + 0x9e3779b97f4a7c15ULL + (seed << 6) +
	               (seed >> 2));
}

size_t dependent_cache_string_hash(const string& value)
{
	return dependent_cache_hash_combine(value.size(),
	                                    hash<string>()(value));
}

size_t dependent_cache_type_identity(TypePtr type)
{
	type = type.get() != NULL ? pa11::strip_cv(type) : TypePtr();
	if (type.get() == NULL)
		return 0;
	size_t out = reinterpret_cast<uintptr_t>(type.get());
	out = dependent_cache_hash_combine(
		out,
		static_cast<size_t>(type->kind));
	out = dependent_cache_hash_combine(out,
	                                   type->is_template_specialization);
	out = dependent_cache_hash_combine(out, type->is_dependent_typename);
	out = dependent_cache_hash_combine(
		out,
		dependent_cache_string_hash(type->template_primary_name));
	return out;
}

size_t dependent_cache_instance_argument_identity(
	const pa11::TemplateInstanceArgument& argument,
	int depth);

size_t dependent_cache_template_argument_identity(
	const TemplateArgument& argument,
	int depth)
{
	size_t out = static_cast<size_t>(argument.kind);
	if (depth > 8)
		return dependent_cache_hash_combine(out, 0xfeed);
	if (argument.kind == TemplateArgumentKind::Type)
		return dependent_cache_hash_combine(
			out,
			dependent_cache_type_identity(argument.type));
	if (argument.kind == TemplateArgumentKind::Value)
	{
		out = dependent_cache_hash_combine(
			out,
			dependent_cache_type_identity(argument.type));
		out = dependent_cache_hash_combine(
			out,
			reinterpret_cast<uintptr_t>(argument.value_binding));
		out = dependent_cache_hash_combine(
			out,
			dependent_cache_string_hash(argument.value_name));
		out = dependent_cache_hash_combine(
			out,
			dependent_cache_string_hash(
				argument.value_owner_template_name));
		out = dependent_cache_hash_combine(
			out,
			dependent_cache_string_hash(argument.value_member_name));
		out = dependent_cache_hash_combine(out, argument.value);
		out = dependent_cache_hash_combine(out, argument.dependent);
		out = dependent_cache_hash_combine(out, argument.value_negated);
		for (size_t i = 0;
		     i < argument.value_owner_template_arguments.size();
		     ++i)
			out = dependent_cache_hash_combine(
				out,
				dependent_cache_instance_argument_identity(
					argument.value_owner_template_arguments[i],
					depth + 1));
		return out;
	}
	if (argument.kind == TemplateArgumentKind::Template)
	{
		out = dependent_cache_hash_combine(
			out,
			reinterpret_cast<uintptr_t>(argument.template_declaration));
		return dependent_cache_hash_combine(
			out,
			dependent_cache_string_hash(argument.value_name));
	}
	out = dependent_cache_hash_combine(
		out,
		dependent_cache_string_hash(argument.value_name));
	for (size_t i = 0; i < argument.pack.size(); ++i)
		out = dependent_cache_hash_combine(
			out,
			dependent_cache_template_argument_identity(argument.pack[i],
			                                           depth + 1));
	return out;
}

size_t dependent_cache_instance_argument_identity(
	const pa11::TemplateInstanceArgument& argument,
	int depth)
{
	size_t out = static_cast<size_t>(argument.kind);
	if (depth > 8)
		return dependent_cache_hash_combine(out, 0xbeef);
	if (argument.kind == pa11::TemplateInstanceArgumentKind::Type)
		return dependent_cache_hash_combine(
			out,
			dependent_cache_type_identity(argument.type));
	if (argument.kind == pa11::TemplateInstanceArgumentKind::Value)
	{
		out = dependent_cache_hash_combine(
			out,
			dependent_cache_type_identity(argument.type));
		out = dependent_cache_hash_combine(
			out,
			dependent_cache_string_hash(argument.value_name));
		out = dependent_cache_hash_combine(
			out,
			dependent_cache_string_hash(
				argument.value_owner_template_name));
		out = dependent_cache_hash_combine(
			out,
			dependent_cache_string_hash(argument.value_member_name));
		out = dependent_cache_hash_combine(out, argument.value);
		out = dependent_cache_hash_combine(out, argument.dependent);
		out = dependent_cache_hash_combine(out, argument.value_negated);
		for (size_t i = 0;
		     i < argument.value_owner_template_arguments.size();
		     ++i)
			out = dependent_cache_hash_combine(
				out,
				dependent_cache_instance_argument_identity(
					argument.value_owner_template_arguments[i],
					depth + 1));
		return out;
	}
	if (argument.kind == pa11::TemplateInstanceArgumentKind::Template)
	{
		out = dependent_cache_hash_combine(
			out,
			dependent_cache_string_hash(argument.template_name));
		return dependent_cache_hash_combine(out, argument.dependent);
	}
	out = dependent_cache_hash_combine(
		out,
		dependent_cache_string_hash(argument.value_name));
	out = dependent_cache_hash_combine(
		out,
		dependent_cache_string_hash(argument.template_name));
	for (size_t i = 0; i < argument.pack.size(); ++i)
		out = dependent_cache_hash_combine(
			out,
			dependent_cache_instance_argument_identity(argument.pack[i],
			                                           depth + 1));
	return out;
}

size_t dependent_value_member_cache_prefix(const TemplateArgument& arg)
{
	size_t out = dependent_cache_string_hash(arg.value_owner_template_name);
	out = dependent_cache_hash_combine(
		out,
		dependent_cache_string_hash(arg.value_member_name));
	out = dependent_cache_hash_combine(
		out,
		dependent_cache_string_hash(arg.value_name));
	for (size_t i = 0; i < arg.value_owner_template_arguments.size(); ++i)
		out = dependent_cache_hash_combine(
			out,
			dependent_cache_instance_argument_identity(
				arg.value_owner_template_arguments[i],
				0));
	return out;
}

}  // namespace internal
}  // namespace pa12
