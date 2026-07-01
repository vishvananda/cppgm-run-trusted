#include "pa12_templates_instance_support.h"
#include "pa12_types_support.h"

#include <algorithm>
#include <cstdint>
#include <functional>
#include <map>
#include <sstream>
#include <stdexcept>
#include <utility>

#include "posttoken_pipeline.h"
#include "pp_token.h"

using namespace std;

namespace pa12 {
namespace internal {

const size_t kDependentIdentityMemoEntryLimit = 500000;

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

size_t dependent_cache_instance_argument_identity(
	const pa11::TemplateInstanceArgument& argument,
	int depth);

size_t dependent_cache_type_identity_fingerprint_impl(TypePtr type, int depth)
{
	if (type.get() == NULL)
		return 0;
	size_t out = reinterpret_cast<uintptr_t>(type.get());
	out = dependent_cache_hash_combine(out, static_cast<size_t>(type->kind));
	out = dependent_cache_hash_combine(out, type->fundamental);
	out = dependent_cache_hash_combine(out, type->cv);
	out = dependent_cache_hash_combine(out, type->ref_qualifier);
	out = dependent_cache_hash_combine(
		out,
		reinterpret_cast<uintptr_t>(type->base.get()));
	out = dependent_cache_hash_combine(
		out,
		reinterpret_cast<uintptr_t>(type->member_class.get()));
	out = dependent_cache_hash_combine(out, type->unknown_bound);
	out = dependent_cache_hash_combine(out, type->bound);
	out = dependent_cache_hash_combine(out, type->variadic);
	out = dependent_cache_hash_combine(
		out,
		dependent_cache_string_hash(type->name));
	out = dependent_cache_hash_combine(
		out,
		dependent_cache_string_hash(type->template_primary_name));
	out = dependent_cache_hash_combine(
		out,
		reinterpret_cast<uintptr_t>(type->scope));
	out = dependent_cache_hash_combine(out,
	                                   type->is_template_specialization);
	out = dependent_cache_hash_combine(out,
	                                   type->is_extern_template_instantiation);
	out = dependent_cache_hash_combine(out, type->is_dependent_typename);
	out = dependent_cache_hash_combine(out,
	                                   type->dependent_typename_qualified);
	out = dependent_cache_hash_combine(out,
	                                   type->dependent_typename_template_id);
	out = dependent_cache_hash_combine(out,
	                                   type->dependent_typename_decltype);
	if (type->is_dependent_typename)
		out = dependent_cache_hash_combine(
			out,
			reinterpret_cast<uintptr_t>(type.get()));
	out = dependent_cache_hash_combine(out, type->parameters.size());
	out = dependent_cache_hash_combine(out, type->template_arguments.size());
	out = dependent_cache_hash_combine(
		out,
		type->dependent_typename_template_argument_lists.size());
	if (depth > 8)
		return dependent_cache_hash_combine(out, 0x1d37);
	out = dependent_cache_hash_combine(
		out,
		dependent_cache_type_identity_fingerprint_impl(type->base,
		                                               depth + 1));
	out = dependent_cache_hash_combine(
		out,
		dependent_cache_type_identity_fingerprint_impl(type->member_class,
		                                               depth + 1));
	for (size_t i = 0; i < type->parameters.size(); ++i)
		out = dependent_cache_hash_combine(
			out,
			dependent_cache_type_identity_fingerprint_impl(
				type->parameters[i],
				depth + 1));
	return out;
}

size_t dependent_cache_type_identity_fingerprint(TypePtr type)
{
	return dependent_cache_type_identity_fingerprint_impl(type, 0);
}

size_t dependent_cache_type_identity_impl(TypePtr type, int depth)
{
	if (type.get() == NULL)
		return 0;
	static size_t calls = 0;
	static size_t hits = 0;
	static size_t inserts = 0;
	++calls;
	typedef pair<const void*, int> CacheKey;
	static map<CacheKey, pair<size_t, size_t> > cache;
	CacheKey cache_key(type.get(), depth);
	size_t fingerprint = dependent_cache_type_identity_fingerprint(type);
	map<CacheKey, pair<size_t, size_t> >::const_iterator cached =
		cache.find(cache_key);
	if (cached != cache.end() && cached->second.first == fingerprint)
	{
		++hits;
		return cached->second.second;
	}
	size_t out = reinterpret_cast<uintptr_t>(type.get());
	out = dependent_cache_hash_combine(
		out,
		static_cast<size_t>(type->kind));
	out = dependent_cache_hash_combine(out, type->fundamental);
	out = dependent_cache_hash_combine(out, type->cv);
	out = dependent_cache_hash_combine(out, type->ref_qualifier);
	out = dependent_cache_hash_combine(out, type->unknown_bound);
	out = dependent_cache_hash_combine(out, type->bound);
	out = dependent_cache_hash_combine(out, type->variadic);
	out = dependent_cache_hash_combine(
		out,
		dependent_cache_string_hash(type->name));
	out = dependent_cache_hash_combine(
		out,
		dependent_cache_string_hash(type->template_primary_name));
	out = dependent_cache_hash_combine(
		out,
		reinterpret_cast<uintptr_t>(type->scope));
	out = dependent_cache_hash_combine(out,
	                                   type->is_template_specialization);
	out = dependent_cache_hash_combine(out,
	                                   type->is_extern_template_instantiation);
	out = dependent_cache_hash_combine(out, type->is_dependent_typename);
	out = dependent_cache_hash_combine(out,
	                                   type->dependent_typename_qualified);
	out = dependent_cache_hash_combine(out,
	                                   type->dependent_typename_template_id);
	out = dependent_cache_hash_combine(out,
	                                   type->dependent_typename_decltype);
	out = dependent_cache_hash_combine(out, type->parameters.size());
	out = dependent_cache_hash_combine(out, type->template_arguments.size());
	out = dependent_cache_hash_combine(
		out,
		type->dependent_typename_template_argument_lists.size());
	if (depth > 8)
		return dependent_cache_hash_combine(out, 0xcafe);
	out = dependent_cache_hash_combine(
		out,
		dependent_cache_type_identity_impl(type->base, depth + 1));
	out = dependent_cache_hash_combine(
		out,
		dependent_cache_type_identity_impl(type->member_class, depth + 1));
	for (size_t i = 0; i < type->parameters.size(); ++i)
		out = dependent_cache_hash_combine(
			out,
			dependent_cache_type_identity_impl(type->parameters[i],
			                                   depth + 1));
	for (size_t i = 0; i < type->template_arguments.size(); ++i)
		out = dependent_cache_hash_combine(
			out,
			dependent_cache_instance_argument_identity(
				type->template_arguments[i],
				depth + 1));
	for (size_t i = 0;
	     i < type->dependent_typename_template_argument_lists.size();
	     ++i)
	{
		out = dependent_cache_hash_combine(
			out,
			type->dependent_typename_template_argument_lists[i].size());
		for (size_t j = 0;
		     j < type->dependent_typename_template_argument_lists[i].size();
		     ++j)
			out = dependent_cache_hash_combine(
			out,
			dependent_cache_instance_argument_identity(
				type->dependent_typename_template_argument_lists[i][j],
				depth + 1));
	}
	cache[cache_key] = make_pair(fingerprint, out);
	++inserts;
	if (cache.size() > kDependentIdentityMemoEntryLimit)
		cache.clear();
	return out;
}

size_t dependent_cache_type_identity(TypePtr type)
{
	return dependent_cache_type_identity_impl(type, 0);
}

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
			dependent_cache_type_identity_impl(argument.type,
			                                   depth + 1));
	if (argument.kind == TemplateArgumentKind::Value)
	{
		out = dependent_cache_hash_combine(
			out,
			dependent_cache_type_identity_impl(argument.type,
			                                   depth + 1));
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
		out = dependent_cache_hash_combine(out, argument.value_expr_begin);
		out = dependent_cache_hash_combine(out, argument.value_expr_end);
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
			dependent_cache_type_identity_impl(argument.type,
			                                   depth + 1));
	if (argument.kind == pa11::TemplateInstanceArgumentKind::Value)
	{
		out = dependent_cache_hash_combine(
			out,
			dependent_cache_type_identity_impl(argument.type,
			                                   depth + 1));
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
		out = dependent_cache_hash_combine(out, argument.value_expr_begin);
		out = dependent_cache_hash_combine(out, argument.value_expr_end);
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
