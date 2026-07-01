#include "pa12_templates_instance_support.h"
#include "pa12_types_support.h"
#include <algorithm>
#include <cstdint>
#include <sstream>
#include <stdexcept>
#include <utility>
#include "posttoken_pipeline.h"
#include "pp_token.h"
using namespace std;
namespace pa12 {
namespace internal {

const size_t kDependentTypenameResolutionCacheLimit = 65536;

size_t dependent_cache_hash_combine(size_t seed, size_t value);
size_t dependent_type_argument_hash(const TemplateArgument& argument,
                                    int depth);
size_t dependent_type_cache_hash_combine(size_t seed, size_t value);
size_t dependent_type_cache_string_hash(const string& value);
size_t dependent_type_structural_hash(TypePtr type, int depth);

void Parser::trim_dependent_typename_resolution_caches() const
{
	if (dependent_typename_resolution_cache_.size() +
	    dependent_typename_resolution_fail_cache_.size() <=
	    kDependentTypenameResolutionCacheLimit)
		return;
	dependent_typename_resolution_cache_.clear();
	dependent_typename_resolution_fail_cache_.clear();
}

size_t Parser::dependent_typename_resolution_active_key(TypePtr type) const
{
	size_t key = dependent_type_cache_hash_combine(
		0x39a,
		dependent_type_structural_hash(type, 0));
	key = dependent_type_cache_hash_combine(
		key,
		reinterpret_cast<uintptr_t>(current_scope()));
	key = dependent_type_cache_hash_combine(
		key,
		validating_template_definition_ ? 1 : 0);
	key = dependent_type_cache_hash_combine(
		key,
		function_template_candidate_instantiation_depth_);
	key = dependent_type_cache_hash_combine(key,
	                                        active_class_instantiations_.size());
	for (size_t i = 0; i < active_class_instantiations_.size(); ++i)
	{
		const ActiveClassInstantiation& active =
			active_class_instantiations_[i];
		key = dependent_type_cache_hash_combine(
			key,
			reinterpret_cast<uintptr_t>(active.declaration));
		key = dependent_type_cache_hash_combine(
			key,
			dependent_type_cache_string_hash(active.specialization_name));
		key = dependent_type_cache_hash_combine(
			key,
			dependent_type_structural_hash(active.type, 0));
	}
	key = dependent_type_cache_hash_combine(
		key,
		template_type_substitutions_.size());
	for (size_t i = 0; i < template_type_substitutions_.size(); ++i)
	{
		key = dependent_type_cache_hash_combine(key, i);
		for (map<string, TypePtr>::const_iterator it =
			     template_type_substitutions_[i].begin();
		     it != template_type_substitutions_[i].end();
		     ++it)
		{
			key = dependent_type_cache_hash_combine(
				key,
				dependent_type_cache_string_hash(it->first));
			key = dependent_type_cache_hash_combine(
				key,
				dependent_type_structural_hash(it->second, 0));
		}
	}
	key = dependent_type_cache_hash_combine(
		key,
		template_value_substitutions_.size());
	for (size_t i = 0; i < template_value_substitutions_.size(); ++i)
	{
		key = dependent_type_cache_hash_combine(key, i);
		for (map<string, TemplateArgument>::const_iterator it =
			     template_value_substitutions_[i].begin();
		     it != template_value_substitutions_[i].end();
		     ++it)
		{
			key = dependent_type_cache_hash_combine(
				key,
				dependent_type_cache_string_hash(it->first));
			key = dependent_type_cache_hash_combine(
				key,
				dependent_type_argument_hash(it->second, 0));
		}
	}
	return key;
}

TypePtr Parser::resolve_dependent_typename_type(TypePtr type) const
{
	if (type.get() == NULL ||
	    !type->is_dependent_typename)
		return TypePtr();
	size_t cache_key = dependent_typename_match_cache_key(type);
	cache_key = dependent_cache_hash_combine(
		cache_key,
		template_declarations_.size());
	cache_key = dependent_cache_hash_combine(
		cache_key,
		member_function_template_generation_);
	map<size_t, TypePtr>::const_iterator cached =
		dependent_typename_resolution_cache_.find(cache_key);
	if (cached != dependent_typename_resolution_cache_.end())
		return cached->second;
	if (dependent_typename_resolution_fail_cache_.count(cache_key) != 0)
		return TypePtr();
	size_t active_key = dependent_typename_resolution_active_key(type);
	if (!active_dependent_typename_resolution_keys_.insert(active_key).second)
		return TypePtr();
	struct ActiveDependentTypenameResolution
	{
		set<size_t>& keys;
		size_t key;
		ActiveDependentTypenameResolution(set<size_t>& k, size_t cache_key)
			: keys(k), key(cache_key)
		{
		}
		~ActiveDependentTypenameResolution()
		{
			keys.erase(key);
		}
	} active(active_dependent_typename_resolution_keys_, active_key);
	TypePtr resolved = resolve_dependent_typename_type_uncached(type);
	if (resolved.get() != NULL && resolved != type)
	{
		dependent_typename_resolution_cache_[cache_key] = resolved;
		trim_dependent_typename_resolution_caches();
	}
	else
	{
		dependent_typename_resolution_fail_cache_.insert(cache_key);
		trim_dependent_typename_resolution_caches();
	}
	return resolved;
}


}  // namespace internal
}  // namespace pa12
