#include "pa12_templates_function_support.h"
#include "pa12_templates_instance_support.h"
#include "pa12_templates_type_substitution_engine.h"
#include "pa12_types_support.h"

#include <algorithm>
#include <stdexcept>
#include <utility>

using namespace std;

namespace pa12 {
namespace internal {

size_t dependent_type_cache_hash_combine(size_t seed, size_t value);

bool active_class_instantiation_named(
	const vector<ActiveClassInstantiation>& active,
	const string& name)
{
	for (size_t i = 0; i < active.size(); ++i)
		if (active[i].declaration != NULL &&
		    active[i].declaration->name == name)
			return true;
	return false;
}

bool hosted_nonrecord_member_typename_probe(
	bool hosted_compatibility,
	const vector<ActiveClassInstantiation>& active,
	const string& root_name,
	const string& suffix,
	TypePtr root_substitution)
{
	if (!hosted_compatibility ||
	    root_name.empty() ||
	    suffix.empty() ||
	    !active_class_instantiation_named(active, "allocator_traits"))
		return false;
	TypePtr bare_root = root_substitution.get() != NULL
		? pa11::strip_cv(root_substitution) : TypePtr();
	return bare_root.get() != NULL &&
	       !bare_root->is_dependent_typename &&
	       bare_root->kind != pa11::TypeKind::Record &&
	       bare_root->kind != pa11::TypeKind::TemplateParameter;
}

bool dependent_typename_member_type_name(TypePtr type)
{
	if (type.get() == NULL)
		return false;
	size_t pos = type->name.rfind("::");
	return pos != string::npos && type->name.substr(pos + 2) == "type";
}

size_t shallow_type_cache_hash(TypePtr type)
{
	if (type.get() == NULL)
		return 0;
	TypePtr bare = pa11::strip_cv(type);
	size_t key = reinterpret_cast<uintptr_t>(bare.get());
	key = dependent_type_cache_hash_combine(
		key,
		static_cast<size_t>(bare->kind));
	key = dependent_type_cache_hash_combine(
		key,
		bare->template_arguments.size());
	key = dependent_type_cache_hash_combine(
		key,
		bare->dependent_typename_template_argument_lists.size());
	return key;
}

	size_t shallow_template_argument_cache_hash(const TemplateArgument& argument)
	{
	size_t key = static_cast<size_t>(argument.kind);
	key = dependent_type_cache_hash_combine(
		key,
		shallow_type_cache_hash(argument.type));
	key = dependent_type_cache_hash_combine(
		key,
		reinterpret_cast<uintptr_t>(argument.value_binding));
	key = dependent_type_cache_hash_combine(
		key,
		reinterpret_cast<uintptr_t>(argument.template_declaration));
	key = dependent_type_cache_hash_combine(key, argument.value);
	key = dependent_type_cache_hash_combine(key, argument.dependent);
	key = dependent_type_cache_hash_combine(key, argument.pack.size());
	key = dependent_type_cache_hash_combine(
		key,
		argument.value_owner_template_arguments.size());
		return key;
	}

	bool replayable_dependent_value_instance_argument(
		const pa11::TemplateInstanceArgument& argument)
	{
		if (argument.kind == pa11::TemplateInstanceArgumentKind::Value &&
		    argument.dependent &&
		    argument.value_expr_end > argument.value_expr_begin)
			return true;
		for (size_t i = 0; i < argument.value_owner_template_arguments.size();
		     ++i)
			if (replayable_dependent_value_instance_argument(
				    argument.value_owner_template_arguments[i]))
				return true;
		for (size_t i = 0; i < argument.pack.size(); ++i)
			if (replayable_dependent_value_instance_argument(
				    argument.pack[i]))
				return true;
		return false;
	}

	bool replayable_dependent_value_argument(const TemplateArgument& argument)
	{
		if (argument.kind == TemplateArgumentKind::Value &&
		    argument.dependent &&
		    argument.value_expr_end > argument.value_expr_begin)
			return true;
		for (size_t i = 0; i < argument.value_owner_template_arguments.size();
		     ++i)
			if (replayable_dependent_value_instance_argument(
				    argument.value_owner_template_arguments[i]))
				return true;
		for (size_t i = 0; i < argument.pack.size(); ++i)
			if (replayable_dependent_value_argument(argument.pack[i]))
				return true;
		return false;
	}

	bool dependent_decltype_has_template_argument_name(
		const string& spelling,
		const string& name)
	{
		if (name.empty())
			return false;
		for (size_t pos = spelling.find(name);
		     pos != string::npos;
		     pos = spelling.find(name, pos + name.size()))
		{
			size_t end = pos + name.size();
			if (pos != 0 &&
			    dependent_spelling_word_char(spelling[pos - 1]))
				continue;
			if (end < spelling.size() &&
			    dependent_spelling_word_char(spelling[end]))
				continue;
			char before = pos == 0 ? '\0' : spelling[pos - 1];
			char after = end < spelling.size() ? spelling[end] : '\0';
			if ((before == '<' || before == ',') &&
			    (after == '>' || after == ','))
				return true;
		}
		return false;
	}
}  // namespace internal
}  // namespace pa12
