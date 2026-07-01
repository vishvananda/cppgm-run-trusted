#include "pa12_templates_instance_support.h"
#include "pa12_types_support.h"
#include "pa12_templates_dependent_value_member_body_a.h"
#include "pa12_templates_dependent_value_member_body_b.h"

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
size_t dependent_cache_hash_combine(size_t seed, size_t value);
size_t dependent_cache_string_hash(const string& value);
size_t dependent_cache_type_identity(TypePtr type);
size_t dependent_cache_template_argument_identity(
	const TemplateArgument& argument,
	int depth);
size_t dependent_value_member_cache_prefix(const TemplateArgument& arg);

string hosted_unqualified_template_primary(TypePtr record)
{
	record = record.get() != NULL ? pa11::strip_cv(record) : TypePtr();
	if (record.get() == NULL)
		return string();
	string primary = record->template_primary_name;
	if (primary.empty() && record->scope != NULL)
		primary = record->scope->name;
	size_t pos = primary.rfind("::");
	return pos == string::npos ? primary : primary.substr(pos + 2);
}

bool hosted_enable_shared_from_this_type(TypePtr record)
{
	return hosted_unqualified_template_primary(record) ==
	       "enable_shared_from_this";
}

bool hosted_record_has_esft_base_type(TypePtr record, set<const void*>& seen)
{
	record = record.get() != NULL ? pa11::strip_cv(record) : TypePtr();
	if (record.get() == NULL ||
	    record->kind != pa11::TypeKind::Record ||
	    !seen.insert(record.get()).second)
		return false;
	vector<TypePtr> bases = pa11::record_direct_bases(record);
	for (size_t i = 0; i < bases.size(); ++i)
	{
		TypePtr base = bases[i].get() != NULL
			? pa11::strip_cv(bases[i]) : TypePtr();
		if (hosted_enable_shared_from_this_type(base) ||
		    hosted_record_has_esft_base_type(base, seen))
			return true;
	}
	return false;
}

bool Parser::resolve_dependent_trait_subject_type(TypePtr raw_type,
                                                  TypePtr& out_type) const
{
	TypePtr bare = raw_type.get() != NULL
		? pa11::strip_cv(raw_type) : TypePtr();
	if (bare.get() == NULL)
		return false;
	if (bare->kind == pa11::TypeKind::TemplateParameter &&
	    !bare->is_dependent_typename)
	{
		TypePtr subst;
		if (!find_template_type_substitution(bare->name, subst))
			return false;
		out_type = subst;
		return true;
	}
	if (bare->is_dependent_typename ||
	    template_type_has_template_parameter(raw_type,
	                                         record_template_arguments_))
		return false;
	out_type = raw_type;
	return true;
}

bool Parser::resolve_dependent_value_member_argument(
	const TemplateArgument& arg,
	TemplateArgument& out) const
{
	PA12_DEPENDENT_VALUE_MEMBER_BODY_A
	PA12_DEPENDENT_VALUE_MEMBER_BODY_B
}

}  // namespace internal
}  // namespace pa12
