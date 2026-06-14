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
namespace {

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

}  // namespace

TypePtr substitute_template_type_with_engine(const Parser& parser, TypePtr type);

TypePtr Parser::substitute_template_type(TypePtr type) const
{
	return substitute_template_type_with_engine(*this, type);
}

}  // namespace internal
}  // namespace pa12
