#include "pa12_internal.h"

using namespace std;

namespace pa12 {
namespace internal {
namespace {

bool aggregate_blocking_constructor(Binding* binding)
{
	if (binding->kind != BindingKind::Function ||
	    binding->type->kind != pa11::TypeKind::Function)
		return false;
	if (binding->is_generated_default_constructor ||
	    binding->is_generated_aggregate_constructor ||
	    binding->is_generated_copy_move_constructor)
		return false;
	if (binding->is_defaulted && binding->type->parameters.size() == 1)
		return false;
	return true;
}

}  // namespace

bool record_has_aggregate_blocking_constructor(TypePtr record)
{
	TypePtr bare = pa11::strip_cv(record);
	if (bare->kind != pa11::TypeKind::Record || bare->scope == NULL)
		return false;
	map<string, vector<Binding*> >::const_iterator found =
		bare->scope->members.find(bare->scope->name);
	if (found == bare->scope->members.end())
		return false;
	for (size_t i = 0; i < found->second.size(); ++i)
		if (aggregate_blocking_constructor(found->second[i]))
			return true;
	return false;
}

bool string_literal_initializes_array(TypePtr type,
                                      const Expr& init,
                                      uint64_t* elements)
{
	TypePtr bare = pa11::strip_cv(type);
	if (bare->kind != pa11::TypeKind::Array ||
	    init.node.token_text.empty() ||
	    init.node.token_text[init.node.token_text.size() - 1] != '"')
		return false;
	TypePtr elem = pa11::strip_cv(bare->base);
	if (elem->kind != pa11::TypeKind::Fundamental)
		return false;
	StringLiteralInfo info;
	if (!AnalyzeStringLiteral(init.node.token_text, info) ||
	    !info.ud_suffix.empty() ||
	    elem->fundamental != info.type)
		return false;
	if (!bare->unknown_bound && bare->bound < info.elements)
		return false;
	if (elements != NULL)
		*elements = info.elements;
	return true;
}

}  // namespace internal
}  // namespace pa12

