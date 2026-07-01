#include "pa12_templates_instance_support.h"

using namespace std;

namespace pa12 {
namespace internal {

bool same_member_owner_template_family(TypePtr left, TypePtr right)
{
	TypePtr l = left.get() != NULL ? pa11::strip_cv(left) : TypePtr();
	TypePtr r = right.get() != NULL ? pa11::strip_cv(right) : TypePtr();
	if (l.get() == NULL || r.get() == NULL ||
	    l->kind != pa11::TypeKind::Record ||
	    r->kind != pa11::TypeKind::Record)
		return false;
	string l_primary = l->template_primary_name.empty()
		? l->name : l->template_primary_name;
	string r_primary = r->template_primary_name.empty()
		? r->name : r->template_primary_name;
	return l_primary == r_primary &&
	       l->is_template_specialization == r->is_template_specialization;
}

bool same_nested_constructor_record_family(TypePtr candidate, TypePtr current)
{
	TypePtr c = candidate.get() != NULL ? pa11::strip_cv(candidate) : TypePtr();
	TypePtr self = current.get() != NULL ? pa11::strip_cv(current) : TypePtr();
	if (c.get() == NULL || self.get() == NULL ||
	    c->kind != pa11::TypeKind::Record ||
	    self->kind != pa11::TypeKind::Record)
		return false;
	if (c.get() == self.get())
		return true;
	if (c->scope == NULL || self->scope == NULL ||
	    c->scope->name != self->scope->name ||
	    c->scope->parent == NULL || self->scope->parent == NULL)
		return false;
	TypePtr c_owner = pa11::record_type_for_scope(c->scope->parent);
	TypePtr self_owner = pa11::record_type_for_scope(self->scope->parent);
	return same_member_owner_template_family(c_owner, self_owner);
}

TypePtr rebind_nested_constructor_self_type(TypePtr type, TypePtr current)
{
	if (type.get() == NULL)
		return type;
	if (same_nested_constructor_record_family(type, current))
		return current;
	switch (type->kind)
	{
	case pa11::TypeKind::Cv:
		return pa11::make_cv(
			rebind_nested_constructor_self_type(type->base, current),
			type->cv);
	case pa11::TypeKind::Pointer:
		return pa11::make_pointer(
			rebind_nested_constructor_self_type(type->base, current));
	case pa11::TypeKind::LValueReference:
		return pa11::make_lvalue_reference(
			rebind_nested_constructor_self_type(type->base, current));
	case pa11::TypeKind::RValueReference:
		return pa11::make_rvalue_reference(
			rebind_nested_constructor_self_type(type->base, current));
	case pa11::TypeKind::Array:
	{
		TypePtr rebound = pa11::make_array(
			rebind_nested_constructor_self_type(type->base, current),
			type->unknown_bound,
			type->bound);
		rebound->name = type->name;
		return rebound;
	}
	case pa11::TypeKind::Function:
	{
		vector<TypePtr> params;
		for (size_t i = 0; i < type->parameters.size(); ++i)
			params.push_back(
				rebind_nested_constructor_self_type(type->parameters[i],
				                                    current));
		TypePtr rebound = pa11::make_function(
			rebind_nested_constructor_self_type(type->base, current),
			params,
			type->variadic);
		rebound->cv = type->cv;
		rebound->ref_qualifier = type->ref_qualifier;
		return rebound;
	}
	case pa11::TypeKind::MemberPointer:
		return pa11::make_member_pointer(
			rebind_nested_constructor_self_type(type->member_class, current),
			rebind_nested_constructor_self_type(type->base, current));
	default:
		return type;
	}
}

}  // namespace internal
}  // namespace pa12
