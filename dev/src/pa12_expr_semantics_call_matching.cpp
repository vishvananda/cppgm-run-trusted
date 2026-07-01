#include "pa12_expr_semantics_support.h"
#include "pa12_templates_function_support.h"
#include "pa12_templates_instance_support.h"
#include "pa12_types_support.h"

#include <algorithm>

using namespace std;

namespace pa12 {
namespace internal {

bool same_parameter_family_ignoring_pointer_cv(TypePtr left, TypePtr right)
{
	if (same_template_signature_type(left, right))
		return true;
	TypePtr l = pa11::strip_cv(left);
	TypePtr r = pa11::strip_cv(right);
	if (l->kind == pa11::TypeKind::Pointer &&
	    r->kind == pa11::TypeKind::Pointer)
		return same_template_signature_type(pa11::strip_cv(l->base),
		                                    pa11::strip_cv(r->base));
	return false;
}

string call_unqualified_template_primary(TypePtr type)
{
	TypePtr bare = type.get() != NULL ? pa11::strip_cv(type) : TypePtr();
	if (bare.get() == NULL)
		return "";
	string primary = bare->template_primary_name.empty()
		? bare->name : bare->template_primary_name;
	size_t pos = primary.rfind("::");
	return pos == string::npos ? primary : primary.substr(pos + 2);
}

bool unresolved_enable_if_typename(TypePtr type)
{
	TypePtr bare = type.get() != NULL ? pa11::strip_cv(type) : TypePtr();
	if (bare.get() == NULL || !bare->is_dependent_typename)
		return false;
	string primary = call_unqualified_template_primary(bare);
	return primary == "enable_if" ||
	       primary == "enable_if_t" ||
	       primary == "__enable_if_t";
}

bool same_overload_parameter_signature(TypePtr left, TypePtr right)
{
	if (left.get() == NULL || right.get() == NULL ||
	    left->kind != pa11::TypeKind::Function ||
	    right->kind != pa11::TypeKind::Function)
		return false;
	if (left->cv != right->cv ||
	    left->variadic != right->variadic ||
	    left->ref_qualifier != right->ref_qualifier ||
	    left->parameters.size() != right->parameters.size())
		return false;
	for (size_t i = 0; i < left->parameters.size(); ++i)
		if (!pa11::same_type(left->parameters[i], right->parameters[i]) &&
		    !same_template_signature_type(left->parameters[i],
		                                  right->parameters[i]))
			return false;
	return true;
}

bool function_template_candidate_binding(
	Binding* binding,
	const map<Binding*, TemplateDeclaration*>& placeholders,
	const map<Binding*, vector<TemplateArgument> >& specializations)
{
	if (binding == NULL)
		return false;
	if (placeholders.find(binding) != placeholders.end() ||
	    specializations.find(binding) != specializations.end() ||
	    !binding->function_specialization_symbol.empty())
		return true;
	Binding* alias = binding->aliased_binding;
	return alias != NULL &&
	       (placeholders.find(alias) != placeholders.end() ||
	        specializations.find(alias) != specializations.end() ||
	        !alias->function_specialization_symbol.empty());
}

bool same_function_specialization_symbol(Binding* left, Binding* right)
{
	return left != NULL &&
	       right != NULL &&
	       !left->function_specialization_symbol.empty() &&
	       left->function_specialization_symbol ==
		       right->function_specialization_symbol;
}

bool has_function_template_origin(
	Binding* binding,
	const map<Binding*, TemplateDeclaration*>& placeholders)
{
	return function_template_origin(placeholders, binding) != NULL;
}

bool distinct_function_template_candidate_origins(
	const map<Binding*, TemplateDeclaration*>& placeholders,
	Binding* left,
	Binding* right)
{
	TemplateDeclaration* left_origin =
		function_template_origin(placeholders, left);
	TemplateDeclaration* right_origin =
		function_template_origin(placeholders, right);
	return left_origin != NULL &&
	       right_origin != NULL &&
	       left_origin != right_origin &&
	       !same_function_template_declaration_family(left_origin,
	                                                  right_origin);
}

void append_normalized_object_specialization_arguments(
	vector<pa11::TemplateInstanceArgument>& out,
	const vector<pa11::TemplateInstanceArgument>& arguments)
{
	for (size_t i = 0; i < arguments.size(); ++i)
	{
		if (arguments[i].kind == pa11::TemplateInstanceArgumentKind::Pack)
		{
			append_normalized_object_specialization_arguments(out,
			                                                 arguments[i].pack);
			continue;
		}
		out.push_back(arguments[i]);
	}
}

bool same_object_specialization_type(TypePtr left, TypePtr right);
bool same_object_specialization_arguments(
	const vector<pa11::TemplateInstanceArgument>& left,
	const vector<pa11::TemplateInstanceArgument>& right);

bool same_object_specialization_argument(
	const pa11::TemplateInstanceArgument& left,
	const pa11::TemplateInstanceArgument& right)
{
	if (left.kind != right.kind)
		return false;
	if (left.kind == pa11::TemplateInstanceArgumentKind::Type)
		return same_object_specialization_type(left.type, right.type);
	if (left.kind == pa11::TemplateInstanceArgumentKind::Value)
		return left.dependent == right.dependent &&
		       left.value_negated == right.value_negated &&
		       left.value == right.value &&
		       left.value_name == right.value_name &&
		       left.value_owner_template_name ==
			       right.value_owner_template_name &&
		       left.value_member_name == right.value_member_name &&
		       same_object_specialization_type(left.type, right.type) &&
		       same_object_specialization_arguments(
			       left.value_owner_template_arguments,
			       right.value_owner_template_arguments);
	if (left.kind == pa11::TemplateInstanceArgumentKind::Template)
		return left.template_name == right.template_name &&
		       left.dependent == right.dependent;
	if (left.pack.size() != right.pack.size())
		return false;
	for (size_t i = 0; i < left.pack.size(); ++i)
		if (!same_object_specialization_argument(left.pack[i],
		                                         right.pack[i]))
			return false;
	return true;
}

bool same_object_specialization_arguments(
	const vector<pa11::TemplateInstanceArgument>& left,
	const vector<pa11::TemplateInstanceArgument>& right)
{
	vector<pa11::TemplateInstanceArgument> flat_left;
	vector<pa11::TemplateInstanceArgument> flat_right;
	append_normalized_object_specialization_arguments(flat_left, left);
	append_normalized_object_specialization_arguments(flat_right, right);
	if (flat_left.size() != flat_right.size())
		return false;
	for (size_t i = 0; i < flat_left.size(); ++i)
		if (!same_object_specialization_argument(flat_left[i],
		                                         flat_right[i]))
			return false;
	return true;
}

bool same_object_specialization_type(TypePtr left, TypePtr right)
{
	if (left.get() == NULL || right.get() == NULL)
		return left.get() == right.get();
	if (pa11::same_type(left, right))
		return true;
	TypePtr l = pa11::strip_cv(left);
	TypePtr r = pa11::strip_cv(right);
	return l->kind == pa11::TypeKind::Record &&
	       r->kind == pa11::TypeKind::Record &&
	       l->is_template_specialization &&
	       r->is_template_specialization &&
	       !l->template_primary_name.empty() &&
	       l->template_primary_name == r->template_primary_name &&
	       same_object_specialization_arguments(l->template_arguments,
	                                            r->template_arguments);
}

TypePtr reference_binding_target(TypePtr type)
{
	TypePtr bare = type.get() != NULL ? pa11::strip_cv(type) : TypePtr();
	if (bare.get() == NULL ||
	    (bare->kind != pa11::TypeKind::LValueReference &&
	     bare->kind != pa11::TypeKind::RValueReference))
		return TypePtr();
	return pa11::strip_cv(bare->base);
}

bool same_reference_binding_target(TypePtr left, TypePtr right)
{
	TypePtr l = reference_binding_target(left);
	TypePtr r = reference_binding_target(right);
	return l.get() != NULL && r.get() != NULL &&
	       same_object_specialization_type(l, r);
}

int reference_binding_tie_break(Binding* candidate,
                                const vector<Expr>& candidate_args,
                                Binding* current,
                                const vector<Expr>& current_args)
{
	if (candidate == NULL || current == NULL ||
	    candidate->type.get() == NULL || current->type.get() == NULL ||
	    candidate->type->kind != pa11::TypeKind::Function ||
	    current->type->kind != pa11::TypeKind::Function ||
	    candidate->type->parameters.size() !=
		    current->type->parameters.size())
		return 0;
	int score = 0;
	size_t first =
		candidate->owner != NULL &&
		candidate->owner->kind == ScopeKind::Class &&
		!candidate->is_static_member ? 1 : 0;
	for (size_t i = first; i < candidate->type->parameters.size(); ++i)
	{
		if (i >= candidate_args.size() || i >= current_args.size())
			continue;
		TypePtr cparam = pa11::strip_cv(candidate->type->parameters[i]);
		TypePtr bparam = pa11::strip_cv(current->type->parameters[i]);
			if (!same_reference_binding_target(cparam, bparam))
				continue;
			bool candidate_rvalue =
				cparam->kind == pa11::TypeKind::RValueReference;
			bool current_rvalue =
				bparam->kind == pa11::TypeKind::RValueReference;
			if (candidate_rvalue == current_rvalue)
				continue;
			score += candidate_rvalue ? 1 : -1;
		}
	if (score > 0)
		return 1;
	if (score < 0)
		return -1;
	return 0;
}

bool call_object_specialization_type_equivalent(TypePtr left, TypePtr right)
{
	return same_object_specialization_type(left, right);
}

}  // namespace internal
}  // namespace pa12
