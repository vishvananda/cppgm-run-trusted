#include "pa12_internal.h"

#include <algorithm>
#include <stdexcept>

using namespace std;

namespace pa12 {
namespace internal {
namespace {

bool is_function_pointer(TypePtr type)
{
	TypePtr bare = pa11::strip_cv(type);
	return bare->kind == pa11::TypeKind::Pointer &&
	       bare->base->kind == pa11::TypeKind::Function;
}

bool is_function_reference(TypePtr type)
{
	return (type->kind == pa11::TypeKind::LValueReference ||
	        type->kind == pa11::TypeKind::RValueReference) &&
	       pa11::strip_cv(type->base)->kind == pa11::TypeKind::Function;
}

bool is_member_function_pointer(TypePtr type)
{
	TypePtr bare = pa11::strip_cv(type);
	return bare->kind == pa11::TypeKind::MemberPointer &&
	       bare->base.get() != NULL &&
	       bare->base->kind == pa11::TypeKind::Function;
}

bool template_parameter_lists_match_local(
	const vector<TemplateParameterInfo>& left,
	const vector<TemplateParameterInfo>& right)
{
	if (left.size() != right.size())
		return false;
	for (size_t i = 0; i < left.size(); ++i)
	{
		if (left[i].kind != right[i].kind ||
		    left[i].is_pack != right[i].is_pack ||
		    left[i].template_parameters.size() !=
			    right[i].template_parameters.size())
			return false;
		for (size_t j = 0; j < left[i].template_parameters.size(); ++j)
			if (left[i].template_parameters[j].kind !=
				    right[i].template_parameters[j].kind ||
			    left[i].template_parameters[j].is_pack !=
				    right[i].template_parameters[j].is_pack)
				return false;
	}
	return true;
}

bool same_function_template_signature_type(TypePtr left, TypePtr right)
{
	if (left.get() == NULL || right.get() == NULL)
		return left.get() == right.get();
	if (left->kind == pa11::TypeKind::TemplateParameter &&
	    right->kind == pa11::TypeKind::TemplateParameter)
		return true;
	if (pa11::same_type(left, right))
		return true;
	if (left->kind != right->kind)
		return false;
	switch (left->kind)
	{
	case pa11::TypeKind::Cv:
		return left->cv == right->cv &&
		       same_function_template_signature_type(left->base,
		                                             right->base);
	case pa11::TypeKind::Pointer:
	case pa11::TypeKind::LValueReference:
	case pa11::TypeKind::RValueReference:
		return same_function_template_signature_type(left->base,
		                                             right->base);
	case pa11::TypeKind::Array:
		return left->unknown_bound == right->unknown_bound &&
		       left->bound == right->bound &&
		       same_function_template_signature_type(left->base,
		                                             right->base);
	case pa11::TypeKind::Function:
		if (left->cv != right->cv ||
		    left->variadic != right->variadic ||
		    left->parameters.size() != right->parameters.size() ||
		    !same_function_template_signature_type(left->base,
		                                           right->base))
			return false;
		for (size_t i = 0; i < left->parameters.size(); ++i)
			if (!same_function_template_signature_type(
				    left->parameters[i],
				    right->parameters[i]))
				return false;
		return true;
	case pa11::TypeKind::MemberPointer:
		return same_function_template_signature_type(left->member_class,
		                                             right->member_class) &&
		       same_function_template_signature_type(left->base,
		                                             right->base);
	default:
		return false;
	}
}

TypePtr member_function_pointer_type(Binding* binding)
{
	if (binding == NULL ||
	    binding->owner == NULL ||
	    binding->owner->kind != ScopeKind::Class ||
	    binding->type.get() == NULL ||
	    binding->type->kind != pa11::TypeKind::Function ||
	    binding->type->parameters.empty())
		return TypePtr();
	TypePtr this_type = binding->type->parameters[0];
	TypePtr class_type = this_type.get() == NULL ? TypePtr() :
		pa11::strip_cv(pa11::strip_cv(this_type)->base);
	vector<TypePtr> params;
	for (size_t i = 1; i < binding->type->parameters.size(); ++i)
		params.push_back(binding->type->parameters[i]);
	TypePtr member_fn =
		pa11::make_function(binding->type->base,
		                    params,
		                    binding->type->variadic);
	if (this_type.get() != NULL &&
	    pa11::strip_cv(this_type)->kind == pa11::TypeKind::Pointer)
		member_fn->cv = pa11::strip_cv(this_type)->base->kind ==
			pa11::TypeKind::Cv ? this_type->base->cv : pa11::CV_NONE;
	return pa11::make_member_pointer(class_type, member_fn);
}

bool same_template_instance_argument(
	const pa11::TemplateInstanceArgument& left,
	const pa11::TemplateInstanceArgument& right)
{
	if (left.kind != right.kind ||
	    left.value != right.value ||
	    left.value_name != right.value_name ||
	    left.template_name != right.template_name ||
	    left.dependent != right.dependent ||
	    left.type.get() != right.type.get() ||
	    left.pack.size() != right.pack.size())
		return false;
	for (size_t i = 0; i < left.pack.size(); ++i)
		if (!same_template_instance_argument(left.pack[i], right.pack[i]))
			return false;
	return true;
}

bool same_template_specialization_record(TypePtr left, TypePtr right)
{
	TypePtr l = pa11::strip_cv(left);
	TypePtr r = pa11::strip_cv(right);
	if (l->kind != pa11::TypeKind::Record ||
	    r->kind != pa11::TypeKind::Record ||
	    !l->is_template_specialization ||
	    !r->is_template_specialization)
		return false;
	if (l->name == r->name)
		return true;
	if (l->template_primary_name.empty() ||
	    l->template_primary_name != r->template_primary_name ||
	    l->template_arguments.size() != r->template_arguments.size())
		return false;
	for (size_t i = 0; i < l->template_arguments.size(); ++i)
		if (!same_template_instance_argument(l->template_arguments[i],
		                                     r->template_arguments[i]))
			return false;
	return true;
}

}  // namespace

Expr Parser::select_overload_expr(const Expr& expr, TypePtr target)
{ if (expr.overloads.empty()) return expr; TypePtr target_object = target; if (target_object->kind == pa11::TypeKind::LValueReference || target_object->kind == pa11::TypeKind::RValueReference)
target_object = target_object->base; TypePtr wanted = target_object; bool target_member_function_pointer = false; if (is_function_pointer(target_object)) wanted = pa11::strip_cv(target_object)->base;
else if (is_function_reference(target)) wanted = pa11::strip_cv(target->base); else if (is_member_function_pointer(target_object)) target_member_function_pointer = true; else
throw runtime_error("overloaded function id needs target"); Binding* found = NULL; vector<Binding*> considered; for (size_t i = 0; i < expr.overloads.size(); ++i) { Binding* candidate = expr.overloads[i];
map<Binding*, TemplateDeclaration*>::iterator template_it = function_template_placeholders_.find(candidate); Binding* placeholder = candidate->aliased_binding != NULL ? candidate->aliased_binding : candidate;
if (template_it != function_template_placeholders_.end() && template_it->second->placeholder == placeholder) { TemplateDeclaration* declaration = template_it->second; if (!declaration->has_definition) {
map<Scope*, map<string, vector<TemplateDeclaration*> > >::iterator sit = function_templates_.find(declaration->owner); if (sit != function_templates_.end()) { map<string, vector<TemplateDeclaration*> >::iterator it =
sit->second.find(declaration->name); if (it != sit->second.end()) for (size_t j = 0; j < it->second.size(); ++j) { TemplateDeclaration* candidate = it->second[j]; if (candidate == declaration ||
!candidate->has_definition || candidate->generic_function_type.get() == NULL || !same_function_template_signature_type( candidate->generic_function_type, declaration->generic_function_type) ||
!template_parameter_lists_match_local( candidate->parameters, declaration->parameters)) continue; declaration = candidate; break; } } } vector<TemplateArgument> explicit_args;
map<Binding*, vector<TemplateArgument> >::const_iterator eit = expr.explicit_template_arguments.find(candidate); if (eit != expr.explicit_template_arguments.end()) explicit_args = eit->second;
vector<TemplateArgument> deduced; if (!deduce_function_template_target_type(declaration, wanted, explicit_args, deduced)) continue; candidate = instantiate_function_template(declaration, deduced); }
Binding* duplicate = NULL; for (size_t j = 0; j < considered.size(); ++j) if (pa11::same_type(considered[j]->type, candidate->type) && considered[j]->is_static_member == candidate->is_static_member) {
duplicate = considered[j]; break; } if (duplicate != NULL) { if (!(candidate->is_inline_definition && !duplicate->is_inline_definition)) continue; vector<Binding*>::iterator pos =
find(considered.begin(), considered.end(), duplicate); if (pos != considered.end()) *pos = candidate; if (found == duplicate) found = NULL; } else considered.push_back(candidate);
TypePtr candidate_member_pointer = target_member_function_pointer ? member_function_pointer_type(candidate) : TypePtr(); bool matches = target_member_function_pointer ? (candidate_member_pointer.get() != NULL &&
pa11::same_type(candidate_member_pointer, target_object)) : pa11::same_type(candidate->type, wanted); if (matches) { if (found != NULL) throw runtime_error("ambiguous overloaded function id"); found = candidate; } }
if (found == NULL) throw runtime_error("no overloaded function id target"); if (unevaluated_expression_depth_ == 0) { parse_pending_function_body(found); parse_pending_member_body(found); } Expr out = expr;
out.overloads.clear(); out.binding = found; bool address_expr = expr.node.line.compare(0, 16, "unary-expression") == 0 && expr.node.has_op && expr.node.op == OP_AMP && !expr.node.children.empty(); Expr selected_id;
selected_id.valid = true; selected_id.binding = found; selected_id.type = found->type; selected_id.category = ValueCategory::LValue; selected_id.node = Node("id-expression lvalue " +
pa11::describe_type(found->type) + " " + qualified_decl_name(found)); selected_id.node.binding = found; annotate_expr_node(selected_id); if (address_expr) { out.type = target_member_function_pointer
? member_function_pointer_type(found) : pa11::make_pointer(found->type); out.category = ValueCategory::PRValue; out.node = Node("unary-expression prvalue " + pa11::describe_type(out.type) + " OP_AMP:&");
add_child(out.node, selected_id.node); out.node.has_op = true; out.node.op = OP_AMP; out.node.token_text = "&"; } else { out.type = found->type; out.category = ValueCategory::LValue; out.node = selected_id.node; }
annotate_expr_node(out); return out; }

Expr Parser::make_dependent_call_expr(const Expr& callee,
                                      const vector<Expr>& args)
{
	for (map<Binding*, vector<TemplateArgument> >::const_iterator it =
		     callee.explicit_template_arguments.begin();
	     it != callee.explicit_template_arguments.end();
	     ++it)
	{
		Binding* binding = it->first;
		Binding* placeholder =
			binding != NULL && binding->aliased_binding != NULL
			? binding->aliased_binding : binding;
		if (function_template_placeholders_.find(placeholder) !=
		    function_template_placeholders_.end())
			placeholder->reserve_primary_function_symbol = true;
	}
	Expr out;
	TypePtr result;
	TypePtr callee_type = callee.type.get() != NULL
		? pa11::strip_cv(expression_object_type(callee.type)) : TypePtr();
	if (callee_type.get() != NULL &&
	    callee_type->kind == pa11::TypeKind::Function)
		result = callee_type->base;
	if (result.get() != NULL && !callee.explicit_template_arguments.empty())
	{
		map<Binding*, vector<TemplateArgument> >::const_iterator explicit_it =
			callee.explicit_template_arguments.begin();
		Binding* binding = explicit_it->first;
		Binding* placeholder =
			binding != NULL && binding->aliased_binding != NULL
			? binding->aliased_binding : binding;
		map<Binding*, TemplateDeclaration*>::const_iterator decl =
			function_template_placeholders_.find(placeholder);
		if (decl == function_template_placeholders_.end() && binding != NULL)
			decl = function_template_placeholders_.find(binding);
		if (decl != function_template_placeholders_.end())
		{
			const vector<TemplateArgument>& explicit_args =
				explicit_it->second;
			for (size_t i = 0; i < explicit_args.size() &&
			     i < decl->second->parameters.size(); ++i)
			{
				const TemplateParameterInfo& parameter =
					decl->second->parameters[i];
				if (parameter.kind == TemplateParameterKind::Type &&
				    !parameter.name.empty() &&
				    explicit_args[i].kind == TemplateArgumentKind::Type)
					result = substitute_template_type_parameter(
						result,
						parameter.name,
						explicit_args[i].type);
			}
		}
	}
	out.type = result.get() != NULL
		? result
		: replaying_dependent_decltype_
		? pa11::make_fundamental(FT_INT)
		: pa11::make_dependent_typename_type("__dependent_call",
		                                     false,
		                                     false,
		                                     false);
	out.category = call_category(out.type);
	out.node = Node("call-expression " + value_category_name(out.category) +
	                " " + pa11::describe_type(out.type));
	add_child(out.node, callee.node);
	for (size_t i = 0; i < args.size(); ++i)
		add_child(out.node, args[i].node);
	out.valid = true;
	annotate_expr_node(out);
	return out;
}

void Parser::ensure_copy_move_constructor_for_single_arg(
	TypePtr record,
	const vector<Expr>& args)
{
	if (args.size() != 1)
		return;
	TypePtr arg_record = pa11::strip_cv(expression_object_type(args[0].type));
	if (arg_record->kind != pa11::TypeKind::Record ||
	    (!pa11::same_type(arg_record, record) &&
	     !same_template_specialization_record(arg_record, record)))
		return;
	if (args[0].category == ValueCategory::XValue)
		ensure_copy_move_constructor(record, true);
	ensure_copy_move_constructor(record, false);
}

void Parser::add_variadic_argument_ranks(Binding* fn,
                                         size_t arg_count,
                                         vector<int>& ranks) const
{
	if (fn == NULL ||
	    fn->type->kind != pa11::TypeKind::Function ||
	    !fn->type->variadic ||
	    arg_count <= fn->type->parameters.size())
		return;
	for (size_t i = fn->type->parameters.size(); i < arg_count; ++i)
		ranks.push_back(100);
}

void Parser::prepare_member_call(Expr& callee, vector<Expr>& args)
{
	bool needs_this = false;
	Expr object;
	object.node = callee.node.children[0];
	object.type = object.node.type;
	object.category = object.node.category;
	object.binding = object.node.binding;
	object.valid = true;
	vector<Binding*> viable_overloads;
	vector<Binding*> nonstatic_overloads;
	for (size_t i = 0; i < callee.overloads.size(); ++i)
	{
		Binding* candidate = callee.overloads[i];
		if (candidate->owner != NULL &&
		    candidate->owner->kind == ScopeKind::Class &&
		    !candidate->is_static_member)
		{
			if (candidate->ref_qualifier == 1 &&
			    object.category != ValueCategory::LValue)
			{
				TypePtr this_param =
					candidate->type->parameters.empty()
					? TypePtr() : candidate->type->parameters[0];
				TypePtr this_object =
					this_param.get() != NULL &&
					pa11::strip_cv(this_param)->kind ==
					pa11::TypeKind::Pointer
					? pa11::strip_cv(this_param)->base : TypePtr();
				if (this_object.get() == NULL ||
				    !pa11::type_has_const(this_object))
					continue;
			}
			if (candidate->ref_qualifier == 2 &&
			    object.category == ValueCategory::LValue)
				continue;
			needs_this = true;
			nonstatic_overloads.push_back(candidate);
		}
		viable_overloads.push_back(candidate);
	}
	if (!nonstatic_overloads.empty())
		viable_overloads = nonstatic_overloads;
	if (viable_overloads.empty())
		throw runtime_error("cannot resolve call overload");
	callee.overloads = viable_overloads;
	if (needs_this)
	{
		Expr this_arg = callee.node.has_op && callee.node.op == OP_ARROW
			? object : make_address_expr("&", object);
		args.insert(args.begin(), this_arg);
	}
}

bool Parser::ranks_better(const vector<int>& lhs, const vector<int>& rhs) const
{
	if (rhs.empty())
		return false;
	if (lhs.size() != rhs.size())
		return false;
	bool any = false;
	for (size_t i = 0; i < lhs.size(); ++i)
	{
		if (lhs[i] > rhs[i])
			return false;
		if (lhs[i] < rhs[i])
			any = true;
	}
	return any;
}

}  // namespace internal
}  // namespace pa12
