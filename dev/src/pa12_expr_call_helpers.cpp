#include "pa12_internal.h"

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

}  // namespace

Expr Parser::select_overload_expr(const Expr& expr, TypePtr target)
{
	if (expr.overloads.empty())
		return expr;
	TypePtr wanted = target;
	bool target_member_function_pointer = false;
	if (is_function_pointer(target))
		wanted = pa11::strip_cv(target)->base;
	else if (is_function_reference(target))
		wanted = pa11::strip_cv(target->base);
	else if (is_member_function_pointer(target))
		target_member_function_pointer = true;
	else
		throw runtime_error("overloaded function id needs target");

	Binding* found = NULL;
	vector<Binding*> considered;
	for (size_t i = 0; i < expr.overloads.size(); ++i)
	{
		Binding* candidate = expr.overloads[i];
		map<Binding*, TemplateDeclaration*>::iterator template_it =
			function_template_placeholders_.find(candidate);
		Binding* placeholder = candidate->aliased_binding != NULL
			? candidate->aliased_binding : candidate;
		if (template_it != function_template_placeholders_.end() &&
		    template_it->second->placeholder == placeholder)
		{
			vector<TemplateArgument> explicit_args;
			map<Binding*, vector<TemplateArgument> >::const_iterator eit =
				expr.explicit_template_arguments.find(candidate);
			if (eit != expr.explicit_template_arguments.end())
				explicit_args = eit->second;
			vector<TemplateArgument> deduced;
			if (!deduce_function_template_target_type(template_it->second,
			                                          wanted,
			                                          explicit_args,
			                                          deduced))
				continue;
			candidate = instantiate_function_template(template_it->second,
			                                          deduced);
		}
		bool duplicate = false;
		for (size_t j = 0; j < considered.size(); ++j)
			if (pa11::same_type(considered[j]->type, candidate->type) &&
			    considered[j]->is_static_member == candidate->is_static_member)
				duplicate = true;
		if (duplicate)
			continue;
		considered.push_back(candidate);
		TypePtr candidate_member_pointer = target_member_function_pointer
			? member_function_pointer_type(candidate) : TypePtr();
		bool matches = target_member_function_pointer
			? (candidate_member_pointer.get() != NULL &&
			   pa11::same_type(candidate_member_pointer, target))
			: pa11::same_type(candidate->type, wanted);
		if (matches)
		{
			if (found != NULL)
				throw runtime_error("ambiguous overloaded function id");
			found = candidate;
		}
	}
	if (found == NULL)
		throw runtime_error("no overloaded function id target");

	Expr out = expr;
	out.overloads.clear();
	out.binding = found;
	bool address_expr =
		expr.node.line.compare(0, 16, "unary-expression") == 0 &&
		expr.node.has_op &&
		expr.node.op == OP_AMP &&
		!expr.node.children.empty();
	Expr selected_id;
	selected_id.valid = true;
	selected_id.binding = found;
	selected_id.type = found->type;
	selected_id.category = ValueCategory::LValue;
	selected_id.node = Node("id-expression lvalue " +
	                        pa11::describe_type(found->type) + " " +
	                        qualified_decl_name(found));
	selected_id.node.binding = found;
	annotate_expr_node(selected_id);
	if (address_expr)
	{
		out.type = target_member_function_pointer
			? member_function_pointer_type(found)
			: pa11::make_pointer(found->type);
		out.category = ValueCategory::PRValue;
		out.node = Node("unary-expression prvalue " +
		                pa11::describe_type(out.type) + " OP_AMP:&");
		add_child(out.node, selected_id.node);
		out.node.has_op = true;
		out.node.op = OP_AMP;
		out.node.token_text = "&";
	}
	else
	{
		out.type = found->type;
		out.category = ValueCategory::LValue;
		out.node = selected_id.node;
	}
	annotate_expr_node(out);
	return out;
}

Expr Parser::make_dependent_call_expr(const Expr& callee,
                                      const vector<Expr>& args)
{
	Expr out;
	out.type = pa11::make_dependent_typename_type("__dependent_call",
	                                             false,
	                                             false,
	                                             false);
	out.category = ValueCategory::PRValue;
	out.node = Node("call-expression prvalue " + pa11::describe_type(out.type));
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
	    !pa11::same_type(arg_record, record))
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
