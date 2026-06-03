#include "pa12_internal.h"

#include <stdexcept>

using namespace std;

namespace pa12 {
namespace internal {

bool Parser::is_pointer_arithmetic(const Expr& lhs, const Expr& rhs) const
{
	TypePtr left = lvalue_to_rvalue_type(lhs.type);
	TypePtr right = lvalue_to_rvalue_type(rhs.type);
	return (pa11::strip_cv(left)->kind == pa11::TypeKind::Pointer &&
	        pa11::is_integral_or_bool_type(right)) ||
	       (pa11::strip_cv(right)->kind == pa11::TypeKind::Pointer &&
	        pa11::is_integral_or_bool_type(left));
}

bool Parser::is_pointer_difference(const Expr& lhs, const Expr& rhs) const
{
	return pa11::strip_cv(lvalue_to_rvalue_type(lhs.type))->kind ==
	           pa11::TypeKind::Pointer &&
	       pa11::strip_cv(lvalue_to_rvalue_type(rhs.type))->kind ==
	           pa11::TypeKind::Pointer;
}

TypePtr Parser::pointer_arithmetic_type(ETokenType op,
                                        const Expr& lhs,
                                        const Expr& rhs) const
{
	(void)op;
	TypePtr left = lvalue_to_rvalue_type(lhs.type);
	TypePtr right = lvalue_to_rvalue_type(rhs.type);
	if (pa11::strip_cv(left)->kind == pa11::TypeKind::Pointer)
		return left;
	return right;
}

TypePtr Parser::pointee_type_for_member(TypePtr type) const
{
	TypePtr bare = pa11::strip_cv(expression_object_type(type));
	if (bare->kind != pa11::TypeKind::Pointer)
		throw runtime_error("arrow on non-pointer");
	return bare->base;
}

Expr Parser::make_address_expr(const string& text, Expr inner)
{
	Expr out;
	out.valid = true;
	out.category = ValueCategory::PRValue;
	if (inner.binding != NULL &&
	    inner.binding->owner != NULL &&
	    inner.binding->owner->kind == ScopeKind::Class &&
	    inner.binding->type->kind == pa11::TypeKind::Function)
	{
		TypePtr fn = inner.binding->type;
		TypePtr this_type = fn->parameters.empty() ? TypePtr() : fn->parameters[0];
		TypePtr class_type = this_type.get() == NULL ? TypePtr() :
			pa11::strip_cv(pa11::strip_cv(this_type)->base);
		vector<TypePtr> params;
		for (size_t i = 1; i < fn->parameters.size(); ++i)
			params.push_back(fn->parameters[i]);
		TypePtr member_fn = pa11::make_function(fn->base, params, fn->variadic);
		if (this_type.get() != NULL &&
		    pa11::strip_cv(this_type)->kind == pa11::TypeKind::Pointer)
			member_fn->cv = pa11::strip_cv(this_type)->base->kind ==
				pa11::TypeKind::Cv ? this_type->base->cv : pa11::CV_NONE;
		out.type = pa11::make_member_pointer(class_type, member_fn);
	}
	else if (inner.type->kind == pa11::TypeKind::Function)
		out.type = pa11::make_pointer(inner.type);
	else
		out.type = pa11::make_pointer(expression_object_type(inner.type));
	out.node = Node("unary-expression prvalue " + pa11::describe_type(out.type) +
	                " OP_AMP:" + text);
	add_child(out.node, inner.node);
	out.node.has_op = true;
	out.node.op = OP_AMP;
	out.node.token_text = text;
	annotate_expr_node(out);
	return out;
}

Expr Parser::make_deref_expr(const string& text, Expr inner)
{
	TypePtr object = expression_object_type(inner.type);
	TypePtr bare = pa11::strip_cv(object);
	if (bare->kind == pa11::TypeKind::Pointer)
		object = bare->base;
	else if (bare->kind == pa11::TypeKind::Array)
		object = bare->base;
	else
		throw runtime_error("deref of non-pointer");
	Expr out;
	out.type = object;
	out.category = ValueCategory::LValue;
	out.valid = true;
	out.node = Node("unary-expression lvalue " + pa11::describe_type(object) +
	                " OP_STAR:" + text);
	add_child(out.node, inner.node);
	out.node.has_op = true;
	out.node.op = OP_STAR;
	out.node.token_text = text;
	annotate_expr_node(out);
	return out;
}

}  // namespace internal
}  // namespace pa12
