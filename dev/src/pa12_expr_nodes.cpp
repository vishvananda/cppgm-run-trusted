#include "pa12_internal.h"

#include <stdexcept>

using namespace std;

namespace pa12 {
namespace internal {

Expr Parser::make_id_expr(const QualifiedName& name)
{
	if (!name.qualified && name.name == "__builtin_constant_p")
	{
		Expr out;
		out.type = pa11::make_function(pa11::make_fundamental(FT_INT),
		                               vector<TypePtr>(1, pa11::make_fundamental(FT_INT)),
		                               false);
		out.category = ValueCategory::LValue;
		out.valid = true;
		out.node = Node("id-expression lvalue " + pa11::describe_type(out.type) +
		                " __builtin_constant_p");
		return out;
	}
	vector<Binding*> found = resolve_name_set(name, pa11::LOOKUP_VALUE);
	if (found.empty())
		throw runtime_error("name not found");
	Expr out;
	out.valid = true;
	for (size_t i = 0; i < found.size(); ++i)
	{
		if (found[i]->kind == BindingKind::Function)
			out.overloads.push_back(found[i]);
	}
	Binding* binding = found[0];
	if (binding->aliased_binding != NULL &&
	    binding->target_scope != NULL &&
	    binding->kind == BindingKind::Variable)
	{
		Binding* storage = binding->aliased_binding;
		out.binding = binding;
		out.type = binding->type;
		out.category = ValueCategory::LValue;
		out.node = Node("member-expression lvalue " +
		                pa11::describe_type(out.type) + " " + binding->name);
		TypePtr storage_type = expression_object_type(storage->type);
		add_child(out.node,
		          Node("id-expression lvalue " +
		               pa11::describe_type(storage_type) + " " +
		               storage->name));
		return out;
	}
	if (binding->kind == BindingKind::Enumerator)
	{
		out.binding = binding;
		out.type = binding->type;
		out.category = ValueCategory::PRValue;
		out.node = Node("literal prvalue " + pa11::describe_type(out.type) +
		                " " + to_string(binding->constant_value));
		out.null_pointer_constant = binding->constant_value == 0;
		return out;
	}
	if (!out.overloads.empty())
		binding = out.overloads[0];
	out.binding = binding;
	out.type = expression_object_type(binding->type);
	if (binding->kind == BindingKind::Function)
		out.type = binding->type;
	out.category = binding->kind == BindingKind::Enumerator
		? ValueCategory::PRValue : ValueCategory::LValue;
	string spelling = name.qualified ? name.spelling : binding->name;
	out.node = Node("id-expression " + value_category_name(out.category) + " " +
	                pa11::describe_type(out.type) + " " + spelling);
	if (binding->has_constant)
		out.null_pointer_constant = binding->constant_value == 0;
	return out;
}

Expr Parser::make_binary_expr(ETokenType op,
                              const string& text,
                              Expr lhs,
                              Expr rhs)
{
	TypePtr type = usual_arithmetic_type(lhs.type, rhs.type);
	if (op == OP_EQ || op == OP_NE || op == OP_LT || op == OP_GT ||
	    op == OP_LE || op == OP_GE || op == OP_LAND || op == OP_LOR)
		type = pa11::make_fundamental(FT_BOOL);
	else if ((op == OP_PLUS || op == OP_MINUS) && is_pointer_arithmetic(lhs, rhs))
		type = pointer_arithmetic_type(op, lhs, rhs);
	else if (op == OP_MINUS && is_pointer_difference(lhs, rhs))
		type = pa11::make_fundamental(FT_LONG_INT);
	else if (op == OP_COMMA)
		type = rhs.type;
	Expr out;
	out.type = type;
	out.category = ValueCategory::PRValue;
	out.valid = true;
	out.node = Node("binary-expression prvalue " + pa11::describe_type(type) +
	                " " + op_leaf(op, text));
	add_child(out.node, lhs.node);
	add_child(out.node, rhs.node);
	return out;
}

Expr Parser::make_assignment_expr(ETokenType op,
                                  const string& text,
                                  Expr lhs,
                                  Expr rhs)
{
	if (lhs.category != ValueCategory::LValue)
		throw runtime_error("assignment lhs is not lvalue");
	Conversion conv = convert_to(rhs, expression_object_type(lhs.type));
	if (!conv.viable && op == OP_ASS)
		throw runtime_error("invalid assignment conversion");
	if (!conv.viable)
		conv = Conversion(true, 2, rhs);
	Expr out;
	out.type = expression_object_type(lhs.type);
	out.category = ValueCategory::LValue;
	out.valid = true;
	out.node = Node("assignment-expression lvalue " +
	                pa11::describe_type(out.type) + " " + op_leaf(op, text));
	add_child(out.node, lhs.node);
	add_child(out.node, conv.expr.node);
	return out;
}

Expr Parser::make_unary_expr(ETokenType op, const string& text, Expr inner)
{
	Expr out;
	out.valid = true;
	if (op == OP_AMP)
		return make_address_expr(text, inner);
	if (op == OP_STAR)
		return make_deref_expr(text, inner);
	if (op == OP_LNOT)
		out.type = pa11::make_fundamental(FT_BOOL);
	else if (op == OP_COMPL &&
	         pa11::strip_cv(expression_object_type(inner.type))->kind ==
	             pa11::TypeKind::Enum)
		out.type = pa11::make_fundamental(FT_INT);
	else
		out.type = expression_object_type(inner.type);
	out.category = (op == OP_INC || op == OP_DEC) ? ValueCategory::LValue :
		ValueCategory::PRValue;
	out.node = Node("unary-expression " + value_category_name(out.category) +
	                " " + pa11::describe_type(out.type) + " " +
	                op_leaf(op, text));
	add_child(out.node, inner.node);
	return out;
}

Expr Parser::make_postfix_expr(ETokenType op, const string& text, Expr inner)
{
	Expr out;
	out.type = expression_object_type(inner.type);
	out.category = ValueCategory::PRValue;
	out.valid = true;
	out.node = Node("postfix-expression prvalue " +
	                pa11::describe_type(out.type) + " " + op_leaf(op, text));
	add_child(out.node, inner.node);
	return out;
}

Expr Parser::make_subscript_expr(Expr lhs, Expr rhs)
{
	TypePtr base = expression_object_type(lhs.type);
	if (base->kind == pa11::TypeKind::Array)
		base = base->base;
	else if (base->kind == pa11::TypeKind::Pointer)
		base = base->base;
	else
	{
		TypePtr rbase = expression_object_type(rhs.type);
		if (rbase->kind == pa11::TypeKind::Array)
			base = rbase->base;
		else if (rbase->kind == pa11::TypeKind::Pointer)
			base = rbase->base;
		else
			throw runtime_error("invalid subscript operands");
	}
	Expr out;
	out.type = base;
	out.category = ValueCategory::LValue;
	out.valid = true;
	out.node = Node("subscript-expression lvalue " + pa11::describe_type(base));
	if (expression_object_type(rhs.type)->kind == pa11::TypeKind::Array ||
	    expression_object_type(rhs.type)->kind == pa11::TypeKind::Pointer)
	{
		add_child(out.node, rhs.node);
		add_child(out.node, lhs.node);
	}
	else
	{
		add_child(out.node, lhs.node);
		add_child(out.node, rhs.node);
	}
	return out;
}

Expr Parser::make_member_expr(Expr object, const string& name, const string& op)
{
	TypePtr type = expression_object_type(object.type);
	if (op == "->")
		type = pointee_type_for_member(type);
	TypePtr bare = pa11::strip_cv(type);
	if (bare->kind != pa11::TypeKind::Record || bare->scope == NULL)
		throw runtime_error("member access on non-record");
	vector<Binding*> found = lookup_qualified_set(bare->scope, name, pa11::LOOKUP_VALUE);
	if (found.empty() || found[0]->kind == BindingKind::Function)
		throw runtime_error("unsupported member function access");
	TypePtr member_type = found[0]->type;
	if (pa11::type_has_const(type))
		member_type = pa11::make_cv(member_type, pa11::CV_CONST);
	Expr out;
	out.type = member_type;
	out.category = ValueCategory::LValue;
	out.valid = true;
	out.node = Node("member-expression lvalue " +
	                pa11::describe_type(member_type) + " OP_DOT:" + name);
	add_child(out.node, object.node);
	return out;
}

Expr Parser::make_cast_expr(TypePtr target, const string& op_text, Expr inner)
{
	Expr out;
	out.type = target;
	out.category = target->kind == pa11::TypeKind::RValueReference
		? ValueCategory::XValue : ValueCategory::PRValue;
	out.valid = true;
	if (target->kind == pa11::TypeKind::RValueReference &&
	    inner.binding != NULL)
	{
		out.node = Node("id-expression xvalue " + pa11::describe_type(target) +
		                " " + inner.binding->name);
		return out;
	}
	string line = "cast-expression prvalue " + pa11::describe_type(target);
	if (!op_text.empty())
		line += " " + op_text;
	out.node = Node(line);
	add_child(out.node, inner.node);
	return out;
}

Expr Parser::make_sizeof_expr(uint64_t value)
{
	(void)value;
	Expr out;
	out.type = pa11::make_fundamental(FT_UNSIGNED_LONG_INT);
	out.category = ValueCategory::PRValue;
	out.valid = true;
	out.node = Node("sizeof-expression prvalue unsigned long int");
	return out;
}

}  // namespace internal
}  // namespace pa12
