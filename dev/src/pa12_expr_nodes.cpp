#include "pa12_internal.h"

#include <stdexcept>

using namespace std;

namespace pa12 {
namespace internal {
namespace {

bool type_is_floating(TypePtr type)
{
	TypePtr bare = pa11::strip_cv(type);
	return bare->kind == pa11::TypeKind::Fundamental &&
	       (bare->fundamental == FT_FLOAT ||
	        bare->fundamental == FT_DOUBLE ||
	        bare->fundamental == FT_LONG_DOUBLE);
}

bool type_is_arithmetic(TypePtr type)
{
	return pa11::is_integral_or_bool_type(type) || type_is_floating(type);
}

bool type_is_pointer(TypePtr type)
{
	return pa11::strip_cv(type)->kind == pa11::TypeKind::Pointer;
}

bool top_level_const(TypePtr type)
{
	return type->kind == pa11::TypeKind::Cv &&
	       (type->cv & pa11::CV_CONST) != 0;
}

bool constant_binary_value(ETokenType op,
                           uint64_t lhs,
                           uint64_t rhs,
                           uint64_t& out)
{
	switch (op)
	{
	case OP_PLUS: out = lhs + rhs; return true;
	case OP_MINUS: out = lhs - rhs; return true;
	case OP_STAR: out = lhs * rhs; return true;
	case OP_DIV:
		if (rhs == 0) return false;
		out = lhs / rhs;
		return true;
	case OP_MOD:
		if (rhs == 0) return false;
		out = lhs % rhs;
		return true;
	case OP_XOR: out = lhs ^ rhs; return true;
	case OP_AMP: out = lhs & rhs; return true;
	case OP_BOR: out = lhs | rhs; return true;
	case OP_LSHIFT:
		if (rhs >= 64) return false;
		out = lhs << rhs;
		return true;
	case OP_RSHIFT:
		if (rhs >= 64) return false;
		out = lhs >> rhs;
		return true;
	case OP_EQ: out = lhs == rhs ? 1 : 0; return true;
	case OP_NE: out = lhs != rhs ? 1 : 0; return true;
	case OP_LT: out = lhs < rhs ? 1 : 0; return true;
	case OP_GT: out = lhs > rhs ? 1 : 0; return true;
	case OP_LE: out = lhs <= rhs ? 1 : 0; return true;
	case OP_GE: out = lhs >= rhs ? 1 : 0; return true;
	case OP_LAND: out = (lhs != 0 && rhs != 0) ? 1 : 0; return true;
	case OP_LOR: out = (lhs != 0 || rhs != 0) ? 1 : 0; return true;
	case OP_COMMA: out = rhs; return true;
	default:
		return false;
	}
}

bool compound_assignment_rhs_viable(ETokenType op, TypePtr lhs, TypePtr rhs)
{
	TypePtr left = pa11::strip_cv(lhs);
	TypePtr right = pa11::strip_cv(rhs);
	if (op == OP_PLUSASS || op == OP_MINUSASS)
	{
		if (left->kind == pa11::TypeKind::Pointer)
			return pa11::is_integral_or_bool_type(right);
		return type_is_arithmetic(left) && type_is_arithmetic(right);
	}
	if (op == OP_STARASS || op == OP_DIVASS)
		return type_is_arithmetic(left) && type_is_arithmetic(right);
	if (op == OP_MODASS || op == OP_XORASS || op == OP_BANDASS ||
	    op == OP_BORASS || op == OP_LSHIFTASS || op == OP_RSHIFTASS)
		return pa11::is_integral_or_bool_type(left) &&
		       pa11::is_integral_or_bool_type(right);
	return false;
}

}  // namespace

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
		out.builtin_constant_p = true;
		out.node = Node("id-expression lvalue " + pa11::describe_type(out.type) +
		                " __builtin_constant_p");
		annotate_expr_node(out);
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
		out.node.binding = binding;
		annotate_expr_node(out);
		return out;
	}
	if (binding->kind == BindingKind::Enumerator)
	{
		out.binding = binding;
		out.type = binding->type;
		out.category = ValueCategory::PRValue;
		out.node = Node("literal prvalue " + pa11::describe_type(out.type) +
		                " " + to_string(binding->constant_value));
		out.constant_expression = true;
		out.has_constant_value = true;
		out.constant_value = binding->constant_value;
		out.null_pointer_constant = binding->constant_value == 0;
		out.node.binding = binding;
		out.node.token_text = to_string(binding->constant_value);
		annotate_expr_node(out);
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
	{
		out.constant_expression = true;
		out.has_constant_value = true;
		out.constant_value = binding->constant_value;
		out.null_pointer_constant = binding->constant_value == 0;
	}
	annotate_expr_node(out);
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
	out.category = op == OP_COMMA ? rhs.category : ValueCategory::PRValue;
	out.valid = true;
	out.constant_expression = lhs.constant_expression && rhs.constant_expression;
	if (lhs.has_constant_value && rhs.has_constant_value)
	{
		uint64_t value = 0;
		if (constant_binary_value(op, lhs.constant_value, rhs.constant_value, value))
		{
			out.has_constant_value = true;
			out.constant_value = value;
			out.null_pointer_constant = value == 0 &&
				pa11::is_integral_or_bool_type(out.type);
		}
	}
	out.node = Node("binary-expression prvalue " + pa11::describe_type(type) +
	                " " + op_leaf(op, text));
	add_child(out.node, lhs.node);
	add_child(out.node, rhs.node);
	out.node.has_op = true;
	out.node.op = op;
	out.node.token_text = text;
	annotate_expr_node(out);
	return out;
}

Expr Parser::make_assignment_expr(ETokenType op,
                                  const string& text,
                                  Expr lhs,
                                  Expr rhs)
{
	TypePtr lhs_type = expression_object_type(lhs.type);
	TypePtr lhs_bare = pa11::strip_cv(lhs_type);
	if (lhs.category != ValueCategory::LValue ||
	    top_level_const(lhs_type) ||
	    lhs_bare->kind == pa11::TypeKind::Array ||
	    lhs_bare->kind == pa11::TypeKind::Function)
		throw runtime_error("assignment lhs is not lvalue");
	Conversion conv;
	if (op == OP_ASS)
	{
		conv = convert_to(rhs, lhs_type);
		if (!conv.viable)
			throw runtime_error("invalid assignment conversion");
	}
	else
	{
		TypePtr rhs_type = lvalue_to_rvalue_type(rhs.type);
		if (!compound_assignment_rhs_viable(op,
		                                    lvalue_to_rvalue_type(lhs.type),
		                                    rhs_type))
			throw runtime_error("invalid compound assignment conversion");
		conv = Conversion(true, 2, rhs);
	}
	Expr out;
	out.type = lhs_type;
	out.category = ValueCategory::LValue;
	out.valid = true;
	out.node = Node("assignment-expression lvalue " +
	                pa11::describe_type(out.type) + " " + op_leaf(op, text));
	add_child(out.node, lhs.node);
	add_child(out.node, conv.expr.node);
	out.node.has_op = true;
	out.node.op = op;
	out.node.token_text = text;
	annotate_expr_node(out);
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
	out.constant_expression = out.category == ValueCategory::PRValue &&
	                          inner.constant_expression;
	if (inner.has_constant_value)
	{
		uint64_t value = inner.constant_value;
		bool have_value = true;
		if (op == OP_MINUS)
			value = uint64_t(0) - value;
		else if (op == OP_LNOT)
			value = value == 0 ? 1 : 0;
		else if (op == OP_COMPL)
			value = ~value;
		else if (op != OP_PLUS)
			have_value = false;
		if (have_value)
		{
			out.has_constant_value = true;
			out.constant_value = value;
			out.null_pointer_constant = value == 0 &&
				pa11::is_integral_or_bool_type(out.type);
		}
	}
	out.node = Node("unary-expression " + value_category_name(out.category) +
	                " " + pa11::describe_type(out.type) + " " +
	                op_leaf(op, text));
	add_child(out.node, inner.node);
	out.node.has_op = true;
	out.node.op = op;
	out.node.token_text = text;
	annotate_expr_node(out);
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
	out.node.has_op = true;
	out.node.op = op;
	out.node.token_text = text;
	annotate_expr_node(out);
	return out;
}

Expr Parser::make_subscript_expr(Expr lhs, Expr rhs)
{
	TypePtr base = pa11::strip_cv(expression_object_type(lhs.type));
	if (base->kind == pa11::TypeKind::Array)
		base = base->base;
	else if (base->kind == pa11::TypeKind::Pointer)
		base = base->base;
	else
	{
		TypePtr rbase = pa11::strip_cv(expression_object_type(rhs.type));
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
	TypePtr rhs_base = pa11::strip_cv(expression_object_type(rhs.type));
	if (rhs_base->kind == pa11::TypeKind::Array ||
	    rhs_base->kind == pa11::TypeKind::Pointer)
	{
		add_child(out.node, rhs.node);
		add_child(out.node, lhs.node);
	}
	else
	{
		add_child(out.node, lhs.node);
		add_child(out.node, rhs.node);
	}
	annotate_expr_node(out);
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
	out.binding = found[0];
	out.valid = true;
	out.node = Node("member-expression lvalue " +
	                pa11::describe_type(member_type) + " OP_DOT:" + name);
	add_child(out.node, object.node);
	out.node.binding = found[0];
	out.node.token_text = name;
	annotate_expr_node(out);
	return out;
}

Expr Parser::make_cast_expr(TypePtr target, const string& op_text, Expr inner)
{
	Expr out;
	out.type = target;
	out.category = target->kind == pa11::TypeKind::LValueReference
		? ValueCategory::LValue :
		target->kind == pa11::TypeKind::RValueReference
		? ValueCategory::XValue :
		ValueCategory::PRValue;
	out.valid = true;
	out.constant_expression = inner.constant_expression;
	out.has_constant_value = inner.has_constant_value;
	out.constant_value = inner.constant_value;
	out.null_pointer_constant = inner.null_pointer_constant &&
	                            !type_is_pointer(target);
	if (target->kind == pa11::TypeKind::RValueReference &&
	    inner.binding != NULL)
	{
		out.binding = inner.binding;
		out.node = Node("id-expression xvalue " + pa11::describe_type(target) +
		                " " + inner.binding->name);
		annotate_expr_node(out);
		return out;
	}
	string line = "cast-expression prvalue " + pa11::describe_type(target);
	if (!op_text.empty())
		line += " " + op_text;
	out.node = Node(line);
	add_child(out.node, inner.node);
	out.node.token_text = op_text;
	annotate_expr_node(out);
	return out;
}

Expr Parser::make_sizeof_expr(uint64_t value)
{
	Expr out;
	out.type = pa11::make_fundamental(FT_UNSIGNED_LONG_INT);
	out.category = ValueCategory::PRValue;
	out.valid = true;
	out.constant_expression = true;
	out.has_constant_value = true;
	out.constant_value = value;
	out.null_pointer_constant = value == 0;
	out.node = Node("sizeof-expression prvalue unsigned long int");
	out.node.token_text = to_string(value);
	annotate_expr_node(out);
	return out;
}

}  // namespace internal
}  // namespace pa12
