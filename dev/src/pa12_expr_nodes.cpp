#include "pa12_internal.h"

#include <algorithm>
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

Expr make_this_id_expr(Binding* binding)
{
	Expr out;
	out.binding = binding;
	out.type = binding->type;
	out.category = ValueCategory::LValue;
	out.valid = true;
	out.node = Node("id-expression lvalue " + pa11::describe_type(out.type) +
	                " this");
	annotate_expr_node(out);
	return out;
}

Expr make_constant_binding_expr(Binding* binding, TypePtr type)
{
	Expr out;
	out.binding = binding;
	out.type = type;
	out.category = ValueCategory::PRValue;
	out.valid = true;
	out.constant_expression = true;
	out.has_constant_value = true;
	out.constant_value = binding->constant_value;
	out.null_pointer_constant = binding->constant_value == 0;
	out.node = Node("literal prvalue " + pa11::describe_type(out.type) +
	                " " + to_string(binding->constant_value));
	out.node.binding = binding;
	out.node.token_text = to_string(binding->constant_value);
	annotate_expr_node(out);
	return out;
}

}  // namespace

Expr Parser::make_builtin_id_expr(const QualifiedName& name)
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
	if (!name.qualified &&
	    (name.name == "__builtin_strlen" ||
	     name.name == "__builtin_unreachable" ||
	     name.name == "__builtin_memcpy" ||
	     name.name == "__builtin_memmove"))
	{
		Binding* binding =
			pa11::lookup_unqualified(global_scope(), name.name, pa11::LOOKUP_FUNCTION);
		if (binding == NULL)
		{
			vector<TypePtr> params;
			TypePtr result = pa11::make_fundamental(FT_VOID);
			TypePtr void_ptr =
				pa11::make_pointer(pa11::make_fundamental(FT_VOID));
			TypePtr const_void_ptr =
				pa11::make_pointer(pa11::make_cv(pa11::make_fundamental(FT_VOID),
				                                  pa11::CV_CONST));
			if (name.name == "__builtin_strlen")
			{
				TypePtr chr = pa11::make_cv(pa11::make_fundamental(FT_CHAR),
				                            pa11::CV_CONST);
				params.push_back(pa11::make_pointer(chr));
				result = pa11::make_fundamental(FT_UNSIGNED_LONG_INT);
			}
			else if (name.name == "__builtin_memcpy" ||
			         name.name == "__builtin_memmove")
			{
				params.push_back(void_ptr);
				params.push_back(const_void_ptr);
				params.push_back(pa11::make_fundamental(FT_UNSIGNED_LONG_INT));
				result = void_ptr;
			}
			TypePtr fn = pa11::make_function(result, params, false);
			binding = add_value(global_scope(), BindingKind::Function, name.name, fn);
		}
		Expr out;
		out.valid = true;
		out.binding = binding;
		out.type = binding->type;
		out.category = ValueCategory::LValue;
		out.overloads.push_back(binding);
		out.node = Node("id-expression lvalue " +
		                pa11::describe_type(out.type) + " " + binding->name);
		annotate_expr_node(out);
		return out;
	}
	return Expr();
}

Expr Parser::make_implicit_member_id_expr(const QualifiedName& name,
                                          const vector<Binding*>& found,
                                          Binding* binding,
                                          Binding* this_binding)
{
	if ((!name.qualified ||
	     (name.qualifier != NULL && name.qualifier->kind == ScopeKind::Class)) &&
	    this_binding != NULL &&
	    binding->owner != NULL &&
	    binding->owner->kind == ScopeKind::Class &&
	    !binding->is_static_member)
	{
		Expr this_expr = make_this_id_expr(this_binding);
		if (name.qualified)
		{
			TypePtr this_type =
				pa11::strip_cv(expression_object_type(this_binding->type));
			TypePtr object_type = this_type->kind == pa11::TypeKind::Pointer
				? this_type->base : TypePtr();
			TypePtr object_record = object_type.get() != NULL
				? pa11::strip_cv(object_type) : TypePtr();
			if (!member_access_allowed(binding, object_record))
			{
				if (binding->is_private)
					throw runtime_error("private member access");
				throw runtime_error("protected member access");
			}
			Expr member;
			member.valid = true;
			member.binding = binding;
			member.type = binding->type;
			member.category = ValueCategory::LValue;
			if (binding->kind == BindingKind::Function)
			{
				for (size_t i = 0; i < found.size(); ++i)
					if (found[i]->kind == BindingKind::Function)
						member.overloads.push_back(found[i]);
			}
			else if (object_type.get() != NULL &&
			         pa11::type_has_const(object_type) &&
			         !binding->is_mutable_member)
				member.type = pa11::make_cv(member.type, pa11::CV_CONST);
			member.node = Node("member-expression lvalue " +
			                   pa11::describe_type(member.type) +
			                   " OP_ARROW:" + binding->name);
			add_child(member.node, this_expr.node);
			member.node.binding = binding;
			member.node.has_op = true;
			member.node.op = OP_ARROW;
			member.node.token_text = binding->name;
			annotate_expr_node(member);
			return member;
		}
		return make_member_expr(this_expr, binding->name, "->");
	}
	return Expr();
}

Expr Parser::make_id_expr(const QualifiedName& name)
{
	Expr builtin = make_builtin_id_expr(name);
	if (builtin.valid)
		return builtin;
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
	Binding* this_binding =
		pa11::lookup_unqualified(current_scope(), "this", pa11::LOOKUP_PARAMETER);
	if (name.qualified &&
	    name.qualifier != NULL &&
	    name.qualifier->kind == ScopeKind::Class &&
	    this_binding == NULL &&
	    !out.overloads.empty())
	{
		vector<Binding*> static_overloads;
		for (size_t i = 0; i < out.overloads.size(); ++i)
			if (out.overloads[i]->is_static_member)
				static_overloads.push_back(out.overloads[i]);
		if (!static_overloads.empty())
		{
			out.overloads = static_overloads;
			binding = out.overloads[0];
		}
	}
	Expr member = make_implicit_member_id_expr(name, found, binding, this_binding);
	if (member.valid)
		return member;
	if (binding->owner != NULL &&
	    binding->owner->kind == ScopeKind::Class &&
	    binding->is_static_member &&
	    binding->kind == BindingKind::Variable &&
	    binding->has_constant)
	{
		return make_constant_binding_expr(binding,
		                                  expression_object_type(binding->type));
	}
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
	vector<Binding*> candidates = binary_operator_candidates(op, text, lhs, rhs);
	if (!candidates.empty())
	{
		Expr callee;
		callee.valid = true;
		callee.binding = candidates[0];
		callee.type = candidates[0]->type;
		callee.category = ValueCategory::LValue;
		callee.overloads = candidates;
		callee.node = Node("id-expression lvalue " +
		                   pa11::describe_type(callee.type) + " " +
		                   candidates[0]->name);
		annotate_expr_node(callee);
		vector<Expr> args;
		args.push_back(lhs);
		args.push_back(rhs);
		try
		{
			return make_call_expr(callee, args);
		}
		catch (const runtime_error&)
		{
		}
	}
	TypePtr left_record = pa11::strip_cv(expression_object_type(lhs.type));
	if (left_record->kind == pa11::TypeKind::Record &&
	    left_record->scope != NULL)
	{
		string opname = operator_function_name(op, text);
		vector<Binding*> members =
			lookup_qualified_set(left_record->scope, opname, pa11::LOOKUP_FUNCTION);
		if (!members.empty())
		{
			Expr callee = make_member_expr(lhs, opname, ".");
			vector<Expr> args;
			args.push_back(rhs);
			return make_call_expr(callee, args);
		}
	}
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

void Parser::collect_associated_hidden_friends(TypePtr type,
                                               const string& name,
                                               set<Scope*>& seen,
                                               vector<Binding*>& out) const
{
	TypePtr object = expression_object_type(type);
	TypePtr bare = pa11::strip_cv(object);
	if (bare->kind != pa11::TypeKind::Record || bare->scope == NULL)
		return;
	if (!seen.insert(bare->scope).second)
		return;
	map<Scope*, vector<Binding*> >::const_iterator found =
		class_friend_functions_.find(bare->scope);
	if (found != class_friend_functions_.end())
	{
		for (size_t i = 0; i < found->second.size(); ++i)
		{
			Binding* binding = found->second[i];
			if (!binding->is_hidden_friend || binding->name != name)
				continue;
			if (find(out.begin(), out.end(), binding) == out.end())
				out.push_back(binding);
		}
	}
	TypePtr direct_base = bare->base.get() != NULL
		? pa11::strip_cv(bare->base) : TypePtr();
	if (direct_base.get() != NULL &&
	    direct_base->kind == pa11::TypeKind::Record)
		collect_associated_hidden_friends(direct_base, name, seen, out);
}

void Parser::collect_associated_namespace_functions(TypePtr type,
                                                    const string& name,
                                                    set<Scope*>& seen,
                                                    vector<Binding*>& out)
{
	TypePtr object = expression_object_type(type);
	TypePtr bare = pa11::strip_cv(object);
	if (bare->kind != pa11::TypeKind::Record || bare->scope == NULL)
		return;
	for (Scope* scope = bare->scope->parent; scope != NULL; scope = scope->parent)
	{
		if (scope->kind != ScopeKind::Namespace)
			continue;
		if (!seen.insert(scope).second)
			break;
		vector<Binding*> found =
			lookup_qualified_set(scope, name, pa11::LOOKUP_FUNCTION);
		for (size_t i = 0; i < found.size(); ++i)
			if (find(out.begin(), out.end(), found[i]) == out.end())
				out.push_back(found[i]);
		break;
	}
	TypePtr direct_base = bare->base.get() != NULL
		? pa11::strip_cv(bare->base) : TypePtr();
	if (direct_base.get() != NULL &&
	    direct_base->kind == pa11::TypeKind::Record)
		collect_associated_namespace_functions(direct_base, name, seen, out);
}

vector<Binding*> Parser::binary_operator_candidates(ETokenType op,
                                                    const string& text,
                                                    const Expr& lhs,
                                                    const Expr& rhs)
{
	TypePtr left = pa11::strip_cv(expression_object_type(lhs.type));
	TypePtr right = pa11::strip_cv(expression_object_type(rhs.type));
	bool overload_operand =
		left->kind == pa11::TypeKind::Record ||
		right->kind == pa11::TypeKind::Record ||
		left->kind == pa11::TypeKind::Enum ||
		right->kind == pa11::TypeKind::Enum;
	if (!overload_operand)
		return vector<Binding*>();
	string name = operator_function_name(op, text);
	vector<Binding*> out =
		lookup_unqualified_set(current_scope(), name, pa11::LOOKUP_FUNCTION);
	for (size_t i = 0; i < out.size();)
	{
		if (out[i]->owner != NULL &&
		    out[i]->owner->kind == ScopeKind::Class &&
		    !out[i]->is_static_member)
			out.erase(out.begin() + i);
		else
			++i;
	}
	set<Scope*> seen;
	collect_associated_hidden_friends(lhs.type, name, seen, out);
	collect_associated_hidden_friends(rhs.type, name, seen, out);
	set<Scope*> namespaces;
	collect_associated_namespace_functions(lhs.type, name, namespaces, out);
	collect_associated_namespace_functions(rhs.type, name, namespaces, out);
	return out;
}

Expr Parser::make_assignment_expr(ETokenType op,
                                  const string& text,
                                  Expr lhs,
                                  Expr rhs)
{
	TypePtr lhs_type = expression_object_type(lhs.type);
	TypePtr lhs_bare = pa11::strip_cv(lhs_type);
	if (op != OP_ASS)
	{
		vector<Binding*> candidates =
			binary_operator_candidates(op, text, lhs, rhs);
		if (!candidates.empty())
		{
			Expr callee;
			callee.valid = true;
			callee.binding = candidates[0];
			callee.type = candidates[0]->type;
			callee.category = ValueCategory::LValue;
			callee.overloads = candidates;
			callee.node = Node("id-expression lvalue " +
			                   pa11::describe_type(callee.type) + " " +
			                   candidates[0]->name);
			annotate_expr_node(callee);
			vector<Expr> args;
			args.push_back(lhs);
			args.push_back(rhs);
			return make_call_expr(callee, args);
		}
	}
	if (op == OP_ASS &&
	    lhs_bare->kind == pa11::TypeKind::Record &&
	    lhs_bare->scope != NULL)
	{
		vector<Binding*> members =
			lookup_qualified_set(lhs_bare->scope,
			                     "operator=",
			                     pa11::LOOKUP_FUNCTION);
		if (!members.empty())
		{
			Expr callee = make_member_expr(lhs, "operator=", ".");
			vector<Expr> args;
			args.push_back(rhs);
			return make_call_expr(callee, args);
		}
	}
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
	TypePtr record = pa11::strip_cv(expression_object_type(inner.type));
	if (record->kind == pa11::TypeKind::Record && record->scope != NULL)
	{
		string opname = operator_function_name(op, text);
		vector<Binding*> members =
			lookup_qualified_set(record->scope, opname, pa11::LOOKUP_FUNCTION);
		if (!members.empty())
		{
			Expr callee = make_member_expr(inner, opname, ".");
			vector<Expr> args;
			return make_call_expr(callee, args);
		}
	}
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
		{
			if (base->kind == pa11::TypeKind::Record && base->scope != NULL)
			{
				vector<Binding*> members =
					lookup_qualified_set(base->scope,
					                     "operator[]",
					                     pa11::LOOKUP_FUNCTION);
				if (!members.empty())
				{
					Expr callee = make_member_expr(lhs, "operator[]", ".");
					vector<Expr> args;
					args.push_back(rhs);
					return make_call_expr(callee, args);
				}
			}
			throw runtime_error("invalid subscript operands");
		}
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
	if (found.empty())
		throw runtime_error("member not found");
	if (!member_access_allowed(found[0], bare))
	{
		if (found[0]->is_private)
			throw runtime_error("private member access");
		throw runtime_error("protected member access");
	}
	if (found[0]->kind == BindingKind::Enumerator)
	{
		Expr out;
		out.binding = found[0];
		out.type = found[0]->type;
		out.category = ValueCategory::PRValue;
		out.valid = true;
		out.constant_expression = true;
		out.has_constant_value = true;
		out.constant_value = found[0]->constant_value;
		out.null_pointer_constant = found[0]->constant_value == 0;
		out.node = Node("literal prvalue " + pa11::describe_type(out.type) +
		                " " + to_string(found[0]->constant_value));
		out.node.binding = found[0];
		out.node.token_text = to_string(found[0]->constant_value);
		annotate_expr_node(out);
		return out;
	}
	if (found[0]->kind == BindingKind::Function)
	{
		vector<Binding*> overloads;
		bool have_nonstatic = false;
		for (size_t i = 0; i < found.size(); ++i)
			if (found[i]->kind == BindingKind::Function &&
			    !found[i]->is_static_member)
				have_nonstatic = true;
		for (size_t i = 0; i < found.size(); ++i)
			if (found[i]->kind == BindingKind::Function &&
			    (!have_nonstatic || !found[i]->is_static_member))
				overloads.push_back(found[i]);
		Binding* first = overloads.empty() ? found[0] : overloads[0];
		Expr out;
		out.valid = true;
		out.binding = first;
		out.type = first->type;
		out.category = ValueCategory::LValue;
		out.overloads = overloads;
		out.node = Node("member-expression lvalue " +
		                pa11::describe_type(out.type) + " OP_DOT:" + name);
		add_child(out.node, object.node);
		out.node.binding = first;
		out.node.has_op = true;
		out.node.op = op == "->" ? OP_ARROW : OP_DOT;
		out.node.token_text = name;
		annotate_expr_node(out);
		return out;
	}
	if (found[0]->is_static_member && found[0]->has_constant)
	{
		Expr out;
		out.type = expression_object_type(found[0]->type);
		out.category = ValueCategory::PRValue;
		out.binding = found[0];
		out.valid = true;
		out.constant_expression = true;
		out.has_constant_value = true;
		out.constant_value = found[0]->constant_value;
		out.null_pointer_constant = found[0]->constant_value == 0;
		out.node = Node("literal prvalue " + pa11::describe_type(out.type) +
		                " " + to_string(found[0]->constant_value));
		out.node.binding = found[0];
		out.node.token_text = to_string(found[0]->constant_value);
		annotate_expr_node(out);
		return out;
	}
	TypePtr member_type = found[0]->type;
	if (pa11::type_has_const(type) && !found[0]->is_mutable_member)
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
	out.node.has_op = true;
	out.node.op = op == "->" ? OP_ARROW : OP_DOT;
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
