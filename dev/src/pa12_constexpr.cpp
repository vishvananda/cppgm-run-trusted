#include "pa12_internal.h"

#include <cstdlib>
#include <iomanip>
#include <limits>
#include <sstream>

using namespace std;

namespace pa12 {
namespace internal {
namespace {

enum class EvalFlow
{
	Normal,
	Return,
	Break,
	Continue,
	Invalid
};

struct EvalState
{
	map<Binding*, ConstexprValue> locals;

	EvalState() {}
};

struct EvalBudget
{
	int steps;
	int depth;

	EvalBudget() : steps(0), depth(0) {}
};

EvalBudget* active_budget = NULL;

const int kMaxEvalSteps = 200000;
const int kMaxEvalDepth = 512;

struct EvalBudgetScope
{
	EvalBudget budget;
	EvalBudget* previous;

	EvalBudgetScope() : previous(active_budget)
	{
		if (active_budget == NULL)
			active_budget = &budget;
	}

	~EvalBudgetScope()
	{
		active_budget = previous;
	}
};

struct EvalCallScope
{
	bool entered;
	bool ok_;

	EvalCallScope() : entered(false), ok_(true)
	{
		if (active_budget != NULL)
		{
			entered = true;
			++active_budget->depth;
			ok_ = active_budget->depth <= kMaxEvalDepth;
		}
	}

	~EvalCallScope()
	{
		if (entered && active_budget != NULL)
			--active_budget->depth;
	}

	bool ok() const { return ok_; }
};

bool is_float_type(TypePtr type)
{
	TypePtr bare = pa11::strip_cv(type);
	return bare->kind == pa11::TypeKind::Fundamental &&
	       (bare->fundamental == FT_FLOAT ||
	        bare->fundamental == FT_DOUBLE ||
	        bare->fundamental == FT_LONG_DOUBLE);
}

bool starts_with(const string& text, const string& prefix)
{
	return text.compare(0, prefix.size(), prefix) == 0;
}

bool truthy(const ConstexprValue& value)
{
	if (value.is_pointer)
		return value.pointer_binding != NULL || value.pointer_index != 0;
	return value.is_float ? value.float_value != 0 : value.int_value != 0;
}

uint64_t integer_value(const ConstexprValue& value)
{
	if (value.is_pointer)
		return static_cast<uint64_t>(value.pointer_index);
	return value.is_float ? static_cast<uint64_t>(value.float_value) :
		value.int_value;
}

long double float_value(const ConstexprValue& value)
{
	return value.is_float ? value.float_value :
		static_cast<long double>(value.int_value);
}

string trim_float_suffix(string text)
{
	if (!text.empty())
	{
		char last = text[text.size() - 1];
		if (last == 'f' || last == 'F' || last == 'l' || last == 'L')
			text.resize(text.size() - 1);
	}
	return text;
}

string format_float(long double value)
{
	ostringstream out;
	out << setprecision(numeric_limits<long double>::digits10) << value;
	return out.str();
}

bool is_array_type(TypePtr type)
{
	return type.get() != NULL &&
	       pa11::strip_cv(type)->kind == pa11::TypeKind::Array;
}

bool consume_eval_step()
{
	if (active_budget == NULL)
		return true;
	++active_budget->steps;
	return active_budget->steps <= kMaxEvalSteps;
}

bool eval_node(Parser& parser,
               const Node& node,
               EvalState& state,
               ConstexprValue& out);

bool eval_lvalue_binding(const Node& node, Binding*& binding)
{
	if (node.binding != NULL)
	{
		binding = node.binding;
		return true;
	}
	if (!node.children.empty())
		return eval_lvalue_binding(node.children[0], binding);
	return false;
}

bool eval_pointer_deref(Parser& parser,
                        const ConstexprValue& pointer,
                        ConstexprValue& out)
{
	if (!pointer.is_pointer || pointer.pointer_binding == NULL)
		return false;
	ConstexprValue array;
	if (!parser.try_evaluate_constexpr_binding(pointer.pointer_binding, array) ||
	    !array.is_object ||
	    pointer.pointer_index < 0 ||
	    static_cast<size_t>(pointer.pointer_index) >= array.elements.size())
		return false;
	out = array.elements[static_cast<size_t>(pointer.pointer_index)];
	return true;
}

bool adjust_value(ConstexprValue& value, long long delta)
{
	if (value.is_pointer)
	{
		value.pointer_index += delta;
		return true;
	}
	if (value.is_float)
		value = ConstexprValue::floating(value.float_value + delta);
	else
		value = ConstexprValue::integer(value.int_value + delta);
	return true;
}

bool eval_literal(const Node& node, ConstexprValue& out)
{
	if (node.token_text == "true")
	{
		out = ConstexprValue::integer(1);
		return true;
	}
	if (node.token_text == "false" || node.token_text == "nullptr")
	{
		out = ConstexprValue::integer(0);
		return true;
	}
	StringLiteralInfo string_info;
	if (is_array_type(node.type) &&
	    AnalyzeStringLiteral(node.token_text, string_info) &&
	    string_info.ud_suffix.empty())
	{
		out = ConstexprValue::pointer(NULL, 1);
		return true;
	}
	if (is_float_type(node.type))
	{
		string text = trim_float_suffix(node.token_text);
		if (text.empty())
			return false;
		char* end = NULL;
		long double value = strtold(text.c_str(), &end);
		if (end == text.c_str())
			return false;
		out = ConstexprValue::floating(value);
		return true;
	}
	if (node.has_constant_value &&
	    starts_with(node.line, "sizeof-expression"))
	{
		out = ConstexprValue::integer(node.constant_value);
		return true;
	}
	if (!node.token_text.empty())
	{
		char* end = NULL;
		unsigned long long value = strtoull(node.token_text.c_str(), &end, 0);
		if (end != node.token_text.c_str())
		{
			out = ConstexprValue::integer(value);
			return true;
		}
	}
	return false;
}

bool eval_binary_value(ETokenType op,
                       const ConstexprValue& lhs,
                       const ConstexprValue& rhs,
                       ConstexprValue& out)
{
	if (lhs.is_pointer || rhs.is_pointer)
	{
		if (lhs.is_pointer && rhs.is_pointer)
		{
			bool same = lhs.pointer_binding == rhs.pointer_binding &&
			            lhs.pointer_index == rhs.pointer_index;
			if (op == OP_EQ)
			{
				out = ConstexprValue::integer(same ? 1 : 0);
				return true;
			}
			if (op == OP_NE)
			{
				out = ConstexprValue::integer(same ? 0 : 1);
				return true;
			}
			return false;
		}
		if (lhs.is_pointer && !rhs.is_pointer && !rhs.is_float &&
		    (op == OP_EQ || op == OP_NE))
		{
			bool same_null = !truthy(lhs) && rhs.int_value == 0;
			out = ConstexprValue::integer((op == OP_EQ) == same_null ? 1 : 0);
			return true;
		}
		if (rhs.is_pointer && !lhs.is_pointer && !lhs.is_float &&
		    (op == OP_EQ || op == OP_NE))
		{
			bool same_null = !truthy(rhs) && lhs.int_value == 0;
			out = ConstexprValue::integer((op == OP_EQ) == same_null ? 1 : 0);
			return true;
		}
		if (lhs.is_pointer && !rhs.is_float &&
		    (op == OP_PLUS || op == OP_MINUS))
		{
			long long delta = static_cast<long long>(rhs.int_value);
			if (op == OP_MINUS)
				delta = -delta;
			out = ConstexprValue::pointer(lhs.pointer_binding,
			                              lhs.pointer_index + delta);
			return true;
		}
		if (rhs.is_pointer && !lhs.is_float && op == OP_PLUS)
		{
			out = ConstexprValue::pointer(rhs.pointer_binding,
			                              rhs.pointer_index +
			                              static_cast<long long>(lhs.int_value));
			return true;
		}
		return false;
	}
	bool use_float = lhs.is_float || rhs.is_float;
	if (use_float)
	{
		long double l = float_value(lhs);
		long double r = float_value(rhs);
		switch (op)
		{
		case OP_PLUS: out = ConstexprValue::floating(l + r); return true;
		case OP_MINUS: out = ConstexprValue::floating(l - r); return true;
		case OP_STAR: out = ConstexprValue::floating(l * r); return true;
		case OP_DIV:
			if (r == 0) return false;
			out = ConstexprValue::floating(l / r);
			return true;
		case OP_EQ: out = ConstexprValue::integer(l == r ? 1 : 0); return true;
		case OP_NE: out = ConstexprValue::integer(l != r ? 1 : 0); return true;
		case OP_LT: out = ConstexprValue::integer(l < r ? 1 : 0); return true;
		case OP_GT: out = ConstexprValue::integer(l > r ? 1 : 0); return true;
		case OP_LE: out = ConstexprValue::integer(l <= r ? 1 : 0); return true;
		case OP_GE: out = ConstexprValue::integer(l >= r ? 1 : 0); return true;
		case OP_LAND:
			out = ConstexprValue::integer((l != 0 && r != 0) ? 1 : 0);
			return true;
		case OP_LOR:
			out = ConstexprValue::integer((l != 0 || r != 0) ? 1 : 0);
			return true;
		case OP_COMMA: out = rhs; return true;
		default:
			return false;
		}
	}
	uint64_t l = lhs.int_value;
	uint64_t r = rhs.int_value;
	switch (op)
	{
	case OP_PLUS: out = ConstexprValue::integer(l + r); return true;
	case OP_MINUS: out = ConstexprValue::integer(l - r); return true;
	case OP_STAR: out = ConstexprValue::integer(l * r); return true;
	case OP_DIV:
		if (r == 0) return false;
		out = ConstexprValue::integer(static_cast<int64_t>(l) /
		                              static_cast<int64_t>(r));
		return true;
	case OP_MOD:
		if (r == 0) return false;
		out = ConstexprValue::integer(static_cast<int64_t>(l) %
		                              static_cast<int64_t>(r));
		return true;
	case OP_EQ: out = ConstexprValue::integer(l == r ? 1 : 0); return true;
	case OP_NE: out = ConstexprValue::integer(l != r ? 1 : 0); return true;
	case OP_LT:
		out = ConstexprValue::integer(static_cast<int64_t>(l) <
		                              static_cast<int64_t>(r) ? 1 : 0);
		return true;
	case OP_GT:
		out = ConstexprValue::integer(static_cast<int64_t>(l) >
		                              static_cast<int64_t>(r) ? 1 : 0);
		return true;
	case OP_LE:
		out = ConstexprValue::integer(static_cast<int64_t>(l) <=
		                              static_cast<int64_t>(r) ? 1 : 0);
		return true;
	case OP_GE:
		out = ConstexprValue::integer(static_cast<int64_t>(l) >=
		                              static_cast<int64_t>(r) ? 1 : 0);
		return true;
	case OP_LAND: out = ConstexprValue::integer((l && r) ? 1 : 0); return true;
	case OP_LOR: out = ConstexprValue::integer((l || r) ? 1 : 0); return true;
	case OP_AMP: out = ConstexprValue::integer(l & r); return true;
	case OP_BOR: out = ConstexprValue::integer(l | r); return true;
	case OP_XOR: out = ConstexprValue::integer(l ^ r); return true;
	case OP_LSHIFT: out = ConstexprValue::integer(l << r); return true;
	case OP_RSHIFT:
		out = ConstexprValue::integer(static_cast<int64_t>(l) >> r);
		return true;
	case OP_COMMA: out = rhs; return true;
	default:
		return false;
	}
}

bool eval_expr_list(Parser& parser,
                    const vector<Node>& children,
                    size_t begin,
                    EvalState& state,
                    vector<ConstexprValue>& out)
{
	for (size_t i = begin; i < children.size(); ++i)
	{
		ConstexprValue value;
		if (!eval_node(parser, children[i], state, value))
			return false;
		out.push_back(value);
	}
	return true;
}

bool eval_call(Parser& parser,
               const Node& node,
               EvalState& state,
               ConstexprValue& out)
{
	Binding* direct = node.direct_call;
	if (direct == NULL &&
	    !node.children.empty() &&
	    node.children[0].direct_call != NULL)
		direct = node.children[0].direct_call;
	if (direct == NULL)
		return false;
	size_t arg_begin = !node.children.empty() &&
	                   node.children[0].line.compare(0, 7, "callee ") == 0
		? 1 : 0;
	vector<ConstexprValue> values;
	if (!eval_expr_list(parser, node.children, arg_begin, state, values))
		return false;
	return parser.try_evaluate_constexpr_call_values(direct, values, out);
}

bool eval_braced_init_list(Parser& parser,
                           const Node& node,
                           EvalState& state,
                           ConstexprValue& out)
{
	if (node.type.get() == NULL)
		return false;
	TypePtr type = pa11::strip_cv(node.type);
	if (node.direct_call != NULL)
	{
		vector<ConstexprValue> args;
		if (!eval_expr_list(parser, node.children, 0, state, args))
			return false;
		return parser.try_evaluate_constexpr_constructor(node.direct_call,
		                                                type,
		                                                args,
		                                                out);
	}
	if (type->kind == pa11::TypeKind::Array)
	{
		out = ConstexprValue::object(type);
		for (size_t i = 0; i < node.children.size(); ++i)
		{
			Node child = node.children[i];
			if (starts_with(child.line, "braced-init-list") &&
			    child.type.get() == NULL)
				child.type = type->base;
			ConstexprValue elem;
			if (!eval_node(parser, child, state, elem))
				return false;
			out.elements.push_back(elem);
		}
		return true;
	}
	if (type->kind != pa11::TypeKind::Record)
		return false;
	pa11::layout_record_type(type);
	out = ConstexprValue::object(type);
	size_t index = 0;
	for (size_t i = 0; i < type->fields.size() && index < node.children.size(); ++i)
	{
		Binding* field = type->fields[i];
		if (field == NULL || field->is_static_member)
			continue;
		Node child = node.children[index++];
		if (starts_with(child.line, "braced-init-list") &&
		    child.type.get() == NULL)
			child.type = field->type;
		ConstexprValue value;
		if (!eval_node(parser, child, state, value))
			return false;
		out.fields[field] = value;
	}
	return true;
}

bool eval_member_field(Parser& parser,
                       const Node& node,
                       EvalState& state,
                       ConstexprValue& out)
{
	if (!starts_with(node.line, "member-expression") ||
	    node.binding == NULL ||
	    node.children.empty())
		return false;
	ConstexprValue object;
	if (!eval_node(parser, node.children[0], state, object) ||
	    !object.is_object)
		return false;
	map<Binding*, ConstexprValue>::const_iterator found =
		object.fields.find(node.binding);
	if (found == object.fields.end())
		return false;
	out = found->second;
	return true;
}

bool eval_named_node(Parser& parser,
                     const Node& node,
                     EvalState& state,
                     ConstexprValue& out)
{
	if (node.binding != NULL)
	{
		map<Binding*, ConstexprValue>::const_iterator found =
			state.locals.find(node.binding);
		if (found != state.locals.end())
		{
			out = found->second;
			return true;
		}
		if (is_array_type(node.type))
		{
			out = ConstexprValue::pointer(node.binding, 0);
			return true;
		}
		if (node.binding->has_constant)
		{
			out = ConstexprValue::integer(node.binding->constant_value);
			return true;
		}
		if (parser.try_evaluate_constexpr_binding(node.binding, out))
			return true;
	}
	if (!node.children.empty())
		return eval_node(parser, node.children[0], state, out);
	return false;
}

bool eval_cast_node(Parser& parser,
                    const Node& node,
                    EvalState& state,
                    ConstexprValue& out)
{
	bool child_ok = !node.children.empty() &&
	                eval_node(parser, node.children[0], state, out);
	if (node.op == OP_AMP)
		return child_ok && out.is_object;
	if (!child_ok)
		return false;
	TypePtr target = node.type.get() == NULL ? TypePtr() : pa11::strip_cv(node.type);
	if (target.get() != NULL && target->kind == pa11::TypeKind::Pointer)
	{
		if (out.is_object || out.is_pointer)
			return true;
		if (!out.is_float && out.int_value == 0)
		{
			out = ConstexprValue::pointer(NULL, 0);
			return true;
		}
		return false;
	}
	if (is_float_type(node.type))
		out = ConstexprValue::floating(float_value(out));
	else
		out = ConstexprValue::integer(integer_value(out));
	return true;
}

bool eval_unary_node(Parser& parser,
                     const Node& node,
                     EvalState& state,
                     ConstexprValue& out)
{
	if (node.children.empty() ||
	    !eval_node(parser, node.children[0], state, out))
	{
		return false;
	}
	switch (node.op)
	{
	case OP_PLUS:
		return true;
	case OP_MINUS:
		out = out.is_float
			? ConstexprValue::floating(-out.float_value)
			: ConstexprValue::integer(uint64_t(0) - out.int_value);
		return true;
	case OP_LNOT:
		out = ConstexprValue::integer(truthy(out) ? 0 : 1);
		return true;
	case OP_COMPL:
		out = ConstexprValue::integer(~integer_value(out));
		return true;
	case OP_STAR:
		return eval_pointer_deref(parser, out, out);
	case OP_AMP:
		return out.is_object;
	case OP_INC:
	case OP_DEC:
	{
		Binding* target = NULL;
		if (!eval_lvalue_binding(node.children[0], target) || target == NULL)
			return false;
		adjust_value(out, node.op == OP_INC ? 1 : -1);
		state.locals[target] = out;
		return true;
	}
	default:
		return false;
	}
}

bool eval_constructor_action(Parser& parser,
                             const Node& action,
                             TypePtr object_type,
                             EvalState& state,
                             ConstexprValue& out)
{
	if (action.children.empty())
		return false;
	const Node& call = action.children[0];
	if (!starts_with(call.line, "call-expression") ||
	    call.direct_call == NULL)
		return false;
	vector<ConstexprValue> args;
	for (size_t i = 2; i < call.children.size(); ++i)
	{
		ConstexprValue arg;
		if (!eval_node(parser, call.children[i], state, arg))
			return false;
		args.push_back(arg);
	}
	return parser.try_evaluate_constexpr_constructor(call.direct_call,
	                                                object_type,
	                                                args,
	                                                out);
}

TypePtr constructor_action_object_type(const Node& action)
{
	if (action.type.get() != NULL)
		return action.type;
	if (action.children.empty())
		return TypePtr();
	const Node& call = action.children[0];
	if (call.children.size() < 2 ||
	    call.children[1].children.empty())
		return TypePtr();
	return call.children[1].children[0].type;
}

bool eval_variable_initializer(Parser& parser,
                               const Node& var,
                               EvalState& state,
                               ConstexprValue& out)
{
	if (var.binding == NULL)
		return false;
	if (var.children.empty())
		return constexpr_zero_value_for_type(var.binding->type, out);
	const Node& init = var.children[0];
	if (starts_with(init.line, "constructor-action"))
		return eval_constructor_action(parser,
		                               init,
		                               var.binding->type,
		                               state,
		                               out);
	if (starts_with(init.line, "no-op-initializer"))
		return constexpr_zero_value_for_type(var.binding->type, out);
	return eval_node(parser, init, state, out);
}

bool eval_binary_node(Parser& parser,
                      const Node& node,
                      EvalState& state,
                      ConstexprValue& out)
{
	if (node.children.size() != 2)
		return false;
	if (node.op == OP_LAND)
	{
		ConstexprValue lhs;
		if (!eval_node(parser, node.children[0], state, lhs))
			return false;
		if (!truthy(lhs))
		{
			out = ConstexprValue::integer(0);
			return true;
		}
		ConstexprValue rhs;
		if (!eval_node(parser, node.children[1], state, rhs))
			return false;
		out = ConstexprValue::integer(truthy(rhs) ? 1 : 0);
		return true;
	}
	if (node.op == OP_LOR)
	{
		ConstexprValue lhs;
		if (!eval_node(parser, node.children[0], state, lhs))
			return false;
		if (truthy(lhs))
		{
			out = ConstexprValue::integer(1);
			return true;
		}
		ConstexprValue rhs;
		if (!eval_node(parser, node.children[1], state, rhs))
			return false;
		out = ConstexprValue::integer(truthy(rhs) ? 1 : 0);
		return true;
	}
	ConstexprValue lhs;
	ConstexprValue rhs;
	if (!eval_node(parser, node.children[0], state, lhs) ||
	    !eval_node(parser, node.children[1], state, rhs))
		return false;
	if (node.op == OP_EQ || node.op == OP_NE || node.op == OP_LT ||
	    node.op == OP_GT || node.op == OP_LE || node.op == OP_GE)
	{
		if (constexpr_integral_compare(node.op,
		                          node.children[0].type,
		                          lhs,
		                          rhs,
		                          out))
			return true;
	}
	return eval_binary_value(node.op, lhs, rhs, out);
}

bool assignment_base_op(ETokenType op, ETokenType& base)
{
	if (op == OP_PLUSASS) base = OP_PLUS;
	else if (op == OP_MINUSASS) base = OP_MINUS;
	else if (op == OP_STARASS) base = OP_STAR;
	else if (op == OP_DIVASS) base = OP_DIV;
	else if (op == OP_MODASS) base = OP_MOD;
	else if (op == OP_BANDASS) base = OP_AMP;
	else if (op == OP_BORASS) base = OP_BOR;
	else if (op == OP_XORASS) base = OP_XOR;
	else if (op == OP_LSHIFTASS) base = OP_LSHIFT;
	else if (op == OP_RSHIFTASS) base = OP_RSHIFT;
	else return false;
	return true;
}

bool eval_assignment_node(Parser& parser,
                          const Node& node,
                          EvalState& state,
                          ConstexprValue& out)
{
	if (node.children.size() != 2)
		return false;
	Binding* target = NULL;
	if (!eval_lvalue_binding(node.children[0], target) || target == NULL)
		return false;
	ConstexprValue rhs;
	if (!eval_node(parser, node.children[1], state, rhs))
		return false;
	if (node.op != OP_ASS)
	{
		map<Binding*, ConstexprValue>::const_iterator found =
			state.locals.find(target);
		if (found == state.locals.end())
			return false;
		ETokenType op = OP_PLUS;
		if (!assignment_base_op(node.op, op) ||
		    !eval_binary_value(op, found->second, rhs, rhs))
			return false;
	}
	state.locals[target] = rhs;
	out = rhs;
	return true;
}

bool eval_postfix_node(Parser& parser,
                       const Node& node,
                       EvalState& state,
                       ConstexprValue& out)
{
	if (node.children.empty() ||
	    !eval_node(parser, node.children[0], state, out))
		return false;
	if (node.op != OP_INC && node.op != OP_DEC)
		return false;
	Binding* target = NULL;
	if (!eval_lvalue_binding(node.children[0], target) || target == NULL)
		return false;
	ConstexprValue updated = out;
	adjust_value(updated, node.op == OP_INC ? 1 : -1);
	state.locals[target] = updated;
	return true;
}

bool eval_subscript_node(Parser& parser,
                         const Node& node,
                         EvalState& state,
                         ConstexprValue& out)
{
	if (node.children.size() != 2)
		return false;
	ConstexprValue index;
	if (!eval_node(parser, node.children[1], state, index))
		return false;
	if (constexpr_string_literal_element(node.children[0], index, out))
		return true;
	ConstexprValue base;
	if (!eval_node(parser, node.children[0], state, base))
		return false;
	long long offset = static_cast<long long>(integer_value(index));
	if (base.is_pointer)
	{
		base.pointer_index += offset;
		return eval_pointer_deref(parser, base, out);
	}
	if (!base.is_object || offset < 0 ||
	    static_cast<size_t>(offset) >= base.elements.size())
		return false;
	out = base.elements[static_cast<size_t>(offset)];
	return true;
}

bool eval_condition_declaration(Parser& parser,
                                const Node& node,
                                EvalState& state,
                                ConstexprValue& out)
{
	bool have_value = false;
	for (size_t i = 0; i < node.children.size(); ++i)
	{
		const Node& child = node.children[i];
		if (starts_with(child.line, "variable ") &&
		    child.binding != NULL)
		{
			ConstexprValue value;
			if (!eval_variable_initializer(parser, child, state, value))
				return false;
			state.locals[child.binding] = value;
			out = value;
			have_value = true;
		}
		else
		{
			if (!eval_node(parser, child, state, out))
				return false;
			have_value = true;
		}
	}
	return have_value;
}

bool eval_node(Parser& parser,
               const Node& node,
               EvalState& state,
               ConstexprValue& out)
{
	if (!consume_eval_step())
		return false;
	if (node.has_constant_value)
	{
		out = ConstexprValue::integer(node.constant_value);
		return true;
	}
	if (starts_with(node.line, "literal "))
		return eval_literal(node, out);
	if (starts_with(node.line, "braced-init-list"))
		return eval_braced_init_list(parser, node, state, out);
	if (starts_with(node.line, "constructor-action"))
	{
		TypePtr object_type = constructor_action_object_type(node);
		if (object_type.get() == NULL)
			return false;
		return eval_constructor_action(parser, node, object_type, state, out);
	}
	if (eval_member_field(parser, node, state, out))
		return true;
	if (starts_with(node.line, "id-expression") ||
	    starts_with(node.line, "member-expression") ||
	    starts_with(node.line, "variable "))
		return eval_named_node(parser, node, state, out);
	if (starts_with(node.line, "cast-expression"))
		return eval_cast_node(parser, node, state, out);
	if (starts_with(node.line, "unary-expression"))
		return eval_unary_node(parser, node, state, out);
	if (starts_with(node.line, "binary-expression"))
		return eval_binary_node(parser, node, state, out);
	if (starts_with(node.line, "conditional-expression"))
	{
		if (node.children.size() != 3)
			return false;
		ConstexprValue cond;
		if (!eval_node(parser, node.children[0], state, cond))
			return false;
		return eval_node(parser, node.children[truthy(cond) ? 1 : 2],
		                 state,
		                 out);
	}
	if (starts_with(node.line, "assignment-expression"))
		return eval_assignment_node(parser, node, state, out);
	if (starts_with(node.line, "call-expression"))
		return eval_call(parser, node, state, out);
	if (starts_with(node.line, "postfix-expression"))
		return eval_postfix_node(parser, node, state, out);
	if (starts_with(node.line, "subscript-expression"))
		return eval_subscript_node(parser, node, state, out);
	if (starts_with(node.line, "condition-declaration"))
		return eval_condition_declaration(parser, node, state, out);
	if (starts_with(node.line, "condition") && !node.children.empty())
		return eval_node(parser, node.children[0], state, out);
	return false;
}

EvalFlow eval_statement(Parser& parser,
                        const Node& node,
                        EvalState& state,
                        ConstexprValue& out);

EvalFlow eval_compound(Parser& parser,
                       const Node& node,
                       EvalState& state,
                       ConstexprValue& out)
{
	for (size_t i = 0; i < node.children.size(); ++i)
	{
		EvalFlow flow = eval_statement(parser, node.children[i], state, out);
		if (flow != EvalFlow::Normal)
			return flow;
	}
	return EvalFlow::Normal;
}

EvalFlow eval_branch_child(Parser& parser,
                           const Node& wrapper,
                           EvalState& state,
                           ConstexprValue& out)
{
	if (wrapper.children.empty())
		return EvalFlow::Normal;
	return eval_statement(parser, wrapper.children[0], state, out);
}

EvalFlow eval_statement(Parser& parser,
                        const Node& node,
                        EvalState& state,
                        ConstexprValue& out)
{
	if (starts_with(node.line, "compound-statement"))
		return eval_compound(parser, node, state, out);
	if (starts_with(node.line, "for-init-statement"))
	{
		for (size_t i = 0; i < node.children.size(); ++i)
		{
			const Node& child = node.children[i];
			if (starts_with(child.line, "simple-declaration"))
			{
				EvalFlow flow = eval_statement(parser, child, state, out);
				if (flow != EvalFlow::Normal)
					return flow;
			}
			else if (!eval_node(parser, child, state, out))
				return EvalFlow::Invalid;
		}
		return EvalFlow::Normal;
	}
	if (starts_with(node.line, "simple-declaration"))
	{
		for (size_t i = 0; i < node.children.size(); ++i)
		{
			const Node& var = node.children[i];
			if (!starts_with(var.line, "variable ") || var.binding == NULL)
				continue;
			ConstexprValue value;
			if (!eval_variable_initializer(parser, var, state, value))
				return EvalFlow::Invalid;
			state.locals[var.binding] = value;
		}
		return EvalFlow::Normal;
	}
	if (starts_with(node.line, "storage-copy-action"))
	{
		if (node.children.empty())
			return EvalFlow::Invalid;
		ConstexprValue source;
		if (!eval_node(parser, node.children[0], state, source) ||
		    !source.is_object)
			return EvalFlow::Invalid;
		bool stored = false;
		for (map<Binding*, ConstexprValue>::iterator it = state.locals.begin();
		     it != state.locals.end();
		     ++it)
		{
			if (it->first == NULL || it->first->name != "this" ||
			    !it->second.is_object)
				continue;
			for (map<Binding*, ConstexprValue>::const_iterator fit =
			     source.fields.begin();
			     fit != source.fields.end();
			     ++fit)
				it->second.fields[fit->first] = fit->second;
			stored = true;
			break;
		}
		return stored ? EvalFlow::Normal : EvalFlow::Invalid;
	}
	if (starts_with(node.line, "base-init-action"))
	{
		ConstexprValue value;
		if (!node.children.empty())
		{
			if (!eval_node(parser, node.children[0], state, value))
				return EvalFlow::Invalid;
		}
		else if (node.direct_call != NULL)
		{
			vector<ConstexprValue> args;
			if (!parser.try_evaluate_constexpr_constructor(node.direct_call,
			                                               node.type,
			                                               args,
			                                               value))
				return EvalFlow::Invalid;
		}
		else if (!constexpr_zero_value_for_type(node.type, value))
			return EvalFlow::Invalid;
		bool stored = false;
		for (map<Binding*, ConstexprValue>::iterator it = state.locals.begin();
		     it != state.locals.end();
		     ++it)
		{
			if (it->first == NULL || it->first->name != "this" ||
			    !it->second.is_object)
				continue;
			for (map<Binding*, ConstexprValue>::const_iterator fit =
			     value.fields.begin();
			     fit != value.fields.end();
			     ++fit)
				it->second.fields[fit->first] = fit->second;
			stored = true;
			break;
		}
		return stored ? EvalFlow::Normal : EvalFlow::Invalid;
	}
	if (starts_with(node.line, "delegating-init-action"))
	{
		if (node.children.empty())
			return EvalFlow::Invalid;
		ConstexprValue value;
		if (!eval_node(parser, node.children[0], state, value) ||
		    !value.is_object)
			return EvalFlow::Invalid;
		for (map<Binding*, ConstexprValue>::iterator it = state.locals.begin();
		     it != state.locals.end();
		     ++it)
		{
			if (it->first != NULL && it->first->name == "this")
			{
				it->second = value;
				return EvalFlow::Normal;
			}
		}
		return EvalFlow::Invalid;
	}
	if (starts_with(node.line, "member-init-action") && node.binding != NULL)
	{
		ConstexprValue value;
		if (!node.children.empty() &&
		    !eval_node(parser, node.children[0], state, value))
			return EvalFlow::Invalid;
		else if (node.children.empty() && node.direct_call != NULL)
		{
			vector<ConstexprValue> args;
			if (!parser.try_evaluate_constexpr_constructor(node.direct_call,
			                                               node.binding->type,
			                                               args,
			                                               value))
				return EvalFlow::Invalid;
		}
		else if (node.children.empty() &&
		         !constexpr_zero_value_for_type(node.binding->type, value))
			return EvalFlow::Invalid;
		bool stored = false;
		for (map<Binding*, ConstexprValue>::iterator it = state.locals.begin();
		     it != state.locals.end();
		     ++it)
		{
			if (it->first == NULL || it->first->name != "this" ||
			    !it->second.is_object)
				continue;
			it->second.fields[node.binding] = value;
			stored = true;
			break;
		}
		return stored ? EvalFlow::Normal : EvalFlow::Invalid;
	}
	if (starts_with(node.line, "expression-statement"))
	{
		if (!node.children.empty() &&
		    !eval_node(parser, node.children[0], state, out))
			return EvalFlow::Invalid;
		return EvalFlow::Normal;
	}
	if (starts_with(node.line, "return-statement"))
	{
		if (node.children.empty())
			out = ConstexprValue::integer(0);
		else if (!eval_node(parser, node.children[0], state, out))
			return EvalFlow::Invalid;
		return EvalFlow::Return;
	}
	if (starts_with(node.line, "if-statement"))
	{
		if (node.children.size() < 2)
			return EvalFlow::Normal;
		ConstexprValue cond;
		if (!eval_node(parser, node.children[0], state, cond))
			return EvalFlow::Invalid;
		if (truthy(cond))
			return eval_branch_child(parser, node.children[1], state, out);
		if (node.children.size() > 2)
			return eval_branch_child(parser, node.children[2], state, out);
		return EvalFlow::Normal;
	}
	if (starts_with(node.line, "while-statement"))
	{
		if (node.children.size() < 2)
			return EvalFlow::Normal;
		for (;;)
		{
			ConstexprValue cond;
			if (!eval_node(parser, node.children[0], state, cond))
				return EvalFlow::Invalid;
			if (!truthy(cond))
				return EvalFlow::Normal;
			EvalFlow flow = eval_statement(parser, node.children[1], state, out);
			if (flow == EvalFlow::Return)
				return flow;
			if (flow == EvalFlow::Invalid)
				return flow;
			if (flow == EvalFlow::Break)
				return EvalFlow::Normal;
		}
	}
	if (starts_with(node.line, "do-statement"))
	{
		if (node.children.size() < 2)
			return EvalFlow::Normal;
		for (;;)
		{
			EvalFlow flow = eval_statement(parser, node.children[0], state, out);
			if (flow == EvalFlow::Return)
				return flow;
			if (flow == EvalFlow::Invalid)
				return flow;
			if (flow == EvalFlow::Break)
				return EvalFlow::Normal;
			ConstexprValue cond;
			if (!eval_node(parser, node.children[1], state, cond))
				return EvalFlow::Invalid;
			if (!truthy(cond))
				return EvalFlow::Normal;
		}
	}
	if (starts_with(node.line, "for-statement"))
	{
		if (node.children.empty())
			return EvalFlow::Normal;
		size_t index = 0;
		if (starts_with(node.children[index].line, "for-init-statement"))
		{
			EvalFlow init_flow =
				eval_statement(parser, node.children[index], state, out);
			if (init_flow != EvalFlow::Normal)
				return init_flow;
			++index;
		}
		const Node* cond = NULL;
		const Node* iter = NULL;
		const Node* body = NULL;
		for (; index < node.children.size(); ++index)
		{
			if (starts_with(node.children[index].line, "condition"))
				cond = &node.children[index];
			else if (starts_with(node.children[index].line, "iteration"))
				iter = &node.children[index];
			else
				body = &node.children[index];
		}
		while (body != NULL)
		{
			if (cond != NULL)
			{
				ConstexprValue c;
				if (!eval_node(parser, *cond, state, c))
					return EvalFlow::Invalid;
				if (!truthy(c))
					return EvalFlow::Normal;
			}
			EvalFlow flow = eval_statement(parser, *body, state, out);
			if (flow == EvalFlow::Return)
				return flow;
			if (flow == EvalFlow::Invalid)
				return flow;
			if (flow == EvalFlow::Break)
				return EvalFlow::Normal;
			if (iter != NULL && !iter->children.empty() &&
			    !eval_node(parser, iter->children[0], state, out))
				return EvalFlow::Invalid;
		}
		return EvalFlow::Normal;
	}
	if (starts_with(node.line, "break-statement"))
		return EvalFlow::Break;
	if (starts_with(node.line, "continue-statement"))
		return EvalFlow::Continue;
	return EvalFlow::Invalid;
}

}  // namespace

bool Parser::try_evaluate_constexpr_call(Binding* function,
                                         const vector<Node>& args,
                                         ConstexprValue& out)
{
	EvalBudgetScope budget;
	EvalState arg_state;
	vector<ConstexprValue> values;
	for (size_t i = 0; i < args.size(); ++i)
	{
		ConstexprValue value;
		if (!eval_node(*this, args[i], arg_state, value))
			return false;
		values.push_back(value);
	}
	return try_evaluate_constexpr_call_values(function, values, out);
}

bool Parser::try_evaluate_constexpr_call_values(
	Binding* function,
	const vector<ConstexprValue>& args,
	ConstexprValue& out)
{
	EvalBudgetScope budget;
	EvalCallScope call_scope;
	if (!call_scope.ok())
		return false;
	if (function == NULL)
		return false;
	Binding* body_binding = function;
	map<Binding*, Node>::const_iterator found = function_bodies_.end();
	for (Binding* cur = function; cur != NULL; cur = cur->aliased_binding)
		{
			if (cur->kind != BindingKind::Function)
				break;
			if (!cur->is_constexpr &&
			    !cur->is_generated_default_constructor &&
			    !cur->is_generated_aggregate_constructor &&
			    !cur->is_defaulted)
				continue;
		found = function_bodies_.find(cur);
		if (found != function_bodies_.end())
		{
			body_binding = cur;
			break;
		}
	}
	if (found == function_bodies_.end() || body_binding == NULL)
		return false;
	const Node& fn = found->second;
	EvalState state;
	size_t arg_index = 0;
	size_t body_index = fn.children.size();
	for (size_t i = 0; i < fn.children.size(); ++i)
	{
		if (starts_with(fn.children[i].line, "compound-statement"))
		{
			body_index = i;
			break;
		}
		if (!starts_with(fn.children[i].line, "parameter "))
			continue;
		if (fn.children[i].binding != NULL &&
		    fn.children[i].binding->name == "this")
		{
			if (arg_index < args.size())
			{
				state.locals[fn.children[i].binding] = args[arg_index];
				++arg_index;
			}
			continue;
		}
		if (arg_index >= args.size())
			return false;
		if (fn.children[i].binding != NULL)
			state.locals[fn.children[i].binding] = args[arg_index];
		++arg_index;
	}
	if (body_index >= fn.children.size())
		return false;
	ConstexprValue result;
	EvalFlow flow = eval_statement(*this, fn.children[body_index], state, result);
	if (flow != EvalFlow::Return || !result.valid)
		return false;
	out = result;
	return true;
}

bool Parser::try_evaluate_constexpr_constructor(
	Binding* function,
	TypePtr object_type,
	const vector<ConstexprValue>& args,
	ConstexprValue& out)
{
	EvalBudgetScope budget;
	EvalCallScope call_scope;
	if (!call_scope.ok())
		return false;
	if (function == NULL)
		return false;
	Binding* body_binding = function;
	map<Binding*, Node>::const_iterator found = function_bodies_.end();
	for (Binding* cur = function; cur != NULL; cur = cur->aliased_binding)
		{
			if (cur->kind != BindingKind::Function)
				break;
			if (!cur->is_constexpr &&
			    !cur->is_generated_default_constructor &&
			    !cur->is_generated_aggregate_constructor &&
			    !cur->is_defaulted)
				continue;
		found = function_bodies_.find(cur);
		if (found != function_bodies_.end())
		{
			body_binding = cur;
			break;
		}
	}
	if (found == function_bodies_.end() || body_binding == NULL)
	{
		if (function->is_generated_default_constructor || function->is_defaulted)
		{
			if (args.size() == 1 && args[0].is_object)
			{
				out = args[0];
				return true;
			}
			if (!constexpr_zero_value_for_type(object_type, out))
				out = ConstexprValue::object(object_type);
			return out.valid;
		}
		return false;
	}
	const Node& fn = found->second;
	EvalState state;
	size_t arg_index = 0;
	size_t body_index = fn.children.size();
	Binding* this_binding = NULL;
	for (size_t i = 0; i < fn.children.size(); ++i)
	{
		if (starts_with(fn.children[i].line, "compound-statement"))
		{
			body_index = i;
			break;
		}
		if (!starts_with(fn.children[i].line, "parameter "))
			continue;
		Binding* parameter = fn.children[i].binding;
		bool this_parameter =
			(parameter != NULL && parameter->name == "this") ||
			starts_with(fn.children[i].line, "parameter this ");
		if (this_parameter)
		{
			if (parameter != NULL)
			{
				this_binding = parameter;
				ConstexprValue this_value = ConstexprValue::object(object_type);
				if ((function->is_generated_default_constructor ||
				     function->is_defaulted) &&
				    !constexpr_zero_value_for_type(object_type, this_value))
					return false;
				state.locals[parameter] = this_value;
			}
			continue;
		}
		if (arg_index >= args.size())
			return false;
		if (parameter != NULL)
			state.locals[parameter] = args[arg_index];
		++arg_index;
	}
	if (body_index >= fn.children.size())
		return false;
	if (this_binding == NULL &&
	    (function->is_generated_default_constructor || function->is_defaulted))
	{
		if (!constexpr_zero_value_for_type(object_type, out))
			out = ConstexprValue::object(object_type);
		return out.valid;
	}
	if (this_binding == NULL)
		return false;
	ConstexprValue ignored;
	EvalFlow flow = eval_statement(*this, fn.children[body_index], state, ignored);
	if (flow == EvalFlow::Return || flow == EvalFlow::Invalid)
		return false;
	map<Binding*, ConstexprValue>::const_iterator result =
		state.locals.find(this_binding);
	if (result == state.locals.end() || !result->second.is_object)
		return false;
	out = result->second;
	return true;
}

bool Parser::try_evaluate_constexpr_binding(Binding* binding,
                                            ConstexprValue& out)
{
	EvalBudgetScope budget;
	if (binding == NULL)
		return false;
	if (binding->has_constant)
	{
		out = ConstexprValue::integer(binding->constant_value);
		return true;
	}
	map<Binding*, Node>::const_iterator found =
		static_member_initializers_.find(binding);
	if (found == static_member_initializers_.end() &&
	    binding->aliased_binding != NULL)
		found = static_member_initializers_.find(binding->aliased_binding);
	if (found == static_member_initializers_.end())
	{
		for (map<Binding*, Node>::const_iterator it =
		     static_member_initializers_.begin();
		     it != static_member_initializers_.end();
		     ++it)
		{
			Binding* candidate = it->first;
			if (candidate != NULL &&
			    candidate->name == binding->name &&
			    candidate->owner == binding->owner &&
			    pa11::same_type(candidate->type, binding->type))
			{
				found = it;
				break;
			}
		}
	}
	if (found == static_member_initializers_.end())
		return false;
	EvalState state;
	if (!eval_node(*this, found->second, state, out))
		return false;
	return out.valid;
}

bool Parser::try_evaluate_constexpr_expr(const Node& node, ConstexprValue& out)
{
	EvalBudgetScope budget;
	EvalState state;
	return eval_node(*this, node, state, out);
}

void Parser::apply_constexpr_value(Expr& expr, const ConstexprValue& value)
{
	if (!value.valid || value.is_object || value.is_pointer)
		return;
	expr.constant_expression = true;
	expr.has_constant_value = true;
	expr.constant_value = value.int_value;
	expr.null_pointer_constant = value.int_value == 0 && !value.is_float;
	expr.node.has_constant_value = true;
	expr.node.constant_value = value.int_value;
	expr.node.token_text = value.is_float
		? format_float(value.float_value)
		: to_string(value.int_value);
}

}  // namespace internal
}  // namespace pa12
