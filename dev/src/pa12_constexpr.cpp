#include "pa12_internal.h"
#include "pa12_constexpr_eval.h"
#include "pa12_templates_function_support.h"
#include <cstdlib>
#include <limits>
#include <sstream>
using namespace std;
namespace pa12 {
namespace internal {
EvalState::EvalState() {}
namespace {
struct EvalBudget { int steps; int depth; EvalBudget() : steps(0), depth(0) {} };
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
	~EvalBudgetScope() { active_budget = previous; }
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
{ TypePtr bare = pa11::strip_cv(type); return bare->kind == pa11::TypeKind::Fundamental && (bare->fundamental == FT_FLOAT || bare->fundamental == FT_DOUBLE || bare->fundamental == FT_LONG_DOUBLE); }
bool starts_with(const string& text, const string& prefix)
{ return text.compare(0, prefix.size(), prefix) == 0; }
bool template_name_is(const string& name, const string& unqualified)
{
	if (name == unqualified)
		return true;
	if (name.size() <= unqualified.size() + 2)
		return false;
	size_t offset = name.size() - unqualified.size();
	return name.compare(offset, unqualified.size(), unqualified) == 0 &&
	       offset >= 2 &&
	       name.compare(offset - 2, 2, "::") == 0;
}
bool truthy(const ConstexprValue& value)
{ if (value.is_pointer) return value.pointer_binding != NULL || value.pointer_index != 0; return value.is_float ? value.float_value != 0 : value.int_value != 0; }
uint64_t integer_value(const ConstexprValue& value)
{ if (value.is_pointer) return static_cast<uint64_t>(value.pointer_index); return value.is_float ? static_cast<uint64_t>(value.float_value) : value.int_value; }
bool constexpr_integral_or_bool_type(TypePtr type)
{ TypePtr bare = type.get() != NULL ? pa11::strip_cv(type) : TypePtr(); return bare.get() != NULL && (pa11::is_integral_or_bool_type(bare) || bare->kind == pa11::TypeKind::Enum); }
bool constexpr_integral_unsigned(TypePtr type)
{
	TypePtr bare = type.get() != NULL
		? pa11::strip_cv(type) : TypePtr();
	if (bare.get() == NULL)
		return false;
	if (bare->kind == pa11::TypeKind::Enum)
	{
		switch (bare->enum_underlying)
		{
		case FT_UNSIGNED_CHAR:
		case FT_UNSIGNED_SHORT_INT:
		case FT_UNSIGNED_INT:
		case FT_UNSIGNED_LONG_INT:
		case FT_UNSIGNED_LONG_LONG_INT:
			return true;
		default:
			return false;
		}
	}
	if (bare->kind != pa11::TypeKind::Fundamental)
		return false;
	switch (bare->fundamental)
	{
	case FT_BOOL:
	case FT_UNSIGNED_CHAR:
	case FT_UNSIGNED_SHORT_INT:
	case FT_UNSIGNED_INT:
	case FT_UNSIGNED_LONG_INT:
	case FT_UNSIGNED_LONG_LONG_INT:
	case FT_CHAR16_T:
	case FT_CHAR32_T:
		return true;
	default:
		return false;
	}
}
unsigned constexpr_integral_bits(TypePtr type)
{ uint64_t bytes = pa11::type_size(pa11::strip_cv(type)); return bytes >= 8 ? 64 : static_cast<unsigned>(bytes * 8); }
uint64_t constexpr_integral_mask(unsigned bits)
{ return bits >= 64 ? ~uint64_t(0) : ((uint64_t(1) << bits) - 1); }
uint64_t constexpr_normalize_integral(TypePtr type, uint64_t value)
{ return value & constexpr_integral_mask(constexpr_integral_bits(type)); }
int64_t constexpr_signed_integral(TypePtr type, uint64_t value)
{
	unsigned bits = constexpr_integral_bits(type);
	uint64_t normalized = value & constexpr_integral_mask(bits);
	if (bits >= 64)
		return static_cast<int64_t>(normalized);
	uint64_t sign = uint64_t(1) << (bits - 1);
	if ((normalized & sign) == 0)
		return static_cast<int64_t>(normalized);
	return static_cast<int64_t>(normalized | ~constexpr_integral_mask(bits));
}
uint64_t constexpr_convert_integral(TypePtr source,
                                    TypePtr target,
                                    uint64_t value)
{
	if (source.get() != NULL &&
	    target.get() != NULL &&
	    constexpr_integral_or_bool_type(source) &&
	    constexpr_integral_or_bool_type(target) &&
	    !constexpr_integral_unsigned(source) &&
	    constexpr_integral_bits(target) > constexpr_integral_bits(source))
		return constexpr_normalize_integral(
			target,
			static_cast<uint64_t>(
				constexpr_signed_integral(source, value)));
	return constexpr_normalize_integral(target, value);
}
long double float_value(const ConstexprValue& value)
{ return value.is_float ? value.float_value : static_cast<long double>(value.int_value); }
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
bool is_array_type(TypePtr type)
{ return type.get() != NULL && pa11::strip_cv(type)->kind == pa11::TypeKind::Array; }
bool consume_eval_step()
{ if (active_budget == NULL) return true; ++active_budget->steps; return active_budget->steps <= kMaxEvalSteps; }
bool eval_node(Parser& parser,
               const Node& node,
               EvalState& state,
               ConstexprValue& out);
void append_constexpr_value_cache_key(ostringstream& out,
                                      const ConstexprValue& value)
{
	if (!value.valid)
	{
		out << "invalid";
		return;
	}
	if (value.is_object)
	{
		out << "obj:" << value.object_type.get() << '{';
		for (map<Binding*, ConstexprValue>::const_iterator it =
			     value.fields.begin();
		     it != value.fields.end();
		     ++it)
		{
			out << it->first << '=';
			append_constexpr_value_cache_key(out, it->second);
			out << ';';
		}
		out << "}[" << value.elements.size() << ':';
		for (size_t i = 0; i < value.elements.size(); ++i)
		{
			append_constexpr_value_cache_key(out, value.elements[i]);
			out << ';';
		}
		out << ']';
		return;
	}
	if (value.is_pointer)
	{
		out << "ptr:" << value.pointer_binding << ':' << value.pointer_index;
		return;
	}
	if (value.is_float)
	{
		out << "float:" << value.float_value;
		return;
	}
	out << "int:" << value.int_value;
}
	string constexpr_call_cache_key(Binding* function,
	                                const vector<ConstexprValue>& args)
	{
	ostringstream out;
	out << function;
	for (size_t i = 0; i < args.size(); ++i)
	{
		out << '|';
		append_constexpr_value_cache_key(out, args[i]);
		}
		return out.str();
	}
	bool constexpr_function_can_have_body(Binding* function)
	{
		return function != NULL &&
		       function->kind == BindingKind::Function &&
		       (function->is_constexpr ||
		        function->is_generated_default_constructor ||
		        function->is_generated_aggregate_constructor ||
		        function->is_defaulted);
	}
	bool bind_constexpr_function_arguments(const Node& fn,
	                                       const vector<ConstexprValue>& args,
	                                       EvalState& state,
	                                       size_t& body_index)
	{
		size_t arg_index = 0;
		body_index = fn.children.size();
		for (size_t i = 0; i < fn.children.size(); ++i)
		{
			const Node& child = fn.children[i];
			if (starts_with(child.line, "compound-statement"))
			{
				body_index = i;
				break;
			}
			if (!starts_with(child.line, "parameter "))
				continue;
			if (child.binding != NULL && child.binding->name == "this")
			{
				if (arg_index < args.size())
				{
					state.locals[child.binding] = args[arg_index];
					++arg_index;
				}
				continue;
			}
			if (arg_index >= args.size())
				return false;
			if (child.binding != NULL)
				state.locals[child.binding] = args[arg_index];
			++arg_index;
		}
		return body_index < fn.children.size();
	}
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

bool comparison_function_op(Binding* function, ETokenType& op)
{
	if (function == NULL)
		return false;
	if (function->name == "operator==")
		op = OP_EQ;
	else if (function->name == "operator!=")
		op = OP_NE;
	else if (function->name == "operator<")
		op = OP_LT;
	else if (function->name == "operator>")
		op = OP_GT;
	else if (function->name == "operator<=")
		op = OP_LE;
	else if (function->name == "operator>=")
		op = OP_GE;
	else
		return false;
	return true;
}

bool single_value_field(const ConstexprValue& object,
                        Binding*& field,
                        ConstexprValue& value)
{
	if (!object.is_object)
		return false;
	field = NULL;
	for (map<Binding*, ConstexprValue>::const_iterator it =
		     object.fields.begin();
	     it != object.fields.end();
	     ++it)
	{
		if (it->first == NULL || it->second.is_object || it->second.is_pointer)
			return false;
		if (field != NULL)
			return false;
		field = it->first;
		value = it->second;
	}
	return field != NULL;
}

bool try_eval_single_field_comparison(Binding* function,
                                      const vector<ConstexprValue>& args,
                                      ConstexprValue& out)
{
	ETokenType op = OP_PLUS;
	if (!comparison_function_op(function, op) || args.size() != 2)
		return false;
	Binding* left_field = NULL;
	Binding* right_field = NULL;
	ConstexprValue left;
	ConstexprValue right;
	if (!single_value_field(args[0], left_field, left) ||
	    !single_value_field(args[1], right_field, right))
		return false;
	TypePtr field_type = left_field->type;
	if (right_field != left_field &&
	    (right_field->type.get() == NULL ||
	     field_type.get() == NULL ||
	     !pa11::same_type(pa11::strip_cv(field_type),
	                      pa11::strip_cv(right_field->type))))
		return false;
	if (constexpr_integral_compare(op, field_type, left, right, out))
		return true;
	return eval_binary_value(op, left, right, out);
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
	if (type->kind != pa11::TypeKind::Record &&
	    node.children.size() == 1)
	{
		ConstexprValue child;
		if (!eval_node(parser, node.children[0], state, child) ||
		    child.is_object)
			return false;
		out = child;
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
	if (!node.dependent_value_name.empty() &&
	    parser.try_evaluate_dependent_value_node(node, out))
		return true;
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
	else if (constexpr_integral_or_bool_type(target))
	{
		TypePtr source = node.children[0].type;
		if (source.get() != NULL &&
		    (source->kind == pa11::TypeKind::LValueReference ||
		     source->kind == pa11::TypeKind::RValueReference))
			source = source->base;
		source = source.get() != NULL ? pa11::strip_cv(source) : TypePtr();
		out = ConstexprValue::integer(
			constexpr_convert_integral(source,
			                           target,
			                           integer_value(out)));
	}
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
	}  // namespace
	bool constexpr_eval_node(Parser& parser,
	                         const Node& node,
	                         EvalState& state,
	                         ConstexprValue& out)
	{
		return eval_node(parser, node, state, out);
	}
	bool constexpr_eval_variable_initializer(Parser& parser,
	                                         const Node& node,
	                                         EvalState& state,
	                                         ConstexprValue& out)
	{
		return eval_variable_initializer(parser, node, state, out);
	}
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
	bool Parser::try_evaluate_constexpr_call_values(Binding* function,
	                                                const vector<ConstexprValue>& args,
	                                                ConstexprValue& out)
	{
		EvalBudgetScope budget;
		EvalCallScope call_scope;
	if (!call_scope.ok())
		return false;
	if (function == NULL)
		return false;
	if (hosted_compatibility_ &&
	    try_eval_single_field_comparison(function, args, out))
		return true;
	string cache_key = constexpr_call_cache_key(function, args);
		map<string, ConstexprValue>::const_iterator cached =
			constexpr_call_result_cache_.find(cache_key);
		if (cached != constexpr_call_result_cache_.end())
		{
			out = cached->second;
			return true;
		}
		parse_pending_constexpr_function_bodies(function, false);
		for (Binding* cur = function; cur != NULL; cur = cur->aliased_binding)
		{
			if (cur->kind != BindingKind::Function)
				break;
			if (constexpr_function_can_have_body(cur))
				replay_bodyless_constexpr_template(cur);
		}
		Binding* body_binding = NULL;
		map<Binding*, Node>::const_iterator found = function_bodies_.end();
		if (!ensure_constexpr_function_body(function, body_binding, found))
			return false;
		const Node& fn = found->second;
		EvalState state;
		size_t body_index = 0;
		if (body_binding == NULL ||
		    !bind_constexpr_function_arguments(fn, args, state, body_index))
			return false;

		ConstexprValue result;
	EvalFlow flow = eval_statement(*this, fn.children[body_index], state, result);
	if (flow != EvalFlow::Return || !result.valid)
		return false;
	constexpr_call_result_cache_[cache_key] = result;
	out = result;
	return true;
}
bool Parser::try_evaluate_constexpr_constructor(Binding* function,
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
	for (Binding* cur = function; cur != NULL; cur = cur->aliased_binding)
	{
		if (cur->kind != BindingKind::Function)
			break;
		if (!cur->is_constexpr &&
		    !cur->is_generated_default_constructor &&
		    !cur->is_generated_aggregate_constructor &&
		    !cur->is_defaulted)
			continue;
		size_t extra_before = extra_lowir_nodes_.size();
		parse_pending_function_body(cur);
		parse_pending_member_body(cur);
		ensure_function_body_extra_node(cur);
		extra_lowir_nodes_.resize(extra_before);
	}
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
	if (binding->name == "value" &&
	    binding->owner != NULL &&
	    binding->owner->kind == ScopeKind::Class)
	{
		TypePtr owner = pa11::record_type_for_scope(binding->owner);
		owner = owner.get() != NULL ? pa11::strip_cv(owner) : TypePtr();
		map<const void*, vector<TemplateArgument> >::const_iterator args =
			owner.get() != NULL
			? record_template_arguments_.find(owner.get())
			: record_template_arguments_.end();
		if (hosted_compatibility_ &&
		    owner.get() != NULL &&
		    owner->kind == pa11::TypeKind::Record &&
		    template_name_is(owner->template_primary_name,
		                     "__is_nothrow_invocable") &&
		    args != record_template_arguments_.end())
		{
			vector<TypePtr> types;
			bool type_args = true;
			for (size_t i = 0; i < args->second.size(); ++i)
			{
				const TemplateArgument& arg = args->second[i];
				if (arg.kind == TemplateArgumentKind::Type)
					types.push_back(arg.type);
				else if (arg.kind == TemplateArgumentKind::Pack)
				{
					for (size_t j = 0; j < arg.pack.size(); ++j)
					{
						if (arg.pack[j].kind != TemplateArgumentKind::Type)
						{
							type_args = false;
							break;
						}
						types.push_back(arg.pack[j].type);
					}
				}
				else
					type_args = false;
				if (!type_args)
					break;
			}
			if (type_args)
			{
				bool value = is_invocable_type_trait(types, true);
				out = ConstexprValue::integer(value ? 1 : 0);
				return true;
			}
		}
	}
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

}  // namespace internal
}  // namespace pa12
