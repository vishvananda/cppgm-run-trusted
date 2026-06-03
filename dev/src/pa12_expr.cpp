#include "pa12_internal.h"

#include <cctype>
#include <stdexcept>

using namespace std;

namespace pa12 {
namespace internal {
namespace {

bool is_float_literal_text(const string& source)
{
	if (source.size() > 2 && source[0] == '0' &&
	    (source[1] == 'x' || source[1] == 'X'))
	{
		for (size_t i = 2; i < source.size(); ++i)
		{
			if (source[i] == '.' || source[i] == 'p' || source[i] == 'P')
				return true;
		}
		return false;
	}
	for (size_t i = 0; i < source.size(); ++i)
	{
		if (source[i] == '.' || source[i] == 'e' || source[i] == 'E' ||
		    source[i] == 'p' || source[i] == 'P')
			return true;
	}
	return false;
}

TypePtr floating_literal_type(const string& source)
{
	if (!source.empty())
	{
		char last = source[source.size() - 1];
		if (last == 'f' || last == 'F')
			return pa11::make_fundamental(FT_FLOAT);
		if (last == 'l' || last == 'L')
			return pa11::make_fundamental(FT_LONG_DOUBLE);
	}
	return pa11::make_fundamental(FT_DOUBLE);
}

bool type_is_nullptr(TypePtr type)
{
	TypePtr bare = pa11::strip_cv(type);
	return bare->kind == pa11::TypeKind::Fundamental &&
	       bare->fundamental == FT_NULLPTR_T;
}

bool type_is_pointer(TypePtr type)
{
	return pa11::strip_cv(type)->kind == pa11::TypeKind::Pointer;
}

size_t ordinary_string_elements(const string& source, size_t fallback)
{
	if (source.empty() || source[0] != '"')
		return fallback;
	vector<uint32_t> code_points;
	if (!DecodeOrdinaryBody(source, 1, source.size() - 1, code_points))
		return fallback;
	return code_points.size() + 1;
}

}  // namespace

Expr Parser::parse_expression()
{
	Expr lhs = parse_assignment_expression();
	while (consume(OP_COMMA))
	{
		Expr rhs = parse_assignment_expression();
		lhs = make_binary_expr(OP_COMMA, ",", lhs, rhs);
	}
	return lhs;
}

Expr Parser::parse_assignment_expression()
{
	Expr lhs = parse_conditional_expression();
	ETokenType op = OP_ASS;
	if (is_assignment_operator(op))
	{
		string text = current().source;
		++pos_;
		Expr rhs = parse_assignment_expression();
		return make_assignment_expr(op, text, lhs, rhs);
	}
	return lhs;
}

Expr Parser::parse_conditional_expression()
{
	Expr cond = parse_binary_expression(1);
	if (!consume(OP_QMARK))
		return cond;
	Expr yes = parse_expression();
	expect(OP_COLON);
	Expr no = parse_assignment_expression();
	TypePtr result_type = usual_arithmetic_type(yes.type, no.type);
	ValueCategory category = ValueCategory::PRValue;
	if (pa11::same_type(yes.type, no.type))
	{
		result_type = lvalue_to_rvalue_type(yes.type);
		if (yes.category == ValueCategory::LValue &&
		    no.category == ValueCategory::LValue)
		{
			result_type = yes.type;
			category = ValueCategory::LValue;
		}
	}
	else if (type_is_pointer(yes.type) && type_is_pointer(no.type))
	{
		if (pointer_conversion_viable(yes.type, no.type))
			result_type = lvalue_to_rvalue_type(no.type);
		else
			result_type = lvalue_to_rvalue_type(yes.type);
	}
	else if (type_is_nullptr(yes.type) && type_is_pointer(no.type))
		result_type = lvalue_to_rvalue_type(no.type);
	else if (type_is_pointer(yes.type) && type_is_nullptr(no.type))
		result_type = lvalue_to_rvalue_type(yes.type);
	else if (yes.null_pointer_constant && type_is_pointer(no.type))
		result_type = lvalue_to_rvalue_type(no.type);
	else if (type_is_pointer(yes.type) && no.null_pointer_constant)
		result_type = lvalue_to_rvalue_type(yes.type);

	Expr out;
	out.type = result_type;
	out.category = category;
	out.valid = true;
	out.constant_expression = cond.constant_expression &&
	                          yes.constant_expression &&
	                          no.constant_expression;
	if (cond.has_constant_value)
	{
		const Expr& selected = cond.constant_value != 0 ? yes : no;
		out.has_constant_value = selected.has_constant_value;
		out.constant_value = selected.constant_value;
		out.null_pointer_constant = selected.null_pointer_constant;
	}
	out.node = Node("conditional-expression " + value_category_name(category) +
	                " " + pa11::describe_type(result_type));
	add_child(out.node, cond.node);
	add_child(out.node, yes.node);
	add_child(out.node, no.node);
	annotate_expr_node(out);
	return out;
}

Expr Parser::parse_binary_expression(int min_prec)
{
	Expr lhs = parse_unary_expression();
	for (;;)
	{
		ETokenType op = OP_PLUS;
		int prec = 0;
		if (!binary_operator(op, prec) || prec < min_prec)
			break;
		string text = current().source;
		if (op == OP_RSHIFT && current().type == OP_GT)
		{
			text = ">>";
			pos_ += 2;
		}
		else
			++pos_;
		Expr rhs = parse_binary_expression(prec + 1);
		lhs = make_binary_expr(op, text, lhs, rhs);
	}
	return lhs;
}

Expr Parser::parse_unary_expression()
{
	if (at(OP_LPAREN))
		return parse_c_style_cast_or_parenthesized();
	if (at(KW_STATIC_CAST) || at(KW_CONST_CAST) ||
	    at(KW_REINTERPET_CAST) || at(KW_DYNAMIC_CAST))
		return parse_postfix_suffixes(parse_cast_expression());
	if (at(KW_SIZEOF) || at(KW_ALIGNOF))
		return parse_type_trait_expression(current().type);
	TypePtr target;
	if (expression_starts_type_name(target) && at(OP_LPAREN))
		return parse_postfix_suffixes(parse_functional_cast(target));
	if (at(OP_INC) || at(OP_DEC) || at(OP_STAR) || at(OP_AMP) ||
	    at(OP_PLUS) || at(OP_MINUS) || at(OP_LNOT) || at(OP_COMPL))
	{
		ETokenType op = current().type;
		string text = current().source;
		++pos_;
		return make_unary_expr(op, text, parse_unary_expression());
	}
	return parse_postfix_expression();
}

Expr Parser::parse_postfix_expression()
{
	return parse_postfix_suffixes(parse_primary_expression());
}

Expr Parser::parse_postfix_suffixes(Expr expr)
{
	for (;;)
	{
		if (consume(OP_LPAREN))
		{
			vector<Expr> args;
			if (!at(OP_RPAREN))
				args = parse_argument_list();
			expect(OP_RPAREN);
			expr = make_call_expr(expr, args);
		}
		else if (consume(OP_LSQUARE))
		{
			Expr rhs = parse_expression();
			expect(OP_RSQUARE);
			expr = make_subscript_expr(expr, rhs);
		}
		else if (consume(OP_DOT) || consume(OP_ARROW))
		{
			string op = tokens_[pos_ - 1].source;
			string name = consume_identifier();
			expr = make_member_expr(expr, name, op);
		}
		else if (at(OP_INC) || at(OP_DEC))
		{
			ETokenType op = current().type;
			string text = current().source;
			++pos_;
			expr = make_postfix_expr(op, text, expr);
		}
		else
			break;
	}
	return expr;
}

Expr Parser::parse_primary_expression()
{
	if (consume(KW_TRUE))
	{
		Expr out;
		out.type = pa11::make_fundamental(FT_BOOL);
		out.valid = true;
		out.constant_expression = true;
		out.has_constant_value = true;
		out.constant_value = 1;
		out.node = Node("literal prvalue bool KW_TRUE:true");
		out.node.token_text = "true";
		annotate_expr_node(out);
		return out;
	}
	if (consume(KW_FALSE))
	{
		Expr out;
		out.type = pa11::make_fundamental(FT_BOOL);
		out.valid = true;
		out.constant_expression = true;
		out.has_constant_value = true;
		out.constant_value = 0;
		out.node = Node("literal prvalue bool KW_FALSE:false");
		out.node.token_text = "false";
		annotate_expr_node(out);
		return out;
	}
	if (consume(KW_NULLPTR))
	{
		Expr out;
		out.type = pa11::make_fundamental(FT_NULLPTR_T);
		out.valid = true;
		out.constant_expression = true;
		out.has_constant_value = true;
		out.constant_value = 0;
		out.node = Node("literal prvalue nullptr_t KW_NULLPTR:nullptr");
		out.node.token_text = "nullptr";
		annotate_expr_node(out);
		return out;
	}
	if (consume(KW_THIS))
	{
		Binding* binding =
			pa11::lookup_unqualified(current_scope(), "this", pa11::LOOKUP_PARAMETER);
		if (binding == NULL)
			throw runtime_error("this outside member function");
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
	if (at_literal())
		return parse_literal_expression();
	if (consume(OP_LPAREN))
	{
		Expr inner = parse_expression();
		expect(OP_RPAREN);
		return inner;
	}
	return make_id_expr(parse_id_expression_name());
}

Expr Parser::parse_literal_expression()
{
	string source = consume_literal();
	Expr out;
	out.valid = true;
	if (!source.empty() && source[source.size() - 1] == '"')
	{
		StringLiteralInfo info;
		if (!AnalyzeStringLiteral(source, info))
			throw runtime_error("invalid string literal");
		TypePtr type = pa11::make_array(pa11::make_cv(pa11::make_fundamental(info.type),
		                                             pa11::CV_CONST),
		                                false,
		                                ordinary_string_elements(source,
		                                                         info.elements));
		out.type = type;
		out.category = ValueCategory::LValue;
		out.constant_expression = true;
		out.node = Node("literal lvalue " + pa11::describe_type(type) + " " + source);
		out.node.token_text = source;
		annotate_expr_node(out);
		return out;
	}
	if (is_float_literal_text(source))
	{
		out.type = floating_literal_type(source);
		out.constant_expression = true;
	}
	else if (!source.empty() && source[source.size() - 1] == '\'')
	{
		CharacterLiteralInfo info;
		if (!AnalyzeCharacterLiteral(source, false, info))
			throw runtime_error("invalid character literal");
		out.type = pa11::make_fundamental(info.type);
		out.constant_expression = true;
		out.has_constant_value = true;
		out.constant_value = info.code_point;
		out.null_pointer_constant = false;
	}
	else
	{
		IntegerLiteralInfo info;
		if (!AnalyzeIntegerLiteral(source, info))
			throw runtime_error("invalid integer literal");
		out.type = pa11::make_fundamental(info.type);
		out.constant_expression = true;
		out.has_constant_value = true;
		out.constant_value = info.value;
		out.null_pointer_constant = info.value == 0;
	}
	out.node = Node("literal prvalue " + pa11::describe_type(out.type) +
	                " " + source);
	out.node.token_text = source;
	annotate_expr_node(out);
	return out;
}

Expr Parser::parse_cast_expression()
{
	ETokenType kw = current().type;
	string text = current().source;
	++pos_;
	expect(OP_LT);
	TypePtr target = parse_type_id();
	expect(OP_GT);
	expect(OP_LPAREN);
	Expr inner = parse_expression();
	expect(OP_RPAREN);
	return make_cast_expr(target, op_leaf(kw, text), inner);
}

Expr Parser::parse_type_trait_expression(ETokenType keyword)
{
	const bool is_sizeof = keyword == KW_SIZEOF;
	++pos_;
	expect(OP_LPAREN);
	size_t save = pos_;
	uint64_t value = 0;
	try
	{
		TypePtr type = parse_type_id();
		expect(OP_RPAREN);
		value = is_sizeof ? pa11::type_size(type) : pa11::type_align(type);
	}
	catch (const exception&)
	{
		pos_ = save;
		Expr expr = parse_expression();
		expect(OP_RPAREN);
		TypePtr object_type = expression_object_type(expr.type);
		value = is_sizeof ? pa11::type_size(object_type) :
			pa11::type_align(object_type);
	}
	return make_sizeof_expr(value);
}

Expr Parser::parse_c_style_cast_or_parenthesized()
{
	size_t save = pos_;
	expect(OP_LPAREN);
	try
	{
		TypePtr target = parse_type_id();
		expect(OP_RPAREN);
		Expr inner = parse_unary_expression();
		return make_cast_expr(target, "OP_LPAREN:", inner);
	}
	catch (const exception&)
	{
		pos_ = save;
		expect(OP_LPAREN);
		Expr inner = parse_expression();
		expect(OP_RPAREN);
		return parse_postfix_suffixes(inner);
	}
}

Expr Parser::parse_functional_cast(TypePtr target)
{
	expect(OP_LPAREN);
	if (consume(OP_RPAREN))
	{
		Expr zero;
		zero.type = target;
		zero.valid = true;
		zero.constant_expression = true;
		if (pa11::is_integral_or_bool_type(target))
		{
			zero.has_constant_value = true;
			zero.constant_value = 0;
		}
		zero.node = Node("literal prvalue " + pa11::describe_type(target) + " 0");
		zero.node.token_text = "0";
		annotate_expr_node(zero);
		return zero;
	}
	Expr inner = parse_expression();
	expect(OP_RPAREN);
	return make_cast_expr(target, "", inner);
}

vector<Expr> Parser::parse_argument_list()
{
	vector<Expr> args;
	for (;;)
	{
		args.push_back(parse_assignment_expression());
		if (!consume(OP_COMMA))
			break;
	}
	return args;
}

}  // namespace internal
}  // namespace pa12
