#include "pa12_internal.h"

#include <algorithm>
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
		Expr rhs = at(OP_LBRACE)
			? parse_braced_init_list()
			: parse_assignment_expression();
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
	else if (yes.category == ValueCategory::LValue &&
	         no.category == ValueCategory::LValue &&
	         pa11::strip_cv(expression_object_type(yes.type))->kind ==
	             pa11::TypeKind::Record &&
	         pa11::strip_cv(expression_object_type(no.type))->kind ==
	             pa11::TypeKind::Record)
	{
		TypePtr y = expression_object_type(yes.type);
		TypePtr n = expression_object_type(no.type);
		if (record_base_distance(n, y) < 1000000)
		{
			result_type = y;
			category = ValueCategory::LValue;
		}
		else if (record_base_distance(y, n) < 1000000)
		{
			result_type = n;
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
	if (at(OP_COLON2) && lookahead(KW_NEW, 1))
		return parse_new_expression();
	if (at(KW_NEW))
		return parse_new_expression();
	if (at(OP_COLON2) && lookahead(KW_DELETE, 1))
		return parse_delete_expression();
	if (at(KW_DELETE))
		return parse_delete_expression();
	TypePtr target;
	if (expression_starts_type_name(target))
	{
		if (at(OP_LPAREN))
			return parse_postfix_suffixes(parse_functional_cast(target));
		if (at(OP_LBRACE))
		{
			Expr init = parse_braced_init_list();
			init.type = target;
			init.category = ValueCategory::PRValue;
			if (pa11::strip_cv(target)->kind == pa11::TypeKind::Record)
			{
				Binding* ctor = ensure_default_constructor(target, true);
				if (init.node.children.empty())
					init.node.direct_call = ctor;
				bool force_dtor =
					pa11::strip_cv(target)->base.get() != NULL;
				ensure_default_destructor(target, force_dtor);
			}
			annotate_expr_node(init);
			return parse_postfix_suffixes(init);
		}
	}
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
	if (at_identifier() && lookahead(OP_LPAREN, 1))
	{
		QualifiedName name = parse_id_expression_name();
		expect(OP_LPAREN);
		vector<Expr> args;
		if (!at(OP_RPAREN))
			args = parse_argument_list();
		expect(OP_RPAREN);
		Expr callee;
		bool have_ordinary = false;
		try
		{
			callee = make_id_expr(name);
			have_ordinary = true;
		}
		catch (const runtime_error&)
		{
			if (name.qualified)
				throw;
		}
		bool ordinary_member =
			have_ordinary &&
			callee.node.line.compare(0, 17, "member-expression") == 0;
		if (!name.qualified && !ordinary_member)
		{
			vector<Binding*> candidates =
				have_ordinary ? callee.overloads : vector<Binding*>();
			set<Scope*> hidden_seen;
			set<Scope*> namespace_seen;
			for (size_t i = 0; i < args.size(); ++i)
			{
				collect_associated_hidden_friends(args[i].type,
				                                  name.name,
				                                  hidden_seen,
				                                  candidates);
				collect_associated_namespace_functions(args[i].type,
				                                       name.name,
				                                       namespace_seen,
				                                       candidates);
			}
			for (size_t i = 0; i < candidates.size();)
			{
				if (find(candidates.begin(), candidates.begin() + i,
				         candidates[i]) != candidates.begin() + i)
					candidates.erase(candidates.begin() + i);
				else
					++i;
			}
			if (!candidates.empty())
			{
				callee.valid = true;
				callee.binding = candidates[0];
				callee.type = candidates[0]->type;
				callee.category = ValueCategory::LValue;
				callee.overloads = candidates;
				callee.node = Node("id-expression lvalue " +
				                   pa11::describe_type(callee.type) + " " +
				                   candidates[0]->name);
				annotate_expr_node(callee);
			}
		}
		if (!callee.valid)
			throw runtime_error("name not found");
		return parse_postfix_suffixes(make_call_expr(callee, args));
	}
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
			if (at(OP_COMPL))
			{
				++pos_;
				consume_identifier();
				expect(OP_LPAREN);
				expect(OP_RPAREN);
				Expr out;
				out.valid = true;
				out.type = pa11::make_fundamental(FT_VOID);
				out.category = ValueCategory::PRValue;
				out.node = Node("pseudo-destructor-expression prvalue void");
				TypePtr object = expression_object_type(expr.type);
				if (op == "->")
					object = pointee_type_for_member(object);
				TypePtr record = pa11::strip_cv(object);
				if (record->kind == pa11::TypeKind::Record &&
				    record->scope != NULL)
				{
					string dtor_name = "~" + record->scope->name;
					Binding* dtor = pa11::lookup_qualified(record->scope,
					                                       dtor_name,
					                                       pa11::LOOKUP_FUNCTION);
					out.node.direct_call = dtor;
				}
				out.node.has_op = true;
				out.node.op = op == "->" ? OP_ARROW : OP_DOT;
				add_child(out.node, expr.node);
				annotate_expr_node(out);
				expr = out;
				continue;
			}
			string name = at(KW_OPERATOR)
				? consume_operator_function_name()
				: consume_identifier();
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

Expr Parser::parse_new_expression()
{
	if (consume(OP_COLON2))
	{
	}
	expect(KW_NEW);
	Expr placement;
	bool have_placement = false;
	if (consume(OP_LPAREN))
	{
		vector<Expr> args;
		if (!at(OP_RPAREN))
			args = parse_argument_list();
		expect(OP_RPAREN);
		if (args.size() != 1)
			throw runtime_error("unsupported placement new");
		placement = args[0];
		have_placement = true;
	}
	TypePtr type;
	if (!try_parse_type_name(type))
	{
		if (!at_simple_builtin() && !at_simple_cv())
			throw runtime_error("expected new type");
		DeclSpecs specs = parse_decl_specifier_seq(false);
		type = type_from_decl_specs(specs);
	}
	bool array_new = false;
	Expr bound;
	if (consume(OP_LSQUARE))
	{
		array_new = true;
		bound = parse_expression();
		expect(OP_RSQUARE);
	}
	vector<Expr> args;
	bool have_initializer_parens = false;
	if (consume(OP_LPAREN))
	{
		have_initializer_parens = true;
		if (!at(OP_RPAREN))
			args = parse_argument_list();
		expect(OP_RPAREN);
	}
	TypePtr record = pa11::strip_cv(type);
	Binding* ctor = NULL;
	if (!array_new && record->kind == pa11::TypeKind::Record && record->scope != NULL)
	{
		map<string, vector<Binding*> >::const_iterator found =
			record->scope->members.find(record->scope->name);
		if (found != record->scope->members.end())
		{
			for (size_t i = 0; i < found->second.size(); ++i)
			{
				Binding* candidate = found->second[i];
				if (candidate->kind == BindingKind::Function &&
				    candidate->type->parameters.size() == args.size() + 1)
				{
					ctor = candidate;
					break;
				}
			}
		}
	if (ctor == NULL)
			throw runtime_error("no matching constructor");
	}
	Binding* opnew = NULL;
	if (have_placement)
	{
		vector<Binding*> news =
			lookup_unqualified_set(current_scope(), "operatornew", pa11::LOOKUP_FUNCTION);
		for (size_t i = 0; i < news.size(); ++i)
		{
			if (news[i]->type->parameters.size() == 2)
			{
				opnew = news[i];
				break;
			}
		}
	}
	Expr out;
	out.valid = true;
	out.binding = opnew;
	out.type = pa11::make_pointer(type);
	out.category = ValueCategory::PRValue;
	out.node = Node(string("new-expression prvalue ") +
	                pa11::describe_type(out.type) +
	                (array_new ? " array" : ""));
	out.node.direct_call = ctor;
	out.node.binding = opnew;
	if (have_initializer_parens)
		out.node.token_text = "paren-init";
	if (have_placement)
		add_child(out.node, placement.node);
	if (array_new)
		add_child(out.node, bound.node);
	for (size_t i = 0; i < args.size(); ++i)
		add_child(out.node, args[i].node);
	annotate_expr_node(out);
	return out;
}

Expr Parser::parse_delete_expression()
{
	consume(OP_COLON2);
	expect(KW_DELETE);
	bool array_delete = false;
	if (consume(OP_LSQUARE))
	{
		expect(OP_RSQUARE);
		array_delete = true;
	}
	Expr operand = parse_unary_expression();
	TypePtr ptr_type = pa11::strip_cv(expression_object_type(operand.type));
	if (ptr_type->kind != pa11::TypeKind::Pointer)
		throw runtime_error("delete operand is not pointer");
	QualifiedName opname;
	opname.name = array_delete ? "operatordelete[]" : "operatordelete";
	opname.spelling = array_delete ? "::operatordelete[]" : "::operatordelete";
	opname.qualified = true;
	opname.qualifier = global_scope();
	Expr op = make_builtin_id_expr(opname);
	if (!op.valid || op.binding == NULL)
		throw runtime_error("operator delete not found");
	Expr out;
	out.valid = true;
	out.binding = op.binding;
	out.type = pa11::make_fundamental(FT_VOID);
	out.category = ValueCategory::PRValue;
	out.node = Node(string("delete-expression prvalue void") +
	                (array_delete ? " array" : ""));
	out.node.binding = op.binding;
	add_child(out.node, operand.node);
	annotate_expr_node(out);
	return out;
}

Expr Parser::parse_literal_expression()
{
	string source = consume_literal();
	Expr out;
	out.valid = true;
	if (!source.empty() && source[0] == '"' &&
	    !(source.size() >= 2 && source[source.size() - 1] == '"'))
	{
		size_t close = source.rfind('"');
		if (close == string::npos || close == 0)
			throw runtime_error("invalid string literal");
		string quoted = source.substr(0, close + 1);
		string suffix = source.substr(close + 1);
		QualifiedName name;
		name.name = "operator\"\"" + suffix;
		name.spelling = name.name;
		Expr callee = make_id_expr(name);
		StringLiteralInfo info;
		if (!AnalyzeStringLiteral(quoted, info))
			throw runtime_error("invalid string literal");
		Expr text;
		text.valid = true;
		text.type = pa11::make_array(pa11::make_cv(pa11::make_fundamental(info.type),
		                                          pa11::CV_CONST),
		                             false,
		                             ordinary_string_elements(quoted,
		                                                      info.elements));
		text.category = ValueCategory::LValue;
		text.constant_expression = true;
		text.node = Node("literal lvalue " + pa11::describe_type(text.type) +
		                 " " + quoted);
		text.node.token_text = quoted;
		annotate_expr_node(text);
		Expr size;
		size.valid = true;
		size.type = pa11::make_fundamental(FT_INT);
		size.category = ValueCategory::PRValue;
		size.constant_expression = true;
		size.has_constant_value = true;
		size.constant_value = ordinary_string_elements(quoted, info.elements) - 1;
		size.node = Node("literal prvalue int " +
		                 to_string(size.constant_value));
		size.node.token_text = to_string(size.constant_value);
		annotate_expr_node(size);
		vector<Expr> args;
		args.push_back(text);
		args.push_back(size);
		return make_call_expr(callee, args);
	}
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
	if (pa11::strip_cv(target)->kind == pa11::TypeKind::Record)
	{
		Expr init;
		init.valid = true;
		init.type = target;
		init.category = ValueCategory::PRValue;
		init.braced_init_list = true;
		init.node = Node("braced-init-list");
		if (!consume(OP_RPAREN))
		{
			vector<Expr> args = parse_argument_list();
			for (size_t i = 0; i < args.size(); ++i)
				add_child(init.node, args[i].node);
			expect(OP_RPAREN);
		}
		else
		{
			init.node.direct_call = ensure_default_constructor(target, true);
			bool force_dtor =
				pa11::strip_cv(target)->base.get() != NULL;
			ensure_default_destructor(target, force_dtor);
		}
		annotate_expr_node(init);
		return init;
	}
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

Expr Parser::parse_braced_init_list()
{
	expect(OP_LBRACE);
	Expr init;
	init.valid = true;
	init.braced_init_list = true;
	init.node = Node("braced-init-list");
	while (!at(OP_RBRACE))
	{
		if (at(OP_LBRACE))
			add_child(init.node, parse_braced_init_list().node);
		else
		{
			Expr child = parse_assignment_expression();
			if (child.category == ValueCategory::PRValue)
			{
				TypePtr object =
					pa11::strip_cv(expression_object_type(child.type));
				if (object->kind == pa11::TypeKind::Record &&
				    object->base.get() != NULL)
					ensure_default_destructor(object, true);
			}
			add_child(init.node, child.node);
		}
		if (!consume(OP_COMMA))
			break;
	}
	expect(OP_RBRACE);
	return init;
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
