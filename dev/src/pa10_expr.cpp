#include "pa10_parser_internal.h"

#include <stdexcept>

using namespace std;

namespace pa10 {
namespace internal {

Ast Parser::parse_statement()
{
	skip_attributes();
	if (simple(OP_LBRACE))
		return parse_compound_statement();
	if (simple(KW_IF))
		return parse_if_statement();
	if (simple(KW_SWITCH))
		return parse_switch_statement();
	if (simple(KW_WHILE))
		return parse_while_statement();
	if (simple(KW_DO))
		return parse_do_statement();
	if (simple(KW_FOR))
		return parse_for_statement();
	if (simple(KW_TRY))
		return parse_try_block();
	if (simple(KW_BREAK) || simple(KW_CONTINUE) || simple(KW_GOTO) ||
	    simple(KW_RETURN) || simple(KW_THROW))
		return parse_jump_statement();
	if ((identifier() && simple_at(pos_ + 1, OP_COLON)) ||
	    simple(KW_CASE) || simple(KW_DEFAULT))
		return parse_labeled_statement();
	return parse_expression_statement();
}

Ast Parser::parse_compound_statement()
{
	Ast node = make_ast("compound-statement");
	expect(OP_LBRACE);
	vector<string> pending_imports = pending_compound_type_imports_;
	vector<string> pending_names = pending_compound_type_names_;
	pending_compound_type_imports_.clear();
	pending_compound_type_names_.clear();
	push_scope();
	for (size_t i = 0; i < pending_imports.size(); ++i)
		import_class_member_types(pending_imports[i]);
	for (size_t i = 0; i < pending_names.size(); ++i)
		scopes_.back().types.insert(pending_names[i]);
	while (!consume(OP_RBRACE))
		add_child(node, parse_block_item());
	pop_scope();
	return node;
}

Ast Parser::parse_if_statement()
{
	expect(KW_IF);
	Ast node = make_ast("if-statement");
	expect(OP_LPAREN);
	add_child(node, parse_condition());
	expect(OP_RPAREN);
	Ast then_node = make_ast("then");
	add_child(then_node, parse_statement());
	add_child(node, then_node);
	if (consume(KW_ELSE))
	{
		Ast else_node = make_ast("else");
		add_child(else_node, parse_statement());
		add_child(node, else_node);
	}
	return node;
}

Ast Parser::parse_switch_statement()
{
	expect(KW_SWITCH);
	Ast node = make_ast("switch-statement");
	expect(OP_LPAREN);
	add_child(node, parse_condition());
	expect(OP_RPAREN);
	add_child(node, parse_statement());
	return node;
}

Ast Parser::parse_while_statement()
{
	expect(KW_WHILE);
	Ast node = make_ast("while-statement");
	expect(OP_LPAREN);
	add_child(node, parse_condition());
	expect(OP_RPAREN);
	add_child(node, parse_statement());
	return node;
}

Ast Parser::parse_do_statement()
{
	expect(KW_DO);
	Ast node = make_ast("do-statement");
	add_child(node, parse_statement());
	expect(KW_WHILE);
	expect(OP_LPAREN);
	Ast cond = make_ast("condition");
	add_child(cond, parse_expression());
	add_child(node, cond);
	expect(OP_RPAREN);
	expect(OP_SEMICOLON);
	return node;
}

Ast Parser::parse_for_statement()
{
	expect(KW_FOR);
	Ast node = make_ast("for-statement");
	expect(OP_LPAREN);
	Ast init = make_ast("for-init-statement");
	if (starts_declaration())
		add_child(init, parse_declaration());
	else
	{
		if (!simple(OP_SEMICOLON))
			add_child(init, parse_expression());
		expect(OP_SEMICOLON);
	}
	add_child(node, init);
	if (!simple(OP_SEMICOLON))
		add_child(node, parse_condition());
	expect(OP_SEMICOLON);
	if (!simple(OP_RPAREN))
	{
		Ast iter = make_ast("iteration");
		add_child(iter, parse_expression());
		add_child(node, iter);
	}
	expect(OP_RPAREN);
	add_child(node, parse_statement());
	return node;
}

Ast Parser::parse_try_block()
{
	expect(KW_TRY);
	Ast node = make_ast("try-block");
	add_child(node, parse_compound_statement());
	do
	{
		add_child(node, parse_handler());
	}
	while (simple(KW_CATCH));
	return node;
}

Ast Parser::parse_handler()
{
	expect(KW_CATCH);
	Ast node = make_ast("handler");
	expect(OP_LPAREN);
	add_child(node, parse_exception_declaration());
	expect(OP_RPAREN);
	add_child(node, parse_compound_statement());
	return node;
}

Ast Parser::parse_exception_declaration()
{
	Ast node = make_ast("exception-declaration");
	if (consume(OP_DOTS))
	{
		add_child(node, make_ast("ellipsis ..."));
		return node;
	}
	DeclParse specs = parse_decl_specifier_seq(false);
	add_child(node, specs.specs);
	if (!simple(OP_RPAREN))
	{
		DeclaratorParse decl = parse_declarator(true);
		if (!decl.node->children.empty())
			add_child(node, decl.node);
	}
	return node;
}

Ast Parser::parse_jump_statement()
{
	if (consume(KW_BREAK))
	{
		expect(OP_SEMICOLON);
		return make_ast("break-statement");
	}
	if (consume(KW_CONTINUE))
	{
		expect(OP_SEMICOLON);
		return make_ast("continue-statement");
	}
	if (consume(KW_GOTO))
	{
		string label = expect_identifier();
		expect(OP_SEMICOLON);
		return make_ast("goto-statement " + label);
	}
	if (consume(KW_THROW))
	{
		Ast node = make_ast("throw-statement");
		if (!simple(OP_SEMICOLON))
			add_child(node, parse_assignment_expression());
		expect(OP_SEMICOLON);
		return node;
	}
	expect(KW_RETURN);
	Ast node = make_ast("return-statement");
	if (!simple(OP_SEMICOLON))
		add_child(node, parse_expression());
	expect(OP_SEMICOLON);
	return node;
}

Ast Parser::parse_labeled_statement()
{
	if (consume(KW_CASE))
	{
		Ast node = make_ast("case-statement");
		add_child(node, parse_expression());
		expect(OP_COLON);
		add_child(node, parse_statement());
		return node;
	}
	if (consume(KW_DEFAULT))
	{
		Ast node = make_ast("default-statement");
		expect(OP_COLON);
		add_child(node, parse_statement());
		return node;
	}
	string label = expect_identifier();
	expect(OP_COLON);
	Ast node = make_ast("labeled-statement " + label);
	add_child(node, parse_statement());
	return node;
}

Ast Parser::parse_expression_statement()
{
	Ast node = make_ast("expression-statement");
	if (!simple(OP_SEMICOLON))
		add_child(node, parse_expression());
	expect(OP_SEMICOLON);
	return node;
}

Ast Parser::parse_condition()
{
	Ast node = make_ast("condition");
	if (starts_declaration())
	{
		size_t save = pos_;
		try
		{
			DeclParse specs = parse_decl_specifier_seq(false);
			DeclaratorParse decl = parse_declarator(false);
			if (simple(OP_ASS) || simple(OP_LBRACE))
			{
				Ast cd = make_ast("condition-declaration");
				add_child(cd, specs.specs);
				add_child(cd, decl.node);
				add_child(cd, parse_initializer());
				add_child(node, cd);
				return node;
			}
		}
		catch (const exception&)
		{
		}
		pos_ = save;
	}
	add_child(node, parse_expression());
	return node;
}

Ast Parser::parse_expression()
{
	Ast lhs = parse_assignment_expression();
	while (consume(OP_COMMA))
	{
		Ast rhs = parse_assignment_expression();
		Ast node = make_ast("binary-expression OP_COMMA:,");
		add_child(node, lhs);
		add_child(node, rhs);
		lhs = node;
	}
	return lhs;
}

Ast Parser::parse_assignment_expression()
{
	Ast lhs = parse_conditional_expression();
	ETokenType op = OP_ASS;
	if (is_assignment_operator(op))
	{
		string text = current().source;
		++pos_;
		Ast node = make_ast("assignment-expression " + op_leaf(op, text));
		add_child(node, lhs);
		add_child(node, parse_assignment_expression());
		return node;
	}
	return lhs;
}

Ast Parser::parse_conditional_expression()
{
	Ast cond = parse_binary_expression(1);
	if (consume(OP_QMARK))
	{
		Ast node = make_ast("conditional-expression");
		add_child(node, cond);
		add_child(node, parse_expression());
		expect(OP_COLON);
		add_child(node, parse_assignment_expression());
		return node;
	}
	return cond;
}

Ast Parser::parse_binary_expression(int min_prec)
{
	Ast lhs = parse_unary_expression();
	while (true)
	{
		ETokenType op = OP_PLUS;
		int prec = 0;
		if (!binary_operator(op, prec) || prec < min_prec)
			break;
		string text = current().source;
		if (op == OP_RSHIFT)
		{
			text = ">>";
			pos_ += 2;
		}
		else
			++pos_;
		Ast rhs = parse_binary_expression(prec + 1);
		lhs = make_binary(op, text, lhs, rhs);
	}
	return lhs;
}

bool Parser::is_assignment_operator(ETokenType& op) const
{
	if (current().kind != posttoken::TokenKind::Simple)
		return false;
	switch (current().type)
	{
	case OP_ASS:
	case OP_PLUSASS:
	case OP_MINUSASS:
	case OP_STARASS:
	case OP_DIVASS:
	case OP_MODASS:
	case OP_XORASS:
	case OP_BANDASS:
	case OP_BORASS:
	case OP_LSHIFTASS:
	case OP_RSHIFTASS:
		op = current().type;
		return true;
	default:
		return false;
	}
}

bool Parser::binary_operator(ETokenType& op, int& prec) const
{
	if (current().kind != posttoken::TokenKind::Simple)
		return false;
	if (expression_angle_stop_ > 0 && simple(OP_GT))
		return false;
	op = current().type;
	if (simple(OP_GT) && current().split_rshift &&
	    at(pos_ + 1).split_rshift &&
	    at(pos_ + 1).split_group == current().split_group)
		op = OP_RSHIFT;
	switch (op)
	{
	case OP_LOR: prec = 1; return true;
	case OP_LAND: prec = 2; return true;
	case OP_BOR: prec = 3; return true;
	case OP_XOR: prec = 4; return true;
	case OP_AMP: prec = 5; return true;
	case OP_EQ: case OP_NE: prec = 6; return true;
	case OP_LT: case OP_GT: case OP_LE: case OP_GE: prec = 7; return true;
	case OP_LSHIFT: case OP_RSHIFT: prec = 8; return true;
	case OP_PLUS: case OP_MINUS: prec = 9; return true;
	case OP_STAR: case OP_DIV: case OP_MOD: prec = 10; return true;
	case OP_DOTSTAR: case OP_ARROWSTAR: prec = 11; return true;
	default:
		return false;
	}
}

Ast Parser::parse_unary_expression()
{
	if (simple(OP_LPAREN))
	{
		Ast expr = parse_c_style_cast_or_parenthesized();
		if (expr->line == "parenthesized-expression")
			return parse_postfix_suffixes(expr);
		return expr;
	}
	if (simple(KW_STATIC_CAST) || simple(KW_DYNAMIC_CAST) ||
	    simple(KW_CONST_CAST) || simple(KW_REINTERPET_CAST))
		return parse_cast_expression();
	if (simple(KW_NEW) || (simple(OP_COLON2) && simple_at(pos_ + 1, KW_NEW)))
		return parse_new_expression();
	if (simple(KW_DELETE) || (simple(OP_COLON2) && simple_at(pos_ + 1, KW_DELETE)))
		return parse_delete_expression();
	if (simple(KW_SIZEOF))
		return parse_type_trait_expression(KW_SIZEOF);
	if (simple(KW_ALIGNOF))
		return parse_type_trait_expression(KW_ALIGNOF);
	if (simple(KW_NOEXCEPT))
		return parse_type_trait_expression(KW_NOEXCEPT);
	if (simple(KW_TYPEID))
		return parse_type_trait_expression(KW_TYPEID);
	if (simple(OP_INC) || simple(OP_DEC) || simple(OP_STAR) || simple(OP_AMP) ||
	    simple(OP_PLUS) || simple(OP_MINUS) || simple(OP_LNOT) || simple(OP_COMPL))
	{
		Token token = current();
		++pos_;
		Ast node = make_ast("unary-expression " + token_leaf(token));
		add_child(node, parse_unary_expression());
		return node;
	}
	return parse_postfix_expression();
}

Ast Parser::parse_postfix_expression()
{
	Ast expr = parse_primary_expression();
	return parse_postfix_suffixes(expr);
}

Ast Parser::parse_postfix_suffixes(Ast expr)
{
	while (true)
	{
		if (simple(OP_LPAREN))
		{
			Ast call = make_ast("call-expression");
			add_child(call, expr);
			add_child(call, parse_argument_list(
				expr->builtin_type_expression ? "paren-argument-list" :
				"argument-list",
				OP_RPAREN));
			expr = call;
			continue;
		}
		if (consume(OP_LSQUARE))
		{
			Ast node = make_ast("subscript-expression");
			add_child(node, expr);
			add_child(node, parse_expression());
			expect(OP_RSQUARE);
			expr = node;
			continue;
		}
		if (simple(OP_DOT) || simple(OP_ARROW))
		{
			Token token = current();
			++pos_;
			Ast node = make_ast("member-expression " + token_leaf(token));
			add_child(node, expr);
			if (consume(KW_TEMPLATE))
				add_child(node, make_ast("identifier " + parse_id_expression_text()));
			else
			{
				string name;
				if (consume(OP_COLON2))
					name = "::" + parse_unqualified_id_text(false);
				else
					name = parse_unqualified_id_text(false);
				add_child(node, make_ast("identifier " +
				                         parse_qualified_suffix_text(name)));
			}
			expr = node;
			continue;
		}
		if (simple(OP_INC) || simple(OP_DEC))
		{
			Token token = current();
			++pos_;
			Ast node = make_ast("postfix-expression " + token_leaf(token));
			add_child(node, expr);
			expr = node;
			continue;
		}
		break;
	}
	return expr;
}

Ast Parser::parse_primary_expression()
{
	if (literal())
		return make_ast("literal " + expect_literal());
	if (simple(KW_TRUE) || simple(KW_FALSE) || simple(KW_NULLPTR))
	{
		Token token = current();
		++pos_;
		return make_ast("keyword-literal " + token_leaf(token));
	}
	if (simple(KW_THIS))
	{
		Token token = current();
		++pos_;
		return make_ast("keyword-literal " + token_leaf(token));
	}
	if (simple(OP_LSQUARE))
		return parse_lambda_expression();
	if (simple(OP_LBRACE))
		return parse_braced_init_list();
	if (current().kind == posttoken::TokenKind::Simple &&
	    is_builtin_type(current().type))
	{
		string name = current().source;
		++pos_;
		Ast node = make_id_expression(name);
		node->builtin_type_expression = true;
		return node;
	}
	if (simple(KW_DECLTYPE))
	{
		size_t begin = pos_;
		++pos_;
		skip_balanced(OP_LPAREN, OP_RPAREN);
		string text = format_token_range(tokens_, begin, pos_);
		text = parse_qualified_suffix_text(text);
		return make_id_expression(text);
	}
	if (identifier() || simple(OP_COLON2) || simple(KW_OPERATOR) || simple(OP_COMPL))
		return make_id_expression(parse_id_expression_text());
	throw runtime_error("expected primary expression before '" + current().source + "'");
}

Ast Parser::parse_lambda_expression()
{
	Ast node = make_ast("lambda-expression");
	string intro = parse_balanced_text(OP_LSQUARE, OP_RSQUARE);
	add_child(node, make_ast("lambda-introducer " + intro));
	if (simple(OP_LPAREN))
	{
		Ast decl = make_ast("lambda-declarator");
		add_child(decl, parse_parameter_clause());
		if (simple(KW_MUTABLE))
		{
			add_child(decl, make_ast("lambda-specifier " + token_leaf(current())));
			++pos_;
		}
		parse_function_suffixes(decl);
		add_child(node, decl);
	}
	add_child(node, parse_compound_statement());
	return node;
}

Ast Parser::parse_cast_expression()
{
	ETokenType kw = current().type;
	string source = current().source;
	++pos_;
	Ast node = make_ast("cast-expression " + keyword_leaf(kw, source));
	expect(OP_LT);
	add_child(node, parse_type_id());
	if (!consume_close_angle())
		throw runtime_error("expected cast close angle");
	expect(OP_LPAREN);
	add_child(node, parse_expression());
	expect(OP_RPAREN);
	return node;
}

Ast Parser::parse_new_expression()
{
	Ast node = make_ast("new-expression");
	if (consume(OP_COLON2))
		add_child(node, make_ast("global-scope"));
	expect(KW_NEW);
	if (simple(OP_LPAREN) && !starts_parameter_declaration_at(pos_ + 1))
	{
		size_t begin = pos_;
		Ast args = parse_argument_list("paren-argument-list", OP_RPAREN);
		Ast placement = make_ast("placement " + format_token_range(tokens_, begin, pos_));
		add_child(placement, args);
		add_child(node, placement);
	}
	if (simple(OP_LPAREN))
	{
		expect(OP_LPAREN);
		add_child(node, parse_type_id());
		expect(OP_RPAREN);
	}
	else
		add_child(node, parse_type_id());
	if (simple(OP_LPAREN) || simple(OP_LBRACE))
	{
		Ast init = make_ast("initializer");
		if (simple(OP_LPAREN))
			add_child(init, parse_argument_list("paren-initializer", OP_RPAREN));
		else
			add_child(init, parse_braced_init_list());
		add_child(node, init);
	}
	return node;
}

Ast Parser::parse_delete_expression()
{
	Ast node = make_ast("delete-expression");
	consume(OP_COLON2);
	expect(KW_DELETE);
	if (consume(OP_LSQUARE))
	{
		expect(OP_RSQUARE);
		add_child(node, make_ast("array-delete"));
	}
	add_child(node, parse_unary_expression());
	return node;
}

Ast Parser::parse_type_trait_expression(ETokenType keyword)
{
	Token token = current();
	++pos_;
	if (keyword == KW_SIZEOF && !simple(OP_LPAREN))
	{
		Ast node = make_ast("sizeof-expression");
		add_child(node, parse_unary_expression());
		return node;
	}
	expect(OP_LPAREN);
	if (keyword == KW_SIZEOF &&
	    id_expression_call_follows(pos_))
	{
		Ast node = make_ast("sizeof-expression");
		add_child(node, parse_expression());
		expect(OP_RPAREN);
		return node;
	}
	if ((keyword == KW_SIZEOF || keyword == KW_ALIGNOF ||
	     keyword == KW_TYPEID) && starts_type_id())
	{
		Ast node = keyword == KW_SIZEOF ? make_ast("sizeof-expression") :
			make_ast("type-trait-expression " + token_leaf(token));
		add_child(node, parse_type_id());
		expect(OP_RPAREN);
		return node;
	}
	Ast node = keyword == KW_SIZEOF ? make_ast("sizeof-expression") :
		make_ast("type-trait-expression " + token_leaf(token));
	add_child(node, parse_expression());
	expect(OP_RPAREN);
	return node;
}

Ast Parser::parse_c_style_cast_or_parenthesized()
{
	size_t save = pos_;
	expect(OP_LPAREN);
	if (starts_type_id())
	{
		try
		{
			Ast type = parse_type_id();
			expect(OP_RPAREN);
			if (simple(OP_LPAREN) &&
			    type->type_id_has_qualified_name)
			{
				pos_ = save;
				throw runtime_error("not a c-style cast");
			}
			Ast node = make_ast("cast-expression OP_LPAREN:");
			add_child(node, type);
			add_child(node, parse_unary_expression());
			return node;
		}
		catch (const exception&)
		{
			pos_ = save;
		}
	}
	else
		pos_ = save;
	expect(OP_LPAREN);
	Ast node = make_ast("parenthesized-expression");
	add_child(node, parse_expression());
	expect(OP_RPAREN);
	return node;
}

Ast Parser::parse_argument_list(const string& node_name, ETokenType close)
{
	Ast node = make_ast(node_name);
	expect(close == OP_RPAREN ? OP_LPAREN : OP_LBRACE);
	if (!simple(close))
	{
		do
		{
			Ast arg = parse_assignment_expression();
			if (consume(OP_DOTS))
			{
				Ast pack = make_ast("pack-expansion-expression");
				add_child(pack, arg);
				arg = pack;
			}
			add_child(node, arg);
		}
		while (consume(OP_COMMA));
	}
	expect(close);
	return node;
}

}  // namespace internal
}  // namespace pa10
