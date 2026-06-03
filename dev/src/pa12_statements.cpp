#include "pa12_internal.h"

#include <stdexcept>

using namespace std;

namespace pa12 {
namespace internal {

void Parser::parse_function_body(Binding* function,
                                 const Declarator& declarator,
                                 Node& function_node)
{
	if (function_node.children.empty())
		throw runtime_error("missing function node");
	Node& fn = function_node.children.back();
	Scope* function_scope =
		pa11::create_child_scope(current_scope(), ScopeKind::Function, function->name);
	const Suffix* suffix = declarator_function_suffix(declarator);
	if (suffix != NULL)
	{
		for (size_t i = 0; i < suffix->parameters.size(); ++i)
		{
			string name = suffix->parameters[i].name;
			if (!name.empty())
			{
				pa11::add_binding(function_scope,
				                  BindingKind::Parameter,
				                  name,
				                  suffix->parameters[i].type);
				add_child(fn, Node("parameter " + name + " " +
				                   pa11::describe_type(suffix->parameters[i].type)));
			}
			else
				add_child(fn, Node("parameter  " +
				                   pa11::describe_type(suffix->parameters[i].type)));
		}
	}
	scopes_.push_back(function_scope);
	function_returns_.push_back(function->type->base);
	add_child(fn, parse_compound_statement());
	function_returns_.pop_back();
	scopes_.pop_back();
}

Node Parser::parse_compound_statement()
{
	expect(OP_LBRACE);
	Node node("compound-statement");
	Scope* block = pa11::create_child_scope(current_scope(), ScopeKind::Block, "");
	scopes_.push_back(block);
	while (!at(OP_RBRACE))
	{
		Node item = parse_block_item();
		if (!item.line.empty())
			add_child(node, item);
	}
	scopes_.pop_back();
	expect(OP_RBRACE);
	return node;
}

Node Parser::parse_block_item()
{
	if (at(KW_USING))
	{
		Node node("compound-statement-placeholder");
		parse_using_family(node);
		if (node.children.empty())
			return Node();
		return node.children[0];
	}
	if (at(KW_NAMESPACE))
	{
		Node node;
		parse_namespace_or_alias(node);
		return Node();
	}
	if (starts_declaration())
	{
		size_t save = pos_;
		try
		{
			Node node;
			parse_simple_or_function_declaration(node, true);
			if (!node.children.empty())
				return node.children[0];
			return Node();
		}
		catch (const exception&)
		{
			pos_ = save;
		}
	}
	return parse_statement();
}

Node Parser::parse_statement()
{
	if (at(OP_LBRACE))
		return parse_compound_statement();
	if (at(KW_IF))
		return parse_if_statement();
	if (at(KW_SWITCH))
		return parse_switch_statement();
	if (at(KW_WHILE))
		return parse_while_statement();
	if (at(KW_DO))
		return parse_do_statement();
	if (at(KW_FOR))
		return parse_for_statement();
	if (at(KW_RETURN) || at(KW_BREAK) || at(KW_CONTINUE))
		return parse_jump_statement();
	if ((at_identifier() && lookahead(OP_COLON, 1)) ||
	    at(KW_CASE) || at(KW_DEFAULT))
		return parse_labeled_statement();
	return parse_expression_statement();
}

Node Parser::parse_if_statement()
{
	expect(KW_IF);
	Node node("if-statement");
	expect(OP_LPAREN);
	add_child(node, parse_condition());
	expect(OP_RPAREN);
	Node then_node("then");
	add_child(then_node, parse_statement());
	add_child(node, then_node);
	if (consume(KW_ELSE))
	{
		Node else_node("else");
		add_child(else_node, parse_statement());
		add_child(node, else_node);
	}
	return node;
}

Node Parser::parse_switch_statement()
{
	expect(KW_SWITCH);
	Node node("switch-statement");
	expect(OP_LPAREN);
	add_child(node, parse_condition());
	expect(OP_RPAREN);
	add_child(node, parse_statement());
	return node;
}

Node Parser::parse_while_statement()
{
	expect(KW_WHILE);
	Node node("while-statement");
	expect(OP_LPAREN);
	add_child(node, parse_condition());
	expect(OP_RPAREN);
	add_child(node, parse_statement());
	return node;
}

Node Parser::parse_do_statement()
{
	expect(KW_DO);
	Node node("do-statement");
	add_child(node, parse_statement());
	expect(KW_WHILE);
	expect(OP_LPAREN);
	Node cond("condition");
	add_child(cond, parse_expression().node);
	add_child(node, cond);
	expect(OP_RPAREN);
	expect(OP_SEMICOLON);
	return node;
}

Node Parser::parse_for_statement()
{
	expect(KW_FOR);
	Node node("for-statement");
	expect(OP_LPAREN);
	Node init("for-init-statement");
	if (starts_declaration())
		add_child(init, parse_block_item());
	else
	{
		if (!at(OP_SEMICOLON))
			add_child(init, parse_expression().node);
		expect(OP_SEMICOLON);
	}
	add_child(node, init);
	if (!at(OP_SEMICOLON))
		add_child(node, parse_condition());
	expect(OP_SEMICOLON);
	if (!at(OP_RPAREN))
	{
		Node iter("iteration");
		add_child(iter, parse_expression().node);
		add_child(node, iter);
	}
	expect(OP_RPAREN);
	add_child(node, parse_statement());
	return node;
}

Node Parser::parse_jump_statement()
{
	if (consume(KW_BREAK))
	{
		expect(OP_SEMICOLON);
		return Node("break-statement");
	}
	if (consume(KW_CONTINUE))
	{
		expect(OP_SEMICOLON);
		return Node("continue-statement");
	}
	expect(KW_RETURN);
	Node node("return-statement");
	if (!at(OP_SEMICOLON))
	{
		Expr expr = parse_expression();
		TypePtr result = current_return_type();
		if (result.get() != NULL && !pa11::is_void_type(result))
		{
			Conversion conv = convert_to(expr, result);
			if (!conv.viable)
				throw runtime_error("invalid return conversion");
			expr = conv.expr;
		}
		add_child(node, expr.node);
	}
	expect(OP_SEMICOLON);
	return node;
}

Node Parser::parse_labeled_statement()
{
	if (consume(KW_CASE))
	{
		Node node("case-statement");
		add_child(node, parse_expression().node);
		expect(OP_COLON);
		add_child(node, parse_block_item());
		return node;
	}
	if (consume(KW_DEFAULT))
	{
		Node node("default-statement");
		expect(OP_COLON);
		add_child(node, parse_block_item());
		return node;
	}
	string label = consume_identifier();
	expect(OP_COLON);
	Node node("labeled-statement " + label);
	add_child(node, parse_statement());
	return node;
}

Node Parser::parse_expression_statement()
{
	Node node("expression-statement");
	if (!at(OP_SEMICOLON))
		add_child(node, parse_expression().node);
	expect(OP_SEMICOLON);
	return node;
}

Node Parser::parse_condition()
{
	Node node("condition");
	if (starts_declaration())
	{
		size_t save = pos_;
		try
		{
			DeclSpecs specs = parse_decl_specifier_seq(false);
			TypePtr base = type_from_decl_specs(specs);
			Declarator declarator = parse_declarator(false);
			if (consume(OP_ASS))
			{
				Expr init = parse_expression();
				Node wrapper("condition-declaration");
				declare_one(specs, base, declarator, &init, false, wrapper);
				if (!wrapper.children.empty())
					add_child(node, wrapper);
				return node;
			}
		}
		catch (const exception&)
		{
		}
		pos_ = save;
	}
	add_child(node, parse_expression().node);
	return node;
}

}  // namespace internal
}  // namespace pa12
