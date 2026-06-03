#include "pa10_internal.h"

#include <stdexcept>

using namespace std;

namespace pa10 {
namespace internal {

Ast Parser::parse_simple_or_function_declaration(bool member_context)
{
	DeclParse specs = parse_decl_specifier_seq(false);
	if (simple(OP_SEMICOLON))
	{
		expect(OP_SEMICOLON);
		Ast node = make_ast("simple-declaration");
		add_child(node, specs.specs);
		return node;
	}
	DeclaratorParse declarator = parse_declarator(false);

	if ((simple(OP_LBRACE) || simple(OP_COLON)) && declarator.has_parameter_clause)
	{
		Ast node = make_ast("function-definition");
		add_child(node, specs.specs);
		add_child(node, declarator.node);
		if (consume(OP_COLON))
		{
			--pos_;
			Ast ctor = make_ast("ctor-initializer");
			expect(OP_COLON);
			do
			{
				Ast mem = make_ast("mem-initializer");
				add_child(mem, make_ast("mem-initializer-id " + parse_type_name_text()));
				if (simple(OP_LPAREN))
					add_child(mem, parse_argument_list("paren-argument-list", OP_RPAREN));
				else
					add_child(mem, parse_braced_init_list());
				add_child(ctor, mem);
			}
			while (consume(OP_COMMA));
			add_child(node, ctor);
		}
		add_child(node, parse_compound_statement());
		if (!declarator.name.empty())
			add_value_name(declarator.name);
		return node;
	}

	Ast list = make_ast("init-declarator-list");
	Ast first = make_ast("init-declarator");
	add_child(first, declarator.node);
	if (simple(OP_ASS) && simple_at(pos_ + 1, KW_DEFAULT))
	{
		consume(OP_ASS);
		consume(KW_DEFAULT);
		add_child(first, make_ast("initializer"));
		first->children.back()->children.push_back(make_ast("special-initializer default"));
	}
	else if (simple(OP_ASS) || simple(OP_LBRACE) || simple(OP_LPAREN))
		add_child(first, parse_initializer());
	add_child(list, first);
	if (!declarator.name.empty() && !specs.has_typedef)
		add_value_name(declarator.name);
	if (specs.has_typedef && !declarator.name.empty())
		add_type_name(declarator.name);

	while (consume(OP_COMMA))
	{
		DeclaratorParse next = parse_declarator(false);
		Ast item = make_ast("init-declarator");
		add_child(item, next.node);
		if (simple(OP_ASS) || simple(OP_LBRACE) || simple(OP_LPAREN))
			add_child(item, parse_initializer());
		add_child(list, item);
		if (!next.name.empty() && !specs.has_typedef)
			add_value_name(next.name);
		if (specs.has_typedef && !next.name.empty())
			add_type_name(next.name);
	}
	expect(OP_SEMICOLON);

	Ast node = make_ast("simple-declaration");
	add_child(node, specs.specs);
	add_child(node, list);
	(void)member_context;
	return node;
}

Ast Parser::parse_member_declaration()
{
	skip_attributes();
	if (current().kind == posttoken::TokenKind::Simple &&
	    is_access_specifier(current().type) && simple_at(pos_ + 1, OP_COLON))
	{
		Ast node = make_ast("access-specifier " + token_leaf(current()));
		++pos_;
		expect(OP_COLON);
		return node;
	}
	if (consume(OP_SEMICOLON))
		return make_ast("empty-declaration");
	if (simple(KW_TEMPLATE))
		return parse_template_declaration();
	if (simple(KW_USING))
		return parse_using();
	if (simple(KW_STATIC_ASSERT))
		return parse_static_assert_declaration();
	if ((simple(KW_STRUCT) || simple(KW_CLASS) || simple(KW_UNION)) &&
	    !simple_at(pos_ + 1, OP_LBRACE))
		return parse_class_declaration();
	if (simple(KW_ENUM))
		return parse_enum_declaration();
	if (starts_special_member())
	{
		size_t save = pos_;
		try
		{
			return parse_special_member(true);
		}
		catch (const exception&)
		{
			pos_ = save;
		}
	}

	size_t save = pos_;
	DeclParse specs = parse_decl_specifier_seq(false);
	if (simple(OP_COLON) || (identifier() && simple_at(pos_ + 1, OP_COLON)))
		return parse_bit_field_declaration(specs);
	pos_ = save;
	return parse_simple_or_function_declaration(true);
}

Ast Parser::parse_bit_field_declaration(const DeclParse& specs)
{
	Ast node = make_ast("bit-field-declaration");
	add_child(node, specs.specs);
	do
	{
		Ast field = make_ast("bit-field-declarator");
		if (!simple(OP_COLON))
			add_child(field, parse_declarator(false).node);
		expect(OP_COLON);
		add_child(field, parse_assignment_expression());
		add_child(node, field);
	}
	while (consume(OP_COMMA));
	expect(OP_SEMICOLON);
	return node;
}

Ast Parser::parse_special_member(bool member_context)
{
	Ast specs = make_ast("member-specifiers");
	while (current().kind == posttoken::TokenKind::Simple &&
	       is_member_function_specifier(current().type))
	{
		string text = current().type == KW_EXPLICIT ?
			current().source : token_leaf(current());
		add_child(specs, make_ast("specifier " + text));
		++pos_;
		skip_attributes();
	}
	string name = parse_id_expression_text();
	Ast node = make_ast("special-member " + name);
	if (!specs->children.empty())
		add_child(node, specs);
	Ast declarator = make_ast("declarator");
	add_child(declarator, make_ast("identifier " + name));
	add_child(declarator, parse_parameter_clause());
	parse_function_suffixes(declarator);
	add_child(node, declarator);
	if (consume(OP_ASS))
	{
		node->line = "special-member-declaration " + name;
		if (consume(KW_DEFAULT))
			add_child(node, make_ast("special-initializer default"));
		else if (consume(KW_DELETE))
			add_child(node, make_ast("special-initializer delete"));
		else
			throw runtime_error("bad special member initializer");
		expect(OP_SEMICOLON);
		return node;
	}
	bool is_definition = simple(OP_COLON) || simple(OP_LBRACE);
	if (consume(OP_COLON))
	{
		Ast ctor = make_ast("ctor-initializer");
		do
		{
			Ast mem = make_ast("mem-initializer");
			add_child(mem, make_ast("mem-initializer-id " + parse_type_name_text()));
			if (simple(OP_LPAREN))
				add_child(mem, parse_argument_list("paren-argument-list", OP_RPAREN));
			else
				add_child(mem, parse_braced_init_list());
			add_child(ctor, mem);
		}
		while (consume(OP_COMMA));
		add_child(node, ctor);
	}
	if (simple(OP_LBRACE))
		add_child(node, parse_compound_statement());
	else
		expect(OP_SEMICOLON);
	node->line = (is_definition ? "special-member-definition " :
	              "special-member-declaration ") + name;
	(void)member_context;
	return node;
}

DeclParse Parser::parse_decl_specifier_seq(bool type_id_context)
{
	DeclParse out;
	out.specs = make_ast(type_id_context ? "type-specifier-seq" : "decl-specifier-seq");
	bool consumed_any = false;
	bool saw_non_cv_type = false;
	while (true)
	{
		skip_attributes();
		if (saw_non_cv_type &&
		    (identifier() || simple(OP_COLON2) || simple(KW_TYPENAME) ||
		     simple(KW_DECLTYPE) || simple(KW_STRUCT) || simple(KW_CLASS) ||
		     simple(KW_UNION) || simple(KW_ENUM)))
			break;
		bool consumed = false;
		Ast spec = parse_one_decl_specifier(type_id_context, out, consumed);
		if (!consumed)
			break;
		consumed_any = true;
		if (spec->line.find("KW_CONST:") == string::npos &&
		    spec->line.find("KW_VOLATILE:") == string::npos &&
		    spec->line.find("KW_TYPEDEF:") == string::npos &&
		    spec->line.find("KW_EXTERN:") == string::npos &&
		    spec->line.find("KW_STATIC:") == string::npos &&
		    spec->line.find("KW_INLINE:") == string::npos &&
		    spec->line.find("KW_VIRTUAL:") == string::npos &&
		    spec->line.find("KW_CONSTEXPR:") == string::npos &&
		    spec->line.find("KW_THREAD_LOCAL:") == string::npos &&
		    spec->line.find("KW_FRIEND:") == string::npos &&
		    spec->line.find("KW_MUTABLE:") == string::npos &&
		    spec->line.find("KW_REGISTER:") == string::npos &&
		    spec->line.find("KW_EXPLICIT:") == string::npos)
			saw_non_cv_type = true;
		add_child(out.specs, spec);
	}
	if (!consumed_any)
		throw runtime_error("expected decl-specifier-seq");
	return out;
}

Ast Parser::parse_one_decl_specifier(bool type_id_context,
                                     DeclParse& out,
                                     bool& consumed)
{
	consumed = true;
	if (current().kind == posttoken::TokenKind::Simple &&
	    is_decl_specifier_keyword(current().type))
	{
		const Token token = current();
		++pos_;
		if (token.type == KW_TYPEDEF)
			out.has_typedef = true;
		if (token.type == KW_FRIEND)
			out.has_friend = true;
		string label = type_id_context && is_cv_qualifier(token.type) ?
			"cv-qualifier " : type_id_context && is_builtin_type(token.type) ?
			"type-specifier " : "decl-specifier ";
		return make_ast(label + token_leaf(token));
	}
	if (simple(KW_DECLTYPE))
	{
		size_t text_begin = pos_;
		++pos_;
		expect(OP_LPAREN);
		Ast expr = parse_expression();
		expect(OP_RPAREN);
		string text = format_token_range(tokens_, text_begin, pos_);
		Ast node = make_ast((type_id_context ? "decltype-specifier " : "decl-specifier ") + text);
		add_child(node, expr);
		return node;
	}
	if (simple(KW_STRUCT) || simple(KW_CLASS) || simple(KW_UNION))
	{
		if (identifier() || simple_at(pos_ + 1, OP_LBRACE))
			return parse_class_specifier(false);
		ETokenType key = current().type;
		string key_source = current().source;
		if (at(pos_ + 1).kind == posttoken::TokenKind::Identifier &&
		    !simple_at(pos_ + 2, OP_LBRACE))
		{
			++pos_;
			string name = expect_identifier();
			add_type_name(name);
			Ast fwd = make_ast("class-forward-declaration " + name);
			add_child(fwd, make_ast("class-key " + keyword_leaf(key, key_source)));
			return fwd;
		}
		return parse_class_specifier(false);
	}
	if (simple(KW_ENUM))
		return parse_enum_specifier(false);
	if (simple(KW_TYPENAME) ||
	    simple(OP_COLON2) ||
	    (identifier() &&
	     (type_id_context || is_type_name(current().source) ||
	      simple_at(pos_ + 1, OP_COLON2) ||
	      simple_at(pos_ + 1, OP_LT))))
	{
		string text = parse_type_name_text();
		string label = type_id_context ? "type-name " : "decl-specifier ";
		if (!type_id_context && text.find('<') == string::npos &&
		    text.find("::") == string::npos)
			label += "TT_IDENTIFIER:";
		return make_ast(label + text);
	}
	consumed = false;
	return Ast();
}

Ast Parser::parse_type_id()
{
	Ast node = make_ast("type-id");
	add_child(node, parse_type_specifier_seq());
	if (starts_abstract_declarator_at(pos_))
		add_child(node, parse_abstract_declarator());
	return node;
}

Ast Parser::parse_type_specifier_seq()
{
	DeclParse specs = parse_decl_specifier_seq(true);
	return specs.specs;
}

Ast Parser::parse_type_specifier(bool& consumed)
{
	DeclParse out;
	return parse_one_decl_specifier(true, out, consumed);
}

bool Parser::starts_parameter_declaration_at(size_t p) const
{
	const Token& token = at(p);
	if (simple_at(p, OP_RPAREN) || simple_at(p, OP_DOTS))
		return true;
	if (token.kind == posttoken::TokenKind::Simple)
	{
		return is_decl_specifier_keyword(token.type) ||
		       token.type == KW_STRUCT ||
		       token.type == KW_CLASS ||
		       token.type == KW_UNION ||
		       token.type == KW_ENUM ||
		       token.type == KW_TYPENAME ||
		       token.type == KW_DECLTYPE ||
		       token.type == OP_COLON2;
	}
	if (token.kind != posttoken::TokenKind::Identifier)
		return false;
	if (!simple_at(p + 1, OP_COLON2))
		return is_type_name(token.source);
	size_t q = p + 2;
	while (at(q).kind == posttoken::TokenKind::Identifier)
	{
		++q;
		if (simple_at(q, OP_LT))
		{
			int depth = 0;
			do
			{
				if (simple_at(q, OP_LT))
					++depth;
				else if (simple_at(q, OP_GT))
					--depth;
				++q;
			}
			while (depth > 0);
		}
		if (!simple_at(q, OP_COLON2))
			break;
		++q;
	}
	return !simple_at(q, OP_LPAREN);
}

bool Parser::starts_abstract_declarator_at(size_t p) const
{
	if (simple_at(p, OP_STAR) ||
	    simple_at(p, OP_AMP) ||
	    simple_at(p, OP_LAND) ||
	    simple_at(p, OP_LSQUARE))
		return true;
	return simple_at(p, OP_LPAREN) && starts_parameter_declaration_at(p + 1);
}

Ast Parser::parse_abstract_declarator()
{
	DeclaratorParse parsed = parse_declarator(true);
	parsed.node->line = "abstract-declarator";
	return parsed.node;
}

DeclaratorParse Parser::parse_declarator(bool abstract_allowed)
{
	DeclaratorParse out;
	out.node = make_ast("declarator");
	parse_ptr_operators(out.node);
	DeclaratorParse direct = parse_direct_declarator(abstract_allowed);
	for (size_t i = 0; i < direct.node->children.size(); ++i)
		add_child(out.node, direct.node->children[i]);
	out.name = direct.name;
	out.has_parameter_clause = direct.has_parameter_clause;
	out.is_pack = direct.is_pack;
	return out;
}

DeclaratorParse Parser::parse_direct_declarator(bool abstract_allowed)
{
	DeclaratorParse out;
	out.node = make_ast("declarator");
	if (simple(OP_LPAREN) && !(abstract_allowed &&
	                           starts_parameter_declaration_at(pos_ + 1)))
	{
		consume(OP_LPAREN);
		Ast nested = make_ast("nested-declarator");
		DeclaratorParse inner = parse_declarator(true);
		add_child(nested, inner.node);
		expect(OP_RPAREN);
		add_child(out.node, nested);
		out.name = inner.name;
	}
	else if (consume(OP_DOTS))
	{
		add_child(out.node, make_ast("parameter-pack ..."));
		out.is_pack = true;
		if (identifier())
			out.name = expect_identifier();
		if (!out.name.empty())
			add_child(out.node, make_ast("identifier " + out.name));
	}
	else if (!abstract_allowed || identifier() || simple(KW_OPERATOR) ||
	         simple(OP_COMPL) || simple(OP_COLON2))
	{
		out.name = parse_id_expression_text();
		add_child(out.node, make_ast("identifier " + out.name));
	}

	while (true)
	{
		if (starts_attribute())
		{
			skip_attributes();
			continue;
		}
		if (simple(OP_LPAREN))
		{
			if (!starts_parameter_declaration_at(pos_ + 1))
				break;
			add_child(out.node, parse_parameter_clause());
			out.has_parameter_clause = true;
			parse_function_suffixes(out.node);
			continue;
		}
		if (consume(OP_LSQUARE))
		{
			Ast suffix = make_ast("array-suffix");
			if (!simple(OP_RSQUARE))
				add_child(suffix, parse_expression());
			expect(OP_RSQUARE);
			add_child(out.node, suffix);
			continue;
		}
		break;
	}
	return out;
}

void Parser::parse_ptr_operators(const Ast& node)
{
	while (true)
	{
		if (simple(OP_STAR) || simple(OP_AMP) || simple(OP_LAND))
		{
			Token token = current();
			++pos_;
			add_child(node, make_ast("ptr-operator " + token_leaf(token)));
			while (current().kind == posttoken::TokenKind::Simple &&
			       is_cv_qualifier(current().type))
			{
				add_child(node, make_ast("cv-qualifier " + token_leaf(current())));
				++pos_;
			}
			continue;
		}
		if ((identifier() || simple(OP_COLON2)) && simple_at(pos_ + 1, OP_COLON2))
		{
			size_t save = pos_;
			string q;
			if (consume(OP_COLON2))
				q = "::" + expect_identifier();
			else
				q = expect_identifier();
			while (consume(OP_COLON2))
			{
				if (simple(OP_STAR))
					break;
				q += "::" + expect_identifier();
			}
			if (consume(OP_STAR))
			{
				add_child(node, make_ast("ptr-operator " + q + "::*"));
				continue;
			}
			pos_ = save;
		}
		break;
	}
}

Ast Parser::parse_parameter_clause()
{
	Ast node = make_ast("parameter-clause");
	expect(OP_LPAREN);
	if (!simple(OP_RPAREN))
	{
		if (consume(OP_DOTS))
			add_child(node, make_ast("parameter-pack ..."));
		else
		{
			do
			{
				if (simple(OP_DOTS))
				{
					consume(OP_DOTS);
					add_child(node, make_ast("parameter-pack ..."));
					break;
				}
				add_child(node, parse_parameter_declaration());
			}
			while (consume(OP_COMMA));
		}
	}
	expect(OP_RPAREN);
	return node;
}

Ast Parser::parse_parameter_declaration()
{
	Ast node = make_ast("parameter-declaration");
	DeclParse specs = parse_decl_specifier_seq(false);
	add_child(node, specs.specs);
	if (!simple(OP_COMMA) && !simple(OP_RPAREN) && !simple(OP_ASS))
	{
		DeclaratorParse declarator = parse_declarator(true);
		if (!declarator.node->children.empty())
			add_child(node, declarator.node);
		if (!declarator.name.empty())
			add_value_name(declarator.name);
	}
	if (consume(OP_ASS))
	{
		Ast dflt = make_ast("default-argument");
		Ast init = make_ast("initializer");
		if (simple(OP_LBRACE))
			add_child(init, parse_braced_init_list());
		else
			add_child(init, parse_assignment_expression());
		add_child(dflt, init);
		add_child(node, dflt);
	}
	skip_attributes();
	return node;
}

void Parser::parse_function_suffixes(const Ast& node)
{
	while (true)
	{
		if (current().kind == posttoken::TokenKind::Simple &&
		    is_cv_qualifier(current().type))
		{
			add_child(node, make_ast("cv-qualifier " + token_leaf(current())));
			++pos_;
			continue;
		}
		if (simple(OP_AMP) || simple(OP_LAND))
		{
			add_child(node, make_ast("ref-qualifier " + token_leaf(current())));
			++pos_;
			continue;
		}
		if (simple(KW_NOEXCEPT))
		{
			++pos_;
			if (consume(OP_LPAREN))
			{
				Ast noex = make_ast("noexcept-specification");
				add_child(noex, parse_expression());
				expect(OP_RPAREN);
				add_child(node, noex);
			}
			else
				add_child(node, make_ast("function-qualifier noexcept"));
			continue;
		}
		if (simple(KW_THROW))
		{
			++pos_;
			string text = "throw" + parse_balanced_text(OP_LPAREN, OP_RPAREN);
			add_child(node, make_ast("function-qualifier " + text));
			continue;
		}
		if (simple(OP_ARROW))
		{
			Ast trailing = parse_trailing_return_type();
			if (node->line != "lambda-declarator" &&
			    !trailing->children.empty() &&
			    !trailing->children[0]->children.empty() &&
			    !trailing->children[0]->children[0]->children.empty())
			{
				string first = trailing->children[0]->children[0]->children[0]->line;
				const string prefix = "type-name ";
				if (first.compare(0, prefix.size(), prefix) == 0)
					trailing->line += " " + first.substr(prefix.size());
			}
			add_child(node, trailing);
			continue;
		}
		break;
	}
}

Ast Parser::parse_trailing_return_type()
{
	expect(OP_ARROW);
	Ast node = make_ast("trailing-return-type");
	add_child(node, parse_type_id());
	return node;
}

Ast Parser::parse_initializer()
{
	Ast node = make_ast("initializer");
	if (consume(OP_ASS))
	{
		if (simple(KW_DEFAULT))
		{
			++pos_;
			add_child(node, make_ast("special-initializer default"));
		}
		else if (simple(KW_DELETE))
		{
			++pos_;
			add_child(node, make_ast("special-initializer delete"));
		}
		else
			add_child(node, parse_assignment_expression());
		return node;
	}
	if (simple(OP_LBRACE))
		add_child(node, parse_braced_init_list());
	else if (simple(OP_LPAREN))
		add_child(node, parse_argument_list("paren-initializer", OP_RPAREN));
	else
		throw runtime_error("expected initializer");
	return node;
}

Ast Parser::parse_braced_init_list()
{
	Ast node = make_ast("braced-init-list");
	expect(OP_LBRACE);
	if (!simple(OP_RBRACE))
		parse_initializer_items(node, OP_RBRACE);
	expect(OP_RBRACE);
	return node;
}

void Parser::parse_initializer_items(const Ast& node, ETokenType close)
{
	while (!simple(close))
	{
		if (simple(OP_LBRACE))
			add_child(node, parse_braced_init_list());
		else
			add_child(node, parse_assignment_expression());
		if (!consume(OP_COMMA))
			break;
		if (simple(close))
			break;
	}
}

}  // namespace internal
}  // namespace pa10
