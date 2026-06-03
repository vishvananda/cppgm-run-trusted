#include "pa10_internal.h"

#include <stdexcept>

using namespace std;

namespace pa10 {
namespace internal {

namespace {

string unqualified_decl_name(const string& name)
{
	size_t end = name.find('<');
	string stem = name.substr(0, end);
	size_t colon = stem.rfind("::");
	if (colon != string::npos)
		stem = stem.substr(colon + 2);
	if (!stem.empty() && stem[0] == '~')
		stem = stem.substr(1);
	return stem;
}

bool starts_qualified_nonconversion_operator(const vector<Token>& tokens,
                                             size_t pos)
{
	if (pos + 3 >= tokens.size() ||
	    tokens[pos].kind != posttoken::TokenKind::Identifier)
		return false;
	size_t p = pos + 1;
	while (p + 1 < tokens.size() &&
	       tokens[p].kind == posttoken::TokenKind::Simple &&
	       tokens[p].type == OP_COLON2)
	{
		++p;
		if (tokens[p].kind == posttoken::TokenKind::Simple &&
		    tokens[p].type == KW_OPERATOR)
		{
			const Token& next = tokens[p + 1];
			return next.kind == posttoken::TokenKind::Simple &&
			       !is_builtin_type(next.type);
		}
		if (tokens[p].kind != posttoken::TokenKind::Identifier)
			return false;
		++p;
	}
	return false;
}

bool keyword_decl_specifier_seq(const Ast& specs)
{
	const string prefix = "decl-specifier KW_";
	for (size_t i = 0; i < specs->children.size(); ++i)
	{
		const string& line = specs->children[i]->line;
		if (line.size() < prefix.size() ||
		    line.substr(0, prefix.size()) != prefix)
			return false;
	}
	return !specs->children.empty();
}

}  // namespace

Ast Parser::parse_declaration()
{
	skip_attributes();
	if (consume(OP_SEMICOLON))
		return make_ast("empty-declaration");
	if (simple(KW_EXTERN) && at(pos_ + 1).kind == posttoken::TokenKind::Literal)
		return parse_linkage_specification();
	if (simple(KW_EXTERN) && simple_at(pos_ + 1, KW_TEMPLATE))
		return parse_explicit_instantiation();
	if (simple(KW_TEMPLATE))
		return parse_template_declaration();
	if (simple(KW_INLINE) && simple_at(pos_ + 1, KW_NAMESPACE))
		return parse_namespace_definition();
	if (simple(KW_NAMESPACE))
	{
		if (simple_at(pos_ + 2, OP_ASS))
			return parse_namespace_alias_definition();
		return parse_namespace_definition();
	}
	if (simple(KW_USING))
		return parse_using();
	if (simple(KW_STATIC_ASSERT))
		return parse_static_assert_declaration();
	if (starts_qualified_nonconversion_operator(tokens_, pos_))
		throw runtime_error("qualified nonconversion operator needs return type");
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
			return parse_special_member(false);
		}
		catch (const exception&)
		{
			pos_ = save;
		}
	}
	return parse_simple_or_function_declaration(false);
}

Ast Parser::parse_block_item()
{
	skip_attributes();
	if (starts_declaration())
	{
		size_t save = pos_;
		try
		{
			return parse_declaration();
		}
		catch (const exception&)
		{
			pos_ = save;
		}
	}
	return parse_statement();
}

Ast Parser::parse_namespace_definition()
{
	bool is_inline = consume(KW_INLINE);
	expect(KW_NAMESPACE);
	string name;
	if (identifier())
		name = expect_identifier();
	add_namespace_name(name);

	Ast node = make_ast("namespace-definition " + (name.empty() ? "<unnamed>" : name));
	if (is_inline)
		add_child(node, make_ast("inline"));
	expect(OP_LBRACE);
	push_scope();
	while (!consume(OP_RBRACE))
		add_child(node, parse_declaration());
	pop_scope();
	return node;
}

Ast Parser::parse_namespace_alias_definition()
{
	expect(KW_NAMESPACE);
	string name = expect_identifier();
	expect(OP_ASS);
	string target = parse_id_expression_text();
	expect(OP_SEMICOLON);
	add_namespace_name(name);
	Ast node = make_ast("namespace-alias-definition " + name);
	add_child(node, make_ast("target " + target));
	return node;
}

Ast Parser::parse_using()
{
	expect(KW_USING);
	if (consume(KW_NAMESPACE))
	{
		string target = parse_id_expression_text();
		expect(OP_SEMICOLON);
		Ast node = make_ast("using-directive");
		add_child(node, make_ast("target " + target));
		return node;
	}
	if (identifier() && simple_at(pos_ + 1, OP_ASS))
	{
		--pos_;
		return parse_alias_declaration();
	}
	string target = parse_id_expression_text();
	expect(OP_SEMICOLON);
	add_type_name(unqualified_decl_name(target));
	Ast node = make_ast("using-declaration");
	add_child(node, make_ast("target " + target));
	return node;
}

Ast Parser::parse_alias_declaration()
{
	expect(KW_USING);
	string name = expect_identifier();
	expect(OP_ASS);
	Ast node = make_ast("alias-declaration " + name);
	add_child(node, parse_type_id());
	expect(OP_SEMICOLON);
	add_type_name(name);
	return node;
}

Ast Parser::parse_template_declaration()
{
	expect(KW_TEMPLATE);
	Ast node = make_ast("template-declaration");
	push_scope();
	add_child(node, parse_template_parameter_clause());
	add_child(node, parse_declaration());
	pop_scope();
	return node;
}

Ast Parser::parse_template_parameter_clause()
{
	Ast node = make_ast("template-parameter-clause");
	expect(OP_LT);
	if (!simple(OP_GT))
	{
		Ast list = make_ast("template-parameter-list");
		do
		{
			add_child(list, parse_template_parameter());
		}
		while (consume(OP_COMMA));
		add_child(node, list);
	}
	if (!consume_close_angle())
		throw runtime_error("expected template close angle before '" + current().source + "'");
	return node;
}

Ast Parser::parse_template_parameter()
{
	if (simple(KW_TEMPLATE))
	{
		expect(KW_TEMPLATE);
		Ast node = make_ast("type-parameter");
		add_child(node, make_ast("template-template-parameter"));
		add_child(node, parse_template_parameter_clause());
		ETokenType key = current().type;
		expect(key);
		add_child(node, make_ast("parameter-key " + keyword_leaf(key, TokenTypeToStringMap.at(key) == "KW_CLASS" ? "class" : current().source)));
		if (identifier())
		{
			string name = expect_identifier();
			add_child(node, make_ast("identifier " + name));
			add_type_name(name);
		}
		if (consume(OP_ASS))
		{
			Ast dflt = make_ast("default-template-argument");
			add_child(dflt, parse_type_id());
			add_child(node, dflt);
		}
		return node;
	}
	if (simple(KW_CLASS) || simple(KW_TYPENAME))
	{
		ETokenType key = current().type;
		string source = current().source;
		++pos_;
		Ast node = make_ast("type-parameter");
		add_child(node, make_ast("parameter-key " + keyword_leaf(key, source)));
		if (consume(OP_DOTS))
			add_child(node, make_ast("parameter-pack ..."));
		if (identifier())
		{
			string name = expect_identifier();
			add_child(node, make_ast("identifier " + name));
			add_type_name(name);
		}
		if (consume(OP_ASS))
		{
			Ast dflt = make_ast("default-template-argument");
			add_child(dflt, parse_type_id());
			add_child(node, dflt);
		}
		return node;
	}

	Ast node = make_ast("non-type-template-parameter");
	DeclParse specs = parse_decl_specifier_seq(false);
	add_child(node, specs.specs);
	if (consume(OP_DOTS))
		add_child(node, make_ast("parameter-pack ..."));
	bool has_declarator = false;
	if (!simple(OP_COMMA) && !simple(OP_GT) && !simple(OP_ASS))
	{
		DeclaratorParse declarator = parse_declarator(false);
		add_child(node, declarator.node);
		has_declarator = true;
		if (!declarator.name.empty())
			add_value_name(declarator.name);
	}
	if (consume(OP_ASS))
	{
		Ast dflt = make_ast("default-template-argument");
		if (!has_declarator && keyword_decl_specifier_seq(specs.specs) && literal())
		{
			add_child(dflt, make_ast("literal TT_LITERAL:" + current().source));
			++pos_;
		}
		else
		{
			++expression_angle_stop_;
			add_child(dflt, parse_assignment_expression());
			--expression_angle_stop_;
		}
		add_child(node, dflt);
	}
	return node;
}

Ast Parser::parse_class_declaration()
{
	if (simple_at(pos_ + 2, OP_SEMICOLON))
		return parse_class_forward();
	return parse_class_specifier(true);
}

Ast Parser::parse_class_forward()
{
	ETokenType key = current().type;
	string key_source = current().source;
	++pos_;
	string name = expect_identifier();
	expect(OP_SEMICOLON);
	add_type_name(name);
	Ast node = make_ast("class-forward-declaration " + name);
	add_child(node, make_ast("class-key " + keyword_leaf(key, key_source)));
	return node;
}

Ast Parser::parse_class_specifier(bool consume_semicolon)
{
	ETokenType key = current().type;
	string key_source = current().source;
	++pos_;
	skip_attributes();
	string name;
	if (identifier())
	{
		name = expect_identifier();
		if (starts_template_argument_list())
			name = parse_template_id_text(name);
		add_type_name(unqualified_decl_name(name));
	}

	Ast node = make_ast(name.empty() ? "class-specifier" : "class-specifier " + name);
	add_child(node, make_ast("class-key " + keyword_leaf(key, key_source)));
	if (consume(OP_COLON))
	{
		Ast base = make_ast("base-clause");
		do
		{
			Ast spec = make_ast("base-specifier");
			if (simple(KW_VIRTUAL))
			{
				add_child(spec, make_ast("virtual " + token_leaf(current())));
				++pos_;
			}
			if (current().kind == posttoken::TokenKind::Simple &&
			    is_access_specifier(current().type))
			{
				add_child(spec, make_ast("access-specifier " + token_leaf(current())));
				++pos_;
			}
			if (simple(KW_VIRTUAL))
			{
				add_child(spec, make_ast("virtual " + token_leaf(current())));
				++pos_;
			}
			add_child(spec, make_ast("base-name " + parse_type_name_text()));
			consume(OP_DOTS);
			add_child(base, spec);
		}
		while (consume(OP_COMMA));
		add_child(node, base);
	}

	expect(OP_LBRACE);
	class_stack_.push_back(unqualified_decl_name(name));
	++class_depth_;
	push_scope();
	while (!consume(OP_RBRACE))
		add_child(node, parse_member_declaration());
	pop_scope();
	--class_depth_;
	class_stack_.pop_back();
	if (consume_semicolon)
		expect(OP_SEMICOLON);
	return node;
}

Ast Parser::parse_enum_declaration()
{
	return parse_enum_specifier(true);
}

Ast Parser::parse_enum_specifier(bool consume_semicolon)
{
	expect(KW_ENUM);
	bool scoped = false;
	ETokenType enum_key = KW_ENUM;
	string enum_source;
	if (simple(KW_CLASS) || simple(KW_STRUCT))
	{
		scoped = true;
		enum_key = current().type;
		enum_source = current().source;
		++pos_;
	}
	string name;
	if (identifier())
	{
		name = expect_identifier();
		add_type_name(name);
	}
	Ast node = make_ast(name.empty() ? "enum-specifier" : "enum-specifier " + name);
	if (scoped)
		add_child(node, make_ast("enum-key " + keyword_leaf(enum_key, enum_source)));
	if (consume(OP_COLON))
		add_child(node, parse_type_id());
	if (consume(OP_LBRACE))
	{
		if (!simple(OP_RBRACE))
		{
			do
			{
				string enumerator = expect_identifier();
				Ast e = make_ast("enumerator " + enumerator);
				add_value_name(enumerator);
				if (consume(OP_ASS))
					add_child(e, parse_assignment_expression());
				add_child(node, e);
			}
			while (consume(OP_COMMA) && !simple(OP_RBRACE));
		}
		expect(OP_RBRACE);
	}
	if (consume_semicolon)
		expect(OP_SEMICOLON);
	return node;
}

Ast Parser::parse_static_assert_declaration()
{
	expect(KW_STATIC_ASSERT);
	expect(OP_LPAREN);
	Ast node = make_ast("static-assert-declaration");
	add_child(node, parse_assignment_expression());
	if (consume(OP_COMMA))
		add_child(node, make_ast("message " + expect_literal()));
	expect(OP_RPAREN);
	expect(OP_SEMICOLON);
	return node;
}

Ast Parser::parse_linkage_specification()
{
	expect(KW_EXTERN);
	string lang = expect_literal();
	if (lang.size() >= 2 && lang[0] == '"')
		lang = lang.substr(1, lang.size() - 2);
	Ast node = make_ast("linkage-specification " + lang);
	if (consume(OP_LBRACE))
	{
		while (!consume(OP_RBRACE))
			add_child(node, parse_declaration());
	}
	else
		add_child(node, parse_declaration());
	return node;
}

Ast Parser::parse_explicit_instantiation()
{
	consume(KW_EXTERN);
	expect(KW_TEMPLATE);
	Ast node = make_ast("explicit-instantiation-declaration");
	add_child(node, parse_declaration());
	return node;
}

}  // namespace internal
}  // namespace pa10
