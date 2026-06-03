#include "pa12_internal.h"

#include <stdexcept>

using namespace std;

namespace pa12 {
namespace internal {

void Parser::parse_declaration_into(Node& out)
{
	if (consume(OP_SEMICOLON))
		return;
	if ((at(KW_INLINE) && lookahead(KW_NAMESPACE, 1)) || at(KW_NAMESPACE))
	{
		parse_namespace_or_alias(out);
		return;
	}
	if (at(KW_USING))
	{
		parse_using_family(out);
		return;
	}
	if (at(KW_EXTERN) && lookahead(OP_LBRACE, 1))
	{
		parse_linkage_specification(out);
		return;
	}
	if (at(KW_EXTERN) && pos_ + 1 < tokens_.size() &&
	    tokens_[pos_ + 1].kind == posttoken::TokenKind::Literal)
	{
		parse_linkage_specification(out);
		return;
	}
	if (at(KW_TEMPLATE))
	{
		parse_template_declaration();
		return;
	}
	parse_simple_or_function_declaration(out, true);
}

void Parser::parse_namespace_or_alias(Node& out)
{
	bool inline_ns = consume(KW_INLINE);
	expect(KW_NAMESPACE);
	if (!inline_ns && at_identifier() && lookahead(OP_ASS, 1))
	{
		string alias = consume_identifier();
		expect(OP_ASS);
		Scope* target = parse_qualified_namespace_specifier();
		expect(OP_SEMICOLON);
		pa11::add_namespace_alias(current_scope(), alias, target);
		return;
	}

	string name;
	bool named = false;
	if (at_identifier())
	{
		named = true;
		name = consume_identifier();
	}
	expect(OP_LBRACE);
	Scope* child = NULL;
	if (named)
		child = pa11::get_or_create_namespace(current_scope(), name, inline_ns);
	else
	{
		if (current_scope()->unnamed_namespace == NULL)
		{
			current_scope()->unnamed_namespace =
				pa11::create_child_scope(current_scope(),
				                         ScopeKind::Namespace,
				                         "<unnamed>");
			pa11::add_using_directive(current_scope(),
			                          current_scope()->unnamed_namespace);
		}
		child = current_scope()->unnamed_namespace;
		name = "<unnamed>";
	}

	Node node("namespace-definition " + name);
	scopes_.push_back(child);
	while (!at(OP_RBRACE))
		parse_declaration_into(node);
	scopes_.pop_back();
	expect(OP_RBRACE);
	add_child(out, node);
}

void Parser::parse_using_family(Node& out)
{
	expect(KW_USING);
	if (consume(KW_NAMESPACE))
	{
		Scope* target = parse_qualified_namespace_specifier();
		expect(OP_SEMICOLON);
		pa11::add_using_directive(current_scope(), target);
		return;
	}
	if (at_identifier() && lookahead(OP_ASS, 1))
	{
		string name = consume_identifier();
		expect(OP_ASS);
		TypePtr type = parse_type_id();
		expect(OP_SEMICOLON);
		add_alias(current_scope(), name, type);
		Node node("type-alias " + name + " " + pa11::describe_type(type));
		add_child(out, node);
		return;
	}
	string spelling;
	Scope* qualifier = parse_nested_name_specifier(&spelling);
	string name = consume_identifier();
	expect(OP_SEMICOLON);
	vector<Binding*> targets = lookup_qualified_set(qualifier, name, pa11::LOOKUP_ANY);
	if (targets.empty())
		throw runtime_error("using declaration target not found");
	for (size_t i = 0; i < targets.size(); ++i)
		pa11::add_using_declaration(current_scope(), name, targets[i]);
}

void Parser::parse_linkage_specification(Node& out)
{
	expect(KW_EXTERN);
	if (at_literal())
		++pos_;
	if (consume(OP_LBRACE))
	{
		while (!at(OP_RBRACE))
			parse_declaration_into(out);
		expect(OP_RBRACE);
		return;
	}
	parse_simple_or_function_declaration(out, true);
}

void Parser::parse_template_declaration()
{
	expect(KW_TEMPLATE);
	skip_template_parameter_clause();
	Node ignored;
	parse_declaration_into(ignored);
}

void Parser::skip_template_parameter_clause()
{
	expect(OP_LT);
	int depth = 1;
	while (depth > 0 && !at_eof())
	{
		if (consume(OP_LT))
			++depth;
		else if (consume(OP_GT))
			--depth;
		else
			++pos_;
	}
}

void Parser::parse_simple_or_function_declaration(Node& out, bool emit_node)
{
	if (parse_constructor_like_member())
		return;
	DeclSpecs specs = parse_decl_specifier_seq(false);
	TypePtr base = type_from_decl_specs(specs);
	if (consume(OP_SEMICOLON))
	{
		if (current_scope()->kind != ScopeKind::Namespace)
		{
			TypePtr bare = pa11::strip_cv(base);
			Node simple("simple-declaration");
			if (bare->kind == pa11::TypeKind::Record &&
			    bare->tag == "union" &&
			    bare->name.find("__anonymous_union_type__") == 0)
			{
				string storage_name = bare->name;
				const string prefix = "__anonymous_union_type__";
				storage_name.replace(0,
				                     prefix.size(),
				                     "__anonymous_union_storage__");
				Binding* storage = add_value(current_scope(),
				                             BindingKind::Variable,
				                             storage_name,
				                             bare);
				Node var("variable " + storage_name + " " +
				         pa11::describe_type(bare));
				ensure_default_constructor(bare);
				add_child(var, default_constructor_action(storage));
				add_child(simple, var);
				if (bare->scope != NULL)
					inject_anonymous_union_members(bare->scope, storage);
			}
			add_child(out, simple);
		}
		return;
	}

	Declarator declarator = parse_declarator(false);
	if (at(OP_LBRACE))
	{
		Node node(current_scope()->kind == ScopeKind::Namespace ? "" :
		          "simple-declaration");
		Binding* function =
			declare_one(specs, base, declarator, NULL, true, node);
		parse_function_body(function, declarator, node);
		if (emit_node)
		{
			if (node.line.empty())
				add_child(out, node.children.back());
			else
				add_child(out, node);
		}
		return;
	}

	Expr init;
	bool has_init = false;
	bool brace_init = false;
	if (consume(OP_ASS))
	{
		if (consume(OP_LBRACE))
		{
			has_init = true;
			init.valid = true;
			init.braced_init_list = true;
			init.node = Node("braced-init-list");
			while (!at(OP_RBRACE))
			{
				add_child(init.node, parse_assignment_expression().node);
				if (!consume(OP_COMMA))
					break;
			}
			expect(OP_RBRACE);
		}
		else
		{
			has_init = true;
			init = parse_expression();
		}
	}
	else if ((brace_init = consume(OP_LBRACE)))
	{
		has_init = true;
		init.valid = true;
		init.braced_init_list = true;
		init.node = Node("braced-init-list");
		while (!at(OP_RBRACE))
		{
			add_child(init.node, parse_assignment_expression().node);
			if (!consume(OP_COMMA))
				break;
		}
		expect(OP_RBRACE);
	}
	else if (at(OP_LPAREN) && !declarator_function_suffix(declarator))
	{
		expect(OP_LPAREN);
		if (!at(OP_RPAREN))
		{
			vector<Expr> args = parse_argument_list();
			if (args.size() != 1)
				throw runtime_error("unsupported direct initializer");
			init = args[0];
			has_init = true;
		}
		expect(OP_RPAREN);
	}

	Node node(current_scope()->kind == ScopeKind::Namespace ? "" :
	          "simple-declaration");
	declare_one(specs, base, declarator, has_init ? &init : NULL, false, node);
	while (consume(OP_COMMA))
	{
		Declarator next = parse_declarator(false);
		Expr next_init;
		bool next_has_init = false;
		if (consume(OP_ASS))
		{
			next_has_init = true;
			next_init = parse_expression();
		}
		declare_one(specs, base, next, next_has_init ? &next_init : NULL, false, node);
	}
	expect(OP_SEMICOLON);
	if (emit_node && !node.children.empty())
	{
		if (node.line.empty())
		{
			for (size_t i = 0; i < node.children.size(); ++i)
				add_child(out, node.children[i]);
		}
		else
			add_child(out, node);
	}
}

bool Parser::parse_constructor_like_member()
{
	if (current_scope()->kind != ScopeKind::Class || !at_identifier())
		return false;
	if (current().source != current_scope()->name)
		return false;
	++pos_;
	if (at(OP_LPAREN))
		skip_balanced(OP_LPAREN, OP_RPAREN);
	while (!consume(OP_SEMICOLON))
	{
		if (at(OP_LBRACE))
		{
			skip_balanced(OP_LBRACE, OP_RBRACE);
			break;
		}
		++pos_;
	}
	return true;
}

Binding* Parser::declare_one(const DeclSpecs& specs,
                             TypePtr base,
                             const Declarator& declarator,
                             const Expr* init,
                             bool function_definition,
                             Node& out)
{
	const QualifiedName& qname = declarator_name(declarator);
	Scope* target = qname.qualifier != NULL ? qname.qualifier : current_scope();
	TypePtr type = apply_declarator(declarator, base);
	if (specs.typedef_decl)
	{
		Binding* alias = add_alias(target, qname.name, type);
		add_child(out, Node("type-alias " + qname.name + " " +
		                    pa11::describe_type(alias->type)));
		return alias;
	}

	if (specs.constexpr_decl && !pa11::is_reference_type(type))
		type = pa11::make_cv(type, pa11::CV_CONST);
	if (target->kind == ScopeKind::Class && type->kind == pa11::TypeKind::Function)
		type = make_member_function_type(target, type);
	if (type->kind == pa11::TypeKind::Function || function_definition)
	{
		Binding* function = add_value(target, BindingKind::Function, qname.name, type);
		string keyword = function_definition ? "function-definition " :
			"function-declaration ";
		add_child(out, Node(keyword + qualified_decl_name(function) + " " +
		                    pa11::describe_type(type)));
		return function;
	}

	Binding* variable = add_value(target, BindingKind::Variable, qname.name, type);
	Node var("variable " + qname.name + " " + pa11::describe_type(type));
	if (init != NULL)
	{
		if (init->braced_init_list)
		{
			Node list = init->node;
			list.line += " lvalue " + pa11::describe_type(type);
			add_child(var, list);
		}
		else
		{
			Conversion conv = convert_to(*init, type);
			if (!conv.viable)
				throw runtime_error("invalid initializer conversion");
			add_child(var, conv.expr.node);
			if ((specs.constexpr_decl || pa11::type_has_const(type)) &&
			    conv.expr.has_constant_value)
			{
				variable->has_constant = true;
				variable->constant_value = conv.expr.constant_value;
			}
		}
	}
	else if (pa11::strip_cv(type)->kind == pa11::TypeKind::Record)
	{
		ensure_default_constructor(type);
		add_child(var, default_constructor_action(variable));
	}
	add_child(out, var);
	return variable;
}

}  // namespace internal
}  // namespace pa12
