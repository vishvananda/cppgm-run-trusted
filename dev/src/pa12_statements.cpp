#include "pa12_internal.h"

#include <stdexcept>

using namespace std;

namespace pa12 {
namespace internal {

void Parser::parse_function_body(Binding* function,
                                 const Declarator& declarator,
                                 Node& function_node)
{
	vector<ParameterInfo> parameters;
	const Suffix* suffix = declarator_function_suffix(declarator);
	if (suffix != NULL)
		parameters = suffix->parameters;
	parse_function_body_from_parameters(function, parameters, function_node);
}

void Parser::parse_function_body_from_parameters(
	Binding* function,
	const vector<ParameterInfo>& parameters,
	Node& function_node)
{
	if (function_node.children.empty())
		throw runtime_error("missing function node");
	Node& fn = function_node.children.back();
	Scope* lexical_parent =
		function->owner != NULL && function->owner->kind == ScopeKind::Class
		? function->owner : current_scope();
	Scope* function_scope =
		pa11::create_child_scope(lexical_parent, ScopeKind::Function, function->name);
	if (function->owner != NULL &&
	    function->owner->kind == ScopeKind::Class &&
	    !function->is_static_member)
	{
		if (function->type->parameters.empty())
			throw runtime_error("member function missing this parameter");
		TypePtr this_type = function->type->parameters[0];
		Binding* this_binding =
			pa11::add_binding(function_scope,
			                  BindingKind::Parameter,
			                  "this",
			                  this_type);
		Node this_node("parameter this " + pa11::describe_type(this_type));
		this_node.binding = this_binding;
		this_node.type = this_type;
		add_child(fn, this_node);
	}
	for (size_t i = 0; i < parameters.size(); ++i)
	{
		string name = parameters[i].name;
		if (!name.empty())
		{
			Binding* param =
				pa11::add_binding(function_scope,
				                  BindingKind::Parameter,
				                  name,
				                  parameters[i].type);
			Node param_node("parameter " + name + " " +
			                pa11::describe_type(parameters[i].type));
			param_node.binding = param;
			param_node.type = parameters[i].type;
			add_child(fn, param_node);
		}
		else
		{
			Node param_node("parameter  " +
			                pa11::describe_type(parameters[i].type));
			param_node.type = parameters[i].type;
			add_child(fn, param_node);
		}
	}
	scopes_.push_back(function_scope);
	function_returns_.push_back(function->type->base);
	active_functions_.push_back(function);
	add_child(fn, parse_compound_statement());
	active_functions_.pop_back();
	function_returns_.pop_back();
	scopes_.pop_back();
}

static bool function_body_empty(const Node& fn)
{
	if (fn.children.empty())
		return true;
	const Node& body = fn.children.back();
	return body.line == "compound-statement" && body.children.empty();
}

static void mark_empty_destructor(Binding* function, const Node& fn)
{
	if (function == NULL ||
	    function->name.empty() ||
	    function->name[0] != '~' ||
	    function->is_virtual ||
	    !function_body_empty(fn))
		return;
	function->is_noop_destructor = true;
	Scope* owner = function->owner;
	if (owner == NULL)
		return;
	map<string, vector<Binding*> >::iterator found =
		owner->members.find(function->name);
	if (found == owner->members.end())
		return;
	for (size_t i = 0; i < found->second.size(); ++i)
	{
		Binding* candidate = found->second[i];
		if (candidate->kind == BindingKind::Function &&
		    pa11::same_type(candidate->type, function->type))
			candidate->is_noop_destructor = true;
	}
}

void Parser::parse_pending_member_bodies(Scope* class_scope)
{
	map<Scope*, vector<PendingFunctionBody> >::iterator found =
		pending_member_bodies_.find(class_scope);
	if (found == pending_member_bodies_.end())
		return;
	vector<PendingFunctionBody> pending = found->second;
	pending_member_bodies_.erase(found);
	size_t saved = pos_;
	for (size_t i = 0; i < pending.size(); ++i)
	{
		pos_ = pending[i].body_pos;
		Node wrapper;
		add_child(wrapper, pending[i].node);
		if (pending[i].constructor_body)
			parse_constructor_body_from_parameters(pending[i].function,
			                                       pending[i].class_type,
			                                       pending[i].parameters,
			                                       wrapper);
		else
			parse_function_body_from_parameters(pending[i].function,
			                                    pending[i].parameters,
			                                    wrapper);
		if (!wrapper.children.empty())
			mark_empty_destructor(pending[i].function, wrapper.children.back());
		if (!wrapper.children.empty())
			extra_lowir_nodes_.push_back(wrapper.children.back());
	}
	pos_ = saved;
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
		bool definitely_declaration =
			at_simple_builtin() ||
			at_simple_cv() ||
			at(KW_TYPEDEF) ||
			at(KW_CONSTEXPR) ||
			at(KW_EXTERN) ||
			at(KW_STATIC) ||
			at(KW_DECLTYPE) ||
			starts_class_key() ||
			at(KW_ENUM) ||
			(at_identifier() &&
			 pos_ + 1 < tokens_.size() &&
			 tokens_[pos_ + 1].kind == posttoken::TokenKind::Identifier);
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
			if (definitely_declaration)
				throw;
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
	if (at(KW_RETURN) || at(KW_BREAK) || at(KW_CONTINUE) || at(KW_GOTO))
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
	add_child(node, parse_condition(pa11::make_fundamental(FT_BOOL)));
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
	add_child(node, parse_condition(pa11::make_fundamental(FT_INT)));
	expect(OP_RPAREN);
	add_child(node, parse_statement());
	return node;
}

Node Parser::parse_while_statement()
{
	expect(KW_WHILE);
	Node node("while-statement");
	expect(OP_LPAREN);
	add_child(node, parse_condition(pa11::make_fundamental(FT_BOOL)));
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
	Expr do_cond = parse_expression();
	if (pa11::strip_cv(expression_object_type(do_cond.type))->kind ==
	    pa11::TypeKind::Record)
	{
		Conversion conv =
			convert_to(do_cond, pa11::make_fundamental(FT_BOOL));
		if (conv.viable)
			do_cond = conv.expr;
	}
	add_child(cond, do_cond.node);
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
		add_child(node, parse_condition(pa11::make_fundamental(FT_BOOL)));
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
	if (consume(KW_GOTO))
	{
		string label = consume_identifier();
		expect(OP_SEMICOLON);
		return Node("goto-statement " + label);
	}
	expect(KW_RETURN);
	Node node("return-statement");
	if (!at(OP_SEMICOLON))
	{
		Expr expr = parse_expression();
		TypePtr result = current_return_type();
		if (result.get() != NULL && !pa11::is_void_type(result))
		{
			TypePtr result_record = pa11::strip_cv(result);
			TypePtr expr_record =
				pa11::strip_cv(expression_object_type(expr.type));
			if (result_record->kind == pa11::TypeKind::Record &&
			    expr.braced_init_list)
			{
				expr.type = result;
				expr.node.type = result;
				ensure_aggregate_constructors_for_init(result, expr.node);
				vector<Expr> args;
				for (size_t i = 0; i < expr.node.children.size(); ++i)
				{
					Expr arg;
					arg.valid = true;
					arg.node = expr.node.children[i];
					arg.type = arg.node.type;
					arg.category = arg.node.category;
					arg.binding = arg.node.binding;
					args.push_back(arg);
				}
				try
				{
					expr = make_constructor_init_expr(result, args, true);
				}
				catch (const runtime_error&)
				{
					Conversion conv = convert_to(expr, result);
					if (!conv.viable)
						throw runtime_error("invalid return conversion");
					expr = conv.expr;
				}
			}
			else if (result_record->kind == pa11::TypeKind::Record &&
			         expr_record->kind != pa11::TypeKind::Record)
			{
				vector<Expr> args;
				args.push_back(expr);
				try
				{
					expr = make_constructor_init_expr(result, args, true);
				}
				catch (const runtime_error&)
				{
					Conversion conv = convert_to(expr, result);
					if (!conv.viable)
						throw runtime_error("invalid return conversion");
					expr = conv.expr;
				}
			}
			else if (result_record->kind == pa11::TypeKind::Record &&
			         expr_record->kind == pa11::TypeKind::Record &&
			         pa11::same_type(result_record, expr_record))
			{
				bool local_return =
					expr.binding != NULL &&
					expr.binding->kind == BindingKind::Variable &&
					expr.binding->owner != NULL &&
					expr.binding->owner->kind != ScopeKind::Namespace &&
					expr.binding->owner->kind != ScopeKind::Class;
				bool use_move =
					expr.category != ValueCategory::LValue || local_return;
				if (use_move &&
				    !copy_move_constructor_available(result, true))
					use_move = false;
				if (!copy_move_constructor_available(result, use_move))
					throw runtime_error("invalid return conversion");
				ensure_copy_move_constructor(result, use_move);
			}
			else
			{
				Conversion conv = convert_to(expr, result);
				if (!conv.viable)
					throw runtime_error("invalid return conversion");
				expr = conv.expr;
			}
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
	add_child(node, parse_block_item());
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

Node Parser::parse_condition(TypePtr target)
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
				if (!wrapper.children.empty() &&
				    wrapper.children[0].binding != NULL &&
				    target.get() != NULL &&
				    pa11::strip_cv(expression_object_type(
					    wrapper.children[0].binding->type))->kind ==
				    pa11::TypeKind::Record)
				{
					Binding* binding = wrapper.children[0].binding;
					Expr ref;
					ref.valid = true;
					ref.binding = binding;
					ref.type = binding->type;
					ref.category = ValueCategory::LValue;
					ref.node = Node("id-expression lvalue " +
					                pa11::describe_type(binding->type) +
					                " " + binding->name);
					annotate_expr_node(ref);
					Conversion conv = convert_to(ref, target);
					if (conv.viable)
						add_child(wrapper, conv.expr.node);
				}
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
	Expr expr = parse_expression();
	if (target.get() != NULL &&
	    pa11::strip_cv(expression_object_type(expr.type))->kind ==
	    pa11::TypeKind::Record)
	{
		Conversion conv = convert_to(expr, target);
		if (conv.viable)
			expr = conv.expr;
	}
	add_child(node, expr.node);
	return node;
}

}  // namespace internal
}  // namespace pa12
