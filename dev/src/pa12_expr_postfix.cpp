#include "pa12_expr_parser_support.h"

#include <algorithm>
#include <stdexcept>

using namespace std;

namespace pa12 {
namespace internal {

Expr Parser::parse_postfix_expression()
{
	if (at_identifier() && (lookahead(OP_LPAREN, 1) || lookahead(OP_LT, 1)))
		return parse_direct_call_postfix_expression();
	return parse_postfix_suffixes(parse_primary_expression());
}

Expr Parser::parse_direct_call_postfix_expression()
{
	size_t direct_call_save = pos_;
	QualifiedName name;
	try
	{
		name = parse_id_expression_name();
	}
	catch (const exception&)
	{
		pos_ = direct_call_save;
		return parse_postfix_suffixes(parse_primary_expression());
	}
	if (!at(OP_LPAREN))
	{
		pos_ = direct_call_save;
		return parse_postfix_suffixes(parse_primary_expression());
	}
	if (!name.qualified && name.name == "__builtin_offsetof")
	{
		expect(OP_LPAREN);
		TypePtr record = parse_type_id();
		expect(OP_COMMA);
		vector<string> members;
		if (!at_identifier())
			throw runtime_error("expected offsetof member");
		members.push_back(consume_identifier());
		while (consume(OP_DOT))
		{
			if (!at_identifier())
				throw runtime_error("expected offsetof member");
			members.push_back(consume_identifier());
		}
		expect(OP_RPAREN);
		return parse_postfix_suffixes(
			make_builtin_offsetof_expr(record, members));
	}
	if (!name.qualified && name.name == "__builtin_va_arg")
	{
		expect(OP_LPAREN);
		Expr list = parse_assignment_expression();
		expect(OP_COMMA);
		TypePtr result = parse_type_id();
		expect(OP_RPAREN);
		return parse_postfix_suffixes(make_builtin_va_arg_expr(list, result));
	}
	expect(OP_LPAREN);
	vector<Expr> args;
	if (!at(OP_RPAREN))
		args = parse_argument_list();
	expect(OP_RPAREN);
	return parse_postfix_suffixes(make_direct_named_call_expr(name, args));
}

void Parser::add_adl_call_candidates(const QualifiedName& name,
                                     const vector<Expr>& args,
                                     Expr& callee)
{
	bool ordinary_member =
		callee.valid &&
		callee.node.line.compare(0, 17, "member-expression") == 0;
	if (name.qualified || ordinary_member)
		return;

	vector<Binding*> candidates =
		callee.valid ? callee.overloads : vector<Binding*>();
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
		if (find(candidates.begin(), candidates.begin() + i, candidates[i]) !=
		    candidates.begin() + i)
			candidates.erase(candidates.begin() + i);
		else
			++i;
	}
	if (candidates.empty())
		return;

	callee.valid = true;
	callee.binding = candidates[0];
	callee.type = candidates[0]->type;
	callee.category = ValueCategory::LValue;
	callee.overloads = candidates;
	if (name.has_template_arguments)
		for (size_t i = 0; i < candidates.size(); ++i)
		{
			Binding* placeholder = candidates[i]->aliased_binding != NULL
				? candidates[i]->aliased_binding : candidates[i];
			if (function_template_placeholders_.find(placeholder) !=
			    function_template_placeholders_.end() ||
			    function_template_placeholders_.find(candidates[i]) !=
			    function_template_placeholders_.end())
				callee.explicit_template_arguments[candidates[i]] =
					name.template_arguments;
		}
	callee.node = Node("id-expression lvalue " +
	                   pa11::describe_type(callee.type) + " " +
	                   candidates[0]->name);
	annotate_expr_node(callee);
}

bool Parser::make_dependent_or_missing_direct_call(const QualifiedName& name,
                                                   const vector<Expr>& args,
                                                   Expr& out)
{
	bool dependent_args = false;
	for (size_t i = 0; i < args.size(); ++i)
		if (type_is_template_dependent(args[i].type))
			dependent_args = true;
	if (!name.qualified && dependent_args)
	{
		Expr callee;
		callee.valid = true;
		callee.type = pa11::make_dependent_typename_type(
			"__dependent_function",
			false,
			false,
			false);
		callee.category = ValueCategory::LValue;
		callee.dependent_value_name = name.spelling;
		callee.node = Node("id-expression lvalue " +
		                   pa11::describe_type(callee.type) +
		                   " " + name.spelling);
		annotate_expr_node(callee);
		out = make_dependent_call_expr(callee, args);
		return true;
	}
	if (!name.qualified)
	{
		try
		{
			Expr callee = make_missing_id_expr(name);
			if (callee.valid)
			{
				out = make_call_expr(callee, args);
				return true;
			}
		}
		catch (const runtime_error&)
		{
		}
	}
	return false;
}

Expr Parser::make_direct_named_call_expr(const QualifiedName& name,
                                         const vector<Expr>& args)
{
	Expr callee;
	try
	{
		callee = make_id_expr(name);
	}
	catch (const runtime_error&)
	{
		if (name.qualified)
			throw;
	}
	add_adl_call_candidates(name, args, callee);
	if (!callee.valid)
	{
		Expr out;
		if (make_dependent_or_missing_direct_call(name, args, out))
			return out;
		throw runtime_error("name not found: " + name.spelling);
	}
	return make_call_expr(callee, args);
}

Expr Parser::make_pseudo_destructor_suffix(Expr expr, const string& op)
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
	if (record->kind == pa11::TypeKind::Record && record->scope != NULL)
	{
		string dtor_name = "~" + record->scope->name;
		out.node.direct_call = pa11::lookup_qualified(record->scope,
		                                              dtor_name,
		                                              pa11::LOOKUP_FUNCTION);
	}
	out.node.has_op = true;
	out.node.op = op == "->" ? OP_ARROW : OP_DOT;
	add_child(out.node, expr.node);
	annotate_expr_node(out);
	return out;
}

void Parser::reject_missing_template_disambiguator(
	const Expr& expr,
	bool template_disambiguator)
{
	if (template_disambiguator ||
	    !type_is_template_dependent(expr.type) ||
	    !((at_identifier() && lookahead(OP_LT, 1)) || at(KW_OPERATOR)))
		return;
	size_t member_save = pos_;
	bool template_id = false;
	if (at(KW_OPERATOR))
	{
		consume_operator_function_name();
		if (at(OP_LT))
		{
			size_t arg_save = pos_;
			try
			{
				vector<TemplateArgument> ignored;
				parse_template_argument_list(ignored);
				template_id = true;
			}
			catch (const exception&)
			{
				pos_ = arg_save;
			}
		}
	}
	else
	{
		consume_identifier();
		try
		{
			vector<TemplateArgument> ignored;
			parse_template_argument_list(ignored);
			template_id = true;
		}
		catch (const exception&)
		{
		}
	}
	pos_ = member_save;
	if (template_id)
		throw runtime_error("missing template disambiguator");
}

Expr Parser::make_qualified_member_suffix_expr(Expr object,
                                               const QualifiedName& member_name,
                                               const string& op)
{
	vector<Binding*> found = lookup_qualified_set(member_name.qualifier,
	                                             member_name.name,
	                                             pa11::LOOKUP_VALUE);
	if (found.empty())
	{
		TypePtr qualifier_record =
			pa11::record_type_for_scope(member_name.qualifier);
		qualifier_record = qualifier_record.get() != NULL
			? pa11::strip_cv(qualifier_record) : TypePtr();
		bool dependent_qualifier =
			qualifier_record.get() == NULL ||
			qualifier_record->kind == pa11::TypeKind::TemplateParameter ||
			type_is_template_dependent(qualifier_record);
		TypePtr object_record =
			pa11::strip_cv(expression_object_type(object.type));
		if (op == "->" &&
		    object_record.get() != NULL &&
		    object_record->kind == pa11::TypeKind::Pointer)
			object_record = pa11::strip_cv(object_record->base);
		if (dependent_qualifier &&
		    object_record.get() != NULL &&
		    object_record->kind == pa11::TypeKind::Record &&
		    object_record->scope != NULL)
			found = lookup_qualified_set(object_record->scope,
			                             member_name.name,
			                             pa11::LOOKUP_VALUE);
	}
	if (found.empty())
	{
		try
		{
			return make_member_expr(object, member_name.name, op);
		}
		catch (const runtime_error&)
		{
			throw runtime_error("member not found: " + member_name.name);
		}
	}
	if (found[0]->kind != BindingKind::Function)
		return make_member_expr(object, member_name.name, op);

	vector<Binding*> overloads;
	for (size_t i = 0; i < found.size(); ++i)
		if (found[i]->kind == BindingKind::Function)
			overloads.push_back(found[i]);
	Expr out;
	out.valid = true;
	out.binding = overloads.empty() ? found[0] : overloads[0];
	out.type = out.binding->type;
	out.category = ValueCategory::LValue;
	out.overloads = overloads;
	out.node = Node("member-expression lvalue " +
	                pa11::describe_type(out.type) +
	                " OP_DOT:" + member_name.name);
	add_child(out.node, object.node);
	out.node.binding = out.binding;
	out.node.has_op = true;
	out.node.op = op == "->" ? OP_ARROW : OP_DOT;
	out.node.token_text = member_name.name;
	annotate_expr_node(out);
	return out;
}

void Parser::attach_explicit_member_template_arguments(
	Expr& expr,
	const QualifiedName& member_name)
{
	if (!member_name.has_template_arguments)
		return;
	for (size_t i = 0; i < expr.overloads.size(); ++i)
	{
		Binding* overload = expr.overloads[i];
		map<Binding*, TemplateDeclaration*>::iterator templ =
			function_template_placeholders_.find(overload);
		Binding* placeholder = overload->aliased_binding != NULL
			? overload->aliased_binding : overload;
		if (templ == function_template_placeholders_.end() &&
		    placeholder != overload)
			templ = function_template_placeholders_.find(placeholder);
		if (templ != function_template_placeholders_.end() ||
		    function_template_specialization_arguments_.find(overload) !=
		    function_template_specialization_arguments_.end())
			expr.explicit_template_arguments[overload] =
				member_name.template_arguments;
	}
}

Expr Parser::parse_member_access_postfix_suffix(Expr expr, const string& op)
{
	if (at(OP_COMPL))
		return make_pseudo_destructor_suffix(expr, op);
	bool template_disambiguator = consume(KW_TEMPLATE);
	reject_missing_template_disambiguator(expr, template_disambiguator);
	QualifiedName member_name = parse_id_expression_name();
	if (member_name.qualifier != NULL)
		expr = make_qualified_member_suffix_expr(expr, member_name, op);
	else
		expr = make_member_expr(expr, member_name.name, op);
	attach_explicit_member_template_arguments(expr, member_name);
	return expr;
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
			expr = parse_member_access_postfix_suffix(
				expr,
				tokens_[pos_ - 1].source);
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

}  // namespace internal
}  // namespace pa12
