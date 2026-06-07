#include "pa12_expr_parser_support.h"

#include <algorithm>
#include <cctype>
#include <stdexcept>

using namespace std;

namespace pa12 {
namespace internal {

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
	{
		size_t save = pos_;
		TemplateArgument dependent;
		if (try_parse_dependent_qualified_non_type_template_argument(dependent))
		{
			Expr out;
			out.valid = true;
			out.type = dependent.type.get() != NULL
				? dependent.type
				: pa11::make_fundamental(FT_INT);
			out.category = ValueCategory::PRValue;
			out.constant_expression = true;
			out.dependent_value_name = dependent.value_name;
			out.dependent_value_owner_template_name =
				dependent.value_owner_template_name;
			out.dependent_value_member_name =
				dependent.value_member_name;
			out.dependent_value_owner_template_arguments =
				dependent.value_owner_template_arguments;
			out.dependent_value_negated = dependent.value_negated;
			out.node = Node("id-expression prvalue " +
			                pa11::describe_type(out.type) + " " +
			                dependent.value_name);
			out.node.token_text = dependent.value_name;
			annotate_expr_node(out);
			return out;
		}
		pos_ = save;
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
	type = substitute_template_type(type);
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
		complete_template_record(record);
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
		if (ctor == NULL && args.empty())
			ctor = ensure_default_constructor(record, true);
		bool dependent_new_args = false;
		for (size_t i = 0; i < args.size(); ++i)
			if (type_is_template_dependent(args[i].type) ||
			    args[i].pack_expansion)
				dependent_new_args = true;
		if (ctor == NULL &&
		    !type_is_template_dependent(record) &&
		    !dependent_new_args)
			throw runtime_error("no matching constructor for new " +
			                    pa11::describe_type(type));
		if (ctor != NULL && unevaluated_expression_depth_ == 0)
		{
			parse_pending_function_body(ctor);
			parse_pending_member_body(ctor);
		}
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
		if (info.user_defined)
		{
			QualifiedName name;
			name.name = "operator\"\"" + info.ud_suffix;
			name.spelling = name.name;
			name.has_template_arguments = true;
			vector<TemplateArgument> chars;
			TypePtr char_type = pa11::make_fundamental(FT_CHAR);
			for (size_t i = 0; i < info.prefix.size(); ++i)
				chars.push_back(TemplateArgument::value_arg(
					char_type,
					static_cast<unsigned char>(info.prefix[i])));
			name.template_arguments.push_back(
				TemplateArgument::pack_arg(chars));
			Expr callee = make_id_expr(name);
			return make_call_expr(callee, vector<Expr>());
		}
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
	size_t target_begin = pos_;
	TypePtr target = parse_type_id();
	size_t target_end = pos_;
	expect(OP_GT);
	expect(OP_LPAREN);
	Expr inner;
	try
	{
		inner = parse_expression();
	}
	catch (const runtime_error& err)
	{
		if (!replaying_dependent_decltype_ ||
		    string(err.what()).compare(0, 16, "name not found: ") != 0)
			throw;
		TypePtr object = target;
		TypePtr bare = pa11::strip_cv(target);
		if (bare->kind == pa11::TypeKind::LValueReference ||
		    bare->kind == pa11::TypeKind::RValueReference)
			object = bare->base;
		inner.valid = true;
		inner.type = object;
		inner.category = ValueCategory::LValue;
		inner.node = Node("id-expression lvalue " +
		                  pa11::describe_type(object) +
		                  " <dependent-cast-operand>");
		annotate_expr_node(inner);
	}
	expect(OP_RPAREN);
	Expr cast = make_cast_expr(target, op_leaf(kw, text), inner);
	if (!cast.pack_expansion && at(OP_DOTS))
	{
		string visible_pack_name;
		bool target_still_mentions_pack =
			type_contains_template_parameter_name(target, visible_pack_name) &&
			parameter_pack_expansion_name(visible_pack_name);
		if (!target_still_mentions_pack)
		{
			for (size_t i = target_begin; i < target_end; ++i)
				if (parameter_pack_expansion_name(tokens_[i].source))
				{
					visible_pack_name = tokens_[i].source;
					break;
				}
			TemplateArgument subst;
			if (!visible_pack_name.empty() &&
			    find_template_value_substitution(visible_pack_name, subst) &&
			    subst.kind == TemplateArgumentKind::Pack &&
			    subst.pack.size() == 1)
			{
				Expr pack;
				pack.valid = true;
				pack.pack_expansion = true;
				pack.type = target;
				pack.category = cast.category;
				pack.node = Node("pack-expression cast");
				pack.pack.push_back(cast);
				add_child(pack.node, cast.node);
				annotate_expr_node(pack);
				return pack;
			}
		}
	}
	return cast;
}

Expr Parser::parse_type_trait_expression(ETokenType keyword)
{
	const bool is_sizeof = keyword == KW_SIZEOF;
	++pos_;
	if (is_sizeof && consume(OP_DOTS))
	{
		expect(OP_LPAREN);
		string name = consume_identifier();
		expect(OP_RPAREN);
		vector<Binding*> pack;
		if (!find_function_parameter_pack_substitution(name, pack))
		{
			TemplateArgument subst;
			if (find_template_value_substitution(name, subst) &&
			    subst.kind == TemplateArgumentKind::Pack)
			{
				if (validating_template_definition_ &&
				    active_type_parameter_pack(name))
					return make_dependent_sizeof_pack_expr(name);
				return make_sizeof_expr(subst.pack.size());
			}
			if (active_type_parameter_pack(name))
				return make_dependent_sizeof_pack_expr(name);
			throw runtime_error("parameter pack not found");
		}
		return make_sizeof_expr(pack.size());
	}
	expect(OP_LPAREN);
	size_t save = pos_;
	uint64_t value = 0;
	bool parsed_type_operand = false;
	try
	{
		TypePtr type = parse_type_id();
		expect(OP_RPAREN);
		parsed_type_operand = true;
		if (type_is_template_dependent(type))
			return make_dependent_sizeof_expr(keyword, type);
		try
		{
			TypePtr bare = pa11::strip_cv(type);
			if (!type_is_template_dependent(type) &&
			    bare->kind == pa11::TypeKind::Record)
				complete_template_record(bare);
			value = is_sizeof ? pa11::type_size(type) : pa11::type_align(type);
		}
		catch (const runtime_error& err)
		{
			if (!type_is_template_dependent(type) ||
			    (string(err.what()) != "incomplete object type" &&
			     string(err.what()) != "incomplete class type"))
				throw;
			value = 8;
		}
	}
	catch (const exception&)
	{
		if (parsed_type_operand)
			throw;
		pos_ = save;
		++unevaluated_expression_depth_;
		Expr expr;
		try
		{
			expr = parse_expression();
		}
		catch (...)
		{
			--unevaluated_expression_depth_;
			throw;
		}
		--unevaluated_expression_depth_;
		expect(OP_RPAREN);
		TypePtr object_type = expression_object_type(expr.type);
		if (type_is_template_dependent(object_type))
			return make_dependent_sizeof_expr(keyword, object_type);
		try
		{
			TypePtr bare = pa11::strip_cv(object_type);
			if (!type_is_template_dependent(object_type) &&
			    bare->kind == pa11::TypeKind::Record)
				complete_template_record(bare);
			value = is_sizeof ? pa11::type_size(object_type) :
				pa11::type_align(object_type);
		}
		catch (const runtime_error& err)
		{
			if (!type_is_template_dependent(object_type) ||
			    (string(err.what()) != "incomplete object type" &&
			     string(err.what()) != "incomplete class type"))
				throw;
			value = 8;
		}
	}
	return make_sizeof_expr(value);
}

Expr Parser::parse_c_style_cast_or_parenthesized()
{
	size_t save = pos_;
	expect(OP_LPAREN);
	TypePtr target;
	bool parsed_type_id = false;
	try
	{
		target = parse_type_id();
		expect(OP_RPAREN);
		parsed_type_id = true;
	}
	catch (const exception&)
	{
	}
	if (!parsed_type_id ||
	    at(OP_RPAREN) ||
	    at(OP_COMMA) ||
	    at(OP_SEMICOLON) ||
	    at(OP_RSQUARE) ||
	    at(OP_RBRACE))
	{
		pos_ = save;
		expect(OP_LPAREN);
		int save_template_argument_depth = template_argument_expression_depth_;
		template_argument_expression_depth_ = 0;
		Expr inner;
		try
		{
			inner = parse_expression();
			expect(OP_RPAREN);
		}
		catch (...)
		{
			template_argument_expression_depth_ =
				save_template_argument_depth;
			throw;
		}
		template_argument_expression_depth_ = save_template_argument_depth;
		return parse_postfix_suffixes(inner);
	}
	Expr inner = parse_unary_expression();
	return make_cast_expr(target, "OP_LPAREN:", inner);
}

Expr Parser::parse_functional_cast(TypePtr target)
{
	expect(OP_LPAREN);
	if (pa11::strip_cv(target)->kind == pa11::TypeKind::Record)
	{
		vector<Expr> args;
		if (!at(OP_RPAREN))
			args = parse_argument_list();
		expect(OP_RPAREN);
			if (!type_is_template_dependent(target))
			{
				TypePtr target_record = pa11::strip_cv(target);
				if (target_record->kind == pa11::TypeKind::Record)
				{
					complete_template_record(target_record);
				}
				if (!args.empty())
					return make_constructor_init_expr(target, args, false);
				bool active_incomplete_default = false;
				Expr init;
				init.valid = true;
				init.type = target;
				init.category = ValueCategory::PRValue;
				init.braced_init_list = true;
				init.node = Node("braced-init-list");
				try
				{
					init.node.direct_call =
						ensure_default_constructor(target, true);
				}
				catch (const runtime_error& err)
				{
					if ((string(err.what()) != "incomplete class type" &&
					     string(err.what()) != "incomplete object type") ||
					    active_class_instantiations_.empty())
						throw;
					active_incomplete_default = true;
				}
					if (init.node.direct_call == NULL &&
					    !active_incomplete_default)
						throw runtime_error("no matching constructor");
				bool force_dtor =
					pa11::strip_cv(target)->base.get() != NULL;
				try
				{
					ensure_default_destructor(target, force_dtor);
				}
				catch (const runtime_error& err)
				{
					if ((string(err.what()) != "incomplete class type" &&
					     string(err.what()) != "incomplete object type") ||
					    active_class_instantiations_.empty())
						throw;
				}
				annotate_expr_node(init);
				return init;
			}
		Expr init;
		init.valid = true;
		init.type = target;
		init.category = ValueCategory::PRValue;
		init.braced_init_list = true;
		init.node = Node("braced-init-list");
		for (size_t i = 0; i < args.size(); ++i)
			add_child(init.node, args[i].node);
		annotate_expr_node(init);
		return init;
	}
	if (consume(OP_RPAREN))
	{
		string pack_name;
		TemplateArgument subst;
		if (type_contains_template_parameter_name(target, pack_name) &&
		    find_template_value_substitution(pack_name, subst) &&
		    subst.kind == TemplateArgumentKind::Pack)
		{
			Expr out;
			out.valid = true;
			out.pack_expansion = true;
			out.type = target;
			out.category = ValueCategory::PRValue;
			out.node = Node("pack-expression functional-cast");
			for (size_t i = 0; i < subst.pack.size(); ++i)
			{
				if (subst.pack[i].kind != TemplateArgumentKind::Type)
					throw runtime_error("type pack required");
				TypePtr element_type =
					substitute_template_type_parameter(target,
					                                   pack_name,
					                                   subst.pack[i].type);
				Expr elem;
				elem.type = element_type;
				elem.valid = true;
				elem.category = ValueCategory::PRValue;
				elem.constant_expression = true;
				if (pa11::is_integral_or_bool_type(element_type))
				{
					elem.has_constant_value = true;
					elem.constant_value = 0;
				}
				elem.node = Node("literal prvalue " +
				                 pa11::describe_type(element_type) +
				                 " 0");
				elem.node.token_text = "0";
				annotate_expr_node(elem);
				out.pack.push_back(elem);
				add_child(out.node, elem.node);
			}
			annotate_expr_node(out);
			return out;
		}
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
			if (type_is_pointer(target))
			{
				zero.null_pointer_constant = true;
				zero.node.token_text = "nullptr";
			}
			else
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
				vector<Expr> expanded;
				if (try_parse_static_member_pack_expansion(expanded))
				{
					for (size_t i = 0; i < expanded.size(); ++i)
						add_child(init.node, expanded[i].node);
					if (!consume(OP_COMMA))
						break;
					continue;
				}
				size_t child_begin = pos_;
				Expr child = parse_assignment_expression();
				size_t child_end = pos_;
				if (consume(OP_DOTS))
				{
					if (!child.pack_expansion)
					{
						vector<Expr> pattern_expansion;
						if (!try_expand_expression_pack_pattern(
							    child_begin,
							    child_end,
							    pattern_expansion))
							throw runtime_error(
								"pack expansion requires a pack");
						for (size_t i = 0; i < pattern_expansion.size(); ++i)
							add_child(init.node, pattern_expansion[i].node);
						if (!consume(OP_COMMA))
							break;
						continue;
					}
				for (size_t i = 0; i < child.pack.size(); ++i)
					add_child(init.node, child.pack[i].node);
				if (!consume(OP_COMMA))
					break;
				continue;
			}
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

bool Parser::try_parse_static_member_pack_expansion(vector<Expr>& out)
{
	size_t save = pos_;
	out.clear();
	if (!at_identifier())
		return false;
	string root = consume_identifier();
	string pack_name;
	TemplateDeclaration* owner_template = NULL;
	vector<TemplateArgument> owner_arguments;
	bool owner_is_template_id = false;
	size_t owner_arguments_begin = 0;
	size_t owner_arguments_end = 0;
	if (at(OP_LT))
	{
		owner_is_template_id = true;
		owner_arguments_begin = pos_;
		try
		{
			parse_template_argument_list(owner_arguments);
			owner_arguments_end = pos_;
		}
		catch (const exception&)
		{
			pos_ = save;
			return false;
		}
		TemplateArgument template_subst;
		if (find_template_value_substitution(root, template_subst) &&
		    template_subst.kind == TemplateArgumentKind::Template &&
		    template_subst.template_declaration != NULL)
			owner_template = template_subst.template_declaration;
		if (owner_template == NULL)
			owner_template = find_alias_template(NULL, root);
		if (owner_template == NULL)
			owner_template = find_class_template(NULL, root);
		if (owner_template == NULL)
		{
			pos_ = save;
			return false;
		}
	}
	if (!consume(OP_COLON2) || !at_identifier())
	{
		pos_ = save;
		return false;
	}
	string member_name = consume_identifier();
	if (!consume(OP_DOTS))
	{
		pos_ = save;
		return false;
	}
	if (owner_is_template_id)
	{
		vector<string> owner_parameter_names;
		for (size_t i = 0; i < owner_arguments.size(); ++i)
			collect_template_parameter_names_from_argument(
				owner_arguments[i],
				owner_parameter_names);
		for (size_t i = 0; i < owner_parameter_names.size(); ++i)
			if (parameter_pack_expansion_name(owner_parameter_names[i]))
			{
				pack_name = owner_parameter_names[i];
				break;
			}
		for (size_t i = 0; i < owner_arguments.size(); ++i)
		{
			if (!pack_name.empty())
				break;
			if (template_argument_contains_template_parameter_name(
				    owner_arguments[i],
				    pack_name))
				break;
		}
		if (pack_name.empty())
			for (size_t i = owner_arguments_begin;
			     i < owner_arguments_end;
			     ++i)
				if (parameter_pack_expansion_name(tokens_[i].source))
				{
					pack_name = tokens_[i].source;
					break;
				}
		if (pack_name.empty())
		{
			TypePtr owner_type =
				owner_template->kind == TemplateDeclarationKind::Alias
				? instantiate_alias_template(owner_template, owner_arguments)
				: instantiate_class_template(owner_template, owner_arguments);
			type_contains_template_parameter_name(owner_type, pack_name);
		}
	}
	else
	{
		pack_name = root;
	}
	if (pack_name.empty())
	{
		pos_ = save;
		return false;
	}
	if (validating_template_definition_ &&
	    active_type_parameter_pack(pack_name))
	{
		Expr elem;
		elem.valid = true;
		elem.pack_expansion = true;
		elem.type = pa11::make_fundamental(FT_INT);
		elem.category = ValueCategory::PRValue;
		elem.dependent_value_name = root + "::" + member_name;
		elem.dependent_value_owner_template_name = root;
		elem.dependent_value_member_name = member_name;
		for (size_t i = 0; i < owner_arguments.size(); ++i)
			elem.dependent_value_owner_template_arguments.push_back(
				expr_template_instance_argument(owner_arguments[i]));
		elem.node = Node("pack-expression " + elem.dependent_value_name);
		elem.node.token_text = elem.dependent_value_name;
		annotate_expr_node(elem);
		out.push_back(elem);
		return true;
	}
	TemplateArgument subst;
	if (!find_template_value_substitution(pack_name, subst) ||
	    subst.kind != TemplateArgumentKind::Pack)
	{
		pos_ = save;
		return false;
	}
	for (size_t i = 0; i < subst.pack.size(); ++i)
	{
		if (subst.pack[i].kind != TemplateArgumentKind::Type)
			throw runtime_error("type pack required");
		TypePtr record;
		if (owner_is_template_id)
		{
			vector<TemplateArgument> element_arguments;
			for (size_t j = 0; j < owner_arguments.size(); ++j)
			{
				TemplateArgument element_argument =
					substitute_template_argument_type_parameter(
						owner_arguments[j],
						pack_name,
						subst.pack[i].type);
				if (element_argument.kind == TemplateArgumentKind::Type)
				{
					TypePtr arg_type = pa11::strip_cv(element_argument.type);
					if (arg_type.get() != NULL &&
					    arg_type->kind == pa11::TypeKind::Record &&
					    arg_type->is_template_specialization &&
					    arg_type->scope == NULL &&
					    !arg_type->template_primary_name.empty())
					{
						TemplateArgument template_subst;
						bool have_template_subst =
							find_template_value_substitution(
								arg_type->template_primary_name,
								template_subst) &&
							template_subst.kind ==
								TemplateArgumentKind::Template &&
							template_subst.template_declaration != NULL;
						if (!have_template_subst)
							for (size_t ai =
								     active_class_instantiations_.size();
							     ai > 0 && !have_template_subst;
							     --ai)
							{
								TemplateDeclaration* active_decl =
									active_class_instantiations_[ai - 1].
									declaration;
								TypePtr active_type = pa11::strip_cv(
									active_class_instantiations_[ai - 1].
									type);
								map<const void*,
								    vector<TemplateArgument> >::const_iterator
									active_args =
										record_template_arguments_.find(
											active_type.get());
								if (active_decl == NULL ||
								    active_args ==
									    record_template_arguments_.end())
									continue;
								for (size_t pi = 0;
								     pi < active_decl->parameters.size() &&
								     pi < active_args->second.size();
								     ++pi)
									if (active_decl->parameters[pi].kind ==
										    TemplateParameterKind::
											    TemplateTemplate &&
									    active_decl->parameters[pi].name ==
										    arg_type->template_primary_name)
									{
										template_subst =
											substitute_template_argument(
												active_args->second[pi]);
										have_template_subst =
											template_subst.kind ==
												TemplateArgumentKind::
													Template &&
											template_subst.
												template_declaration != NULL;
										if (!have_template_subst)
											for (size_t si = 0;
											     si < active_decl->
												     class_specialization_pattern.
												     size() &&
											     si < active_type->
												     template_arguments.size();
											     ++si)
											{
												const TemplateArgument&
													pattern_arg =
														active_decl->
														class_specialization_pattern
															[si];
												if (pattern_arg.kind !=
													    TemplateArgumentKind::
														    Template ||
												    pattern_arg.
													    template_declaration !=
													    NULL ||
												    pattern_arg.value_name !=
													    arg_type->
														    template_primary_name)
													continue;
												template_subst =
													substitute_template_argument(
														template_argument_from_instance_argument(
															active_type->
																template_arguments
																	[si]));
												have_template_subst =
													template_subst.kind ==
														TemplateArgumentKind::
															Template &&
													template_subst.
														template_declaration !=
														NULL;
												if (have_template_subst)
													break;
											}
										break;
									}
							}
						if (have_template_subst)
						{
							vector<TemplateArgument> nested_arguments;
							for (size_t ti = 0;
							     ti < arg_type->template_arguments.size();
							     ++ti)
								nested_arguments.push_back(
									substitute_template_argument(
										template_argument_from_instance_argument(
											arg_type->
												template_arguments[ti])));
							element_argument =
								TemplateArgument::type_arg(
									template_subst.template_declaration->
												kind ==
											TemplateDeclarationKind::Alias
										? instantiate_alias_template(
											template_subst.
												template_declaration,
											nested_arguments)
										: instantiate_class_template(
											template_subst.
												template_declaration,
											nested_arguments));
						}
					}
				}
				element_arguments.push_back(
					substitute_template_argument(element_argument));
			}
				TypePtr pack_record = pa11::strip_cv(subst.pack[i].type);
				map<const void*, vector<TemplateArgument> >::iterator
					saved_pack_record_args =
						record_template_arguments_.end();
				vector<TemplateArgument> pack_record_args;
				bool restore_pack_record_args = false;
				if (pack_record.get() != NULL &&
				    pack_record->kind == pa11::TypeKind::Record &&
				    !pack_record->is_template_specialization &&
				    !pack_record->is_dependent_typename &&
				    pack_record->scope != NULL &&
				    pack_record->complete &&
				    pack_record->template_arguments.empty())
				{
					saved_pack_record_args =
						record_template_arguments_.find(pack_record.get());
					if (saved_pack_record_args !=
					    record_template_arguments_.end())
					{
						pack_record_args = saved_pack_record_args->second;
						restore_pack_record_args = true;
						record_template_arguments_.erase(
							saved_pack_record_args);
					}
				}
				try
				{
					record = owner_template->kind ==
						TemplateDeclarationKind::Alias
						? instantiate_alias_template(owner_template,
						                             element_arguments)
						: instantiate_class_template(owner_template,
						                             element_arguments);
				}
				catch (...)
				{
					if (restore_pack_record_args)
						record_template_arguments_[pack_record.get()] =
							pack_record_args;
					throw;
				}
				if (restore_pack_record_args)
					record_template_arguments_[pack_record.get()] =
						pack_record_args;
			}
		else
			record = subst.pack[i].type;
		try
		{
			record = substitute_template_type(record);
		}
		catch (const runtime_error&)
		{
		}
		record = pa11::strip_cv(record);
		complete_template_record(record);
		if (record->kind != pa11::TypeKind::Record || record->scope == NULL)
		{
			if (validating_template_definition_ &&
			    active_class_instantiation_dependent())
			{
				Expr elem;
				elem.valid = true;
				elem.type = pa11::make_fundamental(FT_INT);
				elem.category = ValueCategory::PRValue;
				elem.node = Node("id-expression prvalue " +
				                 pa11::describe_type(elem.type) + " " +
				                 member_name);
				elem.node.token_text = member_name;
				annotate_expr_node(elem);
				out.push_back(elem);
				return true;
			}
			if (active_class_instantiation_dependent())
			{
				pos_ = save;
				out.clear();
				return false;
			}
			throw runtime_error("pack expansion qualifier is not a record");
		}
		vector<Binding*> found =
			lookup_qualified_set(record->scope, member_name, pa11::LOOKUP_VALUE);
		if (found.empty())
			throw runtime_error("pack expansion member not found");
		out.push_back(make_static_member_pack_element(found[0]));
	}
	return true;
}

vector<Expr> Parser::parse_argument_list()
{
	vector<Expr> args;
	for (;;)
	{
		vector<Expr> expanded;
		if (try_parse_static_member_pack_expansion(expanded))
		{
			args.insert(args.end(), expanded.begin(), expanded.end());
			if (!consume(OP_COMMA))
				break;
			continue;
		}
		size_t arg_begin = pos_;
		Expr arg = parse_assignment_expression();
		size_t arg_end = pos_;
		if (consume(OP_DOTS))
		{
			if (arg.pack_expansion)
				args.insert(args.end(), arg.pack.begin(), arg.pack.end());
			else
			{
				vector<Expr> pattern_expansion;
				if (try_expand_expression_pack_pattern(arg_begin,
				                                       arg_end,
				                                       pattern_expansion))
				{
					args.insert(args.end(),
					            pattern_expansion.begin(),
					            pattern_expansion.end());
					if (!consume(OP_COMMA))
						break;
					continue;
				}
				string pack_name;
				TemplateArgument subst;
				if (!type_contains_template_parameter_name(arg.type,
				                                           pack_name) ||
				    (!find_template_value_substitution(pack_name, subst) ||
				     subst.kind != TemplateArgumentKind::Pack))
				{
					if (pack_name.empty())
						for (size_t i = arg_begin;
						     i < arg_end && i < tokens_.size();
						     ++i)
							if (parameter_pack_expansion_name(
								    tokens_[i].source))
							{
								pack_name = tokens_[i].source;
								break;
							}
					if (!pack_name.empty() &&
					    find_template_value_substitution(pack_name, subst) &&
					    subst.kind == TemplateArgumentKind::Pack)
						;
					else if (!pack_name.empty() &&
					         parameter_pack_expansion_name(pack_name))
					{
						arg.pack_expansion = true;
						arg.pack.clear();
						args.push_back(arg);
						if (!consume(OP_COMMA))
						break;
						continue;
					}
					else
						throw runtime_error(
							"pack expansion requires a pack");
				}
				for (size_t i = 0; i < subst.pack.size(); ++i)
				{
					if (subst.pack[i].kind != TemplateArgumentKind::Type)
						throw runtime_error("type pack required");
					Expr elem = arg;
					elem.pack_expansion = false;
					elem.pack.clear();
					elem.type =
						substitute_template_type_parameter(arg.type,
						                                   pack_name,
						                                   subst.pack[i].type);
					elem.node.type = elem.type;
					args.push_back(elem);
				}
			}
		}
		else
			args.push_back(arg);
		if (!consume(OP_COMMA))
			break;
	}
	return args;
}


}  // namespace internal
}  // namespace pa12
