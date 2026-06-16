#include "pa12_expr_parser_support.h"

#include <algorithm>
#include <cctype>
#include <stdexcept>

using namespace std;

namespace pa12 {
namespace internal {


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
	if (source.size() >= 4)
	{
		string suffix4 = source.substr(source.size() - 4);
		if (suffix4 == "f128" || suffix4 == "F128")
			return pa11::make_fundamental(FT_LONG_DOUBLE);
		if (suffix4 == "bf16" || suffix4 == "BF16")
			return pa11::make_fundamental(FT_FLOAT);
	}
	if (source.size() >= 3)
	{
		string suffix3 = source.substr(source.size() - 3);
		if (suffix3 == "f16" || suffix3 == "F16" ||
		    suffix3 == "f32" || suffix3 == "F32")
			return pa11::make_fundamental(FT_FLOAT);
		if (suffix3 == "f64" || suffix3 == "F64")
			return pa11::make_fundamental(FT_DOUBLE);
	}
	if (!source.empty())
	{
		char last = source[source.size() - 1];
		if (last == 'f' || last == 'F')
			return pa11::make_fundamental(FT_FLOAT);
		if (last == 'l' || last == 'L' || last == 'q' || last == 'Q')
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

bool scope_chain_contains(Scope* scope, Scope* candidate)
{
	for (Scope* cur = scope; cur != NULL; cur = cur->parent)
		if (cur == candidate)
			return true;
	return false;
}

bool template_instance_argument_contains_template_parameter_name(
	const pa11::TemplateInstanceArgument& argument,
	string& name);

bool template_argument_contains_template_parameter_name(
	const TemplateArgument& argument,
	string& name);
pa11::TemplateInstanceArgument expr_template_instance_argument(
	const TemplateArgument& argument);

void collect_template_parameter_names_from_instance(
	const pa11::TemplateInstanceArgument& argument,
	vector<string>& names);
void collect_template_parameter_names_from_type(TypePtr type,
                                                vector<string>& names);
void collect_template_parameter_names_from_argument(
	const TemplateArgument& argument,
	vector<string>& names);

bool type_contains_template_parameter_name(TypePtr type, string& name)
{
	if (type.get() == NULL)
		return false;
	type = pa11::strip_cv(type);
	if (type->kind == pa11::TypeKind::TemplateParameter)
	{
		if (type->is_dependent_typename)
		{
			for (size_t i = 0; i < type->template_arguments.size(); ++i)
				if (template_instance_argument_contains_template_parameter_name(
					    type->template_arguments[i],
					    name))
					return true;
			for (size_t i = 0;
			     i < type->dependent_typename_template_argument_lists.size();
			     ++i)
				for (size_t j = 0;
				     j < type->dependent_typename_template_argument_lists[i].size();
				     ++j)
					if (template_instance_argument_contains_template_parameter_name(
						    type->dependent_typename_template_argument_lists[i][j],
						    name))
						return true;
		}
		if (!pa11::is_deducible_template_parameter_type(type))
			return false;
		name = type->name;
		return true;
	}
	if (type->kind == pa11::TypeKind::Pointer ||
	    type->kind == pa11::TypeKind::LValueReference ||
	    type->kind == pa11::TypeKind::RValueReference ||
	    type->kind == pa11::TypeKind::Array)
		return type_contains_template_parameter_name(type->base, name);
	if (type->kind == pa11::TypeKind::Function)
	{
		if (type_contains_template_parameter_name(type->base, name))
			return true;
		for (size_t i = 0; i < type->parameters.size(); ++i)
			if (type_contains_template_parameter_name(type->parameters[i],
			                                          name))
				return true;
	}
	if (type->kind == pa11::TypeKind::MemberPointer)
		return type_contains_template_parameter_name(type->member_class,
		                                             name) ||
		       type_contains_template_parameter_name(type->base, name);
	if (type->is_template_specialization)
		for (size_t i = 0; i < type->template_arguments.size(); ++i)
			if (template_instance_argument_contains_template_parameter_name(
				    type->template_arguments[i],
				    name))
				return true;
	return false;
}

bool template_argument_contains_template_parameter_name(
	const TemplateArgument& argument,
	string& name)
{
	if (argument.kind == TemplateArgumentKind::Type)
		return template_type_has_template_parameter_name(argument.type, name);
	if (argument.kind == TemplateArgumentKind::Value)
	{
		for (size_t i = 0;
		     i < argument.value_owner_template_arguments.size();
		     ++i)
			if (template_instance_argument_contains_template_parameter_name(
				    argument.value_owner_template_arguments[i],
				    name))
				return true;
		if (!argument.value_owner_template_name.empty())
		{
			name = argument.value_owner_template_name;
			return true;
		}
		if (argument.dependent && !argument.value_name.empty())
		{
			name = argument.value_name;
			return true;
		}
		return template_type_has_template_parameter_name(argument.type, name);
	}
	if (argument.kind == TemplateArgumentKind::Pack)
		for (size_t i = 0; i < argument.pack.size(); ++i)
			if (template_argument_contains_template_parameter_name(
				    argument.pack[i],
				    name))
				return true;
	return false;
}

void collect_template_parameter_names_from_type(TypePtr type,
                                                vector<string>& names)
{
	if (type.get() == NULL)
		return;
	type = pa11::strip_cv(type);
	if (type->kind == pa11::TypeKind::TemplateParameter)
	{
		if (!type->name.empty())
			names.push_back(type->name);
		for (size_t i = 0; i < type->template_arguments.size(); ++i)
			collect_template_parameter_names_from_instance(
				type->template_arguments[i],
				names);
		for (size_t i = 0;
		     i < type->dependent_typename_template_argument_lists.size();
		     ++i)
			for (size_t j = 0;
			     j < type->dependent_typename_template_argument_lists[i].size();
			     ++j)
				collect_template_parameter_names_from_instance(
					type->dependent_typename_template_argument_lists[i][j],
					names);
		return;
	}
	if (type->kind == pa11::TypeKind::Pointer ||
	    type->kind == pa11::TypeKind::LValueReference ||
	    type->kind == pa11::TypeKind::RValueReference ||
	    type->kind == pa11::TypeKind::Array)
		collect_template_parameter_names_from_type(type->base, names);
	else if (type->kind == pa11::TypeKind::Function)
	{
		collect_template_parameter_names_from_type(type->base, names);
		for (size_t i = 0; i < type->parameters.size(); ++i)
			collect_template_parameter_names_from_type(type->parameters[i],
			                                           names);
	}
	else if (type->kind == pa11::TypeKind::MemberPointer)
	{
		collect_template_parameter_names_from_type(type->member_class, names);
		collect_template_parameter_names_from_type(type->base, names);
	}
	if (type->is_template_specialization)
	{
		if (!type->template_primary_name.empty())
			names.push_back(type->template_primary_name);
		for (size_t i = 0; i < type->template_arguments.size(); ++i)
			collect_template_parameter_names_from_instance(
				type->template_arguments[i],
				names);
	}
}

void collect_template_parameter_names_from_argument(
	const TemplateArgument& argument,
	vector<string>& names)
{
	if (argument.kind == TemplateArgumentKind::Type)
		collect_template_parameter_names_from_type(argument.type, names);
	else if (argument.kind == TemplateArgumentKind::Value)
	{
		if (!argument.value_name.empty())
			names.push_back(argument.value_name);
		if (!argument.value_owner_template_name.empty())
			names.push_back(argument.value_owner_template_name);
		collect_template_parameter_names_from_type(argument.type, names);
		for (size_t i = 0;
		     i < argument.value_owner_template_arguments.size();
		     ++i)
			collect_template_parameter_names_from_instance(
				argument.value_owner_template_arguments[i],
				names);
	}
	else if (argument.kind == TemplateArgumentKind::Template)
	{
		if (!argument.value_name.empty())
			names.push_back(argument.value_name);
	}
	else
		for (size_t i = 0; i < argument.pack.size(); ++i)
			collect_template_parameter_names_from_argument(argument.pack[i],
			                                               names);
}

void collect_template_parameter_names_from_instance(
	const pa11::TemplateInstanceArgument& argument,
	vector<string>& names)
{
	if (argument.kind == pa11::TemplateInstanceArgumentKind::Type)
		collect_template_parameter_names_from_type(argument.type, names);
	else if (argument.kind == pa11::TemplateInstanceArgumentKind::Value)
	{
		if (!argument.value_name.empty())
			names.push_back(argument.value_name);
		if (!argument.value_owner_template_name.empty())
			names.push_back(argument.value_owner_template_name);
		collect_template_parameter_names_from_type(argument.type, names);
		for (size_t i = 0;
		     i < argument.value_owner_template_arguments.size();
		     ++i)
			collect_template_parameter_names_from_instance(
				argument.value_owner_template_arguments[i],
				names);
	}
	else if (argument.kind == pa11::TemplateInstanceArgumentKind::Template)
	{
		if (!argument.template_name.empty())
			names.push_back(argument.template_name);
	}
	else
			for (size_t i = 0; i < argument.pack.size(); ++i)
				collect_template_parameter_names_from_instance(argument.pack[i],
				                                               names);
}

pa11::TemplateInstanceArgument expr_template_instance_argument(
	const TemplateArgument& argument)
{
	if (argument.pack_expansion && argument.kind != TemplateArgumentKind::Pack)
	{
		TemplateArgument element = argument;
		element.pack_expansion = false;
		vector<pa11::TemplateInstanceArgument> pack;
		pack.push_back(expr_template_instance_argument(element));
		return pa11::TemplateInstanceArgument::pack_arg(pack);
	}
	if (argument.kind == TemplateArgumentKind::Type)
		return pa11::TemplateInstanceArgument::type_arg(argument.type);
	if (argument.kind == TemplateArgumentKind::Value)
	{
		pa11::TemplateInstanceArgument out = argument.dependent
			? pa11::TemplateInstanceArgument::dependent_value_arg(
				argument.type)
			: pa11::TemplateInstanceArgument::value_arg(argument.type,
			                                            argument.value);
		out.value_name = argument.value_name;
		out.value_negated = argument.value_negated;
		out.value_owner_template_name = argument.value_owner_template_name;
		out.value_member_name = argument.value_member_name;
		out.value_owner_template_arguments =
			argument.value_owner_template_arguments;
		out.value_expr_begin = argument.value_expr_begin;
		out.value_expr_end = argument.value_expr_end;
		return out;
	}
	if (argument.kind == TemplateArgumentKind::Template)
	{
		pa11::TemplateInstanceArgument out =
			pa11::TemplateInstanceArgument::template_arg(
				argument.template_declaration != NULL
				? qualified_template_declaration_name(
					argument.template_declaration)
				: !argument.value_name.empty()
				  ? argument.value_name
				  : string("template_parameter"));
		out.dependent = argument.template_declaration == NULL;
		return out;
	}
	vector<pa11::TemplateInstanceArgument> pack;
	for (size_t i = 0; i < argument.pack.size(); ++i)
		pack.push_back(expr_template_instance_argument(argument.pack[i]));
	pa11::TemplateInstanceArgument out =
		pa11::TemplateInstanceArgument::pack_arg(pack);
	out.value_name = argument.value_name;
	out.template_name = argument.value_name;
	return out;
}

bool template_instance_argument_contains_template_parameter_name(
	const pa11::TemplateInstanceArgument& argument,
	string& name)
{
	if (argument.kind == pa11::TemplateInstanceArgumentKind::Type)
		return type_contains_template_parameter_name(argument.type, name);
	if (argument.kind == pa11::TemplateInstanceArgumentKind::Value)
	{
		for (size_t i = 0;
		     i < argument.value_owner_template_arguments.size();
		     ++i)
			if (template_instance_argument_contains_template_parameter_name(
				    argument.value_owner_template_arguments[i],
				    name))
				return true;
		if (!argument.value_owner_template_name.empty())
		{
			name = argument.value_owner_template_name;
			return true;
		}
		if (argument.dependent && !argument.value_name.empty())
		{
			name = argument.value_name;
			return true;
		}
		return type_contains_template_parameter_name(argument.type, name);
	}
	if (argument.kind == pa11::TemplateInstanceArgumentKind::Pack)
		for (size_t i = 0; i < argument.pack.size(); ++i)
			if (template_instance_argument_contains_template_parameter_name(
				    argument.pack[i],
				    name))
				return true;
	return false;
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

Expr make_static_member_pack_element(Binding* binding)
{
	Expr out;
	if (binding == NULL)
		return out;
	out.valid = true;
	out.binding = binding;
	out.type = binding->type;
	if (out.type->kind == pa11::TypeKind::LValueReference ||
	    out.type->kind == pa11::TypeKind::RValueReference)
		out.type = out.type->base;
	if (binding->has_constant)
	{
		out.category = ValueCategory::PRValue;
		out.constant_expression = true;
		out.has_constant_value = true;
		out.constant_value = binding->constant_value;
		out.null_pointer_constant = binding->constant_value == 0;
		out.node = Node("literal prvalue " + pa11::describe_type(out.type) +
		                " " + to_string(binding->constant_value));
		out.node.token_text = to_string(binding->constant_value);
	}
	else
	{
		out.category = ValueCategory::LValue;
		out.node = Node("id-expression lvalue " +
		                pa11::describe_type(out.type) + " " + binding->name);
	}
	out.node.binding = binding;
	annotate_expr_node(out);
	return out;
}


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
	if (consume(KW_THROW))
	{
		Expr out;
		out.type = pa11::make_fundamental(FT_VOID);
		out.category = ValueCategory::PRValue;
		out.valid = true;
		out.node = Node("throw-expression prvalue void");
		if (!at(OP_SEMICOLON) && !at(OP_RPAREN))
		{
			Expr operand = parse_assignment_expression();
			TypePtr object = pa11::strip_cv(expression_object_type(operand.type));
			if (object->kind == pa11::TypeKind::Record)
				ensure_copy_move_constructor(
					object, operand.category == ValueCategory::XValue);
			add_child(out.node, operand.node);
		}
		annotate_expr_node(out);
		return out;
	}
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
	bool fold_selected_conditional = false;
	if (pa11::strip_cv(expression_object_type(cond.type))->kind ==
	    pa11::TypeKind::Record)
	{
		++explicit_conversion_context_;
		Conversion conv;
		try
		{
			conv = convert_to(cond, pa11::make_fundamental(FT_BOOL));
		}
		catch (...)
		{
			--explicit_conversion_context_;
			throw;
		}
		--explicit_conversion_context_;
		if (conv.viable)
		{
			cond = conv.expr;
			if (!cond.has_constant_value)
			{
				ConstexprValue value;
				if (try_evaluate_constexpr_expr(cond.node, value))
					apply_constexpr_value(cond, value);
			}
			fold_selected_conditional = cond.has_constant_value;
		}
	}
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
	if (fold_selected_conditional)
	{
		Expr selected = cond.constant_value != 0 ? yes : no;
		if (category == ValueCategory::PRValue &&
		    !pa11::same_type(selected.type, result_type))
		{
			Conversion conv = convert_to(selected, result_type);
			if (conv.viable)
				selected = conv.expr;
		}
		selected.type = result_type;
		selected.category = category;
		annotate_expr_node(selected);
		return selected;
	}

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
	const Expr* dependent_operand = NULL;
	if (!cond.dependent_value_name.empty())
		dependent_operand = &cond;
	else if (!yes.dependent_value_name.empty())
		dependent_operand = &yes;
	else if (!no.dependent_value_name.empty())
		dependent_operand = &no;
	if (dependent_operand != NULL)
	{
		out.dependent_value_name = dependent_operand->dependent_value_name;
		out.dependent_value_owner_template_name =
			dependent_operand->dependent_value_owner_template_name;
		out.dependent_value_member_name =
			dependent_operand->dependent_value_member_name;
		out.dependent_value_owner_template_arguments =
			dependent_operand->dependent_value_owner_template_arguments;
		out.dependent_value_negated =
			dependent_operand->dependent_value_negated;
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
		if (template_argument_expression_depth_ > 0 && at(OP_GT))
			break;
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
			bool suppress_static_member_demand =
				((op == OP_LOR && lhs.has_constant_value &&
				  lhs.constant_value != 0) ||
				 (op == OP_LAND && lhs.has_constant_value &&
				  lhs.constant_value == 0));
			if (suppress_static_member_demand)
				++short_circuit_static_member_demand_depth_;
			Expr rhs;
			try
			{
				rhs = parse_binary_expression(prec + 1);
			}
			catch (...)
			{
				if (suppress_static_member_demand)
					--short_circuit_static_member_demand_depth_;
				throw;
			}
			if (suppress_static_member_demand)
				--short_circuit_static_member_demand_depth_;
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
	if (at_identifier() && current().source == "__extension__")
	{
		++pos_;
		return parse_unary_expression();
	}
	if (at(KW_SIZEOF) || at(KW_ALIGNOF))
		return parse_type_trait_expression(current().type);
	if (at_identifier() &&
	    (current().source == "__alignof__" ||
	     current().source == "__alignof"))
		return parse_type_trait_expression(KW_ALIGNOF);
	if (at_identifier() &&
	    current().source == "__is_constructible" &&
	    lookahead(OP_LPAREN, 1))
	{
		QualifiedName trait_name;
		trait_name.name = "__is_constructible";
		trait_name.spelling = "__is_constructible";
		if (pa11::lookup_unqualified(current_scope(),
		                             "__is_constructible",
		                             pa11::LOOKUP_FUNCTION) == NULL &&
		    find_function_templates(trait_name).empty())
			return parse_is_constructible_expression();
	}
	if (at_builtin_integral_type_trait_expression())
		return parse_builtin_integral_type_trait_expression();
	if (at_builtin_type_trait_expression())
		return parse_builtin_type_trait_expression();
	if (at(KW_NOEXCEPT))
		return parse_noexcept_expression();
	if (at_identifier() &&
	    (current().source == "__real__" ||
	     current().source == "__imag__"))
	{
		++pos_;
		return parse_unary_expression();
	}
	if (at(OP_COLON2) && lookahead(KW_NEW, 1))
		return parse_new_expression();
	if (at(KW_NEW))
		return parse_new_expression();
	if (at(OP_COLON2) && lookahead(KW_DELETE, 1))
		return parse_delete_expression();
	if (at(KW_DELETE))
		return parse_delete_expression();
	TypePtr target;
	Binding* visible_call =
		at_identifier() && lookahead(OP_LPAREN, 1)
		? pa11::lookup_unqualified(current_scope(),
		                            current().source,
		                            pa11::LOOKUP_FUNCTION)
		: NULL;
	Binding* visible_value =
		at_identifier() && lookahead(OP_LPAREN, 1)
		? pa11::lookup_unqualified(current_scope(),
		                            current().source,
		                            pa11::LOOKUP_VARIABLE |
		                            pa11::LOOKUP_PARAMETER |
		                            pa11::LOOKUP_ENUMERATOR)
		: NULL;
	bool prefer_visible_call =
		(visible_call != NULL &&
		 !(visible_call->owner != NULL &&
		   visible_call->owner->kind == ScopeKind::Class &&
		   visible_call->name == visible_call->owner->name)) ||
		visible_value != NULL;
	if (prefer_visible_call && visible_call != NULL && at_identifier())
	{
		Binding* visible_type =
			pa11::lookup_unqualified(current_scope(),
			                         current().source,
			                         pa11::LOOKUP_TYPE);
		if (visible_type != NULL &&
		    visible_type->owner != visible_call->owner &&
		    scope_chain_contains(current_scope(), visible_type->owner))
			prefer_visible_call = false;
	}
	bool qualified_explicit_template_call = false;
	if (!prefer_visible_call &&
	    (at(OP_COLON2) || (at_identifier() &&
	                       (lookahead(OP_COLON2, 1) ||
	                        lookahead(OP_LT, 1)))))
	{
		size_t template_call_save = pos_;
		++direct_template_call_depth_;
		try
		{
			QualifiedName qname = parse_id_expression_name();
			qualified_explicit_template_call =
				qname.qualified &&
				qname.has_template_arguments &&
				at(OP_LPAREN) &&
				find_alias_template(qname.qualifier, qname.name) ==
					NULL &&
				find_class_template(qname.qualifier, qname.name) ==
					NULL;
		}
		catch (const exception&)
		{
			qualified_explicit_template_call = false;
		}
		--direct_template_call_depth_;
		pos_ = template_call_save;
	}
	if (qualified_explicit_template_call)
		return parse_postfix_expression();
	if (!prefer_visible_call && expression_starts_type_name(target))
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
				if (!type_is_template_dependent(target))
				{
					TypePtr target_record = pa11::strip_cv(target);
					if (target_record->kind == pa11::TypeKind::Record)
						complete_template_record(target_record);
					if (!init.node.children.empty())
					{
						vector<Expr> args;
						for (size_t i = 0; i < init.node.children.size(); ++i)
						{
							const Node& child = init.node.children[i];
							Expr arg;
							arg.valid = true;
							arg.node = child;
							arg.type = child.type;
							arg.category = child.category;
							arg.binding = child.binding;
							arg.braced_init_list =
								child.line.compare(0, 16,
								                   "braced-init-list") == 0;
							arg.has_constant_value = child.has_constant_value;
							arg.constant_value = child.constant_value;
							arg.null_pointer_constant =
								arg.has_constant_value &&
								arg.constant_value == 0 &&
								arg.type.get() != NULL &&
								pa11::is_integral_or_bool_type(arg.type);
							args.push_back(arg);
						}
						Expr constructed =
							make_constructor_init_expr(target, args, false);
						bool force_dtor =
							!pa11::record_direct_bases(pa11::strip_cv(target)).empty();
						ensure_default_destructor(target, force_dtor);
						return parse_postfix_suffixes(constructed);
					}
					ensure_aggregate_constructors_for_init(target,
					                                       init.node);
					if (!init.node.children.empty() &&
					    target_record->kind == pa11::TypeKind::Record &&
					    target_record->is_template_specialization)
						init.node.direct_call =
							ensure_aggregate_constructor(
								target_record,
								init.node.children.size());
					Binding* ctor = ensure_default_constructor(target, true);
					if (init.node.children.empty())
						init.node.direct_call = ctor;
					bool force_dtor =
						!pa11::record_direct_bases(pa11::strip_cv(target)).empty();
					ensure_default_destructor(target, force_dtor);
				}
			}
			else if (pa11::strip_cv(target)->kind != pa11::TypeKind::Array &&
			         !type_is_template_dependent(target))
			{
				if (init.node.children.empty())
				{
					Expr zero;
					zero.type = target;
					zero.valid = true;
					zero.category = ValueCategory::PRValue;
					zero.constant_expression = true;
					if (pa11::is_integral_or_bool_type(target))
					{
						zero.has_constant_value = true;
						zero.constant_value = 0;
					}
					zero.node = Node("literal prvalue " +
					                 pa11::describe_type(target) + " 0");
					zero.node.token_text = type_is_pointer(target)
						? "nullptr" : "0";
					annotate_expr_node(zero);
					return parse_postfix_suffixes(zero);
				}
				if (init.node.children.size() != 1)
					throw runtime_error("invalid braced initializer");
				const Node& child_node = init.node.children[0];
				Expr child;
				child.valid = true;
				child.node = child_node;
				child.type = child_node.type;
				child.category = child_node.category;
				child.binding = child_node.binding;
				child.has_constant_value = child_node.has_constant_value;
				child.constant_value = child_node.constant_value;
				child.null_pointer_constant =
					child.has_constant_value &&
					child.constant_value == 0 &&
					child.type.get() != NULL &&
					pa11::is_integral_or_bool_type(child.type);
				Conversion conv = convert_to(child, target);
				if (!conv.viable)
					throw runtime_error("invalid braced initializer");
				return parse_postfix_suffixes(conv.expr);
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

bool node_is_noexcept(const Node& node)
{
	if (node.direct_call != NULL &&
	    !node.direct_call->unwind_no &&
	    node.direct_call->name != "declval" &&
	    !(node.direct_call->name == "operator()" &&
	      node.direct_call->is_constexpr))
		return false;
	for (size_t i = 0; i < node.children.size(); ++i)
		if (!node_is_noexcept(node.children[i]))
			return false;
	return true;
}

bool builtin_type_trait_name(const string& name)
{
	return name == "__is_same" ||
	       name == "__is_assignable" ||
	       name == "__is_convertible" ||
	       name == "__is_invocable" ||
	       name == "__is_invocable_r" ||
	       name == "__is_nothrow_invocable" ||
	       name == "__is_nothrow_constructible" ||
	       name == "__is_nothrow_assignable" ||
	       name == "__is_trivially_constructible" ||
	       name == "__is_trivially_assignable" ||
	       name == "__is_trivially_destructible" ||
	       name == "__is_destructible" ||
	       name == "__is_trivially_copyable" ||
	       name == "__is_integral" ||
	       name == "__is_signed" ||
	       name == "__is_floating_point" ||
	       name == "__is_scalar" ||
	       name == "__is_enum" ||
	       name == "__is_union" ||
	       name == "__is_class" ||
	       name == "__is_function" ||
	       name == "__is_empty" ||
	       name == "__is_final" ||
	       name == "__is_pod" ||
	       name == "__is_trivial" ||
	       name == "__is_standard_layout" ||
	       name == "__is_abstract" ||
	       name == "__is_polymorphic" ||
	       name == "__is_literal_type" ||
	       name == "__has_virtual_destructor" ||
	       name == "__has_trivial_constructor" ||
	       name == "__has_trivial_destructor" ||
	       name == "__is_member_pointer" ||
	       name == "__is_member_object_pointer" ||
	       name == "__is_member_function_pointer" ||
	       name == "__is_base_of" ||
	       name == "__is_complete_or_unbounded" ||
	       name == "__reference_constructs_from_temporary" ||
	       name == "__reference_binds_to_temporary";
}

TypePtr trait_object_type(TypePtr type)
{
	TypePtr bare = pa11::strip_cv(type);
	if (bare->kind == pa11::TypeKind::LValueReference ||
	    bare->kind == pa11::TypeKind::RValueReference)
		return pa11::strip_cv(bare->base);
	return bare;
}

bool trait_is_scalar(TypePtr type)
{
	TypePtr bare = pa11::strip_cv(type);
	return pa11::is_integral_or_bool_type(bare) ||
	       (bare->kind == pa11::TypeKind::Fundamental &&
	        (bare->fundamental == FT_FLOAT ||
	         bare->fundamental == FT_DOUBLE ||
	         bare->fundamental == FT_LONG_DOUBLE)) ||
	       bare->kind == pa11::TypeKind::Pointer ||
	       bare->kind == pa11::TypeKind::MemberPointer ||
	       bare->kind == pa11::TypeKind::Enum ||
	       (bare->kind == pa11::TypeKind::Fundamental &&
	        bare->fundamental == FT_NULLPTR_T);
}

bool trait_record_is_empty(TypePtr record)
{
	TypePtr bare = pa11::strip_cv(record);
	if (bare->kind != pa11::TypeKind::Record)
		return false;
	pa11::layout_record_type(bare);
	for (size_t i = 0; i < bare->fields.size(); ++i)
	{
		Binding* field = bare->fields[i];
		if (field != NULL &&
		    field->is_no_unique_address &&
		    trait_record_is_empty(field->type))
			continue;
		return false;
	}
	vector<TypePtr> bases = pa11::record_direct_bases(bare);
	for (size_t i = 0; i < bases.size(); ++i)
		if (!trait_record_is_empty(bases[i]))
			return false;
	return true;
}

bool trait_record_has_virtual_destructor(TypePtr record)
{
	TypePtr bare = pa11::strip_cv(record);
	if (bare->kind != pa11::TypeKind::Record)
		return false;
	for (size_t i = 0; i < bare->virtual_entries.size(); ++i)
	{
		Binding* fn = bare->virtual_entries[i].function;
		if (fn != NULL && !fn->name.empty() && fn->name[0] == '~')
			return true;
	}
	return false;
}

bool trait_record_is_abstract(TypePtr record)
{
	TypePtr bare = pa11::strip_cv(record);
	if (bare->kind != pa11::TypeKind::Record)
		return false;
	for (size_t i = 0; i < bare->virtual_entries.size(); ++i)
	{
		Binding* fn = bare->virtual_entries[i].function;
		if (fn != NULL && fn->is_pure_virtual)
			return true;
	}
	return false;
}

bool trait_record_has_nonpublic_field(TypePtr record)
{
	TypePtr bare = pa11::strip_cv(record);
	if (bare->kind != pa11::TypeKind::Record)
		return false;
	pa11::layout_record_type(bare);
	for (size_t i = 0; i < bare->fields.size(); ++i)
		if (bare->fields[i]->is_private ||
		    bare->fields[i]->is_protected_member)
			return true;
	return false;
}

bool trait_record_derives_from(TypePtr source, TypePtr target)
{
	TypePtr wanted = pa11::strip_cv(target);
	for (TypePtr cur = pa11::strip_cv(source);
	     cur.get() != NULL && cur->kind == pa11::TypeKind::Record;
	     cur = cur->base.get() != NULL ? pa11::strip_cv(cur->base) : TypePtr())
	{
		if (pa11::same_type(cur, wanted))
			return true;
		vector<TypePtr> bases = pa11::record_direct_bases(cur);
		for (size_t i = 0; i < bases.size(); ++i)
			if (trait_record_derives_from(bases[i], wanted))
				return true;
		break;
	}
	return false;
}

bool trait_record_has_user_copy_constructor(TypePtr record)
{
	TypePtr bare = pa11::strip_cv(record);
	if (bare->kind != pa11::TypeKind::Record || bare->scope == NULL)
		return false;
	map<string, vector<Binding*> >::const_iterator ctors =
		bare->scope->members.find(bare->scope->name);
	if (ctors == bare->scope->members.end())
		return false;
	for (size_t i = 0; i < ctors->second.size(); ++i)
	{
		Binding* fn = ctors->second[i];
		if (fn == NULL || fn->type.get() == NULL ||
		    fn->type->kind != pa11::TypeKind::Function ||
		    fn->type->parameters.size() != 2)
			continue;
		TypePtr param = pa11::strip_cv(fn->type->parameters[1]);
		if ((param->kind == pa11::TypeKind::LValueReference ||
		     param->kind == pa11::TypeKind::RValueReference) &&
		    pa11::same_type(pa11::strip_cv(param->base), bare) &&
		    !fn->is_defaulted &&
		    !fn->is_generated_copy_move_constructor)
			return true;
	}
	return false;
}

bool trait_record_has_user_assignment(TypePtr record)
{
	TypePtr bare = pa11::strip_cv(record);
	if (bare->kind != pa11::TypeKind::Record || bare->scope == NULL)
		return false;
	map<string, vector<Binding*> >::const_iterator assigns =
		bare->scope->members.find("operator=");
	if (assigns == bare->scope->members.end())
		return false;
	for (size_t i = 0; i < assigns->second.size(); ++i)
	{
		Binding* fn = assigns->second[i];
		if (fn != NULL && !fn->is_defaulted &&
		    !fn->is_generated_copy_move_assignment)
			return true;
	}
	return false;
}

Expr make_bool_trait_expr(bool value)
{
	Expr out;
	out.type = pa11::make_fundamental(FT_BOOL);
	out.category = ValueCategory::PRValue;
	out.valid = true;
	out.constant_expression = true;
	out.has_constant_value = true;
	out.constant_value = value ? 1 : 0;
	out.null_pointer_constant = !value;
	out.node = Node(string("literal prvalue bool ") +
	                (value ? "KW_TRUE:true" : "KW_FALSE:false"));
	out.node.token_text = value ? "true" : "false";
	annotate_expr_node(out);
	return out;
}

bool Parser::at_builtin_type_trait_expression() const
{
	return at_identifier() &&
	       lookahead(OP_LPAREN, 1) &&
	       builtin_type_trait_name(current().source);
}

bool Parser::at_builtin_integral_type_trait_expression() const
{
	return at_identifier() &&
	       lookahead(OP_LPAREN, 1) &&
	       current().source == "__array_rank";
}

Expr Parser::parse_builtin_integral_type_trait_expression()
{
	if (!at_builtin_integral_type_trait_expression())
		throw runtime_error("expected builtin integral type trait");
	string name = current().source;
	++pos_;
	expect(OP_LPAREN);
	TypePtr type = parse_type_id();
	expect(OP_RPAREN);
	if (type_is_template_dependent(type))
	{
		Expr out;
		out.type = pa11::make_fundamental(FT_UNSIGNED_LONG_INT);
		out.category = ValueCategory::PRValue;
		out.valid = true;
		out.constant_expression = true;
		out.has_constant_value = false;
		out.dependent_value_name =
			name + "(" + pa11::describe_type(type) + ")";
		out.node = Node("type-trait-expression prvalue " +
		                pa11::describe_type(out.type));
		out.node.token_text = out.dependent_value_name;
		annotate_expr_node(out);
		return out;
	}
	uint64_t value = 0;
	TypePtr cur = pa11::strip_cv(type);
	while (cur.get() != NULL && cur->kind == pa11::TypeKind::Array)
	{
		++value;
		cur = pa11::strip_cv(cur->base);
	}
	return make_integer_literal_expr(FT_UNSIGNED_LONG_INT, value);
}

Expr Parser::parse_noexcept_expression()
{
	expect(KW_NOEXCEPT);
	expect(OP_LPAREN);
	++unevaluated_expression_depth_;
	Expr operand;
	try
	{
		operand = parse_expression();
	}
	catch (...)
	{
		--unevaluated_expression_depth_;
		throw;
	}
	--unevaluated_expression_depth_;
	expect(OP_RPAREN);
	bool dependent = type_is_template_dependent(operand.type);
	bool value = !dependent && node_is_noexcept(operand.node);
	Expr out = make_bool_trait_expr(value);
	out.constant_expression = !dependent;
	out.has_constant_value = !dependent;
	return out;
}

}  // namespace internal
}  // namespace pa12
