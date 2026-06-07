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
	return pa11::TemplateInstanceArgument::pack_arg(pack);
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
	if (pa11::strip_cv(expression_object_type(cond.type))->kind ==
	    pa11::TypeKind::Record)
	{
		Conversion conv = convert_to(cond, pa11::make_fundamental(FT_BOOL));
		if (conv.viable)
			cond = conv.expr;
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
	if (at(KW_SIZEOF) || at(KW_ALIGNOF))
		return parse_type_trait_expression(current().type);
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
	if (at(KW_NOEXCEPT))
		return parse_noexcept_expression();
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
						pa11::strip_cv(target)->base.get() != NULL;
					ensure_default_destructor(target, force_dtor);
				}
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

namespace {

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

}  // namespace

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

Expr Parser::parse_is_constructible_expression()
{
	if (!at_identifier() || current().source != "__is_constructible")
		throw runtime_error("expected __is_constructible");
	++pos_;
	expect(OP_LPAREN);
	vector<TypePtr> types;
	bool dependent = false;
	string spelling = "__is_constructible(";
	if (!at(OP_RPAREN))
	{
		for (;;)
		{
			TypePtr type = parse_type_id();
			bool pack_expansion = consume(OP_DOTS);
			if (pack_expansion || type_is_template_dependent(type))
				dependent = true;
			if (!types.empty())
				spelling += ", ";
			spelling += pa11::describe_type(type);
			if (pack_expansion)
				spelling += "...";
			types.push_back(type);
			if (!consume(OP_COMMA))
				break;
		}
	}
	expect(OP_RPAREN);
	spelling += ")";
	if (types.empty())
		return make_bool_trait_expr(false);
	if (dependent)
	{
		Expr out;
		out.type = pa11::make_fundamental(FT_BOOL);
		out.category = ValueCategory::PRValue;
		out.valid = true;
		out.constant_expression = true;
		out.has_constant_value = false;
		out.dependent_value_name = spelling;
		out.node = Node("type-trait-expression prvalue bool");
		out.node.token_text = spelling;
		annotate_expr_node(out);
		return out;
	}
	return make_bool_trait_expr(is_constructible_type_trait(types));
}

bool Parser::is_constructible_type_trait(const vector<TypePtr>& types)
{
	if (types.empty())
		return false;
	TypePtr target = types[0];
	TypePtr bare = pa11::strip_cv(target);
	if (bare->kind == pa11::TypeKind::LValueReference ||
	    bare->kind == pa11::TypeKind::RValueReference)
	{
		if (types.size() != 2)
			return false;
		Expr arg;
		arg.valid = true;
		arg.type = types[1];
		arg.category = call_category(types[1]);
		arg.node = Node("id-expression " +
		                value_category_name(arg.category) + " " +
		                pa11::describe_type(types[1]) +
		                " <constructible-arg>");
		arg.node.type = types[1];
		arg.node.category = arg.category;
		annotate_expr_node(arg);
		try
		{
			return convert_to(arg, target).viable;
		}
		catch (const runtime_error&)
		{
			return false;
		}
	}
	if (bare->kind == pa11::TypeKind::Fundamental &&
	    bare->fundamental == FT_VOID)
		return false;
	if (bare->kind == pa11::TypeKind::Function)
		return false;
	if (types.size() == 1)
	{
		if (bare->kind == pa11::TypeKind::Array)
		{
			vector<TypePtr> elem;
			elem.push_back(bare->base);
			return is_constructible_type_trait(elem);
		}
		if (bare->kind != pa11::TypeKind::Record)
			return true;
		try
		{
			return ensure_default_constructor(target, true) != NULL;
		}
		catch (const runtime_error&)
		{
			return false;
		}
	}
	vector<Expr> args;
	for (size_t i = 1; i < types.size(); ++i)
	{
		Expr arg;
		arg.valid = true;
		arg.type = types[i];
		arg.category = call_category(types[i]);
		arg.node = Node("id-expression " +
		                value_category_name(arg.category) + " " +
		                pa11::describe_type(types[i]) +
		                " <constructible-arg>");
		arg.node.type = types[i];
		arg.node.category = arg.category;
		annotate_expr_node(arg);
		args.push_back(arg);
	}
	if (bare->kind == pa11::TypeKind::Record)
	{
		try
		{
			complete_template_record(bare);
			make_constructor_init_expr(target, args, false);
			return true;
		}
		catch (const runtime_error&)
		{
			return false;
		}
	}
	if (args.size() != 1)
		return false;
	try
	{
		return convert_to(args[0], target).viable;
	}
	catch (const runtime_error&)
	{
		return false;
	}
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

Expr Parser::parse_postfix_expression()
{
	if (at_identifier() && (lookahead(OP_LPAREN, 1) || lookahead(OP_LT, 1)))
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
				if (name.has_template_arguments)
					for (size_t i = 0; i < candidates.size(); ++i)
					{
						Binding* placeholder =
							candidates[i]->aliased_binding != NULL
							? candidates[i]->aliased_binding
							: candidates[i];
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
		}
		if (!callee.valid)
		{
			bool dependent_args = false;
			for (size_t i = 0; i < args.size(); ++i)
				if (type_is_template_dependent(args[i].type))
					dependent_args = true;
			if (!name.qualified && dependent_args)
			{
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
				return parse_postfix_suffixes(
					make_dependent_call_expr(callee, args));
			}
			throw runtime_error("name not found: " + name.spelling);
		}
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
			bool template_disambiguator = consume(KW_TEMPLATE);
			if (!template_disambiguator &&
			    type_is_template_dependent(expr.type) &&
			    ((at_identifier() && lookahead(OP_LT, 1)) ||
			     at(KW_OPERATOR)))
			{
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
			QualifiedName member_name = parse_id_expression_name();
			if (member_name.qualifier != NULL)
			{
				vector<Binding*> found =
					lookup_qualified_set(member_name.qualifier,
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
						qualifier_record->kind ==
							pa11::TypeKind::TemplateParameter ||
						type_is_template_dependent(qualifier_record);
					TypePtr object_record =
						pa11::strip_cv(expression_object_type(expr.type));
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
							expr = make_member_expr(expr,
							                        member_name.name,
							                        op);
						}
						catch (const runtime_error&)
						{
							throw runtime_error("member not found: " +
							                    member_name.name);
						}
					}
					else if (found[0]->kind != BindingKind::Function)
						expr = make_member_expr(expr, member_name.name, op);
					else
				{
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
					add_child(out.node, expr.node);
					out.node.binding = out.binding;
					out.node.has_op = true;
					out.node.op = op == "->" ? OP_ARROW : OP_DOT;
					out.node.token_text = member_name.name;
					annotate_expr_node(out);
					expr = out;
				}
			}
			else
				expr = make_member_expr(expr, member_name.name, op);
			if (member_name.has_template_arguments)
				for (size_t i = 0; i < expr.overloads.size(); ++i)
				{
					Binding* overload = expr.overloads[i];
					map<Binding*, TemplateDeclaration*>::iterator templ =
						function_template_placeholders_.find(overload);
					Binding* placeholder =
						overload->aliased_binding != NULL
						? overload->aliased_binding : overload;
					if (templ == function_template_placeholders_.end() &&
					    placeholder != overload)
						templ = function_template_placeholders_.find(
							placeholder);
					if (templ != function_template_placeholders_.end())
						expr.explicit_template_arguments[overload] =
							member_name.template_arguments;
				}
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

}  // namespace internal
}  // namespace pa12
