#include "pa12_expr_parser_support.h"

#include <stdexcept>

using namespace std;

namespace pa12 {
namespace internal {

void Parser::parse_type_trait_operand_list(const string& name,
                                           vector<TypePtr>& types,
                                           bool& dependent,
                                           string& spelling)
{
	expect(OP_LPAREN);
	if (!at(OP_RPAREN))
	{
		for (;;)
		{
			size_t type_begin = pos_;
			TypePtr type = parse_type_id();
			size_t type_end = pos_;
			bool pack_expansion = consume(OP_DOTS);
			if (pack_expansion)
			{
				string pack_name;
				TemplateArgument subst;
				if (type_contains_template_parameter_name(type, pack_name) &&
				    find_template_value_substitution(pack_name, subst) &&
				    subst.kind == TemplateArgumentKind::Pack)
				{
					TemplateArgument pattern =
						TemplateArgument::type_arg(type);
					pattern.pack_expansion = true;
					vector<TemplateArgument> expanded =
						expand_template_argument_pack(pattern);
					for (size_t i = 0; i < expanded.size(); ++i)
					{
						TemplateArgument elem =
							substitute_template_argument(expanded[i]);
						if (elem.kind != TemplateArgumentKind::Type)
							throw runtime_error("type pack required");
						if (!types.empty())
							spelling += ", ";
						spelling += pa11::describe_type(elem.type);
						types.push_back(elem.type);
						if (type_is_template_dependent(elem.type))
							dependent = true;
					}
					if (!consume(OP_COMMA))
						break;
					continue;
				}
				if (type_end == type_begin + 1 &&
				    parameter_pack_expansion_name(tokens_[type_begin].source) &&
				    find_template_value_substitution(tokens_[type_begin].source,
				                                     subst) &&
				    subst.kind == TemplateArgumentKind::Pack)
				{
					for (size_t i = 0; i < subst.pack.size(); ++i)
					{
						TemplateArgument elem =
							substitute_template_argument(subst.pack[i]);
						if (elem.kind != TemplateArgumentKind::Type)
							throw runtime_error("type pack required");
						if (!types.empty())
							spelling += ", ";
						spelling += pa11::describe_type(elem.type);
						types.push_back(elem.type);
						if (type_is_template_dependent(elem.type))
							dependent = true;
					}
					if (!consume(OP_COMMA))
						break;
					continue;
				}
				dependent = true;
			}
			else if (type_is_template_dependent(type))
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
	(void)name;
}

Expr Parser::make_dependent_type_trait_expr(const string& spelling)
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

bool Parser::evaluate_builtin_type_relation_trait(const string& name,
                                                  const vector<TypePtr>& types,
                                                  bool& value)
{
	if (name == "__is_same")
	{
		value = types.size() == 2 && pa11::same_type(types[0], types[1]);
		return true;
	}
	if (name == "__is_constructible" ||
	    name == "__is_nothrow_constructible" ||
	    name == "__is_trivially_constructible")
	{
		value = name == "__is_nothrow_constructible"
			? is_nothrow_constructible_type_trait(types)
			: is_constructible_type_trait(types);
		if (value && name == "__is_trivially_constructible" && !types.empty())
		{
			TypePtr target = trait_object_type(types[0]);
			if (target->kind == pa11::TypeKind::Record)
			{
				complete_template_record(target);
				if (types.size() == 2)
					value = !trait_record_has_user_copy_constructor(target);
			}
		}
		return true;
	}
	if ((name == "__is_assignable" ||
	     name == "__is_nothrow_assignable" ||
	     name == "__is_trivially_assignable") && types.size() == 2)
	{
		TypePtr lhs = pa11::strip_cv(types[0]);
		if (lhs->kind == pa11::TypeKind::LValueReference)
		{
			TypePtr object = lhs->base;
			value = !pa11::type_has_const(object);
			TypePtr record = trait_object_type(object);
			if (value && record->kind == pa11::TypeKind::Record)
			{
				complete_template_record(record);
				value = copy_move_assignment_available(record, false);
				if (value && name == "__is_trivially_assignable")
					value = !trait_record_has_user_assignment(record);
			}
		}
		return true;
	}
	if (name == "__is_convertible" && types.size() == 2)
	{
		Expr probe;
		probe.valid = true;
		probe.type = types[0];
		probe.category = pa11::is_reference_type(types[0])
			? ValueCategory::LValue : ValueCategory::PRValue;
		probe.node = Node("type-trait-probe " + pa11::describe_type(types[0]));
		try
		{
			value = convert_to(probe, types[1]).viable;
		}
		catch (const runtime_error&)
		{
			value = false;
		}
		return true;
	}
	if (name == "__is_invocable" || name == "__is_nothrow_invocable")
	{
		value = is_invocable_type_trait(types, name == "__is_nothrow_invocable");
		return true;
	}
	return false;
}

bool Parser::evaluate_unary_builtin_type_trait(const string& name,
                                               TypePtr type,
                                               bool& value)
{
	TypePtr bare = pa11::strip_cv(type);
	if (bare->kind == pa11::TypeKind::Record)
		complete_template_record(bare);
	if (name == "__is_trivially_destructible" ||
	    name == "__is_destructible" ||
	    name == "__is_trivially_copyable" ||
	    name == "__is_literal_type" ||
	    name == "__has_trivial_constructor" ||
	    name == "__has_trivial_destructor")
		value = true;
	else if (name == "__is_integral")
		value = pa11::is_integral_or_bool_type(type);
	else if (name == "__is_floating_point")
	{
		TypePtr object = pa11::strip_cv(type);
		value = object->kind == pa11::TypeKind::Fundamental &&
		        (object->fundamental == FT_FLOAT ||
		         object->fundamental == FT_DOUBLE ||
		         object->fundamental == FT_LONG_DOUBLE);
	}
	else if (name == "__is_scalar")
		value = trait_is_scalar(type);
	else if (name == "__is_enum")
		value = bare->kind == pa11::TypeKind::Enum;
	else if (name == "__is_union")
		value = bare->kind == pa11::TypeKind::Record && bare->tag == "union";
	else if (name == "__is_class")
		value = bare->kind == pa11::TypeKind::Record && bare->tag != "union";
	else if (name == "__is_function")
		value = bare->kind == pa11::TypeKind::Function;
	else if (name == "__is_empty")
		value = trait_record_is_empty(type);
	else if (name == "__is_final")
		value = bare->kind == pa11::TypeKind::Record && bare->is_final_record;
	else if (name == "__is_pod" || name == "__is_trivial")
		value = bare->kind != pa11::TypeKind::Record ||
		        !trait_record_has_nonpublic_field(type);
	else if (name == "__is_standard_layout")
		value = bare->kind != pa11::TypeKind::Record ||
		        !trait_record_has_nonpublic_field(type);
	else if (name == "__is_abstract")
		value = trait_record_is_abstract(type);
	else if (name == "__is_polymorphic")
		value = bare->kind == pa11::TypeKind::Record && bare->is_polymorphic;
	else if (name == "__has_virtual_destructor")
		value = trait_record_has_virtual_destructor(type);
	else if (name == "__is_member_pointer")
		value = bare->kind == pa11::TypeKind::MemberPointer;
	else if (name == "__is_member_object_pointer")
		value = bare->kind == pa11::TypeKind::MemberPointer &&
		        bare->base.get() != NULL &&
		        bare->base->kind != pa11::TypeKind::Function;
	else if (name == "__is_member_function_pointer")
		value = bare->kind == pa11::TypeKind::MemberPointer &&
		        bare->base.get() != NULL &&
		        bare->base->kind == pa11::TypeKind::Function;
	else if (name == "__is_complete_or_unbounded")
		value = bare->kind != pa11::TypeKind::Record || bare->complete;
	else if (name == "__reference_constructs_from_temporary" ||
	         name == "__reference_binds_to_temporary")
		value = false;
	else
		return false;
	return true;
}

bool Parser::evaluate_builtin_type_trait(const string& name,
                                         const vector<TypePtr>& types)
{
	bool value = false;
	if (evaluate_builtin_type_relation_trait(name, types, value))
		return value;
	if (!types.empty() &&
	    evaluate_unary_builtin_type_trait(name, types[0], value))
		return value;
	if (name == "__is_base_of" && types.size() == 2)
		return trait_record_derives_from(types[1], types[0]);
	return false;
}

Expr Parser::parse_builtin_type_trait_expression()
{
	if (!at_builtin_type_trait_expression())
		throw runtime_error("expected builtin type trait");
	string name = current().source;
	++pos_;
	vector<TypePtr> types;
	bool dependent = false;
	string spelling = name + "(";
	parse_type_trait_operand_list(name, types, dependent, spelling);
	if (dependent)
		return make_dependent_type_trait_expr(spelling);
	return make_bool_trait_expr(evaluate_builtin_type_trait(name, types));
}

Expr Parser::parse_is_constructible_expression()
{
	if (!at_identifier() || current().source != "__is_constructible")
		throw runtime_error("expected __is_constructible");
	++pos_;
	vector<TypePtr> types;
	bool dependent = false;
	string spelling = "__is_constructible(";
	parse_type_trait_operand_list("__is_constructible",
	                              types,
	                              dependent,
	                              spelling);
	if (types.empty())
		return make_bool_trait_expr(false);
	if (dependent)
		return make_dependent_type_trait_expr(spelling);
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
		TypePtr target_object = pa11::strip_cv(bare->base);
		TypePtr source_object = expression_object_type(types[1]);
		source_object = source_object.get() != NULL
			? pa11::strip_cv(source_object) : TypePtr();
		if (target_object.get() != NULL &&
		    source_object.get() != NULL &&
		    target_object->kind == pa11::TypeKind::Function &&
		    pa11::same_type(target_object, source_object))
			return true;
		Expr arg;
		arg.valid = true;
		arg.type = types[1];
		arg.category = call_category(types[1]);
		arg.node = Node("id-expression " + value_category_name(arg.category) +
		                " " + pa11::describe_type(types[1]) +
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
		arg.node = Node("id-expression " + value_category_name(arg.category) +
		                " " + pa11::describe_type(types[i]) +
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

bool Parser::is_nothrow_constructible_type_trait(const vector<TypePtr>& types)
{
	if (!is_constructible_type_trait(types) || types.empty())
		return false;
	TypePtr target = types[0];
	TypePtr bare = pa11::strip_cv(target);
	if (bare->kind == pa11::TypeKind::Array)
	{
		vector<TypePtr> elem;
		elem.push_back(bare->base);
		return is_nothrow_constructible_type_trait(elem);
	}
	if (bare->kind != pa11::TypeKind::Record)
		return true;
	if (types.size() == 2)
	{
		TypePtr arg = pa11::strip_cv(types[1]);
		bool move = arg->kind == pa11::TypeKind::RValueReference;
		bool copy_ref = arg->kind == pa11::TypeKind::LValueReference ||
		                arg->kind == pa11::TypeKind::RValueReference;
		if (copy_ref && pa11::same_type(pa11::strip_cv(arg->base), bare))
		{
			Binding* ctor = ensure_copy_move_constructor(bare, move);
			if (ctor == NULL && move)
				ctor = ensure_copy_move_constructor(bare, false);
			if (ctor == NULL ||
			    deleted_functions_.find(ctor) != deleted_functions_.end())
				return false;
			if (!ctor->is_generated_copy_move_constructor &&
			    !ctor->is_defaulted)
				return ctor->unwind_no;
			return true;
		}
	}
	vector<Expr> args;
	for (size_t i = 1; i < types.size(); ++i)
	{
		Expr arg;
		arg.valid = true;
		arg.type = types[i];
		arg.category = call_category(types[i]);
		arg.node = Node("id-expression " + value_category_name(arg.category) +
		                " " + pa11::describe_type(types[i]) +
		                " <constructible-arg>");
		arg.node.type = types[i];
		arg.node.category = arg.category;
		annotate_expr_node(arg);
		args.push_back(arg);
	}
	try
	{
		++unevaluated_expression_depth_;
		Expr init = make_constructor_init_expr(target, args, false);
		--unevaluated_expression_depth_;
		return node_is_noexcept(init.node);
	}
	catch (const runtime_error&)
	{
		--unevaluated_expression_depth_;
		return false;
	}
}

bool Parser::is_invocable_type_trait(const vector<TypePtr>& types,
                                     bool require_noexcept)
{
	if (types.empty())
		return false;
	Expr callee;
	callee.valid = true;
	callee.type = types[0];
	callee.category = call_category(types[0]);
	if (pa11::strip_cv(expression_object_type(types[0]))->kind ==
	    pa11::TypeKind::Function)
		callee.category = ValueCategory::LValue;
	callee.node = Node("id-expression " + value_category_name(callee.category) +
	                   " " + pa11::describe_type(types[0]) +
	                   " <invocable-callee>");
	callee.node.type = types[0];
	callee.node.category = callee.category;
	annotate_expr_node(callee);

	vector<Expr> args;
	for (size_t i = 1; i < types.size(); ++i)
	{
		Expr arg;
		arg.valid = true;
		arg.type = types[i];
		arg.category = call_category(types[i]);
		arg.node = Node("id-expression " + value_category_name(arg.category) +
		                " " + pa11::describe_type(types[i]) +
		                " <invocable-arg>");
		arg.node.type = types[i];
		arg.node.category = arg.category;
		annotate_expr_node(arg);
		args.push_back(arg);
	}

	++unevaluated_expression_depth_;
	try
	{
		Expr call = make_call_expr(callee, args);
		--unevaluated_expression_depth_;
		return !require_noexcept || node_is_noexcept(call.node);
	}
	catch (const runtime_error&)
	{
		--unevaluated_expression_depth_;
		return false;
	}
}

}  // namespace internal
}  // namespace pa12
