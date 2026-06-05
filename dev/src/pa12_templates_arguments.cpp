#include "pa12_internal.h"

#include <stdexcept>

using namespace std;

namespace pa12 {
namespace internal {
namespace {

bool template_argument_kind_matches_parameter(
	const TemplateArgument& argument,
	const TemplateParameterInfo& parameter)
{
	if (parameter.kind == TemplateParameterKind::Type)
		return argument.kind == TemplateArgumentKind::Type;
	if (parameter.kind == TemplateParameterKind::NonType)
		return argument.kind == TemplateArgumentKind::Value;
	if (argument.kind != TemplateArgumentKind::Template ||
	    argument.template_declaration == NULL)
		return false;
	const vector<TemplateParameterInfo>& params =
		argument.template_declaration->parameters;
	if (params.size() != parameter.template_parameters.size())
		return false;
	for (size_t i = 0; i < params.size(); ++i)
		if (params[i].kind != parameter.template_parameters[i].kind ||
		    params[i].is_pack != parameter.template_parameters[i].is_pack)
			return false;
	return true;
}

}  // namespace

vector<TemplateArgument> Parser::expand_template_argument_pack(
	const TemplateArgument& argument) const
{
	if (!argument.pack_expansion)
	{
		vector<TemplateArgument> single;
		single.push_back(argument);
		return single;
	}
	if (argument.kind == TemplateArgumentKind::Pack)
		return argument.pack;

	string pack_name;
	if (argument.kind == TemplateArgumentKind::Type &&
	    template_type_has_template_parameter_name(argument.type, pack_name))
	{
		TemplateArgument subst;
		if (!find_template_value_substitution(pack_name, subst) ||
		    subst.kind != TemplateArgumentKind::Pack)
		{
			vector<TemplateArgument> unresolved;
			unresolved.push_back(argument);
			return unresolved;
		}
		vector<TemplateArgument> out;
		for (size_t i = 0; i < subst.pack.size(); ++i)
		{
			if (subst.pack[i].kind != TemplateArgumentKind::Type)
				throw runtime_error("type template argument pack required");
			TypePtr expanded =
				substitute_template_type_parameter(argument.type,
				                                   pack_name,
				                                   subst.pack[i].type);
			out.push_back(TemplateArgument::type_arg(expanded));
		}
		return out;
	}
	if (argument.kind == TemplateArgumentKind::Value)
	{
		TemplateArgument subst;
		if (argument.type.get() != NULL &&
		    template_type_has_template_parameter_name(argument.type, pack_name) &&
		    find_template_value_substitution(pack_name, subst) &&
		    subst.kind == TemplateArgumentKind::Pack)
		{
			vector<TemplateArgument> out;
			for (size_t i = 0; i < subst.pack.size(); ++i)
			{
				if (subst.pack[i].kind != TemplateArgumentKind::Value)
					throw runtime_error("value template argument pack required");
				out.push_back(subst.pack[i]);
			}
			return out;
		}
		vector<TemplateArgument> unresolved;
		unresolved.push_back(argument);
		return unresolved;
	}
	throw runtime_error("unsupported template argument pack expansion");
}

void Parser::append_completed_template_pack_argument(
	TemplateDeclaration* declaration,
	size_t parameter_index,
	const vector<TemplateArgument>& explicit_expanded,
	size_t& explicit_index,
	vector<TemplateArgument>& out)
{
	const TemplateParameterInfo& parameter =
		declaration->parameters[parameter_index];
	if (explicit_index < explicit_expanded.size() &&
	    explicit_expanded[explicit_index].kind == TemplateArgumentKind::Pack)
	{
		TemplateArgument arg = explicit_expanded[explicit_index++];
		vector<TemplateArgument> flat_pack;
		for (size_t i = 0; i < arg.pack.size(); ++i)
		{
			if (arg.pack[i].kind == TemplateArgumentKind::Pack)
			{
				flat_pack.insert(flat_pack.end(),
				                 arg.pack[i].pack.begin(),
				                 arg.pack[i].pack.end());
				continue;
			}
			flat_pack.push_back(arg.pack[i]);
		}
		for (size_t i = 0; i < flat_pack.size(); ++i)
		{
			if (parameter.kind == TemplateParameterKind::Type &&
			    flat_pack[i].kind == TemplateArgumentKind::Value &&
			    flat_pack[i].type.get() != NULL &&
			    (flat_pack[i].dependent ||
			     pa11::strip_cv(flat_pack[i].type)->kind !=
				     pa11::TypeKind::Fundamental))
				flat_pack[i] = TemplateArgument::type_arg(flat_pack[i].type);
			if (!template_argument_kind_matches_parameter(flat_pack[i],
			                                              parameter))
				throw runtime_error("template pack argument kind mismatch");
		}
		out.push_back(TemplateArgument::pack_arg(flat_pack));
		return;
	}
	size_t required_after = 0;
	for (size_t j = parameter_index + 1;
	     j < declaration->parameters.size();
	     ++j)
		if (!declaration->parameters[j].is_pack &&
		    !declaration->parameters[j].has_default)
			++required_after;
	if (explicit_index + required_after > explicit_expanded.size())
		throw runtime_error("missing template argument");
	size_t take = explicit_expanded.size() - explicit_index - required_after;
	vector<TemplateArgument> pack;
	for (size_t i = 0; i < take; ++i)
	{
		TemplateArgument arg = explicit_expanded[explicit_index++];
		if (arg.kind == TemplateArgumentKind::Pack)
		{
			for (size_t p = 0; p < arg.pack.size(); ++p)
			{
				TemplateArgument elem = arg.pack[p];
				if (parameter.kind == TemplateParameterKind::Type &&
				    elem.kind == TemplateArgumentKind::Value &&
				    elem.type.get() != NULL &&
				    (elem.dependent ||
				     pa11::strip_cv(elem.type)->kind !=
					     pa11::TypeKind::Fundamental))
					elem = TemplateArgument::type_arg(elem.type);
				if (!template_argument_kind_matches_parameter(elem, parameter))
					throw runtime_error("template pack argument kind mismatch");
				pack.push_back(elem);
			}
			continue;
		}
		if (parameter.kind == TemplateParameterKind::Type &&
		    arg.kind == TemplateArgumentKind::Value &&
		    arg.type.get() != NULL &&
		    (arg.dependent ||
		     pa11::strip_cv(arg.type)->kind != pa11::TypeKind::Fundamental))
			arg = TemplateArgument::type_arg(arg.type);
		if (!template_argument_kind_matches_parameter(arg, parameter))
			throw runtime_error("template pack argument kind mismatch");
		pack.push_back(arg);
	}
	out.push_back(TemplateArgument::pack_arg(pack));
}

TemplateArgument Parser::parse_default_template_argument(
	TemplateDeclaration* declaration,
	size_t parameter_index,
	const vector<TemplateArgument>& completed_args)
{
	const TemplateParameterInfo& parameter =
		declaration->parameters[parameter_index];
	size_t save_pos = pos_;
	vector<map<string, TypePtr> > save_subst = template_type_substitutions_;
	vector<map<string, TemplateArgument> > save_value_subst =
		template_value_substitutions_;
	map<string, TypePtr> subst;
	map<string, TemplateArgument> value_subst;
	for (size_t i = 0; i < completed_args.size(); ++i)
		if (!declaration->parameters[i].name.empty())
		{
			if (declaration->parameters[i].is_pack)
			{
				subst[declaration->parameters[i].name] =
					pa11::make_template_parameter_type(
						declaration->parameters[i].name);
				value_subst[declaration->parameters[i].name] =
					completed_args[i];
			}
			else if (declaration->parameters[i].kind ==
			         TemplateParameterKind::Type)
				subst[declaration->parameters[i].name] =
					completed_args[i].type;
			else
				value_subst[declaration->parameters[i].name] =
					completed_args[i];
		}
	template_type_substitutions_.push_back(subst);
	template_value_substitutions_.push_back(value_subst);
	pos_ = parameter.default_begin;
	TemplateArgument arg;
	try
	{
		if (parameter.kind == TemplateParameterKind::Type)
			arg = TemplateArgument::type_arg(parse_type_id());
		else if (parameter.kind == TemplateParameterKind::TemplateTemplate)
		{
			if (!try_parse_template_template_argument(arg))
				throw runtime_error("invalid default template argument");
		}
		else
		{
			bool default_dependent = type_is_template_dependent(parameter.type);
			for (size_t i = 0; i < completed_args.size(); ++i)
				if (template_argument_has_template_parameter(
					    completed_args[i],
					    record_template_arguments_))
					default_dependent = true;
			int save_expression_depth = template_argument_expression_depth_;
			++template_argument_expression_depth_;
			Expr expr;
			try
			{
				expr = parse_assignment_expression();
			}
			catch (...)
			{
				template_argument_expression_depth_ = save_expression_depth;
				if (!default_dependent)
					throw;
				expr = Expr();
			}
			template_argument_expression_depth_ = save_expression_depth;
			if (expr.valid && !expr.has_constant_value)
			{
				ConstexprValue value;
				if (try_evaluate_constexpr_expr(expr.node, value) &&
				    !value.is_object)
				{
					expr.has_constant_value = true;
					expr.constant_value = value.int_value;
					expr.node.has_constant_value = true;
					expr.node.constant_value = value.int_value;
				}
			}
			if (expr.valid && !expr.has_constant_value)
			{
				try
				{
					Conversion conv =
						convert_to(expr, pa11::make_fundamental(FT_BOOL));
					if (conv.viable && !conv.expr.has_constant_value)
					{
						ConstexprValue value;
						if (try_evaluate_constexpr_expr(conv.expr.node, value))
							apply_constexpr_value(conv.expr, value);
					}
					if (conv.viable && conv.expr.has_constant_value)
						expr = conv.expr;
				}
				catch (const runtime_error&)
				{
				}
			}
			if (!expr.has_constant_value && !default_dependent)
				throw runtime_error("invalid default template argument");
			if (expr.has_constant_value)
				arg = TemplateArgument::value_arg(
					expression_object_type(expr.type),
					expr.constant_value);
			else
				arg = TemplateArgument::dependent_value_arg(parameter.type);
		}
		if (pos_ != parameter.default_end)
			throw runtime_error("invalid default template argument");
	}
	catch (...)
	{
		template_type_substitutions_ = save_subst;
		template_value_substitutions_ = save_value_subst;
		pos_ = save_pos;
		throw;
	}
	template_type_substitutions_ = save_subst;
	template_value_substitutions_ = save_value_subst;
	pos_ = save_pos;
	return arg;
}

vector<TemplateArgument> Parser::complete_template_arguments(
	TemplateDeclaration* declaration,
	const vector<TemplateArgument>& explicit_arguments)
{
	vector<TemplateArgument> explicit_expanded;
	for (size_t i = 0; i < explicit_arguments.size(); ++i)
	{
		vector<TemplateArgument> expansion =
			expand_template_argument_pack(explicit_arguments[i]);
		explicit_expanded.insert(explicit_expanded.end(),
		                         expansion.begin(),
		                         expansion.end());
	}
	vector<TemplateArgument> out;
	size_t explicit_index = 0;
	for (size_t param_index = 0;
	     param_index < declaration->parameters.size();
	     ++param_index)
	{
		const TemplateParameterInfo& parameter =
			declaration->parameters[param_index];
		if (parameter.is_pack)
		{
			append_completed_template_pack_argument(declaration,
			                                        param_index,
			                                        explicit_expanded,
			                                        explicit_index,
			                                        out);
			continue;
		}
		if (explicit_index < explicit_expanded.size())
		{
			TemplateArgument arg = explicit_expanded[explicit_index++];
			if (!template_argument_kind_matches_parameter(arg, parameter))
				throw runtime_error("template argument kind mismatch");
			out.push_back(arg);
			continue;
		}
		if (!parameter.has_default)
			throw runtime_error("missing template argument");
		out.push_back(parse_default_template_argument(declaration,
		                                             param_index,
		                                             out));
	}
	if (explicit_index != explicit_expanded.size())
		throw runtime_error("too many template arguments");
	return out;
}

}  // namespace internal
}  // namespace pa12
