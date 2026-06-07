#include "pa12_templates_function_support.h"

#include <algorithm>
#include <functional>
#include <stdexcept>

using namespace std;

namespace pa12 {
namespace internal {

bool Parser::deduce_function_template_arguments(
	TemplateDeclaration* declaration,
	const vector<Expr>& args,
	const vector<TemplateArgument>& explicit_arguments,
	vector<TemplateArgument>& out)
{
	if (declaration->generic_function_type.get() == NULL ||
	    declaration->generic_function_type->kind != pa11::TypeKind::Function)
		return false;
	bool has_template_parameter_pack = false;
	for (size_t i = 0; i < declaration->parameters.size(); ++i)
		if (declaration->parameters[i].is_pack)
			has_template_parameter_pack = true;
	if (explicit_arguments.size() > declaration->parameters.size() &&
	    !has_template_parameter_pack)
		return false;
	TypePtr fn = declaration->generic_function_type;
	map<string, TypePtr> deduced;
	map<string, TypePtr> fixed;
	map<string, vector<TemplateArgument> > deduced_packs;
	map<string, TemplateArgument> fixed_arguments;
	size_t explicit_index = 0;
		for (size_t i = 0;
		     i < declaration->parameters.size() &&
		     explicit_index < explicit_arguments.size();
		     ++i)
		{
			const TemplateParameterInfo& parameter = declaration->parameters[i];
			const string& pname = parameter.name;
			if (pname.empty())
			{
				TemplateArgument explicit_arg =
					explicit_arguments[explicit_index++];
				if (parameter.kind == TemplateParameterKind::Type &&
				    explicit_arg.kind != TemplateArgumentKind::Type)
					return false;
				if (parameter.kind == TemplateParameterKind::NonType &&
				    explicit_arg.kind != TemplateArgumentKind::Value)
					return false;
				if (parameter.kind == TemplateParameterKind::TemplateTemplate &&
				    explicit_arg.kind != TemplateArgumentKind::Template)
					return false;
				continue;
			}
			if (parameter.is_pack)
			{
				if (explicit_index < explicit_arguments.size() &&
				    explicit_arguments[explicit_index].kind ==
					    TemplateArgumentKind::Pack)
			{
					TemplateArgument pack_arg =
						explicit_arguments[explicit_index++];
					for (size_t p = 0; p < pack_arg.pack.size(); ++p)
						{
							if (parameter.kind ==
								    TemplateParameterKind::Type &&
							    pack_arg.pack[p].kind != TemplateArgumentKind::Type)
								return false;
							if (parameter.kind ==
								    TemplateParameterKind::NonType &&
							    pack_arg.pack[p].kind != TemplateArgumentKind::Value)
								return false;
							if (parameter.kind ==
								    TemplateParameterKind::TemplateTemplate &&
							    pack_arg.pack[p].kind != TemplateArgumentKind::Template)
								return false;
						}
					fixed_arguments[pname] = pack_arg;
					if (parameter.kind == TemplateParameterKind::Type)
						deduced_packs[pname] = pack_arg.pack;
					continue;
				}
			size_t take =
				explicit_arguments.size() - explicit_index;
			vector<TemplateArgument> pack;
			for (size_t j = 0; j < take; ++j)
			{
				vector<TemplateArgument> expansion =
					expand_template_argument_pack(
						explicit_arguments[explicit_index++]);
					for (size_t p = 0; p < expansion.size(); ++p)
						{
							if (parameter.kind ==
								    TemplateParameterKind::Type &&
							    expansion[p].kind != TemplateArgumentKind::Type)
								return false;
							if (parameter.kind ==
								    TemplateParameterKind::NonType &&
							    expansion[p].kind != TemplateArgumentKind::Value)
								return false;
							if (parameter.kind ==
								    TemplateParameterKind::TemplateTemplate &&
							    expansion[p].kind != TemplateArgumentKind::Template)
								return false;
							pack.push_back(expansion[p]);
						}
				}
				TemplateArgument pack_arg = TemplateArgument::pack_arg(pack);
				fixed_arguments[pname] = pack_arg;
				if (parameter.kind == TemplateParameterKind::Type)
					deduced_packs[pname] = pack;
				continue;
			}
			TemplateArgument explicit_arg =
				explicit_arguments[explicit_index++];
			if (parameter.kind == TemplateParameterKind::Type)
			{
				if (explicit_arg.kind != TemplateArgumentKind::Type)
					return false;
			deduced[pname] = explicit_arg.type;
			fixed[pname] = explicit_arg.type;
			fixed_arguments[pname] = explicit_arg;
			}
				else
				{
					if (parameter.kind ==
					    TemplateParameterKind::TemplateTemplate)
					{
						if (explicit_arg.kind != TemplateArgumentKind::Template)
							return false;
				}
				else if (explicit_arg.kind != TemplateArgumentKind::Value)
					return false;
				fixed_arguments[pname] = explicit_arg;
			}
	}
	if (explicit_index != explicit_arguments.size())
		return false;
	if (explicit_arguments.size() == declaration->parameters.size())
	{
		try
		{
			out = complete_template_arguments(declaration, explicit_arguments);
		}
		catch (const runtime_error&)
		{
			return false;
		}
		return true;
	}
	size_t arg_index = 0;
	if (declaration->placeholder != NULL &&
	    declaration->placeholder->owner != NULL &&
	    declaration->placeholder->owner->kind == ScopeKind::Class &&
	    !declaration->placeholder->is_static_member)
	{
		TypePtr placeholder_type = declaration->placeholder->type;
		bool generic_omits_object_parameter =
			placeholder_type.get() != NULL &&
			placeholder_type->kind == pa11::TypeKind::Function &&
			placeholder_type->parameters.size() ==
				fn->parameters.size() + 1;
		if (generic_omits_object_parameter && !args.empty())
			arg_index = 1;
	}
	for (size_t i = 0; i < fn->parameters.size(); ++i)
	{
		TypePtr pattern = fn->parameters[i];
		for (map<string, TypePtr>::const_iterator fit = fixed.begin();
		     fit != fixed.end();
		     ++fit)
			pattern = substitute_template_type_parameter(pattern,
			                                             fit->first,
			                                             fit->second);
		string pack_name;
		bool parameter_pack =
			function_parameter_pack_name(declaration, pattern, pack_name);
		size_t remaining_function_parameters =
			fn->parameters.size() - i - 1;
		if (parameter_pack)
		{
			if (arg_index + remaining_function_parameters > args.size())
				return false;
			if (remaining_function_parameters != 0)
			{
				map<string, TemplateArgument>::const_iterator fixed_pack =
					fixed_arguments.find(pack_name);
				if (fixed_pack == fixed_arguments.end())
					continue;
				if (fixed_pack->second.kind != TemplateArgumentKind::Pack)
					return false;
				if (arg_index + fixed_pack->second.pack.size() +
				    remaining_function_parameters > args.size())
					return false;
				arg_index += fixed_pack->second.pack.size();
				continue;
			}
			size_t take =
				args.size() - arg_index - remaining_function_parameters;
			vector<TemplateArgument> pack;
			for (size_t j = 0; j < take; ++j)
			{
				const Expr& actual_expr = args[arg_index + j];
				if (actual_expr.braced_init_list &&
				    actual_expr.type.get() == NULL)
					return false;
				TypePtr argument =
					expression_object_type(actual_expr.type);
				TypePtr element_pattern = pattern;
				TypePtr bare_pattern = pa11::strip_cv(element_pattern);
				map<string, TypePtr> one;
				if (bare_pattern->kind ==
				    pa11::TypeKind::RValueReference &&
				    pa11::strip_cv(bare_pattern->base)->kind ==
					    pa11::TypeKind::TemplateParameter &&
				    pa11::is_deducible_template_parameter_type(
					    pa11::strip_cv(bare_pattern->base)) &&
				    actual_expr.category == ValueCategory::LValue)
				{
					if (!deduce_template_type(
						    bare_pattern->base,
						    pa11::make_lvalue_reference(argument),
						    one,
						    &fixed,
						    &fixed_arguments))
						return false;
				}
				else
				{
					if (element_pattern->kind !=
						    pa11::TypeKind::LValueReference &&
					    element_pattern->kind !=
						    pa11::TypeKind::RValueReference)
					{
						element_pattern =
							pa11::strip_top_level_cv(element_pattern);
						argument =
							lvalue_to_rvalue_type(actual_expr.type);
					}
					if (!deduce_template_type(element_pattern,
					                          argument,
					                          one,
					                          &fixed,
					                          &fixed_arguments))
						return false;
				}
				if (!deduce_array_bound_arguments(element_pattern,
				                                  argument,
				                                  fixed_arguments))
					return false;
				map<string, TypePtr>::iterator found = one.find(pack_name);
				if (found == one.end())
					return false;
				pack.push_back(TemplateArgument::type_arg(found->second));
			}
			deduced_packs[pack_name] = pack;
			arg_index += take;
			continue;
		}
		if (arg_index >= args.size())
			break;
		if (!args[arg_index].overloads.empty())
		{
			vector<TypePtr> overload_types;
			for (size_t j = 0; j < args[arg_index].overloads.size(); ++j)
			{
				Binding* overload = args[arg_index].overloads[j];
				if (overload == NULL ||
				    overload->type.get() == NULL ||
				    overload->type->kind != pa11::TypeKind::Function)
					continue;
				bool duplicate_type = false;
				for (size_t k = 0; k < overload_types.size(); ++k)
					if (pa11::same_type(overload_types[k], overload->type))
						duplicate_type = true;
				if (!duplicate_type)
					overload_types.push_back(overload->type);
			}
			if (overload_types.empty())
				return false;
			if (overload_types.size() == 1)
			{
				bool address_overload_expr =
					args[arg_index].node.line.compare(0, 16,
					                                  "unary-expression") == 0 &&
					args[arg_index].node.has_op &&
					args[arg_index].node.op == OP_AMP;
				TypePtr argument = address_overload_expr
					? expression_object_type(args[arg_index].type)
					: overload_types[0];
				TypePtr single_pattern = pattern;
				TypePtr bare_pattern = pa11::strip_cv(single_pattern);
				if (bare_pattern->kind ==
				    pa11::TypeKind::RValueReference &&
				    pa11::strip_cv(bare_pattern->base)->kind ==
					    pa11::TypeKind::TemplateParameter &&
				    pa11::is_deducible_template_parameter_type(
					    pa11::strip_cv(bare_pattern->base)) &&
				    !address_overload_expr &&
				    args[arg_index].category == ValueCategory::LValue)
				{
					if (!deduce_template_type(
						    bare_pattern->base,
						    pa11::make_lvalue_reference(argument),
						    deduced,
						    &fixed,
						    &fixed_arguments))
						return false;
					if (!deduce_array_bound_arguments(
						    bare_pattern->base,
						    pa11::make_lvalue_reference(argument),
						    fixed_arguments))
						return false;
				}
				else
				{
					if (single_pattern->kind !=
						    pa11::TypeKind::LValueReference &&
					    single_pattern->kind !=
						    pa11::TypeKind::RValueReference)
					{
						single_pattern =
							pa11::strip_top_level_cv(single_pattern);
						argument = lvalue_to_rvalue_type(argument);
					}
					if (!deduce_template_type(single_pattern,
					                          argument,
					                          deduced,
					                          &fixed,
					                          &fixed_arguments))
						return false;
					if (!deduce_array_bound_arguments(single_pattern,
					                                  argument,
					                                  fixed_arguments))
						return false;
				}
				++arg_index;
				continue;
			}
			TypePtr bare_overload_pattern = pa11::strip_cv(pattern);
			bool accepts_overload_set =
				bare_overload_pattern->kind == pa11::TypeKind::Function ||
				(bare_overload_pattern->kind == pa11::TypeKind::Pointer &&
				 pa11::strip_cv(bare_overload_pattern->base)->kind ==
					 pa11::TypeKind::Function) ||
				((bare_overload_pattern->kind ==
				      pa11::TypeKind::LValueReference ||
				  bare_overload_pattern->kind ==
				      pa11::TypeKind::RValueReference) &&
				 pa11::strip_cv(bare_overload_pattern->base)->kind ==
					 pa11::TypeKind::Function);
				if (!accepts_overload_set)
					return false;
				bool have_match = false;
				bool ambiguous_match = false;
				map<string, TypePtr> matched_deduced;
				map<string, TemplateArgument> matched_arguments;
				vector<TypePtr> matched_types;
			for (size_t j = 0; j < args[arg_index].overloads.size(); ++j)
			{
				Binding* overload = args[arg_index].overloads[j];
				if (overload == NULL ||
				    overload->type.get() == NULL ||
				    overload->type->kind != pa11::TypeKind::Function)
					continue;
				bool duplicate_type = false;
				for (size_t k = 0; k < matched_types.size(); ++k)
					if (pa11::same_type(matched_types[k], overload->type))
						duplicate_type = true;
				if (duplicate_type)
					continue;
				TypePtr overload_argument = overload->type;
				TypePtr overload_pattern = pattern;
				if (overload_pattern->kind !=
					    pa11::TypeKind::LValueReference &&
				    overload_pattern->kind !=
					    pa11::TypeKind::RValueReference)
				{
					overload_pattern =
						pa11::strip_top_level_cv(overload_pattern);
					overload_argument =
						pa11::make_pointer(overload_argument);
				}
				map<string, TypePtr> one_deduced = deduced;
				map<string, TemplateArgument> one_arguments =
					fixed_arguments;
					if (!deduce_template_type(overload_pattern,
					                          overload_argument,
					                          one_deduced,
					                          &fixed,
					                          &one_arguments))
						continue;
					if (!deduce_array_bound_arguments(overload_pattern,
					                                  overload_argument,
					                                  one_arguments))
						continue;
					if (have_match)
					{
						ambiguous_match = true;
						continue;
					}
					have_match = true;
					matched_types.push_back(overload->type);
					matched_deduced = one_deduced;
					matched_arguments = one_arguments;
				}
				if (!have_match)
					return false;
				if (!ambiguous_match)
				{
					deduced = matched_deduced;
					fixed_arguments = matched_arguments;
				}
				++arg_index;
				continue;
			}
		TypePtr initializer_element_pattern;
		if (args[arg_index].braced_init_list &&
		    args[arg_index].type.get() == NULL &&
		    is_std_initializer_list_type(pattern,
		                                 &initializer_element_pattern))
		{
			for (size_t ci = 0; ci < args[arg_index].node.children.size(); ++ci)
			{
				const Node& child = args[arg_index].node.children[ci];
				if (!deduce_template_type(initializer_element_pattern,
				                          lvalue_to_rvalue_type(child.type),
				                          deduced,
				                          &fixed,
				                          &fixed_arguments))
					return false;
			}
			++arg_index;
			continue;
		}
		if (args[arg_index].braced_init_list &&
		    args[arg_index].type.get() == NULL)
			return false;
		TypePtr argument = expression_object_type(args[arg_index].type);
		TypePtr bare_pattern = pa11::strip_cv(pattern);
		if (bare_pattern->kind == pa11::TypeKind::RValueReference &&
		    pa11::strip_cv(bare_pattern->base)->kind ==
			    pa11::TypeKind::TemplateParameter &&
		    pa11::is_deducible_template_parameter_type(
			    pa11::strip_cv(bare_pattern->base)) &&
		    args[arg_index].category == ValueCategory::LValue)
		{
			if (!deduce_template_type(bare_pattern->base,
			                          pa11::make_lvalue_reference(argument),
			                          deduced,
			                          &fixed,
			                          &fixed_arguments))
				return false;
			if (!deduce_array_bound_arguments(
				    bare_pattern->base,
				    pa11::make_lvalue_reference(argument),
				    fixed_arguments))
				return false;
			++arg_index;
			continue;
		}
			if (pattern->kind != pa11::TypeKind::LValueReference &&
			    pattern->kind != pa11::TypeKind::RValueReference)
			{
				pattern = pa11::strip_top_level_cv(pattern);
				argument = lvalue_to_rvalue_type(args[arg_index].type);
			}
			if (!deduce_template_type(pattern,
			                          argument,
			                          deduced,
			                          &fixed,
			                          &fixed_arguments))
			{
				return false;
			}
		if (!deduce_array_bound_arguments(pattern,
		                                  argument,
		                                  fixed_arguments))
				return false;
		++arg_index;
	}
	if (arg_index != args.size() && !fn->variadic)
		return false;
	vector<TemplateArgument> explicit_args;
	for (size_t i = 0; i < declaration->parameters.size(); ++i)
	{
		const string& pname = declaration->parameters[i].name;
		if (declaration->parameters[i].is_pack)
		{
			map<string, TemplateArgument>::iterator fixed_pack =
				fixed_arguments.find(pname);
			if (fixed_pack != fixed_arguments.end())
				explicit_args.push_back(fixed_pack->second);
			else
			{
				map<string, vector<TemplateArgument> >::iterator found =
					deduced_packs.find(pname);
				map<string, TypePtr>::iterator scalar =
					declaration->parameters[i].kind ==
						TemplateParameterKind::Type
					? deduced.find(pname)
					: deduced.end();
				if (found == deduced_packs.end() &&
				    scalar != deduced.end())
				{
					vector<TemplateArgument> pack;
					pack.push_back(TemplateArgument::type_arg(
						scalar->second));
					explicit_args.push_back(
						TemplateArgument::pack_arg(pack));
				}
				else if (found == deduced_packs.end())
					explicit_args.push_back(
						TemplateArgument::pack_arg(
							vector<TemplateArgument>()));
				else
					explicit_args.push_back(
						TemplateArgument::pack_arg(found->second));
			}
			continue;
		}
		if (declaration->parameters[i].kind ==
		    TemplateParameterKind::Type)
		{
				map<string, TypePtr>::iterator found = deduced.find(pname);
				if (found == deduced.end())
					break;
			explicit_args.push_back(
				TemplateArgument::type_arg(found->second));
		}
		else
		{
			map<string, TemplateArgument>::iterator found =
				fixed_arguments.find(pname);
			if (found == fixed_arguments.end())
				break;
			explicit_args.push_back(found->second);
		}
	}
	try
	{
		out = complete_template_arguments(declaration, explicit_args);
	}
	catch (const runtime_error&)
	{
		return false;
	}
	return out.size() == declaration->parameters.size();
}

}  // namespace internal
}  // namespace pa12
