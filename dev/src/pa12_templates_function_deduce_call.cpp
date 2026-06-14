#include "pa12_templates_function_support.h"
#include "pa12_templates_instance_support.h"

#include <algorithm>
#include <functional>
#include <stdexcept>

using namespace std;

namespace pa12 {
namespace internal {
namespace {

bool is_member_function_pointer_pattern(TypePtr type)
{
	TypePtr bare = pa11::strip_cv(type);
	return bare->kind == pa11::TypeKind::MemberPointer &&
	       bare->base.get() != NULL &&
	       bare->base->kind == pa11::TypeKind::Function;
}

bool pattern_mentions_function_template_parameter(
	TemplateDeclaration* declaration,
	TypePtr pattern,
	const map<const void*, vector<TemplateArgument> >& record_arguments)
{
	for (size_t i = 0; i < declaration->parameters.size(); ++i)
	{
		const TemplateParameterInfo& parameter = declaration->parameters[i];
		if (parameter.name.empty())
			continue;
		if (type_contains_parameter_name(pattern,
		                                 parameter.name,
		                                 record_arguments))
			return true;
	}
	return false;
}

TypePtr member_function_pointer_argument_type(Binding* binding)
{
	if (binding == NULL ||
	    binding->owner == NULL ||
	    binding->owner->kind != ScopeKind::Class ||
	    binding->type.get() == NULL ||
	    binding->type->kind != pa11::TypeKind::Function ||
	    binding->type->parameters.empty())
		return TypePtr();
	TypePtr this_type = binding->type->parameters[0];
	TypePtr class_type = this_type.get() == NULL ? TypePtr() :
		pa11::strip_cv(pa11::strip_cv(this_type)->base);
	vector<TypePtr> params;
	for (size_t i = 1; i < binding->type->parameters.size(); ++i)
		params.push_back(binding->type->parameters[i]);
	TypePtr member_fn =
		pa11::make_function(binding->type->base,
		                    params,
		                    binding->type->variadic);
	if (this_type.get() != NULL &&
	    pa11::strip_cv(this_type)->kind == pa11::TypeKind::Pointer)
		member_fn->cv = pa11::strip_cv(this_type)->base->kind ==
			pa11::TypeKind::Cv ? this_type->base->cv : pa11::CV_NONE;
	member_fn->ref_qualifier = binding->ref_qualifier;
	return pa11::make_member_pointer(class_type, member_fn);
}

bool template_argument_matches_parameter_kind(const TemplateParameterInfo& parameter,
                                              const TemplateArgument& arg)
{
	if (parameter.kind == TemplateParameterKind::Type)
		return arg.kind == TemplateArgumentKind::Type;
	if (parameter.kind == TemplateParameterKind::NonType)
		return arg.kind == TemplateArgumentKind::Value;
	if (parameter.kind == TemplateParameterKind::TemplateTemplate)
		return arg.kind == TemplateArgumentKind::Template;
	return false;
}

bool hosted_library_template_declaration(const TemplateDeclaration* declaration)
{
	if (declaration == NULL)
		return false;
	Scope* scope =
		declaration->placeholder != NULL
		? declaration->placeholder->owner
		: declaration->owner;
	for (; scope != NULL; scope = scope->parent)
		if (scope->kind == ScopeKind::Namespace &&
		    (scope->name == "std" || scope->name == "__gnu_cxx"))
			return true;
	return false;
}

TemplateArgument dependent_default_template_argument(
	const TemplateDeclaration* declaration,
	const TemplateParameterInfo& parameter,
	size_t index)
{
	if (parameter.kind == TemplateParameterKind::Type)
	{
		string name = parameter.name.empty()
			? declaration->name + "__default" + to_string(index)
			: parameter.name;
		return TemplateArgument::type_arg(
			pa11::make_dependent_typename_type(name,
			                                   false,
			                                   false,
			                                   false));
	}
	TypePtr type = parameter.type.get() != NULL
		? parameter.type : pa11::make_fundamental(FT_INT);
	return TemplateArgument::dependent_value_arg(type);
}

bool call_parameter_pack_name(TemplateDeclaration* declaration,
                              TypePtr pattern,
                              string& name)
{
	if (pattern.get() == NULL)
		return false;
	TypePtr bare = pa11::strip_cv(pattern);
	if (bare->kind == pa11::TypeKind::Pointer ||
	    bare->kind == pa11::TypeKind::LValueReference ||
	    bare->kind == pa11::TypeKind::RValueReference ||
	    bare->kind == pa11::TypeKind::Array)
	{
		TypePtr base = bare->base.get() != NULL
			? pa11::strip_cv(bare->base) : TypePtr();
		if (base.get() != NULL && base->kind == pa11::TypeKind::Function)
			return false;
		return call_parameter_pack_name(declaration, bare->base, name);
	}
	if (bare->kind == pa11::TypeKind::Function)
		return false;
	if (bare->kind == pa11::TypeKind::MemberPointer)
	{
		TypePtr base = bare->base.get() != NULL
			? pa11::strip_cv(bare->base) : TypePtr();
		if (base.get() != NULL && base->kind == pa11::TypeKind::Function)
			return false;
	}
	return function_parameter_pack_name(declaration, pattern, name);
}

}  // namespace

bool Parser::deduce_explicit_single_template_argument(
	const TemplateParameterInfo& parameter,
	const TemplateArgument& explicit_arg,
	map<string, TypePtr>& deduced,
	map<string, TypePtr>& fixed,
	map<string, TemplateArgument>& fixed_arguments) const
{
	if (!template_argument_matches_parameter_kind(parameter, explicit_arg))
		return false;
	if (parameter.name.empty())
		return true;
	if (parameter.kind == TemplateParameterKind::Type)
	{
		deduced[parameter.name] = explicit_arg.type;
		fixed[parameter.name] = explicit_arg.type;
	}
	fixed_arguments[parameter.name] = explicit_arg;
	return true;
}

bool Parser::deduce_explicit_pack_template_argument(
	const TemplateParameterInfo& parameter,
	const vector<TemplateArgument>& explicit_arguments,
	size_t& explicit_index,
	map<string, vector<TemplateArgument> >& deduced_packs,
	map<string, TemplateArgument>& fixed_arguments) const
{
	vector<TemplateArgument> pack;
	if (explicit_index < explicit_arguments.size() &&
	    explicit_arguments[explicit_index].kind == TemplateArgumentKind::Pack)
	{
		TemplateArgument pack_arg = explicit_arguments[explicit_index++];
		for (size_t p = 0; p < pack_arg.pack.size(); ++p)
			if (!template_argument_matches_parameter_kind(parameter,
			                                             pack_arg.pack[p]))
				return false;
		fixed_arguments[parameter.name] = pack_arg;
		if (parameter.kind == TemplateParameterKind::Type)
			deduced_packs[parameter.name] = pack_arg.pack;
		return true;
	}
	size_t take = explicit_arguments.size() - explicit_index;
	for (size_t j = 0; j < take; ++j)
	{
		vector<TemplateArgument> expansion =
			expand_template_argument_pack(explicit_arguments[explicit_index++]);
		for (size_t p = 0; p < expansion.size(); ++p)
		{
			if (!template_argument_matches_parameter_kind(parameter,
			                                             expansion[p]))
				return false;
			pack.push_back(expansion[p]);
		}
	}
	TemplateArgument pack_arg = TemplateArgument::pack_arg(pack);
	fixed_arguments[parameter.name] = pack_arg;
	if (parameter.kind == TemplateParameterKind::Type)
		deduced_packs[parameter.name] = pack;
	return true;
}

bool Parser::deduce_explicit_function_template_arguments(
	TemplateDeclaration* declaration,
	const vector<TemplateArgument>& explicit_arguments,
	map<string, TypePtr>& deduced,
	map<string, TypePtr>& fixed,
	map<string, vector<TemplateArgument> >& deduced_packs,
	map<string, TemplateArgument>& fixed_arguments,
	vector<TemplateArgument>& out,
	bool& complete)
{
	complete = false;
	size_t explicit_index = 0;
	for (size_t i = 0;
	     i < declaration->parameters.size() &&
	     explicit_index < explicit_arguments.size();
	     ++i)
	{
		const TemplateParameterInfo& parameter = declaration->parameters[i];
		if (parameter.name.empty())
		{
			if (!deduce_explicit_single_template_argument(
				    parameter,
				    explicit_arguments[explicit_index++],
				    deduced,
				    fixed,
				    fixed_arguments))
				return false;
			continue;
		}
		if (parameter.is_pack)
		{
			if (!deduce_explicit_pack_template_argument(parameter,
			                                           explicit_arguments,
			                                           explicit_index,
			                                           deduced_packs,
			                                           fixed_arguments))
				return false;
			continue;
		}
		if (!deduce_explicit_single_template_argument(
			    parameter,
			    explicit_arguments[explicit_index++],
			    deduced,
			    fixed,
			    fixed_arguments))
			return false;
	}
	if (explicit_index != explicit_arguments.size())
		return false;
	if (explicit_arguments.size() != declaration->parameters.size())
		return true;
	try
	{
		out = complete_template_arguments(declaration, explicit_arguments);
	}
	catch (const runtime_error&)
	{
		return false;
	}
	complete = true;
	return true;
}

bool Parser::deduce_function_template_parameter_pack(
	TemplateDeclaration* declaration,
	TypePtr pattern,
	const string& pack_name,
	size_t remaining_function_parameters,
	const vector<Expr>& args,
	map<string, TypePtr>& deduced,
	map<string, TypePtr>& fixed,
	map<string, vector<TemplateArgument> >& deduced_packs,
	map<string, TemplateArgument>& fixed_arguments,
	size_t& arg_index) const
{
	if (arg_index + remaining_function_parameters > args.size())
		return false;
	if (remaining_function_parameters != 0)
	{
		map<string, TemplateArgument>::const_iterator fixed_pack =
			fixed_arguments.find(pack_name);
		if (fixed_pack == fixed_arguments.end())
			return true;
		if (fixed_pack->second.kind != TemplateArgumentKind::Pack)
			return false;
		if (arg_index + fixed_pack->second.pack.size() +
		    remaining_function_parameters > args.size())
			return false;
		arg_index += fixed_pack->second.pack.size();
		return true;
	}
	size_t take = args.size() - arg_index - remaining_function_parameters;
	vector<TemplateArgument> pack;
	for (size_t j = 0; j < take; ++j)
	{
		const Expr& actual_expr = args[arg_index + j];
		if (actual_expr.braced_init_list && actual_expr.type.get() == NULL)
			return false;
		TypePtr argument = expression_object_type(actual_expr.type);
		TypePtr element_pattern = pattern;
		TypePtr bare_pattern = pa11::strip_cv(element_pattern);
		map<string, TypePtr> one;
		if (bare_pattern->kind == pa11::TypeKind::RValueReference &&
		    pa11::strip_cv(bare_pattern->base)->kind ==
			    pa11::TypeKind::TemplateParameter &&
		    pa11::is_deducible_template_parameter_type(
			    pa11::strip_cv(bare_pattern->base)) &&
		    actual_expr.category == ValueCategory::LValue)
		{
			if (!deduce_template_type(bare_pattern->base,
			                          pa11::make_lvalue_reference(argument),
			                          one,
			                          &fixed,
			                          &fixed_arguments))
				return false;
		}
		else
		{
			if (element_pattern->kind != pa11::TypeKind::LValueReference &&
			    element_pattern->kind != pa11::TypeKind::RValueReference)
			{
				element_pattern = pa11::strip_top_level_cv(element_pattern);
				argument = lvalue_to_rvalue_type(actual_expr.type);
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
		one.erase(found);
		for (map<string, TypePtr>::const_iterator oi = one.begin();
		     oi != one.end();
		     ++oi)
		{
			map<string, TypePtr>::const_iterator fi = fixed.find(oi->first);
			if (fi != fixed.end() &&
			    !pa11::same_type(fi->second, oi->second))
				return false;
			map<string, TypePtr>::iterator existing = deduced.find(oi->first);
			if (existing == deduced.end())
				deduced[oi->first] = oi->second;
			else if (!pa11::same_type(existing->second, oi->second))
				return false;
		}
	}
	deduced_packs[pack_name] = pack;
	arg_index += take;
	(void)declaration;
	return true;
}

bool Parser::deduce_single_overload_template_argument(
	TypePtr pattern,
	const Expr& actual,
	const vector<TypePtr>& overload_types,
	map<string, TypePtr>& deduced,
	map<string, TypePtr>& fixed,
	map<string, TemplateArgument>& fixed_arguments) const
{
	bool address_overload_expr =
		actual.node.line.compare(0, 16, "unary-expression") == 0 &&
		actual.node.has_op &&
		actual.node.op == OP_AMP;
	TypePtr argument = address_overload_expr
		? expression_object_type(actual.type) : overload_types[0];
	TypePtr single_pattern = pattern;
	TypePtr bare_pattern = pa11::strip_cv(single_pattern);
	if (bare_pattern->kind == pa11::TypeKind::RValueReference &&
	    pa11::strip_cv(bare_pattern->base)->kind ==
		    pa11::TypeKind::TemplateParameter &&
	    pa11::is_deducible_template_parameter_type(
		    pa11::strip_cv(bare_pattern->base)) &&
	    !address_overload_expr &&
	    actual.category == ValueCategory::LValue)
	{
		if (!deduce_template_type(bare_pattern->base,
		                          pa11::make_lvalue_reference(argument),
		                          deduced,
		                          &fixed,
		                          &fixed_arguments))
			return false;
		return deduce_array_bound_arguments(
			bare_pattern->base,
			pa11::make_lvalue_reference(argument),
			fixed_arguments);
	}
	if (single_pattern->kind != pa11::TypeKind::LValueReference &&
	    single_pattern->kind != pa11::TypeKind::RValueReference)
	{
		single_pattern = pa11::strip_top_level_cv(single_pattern);
		argument = lvalue_to_rvalue_type(argument);
	}
	return deduce_template_type(single_pattern,
	                            argument,
	                            deduced,
	                            &fixed,
	                            &fixed_arguments) &&
	       deduce_array_bound_arguments(single_pattern,
	                                    argument,
	                                    fixed_arguments);
}

bool Parser::deduce_overload_set_template_argument(
	TypePtr pattern,
	const Expr& actual,
	map<string, TypePtr>& deduced,
	map<string, TypePtr>& fixed,
	map<string, TemplateArgument>& fixed_arguments) const
{
	TypePtr bare_overload_pattern = pa11::strip_cv(pattern);
	bool accepts_overload_set =
		bare_overload_pattern->kind == pa11::TypeKind::Function ||
		(bare_overload_pattern->kind == pa11::TypeKind::Pointer &&
		 pa11::strip_cv(bare_overload_pattern->base)->kind ==
			 pa11::TypeKind::Function) ||
		is_member_function_pointer_pattern(bare_overload_pattern) ||
		((bare_overload_pattern->kind == pa11::TypeKind::LValueReference ||
		  bare_overload_pattern->kind == pa11::TypeKind::RValueReference) &&
		 pa11::strip_cv(bare_overload_pattern->base)->kind ==
			 pa11::TypeKind::Function);
	if (!accepts_overload_set)
		return false;
	bool have_match = false;
	bool ambiguous_match = false;
	map<string, TypePtr> matched_deduced;
	map<string, TemplateArgument> matched_arguments;
	vector<TypePtr> matched_types;
	for (size_t j = 0; j < actual.overloads.size(); ++j)
	{
		Binding* overload = actual.overloads[j];
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
		bool member_pointer_pattern =
			is_member_function_pointer_pattern(pa11::strip_cv(pattern));
		TypePtr overload_argument = member_pointer_pattern
			? member_function_pointer_argument_type(overload) : overload->type;
		if (overload_argument.get() == NULL)
			continue;
		TypePtr overload_pattern = pattern;
		if (!member_pointer_pattern &&
		    overload_pattern->kind != pa11::TypeKind::LValueReference &&
		    overload_pattern->kind != pa11::TypeKind::RValueReference)
		{
			overload_pattern = pa11::strip_top_level_cv(overload_pattern);
			overload_argument = pa11::make_pointer(overload_argument);
		}
		map<string, TypePtr> one_deduced = deduced;
		map<string, TemplateArgument> one_arguments = fixed_arguments;
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
	return true;
}

bool Parser::deduce_function_template_overload_argument(
	TypePtr pattern,
	const Expr& actual,
	map<string, TypePtr>& deduced,
	map<string, TypePtr>& fixed,
	map<string, TemplateArgument>& fixed_arguments) const
{
	vector<TypePtr> overload_types;
	for (size_t j = 0; j < actual.overloads.size(); ++j)
	{
		Binding* overload = actual.overloads[j];
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
		return deduce_single_overload_template_argument(pattern,
		                                                actual,
		                                                overload_types,
		                                                deduced,
		                                                fixed,
		                                                fixed_arguments);
	return deduce_overload_set_template_argument(pattern,
	                                             actual,
	                                             deduced,
	                                             fixed,
	                                             fixed_arguments);
}

bool Parser::deduce_initializer_list_template_argument(
	TypePtr pattern,
	const Expr& actual,
	map<string, TypePtr>& deduced,
	const map<string, TypePtr>& fixed,
	map<string, TemplateArgument>& fixed_arguments) const
{
	TypePtr initializer_element_pattern;
	if (!actual.braced_init_list ||
	    actual.type.get() != NULL ||
	    !is_std_initializer_list_type(pattern, &initializer_element_pattern))
		return false;
	for (size_t ci = 0; ci < actual.node.children.size(); ++ci)
	{
		const Node& child = actual.node.children[ci];
		if (!deduce_template_type(initializer_element_pattern,
		                          lvalue_to_rvalue_type(child.type),
		                          deduced,
		                          &fixed,
		                          &fixed_arguments))
			return false;
	}
	return true;
}

bool Parser::deduce_regular_template_call_argument(
	TypePtr pattern,
	const Expr& actual,
	map<string, TypePtr>& deduced,
	map<string, TypePtr>& fixed,
	map<string, TemplateArgument>& fixed_arguments) const
{
	TypePtr argument = expression_object_type(actual.type);
	TypePtr bare_pattern = pa11::strip_cv(pattern);
	if (bare_pattern->kind == pa11::TypeKind::RValueReference &&
	    pa11::strip_cv(bare_pattern->base)->kind ==
		    pa11::TypeKind::TemplateParameter &&
	    pa11::is_deducible_template_parameter_type(
		    pa11::strip_cv(bare_pattern->base)) &&
	    actual.category == ValueCategory::LValue)
	{
		TypePtr ref = pa11::make_lvalue_reference(argument);
		return deduce_template_type(bare_pattern->base,
		                            ref,
		                            deduced,
		                            &fixed,
		                            &fixed_arguments) &&
		       deduce_array_bound_arguments(bare_pattern->base,
		                                    ref,
		                                    fixed_arguments);
	}
	if (pattern->kind != pa11::TypeKind::LValueReference &&
	    pattern->kind != pa11::TypeKind::RValueReference)
	{
		pattern = pa11::strip_top_level_cv(pattern);
		argument = lvalue_to_rvalue_type(actual.type);
	}
	return deduce_template_type(pattern,
	                            argument,
	                            deduced,
	                            &fixed,
	                            &fixed_arguments) &&
	       deduce_array_bound_arguments(pattern, argument, fixed_arguments);
}

bool Parser::deduce_function_template_call_parameters(
	TemplateDeclaration* declaration,
	TypePtr fn,
	const vector<Expr>& args,
	map<string, TypePtr>& deduced,
	map<string, TypePtr>& fixed,
	map<string, vector<TemplateArgument> >& deduced_packs,
	map<string, TemplateArgument>& fixed_arguments,
	size_t& arg_index) const
{
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
				call_parameter_pack_name(declaration, pattern, pack_name);
			size_t remaining = fn->parameters.size() - i - 1;
		if (parameter_pack)
		{
			if (!deduce_function_template_parameter_pack(declaration,
			                                            pattern,
			                                            pack_name,
			                                            remaining,
			                                            args,
			                                            deduced,
			                                            fixed,
			                                            deduced_packs,
			                                            fixed_arguments,
			                                            arg_index))
				return false;
			continue;
		}
		if (arg_index >= args.size())
			break;
		bool pattern_mentions_parameter =
			pattern_mentions_function_template_parameter(
			    declaration,
			    pattern,
			    record_template_arguments_);
		if (!pattern_mentions_parameter)
		{
			++arg_index;
			continue;
		}
		const Expr& actual = args[arg_index];
		if (!actual.overloads.empty())
		{
			if (!deduce_function_template_overload_argument(pattern,
			                                               actual,
			                                               deduced,
			                                               fixed,
			                                               fixed_arguments))
				return false;
			++arg_index;
			continue;
		}
		if (actual.braced_init_list && actual.type.get() == NULL)
		{
			if (!deduce_initializer_list_template_argument(pattern,
			                                              actual,
			                                              deduced,
			                                              fixed,
			                                              fixed_arguments))
				return false;
			++arg_index;
			continue;
		}
		if (!deduce_regular_template_call_argument(pattern,
		                                           actual,
		                                           deduced,
		                                           fixed,
		                                           fixed_arguments))
			return false;
		++arg_index;
	}
	return true;
}

bool Parser::append_deduced_function_template_argument(
	TemplateDeclaration* declaration,
	const TemplateParameterInfo& parameter,
	size_t parameter_index,
	map<string, TypePtr>& deduced,
	map<string, vector<TemplateArgument> >& deduced_packs,
	map<string, TemplateArgument>& fixed_arguments,
	bool& saw_template_parameter_pack,
	vector<TemplateArgument>& explicit_args)
{
	const string& pname = parameter.name;
	if (parameter.is_pack)
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
				parameter.kind == TemplateParameterKind::Type
				? deduced.find(pname) : deduced.end();
			if (found == deduced_packs.end() && scalar != deduced.end())
			{
				vector<TemplateArgument> pack;
				pack.push_back(TemplateArgument::type_arg(scalar->second));
				explicit_args.push_back(TemplateArgument::pack_arg(pack));
			}
			else if (found == deduced_packs.end())
				explicit_args.push_back(TemplateArgument::pack_arg(
					vector<TemplateArgument>()));
			else
				explicit_args.push_back(
					TemplateArgument::pack_arg(found->second));
		}
		saw_template_parameter_pack = true;
		return true;
	}
	if (parameter.kind == TemplateParameterKind::Type)
	{
		map<string, TypePtr>::iterator found = deduced.find(pname);
		if (found != deduced.end())
			explicit_args.push_back(
				TemplateArgument::type_arg(found->second));
		else if (parameter.has_default)
		{
			if (saw_template_parameter_pack)
				return false;
			if (hosted_compatibility_ &&
			    validating_template_definition_ &&
			    hosted_library_template_declaration(declaration))
			{
				explicit_args.push_back(
					dependent_default_template_argument(
						declaration,
						parameter,
						parameter_index));
				return true;
			}
			try
			{
				explicit_args.push_back(
					parse_default_template_argument(declaration,
					                                parameter_index,
					                                explicit_args));
			}
			catch (const runtime_error& err)
			{
				if (function_template_candidate_instantiation_depth_ == 0 ||
				    string(err.what()) != "dependent typename not resolved")
					throw;
				bool dependent_context = false;
				for (size_t ai = 0; ai < explicit_args.size(); ++ai)
					if (template_argument_has_template_parameter(
						    explicit_args[ai],
						    record_template_arguments_))
						dependent_context = true;
				if (!dependent_context)
					return false;
				string default_name = parameter.name.empty()
					? declaration->name + "__default" +
					  to_string(parameter_index)
					: parameter.name;
				explicit_args.push_back(TemplateArgument::type_arg(
					pa11::make_dependent_typename_type(default_name,
					                                   false,
					                                   false,
					                                   false)));
			}
		}
		else
			return false;
		return true;
	}
	map<string, TemplateArgument>::iterator found =
		fixed_arguments.find(pname);
	if (found != fixed_arguments.end())
		explicit_args.push_back(found->second);
	else if (parameter.has_default)
	{
		if (saw_template_parameter_pack)
			return false;
		if (hosted_compatibility_ &&
		    validating_template_definition_ &&
		    hosted_library_template_declaration(declaration))
		{
			explicit_args.push_back(
				dependent_default_template_argument(
					declaration,
					parameter,
					parameter_index));
			return true;
		}
		explicit_args.push_back(
			parse_default_template_argument(declaration,
			                                parameter_index,
			                                explicit_args));
	}
	else
		return false;
	return true;
}

bool Parser::finish_deduced_function_template_arguments(
	TemplateDeclaration* declaration,
	map<string, TypePtr>& deduced,
	map<string, vector<TemplateArgument> >& deduced_packs,
	map<string, TemplateArgument>& fixed_arguments,
	vector<TemplateArgument>& out)
{
	vector<TemplateArgument> explicit_args;
	bool saw_template_parameter_pack = false;
	for (size_t i = 0; i < declaration->parameters.size(); ++i)
	{
		const TemplateParameterInfo& parameter = declaration->parameters[i];
		if (!append_deduced_function_template_argument(
			    declaration,
			    parameter,
			    i,
			    deduced,
			    deduced_packs,
			    fixed_arguments,
			    saw_template_parameter_pack,
			    explicit_args))
			break;
	}
	try
	{
		out = complete_template_arguments(declaration, explicit_args);
	}
	catch (const runtime_error&)
	{
		return false;
	}
	bool size_matches = out.size() == declaration->parameters.size();
	return size_matches;
}

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
	bool complete = false;
	if (!deduce_explicit_function_template_arguments(declaration,
	                                                explicit_arguments,
	                                                deduced,
	                                                fixed,
	                                                deduced_packs,
	                                                fixed_arguments,
	                                                out,
	                                                complete))
	{
		return false;
	}
	if (complete)
		return true;
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
			placeholder_type->parameters.size() == fn->parameters.size() + 1;
		if (generic_omits_object_parameter && !args.empty())
			arg_index = 1;
	}
	vector<set<string> > save_pack_subst = template_type_parameter_packs_;
	set<string> deduction_pack_subst;
	for (size_t i = 0; i < declaration->parameters.size(); ++i)
		if (declaration->parameters[i].kind == TemplateParameterKind::Type &&
		    declaration->parameters[i].is_pack &&
		    !declaration->parameters[i].name.empty())
			deduction_pack_subst.insert(declaration->parameters[i].name);
	template_type_parameter_packs_.push_back(deduction_pack_subst);
	bool call_parameters_deduced =
		deduce_function_template_call_parameters(declaration,
		                                         fn,
		                                         args,
		                                         deduced,
		                                         fixed,
		                                         deduced_packs,
		                                         fixed_arguments,
		                                         arg_index);
	template_type_parameter_packs_ = save_pack_subst;
	if (!call_parameters_deduced)
	{
		return false;
	}
	if (arg_index != args.size() && !fn->variadic)
	{
		return false;
	}
	bool finished =
		finish_deduced_function_template_arguments(declaration,
		                                           deduced,
		                                           deduced_packs,
	                                           fixed_arguments,
	                                           out);
	return finished;
}

}  // namespace internal
}  // namespace pa12
