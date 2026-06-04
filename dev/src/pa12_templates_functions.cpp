#include "pa12_internal.h"

#include <algorithm>
#include <stdexcept>

using namespace std;

namespace pa12 {
namespace internal {
namespace {

bool type_contains_template_parameter_name(TypePtr type, string& name)
{
	if (type.get() == NULL)
		return false;
	type = pa11::strip_cv(type);
	if (type->kind == pa11::TypeKind::TemplateParameter)
	{
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
	return false;
}

bool declaration_parameter_is_pack(TemplateDeclaration* declaration,
                                   const string& name)
{
	for (size_t i = 0; i < declaration->parameters.size(); ++i)
		if (declaration->parameters[i].name == name &&
		    declaration->parameters[i].is_pack)
			return true;
	return false;
}

bool function_parameter_pack_name(TemplateDeclaration* declaration,
                                  TypePtr pattern,
                                  string& name)
{
	if (!type_contains_template_parameter_name(pattern, name))
		return false;
	return declaration_parameter_is_pack(declaration, name);
}

}  // namespace

Binding* Parser::instantiate_function_template(
	TemplateDeclaration* declaration,
	const vector<TemplateArgument>& arguments)
{
	vector<TemplateArgument> full_args =
		complete_template_arguments(declaration, arguments);
	string key = template_argument_key(full_args);
	map<string, Binding*>::iterator existing =
		declaration->function_specializations.find(key);
	if (existing != declaration->function_specializations.end())
		return existing->second;
	if (declaration->completing_specializations.count(key) != 0)
		throw runtime_error("recursive function template instantiation");
	declaration->completing_specializations.insert(key);

	size_t save_pos = pos_;
	vector<Scope*> save_scopes = scopes_;
	vector<map<string, TypePtr> > save_subst = template_type_substitutions_;
	vector<map<string, TemplateArgument> > save_value_subst =
		template_value_substitutions_;
	bool save_force_new_function_binding = force_new_function_binding_;
	map<string, TypePtr> subst;
	map<string, TemplateArgument> value_subst;
	for (size_t i = 0; i < full_args.size() &&
	     i < declaration->parameters.size(); ++i)
		if (!declaration->parameters[i].name.empty())
		{
			if (declaration->parameters[i].kind ==
			    TemplateParameterKind::Type)
			{
				if (declaration->parameters[i].is_pack)
				{
					subst[declaration->parameters[i].name] =
						pa11::make_template_parameter_type(
							declaration->parameters[i].name);
					value_subst[declaration->parameters[i].name] =
						full_args[i];
				}
				else
					subst[declaration->parameters[i].name] =
						full_args[i].type;
			}
			else
				value_subst[declaration->parameters[i].name] =
					full_args[i];
		}
	template_type_substitutions_.push_back(subst);
	template_value_substitutions_.push_back(value_subst);
	bool dependent = false;
	for (size_t i = 0; i < full_args.size(); ++i)
	{
		vector<TemplateArgument> pending;
		pending.push_back(full_args[i]);
		while (!pending.empty())
		{
			TemplateArgument arg = pending.back();
			pending.pop_back();
			if (arg.kind == TemplateArgumentKind::Type)
			{
				if (type_is_template_dependent(arg.type))
					dependent = true;
			}
				else if (arg.kind == TemplateArgumentKind::Value)
				{
					if (arg.dependent || type_is_template_dependent(arg.type))
						dependent = true;
				}
				else if (arg.kind == TemplateArgumentKind::Template)
				{
					if (arg.template_declaration == NULL)
						dependent = true;
				}
				else
				{
					for (size_t p = 0; p < arg.pack.size(); ++p)
					pending.push_back(arg.pack[p]);
			}
		}
	}
	if (dependent)
	{
		TypePtr type =
			substitute_template_type(declaration->generic_function_type);
			Binding* binding =
				add_function_binding(declaration->owner,
				                     declaration->name,
				                     type,
				                     false);
			if (declaration->placeholder != NULL)
				binding->unwind_no = declaration->placeholder->unwind_no;
			declaration->function_specializations[key] = binding;
		function_template_placeholders_[binding] = declaration;
		declaration->completing_specializations.erase(key);
		template_type_substitutions_ = save_subst;
		template_value_substitutions_ = save_value_subst;
		scopes_ = save_scopes;
		pos_ = save_pos;
		force_new_function_binding_ = save_force_new_function_binding;
		return binding;
	}
	scopes_.clear();
	scopes_.push_back(declaration->lexical_scope != NULL
	                  ? declaration->lexical_scope
	                  : declaration->owner);
	pos_ = declaration->decl_begin;
	force_new_function_binding_ = true;
	Node node;
	try
	{
		if (declaration->constructor_template)
		{
			if (!parse_qualified_constructor_definition(node, true))
				throw runtime_error(
					"constructor template instantiation failed");
		}
		else
			parse_simple_or_function_declaration(node, true);
	}
	catch (const exception&)
	{
		declaration->completing_specializations.erase(key);
		template_type_substitutions_ = save_subst;
		template_value_substitutions_ = save_value_subst;
		scopes_ = save_scopes;
		pos_ = save_pos;
		force_new_function_binding_ = save_force_new_function_binding;
		throw;
	}
	template_type_substitutions_ = save_subst;
	template_value_substitutions_ = save_value_subst;
	scopes_ = save_scopes;
	pos_ = save_pos;
	force_new_function_binding_ = save_force_new_function_binding;
	Node fn;
	if (!node.children.empty())
		fn = node.children.back();
	else if (node.line.compare(0, 19, "function-definition") == 0 &&
	         node.binding != NULL)
		fn = node;
	if (fn.binding == NULL)
	{
		declaration->completing_specializations.erase(key);
		throw runtime_error("function template instantiation failed");
	}
		if (fn.line.compare(0, 19, "function-definition") != 0)
		{
			if (declaration->placeholder != NULL)
				fn.binding->unwind_no = declaration->placeholder->unwind_no;
			declaration->function_specializations[key] = fn.binding;
		function_template_placeholders_[fn.binding] = declaration;
		declaration->completing_specializations.erase(key);
		return fn.binding;
	}
		fn.binding->is_inline_definition = true;
		if (declaration->placeholder != NULL)
			fn.binding->unwind_no = declaration->placeholder->unwind_no;
	extra_lowir_nodes_.push_back(fn);
	declaration->function_specializations[key] = fn.binding;
	function_template_placeholders_[fn.binding] = declaration;
	declaration->completing_specializations.erase(key);
	return fn.binding;
}

bool Parser::deduce_template_type(TypePtr pattern,
                                  TypePtr argument,
                                  map<string, TypePtr>& deduced,
                                  const map<string, TypePtr>* fixed) const
{
	if (pattern->kind == pa11::TypeKind::Cv &&
	    type_is_template_dependent(pattern->base))
	{
		unsigned argument_cv = argument->kind == pa11::TypeKind::Cv
			? argument->cv : pa11::CV_NONE;
		TypePtr argument_base = argument->kind == pa11::TypeKind::Cv
			? argument->base : argument;
		TypePtr remaining_argument =
			pa11::make_cv(argument_base, argument_cv & ~pattern->cv);
		return deduce_template_type(pattern->base,
		                            remaining_argument,
		                            deduced,
		                            fixed);
	}
	if (pattern->kind == pa11::TypeKind::LValueReference ||
	    pattern->kind == pa11::TypeKind::RValueReference)
	{
		if (argument->kind == pa11::TypeKind::LValueReference ||
		    argument->kind == pa11::TypeKind::RValueReference)
			argument = argument->base;
		return deduce_template_type(pattern->base, argument, deduced, fixed);
	}
	if (pattern->kind == pa11::TypeKind::TemplateParameter)
	{
		if (fixed != NULL && fixed->find(pattern->name) != fixed->end())
			return true;
		map<string, TypePtr>::iterator found = deduced.find(pattern->name);
		if (found == deduced.end())
		{
			deduced[pattern->name] = argument;
			return true;
		}
		return pa11::same_type(found->second, argument);
	}
	pattern = pa11::strip_cv(pattern);
	argument = pa11::strip_cv(argument);
	bool pattern_dependent =
		type_is_template_dependent(pattern);
	if (!pattern_dependent && pattern->kind == pa11::TypeKind::Record)
	{
			map<const void*, vector<TemplateArgument> >::const_iterator pit =
				record_template_arguments_.find(pattern.get());
			if (pit != record_template_arguments_.end())
				for (size_t i = 0; i < pit->second.size(); ++i)
				{
					vector<TemplateArgument> pending;
					pending.push_back(pit->second[i]);
					while (!pending.empty())
					{
						TemplateArgument arg = pending.back();
						pending.pop_back();
						if (arg.kind == TemplateArgumentKind::Type)
						{
							if (type_is_template_dependent(arg.type))
								pattern_dependent = true;
						}
							else if (arg.kind == TemplateArgumentKind::Value)
							{
								if (arg.dependent ||
								    type_is_template_dependent(arg.type))
									pattern_dependent = true;
							}
							else if (arg.kind == TemplateArgumentKind::Template)
							{
								if (arg.template_declaration == NULL)
									pattern_dependent = true;
							}
							else
							{
								for (size_t p = 0; p < arg.pack.size(); ++p)
								pending.push_back(arg.pack[p]);
						}
					}
				}
		}
	if (!pattern_dependent)
		return true;
	if (pattern->kind != argument->kind)
		return false;
	if (pattern->kind == pa11::TypeKind::Pointer ||
	    pattern->kind == pa11::TypeKind::Array)
		return deduce_template_type(pattern->base,
		                            argument->base,
		                            deduced,
		                            fixed);
	if (pattern->kind == pa11::TypeKind::Function)
	{
		if (pattern->parameters.size() != argument->parameters.size())
			return false;
		if (!deduce_template_type(pattern->base,
		                          argument->base,
		                          deduced,
		                          fixed))
			return false;
		for (size_t i = 0; i < pattern->parameters.size(); ++i)
			if (!deduce_template_type(pattern->parameters[i],
			                          argument->parameters[i],
			                          deduced,
			                          fixed))
				return false;
		return true;
	}
	if (pattern->kind == pa11::TypeKind::Record)
	{
		if (argument->kind == pa11::TypeKind::Record)
		{
			const_cast<Parser*>(this)->complete_template_record(argument);
			TypePtr base = argument->base.get() != NULL
				? pa11::strip_cv(argument->base) : TypePtr();
			if (base.get() != NULL &&
			    deduce_template_type(pattern, base, deduced, fixed))
				return true;
		}
		map<const void*, TemplateDeclaration*>::const_iterator pt =
			record_template_declarations_.find(pattern.get());
		map<const void*, TemplateDeclaration*>::const_iterator at =
			record_template_declarations_.find(argument.get());
		if (pt != record_template_declarations_.end() &&
		    at != record_template_declarations_.end() &&
		    pt->second == at->second)
		{
			const vector<TemplateArgument>& p_args =
				record_template_arguments_.find(pattern.get())->second;
			const vector<TemplateArgument>& a_args =
				record_template_arguments_.find(argument.get())->second;
			if (p_args.size() != a_args.size())
				return false;
			for (size_t i = 0; i < p_args.size(); ++i)
			{
				if (p_args[i].kind == TemplateArgumentKind::Type &&
				    a_args[i].kind == TemplateArgumentKind::Type)
				{
					if (!deduce_template_type(p_args[i].type,
					                          a_args[i].type,
					                          deduced,
					                          fixed))
						return false;
				}
				else if (p_args[i].kind == TemplateArgumentKind::Value &&
				         a_args[i].kind == TemplateArgumentKind::Value)
				{
					if (p_args[i].dependent || a_args[i].dependent)
						continue;
					if (p_args[i].value != a_args[i].value)
						return false;
				}
				else
					return false;
			}
			return true;
		}
	}
	return pa11::same_type(pattern, argument);
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
	size_t explicit_index = 0;
	for (size_t i = 0;
	     i < declaration->parameters.size() &&
	     explicit_index < explicit_arguments.size();
	     ++i)
	{
		const string& pname = declaration->parameters[i].name;
		if (pname.empty())
			return false;
		if (declaration->parameters[i].is_pack)
		{
			if (explicit_index < explicit_arguments.size() &&
			    explicit_arguments[explicit_index].kind ==
				    TemplateArgumentKind::Pack)
			{
				TemplateArgument pack_arg =
					explicit_arguments[explicit_index++];
				for (size_t p = 0; p < pack_arg.pack.size(); ++p)
					{
						if (declaration->parameters[i].kind ==
							    TemplateParameterKind::Type &&
						    pack_arg.pack[p].kind != TemplateArgumentKind::Type)
							return false;
						if (declaration->parameters[i].kind ==
							    TemplateParameterKind::NonType &&
						    pack_arg.pack[p].kind != TemplateArgumentKind::Value)
							return false;
						if (declaration->parameters[i].kind ==
							    TemplateParameterKind::TemplateTemplate &&
						    pack_arg.pack[p].kind != TemplateArgumentKind::Template)
							return false;
					}
				fixed_arguments[pname] = pack_arg;
				if (declaration->parameters[i].kind ==
				    TemplateParameterKind::Type)
					deduced_packs[pname] = pack_arg.pack;
				continue;
			}
			size_t required_after = 0;
			for (size_t j = i + 1; j < declaration->parameters.size(); ++j)
				if (!declaration->parameters[j].is_pack &&
				    !declaration->parameters[j].has_default)
					++required_after;
			if (explicit_index + required_after > explicit_arguments.size())
				return false;
			size_t take =
				explicit_arguments.size() - explicit_index - required_after;
			vector<TemplateArgument> pack;
			for (size_t j = 0; j < take; ++j)
			{
				vector<TemplateArgument> expansion =
					expand_template_argument_pack(
						explicit_arguments[explicit_index++]);
				for (size_t p = 0; p < expansion.size(); ++p)
					{
						if (declaration->parameters[i].kind ==
							    TemplateParameterKind::Type &&
						    expansion[p].kind != TemplateArgumentKind::Type)
							return false;
						if (declaration->parameters[i].kind ==
							    TemplateParameterKind::NonType &&
						    expansion[p].kind != TemplateArgumentKind::Value)
							return false;
						if (declaration->parameters[i].kind ==
							    TemplateParameterKind::TemplateTemplate &&
						    expansion[p].kind != TemplateArgumentKind::Template)
							return false;
						pack.push_back(expansion[p]);
					}
			}
			TemplateArgument pack_arg = TemplateArgument::pack_arg(pack);
			fixed_arguments[pname] = pack_arg;
			if (declaration->parameters[i].kind ==
			    TemplateParameterKind::Type)
				deduced_packs[pname] = pack;
			continue;
		}
		TemplateArgument explicit_arg =
			explicit_arguments[explicit_index++];
		if (declaration->parameters[i].kind ==
		    TemplateParameterKind::Type)
		{
			if (explicit_arg.kind != TemplateArgumentKind::Type)
				return false;
			deduced[pname] = explicit_arg.type;
			fixed[pname] = explicit_arg.type;
			fixed_arguments[pname] = explicit_arg;
		}
			else
			{
				if (declaration->parameters[i].kind ==
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
	for (size_t i = 0; i < fn->parameters.size(); ++i)
	{
		TypePtr pattern = fn->parameters[i];
		string pack_name;
		bool parameter_pack =
			function_parameter_pack_name(declaration, pattern, pack_name);
		size_t remaining_function_parameters =
			fn->parameters.size() - i - 1;
		if (parameter_pack)
		{
			if (arg_index + remaining_function_parameters > args.size())
				return false;
			size_t take =
				args.size() - arg_index - remaining_function_parameters;
			vector<TemplateArgument> pack;
			for (size_t j = 0; j < take; ++j)
			{
				const Expr& actual_expr = args[arg_index + j];
				TypePtr argument =
					expression_object_type(actual_expr.type);
				TypePtr element_pattern = pattern;
				TypePtr bare_pattern = pa11::strip_cv(element_pattern);
				map<string, TypePtr> one;
				if (bare_pattern->kind ==
				    pa11::TypeKind::RValueReference &&
				    pa11::strip_cv(bare_pattern->base)->kind ==
					    pa11::TypeKind::TemplateParameter &&
				    actual_expr.category == ValueCategory::LValue)
				{
					if (!deduce_template_type(
						    bare_pattern->base,
						    pa11::make_lvalue_reference(argument),
						    one,
						    &fixed))
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
					                          &fixed))
						return false;
				}
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
		TypePtr argument = expression_object_type(args[arg_index].type);
		TypePtr bare_pattern = pa11::strip_cv(pattern);
		if (bare_pattern->kind == pa11::TypeKind::RValueReference &&
		    pa11::strip_cv(bare_pattern->base)->kind ==
			    pa11::TypeKind::TemplateParameter &&
		    args[arg_index].category == ValueCategory::LValue)
		{
			if (!deduce_template_type(bare_pattern->base,
			                          pa11::make_lvalue_reference(argument),
			                          deduced,
			                          &fixed))
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
		if (!deduce_template_type(pattern, argument, deduced, &fixed))
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
				if (found == deduced_packs.end())
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

bool Parser::deduce_function_template_target_type(
	TemplateDeclaration* declaration,
	TypePtr target,
	const vector<TemplateArgument>& explicit_arguments,
	vector<TemplateArgument>& out)
{
	if (declaration->generic_function_type.get() == NULL ||
	    declaration->generic_function_type->kind != pa11::TypeKind::Function)
		return false;
	if (target.get() == NULL ||
	    pa11::strip_cv(target)->kind != pa11::TypeKind::Function ||
	    explicit_arguments.size() > declaration->parameters.size())
		return false;
	map<string, TypePtr> deduced;
	map<string, TypePtr> fixed;
	for (size_t i = 0; i < explicit_arguments.size(); ++i)
	{
		const string& pname = declaration->parameters[i].name;
		if (pname.empty())
			return false;
		if (declaration->parameters[i].kind ==
		    TemplateParameterKind::Type)
		{
			if (explicit_arguments[i].kind != TemplateArgumentKind::Type)
				return false;
			deduced[pname] = explicit_arguments[i].type;
			fixed[pname] = explicit_arguments[i].type;
		}
	}
	if (!deduce_template_type(declaration->generic_function_type,
	                          target,
	                          deduced,
	                          &fixed))
		return false;
	vector<TemplateArgument> full_args;
	for (size_t i = 0; i < declaration->parameters.size(); ++i)
	{
		if (declaration->parameters[i].kind !=
		    TemplateParameterKind::Type)
			break;
		const string& pname = declaration->parameters[i].name;
		map<string, TypePtr>::iterator found = deduced.find(pname);
		if (found == deduced.end())
			break;
		full_args.push_back(TemplateArgument::type_arg(found->second));
	}
	try
	{
		out = complete_template_arguments(declaration, full_args);
	}
	catch (const runtime_error&)
	{
		return false;
	}
	return out.size() == declaration->parameters.size();
}


}  // namespace internal
}  // namespace pa12
