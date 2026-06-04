#include "pa12_internal.h"

#include <algorithm>
#include <stdexcept>

using namespace std;

namespace pa12 {
namespace internal {

Binding* Parser::instantiate_function_template(
	TemplateDeclaration* declaration,
	const vector<TypePtr>& arguments)
{
	vector<TypePtr> full_args =
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
	bool save_force_new_function_binding = force_new_function_binding_;
	map<string, TypePtr> subst;
	for (size_t i = 0; i < full_args.size() &&
	     i < declaration->parameters.size(); ++i)
		if (!declaration->parameters[i].name.empty())
			subst[declaration->parameters[i].name] = full_args[i];
	template_type_substitutions_.push_back(subst);
	bool dependent = false;
	for (size_t i = 0; i < full_args.size(); ++i)
		if (type_is_template_dependent(full_args[i]))
			dependent = true;
	if (dependent)
	{
		TypePtr type =
			substitute_template_type(declaration->generic_function_type);
		Binding* binding =
			add_function_binding(declaration->owner,
			                     declaration->name,
			                     type,
			                     false);
		declaration->function_specializations[key] = binding;
		function_template_placeholders_[binding] = declaration;
		declaration->completing_specializations.erase(key);
		template_type_substitutions_ = save_subst;
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
		scopes_ = save_scopes;
		pos_ = save_pos;
		force_new_function_binding_ = save_force_new_function_binding;
		throw;
	}
	template_type_substitutions_ = save_subst;
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
		declaration->function_specializations[key] = fn.binding;
		function_template_placeholders_[fn.binding] = declaration;
		declaration->completing_specializations.erase(key);
		return fn.binding;
	}
	fn.binding->is_inline_definition = true;
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
			map<const void*, vector<TypePtr> >::const_iterator pit =
				record_template_arguments_.find(pattern.get());
			if (pit != record_template_arguments_.end())
				for (size_t i = 0; i < pit->second.size(); ++i)
					if (type_is_template_dependent(pit->second[i]))
						pattern_dependent = true;
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
		map<const void*, TemplateDeclaration*>::const_iterator pt =
			record_template_declarations_.find(pattern.get());
		map<const void*, TemplateDeclaration*>::const_iterator at =
			record_template_declarations_.find(argument.get());
		if (pt != record_template_declarations_.end() &&
		    at != record_template_declarations_.end() &&
		    pt->second == at->second)
		{
			const vector<TypePtr>& p_args =
				record_template_arguments_.find(pattern.get())->second;
			const vector<TypePtr>& a_args =
				record_template_arguments_.find(argument.get())->second;
			if (p_args.size() != a_args.size())
				return false;
			for (size_t i = 0; i < p_args.size(); ++i)
				if (!deduce_template_type(p_args[i],
				                          a_args[i],
				                          deduced,
				                          fixed))
					return false;
			return true;
		}
	}
	return pa11::same_type(pattern, argument);
}

bool Parser::deduce_function_template_arguments(
	TemplateDeclaration* declaration,
	const vector<Expr>& args,
	const vector<TypePtr>& explicit_arguments,
	vector<TypePtr>& out)
{
	if (declaration->generic_function_type.get() == NULL ||
	    declaration->generic_function_type->kind != pa11::TypeKind::Function)
		return false;
	if (explicit_arguments.size() > declaration->parameters.size())
		return false;
	TypePtr fn = declaration->generic_function_type;
	if (args.size() > fn->parameters.size() && !fn->variadic)
		return false;
	map<string, TypePtr> deduced;
	map<string, TypePtr> fixed;
	for (size_t i = 0; i < explicit_arguments.size(); ++i)
	{
		const string& pname = declaration->parameters[i].name;
		if (pname.empty())
			return false;
		deduced[pname] = explicit_arguments[i];
		fixed[pname] = explicit_arguments[i];
	}
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
	size_t count = min(args.size(), fn->parameters.size());
	for (size_t i = 0; i < count; ++i)
	{
		TypePtr pattern = fn->parameters[i];
		TypePtr argument = expression_object_type(args[i].type);
		TypePtr bare_pattern = pa11::strip_cv(pattern);
		if (bare_pattern->kind == pa11::TypeKind::RValueReference &&
		    pa11::strip_cv(bare_pattern->base)->kind ==
			    pa11::TypeKind::TemplateParameter &&
		    args[i].category == ValueCategory::LValue)
		{
			if (!deduce_template_type(bare_pattern->base,
			                          pa11::make_lvalue_reference(argument),
			                          deduced,
			                          &fixed))
				return false;
			continue;
		}
			if (pattern->kind != pa11::TypeKind::LValueReference &&
			    pattern->kind != pa11::TypeKind::RValueReference)
			{
				pattern = pa11::strip_top_level_cv(pattern);
				argument = lvalue_to_rvalue_type(args[i].type);
			}
		if (!deduce_template_type(pattern, argument, deduced, &fixed))
			return false;
	}
		vector<TypePtr> explicit_args;
		for (size_t i = 0; i < declaration->parameters.size(); ++i)
		{
			const string& pname = declaration->parameters[i].name;
			map<string, TypePtr>::iterator found = deduced.find(pname);
			if (found == deduced.end())
				break;
			explicit_args.push_back(found->second);
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
	const vector<TypePtr>& explicit_arguments,
	vector<TypePtr>& out)
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
		deduced[pname] = explicit_arguments[i];
		fixed[pname] = explicit_arguments[i];
	}
	if (!deduce_template_type(declaration->generic_function_type,
	                          target,
	                          deduced,
	                          &fixed))
		return false;
	vector<TypePtr> full_args;
	for (size_t i = 0; i < declaration->parameters.size(); ++i)
	{
		const string& pname = declaration->parameters[i].name;
		map<string, TypePtr>::iterator found = deduced.find(pname);
		if (found == deduced.end())
			break;
		full_args.push_back(found->second);
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
