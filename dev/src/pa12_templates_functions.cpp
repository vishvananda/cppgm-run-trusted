#include "pa12_internal.h"

#include <algorithm>
#include <stdexcept>

using namespace std;

namespace pa12 {
namespace internal {
namespace {

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
	if (!template_type_has_template_parameter_name(pattern, name))
		return false;
	return declaration_parameter_is_pack(declaration, name);
}

string abi_source_name(const string& name)
{
	string unqualified = name;
	size_t pos = unqualified.rfind("::");
	if (pos != string::npos)
		unqualified = unqualified.substr(pos + 2);
	return to_string(unqualified.size()) + unqualified;
}

string abi_fundamental_type(EFundamentalType type)
{
	switch (type)
	{
	case FT_VOID: return "v";
	case FT_BOOL: return "b";
	case FT_CHAR: return "c";
	case FT_SIGNED_CHAR: return "a";
	case FT_UNSIGNED_CHAR: return "h";
	case FT_SHORT_INT: return "s";
	case FT_UNSIGNED_SHORT_INT: return "t";
	case FT_INT: return "i";
	case FT_UNSIGNED_INT: return "j";
	case FT_LONG_INT: return "l";
	case FT_UNSIGNED_LONG_INT: return "m";
	case FT_LONG_LONG_INT: return "x";
	case FT_UNSIGNED_LONG_LONG_INT: return "y";
	case FT_FLOAT: return "f";
	case FT_DOUBLE: return "d";
	default: return "i";
	}
}

string abi_type(TypePtr type, const map<string, size_t>& template_parameters);

string abi_template_instance_argument(
	const pa11::TemplateInstanceArgument& arg,
	const map<string, size_t>& template_parameters)
{
	if (arg.kind == pa11::TemplateInstanceArgumentKind::Type)
		return abi_type(arg.type, template_parameters);
	if (arg.kind == pa11::TemplateInstanceArgumentKind::Value)
		return "L" + abi_type(arg.type, template_parameters) +
		       to_string(arg.value) + "E";
	if (arg.kind == pa11::TemplateInstanceArgumentKind::Pack)
	{
		string out = "J";
		for (size_t i = 0; i < arg.pack.size(); ++i)
			out += abi_template_instance_argument(arg.pack[i],
			                                     template_parameters);
		out += "E";
		return out;
	}
	return abi_source_name(arg.template_name);
}

string abi_template_argument(const TemplateArgument& arg,
                             const map<string, size_t>& template_parameters)
{
	if (arg.kind == TemplateArgumentKind::Type)
		return abi_type(arg.type, template_parameters);
	if (arg.kind == TemplateArgumentKind::Value)
		return "L" + abi_type(arg.type, template_parameters) +
		       to_string(arg.value) + "E";
	if (arg.kind == TemplateArgumentKind::Pack)
	{
		string out = "J";
		for (size_t i = 0; i < arg.pack.size(); ++i)
			out += abi_template_argument(arg.pack[i], template_parameters);
		out += "E";
		return out;
	}
	return arg.template_declaration != NULL
		? abi_source_name(arg.template_declaration->name) : string("v");
}

string abi_record_type(TypePtr type,
                       const map<string, size_t>& template_parameters)
{
	TypePtr bare = pa11::strip_cv(type);
	string name = bare->is_template_specialization &&
	              !bare->template_primary_name.empty()
		? bare->template_primary_name : bare->name;
	size_t args = name.find('<');
	if (args != string::npos)
		name = name.substr(0, args);
	string out = abi_source_name(name);
	if (bare->is_template_specialization)
	{
		out += "I";
		for (size_t i = 0; i < bare->template_arguments.size(); ++i)
			out += abi_template_instance_argument(
				bare->template_arguments[i],
				template_parameters);
		out += "E";
	}
	return out;
}

string abi_type(TypePtr type, const map<string, size_t>& template_parameters)
{
	if (type.get() == NULL)
		return "v";
	if (type->kind == pa11::TypeKind::Cv)
	{
		string quals;
		if ((type->cv & pa11::CV_CONST) != 0)
			quals += "K";
		if ((type->cv & pa11::CV_VOLATILE) != 0)
			quals += "V";
		return quals + abi_type(type->base, template_parameters);
	}
	if (type->kind == pa11::TypeKind::Pointer)
		return "P" + abi_type(type->base, template_parameters);
	if (type->kind == pa11::TypeKind::LValueReference)
		return "R" + abi_type(type->base, template_parameters);
	if (type->kind == pa11::TypeKind::RValueReference)
		return "O" + abi_type(type->base, template_parameters);
	if (type->kind == pa11::TypeKind::Array)
		return "A" + (type->unknown_bound ? string("") :
		       to_string(type->bound)) + "_" +
		       abi_type(type->base, template_parameters);
	if (type->kind == pa11::TypeKind::Function)
	{
		string out = "F" + abi_type(type->base, template_parameters);
		for (size_t i = 0; i < type->parameters.size(); ++i)
			out += abi_type(type->parameters[i], template_parameters);
		if (type->parameters.empty())
			out += "v";
		out += "E";
		return out;
	}
	if (type->kind == pa11::TypeKind::Record ||
	    type->kind == pa11::TypeKind::Enum)
		return abi_record_type(type, template_parameters);
	if (type->kind == pa11::TypeKind::TemplateParameter)
	{
		map<string, size_t>::const_iterator found =
			template_parameters.find(type->name);
		size_t index = found == template_parameters.end() ? 0 : found->second;
		return index == 0 ? string("T_") :
		       string("T") + to_string(index - 1) + "_";
	}
	if (type->kind == pa11::TypeKind::MemberPointer)
		return "M" + abi_type(type->member_class, template_parameters) +
		       abi_type(type->base, template_parameters);
	return abi_fundamental_type(type->fundamental);
}

string abi_function_template_specialization_symbol(
	TemplateDeclaration* declaration,
	const vector<TemplateArgument>& full_args,
	Binding* binding)
{
	map<string, size_t> template_parameters;
	for (size_t i = 0; i < declaration->parameters.size(); ++i)
		if (!declaration->parameters[i].name.empty())
			template_parameters[declaration->parameters[i].name] = i;
	string encoded_name;
	if (binding->owner != NULL && binding->owner->kind == ScopeKind::Class)
	{
		TypePtr owner_record = pa11::record_type_for_scope(binding->owner);
		encoded_name = "N" +
		               abi_record_type(owner_record, template_parameters);
	}
	encoded_name += abi_source_name(declaration->name) + "I";
	for (size_t i = 0; i < full_args.size(); ++i)
		encoded_name += abi_template_argument(full_args[i],
		                                      template_parameters);
	encoded_name += "E";
	if (binding->owner != NULL && binding->owner->kind == ScopeKind::Class)
		encoded_name += "E";
	TypePtr fn_type = declaration->generic_function_type;
	string bare = abi_type(fn_type->base, template_parameters);
	size_t first_param =
		binding->owner != NULL &&
		binding->owner->kind == ScopeKind::Class &&
		!binding->is_static_member ? 1 : 0;
	for (size_t i = first_param; i < fn_type->parameters.size(); ++i)
		bare += abi_type(fn_type->parameters[i], template_parameters);
	if (fn_type->parameters.size() == first_param)
		bare += "v";
	return "_Z" + encoded_name + bare;
}

}  // namespace

Binding* Parser::instantiate_function_template(
	TemplateDeclaration* declaration,
	const vector<TemplateArgument>& arguments)
{
	vector<TemplateArgument> full_args =
		complete_template_arguments(declaration, arguments);
	string key = template_argument_key(full_args);
	validate_function_template_definition(declaration);
	map<string, Binding*>::iterator existing =
		declaration->function_specializations.find(key);
	Binding* replaced_specialization = NULL;
	if (existing != declaration->function_specializations.end())
	{
		if (!declaration->has_definition ||
		    existing->second->is_inline_definition ||
		    existing->second->is_object_root)
			return existing->second;
		replaced_specialization = existing->second;
		declaration->function_specializations.erase(existing);
	}
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
	template_type_substitutions_.insert(
		template_type_substitutions_.end(),
		declaration->outer_type_substitutions.begin(),
		declaration->outer_type_substitutions.end());
	template_value_substitutions_.insert(
		template_value_substitutions_.end(),
		declaration->outer_value_substitutions.begin(),
		declaration->outer_value_substitutions.end());
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
				                     declaration->hidden_friend);
			if (declaration->placeholder != NULL)
				binding->unwind_no = declaration->placeholder->unwind_no;
			declaration->function_specializations[key] = binding;
		if (declaration->friend_class_scope != NULL)
			add_friend_function(declaration->friend_class_scope, binding);
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
	size_t friend_scope_depth = active_friend_class_scopes_.size();
	if (declaration->friend_class_scope != NULL)
		active_friend_class_scopes_.push_back(declaration->friend_class_scope);
	if (declaration->placeholder != NULL)
		for (map<Scope*, vector<Binding*> >::const_iterator it =
			     class_friend_functions_.begin();
		     it != class_friend_functions_.end();
		     ++it)
			if (find(it->second.begin(),
			         it->second.end(),
			         declaration->placeholder) != it->second.end() &&
			    find(active_friend_class_scopes_.begin(),
			         active_friend_class_scopes_.end(),
			         it->first) == active_friend_class_scopes_.end())
				active_friend_class_scopes_.push_back(it->first);
	Node node;
	try
	{
		if (declaration->constructor_template)
		{
			size_t extra_before = extra_lowir_nodes_.size();
			if (!parse_qualified_constructor_definition(node, true))
			{
				parse_simple_or_function_declaration(node, true);
				if (node.binding == NULL &&
				    node.children.empty() &&
				    extra_lowir_nodes_.size() <= extra_before)
					throw runtime_error(
						"constructor template instantiation failed");
				if (node.binding == NULL && node.children.empty())
				{
					node = extra_lowir_nodes_.back();
					extra_lowir_nodes_.pop_back();
				}
			}
		}
		else
			parse_simple_or_function_declaration(node, true);
	}
	catch (const exception&)
	{
		active_friend_class_scopes_.resize(friend_scope_depth);
		declaration->completing_specializations.erase(key);
		template_type_substitutions_ = save_subst;
		template_value_substitutions_ = save_value_subst;
		scopes_ = save_scopes;
		pos_ = save_pos;
		force_new_function_binding_ = save_force_new_function_binding;
		throw;
	}
	active_friend_class_scopes_.resize(friend_scope_depth);
	template_type_substitutions_ = save_subst;
	template_value_substitutions_ = save_value_subst;
	scopes_ = save_scopes;
	pos_ = save_pos;
	force_new_function_binding_ = save_force_new_function_binding;
	Node fn;
	if (node.line.compare(0, 19, "function-definition") == 0 &&
	    node.binding != NULL)
		fn = node;
	else if (!node.children.empty())
		fn = node.children.back();
	if (fn.binding == NULL)
	{
		declaration->completing_specializations.erase(key);
		throw runtime_error("function template instantiation failed");
	}
	if (fn.line.compare(0, 19, "function-definition") != 0)
	{
		fn.binding->function_specialization_symbol =
			abi_function_template_specialization_symbol(declaration,
			                                            full_args,
			                                            fn.binding);
		if (declaration->placeholder != NULL)
			fn.binding->unwind_no = declaration->placeholder->unwind_no;
		if (replaced_specialization != NULL &&
		    replaced_specialization != fn.binding)
			replaced_specialization->aliased_binding = fn.binding;
		declaration->function_specializations[key] = fn.binding;
		if (declaration->friend_class_scope != NULL)
			add_friend_function(declaration->friend_class_scope, fn.binding);
		function_template_placeholders_[fn.binding] = declaration;
		declaration->completing_specializations.erase(key);
		return fn.binding;
	}
	fn.binding->is_inline_definition = true;
	fn.binding->function_specialization_symbol =
		abi_function_template_specialization_symbol(declaration,
		                                            full_args,
		                                            fn.binding);
	if (declaration->placeholder != NULL)
		fn.binding->unwind_no = declaration->placeholder->unwind_no;
	if (replaced_specialization != NULL &&
	    replaced_specialization != fn.binding)
		replaced_specialization->aliased_binding = fn.binding;
	extra_lowir_nodes_.push_back(fn);
	declaration->function_specializations[key] = fn.binding;
	if (declaration->friend_class_scope != NULL)
		add_friend_function(declaration->friend_class_scope, fn.binding);
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
		if (!pa11::is_deducible_template_parameter_type(pattern))
			return true;
		if (fixed != NULL && fixed->find(pattern->name) != fixed->end())
			return pa11::same_type(fixed->find(pattern->name)->second,
			                       argument);
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
			if (!pattern_dependent && pattern->is_template_specialization)
				for (size_t i = 0; i < pattern->template_arguments.size(); ++i)
				{
					vector<pa11::TemplateInstanceArgument> pending;
					pending.push_back(pattern->template_arguments[i]);
					while (!pending.empty())
					{
						pa11::TemplateInstanceArgument arg = pending.back();
						pending.pop_back();
						if (arg.kind == pa11::TemplateInstanceArgumentKind::Type)
						{
							if (type_is_template_dependent(arg.type))
								pattern_dependent = true;
						}
						else if (arg.kind == pa11::TemplateInstanceArgumentKind::Value)
						{
							if (arg.dependent ||
							    type_is_template_dependent(arg.type))
								pattern_dependent = true;
						}
						else if (arg.kind == pa11::TemplateInstanceArgumentKind::Template)
						{
							if (arg.dependent)
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
		Scope* pattern_owner =
			pattern->scope != NULL ? pattern->scope->parent : NULL;
		Scope* argument_owner =
			argument->scope != NULL ? argument->scope->parent : NULL;
		if (pt != record_template_declarations_.end() &&
		    at != record_template_declarations_.end() &&
		    pattern->is_template_specialization &&
		    argument->is_template_specialization &&
		    pattern->template_primary_name == argument->template_primary_name &&
		    (pattern_owner == NULL || argument_owner == NULL ||
		     pattern_owner == argument_owner))
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
		if (pattern->is_template_specialization &&
		    argument->is_template_specialization &&
		    pattern->template_primary_name == argument->template_primary_name &&
		    (pattern_owner == NULL || argument_owner == NULL ||
		     pattern_owner == argument_owner) &&
		    pattern->template_arguments.size() ==
			    argument->template_arguments.size())
		{
			for (size_t i = 0; i < pattern->template_arguments.size(); ++i)
			{
				const pa11::TemplateInstanceArgument& p_arg =
					pattern->template_arguments[i];
				const pa11::TemplateInstanceArgument& a_arg =
					argument->template_arguments[i];
				if (p_arg.kind == pa11::TemplateInstanceArgumentKind::Type &&
				    a_arg.kind == pa11::TemplateInstanceArgumentKind::Type)
				{
					if (!deduce_template_type(p_arg.type,
					                          a_arg.type,
					                          deduced,
					                          fixed))
						return false;
					continue;
				}
				if (p_arg.kind == pa11::TemplateInstanceArgumentKind::Value &&
				    a_arg.kind == pa11::TemplateInstanceArgumentKind::Value)
				{
					if (p_arg.dependent || a_arg.dependent)
						continue;
					if (p_arg.value != a_arg.value)
						return false;
					continue;
				}
				if (p_arg.kind == pa11::TemplateInstanceArgumentKind::Pack &&
				    a_arg.kind == pa11::TemplateInstanceArgumentKind::Pack &&
				    p_arg.pack.size() == a_arg.pack.size())
				{
					for (size_t p = 0; p < p_arg.pack.size(); ++p)
					{
						if (p_arg.pack[p].kind !=
						    pa11::TemplateInstanceArgumentKind::Type ||
						    a_arg.pack[p].kind !=
						    pa11::TemplateInstanceArgumentKind::Type)
							return false;
						if (!deduce_template_type(p_arg.pack[p].type,
						                          a_arg.pack[p].type,
						                          deduced,
						                          fixed))
							return false;
					}
					continue;
				}
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
				    pa11::is_deducible_template_parameter_type(
					    pa11::strip_cv(bare_pattern->base)) &&
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
		    pa11::is_deducible_template_parameter_type(
			    pa11::strip_cv(bare_pattern->base)) &&
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
