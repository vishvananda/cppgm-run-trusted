#include "pa12_templates_instance_support.h"
#include "pa12_types_support.h"

#include <algorithm>
#include <cstdint>
#include <functional>
#include <sstream>
#include <stdexcept>
#include <utility>

#include "posttoken_pipeline.h"
#include "pp_token.h"

using namespace std;

namespace pa12 {
namespace internal {
	TemplateArgument Parser::substitute_template_argument(
		const TemplateArgument& arg) const
	{
		if (arg.kind == TemplateArgumentKind::Pack &&
		    arg.pack_expansion &&
		    !arg.value_name.empty())
		{
			TemplateArgument out = arg;
			out.pack_expansion = false;
			return out;
		}
		string active_key = template_argument_key_part(arg);
		if (find(active_template_argument_substitution_keys_.begin(),
		         active_template_argument_substitution_keys_.end(),
		         active_key) !=
		    active_template_argument_substitution_keys_.end())
			return arg;
		struct ActiveTemplateArgumentSubstitution
		{
			vector<string>& keys;
			ActiveTemplateArgumentSubstitution(vector<string>& k,
			                                   const string& key)
			  : keys(k)
			{
				keys.push_back(key);
			}
			~ActiveTemplateArgumentSubstitution()
			{
				keys.pop_back();
			}
		} active_template_argument_substitution(
			active_template_argument_substitution_keys_,
			active_key);
		TemplateArgument resolved_member_value;
		bool dependent_value_expression =
			arg.kind == TemplateArgumentKind::Value &&
			arg.dependent &&
			arg.value_expr_end > arg.value_expr_begin;
		if (dependent_value_expression)
		{
			TemplateArgument evaluated;
			if (const_cast<Parser*>(this)->
				    try_evaluate_dependent_value_expression_argument(
					    arg,
					    evaluated))
			{
				if (!evaluated.dependent)
					return evaluated;
				if (template_argument_key_part(evaluated) ==
				    template_argument_key_part(arg))
					return evaluated;
				return substitute_template_argument(evaluated);
			}
		}
		bool simple_dependent_member_value =
			arg.kind == TemplateArgumentKind::Value &&
			arg.dependent &&
			!arg.value_owner_template_name.empty() &&
			!arg.value_member_name.empty() &&
			arg.value_name.find("()") == string::npos;
		if (dependent_value_expression && !simple_dependent_member_value)
			return arg;
		if (arg.kind == TemplateArgumentKind::Value &&
		    arg.dependent &&
		    !arg.value_name.empty() &&
		    arg.value_name.find("::") == string::npos)
	{
		TemplateArgument subst;
		if (find_template_value_substitution(arg.value_name, subst) &&
		    subst.kind == TemplateArgumentKind::Value)
		{
			if (template_argument_key_part(subst) ==
			    template_argument_key_part(arg))
				return arg;
			return substitute_template_argument(subst);
		}
	}
	if (arg.kind == TemplateArgumentKind::Value &&
	    arg.dependent &&
	    !arg.value_owner_template_name.empty() &&
	    arg.value_name.find("()") == string::npos &&
	    resolve_dependent_value_member_argument(arg, resolved_member_value))
	{
		return substitute_template_argument(resolved_member_value);
	}
		if (arg.kind == TemplateArgumentKind::Value &&
		    arg.dependent &&
		    resolve_dependent_value_member_argument(arg, resolved_member_value))
		return substitute_template_argument(resolved_member_value);
	if (arg.kind == TemplateArgumentKind::Value &&
	    arg.dependent &&
	    !arg.value_owner_template_name.empty() &&
	    !arg.value_owner_template_arguments.empty())
	{
		TemplateArgument deferred = arg;
		deferred.value_owner_template_arguments.clear();
		bool still_dependent = false;
		for (size_t i = 0; i < arg.value_owner_template_arguments.size(); ++i)
		{
			TemplateArgument owner_arg =
				template_argument_from_instance_argument(
					arg.value_owner_template_arguments[i]);
			owner_arg = substitute_template_argument(owner_arg);
			if (template_argument_has_template_parameter(
				    owner_arg,
				    record_template_arguments_))
				still_dependent = true;
			deferred.value_owner_template_arguments.push_back(
				template_instance_argument(owner_arg));
		}
		if (still_dependent)
			return deferred;
	}
	if (arg.kind == TemplateArgumentKind::Value &&
	    !arg.value_name.empty())
	{
		TemplateArgument subst;
		if (find_template_value_substitution(arg.value_name, subst))
		{
			if (subst.kind == TemplateArgumentKind::Value &&
			    subst.dependent == arg.dependent &&
			    subst.value_name == arg.value_name &&
			    subst.value_binding == arg.value_binding)
				subst = arg;
			if (arg.pack_expansion)
			{
				if (subst.kind == TemplateArgumentKind::Pack)
					return substitute_template_argument(subst);
			}
			else if (subst.kind == TemplateArgumentKind::Pack &&
			         parameter_pack_expansion_name(arg.value_name))
			{
				bool self_substitution =
					subst.pack.size() == 1 &&
					same_template_argument_value(
						subst.pack[0],
						arg,
						record_template_arguments_);
				if (!self_substitution)
					return substitute_template_argument(subst);
			}
			else if (subst.kind == TemplateArgumentKind::Value &&
			        !(subst.dependent == arg.dependent &&
			          subst.value_name == arg.value_name &&
			          subst.value_binding == arg.value_binding))
			{
				if (subst.dependent &&
				    !subst.value_owner_template_arguments.empty())
				{
					bool owner_still_dependent = false;
					for (size_t i = 0;
					     i < subst.value_owner_template_arguments.size();
					     ++i)
						if (template_instance_argument_has_template_parameter(
							    subst.value_owner_template_arguments[i],
							    record_template_arguments_))
							owner_still_dependent = true;
					if (owner_still_dependent)
						return subst;
				}
				return substitute_template_argument(subst);
			}
		}
	}
	if (arg.kind == TemplateArgumentKind::Template &&
	    !arg.value_name.empty())
	{
		TemplateArgument subst;
		if (find_template_value_substitution(arg.value_name, subst) &&
		    subst.kind == TemplateArgumentKind::Template &&
		    !(subst.template_declaration == arg.template_declaration &&
		      subst.value_name == arg.value_name))
			return subst;
		if (arg.template_declaration == NULL)
		{
			size_t member_sep = arg.value_name.rfind("::");
			if (member_sep != string::npos)
			{
				string owner_name = arg.value_name.substr(0, member_sep);
				string member_name = arg.value_name.substr(member_sep + 2);
				TypePtr owner_type;
					if (find_template_type_substitution(owner_name, owner_type))
					{
						owner_type = substitute_template_type(owner_type);
						TypePtr owner = owner_type.get() != NULL
							? pa11::strip_cv(owner_type) : TypePtr();
						if (owner.get() != NULL &&
					    owner->kind == pa11::TypeKind::Record &&
					    owner->scope != NULL)
					{
						const_cast<Parser*>(this)->
							complete_template_record(owner);
						TemplateDeclaration* declaration =
							const_cast<Parser*>(this)->
								find_class_template(owner->scope,
								                    member_name);
						if (declaration == NULL)
						{
							declaration = const_cast<Parser*>(this)->
								find_alias_template(owner->scope,
								                    member_name);
						}
							if (declaration != NULL)
							{
								return TemplateArgument::template_arg(
									declaration);
						}
					}
				}
			}
			Scope* qualifier = NULL;
			string lookup_name = arg.value_name;
			if (const_cast<Parser*>(this)->
				    resolve_template_name_spelling(arg.value_name,
				                                   qualifier,
				                                   lookup_name))
			{
				TemplateDeclaration* declaration =
					const_cast<Parser*>(this)->
						find_class_template(qualifier,
						                    lookup_name);
				if (declaration == NULL)
					declaration = const_cast<Parser*>(this)->
						find_alias_template(qualifier,
						                    lookup_name);
				if (declaration != NULL)
					return TemplateArgument::template_arg(declaration);
			}
		}
	}
	TemplateArgument out = arg;
	if (arg.kind == TemplateArgumentKind::Type)
	{
		if (arg.pack_expansion)
		{
			string pack_name;
			TemplateArgument subst;
			TypePtr bare = arg.type.get() != NULL
				? pa11::strip_cv(arg.type) : TypePtr();
			if (bare.get() != NULL &&
			    bare->is_dependent_typename &&
			    (bare->kind != pa11::TypeKind::TemplateParameter ||
			     bare->is_dependent_typename))
			{
				TemplateArgument single = arg;
				single.pack_expansion = false;
				TemplateArgument substituted =
					substitute_template_argument(single);
				if (substituted.kind == TemplateArgumentKind::Type &&
				    !template_argument_has_template_parameter(
					    substituted,
					    record_template_arguments_))
					return substituted;
			}
			if (bare.get() != NULL &&
			    bare->kind == pa11::TypeKind::TemplateParameter &&
			    !bare->is_dependent_typename &&
			    template_type_has_template_parameter_name(arg.type,
			                                              pack_name) &&
			    bare->name == pack_name &&
			    find_template_value_substitution(pack_name, subst) &&
			    subst.kind == TemplateArgumentKind::Pack)
				return substitute_template_argument(subst);
			vector<TemplateArgument> expanded =
				expand_template_argument_pack(arg);
			if (expanded.size() != 1 ||
			    template_argument_key_part(expanded[0]) !=
				    template_argument_key_part(arg))
			{
				vector<TemplateArgument> pack;
				for (size_t i = 0; i < expanded.size(); ++i)
				{
					TemplateArgument element =
						substitute_template_argument(expanded[i]);
					if (element.kind == TemplateArgumentKind::Pack)
						pack.insert(pack.end(),
						            element.pack.begin(),
						            element.pack.end());
					else
						pack.push_back(element);
				}
				return TemplateArgument::pack_arg(pack);
			}
		}
			try
			{
				out.type = substitute_template_type(arg.type);
				string substituted_pack_name;
				if (out.pack_expansion &&
				    !template_type_has_template_parameter_name(
					    out.type,
					    substituted_pack_name))
					out.pack_expansion = false;
			}
		catch (const runtime_error& err)
		{
			TypePtr bare = arg.type.get() != NULL
				? pa11::strip_cv(arg.type) : TypePtr();
			if (string(err.what()) != "dependent typename not resolved" ||
			    bare.get() == NULL ||
			    !bare->is_dependent_typename ||
			    !bare->dependent_typename_qualified)
				throw;
			size_t member_pos = bare->name.rfind("::");
			if (member_pos == string::npos)
				throw;
			if (bare->name.substr(member_pos + 2) == "type")
			{
				string parameter_name;
				if (function_template_candidate_instantiation_depth_ == 0 ||
				    template_type_has_template_parameter_name(arg.type,
				                                             parameter_name))
					return arg;
			}
			TemplateArgument value_arg =
				TemplateArgument::dependent_value_arg(TypePtr());
			value_arg.value_name = bare->name;
			value_arg.value_member_name =
				bare->name.substr(member_pos + 2);
			string owner_name = bare->template_primary_name;
			if (owner_name.empty())
			{
				string root = bare->name.substr(0, member_pos);
				size_t template_pos = root.find('<');
				owner_name = root.substr(0, template_pos);
			}
			value_arg.value_owner_template_name = owner_name;
			for (size_t ai = 0; ai < bare->template_arguments.size(); ++ai)
			{
				TemplateArgument owner_arg =
					template_argument_from_instance_argument(
						bare->template_arguments[ai]);
				owner_arg = substitute_template_argument(owner_arg);
				value_arg.value_owner_template_arguments.push_back(
					template_instance_argument(owner_arg));
			}
			return substitute_template_argument(value_arg);
		}
	}
	else if (arg.kind == TemplateArgumentKind::Value)
	{
		if (out.type.get() != NULL)
			out.type = substitute_template_type(out.type);
	}
	else if (arg.kind == TemplateArgumentKind::Pack)
	{
		if (!arg.value_name.empty())
		{
			TemplateArgument subst;
			if (find_template_value_substitution(arg.value_name, subst) &&
			    subst.kind != TemplateArgumentKind::Pack)
				return substitute_template_argument(subst);
		}
		if (arg.value_name.empty() &&
		    arg.pack.size() == 1 &&
		    arg.pack[0].kind == TemplateArgumentKind::Type)
		{
			string pack_name;
			TemplateArgument subst;
			TypePtr bare = arg.pack[0].type.get() != NULL
				? pa11::strip_cv(arg.pack[0].type) : TypePtr();
			if (bare.get() != NULL &&
			    bare->kind == pa11::TypeKind::TemplateParameter &&
			    !bare->is_dependent_typename &&
			    template_type_has_template_parameter_name(arg.pack[0].type,
			                                              pack_name) &&
			    bare->name == pack_name &&
			    find_template_value_substitution(pack_name, subst) &&
			    subst.kind == TemplateArgumentKind::Pack)
			{
					bool self_substitution =
						subst.pack.size() == 1 &&
						subst.pack[0].kind == TemplateArgumentKind::Type &&
						subst.pack[0].type.get() != NULL &&
						arg.pack[0].type.get() != NULL &&
						pa11::same_type(subst.pack[0].type,
						                arg.pack[0].type);
					if (!self_substitution)
						return substitute_template_argument(subst);
				}
			TemplateArgument pattern = arg.pack[0];
			string wrapped_pack_name;
			TemplateArgument wrapped_subst;
			if (template_type_has_template_parameter_name(pattern.type,
			                                              wrapped_pack_name) &&
			    find_template_value_substitution(wrapped_pack_name,
			                                     wrapped_subst) &&
			    wrapped_subst.kind == TemplateArgumentKind::Pack)
			{
				pattern.pack_expansion = true;
				vector<TemplateArgument> expanded =
					expand_template_argument_pack(pattern);
				if (expanded.size() != 1 ||
				    template_argument_key_part(expanded[0]) !=
					    template_argument_key_part(pattern))
				{
					vector<TemplateArgument> pack;
					for (size_t i = 0; i < expanded.size(); ++i)
					{
						TemplateArgument elem =
							substitute_template_argument(expanded[i]);
						if (elem.kind == TemplateArgumentKind::Pack)
							pack.insert(pack.end(),
							            elem.pack.begin(),
							            elem.pack.end());
						else
							pack.push_back(elem);
					}
					return TemplateArgument::pack_arg(pack);
				}
			}
			}
		out.pack.clear();
		for (size_t i = 0; i < arg.pack.size(); ++i)
		{
			TemplateArgument elem =
				substitute_template_argument(arg.pack[i]);
			if (elem.kind == TemplateArgumentKind::Pack)
				out.pack.insert(out.pack.end(),
				                elem.pack.begin(),
				                elem.pack.end());
			else
				out.pack.push_back(elem);
		}
	}
	return out;
}


}  // namespace internal
}  // namespace pa12
