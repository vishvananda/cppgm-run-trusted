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
bool Parser::type_is_template_dependent(TypePtr type) const
{
	return template_type_has_template_parameter(type,
	                                           record_template_arguments_);
}

TypePtr Parser::substitute_template_type_parameter(TypePtr type,
                                                   const string& name,
                                                   TypePtr replacement) const
{
	if (type.get() == NULL)
		return type;
	if (type->kind == pa11::TypeKind::TemplateParameter &&
	    type->name == name)
		return replacement;
	if (type->kind == pa11::TypeKind::TemplateParameter &&
	    type->is_dependent_typename)
	{
		TypePtr out = pa11::make_dependent_typename_type(
			type->name,
			type->dependent_typename_qualified,
			type->dependent_typename_template_id,
			type->dependent_typename_decltype);
		out->template_primary_name = type->template_primary_name;
			for (size_t i = 0; i < type->template_arguments.size(); ++i)
			{
				TemplateArgument arg =
					template_argument_from_instance_argument(
						type->template_arguments[i]);
			arg = substitute_template_argument_type_parameter(arg,
			                                                  name,
			                                                  replacement);
			out->template_arguments.push_back(template_instance_argument(arg));
		}
		for (size_t i = 0;
		     i < type->dependent_typename_template_argument_lists.size();
		     ++i)
		{
			vector<pa11::TemplateInstanceArgument> argument_list;
			for (size_t j = 0;
			     j < type->dependent_typename_template_argument_lists[i].size();
			     ++j)
			{
				TemplateArgument arg =
					template_argument_from_instance_argument(
						type->dependent_typename_template_argument_lists[i][j]);
				arg = substitute_template_argument_type_parameter(
					arg,
					name,
					replacement);
				argument_list.push_back(template_instance_argument(arg));
			}
			out->dependent_typename_template_argument_lists.push_back(
				argument_list);
		}
		if (type->dependent_typename_qualified)
		{
		vector<string> parts;
		size_t begin = 0;
		for (;;)
		{
			size_t pos = type->name.find("::", begin);
				parts.push_back(type->name.substr(begin, pos - begin));
				if (pos == string::npos)
					break;
				begin = pos + 2;
			}
			string root_name = parts.empty() ? string() : parts[0];
			size_t root_template = root_name.find('<');
			if (root_template != string::npos)
				root_name = root_name.substr(0, root_template);
			TypePtr resolved = replacement;
			if (root_name == name && parts.size() >= 2)
			{
				bool resolved_ok = true;
				for (size_t i = 1; i < parts.size(); ++i)
				{
					TypePtr owner = resolved.get() != NULL
						? pa11::strip_cv(resolved) : TypePtr();
					if (owner.get() == NULL ||
					    owner->kind != pa11::TypeKind::Record ||
					    owner->scope == NULL)
					{
						resolved_ok = false;
						break;
					}
					try
					{
						const_cast<Parser*>(this)->
							complete_template_record(owner);
					}
					catch (const runtime_error&)
					{
					}
					string member_name = parts[i];
					size_t member_template = member_name.find('<');
					if (member_template != string::npos)
					{
						member_name =
							member_name.substr(0, member_template);
						if (out->template_arguments.empty())
						{
							resolved_ok = false;
							break;
						}
						vector<TemplateArgument> arguments;
						for (size_t j = 0;
						     j < out->template_arguments.size();
						     ++j)
							arguments.push_back(
								template_argument_from_instance_argument(
									out->template_arguments[j]));
						TemplateDeclaration* alias =
							const_cast<Parser*>(this)->
								find_alias_template(owner->scope,
								                    member_name);
						TemplateDeclaration* klass = alias == NULL
							? const_cast<Parser*>(this)->
								find_class_template(owner->scope,
								                    member_name)
							: NULL;
						if (alias == NULL && klass == NULL)
						{
							resolved_ok = false;
							break;
						}
						resolved = alias != NULL
							? const_cast<Parser*>(this)->
								instantiate_alias_template(alias,
								                           arguments)
							: const_cast<Parser*>(this)->
								instantiate_class_template(klass,
								                           arguments);
					}
					else
					{
						vector<Binding*> found =
							const_cast<Parser*>(this)->
								lookup_qualified_set(owner->scope,
								                     member_name,
								                     pa11::LOOKUP_TYPE);
						if (found.empty())
						{
							resolved_ok = false;
							break;
						}
						resolved = found[0]->type;
						const_cast<Parser*>(this)->
							complete_member_class_template_record(
								found[0]);
					}
				}
				if (resolved_ok)
					return resolved;
			}
		}
		return out;
	}
	if (type->kind == pa11::TypeKind::Cv)
		return pa11::make_cv(
			substitute_template_type_parameter(type->base,
			                                   name,
			                                   replacement),
			type->cv);
	if (type->kind == pa11::TypeKind::Pointer)
		return pa11::make_pointer(
			substitute_template_type_parameter(type->base,
			                                   name,
			                                   replacement));
	if (type->kind == pa11::TypeKind::LValueReference)
	{
		TypePtr base = substitute_template_type_parameter(type->base,
		                                                  name,
		                                                  replacement);
		if (base->kind == pa11::TypeKind::LValueReference ||
		    base->kind == pa11::TypeKind::RValueReference)
			return pa11::make_lvalue_reference(base->base);
		return pa11::make_lvalue_reference(base);
	}
	if (type->kind == pa11::TypeKind::RValueReference)
	{
		TypePtr base = substitute_template_type_parameter(type->base,
		                                                  name,
		                                                  replacement);
		if (base->kind == pa11::TypeKind::LValueReference)
			return base;
		if (base->kind == pa11::TypeKind::RValueReference)
			return pa11::make_rvalue_reference(base->base);
		return pa11::make_rvalue_reference(base);
	}
	if (type->kind == pa11::TypeKind::Array)
	{
		TypePtr out = pa11::make_array(
			substitute_template_type_parameter(type->base,
			                                   name,
			                                   replacement),
			type->unknown_bound,
			type->bound);
		out->name = type->name;
		out->tag = type->tag;
		return out;
	}
	if (type->kind == pa11::TypeKind::Function)
	{
		vector<TypePtr> params;
		bool consumed_variadic_pack = false;
		for (size_t i = 0; i < type->parameters.size(); ++i)
		{
			if (type->variadic && i + 1 == type->parameters.size())
			{
				string pack_name;
				bool has_pack_name = template_type_has_template_parameter_name(
					type->parameters[i],
					pack_name);
				if (has_pack_name && pack_name == name)
					consumed_variadic_pack = true;
			}
			params.push_back(
				substitute_template_type_parameter(type->parameters[i],
				                                   name,
				                                   replacement));
		}
		TypePtr out = pa11::make_function(
			substitute_template_type_parameter(type->base,
			                                   name,
			                                   replacement),
			params,
			type->variadic && !consumed_variadic_pack);
		out->cv = type->cv;
		out->ref_qualifier = type->ref_qualifier;
		return out;
	}
	if (type->kind == pa11::TypeKind::MemberPointer)
		return pa11::make_member_pointer(
			substitute_template_type_parameter(type->member_class,
			                                   name,
			                                   replacement),
			substitute_template_type_parameter(type->base,
			                                   name,
			                                   replacement));
	if (type->kind == pa11::TypeKind::Record &&
	    type->is_template_specialization)
	{
		for (size_t i = active_class_instantiations_.size(); i > 0; --i)
		{
			TypePtr active =
				pa11::strip_cv(active_class_instantiations_[i - 1].type);
			if (active.get() == type.get())
				return type;
		}
		TemplateArgument template_subst;
		if (!type->template_primary_name.empty() &&
		    find_template_value_substitution(type->template_primary_name,
		                                     template_subst) &&
		    template_subst.kind == TemplateArgumentKind::Template &&
		    template_subst.template_declaration != NULL)
		{
			map<const void*, vector<TemplateArgument> >::const_iterator args =
				record_template_arguments_.find(type.get());
			vector<TemplateArgument> substituted;
			if (args != record_template_arguments_.end())
			{
				for (size_t i = 0; i < args->second.size(); ++i)
				{
					TemplateArgument arg =
						substitute_template_argument_type_parameter(
							args->second[i],
							name,
							replacement);
					vector<TemplateArgument> expanded =
						expand_template_argument_pack(arg);
					for (size_t j = 0; j < expanded.size(); ++j)
					{
						TemplateArgument element =
							substitute_template_argument_type_parameter(
								expanded[j],
								name,
								replacement);
						if (element.kind == TemplateArgumentKind::Pack)
							substituted.insert(substituted.end(),
							                   element.pack.begin(),
							                   element.pack.end());
						else
							substituted.push_back(element);
					}
				}
			}
			else
			{
				for (size_t i = 0; i < type->template_arguments.size(); ++i)
				{
					TemplateArgument arg =
						raw_template_argument_from_instance_argument(
							type->template_arguments[i]);
					arg = substitute_template_argument_type_parameter(
						arg,
						name,
						replacement);
					vector<TemplateArgument> expanded =
						expand_template_argument_pack(arg);
					for (size_t j = 0; j < expanded.size(); ++j)
					{
						TemplateArgument element =
							substitute_template_argument_type_parameter(
								expanded[j],
								name,
								replacement);
						if (element.kind == TemplateArgumentKind::Pack)
							substituted.insert(substituted.end(),
							                   element.pack.begin(),
							                   element.pack.end());
						else
							substituted.push_back(element);
					}
				}
			}
			substituted = flatten_template_argument_packs(substituted);
			return template_subst.template_declaration->kind ==
				TemplateDeclarationKind::Alias
				? const_cast<Parser*>(this)->instantiate_alias_template(
					template_subst.template_declaration,
					substituted)
				: const_cast<Parser*>(this)->instantiate_class_template(
					template_subst.template_declaration,
					substituted);
		}
		map<const void*, TemplateDeclaration*>::const_iterator decl =
			record_template_declarations_.find(type.get());
		map<const void*, vector<TemplateArgument> >::const_iterator args =
			record_template_arguments_.find(type.get());
		vector<TemplateArgument> fallback_args;
		const vector<TemplateArgument>* source_args = NULL;
		if (args != record_template_arguments_.end())
			source_args = &args->second;
		else if (!type->template_arguments.empty())
		{
			for (size_t i = 0; i < type->template_arguments.size(); ++i)
				fallback_args.push_back(
					raw_template_argument_from_instance_argument(
						type->template_arguments[i]));
			source_args = &fallback_args;
		}
		TemplateDeclaration* record_decl =
			decl != record_template_declarations_.end()
			? decl->second : NULL;
		if (record_decl == NULL &&
		    source_args != NULL &&
		    !type->template_primary_name.empty())
			record_decl = const_cast<Parser*>(this)->
				find_class_template(NULL,
				                    type->template_primary_name);
		if (record_decl != NULL &&
		    find(completing_class_template_arguments_.begin(),
		         completing_class_template_arguments_.end(),
		         record_decl) !=
			    completing_class_template_arguments_.end())
			return type;
		if (record_decl != NULL && source_args != NULL)
		{
			bool needs_substitution = false;
			for (size_t i = 0; i < source_args->size(); ++i)
				if (template_argument_has_template_parameter(
					    (*source_args)[i],
					    record_template_arguments_))
					needs_substitution = true;
			if (needs_substitution)
			{
				vector<TemplateArgument> substituted;
				for (size_t i = 0; i < source_args->size(); ++i)
					substituted.push_back(
						substitute_template_argument_type_parameter(
							(*source_args)[i],
							name,
							replacement));
				return const_cast<Parser*>(this)->instantiate_class_template(
					record_decl,
					substituted);
			}
		}
	}
	return type;
}

TemplateArgument Parser::substitute_template_argument_type_parameter(
	const TemplateArgument& arg,
	const string& name,
	TypePtr replacement) const
{
	if (arg.kind == TemplateArgumentKind::Type)
		return TemplateArgument::type_arg(
			substitute_template_type_parameter(arg.type,
			                                   name,
			                                   replacement));
	if (arg.kind == TemplateArgumentKind::Value)
	{
		TemplateArgument out = arg;
		if (out.type.get() != NULL)
			out.type = substitute_template_type_parameter(out.type,
			                                             name,
			                                             replacement);
		for (size_t i = 0; i < out.value_owner_template_arguments.size(); ++i)
		{
			TemplateArgument owner_arg =
				template_argument_from_instance_argument(
					out.value_owner_template_arguments[i]);
			owner_arg = substitute_template_argument_type_parameter(
				owner_arg,
				name,
				replacement);
			out.value_owner_template_arguments[i] =
				template_instance_argument(owner_arg);
		}
		if (out.dependent &&
		    out.value_owner_template_name == name)
		{
			TypePtr owner = replacement.get() != NULL
				? pa11::strip_cv(replacement) : TypePtr();
			if (owner.get() != NULL &&
			    owner->kind == pa11::TypeKind::Record)
			{
					out.value_owner_template_name =
						owner->template_primary_name.empty()
						? owner->name
						: owner->template_primary_name;
					out.value_owner_template_arguments.clear();
					if (!owner->template_arguments.empty())
						out.value_owner_template_arguments =
							owner->template_arguments;
					else
					{
						map<const void*, vector<TemplateArgument> >::const_iterator args =
							record_template_arguments_.find(owner.get());
						if (args != record_template_arguments_.end() &&
						    !args->second.empty())
							for (size_t i = 0; i < args->second.size(); ++i)
								out.value_owner_template_arguments.push_back(
									template_instance_argument(args->second[i]));
					}
				}
			}
		return out;
	}
	if (arg.kind == TemplateArgumentKind::Pack)
	{
		vector<TemplateArgument> pack;
		for (size_t i = 0; i < arg.pack.size(); ++i)
			pack.push_back(substitute_template_argument_type_parameter(
				arg.pack[i],
				name,
				replacement));
		return TemplateArgument::pack_arg(pack);
	}
	return arg;
}


}  // namespace internal
}  // namespace pa12
