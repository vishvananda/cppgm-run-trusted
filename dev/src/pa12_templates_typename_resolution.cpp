#include "pa12_templates_instance_support.h"

#include <algorithm>
#include <cstdint>
#include <sstream>
#include <stdexcept>
#include <utility>

#include "posttoken_pipeline.h"
#include "pp_token.h"

using namespace std;

namespace pa12 {
namespace internal {

TypePtr Parser::resolve_dependent_typename_type(TypePtr type) const
{
	if (type.get() == NULL ||
	    !type->is_dependent_typename)
		return TypePtr();
	if (!type->dependent_typename_qualified)
	{
		if (!type->dependent_typename_template_id)
			return TypePtr();
		string root_name = !type->template_primary_name.empty()
			? type->template_primary_name
			: type->name;
		size_t root_template = root_name.find('<');
		if (root_template != string::npos)
			root_name = root_name.substr(0, root_template);
		size_t template_argument_list_index = 0;
		vector<TemplateArgument> stored_arguments;
		if (!dependent_typename_template_argument_list(
			    type,
			    template_argument_list_index,
			    stored_arguments))
			return TypePtr();
		vector<TemplateArgument> arguments;
		for (size_t i = 0; i < stored_arguments.size(); ++i)
		{
			TemplateArgument arg = stored_arguments[i];
				vector<TemplateArgument> expanded;
				if (arg.kind == TemplateArgumentKind::Pack)
				{
					if (arg.pack.empty() && validating_template_definition_)
						return TypePtr();
					for (size_t p = 0; p < arg.pack.size(); ++p)
					{
					TemplateArgument element = arg.pack[p];
					string pack_name;
					TemplateArgument pack_subst;
						bool expands_current_pack =
							arg.value_name.empty() &&
							element.kind == TemplateArgumentKind::Type &&
							template_type_has_template_parameter_name(
							element.type,
							pack_name) &&
						find_template_value_substitution(pack_name,
						                                 pack_subst) &&
						pack_subst.kind == TemplateArgumentKind::Pack;
					if (expands_current_pack)
					{
						element.pack_expansion = true;
						vector<TemplateArgument> pieces =
							expand_template_argument_pack(element);
						expanded.insert(expanded.end(),
						                pieces.begin(),
						                pieces.end());
					}
					else
						expanded.push_back(element);
				}
			}
			else
			{
				expanded = expand_template_argument_pack(arg);
			}
			for (size_t j = 0; j < expanded.size(); ++j)
			{
				TemplateArgument subst =
					substitute_template_argument(expanded[j]);
				if (subst.kind == TemplateArgumentKind::Type)
				{
					TypePtr bare = subst.type.get() != NULL
						? pa11::strip_cv(subst.type) : TypePtr();
					if (bare.get() != NULL &&
					    bare->kind == pa11::TypeKind::Record &&
					    bare->is_template_specialization &&
					    bare->scope == NULL &&
					    !bare->template_primary_name.empty())
					{
						vector<TemplateArgument> concrete_args;
						bool concrete_args_dependent = false;
						map<const void*, vector<TemplateArgument> >::
							const_iterator stored_args =
								record_template_arguments_.find(
									bare.get());
						if (stored_args !=
						    record_template_arguments_.end())
						{
							for (size_t ai = 0;
							     ai < stored_args->second.size();
							     ++ai)
							{
								TemplateArgument concrete_arg =
									substitute_template_argument(
										stored_args->second[ai]);
								if (template_argument_has_template_parameter(
									    concrete_arg,
									    record_template_arguments_))
									concrete_args_dependent = true;
								concrete_args.push_back(concrete_arg);
							}
						}
						else
						{
							for (size_t ai = 0;
							     ai < bare->template_arguments.size();
							     ++ai)
							{
								TemplateArgument concrete_arg =
									template_argument_from_instance_argument(
										bare->template_arguments[ai]);
								concrete_arg =
									substitute_template_argument(
										concrete_arg);
								if (template_argument_has_template_parameter(
									    concrete_arg,
									    record_template_arguments_))
									concrete_args_dependent = true;
								concrete_args.push_back(concrete_arg);
							}
							}
							if (!concrete_args_dependent)
							{
								map<const void*, TemplateDeclaration*>::const_iterator
									stored_decl =
										record_template_declarations_.find(
											bare.get());
								TemplateDeclaration* alias = NULL;
								TemplateDeclaration* klass = NULL;
								if (stored_decl !=
								    record_template_declarations_.end())
								{
									if (stored_decl->second->kind ==
									    TemplateDeclarationKind::Alias)
										alias = stored_decl->second;
									else
										klass = stored_decl->second;
								}
								if (alias == NULL && klass == NULL)
								{
									Scope* qualifier = NULL;
									string lookup_name = bare->template_primary_name;
									const_cast<Parser*>(this)->
										resolve_template_name_spelling(
											bare->template_primary_name,
											qualifier,
											lookup_name);
									if (qualifier != NULL)
									{
										alias = const_cast<Parser*>(this)->
											find_alias_template(qualifier,
											                    lookup_name);
										if (alias == NULL)
											klass = const_cast<Parser*>(this)->
												find_class_template(qualifier,
												                    lookup_name);
									}
								}
								if (alias == NULL && klass == NULL)
									alias =
									const_cast<Parser*>(this)->
										find_alias_template(
											NULL,
											bare->template_primary_name);
								if (alias == NULL && klass == NULL)
									klass = const_cast<Parser*>(this)->
										find_class_template(
											NULL,
											bare->template_primary_name);
								if (alias != NULL)
									subst.type =
										const_cast<Parser*>(this)->
										instantiate_alias_template(
											alias,
											concrete_args);
							else if (klass != NULL)
								subst.type =
									const_cast<Parser*>(this)->
										instantiate_class_template(
											klass,
											concrete_args);
						}
					}
				}
				if (subst.kind == TemplateArgumentKind::Pack)
				{
					if (subst.pack.empty() && validating_template_definition_)
						return TypePtr();
					for (size_t p = 0; p < subst.pack.size(); ++p)
					{
						bool pack_element_dependent =
							template_argument_has_template_parameter(
								subst.pack[p],
								record_template_arguments_);
						if (pack_element_dependent &&
						    subst.pack[p].kind ==
							    TemplateArgumentKind::Type)
						{
							TypePtr bare = subst.pack[p].type.get() != NULL
								? pa11::strip_cv(subst.pack[p].type)
								: TypePtr();
							if (bare.get() != NULL &&
							    bare->is_dependent_typename)
							{
								try
								{
									TypePtr resolved =
										resolve_dependent_typename_type(bare);
									if (resolved.get() != NULL)
									{
										subst.pack[p].type = resolved;
										pack_element_dependent =
											type_is_template_dependent(resolved);
										bare = pa11::strip_cv(resolved);
									}
								}
								catch (const runtime_error&)
								{
								}
							}
							if (bare.get() != NULL &&
							    bare->kind == pa11::TypeKind::Record &&
							    bare->scope != NULL &&
							    !bare->is_dependent_typename &&
							    !validating_template_definition_)
								pack_element_dependent = false;
						}
						if (pack_element_dependent)
							return TypePtr();
						arguments.push_back(subst.pack[p]);
					}
					continue;
				}
				bool subst_dependent =
					template_argument_has_template_parameter(
						subst,
						record_template_arguments_);
				if (subst_dependent &&
				    subst.kind == TemplateArgumentKind::Type)
				{
					TypePtr bare = subst.type.get() != NULL
						? pa11::strip_cv(subst.type) : TypePtr();
					if (bare.get() != NULL &&
					    bare->is_dependent_typename)
					{
						try
						{
							TypePtr resolved =
								resolve_dependent_typename_type(bare);
							if (resolved.get() != NULL)
							{
								subst.type = resolved;
								subst_dependent =
									type_is_template_dependent(resolved);
								bare = pa11::strip_cv(resolved);
							}
						}
						catch (const runtime_error&)
						{
						}
					}
					if (bare.get() != NULL &&
					    bare->kind == pa11::TypeKind::Record &&
					    bare->scope != NULL &&
					    !bare->is_dependent_typename &&
					    !validating_template_definition_)
						subst_dependent = false;
				}
				if (subst_dependent)
					return TypePtr();
				arguments.push_back(subst);
			}
			}
				arguments = flatten_template_argument_packs(arguments);
				map<const void*, TemplateDeclaration*>::const_iterator
					stored_decl = record_template_declarations_.find(type.get());
				if (stored_decl != record_template_declarations_.end() &&
				    stored_decl->second != NULL)
				{
					vector<TemplateArgument> stored_instantiation_args =
						arguments;
					map<const void*, vector<TemplateArgument> >::const_iterator
						stored_args = record_template_arguments_.find(type.get());
					if (stored_args != record_template_arguments_.end())
					{
						stored_instantiation_args.clear();
						for (size_t ai = 0; ai < stored_args->second.size();
						     ++ai)
						{
							TemplateArgument stored_arg =
								substitute_template_argument(
									stored_args->second[ai]);
							if (template_argument_has_template_parameter(
								    stored_arg,
								    record_template_arguments_))
								return TypePtr();
							stored_instantiation_args.push_back(stored_arg);
						}
						stored_instantiation_args =
							flatten_template_argument_packs(
								stored_instantiation_args);
					}
					return stored_decl->second->kind ==
						TemplateDeclarationKind::Alias
						? const_cast<Parser*>(this)->instantiate_alias_template(
							stored_decl->second,
							stored_instantiation_args)
						: const_cast<Parser*>(this)->instantiate_class_template(
							stored_decl->second,
							stored_instantiation_args);
				}
				Scope* qualifier = NULL;
				string lookup_root_name = root_name;
				const_cast<Parser*>(this)->resolve_template_name_spelling(
					root_name,
					qualifier,
					lookup_root_name);
					TemplateArgument template_subst;
					if (qualifier == NULL &&
					    find_template_value_substitution(root_name, template_subst) &&
					    template_subst.kind == TemplateArgumentKind::Template &&
					    template_subst.template_declaration != NULL)
				{
					return template_subst.template_declaration->kind ==
						TemplateDeclarationKind::Alias
						? const_cast<Parser*>(this)->instantiate_alias_template(
							template_subst.template_declaration,
							arguments)
						: const_cast<Parser*>(this)->instantiate_class_template(
							template_subst.template_declaration,
							arguments);
				}
					TemplateDeclaration* alias =
						const_cast<Parser*>(this)->find_alias_template(
							qualifier,
							lookup_root_name);
					if (alias == NULL)
				{
					for (map<Scope*, map<string, TemplateDeclaration*> >::const_iterator
						     sit = alias_templates_.begin();
					     qualifier == NULL &&
					     sit != alias_templates_.end() && alias == NULL;
				     ++sit)
				{
					map<string, TemplateDeclaration*>::const_iterator it =
						sit->second.find(root_name);
					if (it != sit->second.end())
						alias = it->second;
				}
			}
				TemplateDeclaration* klass = alias == NULL
					? const_cast<Parser*>(this)->find_class_template(
						qualifier,
						lookup_root_name)
					: NULL;
				if (alias == NULL && klass == NULL && qualifier == NULL)
				{
					size_t member_sep = root_name.rfind("::");
					if (member_sep != string::npos)
					{
						string owner_name = root_name.substr(0, member_sep);
						string member_name = root_name.substr(member_sep + 2);
						Scope* owner_qualifier = NULL;
						string owner_lookup_name = owner_name;
						const_cast<Parser*>(this)->resolve_template_name_spelling(
							owner_name,
							owner_qualifier,
							owner_lookup_name);
						TemplateDeclaration* owner_template =
							const_cast<Parser*>(this)->find_class_template(
								owner_qualifier,
								owner_lookup_name);
						if (owner_template != NULL)
						{
							map<pair<TemplateDeclaration*, string>,
							    TemplateDeclaration*>::const_iterator mit =
								member_class_templates_.find(
									make_pair(owner_template, member_name));
							if (mit != member_class_templates_.end())
								klass = mit->second;
						}
					}
				}
				if (alias == NULL && klass == NULL)
				{
					for (map<Scope*, map<string, TemplateDeclaration*> >::const_iterator
						     sit = class_templates_.begin();
					     qualifier == NULL &&
					     sit != class_templates_.end() && klass == NULL;
				     ++sit)
				{
					map<string, TemplateDeclaration*>::const_iterator it =
						sit->second.find(root_name);
					if (it != sit->second.end())
						klass = it->second;
				}
			}
			if (alias == NULL && klass == NULL)
				return TypePtr();
			return alias != NULL
				? const_cast<Parser*>(this)->instantiate_alias_template(
					alias,
					arguments)
				: const_cast<Parser*>(this)->instantiate_class_template(
					klass,
					arguments);
		}
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
		if (parts.size() < 2)
			return TypePtr();
		TypePtr root_subst;
		TypePtr resolved;
		Scope* resolved_type_scope = NULL;
		size_t first_type_part = 0;
		Scope* namespace_scope = NULL;
		while (first_type_part < parts.size())
		{
			string qualifier_name = parts[first_type_part];
			if (qualifier_name.find('<') != string::npos)
				break;
			vector<Binding*> qualifiers = namespace_scope != NULL
				? const_cast<Parser*>(this)->lookup_qualified_set(
					namespace_scope,
					qualifier_name,
					pa11::LOOKUP_NAMESPACE)
				: const_cast<Parser*>(this)->lookup_unqualified_set(
					current_scope(),
					qualifier_name,
					pa11::LOOKUP_NAMESPACE);
			if (qualifiers.empty())
				break;
			namespace_scope = qualifiers[0]->target_scope;
			++first_type_part;
		}
		if (first_type_part >= parts.size())
			return TypePtr();
		string root_name = parts[first_type_part];
		size_t root_template = root_name.find('<');
		if (root_template != string::npos)
			root_name = root_name.substr(0, root_template);
		size_t template_argument_list_index = 0;
		if (root_template != string::npos)
		{
			vector<TemplateArgument> stored_arguments;
			if (!dependent_typename_template_argument_list(
				    type,
				    template_argument_list_index,
				    stored_arguments))
				return TypePtr();
			vector<TemplateArgument> arguments;
			for (size_t i = 0; i < stored_arguments.size(); ++i)
			{
				TemplateArgument arg = substitute_template_argument(
					stored_arguments[i]);
				if (arg.kind == TemplateArgumentKind::Template &&
				    arg.template_declaration == NULL &&
				    !arg.value_name.empty())
				{
					TemplateDeclaration* alias =
						const_cast<Parser*>(this)->find_alias_template(
							NULL,
							arg.value_name);
					if (alias == NULL)
					{
						for (map<Scope*, map<string, TemplateDeclaration*> >::
							     const_iterator sit = alias_templates_.begin();
						     sit != alias_templates_.end() && alias == NULL;
						     ++sit)
						{
							map<string, TemplateDeclaration*>::const_iterator it =
								sit->second.find(arg.value_name);
							if (it != sit->second.end())
								alias = it->second;
						}
					}
					TemplateDeclaration* klass = alias == NULL
						? const_cast<Parser*>(this)->find_class_template(
							NULL,
							arg.value_name)
						: NULL;
					if (alias == NULL && klass == NULL)
					{
						for (map<Scope*, map<string, TemplateDeclaration*> >::
							     const_iterator sit = class_templates_.begin();
						     sit != class_templates_.end() && klass == NULL;
						     ++sit)
						{
							map<string, TemplateDeclaration*>::const_iterator it =
								sit->second.find(arg.value_name);
							if (it != sit->second.end())
								klass = it->second;
						}
					}
					if (alias != NULL || klass != NULL)
					{
						arg.template_declaration =
							alias != NULL ? alias : klass;
						arg.value_name.clear();
					}
				}
				bool arg_dependent =
					template_argument_has_template_parameter(
						arg,
						record_template_arguments_);
				if (arg_dependent &&
				    arg.kind == TemplateArgumentKind::Type)
				{
					TypePtr bare = arg.type.get() != NULL
						? pa11::strip_cv(arg.type) : TypePtr();
					if (bare.get() != NULL &&
					    bare->kind == pa11::TypeKind::Record &&
					    bare->scope != NULL &&
					    !bare->is_dependent_typename &&
					    !validating_template_definition_)
						arg_dependent = false;
				}
					if (arg_dependent &&
					    active_template_match_parser != this)
						return TypePtr();
				arguments.push_back(arg);
			}
			arguments = flatten_template_argument_packs(arguments);
			TemplateArgument template_subst;
			if (namespace_scope == NULL &&
			    find_template_value_substitution(root_name, template_subst) &&
			    template_subst.kind == TemplateArgumentKind::Template &&
			    template_subst.template_declaration != NULL)
			{
				resolved = template_subst.template_declaration->kind ==
					TemplateDeclarationKind::Alias
					? const_cast<Parser*>(this)->instantiate_alias_template(
						template_subst.template_declaration,
						arguments)
					: const_cast<Parser*>(this)->instantiate_class_template(
						template_subst.template_declaration,
						arguments);
				resolved_type_scope = NULL;
			}
			if (resolved.get() == NULL)
			{
				TemplateDeclaration* alias =
					const_cast<Parser*>(this)->find_alias_template(
						namespace_scope,
						root_name);
				if (alias == NULL)
				{
					for (map<Scope*, map<string, TemplateDeclaration*> >::const_iterator
						     sit = alias_templates_.begin();
					     namespace_scope == NULL &&
					     sit != alias_templates_.end() && alias == NULL;
					     ++sit)
					{
						map<string, TemplateDeclaration*>::const_iterator it =
							sit->second.find(root_name);
						if (it != sit->second.end())
							alias = it->second;
					}
				}
				TemplateDeclaration* klass = alias == NULL
					? const_cast<Parser*>(this)->find_class_template(
						namespace_scope,
						root_name)
					: NULL;
				if (alias == NULL && klass == NULL)
				{
					for (map<Scope*, map<string, TemplateDeclaration*> >::const_iterator
						     sit = class_templates_.begin();
					     namespace_scope == NULL &&
					     sit != class_templates_.end() && klass == NULL;
					     ++sit)
					{
						map<string, TemplateDeclaration*>::const_iterator it =
							sit->second.find(root_name);
						if (it != sit->second.end())
							klass = it->second;
					}
				}
				if (alias == NULL && klass == NULL)
					return TypePtr();
				resolved = alias != NULL
					? const_cast<Parser*>(this)->instantiate_alias_template(
						alias,
						arguments)
					: const_cast<Parser*>(this)->instantiate_class_template(
						klass,
						arguments);
				resolved_type_scope = NULL;
			}
			if (resolved.get() != NULL && resolved->is_dependent_typename)
				resolved = substitute_template_type(resolved);
			if (resolved.get() != NULL &&
			    resolved->is_dependent_typename &&
			    parts.size() > first_type_part + 1)
			{
				string rewritten_name = resolved->name;
				for (size_t suffix = first_type_part + 1;
				     suffix < parts.size();
				     ++suffix)
					rewritten_name += "::" + parts[suffix];
				TypePtr out = pa11::make_dependent_typename_type(
					rewritten_name,
					true,
					resolved->dependent_typename_template_id,
					resolved->dependent_typename_decltype);
				out->template_primary_name =
					resolved->template_primary_name;
				out->template_arguments = resolved->template_arguments;
				out->dependent_typename_template_argument_lists =
					resolved->dependent_typename_template_argument_lists;
				return out;
			}
		}
		else if (namespace_scope == NULL &&
		         find_template_type_substitution(parts[first_type_part],
		                                         root_subst))
			resolved = substitute_template_type(root_subst);
		else
		{
			vector<Binding*> roots = namespace_scope != NULL
				? const_cast<Parser*>(this)->lookup_qualified_set(
					namespace_scope,
					parts[first_type_part],
					pa11::LOOKUP_TYPE)
				: const_cast<Parser*>(this)->lookup_unqualified_set(
					current_scope(),
					parts[first_type_part],
					pa11::LOOKUP_TYPE);
			if (roots.empty())
				return TypePtr();
			resolved = roots[0]->type;
			const_cast<Parser*>(this)->
				complete_member_class_template_record(roots[0]);
		}
		for (size_t i = first_type_part + 1; i < parts.size(); ++i)
	{
			TypePtr owner = resolved.get() != NULL
				? pa11::strip_cv(resolved) : TypePtr();
			if (owner.get() == NULL ||
		    owner->kind != pa11::TypeKind::Record ||
		    owner->scope == NULL)
			return TypePtr();
		try
		{
			const_cast<Parser*>(this)->complete_template_record(owner);
		}
		catch (const runtime_error&)
		{
			if (!active_class_instantiation_dependent() &&
			    !validating_template_definition_)
				throw;
		}
		string member_name = parts[i];
		size_t member_template = member_name.find('<');
		if (member_template != string::npos)
		{
			member_name = member_name.substr(0, member_template);
			vector<TemplateArgument> stored_arguments;
			if (!dependent_typename_template_argument_list(
				    type,
				    template_argument_list_index,
				    stored_arguments))
				return TypePtr();
			vector<TemplateArgument> arguments;
			for (size_t j = 0; j < stored_arguments.size(); ++j)
			{
				TemplateArgument arg = stored_arguments[j];
				arguments.push_back(substitute_template_argument(arg));
			}
			arguments = flatten_template_argument_packs(arguments);
			TemplateDeclaration* alias =
				const_cast<Parser*>(this)->find_alias_template(
					owner->scope,
					member_name);
			TemplateDeclaration* klass = alias == NULL
					? const_cast<Parser*>(this)->find_class_template(
						owner->scope,
						member_name)
					: NULL;
						if (alias == NULL && klass == NULL)
							return TypePtr();
						resolved = alias != NULL
				? const_cast<Parser*>(this)->instantiate_alias_template(
					alias,
					arguments)
				: const_cast<Parser*>(this)->instantiate_class_template(
					klass,
					arguments);
			resolved_type_scope = NULL;
		}
		else
		{
			vector<Binding*> found =
				const_cast<Parser*>(this)->lookup_qualified_set(
					owner->scope,
					member_name,
					pa11::LOOKUP_TYPE);
			if (found.empty())
			{
				TypePtr base = owner->base;
				if (base.get() != NULL &&
				    base->is_dependent_typename)
				{
					try
					{
						TypePtr resolved_base =
							resolve_dependent_typename_type(base);
						base = resolved_base.get() != NULL
							? resolved_base
							: substitute_template_type(base);
					}
					catch (const runtime_error&)
					{
					}
				}
				base = base.get() != NULL ? pa11::strip_cv(base) : TypePtr();
				if (base.get() != NULL &&
				    base->kind == pa11::TypeKind::Record &&
				    base->scope != NULL)
				{
					const_cast<Parser*>(this)->complete_template_record(base);
					found = const_cast<Parser*>(this)->lookup_qualified_set(
						base->scope,
						member_name,
						pa11::LOOKUP_TYPE);
				}
			}
					if (found.empty())
						return TypePtr();
					resolved = found[0]->type;
				resolved_type_scope = owner->scope;
				const_cast<Parser*>(this)->
					complete_member_class_template_record(found[0]);
			}
	}
	if (resolved_type_scope != NULL)
		return substitute_template_type_in_scope(resolved,
		                                         resolved_type_scope);
	return resolved;
}

TypePtr Parser::substitute_template_type_in_scope(TypePtr type,
                                                  Scope* scope) const
{
	if (scope == NULL)
		return substitute_template_type(type);
	Parser* self = const_cast<Parser*>(this);
	vector<Scope*> save_scopes = self->scopes_;
	vector<map<string, TypePtr> > save_subst =
		self->template_type_substitutions_;
	vector<map<string, TemplateArgument> > save_value_subst =
		self->template_value_substitutions_;
	vector<set<string> > save_pack_subst =
		self->template_type_parameter_packs_;
	self->scopes_.clear();
	self->scopes_.push_back(scope);
	TypePtr record = pa11::record_type_for_scope(scope);
	record = record.get() != NULL ? pa11::strip_cv(record) : TypePtr();
	map<const void*, TemplateDeclaration*>::const_iterator decl =
		record.get() != NULL
		? record_template_declarations_.find(record.get())
		: record_template_declarations_.end();
	map<const void*, vector<TemplateArgument> >::const_iterator args =
		record.get() != NULL
		? record_template_arguments_.find(record.get())
		: record_template_arguments_.end();
	auto push_record_template_substitutions =
		[&](TemplateDeclaration* declaration,
		    const vector<TemplateArgument>& arguments) {
			map<string, TypePtr> subst;
			map<string, TemplateArgument> value_subst;
			set<string> pack_subst;
			for (size_t i = 0;
			     i < arguments.size() && i < declaration->parameters.size();
			     ++i)
				if (!declaration->parameters[i].name.empty())
				{
					const TemplateParameterInfo& parameter =
						declaration->parameters[i];
					if (parameter.kind == TemplateParameterKind::Type)
					{
						if (parameter.is_pack)
						{
							subst[parameter.name] =
								pa11::make_template_parameter_type(
									parameter.name);
							value_subst[parameter.name] = arguments[i];
							if (arguments[i].kind ==
							        TemplateArgumentKind::Pack &&
							    arguments[i].pack.size() == 1 &&
							    arguments[i].pack[0].kind ==
								    TemplateArgumentKind::Type)
								subst[parameter.name] =
									arguments[i].pack[0].type;
							else if (arguments[i].kind ==
							         TemplateArgumentKind::Type)
								subst[parameter.name] =
									arguments[i].type;
							pack_subst.insert(parameter.name);
						}
						else
							subst[parameter.name] = arguments[i].type;
					}
					else
						value_subst[parameter.name] = arguments[i];
				}
			self->template_type_substitutions_.insert(
				self->template_type_substitutions_.end(),
				declaration->outer_type_substitutions.begin(),
				declaration->outer_type_substitutions.end());
			self->template_value_substitutions_.insert(
				self->template_value_substitutions_.end(),
				declaration->outer_value_substitutions.begin(),
				declaration->outer_value_substitutions.end());
			self->template_type_substitutions_.push_back(subst);
			self->template_value_substitutions_.push_back(value_subst);
			self->template_type_parameter_packs_.push_back(pack_subst);
		};
	vector<TypePtr> enclosing_records;
	for (Scope* cur = scope->parent; cur != NULL; cur = cur->parent)
	{
		TypePtr cur_record = pa11::record_type_for_scope(cur);
		cur_record = cur_record.get() != NULL
			? pa11::strip_cv(cur_record) : TypePtr();
		if (cur_record.get() != NULL &&
		    record_template_declarations_.find(cur_record.get()) !=
			    record_template_declarations_.end() &&
		    record_template_arguments_.find(cur_record.get()) !=
			    record_template_arguments_.end())
			enclosing_records.push_back(cur_record);
	}
	for (size_t i = enclosing_records.size(); i > 0; --i)
	{
		TypePtr enclosing = enclosing_records[i - 1];
		push_record_template_substitutions(
			record_template_declarations_.find(enclosing.get())->second,
			record_template_arguments_.find(enclosing.get())->second);
	}
	if (decl != record_template_declarations_.end() &&
	    args != record_template_arguments_.end())
		push_record_template_substitutions(decl->second, args->second);
	try
	{
		TypePtr out = substitute_template_type(type);
		self->scopes_ = save_scopes;
		self->template_type_substitutions_ = save_subst;
		self->template_value_substitutions_ = save_value_subst;
		self->template_type_parameter_packs_ = save_pack_subst;
		return out;
	}
	catch (...)
	{
		self->scopes_ = save_scopes;
		self->template_type_substitutions_ = save_subst;
		self->template_value_substitutions_ = save_value_subst;
		self->template_type_parameter_packs_ = save_pack_subst;
		throw;
	}
}

}  // namespace internal
}  // namespace pa12
