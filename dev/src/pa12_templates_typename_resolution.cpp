#include "pa12_templates_instance_support.h"
#include "pa12_types_support.h"
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
	auto hash_node_value_type = [&](TypePtr node_type) -> TypePtr {
		if (node_type.get() == NULL)
			return TypePtr();
		try
		{
			node_type = substitute_template_type(node_type);
		}
		catch (const runtime_error&)
		{
		}
		TypePtr bare = pa11::strip_cv(node_type);
		if (bare.get() == NULL ||
		    bare->kind != pa11::TypeKind::Record)
			return TypePtr();
		string primary = bare->template_primary_name.empty()
			? bare->name : bare->template_primary_name;
		size_t sep = primary.rfind("::");
		if (sep != string::npos)
			primary = primary.substr(sep + 2);
		size_t args_pos = primary.find('<');
		if (args_pos != string::npos)
			primary = primary.substr(0, args_pos);
		if (primary != "_Hash_node")
			return TypePtr();
		vector<TemplateArgument> args;
		map<const void*, vector<TemplateArgument> >::const_iterator stored =
			record_template_arguments_.find(bare.get());
		if (stored != record_template_arguments_.end())
			args = stored->second;
		else
			for (size_t i = 0; i < bare->template_arguments.size(); ++i)
				args.push_back(template_argument_from_instance_argument(
					bare->template_arguments[i]));
		if (args.empty())
			return TypePtr();
		TemplateArgument value_arg = substitute_template_argument(args[0]);
		return value_arg.kind == TemplateArgumentKind::Type
			? value_arg.type : TypePtr();
	};
	auto lookup_type_member = [&](Scope* scope,
	                              const string& name) -> TypePtr {
		if (scope == NULL)
			return TypePtr();
		try
		{
			vector<Binding*> found =
				const_cast<Parser*>(this)->lookup_qualified_set(
					scope,
					name,
					pa11::LOOKUP_TYPE);
			if (found.empty() || found[0]->type.get() == NULL)
				return TypePtr();
			return substitute_template_type_in_scope(found[0]->type, scope);
		}
		catch (const runtime_error&)
		{
			return TypePtr();
		}
	};
	auto allocator_member_type =
		[&](TypePtr allocator_type, const string& member_name) -> TypePtr {
		try
		{
			allocator_type = substitute_template_type(allocator_type);
		}
		catch (const runtime_error&)
		{
		}
		TypePtr bare = allocator_type.get() != NULL
			? pa11::strip_cv(allocator_type) : TypePtr();
		if (bare.get() == NULL ||
		    bare->kind != pa11::TypeKind::Record ||
		    bare->scope == NULL)
			return TypePtr();
		try
		{
			const_cast<Parser*>(this)->complete_template_record(bare);
		}
		catch (const runtime_error&)
		{
		}
		return lookup_type_member(bare->scope, member_name);
	};
	auto allocator_value_type = [&](TypePtr allocator_type) -> TypePtr {
		return allocator_member_type(allocator_type, "value_type");
	};
	auto hosted_get_value_type_from_context = [&]() -> TypePtr {
		if (!hosted_compatibility_)
			return TypePtr();
		for (size_t i = active_class_instantiations_.size(); i > 0; --i)
		{
			const ActiveClassInstantiation& active =
				active_class_instantiations_[i - 1];
			TypePtr active_record = active.type.get() != NULL
				? pa11::strip_cv(active.type) : TypePtr();
			if (active_record.get() == NULL ||
			    active_record->kind != pa11::TypeKind::Record)
				continue;
			TypePtr node_type = lookup_type_member(active_record->scope,
			                                       "__node_type");
			TypePtr value_type = hash_node_value_type(node_type);
			if (value_type.get() != NULL)
				return value_type;
			map<const void*, vector<TemplateArgument> >::const_iterator args =
				record_template_arguments_.find(active_record.get());
			if (active.declaration == NULL ||
			    args == record_template_arguments_.end())
				continue;
			for (size_t pi = 0;
			     pi < active.declaration->parameters.size() &&
			     pi < args->second.size();
			     ++pi)
			{
				if (active.declaration->parameters[pi].name != "_NodeAlloc" ||
				    args->second[pi].kind != TemplateArgumentKind::Type)
					continue;
				node_type = allocator_value_type(args->second[pi].type);
				value_type = hash_node_value_type(node_type);
				if (value_type.get() != NULL)
					return value_type;
			}
		}
		for (Scope* scope = current_scope(); scope != NULL; scope = scope->parent)
		{
			TypePtr node_type = lookup_type_member(scope, "__node_type");
			TypePtr value_type = hash_node_value_type(node_type);
			if (value_type.get() != NULL)
				return value_type;
		}
		for (size_t si = template_type_substitutions_.size(); si > 0; --si)
		{
			map<string, TypePtr>::const_iterator node_alloc =
				template_type_substitutions_[si - 1].find("_NodeAlloc");
			if (node_alloc == template_type_substitutions_[si - 1].end())
				continue;
			TypePtr node_type = allocator_value_type(node_alloc->second);
			TypePtr value_type = hash_node_value_type(node_type);
			if (value_type.get() != NULL)
				return value_type;
		}
		return TypePtr();
	};
	auto hosted_allocator_rebind_value_type = [&]() -> TypePtr {
		if (!hosted_compatibility_)
			return TypePtr();
		const char* allocator_names[] = {"_Alloc", "_NodeAlloc"};
		for (size_t ni = 0;
		     ni < sizeof(allocator_names) / sizeof(allocator_names[0]);
		     ++ni)
		{
			for (size_t si = template_type_substitutions_.size();
			     si > 0;
			     --si)
			{
				map<string, TypePtr>::const_iterator it =
					template_type_substitutions_[si - 1].find(
						allocator_names[ni]);
				if (it == template_type_substitutions_[si - 1].end())
					continue;
				TypePtr value_type = allocator_value_type(it->second);
				if (value_type.get() != NULL)
					return value_type;
			}
		}
		const char* names[] = {"_Tp", "_Up", "_Val", "T"};
		for (size_t ni = 0; ni < sizeof(names) / sizeof(names[0]); ++ni)
		{
			for (size_t si = template_type_substitutions_.size(); si > 0; --si)
			{
				map<string, TypePtr>::const_iterator it =
					template_type_substitutions_[si - 1].find(names[ni]);
				if (it == template_type_substitutions_[si - 1].end())
					continue;
				try
				{
					return substitute_template_type(it->second);
				}
				catch (const runtime_error&)
				{
					return it->second;
				}
			}
		}
		return TypePtr();
	};
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
				if (stored_arguments.empty() &&
				    hosted_compatibility_ &&
				    root_name == "__get_value_type")
				{
					vector<Binding*> node_type =
						const_cast<Parser*>(this)->lookup_unqualified_set(
							current_scope(),
							"__node_type",
							pa11::LOOKUP_TYPE);
					if (!node_type.empty() &&
					    node_type[0]->type.get() != NULL)
						stored_arguments.push_back(
							TemplateArgument::type_arg(node_type[0]->type));
				}
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
		if (hosted_compatibility_)
		{
			TypePtr active_allocator =
				hosted_active_template_parameter_type(root_name);
			if (active_allocator.get() != NULL)
			{
				size_t rebind_list_index = 0;
				size_t part_index = first_type_part + 1;
				bool consumed_rebind = false;
				TypePtr current_allocator = active_allocator;
				while (part_index + 1 < parts.size())
				{
					string member_name = parts[part_index];
					size_t member_template = member_name.find('<');
					if (member_template != string::npos)
						member_name = member_name.substr(0,
						                                  member_template);
					if (member_name != "rebind" ||
					    parts[part_index + 1] != "other")
						break;
					vector<TemplateArgument> stored_arguments;
					if (!dependent_typename_template_argument_list(
						    type,
						    rebind_list_index,
						    stored_arguments) ||
					    stored_arguments.empty())
					{
						size_t skip = part_index;
						while (skip + 1 < parts.size())
						{
							string skipped = parts[skip];
							size_t skipped_template =
								skipped.find('<');
							if (skipped_template != string::npos)
								skipped = skipped.substr(
									0,
									skipped_template);
							if (skipped != "rebind" ||
							    parts[skip + 1] != "other")
								break;
							skip += 2;
						}
						if (consumed_rebind && skip == parts.size())
							return current_allocator;
						break;
					}
					TemplateArgument rebound =
						substitute_template_argument(stored_arguments[0]);
					if (rebound.kind != TemplateArgumentKind::Type)
						break;
					TypePtr rebound_allocator =
						hosted_rebind_allocator_type(current_allocator,
						                            rebound.type);
					if (rebound_allocator.get() == NULL)
						break;
					current_allocator = rebound_allocator;
					consumed_rebind = true;
					part_index += 2;
				}
				if (consumed_rebind)
				{
					TypePtr current = current_allocator;
					for (size_t pi = part_index; pi < parts.size(); ++pi)
					{
						TypePtr owner = current.get() != NULL
							? pa11::strip_cv(current) : TypePtr();
						if (owner.get() == NULL ||
						    owner->kind != pa11::TypeKind::Record ||
						    owner->scope == NULL)
							return TypePtr();
						try
						{
							const_cast<Parser*>(this)->
								complete_template_record(owner);
						}
						catch (const runtime_error&)
						{
						}
						string member_name = parts[pi];
						size_t member_template = member_name.find('<');
						if (member_template != string::npos)
							member_name = member_name.substr(0,
							                                  member_template);
						current = lookup_type_member(owner->scope,
						                             member_name);
						if (current.get() == NULL)
							return TypePtr();
					}
					return current;
				}
			}
			for (size_t i = first_type_part + 1; i + 2 < parts.size(); ++i)
			{
				string member_name = parts[i];
				size_t member_template = member_name.find('<');
				if (member_template != string::npos)
					member_name = member_name.substr(0, member_template);
				if (member_name != "rebind" || parts[i + 1] != "other")
					continue;
				string final_member = parts.back();
				size_t final_template = final_member.find('<');
				if (final_template != string::npos)
					final_member = final_member.substr(0, final_template);
				TypePtr resolved_member =
					hosted_allocator_rebind_member_type(final_member);
				if (resolved_member.get() != NULL)
					return resolved_member;
			}
		}
		if (hosted_compatibility_ &&
		    root_name == "_Policy" &&
		    parts.size() == first_type_part + 2 &&
		    parts[first_type_part + 1] == "__has_load_factor" &&
		    !type->template_arguments.empty())
		{
			TemplateArgument policy =
				template_argument_from_instance_argument(
					type->template_arguments[0]);
			policy = substitute_template_argument(policy);
			if (policy.kind == TemplateArgumentKind::Type)
			{
				TypePtr policy_type = substitute_template_type(policy.type);
				TypePtr policy_record = policy_type.get() != NULL
					? pa11::strip_cv(policy_type) : TypePtr();
				if (policy_record.get() != NULL &&
				    policy_record->kind == pa11::TypeKind::Record &&
				    policy_record->scope != NULL)
				{
					try
					{
						const_cast<Parser*>(this)->
							complete_template_record(policy_record);
					}
					catch (const runtime_error&)
					{
					}
					TypePtr member = lookup_type_member(
						policy_record->scope,
						"__has_load_factor");
					if (member.get() != NULL)
					{
						TypePtr bool_constant =
							hosted_bool_constant_type(true);
						if (bool_constant.get() != NULL)
							return bool_constant;
						return member;
					}
				}
			}
		}
		if (root_template != string::npos)
		{
			vector<TemplateArgument> stored_arguments;
			if (!dependent_typename_template_argument_list(
				    type,
				    template_argument_list_index,
				    stored_arguments))
			{
				if (hosted_compatibility_ &&
				    root_name == "__get_value_type" &&
				    parts.size() > first_type_part + 1 &&
				    parts[first_type_part + 1] == "type")
					return hosted_get_value_type_from_context();
				return TypePtr();
			}
			if (stored_arguments.empty() &&
			    hosted_compatibility_ &&
			    root_name == "__get_value_type" &&
			    parts.size() > first_type_part + 1 &&
			    parts[first_type_part + 1] == "type")
			{
				TypePtr value_type = hosted_get_value_type_from_context();
				if (value_type.get() != NULL)
					return value_type;
			}
			if (!stored_arguments.empty() &&
			    hosted_compatibility_ &&
			    root_name == "__get_value_type" &&
			    parts.size() > first_type_part + 1 &&
			    parts[first_type_part + 1] == "type")
			{
				TemplateArgument node_arg =
					substitute_template_argument(stored_arguments[0]);
				if (node_arg.kind == TemplateArgumentKind::Type)
				{
					TypePtr value_type =
						hash_node_value_type(node_arg.type);
					if (value_type.get() != NULL)
						return value_type;
				}
				TypePtr value_type = hosted_get_value_type_from_context();
				if (value_type.get() != NULL)
					return value_type;
			}
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
			auto resolve_type_suffix =
				[&](TypePtr owner_type, size_t suffix_begin) -> TypePtr {
					TypePtr current = owner_type;
					for (size_t pi = suffix_begin; pi < parts.size(); ++pi)
					{
						TypePtr owner = current.get() != NULL
							? pa11::strip_cv(current) : TypePtr();
						if (owner.get() == NULL ||
						    owner->kind != pa11::TypeKind::Record ||
						    owner->scope == NULL)
							return TypePtr();
						try
						{
							const_cast<Parser*>(this)->
								complete_template_record(owner);
						}
						catch (const runtime_error&)
						{
						}
						string member_name = parts[pi];
						size_t member_template = member_name.find('<');
						if (member_template != string::npos)
							member_name = member_name.substr(0,
							                                  member_template);
						current = lookup_type_member(owner->scope,
						                             member_name);
						if (current.get() == NULL)
							return TypePtr();
					}
					return current;
				};
			if (hosted_compatibility_ &&
			    internal_type_transform_name(root_name) &&
			    parts.size() == first_type_part + 1 &&
			    arguments.size() == 1 &&
			    arguments[0].kind == TemplateArgumentKind::Type &&
			    !template_argument_has_template_parameter(
				    arguments[0],
				    record_template_arguments_))
				return apply_internal_type_transform(root_name,
				                                     arguments[0].type);
			if (hosted_compatibility_ &&
			    root_name == "__iter_category_t" &&
			    parts.size() == first_type_part + 1 &&
			    arguments.size() == 1 &&
			    arguments[0].kind == TemplateArgumentKind::Type &&
			    !template_argument_has_template_parameter(
				    arguments[0],
				    record_template_arguments_))
			{
				TemplateDeclaration* traits =
					const_cast<Parser*>(this)->find_class_template(
						NULL,
						"iterator_traits");
				if (traits != NULL)
				{
					vector<TemplateArgument> trait_args;
					trait_args.push_back(arguments[0]);
					TypePtr traits_type =
						const_cast<Parser*>(this)->
							instantiate_class_template(
								traits,
								trait_args);
					TypePtr traits_record =
						traits_type.get() != NULL
						? pa11::strip_cv(traits_type) : TypePtr();
					if (traits_record.get() != NULL &&
					    traits_record->kind == pa11::TypeKind::Record &&
					    traits_record->scope != NULL)
					{
						try
						{
							const_cast<Parser*>(this)->
								complete_template_record(traits_record);
						}
						catch (const runtime_error&)
						{
						}
						TypePtr category = lookup_type_member(
							traits_record->scope,
							"iterator_category");
						if (category.get() != NULL)
							return category;
					}
				}
			}
				if (hosted_compatibility_ &&
				    root_name == "__enable_if_t" &&
				    !arguments.empty() &&
				    arguments[0].kind == TemplateArgumentKind::Value &&
				    !arguments[0].dependent)
				{
					if (arguments[0].value == 0)
						return TypePtr();
					TypePtr enabled_type = arguments.size() >= 2 &&
					                       arguments[1].kind ==
						                       TemplateArgumentKind::Type
						? arguments[1].type
						: pa11::make_fundamental(FT_VOID);
					if (parts.size() == first_type_part + 1)
						return enabled_type;
					TypePtr resolved = resolve_type_suffix(enabled_type,
					                                       first_type_part + 1);
					if (resolved.get() != NULL)
						return resolved;
				}
					if (hosted_compatibility_ &&
				    root_name == "enable_if" &&
					    parts.size() > first_type_part + 1 &&
					    parts[first_type_part + 1] == "type" &&
				    !arguments.empty() &&
				    arguments[0].kind == TemplateArgumentKind::Value &&
				    !arguments[0].dependent)
				{
					if (arguments[0].value == 0)
						return TypePtr();
					TypePtr enabled_type = arguments.size() >= 2 &&
					                       arguments[1].kind ==
						                       TemplateArgumentKind::Type
						? arguments[1].type
						: pa11::make_fundamental(FT_VOID);
					if (parts.size() == first_type_part + 2)
						return enabled_type;
					TypePtr resolved = resolve_type_suffix(enabled_type,
					                                       first_type_part + 2);
						if (resolved.get() != NULL)
							return resolved;
					}
				if (root_name == "conditional" &&
				    parts.size() > first_type_part + 1 &&
				    parts[first_type_part + 1] == "type" &&
				    arguments.size() >= 3 &&
				    arguments[0].kind == TemplateArgumentKind::Value &&
				    !arguments[0].dependent &&
				    arguments[1].kind == TemplateArgumentKind::Type &&
				    arguments[2].kind == TemplateArgumentKind::Type)
				{
					TypePtr selected_type = arguments[0].value != 0
						? arguments[1].type : arguments[2].type;
					if (parts.size() == first_type_part + 2)
						return selected_type;
					TypePtr resolved = resolve_type_suffix(selected_type,
					                                       first_type_part + 2);
					if (resolved.get() != NULL)
						return resolved;
				}
				if (hosted_compatibility_ &&
				    root_name == "__invoke_result" &&
				    parts.size() > first_type_part + 1 &&
			    parts[first_type_part + 1] == "type")
			{
				vector<TypePtr> call_types;
				bool type_args = true;
				for (size_t ai = 0; ai < arguments.size(); ++ai)
				{
					if (arguments[ai].kind != TemplateArgumentKind::Type)
					{
						type_args = false;
						break;
					}
					call_types.push_back(arguments[ai].type);
				}
				if (type_args)
				{
					TypePtr result = hosted_call_result_type(call_types);
					if (result.get() != NULL)
						return result;
					return TypePtr();
				}
			}
			if (hosted_compatibility_ &&
			    root_name == "__is_invocable_impl" &&
			    parts.size() > first_type_part + 1 &&
			    parts[first_type_part + 1] == "type" &&
			    arguments.size() >= 2 &&
			    arguments[0].kind == TemplateArgumentKind::Type &&
			    arguments[1].kind == TemplateArgumentKind::Type)
			{
				vector<TypePtr> trait_types;
				trait_types.push_back(arguments[1].type);
				vector<TypePtr> call_types;
				if (hosted_invoke_result_call_types(arguments[0].type,
				                                    call_types))
				{
					bool dependent_trait =
						type_structurally_dependent(arguments[1].type);
					for (size_t ci = 0; ci < call_types.size(); ++ci)
						if (type_structurally_dependent(call_types[ci]))
							dependent_trait = true;
					if (!dependent_trait)
					{
						trait_types.insert(trait_types.end(),
						                   call_types.begin(),
						                   call_types.end());
						TypePtr bool_constant =
							hosted_bool_constant_type(
								const_cast<Parser*>(this)->
									is_invocable_r_type_trait(
										trait_types,
										false));
						if (bool_constant.get() != NULL)
							return bool_constant;
					}
				}
			}
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
		if (hosted_compatibility_ &&
		    parts.size() > first_type_part + 1 &&
		    parts[first_type_part + 1] == "type")
		{
			TypePtr result = hosted_invoke_result_type(resolved);
			if (result.get() != NULL)
				return result;
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
			{
				if (hosted_compatibility_ &&
				    member_name == "rebind" &&
				    i + 2 < parts.size() &&
				    parts[i + 1] == "other" &&
				    parts[i + 2] == "value_type")
					return hosted_allocator_rebind_value_type();
				if (hosted_compatibility_ &&
				    member_name == "rebind" &&
				    i + 2 < parts.size() &&
				    parts[i + 1] == "other")
				{
					TypePtr resolved_member =
						hosted_allocator_rebind_member_type(parts[i + 2]);
					if (resolved_member.get() != NULL)
						return resolved_member;
				}
				return TypePtr();
			}
			if (hosted_compatibility_ &&
			    member_name == "rebind" &&
			    i + 1 < parts.size() &&
			    parts[i + 1] == "other" &&
			    !stored_arguments.empty())
			{
				TemplateArgument rebound =
					substitute_template_argument(stored_arguments[0]);
				if (rebound.kind == TemplateArgumentKind::Type)
				{
					TypePtr rebound_allocator =
						hosted_rebind_allocator_type(owner,
						                            rebound.type);
					if (rebound_allocator.get() != NULL)
					{
						if (i + 2 >= parts.size())
							return rebound_allocator;
						resolved = rebound_allocator;
						resolved_type_scope = NULL;
						++i;
						continue;
					}
				}
			}
			if (hosted_compatibility_ &&
			    member_name == "rebind" &&
			    i + 2 < parts.size() &&
			    parts[i + 1] == "other" &&
			    parts[i + 2] == "value_type" &&
			    !stored_arguments.empty())
			{
				TemplateArgument rebound =
					substitute_template_argument(stored_arguments[0]);
				if (rebound.kind == TemplateArgumentKind::Type)
					return rebound.type;
			}
			if (hosted_compatibility_ &&
			    member_name == "rebind" &&
			    i + 2 < parts.size() &&
			    parts[i + 1] == "other")
			{
				TypePtr resolved_member =
					hosted_allocator_rebind_member_type(parts[i + 2]);
				if (resolved_member.get() != NULL)
					return resolved_member;
			}
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
}  // namespace internal
}  // namespace pa12
