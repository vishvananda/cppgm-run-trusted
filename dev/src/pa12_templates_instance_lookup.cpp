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

bool Parser::resolve_template_name_spelling(const string& spelling,
                                            Scope*& qualifier,
                                            string& name)
{
	qualifier = NULL;
	name = spelling;
	if (spelling.find("::") == string::npos)
		return true;
	vector<string> parts;
	size_t begin = 0;
	while (begin < spelling.size())
	{
		size_t pos = spelling.find("::", begin);
		parts.push_back(spelling.substr(begin, pos - begin));
		if (pos == string::npos)
			break;
		begin = pos + 2;
	}
	if (parts.size() < 2)
		return false;
	Scope* scope = global_scope();
	for (size_t i = 0; i + 1 < parts.size(); ++i)
	{
		vector<Binding*> found =
			lookup_qualified_set(scope,
			                     parts[i],
			                     pa11::LOOKUP_QUALIFIER);
		if (found.empty())
			return false;
		scope = resolve_qualifier(found[0]);
		if (scope == NULL)
			return false;
	}
	qualifier = scope;
	name = parts.back();
	return true;
}

TemplateDeclaration* Parser::find_class_template(Scope* scope,
                                                 const string& name)
{
	if (scope != NULL)
	{
		map<Scope*, map<string, TemplateDeclaration*> >::iterator sit =
			class_templates_.find(scope);
		if (sit != class_templates_.end())
		{
				map<string, TemplateDeclaration*>::iterator it =
					sit->second.find(name);
					if (it != sit->second.end())
					{
						TemplateDeclaration* found = it->second;
						TypePtr record = pa11::record_type_for_scope(scope);
						record = record.get() != NULL
							? pa11::strip_cv(record) : TypePtr();
						map<const void*, TemplateDeclaration*>::iterator outer =
							record.get() != NULL
							? record_template_declarations_.find(record.get())
							: record_template_declarations_.end();
						TemplateDeclaration* member_definition = NULL;
						if (outer != record_template_declarations_.end())
						{
							map<pair<TemplateDeclaration*, string>,
							    TemplateDeclaration*>::iterator mit =
								member_class_templates_.find(
									make_pair(outer->second, name));
							member_definition =
								mit != member_class_templates_.end()
								? mit->second : NULL;
							if (member_definition == NULL ||
							    !member_definition->has_definition)
							{
								for (map<pair<TemplateDeclaration*, string>,
								         TemplateDeclaration*>::iterator mt =
									     member_class_templates_.begin();
								     mt != member_class_templates_.end();
							     ++mt)
							{
								TemplateDeclaration* candidate_outer =
									mt->first.first;
								if (mt->first.second == name &&
									    candidate_outer != NULL &&
									    outer->second != NULL &&
									    candidate_outer->name ==
										    outer->second->name &&
									    candidate_outer->owner ==
										    outer->second->owner)
									{
										if (member_definition == NULL ||
										    (mt->second != NULL &&
										     mt->second->has_definition &&
										     !member_definition->has_definition))
											member_definition = mt->second;
										if (member_definition != NULL &&
										    member_definition->has_definition)
											break;
									}
								}
							}
							if (member_definition == NULL ||
							    !member_definition->has_definition)
							{
								map<Scope*, map<string, TemplateDeclaration*> >::
									iterator ps =
									class_templates_.find(outer->second->owner);
								if (ps != class_templates_.end())
								{
									map<string, TemplateDeclaration*>::iterator pt =
										ps->second.find(name);
									if (pt != ps->second.end() &&
									    pt->second != NULL &&
									    pt->second->has_definition)
										member_definition = pt->second;
								}
							}
						}
					if (member_definition != NULL &&
					    member_definition != found &&
					    member_definition->has_definition &&
					    !found->has_definition)
					{
						unique_ptr<TemplateDeclaration> holder(
							new TemplateDeclaration(*member_definition));
						TemplateDeclaration* rebound = holder.get();
						rebound->owner = scope;
						rebound->lexical_scope = scope;
						rebound->class_specializations.clear();
						rebound->completing_specializations.clear();
						it->second = rebound;
						template_declarations_.push_back(
							std::move(holder));
						found = rebound;
					}
					if (found != NULL && found->owner != scope)
					{
						if (record.get() != NULL &&
						    record->kind == pa11::TypeKind::Record)
						{
							unique_ptr<TemplateDeclaration> holder(
								new TemplateDeclaration(*found));
							TemplateDeclaration* rebound = holder.get();
							rebound->owner = scope;
							rebound->lexical_scope = scope;
							rebound->class_specializations.clear();
							rebound->completing_specializations.clear();
							it->second = rebound;
							template_declarations_.push_back(
								std::move(holder));
							found = rebound;
						}
					}
					if (found != NULL &&
					    found->class_specialization_declarations.empty())
					{
						TypePtr record = pa11::record_type_for_scope(scope);
						record = record.get() != NULL
							? pa11::strip_cv(record) : TypePtr();
						if (record.get() != NULL &&
						    record->kind == pa11::TypeKind::Record)
							for (map<Scope*, map<string, TemplateDeclaration*> >::
								     iterator os = class_templates_.begin();
							     os != class_templates_.end();
							     ++os)
							{
								map<string, TemplateDeclaration*>::iterator oi =
									os->second.find(name);
								if (oi == os->second.end() ||
								    oi->second == NULL ||
								    oi->second == found ||
								    oi->second->class_specialization_declarations.empty())
									continue;
								found->class_specialization_declarations.insert(
									found->class_specialization_declarations.end(),
									oi->second->class_specialization_declarations.begin(),
									oi->second->class_specialization_declarations.end());
							}
					}
					return found;
				}
		}
			TypePtr record = pa11::record_type_for_scope(scope);
			TypePtr bare_record = record.get() != NULL
				? pa11::strip_cv(record) : TypePtr();
			map<const void*, TemplateDeclaration*>::iterator outer =
				bare_record.get() != NULL
				? record_template_declarations_.find(bare_record.get())
				: record_template_declarations_.end();
			if (outer != record_template_declarations_.end())
			{
				map<pair<TemplateDeclaration*, string>,
				    TemplateDeclaration*>::iterator mit =
					member_class_templates_.find(make_pair(outer->second, name));
				TemplateDeclaration* found =
					mit != member_class_templates_.end() ? mit->second : NULL;
				if (found == NULL)
				{
					for (map<pair<TemplateDeclaration*, string>,
					         TemplateDeclaration*>::iterator it =
						     member_class_templates_.begin();
					     it != member_class_templates_.end();
					     ++it)
					{
						TemplateDeclaration* candidate_outer = it->first.first;
						if (it->first.second == name &&
						    candidate_outer != NULL &&
						    outer->second != NULL &&
						    candidate_outer->name == outer->second->name &&
						    candidate_outer->owner == outer->second->owner)
						{
							found = it->second;
							break;
						}
					}
				}
				if (found != NULL)
				{
					if (found->owner != scope)
					{
						unique_ptr<TemplateDeclaration> holder(
							new TemplateDeclaration(*found));
						TemplateDeclaration* rebound = holder.get();
						rebound->owner = scope;
						rebound->lexical_scope = scope;
						rebound->class_specializations.clear();
						rebound->completing_specializations.clear();
						class_templates_[scope][name] = rebound;
						template_declarations_.push_back(std::move(holder));
						return rebound;
					}
					return found;
				}
			}
		for (size_t i = 0; i < scope->using_directives.size(); ++i)
		{
			TemplateDeclaration* found =
				find_class_template(scope->using_directives[i], name);
			if (found != NULL)
				return found;
		}
		TypePtr base = record.get() != NULL && record->base.get() != NULL
			? pa11::strip_cv(record->base) : TypePtr();
		if (base.get() != NULL &&
		    base->kind == pa11::TypeKind::Record &&
		    base->scope != NULL &&
		    record_dependent_base_lookup_skips_.count(
			    pa11::strip_cv(record).get()) == 0)
		{
			TemplateDeclaration* found =
				find_class_template(base->scope, name);
			if (found != NULL)
				return found;
		}
		return NULL;
	}
	for (Scope* cur = current_scope(); cur != NULL; cur = cur->parent)
	{
		TemplateDeclaration* found = find_class_template(cur, name);
		if (found != NULL)
			return found;
	}
	if (global_scope() != current_scope())
	{
		TemplateDeclaration* found = find_class_template(global_scope(), name);
		if (found != NULL)
			return found;
	}
	return NULL;
}

TemplateDeclaration* Parser::find_alias_template(Scope* scope,
                                                 const string& name)
{
	if (scope != NULL)
	{
		map<Scope*, map<string, TemplateDeclaration*> >::iterator sit =
			alias_templates_.find(scope);
		if (sit != alias_templates_.end())
		{
			map<string, TemplateDeclaration*>::iterator it =
				sit->second.find(name);
			if (it != sit->second.end())
			{
				TemplateDeclaration* found = it->second;
				if (found != NULL && found->owner != scope)
				{
					TypePtr record = pa11::record_type_for_scope(scope);
					record = record.get() != NULL
						? pa11::strip_cv(record) : TypePtr();
					if (record.get() != NULL &&
					    record->kind == pa11::TypeKind::Record)
					{
						unique_ptr<TemplateDeclaration> holder(
							new TemplateDeclaration(*found));
						TemplateDeclaration* rebound = holder.get();
						rebound->owner = scope;
						rebound->lexical_scope = scope;
						rebound->class_specializations.clear();
						rebound->function_specializations.clear();
						rebound->completing_specializations.clear();
						rebound->emitted_variable_specializations.clear();
						it->second = rebound;
						template_declarations_.push_back(std::move(holder));
						found = rebound;
					}
				}
				return found;
			}
		}
		for (size_t i = 0; i < scope->using_directives.size(); ++i)
		{
			TemplateDeclaration* found =
				find_alias_template(scope->using_directives[i], name);
			if (found != NULL)
				return found;
		}
		TypePtr record = pa11::record_type_for_scope(scope);
		TypePtr base = record.get() != NULL && record->base.get() != NULL
			? pa11::strip_cv(record->base) : TypePtr();
		if (base.get() != NULL &&
		    base->kind == pa11::TypeKind::Record &&
		    base->scope != NULL &&
		    record_dependent_base_lookup_skips_.count(
			    pa11::strip_cv(record).get()) == 0)
		{
			TemplateDeclaration* found =
				find_alias_template(base->scope, name);
			if (found != NULL)
				return found;
		}
		return NULL;
	}
	for (Scope* cur = current_scope(); cur != NULL; cur = cur->parent)
	{
		TemplateDeclaration* found = find_alias_template(cur, name);
		if (found != NULL)
			return found;
	}
	return NULL;
}

TypePtr Parser::instantiate_alias_template(
	TemplateDeclaration* declaration,
	const vector<TemplateArgument>& arguments)
{
	vector<TemplateArgument> full_args =
		complete_template_arguments(declaration, arguments);
	size_t save_pos = pos_;
	vector<Token> save_tokens = tokens_;
	vector<Scope*> save_scopes = scopes_;
	vector<map<string, TypePtr> > save_subst = template_type_substitutions_;
	vector<map<string, TemplateArgument> > save_value_subst =
		template_value_substitutions_;
	vector<set<string> > save_pack_subst = template_type_parameter_packs_;
	map<string, TypePtr> subst;
	map<string, TemplateArgument> value_subst;
	set<string> pack_subst;
	map<string, TypePtr> owner_subst;
	map<string, TemplateArgument> owner_value_subst;
	bool dependent_alias_arguments = false;
	TypePtr owner_record = pa11::record_type_for_scope(declaration->owner);
	owner_record = owner_record.get() != NULL
		? pa11::strip_cv(owner_record) : TypePtr();
	map<const void*, TemplateDeclaration*>::const_iterator owner_decl =
		owner_record.get() != NULL
		? record_template_declarations_.find(owner_record.get())
		: record_template_declarations_.end();
	map<const void*, vector<TemplateArgument> >::const_iterator owner_args =
		owner_record.get() != NULL
		? record_template_arguments_.find(owner_record.get())
		: record_template_arguments_.end();
	if (owner_decl != record_template_declarations_.end() &&
	    owner_args != record_template_arguments_.end())
	{
		for (size_t i = 0;
		     i < owner_args->second.size() &&
		     i < owner_decl->second->parameters.size();
		     ++i)
			if (!owner_decl->second->parameters[i].name.empty())
			{
				const string& param_name =
					owner_decl->second->parameters[i].name;
				if (owner_decl->second->parameters[i].kind ==
				    TemplateParameterKind::Type)
				{
					if (owner_decl->second->parameters[i].is_pack)
					{
						owner_subst[param_name] =
							pa11::make_template_parameter_type(
								param_name);
						owner_value_subst[param_name] =
							substitute_template_argument(
								owner_args->second[i]);
					}
					else
						owner_subst[param_name] =
							substitute_template_type(
								owner_args->second[i].type);
				}
				else
					owner_value_subst[param_name] =
						substitute_template_argument(
							owner_args->second[i]);
		}
	}
	if (!full_args.empty())
	{
		template_type_substitutions_.insert(
			template_type_substitutions_.end(),
			declaration->outer_type_substitutions.begin(),
			declaration->outer_type_substitutions.end());
		template_value_substitutions_.insert(
			template_value_substitutions_.end(),
			declaration->outer_value_substitutions.begin(),
			declaration->outer_value_substitutions.end());
		if (!owner_subst.empty() || !owner_value_subst.empty())
		{
			template_type_substitutions_.push_back(owner_subst);
			template_value_substitutions_.push_back(owner_value_subst);
		}
		try
		{
			for (size_t i = 0; i < full_args.size(); ++i)
				full_args[i] = substitute_template_argument(full_args[i]);
		}
		catch (...)
		{
			template_type_substitutions_ = save_subst;
			template_value_substitutions_ = save_value_subst;
			throw;
		}
		template_type_substitutions_ = save_subst;
		template_value_substitutions_ = save_value_subst;
		dependent_alias_arguments = false;
		for (size_t i = 0; i < full_args.size(); ++i)
			if ((full_args[i].kind == TemplateArgumentKind::Value &&
			     full_args[i].dependent) ||
			    template_argument_has_template_parameter(
				    full_args[i],
				    record_template_arguments_))
				dependent_alias_arguments = true;
	}
	if (declaration->name == "conditional_t" &&
	    full_args.size() == 3 &&
	    full_args[0].kind == TemplateArgumentKind::Value &&
	    !full_args[0].dependent &&
	    full_args[1].kind == TemplateArgumentKind::Type &&
	    full_args[2].kind == TemplateArgumentKind::Type)
		return full_args[0].value != 0 ? full_args[1].type
		                               : full_args[2].type;
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
					pack_subst.insert(declaration->parameters[i].name);
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
	if (!owner_subst.empty() || !owner_value_subst.empty())
	{
		template_type_substitutions_.push_back(owner_subst);
		template_value_substitutions_.push_back(owner_value_subst);
	}
	template_type_substitutions_.push_back(subst);
	template_value_substitutions_.push_back(value_subst);
	template_type_parameter_packs_.push_back(pack_subst);
	scopes_.clear();
	scopes_.push_back(declaration->lexical_scope != NULL
	                  ? declaration->lexical_scope
	                  : declaration->owner);
	tokens_ = declaration_tokens_;
	pos_ = declaration->decl_begin;
	TypePtr type;
	try
	{
		expect(KW_USING);
		consume_identifier();
		expect(OP_ASS);
		type = parse_type_id();
		expect(OP_SEMICOLON);
		if (type.get() != NULL &&
		    type->is_dependent_typename &&
		    type->template_arguments.empty() &&
		    type->dependent_typename_template_argument_lists.empty())
		{
			type->template_primary_name = declaration->name;
			type->template_arguments = template_instance_arguments(full_args);
		}
		if (type.get() != NULL &&
		    type->is_dependent_typename &&
		    dependent_alias_arguments)
		{
			template_type_substitutions_ = save_subst;
			template_value_substitutions_ = save_value_subst;
			template_type_parameter_packs_ = save_pack_subst;
			tokens_ = save_tokens;
			scopes_ = save_scopes;
			pos_ = save_pos;
			return type;
		}
		if (type.get() != NULL)
			type = substitute_template_type(type);
		if (parsing_base_specifier_ &&
		    !active_class_instantiations_.empty() &&
		    type.get() == active_class_instantiations_.back().type.get())
		{
			TypePtr deferred = pa11::make_dependent_typename_type(
				declaration->name,
				false,
				true,
				false);
			deferred->template_primary_name = declaration->name;
			deferred->template_arguments =
				template_instance_arguments(full_args);
			return deferred;
		}
	}
			catch (const runtime_error&)
			{
				template_type_substitutions_ = save_subst;
		template_value_substitutions_ = save_value_subst;
		template_type_parameter_packs_ = save_pack_subst;
		tokens_ = save_tokens;
		scopes_ = save_scopes;
		pos_ = save_pos;
		if (dependent_alias_arguments &&
		    type.get() != NULL &&
		    type->is_dependent_typename)
			return type;
		if (dependent_alias_arguments)
		{
			TypePtr out = pa11::make_dependent_typename_type(
				declaration->name,
				false,
				true,
				false);
			out->template_primary_name = declaration->name;
			out->template_arguments = template_instance_arguments(full_args);
			return out;
		}
		throw;
	}
			catch (...)
			{
				template_type_substitutions_ = save_subst;
		template_value_substitutions_ = save_value_subst;
		template_type_parameter_packs_ = save_pack_subst;
		tokens_ = save_tokens;
		scopes_ = save_scopes;
		pos_ = save_pos;
		if (dependent_alias_arguments &&
		    type.get() != NULL &&
		    type->is_dependent_typename)
			return type;
		if (dependent_alias_arguments)
		{
			TypePtr out = pa11::make_dependent_typename_type(
				declaration->name,
				false,
				true,
				false);
			out->template_primary_name = declaration->name;
			out->template_arguments = template_instance_arguments(full_args);
			return out;
		}
		throw;
	}
	template_type_substitutions_ = save_subst;
	template_value_substitutions_ = save_value_subst;
	template_type_parameter_packs_ = save_pack_subst;
	tokens_ = save_tokens;
	scopes_ = save_scopes;
	pos_ = save_pos;
	return type;
}

}  // namespace internal
}  // namespace pa12
