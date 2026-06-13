#include "pa12_expr_semantics_support.h"
#include "pa12_templates_function_support.h"
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
static bool member_parameter_names_have_non_this(const vector<string>& names)
{
	for (size_t i = 0; i < names.size(); ++i)
		if (!names[i].empty() && names[i] != "this")
			return true;
	return false;
}

pa11::TemplateInstanceArgument remap_template_parameter_names(
	const pa11::TemplateInstanceArgument& argument,
	const map<string, string>& names);

TypePtr remap_template_parameter_names(TypePtr type,
                                       const map<string, string>& names)
{
	if (type.get() == NULL || names.empty())
		return type;
	TypePtr out(new pa11::Type(*type));
	map<string, string>::const_iterator found = names.find(out->name);
	if ((out->kind == pa11::TypeKind::TemplateParameter ||
	     out->kind == pa11::TypeKind::TemplateTemplateParameter) &&
	    found != names.end())
		out->name = found->second;
	found = names.find(out->template_primary_name);
	if (found != names.end())
		out->template_primary_name = found->second;
	if (out->base.get() != NULL)
		out->base = remap_template_parameter_names(out->base, names);
	if (out->member_class.get() != NULL)
		out->member_class =
			remap_template_parameter_names(out->member_class, names);
	for (size_t i = 0; i < out->parameters.size(); ++i)
		out->parameters[i] =
			remap_template_parameter_names(out->parameters[i], names);
	for (size_t i = 0; i < out->template_arguments.size(); ++i)
		out->template_arguments[i] =
			remap_template_parameter_names(out->template_arguments[i],
			                               names);
	for (size_t i = 0;
	     i < out->dependent_typename_template_argument_lists.size();
	     ++i)
		for (size_t j = 0;
		     j < out->dependent_typename_template_argument_lists[i].size();
		     ++j)
			out->dependent_typename_template_argument_lists[i][j] =
				remap_template_parameter_names(
					out->dependent_typename_template_argument_lists[i][j],
					names);
	return out;
}

pa11::TemplateInstanceArgument remap_template_parameter_names(
	const pa11::TemplateInstanceArgument& argument,
	const map<string, string>& names)
{
	if (names.empty())
		return argument;
	pa11::TemplateInstanceArgument out = argument;
	if (out.kind == pa11::TemplateInstanceArgumentKind::Type)
		out.type = remap_template_parameter_names(out.type, names);
	else if (out.kind == pa11::TemplateInstanceArgumentKind::Value)
	{
		out.type = remap_template_parameter_names(out.type, names);
		map<string, string>::const_iterator found =
			names.find(out.value_name);
		if (found != names.end())
			out.value_name = found->second;
		for (size_t i = 0; i < out.value_owner_template_arguments.size(); ++i)
			out.value_owner_template_arguments[i] =
				remap_template_parameter_names(
					out.value_owner_template_arguments[i],
					names);
	}
	else if (out.kind == pa11::TemplateInstanceArgumentKind::Template)
	{
		map<string, string>::const_iterator found =
			names.find(out.template_name);
		if (found != names.end())
			out.template_name = found->second;
	}
	else
	{
		for (size_t i = 0; i < out.pack.size(); ++i)
			out.pack[i] = remap_template_parameter_names(out.pack[i],
			                                             names);
	}
	return out;
}

map<string, string> template_parameter_name_map(
	const vector<TemplateParameterInfo>& from,
	const vector<TemplateParameterInfo>& to)
{
	map<string, string> names;
	size_t count = min(from.size(), to.size());
	for (size_t i = 0; i < count; ++i)
		if (!from[i].name.empty() &&
		    !to[i].name.empty() &&
		    from[i].name != to[i].name)
			names[from[i].name] = to[i].name;
	return names;
}

void Parser::add_member_function_template(
	vector<TemplateDeclaration*>& members,
	TemplateDeclaration* declaration)
{
	if (find(members.begin(), members.end(), declaration) != members.end())
		return;
	members.push_back(declaration);
	++member_function_template_generation_;
}

void Parser::instantiate_member_function_templates(TypePtr type,
                                                   bool object_root)
{
	TypePtr bare = pa11::strip_cv(type);
	if (bare->kind != pa11::TypeKind::Record)
		return;
	size_t save_pos = pos_;
	vector<Scope*> save_scopes = scopes_;
	map<const void*, TemplateDeclaration*>::iterator outer =
		record_template_declarations_.find(bare.get());
	TemplateDeclaration* owner_declaration = outer != record_template_declarations_.end()
		? outer->second : NULL;
	map<const void*, vector<TemplateArgument> >::iterator args_it =
		record_template_arguments_.find(bare.get());
		vector<TemplateArgument> owner_arguments;
		if (args_it != record_template_arguments_.end())
			owner_arguments = args_it->second;
		else if (!bare->template_arguments.empty())
			for (size_t i = 0; i < bare->template_arguments.size(); ++i)
				owner_arguments.push_back(
					template_argument_from_instance_argument(
						bare->template_arguments[i]));
		vector<TemplateArgument> primary_owner_arguments;
		if (!bare->template_arguments.empty())
			for (size_t i = 0; i < bare->template_arguments.size(); ++i)
				primary_owner_arguments.push_back(
					template_argument_from_instance_argument(
						bare->template_arguments[i]));
		if (primary_owner_arguments.empty())
			primary_owner_arguments = owner_arguments;
		bool owner_arguments_still_dependent = false;
		for (size_t i = 0; i < owner_arguments.size(); ++i)
			if (template_argument_has_template_parameter(
				    owner_arguments[i],
				    record_template_arguments_))
				owner_arguments_still_dependent = true;
		if (owner_arguments_still_dependent &&
		    (owner_declaration == NULL ||
		     !owner_declaration->class_specialization) &&
		    !primary_owner_arguments.empty())
			owner_arguments = primary_owner_arguments;
	if (owner_declaration == NULL &&
	    bare->is_template_specialization &&
	    !bare->template_primary_name.empty())
	{
		owner_declaration = find_class_template(NULL,
		                                        bare->template_primary_name);
		if (owner_declaration != NULL)
		{
			for (size_t i = 0; i < bare->template_arguments.size(); ++i)
				owner_arguments.push_back(
					template_argument_from_instance_argument(
						bare->template_arguments[i]));
			record_template_declarations_[bare.get()] = owner_declaration;
			record_template_arguments_[bare.get()] = owner_arguments;
		}
	}
	TemplateDeclaration* primary_owner_declaration = owner_declaration;
	if (owner_declaration != NULL &&
	    owner_declaration->class_specialization &&
	    bare->is_template_specialization &&
	    !bare->template_primary_name.empty())
	{
		TemplateDeclaration* primary =
			find_class_template(owner_declaration->owner,
			                    bare->template_primary_name);
		if (primary != NULL)
			primary_owner_declaration = primary;
	}
		if (owner_declaration == NULL ||
		    (owner_arguments.empty() && !owner_declaration->parameters.empty()))
			return;
	pair<const void*, bool> cache_key(bare.get(), object_root);
	map<pair<const void*, bool>, size_t>::iterator completed =
		completed_member_function_template_records_.find(cache_key);
	if ((completed != completed_member_function_template_records_.end() &&
	     completed->second == member_function_template_generation_) ||
	    active_member_function_template_records_.count(cache_key) != 0)
		return;
	active_member_function_template_records_.insert(cache_key);
	struct ActiveInstantiationGuard
	{
		set<pair<const void*, bool> >& active;
		pair<const void*, bool> key;
		ActiveInstantiationGuard(set<pair<const void*, bool> >& active_records,
		                         pair<const void*, bool> active_key)
			: active(active_records), key(active_key)
		{
		}
		~ActiveInstantiationGuard()
		{
			active.erase(key);
		}
	} active_guard(active_member_function_template_records_, cache_key);
	auto make_concrete_outer_substitutions =
		[&](TemplateDeclaration* declaration,
		    const map<string, TypePtr>& owner_type_subst,
		    const map<string, TemplateArgument>& owner_value_subst,
		    vector<map<string, TypePtr> >& type_substitutions,
		    vector<map<string, TemplateArgument> >& value_substitutions) {
			type_substitutions.clear();
			value_substitutions.clear();
			map<string, TypePtr> renamed_types;
			map<string, TemplateArgument> renamed_values;
			for (size_t p = declaration->decl_begin;
			     p + 1 < declaration->decl_end;
			     ++p)
			{
				if (tokens_[p].kind != posttoken::TokenKind::Identifier ||
				    tokens_[p].source != owner_declaration->name ||
				    tokens_[p + 1].kind != posttoken::TokenKind::Simple ||
				    tokens_[p + 1].type != OP_LT)
					continue;
				size_t after_args = p + 1;
				int angle = 0;
				int paren = 0;
				int square = 0;
				int brace = 0;
				while (after_args < declaration->decl_end)
				{
					const Token& tok = tokens_[after_args];
					if (tok.kind == posttoken::TokenKind::Simple)
					{
						if (tok.type == OP_LPAREN)
							++paren;
						else if (tok.type == OP_RPAREN && paren > 0)
							--paren;
						else if (tok.type == OP_LSQUARE)
							++square;
						else if (tok.type == OP_RSQUARE && square > 0)
							--square;
						else if (tok.type == OP_LBRACE)
							++brace;
						else if (tok.type == OP_RBRACE && brace > 0)
							--brace;
						else if (paren == 0 && square == 0 && brace == 0)
						{
							if (tok.type == OP_LT)
								++angle;
							else if (tok.type == OP_GT)
							{
								--angle;
								if (angle == 0)
								{
									++after_args;
									break;
								}
							}
						}
					}
					++after_args;
				}
				if (after_args >= declaration->decl_end ||
				    tokens_[after_args].kind != posttoken::TokenKind::Simple ||
				    tokens_[after_args].type != OP_COLON2)
					continue;
				vector<TemplateArgument> pattern_args;
				size_t save_pos = pos_;
				vector<map<string, TypePtr> > save_subst =
					template_type_substitutions_;
				vector<map<string, TemplateArgument> > save_value_subst =
					template_value_substitutions_;
				try
				{
					template_type_substitutions_.insert(
						template_type_substitutions_.end(),
						declaration->outer_type_substitutions.begin(),
						declaration->outer_type_substitutions.end());
					template_value_substitutions_.insert(
						template_value_substitutions_.end(),
						declaration->outer_value_substitutions.begin(),
						declaration->outer_value_substitutions.end());
					pos_ = p + 1;
					parse_template_argument_list(pattern_args);
				}
				catch (const exception&)
				{
					pos_ = save_pos;
					template_type_substitutions_ = save_subst;
					template_value_substitutions_ = save_value_subst;
					continue;
				}
				pos_ = save_pos;
				template_type_substitutions_ = save_subst;
				template_value_substitutions_ = save_value_subst;
				for (size_t a = 0;
				     a < pattern_args.size() &&
				     a < owner_arguments.size();
				     ++a)
				{
					const TemplateArgument& pattern = pattern_args[a];
					const TemplateArgument& actual = owner_arguments[a];
					string pack_name;
					if (pack_argument_parameter_name(pattern, pack_name))
					{
						renamed_types[pack_name] =
							pa11::make_template_parameter_type(pack_name);
						renamed_values[pack_name] = actual;
						continue;
					}
					if (pattern.kind == TemplateArgumentKind::Type)
					{
						TypePtr pattern_type =
							pa11::strip_cv(pattern.type);
						if (pattern_type.get() != NULL &&
						    pattern_type->kind ==
							    pa11::TypeKind::TemplateParameter &&
						    actual.kind == TemplateArgumentKind::Type)
							renamed_types[pattern_type->name] =
								actual.type;
					}
					else if (pattern.kind == TemplateArgumentKind::Value &&
					         pattern.dependent &&
					         !pattern.value_name.empty())
						renamed_values[pattern.value_name] = actual;
					else if (pattern.kind == TemplateArgumentKind::Template &&
					         !pattern.value_name.empty())
						renamed_values[pattern.value_name] = actual;
				}
				break;
			}
			type_substitutions.push_back(owner_type_subst);
			value_substitutions.push_back(owner_value_subst);
			if (!renamed_types.empty())
				type_substitutions.push_back(renamed_types);
			if (!renamed_values.empty())
				value_substitutions.push_back(renamed_values);
		};
		for (map<pair<TemplateDeclaration*, string>,
		         vector<TemplateDeclaration*> >::iterator it =
			     member_function_templates_.begin();
		     it != member_function_templates_.end();
		     ++it)
		{
			if (it->first.first != owner_declaration &&
			    it->first.first != primary_owner_declaration)
				continue;
			bool have_matching_member_class_specialization =
				member_template_set_has_class_specialization(
					this,
					primary_owner_declaration,
					it->second,
					primary_owner_arguments,
					record_template_arguments_);
			for (size_t i = 0; i < it->second.size(); ++i)
			{
				TemplateDeclaration* declaration = it->second[i];
				if (!declaration->class_specialization &&
				    have_matching_member_class_specialization)
					continue;
				bool matching_owner_definition =
					member_template_definition_matches_owner(
						this,
						it->first.first,
						owner_declaration,
						primary_owner_declaration,
						declaration,
						primary_owner_arguments,
						record_template_arguments_);
				if (!matching_owner_definition)
					continue;
				bool dependent_qualified_conversion_definition =
				declaration->name == "operator " &&
				declaration->has_definition &&
					(!declaration->outer_type_substitutions.empty() ||
					 !declaration->outer_value_substitutions.empty());
			bool dependent_qualified_member_definition =
				declaration->has_definition &&
				declaration->class_template_member &&
				declaration->generic_function_type.get() != NULL &&
				declaration->generic_function_type->kind ==
					pa11::TypeKind::Function &&
				declaration->generic_function_type->parameters.empty();
			bool substituted_class_template_member_definition =
				declaration->has_definition &&
				declaration->class_template_member &&
				(!declaration->outer_type_substitutions.empty() ||
				 !declaration->outer_value_substitutions.empty());
				bool out_of_class_member_template =
					(!declaration->outer_type_substitutions.empty() ||
					 !declaration->outer_value_substitutions.empty() ||
					 dependent_qualified_member_definition) &&
					(declaration->lexical_scope != declaration->owner ||
					 dependent_qualified_conversion_definition ||
					 dependent_qualified_member_definition ||
					 substituted_class_template_member_definition);
					if (out_of_class_member_template &&
					    declaration->has_definition &&
					    bare->scope != NULL &&
				    !declaration->constructor_template)
				{
					bool rebound_out_of_class_member_template = false;
					bool handled_ordinary_member_definition = false;
					vector<Binding*> candidate_placeholders;
					if (declaration->name == "operator ")
					{
						for (map<string, vector<Binding*> >::iterator mit =
							     bare->scope->members.begin();
						     mit != bare->scope->members.end();
						     ++mit)
							if (mit->first.compare(0, 9, "operator ") == 0)
								candidate_placeholders.insert(
									candidate_placeholders.end(),
									mit->second.begin(),
									mit->second.end());
					}
					else
					{
						map<string, vector<Binding*> >::iterator found =
							bare->scope->members.find(declaration->name);
						if (found != bare->scope->members.end())
							candidate_placeholders = found->second;
					}
					for (size_t j = 0; j < candidate_placeholders.size(); ++j)
						{
							Binding* placeholder = candidate_placeholders[j];
							map<Binding*, TemplateDeclaration*>::iterator existing =
								function_template_placeholders_.find(placeholder);
									bool ordinary_member_definition =
									existing == function_template_placeholders_.end() &&
									declaration->has_definition &&
								declaration->generic_function_type.get() != NULL &&
								declaration->generic_function_type->kind ==
									pa11::TypeKind::Function &&
								declaration->generic_function_type->parameters.empty() &&
								placeholder != NULL &&
								placeholder->kind == BindingKind::Function;
							map<string, TypePtr> subst;
							map<string, TemplateArgument> value_subst;
							set<string> pack_subst;
							for (size_t k = 0;
							     k < owner_arguments.size() &&
							     k < owner_declaration->parameters.size();
							     ++k)
							{
								const TemplateParameterInfo& parameter =
									owner_declaration->parameters[k];
								if (parameter.name.empty())
									continue;
								if (parameter.kind ==
								    TemplateParameterKind::Type)
								{
									if (parameter.is_pack)
									{
										subst[parameter.name] =
											pa11::make_template_parameter_type(
												parameter.name);
										value_subst[parameter.name] =
											owner_arguments[k];
										pack_subst.insert(parameter.name);
									}
									else
										subst[parameter.name] =
											owner_arguments[k].type;
								}
								else
									value_subst[parameter.name] =
										owner_arguments[k];
							}
							bool parameter_lists_match = ordinary_member_definition ||
								(existing != function_template_placeholders_.end() &&
								 template_parameter_lists_match(
									 existing->second->parameters,
									 declaration->parameters));
							if (!parameter_lists_match &&
							    existing != function_template_placeholders_.end())
							{
								vector<TemplateParameterInfo> substituted_parameters =
									declaration->parameters;
								vector<map<string, TypePtr> > save_subst =
									template_type_substitutions_;
								vector<map<string, TemplateArgument> >
									save_value_subst =
										template_value_substitutions_;
								vector<set<string> > save_pack_subst =
									template_type_parameter_packs_;
								template_type_substitutions_.push_back(subst);
								template_value_substitutions_.push_back(
									value_subst);
								template_type_parameter_packs_.push_back(
									pack_subst);
								try
								{
									for (size_t p = 0;
									     p < substituted_parameters.size();
									     ++p)
										if (substituted_parameters[p].kind ==
											    TemplateParameterKind::NonType &&
										    substituted_parameters[p].type.get() !=
											    NULL)
											substituted_parameters[p].type =
												substitute_template_type(
													substituted_parameters[p].type);
								}
								catch (const exception&)
								{
								}
								template_type_substitutions_ = save_subst;
								template_value_substitutions_ =
									save_value_subst;
								template_type_parameter_packs_ =
									save_pack_subst;
								{
									TemplateMatchParserScope
										match_parser_scope(this);
									parameter_lists_match =
										template_parameter_lists_match(
											existing->second->parameters,
											substituted_parameters);
								}
							}
								if ((!ordinary_member_definition &&
								     existing == function_template_placeholders_.end()) ||
								    (!ordinary_member_definition &&
								     existing->second == declaration) ||
								    (!ordinary_member_definition &&
									     (existing->second->decl_begin ==
									          declaration->decl_begin &&
									      existing->second->owner == bare->scope)) ||
									    (!ordinary_member_definition &&
									     !parameter_lists_match))
										{
											continue;
										}
							if (ordinary_member_definition)
							{
								size_t body_pos =
									function_body_start(tokens_,
									                    declaration->decl_begin,
									                    declaration->decl_end);
								if (body_pos == declaration->decl_end)
									continue;
								bool active_equivalent_body = false;
								for (set<Binding*>::const_iterator active =
									     active_function_body_replays_.begin();
								     active != active_function_body_replays_.end();
								     ++active)
								{
									Binding* replay = *active;
									if (replay == placeholder ||
									    (replay != NULL &&
									     placeholder != NULL &&
									     replay->aliased_binding == placeholder) ||
									    (replay != NULL &&
									     placeholder != NULL &&
									     placeholder->aliased_binding == replay))
									{
										active_equivalent_body = true;
										break;
									}
									if (replay == NULL ||
									    placeholder == NULL ||
									    replay->owner != placeholder->owner ||
									    replay->name != placeholder->name ||
									    replay->type.get() == NULL ||
									    placeholder->type.get() == NULL ||
									    !pa11::same_type(replay->type,
									                     placeholder->type))
										continue;
									active_equivalent_body = true;
									break;
								}
								if (active_equivalent_body)
								{
									handled_ordinary_member_definition = true;
									continue;
								}
								map<Binding*, Node>::iterator existing_body =
									function_bodies_.find(placeholder);
								if (existing_body != function_bodies_.end() &&
								    !function_body_signature_matches(
									    placeholder,
									    existing_body->second))
								{
									function_bodies_.erase(existing_body);
									for (size_t extra = 0;
									     extra < extra_lowir_nodes_.size();
									     )
									{
										if (extra_lowir_nodes_[extra].binding ==
										    placeholder)
											extra_lowir_nodes_.erase(
												extra_lowir_nodes_.begin() +
												extra);
										else
											++extra;
									}
								}
								bool already_have_body =
									function_bodies_.find(placeholder) !=
									function_bodies_.end() ||
									active_function_body_replays_.count(
										placeholder) != 0;
								for (size_t extra = 0;
								     !already_have_body &&
								     extra < extra_lowir_nodes_.size();
								     ++extra)
									already_have_body =
										extra_lowir_nodes_[extra].binding ==
										placeholder;
								if (already_have_body &&
								    declaration->class_specialization)
								{
									function_bodies_.erase(placeholder);
									for (size_t extra = 0;
									     extra < extra_lowir_nodes_.size();
									     )
									{
										if (extra_lowir_nodes_[extra].binding ==
										    placeholder)
											extra_lowir_nodes_.erase(
												extra_lowir_nodes_.begin() +
												extra);
										else
											++extra;
									}
									already_have_body = false;
								}
								if (already_have_body)
								{
									if (object_root)
									{
										placeholder->is_object_root = true;
										ensure_function_body_extra_node(placeholder);
									}
									handled_ordinary_member_definition = true;
									continue;
								}
								PendingFunctionBody pending;
								pending.function = placeholder;
								pending.node = Node(
									"function-definition " +
									qualified_decl_name(placeholder) + " " +
									pa11::describe_type(placeholder->type));
									pending.node.binding = placeholder;
									pending.node.type = placeholder->type;
									map<Binding*, vector<string> >::iterator
										placeholder_names =
											function_parameter_names_.find(
												placeholder);
									if ((placeholder_names ==
									     function_parameter_names_.end() ||
									     !member_parameter_names_have_non_this(
										     placeholder_names->second)) &&
									    member_parameter_names_have_non_this(
										    declaration->function_parameter_names))
									{
										function_parameter_names_[placeholder] =
											declaration->function_parameter_names;
										placeholder->function_parameter_names =
											declaration->function_parameter_names;
									}
									pending.parameters =
										concrete_member_body_parameters(
											placeholder,
										function_parameter_names_);
								pending.body_pos = body_pos;
								pending.class_type =
									pa11::record_type_for_scope(bare->scope);
								pending.scopes.clear();
								pending.scopes.push_back(
									declaration->lexical_scope != NULL
									? declaration->lexical_scope
									: owner_declaration->owner);
								pending.friend_class_scopes =
									active_friend_class_scopes_;
								pending.type_substitutions =
									template_type_substitutions_;
								pending.value_substitutions =
									template_value_substitutions_;
								pending.pack_substitutions =
									template_type_parameter_packs_;
								pending.type_substitutions.push_back(subst);
								pending.value_substitutions.push_back(
									value_subst);
								pending.pack_substitutions.push_back(
									pack_subst);
								if (!object_root)
								{
									bool already_pending = false;
									map<Scope*, vector<PendingFunctionBody> >::iterator
										pending_set =
											pending_member_bodies_.find(bare->scope);
									if (pending_set != pending_member_bodies_.end())
										for (size_t pending_i = 0;
										     pending_i < pending_set->second.size();
										     ++pending_i)
											if (pending_set->second[pending_i].function ==
											    placeholder)
												already_pending = true;
									if (!already_pending)
										enqueue_pending_member_body(bare->scope,
										                            pending);
									handled_ordinary_member_definition = true;
								}
								else
								{
									try
									{
										parse_pending_member_body_now(pending);
										placeholder->is_object_root = true;
										ensure_function_body_extra_node(placeholder);
										handled_ordinary_member_definition = true;
									}
									catch (const exception&)
									{
									}
								}
								continue;
							}
							TypePtr matched_type;
							bool dependent_definition_placeholder =
								declaration->has_definition &&
								declaration->generic_function_type.get() != NULL &&
								declaration->generic_function_type->kind ==
									pa11::TypeKind::Function &&
								declaration->generic_function_type->parameters.empty() &&
								existing->second->generic_function_type.get() != NULL &&
								existing->second->generic_function_type->kind ==
									pa11::TypeKind::Function;
							TypePtr generic_for_match =
								dependent_definition_placeholder
								? existing->second->generic_function_type
								: declaration->generic_function_type;
							vector<map<string, TypePtr> > save_subst =
								template_type_substitutions_;
							vector<map<string, TemplateArgument> > save_value_subst =
								template_value_substitutions_;
							vector<set<string> > save_pack_subst =
								template_type_parameter_packs_;
							try
							{
								template_type_substitutions_.push_back(subst);
								template_value_substitutions_.push_back(value_subst);
								template_type_parameter_packs_.push_back(pack_subst);
								matched_type =
									substitute_function_template_type(
										declaration,
										generic_for_match);
							}
									catch (const runtime_error&)
									{
										template_type_substitutions_ = save_subst;
									template_value_substitutions_ = save_value_subst;
									template_type_parameter_packs_ = save_pack_subst;
									continue;
							}
							template_type_substitutions_ = save_subst;
							template_value_substitutions_ = save_value_subst;
							template_type_parameter_packs_ = save_pack_subst;
							map<string, TemplateArgument> signature_deduced;
							TemplateMatchParserScope match_scope(this);
								if (!dependent_definition_placeholder &&
								    (matched_type.get() == NULL ||
								     placeholder->type.get() == NULL ||
								     !match_template_type_pattern(
									     matched_type,
									     placeholder->type,
									     signature_deduced,
									     record_template_arguments_)))
									{
										continue;
									}
						TemplateDeclaration* previous_placeholder_declaration =
							existing->second;
						if (previous_placeholder_declaration != NULL &&
						    previous_placeholder_declaration->placeholder != NULL)
						{
							map<Binding*, vector<string> >::const_iterator
								previous_names =
									function_parameter_names_.find(
										previous_placeholder_declaration->
											placeholder);
							if (previous_names !=
							    function_parameter_names_.end())
							{
								function_parameter_names_[placeholder] =
									previous_names->second;
								placeholder->function_parameter_names =
									previous_names->second;
							}
							map<Binding*, vector<Expr> >::const_iterator
								previous_defaults =
									default_arguments_.find(
										previous_placeholder_declaration->
											placeholder);
							if (previous_defaults !=
							    default_arguments_.end())
								default_arguments_[placeholder] =
									previous_defaults->second;
						}
						unique_ptr<TemplateDeclaration> clone(
							new TemplateDeclaration(*declaration));
						if (previous_placeholder_declaration != NULL)
							merge_template_parameter_defaults(
								clone->parameters,
								previous_placeholder_declaration->parameters);
						clone->owner = bare->scope;
						clone->placeholder = placeholder;
							if (dependent_definition_placeholder)
							{
								clone->name = placeholder->name;
								clone->generic_function_type =
									remap_template_parameter_names(
										generic_for_match,
										previous_placeholder_declaration != NULL
										? template_parameter_name_map(
											previous_placeholder_declaration->
												parameters,
											clone->parameters)
										: map<string, string>());
								if (previous_placeholder_declaration != NULL &&
								    previous_placeholder_declaration->
									    constructor_template)
								clone->constructor_template = true;
						}
							clone->function_specializations.clear();
						clone->completing_specializations.clear();
						clone->emitted_variable_specializations.clear();
						make_concrete_outer_substitutions(
							declaration,
							subst,
							value_subst,
							clone->outer_type_substitutions,
							clone->outer_value_substitutions);
						TemplateDeclaration* clone_ptr = clone.get();
						template_declarations_.push_back(std::move(clone));
							if (previous_placeholder_declaration != NULL &&
							    previous_placeholder_declaration != clone_ptr)
							{
								for (map<string, Binding*>::const_iterator spec =
									     previous_placeholder_declaration->
									     function_specializations.begin();
							     spec != previous_placeholder_declaration->
								     function_specializations.end();
							     ++spec)
							{
								clone_ptr->function_specializations[spec->first] =
									spec->second;
								function_template_placeholders_[spec->second] =
									clone_ptr;
							}
						}
								function_template_placeholders_[placeholder] =
									clone_ptr;
							{
								vector<TemplateDeclaration*>& rebound_templates =
									function_templates_[bare->scope]
									                   [declaration->name];
								if (find(rebound_templates.begin(),
								         rebound_templates.end(),
								         clone_ptr) ==
								    rebound_templates.end())
									rebound_templates.push_back(clone_ptr);
							}
							rebound_out_of_class_member_template = true;
							if (function_template_candidate_instantiation_depth_ == 0 &&
							    placeholder->type.get() != NULL &&
						    !type_is_template_dependent(placeholder->type))
						{
							vector<TemplateArgument> specialization_args;
							bool have_specialization_args = true;
							for (size_t a = 0;
							     a < clone_ptr->parameters.size();
							     ++a)
							{
								const string& parameter_name =
									clone_ptr->parameters[a].name;
								map<string, TemplateArgument>::iterator deduced =
									signature_deduced.find(parameter_name);
								if (parameter_name.empty() ||
								    deduced == signature_deduced.end())
								{
									have_specialization_args = false;
									break;
								}
								specialization_args.push_back(deduced->second);
							}
							if (have_specialization_args)
							{
								function_template_specialization_arguments_[
									placeholder] = specialization_args;
							}
						}
						}
					if (rebound_out_of_class_member_template ||
					    handled_ordinary_member_definition)
						continue;
					}
				if (declaration->constructor_template &&
				    (!declaration->outer_type_substitutions.empty() ||
				     !declaration->outer_value_substitutions.empty()) &&
				    declaration->lexical_scope != declaration->owner &&
				    bare->scope != NULL)
				{
					bool already_cloned = false;
					map<string, vector<Binding*> >::iterator existing_members =
						bare->scope->members.find(declaration->name);
					if (existing_members != bare->scope->members.end())
						for (size_t j = 0;
						     j < existing_members->second.size();
						     ++j)
						{
							map<Binding*, TemplateDeclaration*>::iterator existing =
								function_template_placeholders_.find(
									existing_members->second[j]);
							if (existing == function_template_placeholders_.end())
								continue;
							if (existing->second->decl_begin ==
							    declaration->decl_begin &&
							    existing->second->owner == bare->scope)
								already_cloned = true;
						}
					if (already_cloned)
						continue;
					map<string, TypePtr> subst;
					map<string, TemplateArgument> value_subst;
					set<string> pack_subst;
					for (size_t k = 0;
					     k < owner_arguments.size() &&
					     k < owner_declaration->parameters.size();
					     ++k)
					{
						const TemplateParameterInfo& parameter =
							owner_declaration->parameters[k];
						if (parameter.name.empty())
							continue;
						if (parameter.kind == TemplateParameterKind::Type)
						{
							if (parameter.is_pack)
							{
								subst[parameter.name] =
									pa11::make_template_parameter_type(
										parameter.name);
								value_subst[parameter.name] =
									owner_arguments[k];
								pack_subst.insert(parameter.name);
							}
							else
								subst[parameter.name] =
									owner_arguments[k].type;
						}
						else
							value_subst[parameter.name] =
								owner_arguments[k];
					}
					vector<map<string, TypePtr> > save_subst =
						template_type_substitutions_;
					vector<map<string, TemplateArgument> > save_value_subst =
						template_value_substitutions_;
					vector<set<string> > save_pack_subst =
						template_type_parameter_packs_;
					TypePtr fn_type;
					try
					{
						template_type_substitutions_.push_back(subst);
						template_value_substitutions_.push_back(value_subst);
						template_type_parameter_packs_.push_back(pack_subst);
						fn_type =
							substitute_function_template_type(
								declaration,
								declaration->generic_function_type);
					}
					catch (...)
					{
						template_type_substitutions_ = save_subst;
						template_value_substitutions_ = save_value_subst;
						template_type_parameter_packs_ = save_pack_subst;
						throw;
					}
						if (fn_type.get() != NULL &&
						    fn_type->kind == pa11::TypeKind::Function &&
						    !fn_type->parameters.empty())
						{
							vector<TypePtr> params = fn_type->parameters;
							params[0] = pa11::make_pointer(bare);
							TypePtr rebound =
								pa11::make_function(fn_type->base,
								                    params,
								                    fn_type->variadic);
							rebound->cv = fn_type->cv;
							rebound->ref_qualifier = fn_type->ref_qualifier;
							fn_type = rebound;
						}
						template_type_substitutions_ = save_subst;
					template_value_substitutions_ = save_value_subst;
					template_type_parameter_packs_ = save_pack_subst;
						Binding* placeholder = NULL;
						map<string, vector<Binding*> >::iterator matching_members =
							bare->scope->members.find(declaration->name);
						if (matching_members != bare->scope->members.end())
							for (size_t j = 0;
							     j < matching_members->second.size();
							     ++j)
							{
								Binding* candidate = matching_members->second[j];
								if (candidate->kind != BindingKind::Function ||
								    !same_constructor_type_for_owner(
									    candidate->type,
									    fn_type,
									    bare))
									continue;
								map<Binding*, TemplateDeclaration*>::iterator mapped =
									function_template_placeholders_.find(candidate);
								if (mapped == function_template_placeholders_.end() ||
								    !mapped->second->constructor_template)
									continue;
								if (mapped->second->has_definition &&
								    !template_parameter_lists_match(
									    mapped->second->parameters,
									    declaration->parameters))
									continue;
								placeholder = candidate;
								break;
							}
							if (placeholder == NULL)
								placeholder =
									add_value(bare->scope,
									          BindingKind::Function,
									          declaration->name,
									          fn_type);
							if (declaration->constructor_template)
								discard_implicit_default_constructor(bare,
								                                     placeholder);
						if (declaration->placeholder != NULL)
					{
						placeholder->is_explicit =
							declaration->placeholder->is_explicit;
						placeholder->is_constexpr =
							declaration->placeholder->is_constexpr;
						placeholder->unwind_no =
							declaration->placeholder->unwind_no;
						placeholder->ref_qualifier =
							declaration->placeholder->ref_qualifier;
							map<Binding*, vector<string> >::iterator names =
								function_parameter_names_.find(
									declaration->placeholder);
							if (names != function_parameter_names_.end())
							{
								function_parameter_names_[placeholder] =
									names->second;
								placeholder->function_parameter_names =
									names->second;
							}
							map<Binding*, vector<Expr> >::iterator defaults =
								default_arguments_.find(
									declaration->placeholder);
							if (defaults != default_arguments_.end())
								default_arguments_[placeholder] =
									defaults->second;
					}
						unique_ptr<TemplateDeclaration> clone(
							new TemplateDeclaration(*declaration));
						clone->owner = bare->scope;
						clone->placeholder = placeholder;
						TemplateDeclaration* previous_placeholder_declaration = NULL;
						map<Binding*, TemplateDeclaration*>::iterator previous_placeholder =
							function_template_placeholders_.find(placeholder);
						if (previous_placeholder !=
						    function_template_placeholders_.end())
							previous_placeholder_declaration =
								previous_placeholder->second;
						clone->function_specializations.clear();
					clone->completing_specializations.clear();
					clone->emitted_variable_specializations.clear();
					make_concrete_outer_substitutions(
						declaration,
						subst,
						value_subst,
						clone->outer_type_substitutions,
						clone->outer_value_substitutions);
						TemplateDeclaration* clone_ptr = clone.get();
						template_declarations_.push_back(std::move(clone));
						if (previous_placeholder_declaration != NULL &&
						    previous_placeholder_declaration != clone_ptr)
						{
							bool same_placeholder_family =
								template_parameter_lists_match(
									previous_placeholder_declaration->parameters,
									clone_ptr->parameters) &&
								same_template_signature_type(
									previous_placeholder_declaration->
										generic_function_type,
									clone_ptr->generic_function_type);
							if (same_placeholder_family)
								for (map<string, Binding*>::const_iterator spec =
									     previous_placeholder_declaration->
										     function_specializations.begin();
								     spec != previous_placeholder_declaration->
									     function_specializations.end();
								     ++spec)
								{
									clone_ptr->function_specializations[spec->first] =
										spec->second;
									map<Binding*, TemplateDeclaration*>::iterator
										existing_spec =
											function_template_placeholders_.find(
												spec->second);
									if (clone_ptr->has_definition ||
									    existing_spec ==
										    function_template_placeholders_.end() ||
									    existing_spec->second == NULL ||
									    !existing_spec->second->has_definition)
										function_template_placeholders_[spec->second] =
											clone_ptr;
								}
								if (clone_ptr->has_definition &&
								    same_placeholder_family)
									for (map<Binding*, TemplateDeclaration*>::iterator
										     mapped =
											     function_template_placeholders_.begin();
									     mapped !=
										     function_template_placeholders_.end();
									     ++mapped)
										if (mapped->second ==
										    previous_placeholder_declaration)
											mapped->second = clone_ptr;
								if (clone_ptr->has_definition)
									for (map<Binding*, TemplateDeclaration*>::iterator
										     mapped =
											     function_template_placeholders_.begin();
									     mapped !=
										     function_template_placeholders_.end();
									     ++mapped)
										if (mapped->second != NULL &&
										    mapped->second != clone_ptr &&
										    !mapped->second->has_definition &&
										    mapped->second->name ==
											    clone_ptr->name &&
										    template_parameter_lists_match(
											    mapped->second->parameters,
											    clone_ptr->parameters) &&
										    same_template_signature_type(
											    mapped->second->
												    generic_function_type,
											    clone_ptr->
												    generic_function_type))
											mapped->second = clone_ptr;
							}
							map<Binding*, TemplateDeclaration*>::iterator
								current_placeholder =
									function_template_placeholders_.find(placeholder);
							if (clone_ptr->has_definition ||
							    current_placeholder ==
								    function_template_placeholders_.end() ||
							    current_placeholder->second == NULL ||
							    !current_placeholder->second->has_definition)
								function_template_placeholders_[placeholder] =
									clone_ptr;
							continue;
				}
				if (declaration->constructor_template &&
				    (declaration->inherited_constructor_base != NULL ||
				     !declaration->outer_type_substitutions.empty() ||
				     !template_parameter_lists_match(declaration->parameters,
				                                     owner_declaration->parameters)))
					continue;
				bool class_template_member_function_template =
					!declaration->constructor_template &&
					declaration->class_template_member &&
					declaration->outer_type_substitutions.empty() &&
					declaration->outer_value_substitutions.empty() &&
					!template_parameter_lists_match(declaration->parameters,
					                                owner_declaration->parameters);
				if (!declaration->constructor_template &&
				    declaration->class_template_member &&
				    !class_template_member_function_template)
				{
					if (!declaration->outer_type_substitutions.empty() ||
					    !declaration->outer_value_substitutions.empty() ||
					    !template_parameter_lists_match(declaration->parameters,
					                                    owner_declaration->parameters))
						continue;
				}
					if (!declaration->constructor_template &&
					    (!declaration->class_template_member ||
					     class_template_member_function_template))
					{
						bool already_cloned = false;
						map<string, vector<Binding*> >::iterator existing_members =
							bare->scope->members.find(declaration->name);
							if (existing_members != bare->scope->members.end())
								for (size_t j = 0;
								     j < existing_members->second.size();
								     ++j)
								{
									map<Binding*, TemplateDeclaration*>::iterator mapped =
										function_template_placeholders_.find(
											existing_members->second[j]);
									if (mapped != function_template_placeholders_.end() &&
									    mapped->second->decl_begin ==
										    declaration->decl_begin &&
								    mapped->second->owner == bare->scope)
										already_cloned = true;
								}
							if (already_cloned)
							continue;
						map<string, TypePtr> subst;
						map<string, TemplateArgument> value_subst;
						set<string> pack_subst;
						for (size_t k = 0;
						     k < owner_arguments.size() &&
						     k < owner_declaration->parameters.size();
						     ++k)
						{
							const TemplateParameterInfo& parameter =
								owner_declaration->parameters[k];
							if (parameter.name.empty())
								continue;
							if (parameter.kind == TemplateParameterKind::Type)
							{
								if (parameter.is_pack)
								{
									subst[parameter.name] =
										pa11::make_template_parameter_type(
											parameter.name);
									value_subst[parameter.name] =
										owner_arguments[k];
									pack_subst.insert(parameter.name);
								}
								else
									subst[parameter.name] =
										owner_arguments[k].type;
							}
							else
								value_subst[parameter.name] =
									owner_arguments[k];
						}
						vector<map<string, TypePtr> > save_subst =
							template_type_substitutions_;
						vector<map<string, TemplateArgument> > save_value_subst =
							template_value_substitutions_;
							vector<set<string> > save_pack_subst =
								template_type_parameter_packs_;
							TypePtr fn_type =
								TypePtr();
							try
							{
								template_type_substitutions_.push_back(subst);
								template_value_substitutions_.push_back(value_subst);
								template_type_parameter_packs_.push_back(pack_subst);
								fn_type =
									substitute_function_template_type(
										declaration,
										declaration->generic_function_type);
							}
								catch (const runtime_error& err)
								{
									template_type_substitutions_ = save_subst;
									template_value_substitutions_ = save_value_subst;
									template_type_parameter_packs_ = save_pack_subst;
									if (string(err.what()) ==
									    "dependent typename not resolved")
										fn_type = declaration->generic_function_type;
									else
										throw;
								}
							template_type_substitutions_ = save_subst;
							template_value_substitutions_ = save_value_subst;
							template_type_parameter_packs_ = save_pack_subst;
									Binding* placeholder =
										add_value(bare->scope,
										          BindingKind::Function,
										          declaration->name,
										          fn_type);
									if (declaration->constructor_template)
										discard_implicit_default_constructor(
											bare,
											placeholder);
									if (declaration->placeholder != NULL)
						{
							placeholder->is_static_member =
								declaration->placeholder->is_static_member;
							placeholder->is_explicit =
								declaration->placeholder->is_explicit;
							placeholder->is_constexpr =
								declaration->placeholder->is_constexpr;
							placeholder->unwind_no =
								declaration->placeholder->unwind_no;
							placeholder->ref_qualifier =
								declaration->placeholder->ref_qualifier;
							map<Binding*, vector<string> >::iterator names =
								function_parameter_names_.find(
									declaration->placeholder);
							if (names != function_parameter_names_.end())
							{
								function_parameter_names_[placeholder] =
									names->second;
								placeholder->function_parameter_names =
									names->second;
							}
							map<Binding*, vector<Expr> >::iterator defaults =
								default_arguments_.find(
									declaration->placeholder);
							if (defaults != default_arguments_.end())
								default_arguments_[placeholder] =
									defaults->second;
						}
						unique_ptr<TemplateDeclaration> clone(
							new TemplateDeclaration(*declaration));
						clone->owner = bare->scope;
						clone->placeholder = placeholder;
						clone->function_specializations.clear();
						clone->completing_specializations.clear();
						clone->emitted_variable_specializations.clear();
							make_concrete_outer_substitutions(
								declaration,
								subst,
								value_subst,
								clone->outer_type_substitutions,
								clone->outer_value_substitutions);
							TemplateDeclaration* clone_ptr = clone.get();
							template_declarations_.push_back(std::move(clone));
							map<Binding*, TemplateDeclaration*>::iterator
								current_placeholder =
									function_template_placeholders_.find(placeholder);
							if (clone_ptr->has_definition ||
							    current_placeholder ==
								    function_template_placeholders_.end() ||
							    current_placeholder->second == NULL ||
							    !current_placeholder->second->has_definition)
								function_template_placeholders_[placeholder] =
									clone_ptr;
							function_templates_[bare->scope][declaration->name].
								push_back(clone_ptr);
						continue;
					}
					string key = template_argument_key(owner_arguments);
				if (declaration->completing_specializations.count(key) != 0)
					continue;
				bool restored_placeholder_names = false;
				bool had_placeholder_names = false;
				vector<string> saved_placeholder_names;
				if (declaration->class_template_member &&
				    declaration->placeholder != NULL &&
				    bare->scope != NULL)
				{
					map<string, TypePtr> subst;
					map<string, TemplateArgument> value_subst;
					set<string> pack_subst;
					for (size_t k = 0;
					     k < owner_arguments.size() &&
					     k < owner_declaration->parameters.size();
					     ++k)
					{
						const TemplateParameterInfo& parameter =
							owner_declaration->parameters[k];
						if (parameter.name.empty())
							continue;
						if (parameter.kind == TemplateParameterKind::Type)
						{
							if (parameter.is_pack)
							{
								subst[parameter.name] =
									pa11::make_template_parameter_type(
										parameter.name);
								value_subst[parameter.name] =
									owner_arguments[k];
								pack_subst.insert(parameter.name);
							}
							else
								subst[parameter.name] =
									owner_arguments[k].type;
						}
						else
							value_subst[parameter.name] =
								owner_arguments[k];
					}
					vector<map<string, TypePtr> > save_subst =
						template_type_substitutions_;
					vector<map<string, TemplateArgument> > save_value_subst =
						template_value_substitutions_;
					vector<set<string> > save_pack_subst =
						template_type_parameter_packs_;
					try
					{
						template_type_substitutions_.push_back(subst);
						template_value_substitutions_.push_back(value_subst);
						template_type_parameter_packs_.push_back(pack_subst);
						TypePtr fn_type =
							substitute_function_template_type(
								declaration,
								declaration->generic_function_type);
						map<string, vector<Binding*> >::iterator found =
							bare->scope->members.find(declaration->name);
						if (found != bare->scope->members.end())
							for (size_t j = 0;
							     j < found->second.size();
							     ++j)
							{
								Binding* concrete = found->second[j];
								bool same_member_type =
									pa11::same_type(concrete->type, fn_type) ||
									same_constructor_type_for_owner(
										concrete->type,
										fn_type,
										bare) ||
									same_static_member_type_with_owner_parameter(
										concrete->type,
										fn_type,
										bare);
								if (concrete->kind != BindingKind::Function ||
								    !same_member_type)
									continue;
								map<Binding*, vector<string> >::iterator names =
									function_parameter_names_.find(concrete);
								if (names == function_parameter_names_.end())
									continue;
								map<Binding*, vector<string> >::iterator
									placeholder_names =
										function_parameter_names_.find(
											declaration->placeholder);
									if (placeholder_names !=
									    function_parameter_names_.end())
									{
										had_placeholder_names = true;
										saved_placeholder_names =
											placeholder_names->second;
									}
									function_parameter_names_[
										declaration->placeholder] =
										names->second;
								restored_placeholder_names = true;
								break;
							}
						template_type_substitutions_ = save_subst;
						template_value_substitutions_ = save_value_subst;
						template_type_parameter_packs_ = save_pack_subst;
					}
						catch (const runtime_error& err)
						{
							template_type_substitutions_ = save_subst;
							template_value_substitutions_ = save_value_subst;
							template_type_parameter_packs_ = save_pack_subst;
							if (string(err.what()) ==
							    "dependent typename not resolved")
								continue;
							throw;
						}
					}
				Binding* binding = NULL;
				try
				{
					binding =
						instantiate_function_template(declaration,
						                              owner_arguments);
				}
					catch (const runtime_error& err)
					{
						if (restored_placeholder_names)
						{
						if (had_placeholder_names)
							function_parameter_names_[
								declaration->placeholder] =
								saved_placeholder_names;
						else
								function_parameter_names_.erase(
									declaration->placeholder);
					}
						if (string(err.what()) ==
						    "dependent typename not resolved")
							continue;
						throw;
					}
				if (restored_placeholder_names)
				{
					if (had_placeholder_names)
						function_parameter_names_[
							declaration->placeholder] =
							saved_placeholder_names;
					else
						function_parameter_names_.erase(
							declaration->placeholder);
				}
				if (binding != NULL &&
				    binding->function_parameter_names.empty() &&
				    !declaration->function_parameter_names.empty())
				{
					vector<string> names =
						declaration->function_parameter_names;
					if (binding->type.get() != NULL &&
					    binding->type->kind == pa11::TypeKind::Function &&
					    names.size() < binding->type->parameters.size())
						names.resize(binding->type->parameters.size());
					function_parameter_names_[binding] = names;
					binding->function_parameter_names = names;
				}
				if (binding != NULL && bare->scope != NULL)
				{
					TypePtr binding_owner_record =
						binding->owner != NULL
						? pa11::record_type_for_scope(binding->owner)
						: TypePtr();
					binding_owner_record =
						binding_owner_record.get() != NULL
						? pa11::strip_cv(binding_owner_record) : TypePtr();
					map<const void*, TemplateDeclaration*>::iterator binding_decl =
						binding_owner_record.get() != NULL
						? record_template_declarations_.find(
							binding_owner_record.get())
						: record_template_declarations_.end();
					map<const void*, vector<TemplateArgument> >::iterator
						binding_args = binding_owner_record.get() != NULL
						? record_template_arguments_.find(
							binding_owner_record.get())
						: record_template_arguments_.end();
					if (binding->owner != bare->scope &&
					    binding_decl != record_template_declarations_.end() &&
					    binding_decl->second == owner_declaration &&
					    binding_args != record_template_arguments_.end() &&
					    template_argument_key(binding_args->second) == key)
					{
							Binding* alias =
								add_value(bare->scope,
								          BindingKind::Function,
								          declaration->name,
								          binding->type);
							alias->is_inline_definition =
								binding->is_inline_definition;
							alias->is_explicit = binding->is_explicit;
							alias->is_constexpr = binding->is_constexpr;
							alias->unwind_no = binding->unwind_no;
							alias->ref_qualifier = binding->ref_qualifier;
							string concrete_symbol =
								abi_binding_symbol(alias,
								                   map<string, size_t>());
							alias->function_specialization_symbol =
								concrete_symbol;
							binding->function_specialization_symbol =
								concrete_symbol;
							alias->aliased_binding = binding;
							map<Binding*, vector<string> >::iterator names =
								function_parameter_names_.find(binding);
						if (names != function_parameter_names_.end())
						{
							function_parameter_names_[alias] = names->second;
							alias->function_parameter_names = names->second;
						}
					}
					map<string, vector<Binding*> >::iterator found =
						bare->scope->members.find(declaration->name);
				if (found != bare->scope->members.end())
					for (size_t j = 0; j < found->second.size(); ++j)
					{
						Binding* concrete = found->second[j];
						bool conversion_alias_mismatch = false;
						if (concrete != NULL &&
						    binding != NULL &&
						    concrete->name.compare(0, 9, "operator ") == 0 &&
						    binding->name.compare(0, 9, "operator ") == 0)
						{
							map<Binding*, TemplateDeclaration*>::iterator
								concrete_template =
									function_template_placeholders_.find(
										concrete);
							map<Binding*, TemplateDeclaration*>::iterator
								binding_template =
									function_template_placeholders_.find(
										binding);
							bool concrete_is_function_template =
								concrete_template !=
								    function_template_placeholders_.end() &&
								!concrete_template->second->
									class_template_member;
							bool binding_is_function_template =
								binding_template !=
								    function_template_placeholders_.end() &&
								!binding_template->second->
									class_template_member;
							conversion_alias_mismatch =
								concrete_is_function_template !=
								binding_is_function_template;
						}
						if (concrete != binding &&
						    concrete->kind == BindingKind::Function &&
						    !conversion_alias_mismatch &&
						    (pa11::same_type(concrete->type,
						                    binding->type) ||
						     same_constructor_type_for_owner(
							     concrete->type,
							     binding->type,
							     bare)))
						{
							concrete->aliased_binding = binding;
							map<Binding*, vector<string> >::iterator names =
								function_parameter_names_.find(concrete);
							if (names != function_parameter_names_.end())
							{
								function_parameter_names_[binding] = names->second;
								binding->function_parameter_names = names->second;
							}
						}
					}
			}
			if (object_root && binding != NULL)
			{
				parse_pending_function_body(binding);
				parse_pending_member_body(binding);
				binding->is_object_root = true;
				ensure_function_body_extra_node(binding);
				if (binding->aliased_binding != NULL)
				{
					parse_pending_function_body(binding->aliased_binding);
					parse_pending_member_body(binding->aliased_binding);
					binding->aliased_binding->is_object_root = true;
					ensure_function_body_extra_node(binding->aliased_binding);
				}
				}
			}
		}
	scopes_ = save_scopes;
	pos_ = save_pos;
	completed_member_function_template_records_[cache_key] =
		member_function_template_generation_;
	}


}  // namespace internal
}  // namespace pa12
