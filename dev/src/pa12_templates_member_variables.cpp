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

void Parser::instantiate_member_variable_templates(TypePtr type)
{
	TypePtr bare = pa11::strip_cv(type);
	if (bare->kind != pa11::TypeKind::Record)
		return;
	size_t outer_pos = pos_;
	vector<Scope*> outer_scopes = scopes_;
	map<const void*, TemplateDeclaration*>::iterator outer =
		record_template_declarations_.find(bare.get());
	if (outer == record_template_declarations_.end())
		return;
	map<const void*, vector<TemplateArgument> >::iterator args_it =
		record_template_arguments_.find(bare.get());
	if (args_it == record_template_arguments_.end())
		return;
	if (template_arguments_dependent(args_it->second))
		return;
	for (int template_variable_pass = 0;
	     template_variable_pass < 2;
	     ++template_variable_pass)
	{
		bool want_explicit_initializer = template_variable_pass == 0;
		for (map<pair<TemplateDeclaration*, string>,
		         vector<TemplateDeclaration*> >::iterator it =
			     member_variable_templates_.begin();
		     it != member_variable_templates_.end();
		     ++it)
		{
			if (it->first.first != outer->second)
				continue;
			bool owner_has_nontype_parameter = false;
			for (size_t i = 0; i < outer->second->parameters.size(); ++i)
				if (outer->second->parameters[i].kind ==
				    TemplateParameterKind::NonType)
					owner_has_nontype_parameter = true;
			bool dependent_owner_arguments =
				template_arguments_dependent(args_it->second);
			if (validating_template_definition_ ||
			    function_template_candidate_instantiation_depth_ != 0)
				continue;
			for (size_t i = 0; i < it->second.size(); ++i)
			{
				TemplateDeclaration* declaration = it->second[i];
				size_t save_pos = pos_;
				vector<Scope*> save_scopes = scopes_;
				vector<map<string, TypePtr> > save_subst =
					template_type_substitutions_;
				vector<map<string, TemplateArgument> > save_value_subst =
					template_value_substitutions_;
				map<string, TypePtr> subst;
				map<string, TemplateArgument> value_subst;
				for (size_t j = 0; j < args_it->second.size() &&
				     j < declaration->parameters.size(); ++j)
					if (!declaration->parameters[j].name.empty())
					{
						if (declaration->parameters[j].kind ==
						    TemplateParameterKind::Type)
						{
							if (declaration->parameters[j].is_pack)
							{
								const TemplateParameterInfo& parameter =
									declaration->parameters[j];
								subst[declaration->parameters[j].name] =
									template_parameter_placeholder_type(
										parameter);
								value_subst[declaration->parameters[j].name] =
									args_it->second[j];
							}
							else
								subst[declaration->parameters[j].name] =
									args_it->second[j].type;
						}
						else
							value_subst[declaration->parameters[j].name] =
								args_it->second[j];
					}
				template_type_substitutions_.push_back(subst);
				template_value_substitutions_.push_back(value_subst);
				scopes_.clear();
				scopes_.push_back(declaration->lexical_scope != NULL
				                  ? declaration->lexical_scope
				                  : declaration->owner);
				bool explicit_initializer = false;
				for (size_t j = declaration->decl_begin;
				     j < declaration_tokens_.size();
				     ++j)
				{
					if (declaration_tokens_[j].kind !=
					    posttoken::TokenKind::Simple)
						continue;
					if (declaration_tokens_[j].type == OP_SEMICOLON)
						break;
					if (declaration_tokens_[j].type == OP_ASS ||
					    declaration_tokens_[j].type == OP_LBRACE)
						explicit_initializer = true;
				}
				if (explicit_initializer != want_explicit_initializer)
				{
					template_type_substitutions_ = save_subst;
					template_value_substitutions_ = save_value_subst;
					scopes_ = save_scopes;
					pos_ = save_pos;
					continue;
				}
				string key = template_argument_key(args_it->second) +
				             "::" + declaration->name;
				if (!declaration->emitted_variable_specializations.insert(key).second)
				{
					template_type_substitutions_ = save_subst;
					template_value_substitutions_ = save_value_subst;
					scopes_ = save_scopes;
					pos_ = save_pos;
					continue;
				}
				if (!explicit_initializer)
				{
					vector<Binding*> members =
						lookup_qualified_set(bare->scope,
						                     declaration->name,
						                     pa11::LOOKUP_VALUE);
					Binding* member = NULL;
					for (size_t j = 0; j < members.size(); ++j)
					{
						Binding* candidate = members[j];
						if (candidate == NULL ||
						    candidate->kind != BindingKind::Variable ||
						    !candidate->is_static_member)
							continue;
						if (candidate->owner == bare->scope)
						{
							member = candidate;
							break;
						}
						TypePtr candidate_owner =
							candidate->owner != NULL
							? pa11::record_type_for_scope(candidate->owner)
							: TypePtr();
						if (candidate_owner.get() != NULL &&
						    same_template_record_type(candidate_owner, bare))
							member = candidate;
					}
					if (member != NULL &&
					    (!owner_has_nontype_parameter ||
					     !dependent_owner_arguments))
					{
						TypePtr member_type = member->type;
						try
						{
							TypePtr substituted =
								substitute_template_type(member_type);
							if (substituted_type_is_valid(substituted))
							{
								member_type = substituted;
								member->type = substituted;
							}
						}
						catch (const exception&)
						{
						}
						Node replay("variable " + member->name + " " +
						            pa11::describe_type(member_type));
						replay.binding = member;
						replay.type = member_type;
						map<Binding*, Node>::const_iterator init =
							find_static_member_initializer_for_binding(
								static_member_initializers_,
								member);
						if (init != static_member_initializers_.end())
						{
							add_child(replay, init->second);
							ConstexprValue value;
							bool eval_ok =
								try_evaluate_constexpr_expr(init->second, value);
							if (!member->has_constant &&
							    eval_ok &&
							    !value.is_object &&
							    !value.is_pointer)
							{
								member->has_constant = true;
								member->constant_value = value.int_value;
							}
						}
						TypePtr object_type =
							expression_object_type(member->type);
						TypePtr bare_object = pa11::strip_cv(object_type);
						bool record_or_array_static =
							bare_object->kind == pa11::TypeKind::Record ||
							bare_object->kind == pa11::TypeKind::Array;
						if (!declaration->parameters.empty() &&
						    (!member->is_constexpr ||
						     record_or_array_static ||
						     !replay.children.empty()))
						{
							member->is_template_static_member_definition = true;
							member->is_template_static_member_explicit_definition =
								false;
							replay.token_text =
								"template-static-member-definition";
						}
						add_child(root_, replay);
						template_type_substitutions_ = save_subst;
						template_value_substitutions_ = save_value_subst;
						scopes_ = save_scopes;
						pos_ = save_pos;
						continue;
					}
				}
				pos_ = declaration->decl_begin;
				Node node;
				try
				{
					parse_simple_or_function_declaration(node, true);
				}
				catch (const exception&)
				{
					declaration->emitted_variable_specializations.erase(key);
					template_type_substitutions_ = save_subst;
					template_value_substitutions_ = save_value_subst;
					scopes_ = save_scopes;
					pos_ = save_pos;
					throw;
				}
				vector<Node*> replay_nodes;
				if (node.binding != NULL)
					replay_nodes.push_back(&node);
				for (size_t j = 0; j < node.children.size(); ++j)
					if (node.children[j].binding != NULL)
						replay_nodes.push_back(&node.children[j]);
				for (size_t j = 0; j < replay_nodes.size(); ++j)
				{
					Node& replay = *replay_nodes[j];
					if (replay.binding == NULL ||
					    !replay.binding->is_static_member ||
					    (owner_has_nontype_parameter &&
					     dependent_owner_arguments &&
					     !replay.children.empty()))
						continue;
					TypePtr object_type =
						expression_object_type(replay.binding->type);
					TypePtr bare_object = pa11::strip_cv(object_type);
					bool record_or_array_static =
						bare_object->kind == pa11::TypeKind::Record ||
						bare_object->kind == pa11::TypeKind::Array;
					if (!declaration->parameters.empty() &&
					    (!replay.binding->is_constexpr ||
					     record_or_array_static ||
					     explicit_initializer ||
					     !replay.children.empty()))
					{
						replay.binding->is_template_static_member_definition =
							true;
						replay.binding
							->is_template_static_member_explicit_definition =
							explicit_initializer;
						replay.token_text =
							"template-static-member-definition";
					}
					add_child(root_, replay);
				}
				template_type_substitutions_ = save_subst;
				template_value_substitutions_ = save_value_subst;
				scopes_ = save_scopes;
				pos_ = save_pos;
			}
		}
	}
	scopes_ = outer_scopes;
	pos_ = outer_pos;
}


}  // namespace internal
}  // namespace pa12
