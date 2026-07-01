#include "pa12_expr_semantics_support.h"
#include "pa12_templates_function_support.h"
#include "pa12_templates_instance_support.h"
#include <algorithm>
#include <stdexcept>
#include <utility>
using namespace std;
namespace pa12 {
namespace internal {

bool member_parameter_names_have_non_this(const vector<string>& names);
void build_owner_template_substitutions(const vector<TemplateArgument>& owner_arguments, TemplateDeclaration* owner_declaration, map<string, TypePtr>& subst, map<string, TemplateArgument>& value_subst, set<string>& pack_subst);
void copy_member_template_placeholder_state(Binding* placeholder, Binding* source, map<Binding*, vector<string> >& function_parameter_names, map<Binding*, vector<Expr> >& default_arguments, bool copy_static_member);
void assign_member_template_alias_state(Binding* alias, Binding* source);
void merge_member_template_alias_state(Binding* concrete, Binding* source);
bool ordinary_member_definition_matches_placeholder(const TemplateDeclaration* declaration, Binding* function, const vector<Token>& tokens);
bool class_constructor_binding_name(const Binding* binding);
bool special_member_alias_mismatch(const Binding* left, const Binding* right);
TypePtr rebind_nested_constructor_self_type(TypePtr type, TypePtr current);

bool Parser::clone_class_template_member_template(
	TypePtr bare,
	TemplateDeclaration* owner_declaration,
	const vector<TemplateArgument>& owner_arguments,
	TemplateDeclaration* declaration)
{
				if (declaration->constructor_template &&
				    (declaration->inherited_constructor_base != NULL ||
				     !declaration->outer_type_substitutions.empty() ||
				     !template_parameter_lists_match(declaration->parameters,
				                                     owner_declaration->parameters)))
					return true;
					bool class_template_member_function_template =
						!declaration->constructor_template &&
						declaration->class_template_member &&
						declaration->outer_type_substitutions.empty() &&
						declaration->outer_value_substitutions.empty() &&
						!template_parameter_lists_match(declaration->parameters,
						                                owner_declaration->parameters);
					bool class_template_member_constructor =
						declaration->constructor_template &&
						declaration->has_definition &&
						declaration->class_template_member &&
						declaration->outer_type_substitutions.empty() &&
						declaration->outer_value_substitutions.empty() &&
						template_parameter_lists_match(declaration->parameters,
						                               owner_declaration->parameters);
				if (!declaration->constructor_template &&
				    declaration->class_template_member &&
				    !class_template_member_function_template)
				{
					if (!declaration->outer_type_substitutions.empty() ||
					    !declaration->outer_value_substitutions.empty() ||
					    !template_parameter_lists_match(declaration->parameters,
					                                    owner_declaration->parameters))
						return true;
				}
						if ((!declaration->constructor_template ||
						     class_template_member_constructor) &&
						    (!declaration->class_template_member ||
						     class_template_member_function_template ||
						     class_template_member_constructor))
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
							return true;
						map<string, TypePtr> subst;
						map<string, TemplateArgument> value_subst;
						set<string> pack_subst;
						build_owner_template_substitutions(owner_arguments,
						                                   owner_declaration,
						                                   subst,
						                                   value_subst,
						                                   pack_subst);
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
									Binding* placeholder = NULL;
									if (class_template_member_constructor)
									{
										map<string, vector<Binding*> >::iterator found =
											bare->scope->members.find(
												declaration->name);
										if (found != bare->scope->members.end())
											for (size_t j = 0;
											     j < found->second.size();
											     ++j)
											{
												Binding* candidate =
													found->second[j];
												if (candidate->kind ==
													    BindingKind::Function &&
												    same_constructor_type_for_owner(
													    candidate->type,
													    fn_type,
													    bare))
												{
													placeholder = candidate;
													break;
												}
											}
									}
									if (placeholder == NULL)
										placeholder =
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
								copy_member_template_placeholder_state(
									placeholder,
									declaration->placeholder,
									function_parameter_names_,
									default_arguments_,
									true);
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
								owner_declaration,
								owner_arguments,
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
							if (class_template_member_constructor)
							{
								size_t body_pos =
									constructor_body_start(
										tokens_,
										declaration->decl_begin,
										declaration->decl_end);
								if (body_pos != declaration->decl_end)
								{
									placeholder->is_inline_definition = true;
									if (member_parameter_names_have_non_this(
										    declaration->function_parameter_names))
									{
										function_parameter_names_[placeholder] =
											declaration->function_parameter_names;
										placeholder->function_parameter_names =
											declaration->function_parameter_names;
									}
									PendingFunctionBody pending;
									pending.function = placeholder;
									pending.node = Node(
										"function-definition " +
										qualified_decl_name(placeholder) + " " +
										pa11::describe_type(placeholder->type));
									pending.node.binding = placeholder;
									pending.node.type = placeholder->type;
									pending.parameters =
										concrete_member_body_parameters(
											placeholder,
											function_parameter_names_);
									pending.body_pos = body_pos;
									pending.class_type =
										pa11::record_type_for_scope(bare->scope);
									pending.constructor_body = true;
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
									enqueue_pending_member_body(bare->scope,
									                            pending);
								}
							}
						return true;
					}
	return false;
}

}  // namespace internal
}  // namespace pa12
