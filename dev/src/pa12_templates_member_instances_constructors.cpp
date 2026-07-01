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

bool constructor_member_specialization_owner_matches(Binding* binding,
                                                     Scope* owner)
{
	if (binding == NULL ||
	    owner == NULL ||
	    owner->kind != ScopeKind::Class)
		return false;
	if (binding->owner == owner)
		return true;
	if (binding->owner == NULL ||
	    binding->owner->kind != ScopeKind::Class)
		return false;
	TypePtr binding_record = pa11::record_type_for_scope(binding->owner);
	TypePtr owner_record = pa11::record_type_for_scope(owner);
	binding_record = binding_record.get() != NULL
		? pa11::strip_cv(binding_record) : TypePtr();
	owner_record = owner_record.get() != NULL
		? pa11::strip_cv(owner_record) : TypePtr();
	if (binding_record.get() == NULL ||
	    owner_record.get() == NULL ||
	    binding_record->kind != pa11::TypeKind::Record ||
	    owner_record->kind != pa11::TypeKind::Record)
		return false;
	return pa11::same_type(binding_record, owner_record);
}

bool Parser::clone_out_of_class_member_constructor_template(
	TypePtr bare,
	TemplateDeclaration* owner_declaration,
	const vector<TemplateArgument>& owner_arguments,
	TemplateDeclaration* declaration)
{
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
						return true;
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
									template_parameter_placeholder_type(
										parameter);
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
							copy_member_template_placeholder_state(
								placeholder,
								declaration->placeholder,
								function_parameter_names_,
								default_arguments_,
								false);
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
									owner_declaration,
									owner_arguments,
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
									Binding* specialization = spec->second;
									if (!constructor_member_specialization_owner_matches(
										    specialization,
										    bare->scope))
									{
										Binding* alias =
											specialization != NULL
											? specialization->aliased_binding
											: NULL;
										if (!constructor_member_specialization_owner_matches(
											    alias,
											    bare->scope))
											continue;
										specialization = alias;
									}
									clone_ptr->function_specializations[spec->first] =
										specialization;
									map<Binding*, TemplateDeclaration*>::iterator
										existing_spec =
											function_template_placeholders_.find(
												specialization);
									if (clone_ptr->has_definition ||
									    existing_spec ==
										    function_template_placeholders_.end() ||
									    existing_spec->second == NULL ||
									    !existing_spec->second->has_definition)
										function_template_placeholders_[specialization] =
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
							return true;
				}
	return false;
}

}  // namespace internal
}  // namespace pa12
