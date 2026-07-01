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

void Parser::instantiate_member_function_template_specialization(
	TypePtr bare,
	bool object_root,
	TemplateDeclaration* owner_declaration,
	const vector<TemplateArgument>& owner_arguments,
	TemplateDeclaration* declaration)
{
					string key = template_argument_key(owner_arguments);
				if (declaration->completing_specializations.count(key) != 0)
					return;
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
								return;
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
							return;
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
									assign_member_template_alias_state(alias,
									                                   binding);
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
									merge_member_template_alias_state(concrete,
									                                  binding);
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

}  // namespace internal
}  // namespace pa12
