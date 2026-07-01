#include "pa12_internal.h"
#include "pa12_expr_semantics_support.h"
#include "pa12_templates_function_support.h"
#include <algorithm>
#include <sstream>
#include <stdexcept>
using namespace std;
namespace pa12 {
namespace internal {
bool has_token(const vector<Token>& tokens, size_t begin, size_t end, ETokenType type);
void merge_template_defaults(vector<TemplateParameterInfo>& target, const vector<TemplateParameterInfo>& source);
Binding* find_matching_function_template_placeholder(const map<Binding*, TemplateDeclaration*>& placeholders, Scope* scope, const string& name, TypePtr type, const vector<TemplateParameterInfo>& parameters);
void collect_template_parameter_placeholders(const vector<TemplateParameterInfo>& parameters, map<string, TypePtr>& parameter_types, map<string, TemplateArgument>& parameter_values);
set<string> collect_template_type_parameter_packs(const vector<TemplateParameterInfo>& parameters);
vector<string> function_parameter_names_from_tokens(const vector<Token>& tokens, size_t lparen, size_t end, bool include_this);
bool function_header_has_noexcept(const vector<Token>& tokens, size_t lparen, size_t end);
Scope* primary_class_template_scope(TemplateDeclaration* declaration);
size_t explicit_function_parameter_name_count(const vector<string>& names);
vector<pa11::TemplateInstanceArgument> template_instance_arguments(
	const vector<TemplateArgument>& arguments);
bool hosted_library_namespace_scope(Scope* scope);
bool owner_pattern_is_primary_parameter_list(
	const vector<TemplateArgument>& pattern,
	const vector<TemplateParameterInfo>& parameters);
bool skip_template_id_argument_tokens(const vector<Token>& tokens, size_t& pos);
bool template_parameter_lists_match(const vector<TemplateParameterInfo>& left,
                                    const vector<TemplateParameterInfo>& right);
namespace {
bool same_placeholder_template_instance_type(TypePtr left, TypePtr right);
bool same_placeholder_template_instance_arguments(
	const vector<pa11::TemplateInstanceArgument>& left,
	const vector<pa11::TemplateInstanceArgument>& right);
bool same_placeholder_template_instance_argument(
	const pa11::TemplateInstanceArgument& left,
	const pa11::TemplateInstanceArgument& right)
{
	if (left.kind != right.kind)
		return false;
	if (left.kind == pa11::TemplateInstanceArgumentKind::Type)
		return same_placeholder_template_instance_type(left.type,
		                                               right.type);
	if (left.kind == pa11::TemplateInstanceArgumentKind::Value)
		return left.dependent == right.dependent &&
		       left.value_negated == right.value_negated &&
		       left.value == right.value &&
		       left.value_name == right.value_name &&
		       left.value_owner_template_name ==
			       right.value_owner_template_name &&
		       left.value_member_name == right.value_member_name &&
		       same_placeholder_template_instance_type(left.type,
		                                               right.type) &&
		       same_placeholder_template_instance_arguments(
			       left.value_owner_template_arguments,
			       right.value_owner_template_arguments);
	if (left.kind == pa11::TemplateInstanceArgumentKind::Template)
		return left.template_name == right.template_name &&
		       left.dependent == right.dependent;
	if (left.pack.size() != right.pack.size())
		return false;
	for (size_t i = 0; i < left.pack.size(); ++i)
		if (!same_placeholder_template_instance_argument(left.pack[i],
		                                                 right.pack[i]))
			return false;
	return true;
}
bool same_placeholder_template_instance_arguments(
	const vector<pa11::TemplateInstanceArgument>& left,
	const vector<pa11::TemplateInstanceArgument>& right)
{
	if (left.size() != right.size())
		return false;
	for (size_t i = 0; i < left.size(); ++i)
		if (!same_placeholder_template_instance_argument(left[i], right[i]))
			return false;
	return true;
}
bool same_placeholder_template_argument_lists(
	const vector<vector<pa11::TemplateInstanceArgument> >& left,
	const vector<vector<pa11::TemplateInstanceArgument> >& right)
{
	if (left.size() != right.size())
		return false;
	for (size_t i = 0; i < left.size(); ++i)
		if (!same_placeholder_template_instance_arguments(left[i], right[i]))
			return false;
	return true;
}
bool same_placeholder_template_instance_type(TypePtr left, TypePtr right)
{
	if (left.get() == NULL || right.get() == NULL)
		return left.get() == right.get();
	if (!pa11::same_type(left, right))
		return false;
	if (left->is_dependent_typename || right->is_dependent_typename)
	{
		if (left->is_dependent_typename != right->is_dependent_typename ||
		    left->dependent_typename_qualified !=
			    right->dependent_typename_qualified ||
		    left->dependent_typename_template_id !=
			    right->dependent_typename_template_id ||
		    left->dependent_typename_decltype !=
			    right->dependent_typename_decltype ||
		    left->template_primary_name != right->template_primary_name)
			return false;
	}
	if (!same_placeholder_template_instance_arguments(left->template_arguments,
	                                                 right->template_arguments))
		return false;
	if (!same_placeholder_template_argument_lists(
		    left->dependent_typename_template_argument_lists,
		    right->dependent_typename_template_argument_lists))
		return false;
	if (left->kind == pa11::TypeKind::Function)
	{
		if (!same_placeholder_template_instance_type(left->base, right->base) ||
		    left->parameters.size() != right->parameters.size())
			return false;
		for (size_t i = 0; i < left->parameters.size(); ++i)
			if (!same_placeholder_template_instance_type(left->parameters[i],
			                                            right->parameters[i]))
				return false;
	}
	else if (left->kind == pa11::TypeKind::Cv ||
	         left->kind == pa11::TypeKind::Pointer ||
	         left->kind == pa11::TypeKind::LValueReference ||
	         left->kind == pa11::TypeKind::RValueReference ||
	         left->kind == pa11::TypeKind::Array)
		return same_placeholder_template_instance_type(left->base,
		                                               right->base);
	else if (left->kind == pa11::TypeKind::MemberPointer)
		return same_placeholder_template_instance_type(left->member_class,
		                                               right->member_class) &&
		       same_placeholder_template_instance_type(left->base,
		                                               right->base);
	return true;
}
bool hard_template_registration_error(const string& message)
{
	return message == "template argument kind mismatch" ||
	       message == "template pack argument kind mismatch" ||
	       message == "missing template argument" ||
	       message == "type template argument pack required" ||
	       message == "value template argument pack required";
}
Binding* find_matching_function(Scope* scope,
                                const string& name,
                                TypePtr type)
{
	if (scope == NULL)
		return NULL;
	map<string, vector<Binding*> >::iterator it = scope->members.find(name);
	if (it == scope->members.end())
		return NULL;
	for (size_t i = 0; i < it->second.size(); ++i)
	{
		Binding* binding = it->second[i];
		if (binding->kind == BindingKind::Function &&
		    pa11::same_type(binding->type, type))
			return binding;
	}
	return NULL;
}
}  // namespace
void Parser::register_explicit_function_template_specialization_binding(
	TemplateDeclaration* primary,
	Binding* specialization,
	const string& key,
	const vector<TemplateArgument>& full_args)
{
	specialization->is_explicit_specialization_member = true;
	primary->function_specializations[key] = specialization;
	function_template_placeholders_[specialization] = primary;
	function_template_specialization_arguments_[specialization] = full_args;
	if (specialization->function_specialization_symbol.empty())
		specialization->function_specialization_symbol =
			primary->class_template_member
			? (constructor_template_function_template_symbol(primary) ||
			   class_template_member_function_template_symbol(primary)
				   ? abi_function_template_specialization_symbol(
					 primary,
					 full_args,
					 specialization,
					 &declaration_tokens_)
				   : abi_binding_symbol(specialization,
					                    map<string, size_t>()))
			: abi_function_template_specialization_symbol(
				  primary,
				  full_args,
				  specialization,
				  &declaration_tokens_);
	if (primary->placeholder != NULL)
	{
		specialization->unwind_no = primary->placeholder->unwind_no;
		specialization->dynamic_exception_spec =
			primary->placeholder->dynamic_exception_spec;
		specialization->dynamic_exception_types =
			primary->placeholder->dynamic_exception_types;
	}
}
void Parser::register_explicit_function_template_specialization(
	TemplateDeclaration* declaration,
	const QualifiedName& qname,
	TypePtr declared_type,
	size_t save_pos,
	const vector<map<string, TypePtr> >& save_subst,
	const vector<map<string, TemplateArgument> >& save_value_subst)
{
	vector<TemplateDeclaration*> primaries = find_function_templates(qname);
	if (primaries.empty())
		throw runtime_error("function template specialization without primary");
	TemplateDeclaration* primary = primaries[0];
	vector<TemplateArgument> full_args;
	if (!deduce_function_template_target_type(primary,
	                                          declared_type,
	                                          qname.template_arguments,
	                                          full_args))
		throw runtime_error("function template specialization mismatch");
	string key = template_argument_key(full_args);
	template_type_substitutions_ = save_subst;
	template_value_substitutions_ = save_value_subst;
	pos_ = declaration->decl_begin;
	bool save_force = force_new_function_binding_;
	bool save_override = override_function_parameter_names_;
	vector<string> save_override_names = function_parameter_name_override_;
	map<Binding*, vector<string> >::iterator primary_names =
		function_parameter_names_.find(primary->placeholder);
	force_new_function_binding_ = true;
	if (primary_names != function_parameter_names_.end())
	{
		override_function_parameter_names_ = true;
		function_parameter_name_override_ = primary_names->second;
	}
	Node node;
	try
	{
		parse_simple_or_function_declaration(node, true);
	}
	catch (...)
	{
		force_new_function_binding_ = save_force;
		override_function_parameter_names_ = save_override;
		function_parameter_name_override_ = save_override_names;
		pos_ = save_pos;
		throw;
	}
	force_new_function_binding_ = save_force;
	override_function_parameter_names_ = save_override;
	function_parameter_name_override_ = save_override_names;
	Binding* specialization = NULL;
	if (node.line.compare(0, 19, "function-definition") == 0 &&
	    node.binding != NULL)
	{
		specialization = node.binding;
		register_explicit_function_template_specialization_binding(
			primary,
			specialization,
			key,
			full_args);
		add_child(root_, node);
	}
	else if (!node.children.empty() && node.children.back().binding != NULL)
	{
		specialization = node.children.back().binding;
		register_explicit_function_template_specialization_binding(
			primary,
			specialization,
			key,
			full_args);
		add_child(root_, node.children.back());
	}
	else
		throw runtime_error("function template specialization failed");
	for (size_t i = 0; specialization != NULL && i < primaries.size(); ++i)
	{
		TemplateDeclaration* candidate = primaries[i];
		if (candidate == primary ||
		    !same_function_template_declaration_family(primary, candidate))
			continue;
		vector<TemplateArgument> candidate_args;
		if (!deduce_function_template_target_type(candidate,
		                                          declared_type,
		                                          qname.template_arguments,
		                                          candidate_args))
			continue;
		string candidate_key = template_argument_key(candidate_args);
		candidate->function_specializations[candidate_key] = specialization;
	}
	pos_ = save_pos;
}
void Parser::register_function_template(TemplateDeclaration* declaration)
{ bool could_conversion_template = at(KW_OPERATOR) || at(KW_EXPLICIT) || at(KW_CONSTEXPR) || starts_attribute(); bool could_constructor_template = at_identifier() || at(OP_COLON2) || at(KW_EXPLICIT) || at(KW_CONSTEXPR) || starts_attribute(); if (could_conversion_template && register_conversion_function_template(declaration)) return; if (could_constructor_template && register_constructor_template(declaration)) return; declaration->kind = TemplateDeclarationKind::Function; map<string, TypePtr> parameter_types;
map<string, TemplateArgument> parameter_values; collect_template_parameter_placeholders(declaration->parameters, parameter_types, parameter_values); size_t save_pos = pos_;
vector<map<string, TypePtr> > save_subst = template_type_substitutions_; vector<map<string, TemplateArgument> > save_value_subst = template_value_substitutions_;
vector<set<string> > save_pack_subst = template_type_parameter_packs_; template_type_substitutions_.push_back(parameter_types); template_value_substitutions_.push_back(parameter_values);
template_type_parameter_packs_.push_back( collect_template_type_parameter_packs(declaration->parameters)); pos_ = declaration->decl_begin; if (at(KW_TEMPLATE)) { expect(KW_TEMPLATE);
vector<TemplateParameterInfo> nested_parameters = parse_template_parameter_clause(); unique_ptr<TemplateDeclaration> nested_holder( new TemplateDeclaration()); nested_holder->owner = current_scope();
nested_holder->lexical_scope = current_scope(); nested_holder->parameters = nested_parameters; nested_holder->decl_begin = pos_; nested_holder->decl_end = declaration->decl_end; nested_holder->outer_type_substitutions =
template_type_substitutions_; nested_holder->outer_value_substitutions = template_value_substitutions_; TemplateDeclaration* nested = nested_holder.get(); template_declarations_.push_back(std::move(nested_holder));
if (starts_class_key()) register_class_template(nested); else if (at(KW_USING)) register_alias_template(nested); else register_function_template(nested); template_type_substitutions_ = save_subst;
template_value_substitutions_ = save_value_subst; template_type_parameter_packs_ = save_pack_subst; pos_ = save_pos; return; } if (!declaration->parameters.empty() && register_dependent_qualified_member_function_template(declaration)) { template_type_substitutions_ = save_subst; template_value_substitutions_ = save_value_subst; template_type_parameter_packs_ = save_pack_subst; pos_ = save_pos; return; } try { DeclSpecs specs = parse_decl_specifier_seq(false);
TypePtr base = type_from_decl_specs(specs); Declarator declarator = parse_declarator(false); TypePtr type = apply_declarator(declarator, base); if (type->kind != pa11::TypeKind::Function) {
const QualifiedName& qname = declarator_name(declarator); if (qname.qualifier != NULL && at(OP_LPAREN) && has_token(tokens_, pos_, declaration->decl_end, OP_LBRACE)) { TypePtr owner_record =
pa11::record_type_for_scope(qname.qualifier); owner_record = owner_record.get() != NULL ? pa11::strip_cv(owner_record) : TypePtr(); map<const void*, TemplateDeclaration*>::iterator outer = owner_record.get() != NULL
? record_template_declarations_.find( owner_record.get()) : record_template_declarations_.end(); TemplateDeclaration* owner_template = outer != record_template_declarations_.end() ? outer->second
: find_class_template(qname.qualifier->parent, qname.qualifier->name); if (owner_template != NULL) { declaration->kind = TemplateDeclarationKind::Function; declaration->owner = qname.qualifier;
declaration->name = qname.name; declaration->class_template_member = template_parameter_lists_match( declaration->parameters, owner_template->parameters) || !declaration->outer_type_substitutions.empty(); declaration->generic_function_type = pa11::make_function(
pa11::make_fundamental(FT_VOID), vector<TypePtr>(), false); declaration->has_definition = true; vector<TemplateDeclaration*>& members = member_function_templates_[make_pair( owner_template, qname.name)];
add_member_function_template(members, declaration); template_type_substitutions_ = save_subst; template_value_substitutions_ = save_value_subst;
template_type_parameter_packs_ = save_pack_subst; pos_ = save_pos; return; } } Scope* target = qname.qualifier != NULL ? qname.qualifier : declaration->owner; declaration->owner = target; declaration->name = qname.name;
if (qname.has_template_arguments) { declaration->class_specialization = true; declaration->class_specialization_pattern = qname.template_arguments; } template_type_substitutions_ = save_subst;
template_value_substitutions_ = save_value_subst; template_type_parameter_packs_ = save_pack_subst; pos_ = save_pos; if (declaration->parameters.empty() && target->kind == ScopeKind::Class && qname.qualifier != NULL) {
vector<Binding*> found = lookup_qualified_set(target, qname.name, pa11::LOOKUP_VALUE); Binding* member = NULL; for (size_t i = 0; i < found.size(); ++i) { Binding* candidate = found[i];
if (candidate->kind == BindingKind::Variable && pa11::same_type(candidate->type, type)) { member = candidate; break; } } if (member != NULL) { pos_ = declaration->decl_begin; Node node;
parse_simple_or_function_declaration(node, true); member->is_template_static_member_definition = false; if (node.line.empty()) { for (size_t i = 0; i < node.children.size(); ++i) add_child(root_, node.children[i]); }
else add_child(root_, node); TypePtr owner_record = pa11::record_type_for_scope(target); owner_record = owner_record.get() != NULL ? pa11::strip_cv(owner_record) : TypePtr();
map<const void*, TemplateDeclaration*>::iterator outer = owner_record.get() != NULL ? record_template_declarations_.find( owner_record.get()) : record_template_declarations_.end();
map<const void*, vector<TemplateArgument> >::iterator owner_args = owner_record.get() != NULL ? record_template_arguments_.find(owner_record.get()) : record_template_arguments_.end();
if (outer != record_template_declarations_.end() && owner_args != record_template_arguments_.end()) { string key = template_argument_key(owner_args->second) + "::" + qname.name; map<pair<TemplateDeclaration*, string>,
vector<TemplateDeclaration*> >::iterator templates = member_variable_templates_.find( make_pair(outer->second, qname.name)); if (templates != member_variable_templates_.end()) for (size_t i = 0;
i < templates->second.size(); ++i) templates->second[i]-> emitted_variable_specializations.insert( key); } pos_ = save_pos; return; } } if (register_static_member_variable_template(declaration)) return;
declaration->kind = TemplateDeclarationKind::Variable; vector<TemplateDeclaration*>& variable_family = variable_templates_[target][qname.name]; if (declaration->class_specialization)
for (size_t i = 0; i < variable_family.size(); ++i) if (!variable_family[i]->class_specialization) variable_template_specializations_.erase( variable_family[i]); variable_family.push_back(declaration); return; }
const QualifiedName& qname = declarator_name(declarator); Scope* friend_class_scope = specs.friend_decl && declaration->owner != NULL && declaration->owner->kind == ScopeKind::Class ? declaration->owner : NULL;
Scope* target = qname.qualifier != NULL ? qname.qualifier : (friend_class_scope != NULL ? nearest_namespace_scope(friend_class_scope) : declaration->owner); if (declaration->parameters.empty()) {
if (target->kind == ScopeKind::Class && qname.qualifier != NULL) { Binding* member = find_matching_function(target, qname.name, type); if (member == NULL) { TypePtr member_type = make_member_function_type(target, type);
member = find_matching_function(target, qname.name, member_type); } if (member != NULL && function_template_placeholders_.find(member) == function_template_placeholders_.end()) {
template_type_substitutions_ = save_subst; template_value_substitutions_ = save_value_subst; template_type_parameter_packs_ = save_pack_subst; pos_ = declaration->decl_begin;
bool save_force = force_new_function_binding_; force_new_function_binding_ = false; Node node; try { parse_simple_or_function_declaration(node, true); } catch (...) { force_new_function_binding_ = save_force;
pos_ = save_pos; throw; } force_new_function_binding_ = save_force; if (node.line.compare(0, 19, "function-definition") == 0) add_child(root_, node); else if (!node.children.empty())
add_child(root_, node.children.back()); pos_ = save_pos; return; } } template_type_parameter_packs_ = save_pack_subst;
register_explicit_function_template_specialization(declaration, qname, type, save_pos, save_subst, save_value_subst); return; } declaration->owner = target; declaration->friend_class_scope = friend_class_scope;
declaration->hidden_friend = friend_class_scope != NULL && qname.qualifier == NULL; declaration->name = qname.name; Binding* placeholder = NULL; bool static_member_definition = false;
if (target->kind == ScopeKind::Class && qname.qualifier != NULL) { placeholder = find_matching_function_template_placeholder( function_template_placeholders_, target, qname.name, type, declaration->parameters);
static_member_definition = placeholder != NULL && placeholder->is_static_member; } if (target->kind == ScopeKind::Class && !specs.static_decl && !static_member_definition) type = make_member_function_type(target, type);
declaration->generic_function_type = type; declaration->has_definition = has_token(tokens_, pos_, declaration->decl_end, OP_LBRACE); if (placeholder == NULL) placeholder = find_matching_function_template_placeholder(
function_template_placeholders_, target, qname.name, type, declaration->parameters); TemplateDeclaration* previous_declaration = NULL; if (placeholder != NULL) { map<Binding*, TemplateDeclaration*>::iterator previous =
function_template_placeholders_.find(placeholder); if (previous != function_template_placeholders_.end()) previous_declaration = previous->second; } if (placeholder != NULL && previous_declaration != NULL &&
previous_declaration->has_definition && declaration->has_definition && !same_placeholder_template_instance_type( previous_declaration->generic_function_type, type)) { placeholder = NULL; previous_declaration = NULL; }
if (placeholder == NULL) { placeholder = add_value(target, BindingKind::Function, qname.name, type); placeholder->is_hidden_friend = declaration->hidden_friend; } else if (!declaration->hidden_friend)
placeholder->is_hidden_friend = false; placeholder->is_static_member = target->kind == ScopeKind::Class && (specs.static_decl || static_member_definition); declaration->placeholder = placeholder;
const Suffix* primary_suffix = declarator_function_suffix(declarator); placeholder->is_constexpr = placeholder->is_constexpr || specs.constexpr_decl; placeholder->is_declared_inline = placeholder->is_declared_inline || specs.inline_decl || specs.constexpr_decl; placeholder->is_private = target->kind == ScopeKind::Class && !class_private_access_.empty() && class_private_access_.back(); placeholder->is_protected_member = target->kind == ScopeKind::Class && !class_protected_access_.empty() && class_protected_access_.back(); if (primary_suffix != NULL) { placeholder->unwind_no = primary_suffix->noexcept_decl; placeholder->dynamic_exception_spec = primary_suffix->dynamic_exception_spec; placeholder->dynamic_exception_types = primary_suffix->dynamic_exception_types; placeholder->ref_qualifier = primary_suffix->ref_qualifier; } if (primary_suffix != NULL) { vector<string> names; vector<Expr> defaults; vector<bool> pack_expansions; if (target->kind == ScopeKind::Class && !placeholder->is_static_member) {
defaults.push_back(Expr()); pack_expansions.push_back(false); } for (size_t i = 0; i < primary_suffix->parameters.size(); ++i) { if (primary_suffix->parameters[i].type.get() != NULL || !primary_suffix->parameters[i].name.empty())
	names.push_back(primary_suffix->parameters[i].name); defaults.push_back( primary_suffix->parameters[i].default_value); pack_expansions.push_back(primary_suffix->parameters[i].is_pack_expansion); } map<Binding*, vector<string> >::const_iterator old_names =
	function_parameter_names_.find(placeholder); if (old_names != function_parameter_names_.end()) { vector<string> merged = old_names->second; size_t offset = placeholder->owner != NULL &&
placeholder->owner->kind == ScopeKind::Class && !placeholder->is_static_member && merged.size() == names.size() + 1 ? 1 : 0; if (merged.size() < names.size() + offset) merged.resize(names.size() + offset);
for (size_t i = 0; i < names.size(); ++i) if (!names[i].empty() || merged[i + offset].empty()) merged[i + offset] = names[i]; names = merged; } else if (target->kind == ScopeKind::Class && qname.qualifier != NULL) {
vector<Binding*> existing_functions = lookup_qualified_set(target, qname.name, pa11::LOOKUP_FUNCTION); for (size_t fi = 0; fi < existing_functions.size(); ++fi) { map<Binding*, vector<string> >::const_iterator
existing_names = function_parameter_names_.find( existing_functions[fi]); if (existing_names == function_parameter_names_.end() || existing_names->second.size() != names.size()) continue;
for (size_t ni = 0; ni < names.size(); ++ni) if (names[ni].empty()) names[ni] = existing_names->second[ni]; break; } } function_parameter_names_[placeholder] = names; placeholder->function_parameter_names = names; declaration->function_parameter_names = names; declaration->function_parameter_pack_expansions = pack_expansions;
map<Binding*, vector<Expr> >::const_iterator old_defaults = default_arguments_.find(placeholder); if (old_defaults != default_arguments_.end()) { vector<Expr> merged = defaults;
if (merged.size() < old_defaults->second.size()) merged.resize(old_defaults->second.size()); for (size_t i = 0; i < old_defaults->second.size(); ++i) if (!merged[i].valid && old_defaults->second[i].valid)
merged[i] = old_defaults->second[i]; defaults = merged; } default_arguments_[placeholder] = default_arguments_for_binding(placeholder, defaults); } if (previous_declaration != NULL) merge_template_defaults(declaration->parameters,
previous_declaration->parameters); function_template_placeholders_[placeholder] = declaration; if (friend_class_scope != NULL) add_friend_function(friend_class_scope, placeholder);
vector<TemplateDeclaration*>& overloads = function_templates_[target][qname.name]; if (find(overloads.begin(), overloads.end(), declaration) == overloads.end()) overloads.push_back(declaration);
TypePtr owner_record = pa11::record_type_for_scope(target); if (owner_record.get() != NULL) { map<const void*, TemplateDeclaration*>::iterator outer =
record_template_declarations_.find(pa11::strip_cv(owner_record).get()); TemplateDeclaration* owner_template = outer != record_template_declarations_.end() ? outer->second
: find_class_template(target->parent, target->name); if (qname.qualifier != NULL && owner_template != NULL && (template_parameter_lists_match(declaration->parameters, owner_template->parameters) || !declaration->outer_type_substitutions.empty()))
declaration->class_template_member = true; if (owner_template != NULL) { vector<TemplateDeclaration*>& members = member_function_templates_[make_pair(owner_template, qname.name)];
add_member_function_template(members, declaration); } } } catch (const exception& err) { string message = err.what(); bool hard_registration_error =
hard_template_registration_error(message); template_type_substitutions_ = save_subst; template_value_substitutions_ = save_value_subst; template_type_parameter_packs_ = save_pack_subst; pos_ = save_pos;
if (could_constructor_template && register_constructor_template(declaration)) return; if (register_dependent_nested_constructor_template(declaration)) return; if (register_dependent_qualified_conversion_function_template( declaration)) return;
if (register_dependent_qualified_member_function_template( declaration)) return; if (register_static_member_variable_template(declaration)) return; if (hard_registration_error) throw;
declaration->kind = TemplateDeclarationKind::Variable; } template_type_substitutions_ = save_subst; template_value_substitutions_ = save_value_subst; template_type_parameter_packs_ = save_pack_subst; pos_ = save_pos; }
}  // namespace internal
}  // namespace pa12
