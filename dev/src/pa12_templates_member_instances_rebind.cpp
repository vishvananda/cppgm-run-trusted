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
TypePtr remap_template_parameter_names(TypePtr type, const map<string, string>& names);
map<string, string> template_parameter_name_map(const vector<TemplateParameterInfo>& from, const vector<TemplateParameterInfo>& to);
TypePtr rebind_nested_constructor_self_type(TypePtr type, TypePtr current);

bool member_specialization_owner_matches(Binding* binding, Scope* owner)
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

bool Parser::out_of_class_member_template_definition_applies(
	TypePtr bare,
	TemplateDeclaration* declaration) const
{
	if (bare.get() == NULL ||
	    bare->scope == NULL ||
	    declaration == NULL ||
	    !declaration->has_definition ||
	    declaration->constructor_template)
		return false;
	bool dependent_qualified_conversion_definition =
		declaration->name == "operator " &&
		(!declaration->outer_type_substitutions.empty() ||
		 !declaration->outer_value_substitutions.empty());
	bool dependent_qualified_member_definition =
		declaration->class_template_member &&
		declaration->generic_function_type.get() != NULL &&
		declaration->generic_function_type->kind ==
			pa11::TypeKind::Function &&
		declaration->generic_function_type->parameters.empty();
	bool substituted_class_template_member_definition =
		declaration->class_template_member &&
		(!declaration->outer_type_substitutions.empty() ||
		 !declaration->outer_value_substitutions.empty());
	return (!declaration->outer_type_substitutions.empty() ||
	        !declaration->outer_value_substitutions.empty() ||
	        dependent_qualified_member_definition) &&
	       (declaration->lexical_scope != declaration->owner ||
	        dependent_qualified_conversion_definition ||
	        dependent_qualified_member_definition ||
	        substituted_class_template_member_definition);
}

vector<Binding*> Parser::out_of_class_member_template_rebind_candidates(
	TypePtr bare,
	const string& name) const
{
	vector<Binding*> candidates;
	if (bare.get() == NULL || bare->scope == NULL)
		return candidates;
	if (name == "operator ")
	{
		for (map<string, vector<Binding*> >::const_iterator mit =
			     bare->scope->members.begin();
		     mit != bare->scope->members.end();
		     ++mit)
			if (mit->first.compare(0, 9, "operator ") == 0)
				candidates.insert(candidates.end(),
				                  mit->second.begin(),
				                  mit->second.end());
	}
	else
	{
		map<string, vector<Binding*> >::const_iterator found =
			bare->scope->members.find(name);
		if (found != bare->scope->members.end())
			candidates = found->second;
	}
	return candidates;
}

bool Parser::ordinary_out_of_class_member_definition(
	TemplateDeclaration* declaration,
	Binding* placeholder,
	bool has_existing_template) const
{
	return !has_existing_template &&
	       declaration->has_definition &&
	       declaration->generic_function_type.get() != NULL &&
	       declaration->generic_function_type->kind ==
		       pa11::TypeKind::Function &&
	       declaration->generic_function_type->parameters.empty() &&
	       placeholder != NULL &&
	       placeholder->kind == BindingKind::Function;
}

bool Parser::substituted_member_template_parameter_lists_match(
	TemplateDeclaration* existing_declaration,
	TemplateDeclaration* declaration,
	const map<string, TypePtr>& subst,
	const map<string, TemplateArgument>& value_subst,
	const set<string>& pack_subst)
{
	if (existing_declaration == NULL)
		return false;
	if (template_parameter_lists_match(existing_declaration->parameters,
	                                   declaration->parameters))
		return true;
	vector<TemplateParameterInfo> substituted_parameters =
		declaration->parameters;
	vector<map<string, TypePtr> > save_subst = template_type_substitutions_;
	vector<map<string, TemplateArgument> > save_value_subst =
		template_value_substitutions_;
	vector<set<string> > save_pack_subst = template_type_parameter_packs_;
	template_type_substitutions_.push_back(subst);
	template_value_substitutions_.push_back(value_subst);
	template_type_parameter_packs_.push_back(pack_subst);
	try
	{
		for (size_t p = 0; p < substituted_parameters.size(); ++p)
			if (substituted_parameters[p].kind ==
				    TemplateParameterKind::NonType &&
			    substituted_parameters[p].type.get() != NULL)
				substituted_parameters[p].type =
					substitute_template_type(
						substituted_parameters[p].type);
	}
	catch (const exception&)
	{
	}
	template_type_substitutions_ = save_subst;
	template_value_substitutions_ = save_value_subst;
	template_type_parameter_packs_ = save_pack_subst;
	TemplateMatchParserScope match_parser_scope(this);
	return template_parameter_lists_match(existing_declaration->parameters,
	                                      substituted_parameters);
}

bool Parser::rebind_member_template_candidate_allowed(
	bool ordinary_member_definition,
	TemplateDeclaration* existing_declaration,
	TemplateDeclaration* declaration,
	Scope* owner,
	bool parameter_lists_match) const
{
	if (ordinary_member_definition)
		return true;
	if (existing_declaration == NULL)
		return false;
	if (existing_declaration == declaration)
		return false;
	if (existing_declaration->decl_begin == declaration->decl_begin &&
	    existing_declaration->owner == owner)
		return false;
	return parameter_lists_match;
}

bool Parser::active_equivalent_member_body_replay(Binding* placeholder) const
{
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
			return true;
		if (replay == NULL ||
		    placeholder == NULL ||
		    replay->owner != placeholder->owner ||
		    replay->name != placeholder->name ||
		    replay->type.get() == NULL ||
		    placeholder->type.get() == NULL ||
		    !pa11::same_type(replay->type, placeholder->type))
			continue;
		return true;
	}
	return false;
}

void Parser::erase_rebound_member_body(Binding* placeholder)
{
	function_bodies_.erase(placeholder);
	for (size_t extra = 0; extra < extra_lowir_nodes_.size();)
	{
		if (extra_lowir_nodes_[extra].binding == placeholder)
			extra_lowir_nodes_.erase(extra_lowir_nodes_.begin() + extra);
		else
			++extra;
	}
}

bool Parser::member_body_already_available(Binding* placeholder) const
{
	if (function_bodies_.find(placeholder) != function_bodies_.end())
		return true;
	if (active_function_body_replays_.count(placeholder) != 0)
		return true;
	for (size_t extra = 0; extra < extra_lowir_nodes_.size(); ++extra)
		if (extra_lowir_nodes_[extra].binding == placeholder)
			return true;
	return false;
}

bool Parser::pending_member_body_already_enqueued(Scope* owner,
                                                  Binding* placeholder) const
{
	map<Scope*, vector<PendingFunctionBody> >::const_iterator pending_set =
		pending_member_bodies_.find(owner);
	if (pending_set == pending_member_bodies_.end())
		return false;
	for (size_t pending_i = 0; pending_i < pending_set->second.size(); ++pending_i)
		if (pending_set->second[pending_i].function == placeholder)
			return true;
	return false;
}

PendingFunctionBody Parser::make_rebound_ordinary_member_body(
	TypePtr bare,
	TemplateDeclaration* owner_declaration,
	TemplateDeclaration* declaration,
	Binding* placeholder,
	size_t body_pos,
	const map<string, TypePtr>& subst,
	const map<string, TemplateArgument>& value_subst,
	const set<string>& pack_subst)
{
	PendingFunctionBody pending;
	pending.function = placeholder;
	pending.node = Node(
		"function-definition " +
		qualified_decl_name(placeholder) + " " +
		pa11::describe_type(placeholder->type));
	pending.node.binding = placeholder;
	pending.node.type = placeholder->type;
	if (member_parameter_names_have_non_this(
		    declaration->function_parameter_names))
	{
		function_parameter_names_[placeholder] =
			declaration->function_parameter_names;
		placeholder->function_parameter_names =
			declaration->function_parameter_names;
	}
	pending.parameters =
		concrete_member_body_parameters(placeholder, function_parameter_names_);
	pending.body_pos = body_pos;
	pending.class_type = pa11::record_type_for_scope(bare->scope);
	pending.scopes.clear();
	pending.scopes.push_back(declaration->lexical_scope != NULL
	                         ? declaration->lexical_scope
	                         : owner_declaration->owner);
	pending.friend_class_scopes = active_friend_class_scopes_;
	pending.type_substitutions = template_type_substitutions_;
	pending.value_substitutions = template_value_substitutions_;
	pending.pack_substitutions = template_type_parameter_packs_;
	pending.type_substitutions.push_back(subst);
	pending.value_substitutions.push_back(value_subst);
	pending.pack_substitutions.push_back(pack_subst);
	return pending;
}

bool Parser::rebind_ordinary_out_of_class_member_definition(
	TypePtr bare,
	bool object_root,
	TemplateDeclaration* owner_declaration,
	TemplateDeclaration* declaration,
	Binding* placeholder,
	const map<string, TypePtr>& subst,
	const map<string, TemplateArgument>& value_subst,
	const set<string>& pack_subst)
{
	placeholder->is_inline_definition = true;
	size_t body_pos =
		function_body_start(tokens_, declaration->decl_begin, declaration->decl_end);
	if (body_pos == declaration->decl_end)
		return false;
	if (active_equivalent_member_body_replay(placeholder))
		return true;
	map<Binding*, Node>::iterator existing_body =
		function_bodies_.find(placeholder);
	if (existing_body != function_bodies_.end() &&
	    !function_body_signature_matches(placeholder, existing_body->second))
		erase_rebound_member_body(placeholder);
	bool already_have_body = member_body_already_available(placeholder);
	if (already_have_body && declaration->class_specialization)
	{
		erase_rebound_member_body(placeholder);
		already_have_body = false;
	}
	if (already_have_body)
	{
		if (object_root)
		{
			placeholder->is_object_root = true;
			ensure_function_body_extra_node(placeholder);
		}
		return true;
	}
	PendingFunctionBody pending =
		make_rebound_ordinary_member_body(bare,
		                                  owner_declaration,
		                                  declaration,
		                                  placeholder,
		                                  body_pos,
		                                  subst,
		                                  value_subst,
		                                  pack_subst);
	if (!object_root)
	{
		if (!pending_member_body_already_enqueued(bare->scope, placeholder))
			enqueue_pending_member_body(bare->scope, pending);
		return true;
	}
	try
	{
		bool parsed = parse_pending_member_body_now(pending);
		placeholder->is_object_root = true;
		if (parsed)
			ensure_function_body_extra_node(placeholder);
		else
			enqueue_pending_member_body(bare->scope, pending);
		return true;
	}
	catch (const exception&)
	{
		if (hosted_compatibility_)
		{
			placeholder->is_object_root = true;
			enqueue_pending_member_body(bare->scope, pending);
			return true;
		}
	}
	return false;
}

bool Parser::deduce_rebound_member_template_signature(
	TemplateDeclaration* declaration,
	TemplateDeclaration* existing_declaration,
	Binding* placeholder,
	const map<string, TypePtr>& subst,
	const map<string, TemplateArgument>& value_subst,
	const set<string>& pack_subst,
	bool& dependent_definition_placeholder,
	TypePtr& generic_for_match,
	map<string, TemplateArgument>& signature_deduced)
{
	dependent_definition_placeholder =
		declaration->has_definition &&
		declaration->generic_function_type.get() != NULL &&
		declaration->generic_function_type->kind ==
			pa11::TypeKind::Function &&
		declaration->generic_function_type->parameters.empty() &&
		existing_declaration->generic_function_type.get() != NULL &&
		existing_declaration->generic_function_type->kind ==
			pa11::TypeKind::Function;
	if (dependent_definition_placeholder &&
	    !ordinary_member_definition_matches_placeholder(declaration,
	                                                    placeholder,
	                                                    tokens_))
		return false;
	generic_for_match = dependent_definition_placeholder
		? existing_declaration->generic_function_type
		: declaration->generic_function_type;
	TypePtr matched_type;
	vector<map<string, TypePtr> > save_subst = template_type_substitutions_;
	vector<map<string, TemplateArgument> > save_value_subst =
		template_value_substitutions_;
	vector<set<string> > save_pack_subst = template_type_parameter_packs_;
	try
	{
		template_type_substitutions_.push_back(subst);
		template_value_substitutions_.push_back(value_subst);
		template_type_parameter_packs_.push_back(pack_subst);
		matched_type =
			substitute_function_template_type(declaration, generic_for_match);
	}
	catch (const runtime_error&)
	{
		template_type_substitutions_ = save_subst;
		template_value_substitutions_ = save_value_subst;
		template_type_parameter_packs_ = save_pack_subst;
		return false;
	}
	template_type_substitutions_ = save_subst;
	template_value_substitutions_ = save_value_subst;
	template_type_parameter_packs_ = save_pack_subst;
	if (dependent_definition_placeholder)
		return true;
	return matched_type.get() != NULL &&
	       placeholder->type.get() != NULL &&
	       match_template_type_pattern(matched_type,
	                                   placeholder->type,
	                                   signature_deduced,
	                                   record_template_arguments_);
}

void Parser::copy_previous_member_template_state(
	Binding* placeholder,
	TemplateDeclaration* previous_placeholder_declaration)
{
	if (previous_placeholder_declaration == NULL ||
	    previous_placeholder_declaration->placeholder == NULL)
		return;
	Binding* previous = previous_placeholder_declaration->placeholder;
	map<Binding*, vector<string> >::const_iterator previous_names =
		function_parameter_names_.find(previous);
	if (previous_names != function_parameter_names_.end())
	{
		function_parameter_names_[placeholder] = previous_names->second;
		placeholder->function_parameter_names = previous_names->second;
	}
	map<Binding*, vector<Expr> >::const_iterator previous_defaults =
		default_arguments_.find(previous);
	if (previous_defaults != default_arguments_.end())
		default_arguments_[placeholder] =
			default_arguments_for_binding(placeholder,
			                              previous_defaults->second);
}

TemplateDeclaration* Parser::create_rebound_member_template_clone(
	TypePtr bare,
	TemplateDeclaration* owner_declaration,
	const vector<TemplateArgument>& owner_arguments,
	TemplateDeclaration* declaration,
	Binding* placeholder,
	TemplateDeclaration* previous_placeholder_declaration,
	bool dependent_definition_placeholder,
	TypePtr generic_for_match,
	const map<string, TypePtr>& subst,
	const map<string, TemplateArgument>& value_subst)
{
	unique_ptr<TemplateDeclaration> clone(new TemplateDeclaration(*declaration));
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
					previous_placeholder_declaration->parameters,
					clone->parameters)
				: map<string, string>());
		if (previous_placeholder_declaration != NULL &&
		    previous_placeholder_declaration->constructor_template)
			clone->constructor_template = true;
	}
	clone->function_specializations.clear();
	clone->completing_specializations.clear();
	clone->emitted_variable_specializations.clear();
	make_concrete_outer_substitutions(declaration,
	                                  owner_declaration,
	                                  owner_arguments,
	                                  subst,
	                                  value_subst,
	                                  clone->outer_type_substitutions,
	                                  clone->outer_value_substitutions);
	TemplateDeclaration* clone_ptr = clone.get();
	template_declarations_.push_back(std::move(clone));
	return clone_ptr;
}

void Parser::copy_rebound_member_template_specializations(
	TemplateDeclaration* clone_ptr,
	TemplateDeclaration* previous_placeholder_declaration,
	Scope* owner)
{
	if (previous_placeholder_declaration == NULL ||
	    previous_placeholder_declaration == clone_ptr)
		return;
	for (map<string, Binding*>::const_iterator spec =
		     previous_placeholder_declaration->function_specializations.begin();
	     spec != previous_placeholder_declaration->function_specializations.end();
	     ++spec)
	{
		Binding* specialization = spec->second;
		if (!member_specialization_owner_matches(specialization, owner))
		{
			Binding* alias = specialization != NULL
				? specialization->aliased_binding : NULL;
			if (!member_specialization_owner_matches(alias, owner))
				continue;
			specialization = alias;
		}
		clone_ptr->function_specializations[spec->first] = specialization;
		function_template_placeholders_[specialization] = clone_ptr;
	}
}

void Parser::register_rebound_member_template_clone(
	Scope* owner,
	TemplateDeclaration* declaration,
	Binding* placeholder,
	TemplateDeclaration* clone_ptr)
{
	function_template_placeholders_[placeholder] = clone_ptr;
	vector<TemplateDeclaration*>& rebound_templates =
		function_templates_[owner][declaration->name];
	if (find(rebound_templates.begin(), rebound_templates.end(), clone_ptr) ==
	    rebound_templates.end())
		rebound_templates.push_back(clone_ptr);
}

void Parser::remember_rebound_member_template_specialization_arguments(
	Binding* placeholder,
	TemplateDeclaration* clone_ptr,
	const map<string, TemplateArgument>& signature_deduced)
{
	if (function_template_candidate_instantiation_depth_ != 0 ||
	    placeholder->type.get() == NULL ||
	    type_is_template_dependent(placeholder->type))
		return;
	vector<TemplateArgument> specialization_args;
	for (size_t a = 0; a < clone_ptr->parameters.size(); ++a)
	{
		const string& parameter_name = clone_ptr->parameters[a].name;
		map<string, TemplateArgument>::const_iterator deduced =
			signature_deduced.find(parameter_name);
		if (parameter_name.empty() ||
		    deduced == signature_deduced.end())
			return;
		specialization_args.push_back(deduced->second);
	}
	function_template_specialization_arguments_[placeholder] =
		specialization_args;
}

bool Parser::rebind_member_template_placeholder_candidate(
	TypePtr bare,
	TemplateDeclaration* owner_declaration,
	const vector<TemplateArgument>& owner_arguments,
	TemplateDeclaration* declaration,
	Binding* placeholder,
	TemplateDeclaration* existing_declaration,
	const map<string, TypePtr>& subst,
	const map<string, TemplateArgument>& value_subst,
	const set<string>& pack_subst)
{
	TemplateMatchParserScope match_scope(this);
	bool dependent_definition_placeholder = false;
	TypePtr generic_for_match;
	map<string, TemplateArgument> signature_deduced;
	if (!deduce_rebound_member_template_signature(declaration,
	                                              existing_declaration,
	                                              placeholder,
	                                              subst,
	                                              value_subst,
	                                              pack_subst,
	                                              dependent_definition_placeholder,
	                                              generic_for_match,
	                                              signature_deduced))
		return false;
	copy_previous_member_template_state(placeholder, existing_declaration);
	TemplateDeclaration* clone_ptr =
		create_rebound_member_template_clone(bare,
		                                     owner_declaration,
		                                     owner_arguments,
		                                     declaration,
		                                     placeholder,
		                                     existing_declaration,
		                                     dependent_definition_placeholder,
		                                     generic_for_match,
		                                     subst,
		                                     value_subst);
	copy_rebound_member_template_specializations(clone_ptr,
	                                             existing_declaration,
	                                             bare->scope);
	register_rebound_member_template_clone(bare->scope,
	                                       declaration,
	                                       placeholder,
	                                       clone_ptr);
	remember_rebound_member_template_specialization_arguments(
		placeholder,
		clone_ptr,
		signature_deduced);
	return true;
}

bool Parser::rebind_out_of_class_member_template_definition(
	TypePtr bare,
	bool object_root,
	TemplateDeclaration* owner_declaration,
	const vector<TemplateArgument>& owner_arguments,
	TemplateDeclaration* declaration)
{
	if (!out_of_class_member_template_definition_applies(bare, declaration))
		return false;
	bool rebound_out_of_class_member_template = false;
	bool handled_ordinary_member_definition = false;
	vector<Binding*> candidate_placeholders =
		out_of_class_member_template_rebind_candidates(bare,
		                                               declaration->name);
	for (size_t j = 0; j < candidate_placeholders.size(); ++j)
	{
		Binding* placeholder = candidate_placeholders[j];
		map<Binding*, TemplateDeclaration*>::iterator existing =
			function_template_placeholders_.find(placeholder);
		TemplateDeclaration* existing_declaration =
			existing != function_template_placeholders_.end()
			? existing->second : NULL;
		bool ordinary_member_definition =
			ordinary_out_of_class_member_definition(
				declaration,
				placeholder,
				existing_declaration != NULL);
		if (ordinary_member_definition &&
		    !ordinary_member_definition_matches_placeholder(declaration,
		                                                    placeholder,
		                                                    tokens_))
			continue;
		if (ordinary_member_definition &&
		    candidate_placeholders.size() > 1 &&
		    hosted_library_function(placeholder) &&
		    placeholder->is_virtual)
		{
			handled_ordinary_member_definition = true;
			continue;
		}
		map<string, TypePtr> subst;
		map<string, TemplateArgument> value_subst;
		set<string> pack_subst;
		build_owner_template_substitutions(owner_arguments,
		                                   owner_declaration,
		                                   subst,
		                                   value_subst,
		                                   pack_subst);
		bool parameter_lists_match =
			ordinary_member_definition ||
			substituted_member_template_parameter_lists_match(
				existing_declaration,
				declaration,
				subst,
				value_subst,
				pack_subst);
		if (!rebind_member_template_candidate_allowed(
			    ordinary_member_definition,
			    existing_declaration,
			    declaration,
			    bare->scope,
			    parameter_lists_match))
			continue;
		if (ordinary_member_definition)
		{
			if (rebind_ordinary_out_of_class_member_definition(
				    bare,
				    object_root,
				    owner_declaration,
				    declaration,
				    placeholder,
				    subst,
				    value_subst,
				    pack_subst))
				handled_ordinary_member_definition = true;
			continue;
		}
		if (rebind_member_template_placeholder_candidate(bare,
		                                                 owner_declaration,
		                                                 owner_arguments,
		                                                 declaration,
		                                                 placeholder,
		                                                 existing_declaration,
		                                                 subst,
		                                                 value_subst,
		                                                 pack_subst))
			rebound_out_of_class_member_template = true;
	}
	return rebound_out_of_class_member_template ||
	       handled_ordinary_member_definition;
}

}  // namespace internal
}  // namespace pa12
