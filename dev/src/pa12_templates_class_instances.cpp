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

namespace {

bool hosted_streambuf_iterator_template(const TemplateDeclaration* declaration)
{
	if (declaration == NULL ||
	    (declaration->name != "istreambuf_iterator" &&
	     declaration->name != "ostreambuf_iterator"))
		return false;
	for (Scope* scope = declaration->owner;
	     scope != NULL;
	     scope = scope->parent)
		if (scope->kind == ScopeKind::Namespace && scope->name == "std")
			return true;
	return false;
}

bool hosted_shared_ptr_template(const TemplateDeclaration* declaration)
{
	if (declaration == NULL ||
	    (declaration->name != "shared_ptr" &&
	     declaration->name != "__shared_ptr"))
		return false;
	for (Scope* scope = declaration->owner;
	     scope != NULL;
	     scope = scope->parent)
		if (scope->kind == ScopeKind::Namespace && scope->name == "std")
			return true;
	return false;
}

void complete_hosted_shared_ptr_layout(TypePtr type)
{
	TypePtr bare = type.get() != NULL ? pa11::strip_cv(type) : TypePtr();
	if (bare.get() == NULL || bare->kind != pa11::TypeKind::Record)
		return;
	bare->complete = true;
	bare->fields.clear();
	bare->direct_bases.clear();
	bare->direct_base_offsets.clear();
	bare->direct_base_virtuals.clear();
	bare->virtual_bases.clear();
	bare->virtual_base_offsets.clear();
	bare->direct_base_offset = 0;
	bare->record_size = 16;
	bare->record_align = 8;
	bare->nonvirtual_size = 16;
	bare->nonvirtual_align = 8;
	bare->layout_valid = true;
}

}  // namespace

TypePtr Parser::instantiate_class_template(
	TemplateDeclaration* declaration,
	const vector<TemplateArgument>& arguments)
{
	TemplateMatchParserScope match_scope(this);
	if (!declaration_starts_class_key(declaration_tokens_, declaration))
	{
		TemplateDeclaration* replacement = NULL;
		bool ambiguous_replacement = false;
		for (size_t i = 0; i < template_declarations_.size(); ++i)
		{
			TemplateDeclaration* candidate = template_declarations_[i].get();
			if (candidate == declaration ||
			    candidate->kind != TemplateDeclarationKind::Class ||
			    candidate->name != declaration->name ||
			    !candidate->has_definition ||
			    !declaration_starts_class_key(declaration_tokens_, candidate))
				continue;
			if (candidate->owner == declaration->owner)
			{
				replacement = candidate;
				ambiguous_replacement = false;
				break;
			}
			if (replacement == NULL)
				replacement = candidate;
			else if (replacement->owner != candidate->owner)
				ambiguous_replacement = true;
		}
		if (replacement != NULL && !ambiguous_replacement)
			declaration = replacement;
	}
	vector<TemplateArgument> full_args;
	completing_class_template_arguments_.push_back(declaration);
	try
	{
		full_args = complete_template_arguments(declaration, arguments);
	}
	catch (...)
	{
		completing_class_template_arguments_.pop_back();
		throw;
	}
	completing_class_template_arguments_.pop_back();
	vector<TemplateArgument> specialization_match_args =
		flatten_actual_template_argument_packs(full_args);
	bool template_dependent = false;
	bool dependent = false;
	for (size_t i = 0; i < full_args.size(); ++i)
	{
		bool argument_dependent =
			template_argument_has_template_parameter(
				full_args[i],
				record_template_arguments_);
		if (argument_dependent)
			template_dependent = true;
		if (argument_dependent ||
		    (full_args[i].kind == TemplateArgumentKind::Type &&
		     type_mentions_active_record(full_args[i].type,
		                                 active_class_instantiations_)))
			dependent = true;
	}
	TemplateDeclaration* selected_declaration = declaration;
	vector<TemplateArgument> selected_args = full_args;
	TemplateDeclaration* best_partial = NULL;
	(void)template_dependent;
	string owner_key;
	TypePtr owner_record = pa11::record_type_for_scope(declaration->owner);
	owner_record = owner_record.get() != NULL
		? pa11::strip_cv(owner_record) : TypePtr();
	map<const void*, vector<TemplateArgument> >::const_iterator owner_args =
		owner_record.get() != NULL
		? record_template_arguments_.find(owner_record.get())
		: record_template_arguments_.end();
	if (owner_args != record_template_arguments_.end())
		owner_key = template_argument_key(owner_args->second);
	string key = template_argument_key(full_args);
	if (!owner_key.empty())
		key = owner_key + "::" + declaration->name + "<" + key + ">";
	if (declaration->completing_specializations.count(key) != 0)
	{
		for (size_t i = active_class_instantiations_.size(); i > 0; --i)
		{
			const ActiveClassInstantiation& active =
				active_class_instantiations_[i - 1];
			if (active.declaration != declaration ||
			    active.type.get() == NULL)
				continue;
			TypePtr active_record = pa11::strip_cv(active.type);
			map<const void*, vector<TemplateArgument> >::const_iterator args =
				record_template_arguments_.find(active_record.get());
			if (args == record_template_arguments_.end())
				continue;
			string active_key = template_argument_key(args->second);
			if (!owner_key.empty())
				active_key = owner_key + "::" + declaration->name +
				             "<" + active_key + ">";
			if (active_key == key)
				return active.type;
		}
		map<string, TypePtr>::iterator existing =
			declaration->class_specializations.find(key);
		if (existing != declaration->class_specializations.end())
			return existing->second;
		throw runtime_error("recursive class template instantiation");
	}
	declaration->completing_specializations.insert(key);
	try
	{
		for (size_t i = 0;
		     i < declaration->class_specialization_declarations.size();
		     ++i)
		{
			try
			{
				TemplateDeclaration* candidate =
					declaration->class_specialization_declarations[i];
				vector<TemplateArgument> candidate_args;
					bool candidate_match =
						match_class_specialization(declaration,
						                           candidate,
						                           specialization_match_args,
						                           arguments.size(),
						                           candidate_args,
						                           record_template_arguments_);
					if (!candidate_match)
						continue;
					if (best_partial == NULL ||
				    class_specialization_more_specialized(
					    candidate,
					    best_partial,
					    record_template_arguments_))
				{
					best_partial = candidate;
					selected_declaration = candidate;
					selected_args = candidate_args;
				}
				else if (!class_specialization_more_specialized(
					         best_partial,
					         candidate,
					         record_template_arguments_))
				{
					string best_pattern_key =
						template_argument_key(
							best_partial->class_specialization_pattern);
					string candidate_pattern_key =
						template_argument_key(
							candidate->class_specialization_pattern);
					string best_pattern_spelling =
						template_argument_spelling(
							best_partial->class_specialization_pattern);
					string candidate_pattern_spelling =
						template_argument_spelling(
							candidate->class_specialization_pattern);
					if (best_pattern_key == candidate_pattern_key ||
					    best_pattern_spelling == candidate_pattern_spelling)
					{
						if (!best_partial->has_definition &&
						    candidate->has_definition)
						{
							best_partial = candidate;
							selected_declaration = candidate;
							selected_args = candidate_args;
						}
						continue;
					}
					throw runtime_error(
						"ambiguous class template partial specialization: " +
						declaration->name + "<" + key + "> between " +
						template_argument_spelling(
							best_partial->class_specialization_pattern) +
						" and " +
						template_argument_spelling(
							candidate->class_specialization_pattern));
				}
			}
			catch (const runtime_error& err)
			{
				string message = err.what();
					if (message == "incomplete object type" ||
					    message == "incomplete class type" ||
					    message == "dependent typename not resolved" ||
					    message == "expected declaration specifiers" ||
					    message == "function template not found")
					{
						continue;
				}
				throw;
			}
		}
	}
	catch (...)
	{
		declaration->completing_specializations.erase(key);
		throw;
	}
	declaration->completing_specializations.erase(key);
	string selected_key = template_argument_key(selected_args);
	if (!owner_key.empty())
		selected_key = owner_key + "::" + selected_declaration->name +
		               "<" + selected_key + ">";
	for (size_t i = active_class_instantiations_.size(); i > 0; --i)
	{
		const ActiveClassInstantiation& active =
			active_class_instantiations_[i - 1];
		if (active.declaration != selected_declaration ||
		    active.type.get() == NULL)
			continue;
		TypePtr active_record = pa11::strip_cv(active.type);
		map<const void*, vector<TemplateArgument> >::const_iterator args =
			record_template_arguments_.find(active_record.get());
		if (args == record_template_arguments_.end())
			continue;
		string active_key = template_argument_key(args->second);
		if (!owner_key.empty())
			active_key = owner_key + "::" + selected_declaration->name +
			             "<" + active_key + ">";
		if (active_key == selected_key)
			return active.type;
	}
	map<string, TypePtr>::iterator existing =
		declaration->class_specializations.find(key);
	if (existing != declaration->class_specializations.end())
	{
		TypePtr existing_record = pa11::strip_cv(existing->second);
		existing_record->template_primary_name = declaration->name;
		existing_record->template_arguments = template_instance_arguments(full_args);
		record_template_arguments_[existing_record.get()] = selected_args;
		map<const void*, TemplateDeclaration*>::iterator existing_decl =
			record_template_declarations_.find(existing_record.get());
		bool only_injected_type_members = true;
			if (existing_record->scope != NULL)
				for (size_t i = 0; i < existing_record->scope->binding_order.size(); ++i)
				{
					Binding* member = existing_record->scope->binding_order[i];
					if (member->kind != BindingKind::Type ||
					    member->name != existing_record->scope->name)
						only_injected_type_members = false;
				}
			bool actively_completing = false;
			for (size_t i = 0; i < active_class_instantiations_.size(); ++i)
			{
				TypePtr active_type =
					pa11::strip_cv(active_class_instantiations_[i].type);
				if (active_type.get() == existing_record.get())
					actively_completing = true;
			}
				if (existing_decl != record_template_declarations_.end() &&
			    ((existing_decl->second != selected_declaration &&
			      (!existing_record->complete ||
			       !existing_decl->second->has_definition ||
			       selected_declaration->class_specialization)) ||
			     (selected_declaration->has_definition &&
			      existing_record->complete &&
			      !existing_record->layout_valid &&
			      only_injected_type_members &&
			      !actively_completing)))
		{
			existing_decl->second = selected_declaration;
			record_template_arguments_[existing_record.get()] = selected_args;
			existing_record->complete = false;
		}
		if (function_template_candidate_instantiation_depth_ == 0)
			candidate_only_class_template_specializations_.erase(
				existing->second.get());
		bool complete_now =
			!dependent &&
			defer_class_template_completion_depth_ == 0 &&
			(function_template_candidate_instantiation_depth_ == 0 ||
			 (hosted_compatibility_ &&
			  hosted_streambuf_iterator_template(selected_declaration)));
		if (complete_now)
			complete_template_record(existing->second);
		return existing->second;
	}

	string special_name = template_specialization_name(declaration, full_args);
	Scope* class_scope =
		pa11::create_child_scope(declaration->owner,
		                         ScopeKind::Class,
		                         declaration->name);
	TypePtr type =
		pa11::make_record_type(scoped_type_display_name(declaration->owner,
		                                                special_name),
		                       selected_declaration->tag.empty()
		                       ? (declaration->tag.empty() ? "struct" :
		                          declaration->tag)
		                       : selected_declaration->tag,
		                       false,
		                       class_scope);
	type->is_template_specialization = true;
	type->template_primary_name = declaration->name;
	type->template_arguments = template_instance_arguments(full_args);
	Binding* binding =
		pa11::add_binding(declaration->owner,
		                  BindingKind::Type,
		                  special_name,
		                  type);
	binding->target_scope = class_scope;
	Binding* injected =
		pa11::add_binding(class_scope,
		                  BindingKind::Type,
		                  declaration->name,
		                  type);
	injected->target_scope = class_scope;
	declaration->class_specializations[key] = type;
	record_template_declarations_[type.get()] = selected_declaration;
	record_template_arguments_[type.get()] = selected_args;
	if (function_template_candidate_instantiation_depth_ != 0)
		candidate_only_class_template_specializations_.insert(type.get());
	bool complete_now =
		!dependent &&
		defer_class_template_completion_depth_ == 0 &&
		(function_template_candidate_instantiation_depth_ == 0 ||
		 (hosted_compatibility_ &&
		  hosted_streambuf_iterator_template(selected_declaration)));
	if (complete_now)
		complete_template_record(type);
	return type;
}

void Parser::complete_template_record(TypePtr type)
{
	TypePtr bare = pa11::strip_cv(type);
	if (bare->kind != pa11::TypeKind::Record)
		return;
	if (validating_template_definition_)
	{
		bool active_validation_record = false;
		bool active_validation_base = false;
		for (size_t i = 0; i < active_class_instantiations_.size(); ++i)
		{
			TypePtr active = pa11::strip_cv(
				active_class_instantiations_[i].type);
			if (active.get() == bare.get())
			{
				active_validation_record = true;
				break;
			}
			vector<TypePtr> bases = pa11::record_direct_bases(active);
			for (size_t b = 0; b < bases.size(); ++b)
			{
				TypePtr base = bases[b].get() != NULL
					? pa11::strip_cv(bases[b]) : TypePtr();
				if (base.get() != NULL &&
				    pa11::same_type(base, bare))
					active_validation_base = true;
			}
		}
		if (!active_validation_record && !active_validation_base)
			return;
	}
	if (bare->complete)
		return;
	candidate_only_class_template_specializations_.erase(bare.get());
	map<const void*, TemplateDeclaration*>::iterator found =
		record_template_declarations_.find(bare.get());
	if (found == record_template_declarations_.end())
		return;
	TemplateDeclaration* declaration = found->second;
	if (!declaration_starts_class_key(declaration_tokens_, declaration))
	{
		TemplateDeclaration* replacement = NULL;
		bool ambiguous_replacement = false;
		for (size_t i = 0; i < template_declarations_.size(); ++i)
		{
			TemplateDeclaration* candidate = template_declarations_[i].get();
			if (candidate == declaration ||
			    candidate->kind != TemplateDeclarationKind::Class ||
			    candidate->name != declaration->name ||
			    !candidate->has_definition ||
			    !declaration_starts_class_key(declaration_tokens_, candidate))
				continue;
			if (candidate->owner == declaration->owner)
			{
				replacement = candidate;
				ambiguous_replacement = false;
				break;
			}
			if (replacement == NULL)
				replacement = candidate;
			else if (replacement->owner != candidate->owner)
				ambiguous_replacement = true;
		}
		if (replacement != NULL && !ambiguous_replacement)
		{
			declaration = replacement;
			found->second = declaration;
		}
	}
	if (!declaration->has_definition)
		return;
	vector<TemplateArgument> args = record_template_arguments_[bare.get()];
	bool dependent = template_arguments_dependent(args);
	map<string, TypePtr> owner_subst;
	map<string, TemplateArgument> owner_value_subst;
	set<string> owner_pack_subst;
	vector<TemplateArgument> owner_args_for_key;
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
		owner_args_for_key = owner_args->second;
		for (size_t i = 0;
		     i < owner_args->second.size() &&
		     i < owner_decl->second->parameters.size();
		     ++i)
			if (!owner_decl->second->parameters[i].name.empty())
			{
				const TemplateParameterInfo& parameter =
					owner_decl->second->parameters[i];
				if (parameter.kind == TemplateParameterKind::Type)
				{
					if (parameter.is_pack)
					{
						owner_subst[parameter.name] =
							pa11::make_template_parameter_type(
								parameter.name);
						owner_value_subst[parameter.name] =
							owner_args->second[i];
						if (owner_args->second[i].kind ==
						        TemplateArgumentKind::Pack &&
						    owner_args->second[i].pack.size() == 1 &&
						    owner_args->second[i].pack[0].kind ==
							    TemplateArgumentKind::Type)
							owner_subst[parameter.name] =
								owner_args->second[i].pack[0].type;
						else if (owner_args->second[i].kind ==
						         TemplateArgumentKind::Type)
							owner_subst[parameter.name] =
								owner_args->second[i].type;
						owner_pack_subst.insert(parameter.name);
					}
					else
						owner_subst[parameter.name] =
							owner_args->second[i].type;
				}
				else
					owner_value_subst[parameter.name] =
						owner_args->second[i];
			}
	}
	string key = template_argument_key(args);
	if (!owner_args_for_key.empty())
		key = template_argument_key(owner_args_for_key) + "::" +
		      declaration->name + "<" + key + ">";
	if (declaration->completing_specializations.count(key) != 0)
		return;
	declaration->completing_specializations.insert(key);

	size_t save_pos = pos_;
	bool tokens_are_declaration_tokens =
		tokens_.size() == declaration_tokens_.size() &&
		(tokens_.empty() ||
		 (tokens_.front().source == declaration_tokens_.front().source &&
		  tokens_.back().source == declaration_tokens_.back().source));
	vector<Token> complete_save_tokens;
	if (!tokens_are_declaration_tokens)
		complete_save_tokens = tokens_;
	vector<Scope*> save_scopes = scopes_;
	vector<map<string, TypePtr> > save_subst = template_type_substitutions_;
	vector<map<string, TemplateArgument> > save_value_subst =
		template_value_substitutions_;
	vector<set<string> > save_pack_subst = template_type_parameter_packs_;
	map<string, TypePtr> subst;
	map<string, TemplateArgument> value_subst;
	set<string> pack_subst;
	for (size_t i = 0; i < args.size() && i < declaration->parameters.size(); ++i)
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
						args[i];
					if (args[i].kind == TemplateArgumentKind::Pack &&
					    args[i].pack.size() == 1 &&
					    args[i].pack[0].kind ==
						    TemplateArgumentKind::Type)
						subst[declaration->parameters[i].name] =
							args[i].pack[0].type;
					else if (args[i].kind == TemplateArgumentKind::Type)
						subst[declaration->parameters[i].name] =
							args[i].type;
					pack_subst.insert(declaration->parameters[i].name);
				}
				else
					subst[declaration->parameters[i].name] =
						args[i].type;
			}
			else
				value_subst[declaration->parameters[i].name] = args[i];
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
		template_type_parameter_packs_.push_back(owner_pack_subst);
	}
	template_type_substitutions_.push_back(subst);
	template_value_substitutions_.push_back(value_subst);
	template_type_parameter_packs_.push_back(pack_subst);
	active_class_instantiations_.push_back(
		ActiveClassInstantiation(
			declaration,
			template_specialization_name(declaration, args),
			bare));
	scopes_.clear();
	scopes_.push_back(declaration->lexical_scope != NULL
	                  ? declaration->lexical_scope
	                  : declaration->owner);
	if (!tokens_are_declaration_tokens)
		tokens_ = declaration_tokens_;
	pos_ = declaration->decl_begin;
	try
	{
		TypePtr parsed = parse_class_specifier();
		(void)parsed;
	}
	catch (const runtime_error& err)
	{
		active_class_instantiations_.pop_back();
		template_type_substitutions_ = save_subst;
		template_value_substitutions_ = save_value_subst;
		template_type_parameter_packs_ = save_pack_subst;
		if (!tokens_are_declaration_tokens)
			tokens_ = complete_save_tokens;
		scopes_ = save_scopes;
		pos_ = save_pos;
		declaration->completing_specializations.erase(key);
		bare->complete = false;
		if (hosted_compatibility_ &&
		    hosted_shared_ptr_template(declaration) &&
		    (string(err.what()) == "incomplete object type" ||
		     string(err.what()) == "incomplete class type" ||
		     string(err.what()) == "incomplete array type" ||
		     string(err.what()) == "no matching constructor" ||
		     string(err.what()) == "invalid initializer conversion" ||
		     string(err.what()) == "expected declaration specifiers"))
		{
			complete_hosted_shared_ptr_layout(bare);
			return;
		}
		if (dependent &&
		    (string(err.what()) == "incomplete object type" ||
		     string(err.what()) == "incomplete class type" ||
		     string(err.what()) == "incomplete array type" ||
		     string(err.what()) == "no matching constructor" ||
		     string(err.what()) == "invalid initializer conversion" ||
		     string(err.what()) == "expected declaration specifiers"))
			return;
		throw;
	}
	catch (...)
	{
		active_class_instantiations_.pop_back();
		template_type_substitutions_ = save_subst;
		template_value_substitutions_ = save_value_subst;
		template_type_parameter_packs_ = save_pack_subst;
		if (!tokens_are_declaration_tokens)
			tokens_ = complete_save_tokens;
		scopes_ = save_scopes;
		pos_ = save_pos;
		declaration->completing_specializations.erase(key);
		bare->complete = false;
		throw;
	}
	active_class_instantiations_.pop_back();
	template_type_substitutions_ = save_subst;
	template_value_substitutions_ = save_value_subst;
	template_type_parameter_packs_ = save_pack_subst;
	if (!tokens_are_declaration_tokens)
		tokens_ = complete_save_tokens;
	scopes_ = save_scopes;
	pos_ = save_pos;
	declaration->completing_specializations.erase(key);
	instantiate_member_variable_templates(type);
}

void Parser::mark_template_argument_demanded(
	const TemplateArgument& argument)
{
	if (argument.kind == TemplateArgumentKind::Type)
		mark_template_specialization_demanded(argument.type);
	else if (argument.kind == TemplateArgumentKind::Value)
	{
		mark_template_specialization_demanded(argument.type);
		for (size_t i = 0;
		     i < argument.value_owner_template_arguments.size();
		     ++i)
			mark_template_argument_demanded(
				template_argument_from_instance_argument(
					argument.value_owner_template_arguments[i]));
	}
	else if (argument.kind == TemplateArgumentKind::Pack)
	{
		for (size_t i = 0; i < argument.pack.size(); ++i)
			mark_template_argument_demanded(argument.pack[i]);
	}
}

void Parser::mark_template_specialization_demanded(TypePtr type)
{
	if (type.get() == NULL)
		return;
	if (type->kind == pa11::TypeKind::Cv)
	{
		mark_template_specialization_demanded(type->base);
		return;
	}
	TypePtr bare = pa11::strip_cv(type);
	if (bare.get() != type.get())
	{
		mark_template_specialization_demanded(bare);
		return;
	}
	switch (type->kind)
	{
	case pa11::TypeKind::Pointer:
	case pa11::TypeKind::LValueReference:
	case pa11::TypeKind::RValueReference:
	case pa11::TypeKind::Array:
		mark_template_specialization_demanded(type->base);
		break;
	case pa11::TypeKind::Function:
		mark_template_specialization_demanded(type->base);
		for (size_t i = 0; i < type->parameters.size(); ++i)
			mark_template_specialization_demanded(type->parameters[i]);
		break;
	case pa11::TypeKind::MemberPointer:
		mark_template_specialization_demanded(type->member_class);
		mark_template_specialization_demanded(type->base);
		break;
		case pa11::TypeKind::Record:
				candidate_only_class_template_specializations_.erase(type.get());
				if (type->is_template_specialization)
					demanded_class_template_specializations_.insert(type.get());
			if (type->is_template_specialization &&
			    !type_is_template_dependent(type) &&
			    defer_class_template_completion_depth_ == 0 &&
			    function_template_candidate_instantiation_depth_ == 0 &&
			    !validating_template_definition_)
				{
					if (type->complete)
						instantiate_member_variable_templates(type);
					else
						complete_template_record(type);
					TypePtr direct_base = type->base.get() != NULL
						? pa11::strip_cv(type->base) : TypePtr();
					if (direct_base.get() != NULL &&
					    direct_base->kind == pa11::TypeKind::Record &&
					    direct_base.get() != type.get())
						mark_template_specialization_demanded(direct_base);
				}
				break;
	default:
		break;
	}
}

void Parser::complete_member_class_template_record(Binding* binding)
{
	if (binding == NULL || binding->type.get() == NULL)
		return;
	TypePtr bare = pa11::strip_cv(binding->type);
	if (bare->kind != pa11::TypeKind::Record ||
	    (bare->complete && bare->scope != NULL))
		return;
	TypePtr owner_record = binding->owner != NULL
		? pa11::record_type_for_scope(binding->owner) : TypePtr();
	if (owner_record.get() == NULL)
		return;
	owner_record = pa11::strip_cv(owner_record);
	map<const void*, TemplateDeclaration*>::iterator outer =
		record_template_declarations_.find(owner_record.get());
	if (outer == record_template_declarations_.end())
		return;
	map<pair<TemplateDeclaration*, string>, TemplateDeclaration*>::iterator found =
		member_class_templates_.find(make_pair(outer->second, binding->name));
	TemplateDeclaration* declaration = found != member_class_templates_.end()
		? found->second : NULL;
	if (declaration == NULL)
	{
		for (map<pair<TemplateDeclaration*, string>,
		         TemplateDeclaration*>::iterator it =
			     member_class_templates_.begin();
		     it != member_class_templates_.end();
		     ++it)
		{
			TemplateDeclaration* candidate_outer = it->first.first;
			if (it->first.second == binding->name &&
			    candidate_outer != NULL &&
			    candidate_outer->name == outer->second->name &&
			    candidate_outer->owner == outer->second->owner)
				{
					declaration = it->second;
					break;
				}
			}
		}
		if (declaration == NULL)
			return;
		if (!declaration->has_definition)
			return;
		vector<TemplateArgument> owner_args =
			record_template_arguments_[owner_record.get()];
		vector<TemplateArgument> member_args;
		map<const void*, vector<TemplateArgument> >::const_iterator member_stored =
			record_template_arguments_.find(bare.get());
		if (member_stored != record_template_arguments_.end())
			member_args = member_stored->second;
		else
			for (size_t i = 0; i < bare->template_arguments.size(); ++i)
				member_args.push_back(
					template_argument_from_instance_argument(
						bare->template_arguments[i]));
		string key = template_argument_key(owner_args) + "::" + binding->name +
		             "<" + template_argument_key(member_args) + ">";
		if (declaration->completing_specializations.count(key) != 0)
			return;
		declaration->completing_specializations.insert(key);

		size_t save_pos = pos_;
		vector<Scope*> save_scopes = scopes_;
		vector<map<string, TypePtr> > save_subst =
			template_type_substitutions_;
		vector<map<string, TemplateArgument> > save_value_subst =
			template_value_substitutions_;
		vector<set<string> > save_pack_subst = template_type_parameter_packs_;
		map<string, TypePtr> owner_subst;
		map<string, TemplateArgument> owner_value_subst;
		set<string> owner_pack_subst;
		for (size_t i = 0;
		     i < owner_args.size() && i < outer->second->parameters.size();
		     ++i)
			if (!outer->second->parameters[i].name.empty())
			{
				const TemplateParameterInfo& parameter =
					outer->second->parameters[i];
				if (parameter.kind == TemplateParameterKind::Type)
				{
					if (parameter.is_pack)
					{
						owner_subst[parameter.name] =
							pa11::make_template_parameter_type(
								parameter.name);
						owner_value_subst[parameter.name] =
							owner_args[i];
						owner_pack_subst.insert(parameter.name);
					}
					else
						owner_subst[parameter.name] =
							owner_args[i].type;
				}
				else
					owner_value_subst[parameter.name] = owner_args[i];
			}
		map<string, TypePtr> subst;
		map<string, TemplateArgument> value_subst;
		set<string> pack_subst;
		for (size_t i = 0;
		     i < member_args.size() && i < declaration->parameters.size();
		     ++i)
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
							member_args[i];
						pack_subst.insert(
							declaration->parameters[i].name);
					}
					else
						subst[declaration->parameters[i].name] =
							member_args[i].type;
				}
				else
					value_subst[declaration->parameters[i].name] =
						member_args[i];
			}
		if (!owner_subst.empty() || !owner_value_subst.empty())
		{
			template_type_substitutions_.push_back(owner_subst);
			template_value_substitutions_.push_back(owner_value_subst);
			template_type_parameter_packs_.push_back(owner_pack_subst);
		}
		template_type_substitutions_.push_back(subst);
		template_value_substitutions_.push_back(value_subst);
		template_type_parameter_packs_.push_back(pack_subst);
	scopes_.clear();
	scopes_.push_back(declaration->lexical_scope != NULL
	                  ? declaration->lexical_scope
	                  : declaration->owner);
	pos_ = declaration->decl_begin;
	TypePtr parsed = parse_class_specifier();
	TypePtr parsed_bare = pa11::strip_cv(parsed);
	if (!bare->complete &&
	    parsed_bare.get() != NULL &&
	    parsed_bare->kind == pa11::TypeKind::Record &&
	    parsed_bare->complete &&
	    parsed_bare->scope != NULL)
	{
		*bare = *parsed_bare;
		binding->target_scope = bare->scope;
	}
		template_type_substitutions_ = save_subst;
		template_value_substitutions_ = save_value_subst;
		template_type_parameter_packs_ = save_pack_subst;
		scopes_ = save_scopes;
	pos_ = save_pos;
	declaration->completing_specializations.erase(key);
}

}  // namespace internal
}  // namespace pa12
