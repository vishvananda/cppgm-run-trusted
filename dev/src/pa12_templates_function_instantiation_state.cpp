#include "pa12_templates_function_instantiation_engine.h"

#include <cstdint>
#include <functional>
#include <set>
#include <stdexcept>

using namespace std;

namespace pa12 {
namespace internal {

namespace {

bool disabled_enable_if_typename(TypePtr type)
{
	if (type.get() == NULL)
		return false;
	type = pa11::strip_cv(type);
	if (!type->is_dependent_typename || type->template_arguments.empty())
		return false;
	const pa11::TemplateInstanceArgument& condition =
		type->template_arguments[0];
	if (condition.kind != pa11::TemplateInstanceArgumentKind::Value ||
	    condition.dependent || condition.value != 0)
		return false;
	string root_name = type->name;
	size_t type_suffix = root_name.find("::type");
	if (type_suffix != string::npos)
		root_name = root_name.substr(0, type_suffix);
	size_t template_suffix = root_name.find('<');
	if (template_suffix != string::npos)
		root_name = root_name.substr(0, template_suffix);
	size_t qualifier = root_name.rfind("::");
	if (qualifier != string::npos)
		root_name = root_name.substr(qualifier + 2);
	return root_name == "enable_if" || root_name == "__enable_if_t";
}

bool template_arguments_contain_disabled_enable_if(
	const vector<TemplateArgument>& arguments)
{
	for (size_t i = 0; i < arguments.size(); ++i)
	{
		const TemplateArgument& arg = arguments[i];
		if (arg.kind == TemplateArgumentKind::Type &&
		    disabled_enable_if_typename(arg.type))
			return true;
		if (arg.kind == TemplateArgumentKind::Pack &&
		    template_arguments_contain_disabled_enable_if(arg.pack))
			return true;
	}
	return false;
}

bool hosted_internal_function_name(const string& name)
{
	return name.size() >= 2 && name[0] == '_' && name[1] == '_';
}

bool same_owner_record(TypePtr left, TypePtr right)
{
	left = left.get() != NULL ? pa11::strip_cv(left) : TypePtr();
	right = right.get() != NULL ? pa11::strip_cv(right) : TypePtr();
	if (left.get() == NULL ||
	    right.get() == NULL ||
	    left->kind != pa11::TypeKind::Record ||
	    right->kind != pa11::TypeKind::Record)
		return false;
	if (left->is_template_specialization &&
	    right->is_template_specialization &&
	    !left->template_primary_name.empty() &&
	    left->template_primary_name == right->template_primary_name)
		return pa11::same_type(left, right);
	return pa11::same_type(left, right) ||
	       same_template_signature_type(left, right);
}

TypePtr function_this_record(Binding* binding)
{
	if (binding == NULL ||
	    binding->type.get() == NULL ||
	    binding->type->kind != pa11::TypeKind::Function ||
	    binding->type->parameters.empty())
		return TypePtr();
	TypePtr this_type = pa11::strip_cv(binding->type->parameters[0]);
	if (this_type.get() == NULL ||
	    this_type->kind != pa11::TypeKind::Pointer)
		return TypePtr();
	TypePtr record = pa11::strip_cv(this_type->base);
	if (record.get() == NULL || record->kind != pa11::TypeKind::Record)
		return TypePtr();
	return record;
}

bool same_replay_source_declaration(TemplateDeclaration* left,
                                    TemplateDeclaration* right)
{
	return left != NULL &&
	       right != NULL &&
	       left != right &&
	       left->name == right->name &&
	       left->owner == right->owner &&
	       left->placeholder == right->placeholder &&
	       left->decl_begin == right->decl_begin &&
	       left->decl_end == right->decl_end;
}

map<string, Binding*>::iterator find_specialization_by_key(
	map<string, Binding*>& specializations,
	const string& key)
{
	for (map<string, Binding*>::iterator it = specializations.begin();
	     it != specializations.end();
	     ++it)
		if (it->first.size() == key.size() && it->first == key)
			return it;
	return specializations.end();
}

}  // namespace

FunctionTemplateInstantiationEngine::FunctionTemplateInstantiationEngine(
	Parser& parser,
	TemplateDeclaration* declaration,
	const vector<TemplateArgument>& arguments)
	: p(parser),
	  declaration(declaration),
	  arguments(arguments),
	  replaced_specialization(NULL),
	  save_pos(parser.pos_),
	  save_scopes(parser.scopes_),
	  save_subst(parser.template_type_substitutions_),
	  save_value_subst(parser.template_value_substitutions_),
	  save_pack_subst(parser.template_type_parameter_packs_),
	  save_force_new_function_binding(parser.force_new_function_binding_),
	  save_defer_function_template_bodies(
		  parser.defer_function_template_bodies_),
	  save_suppress_implicit_template_base_init(
		  parser.suppress_implicit_template_base_init_),
	  save_replay_function_type_override_owner(
		  parser.replay_function_type_override_owner_),
	  save_replay_function_type_override_name(
		  parser.replay_function_type_override_name_),
	  save_replay_function_template_declaration(
		  parser.replay_function_template_declaration_),
	  save_replay_function_template_arguments(
		  parser.replay_function_template_arguments_),
	  save_override_function_parameter_names(
		  parser.override_function_parameter_names_),
	  save_function_parameter_name_override(
		  parser.function_parameter_name_override_),
	  completion_active(false)
{
}

Binding* FunctionTemplateInstantiationEngine::run()
{
	complete_arguments();
	Binding* redirected = redirect_to_matching_definition();
	if (redirected != NULL)
		return redirected;
	p.validate_function_template_definition(declaration);
	bool full_args_dependent = p.template_arguments_dependent(full_args);
	share_existing_specialization_if_available();
	map<string, Binding*>::iterator existing =
		declaration->function_specializations.find(key);
	if (existing != declaration->function_specializations.end())
	{
		Binding* reused = reuse_existing_specialization(
			existing,
			full_args_dependent);
		if (reused != NULL)
			return reused;
	}
	if (declaration->completing_specializations.count(key) != 0)
	{
		try
		{
			enter_substitution_scope();
			return instantiate_candidate_signature(false);
		}
		catch (...)
		{
			restore_parser_state();
			throw;
		}
	}
	begin_completion();
	try
	{
		enter_substitution_scope();
		return instantiate_with_substitutions(full_args_dependent);
	}
	catch (...)
	{
		restore_state();
		throw;
	}
}

void FunctionTemplateInstantiationEngine::complete_arguments()
{
	bool defer_completed =
		p.function_template_candidate_instantiation_depth_ == 0 &&
		arguments.size() == declaration->parameters.size();
	bool deferred_context = false;
	bool have_deferred_argument = false;
	for (size_t i = 0; defer_completed && i < arguments.size(); ++i)
	{
		if (arguments[i].kind == TemplateArgumentKind::Value &&
		    arguments[i].dependent &&
		    arguments[i].value_expr_end > arguments[i].value_expr_begin)
			have_deferred_argument = true;
		if (i < declaration->parameters.size() &&
		    declaration->parameters[i].kind == TemplateParameterKind::NonType &&
		    declaration->parameters[i].has_default &&
		    p.type_is_template_dependent(declaration->parameters[i].type))
			have_deferred_argument = true;
	}
	defer_completed = defer_completed && have_deferred_argument;
	if (defer_completed)
	{
		++p.function_template_candidate_instantiation_depth_;
		deferred_context = true;
	}
	try
	{
		full_args = p.complete_template_arguments(declaration, arguments);
	}
	catch (const runtime_error& err)
	{
		if (defer_completed)
		{
			--p.function_template_candidate_instantiation_depth_;
			defer_completed = false;
		}
		if ((!deferred_context &&
		     p.function_template_candidate_instantiation_depth_ == 0) ||
		    string(err.what()) != "dependent typename not resolved" ||
		    arguments.size() != declaration->parameters.size() ||
		    template_arguments_contain_disabled_enable_if(arguments))
			throw;
		full_args = arguments;
	}
	if (defer_completed)
		--p.function_template_candidate_instantiation_depth_;
	key = p.template_argument_key(full_args);
}

Binding* FunctionTemplateInstantiationEngine::redirect_to_matching_definition()
{
	if (declaration->has_definition)
		return NULL;
	vector<size_t> cache_key;
	cache_key.push_back(reinterpret_cast<uintptr_t>(declaration));
	cache_key.push_back(hash<string>()(key));
	cache_key.push_back(arguments.size());
	cache_key.push_back(p.template_declarations_.size());
	cache_key.push_back(p.member_function_template_generation_);
	map<vector<size_t>, Binding*>::iterator cached =
		p.function_template_redirect_cache_.find(cache_key);
	if (cached != p.function_template_redirect_cache_.end())
		return cached->second;
	for (map<Scope*, map<string, vector<TemplateDeclaration*> > >::iterator
		     sit = p.function_templates_.begin();
	     sit != p.function_templates_.end(); ++sit)
	{
		map<string, vector<TemplateDeclaration*> >::iterator nit =
			sit->second.find(declaration->name);
		if (nit == sit->second.end())
			continue;
		for (size_t di = 0; di < nit->second.size(); ++di)
		{
			TemplateDeclaration* candidate = nit->second[di];
			if (candidate == declaration || candidate == NULL ||
			    !candidate->has_definition ||
			    candidate->generic_function_type.get() == NULL ||
			    declaration->generic_function_type.get() == NULL ||
			    !same_template_signature_type(
				    candidate->generic_function_type,
				    declaration->generic_function_type))
				continue;
			size_t required_arguments = 0;
			for (size_t pi = 0; pi < candidate->parameters.size(); ++pi)
				if (!candidate->parameters[pi].has_default &&
				    !candidate->parameters[pi].is_pack)
					++required_arguments;
			if (arguments.size() < required_arguments)
				continue;
			try
			{
				p.complete_template_arguments(candidate, arguments);
			}
			catch (const exception&)
			{
				continue;
			}
			Binding* binding =
				p.instantiate_function_template(candidate, arguments);
			p.function_template_redirect_cache_[cache_key] = binding;
			return binding;
		}
	}
	p.function_template_redirect_cache_[cache_key] = NULL;
	return NULL;
}

void FunctionTemplateInstantiationEngine::
share_existing_specialization_if_available()
{
	if (find_specialization_by_key(declaration->function_specializations,
	                               key) !=
	    declaration->function_specializations.end())
		return;
	if (p.hosted_compatibility_ &&
	    p.function_template_candidate_instantiation_depth_ != 0 &&
	    declaration->constructor_template &&
	    declaration->placeholder != NULL &&
	    p.hosted_library_function(declaration->placeholder))
		return;
	static set<size_t> miss_cache;
	size_t miss_key = reinterpret_cast<uintptr_t>(&p);
	miss_key ^= reinterpret_cast<uintptr_t>(declaration) +
	            0x9e3779b97f4a7c15ULL + (miss_key << 6) + (miss_key >> 2);
	miss_key ^= hash<string>()(key) +
	            0x9e3779b97f4a7c15ULL + (miss_key << 6) + (miss_key >> 2);
	miss_key ^= p.template_declarations_.size() +
	            0x9e3779b97f4a7c15ULL + (miss_key << 6) + (miss_key >> 2);
	miss_key ^= p.member_function_template_generation_ +
	            0x9e3779b97f4a7c15ULL + (miss_key << 6) + (miss_key >> 2);
	if (miss_cache.find(miss_key) != miss_cache.end())
		return;
	for (size_t di = 0; di < p.template_declarations_.size(); ++di)
	{
		TemplateDeclaration* candidate = p.template_declarations_[di].get();
		if (candidate == declaration || candidate == NULL ||
		    candidate->kind != TemplateDeclarationKind::Function ||
		    candidate->name != declaration->name ||
		    candidate->function_specializations.empty())
			continue;
		map<string, Binding*>::iterator found =
			find_specialization_by_key(candidate->function_specializations,
			                           key);
		if (found == candidate->function_specializations.end())
			continue;
		if (!same_function_template_declaration_family(declaration,
		                                               candidate) &&
		    !same_replay_source_declaration(declaration,
		                                    candidate))
			continue;
		if (!specialization_matches_declaration_owner(found->second))
			continue;
		declaration->function_specializations[key] = found->second;
		remember_reused_specialization_body(found->second, candidate);
		remember_reused_specialization_body(found->second, declaration);
		return;
	}
	for (map<Scope*, map<string, vector<TemplateDeclaration*> > >::iterator
		     sit = p.function_templates_.begin();
	     sit != p.function_templates_.end(); ++sit)
	{
		map<string, vector<TemplateDeclaration*> >::iterator nit =
			sit->second.find(declaration->name);
		if (nit == sit->second.end())
			continue;
		for (size_t di = 0; di < nit->second.size(); ++di)
		{
			TemplateDeclaration* candidate = nit->second[di];
			if (candidate == declaration || candidate == NULL ||
			    candidate->name != declaration->name)
				continue;
			map<string, Binding*>::iterator found =
				find_specialization_by_key(candidate->function_specializations,
				                           key);
			if (found == candidate->function_specializations.end())
				continue;
			if (!same_function_template_declaration_family(declaration,
			                                               candidate) &&
			    !same_replay_source_declaration(declaration,
			                                    candidate))
				continue;
			if (!specialization_matches_declaration_owner(found->second))
				continue;
			declaration->function_specializations[key] = found->second;
			remember_reused_specialization_body(found->second, candidate);
			remember_reused_specialization_body(found->second, declaration);
			return;
		}
	}
	miss_cache.insert(miss_key);
}

	TemplateDeclaration* FunctionTemplateInstantiationEngine::
	specialization_body_source(TemplateDeclaration* source)
	{
		if (source == NULL)
			return NULL;
		TemplateDeclaration* replacement =
			p.replacement_function_template_definition(source);
		if (replacement != NULL && replacement->has_definition)
			return replacement;
		return source->has_definition ? source : NULL;
	}

	void FunctionTemplateInstantiationEngine::
	remember_reused_specialization_body(
		Binding* binding,
		TemplateDeclaration* source)
	{
		TemplateDeclaration* body_source = specialization_body_source(source);
		if (binding == NULL || body_source == NULL)
			return;
		map<Binding*, TemplateDeclaration*>::iterator existing =
			p.function_template_placeholders_.find(binding);
		bool existing_has_body =
			existing != p.function_template_placeholders_.end() &&
			existing->second != NULL &&
			existing->second->has_definition;
		if (!existing_has_body)
			p.function_template_placeholders_[binding] = body_source;
		if (p.function_template_specialization_arguments_.find(binding) ==
		    p.function_template_specialization_arguments_.end())
			p.function_template_specialization_arguments_[binding] = full_args;
		if (binding->aliased_binding == NULL)
			return;
		existing =
			p.function_template_placeholders_.find(binding->aliased_binding);
		existing_has_body =
			existing != p.function_template_placeholders_.end() &&
			existing->second != NULL &&
			existing->second->has_definition;
		if (!existing_has_body)
			p.function_template_placeholders_[binding->aliased_binding] =
				body_source;
		if (p.function_template_specialization_arguments_.find(
			    binding->aliased_binding) ==
		    p.function_template_specialization_arguments_.end())
			p.function_template_specialization_arguments_[
				binding->aliased_binding] = full_args;
	}

	bool FunctionTemplateInstantiationEngine::
	specialization_matches_declaration_owner(Binding* binding)
	{
		bool member_function_template =
			declaration->owner != NULL &&
			declaration->owner->kind == ScopeKind::Class;
		if (!member_function_template || binding == NULL)
			return true;
		if (binding->owner == NULL || declaration->owner == NULL ||
		    binding->owner->kind != ScopeKind::Class ||
		    declaration->owner->kind != ScopeKind::Class)
			return false;
		TypePtr binding_owner = pa11::record_type_for_scope(binding->owner);
		TypePtr declaration_owner =
			pa11::record_type_for_scope(declaration->owner);
		binding_owner = binding_owner.get() != NULL
			? pa11::strip_cv(binding_owner) : TypePtr();
		declaration_owner = declaration_owner.get() != NULL
			? pa11::strip_cv(declaration_owner) : TypePtr();
		if (binding_owner.get() == NULL || declaration_owner.get() == NULL)
			return false;
		bool owner_matches = binding->owner == declaration->owner ||
		                     same_owner_record(binding_owner,
		                                       declaration_owner);
		if (!owner_matches)
			return false;
		TypePtr this_record = function_this_record(binding);
		if (this_record.get() == NULL)
			return !declaration->constructor_template;
		if (!same_owner_record(this_record, declaration_owner))
			return false;
		if (declaration->constructor_template &&
		    p.hosted_library_function(binding))
			return true;
		return specialization_signature_matches(binding);
	}

	bool FunctionTemplateInstantiationEngine::
	specialization_signature_matches(Binding* binding)
	{
		if (binding == NULL ||
		    binding->type.get() == NULL ||
		    declaration->generic_function_type.get() == NULL ||
		    declaration->generic_function_type->kind != pa11::TypeKind::Function)
			return true;
		vector<map<string, TypePtr> > save_subst =
			p.template_type_substitutions_;
		vector<map<string, TemplateArgument> > save_value_subst =
			p.template_value_substitutions_;
		vector<set<string> > save_pack_subst =
			p.template_type_parameter_packs_;
		map<string, TypePtr> subst;
		map<string, TemplateArgument> value_subst;
		set<string> pack_subst;
		for (size_t i = 0; i < full_args.size() &&
		     i < declaration->parameters.size(); ++i)
		{
			const TemplateParameterInfo& parameter = declaration->parameters[i];
			if (parameter.name.empty())
				continue;
			if (parameter.kind == TemplateParameterKind::Type)
			{
				if (parameter.is_pack)
				{
					subst[parameter.name] =
						template_parameter_placeholder_type(parameter);
					value_subst[parameter.name] = full_args[i];
					pack_subst.insert(parameter.name);
				}
				else if (full_args[i].kind == TemplateArgumentKind::Type)
					subst[parameter.name] = full_args[i].type;
			}
			else
				value_subst[parameter.name] = full_args[i];
		}
		p.template_type_substitutions_.insert(
			p.template_type_substitutions_.end(),
			declaration->outer_type_substitutions.begin(),
			declaration->outer_type_substitutions.end());
		p.template_value_substitutions_.insert(
			p.template_value_substitutions_.end(),
			declaration->outer_value_substitutions.begin(),
			declaration->outer_value_substitutions.end());
		p.template_type_substitutions_.push_back(subst);
		p.template_value_substitutions_.push_back(value_subst);
		p.template_type_parameter_packs_.push_back(pack_subst);
		TypePtr expected;
		try
		{
			expected = p.substitute_function_template_type(
				declaration,
				declaration->generic_function_type);
		}
		catch (const runtime_error&)
		{
			p.template_type_substitutions_ = save_subst;
			p.template_value_substitutions_ = save_value_subst;
			p.template_type_parameter_packs_ = save_pack_subst;
			return true;
		}
		p.template_type_substitutions_ = save_subst;
		p.template_value_substitutions_ = save_value_subst;
		p.template_type_parameter_packs_ = save_pack_subst;
		bool matches =
			expected.get() == NULL ||
			pa11::same_type(binding->type, expected) ||
			same_template_signature_type(binding->type, expected);
		return matches;
	}

	Binding* FunctionTemplateInstantiationEngine::reuse_existing_specialization(
		map<string, Binding*>::iterator existing,
		bool full_args_dependent)
	{
		if (!specialization_matches_declaration_owner(existing->second))
		{
			declaration->function_specializations.erase(existing);
			return NULL;
		}
		if (declaration->completing_specializations.count(key) != 0)
			return existing->second;
		if (p.active_function_body_replays_.count(existing->second) != 0)
			return existing->second;
	remember_reused_specialization_body(existing->second, declaration);
	bool existing_has_body =
		p.function_bodies_.find(existing->second) != p.function_bodies_.end();
	bool existing_body_dependent =
		existing_has_body &&
		expr_node_structurally_dependent(
			p.function_bodies_.find(existing->second)->second);
	bool existing_type_dependent =
		type_structurally_dependent(existing->second->type) ||
		p.type_is_template_dependent(existing->second->type);
	bool existing_still_dependent =
		existing_type_dependent || existing_body_dependent;
	bool existing_usable = full_args_dependent || !existing_still_dependent;
	if (existing->second->is_extern_template_instantiation &&
	    existing_usable)
		return existing->second;
	if (existing->second->is_explicit_specialization_member &&
	    existing_usable)
		return existing->second;
	if (existing_has_body &&
	    p.function_template_placeholders_.find(existing->second) ==
		    p.function_template_placeholders_.end() &&
	    existing_usable)
		return existing->second;
	bool need_constexpr_value_body =
		(p.template_argument_expression_depth_ != 0 ||
		 p.constexpr_value_expression_depth_ != 0) &&
		declaration->has_definition && existing->second->is_constexpr &&
		!existing_has_body;
	if (!need_constexpr_value_body &&
	    p.function_template_candidate_instantiation_depth_ != 0 &&
	    p.hosted_compatibility_ && !existing->second->is_object_root &&
	    hosted_internal_function_name(existing->second->name))
		return existing->second;
	if (p.function_template_candidate_instantiation_depth_ != 0 &&
	    existing_usable && !need_constexpr_value_body)
		return existing->second;
	if (!existing_usable && !full_args_dependent &&
	    !declaration->class_template_member &&
	    existing->second->is_inline_definition && existing_has_body)
		existing_usable = true;
	bool existing_dependent_return =
		existing->second->type.get() != NULL &&
		existing->second->type->kind == pa11::TypeKind::Function &&
		p.type_is_template_dependent(existing->second->type->base);
	if (!declaration->has_definition && !existing_dependent_return &&
	    existing_usable)
		return existing->second;
	if (existing_usable &&
	    ((existing->second->is_inline_definition && existing_has_body) ||
	     (existing->second->is_object_root && existing_has_body)))
		return existing->second;
	replaced_specialization = existing->second;
	if (!declaration->has_definition)
		declaration->function_specializations.erase(existing);
	return NULL;
}

void FunctionTemplateInstantiationEngine::begin_completion()
{
	if (declaration->completing_specializations.count(key) != 0)
		throw runtime_error("recursive function template instantiation");
	declaration->completing_specializations.insert(key);
	completion_active = true;
}

void FunctionTemplateInstantiationEngine::enter_substitution_scope()
{
	map<string, TypePtr> subst;
	map<string, TemplateArgument> value_subst;
	set<string> pack_subst;
	for (size_t i = 0; i < full_args.size() &&
	     i < declaration->parameters.size(); ++i)
	{
		if (declaration->parameters[i].name.empty())
			continue;
		const string& name = declaration->parameters[i].name;
		if (declaration->parameters[i].kind == TemplateParameterKind::Type)
		{
			if (declaration->parameters[i].is_pack)
			{
				const TemplateParameterInfo& parameter =
					declaration->parameters[i];
				subst[name] = template_parameter_placeholder_type(parameter);
				value_subst[name] = full_args[i];
				pack_subst.insert(name);
			}
			else
				subst[name] = full_args[i].type;
		}
		else
			value_subst[name] = full_args[i];
	}
	p.template_type_substitutions_.insert(
		p.template_type_substitutions_.end(),
		declaration->outer_type_substitutions.begin(),
		declaration->outer_type_substitutions.end());
	p.template_value_substitutions_.insert(
		p.template_value_substitutions_.end(),
		declaration->outer_value_substitutions.begin(),
		declaration->outer_value_substitutions.end());
	p.template_type_substitutions_.push_back(subst);
	p.template_value_substitutions_.push_back(value_subst);
	p.template_type_parameter_packs_.push_back(pack_subst);
	p.scopes_.clear();
	p.scopes_.push_back(declaration->lexical_scope != NULL
	                    ? declaration->lexical_scope
	                    : declaration->owner);
}

void FunctionTemplateInstantiationEngine::restore_state()
{
	if (completion_active)
	{
		declaration->completing_specializations.erase(key);
		completion_active = false;
	}
	restore_parser_state();
}

void FunctionTemplateInstantiationEngine::restore_parser_state()
{
	p.template_type_substitutions_ = save_subst;
	p.template_value_substitutions_ = save_value_subst;
	p.template_type_parameter_packs_ = save_pack_subst;
	p.scopes_ = save_scopes;
	p.pos_ = save_pos;
	p.force_new_function_binding_ = save_force_new_function_binding;
	p.defer_function_template_bodies_ = save_defer_function_template_bodies;
	p.suppress_implicit_template_base_init_ =
		save_suppress_implicit_template_base_init;
	p.replay_function_type_override_owner_ =
		save_replay_function_type_override_owner;
	p.replay_function_type_override_name_ =
		save_replay_function_type_override_name;
	p.replay_function_template_declaration_ =
		save_replay_function_template_declaration;
	p.replay_function_template_arguments_ =
		save_replay_function_template_arguments;
	p.override_function_parameter_names_ =
		save_override_function_parameter_names;
	p.function_parameter_name_override_ =
		save_function_parameter_name_override;
}

Binding* FunctionTemplateInstantiationEngine::finish_with_restore(
	Binding* binding)
{
	restore_state();
	return binding;
}

bool FunctionTemplateInstantiationEngine::
instantiated_arguments_are_dependent() const
{
	for (size_t i = 0; i < full_args.size(); ++i)
	{
		vector<TemplateArgument> pending;
		pending.push_back(full_args[i]);
		while (!pending.empty())
		{
			TemplateArgument arg = pending.back();
			pending.pop_back();
			if (arg.kind == TemplateArgumentKind::Type)
			{
				if (p.type_is_template_dependent(arg.type))
					return true;
			}
			else if (arg.kind == TemplateArgumentKind::Value)
			{
				if (arg.dependent)
					return true;
			}
			else if (arg.kind == TemplateArgumentKind::Template)
			{
				if (arg.template_declaration == NULL)
					return true;
			}
			else
			{
				for (size_t pidx = 0; pidx < arg.pack.size(); ++pidx)
					pending.push_back(arg.pack[pidx]);
			}
		}
	}
	return false;
}

}  // namespace internal
}  // namespace pa12
