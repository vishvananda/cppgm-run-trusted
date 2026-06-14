#include "pa12_templates_function_instantiation_engine.h"

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
			return p.instantiate_function_template(candidate, arguments);
		}
	}
	return NULL;
}

void FunctionTemplateInstantiationEngine::
share_existing_specialization_if_available()
{
	if (declaration->function_specializations.find(key) !=
	    declaration->function_specializations.end())
		return;
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
			    !same_function_template_declaration_family(declaration,
			                                               candidate))
				continue;
			map<string, Binding*>::iterator found =
				candidate->function_specializations.find(key);
			if (found == candidate->function_specializations.end())
				continue;
			declaration->function_specializations[key] = found->second;
			return;
		}
	}
}

Binding* FunctionTemplateInstantiationEngine::reuse_existing_specialization(
	map<string, Binding*>::iterator existing,
	bool full_args_dependent)
{
	if (p.active_function_body_replays_.count(existing->second) != 0)
		return existing->second;
	bool existing_still_dependent =
		type_structurally_dependent(existing->second->type);
	bool existing_usable = full_args_dependent || !existing_still_dependent;
	bool existing_has_body =
		p.function_bodies_.find(existing->second) != p.function_bodies_.end();
	if (existing_has_body &&
	    p.function_template_placeholders_.find(existing->second) ==
		    p.function_template_placeholders_.end())
		return existing->second;
	bool need_constexpr_value_body =
		(p.template_argument_expression_depth_ != 0 ||
		 p.constexpr_value_expression_depth_ != 0) &&
		declaration->has_definition && existing->second->is_constexpr &&
		!existing_has_body;
	if (!need_constexpr_value_body &&
	    p.function_template_candidate_instantiation_depth_ != 0 &&
	    p.hosted_compatibility_ && !existing->second->is_object_root &&
	    hosted_internal_function_name(existing->second->name) &&
	    p.defer_hosted_function_body(existing->second))
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
	     existing->second->is_object_root))
		return existing->second;
	replaced_specialization = existing->second;
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
				subst[name] = pa11::make_template_parameter_type(name);
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
