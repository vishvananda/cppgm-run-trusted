#include "pa12_expr_semantics_support.h"
#include "pa12_templates_function_support.h"
#include "pa12_types_support.h"

#include <algorithm>
#include <functional>
#include <stdexcept>

using namespace std;

namespace pa12 {
namespace internal {

namespace {

size_t function_template_body_start(const vector<Token>& tokens,
                                    size_t begin,
                                    size_t end)
{
	for (size_t i = begin; i < end && i < tokens.size(); ++i)
		if (tokens[i].kind == posttoken::TokenKind::Simple &&
		    tokens[i].type == OP_LBRACE)
			return i;
	return end;
}

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

vector<ParameterInfo> function_body_parameters_from_type(
	Binding* function,
	const vector<string>& names)
{
	vector<ParameterInfo> parameters;
	if (function == NULL || function->type.get() == NULL ||
	    function->type->kind != pa11::TypeKind::Function)
		return parameters;
	size_t first = function->owner != NULL &&
	               function->owner->kind == ScopeKind::Class &&
	               !function->is_static_member ? 1 : 0;
	for (size_t i = first; i < function->type->parameters.size(); ++i)
	{
		ParameterInfo parameter;
		parameter.type = function->type->parameters[i];
		size_t name_index = i;
		if (first != 0 &&
		    (names.size() + first == function->type->parameters.size() ||
		     (names.size() == function->type->parameters.size() &&
		      !names.empty() &&
		      !names[0].empty() &&
		      names[0] != "this")))
			name_index = i - first;
		if (name_index < names.size())
			parameter.name = names[name_index];
		parameters.push_back(parameter);
	}
	for (size_t i = 0; i < parameters.size(); ++i)
	{
		size_t pack_pos = parameters[i].name.find("__pack");
		if (pack_pos == string::npos || pack_pos == 0)
			continue;
		string base_name = parameters[i].name.substr(0, pack_pos);
		parameters[i].pack_expression_name = base_name;
		for (size_t j = 0; j < parameters.size(); ++j)
			if (parameters[j].name == base_name ||
			    parameters[j].name.compare(0, base_name.size() + 6,
			                               base_name + "__pack") == 0)
				parameters[j].pack_expression_name = base_name;
	}
	return parameters;
}

bool parameter_names_have_non_this(const vector<string>& names)
{
	for (size_t i = 0; i < names.size(); ++i)
		if (!names[i].empty() && names[i] != "this")
			return true;
	return false;
}

void normalize_member_function_parameter_names(Binding* function,
                                               vector<string>& names)
{
	if (function == NULL || function->type.get() == NULL ||
	    function->type->kind != pa11::TypeKind::Function ||
	    function->owner == NULL ||
	    function->owner->kind != ScopeKind::Class ||
	    function->is_static_member)
		return;
	size_t parameter_count = function->type->parameters.size();
	if (parameter_count == 0)
		return;
	if (names.empty())
	{
		names.push_back("this");
		return;
	}
	if (names[0] == "this")
		return;
	if (names.size() < parameter_count)
	{
		names.insert(names.begin(), "this");
		return;
	}
	if (names.size() == parameter_count && names.back().empty())
	{
		names.insert(names.begin(), "this");
		names.pop_back();
	}
}

void expand_function_template_pack_parameter_names(
	TemplateDeclaration* declaration,
	Binding* function,
	vector<string>& names)
{
	if (declaration == NULL || function == NULL ||
	    declaration->generic_function_type.get() == NULL ||
	    declaration->generic_function_type->kind != pa11::TypeKind::Function ||
	    function->type.get() == NULL ||
	    function->type->kind != pa11::TypeKind::Function ||
	    names.size() >= function->type->parameters.size())
		return;
	bool has_function_parameter_pack = false;
	for (size_t i = 0;
	     i < declaration->generic_function_type->parameters.size();
	     ++i)
	{
		string pack_name;
		if (function_parameter_pack_name(
			    declaration,
			    declaration->generic_function_type->parameters[i],
			    pack_name))
			has_function_parameter_pack = true;
	}
	if (!has_function_parameter_pack)
		return;
	size_t concrete_count = function->type->parameters.size();
	size_t generic_count =
		declaration->generic_function_type->parameters.size();
	bool generic_has_owner_parameter =
		function->owner != NULL &&
		function->owner->kind == ScopeKind::Class &&
		!function->is_static_member &&
		generic_count != 0;
	bool saved_names_have_owner =
		!names.empty() && names[0] == "this";
	vector<string> expanded;
	for (size_t i = 0; i < generic_count; ++i)
	{
		size_t name_index = i;
		if (generic_has_owner_parameter && !saved_names_have_owner)
			name_index = i == 0 ? names.size() : i - 1;
		string source_name =
			name_index < names.size() ? names[name_index] : string();
		string pack_name;
		bool pack_parameter =
			function_parameter_pack_name(
				declaration,
				declaration->generic_function_type->parameters[i],
				pack_name);
		size_t repeat = 1;
		if (pack_parameter)
		{
			size_t remaining_patterns = generic_count - i - 1;
			repeat = concrete_count > expanded.size() + remaining_patterns
				? concrete_count - expanded.size() - remaining_patterns
				: 0;
		}
		for (size_t p = 0; p < repeat; ++p)
		{
			if (source_name.empty())
				expanded.push_back(string());
			else if (p == 0)
				expanded.push_back(source_name);
			else
				expanded.push_back(
					source_name + "__pack" + to_string(p + 1));
		}
	}
	if (expanded.size() == concrete_count)
		names = expanded;
}

void apply_replayed_function_type(Node& fn, TypePtr type)
{
	if (fn.binding == NULL ||
	    type.get() == NULL ||
	    type->kind != pa11::TypeKind::Function)
		return;
	fn.binding->type = type;
	if (fn.binding->aliased_binding != NULL)
		fn.binding->aliased_binding->type = type;
	fn.type = type;
	size_t param_index = 0;
	for (size_t i = 0; i < fn.children.size() &&
	     param_index < type->parameters.size(); ++i)
	{
		if (fn.children[i].line.compare(0, 10, "parameter ") != 0)
			continue;
		string text = fn.children[i].line.substr(10);
		size_t space = text.find(' ');
		string name = space == string::npos ? text : text.substr(0, space);
		TypePtr param_type = type->parameters[param_index++];
		fn.children[i].type = param_type;
		if (fn.children[i].binding != NULL)
			fn.children[i].binding->type = param_type;
		fn.children[i].line =
			"parameter " + name + " " + pa11::describe_type(param_type);
	}
}

bool hosted_internal_function_name(const string& name)
{
	return name.size() >= 2 && name[0] == '_' && name[1] == '_';
}

bool scope_has_namespace_named(Scope* scope, const string& name)
{
	for (Scope* cur = scope; cur != NULL; cur = cur->parent)
		if (cur->kind == ScopeKind::Namespace && cur->name == name)
			return true;
	return false;
}

bool hosted_std_template_declaration(const TemplateDeclaration* declaration,
                                     const string& name)
{
	if (declaration == NULL || declaration->name != name)
		return false;
	Scope* scope =
		declaration->placeholder != NULL
		? declaration->placeholder->owner
		: declaration->owner;
	return scope_has_namespace_named(scope, "std");
}

string unqualified_template_primary_name(TypePtr type)
{
	TypePtr bare = type.get() != NULL ? pa11::strip_cv(type) : TypePtr();
	if (bare.get() == NULL)
		return "";
	string primary = bare->template_primary_name.empty()
		? bare->name : bare->template_primary_name;
	size_t pos = primary.rfind("::");
	return pos == string::npos ? primary : primary.substr(pos + 2);
}

bool hosted_std_template_record(TypePtr type, const string& primary)
{
	TypePtr bare = type.get() != NULL ? pa11::strip_cv(type) : TypePtr();
	return bare.get() != NULL &&
	       bare->kind == pa11::TypeKind::Record &&
	       bare->is_template_specialization &&
	       unqualified_template_primary_name(bare) == primary &&
	       scope_has_namespace_named(bare->scope, "std");
}

bool hosted_std_member_template_declaration(
	const TemplateDeclaration* declaration,
	const string& owner_primary,
	const string& name)
{
	if (declaration == NULL ||
	    declaration->name != name ||
	    declaration->owner == NULL ||
	    declaration->owner->kind != ScopeKind::Class)
		return false;
	return hosted_std_template_record(
		pa11::record_type_for_scope(declaration->owner),
		owner_primary);
}

TypePtr hosted_forwarding_argument_parameter(TypePtr argument)
{
	if (argument.get() == NULL)
		return argument;
	TypePtr bare = pa11::strip_cv(argument);
	if (bare->kind == pa11::TypeKind::LValueReference ||
	    bare->kind == pa11::TypeKind::RValueReference)
		return argument;
	return pa11::make_rvalue_reference(argument);
}

}  // namespace

Binding* Parser::instantiate_function_template(
	TemplateDeclaration* declaration,
	const vector<TemplateArgument>& arguments)
{
	bool defer_completed_value_expression_arguments =
		function_template_candidate_instantiation_depth_ == 0 &&
		arguments.size() == declaration->parameters.size();
	bool deferred_value_expression_completion_context = false;
	bool have_deferred_value_expression_argument = false;
	for (size_t i = 0;
	     defer_completed_value_expression_arguments && i < arguments.size();
	     ++i)
	{
		if (arguments[i].kind == TemplateArgumentKind::Value &&
		    arguments[i].dependent &&
		    arguments[i].value_expr_end > arguments[i].value_expr_begin)
			have_deferred_value_expression_argument = true;
		if (i < declaration->parameters.size() &&
		    declaration->parameters[i].kind == TemplateParameterKind::NonType &&
		    declaration->parameters[i].has_default &&
		    type_is_template_dependent(declaration->parameters[i].type))
			have_deferred_value_expression_argument = true;
	}
	defer_completed_value_expression_arguments =
		defer_completed_value_expression_arguments &&
		have_deferred_value_expression_argument;
	if (defer_completed_value_expression_arguments)
	{
		++function_template_candidate_instantiation_depth_;
		deferred_value_expression_completion_context = true;
	}
	vector<TemplateArgument> full_args;
	try
	{
		full_args = complete_template_arguments(declaration, arguments);
	}
	catch (const runtime_error& err)
	{
		if (defer_completed_value_expression_arguments)
		{
			--function_template_candidate_instantiation_depth_;
			defer_completed_value_expression_arguments = false;
		}
			if ((!deferred_value_expression_completion_context &&
			     function_template_candidate_instantiation_depth_ == 0) ||
			    string(err.what()) != "dependent typename not resolved" ||
			    arguments.size() != declaration->parameters.size() ||
			    (!deferred_value_expression_completion_context &&
			     template_arguments_contain_disabled_enable_if(arguments)))
				throw;
			full_args = arguments;
		}
	if (defer_completed_value_expression_arguments)
		--function_template_candidate_instantiation_depth_;
	string key = template_argument_key(full_args);
		if (!declaration->has_definition)
		{
			for (map<Scope*, map<string, vector<TemplateDeclaration*> > >::iterator
				     sit = function_templates_.begin();
			     sit != function_templates_.end(); ++sit)
			{
				map<string, vector<TemplateDeclaration*> >::iterator nit =
					sit->second.find(declaration->name);
				if (nit == sit->second.end())
					continue;
				for (size_t di = 0; di < nit->second.size(); ++di)
				{
					TemplateDeclaration* candidate = nit->second[di];
					if (candidate == declaration ||
					    candidate == NULL ||
					    !candidate->has_definition ||
					    candidate->generic_function_type.get() == NULL ||
					    declaration->generic_function_type.get() == NULL ||
					    !same_template_signature_type(
						    candidate->generic_function_type,
						    declaration->generic_function_type))
						continue;
					size_t required_arguments = 0;
					for (size_t pi = 0;
					     pi < candidate->parameters.size();
					     ++pi)
						if (!candidate->parameters[pi].has_default &&
						    !candidate->parameters[pi].is_pack)
							++required_arguments;
					if (arguments.size() < required_arguments)
						continue;
					try
					{
						complete_template_arguments(candidate,
						                            arguments);
					}
					catch (const exception&)
					{
						continue;
					}
					return instantiate_function_template(candidate,
					                                     arguments);
				}
			}
		}
	validate_function_template_definition(declaration);
	bool full_args_dependent = template_arguments_dependent(full_args);
	map<string, Binding*>::iterator existing =
		declaration->function_specializations.find(key);
	if (existing == declaration->function_specializations.end())
	{
		for (map<Scope*, map<string, vector<TemplateDeclaration*> > >::iterator
			     sit = function_templates_.begin();
		     sit != function_templates_.end();
		     ++sit)
		{
			map<string, vector<TemplateDeclaration*> >::iterator nit =
				sit->second.find(declaration->name);
			if (nit == sit->second.end())
				continue;
			for (size_t di = 0; di < nit->second.size(); ++di)
			{
				TemplateDeclaration* candidate = nit->second[di];
				if (candidate == declaration ||
				    candidate == NULL ||
				    !same_function_template_declaration_family(
					    declaration,
					    candidate))
					continue;
				map<string, Binding*>::iterator found =
					candidate->function_specializations.find(key);
				if (found == candidate->function_specializations.end())
					continue;
				declaration->function_specializations[key] =
					found->second;
				existing = declaration->function_specializations.find(key);
				break;
			}
			if (existing != declaration->function_specializations.end())
				break;
		}
	}
	Binding* replaced_specialization = NULL;
		if (existing != declaration->function_specializations.end())
		{
			if (active_function_body_replays_.count(existing->second) != 0)
				return existing->second;
			bool existing_still_dependent =
				type_structurally_dependent(existing->second->type);
			bool existing_usable =
				full_args_dependent || !existing_still_dependent;
			bool existing_has_body =
				function_bodies_.find(existing->second) !=
				function_bodies_.end();
			if (existing_has_body &&
			    function_template_placeholders_.find(existing->second) ==
				    function_template_placeholders_.end())
				return existing->second;
			bool need_constexpr_value_body =
				(template_argument_expression_depth_ != 0 ||
				 constexpr_value_expression_depth_ != 0) &&
				declaration->has_definition &&
				existing->second->is_constexpr &&
				!existing_has_body;
			if (!need_constexpr_value_body &&
			    function_template_candidate_instantiation_depth_ != 0 &&
			    hosted_compatibility_ &&
			    !existing->second->is_object_root &&
			    hosted_internal_function_name(existing->second->name) &&
			    defer_hosted_function_body(existing->second))
				return existing->second;
			if (function_template_candidate_instantiation_depth_ != 0 &&
			    existing_usable &&
			    !need_constexpr_value_body)
				return existing->second;
		if (!existing_usable &&
		    !full_args_dependent &&
		    !declaration->class_template_member &&
		    existing->second->is_inline_definition &&
		    existing_has_body)
			existing_usable = true;
		bool existing_dependent_return =
			existing->second->type.get() != NULL &&
			existing->second->type->kind == pa11::TypeKind::Function &&
			type_is_template_dependent(existing->second->type->base);
			if (!declaration->has_definition && !existing_dependent_return &&
			    existing_usable)
				return existing->second;
			if (existing_usable &&
			    ((existing->second->is_inline_definition && existing_has_body) ||
			     existing->second->is_object_root))
				return existing->second;
		replaced_specialization = existing->second;
		declaration->function_specializations.erase(existing);
	}
	if (declaration->completing_specializations.count(key) != 0)
		throw runtime_error("recursive function template instantiation");
	declaration->completing_specializations.insert(key);

	size_t save_pos = pos_;
	vector<Scope*> save_scopes = scopes_;
	vector<map<string, TypePtr> > save_subst = template_type_substitutions_;
	vector<map<string, TemplateArgument> > save_value_subst =
		template_value_substitutions_;
	vector<set<string> > save_pack_subst = template_type_parameter_packs_;
	bool save_force_new_function_binding = force_new_function_binding_;
	bool save_defer_function_template_bodies =
		defer_function_template_bodies_;
	bool save_suppress_implicit_template_base_init =
		suppress_implicit_template_base_init_;
	bool save_override_function_parameter_names =
		override_function_parameter_names_;
	vector<string> save_function_parameter_name_override =
		function_parameter_name_override_;
	const auto restore_instantiation_state = [&]() {
		declaration->completing_specializations.erase(key);
		template_type_substitutions_ = save_subst;
		template_value_substitutions_ = save_value_subst;
		template_type_parameter_packs_ = save_pack_subst;
		scopes_ = save_scopes;
		pos_ = save_pos;
		force_new_function_binding_ = save_force_new_function_binding;
		defer_function_template_bodies_ =
			save_defer_function_template_bodies;
		suppress_implicit_template_base_init_ =
			save_suppress_implicit_template_base_init;
		override_function_parameter_names_ =
			save_override_function_parameter_names;
		function_parameter_name_override_ =
			save_function_parameter_name_override;
	};
	map<string, TypePtr> subst;
	map<string, TemplateArgument> value_subst;
	set<string> pack_subst;
	for (size_t i = 0; i < full_args.size() &&
	     i < declaration->parameters.size(); ++i)
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
						full_args[i];
					pack_subst.insert(declaration->parameters[i].name);
				}
				else
					subst[declaration->parameters[i].name] =
						full_args[i].type;
			}
			else
				value_subst[declaration->parameters[i].name] =
					full_args[i];
		}
	template_type_substitutions_.insert(
		template_type_substitutions_.end(),
		declaration->outer_type_substitutions.begin(),
		declaration->outer_type_substitutions.end());
	template_value_substitutions_.insert(
		template_value_substitutions_.end(),
			declaration->outer_value_substitutions.begin(),
			declaration->outer_value_substitutions.end());
	template_type_substitutions_.push_back(subst);
	template_value_substitutions_.push_back(value_subst);
	template_type_parameter_packs_.push_back(pack_subst);
	scopes_.clear();
	scopes_.push_back(declaration->lexical_scope != NULL
	                  ? declaration->lexical_scope
	                  : declaration->owner);
	bool dependent = false;
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
				if (type_is_template_dependent(arg.type))
					dependent = true;
			}
				else if (arg.kind == TemplateArgumentKind::Value)
				{
					if (arg.dependent)
						dependent = true;
				}
				else if (arg.kind == TemplateArgumentKind::Template)
				{
					if (arg.template_declaration == NULL)
						dependent = true;
				}
				else
				{
					for (size_t p = 0; p < arg.pack.size(); ++p)
					pending.push_back(arg.pack[p]);
			}
		}
	}
	if (dependent)
	{
			TypePtr type;
			try
				{
					type = substitute_function_template_type(
						declaration,
						declaration->generic_function_type);
				}
				catch (const runtime_error& err)
				{
				if (function_template_candidate_instantiation_depth_ == 0 ||
				    string(err.what()) != "dependent typename not resolved" ||
					    declaration->generic_function_type.get() == NULL ||
					    declaration->generic_function_type->kind !=
						    pa11::TypeKind::Function)
					{
						restore_instantiation_state();
						throw;
					}
					vector<TypePtr> params;
				for (size_t i = 0;
				     i < declaration->generic_function_type->parameters.size();
				     ++i)
					params.push_back(substitute_template_type(
						declaration->generic_function_type->parameters[i]));
				type = pa11::make_function(
					declaration->generic_function_type->base,
					params,
					declaration->generic_function_type->variadic);
				type->cv = declaration->generic_function_type->cv;
				type->ref_qualifier =
					declaration->generic_function_type->ref_qualifier;
			}
			bool distinct_conversion_template =
				declaration->name.compare(0, 9, "operator ") == 0 &&
				!declaration->class_template_member;
			Binding* binding =
				function_template_candidate_instantiation_depth_ != 0 ||
				distinct_conversion_template
				? add_value(declaration->owner,
				            BindingKind::Function,
				            declaration->name,
				            type)
				: add_function_binding(declaration->owner,
				                       declaration->name,
				                       type,
				                       declaration->hidden_friend);
			binding->is_hidden_friend = declaration->hidden_friend;
		if (declaration->placeholder != NULL)
		{
			binding->is_static_member =
				declaration->placeholder->is_static_member;
			binding->is_constexpr =
				declaration->placeholder->is_constexpr;
			binding->is_explicit =
				declaration->placeholder->is_explicit;
			binding->is_private =
				declaration->placeholder->is_private;
			binding->is_protected_member =
				declaration->placeholder->is_protected_member;
			binding->ref_qualifier =
				declaration->placeholder->ref_qualifier;
			binding->unwind_no = declaration->placeholder->unwind_no;
			if (declaration->placeholder->reserve_primary_function_symbol)
				binding->reserve_primary_function_symbol = true;
			map<Binding*, vector<Expr> >::const_iterator defaults =
				default_arguments_.find(declaration->placeholder);
			if (defaults != default_arguments_.end())
				default_arguments_[binding] = defaults->second;
		}
		if (declaration->class_template_member)
			binding->function_specialization_symbol =
				constructor_template_function_template_symbol(declaration) ||
				class_template_member_function_template_symbol(declaration)
				? abi_function_template_specialization_symbol(
					declaration,
					full_args,
					binding,
					&declaration_tokens_)
				: abi_binding_symbol(binding, map<string, size_t>());
		declaration->function_specializations[key] = binding;
		if (declaration->friend_class_scope != NULL)
			add_friend_function(declaration->friend_class_scope, binding);
			function_template_placeholders_[binding] = declaration;
			function_template_specialization_arguments_[binding] = full_args;
			declaration->completing_specializations.erase(key);
			template_type_substitutions_ = save_subst;
			template_value_substitutions_ = save_value_subst;
			template_type_parameter_packs_ = save_pack_subst;
		scopes_ = save_scopes;
		pos_ = save_pos;
		force_new_function_binding_ = save_force_new_function_binding;
		defer_function_template_bodies_ =
			save_defer_function_template_bodies;
		suppress_implicit_template_base_init_ =
			save_suppress_implicit_template_base_init;
		return binding;
	}
	TypePtr generic_return =
		declaration->generic_function_type.get() != NULL &&
		declaration->generic_function_type->kind == pa11::TypeKind::Function
		? pa11::strip_cv(declaration->generic_function_type->base)
		: TypePtr();
	bool generic_return_is_decltype =
		generic_return.get() != NULL &&
		generic_return->is_dependent_typename &&
		generic_return->dependent_typename_decltype;
			bool has_template_parameter_default = false;
			for (size_t i = 0; i < declaration->parameters.size(); ++i)
				if (declaration->parameters[i].has_default)
					has_template_parameter_default = true;
			bool replay_candidate_signature =
				function_template_candidate_instantiation_depth_ != 0 &&
				declaration->has_definition &&
				declaration->decl_begin < declaration->decl_end &&
				has_template_parameter_default;
			if (!declaration->constructor_template &&
			    !replay_candidate_signature &&
			    ((!declaration->has_definition &&
		      (replaying_dependent_decltype_ ||
		       (function_template_candidate_instantiation_depth_ != 0 &&
	        !generic_return_is_decltype))) ||
	     function_template_candidate_instantiation_depth_ != 0))
	{
		TypePtr type;
			bool deferred_candidate_return =
				function_template_candidate_instantiation_depth_ != 0 &&
				generic_return_is_decltype &&
				dependent &&
				declaration->generic_function_type.get() != NULL &&
				declaration->generic_function_type->kind ==
					pa11::TypeKind::Function;
		if (deferred_candidate_return)
		{
			vector<TypePtr> params;
			for (size_t i = 0;
			     i < declaration->generic_function_type->parameters.size();
			     ++i)
			{
				TypePtr pattern =
					declaration->generic_function_type->parameters[i];
				string pack_name;
				TemplateArgument pack_subst;
				if (function_parameter_pack_name(declaration,
				                                 pattern,
				                                 pack_name) &&
				    find_template_value_substitution(pack_name,
				                                     pack_subst) &&
				    pack_subst.kind == TemplateArgumentKind::Pack)
				{
					for (size_t p = 0; p < pack_subst.pack.size(); ++p)
					{
						if (pack_subst.pack[p].kind !=
						    TemplateArgumentKind::Type)
							throw runtime_error(
								"type parameter pack required");
						TypePtr element =
							substitute_template_type_parameter(
								pattern,
								pack_name,
								pack_subst.pack[p].type);
						params.push_back(substitute_template_type(element));
					}
					continue;
				}
				params.push_back(substitute_template_type(pattern));
			}
			type = pa11::make_function(
				declaration->generic_function_type->base,
				params,
				declaration->generic_function_type->variadic);
			type->cv = declaration->generic_function_type->cv;
			type->ref_qualifier =
				declaration->generic_function_type->ref_qualifier;
		}
		else
		{
			try
			{
				type = substitute_function_template_type(
					declaration,
					declaration->generic_function_type);
			}
				catch (const runtime_error& err)
				{
					string message = err.what();
					if (function_template_candidate_instantiation_depth_ == 0 ||
					    !generic_return_is_decltype ||
					    message.compare(0, 16, "name not found: ") != 0 ||
					    declaration->generic_function_type.get() == NULL ||
					    declaration->generic_function_type->kind !=
						    pa11::TypeKind::Function)
					{
						restore_instantiation_state();
						throw;
					}
					vector<TypePtr> params;
				for (size_t i = 0;
				     i < declaration->generic_function_type->parameters.size();
				     ++i)
					params.push_back(substitute_template_type(
						declaration->generic_function_type->parameters[i]));
				type = pa11::make_function(
					declaration->generic_function_type->base,
					params,
					declaration->generic_function_type->variadic);
				type->cv = declaration->generic_function_type->cv;
				type->ref_qualifier =
					declaration->generic_function_type->ref_qualifier;
					deferred_candidate_return = true;
				}
			}
			if (hosted_compatibility_ &&
			    function_template_candidate_instantiation_depth_ != 0 &&
			    hosted_std_template_declaration(declaration, "__write") &&
			    type.get() != NULL &&
			    type->kind == pa11::TypeKind::Function &&
			    (type_structurally_dependent(type) ||
			     !substituted_type_is_valid(type)) &&
			    !full_args.empty() &&
			    full_args[0].kind == TemplateArgumentKind::Type &&
			    full_args[0].type.get() != NULL &&
			    !type_structurally_dependent(full_args[0].type))
			{
				TypePtr char_type = full_args[0].type;
				TypePtr out_iter;
				if (full_args.size() == 1)
				{
					TemplateDeclaration* iter_template =
						find_class_template(declaration->owner,
						                    "ostreambuf_iterator");
					if (iter_template != NULL)
					{
						vector<TemplateArgument> iter_args;
						iter_args.push_back(
							TemplateArgument::type_arg(char_type));
						try
						{
							out_iter = instantiate_class_template(
								iter_template,
								iter_args);
						}
						catch (const exception&)
						{
							out_iter = TypePtr();
						}
					}
				}
				else if (full_args.size() >= 2 &&
				         full_args[1].kind == TemplateArgumentKind::Type &&
				         full_args[1].type.get() != NULL &&
				         !type_structurally_dependent(full_args[1].type))
				{
					out_iter = full_args[1].type;
				}
				if (out_iter.get() != NULL &&
				    !type_structurally_dependent(out_iter))
				{
					vector<TypePtr> params;
					params.push_back(out_iter);
					params.push_back(pa11::make_pointer(pa11::make_cv(
						char_type,
						pa11::CV_CONST)));
					params.push_back(pa11::make_fundamental(FT_INT));
					TypePtr modeled =
						pa11::make_function(out_iter, params, false);
					modeled->cv = type->cv;
					modeled->ref_qualifier = type->ref_qualifier;
					type = modeled;
				}
			}
			if (hosted_compatibility_ &&
			    function_template_candidate_instantiation_depth_ != 0 &&
			    type.get() != NULL &&
			    type->kind == pa11::TypeKind::Function &&
			    (type_structurally_dependent(type) ||
			     !substituted_type_is_valid(type)) &&
			    hosted_std_member_template_declaration(declaration,
			                                           "function",
			                                           "operator=") &&
			    !full_args.empty() &&
			    full_args[0].kind == TemplateArgumentKind::Type &&
			    full_args[0].type.get() != NULL &&
			    !type_structurally_dependent(full_args[0].type))
			{
				TypePtr owner_record =
					pa11::record_type_for_scope(declaration->owner);
				owner_record = owner_record.get() != NULL
					? pa11::strip_cv(owner_record) : TypePtr();
				if (hosted_std_template_record(owner_record, "function") &&
				    type->parameters.size() == 2)
				{
					vector<TypePtr> params;
					params.push_back(type->parameters[0]);
					params.push_back(hosted_forwarding_argument_parameter(
						full_args[0].type));
					TypePtr modeled = pa11::make_function(
						pa11::make_lvalue_reference(owner_record),
						params,
						false);
					modeled->cv = type->cv;
					modeled->ref_qualifier = type->ref_qualifier;
					type = modeled;
				}
			}
			if (hosted_compatibility_ &&
			    function_template_candidate_instantiation_depth_ != 0 &&
			    type.get() != NULL &&
			    type->kind == pa11::TypeKind::Function &&
			    (type_structurally_dependent(type) ||
			     !substituted_type_is_valid(type)) &&
			    hosted_std_member_template_declaration(declaration,
			                                           "vector",
			                                           "insert") &&
			    !full_args.empty() &&
			    full_args[0].kind == TemplateArgumentKind::Type &&
			    full_args[0].type.get() != NULL &&
			    !type_structurally_dependent(full_args[0].type) &&
			    type->parameters.size() == 4)
			{
				vector<TypePtr> params = type->parameters;
				params[2] = full_args[0].type;
				params[3] = full_args[0].type;
				TypePtr modeled = pa11::make_function(type->base,
				                                      params,
				                                      false);
				modeled->cv = type->cv;
				modeled->ref_qualifier = type->ref_qualifier;
				if (!type_structurally_dependent(modeled))
					type = modeled;
			}
					bool invalid_substituted_type = deferred_candidate_return
				    ? !substituted_function_parameter_types_are_valid(type)
				    : !substituted_type_is_valid(type);
			if (invalid_substituted_type &&
			    function_template_candidate_instantiation_depth_ != 0 &&
		    type.get() != NULL &&
		    type->kind == pa11::TypeKind::Function &&
		    deferred_candidate_return &&
		    ((type_is_template_dependent(type->base) &&
		      substituted_function_parameter_types_are_valid(type)) ||
		     substituted_candidate_function_parameter_types_are_valid(type)))
			invalid_substituted_type = false;
			if (invalid_substituted_type)
			{
				declaration->completing_specializations.erase(key);
				template_type_substitutions_ = save_subst;
				template_value_substitutions_ = save_value_subst;
			template_type_parameter_packs_ = save_pack_subst;
			scopes_ = save_scopes;
			pos_ = save_pos;
			force_new_function_binding_ = save_force_new_function_binding;
			defer_function_template_bodies_ =
				save_defer_function_template_bodies;
			suppress_implicit_template_base_init_ =
				save_suppress_implicit_template_base_init;
			throw runtime_error("invalid substituted function type");
		}
			bool distinct_conversion_template =
				declaration->name.compare(0, 9, "operator ") == 0 &&
				!declaration->class_template_member;
			Binding* binding =
				function_template_candidate_instantiation_depth_ != 0 ||
				distinct_conversion_template
				? add_value(declaration->owner,
				            BindingKind::Function,
				            declaration->name,
				            type)
				: add_function_binding(declaration->owner,
				                       declaration->name,
				                       type,
				                       declaration->hidden_friend);
			binding->is_hidden_friend = declaration->hidden_friend;
		if (declaration->placeholder != NULL)
		{
			binding->is_static_member =
				declaration->placeholder->is_static_member;
			binding->is_constexpr =
				declaration->placeholder->is_constexpr;
			binding->is_explicit =
				declaration->placeholder->is_explicit;
			binding->is_private =
				declaration->placeholder->is_private;
			binding->is_protected_member =
				declaration->placeholder->is_protected_member;
			binding->ref_qualifier =
				declaration->placeholder->ref_qualifier;
			binding->unwind_no = declaration->placeholder->unwind_no;
			if (declaration->placeholder->reserve_primary_function_symbol)
				binding->reserve_primary_function_symbol = true;
			map<Binding*, vector<Expr> >::const_iterator defaults =
				default_arguments_.find(declaration->placeholder);
			if (defaults != default_arguments_.end())
				default_arguments_[binding] = defaults->second;
		}
		if (replaced_specialization != NULL &&
		    replaced_specialization != binding)
			replaced_specialization->aliased_binding = binding;
		if (declaration->class_template_member)
			binding->function_specialization_symbol =
				constructor_template_function_template_symbol(declaration) ||
				class_template_member_function_template_symbol(declaration)
				? abi_function_template_specialization_symbol(
					declaration,
					full_args,
					binding,
					&declaration_tokens_)
				: abi_binding_symbol(binding, map<string, size_t>());
		else
			binding->function_specialization_symbol =
				abi_function_template_specialization_symbol(declaration,
				                                            full_args,
				                                            binding,
				                                            &declaration_tokens_);
		declaration->function_specializations[key] = binding;
		if (declaration->friend_class_scope != NULL)
			add_friend_function(declaration->friend_class_scope, binding);
		if (!declaration->class_template_member ||
		    function_template_candidate_instantiation_depth_ != 0)
			{
				function_template_placeholders_[binding] = declaration;
				function_template_specialization_arguments_[binding] = full_args;
			}
		declaration->completing_specializations.erase(key);
		template_type_substitutions_ = save_subst;
		template_value_substitutions_ = save_value_subst;
		template_type_parameter_packs_ = save_pack_subst;
		scopes_ = save_scopes;
		pos_ = save_pos;
		force_new_function_binding_ = save_force_new_function_binding;
		defer_function_template_bodies_ =
			save_defer_function_template_bodies;
		suppress_implicit_template_base_init_ =
			save_suppress_implicit_template_base_init;
		return binding;
	}
	if (declaration->constructor_template &&
	    function_template_candidate_instantiation_depth_ != 0)
	{
		TypePtr type;
		try
		{
			type = substitute_function_template_type(
				declaration,
				declaration->generic_function_type);
		}
		catch (...)
		{
			restore_instantiation_state();
			throw;
		}
		if (!substituted_type_is_valid(type))
		{
			declaration->completing_specializations.erase(key);
			template_type_substitutions_ = save_subst;
			template_value_substitutions_ = save_value_subst;
			template_type_parameter_packs_ = save_pack_subst;
			scopes_ = save_scopes;
			pos_ = save_pos;
			force_new_function_binding_ = save_force_new_function_binding;
			defer_function_template_bodies_ =
				save_defer_function_template_bodies;
			suppress_implicit_template_base_init_ =
				save_suppress_implicit_template_base_init;
			throw runtime_error("invalid substituted constructor type");
		}
			Binding* binding =
				add_value(declaration->owner,
				          BindingKind::Function,
				          declaration->name,
				          type);
			binding->is_hidden_friend = declaration->hidden_friend;
		if (declaration->placeholder != NULL)
		{
			binding->is_static_member =
				declaration->placeholder->is_static_member;
			binding->is_constexpr =
				declaration->placeholder->is_constexpr;
			binding->is_explicit =
				declaration->placeholder->is_explicit;
			binding->is_private =
				declaration->placeholder->is_private;
			binding->is_protected_member =
				declaration->placeholder->is_protected_member;
			binding->ref_qualifier =
				declaration->placeholder->ref_qualifier;
			binding->unwind_no = declaration->placeholder->unwind_no;
			if (declaration->placeholder->reserve_primary_function_symbol)
				binding->reserve_primary_function_symbol = true;
		}
		if (replaced_specialization != NULL &&
		    replaced_specialization != binding)
			replaced_specialization->aliased_binding = binding;
		if (declaration->class_template_member)
			binding->function_specialization_symbol =
				constructor_template_function_template_symbol(declaration) ||
				class_template_member_function_template_symbol(declaration)
				? abi_function_template_specialization_symbol(
					declaration,
					full_args,
					binding,
					&declaration_tokens_)
				: abi_binding_symbol(binding, map<string, size_t>());
		else
			binding->function_specialization_symbol =
				abi_function_template_specialization_symbol(declaration,
				                                            full_args,
				                                            binding,
				                                            &declaration_tokens_);
		declaration->function_specializations[key] = binding;
		if (declaration->friend_class_scope != NULL)
			add_friend_function(declaration->friend_class_scope, binding);
		function_template_placeholders_[binding] = declaration;
		function_template_specialization_arguments_[binding] = full_args;
		declaration->completing_specializations.erase(key);
		template_type_substitutions_ = save_subst;
		template_value_substitutions_ = save_value_subst;
		template_type_parameter_packs_ = save_pack_subst;
		scopes_ = save_scopes;
		pos_ = save_pos;
		force_new_function_binding_ = save_force_new_function_binding;
		defer_function_template_bodies_ =
			save_defer_function_template_bodies;
		suppress_implicit_template_base_init_ =
			save_suppress_implicit_template_base_init;
		return binding;
	}
	if (!declaration->constructor_template &&
	    declaration->has_definition &&
	    declaration->placeholder != NULL &&
	    declaration->owner != NULL &&
	    declaration->owner->kind == ScopeKind::Class &&
	    function_template_candidate_instantiation_depth_ == 0)
	{
		TypePtr owner_record = pa11::record_type_for_scope(
			declaration->owner);
		owner_record = owner_record.get() != NULL
			? pa11::strip_cv(owner_record) : TypePtr();
		map<const void*, TemplateDeclaration*>::iterator owner_template =
			owner_record.get() != NULL
			? record_template_declarations_.find(owner_record.get())
			: record_template_declarations_.end();
		bool ordinary_class_template_member =
			declaration->class_template_member &&
			declaration->outer_type_substitutions.empty() &&
			((owner_template != record_template_declarations_.end() &&
			 template_parameter_lists_equivalent(
				 declaration->parameters,
				 owner_template->second->parameters)) ||
			(!declaration->name.empty() &&
			 (declaration->name[0] == '~' ||
			  declaration->name.compare(0, 8, "operator") == 0)));
		size_t body_pos =
			function_template_body_start(tokens_,
			                             declaration->decl_begin,
			                             declaration->decl_end);
		if (ordinary_class_template_member &&
		    body_pos != declaration->decl_end)
		{
			Binding* binding = declaration->placeholder;
			vector<string> names;
					map<Binding*, vector<string> >::const_iterator saved_names =
						function_parameter_names_.find(binding);
					if (saved_names != function_parameter_names_.end())
						names = saved_names->second;
					if (!parameter_names_have_non_this(names) &&
					    parameter_names_have_non_this(
						    declaration->function_parameter_names))
						names = declaration->function_parameter_names;
					normalize_member_function_parameter_names(binding, names);
				expand_function_template_pack_parameter_names(
					declaration,
					binding,
					names);
				if (binding->type.get() != NULL &&
				    binding->type->kind == pa11::TypeKind::Function &&
				    names.size() < binding->type->parameters.size())
					names.resize(binding->type->parameters.size());
			function_parameter_names_[binding] = names;
			binding->function_parameter_names = names;
			declaration->function_specializations[key] = binding;
			function_template_placeholders_[binding] = declaration;
			function_template_specialization_arguments_[binding] =
				full_args;
			PendingFunctionBody pending;
			pending.function = binding;
			pending.node = Node("function-definition " +
			                    qualified_decl_name(binding) + " " +
			                    pa11::describe_type(binding->type));
			pending.node.binding = binding;
			pending.node.type = binding->type;
			pending.parameters =
				function_body_parameters_from_type(binding, names);
			pending.body_pos = body_pos;
			pending.class_type =
				binding->owner != NULL
				? pa11::record_type_for_scope(binding->owner)
				: TypePtr();
			pending.scopes.clear();
			pending.scopes.push_back(
				declaration->lexical_scope != NULL
				? declaration->lexical_scope
				: declaration->owner);
			pending.friend_class_scopes = active_friend_class_scopes_;
			pending.type_substitutions = template_type_substitutions_;
			pending.value_substitutions = template_value_substitutions_;
			pending.pack_substitutions = template_type_parameter_packs_;
			if (function_template_candidate_instantiation_depth_ == 0)
			{
				try
				{
					bool parsed = parse_pending_member_body_now(
						pending,
						force_function_template_body_instantiation_);
					if (!parsed)
					{
						if (binding->owner != NULL)
							pending_member_bodies_[binding->owner].
								push_back(pending);
						else
							pending_function_bodies_[binding] = pending;
					}
				}
				catch (...)
				{
					restore_instantiation_state();
					throw;
				}
			}
			else if (binding->owner != NULL)
				pending_member_bodies_[binding->owner].push_back(pending);
			restore_instantiation_state();
			return binding;
		}
		if (!ordinary_class_template_member &&
		    body_pos != declaration->decl_end)
		{
			TypePtr type;
			try
			{
				type = substitute_function_template_type(
					declaration,
					declaration->generic_function_type);
			}
			catch (...)
			{
				restore_instantiation_state();
				throw;
				}
					if (!substituted_type_is_valid(type))
					{
						restore_instantiation_state();
						throw runtime_error("invalid substituted function type");
					}
			Binding* binding =
				add_value(declaration->owner,
				          BindingKind::Function,
				          declaration->name,
				          type);
			binding->is_hidden_friend = declaration->hidden_friend;
			vector<string> names;
			if (declaration->placeholder != NULL)
			{
				binding->is_static_member =
					declaration->placeholder->is_static_member;
				binding->is_constexpr =
					declaration->placeholder->is_constexpr;
				binding->is_explicit =
					declaration->placeholder->is_explicit;
				binding->is_private =
					declaration->placeholder->is_private;
				binding->is_protected_member =
					declaration->placeholder->is_protected_member;
				binding->ref_qualifier =
					declaration->placeholder->ref_qualifier;
				binding->unwind_no =
					declaration->placeholder->unwind_no;
					if (declaration->placeholder->
					    reserve_primary_function_symbol)
						binding->reserve_primary_function_symbol = true;
					map<Binding*, vector<string> >::const_iterator saved_names =
						function_parameter_names_.find(
							declaration->placeholder);
					if (saved_names != function_parameter_names_.end())
						names = saved_names->second;
					if (!parameter_names_have_non_this(names) &&
					    parameter_names_have_non_this(
						    declaration->function_parameter_names))
						names = declaration->function_parameter_names;
					map<Binding*, vector<Expr> >::const_iterator defaults =
						default_arguments_.find(declaration->placeholder);
					if (defaults != default_arguments_.end())
						default_arguments_[binding] = defaults->second;
				}
				normalize_member_function_parameter_names(binding, names);
				expand_function_template_pack_parameter_names(
					declaration,
					binding,
					names);
				if (type.get() != NULL &&
				    type->kind == pa11::TypeKind::Function &&
				    names.size() < type->parameters.size())
					names.resize(type->parameters.size());
			function_parameter_names_[binding] = names;
			binding->function_parameter_names = names;
			if (replaced_specialization != NULL &&
			    replaced_specialization != binding)
				replaced_specialization->aliased_binding = binding;
			if (declaration->class_template_member)
				binding->function_specialization_symbol =
					constructor_template_function_template_symbol(declaration) ||
					class_template_member_function_template_symbol(
						declaration)
					? abi_function_template_specialization_symbol(
						declaration,
						full_args,
						binding,
						&declaration_tokens_)
					: abi_binding_symbol(binding,
					                     map<string, size_t>());
			else
				binding->function_specialization_symbol =
					abi_function_template_specialization_symbol(
						declaration,
						full_args,
						binding,
						&declaration_tokens_);
			declaration->function_specializations[key] = binding;
			if (declaration->friend_class_scope != NULL)
				add_friend_function(declaration->friend_class_scope,
				                    binding);
			function_template_placeholders_[binding] = declaration;
			function_template_specialization_arguments_[binding] =
				full_args;
			PendingFunctionBody pending;
			pending.function = binding;
			pending.node = Node("function-definition " +
			                    qualified_decl_name(binding) + " " +
			                    pa11::describe_type(binding->type));
			pending.node.binding = binding;
			pending.node.type = binding->type;
			pending.parameters =
				function_body_parameters_from_type(binding, names);
			pending.body_pos = body_pos;
			pending.class_type =
				binding->owner != NULL
				? pa11::record_type_for_scope(binding->owner)
				: TypePtr();
			pending.scopes.clear();
			pending.scopes.push_back(
				declaration->lexical_scope != NULL
				? declaration->lexical_scope
				: declaration->owner);
			pending.friend_class_scopes = active_friend_class_scopes_;
			pending.type_substitutions = template_type_substitutions_;
			pending.value_substitutions = template_value_substitutions_;
			pending.pack_substitutions = template_type_parameter_packs_;
			if (function_template_candidate_instantiation_depth_ == 0)
			{
				try
				{
					bool parsed = parse_pending_member_body_now(
						pending,
						force_function_template_body_instantiation_);
					if (!parsed)
					{
						if (binding->owner != NULL)
							pending_member_bodies_[binding->owner].
								push_back(pending);
						else
							pending_function_bodies_[binding] = pending;
					}
				}
				catch (...)
				{
					restore_instantiation_state();
					throw;
				}
			}
			else if (binding->owner != NULL)
				pending_member_bodies_[binding->owner].push_back(pending);
			restore_instantiation_state();
			return binding;
		}
	}
	scopes_.clear();
	scopes_.push_back(declaration->lexical_scope != NULL
	                  ? declaration->lexical_scope
	                  : declaration->owner);
	pos_ = declaration->decl_begin;
	force_new_function_binding_ = true;
	defer_function_template_bodies_ =
		!force_function_template_body_instantiation_;
	if (declaration->placeholder != NULL &&
	    declaration->generic_function_type.get() != NULL &&
	    declaration->generic_function_type->kind == pa11::TypeKind::Function)
	{
			map<Binding*, vector<string> >::const_iterator saved_names =
				function_parameter_names_.find(declaration->placeholder);
		if (saved_names != function_parameter_names_.end())
		{
			vector<string> replay_names;
			bool saved_names_already_expanded = false;
			for (size_t i = 0; i < saved_names->second.size(); ++i)
				if (saved_names->second[i].find("__pack") != string::npos)
					saved_names_already_expanded = true;
			bool generic_has_owner_parameter = false;
			if (!declaration->generic_function_type->parameters.empty())
			{
				TypePtr first = pa11::strip_cv(
					declaration->generic_function_type->parameters[0]);
				generic_has_owner_parameter =
					first.get() != NULL &&
					first->kind == pa11::TypeKind::Pointer &&
					pa11::strip_cv(first->base)->kind ==
						pa11::TypeKind::Record;
			}
			if (saved_names_already_expanded ||
			    (generic_has_owner_parameter &&
			     !saved_names->second.empty() &&
			     saved_names->second[0] == "this"))
				replay_names = saved_names->second;
			else
			{
				bool skip_owner_name =
					generic_has_owner_parameter &&
					(saved_names->second.empty() ||
					 saved_names->second[0] != "this");
				for (size_t i = 0;
				     i < declaration->generic_function_type->parameters.size();
				     ++i)
				{
					if (skip_owner_name && i == 0)
						continue;
				TypePtr pattern =
					declaration->generic_function_type->parameters[i];
				size_t source_index = skip_owner_name ? i - 1 : i;
					string source_name =
						source_index < saved_names->second.size()
						? saved_names->second[source_index] : string();
					string pack_name;
				TemplateArgument subst_arg;
				if (function_parameter_pack_name(declaration,
				                                 pattern,
				                                 pack_name) &&
					    find_template_value_substitution(pack_name,
					                                     subst_arg) &&
						    subst_arg.kind == TemplateArgumentKind::Pack)
						{
							if (source_name.empty() &&
							    !replay_names.empty() &&
							    !replay_names.back().empty() &&
							    replay_names.back().compare(0, 7, "__param") != 0)
								source_name =
									generated_pack_parameter_name(pack_name);
							for (size_t p = 0; p < subst_arg.pack.size(); ++p)
						{
						if (source_name.empty())
							replay_names.push_back(string());
						else if (p == 0)
							replay_names.push_back(source_name);
						else
							replay_names.push_back(
								source_name + "__pack" +
								to_string(p + 1));
					}
					continue;
				}
				replay_names.push_back(source_name);
			}
			}
				if (declaration->placeholder != NULL &&
				    declaration->placeholder->is_static_member &&
				    !replay_names.empty() &&
				    replay_names[0] == "this")
					replay_names.erase(replay_names.begin());
				if (!replay_names.empty())
			{
				override_function_parameter_names_ = true;
				function_parameter_name_override_ = replay_names;
			}
		}
	}
	bool class_template_constructor_replay = false;
	if (declaration->constructor_template &&
	    declaration->owner != NULL &&
	    declaration->owner->kind == ScopeKind::Class)
	{
		TypePtr owner_record =
			pa11::record_type_for_scope(declaration->owner);
		owner_record = owner_record.get() != NULL
			? pa11::strip_cv(owner_record) : TypePtr();
		map<const void*, TemplateDeclaration*>::iterator owner_template =
			owner_record.get() != NULL
			? record_template_declarations_.find(owner_record.get())
			: record_template_declarations_.end();
		if (owner_template != record_template_declarations_.end() &&
		    template_parameter_lists_equivalent(
			    declaration->parameters,
			    owner_template->second->parameters))
			class_template_constructor_replay = true;
	}
	suppress_implicit_template_base_init_ =
		save_suppress_implicit_template_base_init ||
		class_template_constructor_replay;
	size_t friend_scope_depth = active_friend_class_scopes_.size();
	if (declaration->friend_class_scope != NULL)
		active_friend_class_scopes_.push_back(declaration->friend_class_scope);
	if (declaration->placeholder != NULL)
		for (map<Scope*, vector<Binding*> >::const_iterator it =
			     class_friend_functions_.begin();
		     it != class_friend_functions_.end();
		     ++it)
			if (find(it->second.begin(),
			         it->second.end(),
			         declaration->placeholder) != it->second.end() &&
			    find(active_friend_class_scopes_.begin(),
			         active_friend_class_scopes_.end(),
			         it->first) == active_friend_class_scopes_.end())
				active_friend_class_scopes_.push_back(it->first);
	size_t replay_extra_begin = extra_lowir_nodes_.size();
	Node node;
	TypePtr replay_substituted_function_type;
	++suppress_qualifier_template_member_instantiation_depth_;
	try
	{
		if (declaration->inherited_constructor_base != NULL)
		{
			map<Binding*, TemplateDeclaration*>::iterator base_template =
				function_template_placeholders_.find(
					declaration->inherited_constructor_base);
			if (base_template == function_template_placeholders_.end())
				throw runtime_error(
					"inherited constructor template base missing");
			Binding* base_call =
				instantiate_function_template(base_template->second, full_args);
			TypePtr fn_type =
				substitute_function_template_type(
					declaration,
					declaration->generic_function_type);
			if (fn_type.get() == NULL ||
			    fn_type->kind != pa11::TypeKind::Function ||
			    fn_type->parameters.empty())
				throw runtime_error("invalid inherited constructor type");
			Binding* binding =
				add_function_binding(declaration->owner,
				                     declaration->name,
				                     fn_type,
				                     false);
			if (declaration->placeholder != NULL)
			{
				binding->is_explicit = declaration->placeholder->is_explicit;
				binding->is_constexpr = declaration->placeholder->is_constexpr;
				binding->unwind_no = declaration->placeholder->unwind_no;
			}
			binding->is_inline_definition = true;
			vector<string> names(1, "this");
			map<Binding*, vector<string> >::const_iterator saved_names =
				declaration->placeholder != NULL
				? function_parameter_names_.find(declaration->placeholder)
				: function_parameter_names_.end();
			for (size_t i = 1; i < fn_type->parameters.size(); ++i)
			{
				string pname;
				if (saved_names != function_parameter_names_.end() &&
				    i < saved_names->second.size() &&
				    !saved_names->second[i].empty())
					pname = saved_names->second[i];
				else if (saved_names != function_parameter_names_.end() &&
				         saved_names->second.size() > 1 &&
				         i >= saved_names->second.size() &&
				         !saved_names->second.back().empty())
					pname = saved_names->second.back() +
					        "__pack" + to_string(i);
				else
					pname = "__param" + to_string(i);
				names.push_back(pname);
			}
			function_parameter_names_[binding] = names;
			binding->function_parameter_names = names;
			node = Node("function-definition " + qualified_decl_name(binding) +
			            " " + pa11::describe_type(fn_type));
			node.binding = binding;
			node.type = fn_type;
			Scope* function_scope =
				pa11::create_child_scope(declaration->owner,
				                         ScopeKind::Function,
				                         binding->name);
			Binding* this_binding =
				pa11::add_binding(function_scope,
				                  BindingKind::Parameter,
				                  "this",
				                  fn_type->parameters[0]);
			Node this_node("parameter this " +
			               pa11::describe_type(fn_type->parameters[0]));
			this_node.binding = this_binding;
			this_node.type = fn_type->parameters[0];
			add_child(node, this_node);
			Node init("braced-init-list");
			for (size_t i = 1; i < fn_type->parameters.size(); ++i)
			{
				Binding* param =
					pa11::add_binding(function_scope,
					                  BindingKind::Parameter,
					                  names[i],
					                  fn_type->parameters[i]);
				Node param_node("parameter " + names[i] + " " +
				                pa11::describe_type(fn_type->parameters[i]));
				param_node.binding = param;
				param_node.type = fn_type->parameters[i];
				add_child(node, param_node);
				Node arg("id-expression lvalue " +
				         pa11::describe_type(fn_type->parameters[i]) +
				         " " + names[i]);
				arg.binding = param;
				arg.type = fn_type->parameters[i];
				arg.category = ValueCategory::LValue;
				add_child(init, arg);
			}
			Node body("compound-statement");
			TypePtr base_type =
				substitute_template_type(
					declaration->inherited_constructor_base_type);
			init.type = base_type;
			init.category = ValueCategory::LValue;
			Node base_action = make_base_init_action(base_type, &init);
			base_action.direct_call = base_call;
			base_action.token_text = "inherited-constructor";
			add_child(body, base_action);
			add_child(node, body);
			remember_function_body(binding, node);
		}
		else if (declaration->constructor_template)
		{
			size_t extra_before = extra_lowir_nodes_.size();
			if (parse_qualified_constructor_definition(node, true))
			{
				if (node.binding == NULL &&
				    node.children.empty() &&
				    extra_lowir_nodes_.size() > extra_before)
				{
					node = extra_lowir_nodes_.back();
					extra_lowir_nodes_.pop_back();
				}
			}
			else
			{
				parse_simple_or_function_declaration(node, true);
				if (node.binding == NULL &&
				    node.children.empty() &&
				    extra_lowir_nodes_.size() <= extra_before)
					throw runtime_error(
						"constructor template instantiation failed");
				if (node.binding == NULL && node.children.empty())
				{
					node = extra_lowir_nodes_.back();
					extra_lowir_nodes_.pop_back();
				}
			}
		}
		else
		{
			size_t extra_before = extra_lowir_nodes_.size();
			parse_simple_or_function_declaration(node, true);
			if (node.binding == NULL &&
			    node.children.empty() &&
			    extra_lowir_nodes_.size() > extra_before)
			{
				node = extra_lowir_nodes_.back();
				extra_lowir_nodes_.pop_back();
			}
		}
		if (declaration->generic_function_type.get() != NULL &&
		    declaration->generic_function_type->kind ==
			    pa11::TypeKind::Function)
			replay_substituted_function_type =
				substitute_function_template_type(
					declaration,
					declaration->generic_function_type);
	}
	catch (const exception&)
	{
		--suppress_qualifier_template_member_instantiation_depth_;
		active_friend_class_scopes_.resize(friend_scope_depth);
		declaration->completing_specializations.erase(key);
		template_type_substitutions_ = save_subst;
		template_value_substitutions_ = save_value_subst;
		template_type_parameter_packs_ = save_pack_subst;
		scopes_ = save_scopes;
		pos_ = save_pos;
		force_new_function_binding_ = save_force_new_function_binding;
		defer_function_template_bodies_ =
			save_defer_function_template_bodies;
		suppress_implicit_template_base_init_ =
			save_suppress_implicit_template_base_init;
		override_function_parameter_names_ =
			save_override_function_parameter_names;
		function_parameter_name_override_ =
			save_function_parameter_name_override;
		throw;
	}
	--suppress_qualifier_template_member_instantiation_depth_;
	active_friend_class_scopes_.resize(friend_scope_depth);
	template_type_substitutions_ = save_subst;
	template_value_substitutions_ = save_value_subst;
	template_type_parameter_packs_ = save_pack_subst;
	scopes_ = save_scopes;
	pos_ = save_pos;
	force_new_function_binding_ = save_force_new_function_binding;
	defer_function_template_bodies_ = save_defer_function_template_bodies;
	suppress_implicit_template_base_init_ =
		save_suppress_implicit_template_base_init;
	override_function_parameter_names_ =
		save_override_function_parameter_names;
	function_parameter_name_override_ =
		save_function_parameter_name_override;
	Node fn;
	if (((node.line.compare(0, 19, "function-definition") == 0) ||
	     (node.line.compare(0, 20, "function-declaration") == 0)) &&
	    node.binding != NULL)
		fn = node;
	else if (!node.children.empty())
		fn = node.children.back();
	if (fn.binding == NULL && !fn.children.empty())
		fn = fn.children.back();
	if (fn.binding == NULL)
	{
		declaration->completing_specializations.erase(key);
		throw runtime_error("function template instantiation failed");
	}
	if (declaration->placeholder != NULL)
	{
		fn.binding->is_static_member =
			declaration->placeholder->is_static_member;
		fn.binding->is_constexpr =
			declaration->placeholder->is_constexpr;
		fn.binding->is_explicit =
			declaration->placeholder->is_explicit;
		fn.binding->is_private =
			declaration->placeholder->is_private;
		fn.binding->is_protected_member =
			declaration->placeholder->is_protected_member;
		fn.binding->ref_qualifier =
			declaration->placeholder->ref_qualifier;
		fn.binding->unwind_no =
			declaration->placeholder->unwind_no;
		if (declaration->placeholder->reserve_primary_function_symbol)
			fn.binding->reserve_primary_function_symbol = true;
		map<Binding*, vector<string> >::const_iterator placeholder_names =
			function_parameter_names_.find(declaration->placeholder);
		map<Binding*, vector<string> >::iterator binding_names =
			function_parameter_names_.find(fn.binding);
	if (placeholder_names != function_parameter_names_.end() &&
	    binding_names != function_parameter_names_.end())
	{
		vector<string>& names = binding_names->second;
			const vector<string>& old_names = placeholder_names->second;
			bool old_names_skip_this =
				old_names.size() + 1 == names.size();
			for (size_t i = 0; i < names.size(); ++i)
			{
				size_t old_index = old_names_skip_this
					? (i == 0 ? old_names.size() : i - 1)
					: i;
				if (old_index >= old_names.size() ||
				    old_names[old_index].empty())
					continue;
				bool generated =
					names[i].empty() ||
					names[i].compare(0, 7, "__param") == 0;
				bool old_generated =
					old_names[old_index].compare(0, 7, "__param") == 0;
				if (generated && !old_generated)
					names[i] = old_names[old_index];
			}
			declaration->function_parameter_names = names;
		}
		else if (binding_names != function_parameter_names_.end())
			declaration->function_parameter_names = binding_names->second;
		else if (placeholder_names != function_parameter_names_.end())
			declaration->function_parameter_names = placeholder_names->second;
	}
	if (!substituted_type_is_valid(fn.binding->type) &&
	    substituted_type_is_valid(replay_substituted_function_type))
		apply_replayed_function_type(fn, replay_substituted_function_type);
	if (declaration->class_template_member)
	{
		fn.binding->function_specialization_symbol =
			constructor_template_function_template_symbol(declaration) ||
			class_template_member_function_template_symbol(declaration)
			? abi_function_template_specialization_symbol(
				declaration,
				full_args,
				fn.binding,
				&declaration_tokens_)
			: abi_binding_symbol(fn.binding, map<string, size_t>());
		if (fn.binding->aliased_binding != NULL)
			fn.binding->aliased_binding->function_specialization_symbol =
				constructor_template_function_template_symbol(declaration) ||
				class_template_member_function_template_symbol(declaration)
				? abi_function_template_specialization_symbol(
					declaration,
					full_args,
					fn.binding->aliased_binding,
					&declaration_tokens_)
				: abi_binding_symbol(fn.binding->aliased_binding,
				                     map<string, size_t>());
	}
		if (!substituted_type_is_valid(fn.binding->type))
		{
			declaration->completing_specializations.erase(key);
			throw runtime_error("invalid substituted function type");
		}
	if (declaration->placeholder != NULL &&
	    declaration->placeholder->reserve_primary_function_symbol)
		fn.binding->reserve_primary_function_symbol = true;
	if (fn.line.compare(0, 19, "function-definition") != 0)
	{
		if (!declaration->class_template_member)
			fn.binding->function_specialization_symbol =
				abi_function_template_specialization_symbol(
					declaration,
					full_args,
					fn.binding,
					&declaration_tokens_);
		if (declaration->placeholder != NULL)
			fn.binding->unwind_no = declaration->placeholder->unwind_no;
		if (declaration->placeholder != NULL)
		{
			map<Binding*, vector<Expr> >::const_iterator defaults =
				default_arguments_.find(declaration->placeholder);
			if (defaults != default_arguments_.end())
			{
				default_arguments_[fn.binding] = defaults->second;
				if (fn.binding->aliased_binding != NULL)
					default_arguments_[fn.binding->aliased_binding] =
						defaults->second;
			}
		}
		if (replaced_specialization != NULL &&
		    replaced_specialization != fn.binding)
			replaced_specialization->aliased_binding = fn.binding;
		function_template_placeholders_[fn.binding] = declaration;
		function_template_specialization_arguments_[fn.binding] =
			full_args;
			if (declaration->has_definition &&
			    unevaluated_expression_depth_ == 0 &&
			    function_template_candidate_instantiation_depth_ == 0 &&
			    !defer_hosted_function_body(fn.binding))
			{
				parse_pending_function_body(fn.binding);
				parse_pending_member_body(fn.binding);
			}
		declaration->function_specializations[key] = fn.binding;
			if (declaration->friend_class_scope != NULL)
				add_friend_function(declaration->friend_class_scope, fn.binding);
			declaration->completing_specializations.erase(key);
			return fn.binding;
		}
	fn.binding->is_inline_definition = true;
	if (!declaration->class_template_member)
		fn.binding->function_specialization_symbol =
			abi_function_template_specialization_symbol(declaration,
			                                            full_args,
			                                            fn.binding,
			                                            &declaration_tokens_);
	if (declaration->placeholder != NULL)
		fn.binding->unwind_no = declaration->placeholder->unwind_no;
	if (declaration->placeholder != NULL)
	{
		map<Binding*, vector<Expr> >::const_iterator defaults =
			default_arguments_.find(declaration->placeholder);
		if (defaults != default_arguments_.end())
		{
			default_arguments_[fn.binding] = defaults->second;
			if (fn.binding->aliased_binding != NULL)
				default_arguments_[fn.binding->aliased_binding] =
					defaults->second;
		}
		}
		if (replaced_specialization != NULL &&
		    replaced_specialization != fn.binding)
			replaced_specialization->aliased_binding = fn.binding;
		if (function_template_candidate_instantiation_depth_ != 0)
		{
			bool keep_constexpr_body_for_value_expression =
				(template_argument_expression_depth_ != 0 ||
				 constexpr_value_expression_depth_ != 0) &&
				fn.binding != NULL &&
				fn.binding->is_constexpr;
			if (!keep_constexpr_body_for_value_expression)
				function_bodies_.erase(fn.binding);
			for (size_t i = replay_extra_begin;
			     i < extra_lowir_nodes_.size();
			     ++i)
				if (extra_lowir_nodes_[i].binding != NULL)
				{
					bool keep_extra_constexpr_body =
						keep_constexpr_body_for_value_expression &&
						extra_lowir_nodes_[i].binding != NULL &&
						extra_lowir_nodes_[i].binding->is_constexpr;
					if (!keep_extra_constexpr_body)
						function_bodies_.erase(extra_lowir_nodes_[i].binding);
				}
			extra_lowir_nodes_.resize(replay_extra_begin);
		}
		else
			extra_lowir_nodes_.push_back(fn);
		declaration->function_specializations[key] = fn.binding;
		if (declaration->friend_class_scope != NULL)
		{
			add_friend_function(declaration->friend_class_scope, fn.binding);
		}
				function_template_placeholders_[fn.binding] = declaration;
				function_template_specialization_arguments_[fn.binding] = full_args;
			declaration->completing_specializations.erase(key);
			return fn.binding;
	}

}  // namespace internal
}  // namespace pa12
