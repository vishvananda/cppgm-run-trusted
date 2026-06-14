#include "pa12_templates_function_instantiation_engine.h"

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
	     i < declaration->generic_function_type->parameters.size(); ++i)
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
	size_t generic_count = declaration->generic_function_type->parameters.size();
	bool generic_has_owner_parameter =
		function->owner != NULL &&
		function->owner->kind == ScopeKind::Class &&
		!function->is_static_member && generic_count != 0;
	bool saved_names_have_owner = !names.empty() && names[0] == "this";
	vector<string> expanded;
	for (size_t i = 0; i < generic_count; ++i)
	{
		size_t name_index = i;
		if (generic_has_owner_parameter && !saved_names_have_owner)
			name_index = i == 0 ? names.size() : i - 1;
		string source_name =
			name_index < names.size() ? names[name_index] : string();
		string pack_name;
		bool pack_parameter = function_parameter_pack_name(
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
		for (size_t pidx = 0; pidx < repeat; ++pidx)
		{
			if (source_name.empty())
				expanded.push_back(string());
			else if (pidx == 0)
				expanded.push_back(source_name);
			else
				expanded.push_back(
					source_name + "__pack" + to_string(pidx + 1));
		}
	}
	if (expanded.size() == concrete_count)
		names = expanded;
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
		      !names.empty() && !names[0].empty() && names[0] != "this")))
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

}  // namespace

Binding* FunctionTemplateInstantiationEngine::instantiate_deferred_member_body()
{
	if (declaration->constructor_template || !declaration->has_definition ||
	    declaration->placeholder == NULL || declaration->owner == NULL ||
	    declaration->owner->kind != ScopeKind::Class ||
	    p.function_template_candidate_instantiation_depth_ != 0)
		return NULL;
	size_t body_pos = function_template_body_start(
		p.tokens_,
		declaration->decl_begin,
		declaration->decl_end);
	if (body_pos == declaration->decl_end)
		return NULL;
	if (ordinary_class_template_member())
		return instantiate_ordinary_member_body(body_pos);
	return instantiate_out_of_line_member_body(body_pos);
}

bool FunctionTemplateInstantiationEngine::ordinary_class_template_member() const
{
	TypePtr owner_record = pa11::record_type_for_scope(declaration->owner);
	owner_record = owner_record.get() != NULL
		? pa11::strip_cv(owner_record) : TypePtr();
	map<const void*, TemplateDeclaration*>::const_iterator owner_template =
		owner_record.get() != NULL
		? p.record_template_declarations_.find(owner_record.get())
		: p.record_template_declarations_.end();
	return declaration->class_template_member &&
	       declaration->outer_type_substitutions.empty() &&
	       ((owner_template != p.record_template_declarations_.end() &&
	         template_parameter_lists_equivalent(
		         declaration->parameters,
		         owner_template->second->parameters)) ||
	        (!declaration->name.empty() &&
	         (declaration->name[0] == '~' ||
	          declaration->name.compare(0, 8, "operator") == 0)));
}

Binding* FunctionTemplateInstantiationEngine::instantiate_ordinary_member_body(
	size_t body_pos)
{
	Binding* binding = declaration->placeholder;
	vector<string> names;
	load_parameter_names(binding, binding, binding->type, names);
	p.function_parameter_names_[binding] = names;
	binding->function_parameter_names = names;
	declaration->function_specializations[key] = binding;
	p.function_template_placeholders_[binding] = declaration;
	p.function_template_specialization_arguments_[binding] = full_args;
	PendingFunctionBody pending = build_pending_body(binding, names, body_pos);
	parse_or_queue_pending_body(pending);
	return finish_with_restore(binding);
}

Binding* FunctionTemplateInstantiationEngine::instantiate_out_of_line_member_body(
	size_t body_pos)
{
	TypePtr type = p.substitute_function_template_type(
		declaration,
		declaration->generic_function_type);
	if (!substituted_type_is_valid(type))
		throw runtime_error("invalid substituted function type");
	Binding* binding = create_specialization_binding(type, true);
	copy_placeholder_properties(binding, true);
	vector<string> names;
	load_parameter_names(declaration->placeholder, binding, type, names);
	p.function_parameter_names_[binding] = names;
	binding->function_parameter_names = names;
	if (replaced_specialization != NULL && replaced_specialization != binding)
		replaced_specialization->aliased_binding = binding;
	assign_specialization_symbol(binding, true);
	register_specialization(binding, true);
	PendingFunctionBody pending = build_pending_body(binding, names, body_pos);
	parse_or_queue_pending_body(pending);
	return finish_with_restore(binding);
}

void FunctionTemplateInstantiationEngine::load_parameter_names(
	Binding* source,
	Binding* target,
	TypePtr type,
	vector<string>& names)
{
	if (source != NULL)
	{
		map<Binding*, vector<string> >::const_iterator saved_names =
			p.function_parameter_names_.find(source);
		if (saved_names != p.function_parameter_names_.end())
			names = saved_names->second;
	}
	if (!parameter_names_have_non_this(names) &&
	    parameter_names_have_non_this(declaration->function_parameter_names))
		names = declaration->function_parameter_names;
	normalize_member_function_parameter_names(target, names);
	expand_function_template_pack_parameter_names(declaration, target, names);
	if (type.get() != NULL && type->kind == pa11::TypeKind::Function &&
	    names.size() < type->parameters.size())
		names.resize(type->parameters.size());
}

PendingFunctionBody FunctionTemplateInstantiationEngine::build_pending_body(
	Binding* binding,
	const vector<string>& names,
	size_t body_pos)
{
	PendingFunctionBody pending;
	pending.function = binding;
	pending.node = Node("function-definition " +
	                    p.qualified_decl_name(binding) + " " +
	                    pa11::describe_type(binding->type));
	pending.node.binding = binding;
	pending.node.type = binding->type;
	pending.parameters = function_body_parameters_from_type(binding, names);
	pending.body_pos = body_pos;
	pending.class_type = binding->owner != NULL
		? pa11::record_type_for_scope(binding->owner) : TypePtr();
	pending.scopes.clear();
	pending.scopes.push_back(declaration->lexical_scope != NULL
	                         ? declaration->lexical_scope
	                         : declaration->owner);
	pending.friend_class_scopes = p.active_friend_class_scopes_;
	pending.type_substitutions = p.template_type_substitutions_;
	pending.value_substitutions = p.template_value_substitutions_;
	pending.pack_substitutions = p.template_type_parameter_packs_;
	return pending;
}

void FunctionTemplateInstantiationEngine::parse_or_queue_pending_body(
	PendingFunctionBody& pending)
{
	Binding* binding = pending.function;
	if (p.function_template_candidate_instantiation_depth_ == 0)
	{
		bool parsed = p.parse_pending_member_body_now(
			pending,
			p.force_function_template_body_instantiation_);
		if (parsed)
			return;
		if (binding->owner != NULL)
			p.pending_member_bodies_[binding->owner].push_back(pending);
		else
			p.pending_function_bodies_[binding] = pending;
	}
	else if (binding->owner != NULL)
		p.pending_member_bodies_[binding->owner].push_back(pending);
}

}  // namespace internal
}  // namespace pa12
