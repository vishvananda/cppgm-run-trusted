#include "pa12_internal.h"
#include "pa12_templates_function_support.h"

using namespace std;

namespace pa12 {
namespace internal {
namespace {

bool constexpr_function_can_have_body(Binding* function)
{
	return function != NULL &&
	       function->kind == BindingKind::Function &&
	       (function->is_constexpr ||
	        function->is_generated_default_constructor ||
	        function->is_generated_aggregate_constructor ||
	        function->is_defaulted);
}

}  // namespace

void Parser::parse_pending_constexpr_function_bodies(Binding* function,
                                                     bool ensure_extra)
{
	for (Binding* cur = function; cur != NULL; cur = cur->aliased_binding)
	{
		if (cur->kind != BindingKind::Function)
			break;
		if (!constexpr_function_can_have_body(cur))
			continue;
		size_t extra_before = extra_lowir_nodes_.size();
		parse_pending_function_body(cur);
		parse_pending_member_body(cur);
		if (ensure_extra)
			ensure_function_body_extra_node(cur);
		extra_lowir_nodes_.resize(extra_before);
	}
}

bool Parser::build_bodyless_constexpr_template_parameters(
	TemplateDeclaration* declaration,
	Binding* target,
	const vector<TemplateArgument>& arguments,
	vector<ParameterInfo>& parameters)
{
	vector<string> names = declaration->function_parameter_names;
	if (declaration->placeholder != NULL)
	{
		map<Binding*, vector<string> >::const_iterator saved =
			function_parameter_names_.find(declaration->placeholder);
		if (saved != function_parameter_names_.end())
		{
			if (names.empty())
				names = saved->second;
			else if (names.size() < saved->second.size())
				names.insert(names.end(),
				             saved->second.begin() + names.size(),
				             saved->second.end());
		}
	}
	size_t first_concrete_index =
		target->owner != NULL &&
		target->owner->kind == ScopeKind::Class &&
		!target->is_static_member
		? 1 : 0;
	size_t concrete_index = first_concrete_index;
	TypePtr generic = declaration->generic_function_type;
	size_t generic_count =
		generic.get() != NULL && generic->kind == pa11::TypeKind::Function
		? generic->parameters.size() : 0;
	for (size_t gi = concrete_index; gi < generic_count; ++gi)
	{
		TypePtr pattern = generic->parameters[gi];
		string pname = gi < names.size() ? names[gi] : string();
		if (first_concrete_index != 0 &&
		    gi - first_concrete_index < names.size())
			pname = names[gi - first_concrete_index];
		string pack_name;
		if (function_parameter_pack_name(declaration, pattern, pack_name))
		{
			size_t pack_size = 0;
			for (size_t pi = 0;
			     pi < declaration->parameters.size() && pi < arguments.size();
			     ++pi)
				if (declaration->parameters[pi].name == pack_name &&
				    arguments[pi].kind == TemplateArgumentKind::Pack)
					pack_size = arguments[pi].pack.size();
			if (pname.empty())
				pname = pack_name;
			if (pack_size == 0)
			{
				ParameterInfo parameter;
				parameter.name = pname;
				parameter.type = pattern;
				parameter.pack_name = pack_name;
				parameter.pack_expression_name = pname;
				parameters.push_back(parameter);
				continue;
			}
			for (size_t p = 0; p < pack_size; ++p)
			{
				if (concrete_index >= target->type->parameters.size())
					return false;
				ParameterInfo parameter;
				parameter.name = p == 0
					? pname : pname + "__pack" + to_string(p + 1);
				parameter.type = target->type->parameters[concrete_index++];
				parameter.pack_name = pack_name;
				parameter.pack_expression_name = pname;
				parameters.push_back(parameter);
			}
			continue;
		}
		if (concrete_index >= target->type->parameters.size())
			return false;
		ParameterInfo parameter;
		parameter.name = pname;
		parameter.type = target->type->parameters[concrete_index++];
		parameters.push_back(parameter);
	}
	return true;
}

bool Parser::replay_bodyless_constexpr_template(Binding* target)
{
	if (target == NULL ||
	    function_bodies_.find(target) != function_bodies_.end())
		return true;
	map<Binding*, TemplateDeclaration*>::iterator templ =
		function_template_placeholders_.find(target);
	map<Binding*, vector<TemplateArgument> >::iterator arg_it =
		function_template_specialization_arguments_.find(target);
	if (templ == function_template_placeholders_.end() ||
	    arg_it == function_template_specialization_arguments_.end())
		return false;
	TemplateDeclaration* declaration = templ->second;
	if (declaration == NULL ||
	    !declaration->has_definition ||
	    !target->is_constexpr ||
	    target->type.get() == NULL ||
	    target->type->kind != pa11::TypeKind::Function)
		return false;
	size_t body_pos = declaration->decl_end;
	for (size_t i = declaration->decl_begin;
	     i < declaration->decl_end && i < tokens_.size();
	     ++i)
		if (tokens_[i].kind == posttoken::TokenKind::Simple &&
		    tokens_[i].type == OP_LBRACE)
		{
			body_pos = i;
			break;
		}
	if (body_pos == declaration->decl_end)
		return false;
	vector<ParameterInfo> parameters;
	if (!build_bodyless_constexpr_template_parameters(declaration,
	                                                  target,
	                                                  arg_it->second,
	                                                  parameters))
		return false;
	PendingFunctionBody pending;
	pending.function = target;
	pending.node = Node("function-definition " +
	                    qualified_decl_name(target) + " " +
	                    pa11::describe_type(target->type));
	pending.node.binding = target;
	pending.node.type = target->type;
	pending.parameters = parameters;
	pending.body_pos = body_pos;
	pending.class_type =
		target->owner != NULL
		? pa11::record_type_for_scope(target->owner) : TypePtr();
	pending.scopes.clear();
	pending.scopes.push_back(
		declaration->lexical_scope != NULL
		? declaration->lexical_scope : declaration->owner);
	pending.friend_class_scopes = active_friend_class_scopes_;
	pending.type_substitutions = template_type_substitutions_;
	pending.value_substitutions = template_value_substitutions_;
	pending.pack_substitutions = template_type_parameter_packs_;
	size_t extra_before = extra_lowir_nodes_.size();
	parse_pending_member_body_now(pending);
	extra_lowir_nodes_.resize(extra_before);
	return function_bodies_.find(target) != function_bodies_.end();
}

bool Parser::find_constexpr_function_body(
	Binding* function,
	Binding*& body_binding,
	map<Binding*, Node>::const_iterator& found)
{
	body_binding = function;
	found = function_bodies_.end();
	for (Binding* cur = function; cur != NULL; cur = cur->aliased_binding)
	{
		if (cur->kind != BindingKind::Function)
			break;
		if (!constexpr_function_can_have_body(cur))
			continue;
		found = function_bodies_.find(cur);
		if (found != function_bodies_.end())
		{
			body_binding = cur;
			return true;
		}
	}
	return false;
}

bool Parser::ensure_constexpr_function_body(
	Binding* function,
	Binding*& body_binding,
	map<Binding*, Node>::const_iterator& found)
{
	if (find_constexpr_function_body(function, body_binding, found))
		return true;
	parse_pending_constexpr_function_bodies(function, true);
	return find_constexpr_function_body(function, body_binding, found);
}

}  // namespace internal
}  // namespace pa12
