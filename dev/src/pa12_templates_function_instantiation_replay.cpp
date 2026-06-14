#include "pa12_templates_function_instantiation_engine.h"

#include <algorithm>
#include <stdexcept>

using namespace std;

namespace pa12 {
namespace internal {

namespace {

void apply_replayed_function_type(Node& fn, TypePtr type)
{
	if (fn.binding == NULL || type.get() == NULL ||
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

}  // namespace

Binding* FunctionTemplateInstantiationEngine::replay_function_template()
{
	p.scopes_.clear();
	p.scopes_.push_back(declaration->lexical_scope != NULL
	                    ? declaration->lexical_scope
	                    : declaration->owner);
	p.pos_ = declaration->decl_begin;
	p.force_new_function_binding_ = true;
	p.defer_function_template_bodies_ =
		!p.force_function_template_body_instantiation_;
	prepare_replay_parameter_names();
	p.suppress_implicit_template_base_init_ =
		save_suppress_implicit_template_base_init ||
		class_template_constructor_replay();
	size_t friend_scope_depth = enter_friend_scopes();
	size_t replay_extra_begin = p.extra_lowir_nodes_.size();
	Node node;
	TypePtr replay_substituted_function_type;
	++p.suppress_qualifier_template_member_instantiation_depth_;
	try
	{
		node = replay_template_declaration(
			replay_extra_begin,
			replay_substituted_function_type);
	}
	catch (...)
	{
		--p.suppress_qualifier_template_member_instantiation_depth_;
		p.active_friend_class_scopes_.resize(friend_scope_depth);
		throw;
	}
	--p.suppress_qualifier_template_member_instantiation_depth_;
	p.active_friend_class_scopes_.resize(friend_scope_depth);
	restore_parser_state();
	return finish_replayed_function(
		node,
		replay_substituted_function_type,
		replay_extra_begin);
}

void FunctionTemplateInstantiationEngine::prepare_replay_parameter_names()
{
	if (declaration->placeholder == NULL ||
	    declaration->generic_function_type.get() == NULL ||
	    declaration->generic_function_type->kind != pa11::TypeKind::Function)
		return;
	map<Binding*, vector<string> >::const_iterator saved_names =
		p.function_parameter_names_.find(declaration->placeholder);
	if (saved_names == p.function_parameter_names_.end())
		return;
	vector<string> replay_names =
		build_replay_parameter_names(saved_names->second);
	if (declaration->placeholder->is_static_member &&
	    !replay_names.empty() && replay_names[0] == "this")
		replay_names.erase(replay_names.begin());
	if (!replay_names.empty())
	{
		p.override_function_parameter_names_ = true;
		p.function_parameter_name_override_ = replay_names;
	}
}

vector<string> FunctionTemplateInstantiationEngine::build_replay_parameter_names(
	const vector<string>& saved_names)
{
	vector<string> replay_names;
	bool saved_names_already_expanded = false;
	for (size_t i = 0; i < saved_names.size(); ++i)
		if (saved_names[i].find("__pack") != string::npos)
			saved_names_already_expanded = true;
	bool generic_has_owner_parameter = replay_generic_has_owner_parameter();
	if (saved_names_already_expanded ||
	    (generic_has_owner_parameter && !saved_names.empty() &&
	     saved_names[0] == "this"))
		return saved_names;
	bool skip_owner_name =
		generic_has_owner_parameter &&
		(saved_names.empty() || saved_names[0] != "this");
	for (size_t i = 0;
	     i < declaration->generic_function_type->parameters.size(); ++i)
	{
		if (skip_owner_name && i == 0)
			continue;
		TypePtr pattern = declaration->generic_function_type->parameters[i];
		size_t source_index = skip_owner_name ? i - 1 : i;
		string source_name =
			source_index < saved_names.size() ? saved_names[source_index]
			                                 : string();
		string pack_name;
		TemplateArgument subst_arg;
		if (function_parameter_pack_name(declaration, pattern, pack_name) &&
		    p.find_template_value_substitution(pack_name, subst_arg) &&
		    subst_arg.kind == TemplateArgumentKind::Pack)
		{
			if (source_name.empty() && !replay_names.empty() &&
			    !replay_names.back().empty() &&
			    replay_names.back().compare(0, 7, "__param") != 0)
				source_name = generated_pack_parameter_name(pack_name);
			for (size_t pidx = 0; pidx < subst_arg.pack.size(); ++pidx)
			{
				if (source_name.empty())
					replay_names.push_back(string());
				else if (pidx == 0)
					replay_names.push_back(source_name);
				else
					replay_names.push_back(
						source_name + "__pack" +
						to_string(pidx + 1));
			}
			continue;
		}
		replay_names.push_back(source_name);
	}
	return replay_names;
}

bool FunctionTemplateInstantiationEngine::replay_generic_has_owner_parameter()
	const
{
	if (declaration->generic_function_type->parameters.empty())
		return false;
	TypePtr first = pa11::strip_cv(
		declaration->generic_function_type->parameters[0]);
	return first.get() != NULL &&
	       first->kind == pa11::TypeKind::Pointer &&
	       pa11::strip_cv(first->base)->kind == pa11::TypeKind::Record;
}

bool FunctionTemplateInstantiationEngine::class_template_constructor_replay()
	const
{
	if (!declaration->constructor_template || declaration->owner == NULL ||
	    declaration->owner->kind != ScopeKind::Class)
		return false;
	TypePtr owner_record = pa11::record_type_for_scope(declaration->owner);
	owner_record = owner_record.get() != NULL
		? pa11::strip_cv(owner_record) : TypePtr();
	map<const void*, TemplateDeclaration*>::const_iterator owner_template =
		owner_record.get() != NULL
		? p.record_template_declarations_.find(owner_record.get())
		: p.record_template_declarations_.end();
	return owner_template != p.record_template_declarations_.end() &&
	       template_parameter_lists_equivalent(
		       declaration->parameters,
		       owner_template->second->parameters);
}

size_t FunctionTemplateInstantiationEngine::enter_friend_scopes()
{
	size_t friend_scope_depth = p.active_friend_class_scopes_.size();
	if (declaration->friend_class_scope != NULL)
		p.active_friend_class_scopes_.push_back(
			declaration->friend_class_scope);
	if (declaration->placeholder == NULL)
		return friend_scope_depth;
	for (map<Scope*, vector<Binding*> >::const_iterator it =
		     p.class_friend_functions_.begin();
	     it != p.class_friend_functions_.end(); ++it)
		if (find(it->second.begin(),
		         it->second.end(),
		         declaration->placeholder) != it->second.end() &&
		    find(p.active_friend_class_scopes_.begin(),
		         p.active_friend_class_scopes_.end(),
		         it->first) == p.active_friend_class_scopes_.end())
			p.active_friend_class_scopes_.push_back(it->first);
	return friend_scope_depth;
}

Node FunctionTemplateInstantiationEngine::replay_template_declaration(
	size_t replay_extra_begin,
	TypePtr& replay_substituted_function_type)
{
	Node node;
	if (declaration->inherited_constructor_base != NULL)
		node = replay_inherited_constructor();
	else if (declaration->constructor_template)
		node = replay_constructor_template(replay_extra_begin);
	else
		node = replay_ordinary_function(replay_extra_begin);
	if (declaration->generic_function_type.get() != NULL &&
	    declaration->generic_function_type->kind == pa11::TypeKind::Function)
		replay_substituted_function_type =
			p.substitute_function_template_type(
				declaration,
				declaration->generic_function_type);
	return node;
}

Node FunctionTemplateInstantiationEngine::replay_inherited_constructor()
{
	map<Binding*, TemplateDeclaration*>::iterator base_template =
		p.function_template_placeholders_.find(
			declaration->inherited_constructor_base);
	if (base_template == p.function_template_placeholders_.end())
		throw runtime_error("inherited constructor template base missing");
	Binding* base_call =
		p.instantiate_function_template(base_template->second, full_args);
	TypePtr fn_type = p.substitute_function_template_type(
		declaration,
		declaration->generic_function_type);
	if (fn_type.get() == NULL ||
	    fn_type->kind != pa11::TypeKind::Function ||
	    fn_type->parameters.empty())
		throw runtime_error("invalid inherited constructor type");
	Binding* binding = p.add_function_binding(
		declaration->owner,
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
		? p.function_parameter_names_.find(declaration->placeholder)
		: p.function_parameter_names_.end();
	for (size_t i = 1; i < fn_type->parameters.size(); ++i)
	{
		string pname;
		if (saved_names != p.function_parameter_names_.end() &&
		    i < saved_names->second.size() && !saved_names->second[i].empty())
			pname = saved_names->second[i];
		else if (saved_names != p.function_parameter_names_.end() &&
		         saved_names->second.size() > 1 &&
		         i >= saved_names->second.size() &&
		         !saved_names->second.back().empty())
			pname = saved_names->second.back() + "__pack" + to_string(i);
		else
			pname = "__param" + to_string(i);
		names.push_back(pname);
	}
	p.function_parameter_names_[binding] = names;
	binding->function_parameter_names = names;
	Node node("function-definition " + p.qualified_decl_name(binding) +
	          " " + pa11::describe_type(fn_type));
	node.binding = binding;
	node.type = fn_type;
	Scope* function_scope = pa11::create_child_scope(
		declaration->owner,
		ScopeKind::Function,
		binding->name);
	Binding* this_binding = pa11::add_binding(
		function_scope,
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
		Binding* param = pa11::add_binding(
			function_scope,
			BindingKind::Parameter,
			names[i],
			fn_type->parameters[i]);
		Node param_node("parameter " + names[i] + " " +
		                pa11::describe_type(fn_type->parameters[i]));
		param_node.binding = param;
		param_node.type = fn_type->parameters[i];
		add_child(node, param_node);
		Node arg("id-expression lvalue " +
		         pa11::describe_type(fn_type->parameters[i]) + " " +
		         names[i]);
		arg.binding = param;
		arg.type = fn_type->parameters[i];
		arg.category = ValueCategory::LValue;
		add_child(init, arg);
	}
	Node body("compound-statement");
	TypePtr base_type =
		p.substitute_template_type(declaration->inherited_constructor_base_type);
	init.type = base_type;
	init.category = ValueCategory::LValue;
	Node base_action = p.make_base_init_action(base_type, &init);
	base_action.direct_call = base_call;
	base_action.token_text = "inherited-constructor";
	add_child(body, base_action);
	add_child(node, body);
	p.remember_function_body(binding, node);
	return node;
}

Node FunctionTemplateInstantiationEngine::replay_constructor_template(
	size_t extra_before)
{
	Node node;
	if (p.parse_qualified_constructor_definition(node, true))
	{
		if (node.binding == NULL && node.children.empty() &&
		    p.extra_lowir_nodes_.size() > extra_before)
		{
			node = p.extra_lowir_nodes_.back();
			p.extra_lowir_nodes_.pop_back();
		}
		return node;
	}
	p.parse_simple_or_function_declaration(node, true);
	if (node.binding == NULL && node.children.empty() &&
	    p.extra_lowir_nodes_.size() <= extra_before)
		throw runtime_error("constructor template instantiation failed");
	if (node.binding == NULL && node.children.empty())
	{
		node = p.extra_lowir_nodes_.back();
		p.extra_lowir_nodes_.pop_back();
	}
	return node;
}

Node FunctionTemplateInstantiationEngine::replay_ordinary_function(
	size_t extra_before)
{
	Node node;
	p.parse_simple_or_function_declaration(node, true);
	if (node.binding == NULL && node.children.empty() &&
	    p.extra_lowir_nodes_.size() > extra_before)
	{
		node = p.extra_lowir_nodes_.back();
		p.extra_lowir_nodes_.pop_back();
	}
	return node;
}

Binding* FunctionTemplateInstantiationEngine::finish_replayed_function(
	Node node,
	TypePtr replay_substituted_function_type,
	size_t replay_extra_begin)
{
	Node fn = selected_replayed_function_node(node);
	if (fn.binding == NULL)
		throw runtime_error("function template instantiation failed");
	copy_replayed_placeholder_properties(fn.binding);
	if (declaration->placeholder != NULL)
		merge_replayed_parameter_names(fn.binding);
	if (!substituted_type_is_valid(fn.binding->type) &&
	    substituted_type_is_valid(replay_substituted_function_type))
		apply_replayed_function_type(fn, replay_substituted_function_type);
	assign_specialization_symbol(fn.binding, false);
	assign_aliased_class_member_symbol(fn.binding);
	if (!substituted_type_is_valid(fn.binding->type))
		throw runtime_error("invalid substituted function type");
	if (declaration->placeholder != NULL &&
	    declaration->placeholder->reserve_primary_function_symbol)
		fn.binding->reserve_primary_function_symbol = true;
	if (fn.line.compare(0, 19, "function-definition") != 0)
		return finish_replayed_declaration(fn);
	return finish_replayed_definition(fn, replay_extra_begin);
}

Node FunctionTemplateInstantiationEngine::selected_replayed_function_node(
	const Node& node) const
{
	Node fn;
	if (((node.line.compare(0, 19, "function-definition") == 0) ||
	     (node.line.compare(0, 20, "function-declaration") == 0)) &&
	    node.binding != NULL)
		fn = node;
	else if (!node.children.empty())
		fn = node.children.back();
	if (fn.binding == NULL && !fn.children.empty())
		fn = fn.children.back();
	return fn;
}

void FunctionTemplateInstantiationEngine::copy_replayed_placeholder_properties(
	Binding* binding)
{
	if (declaration->placeholder == NULL)
		return;
	copy_placeholder_properties(binding, false);
}

void FunctionTemplateInstantiationEngine::merge_replayed_parameter_names(
	Binding* binding)
{
	map<Binding*, vector<string> >::const_iterator placeholder_names =
		p.function_parameter_names_.find(declaration->placeholder);
	map<Binding*, vector<string> >::iterator binding_names =
		p.function_parameter_names_.find(binding);
	if (placeholder_names != p.function_parameter_names_.end() &&
	    binding_names != p.function_parameter_names_.end())
	{
		vector<string>& names = binding_names->second;
		const vector<string>& old_names = placeholder_names->second;
		bool old_names_skip_this = old_names.size() + 1 == names.size();
		for (size_t i = 0; i < names.size(); ++i)
		{
			size_t old_index = old_names_skip_this
				? (i == 0 ? old_names.size() : i - 1) : i;
			if (old_index >= old_names.size() || old_names[old_index].empty())
				continue;
			bool generated =
				names[i].empty() || names[i].compare(0, 7, "__param") == 0;
			bool old_generated =
				old_names[old_index].compare(0, 7, "__param") == 0;
			if (generated && !old_generated)
				names[i] = old_names[old_index];
		}
		declaration->function_parameter_names = names;
	}
	else if (binding_names != p.function_parameter_names_.end())
		declaration->function_parameter_names = binding_names->second;
	else if (placeholder_names != p.function_parameter_names_.end())
		declaration->function_parameter_names = placeholder_names->second;
}

void FunctionTemplateInstantiationEngine::finish_replayed_defaults(
	Binding* binding)
{
	if (declaration->placeholder == NULL)
		return;
	map<Binding*, vector<Expr> >::const_iterator defaults =
		p.default_arguments_.find(declaration->placeholder);
	if (defaults == p.default_arguments_.end())
		return;
	p.default_arguments_[binding] = defaults->second;
	if (binding->aliased_binding != NULL)
		p.default_arguments_[binding->aliased_binding] = defaults->second;
}

void FunctionTemplateInstantiationEngine::parse_replayed_pending_bodies(
	Binding* binding)
{
	if (declaration->has_definition && p.unevaluated_expression_depth_ == 0 &&
	    p.function_template_candidate_instantiation_depth_ == 0 &&
	    !p.defer_hosted_function_body(binding))
	{
		p.parse_pending_function_body(binding);
		p.parse_pending_member_body(binding);
	}
}

Binding* FunctionTemplateInstantiationEngine::finish_replayed_declaration(
	Node& fn)
{
	if (!declaration->class_template_member)
		assign_specialization_symbol(fn.binding, true);
	if (declaration->placeholder != NULL)
		fn.binding->unwind_no = declaration->placeholder->unwind_no;
	finish_replayed_defaults(fn.binding);
	if (replaced_specialization != NULL &&
	    replaced_specialization != fn.binding)
		replaced_specialization->aliased_binding = fn.binding;
	p.function_template_placeholders_[fn.binding] = declaration;
	p.function_template_specialization_arguments_[fn.binding] = full_args;
	parse_replayed_pending_bodies(fn.binding);
	declaration->function_specializations[key] = fn.binding;
	if (declaration->friend_class_scope != NULL)
		p.add_friend_function(declaration->friend_class_scope, fn.binding);
	declaration->completing_specializations.erase(key);
	completion_active = false;
	return fn.binding;
}

void FunctionTemplateInstantiationEngine::prune_candidate_replay_bodies(
	Binding* binding,
	size_t replay_extra_begin)
{
	bool keep_constexpr_body_for_value_expression =
		(p.template_argument_expression_depth_ != 0 ||
		 p.constexpr_value_expression_depth_ != 0) &&
		binding != NULL && binding->is_constexpr;
	if (!keep_constexpr_body_for_value_expression)
		p.function_bodies_.erase(binding);
	for (size_t i = replay_extra_begin; i < p.extra_lowir_nodes_.size(); ++i)
		if (p.extra_lowir_nodes_[i].binding != NULL)
		{
			bool keep_extra_constexpr_body =
				keep_constexpr_body_for_value_expression &&
				p.extra_lowir_nodes_[i].binding != NULL &&
				p.extra_lowir_nodes_[i].binding->is_constexpr;
			if (!keep_extra_constexpr_body)
				p.function_bodies_.erase(p.extra_lowir_nodes_[i].binding);
		}
	p.extra_lowir_nodes_.resize(replay_extra_begin);
}

Binding* FunctionTemplateInstantiationEngine::finish_replayed_definition(
	Node& fn,
	size_t replay_extra_begin)
{
	fn.binding->is_inline_definition = true;
	if (!declaration->class_template_member)
		assign_specialization_symbol(fn.binding, true);
	if (declaration->placeholder != NULL)
		fn.binding->unwind_no = declaration->placeholder->unwind_no;
	finish_replayed_defaults(fn.binding);
	if (replaced_specialization != NULL &&
	    replaced_specialization != fn.binding)
		replaced_specialization->aliased_binding = fn.binding;
	if (p.function_template_candidate_instantiation_depth_ != 0)
		prune_candidate_replay_bodies(fn.binding, replay_extra_begin);
	else
		p.extra_lowir_nodes_.push_back(fn);
	declaration->function_specializations[key] = fn.binding;
	if (declaration->friend_class_scope != NULL)
		p.add_friend_function(declaration->friend_class_scope, fn.binding);
	p.function_template_placeholders_[fn.binding] = declaration;
	p.function_template_specialization_arguments_[fn.binding] = full_args;
	declaration->completing_specializations.erase(key);
	completion_active = false;
	return fn.binding;
}

}  // namespace internal
}  // namespace pa12
