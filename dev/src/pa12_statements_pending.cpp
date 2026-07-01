#include "pa12_internal.h"
#include "pa12_templates_function_support.h"
#include "pa12_types_support.h"
#include <stdexcept>
using namespace std;
namespace pa12 {
namespace internal {

bool explicit_full_class_specialization_member(
	Binding* function,
	const map<const void*, TemplateDeclaration*>& declarations);
bool same_replay_scope(Scope* left, Scope* right);
bool same_member_function_signature(Binding* left, Binding* right);

static void mark_empty_constructor(Binding* function, const Node& fn);
static void mark_empty_destructor(Binding* function, const Node& fn);

static string template_primary(TypePtr type)
{ TypePtr bare = type.get() != NULL ? pa11::strip_cv(type) : TypePtr(); if (bare.get() == NULL) return ""; string primary = bare->template_primary_name.empty() ? bare->name : bare->template_primary_name; size_t args = primary.find('<'); if (args != string::npos) primary = primary.substr(0, args); size_t scope = primary.rfind("::"); if (scope != string::npos) primary = primary.substr(scope + 2); return primary; }
static bool type_in_std_namespace(TypePtr type)
{ type = type.get() != NULL ? pa11::strip_cv(type) : TypePtr(); Scope* scope = type.get() != NULL ? type->scope : NULL; for (Scope* cur = scope; cur != NULL; cur = cur->parent) if (cur->kind == ScopeKind::Namespace && cur->name == "std") return true; return false; }
static bool hosted_vector_insert_owner(Binding* function)
{ if (function == NULL || function->name != "insert" || function->owner == NULL || function->owner->kind != ScopeKind::Class) return false; TypePtr record = pa11::record_type_for_scope(function->owner); record = record.get() != NULL ? pa11::strip_cv(record) : TypePtr(); if (record.get() == NULL || record->kind != pa11::TypeKind::Record || template_primary(record) != "vector") return false; for (Scope* scope = record->scope; scope != NULL; scope = scope->parent) if (scope->kind == ScopeKind::Namespace && scope->name == "std") return true; return false; }
static string hosted_binding_symbol(Binding* function)
{ if (function == NULL) return string(); if (!function->asm_label.empty()) return function->asm_label; if (!function->function_specialization_symbol.empty()) return function->function_specialization_symbol; return function->aliased_binding != NULL ? hosted_binding_symbol(function->aliased_binding) : string(); }
static bool hosted_initializer_list_insert_symbol(Binding* function)
{ string symbol = hosted_binding_symbol(function); return symbol.find("St6vector") != string::npos && symbol.find("6insert") != string::npos && symbol.find("St16initializer_list") != string::npos; }
static bool hosted_vector_realloc_insert_owner(Binding* function)
{ if (function == NULL || function->name != pa11::abi_private_name("M_realloc_insert") || function->owner == NULL || function->owner->kind != ScopeKind::Class || function->type.get() == NULL || function->type->kind != pa11::TypeKind::Function || function->type->parameters.size() != 3) return false; TypePtr record = pa11::record_type_for_scope(function->owner); record = record.get() != NULL ? pa11::strip_cv(record) : TypePtr(); if (record.get() == NULL || record->kind != pa11::TypeKind::Record || template_primary(record) != "vector" || !type_in_std_namespace(record) || record->template_arguments.empty() || record->template_arguments[0].kind != pa11::TemplateInstanceArgumentKind::Type) return false; TypePtr element = pa11::strip_cv(record->template_arguments[0].type); TypePtr param = pa11::strip_cv(function->type->parameters[2]); if (element.get() == NULL || element->kind != pa11::TypeKind::Record || template_primary(element) != "unique_ptr" || !type_in_std_namespace(element) || !pa11::is_reference_type(param)) return false; return pa11::same_type(element, pa11::strip_cv(param->base)); }
static bool hosted_vector_realloc_initializer_list_symbol(Binding* function)
{ string symbol = hosted_binding_symbol(function); return symbol.find("St6vector") != string::npos && symbol.find("17_M_realloc_insert") != string::npos && symbol.find("St16initializer_list") != string::npos; }
static bool hosted_initializer_list_allocator_construct_symbol(Binding* function)
{ string symbol = hosted_binding_symbol(function); return symbol.find("9construct") != string::npos && symbol.find("St16initializer_list") != string::npos && (symbol.find("St15__new_allocator") != string::npos || symbol.find("St16allocator_traits") != string::npos); }
static bool hosted_unique_ptr_allocator_copy_construct(Binding* function)
{ if (function == NULL || function->name != "construct" || function->type.get() == NULL || function->type->kind != pa11::TypeKind::Function || function->type->parameters.size() != 3) return false; string symbol = hosted_binding_symbol(function); if (symbol.find("9construct") == string::npos || (symbol.find("St15__new_allocator") == string::npos && symbol.find("St16allocator_traits") == string::npos)) return false; TypePtr arg = pa11::strip_cv(function->type->parameters[2]); if (arg.get() == NULL || arg->kind != pa11::TypeKind::LValueReference) return false; TypePtr record = pa11::strip_cv(arg->base); return record.get() != NULL && record->kind == pa11::TypeKind::Record && template_primary(record) == "unique_ptr"; }
static bool hosted_unique_ptr_copy_fill_algorithm(Binding* function)
{ if (function == NULL || function->owner == NULL || function->owner->kind != ScopeKind::Namespace || function->owner->name != "std" || (function->name != "__fill_a1" && function->name != "__fill_a" && function->name != "fill") || function->type.get() == NULL || function->type->kind != pa11::TypeKind::Function) return false; return hosted_binding_symbol(function).find("St10unique_ptr") != string::npos; }
static bool hosted_unique_ptr_copy_construct_algorithm(Binding* function)
{ if (function == NULL || function->owner == NULL || function->owner->kind != ScopeKind::Namespace || function->owner->name != "std" || function->name != "_Construct" || function->type.get() == NULL || function->type->kind != pa11::TypeKind::Function) return false; return hosted_binding_symbol(function).find("St10unique_ptr") != string::npos; }
static bool hosted_locale_cache_helper(Binding* function)
{
	if (function == NULL ||
	    function->owner == NULL ||
	    function->owner->kind != ScopeKind::Class)
		return false;
	TypePtr record = pa11::record_type_for_scope(function->owner);
	string primary = template_primary(record);
	return primary == "__use_cache" && function->name == "operator()";
}

static bool pending_body_has_unnamed_parameters(const PendingFunctionBody& pending)
	{ for (size_t i = 0; i < pending.parameters.size(); ++i) if (pending.parameters[i].type.get() != NULL && pending.parameters[i].name.empty()) return true; return false; }
static bool dependent_body_for_concrete_function(Binding* function,
                                                 const Node& body)
{
	if (function == NULL || function->type.get() == NULL)
		return false;
	if (function->is_generated_default_constructor ||
	    function->is_generated_aggregate_constructor ||
	    function->is_generated_copy_move_constructor ||
	    function->is_generated_copy_move_assignment ||
	    function->is_generated_default_destructor)
		return false;
	if (type_structurally_dependent(function->type))
		return false;
	return expr_node_structurally_dependent(body);
}

static void erase_extra_lowir_nodes_for_binding(vector<Node>& nodes,
                                                Binding* function)
{
	for (size_t i = 0; i < nodes.size();)
	{
		if (nodes[i].binding == function)
			nodes.erase(nodes.begin() + i);
		else
			++i;
	}
}

static bool drop_dependent_body_for_concrete_function(
	map<Binding*, Node>& bodies,
	vector<Node>& extra_nodes,
	Binding* function)
{
	if (function == NULL)
		return false;
	if (function->is_object_root)
		return false;
	map<Binding*, Node>::iterator found = bodies.find(function);
	if (found == bodies.end() ||
	    !dependent_body_for_concrete_function(function, found->second))
		return false;
	bodies.erase(found);
	erase_extra_lowir_nodes_for_binding(extra_nodes, function);
	return true;
}

static bool drop_mismatched_body_for_function(
	map<Binding*, Node>& bodies,
	vector<Node>& extra_nodes,
	Binding* function)
{
	if (function == NULL)
		return false;
	map<Binding*, Node>::iterator found = bodies.find(function);
	if (found == bodies.end() ||
	    function_body_signature_matches(function, found->second))
		return false;
	bodies.erase(found);
	erase_extra_lowir_nodes_for_binding(extra_nodes, function);
	return true;
}

Node Parser::retarget_function_body_node(const Node& body, Binding* function)
{
	Node retargeted = body;
	if (function == NULL || function->type.get() == NULL)
		return retargeted;
	retargeted.binding = function;
	retargeted.type = function->type;
	if (retargeted.line.compare(0, 19, "function-definition") == 0)
		retargeted.line = "function-definition " +
			qualified_decl_name(function) + " " +
			pa11::describe_type(function->type);
	size_t parameter_index = 0;
	for (size_t i = 0; i < retargeted.children.size(); ++i)
	{
		Node& child = retargeted.children[i];
		if (child.line.compare(0, 10, "parameter ") != 0)
			continue;
		if (function->type->kind != pa11::TypeKind::Function ||
		    parameter_index >= function->type->parameters.size())
			break;
		string name = child.line.substr(10);
		size_t space = name.find(' ');
		if (space != string::npos)
			name = name.substr(0, space);
		TypePtr parameter_type = function->type->parameters[parameter_index++];
		child.type = parameter_type;
		child.line = "parameter " + name + " " +
			pa11::describe_type(parameter_type);
	}
	return retargeted;
}

bool Parser::finish_prebuilt_pending_body(const PendingFunctionBody& pending)
{
	if (pending.function != NULL &&
	    pending.node.line.compare(0, 19, "function-definition") == 0)
		pending.function->is_inline_definition = true;
	extra_lowir_nodes_.push_back(pending.node);
	if (pending.node.line.compare(0, 19, "function-definition") == 0)
		remember_function_body(pending.function, pending.node);
	if (pending.function != NULL)
		pending_function_bodies_.erase(pending.function);
	return true;
}

bool Parser::pending_body_blocked_by_hosted_deferral(
	const PendingFunctionBody& pending,
	bool force_hosted_body) const
{
	if (force_hosted_body ||
	    !hosted_compatibility_ ||
	    pending.function == NULL ||
	    pending.function->owner == NULL ||
	    pending.function->owner->kind != ScopeKind::Class ||
	    pending.function->is_object_root)
		return false;
	bool pending_class_constructor =
		pending.function->name == pending.function->owner->name;
	if (pending_class_constructor)
		return false;
	if (pending_body_has_unnamed_parameters(pending))
		return true;
	bool pending_inline_definition =
		pending.function->is_inline_definition ||
		pending.node.line.compare(0, 19, "function-definition") == 0;
	bool pending_simple_return_body =
		pending.body_pos + 1 < tokens_.size() &&
		tokens_[pending.body_pos].type == OP_LBRACE &&
		tokens_[pending.body_pos + 1].type == KW_RETURN;
	return pending_inline_definition && !pending_simple_return_body;
}

bool Parser::pending_body_runtime_error_defers(
	const PendingFunctionBody& pending,
	const string& message) const
{
	if (pending.function != NULL &&
	    !pending.function->is_object_root &&
	    function_template_placeholders_.find(pending.function) !=
		    function_template_placeholders_.end() &&
	    (message.compare(0, 16, "name not found: ") == 0 ||
	     message == "member access on non-record" ||
	     message == "arrow on non-pointer"))
		return true;
	return hosted_compatibility_ &&
	       pending.function != NULL &&
	       pending.function->owner != NULL &&
	       pending.function->owner->kind == ScopeKind::Class &&
	       hosted_library_function(pending.function) &&
	       ((!pending.function->is_object_root &&
	         message.compare(0, 16, "name not found: ") == 0) ||
	        message.compare(0, 18, "name not found: __") == 0 ||
	        message == "name not found: _Tp" ||
	        message.compare(0, 28, "cannot resolve call overload") == 0 ||
	        message == "auto return expression has no type" ||
	        (!pending.function->is_object_root &&
	         message == "no matching constructor") ||
	        message == "private member access" ||
	        message == "protected member access");
}

bool Parser::parsed_pending_body_still_dependent(
	const PendingFunctionBody& pending,
	const Node& wrapper,
	bool force_hosted_body) const
{
	return !force_hosted_body &&
	       !wrapper.children.empty() &&
	       pending.function != NULL &&
	       hosted_compatibility_ &&
	       !pending.function->is_object_root &&
	       dependent_body_for_concrete_function(pending.function,
	                                            wrapper.children.back());
}

bool Parser::parse_pending_member_body_now(const PendingFunctionBody& pending,
                                           bool force_hosted_body)
{
	if (pending.prebuilt_node)
		return finish_prebuilt_pending_body(pending);

	bool dropped_stale_body =
		drop_mismatched_body_for_function(function_bodies_,
		                                  extra_lowir_nodes_,
		                                  pending.function);
	if (drop_dependent_body_for_concrete_function(function_bodies_,
	                                              extra_lowir_nodes_,
	                                              pending.function))
		dropped_stale_body = true;
	if (dropped_stale_body)
		note_function_bodies_changed();

	if (pending.function != NULL &&
	    pending.node.line.compare(0, 19, "function-definition") == 0)
		pending.function->is_inline_definition = true;
	if (pending.function != NULL &&
	    function_bodies_.find(pending.function) != function_bodies_.end())
	{
		ensure_function_body_extra_node(pending.function, force_hosted_body);
		return true;
	}

	if (pending_body_blocked_by_hosted_deferral(pending, force_hosted_body))
		return false;

	size_t saved_pos = pos_;
	vector<Scope*> saved_scopes = scopes_;
	vector<Scope*> saved_friend_class_scopes = active_friend_class_scopes_;
	vector<map<string, TypePtr> > saved_type_substitutions =
		template_type_substitutions_;
	vector<map<string, TemplateArgument> > saved_value_substitutions =
		template_value_substitutions_;
	vector<set<string> > saved_pack_substitutions =
		template_type_parameter_packs_;
	auto restore = [&]() {
		template_value_substitutions_ = saved_value_substitutions;
		template_type_substitutions_ = saved_type_substitutions;
		template_type_parameter_packs_ = saved_pack_substitutions;
		active_friend_class_scopes_ = saved_friend_class_scopes;
		scopes_ = saved_scopes;
		pos_ = saved_pos;
	};

	pos_ = pending.body_pos;
	scopes_ = pending.scopes;
	active_friend_class_scopes_ = pending.friend_class_scopes;
	template_type_substitutions_ = pending.type_substitutions;
	template_value_substitutions_ = pending.value_substitutions;
	template_type_parameter_packs_ = pending.pack_substitutions;
	push_pending_owner_template_substitutions(pending);
	push_pending_function_template_substitutions(pending);

	Node wrapper;
	add_child(wrapper, pending.node);
	if (pending.function != NULL &&
	    pending.node.line.compare(0, 19, "function-definition") == 0)
		pending.function->is_inline_definition = true;
	if (pending.function != NULL)
		active_function_body_replays_.insert(pending.function);
	try
	{
		if (pending.constructor_body)
			parse_constructor_body_from_parameters(pending.function,
			                                       pending.class_type,
			                                       pending.parameters,
			                                       wrapper);
		else
			parse_function_body_from_parameters(pending.function,
			                                    pending.parameters,
			                                    wrapper);
		if (pending.function != NULL &&
		    pending.function->owner != NULL &&
		    pending.function->owner->kind == ScopeKind::Class)
			parse_deferred_nested_member_bodies(pending.function->owner);
		}
		catch (const runtime_error& err)
		{
			if (pending.function != NULL)
				active_function_body_replays_.erase(pending.function);
			restore();
			string message = err.what();
			if (pending_body_runtime_error_defers(pending, message))
				return false;
			throw;
	}
	catch (...)
	{
		if (pending.function != NULL)
			active_function_body_replays_.erase(pending.function);
		restore();
		throw;
	}

	if (parsed_pending_body_still_dependent(pending, wrapper, force_hosted_body))
	{
		if (function_bodies_.erase(pending.function) != 0)
			note_function_bodies_changed();
		erase_extra_lowir_nodes_for_binding(extra_lowir_nodes_,
		                                    pending.function);
		active_function_body_replays_.erase(pending.function);
		restore();
		return false;
	}
	if (!wrapper.children.empty())
	{
		mark_empty_constructor(pending.function, wrapper.children.back());
		mark_empty_destructor(pending.function, wrapper.children.back());
		extra_lowir_nodes_.push_back(wrapper.children.back());
	}
	if (pending.function != NULL)
	{
		active_function_body_replays_.erase(pending.function);
		pending_function_bodies_.erase(pending.function);
	}
	restore();
	return true;
}

static bool same_pending_member_function(Binding* pending, Binding* function)
{ return same_member_function_signature(pending, function); }
static bool force_global_pending_member_body(Binding* binding)
{
	if (binding == NULL ||
	    binding->owner == NULL ||
	    binding->owner->kind != ScopeKind::Class)
		return false;
	if (!binding->function_specialization_symbol.empty())
		return false;
	TypePtr owner = pa11::record_type_for_scope(binding->owner);
	owner = owner.get() != NULL ? pa11::strip_cv(owner) : TypePtr();
	if (owner.get() == NULL ||
	    owner->kind != pa11::TypeKind::Record ||
	    owner->is_template_specialization)
		return false;
	for (Scope* scope = binding->owner->parent;
	     scope != NULL;
	     scope = scope->parent)
		if (scope->kind == ScopeKind::Namespace && !scope->name.empty())
			return false;
	return true;
}
bool Parser::parse_pending_function_body(Binding* function)
{
	if (function == NULL ||
	    function_template_candidate_instantiation_depth_ != 0)
		return false;
	if (hosted_compatibility_ &&
	    hosted_library_function(function) &&
	    !function->is_object_root &&
	    ((function->owner != NULL &&
	      function->owner->kind == ScopeKind::Class &&
	      function->name == function->owner->name) ||
	     function->is_inline_definition ||
	     defer_hosted_function_body(function)))
		return false;
	map<Binding*, PendingFunctionBody>::iterator found =
		pending_function_bodies_.find(function);
	if (found == pending_function_bodies_.end())
	{
		map<Binding*, Binding*>::iterator cached =
			pending_function_body_equivalents_.find(function);
		if (cached != pending_function_body_equivalents_.end())
		{
			found = pending_function_bodies_.find(cached->second);
			if (found == pending_function_bodies_.end())
				pending_function_body_equivalents_.erase(cached);
		}
	}
	if (found == pending_function_bodies_.end())
	{
		map<string, set<Binding*> >::iterator named =
			pending_function_body_names_.find(function->name);
		if (named != pending_function_body_names_.end())
		for (set<Binding*>::const_iterator name_it = named->second.begin();
		     name_it != named->second.end();
		     ++name_it)
		{
			Binding* pending = *name_it;
			map<Binding*, PendingFunctionBody>::iterator it =
				pending_function_bodies_.find(pending);
			if (it == pending_function_bodies_.end())
				continue;
			if (pending == NULL ||
			    pending->kind != BindingKind::Function)
				continue;
			if (same_pending_member_function(pending, function))
			{
				pending_function_body_equivalents_[function] =
					pending;
				found = it;
				break;
			}
		}
	}
	if (found == pending_function_bodies_.end())
		return false;
	PendingFunctionBody body = found->second;
	pending_function_bodies_.erase(found);
	bool parsed = parse_pending_member_body_now(body, true);
	if (!parsed && body.function != NULL &&
	    !hosted_library_function(body.function))
		store_pending_function_body(body);
	return parsed;
}

bool Parser::parse_pending_member_body(Binding* function)
{
						if (function == NULL)
							return false;
				if (function_template_candidate_instantiation_depth_ != 0)
					return false;
				if (hosted_compatibility_ &&
				    hosted_library_function(function) &&
				    !function->is_object_root &&
				    ((function->owner != NULL &&
				      function->owner->kind == ScopeKind::Class &&
				      function->name == function->owner->name) ||
				     function->is_inline_definition ||
				     defer_hosted_function_body(function)))
					return false;
		bool parsed = false;
	auto parse_from_bucket =
		[&](map<Scope*, vector<PendingFunctionBody> >::iterator it) -> bool
	{
		vector<PendingFunctionBody>& pending = it->second;
			for (size_t i = 0; i < pending.size(); ++i)
				{
						Binding* pending_function = pending[i].function;
						if (pending_function != function &&
						    (pending_function == NULL ||
					     pending_function->kind != BindingKind::Function ||
					     pending_function->name != function->name))
						continue;
					bool same = pending_function == function ||
					            same_pending_member_function(pending_function,
					                                         function);
					if (!same)
				{
					continue;
				}
				Scope* class_scope = it->first;
			PendingFunctionBody body = pending[i];
			pending.erase(pending.begin() + i);
			unindex_pending_member_body(class_scope, body);
			if (pending.empty())
				pending_member_bodies_.erase(it);
				parsed = parse_pending_member_body_now(body, true);
				if (parsed && body.function != function)
					ensure_function_body_extra_node(function, true);
			if (!parsed)
				enqueue_pending_member_body(class_scope, body);
				return true;
		}
		return false;
	};
	if (function->owner != NULL)
	{
		map<Scope*, vector<PendingFunctionBody> >::iterator exact =
			pending_member_bodies_.find(function->owner);
		if (exact != pending_member_bodies_.end() &&
		    parse_from_bucket(exact))
			return parsed;
	}
	map<string, set<Scope*> >::iterator named =
		pending_member_body_names_.find(function->name);
	if (named != pending_member_body_names_.end())
	{
		vector<Scope*> candidate_scopes(named->second.begin(),
		                                named->second.end());
		for (size_t i = 0; i < candidate_scopes.size(); ++i)
		{
			Scope* class_scope = candidate_scopes[i];
			if (class_scope == function->owner)
				continue;
			if (function->owner != NULL &&
			    !same_replay_scope(class_scope, function->owner))
				continue;
			map<Scope*, vector<PendingFunctionBody> >::iterator it =
				pending_member_bodies_.find(class_scope);
			if (it == pending_member_bodies_.end())
				continue;
			if (parse_from_bucket(it))
				return parsed;
		}
	}
			return false;
			}

bool Parser::hosted_function_has_pending_member_body(Binding* function) const
{
	map<string, set<Scope*> >::const_iterator named =
		pending_member_body_names_.find(function->name);
	if (named == pending_member_body_names_.end())
		return false;
	for (set<Scope*>::const_iterator scope_it = named->second.begin();
	     scope_it != named->second.end();
	     ++scope_it)
	{
		map<Scope*, vector<PendingFunctionBody> >::const_iterator it =
			pending_member_bodies_.find(*scope_it);
		if (it == pending_member_bodies_.end())
			continue;
		for (size_t i = 0; i < it->second.size(); ++i)
			if (same_pending_member_function(it->second[i].function,
			                                 function))
				return true;
	}
	return false;
}

bool Parser::hosted_function_template_body_available(Binding* function) const
{
	map<Binding*, TemplateDeclaration*>::const_iterator demand_template =
		function_template_placeholders_.find(function);
	if (demand_template != function_template_placeholders_.end() &&
	    demand_template->second != NULL &&
	    demand_template->second->has_definition)
		return true;
	if (function->aliased_binding == NULL)
		return false;
	if (pending_function_bodies_.find(function->aliased_binding) !=
	    pending_function_bodies_.end())
		return true;
	map<Binding*, TemplateDeclaration*>::const_iterator alias_template =
		function_template_placeholders_.find(function->aliased_binding);
	return alias_template != function_template_placeholders_.end() &&
	       alias_template->second != NULL &&
	       alias_template->second->has_definition;
}

		bool Parser::defer_hosted_function_body(Binding* function) const
				{
				if (!hosted_compatibility_ || function == NULL)
					return false;
				if (function->is_extern_template_instantiation)
					return true;
				if (hosted_extern_template_class_function(function))
					return true;
				if (hosted_locale_cache_helper(function))
					return true;
				if (function->owner != NULL &&
			    function->owner->kind == ScopeKind::Namespace &&
			    (function->owner->name == "std" ||
			     function->owner->name == "__gnu_cxx") &&
			    function->name == "__stoa")
				return true;
			if (function->type.get() != NULL &&
			    function->type->kind == pa11::TypeKind::Function &&
			    function->type->parameters.size() == 3)
			{
				TypePtr param = function->type->parameters[2];
				if (pa11::is_reference_type(param))
					param = param->base;
				if ((hosted_vector_insert_owner(function) &&
				     is_std_initializer_list_type(pa11::strip_cv(param), NULL)) ||
				    hosted_initializer_list_insert_symbol(function))
					return true;
			}
	if (function->type.get() != NULL &&
	    function->type->kind == pa11::TypeKind::Function &&
	    function->type->parameters.size() == 3 &&
	    (hosted_vector_realloc_insert_owner(function) ||
	     hosted_vector_realloc_initializer_list_symbol(function) ||
	     hosted_initializer_list_allocator_construct_symbol(function) ||
	     hosted_unique_ptr_allocator_copy_construct(function)))
		return true;
			if (function->is_object_root)
				return false;
			if (hosted_unique_ptr_copy_fill_algorithm(function))
				return true;
			if (hosted_unique_ptr_copy_construct_algorithm(function))
				return true;
			if (mark_hosted_stream_insertion_extern_template(function))
				return true;
			if (mark_hosted_getline_extern_template(function))
				return true;
			if (mark_hosted_endl_extern_template(function))
				return true;
				if (function->owner != NULL &&
				    function->owner->kind == ScopeKind::Namespace &&
				    function->owner->name == "std" &&
				    function->name == "forward")
					return true;
				if (function->owner != NULL &&
				    function->owner->kind == ScopeKind::Namespace &&
				    function->owner->name == "std" &&
				    function->name == "make_pair")
					return true;
			if (function->is_inline_definition)
				return false;
		if (pending_function_bodies_.find(function) !=
		    pending_function_bodies_.end())
			return false;
		if (hosted_function_has_pending_member_body(function))
			return false;
		if (hosted_function_template_body_available(function))
			return false;
				if (function->owner != NULL &&
				    function->owner->kind == ScopeKind::Class &&
				    function->name == function->owner->name)
					return false;
			for (Scope* scope = function->owner;
			     scope != NULL;
			     scope = scope->parent)
				if (scope->kind == ScopeKind::Namespace &&
				    (scope->name == "std" ||
				     scope->name == "__gnu_cxx"))
					return true;
		if (function->is_inline_definition)
			return true;
		Binding* probes[2] = { function, function->aliased_binding };
		for (size_t i = 0; i < 2; ++i)
		{
			Binding* probe = probes[i];
			if (probe == NULL || probe->is_object_root)
				continue;
			map<Binding*, TemplateDeclaration*>::const_iterator it =
				function_template_placeholders_.find(probe);
			if (it != function_template_placeholders_.end() &&
			    it->second != NULL &&
			    it->second->has_definition &&
			    !it->second->constructor_template)
				return true;
		}
		return false;
	}
void Parser::drop_stale_function_body_extra_nodes(Binding* function,
                                                  bool force_hosted_body)
{
	if (force_hosted_body)
		return;
	bool dropped =
		drop_mismatched_body_for_function(function_bodies_,
		                                  extra_lowir_nodes_,
		                                  function);
	dropped =
		drop_mismatched_body_for_function(function_bodies_,
		                                  extra_lowir_nodes_,
		                                  function->aliased_binding) ||
		dropped;
	dropped =
		drop_dependent_body_for_concrete_function(function_bodies_,
		                                         extra_lowir_nodes_,
		                                         function) ||
		dropped;
	dropped =
		drop_dependent_body_for_concrete_function(function_bodies_,
		                                         extra_lowir_nodes_,
		                                         function->aliased_binding) ||
		dropped;
	if (dropped)
		note_function_bodies_changed();
}

bool Parser::function_body_available_for_extra_node(Binding* function)
{
	map<Binding*, Node>::const_iterator initial_body =
		function_bodies_.find(function);
	if (initial_body != function_bodies_.end() &&
	    function_body_signature_matches(function, initial_body->second) &&
	    !dependent_body_for_concrete_function(function, initial_body->second))
		return true;
	if (function->aliased_binding != NULL)
	{
		initial_body = function_bodies_.find(function->aliased_binding);
		if (initial_body != function_bodies_.end() &&
		    function_body_signature_matches(function, initial_body->second) &&
		    !dependent_body_for_concrete_function(function,
		                                          initial_body->second))
			return true;
	}
	const vector<Binding*>* candidates =
		function_body_bindings_named(function->name);
	if (candidates == NULL)
		return false;
	for (size_t ci = 0; ci < candidates->size(); ++ci)
	{
		Binding* candidate = (*candidates)[ci];
		if (candidate == NULL ||
		    candidate->kind != BindingKind::Function)
			continue;
		map<Binding*, Node>::const_iterator it =
			function_bodies_.find(candidate);
		if (it == function_bodies_.end())
			continue;
		Node body = it->second;
		if (same_member_function_signature(candidate, function) &&
		    !function_body_signature_matches(function, body))
			body = retarget_function_body_node(body, function);
		if (same_member_function_signature(candidate, function) &&
		    function_body_signature_matches(function, body) &&
		    !dependent_body_for_concrete_function(function, body))
			return true;
	}
	return false;
}

bool Parser::function_body_usable_for_extra_node(Binding* function,
                                                 const Node& body,
                                                 bool force_hosted_body) const
{
	return function_body_signature_matches(function, body) &&
	       (function->is_object_root ||
	        force_hosted_body ||
	        !dependent_body_for_concrete_function(function, body));
}

bool Parser::constructor_template_without_extra_node_arguments(
	TemplateDeclaration* declaration,
	bool have_specialization_arguments) const
{
	if (declaration == NULL ||
	    have_specialization_arguments ||
	    !declaration->constructor_template)
		return false;
	for (size_t pi = 0; pi < declaration->parameters.size(); ++pi)
		if (!declaration->parameters[pi].has_default &&
		    !declaration->parameters[pi].is_pack)
			return false;
	return true;
}

TemplateDeclaration* Parser::function_template_definition_for_extra_node(
	TemplateDeclaration* declaration)
{
	declaration = replacement_function_template_definition(declaration);
	if (declaration->has_definition || declaration->placeholder == NULL)
		return declaration;
	map<Binding*, TemplateDeclaration*>::iterator placeholder =
		function_template_placeholders_.find(declaration->placeholder);
	if (placeholder != function_template_placeholders_.end() &&
	    placeholder->second->has_definition)
		return placeholder->second;
	return declaration;
}

Binding* Parser::instantiate_hosted_alternate_extra_node_template(
	TemplateDeclaration*& declaration,
	const vector<TemplateArgument>& selected_args,
	Binding* function)
{
	for (map<Scope*, map<string, vector<TemplateDeclaration*> > >::iterator
		     scope_it = function_templates_.begin();
	     scope_it != function_templates_.end();
	     ++scope_it)
	{
		map<string, vector<TemplateDeclaration*> >::iterator name_it =
			scope_it->second.find(declaration->name);
		if (name_it == scope_it->second.end())
			continue;
		for (size_t ri = 0; ri < name_it->second.size(); ++ri)
		{
			TemplateDeclaration* candidate = name_it->second[ri];
			if (candidate == NULL ||
			    candidate == declaration ||
			    !candidate->has_definition)
				continue;
			size_t required_arguments = 0;
			for (size_t pi = 0; pi < candidate->parameters.size(); ++pi)
				if (!candidate->parameters[pi].has_default &&
				    !candidate->parameters[pi].is_pack)
					++required_arguments;
			if (selected_args.size() < required_arguments)
				continue;
			try
			{
				complete_template_arguments(candidate, selected_args);
				Binding* alternate =
					instantiate_function_template(candidate, selected_args);
				bool same_signature =
					alternate != NULL &&
					same_member_function_signature(alternate, function);
				if (!same_signature && function->aliased_binding != NULL)
					same_signature = same_member_function_signature(
						alternate,
						function->aliased_binding);
				if (same_signature)
				{
					declaration = candidate;
					return alternate;
				}
			}
			catch (const exception&)
			{
			}
			catch (...)
			{
			}
		}
	}
	return NULL;
}

Binding* Parser::recover_hosted_alternate_extra_node_template(
	TemplateDeclaration*& declaration,
	const vector<TemplateArgument>& selected_args,
	Binding* function)
{
	map<Scope*, map<string, vector<TemplateDeclaration*> > >::iterator scope_it =
		function_templates_.find(declaration->owner);
	if (scope_it == function_templates_.end())
		return NULL;
	map<string, vector<TemplateDeclaration*> >::iterator name_it =
		scope_it->second.find(declaration->name);
	if (name_it == scope_it->second.end())
		return NULL;
	for (size_t ri = 0; ri < name_it->second.size(); ++ri)
	{
		TemplateDeclaration* candidate = name_it->second[ri];
		if (candidate == NULL ||
		    candidate == declaration ||
		    !candidate->has_definition)
			continue;
		try
		{
			Binding* alternate =
				instantiate_function_template(candidate, selected_args);
			bool same_signature =
				alternate != NULL &&
				same_member_function_signature(alternate, function);
			if (same_signature)
			{
				declaration = candidate;
				return alternate;
			}
		}
		catch (const exception&)
		{
		}
		catch (...)
		{
		}
	}
	return NULL;
}

Binding* Parser::instantiate_function_template_for_extra_node(
	Binding* function,
	bool force_hosted_body)
{
	map<Binding*, TemplateDeclaration*>::iterator template_it =
		function_template_placeholders_.find(function);
	if (template_it == function_template_placeholders_.end())
		return function;
	map<Binding*, vector<TemplateArgument> >::iterator args_it =
		function_template_specialization_arguments_.find(function);
	bool have_args =
		args_it != function_template_specialization_arguments_.end();
	bool constructor_without_args =
		constructor_template_without_extra_node_arguments(template_it->second,
		                                                  have_args);
	if (!have_args && !constructor_without_args)
		return function;
	TemplateDeclaration* declaration =
		function_template_definition_for_extra_node(template_it->second);
	vector<TemplateArgument> selected_args =
		have_args ? args_it->second : vector<TemplateArgument>();
	bool saved_force_body_instantiation =
		force_function_template_body_instantiation_;
	if (force_hosted_body)
		force_function_template_body_instantiation_ = true;
	Binding* instantiated = NULL;
	try
	{
		if (!declaration->has_definition && hosted_compatibility_)
			instantiated = instantiate_hosted_alternate_extra_node_template(
				declaration,
				selected_args,
				function);
		if (instantiated == NULL && declaration->has_definition)
		{
			function_template_placeholders_[function] = declaration;
			instantiated =
				instantiate_function_template(declaration, selected_args);
		}
	}
	catch (...)
	{
		instantiated = hosted_compatibility_
			? recover_hosted_alternate_extra_node_template(declaration,
			                                               selected_args,
			                                               function)
			: NULL;
		if (instantiated == NULL)
		{
			force_function_template_body_instantiation_ =
				saved_force_body_instantiation;
			if (!constructor_without_args)
				throw;
		}
	}
	force_function_template_body_instantiation_ =
		saved_force_body_instantiation;
	if (instantiated == NULL || instantiated == function)
		return function;
	bool was_object_root = function->is_object_root;
	function_template_placeholders_[function] = declaration;
	function->aliased_binding = instantiated;
	if (was_object_root)
		instantiated->is_object_root = true;
	return instantiated;
}

map<Binding*, Node>::const_iterator Parser::find_function_body_for_extra_node(
	Binding* function,
	bool force_hosted_body) const
{
	map<Binding*, Node>::const_iterator found = function_bodies_.find(function);
	if (found != function_bodies_.end() &&
	    !function_body_usable_for_extra_node(function,
	                                         found->second,
	                                         force_hosted_body))
		found = function_bodies_.end();
	if (found == function_bodies_.end() && function->aliased_binding != NULL)
	{
		found = function_bodies_.find(function->aliased_binding);
		if (found != function_bodies_.end() &&
		    !function_body_usable_for_extra_node(function,
		                                         found->second,
		                                         force_hosted_body))
			found = function_bodies_.end();
	}
	return found;
}

bool Parser::find_named_function_body_for_extra_node(
	Binding* function,
	bool force_hosted_body,
	map<Binding*, Node>::const_iterator& found)
{
	const vector<Binding*>* candidates =
		function_body_bindings_named(function->name);
	if (candidates == NULL)
		return false;
	for (size_t ci = 0; ci < candidates->size(); ++ci)
	{
		Binding* candidate = (*candidates)[ci];
		if (candidate == NULL ||
		    candidate->kind != BindingKind::Function)
			continue;
		map<Binding*, Node>::const_iterator it =
			function_bodies_.find(candidate);
		if (it == function_bodies_.end())
			continue;
		Node body = it->second;
		if (same_member_function_signature(candidate, function) &&
		    !function_body_signature_matches(function, body))
			body = retarget_function_body_node(body, function);
		if (!same_member_function_signature(candidate, function) ||
		    !function_body_usable_for_extra_node(function,
		                                         body,
		                                         force_hosted_body))
			continue;
		if (candidate != function)
		{
			if (candidate->is_inline_definition &&
			    !explicit_full_class_specialization_member(
				    function,
				    record_template_declarations_))
				function->is_inline_definition = true;
			body.binding = function;
			body.type = function->type;
			remember_function_body(function, body);
			found = function_bodies_.find(function);
		}
		else
			found = it;
		return true;
	}
	return false;
}

bool Parser::extra_function_body_node_already_satisfied(
	Binding* function,
	bool force_hosted_body,
	map<Binding*, Node>::const_iterator found)
{
	for (size_t i = 0; i < extra_lowir_nodes_.size();)
	{
		if (extra_lowir_nodes_[i].binding != function)
		{
			++i;
			continue;
		}
		bool skeleton = extra_lowir_nodes_[i].children.empty();
		bool stale_dependent =
			!function->is_object_root &&
			!force_hosted_body &&
			dependent_body_for_concrete_function(function,
			                                     extra_lowir_nodes_[i]);
		if (stale_dependent ||
		    (skeleton && found != function_bodies_.end()))
			extra_lowir_nodes_.erase(extra_lowir_nodes_.begin() + i);
		else
			return true;
	}
	return false;
}

void Parser::append_function_body_extra_node(
	Binding* function,
	map<Binding*, Node>::const_iterator found)
{
	if (found == function_bodies_.end() ||
	    !function_body_signature_matches(function, found->second))
		return;
	if (found->first != function &&
	    same_member_function_signature(found->first, function))
	{
		if (found->first != NULL &&
		    found->first->is_inline_definition &&
		    !explicit_full_class_specialization_member(
			    function,
			    record_template_declarations_))
			function->is_inline_definition = true;
		Node body = found->second;
		body.binding = function;
		body.type = function->type;
		remember_function_body(function, body);
		extra_lowir_nodes_.push_back(body);
	}
	else
		extra_lowir_nodes_.push_back(found->second);
}

void Parser::ensure_function_body_extra_node(Binding* function,
                                             bool force_hosted_body)
{
	if (function == NULL ||
	    function->is_extern_template_instantiation)
		return;
	drop_stale_function_body_extra_nodes(function, force_hosted_body);
	bool have_body = function_body_available_for_extra_node(function);
	if (!have_body &&
	    !force_hosted_body &&
	    defer_hosted_function_body(function))
		return;
	if (!have_body)
		function = instantiate_function_template_for_extra_node(
			function,
			force_hosted_body);
	map<Binding*, Node>::const_iterator found =
		find_function_body_for_extra_node(function, force_hosted_body);
	if (found == function_bodies_.end())
		find_named_function_body_for_extra_node(function,
		                                        force_hosted_body,
		                                        found);
	if (extra_function_body_node_already_satisfied(function,
	                                               force_hosted_body,
	                                               found))
		return;
	append_function_body_extra_node(function, found);
}

static bool function_body_empty(const Node& fn) { if (fn.children.empty())
return true; const Node& body = fn.children.back(); return body.line == "compound-statement" && body.children.empty(); }
static bool empty_constructor_body_implies_noexcept(Binding* function)
{ return function != NULL &&
         (function->is_generated_default_constructor || function->is_defaulted); }
static void mark_empty_constructor(Binding* function, const Node& fn) { if (function == NULL || function->owner == NULL ||
function->owner->kind != ScopeKind::Class || function->name != function->owner->name || !function_body_empty(fn)) return;
function->is_noop_constructor = true; if (empty_constructor_body_implies_noexcept(function)) function->unwind_no = true; map<string, vector<Binding*> >::iterator found = function->owner->members.find(function->name);
if (found == function->owner->members.end()) return; for (size_t i = 0; i < found->second.size(); ++i) { Binding* candidate = found->second[i];
if (candidate->kind == BindingKind::Function && pa11::same_type(candidate->type, function->type)) { candidate->is_noop_constructor = true; if (empty_constructor_body_implies_noexcept(candidate)) candidate->unwind_no = true; } } }
static void mark_empty_destructor(Binding* function, const Node& fn) { if (function == NULL || function->name.empty() ||
function->name[0] != '~' || function->is_virtual || !function_body_empty(fn)) return;
function->is_noop_destructor = true; Scope* owner = function->owner; if (owner == NULL) return;
map<string, vector<Binding*> >::iterator found = owner->members.find(function->name); if (found == owner->members.end()) return;
for (size_t i = 0; i < found->second.size(); ++i) { Binding* candidate = found->second[i]; if (candidate->kind == BindingKind::Function &&
pa11::same_type(candidate->type, function->type)) candidate->is_noop_destructor = true; } }
void Parser::parse_pending_member_bodies(Scope* class_scope) { map<Scope*, vector<PendingFunctionBody> >::iterator found = pending_member_bodies_.find(class_scope);
	if (function_template_candidate_instantiation_depth_ != 0) return;
	if (found == pending_member_bodies_.end()) return; if (!active_class_instantiations_.empty() && !validating_template_definition_)
	return; vector<PendingFunctionBody> pending = found->second; pending_member_bodies_.erase(found); remove_pending_member_body_scope_from_index(class_scope); vector<PendingFunctionBody> still_pending;
		for (size_t i = 0; i < pending.size(); ++i) { if (pending[i].function != NULL && function_template_placeholders_.find(pending[i].function) !=
		function_template_placeholders_.end()) { still_pending.push_back(pending[i]); continue;
			} bool keep_global_fallback = force_global_pending_member_body(pending[i].function); bool parsed = parse_pending_member_body_now(pending[i]); if (!parsed && keep_global_fallback) { parsed = parse_pending_member_body_now(pending[i], true); }
		if (!parsed || keep_global_fallback) still_pending.push_back(pending[i]); } if (!still_pending.empty())
		{ pending_member_bodies_[class_scope] = still_pending; for (size_t i = 0; i < still_pending.size(); ++i) index_pending_member_body(class_scope, still_pending[i]); } } void Parser::parse_deferred_nested_member_bodies(Scope* class_scope) {
map<Scope*, vector<Scope*> >::iterator found = deferred_nested_member_body_scopes_.find(class_scope); if (found == deferred_nested_member_body_scopes_.end()) return;
vector<Scope*> nested = found->second; deferred_nested_member_body_scopes_.erase(found); for (size_t i = 0; i < nested.size(); ++i) {
parse_pending_member_bodies(nested[i]); parse_deferred_nested_member_bodies(nested[i]); } }

}  // namespace internal
}  // namespace pa12
