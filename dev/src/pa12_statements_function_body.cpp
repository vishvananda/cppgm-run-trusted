#include "pa12_internal.h"
#include "pa12_types_support.h"
#include <stdexcept>
using namespace std; namespace pa12 { namespace internal {
bool class_template_specialization_member(
	Binding* function,
	const map<const void*, TemplateDeclaration*>& declarations);
bool explicit_full_class_specialization_member(
	Binding* function,
	const map<const void*, TemplateDeclaration*>& declarations);
bool same_replay_scope(Scope* left, Scope* right);
bool same_replay_type(TypePtr left, TypePtr right);
static bool same_replay_type_with_cv(TypePtr left, TypePtr right)
{
	if (left.get() == right.get())
		return true;
	if (left.get() == NULL || right.get() == NULL)
		return false;
	if (pa11::same_type(left, right))
		return true;
	unsigned left_cv = 0;
	unsigned right_cv = 0;
	while (left->kind == pa11::TypeKind::Cv)
	{
		left_cv |= left->cv;
		left = left->base;
	}
	while (right->kind == pa11::TypeKind::Cv)
	{
		right_cv |= right->cv;
		right = right->base;
	}
	if (left_cv != right_cv || left->kind != right->kind)
		return false;
	switch (left->kind)
	{
	case pa11::TypeKind::Fundamental:
		return left->fundamental == right->fundamental;
	case pa11::TypeKind::Pointer:
	case pa11::TypeKind::LValueReference:
	case pa11::TypeKind::RValueReference:
		return same_replay_type_with_cv(left->base, right->base);
	case pa11::TypeKind::Array:
		return left->unknown_bound == right->unknown_bound &&
		       (left->unknown_bound || left->bound == right->bound) &&
		       same_replay_type_with_cv(left->base, right->base);
	case pa11::TypeKind::Function:
		if (left->variadic != right->variadic ||
		    left->cv != right->cv ||
		    left->ref_qualifier != right->ref_qualifier ||
		    left->parameters.size() != right->parameters.size() ||
		    !same_replay_type_with_cv(left->base, right->base))
			return false;
		for (size_t i = 0; i < left->parameters.size(); ++i)
			if (!same_replay_type_with_cv(left->parameters[i],
			                              right->parameters[i]))
				return false;
		return true;
	case pa11::TypeKind::MemberPointer:
		return same_replay_type_with_cv(left->member_class,
		                                right->member_class) &&
		       same_replay_type_with_cv(left->base, right->base);
	case pa11::TypeKind::Record:
		return same_replay_type(left, right);
	case pa11::TypeKind::Enum:
		return left->name == right->name &&
		       left->enum_underlying == right->enum_underlying;
	case pa11::TypeKind::TemplateParameter:
	case pa11::TypeKind::TemplateTemplateParameter:
		return left->name == right->name;
	case pa11::TypeKind::Cv:
		return same_replay_type_with_cv(left->base, right->base);
	}
	return false;
}
static Scope* reusable_pending_function_scope(const vector<Scope*>& scopes,
                                              Binding* function)
{
	bool member_function =
		function != NULL &&
		function->owner != NULL &&
		function->owner->kind == ScopeKind::Class &&
		!function->is_static_member;
	TypePtr function_type =
		function != NULL && function->type.get() != NULL &&
		function->type->kind == pa11::TypeKind::Function
		? function->type : TypePtr();
	for (size_t s = scopes.size(); s > 0; --s)
	{
		Scope* scope = scopes[s - 1];
		if (scope == NULL || scope->kind != ScopeKind::Function)
			continue;
		if (function != NULL && !function->name.empty() &&
		    scope->name != function->name)
			continue;
		size_t parameter_index = member_function ? 1 : 0;
		bool compatible = true;
		bool have_non_this_parameter = false;
		for (size_t i = 0; i < scope->binding_order.size(); ++i)
		{
			Binding* binding = scope->binding_order[i];
			if (binding->kind != BindingKind::Parameter)
				continue;
			if (member_function && binding->name == "this")
				{
					if (function_type.get() != NULL &&
					    !function_type->parameters.empty() &&
					    !same_replay_type_with_cv(
						    binding->type,
						    function_type->parameters[0]))
						compatible = false;
					continue;
				}
			if (binding->name == "this")
				continue;
			have_non_this_parameter = true;
			if (function_type.get() != NULL)
				{
					if (parameter_index >= function_type->parameters.size() ||
					    !same_replay_type_with_cv(
						    binding->type,
						    function_type->parameters[parameter_index]))
					{
					compatible = false;
					break;
				}
				++parameter_index;
			}
		}
		if (compatible && have_non_this_parameter)
			return scope;
	}
	return NULL;
}
static vector<ParameterInfo> parameters_from_replay_scope(Binding* function,
                                                          Scope* scope)
{
	vector<ParameterInfo> out;
	if (function == NULL || scope == NULL ||
	    function->type.get() == NULL ||
	    function->type->kind != pa11::TypeKind::Function)
		return out;
	size_t first = function->owner != NULL &&
	               function->owner->kind == ScopeKind::Class &&
	               !function->is_static_member ? 1 : 0;
	size_t index = first;
	for (size_t i = 0; i < scope->binding_order.size(); ++i)
	{
		Binding* binding = scope->binding_order[i];
		if (binding->kind != BindingKind::Parameter)
			continue;
		if (first != 0 && binding->name == "this")
			continue;
		if (index >= function->type->parameters.size())
			break;
		ParameterInfo parameter;
		parameter.name = binding->name;
		parameter.type = function->type->parameters[index++];
		out.push_back(parameter);
	}
	return out;
}
static Binding* find_parameter_binding(Scope* scope, const string& name)
{
	if (scope == NULL || name.empty())
		return NULL;
	map<string, vector<Binding*> >::iterator found =
		scope->members.find(name);
	if (found == scope->members.end())
		return NULL;
	for (size_t i = 0; i < found->second.size(); ++i)
		if (found->second[i]->kind == BindingKind::Parameter)
			return found->second[i];
	return NULL;
}
static Binding* find_matching_parameter_binding(Scope* scope,
                                                const string& name,
                                                TypePtr type)
{
	Binding* binding = find_parameter_binding(scope, name);
	if (binding == NULL)
		return NULL;
	return same_replay_type_with_cv(binding->type, type) ? binding : NULL;
}
static TypePtr member_body_this_type(Binding* function)
{
	if (function == NULL ||
	    function->type.get() == NULL ||
	    function->type->kind != pa11::TypeKind::Function ||
	    function->type->parameters.empty())
		return TypePtr();
	TypePtr this_type = function->type->parameters[0];
	unsigned fn_cv = function->type->cv;
	if (fn_cv == pa11::CV_NONE)
		return this_type;
	TypePtr ptr = this_type.get() != NULL ? pa11::strip_cv(this_type) : TypePtr();
	if (ptr.get() == NULL || ptr->kind != pa11::TypeKind::Pointer ||
	    ptr->base.get() == NULL)
		return this_type;
	TypePtr object = ptr->base;
	unsigned object_cv = 0;
	while (object->kind == pa11::TypeKind::Cv)
	{
		object_cv |= object->cv;
		object = object->base;
	}
	unsigned merged_cv = object_cv | fn_cv;
	if (merged_cv == object_cv)
		return this_type;
	return pa11::make_pointer(pa11::make_cv(object, merged_cv));
}
TypePtr Parser::deduce_auto_return_type(Binding* function, const Expr& expr) { if (expr.type.get() == NULL) throw runtime_error("auto return expression has no type"); map<Binding*, TypePtr>::const_iterator found =
auto_return_patterns_.find(function); if (found == auto_return_patterns_.end()) throw runtime_error("auto return pattern missing"); TypePtr pattern = found->second;
TypePtr bare = pa11::strip_cv(pattern); TypePtr deduced; if (bare->kind == pa11::TypeKind::LValueReference) deduced = pa11::make_lvalue_reference(
pa11::make_cv(expression_object_type(expr.type), pattern->base->kind == pa11::TypeKind::Cv ? pattern->base->cv : pa11::CV_NONE)); else if (bare->kind == pa11::TypeKind::RValueReference)
{ TypePtr object = expression_object_type(expr.type); if (expr.category == ValueCategory::LValue) deduced = pa11::make_lvalue_reference(object);
else deduced = pa11::make_rvalue_reference(object); } else
deduced = lvalue_to_rvalue_type(expr.type); map<Binding*, TypePtr>::const_iterator previous = auto_return_deduced_.find(function); if (previous == auto_return_deduced_.end())
auto_return_deduced_[function] = deduced; else if (!pa11::same_type(previous->second, deduced)) throw runtime_error("inconsistent auto return type"); return deduced;
} void Parser::parse_function_body(Binding* function,
                                   const Declarator& declarator,
                                   Node& function_node,
                                   bool inline_definition_spec)
{ vector<ParameterInfo> parameters; const Suffix* suffix = declarator_function_suffix(declarator); if (suffix != NULL)
parameters = suffix->parameters; parse_function_body_from_parameters(function, parameters, function_node, inline_definition_spec); } void Parser::parse_function_body_from_parameters(
	Binding* function,
	const vector<ParameterInfo>& parameters,
	Node& function_node,
	bool inline_definition_spec) {
	vector<Scope*> saved_scopes = scopes_;
	if (function_node.children.empty()) throw runtime_error("missing function node"); Node& fn = function_node.children.back(); Scope* lexical_parent =
		function->owner != NULL && function->owner->kind == ScopeKind::Class ? function->owner : current_scope();
		if (function != NULL &&
		    function->owner != NULL &&
		    function->owner->kind == ScopeKind::Class &&
		    !function->is_static_member &&
		    function->type.get() != NULL &&
		    function->type->kind == pa11::TypeKind::Function &&
		    !function->type->parameters.empty())
		{
			TypePtr this_type = pa11::strip_cv(function->type->parameters[0]);
			TypePtr this_record =
				this_type.get() != NULL &&
				this_type->kind == pa11::TypeKind::Pointer
				? pa11::strip_cv(this_type->base) : TypePtr();
			if (this_record.get() != NULL &&
			    this_record->kind == pa11::TypeKind::Record &&
			    this_record->scope != NULL &&
			    !type_is_template_dependent(this_record))
				lexical_parent = this_record->scope;
		}
		Scope* replay_function_scope = hosted_compatibility_ ? reusable_pending_function_scope(scopes_, function) : NULL;
		if (replay_function_scope != NULL &&
		    replay_function_scope->parent != NULL &&
		    lexical_parent != NULL &&
		    !same_replay_scope(replay_function_scope->parent, lexical_parent))
			replay_function_scope = NULL;
		vector<ParameterInfo> effective_parameters = parameters;
		size_t first_parameter = function->owner != NULL && function->owner->kind == ScopeKind::Class && !function->is_static_member ? 1 : 0; size_t expected_parameters =
		function->type.get() != NULL && function->type->kind == pa11::TypeKind::Function && function->type->parameters.size() >= first_parameter ? function->type->parameters.size() - first_parameter : effective_parameters.size();
		if (replay_function_scope != NULL && effective_parameters.size() < expected_parameters) { vector<ParameterInfo> replay_parameters = parameters_from_replay_scope(function, replay_function_scope); if (replay_parameters.size() >= effective_parameters.size()) effective_parameters = replay_parameters; }
	bool reuse_function_scope = replay_function_scope != NULL && effective_parameters.size() >= expected_parameters; Scope* function_scope = reuse_function_scope ? replay_function_scope : pa11::create_child_scope(lexical_parent, ScopeKind::Function, function->name);
if (function->owner != NULL && function->owner->kind == ScopeKind::Class && !function->is_static_member) {
	if (function->type->parameters.empty()) throw runtime_error("member function missing this parameter"); TypePtr this_type = member_body_this_type(function); Binding* this_binding =
	reuse_function_scope ? find_matching_parameter_binding(function_scope, "this", this_type) : NULL; if (this_binding == NULL) this_binding = pa11::add_binding(function_scope, BindingKind::Parameter, "this", this_type);
Node this_node("parameter this " + pa11::describe_type(this_type)); this_node.binding = this_binding; this_node.type = this_type; add_child(fn, this_node);
} map<Binding*, vector<string> >::const_iterator saved_names = function_parameter_names_.find(function); size_t saved_name_offset =
function->owner != NULL && function->owner->kind == ScopeKind::Class && !function->is_static_member ? 1 : 0; map<string, vector<Binding*> > parameter_packs;
	for (size_t i = 0; i < effective_parameters.size(); ++i) { if (!effective_parameters[i].pack_expression_name.empty() && !effective_parameters[i].pack_name.empty())
{ TemplateArgument subst; if (find_template_value_substitution(effective_parameters[i].pack_name, subst) &&
subst.kind == TemplateArgumentKind::Pack && subst.pack.empty()) { parameter_packs[effective_parameters[i].pack_expression_name];
continue; } } TypePtr parameter_type = effective_parameters[i].type.get() != NULL
? substitute_template_type(effective_parameters[i].type) : TypePtr(); if (parameter_type.get() == NULL) { if (!effective_parameters[i].pack_expression_name.empty())
parameter_packs[effective_parameters[i].pack_expression_name]; continue; } string name = effective_parameters[i].name;
string node_name = name; size_t saved_name_index = saved_name_offset + i; bool force_saved_name = override_function_parameter_name_bindings_.count(function) != 0; bool saved_name_reused_later = false; bool later_parameter_has_name = false;
for (size_t j = i + 1; j < effective_parameters.size(); ++j)
	if (!effective_parameters[j].name.empty())
		later_parameter_has_name = true;
if (saved_names != function_parameter_names_.end() && saved_name_index < saved_names->second.size())
	for (size_t j = saved_name_index + 1; j < saved_names->second.size(); ++j)
		if (!saved_names->second[saved_name_index].empty() &&
		    saved_names->second[saved_name_index] == saved_names->second[j])
			saved_name_reused_later = true;
if ((force_saved_name || (node_name.empty() && !saved_name_reused_later && !later_parameter_has_name)) && saved_names != function_parameter_names_.end() && saved_name_index < saved_names->second.size() && !saved_names->second[saved_name_index].empty() &&
!(function->is_static_member && saved_name_index == 0 && saved_names->second[saved_name_index] == "this")) node_name = saved_names->second[saved_name_index];
	string binding_name = !name.empty() ? name : node_name; if (!binding_name.empty()) { Binding* param =
	reuse_function_scope ? find_matching_parameter_binding(function_scope, binding_name, parameter_type) : NULL; if (param == NULL) param = pa11::add_binding(function_scope, BindingKind::Parameter, binding_name, parameter_type);
if (!effective_parameters[i].pack_expression_name.empty()) parameter_packs[effective_parameters[i].pack_expression_name] .push_back(param); Node param_node("parameter " + node_name + " " +
pa11::describe_type(parameter_type)); param_node.binding = param; param_node.type = parameter_type; add_child(fn, param_node);
} else { Node param_node("parameter " + node_name + " " +
pa11::describe_type(parameter_type)); param_node.type = parameter_type; add_child(fn, param_node); }
	} if (current_scope() != function_scope) scopes_.push_back(function_scope); bool auto_return = auto_return_functions_.count(function) != 0; function_returns_.push_back(auto_return ? TypePtr() : function->type->base);
	active_functions_.push_back(function); function_parameter_pack_substitutions_.push_back(parameter_packs); try { if (at_try_keyword()) { Node body("compound-statement"); add_child(body, parse_try_statement()); add_child(fn, body); } else add_child(fn, parse_compound_statement()); } catch (...) { function_parameter_pack_substitutions_.pop_back(); active_functions_.pop_back();
	function_returns_.pop_back(); scopes_ = saved_scopes; throw; } if (auto_return)
{ map<Binding*, TypePtr>::const_iterator deduced = auto_return_deduced_.find(function); if (deduced == auto_return_deduced_.end())
function->type->base = pa11::make_fundamental(FT_VOID); else function->type->base = deduced->second; fn.type = function->type;
		} if (explicit_full_class_specialization_member(
			       function,
			       record_template_declarations_))
	{
	bool in_class_definition =
		current_scope() == function->owner &&
		function->owner != NULL &&
		function->owner->kind == ScopeKind::Class;
	function->is_declared_inline =
		function->is_declared_inline || inline_definition_spec;
	function->is_inline_definition =
		function->is_inline_definition ||
		inline_definition_spec ||
		in_class_definition;
	function->is_explicit_specialization_member = true;
	}
	else if (class_template_specialization_member(function,
	                                             record_template_declarations_))
	function->is_inline_definition = true; remember_function_body(function, fn); function_parameter_pack_substitutions_.pop_back(); active_functions_.pop_back();
	function_returns_.pop_back(); scopes_ = saved_scopes; }

}  // namespace internal
}  // namespace pa12
