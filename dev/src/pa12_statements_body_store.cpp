#include "pa12_internal.h"
#include "pa12_types_support.h"
#include <stdexcept>
using namespace std; namespace pa12 { namespace internal {
void Parser::note_function_bodies_changed()
{ ++function_bodies_generation_; noop_constructor_body_scan_misses_.clear(); }
void Parser::refresh_function_body_name_index() const
{
	if (function_body_name_index_generation_ != (size_t)-1)
		return;
	function_body_names_.clear();
	for (map<Binding*, Node>::const_iterator it = function_bodies_.begin();
	     it != function_bodies_.end();
	     ++it)
	{
		Binding* function = it->first;
		if (function == NULL || function->kind != BindingKind::Function)
			continue;
		function_body_names_[function->name].push_back(function);
	}
	function_body_name_index_generation_ = function_bodies_generation_;
}
const vector<Binding*>* Parser::function_body_bindings_named(
	const string& name) const
{
	refresh_function_body_name_index();
	map<string, vector<Binding*> >::const_iterator found =
		function_body_names_.find(name);
	return found == function_body_names_.end() ? NULL : &found->second;
}
void Parser::remember_function_body(Binding* function, const Node& function_node)
{ if (function != NULL) { bool inserted = function_bodies_.find(function) == function_bodies_.end(); function_bodies_[function] = function_node; if (inserted && function->kind == BindingKind::Function && function_body_name_index_generation_ != (size_t)-1) { vector<Binding*>& bucket = function_body_names_[function->name]; bool indexed = false; for (size_t i = 0; i < bucket.size(); ++i) if (bucket[i] == function) { indexed = true; break; } if (!indexed) bucket.push_back(function); } note_function_bodies_changed(); } }
void Parser::append_pending_member_body(Scope* class_scope,
                                        const PendingFunctionBody& pending)
{ pending_member_bodies_[class_scope].push_back(pending); index_pending_member_body(class_scope, pending); }
void Parser::index_pending_member_body(Scope* class_scope,
                                       const PendingFunctionBody& pending)
{ if (class_scope == NULL || pending.function == NULL || pending.function->kind != BindingKind::Function) return; pending_member_body_names_[pending.function->name].insert(class_scope); }
void Parser::unindex_pending_member_body(Scope* class_scope,
                                         const PendingFunctionBody& pending)
{ if (class_scope == NULL || pending.function == NULL || pending.function->kind != BindingKind::Function) return; const string name = pending.function->name; map<string, set<Scope*> >::iterator named = pending_member_body_names_.find(name); if (named == pending_member_body_names_.end()) return; bool still_present = false; map<Scope*, vector<PendingFunctionBody> >::const_iterator bucket = pending_member_bodies_.find(class_scope); if (bucket != pending_member_bodies_.end()) for (size_t i = 0; i < bucket->second.size(); ++i) { Binding* fn = bucket->second[i].function; if (fn != NULL && fn->kind == BindingKind::Function && fn->name == name) { still_present = true; break; } } if (!still_present) { named->second.erase(class_scope); if (named->second.empty()) pending_member_body_names_.erase(named); } }
void Parser::remove_pending_member_body_scope_from_index(Scope* class_scope)
{ if (class_scope == NULL) return; for (map<string, set<Scope*> >::iterator it = pending_member_body_names_.begin(); it != pending_member_body_names_.end(); ) { it->second.erase(class_scope); if (it->second.empty()) { map<string, set<Scope*> >::iterator doomed = it++; pending_member_body_names_.erase(doomed); } else ++it; } }
void Parser::rebuild_pending_member_body_name_index()
{ pending_member_body_names_.clear(); for (map<Scope*, vector<PendingFunctionBody> >::const_iterator it = pending_member_bodies_.begin(); it != pending_member_bodies_.end(); ++it) for (size_t i = 0; i < it->second.size(); ++i) index_pending_member_body(it->first, it->second[i]); }
void Parser::enqueue_pending_member_body(Scope* class_scope, PendingFunctionBody pending) { if (pending.scopes.empty()) {
	pending.scopes = scopes_; pending.friend_class_scopes = active_friend_class_scopes_; pending.type_substitutions = template_type_substitutions_; pending.value_substitutions = template_value_substitutions_; pending.pack_substitutions = template_type_parameter_packs_; }
	append_pending_member_body(class_scope, pending); if (pending.function != NULL && !hosted_library_function(pending.function))
	store_pending_function_body(pending); } void Parser::enqueue_pending_function_body(PendingFunctionBody pending) { if (pending.scopes.empty()) {
pending.scopes = scopes_; pending.friend_class_scopes = active_friend_class_scopes_; pending.type_substitutions = template_type_substitutions_; pending.value_substitutions = template_value_substitutions_;
pending.pack_substitutions = template_type_parameter_packs_; } store_pending_function_body(pending); } void Parser::store_pending_function_body(const PendingFunctionBody& pending)
{ pending_function_bodies_[pending.function] = pending; if (pending.function != NULL && pending.function->kind == BindingKind::Function) pending_function_body_names_[pending.function->name].insert(pending.function); }
void Parser::rebuild_pending_function_body_name_index()
{ pending_function_body_names_.clear(); for (map<Binding*, PendingFunctionBody>::const_iterator it = pending_function_bodies_.begin(); it != pending_function_bodies_.end(); ++it) if (it->first != NULL && it->first->kind == BindingKind::Function) pending_function_body_names_[it->first->name].insert(it->first); }
void Parser::push_pending_owner_template_substitutions(
const PendingFunctionBody& pending) { TypePtr owner_record = pending.function != NULL && pending.function->owner != NULL
? pa11::record_type_for_scope(pending.function->owner) : TypePtr(); owner_record = owner_record.get() != NULL ? pa11::strip_cv(owner_record) : TypePtr();
map<const void*, TemplateDeclaration*>::iterator owner_template = owner_record.get() != NULL ? record_template_declarations_.find(owner_record.get()) : record_template_declarations_.end();
map<const void*, vector<TemplateArgument> >::iterator owner_args = owner_record.get() != NULL ? record_template_arguments_.find(owner_record.get()) : record_template_arguments_.end();
if (owner_template == record_template_declarations_.end() || owner_args == record_template_arguments_.end()) return; map<string, TypePtr> subst;
map<string, TemplateArgument> value_subst; set<string> pack_subst; for (size_t i = 0; i < owner_args->second.size() &&
i < owner_template->second->parameters.size(); ++i) { const TemplateParameterInfo& parameter =
owner_template->second->parameters[i]; if (parameter.name.empty()) continue; if (parameter.kind == TemplateParameterKind::Type)
{ if (parameter.is_pack) { subst[parameter.name] =
template_parameter_placeholder_type(parameter); value_subst[parameter.name] = owner_args->second[i]; pack_subst.insert(parameter.name); }
else subst[parameter.name] = owner_args->second[i].type; } else
value_subst[parameter.name] = owner_args->second[i]; } template_type_substitutions_.push_back(subst); template_value_substitutions_.push_back(value_subst);
template_type_parameter_packs_.push_back(pack_subst); } void Parser::push_pending_function_template_substitutions( const PendingFunctionBody& pending)
{ map<Binding*, TemplateDeclaration*>::iterator function_template = pending.function != NULL ? function_template_placeholders_.find(pending.function)
: function_template_placeholders_.end(); map<Binding*, vector<TemplateArgument> >::iterator function_args = pending.function != NULL ? function_template_specialization_arguments_.find(pending.function)
: function_template_specialization_arguments_.end(); if (function_template == function_template_placeholders_.end() || function_args == function_template_specialization_arguments_.end()) return;
TemplateDeclaration* declaration = function_template->second; map<string, TypePtr> subst; map<string, TemplateArgument> value_subst; set<string> pack_subst;
for (size_t i = 0; i < function_args->second.size() && i < declaration->parameters.size(); ++i)
{ const TemplateParameterInfo& parameter = declaration->parameters[i]; if (parameter.name.empty()) continue;
if (parameter.kind == TemplateParameterKind::Type) { if (parameter.is_pack) {
subst[parameter.name] = template_parameter_placeholder_type(parameter); value_subst[parameter.name] = function_args->second[i]; pack_subst.insert(parameter.name);
} else subst[parameter.name] = function_args->second[i].type; }
	else value_subst[parameter.name] = function_args->second[i]; } template_type_substitutions_.push_back(subst);
	template_value_substitutions_.push_back(value_subst); template_type_parameter_packs_.push_back(pack_subst); }

}  // namespace internal
}  // namespace pa12
