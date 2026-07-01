#include "pa12_internal.h"
#include "pa12_expr_parser_support.h"
#include "pa12_templates_function_support.h"
#include "pa12_templates_instance_support.h"
#include <algorithm>
#include <functional>
#include <stdexcept>
using namespace std; namespace pa12 { namespace internal { namespace {
bool record_has_reference_field(TypePtr type); bool type_contains_enum(TypePtr type) { TypePtr bare = type.get() != NULL ? pa11::strip_cv(type) : TypePtr();
if (bare.get() == NULL) return false; if (bare->kind == pa11::TypeKind::Array) return type_contains_enum(bare->base);
if (bare->kind == pa11::TypeKind::Enum) return true; if (bare->kind != pa11::TypeKind::Record) return false;
pa11::layout_record_type(bare); { vector<TypePtr> bases = pa11::record_direct_bases(bare); for (size_t b = 0; b < bases.size(); ++b) if (type_contains_enum(bases[b])) return true; } for (size_t i = 0; i < bare->fields.size(); ++i)
if (type_contains_enum(bare->fields[i]->type)) return true; return false; }
Node zero_value_node(TypePtr type) { Node zero("literal prvalue " + pa11::describe_type(type) + " 0"); zero.type = pa11::strip_top_level_cv(type);
zero.category = ValueCategory::PRValue; zero.token_text = "0"; zero.has_constant_value = true; zero.constant_value = 0;
return zero; } Node empty_braced_value_node(TypePtr type) {
Node init("braced-init-list"); init.type = type; init.category = ValueCategory::PRValue; return init;
}
bool implicit_generated_default_constructor(Binding* binding) { return binding != NULL && binding->kind == BindingKind::Function &&
binding->type.get() != NULL && binding->type->kind == pa11::TypeKind::Function && binding->type->parameters.size() == 1 &&
binding->is_generated_default_constructor && !binding->is_defaulted; }
bool user_declared_constructor_binding(Binding* binding) { return binding != NULL && binding->kind == BindingKind::Function &&
binding->type.get() != NULL && binding->type->kind == pa11::TypeKind::Function &&
!binding->is_generated_aggregate_constructor && !binding->is_generated_copy_move_constructor &&
!(binding->is_generated_default_constructor && !binding->is_defaulted); }
bool record_has_user_declared_constructor(TypePtr type) { TypePtr bare = type.get() != NULL ? pa11::strip_cv(type) : TypePtr();
if (bare.get() == NULL || bare->kind != pa11::TypeKind::Record || bare->scope == NULL) return false;
map<string, vector<Binding*> >::const_iterator found = bare->scope->members.find(bare->scope->name); if (found == bare->scope->members.end()) return false;
for (size_t i = 0; i < found->second.size(); ++i) if (user_declared_constructor_binding(found->second[i])) return true; return false; }
bool constructor_body_node_empty(const Node& fn)
{ if (fn.children.empty()) return true; const Node& body = fn.children.back();
return body.line == "compound-statement" && body.children.empty(); }
bool compatible_empty_constructor_binding(Binding* candidate, Binding* target)
{ if (candidate == NULL || target == NULL || candidate->owner == NULL || target->owner == NULL ||
candidate->owner->kind != ScopeKind::Class || target->owner->kind != ScopeKind::Class ||
candidate->name != candidate->owner->name || target->name != target->owner->name ||
candidate->type.get() == NULL || target->type.get() == NULL ||
candidate->type->kind != pa11::TypeKind::Function || target->type->kind != pa11::TypeKind::Function ||
candidate->type->parameters.size() != 1 || target->type->parameters.size() != 1) return false;
TypePtr candidate_owner = pa11::record_type_for_scope(candidate->owner);
TypePtr target_owner = pa11::record_type_for_scope(target->owner);
return candidate_owner.get() != NULL && target_owner.get() != NULL &&
same_template_record_type(candidate_owner, target_owner); }
bool empty_constructor_body_implies_noexcept(Binding* ctor)
{ return ctor != NULL && (ctor->is_generated_default_constructor || ctor->is_defaulted); }
void refresh_noop_constructor_from_bodies(
	map<Binding*, Node>& bodies,
	Binding* ctor,
	size_t bodies_generation,
	set<pair<Binding*, size_t> >& scan_misses)
{ if (ctor == NULL || ctor->is_noop_constructor) return; map<Binding*, Node>::const_iterator direct = bodies.find(ctor);
if (direct != bodies.end() && constructor_body_node_empty(direct->second)) { ctor->is_noop_constructor = true; if (empty_constructor_body_implies_noexcept(ctor)) ctor->unwind_no = true; return; }
pair<Binding*, size_t> miss_key = make_pair(ctor, bodies_generation);
if (scan_misses.find(miss_key) != scan_misses.end())
	return;
for (map<Binding*, Node>::const_iterator it = bodies.begin(); it != bodies.end(); ++it)
if (compatible_empty_constructor_binding(it->first, ctor) && constructor_body_node_empty(it->second)) { ctor->is_noop_constructor = true; if (empty_constructor_body_implies_noexcept(ctor)) ctor->unwind_no = true; return; }
scan_misses.insert(miss_key); }
map<Binding*, Node>::const_iterator find_default_member_initializer(
	const map<Binding*, Node>& initializers, Binding* binding)
{
	map<Binding*, Node>::const_iterator found = initializers.find(binding);
	if (found != initializers.end())
		return found;
	if (binding != NULL && binding->aliased_binding != NULL)
	{
		found = initializers.find(binding->aliased_binding);
		if (found != initializers.end())
			return found;
	}
	for (map<Binding*, Node>::const_iterator it = initializers.begin();
	     it != initializers.end();
	     ++it)
	{
		Binding* candidate = it->first;
		if (candidate == NULL || binding == NULL ||
		    candidate->name != binding->name ||
		    candidate->owner == NULL || binding->owner == NULL ||
		    candidate->owner->kind != ScopeKind::Class ||
		    binding->owner->kind != ScopeKind::Class)
			continue;
		TypePtr candidate_owner =
			pa11::record_type_for_scope(candidate->owner);
		TypePtr binding_owner =
			pa11::record_type_for_scope(binding->owner);
		if (candidate_owner.get() != NULL &&
		    binding_owner.get() != NULL &&
		    same_template_record_type(candidate_owner, binding_owner))
			return it;
	}
	return initializers.end();
}
string record_primary_name(TypePtr type)
{
	TypePtr bare = type.get() != NULL ? pa11::strip_cv(type) : TypePtr();
	if (bare.get() == NULL)
		return "";
	string primary = bare->template_primary_name.empty()
		? bare->name : bare->template_primary_name;
	size_t pos = primary.rfind("::");
	if (pos != string::npos)
		primary = primary.substr(pos + 2);
	pos = primary.find('<');
	if (pos != string::npos)
		primary = primary.substr(0, pos);
	return primary;
}
vector<Binding*> default_constructor_data_members(TypePtr type)
{
	TypePtr bare = type.get() != NULL ? pa11::strip_cv(type) : TypePtr();
	if (bare.get() == NULL || bare->kind != pa11::TypeKind::Record)
		return vector<Binding*>();
	if (!bare->fields.empty())
		return bare->fields;
	vector<Binding*> out;
	if (record_primary_name(bare) != pa11::abi_private_name("Hashtable") ||
	    bare->scope == NULL)
		return out;
	for (size_t i = 0; i < bare->scope->binding_order.size(); ++i)
	{
		Binding* member = bare->scope->binding_order[i];
		if (member == NULL ||
		    member->kind != BindingKind::Variable ||
		    member->is_static_member ||
		    member->aliased_binding != NULL)
			continue;
		out.push_back(member);
	}
	return out;
}
Binding* find_nonstatic_data_member(TypePtr record, const string& name)
{
	TypePtr bare = record.get() != NULL ? pa11::strip_cv(record) : TypePtr();
	if (bare.get() == NULL ||
	    bare->kind != pa11::TypeKind::Record ||
	    bare->scope == NULL)
		return NULL;
	Binding* out = NULL;
	map<string, vector<Binding*> >::const_iterator found =
		bare->scope->members.find(name);
	if (found != bare->scope->members.end())
		for (size_t i = 0; i < found->second.size(); ++i)
		{
			Binding* binding = found->second[i];
			if (binding->kind != BindingKind::Variable ||
			    binding->is_static_member)
				continue;
			if (out != NULL && binding != out)
				return NULL;
			out = binding;
		}
	vector<TypePtr> bases = pa11::record_direct_bases(bare);
	for (size_t i = 0; i < bases.size(); ++i)
	{
		Binding* base_member = find_nonstatic_data_member(bases[i], name);
		if (base_member == NULL)
			continue;
		if (out != NULL && base_member != out)
			return NULL;
		out = base_member;
	}
	return out;
}

bool hosted_hashtable_storage_record(TypePtr record)
{
	TypePtr bare = record.get() != NULL ? pa11::strip_cv(record) : TypePtr();
	return bare.get() != NULL &&
	       bare->kind == pa11::TypeKind::Record &&
	       record_primary_name(bare) == pa11::abi_private_name("Hashtable") &&
	       find_nonstatic_data_member(bare, pa11::abi_private_name("M_buckets")) != NULL &&
	       find_nonstatic_data_member(bare, pa11::abi_private_name("M_bucket_count")) != NULL;
}

Binding* default_constructor_binding_for_synthetic_check(TypePtr type)
{
	TypePtr bare = type.get() != NULL ? pa11::strip_cv(type) : TypePtr();
	if (bare.get() == NULL ||
	    bare->kind != pa11::TypeKind::Record ||
	    bare->scope == NULL)
		return NULL;
	map<string, vector<Binding*> >::const_iterator found =
		bare->scope->members.find(bare->scope->name);
	if (found == bare->scope->members.end())
		return NULL;
	for (size_t i = 0; i < found->second.size(); ++i)
	{
		Binding* binding = found->second[i];
		if (binding->kind == BindingKind::Function &&
		    binding->type.get() != NULL &&
		    binding->type->kind == pa11::TypeKind::Function &&
		    binding->type->parameters.size() == 1)
			return binding;
	}
	return NULL;
}

bool default_constructor_type_needs_synthetic_body(
	TypePtr type,
	const map<Binding*, Node>& default_member_initializers,
	set<const pa11::Type*>& seen)
{
	TypePtr bare = type.get() != NULL ? pa11::strip_cv(type) : TypePtr();
	if (bare.get() == NULL)
		return false;
	if (bare->kind == pa11::TypeKind::Array)
		return default_constructor_type_needs_synthetic_body(
			bare->base, default_member_initializers, seen);
	if (bare->kind != pa11::TypeKind::Record)
		return false;
	if (!seen.insert(bare.get()).second)
		return false;
	Binding* ctor = default_constructor_binding_for_synthetic_check(bare);
	bool defaulted_default =
		ctor != NULL &&
		ctor->is_defaulted &&
		ctor->type.get() != NULL &&
		ctor->type->kind == pa11::TypeKind::Function &&
		ctor->type->parameters.size() == 1;
	if (ctor != NULL && !defaulted_default)
		return !ctor->is_noop_constructor;
	pa11::layout_record_type(bare);
	vector<TypePtr> virtual_bases = pa11::record_virtual_bases(bare);
	for (size_t i = 0; i < virtual_bases.size(); ++i)
		if (default_constructor_type_needs_synthetic_body(
			    virtual_bases[i], default_member_initializers, seen))
			return true;
	vector<TypePtr> direct_bases = pa11::record_direct_bases(bare);
	for (size_t i = 0; i < direct_bases.size(); ++i)
		if (!pa11::record_direct_base_is_virtual(bare, i) &&
		    default_constructor_type_needs_synthetic_body(
			    direct_bases[i], default_member_initializers, seen))
			return true;
	vector<Binding*> members = default_constructor_data_members(bare);
	for (size_t i = 0; i < members.size(); ++i)
	{
		Binding* field = members[i];
		if (find_default_member_initializer(default_member_initializers,
		                                    field) !=
		    default_member_initializers.end())
			return true;
		if (default_constructor_type_needs_synthetic_body(
			    field->type, default_member_initializers, seen))
			return true;
	}
	return false;
}

bool default_constructor_needs_synthetic_storage_body(TypePtr record,
                                                      Binding* existing,
                                                      bool defaulted_default,
                                                      const map<Binding*, Node>&
							      default_member_initializers)
{
	if (defaulted_default)
	{
		set<const pa11::Type*> seen;
		return default_constructor_type_needs_synthetic_body(
			record, default_member_initializers, seen);
	}
	return hosted_hashtable_storage_record(record) &&
	       existing != NULL &&
	       existing->type.get() != NULL &&
	       existing->type->kind == pa11::TypeKind::Function &&
	       existing->type->parameters.size() == 1;
}

Expr make_this_member_replay_expr(Binding* this_binding, const string& name)
{
	Expr out;
	if (this_binding == NULL || name.empty())
		return out;
	TypePtr this_type = this_binding->type.get() != NULL
		? pa11::strip_cv(this_binding->type) : TypePtr();
	TypePtr record = this_type.get() != NULL &&
		this_type->kind == pa11::TypeKind::Pointer
		? pa11::strip_cv(this_type->base) : TypePtr();
	if (record.get() == NULL ||
	    record->kind != pa11::TypeKind::Record ||
	    record->scope == NULL)
		return out;
	Binding* member = find_nonstatic_data_member(record, name);
	if (member == NULL)
		return out;
	Expr this_expr;
	this_expr.valid = true;
	this_expr.binding = this_binding;
	this_expr.type = this_binding->type;
	this_expr.category = ValueCategory::LValue;
	this_expr.node = Node("id-expression lvalue " +
	                      pa11::describe_type(this_binding->type) +
	                      " this");
	this_expr.node.token_text = "this";
	annotate_expr_node(this_expr);
	out.valid = true;
	out.binding = member;
	out.type = member->type;
	out.category = ValueCategory::LValue;
	out.node = Node("member-expression lvalue " +
	                pa11::describe_type(member->type) + " OP_DOT:" + name);
	add_child(out.node, this_expr.node);
	out.node.binding = member;
	out.node.has_op = true;
	out.node.op = OP_ARROW;
	out.node.token_text = name;
	annotate_expr_node(out);
	return out;
}
}  // namespace
TypePtr Parser::make_member_function_type(Scope* class_scope, TypePtr type) { TypePtr class_type = pa11::record_type_for_scope(class_scope); if (class_type.get() == NULL)
class_type = pa11::make_record_type(class_scope->name, "struct", true, class_scope);
if (type->cv != pa11::CV_NONE) class_type = pa11::make_cv(class_type, type->cv); vector<TypePtr> params; params.push_back(pa11::make_pointer(class_type));
for (size_t i = 0; i < type->parameters.size(); ++i) params.push_back(type->parameters[i]); TypePtr out = pa11::make_function(type->base, params, type->variadic); out->ref_qualifier = type->ref_qualifier; return out; }
void Parser::discard_implicit_default_constructor(TypePtr type, Binding* keep) { TypePtr bare = type.get() != NULL ? pa11::strip_cv(type) : TypePtr();
if (bare.get() == NULL || bare->kind != pa11::TypeKind::Record || bare->scope == NULL) return; map<string, vector<Binding*> >::iterator found =
bare->scope->members.find(bare->scope->name); if (found == bare->scope->members.end()) return; vector<Binding*> stale;
for (size_t i = 0; i < found->second.size(); ++i) if (implicit_generated_default_constructor(found->second[i])) stale.push_back(found->second[i]);
if (stale.empty()) return; generated_default_ctors_.erase(bare.get()); for (size_t s = 0; s < stale.size(); ++s) {
Binding* binding = stale[s]; if (binding != keep) {
found->second.erase(remove(found->second.begin(), found->second.end(), binding), found->second.end());
bare->scope->binding_order.erase(remove(bare->scope->binding_order.begin(), bare->scope->binding_order.end(), binding), bare->scope->binding_order.end()); }
if (function_bodies_.erase(binding) != 0) note_function_bodies_changed(); default_arguments_.erase(binding); function_parameter_names_.erase(binding); pending_function_bodies_.erase(binding);
deleted_functions_.erase(binding); bool removed_pending_member_body = false; for (map<Scope*, vector<PendingFunctionBody> >::iterator it = pending_member_bodies_.begin(); it != pending_member_bodies_.end(); ++it)
for (size_t i = 0; i < it->second.size(); ) { if (it->second[i].function == binding) { it->second.erase(it->second.begin() + i); removed_pending_member_body = true; } else ++i; } if (removed_pending_member_body) rebuild_pending_member_body_name_index();
for (size_t i = 0; i < generated_nodes_.size(); ) { if (generated_nodes_[i].binding == binding) generated_nodes_.erase(generated_nodes_.begin() + i); else ++i; }
for (size_t i = 0; i < extra_lowir_nodes_.size(); ) { if (extra_lowir_nodes_[i].binding == binding) extra_lowir_nodes_.erase(extra_lowir_nodes_.begin() + i); else ++i; } } }
void Parser::discard_implicit_default_destructor(TypePtr type, Binding* keep) { TypePtr bare = type.get() != NULL ? pa11::strip_cv(type) : TypePtr();
if (bare.get() == NULL || bare->kind != pa11::TypeKind::Record || bare->scope == NULL) return; string name = "~" + bare->scope->name; map<string, vector<Binding*> >::iterator found =
bare->scope->members.find(name); if (found == bare->scope->members.end()) return; vector<Binding*> stale;
for (size_t i = 0; i < found->second.size(); ++i) if (found->second[i] != keep && found->second[i]->is_generated_default_destructor) stale.push_back(found->second[i]);
if (stale.empty()) return; generated_dtors_.erase(bare.get()); active_generated_dtors_.erase(bare.get()); completed_generated_dtors_.erase(bare.get()); for (size_t s = 0; s < stale.size(); ++s) {
Binding* binding = stale[s]; found->second.erase(remove(found->second.begin(), found->second.end(), binding), found->second.end());
bare->scope->binding_order.erase(remove(bare->scope->binding_order.begin(), bare->scope->binding_order.end(), binding), bare->scope->binding_order.end());
if (function_bodies_.erase(binding) != 0) note_function_bodies_changed(); default_arguments_.erase(binding); function_parameter_names_.erase(binding); pending_function_bodies_.erase(binding);
deleted_functions_.erase(binding); bool removed_pending_member_body = false; for (map<Scope*, vector<PendingFunctionBody> >::iterator it = pending_member_bodies_.begin(); it != pending_member_bodies_.end(); ++it)
for (size_t i = 0; i < it->second.size(); ) { if (it->second[i].function == binding) { it->second.erase(it->second.begin() + i); removed_pending_member_body = true; } else ++i; } if (removed_pending_member_body) rebuild_pending_member_body_name_index();
for (size_t i = 0; i < generated_nodes_.size(); ) { if (generated_nodes_[i].binding == binding) generated_nodes_.erase(generated_nodes_.begin() + i); else ++i; }
for (size_t i = 0; i < extra_lowir_nodes_.size(); ) { if (extra_lowir_nodes_[i].binding == binding) extra_lowir_nodes_.erase(extra_lowir_nodes_.begin() + i); else ++i; } } }
Binding* Parser::find_default_constructor(TypePtr type) const { TypePtr bare = pa11::strip_cv(type); if (bare->kind != pa11::TypeKind::Record || bare->scope == NULL)
return NULL; map<string, vector<Binding*> >::iterator found = bare->scope->members.find(bare->scope->name); if (found == bare->scope->members.end())
return NULL; bool has_user_declared_constructor = record_has_user_declared_constructor(bare); for (size_t i = 0; i < found->second.size(); ++i) { Binding* binding = found->second[i];
if (has_user_declared_constructor && implicit_generated_default_constructor(binding)) continue;
if (binding->kind == BindingKind::Function && binding->type->kind == pa11::TypeKind::Function && binding->type->parameters.size() == 1) return binding;
if (binding->kind == BindingKind::Function && binding->type->kind == pa11::TypeKind::Function) { map<Binding*, vector<Expr> >::const_iterator defaults =
default_arguments_.find(binding); if (defaults == default_arguments_.end()) continue; bool have_defaults = true;
for (size_t j = 1; j < binding->type->parameters.size(); ++j) if (j >= defaults->second.size() || !defaults->second[j].valid) have_defaults = false; if (have_defaults)
	return binding; } } return NULL;
	}
bool Parser::default_constructor_is_nothrow(TypePtr type) { TypePtr bare = pa11::strip_cv(type);
if (bare->kind == pa11::TypeKind::Array) return default_constructor_is_nothrow(bare->base);
if (bare->kind != pa11::TypeKind::Record) return true; Binding* ctor = find_default_constructor(bare);
if (ctor == NULL) ctor = ensure_default_constructor(bare); if (ctor == NULL ||
deleted_functions_.find(ctor) != deleted_functions_.end()) return false;
if (!ctor->is_generated_default_constructor && !ctor->is_defaulted) return ctor->unwind_no;
pa11::layout_record_type(bare); vector<TypePtr> virtual_bases = pa11::record_virtual_bases(bare);
for (size_t i = 0; i < virtual_bases.size(); ++i) if (!default_constructor_is_nothrow(virtual_bases[i])) return false;
vector<TypePtr> direct_bases = pa11::record_direct_bases(bare);
for (size_t i = 0; i < direct_bases.size(); ++i) if (!pa11::record_direct_base_is_virtual(bare, i) &&
!default_constructor_is_nothrow(direct_bases[i])) return false;
vector<Binding*> data_members = default_constructor_data_members(bare);
for (size_t i = 0; i < data_members.size(); ++i) { Binding* field = data_members[i];
map<Binding*, Node>::const_iterator init = find_default_member_initializer(default_member_initializers_, field);
if (init != default_member_initializers_.end()) { if (!node_is_noexcept(init->second)) return false; }
else if (!default_constructor_is_nothrow(field->type)) return false; }
return true; }
Binding* Parser::ensure_default_constructor(TypePtr type, bool force_trivial) { TypePtr bare = pa11::strip_cv(type);
if (bare->kind != pa11::TypeKind::Record) return NULL; complete_template_record(bare); bool reemit_stale_generated_default = false;
	bool synthesize_defaulted_default = false;
	Binding* existing = find_default_constructor(bare); if (existing != NULL) { parse_pending_member_body(existing);
		bool have_extra_definition = false; for (size_t i = 0; i < extra_lowir_nodes_.size(); ++i) if (extra_lowir_nodes_[i].binding == existing) have_extra_definition = true;
			bool defaulted_default = existing->is_defaulted && existing->type.get() != NULL &&
				existing->type->kind == pa11::TypeKind::Function && existing->type->parameters.size() == 1;
			bool needs_synthetic_storage_body =
				default_constructor_needs_synthetic_storage_body(
				    bare,
				    existing,
				    defaulted_default,
				    default_member_initializers_);
				if (defaulted_default && existing->is_explicit_defaulted_definition &&
				    !needs_synthetic_storage_body) {
					existing->unwind_no = default_constructor_is_nothrow(bare);
					return existing;
				}
			if (needs_synthetic_storage_body)
				synthesize_defaulted_default = true;
	if (existing->is_generated_default_constructor && existing->is_inline_definition && !have_extra_definition && !bare->is_polymorphic) existing->is_inline_definition = false;
	bool stale_generated_default = !existing->is_inline_definition && existing->is_generated_default_constructor; if (!stale_generated_default)
	{ if (!synthesize_defaulted_default) return existing; } existing->is_generated_default_constructor = true; reemit_stale_generated_default = true; }
map<const void*, TemplateDeclaration*>::iterator template_decl = record_template_declarations_.find(bare.get()); if (template_decl != record_template_declarations_.end()) { map<pair<TemplateDeclaration*, string>, vector<TemplateDeclaration*> >::iterator member_templates =
member_function_templates_.find(make_pair(template_decl->second, bare->scope->name)); if (member_templates != member_function_templates_.end()) for (size_t i = 0; i < member_templates->second.size(); ++i)
if (member_templates->second[i]->constructor_template && !synthesize_defaulted_default) return NULL; }
	if (record_has_user_declared_constructor(bare) && !synthesize_defaulted_default) return NULL;
		TypePtr this_type = pa11::make_pointer(bare);
	Scope* generated_function_scope =
		pa11::create_child_scope(bare->scope, ScopeKind::Function, bare->scope->name);
	Binding* generated_this_binding =
		pa11::add_binding(generated_function_scope,
		                  BindingKind::Parameter,
		                  "this",
		                  this_type);
pa11::layout_record_type(bare); vector<Node> init_actions; vector<TypePtr> direct_bases = pa11::record_direct_bases(bare); vector<TypePtr> virtual_bases = pa11::record_virtual_bases(bare); vector<Binding*> data_members = default_constructor_data_members(bare); bool has_virtual_bases = !virtual_bases.empty(); bool forced_nontrivial = false; if (!force_trivial || !data_members.empty() || !direct_bases.empty()) {
for (size_t b = 0; b < virtual_bases.size(); ++b) { TypePtr virtual_base = virtual_bases[b].get() != NULL ? pa11::strip_cv(virtual_bases[b]) : TypePtr(); Binding* base_ctor = virtual_base.get() != NULL && virtual_base->kind == pa11::TypeKind::Record
? ensure_default_constructor(virtual_base) : NULL; if (virtual_base.get() != NULL && virtual_base->kind == pa11::TypeKind::Record && base_ctor != NULL) {
parse_pending_member_body(base_ctor);
refresh_noop_constructor_from_bodies(function_bodies_, base_ctor, function_bodies_generation_, noop_constructor_body_scan_misses_);
bool base_noop = base_ctor->is_noop_constructor;
if (base_noop && !base_ctor->is_generated_default_constructor && (base_ctor->is_private || base_ctor->is_protected_member))
forced_nontrivial = true;
if ((!base_noop || virtual_base->is_polymorphic || !pa11::record_virtual_bases(virtual_base).empty())) init_actions.push_back(make_base_init_action(virtual_base, NULL)); } }
for (size_t b = 0; b < direct_bases.size(); ++b) { if (pa11::record_direct_base_is_virtual(bare, b)) continue; TypePtr direct_base = direct_bases[b].get() != NULL ? pa11::strip_cv(direct_bases[b]) : TypePtr(); Binding* base_ctor = direct_base.get() != NULL && direct_base->kind == pa11::TypeKind::Record
? ensure_default_constructor(direct_base) : NULL; if (direct_base.get() != NULL && direct_base->kind == pa11::TypeKind::Record && base_ctor != NULL) {
parse_pending_member_body(base_ctor);
refresh_noop_constructor_from_bodies(function_bodies_, base_ctor, function_bodies_generation_, noop_constructor_body_scan_misses_);
bool base_noop = base_ctor->is_noop_constructor;
if (base_noop && !base_ctor->is_generated_default_constructor && (base_ctor->is_private || base_ctor->is_protected_member))
forced_nontrivial = true;
if ((!base_noop || direct_base->is_polymorphic || !pa11::record_virtual_bases(direct_base).empty())) init_actions.push_back(make_base_init_action(direct_base, NULL)); } } for (size_t i = 0; i < data_members.size(); ++i)
	{ Binding* field = data_members[i]; map<Binding*, Node>::const_iterator init = find_default_member_initializer(default_member_initializers_, field);
	if (init != default_member_initializers_.end()) init_actions.push_back(make_member_init_action(field, &init->second, generated_this_binding)); else {
TypePtr field_bare = pa11::strip_cv(field->type); Binding* field_ctor = ensure_default_constructor(field->type); Binding* elem_ctor = field_bare->kind == pa11::TypeKind::Array ? ensure_default_constructor(field_bare->base) : NULL;
if (field_ctor != NULL) parse_pending_member_body(field_ctor);
if (elem_ctor != NULL) parse_pending_member_body(elem_ctor);
refresh_noop_constructor_from_bodies(function_bodies_, field_ctor, function_bodies_generation_, noop_constructor_body_scan_misses_);
refresh_noop_constructor_from_bodies(function_bodies_, elem_ctor, function_bodies_generation_, noop_constructor_body_scan_misses_);
bool field_noop = field_ctor != NULL && field_ctor->is_noop_constructor; bool elem_noop = elem_ctor != NULL &&
elem_ctor->is_noop_constructor; if ((field_ctor != NULL && !field_noop) || (elem_ctor != NULL && !elem_noop))
	init_actions.push_back(make_member_init_action(field, NULL, generated_this_binding)); else if (field_ctor == NULL && elem_ctor == NULL && field_bare->kind == pa11::TypeKind::Record &&
field_bare->scope != NULL) { map<string, vector<Binding*> >::const_iterator ctors = field_bare->scope->members.find(field_bare->scope->name);
bool has_user_ctor = false; if (ctors != field_bare->scope->members.end()) for (size_t j = 0; j < ctors->second.size(); ++j) {
Binding* ctor = ctors->second[j]; if (ctor->kind == BindingKind::Function && !ctor->is_generated_default_constructor && !ctor->is_generated_aggregate_constructor &&
!ctor->is_generated_copy_move_constructor) has_user_ctor = true; } if (has_user_ctor)
throw runtime_error("member has no default constructor"); } } }
} bool has_declared_constructor = false; if (bare->scope != NULL) {
map<string, vector<Binding*> >::const_iterator ctors = bare->scope->members.find(bare->scope->name); if (ctors != bare->scope->members.end()) for (size_t i = 0; i < ctors->second.size(); ++i)
if (ctors->second[i]->kind == BindingKind::Function && !ctors->second[i]->is_generated_default_constructor && !ctors->second[i]->is_generated_aggregate_constructor && !ctors->second[i]->is_generated_copy_move_constructor)
has_declared_constructor = true; } bool empty_implicit_record = (bare->tag == "union" ||
	(data_members.empty() && direct_bases.empty())) && !has_declared_constructor; if (has_declared_constructor && !synthesize_defaulted_default) return NULL;
if (init_actions.empty() && !force_trivial && !empty_implicit_record && !bare->is_polymorphic && !has_virtual_bases && !synthesize_defaulted_default) { return NULL;
} const void* key = bare.get(); if (generated_default_ctors_.find(key) != generated_default_ctors_.end()) {
Binding* generated = find_default_constructor(bare); if (!(generated != NULL && generated->is_generated_default_constructor && !generated->is_inline_definition))
return generated; existing = generated; } generated_default_ctors_.insert(key);
	vector<TypePtr> params; params.push_back(this_type); TypePtr fn_type = pa11::make_function(pa11::make_fundamental(FT_VOID),
	params, false); Binding* ctor = existing != NULL ? existing
		: add_value(bare->scope, BindingKind::Function, bare->scope->name, fn_type); ctor->type = fn_type; ctor->is_inline_definition = true;
	if (bare->is_template_specialization)
		ctor->function_specialization_symbol =
			abi_binding_symbol(ctor, map<string, size_t>());
	if (synthesize_defaulted_default) {
	if (function_bodies_.erase(ctor) != 0) note_function_bodies_changed(); pending_function_bodies_.erase(ctor);
	for (size_t i = 0; i < generated_nodes_.size(); ) { if (generated_nodes_[i].binding == ctor) generated_nodes_.erase(generated_nodes_.begin() + i); else ++i; }
	for (size_t i = 0; i < extra_lowir_nodes_.size(); ) { if (extra_lowir_nodes_[i].binding == ctor) extra_lowir_nodes_.erase(extra_lowir_nodes_.begin() + i); else ++i; }
	}
if (reemit_stale_generated_default && init_actions.empty() && !synthesize_defaulted_default) ctor->is_inline_definition = false; ctor->is_generated_default_constructor = true; ctor->is_noop_constructor = init_actions.empty() && !bare->is_polymorphic && !has_virtual_bases;
ctor->unwind_no = !forced_nontrivial && default_constructor_is_nothrow(bare); Node fn("function-definition " + qualified_decl_name(ctor) + " " + pa11::describe_type(fn_type)); fn.binding = ctor;
	fn.type = fn_type; Node param("parameter this " + pa11::describe_type(this_type)); param.binding = generated_this_binding; param.type = this_type; add_child(fn, param);
Node body("compound-statement"); for (size_t i = 0; i < init_actions.size(); ++i) add_child(body, init_actions[i]); add_child(fn, body);
remember_function_body(ctor, fn); generated_nodes_.push_back(fn); extra_lowir_nodes_.push_back(fn); return ctor;
	}
Binding* Parser::ensure_aggregate_constructor(TypePtr type, size_t arg_count) { TypePtr bare = pa11::strip_cv(type);
if (bare->kind != pa11::TypeKind::Record || bare->scope == NULL || arg_count == 0) return NULL; Binding* reusable_aggregate = NULL; map<string, vector<Binding*> >::const_iterator existing =
bare->scope->members.find(bare->scope->name); if (existing != bare->scope->members.end()) { for (size_t i = 0; i < existing->second.size(); ++i)
{ Binding* binding = existing->second[i]; if (binding->kind == BindingKind::Function && binding->type->kind == pa11::TypeKind::Function &&
binding->type->parameters.size() == arg_count + 1) { if (!binding->is_generated_aggregate_constructor || function_bodies_.find(binding) != function_bodies_.end()) return binding; reusable_aggregate = binding; break; } } }
pa11::layout_record_type(bare); if (arg_count > bare->fields.size()) return NULL; pair<const void*, size_t> key(bare.get(), arg_count);
if (generated_aggregate_ctors_.find(key) != generated_aggregate_ctors_.end() && reusable_aggregate == NULL) { existing = bare->scope->members.find(bare->scope->name); if (existing != bare->scope->members.end())
for (size_t i = 0; i < existing->second.size(); ++i) if (existing->second[i]->kind == BindingKind::Function && existing->second[i]->type->parameters.size() == arg_count + 1 && (!existing->second[i]->is_generated_aggregate_constructor || function_bodies_.find(existing->second[i]) != function_bodies_.end())) return existing->second[i];
return NULL; } generated_aggregate_ctors_.insert(key); if (arg_count > 0)
ensure_default_constructor(bare); TypePtr this_type = pa11::make_pointer(bare); vector<TypePtr> params; vector<string> names;
params.push_back(this_type); names.push_back("this"); for (size_t i = 0; i < arg_count; ++i) {
params.push_back(bare->fields[i]->type); names.push_back(bare->fields[i]->name.empty() ? "__param" + to_string(i + 1) : bare->fields[i]->name);
} TypePtr fn_type = pa11::make_function(pa11::make_fundamental(FT_VOID), params, false);
Binding* ctor = reusable_aggregate != NULL ? reusable_aggregate : add_value(bare->scope, BindingKind::Function, bare->scope->name, fn_type); ctor->type = fn_type; ctor->is_inline_definition = true; ctor->is_generated_aggregate_constructor = true;
ctor->unwind_no = true; function_parameter_names_[ctor] = names; ctor->function_parameter_names = names; Node fn("function-definition " + qualified_decl_name(ctor) + " " + pa11::describe_type(fn_type));
fn.binding = ctor; fn.type = fn_type; Scope* function_scope = pa11::create_child_scope(bare->scope, ScopeKind::Function, ctor->name);
Binding* this_binding = pa11::add_binding(function_scope, BindingKind::Parameter, "this",
this_type); Node this_node("parameter this " + pa11::describe_type(this_type)); this_node.binding = this_binding; this_node.type = this_type;
add_child(fn, this_node); Node body("compound-statement"); for (size_t i = 0; i < arg_count; ++i) {
Binding* param_binding = pa11::add_binding(function_scope, BindingKind::Parameter, names[i + 1],
params[i + 1]); Node param("parameter " + names[i + 1] + " " + pa11::describe_type(params[i + 1])); param.binding = param_binding;
param.type = params[i + 1]; add_child(fn, param); Node arg("id-expression lvalue " + pa11::describe_type(params[i + 1]) + " " + names[i + 1]);
arg.binding = param_binding; arg.type = params[i + 1]; arg.category = ValueCategory::LValue; add_child(body, make_member_init_action(bare->fields[i], &arg));
} for (size_t i = arg_count; i < bare->fields.size(); ++i) { Binding* field = bare->fields[i];
TypePtr field_bare = pa11::strip_cv(field->type); if (field_bare->kind == pa11::TypeKind::Record || field_bare->kind == pa11::TypeKind::Array) {
Node init = empty_braced_value_node(field->type); add_child(body, make_member_init_action(field, &init)); } else
{ Node init = zero_value_node(field->type); add_child(body, make_member_init_action(field, &init)); }
} add_child(fn, body); remember_function_body(ctor, fn); extra_lowir_nodes_.push_back(fn);
return ctor; } bool Parser::aggregate_omitted_field_requires_argument(TypePtr type) {
TypePtr bare = pa11::strip_cv(type); if (bare->kind != pa11::TypeKind::Record) return false; Binding* ctor = ensure_default_constructor(type);
if (ctor == NULL) return false; Binding* dtor = ensure_default_destructor(type); if (dtor != NULL &&
!(dtor->is_generated_default_destructor && dtor->is_noop_destructor && dtor->unwind_no)) return false;
return !(ctor->is_generated_default_constructor && ctor->is_noop_constructor && ctor->unwind_no); }
void Parser::complete_aggregate_constructor_args(TypePtr type,
                                                 vector<Expr>& args)
{
	TypePtr bare = pa11::strip_cv(type);
	if (bare->kind != pa11::TypeKind::Record ||
	    bare->scope == NULL ||
	    record_has_aggregate_blocking_constructor(bare))
		return;
	try
	{
		pa11::layout_record_type(bare);
	}
	catch (const runtime_error& err)
	{
		if (string(err.what()) != "incomplete class type" &&
		    string(err.what()) != "incomplete object type")
			throw;
		return;
	}
	if (args.size() >= bare->fields.size())
		return;
	size_t effective_count = args.size();
	for (size_t i = args.size(); i < bare->fields.size(); ++i)
		if (aggregate_omitted_field_requires_argument(bare->fields[i]->type))
			effective_count = i + 1;
	for (size_t i = args.size(); i < effective_count; ++i)
	{
		TypePtr field_type = bare->fields[i]->type;
		TypePtr field_bare = pa11::strip_cv(field_type);
		if (field_bare->kind == pa11::TypeKind::Record)
		{
			vector<Expr> empty_args;
			args.push_back(make_constructor_init_expr(field_type,
			                                         empty_args,
			                                         false));
			continue;
		}
		Expr zero;
		zero.valid = true;
		zero.type = pa11::strip_top_level_cv(field_type);
		zero.category = ValueCategory::PRValue;
		zero.constant_expression = true;
		zero.has_constant_value = true;
		zero.constant_value = 0;
		zero.node = zero_value_node(field_type);
		annotate_expr_node(zero);
		args.push_back(zero);
	}
}

namespace {
bool constructor_trailing_parameters_have_defaults( Binding* binding,
const map<Binding*, vector<Expr> >* default_arguments) { if (binding->type->parameters.size() <= 2) return true;
if (default_arguments == NULL) return false; map<Binding*, vector<Expr> >::const_iterator found = default_arguments->find(binding);
if (found == default_arguments->end()) return false; for (size_t i = 2; i < binding->type->parameters.size(); ++i) if (i >= found->second.size() || !found->second[i].valid)
return false; return true; } bool type_contains_template_parameter(TypePtr type)
{ TypePtr bare = type.get() != NULL ? pa11::strip_cv(type) : TypePtr(); if (bare.get() == NULL) return false;
if (bare->kind == pa11::TypeKind::TemplateParameter || bare->kind == pa11::TypeKind::TemplateTemplateParameter || bare->is_dependent_typename)
return true; if (bare->kind == pa11::TypeKind::Pointer || bare->kind == pa11::TypeKind::LValueReference || bare->kind == pa11::TypeKind::RValueReference ||
bare->kind == pa11::TypeKind::Array) return type_contains_template_parameter(bare->base);
if (bare->kind == pa11::TypeKind::MemberPointer) return type_contains_template_parameter(bare->member_class) || type_contains_template_parameter(bare->base);
if (bare->kind == pa11::TypeKind::Function) { if (type_contains_template_parameter(bare->base)) return true; for (size_t i = 0; i < bare->parameters.size(); ++i)
if (type_contains_template_parameter(bare->parameters[i])) return true; }
if (bare->kind == pa11::TypeKind::Record && bare->is_template_specialization) for (size_t i = 0; i < bare->template_arguments.size(); ++i) {
const pa11::TemplateInstanceArgument& arg = bare->template_arguments[i]; if (arg.kind == pa11::TemplateInstanceArgumentKind::Type &&
type_contains_template_parameter(arg.type)) return true; if (arg.kind == pa11::TemplateInstanceArgumentKind::Pack) for (size_t j = 0; j < arg.pack.size(); ++j)
if (arg.pack[j].kind == pa11::TemplateInstanceArgumentKind::Type && type_contains_template_parameter(arg.pack[j].type)) return true; }
return false; } bool function_template_specialization_binding(const Binding* binding,
const map<Binding*, TemplateDeclaration*>* placeholders = NULL,
const map<Binding*, vector<TemplateArgument> >* specializations = NULL)
{ if (binding == NULL) return false; Binding* mutable_binding = const_cast<Binding*>(binding);
if ((placeholders != NULL && placeholders->find(mutable_binding) != placeholders->end()) ||
    (specializations != NULL && specializations->find(mutable_binding) != specializations->end()))
	return true;
string symbol = binding->function_specialization_symbol;
if (symbol.find("C1I") != string::npos ||
    symbol.find("C2I") != string::npos)
	return true;
if (binding->aliased_binding == NULL) return false; Binding* alias = binding->aliased_binding;
if ((placeholders != NULL && placeholders->find(alias) != placeholders->end()) ||
    (specializations != NULL && specializations->find(alias) != specializations->end()))
	return true;
symbol = alias->function_specialization_symbol;
return symbol.find("C1I") != string::npos ||
       symbol.find("C2I") != string::npos; }
Binding* find_copy_move_constructor_binding(
TypePtr type, bool move, const map<Binding*, vector<Expr> >* default_arguments = NULL,
const map<Binding*, TemplateDeclaration*>* placeholders = NULL,
const map<Binding*, vector<TemplateArgument> >* specializations = NULL) {
TypePtr bare = pa11::strip_cv(type); if (bare->kind != pa11::TypeKind::Record || bare->scope == NULL) return NULL; map<string, vector<Binding*> >::const_iterator found =
bare->scope->members.find(bare->scope->name); if (found == bare->scope->members.end()) return NULL; for (size_t i = 0; i < found->second.size(); ++i)
{ Binding* binding = found->second[i]; if (binding->kind != BindingKind::Function || binding->type->kind != pa11::TypeKind::Function ||
binding->type->parameters.size() < 2 || !pa11::is_reference_type(binding->type->parameters[1]) ||
function_template_specialization_binding(binding, placeholders, specializations)) continue; if (!constructor_trailing_parameters_have_defaults(binding,
default_arguments)) continue; TypePtr param = binding->type->parameters[1]; if (move && param->kind != pa11::TypeKind::RValueReference)
continue; if (!move && param->kind != pa11::TypeKind::LValueReference) continue; if (pa11::same_type(pa11::strip_cv(param->base), bare))
return binding; } return NULL; }
bool is_copy_move_assignment_for_record(Binding* binding, TypePtr record) { if (binding->kind != BindingKind::Function || binding->name != "operator=" ||
binding->type->kind != pa11::TypeKind::Function || binding->type->parameters.size() != 2) return false;
TypePtr param = binding->type->parameters[1]; TypePtr param_object = pa11::is_reference_type(param) ? param->base : param; return pa11::same_type(pa11::strip_cv(param_object), pa11::strip_cv(record));
} Binding* find_copy_move_assignment_binding(TypePtr type, bool move) { TypePtr bare = pa11::strip_cv(type);
if (bare->kind != pa11::TypeKind::Record || bare->scope == NULL) return NULL; map<string, vector<Binding*> >::const_iterator found = bare->scope->members.find("operator=");
if (found == bare->scope->members.end()) return NULL;
for (size_t i = 0; i < found->second.size(); ++i) {
Binding* binding = found->second[i]; if (binding->kind == BindingKind::Function && binding->name == "operator=" && binding->owner == bare->scope &&
binding->type->kind == pa11::TypeKind::Function && binding->type->parameters.size() == 1) { TypePtr param = binding->type->parameters[0];
TypePtr param_object = pa11::is_reference_type(param) ? param->base : param; if (pa11::same_type(pa11::strip_cv(param_object), bare)) {
vector<TypePtr> params; params.push_back(pa11::make_pointer(bare)); params.push_back(param); binding->type =
pa11::make_function(binding->type->base, params, binding->type->variadic); binding->is_static_member = false;
} } if (!is_copy_move_assignment_for_record(binding, bare)) continue;
TypePtr param = binding->type->parameters[1]; if (move && param->kind == pa11::TypeKind::RValueReference) return binding; if (!move && param->kind != pa11::TypeKind::RValueReference)
return binding; } return NULL; }
bool suppresses_implicit_move( TypePtr type, const map<Binding*, vector<Expr> >* default_arguments,
const map<Binding*, TemplateDeclaration*>* placeholders = NULL,
const map<Binding*, vector<TemplateArgument> >* specializations = NULL) {
TypePtr bare = pa11::strip_cv(type); if (bare->kind != pa11::TypeKind::Record || bare->scope == NULL) return false; map<string, vector<Binding*> >::const_iterator ctors =
bare->scope->members.find(bare->scope->name); if (ctors != bare->scope->members.end()) for (size_t i = 0; i < ctors->second.size(); ++i) if (!ctors->second[i]->is_generated_copy_move_constructor &&
(find_copy_move_constructor_binding( bare, false, default_arguments, placeholders, specializations) == ctors->second[i] ||
 find_copy_move_constructor_binding( bare, true, default_arguments, placeholders, specializations) == ctors->second[i]))
return true; map<string, vector<Binding*> >::const_iterator dtors = bare->scope->members.find("~" + bare->scope->name); if (dtors != bare->scope->members.end())
for (size_t i = 0; i < dtors->second.size(); ++i) if (dtors->second[i]->kind == BindingKind::Function) { if (!dtors->second[i]->is_generated_default_destructor)
return true; } map<string, vector<Binding*> >::const_iterator assigns = bare->scope->members.find("operator=");
if (assigns != bare->scope->members.end()) for (size_t i = 0; i < assigns->second.size(); ++i) if (!assigns->second[i]->is_generated_copy_move_assignment && is_copy_move_assignment_for_record(assigns->second[i], bare))
return true; return false; } bool type_needs_copy_move_helper(
TypePtr type, bool move, const map<Binding*, vector<Expr> >* default_arguments);
bool type_has_nontrivial_value_transfer(
	TypePtr type, const map<Binding*, vector<Expr> >* default_arguments);
bool is_copy_or_move_constructor_for_record(Binding* binding, TypePtr record)
{ if (binding == NULL || binding->kind != BindingKind::Function || binding->type.get() == NULL ||
binding->type->kind != pa11::TypeKind::Function || binding->type->parameters.size() < 2 ||
!pa11::is_reference_type(binding->type->parameters[1]) || function_template_specialization_binding(binding)) return false;
TypePtr param_record = pa11::strip_cv(binding->type->parameters[1]->base);
TypePtr target_record = pa11::strip_cv(record);
return param_record->kind == pa11::TypeKind::Record && pa11::same_type(param_record, target_record);
}
bool is_move_constructor_for_record(Binding* binding, TypePtr record)
{ return is_copy_or_move_constructor_for_record(binding, record) &&
binding->type->parameters[1]->kind == pa11::TypeKind::RValueReference; }
bool type_has_abi_indirect_special_member(
	TypePtr type, const map<Binding*, vector<Expr> >* default_arguments);
bool defaulted_special_member_needs_value_transfer_helper(
	Binding* binding, const map<Binding*, vector<Expr> >* default_arguments)
{ if (binding == NULL || binding->owner == NULL || binding->owner->kind != ScopeKind::Class)
return binding != NULL && binding->is_inline_definition; TypePtr record =
pa11::record_type_for_scope(binding->owner); if (record.get() == NULL)
return binding->is_inline_definition; TypePtr bare = pa11::strip_cv(record);
if (bare->tag == "union") return true; pa11::layout_record_type(bare);
vector<TypePtr> bases = pa11::record_direct_bases(bare); for (size_t i = 0; i < bases.size(); ++i)
if (type_has_abi_indirect_special_member(bases[i], default_arguments) ||
    type_has_nontrivial_value_transfer(bases[i], default_arguments)) return true;
for (size_t i = 0; i < bare->fields.size(); ++i)
if (type_has_abi_indirect_special_member(bare->fields[i]->type, default_arguments) ||
    type_has_nontrivial_value_transfer(bare->fields[i]->type, default_arguments)) return true;
return false; }
bool special_member_needs_value_transfer_helper(
	Binding* binding, const map<Binding*, vector<Expr> >* default_arguments)
{ if (binding == NULL) return false; if (binding->is_generated_default_destructor)
return false; if (binding->is_generated_copy_move_constructor)
return defaulted_special_member_needs_value_transfer_helper(binding, default_arguments); if (!binding->is_defaulted)
return true; return defaulted_special_member_needs_value_transfer_helper(binding, default_arguments);
}
bool record_has_abi_indirect_special_member(
	TypePtr type, const map<Binding*, vector<Expr> >* default_arguments)
{ TypePtr bare = pa11::strip_cv(type); if (bare->kind != pa11::TypeKind::Record || bare->scope == NULL)
return false; if (bare->tag == "union") return true; pa11::layout_record_type(bare);
map<string, vector<Binding*> >::const_iterator ctors = bare->scope->members.find(bare->scope->name);
if (ctors != bare->scope->members.end()) for (size_t i = 0; i < ctors->second.size(); ++i)
{ Binding* ctor = ctors->second[i]; if ((is_move_constructor_for_record(ctor, bare) ||
(bare->is_template_specialization && is_copy_or_move_constructor_for_record(ctor, bare))) &&
special_member_needs_value_transfer_helper(ctor, default_arguments)) return true; }
string dtor_name = "~" + bare->scope->name; map<string, vector<Binding*> >::const_iterator dtors =
bare->scope->members.find(dtor_name); if (dtors != bare->scope->members.end())
for (size_t i = 0; i < dtors->second.size(); ++i)
if (dtors->second[i]->kind == BindingKind::Function &&
special_member_needs_value_transfer_helper(dtors->second[i], default_arguments)) return true;
vector<TypePtr> bases = pa11::record_direct_bases(bare); for (size_t i = 0; i < bases.size(); ++i)
if (type_has_abi_indirect_special_member(bases[i], default_arguments)) return true;
for (size_t i = 0; i < bare->fields.size(); ++i)
if (type_has_abi_indirect_special_member(bare->fields[i]->type, default_arguments)) return true;
return false; }
bool type_has_abi_indirect_special_member(
	TypePtr type, const map<Binding*, vector<Expr> >* default_arguments)
{ TypePtr bare = pa11::strip_cv(type); if (bare->kind == pa11::TypeKind::Array)
return type_has_abi_indirect_special_member(bare->base, default_arguments);
if (bare->kind != pa11::TypeKind::Record) return false;
return record_has_abi_indirect_special_member(bare, default_arguments); }
bool record_has_nontrivial_value_transfer(
	TypePtr type, const map<Binding*, vector<Expr> >* default_arguments)
{ TypePtr bare = pa11::strip_cv(type); if (bare->kind != pa11::TypeKind::Record || bare->scope == NULL)
return false; if (bare->tag == "union") return true; pa11::layout_record_type(bare);
map<string, vector<Binding*> >::const_iterator ctors = bare->scope->members.find(bare->scope->name);
if (ctors != bare->scope->members.end()) for (size_t i = 0; i < ctors->second.size(); ++i)
{ Binding* ctor = ctors->second[i]; if (bare->is_template_specialization && ctor->is_defaulted &&
!ctor->is_generated_copy_move_constructor && is_move_constructor_for_record(ctor, bare) &&
(!pa11::record_direct_bases(bare).empty() || !bare->fields.empty())) return true;
if (is_copy_or_move_constructor_for_record(ctor, bare) &&
special_member_needs_value_transfer_helper(ctor, default_arguments)) return true; }
string dtor_name = "~" + bare->scope->name; map<string, vector<Binding*> >::const_iterator dtors =
bare->scope->members.find(dtor_name); if (dtors != bare->scope->members.end())
for (size_t i = 0; i < dtors->second.size(); ++i)
if (dtors->second[i]->kind == BindingKind::Function &&
special_member_needs_value_transfer_helper(dtors->second[i], default_arguments)) return true;
vector<TypePtr> bases = pa11::record_direct_bases(bare); for (size_t i = 0; i < bases.size(); ++i)
if (type_has_nontrivial_value_transfer(bases[i], default_arguments)) return true;
for (size_t i = 0; i < bare->fields.size(); ++i)
if (type_has_nontrivial_value_transfer(bare->fields[i]->type, default_arguments)) return true;
return false; }
bool type_has_nontrivial_value_transfer(
	TypePtr type, const map<Binding*, vector<Expr> >* default_arguments)
{ TypePtr bare = pa11::strip_cv(type); if (bare->kind == pa11::TypeKind::Array)
return type_has_nontrivial_value_transfer(bare->base, default_arguments);
if (bare->kind != pa11::TypeKind::Record) return false;
return record_has_nontrivial_value_transfer(bare, default_arguments); }
bool constructor_binding_needs_helper(Binding* binding)
{ return binding != NULL && !binding->is_defaulted && !binding->is_generated_copy_move_constructor;
} bool record_needs_copy_move_helper( TypePtr type, bool move,
	const map<Binding*, vector<Expr> >* default_arguments) { TypePtr bare = pa11::strip_cv(type); Binding* exact =
	find_copy_move_constructor_binding(bare, move, default_arguments); if (constructor_binding_needs_helper(exact)) return true; if (move &&
	constructor_binding_needs_helper( find_copy_move_constructor_binding( bare, false, default_arguments))) return true;
	if (record_has_nontrivial_value_transfer(bare, default_arguments)) return true;
	if (bare->is_polymorphic) return true;
	pa11::layout_record_type(bare); if (!pa11::record_virtual_bases(bare).empty()) return true; { vector<TypePtr> bases = pa11::record_direct_bases(bare); for (size_t b = 0; b < bases.size(); ++b) if (type_needs_copy_move_helper(bases[b], move, default_arguments)) return true; }
for (size_t i = 0; i < bare->fields.size(); ++i) { if (bare->fields[i]->is_bit_field) continue;
if (type_needs_copy_move_helper( bare->fields[i]->type, move, default_arguments)) return true; }
return false; } bool type_needs_copy_move_helper( TypePtr type,
bool move, const map<Binding*, vector<Expr> >* default_arguments) { TypePtr bare = pa11::strip_cv(type);
if (bare->kind == pa11::TypeKind::Array) return type_needs_copy_move_helper( bare->base, move, default_arguments); if (bare->kind != pa11::TypeKind::Record || bare->scope == NULL)
return false; return record_needs_copy_move_helper(bare, move, default_arguments); } bool type_needs_copy_move_assignment_helper(TypePtr type, bool move);
bool assignment_binding_needs_helper(Binding* binding) { return binding != NULL && !binding->is_generated_copy_move_assignment; }
vector<Binding*> assignment_dependency_members(TypePtr type)
{ vector<Binding*> members; TypePtr bare = type.get() != NULL ? pa11::strip_cv(type) : TypePtr();
if (bare.get() == NULL || bare->kind != pa11::TypeKind::Record) return members; pa11::layout_record_type(bare); members = bare->fields;
if (bare->scope == NULL) return members; for (size_t i = 0; i < bare->scope->binding_order.size(); ++i) { Binding* member = bare->scope->binding_order[i];
if (member == NULL || member->kind != BindingKind::Variable || member->owner != bare->scope || member->is_static_member || member->aliased_binding != NULL) continue; bool duplicate = false;
	for (size_t j = 0; j < members.size(); ++j) if (members[j] == member || (members[j] != NULL && members[j]->owner == member->owner && members[j]->name == member->name)) duplicate = true; if (!duplicate) members.push_back(member); }
return members; }
bool record_needs_copy_move_assignment_helper(TypePtr type, bool move) { TypePtr bare = pa11::strip_cv(type); Binding* exact = find_copy_move_assignment_binding(bare, move);
if (assignment_binding_needs_helper(exact)) return true; if (move && assignment_binding_needs_helper(
find_copy_move_assignment_binding(bare, false))) return true; pa11::layout_record_type(bare); { vector<TypePtr> bases = pa11::record_direct_bases(bare); for (size_t b = 0; b < bases.size(); ++b) if (type_needs_copy_move_assignment_helper(bases[b], move)) return true; } vector<Binding*> members = assignment_dependency_members(bare); for (size_t i = 0; i < members.size(); ++i) {
if (members[i]->is_bit_field) continue; if (type_needs_copy_move_assignment_helper(members[i]->type, move)) return true;
} return false; } bool type_needs_copy_move_assignment_helper(TypePtr type, bool move)
{ TypePtr bare = pa11::strip_cv(type); if (bare->kind == pa11::TypeKind::Array) return type_needs_copy_move_assignment_helper(bare->base, move);
if (bare->kind != pa11::TypeKind::Record || bare->scope == NULL) return false; return record_needs_copy_move_assignment_helper(bare, move); }
bool type_has_empty_record_assignment_subobject(TypePtr type)
{ TypePtr bare = pa11::strip_cv(type); if (bare->kind == pa11::TypeKind::Array) return type_has_empty_record_assignment_subobject(bare->base);
if (bare->kind != pa11::TypeKind::Record || bare->scope == NULL) return false; pa11::layout_record_type(bare); return bare->fields.empty() && pa11::record_direct_bases(bare).empty(); }
bool generated_field_needs_assignment_statement(TypePtr type, bool move, bool field_needs_helper, Binding* field_assignment)
{ bool needs = field_needs_helper || (field_assignment != NULL && !field_assignment->is_generated_copy_move_assignment) || type_has_empty_record_assignment_subobject(type);
TypePtr bare = pa11::strip_cv(type); if (bare->kind == pa11::TypeKind::Array && !type_needs_copy_move_assignment_helper(bare->base, move) && !type_has_empty_record_assignment_subobject(bare->base))
needs = false; return needs; }
Node make_parameter_lvalue(Binding* binding, TypePtr expr_type) { Node node("id-expression lvalue " + pa11::describe_type(expr_type) + " " + binding->name);
node.binding = binding; node.type = expr_type; node.category = ValueCategory::LValue; return node;
} Node make_this_pointer_node(Binding* binding, TypePtr type) { Node node("id-expression prvalue " + pa11::describe_type(type) +
" this"); node.binding = binding; node.type = type; node.category = ValueCategory::PRValue;
return node; } Node make_deref_node(TypePtr type, const Node& inner) {
Node node("unary-expression lvalue " + pa11::describe_type(type) + " OP_STAR:*"); node.type = type; node.category = ValueCategory::LValue;
node.has_op = true; node.op = OP_STAR; node.token_text = "*"; add_child(node, inner);
return node; } Expr expr_from_node(const Node& node) {
Expr expr; expr.valid = true; expr.node = node; expr.type = node.type;
expr.category = node.category; expr.binding = node.binding;
expr.overloads = node.overloads; expr.explicit_template_arguments = node.explicit_template_arguments; return expr; }
Expr target_field_expr(Binding* field, const Node& object) { Node member("member-expression lvalue " + pa11::describe_type(field->type) + " " + field->name);
member.binding = field; member.type = field->type; member.category = ValueCategory::LValue; add_child(member, object);
return expr_from_node(member); } Expr target_base_expr(TypePtr base, const Node& object) {
TypePtr bare = pa11::strip_cv(base); Node node("base-subobject-expression lvalue " + pa11::describe_type(bare)); node.type = bare;
node.category = ValueCategory::LValue; add_child(node, object); return expr_from_node(node); }
Node make_move_cast(TypePtr type, const Node& inner) { Node node("cast-expression xvalue " + pa11::describe_type(type)); node.type = type;
node.category = ValueCategory::XValue; add_child(node, inner); return node; }
Node source_field_expr(Binding* field, const Node& object, bool move) { Node member("member-expression lvalue " + pa11::describe_type(field->type) + " OP_DOT:" + field->name);
member.binding = field; member.type = field->type; member.category = ValueCategory::LValue; member.has_op = true;
member.op = OP_DOT; member.token_text = field->name; add_child(member, object); if (move)
return make_move_cast(field->type, member); return member; } Node source_base_expr(TypePtr base, const Node& object, bool move)
{ TypePtr bare = pa11::strip_cv(base); Node node("base-subobject-expression lvalue " + pa11::describe_type(bare));
node.type = bare; node.category = ValueCategory::LValue; add_child(node, object); if (move)
return make_move_cast(bare, node); return node; }
}  // namespace
bool Parser::copy_move_constructor_is_nothrow(TypePtr type, bool move) { TypePtr bare = pa11::strip_cv(type);
if (bare->kind == pa11::TypeKind::Array) return copy_move_constructor_is_nothrow(bare->base, move);
if (bare->kind != pa11::TypeKind::Record) return true; bool effective_move = move;
Binding* ctor = find_copy_move_constructor_binding(bare, effective_move, &default_arguments_, &function_template_placeholders_, &function_template_specialization_arguments_);
if (ctor == NULL) ctor = ensure_copy_move_constructor(bare, effective_move); if (ctor == NULL && effective_move) {
effective_move = false; ctor = find_copy_move_constructor_binding(bare, false, &default_arguments_, &function_template_placeholders_, &function_template_specialization_arguments_);
if (ctor == NULL) ctor = ensure_copy_move_constructor(bare, false); }
if (ctor == NULL || deleted_functions_.find(ctor) != deleted_functions_.end()) return false;
if (!ctor->is_generated_copy_move_constructor && !ctor->is_defaulted) return ctor->unwind_no;
pa11::layout_record_type(bare); vector<TypePtr> direct_bases = pa11::record_direct_bases(bare);
for (size_t i = 0; i < direct_bases.size(); ++i) if (!copy_move_constructor_is_nothrow(direct_bases[i], effective_move)) return false;
for (size_t i = 0; i < bare->fields.size(); ++i) if (!copy_move_constructor_is_nothrow(bare->fields[i]->type, effective_move)) return false;
return true; }
bool Parser::copy_move_constructor_available(TypePtr type, bool move) { TypePtr bare = pa11::strip_cv(type); if (bare->kind == pa11::TypeKind::Array)
return copy_move_constructor_available(bare->base, move); if (bare->kind != pa11::TypeKind::Record) return true; Binding* exact =
find_copy_move_constructor_binding(bare, move, &default_arguments_, &function_template_placeholders_, &function_template_specialization_arguments_); if (exact != NULL) { if (exact->is_defaulted)
ensure_copy_move_constructor(bare, move); return deleted_functions_.find(exact) == deleted_functions_.end(); } if (move)
{ Binding* copy = find_copy_move_constructor_binding( bare, false, &default_arguments_, &function_template_placeholders_, &function_template_specialization_arguments_);
if (copy != NULL) return deleted_functions_.find(copy) == deleted_functions_.end(); if (suppresses_implicit_move(bare, &default_arguments_, &function_template_placeholders_, &function_template_specialization_arguments_)) return false;
} if (!record_needs_copy_move_helper(bare, move, &default_arguments_)) return true; Binding* generated = ensure_copy_move_constructor(bare, move);
return generated != NULL && deleted_functions_.find(generated) == deleted_functions_.end(); } Binding* Parser::ensure_copy_move_constructor(TypePtr type, bool move)
{ TypePtr bare = pa11::strip_cv(type); if (bare->kind != pa11::TypeKind::Record || bare->scope == NULL) return NULL;
Binding* existing = find_copy_move_constructor_binding(bare, move, &default_arguments_, &function_template_placeholders_, &function_template_specialization_arguments_); if (existing == NULL && move &&
suppresses_implicit_move(bare, &default_arguments_, &function_template_placeholders_, &function_template_specialization_arguments_)) return NULL; TypePtr source_record = move ? bare : pa11::make_cv(bare, pa11::CV_CONST); TypePtr source_ref = move
? pa11::make_rvalue_reference(bare) : pa11::make_lvalue_reference(source_record); TypePtr this_type = pa11::make_pointer(bare); vector<TypePtr> params;
params.push_back(this_type); params.push_back(source_ref); TypePtr fn_type = pa11::make_function(pa11::make_fundamental(FT_VOID), params,
false); set<const void*>& generated = move ? generated_move_ctors_ : generated_copy_ctors_; const void* key = bare.get(); Binding* ctor = existing;
if (ctor == NULL) { ctor = add_value(bare->scope, BindingKind::Function, bare->scope->name, fn_type);
ctor->is_generated_copy_move_constructor = true; ctor->is_defaulted = true; ctor->is_inline_definition = true; ctor->type = fn_type;
function_parameter_names_[ctor] = vector<string>(2, "this"); function_parameter_names_[ctor][1] = "other"; } try
	{ pa11::layout_record_type(bare); } catch (const runtime_error& err)
	{ if ((string(err.what()) != "incomplete class type" && string(err.what()) != "incomplete object type") || active_class_instantiations_.empty())
	throw; return ctor; } if (generated.find(key) != generated.end()) { Binding* found =
	find_copy_move_constructor_binding( bare, move, &default_arguments_, &function_template_placeholders_, &function_template_specialization_arguments_);
	return found != NULL ? found : ctor; } bool needs_helper =
	record_needs_copy_move_helper(bare, move, &default_arguments_); bool defaulted_storage_copy = type_contains_enum(bare);
bool defaulted_reference_copy =
	existing != NULL && existing->is_defaulted &&
	record_has_reference_field(bare);
if (existing != NULL && !existing->is_generated_copy_move_constructor &&
(!existing->is_defaulted ||
 (!needs_helper && !defaulted_storage_copy && !defaulted_reference_copy))) { if (existing->is_defaulted)
existing->unwind_no = copy_move_constructor_is_nothrow(bare, move); return existing; } if (!needs_helper && !defaulted_storage_copy && !defaulted_reference_copy) {
ctor->unwind_no = copy_move_constructor_is_nothrow(bare, move); return ctor; }
if (generated.find(key) != generated.end()) { Binding* found = find_copy_move_constructor_binding( bare, move, &default_arguments_, &function_template_placeholders_, &function_template_specialization_arguments_);
if (found != NULL) found->unwind_no = copy_move_constructor_is_nothrow(bare, move); return found; } generated.insert(key);
bool deleted = false; vector<Node> init_actions; vector<TypePtr> direct_bases = pa11::record_direct_bases(bare);
ctor->is_inline_definition = true; ctor->type = fn_type; string other_name = "other"; if (existing != NULL)
{ map<Binding*, vector<string> >::const_iterator names = function_parameter_names_.find(existing); if (names != function_parameter_names_.end() &&
names->second.size() > 1 && !names->second[1].empty()) other_name = names->second[1]; else if (existing->is_defaulted)
other_name = "__param1"; } function_parameter_names_[ctor] = vector<string>(2, "this"); function_parameter_names_[ctor][1] = other_name;
Scope* function_scope = pa11::create_child_scope(bare->scope, ScopeKind::Function, ctor->name); Binding* this_binding = pa11::add_binding(function_scope,
BindingKind::Parameter, "this", this_type); Binding* other_binding =
pa11::add_binding(function_scope, BindingKind::Parameter, other_name, source_ref);
Node other = make_parameter_lvalue(other_binding, source_record); uint64_t copied_prefix = 0; bool copy_remaining_fields =
!direct_bases.empty() || bare->is_polymorphic || !pa11::record_virtual_bases(bare).empty();
function<void(TypePtr)> materialize_copy_move_body = [&](TypePtr subobject) {
	TypePtr sub_record = subobject.get() != NULL
		? pa11::strip_cv(subobject) : TypePtr();
	if (sub_record.get() == NULL ||
	    sub_record->kind != pa11::TypeKind::Record ||
	    sub_record->scope == NULL)
		return;
	Binding* sub_ctor = ensure_copy_move_constructor(sub_record, move);
	if (sub_ctor == NULL && move)
		sub_ctor = ensure_copy_move_constructor(sub_record, false);
	if (sub_ctor == NULL || !sub_ctor->is_inline_definition)
		return;
	parse_pending_function_body(sub_ctor);
	parse_pending_member_body(sub_ctor);
	ensure_function_body_extra_node(sub_ctor);
	if (sub_ctor->aliased_binding != NULL)
	{
		parse_pending_function_body(sub_ctor->aliased_binding);
		parse_pending_member_body(sub_ctor->aliased_binding);
		ensure_function_body_extra_node(sub_ctor->aliased_binding);
	}
};
if (!direct_bases.empty()) {
for (size_t b = 0; b < direct_bases.size(); ++b) { TypePtr direct_base = direct_bases[b].get() != NULL ? pa11::strip_cv(direct_bases[b]) : TypePtr(); if (direct_base.get() == NULL || direct_base->kind != pa11::TypeKind::Record) continue;
if (!copy_move_constructor_available(direct_base, move)) deleted = true; else materialize_copy_move_body(direct_base); Node source = source_base_expr(direct_base, other, move); init_actions.push_back(
make_base_init_action(direct_base, &source)); } } else {
for (size_t i = 0; i < bare->fields.size(); ++i) { Binding* field = bare->fields[i]; if (!type_needs_copy_move_helper(
field->type, move, &default_arguments_)) continue; copied_prefix = field->member_offset; copy_remaining_fields = true; break;
} if (copied_prefix != 0) { Node action("storage-copy-action");
action.type = bare; action.has_constant_value = true; action.constant_value = copied_prefix; add_child(action, other);
init_actions.push_back(action); } } for (size_t i = 0; i < bare->fields.size(); ++i)
{ Binding* field = bare->fields[i]; if (!copy_move_constructor_available(field->type, move)) deleted = true;
bool field_needs_helper = type_needs_copy_move_helper( field->type, move, &default_arguments_);
if (copied_prefix != 0 && field->member_offset < copied_prefix && !field_needs_helper)
continue; if (!copy_remaining_fields && !field_needs_helper) continue;
if (field_needs_helper)
	materialize_copy_move_body(field->type);
Node source = source_field_expr(field, other, move); init_actions.push_back( make_member_init_action(field, &source)); }
if (init_actions.empty() && (defaulted_storage_copy || (existing != NULL && existing->is_defaulted)) && !bare->fields.empty())
{ Node action("storage-copy-action"); action.type = bare; action.has_constant_value = true;
action.constant_value = pa11::type_size(bare); add_child(action, other); init_actions.push_back(action); }
if (deleted) deleted_functions_.insert(ctor); ctor->unwind_no = !deleted && copy_move_constructor_is_nothrow(bare, move); Node fn("function-definition " + qualified_decl_name(ctor) + " " + pa11::describe_type(fn_type));
fn.binding = ctor; fn.type = fn_type; if (existing != NULL && existing->is_defaulted && !record_has_reference_field(bare))
fn.token_text = "copy-move-helper"; Node this_node("parameter this " + pa11::describe_type(this_type)); this_node.binding = this_binding; this_node.type = this_type;
add_child(fn, this_node); Node other_node("parameter " + other_name + " " + pa11::describe_type(source_ref)); other_node.binding = other_binding;
other_node.type = source_ref; add_child(fn, other_node); Node body("compound-statement"); for (size_t i = 0; i < init_actions.size(); ++i)
add_child(body, init_actions[i]); add_child(fn, body); remember_function_body(ctor, fn); extra_lowir_nodes_.push_back(fn); return ctor;
} bool Parser::copy_move_assignment_available(TypePtr type, bool move) { TypePtr bare = pa11::strip_cv(type);
if (bare->kind == pa11::TypeKind::Array) return copy_move_assignment_available(bare->base, move); if (bare->kind != pa11::TypeKind::Record) return true;
Binding* exact = find_copy_move_assignment_binding(bare, move); if (exact != NULL) return deleted_functions_.find(exact) == deleted_functions_.end(); if (move)
{ Binding* copy = find_copy_move_assignment_binding(bare, false); if (copy != NULL) return deleted_functions_.find(copy) == deleted_functions_.end();
if (suppresses_implicit_move(bare, &default_arguments_, &function_template_placeholders_, &function_template_specialization_arguments_)) return false; } Binding* generated = ensure_copy_move_assignment(bare, move);
return generated != NULL && deleted_functions_.find(generated) == deleted_functions_.end(); } Binding* Parser::ensure_copy_move_assignment(TypePtr type, bool move)
{ TypePtr bare = pa11::strip_cv(type); if (bare->kind != pa11::TypeKind::Record || bare->scope == NULL) return NULL;
Binding* existing = find_copy_move_assignment_binding(bare, move); if (existing != NULL && !existing->is_generated_copy_move_assignment) {
	if (existing->is_defaulted)
	{
		pa11::layout_record_type(bare);
		function<void(TypePtr)> materialize_assignment_body =
			[&](TypePtr subobject)
		{
			TypePtr sub_record = subobject.get() != NULL
				? pa11::strip_cv(subobject) : TypePtr();
			if (sub_record.get() == NULL ||
			    sub_record->kind != pa11::TypeKind::Record ||
			    sub_record->scope == NULL)
				return;
			Binding* sub_assign =
				find_copy_move_assignment_binding(sub_record, move);
			if (sub_assign == NULL)
				sub_assign = ensure_copy_move_assignment(sub_record, move);
			if (sub_assign == NULL && move)
			{
				sub_assign =
					find_copy_move_assignment_binding(sub_record, false);
				if (sub_assign == NULL)
					sub_assign =
						ensure_copy_move_assignment(sub_record, false);
			}
			if (sub_assign == NULL || !sub_assign->is_inline_definition)
				return;
			parse_pending_function_body(sub_assign);
			parse_pending_member_body(sub_assign);
			ensure_function_body_extra_node(sub_assign);
			if (sub_assign->aliased_binding != NULL)
			{
				parse_pending_function_body(sub_assign->aliased_binding);
				parse_pending_member_body(sub_assign->aliased_binding);
				ensure_function_body_extra_node(sub_assign->aliased_binding);
			}
		};
		vector<TypePtr> direct_bases = pa11::record_direct_bases(bare);
		for (size_t b = 0; b < direct_bases.size(); ++b)
			if (type_needs_copy_move_assignment_helper(direct_bases[b], move))
				materialize_assignment_body(direct_bases[b]);
		vector<Binding*> members = assignment_dependency_members(bare);
		for (size_t i = 0; i < members.size(); ++i)
			if (type_needs_copy_move_assignment_helper(members[i]->type,
			                                           move))
				materialize_assignment_body(members[i]->type);
	}
	return existing;
} if (move && suppresses_implicit_move(bare, &default_arguments_, &function_template_placeholders_, &function_template_specialization_arguments_))
return NULL; set<const void*>& generated = move ? generated_move_assignments_ : generated_copy_assignments_; const void* key = bare.get();
if (generated.find(key) != generated.end()) return find_copy_move_assignment_binding(bare, move); generated.insert(key); pa11::layout_record_type(bare);
	TypePtr source_record = move ? bare : pa11::make_cv(bare, pa11::CV_CONST); TypePtr source_ref = move ? pa11::make_rvalue_reference(bare) : pa11::make_lvalue_reference(source_record);
TypePtr this_type = pa11::make_pointer(bare); vector<TypePtr> params; params.push_back(this_type); params.push_back(source_ref);
TypePtr fn_type = pa11::make_function(pa11::make_lvalue_reference(bare), params, false);
Binding* op = existing != NULL ? existing : add_value(bare->scope, BindingKind::Function, "operator=", fn_type); op->type = fn_type; op->is_generated_copy_move_assignment = true; op->unwind_no = !record_needs_copy_move_assignment_helper(bare, move);
function_parameter_names_[op] = vector<string>(2, "this"); function_parameter_names_[op][1] = "other"; bool has_bitfield = false; for (size_t i = 0; i < bare->fields.size(); ++i)
if (bare->fields[i]->is_bit_field) has_bitfield = true; if (has_bitfield) return op;
op->is_inline_definition = true; Scope* function_scope = pa11::create_child_scope(bare->scope, ScopeKind::Function, op->name); Binding* this_binding =
pa11::add_binding(function_scope, BindingKind::Parameter, "this", this_type);
Binding* other_binding = pa11::add_binding(function_scope, BindingKind::Parameter, "other",
source_ref); Node this_ptr = make_this_pointer_node(this_binding, this_type); Node this_object = make_deref_node(bare, this_ptr); Node other = make_parameter_lvalue(other_binding, source_record);
bool deleted = false; Node fn("function-definition " + qualified_decl_name(op) + " " + pa11::describe_type(fn_type)); fn.binding = op;
fn.type = fn_type; Node this_node("parameter this " + pa11::describe_type(this_type)); this_node.binding = this_binding; this_node.type = this_type;
add_child(fn, this_node); Node other_node("parameter other " + pa11::describe_type(source_ref)); other_node.binding = other_binding; other_node.type = source_ref;
add_child(fn, other_node); Node body("compound-statement"); auto make_index_expr = [](uint64_t value) {
Expr out; out.valid = true; out.type = pa11::make_fundamental(FT_INT); out.category = ValueCategory::PRValue; out.constant_expression = true;
out.has_constant_value = true; out.constant_value = value; out.null_pointer_constant = value == 0; out.node = Node("literal prvalue int " + to_string(value));
out.node.token_text = to_string(value); annotate_expr_node(out); return out; };
function<void(Expr, Expr, TypePtr)> append_assignment_statement = [&](Expr target, Expr source, TypePtr assign_type) {
TypePtr bare_assign = pa11::strip_cv(assign_type); if (bare_assign->kind == pa11::TypeKind::Array) {
if (bare_assign->unknown_bound) throw runtime_error("incomplete array type"); for (uint64_t n = 0; n < bare_assign->bound; ++n) {
Expr index = make_index_expr(n); Expr target_elem = make_subscript_expr(target, index); Expr source_elem = make_subscript_expr(source, index);
append_assignment_statement(target_elem, source_elem, bare_assign->base); } return; }
if (move) source = expr_from_node(make_move_cast(assign_type, source.node)); TypePtr target_bare = pa11::strip_cv(expression_object_type(target.type)); Expr action;
if (target_bare->kind == pa11::TypeKind::Record && target_bare->scope != NULL) { Binding* ensured_assignment = ensure_copy_move_assignment(target_bare, move); if (ensured_assignment == NULL && move) ensured_assignment = ensure_copy_move_assignment(target_bare, false); Expr callee = make_member_expr(target, "operator=", "."); vector<Expr> args;
args.push_back(source); action = make_call_expr(callee, args); } else action = make_assignment_expr(OP_ASS, "=", target, source);
Node stmt("expression-statement"); add_child(stmt, action.node); add_child(body, stmt); };
auto find_or_ensure_field_assignment = [&](TypePtr field_type) -> Binding* {
	TypePtr field_bare = pa11::strip_cv(field_type);
	Binding* field_assignment =
		find_copy_move_assignment_binding(field_type, move);
	if (field_assignment == NULL && move)
		field_assignment =
			find_copy_move_assignment_binding(field_type, false);
	if (field_assignment == NULL &&
	    field_bare->kind == pa11::TypeKind::Record &&
	    field_bare->scope != NULL)
	{
		field_assignment = ensure_copy_move_assignment(field_bare, move);
		if (field_assignment == NULL && move)
			field_assignment =
				ensure_copy_move_assignment(field_bare, false);
	}
	return field_assignment;
};
vector<TypePtr> direct_bases = pa11::record_direct_bases(bare);
bool any_base_needs_helper = false; for (size_t b = 0; b < direct_bases.size(); ++b) { TypePtr direct_base = direct_bases[b].get() != NULL ? pa11::strip_cv(direct_bases[b]) : TypePtr(); bool base_needs_helper = direct_base.get() != NULL && direct_base->kind == pa11::TypeKind::Record && type_needs_copy_move_assignment_helper(direct_base, move);
if (base_needs_helper) any_base_needs_helper = true; if (direct_base.get() != NULL && direct_base->kind == pa11::TypeKind::Record) { bool base_assignment_available = copy_move_assignment_available(direct_base, move); if (!base_assignment_available)
deleted = true; if (base_needs_helper && base_assignment_available) { Expr target = target_base_expr(direct_base, this_object);
Expr callee = make_member_expr(target, "operator=", "."); vector<Expr> args; args.push_back(expr_from_node(source_base_expr(direct_base, other,
move))); Expr call = make_call_expr(callee, args); Node stmt("expression-statement"); add_child(stmt, call.node);
add_child(body, stmt); } } } vector<Binding*> assignment_members = assignment_dependency_members(bare); uint64_t copied_prefix = type_has_empty_record_assignment_subobject(bare) ? 0 : pa11::type_size(bare);
bool assign_remaining_fields = any_base_needs_helper;
if (any_base_needs_helper) copied_prefix = 0; else {
for (size_t i = 0; i < assignment_members.size(); ++i) { Binding* field = assignment_members[i]; Binding* field_assignment =
find_or_ensure_field_assignment(field->type);
bool field_needs_helper = type_needs_copy_move_assignment_helper(field->type, move); bool field_needs_assignment = generated_field_needs_assignment_statement(field->type, move, field_needs_helper, field_assignment);
if (field_needs_assignment) { copied_prefix = field->member_offset; assign_remaining_fields = true; break;
} } } if (copied_prefix != 0)
{ Node action("storage-copy-action"); action.type = bare; action.has_constant_value = true;
action.constant_value = copied_prefix; add_child(action, other); add_child(body, action); }
for (size_t i = 0; i < assignment_members.size(); ++i) { Binding* field = assignment_members[i]; bool field_needs_helper =
type_needs_copy_move_assignment_helper(field->type, move); Binding* field_assignment = find_or_ensure_field_assignment(field->type); bool field_needs_assignment = generated_field_needs_assignment_statement(field->type, move, field_needs_helper, field_assignment); bool field_assignment_available = !(pa11::type_has_const(field->type) || pa11::is_reference_type(field->type));
if (field_assignment_available && (field_needs_helper || field_assignment != NULL)) {
	if (field_assignment != NULL &&
	    !field_assignment->is_generated_copy_move_assignment)
		field_assignment_available =
			deleted_functions_.find(field_assignment) ==
			deleted_functions_.end();
	else
		field_assignment_available =
			copy_move_assignment_available(field->type, move);
}
if (!field_assignment_available) { deleted = true; continue; } if (copied_prefix != 0 &&
pa11::strip_cv(field->type)->kind == pa11::TypeKind::Array && !type_needs_copy_move_assignment_helper(pa11::strip_cv(field->type)->base, move) && !type_has_empty_record_assignment_subobject(pa11::strip_cv(field->type)->base))
field_needs_assignment = false; if (copied_prefix != 0 &&
field->member_offset < copied_prefix && !field_needs_assignment) continue; if (!field_needs_assignment) {
if (!assign_remaining_fields) continue; }
Expr target = target_field_expr(field, this_object); TypePtr field_bare = pa11::strip_cv(field->type); if (!field_needs_assignment ||
field_bare->kind != pa11::TypeKind::Record || field_bare->scope == NULL || field_bare->kind == pa11::TypeKind::Array) {
append_assignment_statement(target, expr_from_node(source_field_expr(field, other, false)), field->type); continue; }
Binding* ensured_assignment = ensure_copy_move_assignment(field_bare, move); if (ensured_assignment == NULL && move) ensured_assignment = ensure_copy_move_assignment(field_bare, false);
Expr callee = make_member_expr(target, "operator=", "."); vector<Expr> args;
args.push_back(expr_from_node(source_field_expr(field, other, move))); Expr call = make_call_expr(callee, args); Node stmt("expression-statement"); add_child(stmt, call.node);
add_child(body, stmt); } if (deleted) deleted_functions_.insert(op);
Node ret("return-statement"); add_child(ret, make_deref_node(bare, this_ptr)); add_child(body, ret); add_child(fn, body);
remember_function_body(op, fn); extra_lowir_nodes_.push_back(fn); return op; } namespace {
Binding* find_destructor_binding(TypePtr type) { TypePtr bare = pa11::strip_cv(type); if (bare->kind != pa11::TypeKind::Record || bare->scope == NULL)
return NULL; string name = "~" + bare->scope->name; map<string, vector<Binding*> >::const_iterator found = bare->scope->members.find(name);
if (found == bare->scope->members.end()) return NULL; for (size_t i = 0; i < found->second.size(); ++i) if (found->second[i]->kind == BindingKind::Function)
return found->second[i]; return NULL; }
bool destructor_needs_call(Binding* dtor)
{ return dtor != NULL && !dtor->is_cleanup_only_destructor && (dtor->is_virtual || !dtor->is_noop_destructor); }
bool destructor_forces_cleanup(Binding* dtor)
{ return dtor != NULL && (dtor->is_cleanup_only_destructor || (dtor->is_noop_destructor && !dtor->is_generated_default_destructor && (dtor->is_private || dtor->is_protected_member))); }
struct ActiveGeneratedDestructor
{
	set<const void*>& active;
	const void* key;
	bool armed;
	ActiveGeneratedDestructor(set<const void*>& a, const void* k, bool enable)
		: active(a), key(k), armed(enable)
	{
		if (armed)
			active.insert(key);
	}
	~ActiveGeneratedDestructor()
	{
		if (armed)
			active.erase(key);
	}
};
}  // namespace
	Binding* Parser::ensure_default_destructor(TypePtr type, bool force_trivial) { TypePtr bare = pa11::strip_cv(type); if (bare->kind == pa11::TypeKind::Array)
	return ensure_default_destructor(bare->base, force_trivial); if (bare->kind != pa11::TypeKind::Record || bare->scope == NULL) return NULL; if (bare->is_template_specialization && !type_is_template_dependent(bare) && !bare->complete) {
	try { complete_template_record(bare); } catch (const runtime_error& err) { if ((string(err.what()) != "incomplete class type" &&
	string(err.what()) != "incomplete object type") || active_class_instantiations_.empty()) throw; return NULL; } } const void* key = bare.get(); Binding* existing = find_destructor_binding(bare);
	bool reemit_generated_default = false; if (existing != NULL) { if (!existing->is_generated_default_destructor) return existing;
	if (active_generated_dtors_.find(key) != active_generated_dtors_.end()) return existing; if (completed_generated_dtors_.find(key) != completed_generated_dtors_.end()) return existing; reemit_generated_default = true;
} bool record_complete = bare->complete && (bare->scope == NULL || find(active_class_body_scopes_.begin(), active_class_body_scopes_.end(), bare->scope) == active_class_body_scopes_.end()); ActiveGeneratedDestructor active_dtor(active_generated_dtors_, key, reemit_generated_default); try { pa11::layout_record_type(bare);
} catch (const runtime_error& err) { if ((string(err.what()) != "incomplete class type" &&
string(err.what()) != "incomplete object type") || active_class_instantiations_.empty()) throw; return NULL;
} vector<Node> fini_actions; vector<TypePtr> direct_bases = pa11::record_direct_bases(bare);
	bool forced_nontrivial = false; if (force_trivial) { for (size_t b = 0; b < direct_bases.size(); ++b) { TypePtr direct_base = direct_bases[b].get() != NULL ? pa11::strip_cv(direct_bases[b]) : TypePtr(); if (direct_base.get() != NULL && direct_base->kind == pa11::TypeKind::Record)
	{ Binding* base_dtor = ensure_default_destructor(direct_base, true); if (destructor_needs_call(base_dtor) || destructor_forces_cleanup(base_dtor)) forced_nontrivial = true; } } }
vector<Binding*> members = assignment_dependency_members(bare);
if (!force_trivial || !members.empty() || !direct_bases.empty()) { for (size_t n = 0; n < members.size(); ++n) {
	size_t i = members.size() - 1 - n; Binding* field_dtor = ensure_default_destructor(members[i]->type); if (destructor_needs_call(field_dtor))
	fini_actions.push_back(make_member_fini_action(members[i], field_dtor)); } for (size_t n = 0; n < direct_bases.size(); ++n) { size_t b = direct_bases.size() - 1 - n; TypePtr direct_base = direct_bases[b].get() != NULL ? pa11::strip_cv(direct_bases[b]) : TypePtr(); if (direct_base.get() != NULL && direct_base->kind == pa11::TypeKind::Record)
	{ Binding* base_dtor = ensure_default_destructor(direct_base); if (destructor_forces_cleanup(base_dtor)) forced_nontrivial = true; if (destructor_needs_call(base_dtor)) fini_actions.push_back(make_base_fini_action(direct_base, base_dtor));
} } } if (fini_actions.empty() && !force_trivial && !forced_nontrivial && !reemit_generated_default) return NULL;
if (generated_dtors_.find(key) != generated_dtors_.end() && !reemit_generated_default) { Binding* generated = find_destructor_binding(bare); if (generated == NULL || !generated->is_generated_default_destructor || completed_generated_dtors_.find(key) != completed_generated_dtors_.end()) return generated; existing = generated; reemit_generated_default = true; }
generated_dtors_.insert(key);
TypePtr this_type = pa11::make_pointer(bare); vector<TypePtr> params(1, this_type); TypePtr fn_type = pa11::make_function(pa11::make_fundamental(FT_VOID), params,
false); Binding* dtor = existing != NULL ? existing : add_value(bare->scope, BindingKind::Function, "~" + bare->scope->name, fn_type); dtor->type = fn_type; dtor->is_inline_definition = true;
if (reemit_generated_default) { if (function_bodies_.erase(dtor) != 0) note_function_bodies_changed(); pending_function_bodies_.erase(dtor);
for (size_t i = 0; i < generated_nodes_.size(); ) { if (generated_nodes_[i].binding == dtor) generated_nodes_.erase(generated_nodes_.begin() + i); else ++i; }
for (size_t i = 0; i < extra_lowir_nodes_.size(); ) { if (extra_lowir_nodes_[i].binding == dtor) extra_lowir_nodes_.erase(extra_lowir_nodes_.begin() + i); else ++i; } }
dtor->is_generated_default_destructor = true; dtor->is_noop_destructor = fini_actions.empty() && !forced_nontrivial; dtor->is_cleanup_only_destructor = fini_actions.empty() && forced_nontrivial; Binding* overridden_virtual_dtor = find_overridden_virtual(bare, dtor); if (overridden_virtual_dtor != NULL)
{ dtor->is_virtual = true; dtor->is_noop_destructor = false; dtor->is_cleanup_only_destructor = false; complete_class_virtuals(bare);
} function_parameter_names_[dtor] = vector<string>(1, "this"); Node fn("function-definition " + qualified_decl_name(dtor) + " " + pa11::describe_type(fn_type));
fn.binding = dtor; fn.type = fn_type; Scope* function_scope = pa11::create_child_scope(bare->scope, ScopeKind::Function, dtor->name);
Binding* this_binding = pa11::add_binding(function_scope, BindingKind::Parameter, "this",
this_type); Node param("parameter this " + pa11::describe_type(this_type)); param.binding = this_binding; param.type = this_type;
add_child(fn, param); Node body("compound-statement"); for (size_t i = 0; i < fini_actions.size(); ++i) add_child(body, fini_actions[i]);
add_child(fn, body); extra_lowir_nodes_.push_back(fn); if (record_complete) completed_generated_dtors_.insert(key); return dtor; }
namespace { bool record_has_ordinary_member_function(TypePtr type) { TypePtr bare = pa11::strip_cv(type);
if (bare->kind != pa11::TypeKind::Record || bare->scope == NULL) return false; for (map<string, vector<Binding*> >::const_iterator it = bare->scope->members.begin();
it != bare->scope->members.end(); ++it) { if (it->first == bare->scope->name ||
it->first == "~" + bare->scope->name) continue; for (size_t i = 0; i < it->second.size(); ++i) if (it->second[i]->kind == BindingKind::Function)
return true; } return false; }
bool record_has_reference_field(TypePtr type) { TypePtr bare = pa11::strip_cv(type); if (bare->kind != pa11::TypeKind::Record)
return false; pa11::layout_record_type(bare); { vector<TypePtr> bases = pa11::record_direct_bases(bare); for (size_t b = 0; b < bases.size(); ++b) if (record_has_reference_field(bases[b])) return true; } for (size_t i = 0; i < bare->fields.size(); ++i) {
TypePtr field = bare->fields[i]->type; if (field->kind == pa11::TypeKind::LValueReference || field->kind == pa11::TypeKind::RValueReference) return true;
} return false; }
}  // namespace
void Parser::ensure_aggregate_constructors_for_init(TypePtr type, const Node& init) { if (init.line.compare(0, 16, "braced-init-list") != 0) return;
TypePtr bare = pa11::strip_cv(type); if (bare->kind == pa11::TypeKind::Array) { for (size_t i = 0; i < init.children.size(); ++i)
ensure_aggregate_constructors_for_init(bare->base, init.children[i]); return; } if (bare->kind != pa11::TypeKind::Record)
	return; bool has_reference_field = false; try {
	has_reference_field = record_has_reference_field(bare); } catch (const runtime_error& err) {
	if ((string(err.what()) != "incomplete class type" && string(err.what()) != "incomplete object type") || active_class_instantiations_.empty()) throw;
	return; } if (!init.children.empty() || pa11::type_has_const(type) || has_reference_field ||
	record_has_ordinary_member_function(bare)) { try {
ensure_aggregate_constructor(bare, init.children.size()); } catch (const runtime_error& err) {
if (string(err.what()) == "member has no default constructor") return; if ((string(err.what()) != "incomplete class type" && string(err.what()) != "incomplete object type") ||
active_class_instantiations_.empty()) throw; return; }
} try { pa11::layout_record_type(bare);
} catch (const runtime_error& err) { if ((string(err.what()) != "incomplete class type" &&
string(err.what()) != "incomplete object type") || active_class_instantiations_.empty()) throw; return;
} size_t child_index = 0; { vector<TypePtr> bases = pa11::record_direct_bases(bare); for (size_t b = 0; b < bases.size() && child_index < init.children.size(); ++b)
ensure_aggregate_constructors_for_init(bases[b], init.children[child_index++]); } for (size_t i = 0; child_index < init.children.size() && i < bare->fields.size(); ++i) ensure_aggregate_constructors_for_init(bare->fields[i]->type, init.children[child_index++]);
	} Node Parser::make_member_init_action(Binding* field, const Node* init, Binding* this_binding) { Node action("member-init-action " + field->name);
	action.binding = field; action.type = field->type; TypePtr bare = pa11::strip_cv(field->type); if (init != NULL)
		{ Node child = *init; if (this_binding != NULL) {
		function<void(Node&)> resolve_member_refs = [&](Node& node) {
			bool bound_data_member =
				node.binding != NULL &&
				node.binding->kind == BindingKind::Variable &&
				node.binding->owner != NULL &&
				node.binding->owner->kind == ScopeKind::Class &&
				!node.binding->is_static_member;
			if ((node.binding == NULL || bound_data_member) &&
			    node.line.compare(0, 13, "id-expression") == 0) {
				string member_name = bound_data_member
					? node.binding->name
					: (!node.dependent_value_member_name.empty()
					   ? node.dependent_value_member_name : node.token_text);
				Expr member =
					make_this_member_replay_expr(this_binding,
					                             member_name);
				if (member.valid)
					node = member.node;
			}
			for (size_t i = 0; i < node.children.size(); ++i)
				resolve_member_refs(node.children[i]);
		};
		resolve_member_refs(child);
	} if (child.direct_call != NULL &&
		child.direct_call->owner != NULL &&
	child.direct_call->owner->kind == ScopeKind::Class &&
	child.direct_call->name == child.direct_call->owner->name) {
	parse_pending_function_body(child.direct_call);
	parse_pending_member_body(child.direct_call);
	if (child.direct_call->aliased_binding != NULL) {
	parse_pending_function_body(child.direct_call->aliased_binding);
	parse_pending_member_body(child.direct_call->aliased_binding); } } if (child.line == "braced-init-list") {
	child.line += " lvalue " + pa11::describe_type(field->type); child.type = field->type; } add_child(action, child);
} if (bare->kind == pa11::TypeKind::Record && init == NULL) { action.direct_call = ensure_default_constructor(field->type);
if (init == NULL && action.direct_call != NULL) { map<Binding*, vector<Expr> >::const_iterator defaults = default_arguments_.find(action.direct_call);
if (defaults != default_arguments_.end()) for (size_t j = 1; j < action.direct_call->type->parameters.size(); ++j) add_child(action, defaults->second[j].node);
} } return action; }
	Node Parser::make_member_fini_action(Binding* field, Binding* dtor) { Node action("member-fini-action " + field->name); action.binding = field;
	action.type = field->type; action.direct_call = dtor; return action; } Node Parser::make_base_init_action(TypePtr base, const Node* init)
{ TypePtr bare = pa11::strip_cv(base); Node action("base-init-action " + bare->name); action.type = bare;
	if (init != NULL) { Node child = *init; if (child.direct_call != NULL &&
	child.direct_call->owner != NULL &&
	child.direct_call->owner->kind == ScopeKind::Class &&
	child.direct_call->name == child.direct_call->owner->name) {
	parse_pending_function_body(child.direct_call);
	parse_pending_member_body(child.direct_call);
	if (child.direct_call->aliased_binding != NULL) {
	parse_pending_function_body(child.direct_call->aliased_binding);
	parse_pending_member_body(child.direct_call->aliased_binding); } } add_child(action, child);
} else { Binding* ctor = find_default_constructor(bare);
if (ctor != NULL) { action.direct_call = ctor; map<Binding*, vector<Expr> >::const_iterator defaults =
default_arguments_.find(ctor); if (defaults != default_arguments_.end()) for (size_t j = 1; j < ctor->type->parameters.size(); ++j) add_child(action, defaults->second[j].node);
} } return action; }
	Node Parser::make_base_fini_action(TypePtr base, Binding* dtor) { TypePtr bare = pa11::strip_cv(base); Node action("base-fini-action " + bare->name);
	action.type = bare; action.direct_call = dtor; return action; } bool Parser::initializer_names_direct_base(Scope* class_scope,
TypePtr direct_base, const string& name, const vector<TemplateArgument>* template_arguments) {
TypePtr bare = pa11::strip_cv(direct_base); if (bare->kind != pa11::TypeKind::Record || bare->scope == NULL) return false; if (name == bare->scope->name)
return true; TypePtr substituted; if (find_template_type_substitution(name, substituted) && pa11::same_type(pa11::strip_cv(substituted), bare))
return true; vector<Binding*> types = lookup_unqualified_set(class_scope, name, pa11::LOOKUP_TYPE); for (size_t i = 0; i < types.size(); ++i)
{ TypePtr named = substitute_template_type(types[i]->type); if (pa11::same_type(pa11::strip_cv(named), bare)) return true;
} if (template_arguments != NULL) { TemplateDeclaration* alias = find_alias_template(NULL, name);
if (alias != NULL) { try {
TypePtr named = instantiate_alias_template(alias, *template_arguments); if (pa11::same_type(pa11::strip_cv(named), bare)) return true;
} catch (const runtime_error&) { }
} } return false; }
Node Parser::default_constructor_action(Binding* variable, bool force_trivial) { TypePtr bare = pa11::strip_cv(variable->type); if (bare->kind != pa11::TypeKind::Record)
throw runtime_error("default constructor action requires record"); string ctor_name = bare->name + "::" + bare->name; Binding* ctor = ensure_default_constructor(bare, force_trivial); if (ctor == NULL)
throw runtime_error("missing default constructor"); Node action("constructor-action " + ctor_name); if (force_trivial) action.token_text = "force-trivial";
Node call("call-expression prvalue void"); call.direct_call = ctor; call.type = ctor->type->base; add_child(call, Node("callee " + qualified_decl_name(ctor) + " " +
pa11::describe_type(ctor->type))); TypePtr this_type = ctor->type->parameters[0]; Node amp("unary-expression prvalue " + pa11::describe_type(this_type) + " OP_AMP:&");
amp.type = this_type; amp.category = ValueCategory::PRValue; amp.has_op = true; amp.op = OP_AMP;
amp.token_text = "&"; TypePtr object_type = expression_object_type(variable->type); Node object("id-expression lvalue " + pa11::describe_type(object_type) + " " + variable->name);
object.binding = variable; object.type = object_type; object.category = ValueCategory::LValue; add_child(amp, object);
add_child(call, amp); map<Binding*, vector<Expr> >::const_iterator defaults = default_arguments_.find(ctor); if (defaults != default_arguments_.end())
for (size_t j = 1; j < ctor->type->parameters.size(); ++j) add_child(call, defaults->second[j].node); add_child(action, call); return action;
} void Parser::resolve_pending_member_initializers(Scope* class_scope, Node& node) { if (node.line.compare(0, 18, "member-init-action") == 0 &&
node.binding == NULL && !node.token_text.empty()) { Binding* field = pa11::lookup_qualified(class_scope,
node.token_text, pa11::LOOKUP_VARIABLE); if (field != NULL && !field->is_static_member) {
node.binding = field; node.type = field->type; if (!node.children.empty()) {
node.children[0].type = field->type; if (node.children[0].line == "braced-init-list") node.children[0].line += " lvalue " + pa11::describe_type(field->type);
} TypePtr bare = pa11::strip_cv(field->type); if (bare->kind == pa11::TypeKind::Record) node.direct_call = ensure_default_constructor(field->type);
} else { TypePtr record = pa11::record_type_for_scope(class_scope);
vector<TypePtr> bases = record.get() != NULL ? pa11::record_direct_bases(record) : vector<TypePtr>(); for (size_t b = 0; b < bases.size(); ++b) { TypePtr direct_base = bases[b]; if (direct_base.get() != NULL && initializer_names_direct_base(class_scope,
direct_base, node.token_text)) { TypePtr bare_base = pa11::strip_cv(direct_base);
node.line = "base-init-action " + bare_base->name; node.type = direct_base; node.binding = NULL; break; } }
} } for (size_t i = 0; i < node.children.size(); ++i) resolve_pending_member_initializers(class_scope, node.children[i]);
} void Parser::inject_anonymous_union_members(Scope* class_scope, Binding* storage) { for (size_t i = 0; i < class_scope->binding_order.size(); ++i)
{ Binding* member = class_scope->binding_order[i]; if (member->kind != BindingKind::Variable) continue;
Binding* injected = add_value(storage->owner, BindingKind::Variable, member->name, member->type);
injected->target_scope = class_scope; injected->aliased_binding = storage; } }
}  // namespace internal
}  // namespace pa12
