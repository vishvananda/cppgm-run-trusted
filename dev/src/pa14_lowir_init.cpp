#include "pa14_lowir_internal.h"
namespace pa14 { namespace internal { bool type_contains_record(TypePtr type); bool default_init_no_op(TypePtr type);
namespace { bool scalar_static_init_known_constant(const Node& init) { if (starts_with(init.line, "literal"))
return true; if (starts_with(init.line, "unary-expression") && init.has_op && init.op == OP_PLUS && !init.children.empty()) return scalar_static_init_known_constant(init.children[0]);
if (starts_with(init.line, "binary-expression") && init.has_op && (init.op == OP_PLUS || init.op == OP_MINUS) && init.children.size() == 2) {
const Node& lhs = init.children[0]; const Node& rhs = init.children[1]; return (lhs.binding != NULL && rhs.has_constant_value) || (rhs.binding != NULL && lhs.has_constant_value);
} return init.has_constant_value; } bool local_static_needs_guard(const Node& var)
{ if (var.binding == NULL || !var.binding->is_local_static) return false; TypePtr type = var.binding->type;
TypePtr bare = pa11::strip_cv(type); if (var.children.empty()) return type_contains_record(type) && !default_init_no_op(type); if (starts_with(var.children[0].line, "no-op-initializer"))
return false; if (bare->kind == TypeKind::Array || bare->kind == TypeKind::Record || is_reference(type))
return true; return !scalar_static_init_known_constant(var.children[0]); }
bool function_definition_body_empty(const Node& node)
{
	return !node.children.empty() &&
	       starts_with(node.children.back().line, "compound-statement") &&
	       node.children.back().children.empty();
}

bool inline_empty_nonvirtual_destructor_body(const ProgramLowerer& program,
                                             const Binding* dtor)
{
	if (dtor != NULL &&
	    dtor->aliased_binding != NULL &&
	    dtor->aliased_binding->is_inline_definition)
		dtor = dtor->aliased_binding;
	if (dtor == NULL || dtor->is_virtual || !dtor->is_inline_definition)
		return false;
	if (dtor->is_cleanup_only_destructor)
		return false;
	const Node* fn = NULL;
	map<const Binding*, const Node*>::const_iterator found =
		program.inline_definitions.find(dtor);
	if (found != program.inline_definitions.end())
		fn = found->second;
	map<const Binding*, Node>::const_iterator synthetic =
		program.synthetic_inline_definitions.find(dtor);
	if (fn == NULL && synthetic != program.synthetic_inline_definitions.end())
		fn = &synthetic->second;
	return fn != NULL && function_definition_body_empty(*fn);
}

}  // namespace
Binding* canonical_constructor_binding(Binding* binding)
{
	if (binding == NULL ||
	    binding->kind != BindingKind::Function ||
	    binding->aliased_binding == NULL ||
	    binding->aliased_binding->kind != BindingKind::Function ||
	    binding->type.get() == NULL ||
	    binding->aliased_binding->type.get() == NULL ||
	    !pa11::same_type(binding->type, binding->aliased_binding->type))
		return binding;
	Binding* alias = binding->aliased_binding;
	if (alias->is_inline_definition ||
	    !alias->function_specialization_symbol.empty())
		return alias;
	return binding;
}

const Binding* canonical_constructor_binding(const Binding* binding)
{
	return canonical_constructor_binding(const_cast<Binding*>(binding));
}

Binding* find_constructor(TypePtr type, size_t arg_count) { TypePtr bare = pa11::strip_cv(type); if (bare->kind != TypeKind::Record || bare->scope == NULL)
return NULL; map<string, vector<Binding*> >::const_iterator found = bare->scope->members.find(bare->scope->name); if (found == bare->scope->members.end())
return NULL; for (size_t i = 0; i < found->second.size(); ++i) { Binding* binding = found->second[i];
if (binding->kind == BindingKind::Function && binding->type->kind == TypeKind::Function && binding->type->parameters.size() == arg_count + 1) return canonical_constructor_binding(binding);
} return NULL; } const Node* record_prvalue_child_for_xvalue(const Node& arg)
{ if (arg.children.empty()) return NULL; if (starts_with(arg.line, "cast-expression") &&
(arg.category == ValueCategory::XValue || is_reference(arg.type))) { const Node* child = record_prvalue_child_for_xvalue(arg.children[0]); if (child != NULL)
return child; if (arg.category != ValueCategory::XValue) return NULL; const Node& direct_child = arg.children[0]; if (direct_child.category == ValueCategory::LValue || direct_child.category == ValueCategory::XValue)
return NULL; if (pa11::strip_cv(object_type(direct_child.type))->kind != TypeKind::Record) return NULL; return &direct_child; }
if (starts_with(arg.line, "base-subobject-expression")) { const Node* child = record_prvalue_child_for_xvalue(arg.children[0]); if (child != NULL)
return child; const Node& direct_child = arg.children[0]; if (direct_child.category == ValueCategory::LValue || direct_child.category == ValueCategory::XValue)
return NULL; if (pa11::strip_cv(object_type(direct_child.type))->kind != TypeKind::Record) return NULL; return &direct_child; }
return NULL;
} Binding* find_any_copy_move_constructor(TypePtr type, bool move) { TypePtr bare = pa11::strip_cv(type);
if (bare->kind != TypeKind::Record || bare->scope == NULL) return NULL; map<string, vector<Binding*> >::const_iterator found = bare->scope->members.find(bare->scope->name);
if (found == bare->scope->members.end()) return NULL; for (size_t i = 0; i < found->second.size(); ++i) {
Binding* binding = found->second[i]; if (binding->kind != BindingKind::Function || binding->type->kind != TypeKind::Function || binding->type->parameters.size() != 2)
continue; if (function_signature_has_unresolved_storage(binding) ||
type_contains_template_symbol_pattern(binding->type) ||
type_contains_template_symbol_pattern(class_record_for_member(binding))) continue; TypePtr param = binding->type->parameters[1]; if (move) {
if (param->kind != TypeKind::RValueReference) continue; } else if (param->kind != TypeKind::LValueReference)
continue; TypePtr param_record = pa11::strip_cv(param->base); if (param_record->kind == TypeKind::Record && pa11::same_type(param_record, bare))
return binding; } return NULL; }
bool type_needs_defaulted_copy_move_helper(TypePtr type, bool move); bool record_needs_defaulted_copy_move_helper(TypePtr type, bool move) { TypePtr bare = pa11::strip_cv(type);
if (bare->kind != TypeKind::Record) return false; if (bare->is_polymorphic) return true; Binding* exact = find_any_copy_move_constructor(bare, move); if (exact != NULL && !exact->is_defaulted)
return true; if (exact == NULL && move) { Binding* copy = find_any_copy_move_constructor(bare, false);
	if (copy != NULL && !copy->is_defaulted) return true; } pa11::layout_record_type(bare);
	if (!pa11::record_virtual_bases(bare).empty()) return true;
	vector<TypePtr> bases = pa11::record_direct_bases(bare); for (size_t i = 0; i < bases.size(); ++i)
	if (type_needs_defaulted_copy_move_helper(bases[i], move)) return true; for (size_t i = 0; i < bare->fields.size(); ++i)
	if (type_needs_defaulted_copy_move_helper(bare->fields[i]->type, move)) return true; return false; }
bool type_needs_defaulted_copy_move_helper(TypePtr type, bool move) { TypePtr bare = pa11::strip_cv(type); if (bare->kind == TypeKind::Array)
return type_needs_defaulted_copy_move_helper(bare->base, move); if (bare->kind != TypeKind::Record) return false; return record_needs_defaulted_copy_move_helper(bare, move);
} bool defaulted_copy_move_constructor_needs_helper(Binding* binding, TypePtr type) { if (binding == NULL ||
binding->type->kind != TypeKind::Function || binding->type->parameters.size() != 2 || !is_reference(binding->type->parameters[1])) return false;
return type_needs_defaulted_copy_move_helper( type, binding->type->parameters[1]->kind == TypeKind::RValueReference); }
Binding* find_copy_move_constructor(TypePtr type, bool move) { TypePtr bare = pa11::strip_cv(type); if (bare->kind != TypeKind::Record || bare->scope == NULL)
return NULL; map<string, vector<Binding*> >::const_iterator found = bare->scope->members.find(bare->scope->name); if (found == bare->scope->members.end())
return NULL; for (size_t i = 0; i < found->second.size(); ++i) { Binding* binding = found->second[i];
	if (binding->kind != BindingKind::Function || binding->type->kind != TypeKind::Function || binding->type->parameters.size() != 2) continue;
	if (function_signature_has_unresolved_storage(binding) ||
	    type_contains_template_symbol_pattern(binding->type) ||
	    type_contains_template_symbol_pattern(class_record_for_member(binding)))
		continue;
	if (binding->is_defaulted &&
	    binding->is_inline_definition &&
	    !binding->is_object_root &&
	    !defaulted_copy_move_constructor_needs_helper(binding, bare)) continue; TypePtr param = binding->type->parameters[1];
if (move) { if (param->kind != TypeKind::RValueReference) continue;
} else if (param->kind != TypeKind::LValueReference) continue; TypePtr param_record = pa11::strip_cv(param->base);
if (param_record->kind == TypeKind::Record && pa11::same_type(param_record, bare)) return binding; }
return NULL; } bool inline_defaulted_copy_move_storage_constructor(Binding* binding, TypePtr type,
const Node& init) { if (binding == NULL || !binding->is_defaulted ||
!binding->is_inline_definition || binding->type->kind != TypeKind::Function || binding->type->parameters.size() != 2 || !is_reference(binding->type->parameters[1]) ||
init.children.size() != 1 || defaulted_copy_move_constructor_needs_helper(binding, type) || !record_has_storage_copy(type)) return false;
TypePtr param_record = pa11::strip_cv(binding->type->parameters[1]->base); TypePtr target_record = pa11::strip_cv(type); return param_record->kind == TypeKind::Record && target_record->kind == TypeKind::Record &&
pa11::same_type(param_record, target_record); } bool same_record_copy_move_constructor(Binding* binding, TypePtr type,
const Node& init) { if (binding == NULL || binding->type->kind != TypeKind::Function ||
binding->type->parameters.size() != 2 || !is_reference(binding->type->parameters[1]) || init.children.size() != 1) return false;
TypePtr param_record = pa11::strip_cv(binding->type->parameters[1]->base); TypePtr target_record = pa11::strip_cv(type); return param_record->kind == TypeKind::Record && target_record->kind == TypeKind::Record &&
pa11::same_type(param_record, target_record); } Binding* find_destructor(TypePtr type) {
TypePtr bare = pa11::strip_cv(type); if (bare->kind != TypeKind::Record || bare->scope == NULL) return NULL; string name = "~" + bare->scope->name;
map<string, vector<Binding*> >::const_iterator found = bare->scope->members.find(name); if (found == bare->scope->members.end()) return NULL;
for (size_t i = 0; i < found->second.size(); ++i) { Binding* binding = found->second[i]; if (binding->kind == BindingKind::Function &&
binding->type->kind == TypeKind::Function) return binding; } return NULL;
} bool type_needs_destructor(TypePtr type) { TypePtr bare = pa11::strip_cv(type);
if (bare->kind == TypeKind::Array) return type_needs_destructor(bare->base); if (bare->kind != TypeKind::Record) return false;
	Binding* dtor = find_destructor(bare); if (dtor != NULL && (dtor->is_virtual || !dtor->is_noop_destructor)) return true; pa11::layout_record_type(bare);
	vector<TypePtr> bases = pa11::record_direct_bases(bare); for (size_t i = 0; i < bases.size(); ++i)
	if (type_needs_destructor(bases[i])) return true; for (size_t i = 0; i < bare->fields.size(); ++i) if (type_needs_destructor(bare->fields[i]->type))
	return true; return false; } bool type_has_generated_noop_destructor(TypePtr type)
{ TypePtr bare = pa11::strip_cv(type); if (bare->kind != TypeKind::Record) return false;
Binding* dtor = find_destructor(bare); return dtor != NULL && dtor->is_generated_default_destructor && dtor->is_noop_destructor;
} bool temp_cleanups_are_generated_noop_destructors( const vector<pair<Value, TypePtr> >& temps)
{ if (temps.empty()) return false; for (size_t i = 0; i < temps.size(); ++i) if (!type_has_generated_noop_destructor(temps[i].second))
return false; return true; } bool type_contains_record(TypePtr type)
{ TypePtr bare = pa11::strip_cv(type); if (bare->kind == TypeKind::Record) return true;
if (bare->kind == TypeKind::Array) return type_contains_record(bare->base); return false; }
bool default_init_no_op_impl(TypePtr type, bool subobject) { TypePtr bare = pa11::strip_cv(type); if (bare->kind == TypeKind::Array)
return default_init_no_op_impl(bare->base, subobject); if (bare->kind != TypeKind::Record) return false; Binding* ctor = find_constructor(bare, 0);
	if (ctor != NULL && !ctor->is_generated_default_constructor) return subobject && ctor->is_noop_constructor; pa11::layout_record_type(bare); vector<TypePtr> bases = pa11::record_direct_bases(bare);
	if (!pa11::record_virtual_bases(bare).empty()) return false;
	for (size_t i = 0; i < bases.size(); ++i) if (!default_init_no_op_impl(bases[i], true)) return false; for (size_t i = 0; i < bare->fields.size(); ++i) if (!default_init_no_op_impl(bare->fields[i]->type, true)) return false;
		return true; } bool default_init_no_op(TypePtr type) { return default_init_no_op_impl(type, false); } bool no_op_generated_default_constructor(Binding* ctor, TypePtr type) {
		if (ctor == NULL) return false; bool explicit_defaulted_noop =
		ctor->is_defaulted && ctor->is_noop_constructor && ctor->type.get() != NULL &&
		ctor->type->kind == TypeKind::Function && ctor->type->parameters.size() == 1;
		if (!ctor->is_generated_default_constructor && !explicit_defaulted_noop) return false; TypePtr bare = pa11::strip_cv(type); if (bare->kind == TypeKind::Record && bare->is_polymorphic)
	return false; if (bare->kind == TypeKind::Record && !pa11::record_direct_bases(bare).empty()) return false; if (ctor->is_noop_constructor)
	return true; return default_init_no_op(type); } bool has_inline_constructor(TypePtr type)
{ TypePtr bare = pa11::strip_cv(type); if (bare->kind != TypeKind::Record || bare->scope == NULL) return false;
map<string, vector<Binding*> >::const_iterator found = bare->scope->members.find(bare->scope->name); if (found == bare->scope->members.end()) return false;
for (size_t i = 0; i < found->second.size(); ++i) if (found->second[i]->kind == BindingKind::Function && found->second[i]->type->kind == TypeKind::Function && found->second[i]->is_inline_definition)
{ if (found->second[i]->type->parameters.size() == 1) return true; } return false; } bool aggregate_blocking_constructor(Binding* binding)
{ if (binding->kind != BindingKind::Function || binding->type->kind != TypeKind::Function) return false;
if (binding->is_generated_default_constructor || binding->is_generated_aggregate_constructor || binding->is_generated_copy_move_constructor) return false;
if (binding->is_defaulted && binding->type->parameters.size() == 1) return false; return true; }
bool record_has_aggregate_blocking_constructor(TypePtr type) { TypePtr bare = pa11::strip_cv(type); if (bare->kind != TypeKind::Record || bare->scope == NULL)
return false; map<string, vector<Binding*> >::const_iterator found = bare->scope->members.find(bare->scope->name); if (found == bare->scope->members.end())
return false; for (size_t i = 0; i < found->second.size(); ++i) if (aggregate_blocking_constructor(found->second[i])) return true;
return false; } bool record_has_nonpublic_field(TypePtr type) {
TypePtr bare = pa11::strip_cv(type); if (bare->kind != TypeKind::Record) return false; pa11::layout_record_type(bare);
for (size_t i = 0; i < bare->fields.size(); ++i) if (bare->fields[i]->is_private || bare->fields[i]->is_protected_member) return true;
return false; } bool record_has_real_inline_constructor(TypePtr type) {
TypePtr bare = pa11::strip_cv(type); if (bare->kind != TypeKind::Record || bare->scope == NULL) return false; map<string, vector<Binding*> >::const_iterator found =
bare->scope->members.find(bare->scope->name); if (found == bare->scope->members.end()) return false; for (size_t i = 0; i < found->second.size(); ++i)
if (found->second[i]->kind == BindingKind::Function && found->second[i]->type->kind == TypeKind::Function && found->second[i]->is_inline_definition && aggregate_blocking_constructor(found->second[i]))
return true; return false; } bool record_has_ordinary_member_function_for_aggregate(TypePtr type)
{ TypePtr bare = pa11::strip_cv(type); if (bare->kind != TypeKind::Record || bare->scope == NULL) return false;
for (map<string, vector<Binding*> >::const_iterator it = bare->scope->members.begin(); it != bare->scope->members.end(); ++it)
{ if (it->first == bare->scope->name || it->first == "~" + bare->scope->name) continue;
for (size_t i = 0; i < it->second.size(); ++i) if (it->second[i]->kind == BindingKind::Function) return true; }
return false; } bool is_brace_elision_aggregate(TypePtr type) {
TypePtr bare = pa11::strip_cv(type); if (bare->kind == TypeKind::Array) return true; if (bare->kind != TypeKind::Record)
return false; return !record_has_aggregate_blocking_constructor(type) && !record_has_nonpublic_field(type); }
bool is_string_literal_node(const Node& node) { return !node.token_text.empty() && node.token_text[node.token_text.size() - 1] == '"';
} bool zero_init_has_store(TypePtr type) { TypePtr bare = pa11::strip_cv(type);
if (bare->kind == TypeKind::Array) return !bare->unknown_bound && bare->bound != 0 && zero_init_has_store(bare->base); if (bare->kind != TypeKind::Record)
	return true; pa11::layout_record_type(bare); vector<TypePtr> bases = pa11::record_direct_bases(bare); for (size_t i = 0; i < bases.size(); ++i) if (zero_init_has_store(bases[i])) return true;
	for (size_t i = 0; i < bare->fields.size(); ++i) if (zero_init_has_store(bare->fields[i]->type)) return true; return false;
	} bool type_has_reference_subobject(TypePtr type) { TypePtr bare = pa11::strip_cv(type);
	if (bare->kind == TypeKind::Array) return type_has_reference_subobject(bare->base); if (bare->kind != TypeKind::Record) return false;
	pa11::layout_record_type(bare); vector<TypePtr> bases = pa11::record_direct_bases(bare); for (size_t i = 0; i < bases.size(); ++i) if (type_has_reference_subobject(bases[i])) return true;
	for (size_t i = 0; i < bare->fields.size(); ++i) { if (is_reference(bare->fields[i]->type) || type_has_reference_subobject(bare->fields[i]->type))
	return true; } return false; }
bool record_has_user_assignment_operator(TypePtr type) { TypePtr bare = pa11::strip_cv(type); if (bare->kind != TypeKind::Record || bare->scope == NULL)
return false; map<string, vector<Binding*> >::const_iterator found = bare->scope->members.find("operator="); if (found == bare->scope->members.end())
return false; for (size_t i = 0; i < found->second.size(); ++i) if (found->second[i]->kind == BindingKind::Function && !found->second[i]->is_generated_copy_move_assignment)
return true; return false; } string zero_integer_type(uint64_t size)
{ switch (size) { case 1: return "i8";
case 2: return "i16"; case 4: return "i32"; case 8: return "i64"; default: return "";
} } bool same_record_initializer(const Node& init, TypePtr type) {
if (init.type.get() == NULL || type.get() == NULL) return false; TypePtr dst = pa11::strip_cv(type); TypePtr src = pa11::strip_cv(object_type(init.type));
return dst->kind == TypeKind::Record && src->kind == TypeKind::Record && pa11::same_type(src, dst); }
bool record_has_base(TypePtr source, TypePtr target) { if (source.get() == NULL || target.get() == NULL) return false; TypePtr dst = pa11::strip_cv(target); TypePtr root = pa11::strip_cv(source); if (root->kind != TypeKind::Record || dst->kind != TypeKind::Record) return false; vector<TypePtr> pending; pending.push_back(root); vector<TypePtr> seen;
while (!pending.empty()) { TypePtr cur = pending.back().get() != NULL ? pa11::strip_cv(pending.back()) : TypePtr(); pending.pop_back(); if (cur.get() == NULL || cur->kind != TypeKind::Record) continue; bool already = false; for (size_t i = 0; i < seen.size(); ++i) if (pa11::same_type(seen[i], cur)) already = true; if (already) continue; seen.push_back(cur); if (pa11::same_type(cur, dst)) return true; vector<TypePtr> bases = pa11::record_direct_bases(cur); pending.insert(pending.end(), bases.begin(), bases.end()); } return false; }
namespace {
void append_default_dependency_members(TypePtr record, vector<Binding*>& members)
{
	TypePtr bare = record.get() != NULL ? pa11::strip_cv(record) : TypePtr();
	if (bare.get() == NULL || bare->kind != TypeKind::Record)
		return;
	pa11::layout_record_type(bare);
	members = bare->fields;
	if (bare->scope == NULL)
		return;
	for (size_t i = 0; i < bare->scope->binding_order.size(); ++i)
	{
		Binding* member = bare->scope->binding_order[i];
		if (member == NULL ||
		    member->kind != BindingKind::Variable ||
		    member->is_static_member ||
		    member->aliased_binding != NULL)
			continue;
		bool duplicate = false;
		for (size_t j = 0; j < members.size(); ++j)
			if (members[j] == member)
				duplicate = true;
		if (!duplicate)
			members.push_back(member);
	}
}

void demand_suppressed_default_init_dependencies(ProgramLowerer& program,
                                                 TypePtr type,
                                                 bool base_entry,
                                                 set<const pa11::Type*>& seen);

void demand_suppressed_default_init_subobjects(ProgramLowerer& program,
                                               TypePtr type,
                                               set<const pa11::Type*>& seen)
{
	TypePtr bare = type.get() != NULL ? pa11::strip_cv(type) : TypePtr();
	if (bare.get() == NULL)
		return;
	if (bare->kind == TypeKind::Array)
	{
		demand_suppressed_default_init_dependencies(program,
		                                            bare->base,
		                                            false,
		                                            seen);
		return;
	}
	if (bare->kind != TypeKind::Record)
		return;
	if (!seen.insert(bare.get()).second)
		return;
	vector<TypePtr> bases = pa11::record_direct_bases(bare);
	for (size_t i = 0; i < bases.size(); ++i)
		demand_suppressed_default_init_dependencies(program,
		                                            bases[i],
		                                            true,
		                                            seen);
	vector<Binding*> members;
	append_default_dependency_members(bare, members);
	for (size_t i = 0; i < members.size(); ++i)
		if (members[i] != NULL)
			demand_suppressed_default_init_dependencies(program,
			                                            members[i]->type,
			                                            false,
			                                            seen);
}

void demand_suppressed_default_init_dependencies(ProgramLowerer& program,
                                                 TypePtr type,
                                                 bool base_entry,
                                                 set<const pa11::Type*>& seen)
{
	TypePtr bare = type.get() != NULL ? pa11::strip_cv(type) : TypePtr();
	if (bare.get() == NULL)
		return;
	if (bare->kind == TypeKind::Array)
	{
		demand_suppressed_default_init_subobjects(program, bare, seen);
		return;
	}
	if (bare->kind != TypeKind::Record)
		return;
	Binding* ctor = find_constructor(bare, 0);
	if (ctor == NULL)
	{
		demand_suppressed_default_init_subobjects(program, bare, seen);
		return;
	}
	if (ctor->is_generated_default_constructor ||
	    ctor->is_generated_aggregate_constructor)
	{
		demand_suppressed_default_init_subobjects(program, bare, seen);
		return;
	}
	if (base_entry)
	{
		program.constructor_symbol_for(ctor, true);
		program.demand_inline_function(ctor, false);
		program.demand_inline_function(ctor, true);
	}
	else
		program.demand_inline_function(ctor);
}
}  // namespace
void demand_suppressed_default_init_subobjects(ProgramLowerer& program,
                                               TypePtr type)
{
	set<const pa11::Type*> seen;
	demand_suppressed_default_init_subobjects(program, type, seen);
}
bool FunctionLowerer::lower_braced_variable_init(const Node& var, TypePtr type) { TypePtr bare = pa11::strip_cv(type); Value direct_base;
if (bare->kind == TypeKind::Array) direct_base = ensure_pointer(emit_lvalue_addr(var)); shared_ptr<Value> cached_base(new Value(direct_base)); function<Value()> addr_for = [this, &var, cached_base]() {
if (cached_base->text.empty()) *cached_base = ensure_pointer(emit_lvalue_addr(var)); return *cached_base; };
if (is_initializer_list_type(type, NULL)) { lower_object_init(addr_for, type, var.children[0]); emit_pending_temp_cleanups(); register_cleanup(var.binding, type); return true; }
if (bare->kind == TypeKind::Array) { direct_base = *cached_base; lower_direct_array_init(direct_base, type, var.children[0]);
} else { if (!record_has_real_inline_constructor(type) &&
!record_has_ordinary_member_function_for_aggregate(type) && var.children[0].direct_call == NULL) { if (!var.children[0].children.empty() ||
zero_init_has_store(type) || var.children[0].token_text == "lambda-closure") ensure_pointer(emit_lvalue_addr(var)); if (var.children[0].token_text == "lambda-closure")
lower_aggregate_init(addr_for, type, var.children[0]); else { function<Value()> aggregate_addr_for = [this, &var]() {
return ensure_pointer(emit_lvalue_addr(var)); }; lower_aggregate_init(aggregate_addr_for, type,
var.children[0]); } emit_pending_temp_cleanups(); register_cleanup(var.binding, type);
return true; } bool generated_aggregate_init = var.children[0].direct_call != NULL &&
var.children[0].direct_call->is_generated_aggregate_constructor; Binding* init_ctor = var.children[0].direct_call; if (init_ctor == NULL) init_ctor = find_constructor(type, var.children[0].children.size());
if (!generated_aggregate_init) generated_aggregate_init = init_ctor != NULL && init_ctor->is_generated_aggregate_constructor;
bool aggregate_storage_init = is_brace_elision_aggregate(type) || generated_aggregate_init; bool copy_move_init = same_record_copy_move_constructor(init_ctor, type, var.children[0]);
bool lambda_closure_init = var.children[0].token_text == "lambda-closure" || (bare->kind == TypeKind::Record && bare->scope != NULL &&
bare->scope->name.compare(0, 8, "__lambda") == 0); if (aggregate_storage_init && lambda_closure_init && !var.children[0].children.empty())
{ lower_aggregate_init(addr_for, type, var.children[0]); emit_pending_temp_cleanups(); register_cleanup(var.binding, type);
return true; } bool const_zero_init = pa11::type_has_const(type) &&
var.children[0].children.empty() && zero_init_has_store(type); if (aggregate_storage_init && var.children[0].token_text == "lambda-closure")
addr_for(); else if (aggregate_storage_init && (!var.children[0].children.empty() || zero_init_has_store(type))) addr_for();
if (aggregate_storage_init && pa11::type_has_const(type) && var.children[0].children.empty() && !zero_init_has_store(type) &&
!type_needs_cleanup(type) && !record_has_real_inline_constructor(type)) { if (var.children[0].token_text == "lambda-closure")
addr_for(); emit_pending_temp_cleanups(); return true; }
if (aggregate_storage_init && !copy_move_init && (!pa11::type_has_const(type) || const_zero_init) && (!type_has_reference_subobject(type) || lambda_closure_init) &&
!record_has_user_assignment_operator(type)) { if (lambda_closure_init) lower_object_init(addr_for, type, var.children[0]);
else { function<Value()> aggregate_addr_for = [this, &var]() { return ensure_pointer(emit_lvalue_addr(var));
}; lower_object_init(aggregate_addr_for, type, var.children[0]);
} } else {
bool saved_destination_before_try = constructor_destination_before_protected_try_; constructor_destination_before_protected_try_ = true; lower_object_init(addr_for, type, var.children[0]);
constructor_destination_before_protected_try_ = saved_destination_before_try; } }
emit_pending_temp_cleanups(); register_cleanup(var.binding, type); return true; }
void FunctionLowerer::lower_variable_decl(const Node& var) { if (!starts_with(var.line, "variable ") || var.binding == NULL) return; if (var.binding->is_local_static) { lower_local_static_decl(var); return; } string slot = return_slot_variables_.find(var.binding) == return_slot_variables_.end() ? slot_for(var.binding) : string(); if (var.children.empty()) { TypePtr bare = pa11::strip_cv(var.binding->type); if (type_contains_record(var.binding->type)) { if (bare->kind != TypeKind::Array) ensure_pointer(emit_lvalue_addr(var)); function<Value()> addr_for = [this, &var]() { return ensure_pointer(emit_lvalue_addr(var)); };
lower_default_init(addr_for, var.binding->type); register_cleanup(var.binding, var.binding->type); } return; } TypePtr type = var.binding->type; if (starts_with(var.children[0].line, "no-op-initializer")) { if (type_contains_record(var.binding->type)) { TypePtr bare_noop = pa11::strip_cv(var.binding->type); bool materialize_noop = (pa11::type_has_const(var.binding->type) && has_inline_constructor(var.binding->type)) || zero_init_has_store(var.binding->type) || type_needs_cleanup(var.binding->type); if (bare_noop->kind == TypeKind::Array) materialize_noop = materialize_noop && pa11::type_has_const(var.binding->type); if (materialize_noop) ensure_pointer(emit_lvalue_addr(var)); register_cleanup(var.binding, var.binding->type); } return; } if (starts_with(var.children[0].line, "constructor-action")) {
Binding* ctor = !var.children[0].children.empty() ? var.children[0].children[0].direct_call : NULL; bool noop_constructor = no_op_generated_default_constructor(ctor, var.binding->type); if (!noop_constructor && var.children[0].token_text.empty() && ctor != NULL && ctor->is_generated_default_constructor && !pa11::strip_cv(var.binding->type)->is_polymorphic) { noop_constructor = default_init_no_op(var.binding->type); if (noop_constructor) demand_suppressed_default_init_subobjects(program_, var.binding->type); } if (noop_constructor) {
ensure_pointer(emit_lvalue_addr(var)); emit_pending_temp_cleanups(); register_cleanup(var.binding, var.binding->type); return; } if (!var.children[0].children.empty()) emit_rvalue(var.children[0].children[0]); emit_pending_temp_cleanups(); register_cleanup(var.binding, var.binding->type); return; } TypePtr bare = pa11::strip_cv(type); if (bare->kind == TypeKind::Array && is_string_literal_node(var.children[0])) { Value base = ensure_pointer(emit_lvalue_addr(var)); function<Value()> addr_for = [base]() { return base; }; lower_string_array_init(addr_for, type, var.children[0]); return; } if ((bare->kind == TypeKind::Record || bare->kind == TypeKind::Array) && starts_with(var.children[0].line, "braced-init-list")) { lower_braced_variable_init(var, type); return; } if (bare->kind == TypeKind::Record) {
Value base = ensure_pointer(emit_lvalue_addr(var)); function<Value()> addr_for = [base]() { return base; }; bool saved_destination_before_try = constructor_destination_before_protected_try_; constructor_destination_before_protected_try_ = true; lower_object_init(addr_for, type, var.children[0]); constructor_destination_before_protected_try_ = saved_destination_before_try; emit_pending_temp_cleanups(); register_cleanup(var.binding, type); return; } if (is_reference(type)) { Value source = ensure_pointer(emit_lvalue_addr(var.children[0])); TypePtr from_ptr = pa11::make_pointer(object_type(var.children[0].type)); TypePtr to_ptr = pa11::make_pointer(type->base); Value converted = convert_value(source, from_ptr, to_ptr); instr("store ptr " + converted.text + ", $" + slot); } else {
if (starts_with(var.children[0].line, "call-expression")) { call_result_store_slot_ = slot; call_result_store_type_ = type; call_result_store_consumed_ = false; } Value init = emit_rvalue(var.children[0]); if (!call_result_store_consumed_) { TypePtr init_bare = pa11::strip_cv(strip_for_value(var.children[0].type)); TypePtr target_bare = pa11::strip_cv(strip_for_value(type)); bool literal_value = !init.text.empty() && init.text[0] != '%' && init.text[0] != '$' && init.text[0] != '@'; bool materialize_widening_literal = literal_value && pa11::is_integral_or_bool_type(init_bare) && pa11::is_integral_or_bool_type(target_bare) && pa11::type_size(target_bare) > pa11::type_size(init_bare); init = convert_value(init, var.children[0].type, type, !materialize_widening_literal);
instr("store " + scalar_lowir_type(type) + " " + init.text + ", $" + slot); } call_result_store_slot_.clear(); call_result_store_type_.reset(); call_result_store_consumed_ = false; } emit_pending_temp_cleanups(); } void FunctionLowerer::lower_local_static_decl(const Node& var) { program_.emit_global(var);
if (!local_static_needs_guard(var)) return; string guard = program_.ensure_local_static_guard(var.binding); string ready_block = fresh_block("local_static_ready");
string init_block = fresh_block("local_static_init"); string loaded = fresh_temp(); instr(loaded + " = load i64 @" + guard); string initialized = fresh_temp();
instr(initialized + " = cmp ne i64 " + loaded + ", 0"); terminate("branch " + initialized + ", ^" + ready_block + ", ^" + init_block); start_block(init_block);
lower_global_variable_init(var); instr("store i64 1, @" + guard);
if (var.binding->is_thread_local && type_needs_destructor(var.binding->type)) {
	program_.ensure_atexit_declaration();
	string fini = fresh_temp();
	instr(fini + " = addr @__cppgm_fini");
	string ignored = fresh_temp();
	instr(ignored + " = call i32 @__external_runtime_atexit(" + fini + ")");
}
terminate("jump ^" + ready_block); start_block(ready_block);
} void FunctionLowerer::register_cleanup(Binding* binding, TypePtr type) { if (cleanups_.empty() || binding == NULL)
return; TypePtr bare = pa11::strip_cv(type); if (bare->kind != TypeKind::Record && bare->kind != TypeKind::Array) return;
if (return_slot_variables_.find(binding) != return_slot_variables_.end())
return;
TypePtr cleanup_type = bare;
while (cleanup_type->kind == TypeKind::Array) cleanup_type = pa11::strip_cv(cleanup_type->base); if (cleanup_type->kind == TypeKind::Record) {
Binding* dtor = find_destructor(cleanup_type); if (dtor != NULL && dtor->is_noop_destructor && !dtor->is_generated_default_destructor)
{ if (program_.native_lowering) program_.demand_inline_function(dtor); } }
if (!type_needs_destructor(type)) return; program_.ensure_eh_declarations(); if (cleanup_type->kind == TypeKind::Record) {
Binding* dtor = find_destructor(cleanup_type); if (dtor != NULL && !dtor->is_noop_destructor) program_.demand_inline_function(dtor); }
cleanups_.back().push_back(Cleanup(binding, type)); active_unwind_dispatch_.clear(); } void FunctionLowerer::emit_scope_cleanups(vector<Cleanup>& scope)
{ for (size_t n = 0; n < scope.size(); ++n) { size_t i = scope.size() - 1 - n;
if (!scope[i].instruction.empty()) { instr(scope[i].instruction); continue;
} Binding* binding = scope[i].binding; TypePtr type = scope[i].type; string cleanup_addr = scope[i].addr;
function<Value()> addr_for = [this, binding, cleanup_addr]() { if (!cleanup_addr.empty()) return Value("ptr", cleanup_addr); return ensure_pointer(Value("ptr", "$" + slot_for(binding)));
}; if (scope[i].force_destructor_call) { TypePtr bare = pa11::strip_cv(type);
Binding* dtor = bare->kind == TypeKind::Record ? find_destructor(bare) : NULL; if (dtor != NULL) {
program_.demand_function_declaration(dtor); program_.demand_inline_function(dtor); Value target = addr_for(); string arg = target.text;
if (!arg.empty() && (arg[0] == '@' || arg[0] == '$')) { string tmp = fresh_temp(); instr(tmp + " = addr " + arg);
arg = tmp; } instr("call void @" + program_.symbol_for(dtor) + "(" + arg + ")");
continue; } } lower_scope_destructor_for_object(addr_for, type);
} } void FunctionLowerer::emit_all_cleanups() {
for (size_t n = 0; n < cleanups_.size(); ++n) { size_t i = cleanups_.size() - 1 - n; emit_scope_cleanups(cleanups_[i]);
	} } bool FunctionLowerer::has_active_cleanups() const {
	for (size_t i = 0; i < cleanups_.size(); ++i) for (size_t j = 0; j < cleanups_[i].size(); ++j) if (cleanups_[i][j].instruction.empty()) return true;
	return false; } void FunctionLowerer::emit_unwind_cleanups() {
	for (size_t n = 0; n < cleanups_.size(); ++n) { size_t i = cleanups_.size() - 1 - n; emit_scope_cleanups(cleanups_[i]);
	} } void FunctionLowerer::emit_active_catch_clause(const ActiveCatchContext& ctx) {
	if (ctx.catch_all) instr("eh_catch_all, " + to_string(ctx.selector));
	else instr("eh_catch @" + ctx.rtti + ", " + to_string(ctx.selector));
		} void FunctionLowerer::emit_active_catch_clauses() {
		if (active_catches_.empty()) return; string entry = active_catches_.back().entry;
		size_t first = active_catches_.size(); while (first > 0 && active_catches_[first - 1].entry == entry) --first;
		for (size_t i = first; i < active_catches_.size(); ++i) emit_active_catch_clause(active_catches_[i]);
		} void FunctionLowerer::terminate_unwind_or_active_catch() {
		if (!active_catches_.empty()) terminate("jump ^" + active_catches_.back().entry);
		else terminate("resume");
		} void FunctionLowerer::emit_unwind_object_cleanups() {
	for (size_t n = 0; n < cleanups_.size(); ++n) { size_t i = cleanups_.size() - 1 - n; vector<Cleanup> objects;
	for (size_t j = 0; j < cleanups_[i].size(); ++j) if (cleanups_[i][j].instruction.empty()) objects.push_back(cleanups_[i][j]);
	if (!objects.empty()) emit_scope_cleanups(objects); }
	} function<Value()> FunctionLowerer::global_storage_addr_for(const Node& var) {
const Node* var_ptr = &var; return [this, var_ptr]() { program_.demand_global_declaration(var_ptr->binding); string tmp = fresh_temp();
instr(tmp + " = addr @" + program_.symbol_for(var_ptr->binding)); return Value("ptr", tmp); }; }
function<Value()> FunctionLowerer::global_variable_addr_for(const Node& var) { const Node* var_ptr = &var; return [this, var_ptr]() {
program_.demand_global_declaration(var_ptr->binding); TypePtr bare = pa11::strip_cv(var_ptr->binding->type); if (var_ptr->binding->is_local_static || bare->kind == TypeKind::Record ||
bare->kind == TypeKind::Array) { string tmp = fresh_temp(); instr(tmp + " = addr @" + program_.symbol_for(var_ptr->binding));
return Value("ptr", tmp); } return Value("ptr", "@" + program_.symbol_for(var_ptr->binding)); };
} bool FunctionLowerer::lower_generated_aggregate_global_init(const Node& var, const Node& init) {
Binding* aggregate_ctor = NULL; if (starts_with(init.line, "braced-init-list")) { aggregate_ctor = init.direct_call;
if (aggregate_ctor == NULL) aggregate_ctor = find_constructor(var.binding->type, init.children.size()); }
else if (init.direct_call != NULL && init.direct_call->is_generated_aggregate_constructor) aggregate_ctor = init.direct_call; if (aggregate_ctor == NULL ||
!aggregate_ctor->is_generated_aggregate_constructor) return false; function<Value()> addr_for = global_storage_addr_for(var); if (var.binding->is_local_static)
(void)addr_for(); lower_aggregate_init(addr_for, var.binding->type, init); return true; }
bool FunctionLowerer::lower_constructor_action_global_init(const Node& var) { const Node& action = var.children[0]; if (!starts_with(action.line, "constructor-action"))
return false; if (!action.children.empty() && action.children[0].direct_call != NULL && no_op_generated_default_constructor(action.children[0].direct_call,
var.binding->type)) return true; if (!action.children.empty() && lower_generated_aggregate_global_init(var, action.children[0]))
return true; if (!action.children.empty()) emit_rvalue(action.children[0]); return true;
} bool FunctionLowerer::lower_function_pointer_global_init(const Node& var, const Node& init) {
Binding* fn = NULL; if (starts_with(init.line, "unary-expression") && init.has_op && init.op == OP_AMP &&
!init.children.empty() && init.children[0].binding != NULL && init.children[0].binding->kind == BindingKind::Function) fn = init.children[0].binding;
else if (starts_with(init.line, "id-expression") && init.binding != NULL && init.binding->kind == BindingKind::Function && pa11::strip_cv(var.binding->type)->kind == TypeKind::Pointer &&
pa11::strip_cv(var.binding->type)->base.get() != NULL && pa11::strip_cv(var.binding->type)->base->kind == TypeKind::Function) fn = init.binding; if (fn == NULL)
return false; if (fn->is_inline_definition) program_.demand_inline_function(fn); program_.demand_function_declaration(fn); string tmp = fresh_temp();
instr(tmp + " = addr @" + program_.symbol_for(fn)); program_.demand_global_declaration(var.binding); instr("store ptr " + tmp + ", @" + program_.symbol_for(var.binding)); return true;
} bool FunctionLowerer::lower_static_member_storage_global_init(const Node& var, const Node& init) {
if (var.binding == NULL || init.binding == NULL || !starts_with(init.line, "id-expression") || !init.binding->is_static_member)
return false; TypePtr target = strip_for_value(var.binding->type); TypePtr source = strip_for_value(init.binding->type); TypePtr target_bare = pa11::strip_cv(target);
TypePtr source_bare = pa11::strip_cv(source); if (target_bare->kind == TypeKind::Array || target_bare->kind == TypeKind::Record || source_bare->kind == TypeKind::Array ||
source_bare->kind == TypeKind::Record || is_reference(var.binding->type) || is_reference(init.binding->type)) return false;
string source_name = program_.symbol_for(init.binding); bool source_has_storage = program_.defined_globals.find(source_name) != program_.defined_globals.end() ||
program_.deferred_global_definitions.find(init.binding) != program_.deferred_global_definitions.end(); if (!source_has_storage) return false;
program_.demand_deferred_global_definition(init.binding); string type = scalar_lowir_type(var.binding->type); if (type != scalar_lowir_type(init.binding->type)) return false;
string tmp = fresh_temp(); instr(tmp + " = load " + type + " @" + source_name); program_.demand_global_declaration(var.binding); instr("store " + type + " " + tmp + ", @" +
program_.symbol_for(var.binding)); return true; } void FunctionLowerer::lower_local_static_array_global_init(
const function<Value()>& addr_for, TypePtr bare, const Node& init) {
Value addr = addr_for(); TypePtr elem = bare->base; uint64_t count = bare->unknown_bound ? init.children.size() : bare->bound; for (size_t i = 0; i < count; ++i)
{ Value elem_addr = direct_array_element_addr(addr, elem, i); function<Value()> elem_addr_for = [elem_addr]() { return elem_addr;
}; if (i >= init.children.size()) lower_zero_init(elem_addr_for, elem); else
lower_object_init(elem_addr_for, elem, init.children[i]); } } bool FunctionLowerer::lower_local_static_global_init(
const Node& var, const function<Value()>& addr_for, TypePtr bare, const Node& init)
	{ if (!var.binding->is_local_static) return false; if (bare->kind == TypeKind::Array &&
	is_string_literal_node(init)) { lower_string_array_init(addr_for, var.binding->type, init); return true;
	} if (bare->kind == TypeKind::Array &&
	starts_with(init.line, "braced-init-list")) { lower_local_static_array_global_init(addr_for, bare, init); return true;
} Value addr = addr_for(); if (bare->kind == TypeKind::Record && starts_with(init.line, "braced-init-list")) {
(void)addr; lower_object_init(addr_for, var.binding->type, init); } else
{ function<Value()> local_static_addr = [addr]() { return addr; };
lower_object_init(local_static_addr, var.binding->type, init); } return true; }
void FunctionLowerer::lower_global_variable_init(const Node& var) { if (!starts_with(var.line, "variable ") || var.binding == NULL || (var.children.empty() &&
(pa11::strip_cv(var.binding->type)->kind != TypeKind::Record || default_init_no_op(var.binding->type)))) return; if (var.children.empty())
{ Binding* ctor = find_constructor(var.binding->type, 0); if (ctor != NULL) {
function<Value()> addr_for = global_variable_addr_for(var); vector<const Node*> args; lower_constructor_call(addr_for, ctor, args); }
return; } const Node& init = var.children[0]; if (lower_constructor_action_global_init(var))
return; if (init.direct_call != NULL && no_op_generated_default_constructor(init.direct_call, var.binding->type)) return;
if (lower_generated_aggregate_global_init(var, init)) return; Binding* default_ctor = find_constructor(var.binding->type, 0); bool explicit_default_ctor =
default_ctor != NULL && !default_ctor->is_generated_default_constructor; if (!explicit_default_ctor && default_init_no_op(var.binding->type)) return;
if (lower_function_pointer_global_init(var, init)) return; function<Value()> addr_for = global_variable_addr_for(var); TypePtr bare = pa11::strip_cv(var.binding->type);
if (lower_static_member_storage_global_init(var, init)) return; if (lower_local_static_global_init(var, addr_for, bare, init)) return;
lower_object_init(addr_for, var.binding->type, init); } void FunctionLowerer::lower_thread_local_variable_init(const Node& node) {
if (node.children.empty() || node.token_text.empty()) return; string run_block = fresh_block("local_static_ctor_run"); string done_block = fresh_block("local_static_ctor_done");
string loaded = fresh_temp(); instr(loaded + " = load i64 @" + node.token_text); string initialized = fresh_temp(); instr(initialized + " = cmp ne i64 " + loaded + ", 0");
terminate("branch " + initialized + ", ^" + done_block + ", ^" + run_block); start_block(run_block); lower_global_variable_init(node.children[0]);
instr("store i64 1, @" + node.token_text); terminate("jump ^" + done_block); start_block(done_block); }
void FunctionLowerer::lower_global_variable_fini(const Node& var) { if (!starts_with(var.line, "variable ") || var.binding == NULL) return;
	if (var.binding->is_local_static && local_static_needs_guard(var)) {
		string guard = program_.ensure_local_static_guard(var.binding);
		string destroy_block = fresh_block("local_static_fini_run");
		string done_block = fresh_block("local_static_fini_done");
		string loaded = fresh_temp(); instr(loaded + " = load i64 @" + guard);
		string initialized = fresh_temp(); instr(initialized + " = cmp ne i64 " + loaded + ", 0");
		terminate("branch " + initialized + ", ^" + destroy_block + ", ^" + done_block);
		start_block(destroy_block);
		function<Value()> local_addr_for = [this, &var]() { program_.demand_global_declaration(var.binding); return Value("ptr", "@" + program_.symbol_for(var.binding)); };
		lower_destructor_for_object(local_addr_for, var.binding->type);
		instr("store i64 0, @" + guard);
		terminate("jump ^" + done_block);
		start_block(done_block);
		return;
	}
function<Value()> addr_for = [this, &var]() { program_.demand_global_declaration(var.binding); return Value("ptr", "@" + program_.symbol_for(var.binding)); };
lower_destructor_for_object(addr_for, var.binding->type); } void FunctionLowerer::lower_destructor_for_object( const function<Value()>& addr_for,
TypePtr type) { TypePtr bare = pa11::strip_cv(type); if (bare->kind == TypeKind::Array)
{ TypePtr elem = bare->base; uint64_t count = bare->unknown_bound ? 0 : bare->bound; for (uint64_t n = 0; n < count; ++n)
{ uint64_t i = count - 1 - n; function<Value()> elem_addr = [this, addr_for, elem, i]() { Value base = addr_for();
string decay = fresh_temp(); instr(decay + " = unary decay ptr " + base.text); string scaled = to_string(i); if (pa11::type_size(elem) != 1)
{ scaled = fresh_temp(); instr(scaled + " = binary mul i64 " + to_string(i) + ", " + to_string(pa11::type_size(elem)));
} string addr = fresh_temp(); instr(addr + " = index i8 [projection=array_element] " + decay + ", " + scaled);
return Value("ptr", addr); }; lower_destructor_for_object(elem_addr, elem); }
return; } if (bare->kind != TypeKind::Record) return;
Binding* dtor = find_destructor(bare); if (dtor != NULL && (dtor->is_virtual || !dtor->is_noop_destructor)) {
if (!inline_empty_nonvirtual_destructor_body(program_, dtor)) { program_.demand_function_declaration(dtor);
program_.demand_inline_function(dtor); Value target = addr_for(); string arg = target.text; if (!arg.empty() && (arg[0] == '@' || arg[0] == '$'))
{ string tmp = fresh_temp(); instr(tmp + " = addr " + arg); arg = tmp;
} instr("call void @" + program_.symbol_for(dtor) + "(" + arg + ")"); return; }
} pa11::layout_record_type(bare); for (size_t n = 0; n < bare->fields.size(); ++n) {
size_t i = bare->fields.size() - 1 - n; Binding* field = bare->fields[i]; function<Value()> field_addr = [this, addr_for, field]() { Value base = addr_for();
string addr = fresh_temp(); instr(addr + " = index i8 [projection=field] " + base.text + ", " + to_string(field->member_offset)); return Value("ptr", addr);
	}; lower_destructor_for_object(field_addr, field->type); } vector<TypePtr> bases = pa11::record_direct_bases(bare);
	for (size_t n = 0; n < bases.size(); ++n) { size_t i = bases.size() - 1 - n; TypePtr direct_base = bases[i];
	function<Value()> base_addr = [this, addr_for, bare, direct_base]() { Value base = addr_for(); return emit_base_subobject_addr(base, bare, direct_base);
	}; lower_destructor_for_object(base_addr, direct_base); } }
void FunctionLowerer::lower_scope_destructor_for_object( const function<Value()>& addr_for, TypePtr type) {
TypePtr bare = pa11::strip_cv(type); if (bare->kind != TypeKind::Array) { lower_destructor_for_object(addr_for, type);
return; } TypePtr elem = bare->base; uint64_t count = bare->unknown_bound ? 0 : bare->bound;
for (uint64_t i = 0; i < count; ++i) { function<Value()> elem_addr = [this, addr_for, elem, i]() { Value base = addr_for();
string decay = fresh_temp(); instr(decay + " = unary decay ptr " + base.text); string scaled = to_string(i); if (pa11::type_size(elem) != 1)
{ scaled = fresh_temp(); instr(scaled + " = binary mul i64 " + to_string(i) + ", " + to_string(pa11::type_size(elem)));
} string addr = fresh_temp(); instr(addr + " = index i8 [projection=array_element] " + decay + ", " + scaled);
return Value("ptr", addr); }; lower_destructor_for_object(elem_addr, elem); }
} void FunctionLowerer::lower_member_fini(const Node& node) { if (node.binding == NULL)
return; function<Value()> member_addr = [this, &node]() { string this_ptr = fresh_temp(); instr(this_ptr + " = load ptr $this");
string addr = fresh_temp(); instr(addr + " = index i8 [projection=field] " + this_ptr + ", " + to_string(node.binding->member_offset)); return Value("ptr", addr);
}; lower_destructor_for_object(member_addr, node.binding->type); } void FunctionLowerer::lower_base_fini(const Node& node)
{ if (node.type.get() == NULL) return; TypePtr source = class_record_for_member(fn_.binding);
function<Value()> base_addr = [this, source, &node]() { string this_ptr = fresh_temp(); instr(this_ptr + " = load ptr $this"); string addr = fresh_temp(); instr(addr + " = index i8 [projection=base_subobject] " + this_ptr + ", " + to_string(base_subobject_offset(source, node.type))); return Value("ptr", addr); }; Binding* dtor = find_destructor(node.type);
	if (dtor != NULL && dtor->is_virtual) { program_.demand_function_declaration(dtor); string callee = program_.destructor_symbol_for(dtor, true);
	program_.demand_inline_function(dtor, false); program_.demand_lifecycle_base_entry_declaration(dtor); Value target = base_addr(); vector<string> args; args.push_back(target.text);
	bool hosted_external_stream_base =
		record_uses_hosted_external_stream_vtable(node.type);
	if (!program_.native_lowering || hosted_external_stream_base) {
		TypePtr current = source.get() != NULL ? pa11::strip_cv(source) : TypePtr();
		TypePtr base = node.type.get() != NULL ? pa11::strip_cv(node.type) : TypePtr();
		if (current.get() != NULL && current->kind == TypeKind::Record &&
		    base.get() != NULL && base->kind == TypeKind::Record &&
		    base->is_polymorphic && record_uses_virtual_base_vtt(base)) {
			size_t vtt_slot = construction_vtt_slot_for_direct_base(current, base);
			if (vtt_slot != static_cast<size_t>(-1)) {
				string vtt_arg;
				if (destructor_base_entry_) {
					vtt_arg = "%__vtt";
					if (vtt_slot != 0) {
						vtt_arg = fresh_temp();
						instr(vtt_arg + " = index i8 %__vtt, " +
						      to_string(vtt_slot * 8));
					}
				} else {
					string vtt_base = fresh_temp();
					instr(vtt_base + " = addr @" + vtt_symbol_for_record(current));
					vtt_arg = vtt_base;
					if (vtt_slot != 0) {
						vtt_arg = fresh_temp();
						instr(vtt_arg + " = index i8 " + vtt_base + ", " +
						      to_string(vtt_slot * 8));
					}
				}
				args.push_back(vtt_arg);
			}
			if (!hosted_external_stream_base) {
				vector<TypePtr> vbases = hidden_virtual_bases_for_record(base);
				vector<TypePtr> current_vbases = hidden_virtual_bases_for_record(current);
				for (size_t v = 0; v < vbases.size(); ++v) {
					string hidden;
					if (destructor_base_entry_) {
						for (size_t cv = 0; cv < current_vbases.size(); ++cv)
							if (pa11::same_type(pa11::strip_cv(current_vbases[cv]),
							                    pa11::strip_cv(vbases[v]))) {
								hidden = "%__vbptr" + to_string(cv);
								break;
							}
					}
					if (hidden.empty() && record_has_base_subobject(current, vbases[v])) {
						string this_ptr = fresh_temp();
						instr(this_ptr + " = load ptr $this");
						uint64_t offset = base_subobject_offset(current, vbases[v]);
						if (offset == 0)
							hidden = this_ptr;
						else {
							hidden = fresh_temp();
							instr(hidden + " = index i8 " + this_ptr + ", " +
							      to_string(offset));
						}
					}
					if (hidden.empty())
						hidden = "0";
					args.push_back(hidden);
				}
			}
		}
	}
	ostringstream call; call << "call void @" << callee << "("; for (size_t i = 0; i < args.size(); ++i) { if (i != 0) call << ", "; call << args[i]; } call << ")"; instr(call.str()); return;
	} lower_destructor_for_object(base_addr, node.type); }
}  // namespace internal
}  // namespace pa14
