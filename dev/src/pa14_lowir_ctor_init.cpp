#include "pa14_lowir_internal.h"
namespace pa14 { namespace internal { namespace { void demand_record_return_calls(ProgramLowerer& program, const Node& node)
{ if (starts_with(node.line, "call-expression") && node.direct_call != NULL && pa11::strip_cv(node.type)->kind == TypeKind::Record)
{ program.demand_function_declaration(node.direct_call); program.demand_inline_function(node.direct_call); }
for (size_t i = 0; i < node.children.size(); ++i) demand_record_return_calls(program, node.children[i]); } bool trivial_lvalue_projection(const Node& node)
{ if (starts_with(node.line, "id-expression")) return true; if (starts_with(node.line, "cast-expression xvalue") &&
node.children.size() == 1) return trivial_lvalue_projection(node.children[0]); if (!starts_with(node.line, "member-expression")) return false;
for (size_t i = 0; i < node.children.size(); ++i) if (!trivial_lvalue_projection(node.children[i])) return false; return true;
}
}  // namespace
void FunctionLowerer::emit_temporary_cleanups( const vector<pair<Value, TypePtr> >& temps) { for (size_t n = 0; n < temps.size(); ++n)
{ size_t i = temps.size() - 1 - n; Value addr = temps[i].first; TypePtr type = temps[i].second;
function<Value()> addr_for = [addr]() { return addr; }; lower_destructor_for_object(addr_for, type);
} } void FunctionLowerer::add_pending_temp_cleanup(Value addr, TypePtr type) {
pending_temp_cleanups_.push_back(make_pair(addr, type)); } bool FunctionLowerer::has_pending_temp_cleanups() const {
return !pending_temp_cleanups_.empty(); } bool FunctionLowerer::node_may_create_temp_cleanup(const Node& node) const {
if (starts_with(node.line, "braced-init-list")) return true; TypePtr object = object_type(node.type); if (node.category == ValueCategory::PRValue &&
pa11::strip_cv(object)->kind == TypeKind::Record && type_needs_cleanup(object)) return true; for (size_t i = 0; i < node.children.size(); ++i)
if (node_may_create_temp_cleanup(node.children[i])) return true; return false; }
bool FunctionLowerer::type_needs_cleanup(TypePtr type) const { return type_needs_destructor(type); }
void FunctionLowerer::emit_pending_temp_cleanups() { vector<pair<Value, TypePtr> > temps; temps.swap(pending_temp_cleanups_);
emit_temporary_cleanups(temps); } void FunctionLowerer::terminate_with_pending_temp_cleanups( const string& cond,
const string& yes, const string& no) { if (pending_temp_cleanups_.empty())
{ terminate("branch " + cond + ", ^" + yes + ", ^" + no); return; }
vector<pair<Value, TypePtr> > temps; temps.swap(pending_temp_cleanups_); string yes_cleanup = fresh_block("cond_true_cleanup"); string no_cleanup = fresh_block("cond_false_cleanup");
terminate("branch " + cond + ", ^" + yes_cleanup + ", ^" + no_cleanup); start_block(yes_cleanup); emit_temporary_cleanups(temps); terminate("jump ^" + yes);
start_block(no_cleanup); emit_temporary_cleanups(temps); terminate("jump ^" + no); }
void FunctionLowerer::lower_temporary_init_with_unwind( const function<Value()>& addr_for, TypePtr type, const Node& init)
{ if (!type_needs_destructor(type)) { lower_object_init(addr_for, type, init);
return; } if (eh_try_depth_ > 0) {
lower_object_init(addr_for, type, init); return; } if (has_active_cleanups() && !active_unwind_dispatch_.empty())
{ instr("eh_try ^" + active_unwind_dispatch_); ++eh_try_depth_; lower_object_init(addr_for, type, init);
--eh_try_depth_; instr("eh_end"); return; }
string dispatch = fresh_block("call_unwind_dispatch"); string end = fresh_block("call_unwind_end"); if (has_active_cleanups()) active_unwind_dispatch_ = dispatch;
instr("eh_try ^" + dispatch); ++eh_try_depth_; lower_object_init(addr_for, type, init); --eh_try_depth_;
instr("eh_end"); terminate("jump ^" + end); start_block(dispatch); emit_unwind_cleanups();
terminate("resume"); start_block(end); } void FunctionLowerer::lower_record_reference_constructor_argument(
const Node& arg, TypePtr param, vector<string>& lowered, vector<pair<Value, TypePtr> >& temp_cleanups,
vector<PendingConstructorConversion>& pending_conversions, bool force_refcall_slot) { TypePtr object = pa11::strip_cv(object_type(arg.type));
TypePtr target = pa11::strip_cv(param->base); const Node* materialized = record_prvalue_child_for_xvalue(arg); bool indirect_call_result = (force_refcall_slot &&
starts_with(arg.line, "call-expression") && record_return_by_address(arg.type)) || (materialized != NULL && starts_with(materialized->line, "call-expression") &&
record_return_by_address(materialized->type)); string prefix = indirect_call_result ? "refcall" : (pa11::same_type(object, target) ? "arg" : "tmpobj");
string slot = fresh_aux_slot(prefix, scalar_lowir_type(object)); string addr_name = fresh_temp(); Value temp_addr("ptr", addr_name); shared_ptr<bool> emitted(new bool(false));
function<Value()> temp_addr_for = [this, slot, temp_addr, emitted]() { if (!*emitted) { *emitted = true;
instr(temp_addr.text + " = addr $" + slot); } return temp_addr; };
bool guard_generated_base_temp = arg.direct_call != NULL && arg.direct_call->is_generated_default_constructor && object->base.get() != NULL;
if (guard_generated_base_temp) lower_temporary_init_with_unwind(temp_addr_for, object, arg); else lower_object_init(temp_addr_for, object, arg);
if (type_needs_destructor(object)) { temp_cleanups.push_back(make_pair(temp_addr, object)); PendingConstructorConversion pending;
pending.index = lowered.size(); pending.value = temp_addr; pending.from = pa11::make_pointer(object); pending.to = pa11::make_pointer(param->base);
pending_conversions.push_back(pending); lowered.push_back(temp_addr.text); return; }
lowered.push_back(convert_value(temp_addr, pa11::make_pointer(object), pa11::make_pointer(param->base)).text); }
void FunctionLowerer::emit_constructor_call_with_cleanups( Binding* ctor, vector<string>& lowered, const vector<pair<Value, TypePtr> >& temp_cleanups,
const vector<PendingConstructorConversion>& pending_conversions, bool base_entry) { if (!(base_entry && ctor->is_inline_definition))
program_.demand_function_declaration(ctor); string callee = program_.constructor_symbol_for(ctor, base_entry); program_.demand_inline_function(ctor, !base_entry); function<string()> call_text = [callee, &lowered]() {
ostringstream call; call << "call void @" << callee << "("; for (size_t i = 0; i < lowered.size(); ++i) {
if (i != 0) call << ", "; call << lowered[i]; }
call << ")"; return call.str(); }; if (temp_cleanups.empty())
{ for (size_t i = 0; i < pending_conversions.size(); ++i) lowered[pending_conversions[i].index] = convert_value(pending_conversions[i].value,
pending_conversions[i].from, pending_conversions[i].to).text; if (eh_try_depth_ == 0 && has_active_cleanups() &&
!lowering_record_return_object_) { string dispatch = active_unwind_dispatch_.empty() ? fresh_block("call_unwind_dispatch")
: active_unwind_dispatch_; bool define_dispatch = active_unwind_dispatch_.empty(); instr("eh_try ^" + dispatch); ++eh_try_depth_;
instr(call_text()); --eh_try_depth_; instr("eh_end"); if (!define_dispatch)
return; string end = fresh_block("call_unwind_end"); terminate("jump ^" + end); active_unwind_dispatch_ = dispatch;
start_block(dispatch); emit_unwind_cleanups(); terminate("resume"); start_block(end);
return; } instr(call_text()); return;
} string dispatch = fresh_block("call_unwind_dispatch"); string end = fresh_block("call_unwind_end"); instr("eh_try ^" + dispatch);
++eh_try_depth_; for (size_t i = 0; i < pending_conversions.size(); ++i) lowered[pending_conversions[i].index] = convert_value(pending_conversions[i].value,
pending_conversions[i].from, pending_conversions[i].to).text; instr(call_text()); emit_temporary_cleanups(temp_cleanups);
--eh_try_depth_; instr("eh_end"); terminate("jump ^" + end); start_block(dispatch);
emit_temporary_cleanups(temp_cleanups); terminate("resume"); start_block(end); }
void FunctionLowerer::lower_constructor_call(const function<Value()>& addr_for, Binding* ctor, const vector<const Node*>& args, bool base_entry)
{ if (ctor == NULL) throw runtime_error("missing constructor"); if (args.size() == 1 && ctor->type.get() != NULL &&
ctor->type->kind == TypeKind::Function && ctor->type->parameters.size() == 2 && is_reference(ctor->type->parameters[1]) && pa11::strip_cv(ctor->type->parameters[1]->base)->kind == TypeKind::Record &&
!defaulted_copy_move_constructor_needs_helper(ctor, ctor->type->parameters[1]->base) && !record_has_storage_copy(ctor->type->parameters[1]->base)) {
const Node& arg = *args[0]; TypePtr src_record = pa11::strip_cv(object_type(arg.type)); TypePtr dst_record = pa11::strip_cv(ctor->type->parameters[1]->base); TypePtr constructed_record = class_record_for_member(ctor);
constructed_record = constructed_record.get() != NULL ? pa11::strip_cv(constructed_record) : TypePtr(); bool glvalue_arg = arg.category == ValueCategory::LValue || arg.category == ValueCategory::XValue ||
starts_with(arg.line, "cast-expression xvalue") || starts_with(arg.line, "id-expression xvalue") || starts_with(arg.line, "member-expression xvalue"); if (src_record->kind == TypeKind::Record &&
dst_record->kind == TypeKind::Record && constructed_record.get() != NULL && constructed_record->kind == TypeKind::Record && pa11::same_type(constructed_record, dst_record) &&
pa11::same_type(src_record, dst_record) && glvalue_arg) { addr_for();
bool reference_parameter_id = starts_with(arg.line, "id-expression") && arg.binding != NULL && arg.binding->kind == BindingKind::Parameter &&
is_reference(arg.binding->type); if (!reference_parameter_id && !trivial_lvalue_projection(arg)) ensure_pointer(emit_lvalue_addr(arg));
return; } } if (binding_has_template_specialization_context(ctor))
{ if (!(base_entry && ctor->is_inline_definition)) program_.demand_function_declaration(ctor); program_.constructor_symbol_for(ctor, base_entry);
program_.demand_inline_function(ctor, !base_entry); } for (size_t i = 0; i < args.size(); ++i) demand_record_return_calls(program_, *args[i]);
vector<string> lowered; vector<pair<Value, TypePtr> > temp_cleanups; vector<PendingConstructorConversion> pending_conversions; bool protect_reference_argument_setup =
eh_try_depth_ == 0 && has_active_cleanups() && !lowering_record_return_object_ && !args.empty();
if (protect_reference_argument_setup) { for (size_t i = 0; i < args.size(); ++i) {
TypePtr param = ctor->type->parameters[i + 1]; const Node& arg = *args[i]; bool glvalue_arg = arg.category == ValueCategory::LValue ||
arg.category == ValueCategory::XValue || starts_with(arg.line, "cast-expression xvalue") || starts_with(arg.line, "id-expression xvalue") || starts_with(arg.line, "member-expression xvalue");
if (!is_reference(param) || !glvalue_arg || record_prvalue_child_for_xvalue(arg) != NULL) {
protect_reference_argument_setup = false; break; } }
} string protected_dispatch; string protected_end; bool protected_define_dispatch = false;
vector<string> prelowered_reference_args(args.size()); Value destination_addr; if (protect_reference_argument_setup && constructor_destination_before_protected_try_)
destination_addr = addr_for(); if (protect_reference_argument_setup) { for (size_t i = 0; i < args.size(); ++i)
{ TypePtr param = ctor->type->parameters[i + 1]; const Node& arg = *args[i]; bool reference_parameter_id =
starts_with(arg.line, "id-expression") && arg.binding != NULL && arg.binding->kind == BindingKind::Parameter && is_reference(arg.binding->type);
bool top_level_trivial_arg = constructor_destination_before_protected_try_ && trivial_lvalue_projection(arg); if (!reference_parameter_id && !top_level_trivial_arg)
continue; Value addr = ensure_pointer(emit_lvalue_addr(arg)); TypePtr from_ptr = pa11::make_pointer(object_type(arg.type)); TypePtr to_ptr = pa11::make_pointer(param->base);
prelowered_reference_args[i] = convert_value(addr, from_ptr, to_ptr).text; } }
if (protect_reference_argument_setup) { protected_dispatch = active_unwind_dispatch_.empty() ? fresh_block("call_unwind_dispatch")
: active_unwind_dispatch_; protected_define_dispatch = active_unwind_dispatch_.empty(); instr("eh_try ^" + protected_dispatch); ++eh_try_depth_;
} if (destination_addr.text.empty()) destination_addr = addr_for(); lowered.push_back(destination_addr.text);
for (size_t i = 0; i < args.size(); ++i) { TypePtr param = ctor->type->parameters[i + 1]; const Node& arg = *args[i];
if (is_reference(param)) { if (!prelowered_reference_args[i].empty()) {
lowered.push_back(prelowered_reference_args[i]); continue; } const Node* materialized = record_prvalue_child_for_xvalue(arg);
bool glvalue_arg = arg.category == ValueCategory::LValue || arg.category == ValueCategory::XValue || starts_with(arg.line, "cast-expression xvalue") ||
starts_with(arg.line, "id-expression xvalue") || starts_with(arg.line, "member-expression xvalue"); if (materialized != NULL && pa11::strip_cv(param->base)->kind == TypeKind::Record)
lower_record_reference_constructor_argument( *materialized, param, lowered, temp_cleanups, pending_conversions, true); else if (glvalue_arg)
{ Value addr = ensure_pointer(emit_lvalue_addr(arg)); TypePtr from_ptr = pa11::make_pointer(object_type(arg.type)); TypePtr to_ptr = pa11::make_pointer(param->base);
lowered.push_back(convert_value(addr, from_ptr, to_ptr).text); } else if (pa11::strip_cv(param->base)->kind == TypeKind::Record && pa11::strip_cv(object_type(arg.type))->kind == TypeKind::Record)
lower_record_reference_constructor_argument( arg, param, lowered, temp_cleanups, pending_conversions); else {
string slot = fresh_aux_slot("refarg", scalar_lowir_type(param->base)); Value raw = arg.binding != NULL && arg.binding->kind == BindingKind::Function
? ensure_pointer(emit_lvalue_addr(arg)) : emit_rvalue(arg); Value value = convert_value(raw, arg.type, param->base); instr("store " + scalar_lowir_type(param->base) + " " +
value.text + ", $" + slot); string addr = fresh_temp(); instr(addr + " = addr $" + slot); lowered.push_back(addr);
} } else {
if (pa11::strip_cv(param)->kind == TypeKind::Record) { bool by_address = record_pass_by_address(param); string slot = fresh_aux_slot(by_address ? "arg" : "argobj",
slot_lowir_type(param)); string addr_name = fresh_temp(); instr(addr_name + " = addr $" + slot); Value target_addr("ptr", addr_name);
function<Value()> arg_addr = [target_addr]() { return target_addr; }; lower_object_init(arg_addr, param, arg);
lowered.push_back(by_address ? target_addr.text : "$" + slot); } else lowered.push_back(
convert_binary_value(emit_rvalue(arg), arg.type, param).text); } } emit_constructor_call_with_cleanups(
ctor, lowered, temp_cleanups, pending_conversions, base_entry); if (protect_reference_argument_setup) { --eh_try_depth_;
instr("eh_end"); if (protected_define_dispatch) { protected_end = fresh_block("call_unwind_end");
terminate("jump ^" + protected_end); active_unwind_dispatch_ = protected_dispatch; start_block(protected_dispatch); emit_unwind_cleanups();
terminate("resume"); start_block(protected_end); } }
} bool FunctionLowerer::lower_string_array_init(const function<Value()>& addr_for, TypePtr type, const Node& init)
{ TypePtr bare = pa11::strip_cv(type); if (bare->kind != TypeKind::Array || !is_string_literal_node(init)) return false;
TypePtr elem = pa11::strip_cv(bare->base); if (elem->kind != TypeKind::Fundamental) return false; StringLiteralInfo info;
if (!AnalyzeStringLiteral(init.token_text, info) || !info.ud_suffix.empty()) return false; uint64_t elem_size = pa11::type_size(elem); if (elem_size == 0 || elem_size > 8 || elem->fundamental != info.type)
return false; uint64_t count = bare->unknown_bound ? info.elements : bare->bound; if (elem_size == 1) {
if (!lowering_array_subobject_init_) { Value base = addr_for(); for (size_t i = 0; i < count; ++i)
{ string addr = base.text; if (i != 0) {
addr = fresh_temp(); instr(addr + " = index i8 " + base.text + ", " + to_string(i)); }
uint64_t value = i < info.bytes.size() ? info.bytes[i] : 0; instr("store " + scalar_lowir_type(bare->base) + " " + to_string(value) + ", " + addr); }
return true; } for (size_t i = 0; i < count; ++i) {
Value base = addr_for(); string decay = fresh_temp(); instr(decay + " = unary decay ptr " + base.text); string addr = fresh_temp();
instr(addr + " = index " + scalar_lowir_type(bare->base) + " " + decay + ", " + to_string(i)); uint64_t value = i < info.bytes.size() ? info.bytes[i] : 0; instr("store " + scalar_lowir_type(bare->base) + " " +
to_string(value) + ", " + addr); } return true; }
Value base = addr_for(); for (size_t i = 0; i < count; ++i) { string addr = base.text;
uint64_t byte_offset = i * elem_size; if (byte_offset != 0) { addr = fresh_temp();
instr(addr + " = index i8 " + base.text + ", " + to_string(byte_offset)); } uint64_t value = 0;
size_t offset = byte_offset; for (size_t b = 0; b < elem_size && offset + b < info.bytes.size(); ++b) value |= uint64_t(info.bytes[offset + b]) << (8 * b); instr("store " + scalar_lowir_type(bare->base) + " " +
to_string(value) + ", " + addr); } return true; }
void FunctionLowerer::lower_base_init(const Node& node) { if (node.type.get() == NULL) return; TypePtr source = class_record_for_member(fn_.binding); function<Value()> base_addr = [this, source, &node]() { string this_ptr = fresh_temp(); instr(this_ptr + " = load ptr $this"); return emit_base_subobject_addr(Value("ptr", this_ptr), source, node.type); }; if (node.children.empty()) { if (node.direct_call != NULL) { if (no_op_generated_default_constructor(node.direct_call, node.type)) return; vector<const Node*> args; lower_constructor_call(base_addr, node.direct_call, args, true); return; } lower_zero_init(base_addr, node.type); } else { const Node& init = node.children[0]; Binding* ctor = node.direct_call;
if (ctor == NULL) ctor = init.direct_call; if (ctor != NULL && ctor->type.get() != NULL && ctor->type->kind == TypeKind::Function) { if (no_op_generated_default_constructor(ctor, node.type)) { return; } const Node& copy_source = starts_with(init.line, "braced-init-list") && init.children.size() == 1 ? init.children[0] : init; TypePtr src_record = pa11::strip_cv(object_type(copy_source.type)); TypePtr dst_record = pa11::strip_cv(node.type); bool structural_copy_move_ctor = ctor->type->parameters.size() == 2 && is_reference(ctor->type->parameters[1]) && pa11::same_type(pa11::strip_cv(ctor->type->parameters[1]->base), dst_record); if (structural_copy_move_ctor && !defaulted_copy_move_constructor_needs_helper(ctor, node.type) && !record_has_storage_copy(node.type) &&
src_record->kind == TypeKind::Record && dst_record->kind == TypeKind::Record && (pa11::same_type(src_record, dst_record) || record_has_base(src_record, dst_record)) && (copy_source.category == ValueCategory::LValue || copy_source.category == ValueCategory::XValue)) { base_addr(); return; } if ((ctor->is_defaulted || ctor->is_generated_copy_move_constructor) && ctor->is_inline_definition && !defaulted_copy_move_constructor_needs_helper(ctor, node.type) && record_has_storage_copy(node.type) && src_record->kind == TypeKind::Record && dst_record->kind == TypeKind::Record && (pa11::same_type(src_record, dst_record) || record_has_base(src_record, dst_record)) && (copy_source.category == ValueCategory::LValue || copy_source.category == ValueCategory::XValue)) { Value target = base_addr();
Value source = ensure_pointer(emit_lvalue_addr(copy_source)); Value converted = convert_value(source, pa11::make_pointer(src_record), pa11::make_pointer(node.type)); instr("copyobj " + to_string(pa11::type_size(node.type)) + "x" + to_string(pa11::type_align(node.type)) + " " + converted.text + ", " + target.text); return; } vector<const Node*> args; if (starts_with(init.line, "braced-init-list")) for (size_t i = 0; i < init.children.size(); ++i) args.push_back(&init.children[i]); else args.push_back(&init); TypePtr inherited_base = node.type.get() != NULL ? pa11::strip_cv(node.type) : TypePtr(); bool function_template_ctor = ctor->function_specialization_symbol.size() != 0 || (ctor->aliased_binding != NULL &&
ctor->aliased_binding->function_specialization_symbol.size() != 0); if (node.token_text == "inherited-constructor" && inherited_base.get() != NULL && record_is_template_specialization(inherited_base) && !function_template_ctor) program_.demand_inline_function(ctor); lower_constructor_call(base_addr, ctor, args, true); return; } TypePtr src_record = pa11::strip_cv(object_type(init.type)); TypePtr dst_record = pa11::strip_cv(node.type); if (src_record->kind == TypeKind::Record && dst_record->kind == TypeKind::Record && pa11::same_type(src_record, dst_record) && (init.category == ValueCategory::LValue || init.category == ValueCategory::XValue)) { Binding* copy_move = find_copy_move_constructor(node.type, init.category == ValueCategory::XValue); if (copy_move == NULL && init.category == ValueCategory::XValue)
copy_move = find_copy_move_constructor(node.type, false); if (copy_move != NULL) { vector<const Node*> args; args.push_back(&init); lower_constructor_call(base_addr, copy_move, args, true); return; } } lower_object_init(base_addr, node.type, node.children[0]); } } void FunctionLowerer::lower_delegating_init(const Node& node) {
Binding* ctor = node.direct_call; const Node* init = NULL; if (ctor == NULL && !node.children.empty()) ctor = node.children[0].direct_call;
if (!node.children.empty()) init = &node.children[0]; if (ctor == NULL) throw runtime_error("missing delegating constructor");
function<Value()> this_addr = [this]() { string this_ptr = fresh_temp(); instr(this_ptr + " = load ptr $this"); return Value("ptr", this_ptr);
}; vector<const Node*> args; if (init != NULL) for (size_t i = 0; i < init->children.size(); ++i)
args.push_back(&init->children[i]); lower_constructor_call(this_addr, ctor, args); } void FunctionLowerer::lower_storage_copy_action(const Node& node)
{ if (!node.has_constant_value || node.constant_value == 0 || node.children.empty()) return;
string self = fresh_temp(); instr(self + " = load ptr $this"); Value source = ensure_pointer(emit_lvalue_addr(node.children[0])); instr("copyobj " + to_string(node.constant_value) + "x" +
to_string(pa11::type_align(node.type)) + " " + source.text + ", " + self); } void FunctionLowerer::lower_member_init(const Node& node)
{ if (node.binding == NULL) return; function<Value()> member_addr = [this, &node]() {
string this_ptr = fresh_temp(); instr(this_ptr + " = load ptr $this"); string addr = fresh_temp(); instr(addr + " = index i8 [projection=field] " + this_ptr +
", " + to_string(node.binding->member_offset)); return Value("ptr", addr); }; if (!node.children.empty() &&
starts_with(node.children[0].line, "braced-init-list")) { if (node.direct_call != NULL) {
if (pa11::strip_cv(node.binding->type)->kind != TypeKind::Record) { lower_object_init(member_addr,
node.binding->type, node.children[0]); return; }
if (no_op_generated_default_constructor(node.direct_call, node.binding->type)) return; if (node.direct_call->is_generated_default_constructor &&
node.direct_call->unwind_no && pa11::strip_cv(node.binding->type)->kind == TypeKind::Record && pa11::strip_cv(node.binding->type)->base.get() != NULL) {
Value addr = member_addr(); if (zero_init_has_store(node.binding->type)) lower_storage_zero(addr, pa11::type_size(node.binding->type));
return; } Value addr = member_addr(); if (node.direct_call->is_generated_default_constructor)
lower_storage_zero(addr, pa11::type_size(node.binding->type)); function<Value()> same_addr = [addr]() { return addr; };
vector<const Node*> args; for (size_t i = 0; i < node.children[0].children.size(); ++i) args.push_back(&node.children[0].children[i]); lower_constructor_call(same_addr, node.direct_call, args);
return; } if (node.children[0].direct_call != NULL && node.children[0].direct_call->is_generated_default_constructor &&
node.children[0].direct_call->unwind_no && pa11::strip_cv(node.binding->type)->kind == TypeKind::Record && pa11::strip_cv(node.binding->type)->base.get() != NULL) {
Value addr = member_addr(); if (zero_init_has_store(node.binding->type)) lower_storage_zero(addr, pa11::type_size(node.binding->type)); return;
} lower_object_init(member_addr, node.binding->type, node.children[0]); return; }
if (node.direct_call != NULL) { if (lower_direct_member_constructor_init(node, member_addr)) return;
return; } if (node.children.empty()) {
if (pa11::strip_cv(node.binding->type)->kind == TypeKind::Array) lower_default_init(member_addr, node.binding->type); return; }
if (pa11::strip_cv(node.binding->type)->kind == TypeKind::Record) { if (!record_has_storage_copy(node.binding->type) && node.children.size() == 1)
{ TypePtr src_record = pa11::strip_cv(object_type(node.children[0].type)); TypePtr dst_record = pa11::strip_cv(node.binding->type);
Binding* copy_move = NULL; if (node.children[0].category == ValueCategory::LValue || node.children[0].category == ValueCategory::XValue) {
copy_move = find_copy_move_constructor( node.binding->type, node.children[0].category == ValueCategory::XValue); if (copy_move == NULL &&
node.children[0].category == ValueCategory::XValue) copy_move = find_copy_move_constructor( node.binding->type, false); }
if (src_record->kind == TypeKind::Record && dst_record->kind == TypeKind::Record && pa11::same_type(src_record, dst_record) && (node.children[0].category == ValueCategory::LValue ||
node.children[0].category == ValueCategory::XValue) && copy_move == NULL) { member_addr();
return; } } lower_object_init(member_addr, node.binding->type, node.children[0]);
return; } if (is_reference(node.binding->type)) {
Value target = ensure_pointer(emit_lvalue_addr(node.children[0])); instr("store ptr " + target.text + ", " + member_addr().text); } else
lower_scalar_member_init(node, member_addr); } bool FunctionLowerer::lower_direct_member_constructor_init( const Node& node,
const function<Value()>& member_addr) { if (node.direct_call->type.get() == NULL || node.direct_call->type->kind != TypeKind::Function ||
node.direct_call->type->parameters.empty()) { if (!node.children.empty()) lower_object_init(member_addr, node.binding->type, node.children[0]);
else lower_default_init(member_addr, node.binding->type); return true; }
if (no_op_generated_default_constructor(node.direct_call, node.binding->type)) return true; if (node.direct_call->is_generated_default_constructor &&
node.direct_call->unwind_no && pa11::strip_cv(node.binding->type)->kind == TypeKind::Record && pa11::strip_cv(node.binding->type)->base.get() != NULL) {
Value addr = member_addr(); if (zero_init_has_store(node.binding->type)) lower_storage_zero(addr, pa11::type_size(node.binding->type)); return true;
} if (node.children.size() == 1 && node.children[0].category == ValueCategory::PRValue && pa11::strip_cv(node.binding->type)->kind == TypeKind::Record &&
pa11::same_type(pa11::strip_cv(node.binding->type), pa11::strip_cv(object_type(node.children[0].type)))) { if (no_op_generated_default_constructor(node.children[0].direct_call,
node.binding->type)) return true; lower_object_init(member_addr, node.binding->type, node.children[0]); return true;
} if (node.direct_call->type->kind != TypeKind::Function || node.children.size() + 1 > node.direct_call->type->parameters.size()) {
if (!node.children.empty()) lower_object_init(member_addr, node.binding->type, node.children[0]); return true; }
if (node.children.size() == 1 && node.direct_call->type->parameters.size() == 2 && (node.direct_call->is_generated_copy_move_constructor || node.direct_call->is_defaulted ||
node.direct_call->is_noop_constructor) && !defaulted_copy_move_constructor_needs_helper(node.direct_call, node.binding->type) && !record_has_storage_copy(node.binding->type))
{ TypePtr src_record = pa11::strip_cv(object_type(node.children[0].type)); TypePtr dst_record = pa11::strip_cv(node.binding->type);
if (src_record->kind == TypeKind::Record && dst_record->kind == TypeKind::Record && pa11::same_type(src_record, dst_record) && (node.children[0].category == ValueCategory::LValue ||
node.children[0].category == ValueCategory::XValue)) { member_addr(); return true;
} } bool needs_common_lowering = false; for (size_t i = 0; i < node.children.size(); ++i)
{ TypePtr param = node.direct_call->type->parameters[i + 1]; if (is_reference(param) && pa11::strip_cv(param->base)->kind == TypeKind::Record)
needs_common_lowering = true; } if (!needs_common_lowering) {
program_.demand_function_declaration(node.direct_call); program_.demand_inline_function(node.direct_call); vector<string> lowered; lowered.push_back(member_addr().text);
for (size_t i = 0; i < node.children.size(); ++i) { if (i == 0 && starts_with(node.children[i].line, "literal prvalue " +
pa11::describe_type(node.binding->type))) continue; lowered.push_back(emit_rvalue(node.children[i]).text); }
ostringstream call; call << "call void @" << program_.symbol_for(node.direct_call) << "("; for (size_t i = 0; i < lowered.size(); ++i) {
if (i != 0) call << ", "; call << lowered[i]; }
call << ")"; instr(call.str()); return true; }
Value addr = member_addr(); function<Value()> same_addr = [addr]() { return addr; };
vector<const Node*> args; for (size_t i = 0; i < node.children.size(); ++i) { if (i == 0 &&
starts_with(node.children[i].line, "literal prvalue " + pa11::describe_type(node.binding->type))) continue; args.push_back(&node.children[i]);
} lower_constructor_call(same_addr, node.direct_call, args); return true; }
void FunctionLowerer::lower_scalar_member_init( const Node& node, const function<Value()>& member_addr) {
Value raw = emit_rvalue(node.children[0]); Value value = convert_value(raw, node.children[0].type, node.binding->type); bool unsigned_i64_widen = scalar_lowir_type(node.binding->type) == "i64" &&
is_unsigned_type(node.binding->type) && pa11::type_size(node.children[0].type) < pa11::type_size(node.binding->type); if (value.text == raw.text &&
!raw.text.empty() && raw.text[0] != '%' && raw.text[0] != '$' && raw.text[0] != '@' && pa11::is_integral_or_bool_type(node.children[0].type) && pa11::is_integral_or_bool_type(node.binding->type) &&
unsigned_i64_widen) { string src = scalar_lowir_type(strip_for_value(node.children[0].type)); string dst = scalar_lowir_type(node.binding->type);
string tmp = fresh_temp(); string op = is_unsigned_type(node.children[0].type) ? "zext" : "sext"; instr(tmp + " = convert " + op + " " + dst + " " + src + " " + raw.text);
value = Value(dst, tmp); } if (node.binding->is_bit_field) {
lower_bitfield_member_init(node, value, member_addr); return; } Value target = member_addr();
instr("store " + scalar_lowir_type(node.binding->type) + " " + value.text + ", " + target.text); } void FunctionLowerer::lower_bitfield_member_init(
const Node& node, Value value, const function<Value()>& member_addr) {
string low_type = scalar_lowir_type(node.binding->type); uint64_t mask = node.binding->bit_width >= 64 ? ~uint64_t(0) : ((uint64_t(1) << node.binding->bit_width) - 1); uint64_t storage_key = node.binding->member_offset;
bool merge = initialized_bitfield_storage_.find(storage_key) != initialized_bitfield_storage_.end(); if (merge) {
Value target = member_addr(); string oldv = fresh_temp(); instr(oldv + " = load " + low_type + " " + target.text); uint64_t storage_mask = mask << node.binding->bit_offset;
uint64_t storage_bits = pa11::type_size(node.binding->type) * 8; uint64_t clear_mask = ~storage_mask; if (storage_bits < 64) clear_mask &= (uint64_t(1) << storage_bits) - 1;
string cleared = fresh_temp(); instr(cleared + " = binary and " + low_type + " " + oldv + ", " + to_string(clear_mask)); string masked = fresh_temp();
instr(masked + " = binary and " + low_type + " " + to_string(mask) + ", " + value.text); if (node.binding->bit_offset != 0) {
string shifted = fresh_temp(); instr(shifted + " = binary shl " + low_type + " " + masked + ", " + to_string(node.binding->bit_offset)); masked = shifted;
} string merged = fresh_temp(); instr(merged + " = binary or " + low_type + " " + cleared + ", " + masked);
Value store_target = member_addr(); instr("store " + low_type + " " + merged + ", " + store_target.text); initialized_bitfield_storage_.insert(storage_key); return;
} string masked = fresh_temp(); instr(masked + " = binary and " + low_type + " " + to_string(mask) + ", " + value.text);
if (node.binding->bit_offset != 0) { string shifted = fresh_temp(); instr(shifted + " = binary shl " + low_type + " " + masked +
", " + to_string(node.binding->bit_offset)); masked = shifted; } Value target = member_addr();
instr("store " + low_type + " " + masked + ", " + target.text); initialized_bitfield_storage_.insert(storage_key); }
}  // namespace internal
}  // namespace pa14
