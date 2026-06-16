#include "pa14_lowir_internal.h"

namespace pa14 {
namespace internal {

bool node_contains_return_statement(const Node& node);
void demand_host_eh_declarations(ProgramLowerer& program, bool catch_runtime);
bool target_is_virtual_base_subobject(TypePtr source, TypePtr target);

bool FunctionLowerer::compound_has_constructor_init_action(const Node& node) const {
for (size_t i = 0; i < node.children.size(); ++i) if (starts_with(node.children[i].line, "base-init-action") ||
starts_with(node.children[i].line, "member-init-action") || starts_with(node.children[i].line, "delegating-init-action")) return true;
return false; } bool FunctionLowerer::constructor_init_action_needs_cleanup(const Node& node) const {
if (starts_with(node.line, "member-init-action")) return node.binding != NULL && type_needs_destructor(node.binding->type);
if (starts_with(node.line, "base-init-action")) return node.type.get() != NULL && type_needs_destructor(node.type);
return false; } void FunctionLowerer::emit_constructor_unwind_cleanups() {
for (size_t n = 0; n < constructor_unwind_actions_.size(); ++n) { const Node& action = *constructor_unwind_actions_[constructor_unwind_actions_.size() - 1 - n];
if (starts_with(action.line, "member-init-action")) { Node fini("member-fini-action"); fini.binding = action.binding; lower_member_fini(fini); }
else if (starts_with(action.line, "base-init-action")) { Node fini("base-fini-action"); fini.type = action.type; lower_base_fini(fini); } }
} void FunctionLowerer::lower_compound(const Node& node) {
cleanups_.push_back(vector<Cleanup>()); bool top_function_body = cleanups_.size() == 2; bool constructor_vptr_written = false; bool destructor_has_fini_actions = false;
bool constructor_init_compound = program_.native_lowering && is_class_constructor_binding(fn_.binding) && compound_has_constructor_init_action(node);
size_t saved_constructor_unwind_actions = constructor_unwind_actions_.size();
if (top_function_body && is_class_destructor_binding(fn_.binding) && fn_.binding->is_virtual) { TypePtr record = class_record_for_member(fn_.binding);
if (record.get() != NULL) lower_vptr_store(record); } if (top_function_body && is_class_constructor_binding(fn_.binding))
{ TypePtr record = class_record_for_member(fn_.binding); TypePtr bare = record.get() != NULL ? pa11::strip_cv(record) : TypePtr(); TypePtr direct_base =
bare.get() != NULL && bare->kind == TypeKind::Record ? bare->base : TypePtr(); bool has_base_init_action = false; for (size_t i = 0; i < node.children.size(); ++i)
if (starts_with(node.children[i].line, "base-init-action")) has_base_init_action = true; if (direct_base.get() != NULL && !has_base_init_action &&
!record_has_storage_copy(direct_base) && fn_.binding->type->parameters.size() == 2) { TypePtr param_record = pa11::strip_cv(
object_type(fn_.binding->type->parameters[1])); if (param_record->kind == TypeKind::Record && pa11::same_type(param_record, pa11::strip_cv(direct_base))) {
string this_ptr = fresh_temp(); instr(this_ptr + " = load ptr $this"); emit_base_subobject_addr(Value("ptr", this_ptr), bare,
direct_base); } } }
Binding* final_return_binding = NULL; bool earlier_return = false; if (!node.children.empty()) {
size_t last = node.children.size() - 1; if (starts_with(node.children[last].line, "return-statement") && !node.children[last].children.empty()) final_return_binding = node.children[last].children[0].binding;
for (size_t i = 0; i < last; ++i) if (node_contains_return_statement(node.children[i])) earlier_return = true; }
for (size_t i = 0; i < node.children.size(); ++i) { if (top_function_body && is_class_constructor_binding(fn_.binding) && !constructor_vptr_written &&
!starts_with(node.children[i].line, "base-init-action")) { TypePtr record = class_record_for_member(fn_.binding); if (record.get() != NULL)
lower_vptr_store(record); constructor_vptr_written = true; } if (starts_with(node.children[i].line, "base-fini-action") ||
starts_with(node.children[i].line, "member-fini-action")) destructor_has_fini_actions = true; if (top_function_body && destructor_base_entry_ && starts_with(node.children[i].line, "base-fini-action")) { TypePtr record = class_record_for_member(fn_.binding); TypePtr bare = record.get() != NULL ? pa11::strip_cv(record) : TypePtr(); TypePtr base = node.children[i].type.get() != NULL ? pa11::strip_cv(node.children[i].type) : TypePtr(); if (bare.get() != NULL && base.get() != NULL && target_is_virtual_base_subobject(bare, base)) continue; } bool returns_declared_variable = false; if (starts_with(node.children[i].line, "simple-declaration") &&
i + 1 < node.children.size() && starts_with(node.children[i + 1].line, "return-statement") && node.children[i].children.size() == 1 && starts_with(node.children[i].children[0].line, "variable ") &&
node.children[i].children[0].binding != NULL && !node.children[i + 1].children.empty()) { const Node& ret_expr = node.children[i + 1].children[0];
Binding* binding = node.children[i].children[0].binding; string suffix = " " + binding->name; returns_declared_variable = ret_expr.binding == binding ||
(starts_with(ret_expr.line, "id-expression") && ret_expr.line.size() >= suffix.size() && ret_expr.line.compare(ret_expr.line.size() - suffix.size(), suffix.size(),
suffix) == 0); } if (pa11::strip_cv(fn_.binding->type->base)->kind == TypeKind::Record && record_return_by_address(fn_.binding->type->base) &&
(returns_declared_variable || (starts_with(node.children[i].line, "simple-declaration") && node.children[i].children.size() == 1 && starts_with(node.children[i].children[0].line, "variable ") &&
node.children[i].children[0].binding != NULL && !earlier_return && node.children[i].children[0].binding == final_return_binding))) return_slot_variables_.insert(node.children[i].children[0].binding);
bool protect_constructor_child = constructor_init_compound && !constructor_unwind_actions_.empty();
if (protect_constructor_child) { string dispatch = fresh_block("ctor_unwind_dispatch"); string end = fresh_block("ctor_unwind_end");
instr("eh_try ^" + dispatch); ++eh_try_depth_; lower_stmt(node.children[i]); --eh_try_depth_; bool child_terminated = current_ == NULL || current_->terminated;
if (!child_terminated) { instr("eh_end"); terminate("jump ^" + end); } start_block(dispatch); emit_constructor_unwind_cleanups(); terminate("resume"); if (!child_terminated) start_block(end);
} else lower_stmt(node.children[i]);
if (constructor_init_compound && current_ != NULL && !current_->terminated && constructor_init_action_needs_cleanup(node.children[i]))
constructor_unwind_actions_.push_back(&node.children[i]); } if (top_function_body && !destructor_has_fini_actions) maybe_lower_destructor_epilogue(destructor_has_fini_actions);
if (top_function_body && is_class_destructor_binding(fn_.binding) && destructor_has_fini_actions && !destructor_base_entry_)
{ TypePtr record = class_record_for_member(fn_.binding); TypePtr bare = record.get() != NULL ? pa11::strip_cv(record) : TypePtr();
if (bare.get() != NULL && bare->kind == TypeKind::Record) { vector<TypePtr> vbases = hidden_virtual_bases_for_record(bare);
for (size_t n = 0; n < vbases.size(); ++n) { size_t i = vbases.size() - 1 - n; TypePtr vbase = vbases[i].get() != NULL ? pa11::strip_cv(vbases[i]) : TypePtr();
if (vbase.get() == NULL || vbase->kind != TypeKind::Record) continue; bool direct_virtual_base = false; vector<TypePtr> direct_bases = pa11::record_direct_bases(bare);
for (size_t b = 0; b < direct_bases.size(); ++b) { TypePtr direct_base = direct_bases[b].get() != NULL ? pa11::strip_cv(direct_bases[b]) : TypePtr(); if (direct_base.get() != NULL && pa11::record_direct_base_is_virtual(bare, b) && pa11::same_type(direct_base, vbase)) direct_virtual_base = true; }
if (direct_virtual_base) continue; Node action("base-fini-action " + vbase->name); action.type = vbase; lower_base_fini(action); } } }
if (top_function_body && is_class_constructor_binding(fn_.binding) && !constructor_vptr_written)
{ TypePtr record = class_record_for_member(fn_.binding); if (record.get() != NULL) lower_vptr_store(record);
	} if (current_ != NULL && !current_->terminated) { bool ended_with_throw = false; for (size_t n = 0; n < current_->instrs.size(); ++n) { const string& inst = current_->instrs[current_->instrs.size() - 1 - n]; if (inst.find("@__external_runtime____cxa_throw") != string::npos) { ended_with_throw = true; break; } if (inst.find("eh_end") == string::npos) break; } if (!ended_with_throw) emit_scope_cleanups(cleanups_.back()); }
if (constructor_init_compound) constructor_unwind_actions_.resize(saved_constructor_unwind_actions);
cleanups_.pop_back(); } void FunctionLowerer::lower_stmt(const Node& node)
{ if (starts_with(node.line, "compound-statement")) lower_compound(node); else if (starts_with(node.line, "base-init-action"))
lower_base_init(node); else if (starts_with(node.line, "member-init-action")) lower_member_init(node); else if (starts_with(node.line, "delegating-init-action"))
lower_delegating_init(node); else if (starts_with(node.line, "storage-copy-action")) lower_storage_copy_action(node); else if (starts_with(node.line, "base-fini-action"))
lower_base_fini(node); else if (starts_with(node.line, "member-fini-action")) lower_member_fini(node); else if (starts_with(node.line, "simple-declaration"))
lower_decl_stmt(node); else if (starts_with(node.line, "global-init-variable")) { if (!node.children.empty())
lower_global_variable_init(node.children[0]); } else if (starts_with(node.line, "thread-local-init-variable")) lower_thread_local_variable_init(node);
else if (starts_with(node.line, "global-fini-variable")) { if (!node.children.empty()) lower_global_variable_fini(node.children[0]);
} else if (starts_with(node.line, "return-statement")) lower_return(node); else if (starts_with(node.line, "expression-statement"))
lower_expr_stmt(node); else if (starts_with(node.line, "if-statement")) lower_if(node); else if (starts_with(node.line, "while-statement"))
lower_while(node); else if (starts_with(node.line, "do-statement")) lower_do(node); else if (starts_with(node.line, "for-statement"))
lower_for(node); else if (starts_with(node.line, "range-for-statement")) lower_range_for(node); else if (starts_with(node.line, "try-statement"))
lower_try(node); else if (starts_with(node.line, "break-statement")) { if (break_targets_.empty())
throw runtime_error("break outside loop or switch"); terminate("jump ^" + break_targets_.back()); } else if (starts_with(node.line, "continue-statement"))
	{ if (continue_targets_.empty()) throw runtime_error("continue outside loop"); terminate("jump ^" + continue_targets_.back());
	} else if (starts_with(node.line, "goto-statement ")) { string label = node.line.substr(15);
	emit_goto_cleanups(label); string block = labels_[label]; if (block.empty()) block = labels_[label] = fresh_block("goto"); terminate("jump ^" + block);
	} else if (starts_with(node.line, "switch-statement")) lower_switch(node); else if (starts_with(node.line, "case-statement"))
{ map<const Node*, string>::const_iterator found = switch_labels_.find(&node); if (found == switch_labels_.end()) throw runtime_error("case outside switch");
if (!current_->terminated) terminate("jump ^" + found->second); start_block(found->second); if (node.children.size() > 1)
lower_stmt(node.children[1]); } else if (starts_with(node.line, "default-statement")) {
map<const Node*, string>::const_iterator found = switch_labels_.find(&node); if (found == switch_labels_.end()) throw runtime_error("default outside switch"); if (!current_->terminated)
terminate("jump ^" + found->second); start_block(found->second); if (!node.children.empty()) lower_stmt(node.children[0]);
} else if (starts_with(node.line, "labeled-statement ")) { string label = node.line.substr(18);
string block = labels_[label]; if (block.empty()) block = labels_[label] = fresh_block("goto"); terminate("jump ^" + block);
start_block(block); if (!node.children.empty()) lower_stmt(node.children[0]); }
else if (!node.children.empty()) lower_stmt(node.children[0]); } void FunctionLowerer::lower_decl_stmt(const Node& node)
{ for (size_t i = 0; i < node.children.size(); ++i) lower_variable_decl(node.children[i]); }
void FunctionLowerer::lower_return(const Node& node) { TypePtr ret = fn_.binding->type->base; if (node.children.empty() || pa11::is_void_type(ret))
{ if (!node.children.empty()) emit_rvalue(node.children[0]); emit_pending_temp_cleanups();
emit_all_cleanups(); terminate("return void"); return; }
if (is_reference(ret)) { Value addr; if (node.children[0].category == ValueCategory::LValue ||
node.children[0].category == ValueCategory::XValue) { addr = ensure_pointer(emit_lvalue_addr(node.children[0])); }
else { string slot = fresh_aux_slot("retref", scalar_lowir_type(ret->base));
Value value = convert_value(emit_rvalue(node.children[0]), node.children[0].type, ret->base); instr("store " + scalar_lowir_type(ret->base) + " " +
value.text + ", $" + slot); string addr_name = fresh_temp(); instr(addr_name + " = addr $" + slot); addr = Value("ptr", addr_name);
} addr = convert_value(addr, pa11::make_pointer(object_type(node.children[0].type)), pa11::make_pointer(ret->base));
emit_pending_temp_cleanups(); emit_all_cleanups(); terminate("return ptr " + addr.text); return;
} if (pa11::strip_cv(ret)->kind == TypeKind::Record) { if (record_return_by_address(ret))
{ if (node.children[0].binding != NULL && return_slot_variables_.find(node.children[0].binding) != return_slot_variables_.end())
{ emit_pending_temp_cleanups(); emit_all_cleanups(); terminate("return void");
return; } Value ret_addr("ptr", "%ret"); function<Value()> addr_for = [ret_addr]() {
return ret_addr; }; bool saved_lowering_record_return_object = lowering_record_return_object_;
lowering_record_return_object_ = true; lower_object_init(addr_for, ret, node.children[0]); lowering_record_return_object_ = saved_lowering_record_return_object;
emit_pending_temp_cleanups(); emit_all_cleanups(); terminate("return void"); return;
} if (record_return_slot_.empty()) record_return_slot_ = fresh_aux_slot("retobj", slot_lowir_type(ret)); string slot = record_return_slot_;
string addr_name = fresh_temp(); instr(addr_name + " = addr $" + slot); Value ret_addr("ptr", addr_name); function<Value()> addr_for = [ret_addr]() {
return ret_addr; }; bool saved_lowering_record_return_object = lowering_record_return_object_;
lowering_record_return_object_ = true; lower_object_init(addr_for, ret, node.children[0]); lowering_record_return_object_ = saved_lowering_record_return_object;
emit_pending_temp_cleanups(); emit_all_cleanups(); terminate("return " + scalar_lowir_type(ret) + " $" + slot); return;
} Value raw = emit_rvalue(node.children[0]); TypePtr raw_type = node.children[0].type; Value value = convert_binary_value(raw, raw_type, ret);
emit_pending_temp_cleanups(); emit_all_cleanups(); terminate("return " + scalar_lowir_type(ret) + " " + value.text); }
void FunctionLowerer::lower_expr_stmt(const Node& node) { if (!node.children.empty()) lower_discarded_expr(node.children[0]);
emit_pending_temp_cleanups(); } void FunctionLowerer::lower_discarded_expr(const Node& expr) {
if (starts_with(expr.line, "call-expression") && expr.direct_call != NULL &&
    (expr.direct_call->name == "__builtin_va_start" ||
     expr.direct_call->name == "__builtin_va_end")) { emit_rvalue(expr); return; }
if (starts_with(expr.line, "cast-expression") && pa11::is_void_type(expr.type) && expr.children.size() == 1) {
TypePtr child_object = pa11::strip_cv(object_type(expr.children[0].type)); if (expr.children[0].category == ValueCategory::LValue && child_object->kind == TypeKind::Record) ensure_pointer(emit_lvalue_addr(expr.children[0]));
else lower_discarded_expr(expr.children[0]); return; }
if (starts_with(expr.line, "call-expression") && is_reference(expr.type)) { TypePtr object = pa11::strip_cv(object_type(expr.type)); if (object->kind == TypeKind::Record ||
object->kind == TypeKind::Array) emit_call(expr); else emit_rvalue(expr);
return; } if (starts_with(expr.line, "binary-expression") && expr.has_op && expr.op == OP_COMMA)
{ lower_discarded_expr(expr.children[0]); lower_discarded_expr(expr.children[1]); return;
} TypePtr object = pa11::strip_cv(object_type(expr.type)); if (expr.category == ValueCategory::PRValue && !is_reference(expr.type) &&
(object->kind == TypeKind::Record || object->kind == TypeKind::Array)) { string slot = fresh_aux_slot(object->kind == TypeKind::Array
? "discardarr" : "discard", slot_lowir_type(object)); string addr_name = fresh_temp(); instr(addr_name + " = addr $" + slot);
Value addr("ptr", addr_name); function<Value()> addr_for = [addr]() { return addr; };
if (object->kind == TypeKind::Array && starts_with(expr.line, "braced-init-list")) lower_direct_array_init(addr, object, expr); else
lower_object_init(addr_for, object, expr); if (type_needs_destructor(object)) add_pending_temp_cleanup(addr, object); return; } if (expr.category == ValueCategory::LValue &&
object->kind == TypeKind::Array) { ensure_pointer(emit_lvalue_addr(expr)); return;
} emit_rvalue(expr); } void FunctionLowerer::lower_if(const Node& node)
{ string then_block = fresh_block("if_then"); string else_block = fresh_block("if_else"); string end_block = fresh_block("if_end");
const Node& cond = node.children[0].children[0]; branch_on(cond, then_block, else_block); start_block(then_block); lower_stmt(node.children[1].children[0]);
bool then_done = current_->terminated; if (!current_->terminated) terminate("jump ^" + end_block); start_block(else_block);
if (node.children.size() > 2) lower_stmt(node.children[2].children[0]); bool else_done = current_->terminated; if (!current_->terminated)
terminate("jump ^" + end_block); if (!then_done || !else_done) start_block(end_block); }
void FunctionLowerer::lower_while(const Node& node) { string cond_block = fresh_block("while_cond"); string body_block = fresh_block("while_body");
string end_block = fresh_block("while_end"); terminate("jump ^" + cond_block); start_block(cond_block); continue_targets_.push_back(cond_block);
break_targets_.push_back(end_block); branch_on(node.children[0].children[0], body_block, end_block); start_block(body_block); lower_stmt(node.children[1]);
if (!current_->terminated) terminate("jump ^" + cond_block); break_targets_.pop_back(); continue_targets_.pop_back();
start_block(end_block); } void FunctionLowerer::lower_do(const Node& node) {
string body_block = fresh_block("do_body"); string cond_block = fresh_block("do_cond"); string end_block = fresh_block("do_end"); terminate("jump ^" + body_block);
start_block(body_block); continue_targets_.push_back(cond_block); break_targets_.push_back(end_block); lower_stmt(node.children[0]);
if (!current_->terminated) terminate("jump ^" + cond_block); start_block(cond_block); branch_on(node.children[1].children[0], body_block, end_block);
break_targets_.pop_back(); continue_targets_.pop_back(); start_block(end_block); }
void FunctionLowerer::lower_for(const Node& node) { bool init_cleanup_scope = false; if (!node.children[0].children.empty())
{ const Node& init = node.children[0].children[0]; if (starts_with(init.line, "simple-declaration")) {
cleanups_.push_back(vector<Cleanup>()); init_cleanup_scope = true; lower_stmt(init); }
else lower_discarded_expr(init); } string cond_block = fresh_block("for_cond");
string body_block = fresh_block("for_body"); string iter_block = fresh_block("for_iter"); string end_block = fresh_block("for_end"); terminate("jump ^" + cond_block);
start_block(cond_block); continue_targets_.push_back(iter_block); break_targets_.push_back(end_block); if (node.children.size() > 1 && starts_with(node.children[1].line, "condition"))
branch_on(node.children[1].children[0], body_block, end_block); else terminate("jump ^" + body_block); start_block(body_block);
lower_stmt(node.children.back()); if (!current_->terminated) terminate("jump ^" + iter_block); start_block(iter_block);
for (size_t i = 0; i < node.children.size(); ++i) if (starts_with(node.children[i].line, "iteration") && !node.children[i].children.empty()) lower_discarded_expr(node.children[i].children[0]);
terminate("jump ^" + cond_block); break_targets_.pop_back(); continue_targets_.pop_back(); start_block(end_block);
if (init_cleanup_scope) { emit_scope_cleanups(cleanups_.back()); cleanups_.pop_back();
} } void FunctionLowerer::lower_range_for(const Node& node) {
if (node.token_text == "iterator") { if (node.children.size() != 7) throw runtime_error("invalid iterator range-for node");
const Node& begin_var = node.children[0]; const Node& end_var = node.children[1]; const Node& loop_var = node.children[2]; const Node& condition = node.children[3];
const Node& deref = node.children[4]; const Node& increment = node.children[5]; const Node& body = node.children[6]; lower_variable_decl(begin_var);
lower_variable_decl(end_var); string cond_block = fresh_block("for_cond"); string body_block = fresh_block("for_body"); string iter_block = fresh_block("for_iter");
string end_block = fresh_block("for_end"); terminate("jump ^" + cond_block); start_block(cond_block); continue_targets_.push_back(iter_block);
break_targets_.push_back(end_block); branch_on(condition, body_block, end_block); start_block(body_block); TypePtr loop_type = loop_var.binding->type;
string loop_slot = slot_for(loop_var.binding); if (is_reference(loop_type)) { Value source = ensure_pointer(emit_lvalue_addr(deref));
Value converted = convert_value(source, pa11::make_pointer(object_type(deref.type)), pa11::make_pointer(loop_type->base));
instr("store ptr " + converted.text + ", $" + loop_slot); } else if (pa11::strip_cv(loop_type)->kind == TypeKind::Record) {
function<Value()> dst_addr = [this, &loop_var]() { return ensure_pointer(emit_lvalue_addr(loop_var)); }; lower_object_init(dst_addr, loop_type, deref);
} else { Value value = emit_rvalue(deref);
value = convert_value(value, deref.type, loop_type); instr("store " + scalar_lowir_type(loop_type) + " " + value.text + ", $" + loop_slot); }
lower_stmt(body); if (!current_->terminated) terminate("jump ^" + iter_block); start_block(iter_block);
lower_discarded_expr(increment); terminate("jump ^" + cond_block); break_targets_.pop_back(); continue_targets_.pop_back();
start_block(end_block); return; } if (node.children.size() != 4)
throw runtime_error("invalid range-for node"); const Node& range = node.children[0]; const Node& idx_var = node.children[1]; const Node& loop_var = node.children[2];
const Node& body = node.children[3]; if (starts_with(range.line, "variable ")) lower_variable_decl(range); lower_variable_decl(idx_var);
TypePtr array_type = object_type(range.type); TypePtr array_bare = pa11::strip_cv(array_type); TypePtr initializer_list_element; bool initializer_list_range = is_initializer_list_type(array_type, &initializer_list_element); if (!initializer_list_range && (array_bare->kind != TypeKind::Array || array_bare->unknown_bound)) throw runtime_error("unsupported range-for");
TypePtr element_type = initializer_list_range ? initializer_list_element : array_bare->base; string cond_block = fresh_block("for_cond"); string body_block = fresh_block("for_body"); string iter_block = fresh_block("for_iter");
string end_block = fresh_block("for_end"); terminate("jump ^" + cond_block); start_block(cond_block); continue_targets_.push_back(iter_block);
break_targets_.push_back(end_block); string idx_loaded = fresh_temp(); instr(idx_loaded + " = load i32 $" + slot_for(idx_var.binding)); string cmp;
if (initializer_list_range) { Value range_addr = ensure_pointer(emit_lvalue_addr(range)); string size_addr = fresh_temp(); instr(size_addr + " = index i8 [projection=field] " + range_addr.text + ", 8"); string size_value = fresh_temp(); instr(size_value + " = load i64 " + size_addr); string idx64 = fresh_temp(); instr(idx64 + " = convert sext i64 i32 " + idx_loaded); cmp = fresh_temp(); instr(cmp + " = cmp lt i64 " + idx64 + ", " + size_value); } else { cmp = fresh_temp(); instr(cmp + " = cmp lt i32 " + idx_loaded + ", " + to_string(array_bare->bound)); } terminate("branch " + cmp + ", ^" + body_block + ", ^" + end_block); start_block(body_block);
Value range_addr = ensure_pointer(emit_lvalue_addr(range)); string decay; if (initializer_list_range) { string begin_addr = fresh_temp(); instr(begin_addr + " = index i8 [projection=field] " + range_addr.text + ", 0"); decay = fresh_temp(); instr(decay + " = load ptr " + begin_addr); } else { decay = fresh_temp(); instr(decay + " = unary decay ptr " + range_addr.text); } string idx_body = fresh_temp();
instr(idx_body + " = load i32 $" + slot_for(idx_var.binding)); string elem_addr_name = fresh_temp(); TypePtr elem_object = pa11::strip_cv(element_type); if (elem_object->kind == TypeKind::Record ||
elem_object->kind == TypeKind::Array) { string scaled = fresh_temp(); instr(scaled + " = binary mul i64 " + idx_body + ", " +
to_string(pa11::type_size(elem_object))); instr(elem_addr_name + " = index i8 [projection=array_element] " + decay + ", " + scaled); }
else { instr(elem_addr_name + " = index " + scalar_lowir_type(element_type) + " [projection=array_element] " + decay + ", " + idx_body);
} TypePtr loop_type = loop_var.binding->type; string loop_slot = slot_for(loop_var.binding); if (is_reference(loop_type))
{ Value elem_addr("ptr", elem_addr_name); Value converted = convert_value(elem_addr,
pa11::make_pointer(element_type), pa11::make_pointer(loop_type->base)); instr("store ptr " + converted.text + ", $" + loop_slot); }
else if (pa11::strip_cv(loop_type)->kind == TypeKind::Record) { function<Value()> dst_addr = [this, &loop_var]() { return ensure_pointer(emit_lvalue_addr(loop_var));
}; Node elem("range-element lvalue " + pa11::describe_type(element_type)); elem.type = element_type;
elem.category = ValueCategory::LValue; lower_object_init(dst_addr, loop_type, elem); } else
{ string loaded = fresh_temp(); instr(loaded + " = load " + scalar_lowir_type(element_type) + " " + elem_addr_name);
Value value = convert_value(Value(scalar_lowir_type(element_type), loaded), element_type, loop_type);
instr("store " + scalar_lowir_type(loop_type) + " " + value.text + ", $" + loop_slot); } lower_stmt(body);
if (!current_->terminated) terminate("jump ^" + iter_block); start_block(iter_block); string iter_loaded = fresh_temp();
instr(iter_loaded + " = load i32 $" + slot_for(idx_var.binding)); string incremented = fresh_temp(); instr(incremented + " = binary add i32 " + iter_loaded + ", 1"); instr("store i32 " + incremented + ", $" + slot_for(idx_var.binding));
terminate("jump ^" + cond_block); break_targets_.pop_back(); continue_targets_.pop_back(); start_block(end_block);
	} void FunctionLowerer::lower_catch_binding(const Node& catch_clause,
	                                            const string& caught) {
	Binding* binding = catch_clause.binding;
	TypePtr catch_type = binding != NULL ? binding->type : catch_clause.type;
	if (catch_type.get() == NULL)
		return;
	if (is_reference(catch_type)) {
		if (binding != NULL) {
			string local_slot = slot_for(binding);
			instr("store ptr " + caught + ", $" + local_slot);
		}
		return;
	}
	TypePtr object = pa11::strip_cv(object_type(catch_type));
	if (object.get() == NULL)
		return;
	if (object->kind == TypeKind::Record) {
		string local_slot = binding != NULL
			? slot_for(binding)
			: fresh_aux_slot("catchobj", slot_lowir_type(object));
		Value target = ensure_pointer(Value("ptr", "$" + local_slot));
		Binding* copy = find_copy_move_constructor(object, false);
		if (copy != NULL) {
			vector<string> lowered;
			vector<pair<Value, TypePtr> > temp_cleanups;
			vector<PendingConstructorConversion> pending_conversions;
			lowered.push_back(target.text);
			lowered.push_back(caught);
			emit_constructor_call_with_cleanups(
				copy, lowered, temp_cleanups, pending_conversions);
		} else {
			instr("copyobj " + to_string(pa11::type_size(object)) +
			      "x" + to_string(pa11::type_align(object)) + " " +
			      caught + ", " + target.text);
		}
		if (type_needs_destructor(object) && !cleanups_.empty())
			cleanups_.back().push_back(Cleanup(target.text, object));
		return;
	}
	if (binding != NULL) {
		string local_slot = slot_for(binding);
		string loaded = fresh_temp();
		instr(loaded + " = load " + scalar_lowir_type(binding->type) +
		      " " + caught);
		instr("store " + scalar_lowir_type(binding->type) + " " +
		      loaded + ", $" + local_slot);
	}
	} void FunctionLowerer::lower_try(const Node& node) {
	if (!program_.native_lowering) {
	if (node.children.size() != 2 ||
	    node.children[0].children.empty() ||
	    !starts_with(node.children[1].line, "catch-clause") ||
	    node.children[1].children.empty())
		throw runtime_error("unsupported try statement");
	const Node& protected_body = node.children[0].children[0];
	const Node& catch_clause = node.children[1];
	TypePtr catch_type = catch_clause.type;
	bool catch_all = catch_clause.token_text == "catch-all";
	string rtti;
	if (!catch_all) {
		if (catch_type.get() == NULL)
			throw runtime_error("unsupported catch clause");
		TypePtr catch_object = object_type(catch_type);
		program_.emit_typeinfo(catch_object);
		rtti = program_.catch_rtti_symbol(catch_object);
		if (rtti.empty())
			throw runtime_error("unsupported catch type");
	}
	demand_host_eh_declarations(program_, true);
	string dispatch = fresh_block("catch_dispatch");
	string entry = fresh_block("catch_entry");
	string try_end = fresh_block("try_end");
	string catch_body;
	string catch_next;
	string catch_cleanup;
	for (size_t i = 0; i < active_catches_.size(); ++i) {
		int selector = static_cast<int>(active_catches_.size() - i + 1);
		if (active_catches_[i].selector < selector)
			active_catches_[i].selector = selector;
	}
	ActiveCatchContext ctx;
	ctx.rtti = rtti;
	ctx.catch_all = catch_all;
	ctx.entry = entry;
	ctx.selector = 1;
	active_catches_.push_back(ctx);
	instr("eh_try ^" + dispatch);
	++eh_try_depth_;
	cleanups_.push_back(vector<Cleanup>());
	cleanups_.back().push_back(Cleanup("eh_end"));
	lower_stmt(protected_body);
	cleanups_.pop_back();
	--eh_try_depth_;
	ctx = active_catches_.back();
	active_catches_.pop_back();
	catch_body = fresh_block("catch_body");
	catch_next = fresh_block("catch_next");
	catch_cleanup = fresh_block("catch_cleanup");
	if (!current_->terminated) {
			bool ended_with_throw = false;
			for (size_t n = 0; n < current_->instrs.size(); ++n) {
				const string& inst =
					current_->instrs[current_->instrs.size() - 1 - n];
				if (inst.find("@__external_runtime____cxa_throw") !=
				    string::npos) {
					ended_with_throw = true;
					break;
				}
				if (inst.find("eh_end") == string::npos)
					break;
			}
			instr("eh_end");
			if (ended_with_throw) {
			TypePtr ret = fn_.binding != NULL && fn_.binding->type.get() != NULL
				? fn_.binding->type->base : pa11::make_fundamental(FT_VOID);
			if (pa11::is_void_type(ret) ||
			    pa11::strip_cv(ret)->kind == TypeKind::Record)
				terminate("return void");
			else
				terminate("return " + scalar_lowir_type(ret) + " 0");
		} else
			terminate("jump ^" + try_end);
	}
	start_block(dispatch);
	emit_active_catch_clause(ctx);
	terminate("jump ^" + entry);
	start_block(entry);
	string exception = fresh_temp();
	instr(exception + " = exception ptr");
	string selector = fresh_temp();
	instr(selector + " = exception_selector i32");
	string selected = fresh_temp();
	instr(selected + " = cmp eq i32 " + selector + ", " +
	      to_string(ctx.selector));
	terminate("branch " + selected + ", ^" + catch_body + ", ^" +
	          catch_next);
	start_block(catch_body);
	string caught = fresh_temp();
	instr(caught + " = call ptr @__external_runtime____cxa_begin_catch(" +
	      exception + ")");
	if (catch_clause.binding != NULL) {
		string catch_slot = fresh_aux_slot("catch", "ptr");
		instr("store ptr " + caught + ", $" + catch_slot);
	}
	instr("eh_cleanup ^" + catch_cleanup);
	if (catch_clause.binding != NULL) {
		string local_slot = slot_for(catch_clause.binding);
		if (is_reference(catch_clause.binding->type))
			instr("store ptr " + caught + ", $" + local_slot);
		else {
			string loaded = fresh_temp();
			instr(loaded + " = load " +
			      scalar_lowir_type(catch_clause.binding->type) + " " +
			      caught);
			instr("store " + scalar_lowir_type(catch_clause.binding->type) +
			      " " + loaded + ", $" + local_slot);
		}
	}
	cleanups_.push_back(vector<Cleanup>());
	cleanups_.back().push_back(
		Cleanup("call void @__external_runtime____cxa_end_catch()"));
	cleanups_.back().push_back(Cleanup("eh_end"));
	lower_stmt(catch_clause.children[0]);
	cleanups_.pop_back();
	if (!current_->terminated) {
		instr("eh_end");
		instr("call void @__external_runtime____cxa_end_catch()");
		terminate("jump ^" + try_end);
	}
	start_block(catch_cleanup);
	if (!active_catches_.empty())
		emit_active_catch_clause(active_catches_.back());
	instr("call void @__external_runtime____cxa_end_catch()");
	instr("eh_end");
	if (!active_catches_.empty()) {
		instr("eh_end");
		terminate("jump ^" + active_catches_.back().entry);
	} else
		terminate("resume");
	start_block(catch_next);
	if (!active_catches_.empty()) {
		emit_unwind_object_cleanups();
		terminate("jump ^" + active_catches_.back().entry);
	} else
		terminate("resume");
	start_block(try_end);
	return;
	}
	if (node.children.size() < 2 || node.children[0].children.empty())
		throw runtime_error("unsupported try statement");
	const Node& protected_body = node.children[0].children[0];
	bool constructor_function_try =
		is_class_constructor_binding(fn_.binding) &&
		compound_has_constructor_init_action(protected_body);
	struct CatchInfo {
		const Node* clause;
		ActiveCatchContext ctx;
		string body;
		string next;
		string cleanup;
	};
	vector<CatchInfo> catches;
	for (size_t i = 1; i < node.children.size(); ++i) {
		const Node& catch_clause = node.children[i];
		if (!starts_with(catch_clause.line, "catch-clause") ||
		    catch_clause.children.empty())
			throw runtime_error("unsupported try statement");
		CatchInfo info;
		info.clause = &catch_clause;
		info.ctx.catch_all = catch_clause.token_text == "catch-all";
		info.ctx.selector = static_cast<int>(catches.size() + 1);
		if (!info.ctx.catch_all) {
			if (catch_clause.type.get() == NULL)
				throw runtime_error("unsupported catch clause");
			TypePtr catch_object = object_type(catch_clause.type);
			program_.emit_typeinfo(catch_object);
			info.ctx.rtti = program_.catch_rtti_symbol(catch_object);
			if (info.ctx.rtti.empty())
				throw runtime_error("unsupported catch type");
		}
		catches.push_back(info);
	}
	demand_host_eh_declarations(program_, true);
	string dispatch = fresh_block("catch_dispatch");
	string entry = fresh_block("catch_entry");
	string try_end = fresh_block("try_end");
	for (size_t i = 0; i < catches.size(); ++i) {
		catches[i].ctx.entry = entry;
		catches[i].body = fresh_block("catch_body");
		catches[i].next = fresh_block("catch_next");
		catches[i].cleanup = fresh_block("catch_cleanup");
	}
	for (size_t i = 0; i < catches.size(); ++i)
		active_catches_.push_back(catches[i].ctx);
	instr("eh_try ^" + dispatch);
	cleanups_.push_back(vector<Cleanup>());
	cleanups_.back().push_back(Cleanup("eh_end"));
	lower_stmt(protected_body);
	cleanups_.pop_back();
	for (size_t i = 0; i < catches.size(); ++i)
		active_catches_.pop_back();
	if (!current_->terminated) {
		bool ended_with_throw = false;
		for (size_t n = 0; n < current_->instrs.size(); ++n) {
			const string& inst =
				current_->instrs[current_->instrs.size() - 1 - n];
			if (inst.find("@__external_runtime____cxa_throw") !=
			    string::npos) {
				ended_with_throw = true;
				break;
			}
			if (inst.find("eh_end") == string::npos)
				break;
		}
		instr("eh_end");
		if (ended_with_throw) {
			TypePtr ret = fn_.binding != NULL && fn_.binding->type.get() != NULL
				? fn_.binding->type->base : pa11::make_fundamental(FT_VOID);
			if (pa11::is_void_type(ret) ||
			    pa11::strip_cv(ret)->kind == TypeKind::Record)
				terminate("return void");
			else
				terminate("return " + scalar_lowir_type(ret) + " 0");
		} else
			terminate("jump ^" + try_end);
	}
	start_block(dispatch);
	for (size_t i = 0; i < catches.size(); ++i)
		emit_active_catch_clause(catches[i].ctx);
	terminate("jump ^" + entry);
	start_block(entry);
	string exception = fresh_temp();
	instr(exception + " = exception ptr");
	string selector = fresh_temp();
	instr(selector + " = exception_selector i32");
	for (size_t i = 0; i < catches.size(); ++i) {
		const CatchInfo& info = catches[i];
		const Node& catch_clause = *info.clause;
		string selected = fresh_temp();
		instr(selected + " = cmp eq i32 " + selector + ", " +
		      to_string(info.ctx.selector));
		terminate("branch " + selected + ", ^" + info.body + ", ^" +
		          info.next);
		start_block(info.body);
		string caught = fresh_temp();
		instr(caught +
		      " = call ptr @__external_runtime____cxa_begin_catch(" +
		      exception + ")");
		if (catch_clause.binding != NULL) {
			string catch_slot = fresh_aux_slot("catch", "ptr");
			instr("store ptr " + caught + ", $" + catch_slot);
		}
		instr("eh_cleanup ^" + info.cleanup);
		cleanups_.push_back(vector<Cleanup>());
		cleanups_.back().push_back(
			Cleanup("call void @__external_runtime____cxa_end_catch()"));
		cleanups_.back().push_back(Cleanup("eh_end"));
		lower_catch_binding(catch_clause, caught);
		lower_stmt(catch_clause.children[0]);
		vector<Cleanup> catch_scope = cleanups_.back();
		cleanups_.pop_back();
		if (!current_->terminated) {
			emit_scope_cleanups(catch_scope);
			if (constructor_function_try) {
				ensure_rethrow_runtime_declaration();
				emit_rethrow();
			} else
				terminate("jump ^" + try_end);
		}
		start_block(info.cleanup);
		if (!active_catches_.empty())
			emit_active_catch_clause(active_catches_.back());
		emit_scope_cleanups(catch_scope);
		if (!active_catches_.empty()) {
			instr("eh_end");
			terminate("jump ^" + active_catches_.back().entry);
		} else
			terminate("resume");
		start_block(info.next);
	}
	if (!active_catches_.empty()) {
		emit_unwind_object_cleanups();
		terminate("jump ^" + active_catches_.back().entry);
	} else
		terminate("resume");
	start_block(try_end);
	} void FunctionLowerer::lower_switch_items(const Node& node,
vector<pair<string, const Node*> >& cases, const Node*& default_node) { if (starts_with(node.line, "switch-statement"))
return; if (starts_with(node.line, "case-statement")) cases.push_back(make_pair(lowir_literal(node.children[0].type, node.children[0]), &node));
else if (starts_with(node.line, "default-statement")) default_node = &node; for (size_t i = 0; i < node.children.size(); ++i) lower_switch_items(node.children[i], cases, default_node);
} void FunctionLowerer::lower_switch(const Node& node) { const Node& condition = node.children[0].children[0];
Value selector; if (starts_with(condition.line, "condition-declaration")) { if (condition.children.empty())
throw runtime_error("empty switch condition declaration"); lower_variable_decl(condition.children[0]); const Node& selector_node = condition.children.size() > 1 ? condition.children[1] :
condition.children[0]; selector = emit_rvalue(selector_node); } else
selector = emit_rvalue(condition); vector<pair<string, const Node*> > cases; const Node* default_node = NULL; lower_switch_items(node.children[1], cases, default_node);
string dispatch = fresh_block("switch_dispatch"); string end = fresh_block("switch_end"); vector<string> case_blocks; for (size_t i = 0; i < cases.size(); ++i)
case_blocks.push_back(fresh_block("switch_case")); string def = default_node == NULL ? end : fresh_block("switch_default"); vector<const Node*> installed; for (size_t i = 0; i < cases.size(); ++i)
{ switch_labels_[cases[i].second] = case_blocks[i]; installed.push_back(cases[i].second); }
if (default_node != NULL) { switch_labels_[default_node] = def; installed.push_back(default_node);
} terminate("jump ^" + dispatch); start_block(dispatch); ostringstream sw;
sw << "switch " << selector.text << ", ^" << def; for (size_t i = 0; i < cases.size(); ++i) sw << ", " << cases[i].first << ":^" << case_blocks[i]; terminate(sw.str());
break_targets_.push_back(end); lower_stmt(node.children[1]); if (!current_->terminated) terminate("jump ^" + end);
break_targets_.pop_back(); for (size_t i = 0; i < installed.size(); ++i) switch_labels_.erase(installed[i]); start_block(end);
}
}  // namespace internal
}  // namespace pa14
