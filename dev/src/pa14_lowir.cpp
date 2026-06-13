#include "pa14_lowir_internal.h"
#include "pa12_templates_function_support.h"
#include <algorithm>
#include <utility>
namespace pa14 { namespace internal { bool node_contains_call_expression(const Node& node) {
if (starts_with(node.line, "call-expression")) return true; for (size_t i = 0; i < node.children.size(); ++i) if (node_contains_call_expression(node.children[i]))
return true; return false; } bool node_contains_return_statement(const Node& node)
{ if (starts_with(node.line, "return-statement")) return true; for (size_t i = 0; i < node.children.size(); ++i)
if (node_contains_return_statement(node.children[i])) return true; return false; }
bool node_may_throw_for_noexcept_wrapper(const Node& node)
{
	if (starts_with(node.line, "throw-expression"))
		return true;
	if (starts_with(node.line, "call-expression"))
		return node.direct_call == NULL || !node.direct_call->unwind_no;
	if (node.direct_call != NULL && !node.direct_call->unwind_no)
		return true;
	for (size_t i = 0; i < node.children.size(); ++i)
		if (node_may_throw_for_noexcept_wrapper(node.children[i]))
			return true;
	return false;
}
void demand_host_eh_declarations(ProgramLowerer& program, bool catch_runtime) { if (program.declared_functions.insert( "__external_runtime___Unwind_Resume").second)
program.declares.push_back( "declare function @__external_runtime___Unwind_Resume() -> void " "[return=noreturn, role=eh_resume, linkage=c, " "binding=strong, object=_Unwind_Resume]");
if (catch_runtime && program.declared_functions.insert( "__external_runtime____cxa_begin_catch").second) program.declares.push_back(
"declare function @__external_runtime____cxa_begin_catch" "(%arg0 : ptr) -> ptr [role=eh_begin_catch, linkage=c, " "binding=strong, object=__cxa_begin_catch]"); if (catch_runtime &&
program.declared_functions.insert( "__external_runtime____cxa_end_catch").second) program.declares.push_back( "declare function @__external_runtime____cxa_end_catch() -> void "
"[role=eh_end_catch, linkage=c, binding=strong, " "object=__cxa_end_catch]"); if (program.declared_functions.insert( "__external_runtime____gxx_personality_v0").second)
program.declares.push_back( "declare function @__external_runtime____gxx_personality_v0() " "-> void [role=eh_personality, linkage=c, binding=strong, " "object=__gxx_personality_v0]");
} void FunctionLowerer::ensure_noexcept_terminate_helper() {
demand_host_eh_declarations(program_, true);
if (program_.declared_functions.insert("std__terminate").second)
program_.declares.push_back(
"declare function @std__terminate() -> void "
"[return=noreturn, unwind=no, binding=strong, object=_ZSt9terminatev]");
if (!program_.defined_functions.insert("cppgm_call_terminate").second)
return;
FunctionOut helper;
helper.name = "cppgm_call_terminate";
helper.header =
"function @cppgm_call_terminate(%exception : ptr) -> void "
"[return=noreturn, binding=weak, object=cppgm_call_terminate]";
helper.parameter_names.push_back("exception");
Block entry("entry");
entry.instrs.push_back(
"    %caught = call ptr @__external_runtime____cxa_begin_catch(%exception)");
entry.instrs.push_back("    call void @std__terminate()");
entry.instrs.push_back("    return void");
entry.terminated = true;
helper.blocks.push_back(entry);
program_.functions.push_back(helper);
} void FunctionLowerer::emit_noexcept_terminate_landing(TypePtr ret,
                                                        bool indirect_result) {
string exception = fresh_temp();
instr(exception + " = exception ptr");
instr("call void @cppgm_call_terminate(" + exception + ")");
if (pa11::is_void_type(ret) || indirect_result ||
    pa11::strip_cv(ret)->kind == TypeKind::Record)
terminate("return void");
else
terminate("return " + scalar_lowir_type(ret) + " 0");
} bool record_has_default_constructor_for_array(TypePtr type) { TypePtr bare = pa11::strip_cv(type);
if (bare->kind != TypeKind::Record || bare->scope == NULL) return false; map<string, vector<Binding*> >::const_iterator found = bare->scope->members.find(bare->scope->name);
if (found == bare->scope->members.end()) return false; for (size_t i = 0; i < found->second.size(); ++i) if (found->second[i]->kind == BindingKind::Function &&
found->second[i]->type->kind == TypeKind::Function && found->second[i]->type->parameters.size() == 1) return true; return false;
} Binding* find_record_destructor(TypePtr type) { TypePtr bare = pa11::strip_cv(type);
if (bare->kind != TypeKind::Record || bare->scope == NULL) return NULL; string name = "~" + bare->scope->name; map<string, vector<Binding*> >::const_iterator found =
bare->scope->members.find(name); if (found == bare->scope->members.end()) return NULL; for (size_t i = 0; i < found->second.size(); ++i)
if (found->second[i]->kind == BindingKind::Function) return found->second[i]; return NULL; }
bool parameter_type_needs_destructor(TypePtr type) { TypePtr bare = pa11::strip_cv(type); if (bare->kind == TypeKind::Array)
return parameter_type_needs_destructor(bare->base); if (bare->kind != TypeKind::Record) return false; Binding* dtor = find_record_destructor(bare);
if (dtor != NULL && (!dtor->is_noop_destructor || !dtor->is_generated_default_destructor)) return true; pa11::layout_record_type(bare);
if (bare->base.get() != NULL && parameter_type_needs_destructor(bare->base)) return true; for (size_t i = 0; i < bare->fields.size(); ++i)
if (parameter_type_needs_destructor(bare->fields[i]->type)) return true; return false; }
bool record_has_base_subobject(TypePtr source, TypePtr target) { if (source.get() == NULL || target.get() == NULL) return false; TypePtr bare = pa11::strip_cv(source); TypePtr wanted = pa11::strip_cv(target);
if (bare->kind != TypeKind::Record || wanted->kind != TypeKind::Record) return false; vector<TypePtr> bases = pa11::record_direct_bases(bare); for (size_t i = 0; i < bases.size(); ++i)
{ TypePtr stripped = bases[i].get() != NULL ? pa11::strip_cv(bases[i]) : TypePtr(); if (stripped.get() == NULL) continue; if (pa11::same_type(stripped, wanted)) return true;
if (record_has_base_subobject(stripped, wanted)) return true; } return false;
} uint64_t base_subobject_offset(TypePtr source, TypePtr target) { if (source.get() == NULL || target.get() == NULL)
return 0; TypePtr root = pa11::strip_cv(source); TypePtr wanted = pa11::strip_cv(target);
if (root->kind != TypeKind::Record || wanted->kind != TypeKind::Record) return 0; vector<pair<TypePtr, uint64_t> > pending; pending.push_back(make_pair(root, 0)); vector<pair<TypePtr, uint64_t> > seen;
while (!pending.empty()) { TypePtr record = pa11::strip_cv(pending.back().first); uint64_t base_offset = pending.back().second; pending.pop_back(); if (record.get() == NULL || record->kind != TypeKind::Record) continue; bool already = false; for (size_t i = 0; i < seen.size(); ++i) if (pa11::same_type(seen[i].first, record) && seen[i].second == base_offset) already = true; if (already) continue; seen.push_back(make_pair(record, base_offset)); pa11::layout_record_type(record); vector<TypePtr> bases = pa11::record_direct_bases(record); for (size_t i = 0; i < bases.size(); ++i) { TypePtr direct = bases[i].get() != NULL ? pa11::strip_cv(bases[i]) : TypePtr(); if (direct.get() == NULL || direct->kind != TypeKind::Record) continue; uint64_t offset = pa11::record_direct_base_is_virtual(record, i) ? pa11::record_virtual_base_offset(root, direct) : base_offset + pa11::record_direct_base_offset(record, direct); if (pa11::same_type(direct, wanted)) return offset; pending.push_back(make_pair(direct, offset)); } }
return 0; }
bool target_is_virtual_base_subobject(TypePtr source, TypePtr target)
{ TypePtr bare = source.get() != NULL ? pa11::strip_cv(source) : TypePtr(); TypePtr wanted = target.get() != NULL ? pa11::strip_cv(target) : TypePtr(); if (bare.get() == NULL || bare->kind != TypeKind::Record || wanted.get() == NULL || wanted->kind != TypeKind::Record) return false; vector<TypePtr> vbases = pa11::record_virtual_bases(bare); for (size_t i = 0; i < vbases.size(); ++i) if (pa11::same_type(pa11::strip_cv(vbases[i]), wanted)) return true; return false; }
vector<size_t> hidden_virtual_base_slot_store_order(
	const vector<TypePtr>& bases)
{
	vector<size_t> order;
	for (size_t i = 0; i < bases.size(); ++i)
		order.push_back(i);
	stable_sort(order.begin(), order.end(),
	            [&bases](size_t lhs, size_t rhs) {
		TypePtr left = bases[lhs].get() != NULL
			? pa11::strip_cv(bases[lhs]) : TypePtr();
		TypePtr right = bases[rhs].get() != NULL
			? pa11::strip_cv(bases[rhs]) : TypePtr();
		bool left_contains_right =
			left.get() != NULL && right.get() != NULL &&
			record_has_base_subobject(left, right);
		bool right_contains_left =
			left.get() != NULL && right.get() != NULL &&
			record_has_base_subobject(right, left);
		if (left_contains_right != right_contains_left)
			return right_contains_left;
		return false;
	});
	return order;
}
Binding* find_record_copy_move_constructor(TypePtr type, bool move) { TypePtr bare = pa11::strip_cv(type); if (bare->kind != TypeKind::Record || bare->scope == NULL)
return NULL; map<string, vector<Binding*> >::const_iterator found = bare->scope->members.find(bare->scope->name); if (found == bare->scope->members.end())
return NULL; for (size_t i = 0; i < found->second.size(); ++i) { Binding* binding = found->second[i];
if (binding->kind != BindingKind::Function || binding->type->kind != TypeKind::Function || binding->type->parameters.size() != 2 || !is_reference(binding->type->parameters[1]))
continue; TypePtr param = binding->type->parameters[1]; if (move && param->kind != TypeKind::RValueReference) continue;
if (!move && param->kind != TypeKind::LValueReference) continue; if (pa11::same_type(pa11::strip_cv(param->base), bare)) return binding;
} return NULL; } Binding* find_record_copy_move_assignment(TypePtr type, bool move)
{ TypePtr bare = pa11::strip_cv(type); if (bare->kind != TypeKind::Record || bare->scope == NULL) return NULL;
map<string, vector<Binding*> >::const_iterator found = bare->scope->members.find("operator="); if (found == bare->scope->members.end()) return NULL;
for (size_t i = 0; i < found->second.size(); ++i) { Binding* binding = found->second[i]; if (binding->kind != BindingKind::Function ||
binding->type->kind != TypeKind::Function || binding->type->parameters.size() != 2 || !is_reference(binding->type->parameters[1])) continue;
TypePtr param = binding->type->parameters[1]; if (move && param->kind != TypeKind::RValueReference) continue; if (!move && param->kind != TypeKind::LValueReference)
continue; if (pa11::same_type(pa11::strip_cv(param->base), bare)) return binding; }
return NULL; } void FunctionLowerer::collect_label_cleanup_depths(const Node& node, size_t depth) {
if (starts_with(node.line, "labeled-statement ")) {
string label = node.line.substr(18);
label_cleanup_depths_[label] = depth;
if (!node.children.empty()) collect_label_cleanup_depths(node.children[0], depth);
return; }
if (starts_with(node.line, "compound-statement")) {
for (size_t i = 0; i < node.children.size(); ++i)
collect_label_cleanup_depths(node.children[i], depth + 1);
return; }
if (starts_with(node.line, "try-statement")) {
if (!node.children.empty() && !node.children[0].children.empty())
collect_label_cleanup_depths(node.children[0].children[0], depth + 1);
for (size_t i = 1; i < node.children.size(); ++i)
if (!node.children[i].children.empty()) collect_label_cleanup_depths(node.children[i].children[0], depth + 1);
return; }
for (size_t i = 0; i < node.children.size(); ++i)
collect_label_cleanup_depths(node.children[i], depth);
} void FunctionLowerer::emit_goto_cleanups(const string& label) {
map<string, size_t>::const_iterator found = label_cleanup_depths_.find(label);
if (found == label_cleanup_depths_.end() || found->second >= cleanups_.size())
return;
for (size_t i = cleanups_.size(); i > found->second; --i)
emit_scope_cleanups(cleanups_[i - 1]);
} FunctionLowerer::FunctionLowerer(ProgramLowerer& program, const Node& fn, bool destructor_base_entry) : program_(program),
fn_(fn), destructor_base_entry_(destructor_base_entry), current_(NULL), temp_counter_(0), block_counter_(0),
aux_slot_counter_(0), eh_try_depth_(0), call_temp_cleanup_defer_depth_(0), logical_call_result_consumed_(false),
call_result_store_addr_(), call_result_store_consumed_(false), record_return_slot_(), lowering_record_return_object_(false), lowering_array_subobject_init_(false),
constructor_destination_before_protected_try_(false) { collect_label_cleanup_depths(fn_, 1); } void FunctionLowerer::add_slot(const string& name, const string& type)
{ if (starts_with(name, "__begin") || starts_with(name, "__end")) out_.has_range_for_state = true; out_.slots.push_back("  slot $" + name + " : " + type); } string FunctionLowerer::slot_for(const Binding* binding)
{ map<const Binding*, string>::const_iterator found = slots_.find(binding); if (found != slots_.end()) return found->second;
string base = binding != NULL && !binding->name.empty() ? binding->name : "__param" + to_string(slots_.size()); int& count = slot_names_[base]; ++count;
string name = base; if (count > 1) name += "__shadow" + to_string(count); slots_[binding] = name;
add_slot(name, slot_lowir_type(binding->type)); return name; } string FunctionLowerer::fresh_temp()
{ ++temp_counter_; return "%t" + to_string(temp_counter_); }
string FunctionLowerer::fresh_block(const string& prefix) { ++block_counter_; return prefix + "_" + to_string(block_counter_);
} string FunctionLowerer::fresh_aux_slot(const string& prefix, const string& type) { ++aux_slot_counter_;
string name = prefix + "__" + to_string(aux_slot_counter_); add_slot(name, type); return name; }
void FunctionLowerer::start_block(const string& name) { blocks_.push_back(unique_ptr<Block>(new Block(name))); current_ = blocks_.back().get();
} void FunctionLowerer::instr(const string& text) { if (current_ == NULL || current_->terminated)
return; current_->instrs.push_back("    " + text); } Value FunctionLowerer::emit_base_subobject_addr(Value object,
TypePtr source, TypePtr target) { TypePtr bare = source.get() != NULL ? pa11::strip_cv(source) : TypePtr(); if (bare.get() != NULL && bare->kind == TypeKind::Record && bare->is_polymorphic && target_is_virtual_base_subobject(bare, target)) { string vptr = fresh_temp(); instr(vptr + " = load ptr " + object.text); string offset_addr = fresh_temp(); instr(offset_addr + " = index i8 " + vptr + ", -" + to_string(vtable_address_point_offset(bare))); string offset = fresh_temp(); instr(offset + " = load i64 " + offset_addr); string addr = fresh_temp(); instr(addr + " = index i8 " + object.text + ", " + offset); return Value("ptr", addr); } string addr = fresh_temp();
instr(addr + " = index i8 [projection=base_subobject] " + object.text + ", " + to_string(base_subobject_offset(source, target))); return Value("ptr", addr); }
const Binding* FunctionLowerer::hidden_virtual_base_parameter_binding(
	const Node& expr) const
{
	if (expr.binding != NULL &&
	    expr.binding->kind == BindingKind::Parameter)
		return expr.binding;
	if (starts_with(expr.line, "unary-expression") &&
	    expr.has_op && expr.op == OP_STAR &&
	    !expr.children.empty() &&
	    expr.children[0].binding != NULL &&
	    expr.children[0].binding->kind == BindingKind::Parameter)
		return expr.children[0].binding;
	if ((starts_with(expr.line, "cast-expression") ||
	     starts_with(expr.line, "parenthesized-expression")) &&
	    expr.children.size() == 1)
		return hidden_virtual_base_parameter_binding(expr.children[0]);
	return NULL;
}

bool FunctionLowerer::hidden_virtual_base_argument_for_parameter(
	const Binding* binding,
	TypePtr target,
	string& hidden_base,
	TypePtr& hidden_base_record)
{
	hidden_base.clear();
	hidden_base_record = TypePtr();
	if (binding == NULL || target.get() == NULL)
		return false;
	TypePtr target_record = pa11::strip_cv(target);
	if (target_record.get() == NULL ||
	    target_record->kind != TypeKind::Record ||
	    fn_.binding == NULL ||
	    fn_.binding->type.get() == NULL ||
	    fn_.binding->type->kind != TypeKind::Function)
		return false;
	TypePtr fn_type = fn_.binding->type;
	size_t param_index = 0;
	size_t hidden_pvb_index = 0;
	for (size_t i = 0; i < fn_.children.size(); ++i)
	{
		if (!starts_with(fn_.children[i].line, "parameter "))
			continue;
		Binding* candidate = fn_.children[i].binding;
		TypePtr ptype = param_index < fn_type->parameters.size()
			? fn_type->parameters[param_index]
			: (candidate != NULL ? candidate->type : TypePtr());
		bool member_this_param =
			fn_.binding->owner != NULL &&
			fn_.binding->owner->kind == ScopeKind::Class &&
			!fn_.binding->is_static_member &&
			param_index == 0;
		if (member_this_param)
		{
			if (candidate == binding &&
			    !is_class_constructor_binding(fn_.binding) &&
			    !is_class_destructor_binding(fn_.binding))
			{
				vector<TypePtr> vbases =
					hidden_virtual_bases_for_record(
						class_record_for_member(fn_.binding));
				for (size_t v = 0; v < vbases.size(); ++v)
				{
					TypePtr hidden_record = pa11::strip_cv(vbases[v]);
					if (hidden_record.get() != NULL &&
					    (pa11::same_type(hidden_record, target_record) ||
					     record_has_base_subobject(hidden_record,
					                               target_record)))
					{
						hidden_base = "%__vbptr" + to_string(v);
						hidden_base_record = hidden_record;
						return true;
					}
				}
			}
			++param_index;
			continue;
		}
		vector<TypePtr> hidden_vbases =
			program_.hidden_virtual_bases_for_function_parameter(
				fn_.binding, param_index, ptype);
		if (candidate == binding)
		{
			TypePtr pbare = ptype.get() != NULL
				? pa11::strip_cv(ptype) : TypePtr();
			bool record_reference =
				pbare.get() != NULL &&
				(pbare->kind == TypeKind::LValueReference ||
				 pbare->kind == TypeKind::RValueReference) &&
				pa11::strip_cv(pbare->base)->kind == TypeKind::Record;
			if (record_reference)
			{
				vector<TypePtr> slot_vbases =
					hidden_virtual_bases_for_record(
						pa11::strip_cv(pbare->base));
				for (size_t v = 0; v < slot_vbases.size(); ++v)
				{
					TypePtr hidden_record =
						pa11::strip_cv(slot_vbases[v]);
					if (hidden_record.get() != NULL &&
					    (pa11::same_type(hidden_record, target_record) ||
					     record_has_base_subobject(hidden_record,
					                               target_record)))
					{
						hidden_base = fresh_temp();
						instr(hidden_base + " = load ptr $" +
						      slot_for(binding) + "__pvb" +
						      to_string(v));
						hidden_base_record = hidden_record;
						return true;
					}
				}
			}
			for (size_t v = 0; v < hidden_vbases.size(); ++v)
			{
				TypePtr hidden_record =
					pa11::strip_cv(hidden_vbases[v]);
				if (hidden_record.get() != NULL &&
				    (pa11::same_type(hidden_record, target_record) ||
				     record_has_base_subobject(hidden_record,
				                               target_record)))
				{
					hidden_base = "%__pvbptr" +
						to_string(hidden_pvb_index + v);
					hidden_base_record = hidden_record;
					return true;
				}
			}
		}
		hidden_pvb_index += hidden_vbases.size();
		++param_index;
	}
	return false;
}

Value FunctionLowerer::emit_hidden_virtual_base_addr_for_lvalue(
	const Node& expr,
	TypePtr target,
	bool& found,
	TypePtr* hidden_record)
{
	found = false;
	if (hidden_record != NULL)
		*hidden_record = TypePtr();
	const Binding* binding = hidden_virtual_base_parameter_binding(expr);
	string hidden_base;
	TypePtr hidden_base_record;
	if (!hidden_virtual_base_argument_for_parameter(binding,
	                                               target,
	                                               hidden_base,
	                                               hidden_base_record))
		return Value();
	found = true;
	if (hidden_record != NULL)
		*hidden_record = hidden_base_record;
	if (pa11::same_type(pa11::strip_cv(hidden_base_record),
	                    pa11::strip_cv(target)))
		return Value("ptr", hidden_base);
	return emit_base_subobject_addr(Value("ptr", hidden_base),
	                                hidden_base_record,
	                                target);
}
void FunctionLowerer::terminate(const string& text) { if (current_ == NULL || current_->terminated) return;
current_->instrs.push_back("    " + text); current_->terminated = true; } void FunctionLowerer::lower_vptr_store(TypePtr record)
{ TypePtr bare = pa11::strip_cv(record); if (bare->kind != TypeKind::Record || !bare->is_polymorphic) return;
program_.demand_vtable(bare); string self = fresh_temp(); instr(self + " = load ptr $this"); string vt = fresh_temp();
instr(vt + " = addr @" + vtable_symbol_for_record(bare)); string addr_point = fresh_temp(); instr(addr_point + " = index i8 " + vt + ", " + to_string(vtable_address_point_offset(bare))); instr("store ptr " + addr_point + ", " + self);
vector<pair<TypePtr, uint64_t> > views = vtt_ordered_vtable_views(bare); set<uint64_t> stored_view_offsets;
for (size_t i = 0; i < views.size(); ++i) { if (!stored_view_offsets.insert(views[i].second).second) continue; string object = fresh_temp(); instr(object + " = load ptr $this"); string base = fresh_temp(); instr(base + " = index i8 [projection=base_subobject] " + object + ", " + to_string(views[i].second)); string view = fresh_temp(); instr(view + " = addr @" + vtable_view_symbol_for_record(bare, views[i].first, views[i].second)); if (vtable_address_point_offset(bare) != 16) { string view_addr = fresh_temp(); instr(view_addr + " = index i8 " + view + ", " + to_string(vtable_address_point_offset(bare))); view = view_addr; } instr("store ptr " + view + ", " + base); }
} void FunctionLowerer::maybe_lower_constructor_vptr(size_t index, size_t total) { Binding* binding = fn_.binding;
if (!is_class_constructor_binding(binding)) return; TypePtr record = class_record_for_member(binding); if (record.get() == NULL ||
!pa11::strip_cv(record)->is_polymorphic) return; const Node* current = index < total ? &fn_.children[index] : NULL; if (current != NULL && starts_with(current->line, "base-init-action"))
return; lower_vptr_store(record); } void FunctionLowerer::maybe_lower_destructor_epilogue(bool& emitted)
{ Binding* binding = fn_.binding; if (!is_class_destructor_binding(binding) || !binding->is_virtual) return;
TypePtr record = class_record_for_member(binding); TypePtr bare = record.get() != NULL ? pa11::strip_cv(record) : TypePtr(); if (bare.get() == NULL || bare->kind != TypeKind::Record) return;
pa11::layout_record_type(bare); for (size_t n = 0; n < bare->fields.size(); ++n) { size_t i = bare->fields.size() - 1 - n;
Binding* field = bare->fields[i]; function<Value()> field_addr = [this, field]() { string this_ptr = fresh_temp(); instr(this_ptr + " = load ptr $this");
string addr = fresh_temp(); instr(addr + " = index i8 [projection=field] " + this_ptr + ", " + to_string(field->member_offset)); return Value("ptr", addr);
}; lower_destructor_for_object(field_addr, field->type); emitted = true; }
vector<TypePtr> bases = pa11::record_direct_bases(bare); for (size_t n = 0; n < bases.size(); ++n) { size_t i = bases.size() - 1 - n; TypePtr base = pa11::strip_cv(bases[i]); if (destructor_base_entry_ && target_is_virtual_base_subobject(bare, base)) continue; Node action("base-fini-action " + base->name); action.type = base; lower_base_fini(action); emitted = true; } }
FunctionOut FunctionLowerer::lower() { Binding* binding = fn_.binding; if (binding == NULL)
throw runtime_error("missing function binding"); out_.binding = binding; string name = program_.symbol_for(binding); out_.name = name; TypePtr fn_type = binding->type;
bool indirect_result = pa11::strip_cv(fn_type->base)->kind == TypeKind::Record && record_return_by_address(fn_type->base); ostringstream header;
out_.returns_pointer_result = !indirect_result && scalar_lowir_type(fn_type->base) == "ptr";
	vector<string> raw_parameter_names;
	map<string, int> raw_parameter_counts;
	for (size_t i = 0; i < fn_type->parameters.size(); ++i)
	{
		string pname = i < fn_.children.size() &&
		starts_with(fn_.children[i].line, "parameter ") ? fn_.children[i].line.substr(10) : "";
		size_t space = pname.find(' ');
		pname = space == string::npos ? pname : pname.substr(0, space);
		if ((pname.empty() || pname.compare(0, 7, "__param") == 0) &&
		    i < binding->function_parameter_names.size() &&
		    !binding->function_parameter_names[i].empty() &&
		    binding->function_parameter_names[i].compare(0, 7, "__param") != 0)
			pname = binding->function_parameter_names[i];
		raw_parameter_names.push_back(pname);
		if (!pname.empty())
			++raw_parameter_counts[pname];
	}
	map<string, int> parameter_name_counts;
	map<string, int> raw_parameter_seen;
	header << "function @" << name << "("; if (indirect_result) { header << "%ret : ptr [pass=indirect_result]"; parameter_name_counts["ret"] = 1; } for (size_t i = 0; i < fn_type->parameters.size(); ++i)
	{ if (i != 0 || indirect_result) header << ", "; string pname = raw_parameter_names[i]; if (!pname.empty()) ++raw_parameter_seen[pname];
	if (pname.empty() || raw_parameter_seen[pname] < raw_parameter_counts[pname]) pname = "__param" + to_string(i); int& count = parameter_name_counts[pname]; ++count; if (count > 1) pname += "__shadow" + to_string(count); out_.parameter_names.push_back(pname); TypePtr ptype = fn_type->parameters[i]; header << "%" << pname << " : " << lowir_parameter(ptype);
} size_t hidden_pvb_index = 0; bool member_this_param = fn_.binding->owner != NULL && fn_.binding->owner->kind == ScopeKind::Class && !fn_.binding->is_static_member && !fn_type->parameters.empty(); for (size_t i = member_this_param ? 1 : 0; i < fn_type->parameters.size(); ++i) { vector<TypePtr> vbases = program_.hidden_virtual_bases_for_function_parameter(fn_.binding, i, fn_type->parameters[i]); for (size_t v = 0; v < vbases.size(); ++v) { if (hidden_pvb_index != 0 || !fn_type->parameters.empty() || indirect_result) header << ", "; header << "%__pvbptr" << hidden_pvb_index++ << " : ptr"; } } vector<TypePtr> this_vbases = member_this_param && !is_class_constructor_binding(fn_.binding) && !is_class_destructor_binding(fn_.binding) ? (fn_.binding->is_virtual ? program_.hidden_virtual_bases_for_function_parameter(fn_.binding, 0, fn_type->parameters[0]) : hidden_virtual_bases_for_record(class_record_for_member(fn_.binding))) : vector<TypePtr>(); for (size_t v = 0; v < this_vbases.size(); ++v) { if (hidden_pvb_index != 0 || !fn_type->parameters.empty() || indirect_result || v != 0) header << ", "; header << "%__vbptr" << v << " : ptr"; } header << ") -> " << (indirect_result ? "void" : scalar_lowir_type(fn_type->base)); vector<string> metadata;
if (fn_type->variadic) metadata.push_back("arity=variadic"); if (binding->language_linkage == "c") metadata.push_back("linkage=c");
if (binding->unwind_no) metadata.push_back("unwind=no"); if (binding->name == "__cppgm_init") metadata.push_back("role=init");
else if (binding->name == "__cppgm_fini") metadata.push_back("role=fini"); else if (binding->name == "main") {
metadata.push_back("role=entry"); metadata.push_back("binding=strong"); out_.strong_binding = true; metadata.push_back("keep_alias=yes"); }
else if (binding->name.compare(0, 8, "__lambda") == 0 || binding_has_internal_linkage(binding)) metadata.push_back("binding=internal"); else if (binding->is_inline_definition) metadata.push_back("binding=weak");
else { metadata.push_back("binding=strong"); out_.strong_binding = true; } if (!binding->function_specialization_symbol.empty()) metadata.push_back("object=" + binding->function_specialization_symbol);
else if (binding->name != "main" &&
         binding->name != "__cppgm_init" &&
         binding->name != "__cppgm_fini") {
string object_symbol = binding->language_linkage == "c" ? binding->name : pa12::internal::abi_binding_symbol(binding, map<string, size_t>());
metadata.push_back("object=" + object_symbol); }
if (binding->is_object_root) metadata.push_back("object_root=yes"); header << metadata_suffix(metadata); out_.header = header.str();
if (binding->is_generated_copy_move_assignment && fn_type->parameters.size() == 2 && fn_type->parameters[1]->kind == TypeKind::RValueReference && binding->owner != NULL &&
binding->owner->kind == ScopeKind::Class) { TypePtr record = pa11::record_type_for_scope(binding->owner); if (record.get() != NULL)
{ pa11::layout_record_type(record); for (size_t i = 0; i < record->fields.size(); ++i) {
Binding* ctor = find_record_copy_move_constructor(record->fields[i]->type, true); if (ctor != NULL && ctor->is_inline_definition)
program_.demand_inline_function(ctor); } } }
cleanups_.push_back(vector<Cleanup>()); lower_params(); start_block("entry"); lower_param_stores();
bool noexcept_terminate =
	program_.host_object_lowering &&
	binding->unwind_no &&
	node_may_throw_for_noexcept_wrapper(fn_);
string noexcept_dispatch;
if (noexcept_terminate) {
ensure_noexcept_terminate_helper();
noexcept_dispatch = fresh_block("noexcept_dispatch");
instr("eh_try ^" + noexcept_dispatch);
cleanups_.back().push_back(Cleanup("eh_end"));
}
if (!lower_defaulted_storage_special_member()) for (size_t i = 0; i < fn_.children.size(); ++i) { if (starts_with(fn_.children[i].line, "compound-statement"))
lower_compound(fn_.children[i]); } if (current_ != NULL && !current_->terminated) {
emit_scope_cleanups(cleanups_.back()); if (pa11::is_void_type(fn_type->base) || indirect_result) terminate("return void"); else if (pa11::strip_cv(fn_type->base)->kind == TypeKind::Record)
{ if (record_return_slot_.empty()) record_return_slot_ = fresh_aux_slot("retobj", slot_lowir_type(fn_type->base));
instr("zeroinit " + to_string(pa11::type_size(fn_type->base)) + "x" + to_string(pa11::type_align(fn_type->base)) + " $" + record_return_slot_);
terminate("return " + scalar_lowir_type(fn_type->base) + " $" + record_return_slot_); } else
terminate("return " + scalar_lowir_type(fn_type->base) + " 0"); } if (noexcept_terminate) {
start_block(noexcept_dispatch);
instr("eh_catch_all, 1");
string noexcept_entry = fresh_block("noexcept_terminate");
terminate("jump ^" + noexcept_entry);
start_block(noexcept_entry);
emit_noexcept_terminate_landing(fn_type->base, indirect_result);
} cleanups_.pop_back(); for (size_t i = 0; i < blocks_.size(); ++i)
out_.blocks.push_back(*blocks_[i]); return out_; }

FunctionOut FunctionLowerer::lower_deleting_destructor_entry(
	const string& name,
	const string& header)
{
	Binding* binding = fn_.binding;
	if (binding == NULL)
		throw runtime_error("missing deleting destructor binding");
	out_.binding = binding;
	out_.name = name;
	out_.header = header;
	cleanups_.push_back(vector<Cleanup>());
	lower_params();
	start_block("entry");
	lower_param_stores();
	TypePtr record = class_record_for_member(binding);
	TypePtr bare = record.get() != NULL ? pa11::strip_cv(record) : TypePtr();
	if (bare.get() != NULL && bare->kind == TypeKind::Record &&
	    binding->is_virtual)
		lower_vptr_store(bare);
	for (size_t i = 0; i < fn_.children.size(); ++i)
		if (starts_with(fn_.children[i].line, "compound-statement"))
			lower_deleting_destructor_compound(fn_.children[i]);
	if (current_ != NULL && !current_->terminated)
	{
		emit_scope_cleanups(cleanups_.back());
		lower_deleting_destructor_nonvirtual_bases(bare);
		string del_arg = fresh_temp();
		instr(del_arg + " = load ptr $this");
		instr("call void @operator_delete(" + del_arg + ")");
		terminate("return void");
	}
	cleanups_.pop_back();
	for (size_t i = 0; i < blocks_.size(); ++i)
		out_.blocks.push_back(*blocks_[i]);
	return out_;
}

void FunctionLowerer::lower_deleting_destructor_compound(const Node& node)
{
	cleanups_.push_back(vector<Cleanup>());
	for (size_t i = 0; i < node.children.size(); ++i)
	{
		if (starts_with(node.children[i].line, "base-fini-action") ||
		    starts_with(node.children[i].line, "member-fini-action"))
			continue;
		lower_stmt(node.children[i]);
	}
	if (current_ != NULL && !current_->terminated)
		emit_scope_cleanups(cleanups_.back());
	cleanups_.pop_back();
}

void FunctionLowerer::lower_deleting_destructor_nonvirtual_bases(TypePtr record)
{
	TypePtr bare = record.get() != NULL ? pa11::strip_cv(record) : TypePtr();
	if (bare.get() == NULL || bare->kind != TypeKind::Record)
		return;
	vector<TypePtr> bases = pa11::record_direct_bases(bare);
	for (size_t n = 0; n < bases.size(); ++n)
	{
		size_t i = bases.size() - 1 - n;
		if (pa11::record_direct_base_is_virtual(bare, i))
			continue;
		TypePtr base = bases[i].get() != NULL
			? pa11::strip_cv(bases[i]) : TypePtr();
		if (base.get() == NULL || base->kind != TypeKind::Record)
			continue;
		Binding* base_dtor = find_destructor(base);
		if (base_dtor == NULL || !base_dtor->is_virtual)
			continue;
		program_.demand_function_declaration(base_dtor);
		string base_callee = program_.destructor_symbol_for(base_dtor, true);
		program_.demand_inline_function(base_dtor, false);
		program_.demand_lifecycle_base_entry_declaration(base_dtor);
		string reload = fresh_temp();
		instr(reload + " = load ptr $this");
		string base_addr = fresh_temp();
		instr(base_addr + " = index i8 [projection=base_subobject] " +
		      reload + ", " + to_string(base_subobject_offset(bare, base)));
			vector<string> args;
			args.push_back(base_addr);
			if (!program_.native_lowering &&
			    base->is_polymorphic &&
			    record_uses_virtual_base_vtt(base))
			{
				size_t vtt_slot = construction_vtt_slot_for_direct_base(bare, base);
				if (vtt_slot != static_cast<size_t>(-1))
				{
					string vtt_base = fresh_temp();
					instr(vtt_base + " = addr @" + vtt_symbol_for_record(bare));
					string vtt_arg = vtt_base;
					if (vtt_slot != 0)
					{
						vtt_arg = fresh_temp();
						instr(vtt_arg + " = index i8 " + vtt_base + ", " +
						      to_string(vtt_slot * 8));
					}
					args.push_back(vtt_arg);
				}
				vector<TypePtr> vbases = hidden_virtual_bases_for_record(base);
				for (size_t v = 0; v < vbases.size(); ++v)
				{
					string hidden;
					if (record_has_base_subobject(bare, vbases[v]))
					{
						string this_ptr = fresh_temp();
						instr(this_ptr + " = load ptr $this");
						uint64_t offset = base_subobject_offset(bare, vbases[v]);
						if (offset == 0)
							hidden = this_ptr;
						else
						{
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
			ostringstream call;
		call << "call void @" << base_callee << "(";
		for (size_t a = 0; a < args.size(); ++a)
		{
			if (a != 0)
				call << ", ";
			call << args[a];
		}
		call << ")";
		instr(call.str());
	}
}

void FunctionLowerer::lower_params()
{ TypePtr fn_type = fn_.binding->type; size_t param_index = 0; for (size_t i = 0; i < fn_.children.size(); ++i)
	{ if (!starts_with(fn_.children[i].line, "parameter ")) continue; string pname = fn_.children[i].line.substr(10);
	size_t space = pname.find(' '); pname = space == string::npos ? pname : pname.substr(0, space); string source_name = pname; if (pname.empty()) pname = "__param" + to_string(param_index);
	if (param_index < out_.parameter_names.size()) pname = out_.parameter_names[param_index];
	if (pname.size() > 1 && pname[0] == 't') { int n = 0; bool digits = true;
for (size_t j = 1; j < pname.size(); ++j) if (pname[j] >= '0' && pname[j] <= '9') n = n * 10 + (pname[j] - '0'); else
digits = false; if (digits && n > temp_counter_) temp_counter_ = n; }
Binding* binding = fn_.children[i].binding; TypePtr ptype = fn_type->parameters[param_index]; bool member_this_param = fn_.binding->owner != NULL && fn_.binding->owner->kind == ScopeKind::Class && !fn_.binding->is_static_member && param_index == 0; TypePtr ptype_bare = pa11::strip_cv(ptype); bool pvb_slots = !member_this_param && (ptype_bare->kind == TypeKind::LValueReference || ptype_bare->kind == TypeKind::RValueReference) && pa11::strip_cv(ptype_bare->base)->kind == TypeKind::Record; vector<TypePtr> param_vbases = pvb_slots ? hidden_virtual_bases_for_record(pa11::strip_cv(ptype_bare->base)) : vector<TypePtr>(); if (binding == NULL) {
if (slot_names_[pname] == 0) slot_names_[pname] = 1; add_slot(pname, slot_lowir_type(ptype)); for (size_t v = 0; v < param_vbases.size(); ++v) add_slot(pname + "__pvb" + to_string(v), "ptr"); ++param_index;
} else { slots_[binding] = pname;
if (!source_name.empty() && pname.compare(0, 7, "__param") == 0) { bool duplicate_later = false; size_t later_index = 0; for (size_t j = 0; j < fn_.children.size(); ++j) { if (!starts_with(fn_.children[j].line, "parameter ")) continue; string later_name = fn_.children[j].line.substr(10); size_t later_space = later_name.find(' '); later_name = later_space == string::npos ? later_name : later_name.substr(0, later_space); if (later_index > param_index && later_name == source_name) duplicate_later = true; ++later_index; } if (duplicate_later) slots_[binding] = source_name; }
if (slot_names_[pname] == 0) slot_names_[pname] = 1; add_slot(pname, slot_lowir_type(binding->type)); for (size_t v = 0; v < param_vbases.size(); ++v) add_slot(pname + "__pvb" + to_string(v), "ptr"); if (pa11::strip_cv(ptype)->kind == TypeKind::Record &&
record_pass_by_address(ptype)) by_address_parameters_.insert(binding); ++param_index; }
} } void FunctionLowerer::lower_param_stores()
{
	TypePtr fn_type = fn_.binding->type;
	size_t param_index = 0;
	size_t hidden_pvb_index = 0;
	for (size_t i = 0; i < fn_.children.size(); ++i)
	{
		if (!starts_with(fn_.children[i].line, "parameter "))
			continue;
		string pname = fn_.children[i].line.substr(10);
		size_t space = pname.find(' ');
		pname = space == string::npos ? pname : pname.substr(0, space);
			if (pname.empty())
				pname = "__param" + to_string(param_index);
			if (param_index < out_.parameter_names.size())
				pname = out_.parameter_names[param_index];
			TypePtr ptype = fn_type->parameters[param_index];
		bool member_this_param =
			fn_.binding->owner != NULL &&
			fn_.binding->owner->kind == ScopeKind::Class &&
			!fn_.binding->is_static_member &&
			param_index == 0;
		TypePtr ptype_bare = pa11::strip_cv(ptype);
		vector<TypePtr> hidden_vbases = !member_this_param
			? program_.hidden_virtual_bases_for_function_parameter(
				fn_.binding, param_index, ptype)
			: vector<TypePtr>();
		bool store_pvb_slots =
			!member_this_param &&
			(ptype_bare->kind == TypeKind::LValueReference ||
			 ptype_bare->kind == TypeKind::RValueReference) &&
			pa11::strip_cv(ptype_bare->base)->kind == TypeKind::Record;
		vector<TypePtr> slot_vbases = store_pvb_slots
			? hidden_virtual_bases_for_record(pa11::strip_cv(ptype_bare->base))
			: vector<TypePtr>();
		size_t hidden_start = hidden_pvb_index;
		Binding* binding = fn_.children[i].binding;
		if (pa11::strip_cv(ptype)->kind == TypeKind::Record)
		{
			if (!record_pass_by_address(ptype) &&
			    record_has_storage_copy(ptype))
			{
				string addr = fresh_temp();
				instr(addr + " = addr $" + pname);
				instr("copyobj " + to_string(pa11::type_size(ptype)) +
				      "x" + to_string(pa11::type_align(ptype)) + " %" +
				      pname + ", " + addr);
			}
			if (!cleanups_.empty() && parameter_type_needs_destructor(ptype))
			{
				if (record_pass_by_address(ptype))
					cleanups_.back().push_back(
						Cleanup("%" + pname, ptype, true));
				else if (binding != NULL)
					cleanups_.back().push_back(
						Cleanup(binding, binding->type, true));
			}
		}
		else
			instr("store " + scalar_lowir_type(ptype) + " %" + pname +
			      ", $" + pname);
		if (store_pvb_slots)
		{
			TypePtr context = hidden_virtual_base_context_record(ptype);
			vector<size_t> store_order =
				hidden_virtual_base_slot_store_order(slot_vbases);
			for (size_t n = 0; n < store_order.size(); ++n)
			{
				size_t v = store_order[n];
				size_t selected = hidden_vbases.size();
				for (size_t h = 0; h < hidden_vbases.size(); ++h)
					if (pa11::same_type(pa11::strip_cv(hidden_vbases[h]),
					                    pa11::strip_cv(slot_vbases[v])))
					{
						selected = h;
						break;
					}
				if (selected != hidden_vbases.size())
					instr("store ptr %__pvbptr" +
					      to_string(hidden_start + selected) +
					      ", $" + pname + "__pvb" + to_string(v));
				else
				{
					uint64_t offset =
						base_subobject_offset(context, slot_vbases[v]);
					if (offset == 0)
						instr("store ptr %" + pname + ", $" + pname +
						      "__pvb" + to_string(v));
					else
					{
						string tmp = fresh_temp();
						instr(tmp + " = index i8 %" + pname + ", " +
						      to_string(offset));
						instr("store ptr " + tmp + ", $" + pname +
						      "__pvb" + to_string(v));
					}
				}
			}
		}
		hidden_pvb_index += hidden_vbases.size();
		++param_index;
	}
} bool FunctionLowerer::lower_defaulted_storage_special_member() { Binding* binding = fn_.binding;
if (binding == NULL || !binding->is_defaulted || binding->owner == NULL || binding->owner->kind != ScopeKind::Class ||
binding->type->kind != TypeKind::Function || binding->type->parameters.size() != 2 || !is_reference(binding->type->parameters[1])) return false;
bool special = binding->name == binding->owner->name || binding->name == "operator="; if (!special) return false;
for (size_t i = 0; i < fn_.children.size(); ++i) if (starts_with(fn_.children[i].line, "compound-statement") && !fn_.children[i].children.empty()) return false;
	TypePtr record = pa11::record_type_for_scope(binding->owner); if (record.get() == NULL) return false; if (binding->name == binding->owner->name && pa11::strip_cv(record)->is_polymorphic) return false; string other_name = "__param1";
if (fn_.children.size() > 1 && starts_with(fn_.children[1].line, "parameter ")) { other_name = fn_.children[1].line.substr(10);
size_t space = other_name.find(' '); other_name = space == string::npos ? other_name : other_name.substr(0, space); if (other_name.empty())
other_name = "__param1"; } if (binding->name == "operator=") {
bool move = binding->type->parameters[1]->kind == TypeKind::RValueReference; TypePtr bare = pa11::strip_cv(record); TypePtr direct_base = bare->base.get() != NULL ? pa11::strip_cv(bare->base) : TypePtr();
Binding* base_assign = direct_base.get() != NULL ? find_record_copy_move_assignment(direct_base, move) : NULL; if (base_assign != NULL) {
program_.demand_function_declaration(base_assign); program_.demand_inline_function(base_assign); string self = fresh_temp(); instr(self + " = load ptr $this");
string self_base = emit_base_subobject_addr(Value("ptr", self), record, direct_base).text;
string other = fresh_temp(); instr(other + " = load ptr $" + other_name); string other_base = emit_base_subobject_addr(Value("ptr", other),
record, direct_base).text; string ignored = fresh_temp(); instr(ignored + " = call ptr @" + program_.symbol_for(base_assign) +
"(" + self_base + ", " + other_base + ")"); string ret = fresh_temp(); instr(ret + " = load ptr $this"); terminate("return ptr " + ret);
return true; } } if (record_has_storage_copy(record))
{ string self = fresh_temp(); string other = fresh_temp(); instr(self + " = load ptr $this");
instr(other + " = load ptr $" + other_name); instr("copyobj " + to_string(pa11::type_size(record)) + "x" + to_string(pa11::type_align(record)) + " " + other + ", " + self); }
if (binding->name == "operator=") { string ret = fresh_temp(); instr(ret + " = load ptr $this");
terminate("return ptr " + ret); } else terminate("return void");
return true; } bool FunctionLowerer::compound_has_constructor_init_action(const Node& node) const {
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
	if (binding != NULL && is_reference(binding->type)) {
		string local_slot = slot_for(binding);
		instr("store ptr " + caught + ", $" + local_slot);
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
