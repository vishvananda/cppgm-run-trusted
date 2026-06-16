#include "pa14_lowir_internal.h"
#include "pa12_templates_function_support.h"
#include <algorithm>
#include <utility>
namespace pa14 { namespace internal { bool node_contains_call_expression(const Node& node) {
if (starts_with(node.line, "call-expression")) return true; for (size_t i = 0; i < node.children.size(); ++i) if (node_contains_call_expression(node.children[i]))
return true; return false; } bool node_contains_return_statement(const Node& node)
{ if (starts_with(node.line, "return-statement")) return true; for (size_t i = 0; i < node.children.size(); ++i)
if (node_contains_return_statement(node.children[i])) return true; return false; }
bool lowir_function_definition_body_empty(const Node& node)
{
	return !node.children.empty() &&
	       starts_with(node.children.back().line, "compound-statement") &&
	       node.children.back().children.empty();
}
bool registered_constructor_body_nonempty(const ProgramLowerer& program,
                                          const Binding* binding)
{
	if (binding == NULL)
		return false;
	map<const Binding*, const Node*>::const_iterator found =
		program.inline_definitions.find(binding);
	if (found != program.inline_definitions.end() &&
	    !lowir_function_definition_body_empty(*found->second))
		return true;
	if (binding->aliased_binding != NULL)
		return registered_constructor_body_nonempty(program,
		                                            binding->aliased_binding);
	return false;
}
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
}

void FunctionLowerer::ensure_unexpected_runtime_declaration()
{
	demand_host_eh_declarations(program_, false);
	if (program_.declared_functions.insert(
		    "__external_runtime____cxa_call_unexpected").second)
		program_.declares.push_back(
			"declare function @__external_runtime____cxa_call_unexpected"
			"(%arg0 : ptr) -> void [return=noreturn, "
			"role=eh_call_unexpected, linkage=c, binding=strong, "
			"object=__cxa_call_unexpected]");
}

void FunctionLowerer::emit_dynamic_exception_filter(const Binding* binding)
{
	vector<string> rttis;
	if (binding != NULL)
	{
		for (size_t i = 0; i < binding->dynamic_exception_types.size(); ++i)
		{
			TypePtr object = object_type(binding->dynamic_exception_types[i]);
			program_.emit_typeinfo(object);
			string rtti = program_.catch_rtti_symbol(object);
			if (!rtti.empty())
				rttis.push_back(rtti);
		}
	}
	if (rttis.empty())
	{
		instr("eh_catch_all, 1");
		return;
	}
	string line = "eh_filter";
	for (size_t i = 0; i < rttis.size(); ++i)
	{
		line += i == 0 ? " @" : ", @";
		line += rttis[i];
	}
	line += ", 1";
	instr(line);
}

void FunctionLowerer::emit_noexcept_terminate_landing(TypePtr ret,
                                                        bool indirect_result) {
string exception = fresh_temp();
instr(exception + " = exception ptr");
instr("call void @cppgm_call_terminate(" + exception + ")");
if (pa11::is_void_type(ret) || indirect_result ||
    pa11::strip_cv(ret)->kind == TypeKind::Record)
terminate("return void");
else
terminate("return " + scalar_lowir_type(ret) + " 0");
}

void FunctionLowerer::emit_unexpected_landing(TypePtr ret,
                                              bool indirect_result)
{
	string exception = fresh_temp();
	instr(exception + " = exception ptr");
	string selector = fresh_temp();
	instr(selector + " = exception_selector i32");
	string selected = fresh_temp();
	instr(selected + " = cmp eq i32 " + selector + ", -1");
	string unexpected = fresh_block("unexpected_call");
	string resume_block = fresh_block("unexpected_resume");
	terminate("branch " + selected + ", ^" + unexpected + ", ^" +
	          resume_block);
	start_block(resume_block);
	terminate("resume");
	start_block(unexpected);
	instr("call void @__external_runtime____cxa_call_unexpected(" +
	      exception + ")");
	if (pa11::is_void_type(ret) || indirect_result ||
	    pa11::strip_cv(ret)->kind == TypeKind::Record)
		terminate("return void");
	else
		terminate("return " + scalar_lowir_type(ret) + " 0");
}

bool record_has_default_constructor_for_array(TypePtr type) { TypePtr bare = pa11::strip_cv(type);
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
bool record_has_base_subobject(TypePtr source, TypePtr target)
{
	if (source.get() == NULL || target.get() == NULL)
		return false;
	TypePtr bare = pa11::strip_cv(source);
	TypePtr wanted = pa11::strip_cv(target);
	if (bare->kind != TypeKind::Record || wanted->kind != TypeKind::Record)
		return false;
	vector<TypePtr> bases = pa11::record_direct_bases(bare);
	for (size_t i = 0; i < bases.size(); ++i)
	{
		TypePtr stripped = bases[i].get() != NULL
			? pa11::strip_cv(bases[i]) : TypePtr();
		if (stripped.get() == NULL)
			continue;
		if (pa11::same_type(stripped, wanted))
			return true;
		if (record_has_base_subobject(stripped, wanted))
			return true;
	}
	return false;
}
uint64_t base_subobject_offset(TypePtr source, TypePtr target)
{
	if (source.get() == NULL || target.get() == NULL)
		return 0;
	TypePtr root = pa11::strip_cv(source);
	TypePtr wanted = pa11::strip_cv(target);
	if (root->kind != TypeKind::Record || wanted->kind != TypeKind::Record)
		return 0;
	vector<pair<TypePtr, uint64_t> > pending;
	pending.push_back(make_pair(root, 0));
	vector<pair<TypePtr, uint64_t> > seen;
	while (!pending.empty())
	{
		TypePtr record = pa11::strip_cv(pending.back().first);
		uint64_t base_offset = pending.back().second;
		pending.pop_back();
		if (record.get() == NULL || record->kind != TypeKind::Record)
			continue;
		bool already = false;
		for (size_t i = 0; i < seen.size(); ++i)
			if (pa11::same_type(seen[i].first, record) &&
			    seen[i].second == base_offset)
				already = true;
		if (already)
			continue;
		seen.push_back(make_pair(record, base_offset));
		pa11::layout_record_type(record);
		vector<TypePtr> bases = pa11::record_direct_bases(record);
		for (size_t i = 0; i < bases.size(); ++i)
		{
			TypePtr direct = bases[i].get() != NULL
				? pa11::strip_cv(bases[i]) : TypePtr();
			if (direct.get() == NULL || direct->kind != TypeKind::Record)
				continue;
			uint64_t offset = pa11::record_direct_base_is_virtual(record, i)
				? pa11::record_virtual_base_offset(root, direct)
				: base_offset + pa11::record_direct_base_offset(record, direct);
			if (pa11::same_type(direct, wanted))
				return offset;
			pending.push_back(make_pair(direct, offset));
		}
	}
	return 0;
}
bool target_is_virtual_base_subobject(TypePtr source, TypePtr target)
{
	TypePtr bare = source.get() != NULL ? pa11::strip_cv(source) : TypePtr();
	TypePtr wanted = target.get() != NULL ? pa11::strip_cv(target) : TypePtr();
	if (bare.get() == NULL || bare->kind != TypeKind::Record ||
	    wanted.get() == NULL || wanted->kind != TypeKind::Record)
		return false;
	vector<TypePtr> vbases = pa11::record_virtual_bases(bare);
	for (size_t i = 0; i < vbases.size(); ++i)
		if (pa11::same_type(pa11::strip_cv(vbases[i]), wanted))
			return true;
	return false;
}
TypePtr virtual_base_containing_subobject(TypePtr source,
                                          TypePtr target,
                                          size_t& index,
                                          uint64_t& nested_offset)
{
	index = 0;
	nested_offset = 0;
	TypePtr bare = source.get() != NULL ? pa11::strip_cv(source) : TypePtr();
	TypePtr wanted = target.get() != NULL ? pa11::strip_cv(target) : TypePtr();
	if (bare.get() == NULL || bare->kind != TypeKind::Record ||
	    wanted.get() == NULL || wanted->kind != TypeKind::Record)
		return TypePtr();
	vector<TypePtr> vbases = pa11::record_virtual_bases(bare);
	for (size_t i = 0; i < vbases.size(); ++i)
	{
		TypePtr vbase = pa11::strip_cv(vbases[i]);
		if (pa11::same_type(vbase, wanted))
		{
			index = i;
			return vbase;
		}
		if (record_has_base_subobject(vbase, wanted))
		{
			index = i;
			nested_offset = base_subobject_offset(vbase, wanted);
			return vbase;
		}
	}
	return TypePtr();
}
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
return; current_->instrs.push_back("    " + text); }

Value FunctionLowerer::emit_base_subobject_addr(Value object,
                                                TypePtr source,
                                                TypePtr target)
{
	TypePtr bare = source.get() != NULL ? pa11::strip_cv(source) : TypePtr();
	if (bare.get() != NULL && bare->kind == TypeKind::Record &&
	    bare->is_polymorphic)
	{
		size_t vbase_index = 0;
		uint64_t nested_offset = 0;
		TypePtr vbase = virtual_base_containing_subobject(bare,
		                                                  target,
		                                                  vbase_index,
		                                                  nested_offset);
		if (vbase.get() != NULL)
		{
			string vptr = fresh_temp();
			instr(vptr + " = load ptr " + object.text);
			uint64_t slot_offset =
				vtable_address_point_offset(bare) - vbase_index * 8;
			string offset_addr = fresh_temp();
			instr(offset_addr + " = index i8 " + vptr + ", -" +
			      to_string(slot_offset));
			string offset = fresh_temp();
			instr(offset + " = load i64 " + offset_addr);
			string addr = fresh_temp();
			instr(addr + " = index i8 " + object.text + ", " + offset);
			if (nested_offset == 0)
				return Value("ptr", addr);
			string nested = fresh_temp();
			instr(nested + " = index i8 [projection=base_subobject] " +
			      addr + ", " + to_string(nested_offset));
			return Value("ptr", nested);
		}
	}
	string addr = fresh_temp();
	instr(addr + " = index i8 [projection=base_subobject] " + object.text +
	      ", " + to_string(base_subobject_offset(source, target)));
	return Value("ptr", addr);
}
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
if (record_uses_hosted_external_stream_vtable(bare)) return;
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
throw runtime_error("missing function binding"); if (is_class_constructor_binding(binding)) { bool noop_body = lowir_function_definition_body_empty(fn_); if (noop_body && binding->is_generated_default_constructor && binding->is_defaulted && registered_constructor_body_nonempty(program_, binding)) noop_body = false; binding->is_noop_constructor = noop_body; } out_.binding = binding; string name = program_.symbol_for(binding); out_.name = name; TypePtr fn_type = binding->type;
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
	header << "function @" << name << "(";
	if (indirect_result)
	{
		header << "%ret : ptr [pass=indirect_result]";
		parameter_name_counts["ret"] = 1;
	}
	for (size_t i = 0; i < fn_type->parameters.size(); ++i)
	{
		if (i != 0 || indirect_result)
			header << ", ";
		string pname = raw_parameter_names[i];
		if (!pname.empty())
			++raw_parameter_seen[pname];
		if (pname.empty() ||
		    raw_parameter_seen[pname] < raw_parameter_counts[pname])
			pname = "__param" + to_string(i);
		int& count = parameter_name_counts[pname];
		++count;
		if (count > 1)
			pname += "__shadow" + to_string(count);
		out_.parameter_names.push_back(pname);
		TypePtr ptype = fn_type->parameters[i];
		header << "%" << pname << " : " << lowir_parameter(ptype);
	}
	size_t hidden_pvb_index = 0;
	bool member_this_param =
		fn_.binding->owner != NULL &&
		fn_.binding->owner->kind == ScopeKind::Class &&
		!fn_.binding->is_static_member &&
		!fn_type->parameters.empty();
	for (size_t i = member_this_param ? 1 : 0;
	     i < fn_type->parameters.size();
	     ++i)
	{
		vector<TypePtr> vbases =
			program_.hidden_virtual_bases_for_function_parameter(
				fn_.binding, i, fn_type->parameters[i]);
		for (size_t v = 0; v < vbases.size(); ++v)
		{
			if (hidden_pvb_index != 0 ||
			    !fn_type->parameters.empty() ||
			    indirect_result)
				header << ", ";
			header << "%__pvbptr" << hidden_pvb_index++ << " : ptr";
		}
	}
	vector<TypePtr> this_vbases =
		member_this_param &&
		!is_class_constructor_binding(fn_.binding) &&
		!is_class_destructor_binding(fn_.binding)
		? (fn_.binding->is_virtual
		   ? program_.hidden_virtual_bases_for_function_parameter(
			   fn_.binding, 0, fn_type->parameters[0])
		   : hidden_virtual_bases_for_record(class_record_for_member(fn_.binding)))
		: vector<TypePtr>();
	for (size_t v = 0; v < this_vbases.size(); ++v)
	{
		if (hidden_pvb_index != 0 ||
		    !fn_type->parameters.empty() ||
		    indirect_result ||
		    v != 0)
			header << ", ";
		header << "%__vbptr" << v << " : ptr";
	}
	header << ") -> "
	       << (indirect_result ? "void" : scalar_lowir_type(fn_type->base));
	vector<string> metadata;
	if (fn_type->variadic)
		metadata.push_back("arity=variadic");
	if (binding->language_linkage == "c")
		metadata.push_back("linkage=c");
	if (binding->unwind_no)
		metadata.push_back("unwind=no");
	if (binding->name == "__cppgm_init")
	{
		metadata.push_back("role=init");
		metadata.push_back("binding=internal");
	}
	else if (binding->name == "__cppgm_fini")
	{
		metadata.push_back("role=fini");
		metadata.push_back("binding=internal");
	}
	else if (binding->name == "main")
	{
		metadata.push_back("role=entry");
		metadata.push_back("binding=strong");
		out_.strong_binding = true;
		metadata.push_back("keep_alias=yes");
	}
	else if (binding->name.compare(0, 8, "__lambda") == 0 ||
	         binding_has_internal_linkage(binding))
		metadata.push_back("binding=internal");
		else if (binding->is_inline_definition ||
		         (binding_has_template_specialization_context(binding) &&
		          !binding->is_explicit_specialization_member))
			metadata.push_back("binding=weak");
	else
	{
		metadata.push_back("binding=strong");
		out_.strong_binding = true;
	}
if (binding->name != "main" &&
    binding->name != "__cppgm_init" &&
    binding->name != "__cppgm_fini") {
string object_symbol = global_object_symbol(binding);
if (!object_symbol.empty())
	metadata.push_back("object=" + object_symbol); }
	if (program_.host_object_lowering &&
	    binding->is_generated_default_constructor)
		metadata.push_back("generated_default_ctor=yes");
	if (binding->is_object_root && !binding->is_defaulted) metadata.push_back("object_root=yes"); header << metadata_suffix(metadata); out_.header = header.str();
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
bool unexpected_wrapper =
	program_.host_object_lowering &&
	binding->dynamic_exception_spec &&
	node_may_throw_for_noexcept_wrapper(fn_);
string noexcept_dispatch;
if (noexcept_terminate || unexpected_wrapper) {
if (unexpected_wrapper)
ensure_unexpected_runtime_declaration();
else
ensure_noexcept_terminate_helper();
noexcept_dispatch = fresh_block("noexcept_dispatch");
instr("eh_try ^" + noexcept_dispatch);
cleanups_.back().push_back(Cleanup("eh_end"));
}
if (!lower_hosted_vector_bool_move_body() && !lower_defaulted_storage_special_member()) for (size_t i = 0; i < fn_.children.size(); ++i) { if (starts_with(fn_.children[i].line, "compound-statement"))
lower_compound(fn_.children[i]); } if (current_ != NULL && !current_->terminated) {
emit_scope_cleanups(cleanups_.back()); if (pa11::is_void_type(fn_type->base) || indirect_result) terminate("return void"); else if (pa11::strip_cv(fn_type->base)->kind == TypeKind::Record)
{ if (record_return_slot_.empty()) record_return_slot_ = fresh_aux_slot("retobj", slot_lowir_type(fn_type->base));
instr("zeroinit " + to_string(pa11::type_size(fn_type->base)) + "x" + to_string(pa11::type_align(fn_type->base)) + " $" + record_return_slot_);
terminate("return " + scalar_lowir_type(fn_type->base) + " $" + record_return_slot_); } else
terminate("return " + scalar_lowir_type(fn_type->base) + " 0"); } if (noexcept_terminate || unexpected_wrapper) {
start_block(noexcept_dispatch);
if (unexpected_wrapper)
emit_dynamic_exception_filter(binding);
else
instr("eh_catch_all, 1");
string noexcept_entry =
	fresh_block(unexpected_wrapper ? "unexpected_spec" : "noexcept_terminate");
terminate("jump ^" + noexcept_entry);
start_block(noexcept_entry);
if (unexpected_wrapper)
emit_unexpected_landing(fn_type->base, indirect_result);
else
emit_noexcept_terminate_landing(fn_type->base, indirect_result);
} cleanups_.pop_back(); for (size_t i = 0; i < blocks_.size(); ++i)
out_.blocks.push_back(*blocks_[i]);
return out_; }

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
} else { slots_[binding] = pname; binding->type = ptype;
if (!source_name.empty() && pname.compare(0, 7, "__param") == 0) { bool duplicate_later = false; size_t later_index = 0; for (size_t j = 0; j < fn_.children.size(); ++j) { if (!starts_with(fn_.children[j].line, "parameter ")) continue; string later_name = fn_.children[j].line.substr(10); size_t later_space = later_name.find(' '); later_name = later_space == string::npos ? later_name : later_name.substr(0, later_space); if (later_index > param_index && later_name == source_name) duplicate_later = true; ++later_index; } if (duplicate_later) slots_[binding] = source_name; }
if (slot_names_[pname] == 0) slot_names_[pname] = 1; add_slot(pname, slot_lowir_type(ptype)); for (size_t v = 0; v < param_vbases.size(); ++v) add_slot(pname + "__pvb" + to_string(v), "ptr"); if (pa11::strip_cv(ptype)->kind == TypeKind::Record &&
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
						Cleanup(binding, ptype, true));
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
}

void append_assignment_dependency_members(TypePtr record, vector<Binding*>& members)
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

uint64_t assignment_storage_copy_limit(TypePtr record)
{
	TypePtr bare = record.get() != NULL ? pa11::strip_cv(record) : TypePtr();
	if (bare.get() == NULL || bare->kind != TypeKind::Record)
		return 0;
	pa11::layout_record_type(bare);
	uint64_t limit = 0;
	for (size_t i = 0; i < bare->fields.size(); ++i)
		if (record_has_storage_copy(bare->fields[i]->type))
		{
			uint64_t end = bare->fields[i]->member_offset +
			               pa11::type_size(bare->fields[i]->type);
			if (end > limit)
				limit = end;
		}
	return limit;
}

uint64_t assignment_member_storage_end(Binding* member)
{
	if (member == NULL)
		return 0;
	if (!record_has_storage_copy(member->type))
		return member->member_offset;
	return member->member_offset + pa11::type_size(member->type);
}

bool FunctionLowerer::lower_defaulted_assignment_fields(TypePtr record,
                                                        bool move,
                                                        const string& other_name)
{
	TypePtr bare = pa11::strip_cv(record);
	if (bare->kind != TypeKind::Record)
		return false;
	pa11::layout_record_type(bare);
	vector<Binding*> members;
	append_assignment_dependency_members(bare, members);
	vector<pair<Binding*, Binding*> > field_ops;
	for (size_t i = 0; i < members.size(); ++i)
	{
		TypePtr field_type = pa11::strip_cv(members[i]->type);
		Binding* op = field_type->kind == TypeKind::Record
			? program_.demand_implicit_copy_assignment(field_type, move)
			: find_record_copy_move_assignment(members[i]->type, move);
		if (op == NULL && move)
			op = field_type->kind == TypeKind::Record
				? program_.demand_implicit_copy_assignment(field_type, false)
				: find_record_copy_move_assignment(members[i]->type,
				                                   false);
		if (op == NULL)
			continue;
		field_ops.push_back(make_pair(members[i], op));
	}
	if (field_ops.empty())
	{
		for (size_t i = 0; i < members.size(); ++i)
		{
			bool storage_field = false;
			for (size_t j = 0; j < bare->fields.size(); ++j)
				if (bare->fields[j] == members[i])
					storage_field = true;
			TypePtr field_type = pa11::strip_cv(members[i]->type);
			if (storage_field || field_type->kind != TypeKind::Record)
				continue;
			program_.demand_implicit_copy_assignment(field_type, move);
			string self = fresh_temp();
			string other = fresh_temp();
			instr(self + " = load ptr $this");
			instr(other + " = load ptr $" + other_name);
			if (members[i]->member_offset != 0)
				instr("copyobj " + to_string(members[i]->member_offset) +
				      "x" + to_string(pa11::type_align(bare)) + " " +
				      other + ", " + self);
			return true;
		}
		return false;
	}
	string self = fresh_temp();
	string other = fresh_temp();
	instr(self + " = load ptr $this");
	instr(other + " = load ptr $" + other_name);
	uint64_t cursor = 0;
	for (size_t i = 0; i < field_ops.size(); ++i)
	{
		Binding* field = field_ops[i].first;
		Binding* op = field_ops[i].second;
		uint64_t offset = field->member_offset;
		if (offset > cursor)
		{
			string self_chunk = fresh_temp();
			string other_chunk = fresh_temp();
			instr(self_chunk + " = index i8 " + self + ", " +
			      to_string(cursor));
			instr(other_chunk + " = index i8 " + other + ", " +
			      to_string(cursor));
			instr("copyobj " + to_string(offset - cursor) +
			      "x1 " + other_chunk + ", " + self_chunk);
		}
		program_.demand_function_declaration(op);
		if (op->is_inline_definition)
			program_.demand_inline_function(op);
		string self_field = fresh_temp();
		string other_field = fresh_temp();
		instr(self_field + " = index i8 " + self + ", " +
		      to_string(offset));
		instr(other_field + " = index i8 " + other + ", " +
		      to_string(offset));
		string ignored = fresh_temp();
		instr(ignored + " = call ptr @" + program_.symbol_for(op) +
		      "(" + self_field + ", " + other_field + ")");
		uint64_t end = assignment_member_storage_end(field);
		if (end > cursor)
			cursor = end;
	}
	uint64_t total = assignment_storage_copy_limit(bare);
	if (total > cursor)
	{
		string self_chunk = fresh_temp();
		string other_chunk = fresh_temp();
		instr(self_chunk + " = index i8 " + self + ", " +
		      to_string(cursor));
		instr(other_chunk + " = index i8 " + other + ", " +
		      to_string(cursor));
		instr("copyobj " + to_string(total - cursor) +
		      "x1 " + other_chunk + ", " + self_chunk);
	}
	return true;
}

bool FunctionLowerer::lower_defaulted_storage_special_member() { Binding* binding = fn_.binding;
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
return true; }
if (lower_defaulted_assignment_fields(record, move, other_name))
{
	string ret = fresh_temp();
	instr(ret + " = load ptr $this");
	terminate("return ptr " + ret);
	return true;
} } if (record_has_storage_copy(record))
{ string self = fresh_temp(); string other = fresh_temp(); instr(self + " = load ptr $this");
instr(other + " = load ptr $" + other_name); instr("copyobj " + to_string(pa11::type_size(record)) + "x" + to_string(pa11::type_align(record)) + " " + other + ", " + self); }
if (binding->name == "operator=") { string ret = fresh_temp(); instr(ret + " = load ptr $this");
terminate("return ptr " + ret); } else terminate("return void");
return true; } 
}  // namespace internal
}  // namespace pa14
