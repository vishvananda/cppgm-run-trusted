#include "pa14_lowir_internal.h"
namespace pa14 { namespace internal { namespace { void demand_record_return_calls(ProgramLowerer& program, const Node& node)
{ if (starts_with(node.line, "call-expression") && node.direct_call != NULL && pa11::strip_cv(node.type)->kind == TypeKind::Record)
{ program.demand_function_declaration(node.direct_call); program.demand_inline_function(node.direct_call); }
for (size_t i = 0; i < node.children.size(); ++i) demand_record_return_calls(program, node.children[i]); } bool trivial_lvalue_projection(const Node& node)
{ if (starts_with(node.line, "id-expression")) return true; if (starts_with(node.line, "cast-expression xvalue") &&
node.children.size() == 1) return trivial_lvalue_projection(node.children[0]); if (!starts_with(node.line, "member-expression")) return false;
for (size_t i = 0; i < node.children.size(); ++i) if (!trivial_lvalue_projection(node.children[i])) return false; return true;
}
bool generated_empty_constructor_record(Binding* ctor)
{
	if (ctor == NULL ||
	    !(ctor->is_generated_default_constructor ||
	      ctor->is_generated_aggregate_constructor) ||
	    ctor->type.get() == NULL ||
	    ctor->type->kind != TypeKind::Function ||
	    ctor->type->parameters.size() != 1)
		return false;
	TypePtr record = class_record_for_member(ctor);
	record = record.get() != NULL ? pa11::strip_cv(record) : TypePtr();
	return record.get() != NULL &&
	       record->kind == TypeKind::Record &&
	       pa11::record_direct_bases(record).empty() &&
	       record->fields.empty();
}

bool base_entry_needs_complete_noop_constructor(Binding* ctor,
                                                bool base_entry)
{
	return base_entry &&
	       ctor != NULL &&
	       ctor->is_inline_definition &&
	       ctor->is_noop_constructor &&
	       !ctor->is_generated_default_constructor &&
	       !ctor->is_generated_aggregate_constructor &&
	       !ctor->is_generated_copy_move_constructor &&
	       binding_has_template_specialization_context(ctor) &&
	       ctor->type.get() != NULL &&
	       ctor->type->kind == TypeKind::Function &&
	       ctor->type->parameters.size() == 1;
}

bool std_tuple_storage_copy_record(TypePtr type)
{
	TypePtr bare = type.get() != NULL ? pa11::strip_cv(type) : TypePtr();
	if (bare.get() == NULL ||
	    bare->kind != TypeKind::Record ||
	    bare->scope == NULL ||
	    (bare->scope->name != "_Tuple_impl" &&
	     bare->scope->name != "_Head_base"))
		return false;
	for (Scope* scope = bare->scope->parent; scope != NULL; scope = scope->parent)
		if (scope->kind == ScopeKind::Namespace && scope->name == "std")
			return true;
	return false;
}

const Node* recorded_constructor_body(const ProgramLowerer& program,
                                      const Binding* ctor)
{
	if (ctor == NULL)
		return NULL;
	map<const Binding*, const Node*>::const_iterator found =
		program.inline_definitions.find(ctor);
	if (found != program.inline_definitions.end())
		return found->second;
	map<const Binding*, Node>::const_iterator synthetic =
		program.synthetic_inline_definitions.find(ctor);
	if (synthetic != program.synthetic_inline_definitions.end())
		return &synthetic->second;
	if (ctor->aliased_binding != NULL)
		return recorded_constructor_body(program, ctor->aliased_binding);
	return NULL;
}

bool generated_constructor_action_chain_noop(
	const ProgramLowerer& program,
	Binding* ctor,
	TypePtr type,
	set<const Binding*>& seen);
bool compound_constructor_actions_noop(const ProgramLowerer& program,
                                       const Node& compound,
                                       set<const Binding*>& seen);

bool constructor_needs_hidden_virtual_base_args(Binding* ctor, TypePtr type)
{
	if (ctor == NULL || !is_class_constructor_binding(ctor))
		return false;
	TypePtr bare = type.get() != NULL ? pa11::strip_cv(type) : TypePtr();
	return bare.get() != NULL &&
	       bare->kind == TypeKind::Record &&
	       !hidden_virtual_bases_for_record(bare).empty();
}

bool constructor_init_action_noop(const ProgramLowerer& program,
                                  const Node& action,
                                  set<const Binding*>& seen)
{
	bool base_action = starts_with(action.line, "base-init-action");
	bool member_action = starts_with(action.line, "member-init-action");
	if (!base_action && !member_action)
		return false;
	if (!action.children.empty())
		return false;
	TypePtr action_type = base_action
		? action.type
		: (action.binding != NULL ? action.binding->type : TypePtr());
	Binding* ctor = action.direct_call;
	if (ctor == NULL)
	{
		TypePtr bare = action_type.get() != NULL
			? pa11::strip_cv(action_type) : TypePtr();
		if (bare.get() != NULL && bare->kind == TypeKind::Record)
			ctor = find_constructor(bare, 0);
	}
	if (ctor == NULL)
		return default_init_no_op(action_type);
	if (ctor->is_generated_default_constructor ||
	    ctor->is_generated_aggregate_constructor)
		return generated_constructor_action_chain_noop(program,
		                                               ctor,
		                                               action_type,
		                                               seen);
	if (no_op_generated_default_constructor(ctor, action_type) &&
	    !constructor_needs_hidden_virtual_base_args(ctor, action_type))
		return true;
	if (!is_class_constructor_binding(ctor))
		return false;
	const Node* body = recorded_constructor_body(program, ctor);
	if (body == NULL || body->children.empty())
		return false;
	return compound_constructor_actions_noop(program,
	                                        body->children.back(),
	                                        seen);
}

bool compound_constructor_actions_noop(const ProgramLowerer& program,
                                       const Node& compound,
                                       set<const Binding*>& seen)
{
	if (!starts_with(compound.line, "compound-statement"))
		return false;
	for (size_t i = 0; i < compound.children.size(); ++i)
		if (!constructor_init_action_noop(program,
		                                  compound.children[i],
		                                  seen))
			return false;
	return true;
}

bool generated_constructor_action_chain_noop(
	const ProgramLowerer& program,
	Binding* ctor,
	TypePtr type,
	set<const Binding*>& seen)
{
	if (ctor == NULL ||
	    !(ctor->is_generated_default_constructor ||
	      ctor->is_generated_aggregate_constructor))
		return false;
	TypePtr bare = type.get() != NULL ? pa11::strip_cv(type) : TypePtr();
	if (bare.get() != NULL &&
	    bare->kind == TypeKind::Record &&
	    bare->is_polymorphic)
		return false;
	if (!seen.insert(ctor).second)
		return false;
	const Node* body = recorded_constructor_body(program, ctor);
	bool flag_noop =
		no_op_generated_default_constructor(ctor, type) &&
		!constructor_needs_hidden_virtual_base_args(ctor, type);
	if (body == NULL || body->children.empty())
	{
		if (ctor->is_generated_default_constructor && ctor->is_defaulted)
			return default_init_no_op(type);
		return flag_noop;
	}
	const Node& compound = body->children.back();
	return compound_constructor_actions_noop(program, compound, seen);
}

void demand_noop_constructor_action_dependencies(ProgramLowerer& program,
                                                 const Node& action);

void demand_noop_generated_constructor_dependencies(ProgramLowerer& program,
                                                   Binding* ctor)
{
	const Node* body = recorded_constructor_body(program, ctor);
	if (body == NULL || body->children.empty())
		return;
	const Node& compound = body->children.back();
	if (!starts_with(compound.line, "compound-statement"))
		return;
	for (size_t i = 0; i < compound.children.size(); ++i)
		demand_noop_constructor_action_dependencies(program,
		                                            compound.children[i]);
}

void demand_noop_constructor_action_dependencies(ProgramLowerer& program,
                                                 const Node& action)
{
	bool base_action = starts_with(action.line, "base-init-action");
	bool member_action = starts_with(action.line, "member-init-action");
	if (!base_action && !member_action)
		return;
	if (!action.children.empty())
		return;
	Binding* ctor = action.direct_call;
	if (ctor == NULL)
	{
		TypePtr action_type = base_action
			? action.type
			: (action.binding != NULL ? action.binding->type : TypePtr());
		TypePtr bare = action_type.get() != NULL
			? pa11::strip_cv(action_type) : TypePtr();
		if (bare.get() != NULL && bare->kind == TypeKind::Record)
			ctor = find_constructor(bare, 0);
	}
	if (ctor == NULL)
		return;
	if (ctor->is_generated_default_constructor ||
	    ctor->is_generated_aggregate_constructor)
	{
		demand_noop_generated_constructor_dependencies(program, ctor);
		return;
	}
	program.demand_inline_function(ctor, !base_action);
	if (base_action)
		program.demand_lifecycle_base_entry_declaration(ctor);
}

bool suppress_effectively_noop_generated_constructor(
	ProgramLowerer& program,
	Binding* ctor,
	TypePtr type)
{
	set<const Binding*> seen;
	if (!generated_constructor_action_chain_noop(program, ctor, type, seen))
		return false;
	demand_noop_generated_constructor_dependencies(program, ctor);
	return true;
}

bool member_default_constructor_init_noop(const ProgramLowerer& program,
                                          Binding* ctor,
                                          TypePtr type)
{
	if (ctor != NULL &&
	    (ctor->is_generated_default_constructor ||
	     ctor->is_generated_aggregate_constructor))
	{
		if (ctor->is_generated_default_constructor &&
		    ctor->is_defaulted)
			return false;
		set<const Binding*> seen;
		return generated_constructor_action_chain_noop(program,
		                                               ctor,
		                                               type,
		                                               seen);
	}
	return no_op_generated_default_constructor(ctor, type);
}

	bool hosted_external_stream_constructor(Binding* ctor)
	{
		return is_class_constructor_binding(ctor) &&
		       record_uses_hosted_external_stream_vtable(
			       class_record_for_member(ctor));
	}
	}  // namespace
void FunctionLowerer::emit_temporary_cleanups( const vector<pair<Value, TypePtr> >& temps) { for (size_t n = 0; n < temps.size(); ++n)
{ size_t i = temps.size() - 1 - n; Value addr = temps[i].first; TypePtr type = temps[i].second;
function<Value()> addr_for = [addr]() { return addr; }; TypePtr bare = pa11::strip_cv(type); Binding* dtor = bare->kind == TypeKind::Record ? find_destructor(bare) : NULL;
if (program_.native_lowering && dtor != NULL && dtor->is_generated_default_destructor && dtor->is_noop_destructor) {
program_.demand_function_declaration(dtor); program_.demand_inline_function(dtor); Value target = addr_for(); string arg = target.text;
if (!arg.empty() && (arg[0] == '@' || arg[0] == '$')) { string tmp = fresh_temp(); instr(tmp + " = addr " + arg); arg = tmp; }
instr("call void @" + program_.symbol_for(dtor) + "(" + arg + ")"); continue; }
lower_destructor_for_object(addr_for, type);
} } void FunctionLowerer::add_pending_temp_cleanup(Value addr, TypePtr type) {
pending_temp_cleanups_.push_back(make_pair(addr, type)); } bool FunctionLowerer::has_pending_temp_cleanups() const {
return !pending_temp_cleanups_.empty(); } bool FunctionLowerer::node_may_create_temp_cleanup(const Node& node) const {
if (starts_with(node.line, "braced-init-list")) return true; TypePtr object = object_type(node.type); if (node.category == ValueCategory::PRValue &&
pa11::strip_cv(object)->kind == TypeKind::Record && (type_needs_cleanup(object) || (program_.native_lowering && type_has_generated_noop_destructor(object)))) return true; for (size_t i = 0; i < node.children.size(); ++i)
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
const vector<PendingConstructorConversion>& pending_conversions, bool base_entry) { if (!(base_entry && ctor->is_inline_definition) ||
base_entry_needs_complete_noop_constructor(ctor, base_entry))
program_.demand_function_declaration(ctor); string callee = program_.constructor_symbol_for(ctor, base_entry); if (base_entry && generated_empty_constructor_record(ctor))
program_.emit_generated_empty_constructor(ctor, callee); program_.demand_inline_function(ctor, !base_entry); if (base_entry) program_.demand_lifecycle_base_entry_declaration(ctor); function<string()> call_text = [callee, &lowered]() {
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
	void FunctionLowerer::append_constructor_hidden_parameter_args(
		Binding* ctor,
		const vector<const Node*>& args,
		vector<string>& lowered)
	{
		for (size_t i = 0; i < args.size(); ++i)
		{
			TypePtr param = ctor->type->parameters[i + 1];
			TypePtr context = hidden_virtual_base_context_record(param);
			vector<TypePtr> vbases = hidden_virtual_bases_for_parameter(param);
			if (vbases.empty())
				continue;
			const Node& arg = *args[i];
			string explicit_arg = i + 1 < lowered.size()
				? lowered[i + 1] : string();
			for (size_t v = 0; v < vbases.size(); ++v)
			{
				string hidden;
				if (starts_with(arg.line, "id-expression") &&
				    arg.binding != NULL &&
				    arg.binding->kind == BindingKind::Parameter)
				{
					vector<TypePtr> arg_vbases =
						hidden_virtual_bases_for_parameter(arg.binding->type);
					for (size_t av = 0; av < arg_vbases.size(); ++av)
						if (pa11::same_type(pa11::strip_cv(arg_vbases[av]),
						                    pa11::strip_cv(vbases[v])))
						{
							TypePtr arg_type = pa11::strip_cv(arg.binding->type);
							if ((arg_type->kind == TypeKind::LValueReference ||
							     arg_type->kind == TypeKind::RValueReference) &&
							    pa11::strip_cv(arg_type->base)->kind ==
								    TypeKind::Record)
							{
								hidden = fresh_temp();
								instr(hidden + " = load ptr $" +
								      slot_for(arg.binding) + "__pvb" +
								      to_string(av));
							}
							else
								hidden = "%__pvbptr" + to_string(av);
							break;
						}
				}
				if (hidden.empty() && !explicit_arg.empty())
				{
					TypePtr source_context =
						hidden_virtual_base_context_record(arg.type);
					if (source_context.get() != NULL &&
					    context.get() != NULL &&
					    pa11::same_type(pa11::strip_cv(source_context),
					                    pa11::strip_cv(context)) &&
					    record_has_base_subobject(context, vbases[v]))
					{
						uint64_t offset = base_subobject_offset(context,
						                                        vbases[v]);
						if (offset == 0)
							hidden = explicit_arg;
						else
						{
							hidden = fresh_temp();
							instr(hidden + " = index i8 " + explicit_arg +
							      ", " + to_string(offset));
						}
					}
				}
				if (hidden.empty())
				{
					TypePtr source;
					Value base;
					if (arg.category == ValueCategory::LValue ||
					    arg.category == ValueCategory::XValue)
					{
						base = ensure_pointer(emit_lvalue_addr(arg));
						source = pa11::strip_cv(object_type(arg.type));
					}
					else
					{
						base = emit_rvalue(arg);
						source = pa11::strip_cv(strip_for_value(arg.type));
						if (source.get() != NULL &&
						    source->kind == TypeKind::Pointer)
							source = pa11::strip_cv(source->base);
					}
					if (source.get() != NULL &&
					    source->kind == TypeKind::Record &&
					    record_has_base_subobject(source, vbases[v]))
					{
						uint64_t offset =
							base_subobject_offset(source, vbases[v]);
						if (offset == 0)
							hidden = base.text;
						else
						{
							hidden = fresh_temp();
							instr(hidden + " = index i8 " + base.text +
							      ", " + to_string(offset));
						}
					}
					else if (!explicit_arg.empty())
					{
						uint64_t offset =
							base_subobject_offset(context, vbases[v]);
						if (offset == 0)
							hidden = explicit_arg;
						else
						{
							hidden = fresh_temp();
							instr(hidden + " = index i8 " + explicit_arg +
							      ", " + to_string(offset));
						}
					}
				}
				if (hidden.empty())
					hidden = "0";
				lowered.push_back(hidden);
			}
		}
	}
	void FunctionLowerer::append_constructor_base_entry_hidden_args(
		Binding* ctor,
		vector<string>& lowered)
	{
		TypePtr constructed = class_record_for_member(ctor);
		TypePtr constructed_bare = constructed.get() != NULL
			? pa11::strip_cv(constructed) : TypePtr();
		TypePtr current_record = class_record_for_member(fn_.binding);
		TypePtr current_bare = current_record.get() != NULL
			? pa11::strip_cv(current_record) : TypePtr();
		if (hosted_external_stream_constructor(ctor))
		{
			if (constructed_bare.get() != NULL &&
			    constructed_bare->kind == TypeKind::Record &&
			    constructed_bare->is_polymorphic &&
			    record_uses_virtual_base_vtt(constructed_bare) &&
			    current_bare.get() != NULL &&
			    current_bare->kind == TypeKind::Record)
			{
				size_t vtt_slot =
					construction_vtt_slot_for_direct_base(current_bare,
					                                      constructed_bare);
				if (vtt_slot != static_cast<size_t>(-1))
				{
					string vtt_base = fresh_temp();
					instr(vtt_base + " = addr @" +
					      vtt_symbol_for_record(current_bare));
					string vtt_arg = vtt_base;
					if (vtt_slot != 0)
					{
						vtt_arg = fresh_temp();
						instr(vtt_arg + " = index i8 " + vtt_base +
						      ", " + to_string(vtt_slot * 8));
					}
					lowered.insert(lowered.begin() + 1, vtt_arg);
				}
			}
			return;
		}
		if (constructed_bare.get() != NULL &&
		    constructed_bare->kind == TypeKind::Record &&
		    constructed_bare->is_polymorphic &&
		    record_uses_virtual_base_vtt(constructed_bare) &&
		    current_bare.get() != NULL &&
		    current_bare->kind == TypeKind::Record)
		{
			size_t vtt_slot =
				construction_vtt_slot_for_direct_base(current_bare,
				                                      constructed_bare);
			if (vtt_slot != static_cast<size_t>(-1))
			{
				string vtt_base = fresh_temp();
				instr(vtt_base + " = addr @" + vtt_symbol_for_record(current_bare));
				string vtt_arg = vtt_base;
				if (vtt_slot != 0)
				{
					vtt_arg = fresh_temp();
					instr(vtt_arg + " = index i8 " + vtt_base +
					      ", " + to_string(vtt_slot * 8));
				}
				lowered.push_back(vtt_arg);
			}
		}
		vector<TypePtr> vbases = hidden_virtual_bases_for_record(constructed_bare);
		vector<TypePtr> current_vbases =
			hidden_virtual_bases_for_record(current_bare);
		for (size_t v = 0; v < vbases.size(); ++v)
		{
			string hidden;
			if (current_bare.get() != NULL &&
			    current_bare->kind == TypeKind::Record &&
			    record_has_base_subobject(current_bare, vbases[v]))
			{
				string this_ptr = fresh_temp();
				instr(this_ptr + " = load ptr $this");
				uint64_t offset = base_subobject_offset(current_bare,
				                                        vbases[v]);
				if (offset == 0)
					hidden = this_ptr;
				else
				{
					hidden = fresh_temp();
					instr(hidden + " = index i8 " + this_ptr +
					      ", " + to_string(offset));
				}
			}
			else
				hidden = "%__vbptr" + to_string(v);
			for (size_t cv = 0; cv < current_vbases.size(); ++cv)
				if (pa11::same_type(pa11::strip_cv(current_vbases[cv]),
				                    pa11::strip_cv(vbases[v])))
				{
					out_.constructor_base_entry_arg_rewrites.push_back(
						make_pair(hidden, "%__vbptr" + to_string(cv)));
					break;
				}
			lowered.push_back(hidden);
		}
	}
bool FunctionLowerer::lower_hosted_shared_ptr_constructor(
	const function<Value()>& addr_for,
	Binding* ctor,
	const vector<const Node*>& args)
{
	TypePtr record = class_record_for_member(ctor);
	record = record.get() != NULL ? pa11::strip_cv(record) : TypePtr();
	if (!hosted_shared_ptr_record(record))
		return false;
	Value target = addr_for();
	if (args.empty())
	{
		instr("store ptr 0, " + target.text);
		string control = fresh_temp();
		instr(control + " = index i8 [projection=field] " +
		      target.text + ", 8");
		instr("store ptr 0, " + control);
		return true;
	}
	if (args.size() != 1)
		return false;
	const Node& arg = *args[0];
	TypePtr arg_object = pa11::strip_cv(object_type(arg.type));
	if (hosted_shared_ptr_record(arg_object) &&
	    (arg.category == ValueCategory::LValue ||
	     arg.category == ValueCategory::XValue))
	{
		Value source = ensure_pointer(emit_lvalue_addr(arg));
		instr("copyobj " + to_string(pa11::type_size(record)) + "x" +
		      to_string(pa11::type_align(record)) + " " +
		      source.text + ", " + target.text);
		return true;
	}
	TypePtr arg_value = pa11::strip_cv(strip_for_value(arg.type));
	if (arg_value.get() == NULL || arg_value->kind != TypeKind::Pointer)
		return false;
	Value raw = emit_rvalue(arg);
	Value pointer = convert_value(
		raw,
		arg.type,
		pa11::make_pointer(pa11::make_fundamental(FT_VOID)));
	instr("store ptr " + pointer.text + ", " + target.text);
	string control = fresh_temp();
	instr(control + " = index i8 [projection=field] " +
	      target.text + ", 8");
	instr("store ptr 0, " + control);
	return true;
}

namespace {

string unqualified_template_primary_name(TypePtr type)
{
	TypePtr bare = type.get() != NULL ? pa11::strip_cv(type) : TypePtr();
	if (bare.get() == NULL)
		return "";
	string primary = bare->template_primary_name.empty()
		? bare->name : bare->template_primary_name;
	size_t pos = primary.rfind("::");
	return pos == string::npos ? primary : primary.substr(pos + 2);
}

bool hosted_std_namespace_scope(Scope* scope)
{
	for (Scope* cur = scope; cur != NULL; cur = cur->parent)
		if (cur->kind == ScopeKind::Namespace && cur->name == "std")
			return true;
	return false;
}

bool hosted_vector_bool_record(TypePtr type)
{
	TypePtr bare = type.get() != NULL ? pa11::strip_cv(type) : TypePtr();
	if (bare.get() == NULL ||
	    bare->kind != TypeKind::Record ||
	    !bare->is_template_specialization ||
	    bare->scope == NULL ||
	    unqualified_template_primary_name(bare) != "vector" ||
	    bare->template_arguments.empty() ||
	    bare->template_arguments[0].kind !=
		    pa11::TemplateInstanceArgumentKind::Type)
		return false;
	TypePtr element = pa11::strip_cv(bare->template_arguments[0].type);
	return element.get() != NULL &&
	       element->kind == TypeKind::Fundamental &&
	       element->fundamental == FT_BOOL &&
	       hosted_std_namespace_scope(bare->scope);
}

bool hosted_vector_record(TypePtr type, TypePtr& element)
{
	TypePtr bare = type.get() != NULL ? pa11::strip_cv(type) : TypePtr();
	if (bare.get() == NULL ||
	    bare->kind != TypeKind::Record ||
	    !bare->is_template_specialization ||
	    bare->scope == NULL ||
	    unqualified_template_primary_name(bare) != "vector" ||
	    bare->template_arguments.empty() ||
	    bare->template_arguments[0].kind !=
		    pa11::TemplateInstanceArgumentKind::Type ||
	    !hosted_std_namespace_scope(bare->scope))
		return false;
	element = pa11::strip_cv(bare->template_arguments[0].type);
	return element.get() != NULL;
}

void declare_hosted_operator_new(ProgramLowerer& program)
{
	if (program.declared_functions.insert("operator_new").second)
		program.declares.push_back(
			"declare function @operator_new(%arg0 : i64) -> ptr "
			"[binding=strong, object=" +
			string(program.native_lowering
			       ? "_Znwm" : "cppgm_builtin_operator_new") + "]");
}

}  // namespace

bool FunctionLowerer::lower_hosted_vector_initializer_list_constructor(
	const function<Value()>& addr_for,
	Binding* ctor,
	const vector<const Node*>& args)
{
	TypePtr record = class_record_for_member(ctor);
	record = record.get() != NULL ? pa11::strip_cv(record) : TypePtr();
	TypePtr element;
	if (!hosted_vector_record(record, element) ||
	    args.empty() ||
	    ctor == NULL ||
	    ctor->type.get() == NULL ||
	    ctor->type->kind != TypeKind::Function ||
	    ctor->type->parameters.size() < 2)
		return false;
	TypePtr param = ctor->type->parameters[1];
	if (is_reference(param))
		param = param->base;
	TypePtr list_element;
	if (!is_initializer_list_type(pa11::strip_cv(param), &list_element) ||
	    !pa11::same_type(pa11::strip_cv(element),
	                     pa11::strip_cv(list_element)))
		return false;
	const Node& list = *args[0];
	if (!starts_with(list.line, "braced-init-list"))
		return false;
	Value target = addr_for();
	if (list.children.empty())
	{
		instr("store ptr 0, " + target.text);
		string finish = fresh_temp();
		instr(finish + " = index i8 [projection=field] " +
		      target.text + ", 8");
		instr("store ptr 0, " + finish);
		string end_storage = fresh_temp();
		instr(end_storage + " = index i8 [projection=field] " +
		      target.text + ", 16");
		instr("store ptr 0, " + end_storage);
		return true;
	}
	declare_hosted_operator_new(program_);
	uint64_t bytes = pa11::type_size(element) * list.children.size();
	string size_tmp = fresh_temp();
	instr(size_tmp + " = convert sext i64 i32 " + to_string(bytes));
	string storage_name = fresh_temp();
	instr(storage_name + " = call ptr @operator_new(" + size_tmp + ")");
	Value storage("ptr", storage_name);
	for (size_t i = 0; i < list.children.size(); ++i)
	{
		Value elem_addr = direct_array_element_addr(storage, element, i);
		function<Value()> elem_addr_for = [elem_addr]() {
			return elem_addr;
		};
		lower_object_init(elem_addr_for, element, list.children[i]);
	}
	string end = fresh_temp();
	instr(end + " = index i8 " + storage.text + ", " + to_string(bytes));
	instr("store ptr " + storage.text + ", " + target.text);
	string finish = fresh_temp();
	instr(finish + " = index i8 [projection=field] " +
	      target.text + ", 8");
	instr("store ptr " + end + ", " + finish);
	string end_storage = fresh_temp();
	instr(end_storage + " = index i8 [projection=field] " +
	      target.text + ", 16");
	instr("store ptr " + end + ", " + end_storage);
	return true;
}

bool FunctionLowerer::lower_hosted_vector_bool_move_constructor(
	const function<Value()>& addr_for,
	Binding* ctor,
	const vector<const Node*>& args)
{
	TypePtr record = class_record_for_member(ctor);
	record = record.get() != NULL ? pa11::strip_cv(record) : TypePtr();
	if (!hosted_vector_bool_record(record) ||
	    args.size() != 1 ||
	    ctor == NULL ||
	    ctor->type.get() == NULL ||
	    ctor->type->kind != TypeKind::Function ||
	    ctor->type->parameters.size() != 2 ||
	    !is_reference(ctor->type->parameters[1]) ||
	    pa11::type_has_const(ctor->type->parameters[1]->base))
		return false;
	const Node& arg = *args[0];
	TypePtr source_record = pa11::strip_cv(object_type(arg.type));
	if (!hosted_vector_bool_record(source_record))
		return false;
	Value target = addr_for();
	Value source = ensure_pointer(emit_lvalue_addr(arg));
	instr("copyobj " + to_string(pa11::type_size(record)) + "x" +
	      to_string(pa11::type_align(record)) + " " +
	      source.text + ", " + target.text);
	lower_storage_zero(source, pa11::type_size(record));
	return true;
}

bool FunctionLowerer::lower_hosted_vector_bool_move_body()
{
	Binding* binding = fn_.binding;
	TypePtr record = class_record_for_member(binding);
	record = record.get() != NULL ? pa11::strip_cv(record) : TypePtr();
	if (!hosted_vector_bool_record(record) ||
	    binding == NULL ||
	    binding->type.get() == NULL ||
	    binding->type->kind != TypeKind::Function ||
	    binding->type->parameters.size() != 2 ||
	    !is_reference(binding->type->parameters[1]) ||
	    pa11::type_has_const(binding->type->parameters[1]->base) ||
	    out_.parameter_names.size() < 2)
		return false;
	string target = fresh_temp();
	instr(target + " = load ptr $" + out_.parameter_names[0]);
	string source = fresh_temp();
	instr(source + " = load ptr $" + out_.parameter_names[1]);
	instr("copyobj " + to_string(pa11::type_size(record)) + "x" +
	      to_string(pa11::type_align(record)) + " " +
	      source + ", " + target);
	lower_storage_zero(Value("ptr", source), pa11::type_size(record));
	return true;
}

		void FunctionLowerer::lower_constructor_call(const function<Value()>& addr_for, Binding* ctor, const vector<const Node*>& args, bool base_entry)
		{ if (ctor == NULL) throw runtime_error("missing constructor"); ctor = canonical_constructor_binding(ctor); if (lower_hosted_shared_ptr_constructor(addr_for, ctor, args)) return; if (lower_hosted_vector_initializer_list_constructor(addr_for, ctor, args)) return; if (lower_hosted_vector_bool_move_constructor(addr_for, ctor, args)) return; if (args.size() == 1 && ctor->type.get() != NULL &&
ctor->type->kind == TypeKind::Function && ctor->type->parameters.size() == 2 && is_reference(ctor->type->parameters[1]) && pa11::strip_cv(ctor->type->parameters[1]->base)->kind == TypeKind::Record &&
!defaulted_copy_move_constructor_needs_helper(ctor, ctor->type->parameters[1]->base) && !record_has_storage_copy(ctor->type->parameters[1]->base)) {
const Node& arg = *args[0]; TypePtr src_record = pa11::strip_cv(object_type(arg.type)); TypePtr dst_record = pa11::strip_cv(ctor->type->parameters[1]->base); TypePtr constructed_record = class_record_for_member(ctor);
constructed_record = constructed_record.get() != NULL ? pa11::strip_cv(constructed_record) : TypePtr(); const Node* prvalue_arg = record_prvalue_child_for_xvalue(arg);
if (prvalue_arg == NULL && arg.category == ValueCategory::PRValue) prvalue_arg = &arg; bool glvalue_arg = arg.category == ValueCategory::LValue || arg.category == ValueCategory::XValue ||
starts_with(arg.line, "cast-expression xvalue") || starts_with(arg.line, "id-expression xvalue") || starts_with(arg.line, "member-expression xvalue"); bool prvalue_call_arg =
prvalue_arg != NULL && starts_with(prvalue_arg->line, "call-expression"); if (prvalue_arg != NULL) src_record = pa11::strip_cv(object_type(prvalue_arg->type)); bool unresolved_copy_target = function_signature_has_unresolved_storage(ctor) ||
type_contains_template_symbol_pattern(ctor->type) || type_contains_template_symbol_pattern(constructed_record) || binding_has_template_specialization_context(ctor); if (src_record->kind == TypeKind::Record &&
dst_record->kind == TypeKind::Record && constructed_record.get() != NULL && constructed_record->kind == TypeKind::Record && pa11::same_type(constructed_record, dst_record) &&
pa11::same_type(src_record, dst_record) && glvalue_arg) { addr_for();
bool reference_parameter_id = starts_with(arg.line, "id-expression") && arg.binding != NULL && arg.binding->kind == BindingKind::Parameter &&
is_reference(arg.binding->type); if (!reference_parameter_id && !trivial_lvalue_projection(arg)) ensure_pointer(emit_lvalue_addr(arg));
return; } if (!program_.host_object_lowering && prvalue_call_arg && unresolved_copy_target && src_record->kind == TypeKind::Record &&
dst_record->kind == TypeKind::Record && constructed_record.get() != NULL && constructed_record->kind == TypeKind::Record && pa11::same_type(constructed_record, dst_record) &&
pa11::type_size(src_record) == pa11::type_size(dst_record) && pa11::type_align(src_record) == pa11::type_align(dst_record)) {
Value target = addr_for(); Value source = emit_rvalue(*prvalue_arg); instr("copyobj " + to_string(pa11::type_size(dst_record)) + "x" + to_string(pa11::type_align(dst_record)) + " " + source.text + ", " + target.text);
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
	convert_binary_value(emit_rvalue(arg), arg.type, param).text); } }
	if (!base_entry)
	{
		if (!hosted_external_stream_constructor(ctor))
			append_constructor_hidden_parameter_args(ctor, args, lowered);
	}
	else
		append_constructor_base_entry_hidden_args(ctor, lowered);
	emit_constructor_call_with_cleanups(
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
void FunctionLowerer::lower_base_init(const Node& node)
{
	if (node.type.get() == NULL)
		return;
	TypePtr source = class_record_for_member(fn_.binding);
	function<Value()> base_addr = [this, source, &node]() {
		string this_ptr = fresh_temp();
		instr(this_ptr + " = load ptr $this");
		string addr = fresh_temp();
		instr(addr + " = index i8 [projection=base_subobject] " +
		      this_ptr + ", " +
		      to_string(base_subobject_offset(source, node.type)));
		return Value("ptr", addr);
	};
	if (node.children.empty())
	{
		if (node.direct_call != NULL)
		{
			if (no_op_generated_default_constructor(node.direct_call,
			                                        node.type) &&
			    !constructor_needs_hidden_virtual_base_args(
				    node.direct_call,
				    node.type))
				return;
			if (suppress_effectively_noop_generated_constructor(
				    program_, node.direct_call, node.type) &&
			    !constructor_needs_hidden_virtual_base_args(
				    node.direct_call,
				    node.type))
				return;
			vector<const Node*> args;
			lower_constructor_call(base_addr, node.direct_call, args, true);
			return;
		}
		lower_zero_init(base_addr, node.type);
		return;
	}
	const Node& init = node.children[0];
	Binding* ctor = node.direct_call;
	if (ctor == NULL)
		ctor = init.direct_call;
	if (ctor != NULL &&
	    ctor->type.get() != NULL &&
	    ctor->type->kind == TypeKind::Function)
	{
		bool empty_braced_init =
			node.children.size() == 1 &&
			starts_with(init.line, "braced-init-list") &&
			init.children.empty();
		if ((no_op_generated_default_constructor(ctor, node.type) &&
		     !constructor_needs_hidden_virtual_base_args(ctor, node.type)) ||
		    (empty_braced_init &&
		     suppress_effectively_noop_generated_constructor(
			     program_, ctor, node.type) &&
		     !constructor_needs_hidden_virtual_base_args(ctor,
		                                                node.type)))
			return;
		const Node& copy_source =
			starts_with(init.line, "braced-init-list") &&
			init.children.size() == 1 ? init.children[0] : init;
		TypePtr src_record = pa11::strip_cv(object_type(copy_source.type));
		TypePtr dst_record = pa11::strip_cv(node.type);
		bool same_or_base =
			src_record->kind == TypeKind::Record &&
			dst_record->kind == TypeKind::Record &&
			(pa11::same_type(src_record, dst_record) ||
			 record_has_base(src_record, dst_record));
		bool glvalue_source =
			copy_source.category == ValueCategory::LValue ||
			copy_source.category == ValueCategory::XValue;
		bool structural_copy_move_ctor =
			ctor->type->parameters.size() == 2 &&
			is_reference(ctor->type->parameters[1]) &&
			pa11::same_type(
				pa11::strip_cv(ctor->type->parameters[1]->base),
				dst_record);
		if (structural_copy_move_ctor &&
		    !defaulted_copy_move_constructor_needs_helper(ctor,
		                                                  node.type) &&
		    !record_has_storage_copy(node.type) &&
		    same_or_base &&
		    glvalue_source)
		{
			base_addr();
			return;
		}
		if ((ctor->is_defaulted ||
		     ctor->is_generated_copy_move_constructor) &&
		    ctor->is_inline_definition &&
		    !defaulted_copy_move_constructor_needs_helper(ctor,
		                                                  node.type) &&
		    record_has_storage_copy(node.type) &&
		    same_or_base &&
		    glvalue_source)
		{
			Value target = base_addr();
			Value source = ensure_pointer(emit_lvalue_addr(copy_source));
			Value converted =
				convert_value(source,
				              pa11::make_pointer(src_record),
				              pa11::make_pointer(node.type));
			instr("copyobj " + to_string(pa11::type_size(node.type)) +
			      "x" + to_string(pa11::type_align(node.type)) + " " +
			      converted.text + ", " + target.text);
			return;
		}
		vector<const Node*> args;
		if (starts_with(init.line, "braced-init-list"))
			for (size_t i = 0; i < init.children.size(); ++i)
				args.push_back(&init.children[i]);
		else
			args.push_back(&init);
		TypePtr inherited_base = node.type.get() != NULL
			? pa11::strip_cv(node.type) : TypePtr();
		if (node.token_text == "inherited-constructor")
		{
			program_.referenced_constructor_base_entries.insert(ctor);
			program_.constructor_base_entry_only_references.insert(ctor);
			Binding* canonical = canonical_constructor_binding(ctor);
			program_.referenced_constructor_base_entries.insert(canonical);
			program_.constructor_base_entry_only_references.insert(canonical);
			if (ctor->aliased_binding != NULL)
			{
				program_.referenced_constructor_base_entries.insert(
					ctor->aliased_binding);
				program_.constructor_base_entry_only_references.insert(
					ctor->aliased_binding);
			}
			if (canonical != NULL && canonical->aliased_binding != NULL)
			{
				program_.referenced_constructor_base_entries.insert(
					canonical->aliased_binding);
				program_.constructor_base_entry_only_references.insert(
					canonical->aliased_binding);
			}
		}
		bool function_template_ctor =
			ctor->function_specialization_symbol.size() != 0 ||
			(ctor->aliased_binding != NULL &&
			 ctor->aliased_binding->function_specialization_symbol.size() != 0);
		if (node.token_text == "inherited-constructor" &&
		    inherited_base.get() != NULL &&
		    record_is_template_specialization(inherited_base) &&
		    !function_template_ctor)
			program_.demand_inline_function(ctor, false);
		lower_constructor_call(base_addr, ctor, args, true);
		return;
	}
	TypePtr src_record = pa11::strip_cv(object_type(init.type));
	TypePtr dst_record = pa11::strip_cv(node.type);
	if (src_record->kind == TypeKind::Record &&
	    dst_record->kind == TypeKind::Record &&
	    pa11::same_type(src_record, dst_record) &&
	    (init.category == ValueCategory::LValue ||
	     init.category == ValueCategory::XValue))
	{
		Binding* copy_move =
			find_copy_move_constructor(
				node.type,
				init.category == ValueCategory::XValue);
		if (copy_move == NULL && init.category == ValueCategory::XValue)
			copy_move = find_copy_move_constructor(node.type, false);
		if (copy_move != NULL)
		{
			if (std_tuple_storage_copy_record(node.type) &&
			    record_has_storage_copy(node.type))
			{
				Value target = base_addr();
				Value source = ensure_pointer(emit_lvalue_addr(init));
				Value converted =
					convert_value(source,
					              pa11::make_pointer(src_record),
					              pa11::make_pointer(node.type));
				instr("copyobj " +
				      to_string(pa11::type_size(node.type)) +
				      "x" +
				      to_string(pa11::type_align(node.type)) +
				      " " + converted.text + ", " + target.text);
				return;
			}
			vector<const Node*> args;
			args.push_back(&init);
			lower_constructor_call(base_addr, copy_move, args, true);
			return;
		}
	}
	lower_object_init(base_addr, node.type, node.children[0]);
}
void FunctionLowerer::lower_delegating_init(const Node& node) {
Binding* ctor = node.direct_call; const Node* init = NULL; if (ctor == NULL && !node.children.empty()) ctor = node.children[0].direct_call;
if (!node.children.empty()) init = &node.children[0]; if (ctor == NULL) throw runtime_error("missing delegating constructor");
function<Value()> this_addr = [this]() { string this_ptr = fresh_temp(); instr(this_ptr + " = load ptr $this"); return Value("ptr", this_ptr);
}; vector<const Node*> args; if (init != NULL) for (size_t i = 0; i < init->children.size(); ++i)
args.push_back(&init->children[i]); lower_constructor_call(this_addr, ctor, args); } void FunctionLowerer::lower_storage_copy_action(const Node& node)
{ if (!node.has_constant_value || node.constant_value == 0 || node.children.empty()) return;
string self = fresh_temp(); instr(self + " = load ptr $this"); Value source = ensure_pointer(emit_lvalue_addr(node.children[0])); instr("copyobj " + to_string(node.constant_value) + "x" +
to_string(pa11::type_align(node.type)) + " " + source.text + ", " + self); } void FunctionLowerer::lower_member_init(const Node& node)
{ if (node.binding == NULL) return; Binding* alias_member = anonymous_storage_member_target(node.binding);
Binding* storage_member = alias_member != NULL ? node.binding->aliased_binding : node.binding;
uint64_t member_offset = storage_member->member_offset + (alias_member != NULL ? alias_member->member_offset : 0);
function<Value()> member_addr = [this, member_offset]() {
string this_ptr = fresh_temp(); instr(this_ptr + " = load ptr $this"); string addr = fresh_temp(); instr(addr + " = index i8 [projection=field] " + this_ptr +
", " + to_string(member_offset)); return Value("ptr", addr); }; if (!node.children.empty() &&
starts_with(node.children[0].line, "braced-init-list")) { if (node.direct_call != NULL) {
if (pa11::strip_cv(node.binding->type)->kind != TypeKind::Record) { lower_object_init(member_addr,
node.binding->type, node.children[0]); return; }
if (node.children[0].children.empty() && member_default_constructor_init_noop(program_, node.direct_call, node.binding->type)) { Value addr = member_addr(); if (zero_init_has_store(node.binding->type)) lower_storage_zero(addr, pa11::type_size(node.binding->type)); return; } if (node.direct_call->is_generated_default_constructor && !node.direct_call->is_defaulted &&
node.direct_call->unwind_no && pa11::strip_cv(node.binding->type)->kind == TypeKind::Record && pa11::strip_cv(node.binding->type)->base.get() != NULL) {
Value addr = member_addr(); if (zero_init_has_store(node.binding->type)) lower_storage_zero(addr, pa11::type_size(node.binding->type));
return; } Value addr = member_addr(); if (node.direct_call->is_generated_default_constructor)
lower_storage_zero(addr, pa11::type_size(node.binding->type)); function<Value()> same_addr = [addr]() { return addr; };
vector<const Node*> args; for (size_t i = 0; i < node.children[0].children.size(); ++i) args.push_back(&node.children[0].children[i]); lower_constructor_call(same_addr, node.direct_call, args);
return; } if (node.children[0].direct_call != NULL && node.children[0].direct_call->is_generated_default_constructor && !node.children[0].direct_call->is_defaulted &&
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
if (node.children.empty() && member_default_constructor_init_noop(program_, node.direct_call, node.binding->type)) { TypePtr bare_member = pa11::strip_cv(node.binding->type); if ((!node.children.empty() || (bare_member->kind == TypeKind::Record && bare_member->tag == "union")) && zero_init_has_store(node.binding->type)) { Value addr = member_addr(); lower_storage_zero(addr, pa11::type_size(node.binding->type)); } return true; } if (node.direct_call->is_generated_default_constructor && !node.direct_call->is_defaulted &&
node.direct_call->unwind_no && pa11::strip_cv(node.binding->type)->kind == TypeKind::Record && pa11::strip_cv(node.binding->type)->base.get() != NULL) {
Value addr = member_addr(); if (zero_init_has_store(node.binding->type)) lower_storage_zero(addr, pa11::type_size(node.binding->type)); return true;
} if (node.children.size() == 1 && node.children[0].category == ValueCategory::PRValue && pa11::strip_cv(node.binding->type)->kind == TypeKind::Record &&
pa11::same_type(pa11::strip_cv(node.binding->type), pa11::strip_cv(object_type(node.children[0].type)))) { if (member_default_constructor_init_noop(program_, node.children[0].direct_call,
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
program_.demand_function_declaration(node.direct_call); program_.demand_inline_function(node.direct_call); Value member = member_addr();
if (node.children.empty() && node.direct_call->is_defaulted && node.direct_call->type->parameters.size() == 1 && zero_init_has_store(node.binding->type))
lower_storage_zero(member, pa11::type_size(node.binding->type)); vector<string> lowered; lowered.push_back(member.text);
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
