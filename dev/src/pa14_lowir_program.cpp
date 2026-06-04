#include "pa14_lowir_internal.h"

#include <fstream>

namespace pa14 {
namespace internal {
namespace {

bool record_has_constructor(TypePtr type)
{
	TypePtr bare = pa11::strip_cv(type);
	if (bare->kind != TypeKind::Record || bare->scope == NULL)
		return false;
	map<string, vector<Binding*> >::const_iterator found =
		bare->scope->members.find(bare->scope->name);
	if (found == bare->scope->members.end())
		return false;
	for (size_t i = 0; i < found->second.size(); ++i)
		if (found->second[i]->kind == BindingKind::Function &&
		    found->second[i]->type->kind == TypeKind::Function)
			return true;
	return false;
}

bool record_has_destructor(TypePtr type)
{
	TypePtr bare = pa11::strip_cv(type);
	if (bare->kind == TypeKind::Array)
		return record_has_destructor(bare->base);
	if (bare->kind != TypeKind::Record)
		return false;
	if (bare->scope != NULL)
	{
		string dtor_name = "~" + bare->scope->name;
		map<string, vector<Binding*> >::const_iterator found =
			bare->scope->members.find(dtor_name);
		if (found != bare->scope->members.end())
			return true;
	}
	pa11::layout_record_type(bare);
	if (bare->base.get() != NULL && record_has_destructor(bare->base))
		return true;
	for (size_t i = 0; i < bare->fields.size(); ++i)
		if (record_has_destructor(bare->fields[i]->type))
			return true;
	return false;
}

Binding* find_assignment_binding(TypePtr type, bool move)
{
	TypePtr bare = pa11::strip_cv(type);
	if (bare->kind != TypeKind::Record || bare->scope == NULL)
		return NULL;
	map<string, vector<Binding*> >::const_iterator found =
		bare->scope->members.find("operator=");
	if (found == bare->scope->members.end())
		return NULL;
	for (size_t i = 0; i < found->second.size(); ++i)
	{
		Binding* op = found->second[i];
		if (op->kind != BindingKind::Function ||
		    op->type->kind != TypeKind::Function ||
		    op->type->parameters.size() != 2)
			continue;
		TypePtr param = op->type->parameters[1];
		if (!move &&
		    param->kind == TypeKind::LValueReference &&
		    pa11::same_type(pa11::strip_cv(param->base), bare))
			return op;
		if (move &&
		    param->kind == TypeKind::RValueReference &&
		    pa11::same_type(pa11::strip_cv(param->base), bare))
			return op;
	}
	return NULL;
}

bool global_static_scalar_initializer(const Node& init)
{
	if (starts_with(init.line, "literal"))
		return true;
	if (starts_with(init.line, "unary-expression") && init.has_op &&
	    init.op == OP_PLUS && !init.children.empty())
		return global_static_scalar_initializer(init.children[0]);
	if (starts_with(init.line, "binary-expression") && init.has_op &&
	    (init.op == OP_PLUS || init.op == OP_MINUS) &&
	    init.children.size() == 2)
	{
		const Node& lhs = init.children[0];
		const Node& rhs = init.children[1];
		return (lhs.binding != NULL && rhs.has_constant_value) ||
		       (rhs.binding != NULL && lhs.has_constant_value);
	}
	return init.has_constant_value;
}

bool global_needs_runtime_init(TypePtr type, const Node& init)
{
	TypePtr bare = pa11::strip_cv(type);
	if (starts_with(init.line, "constructor-action"))
		return true;
	if (starts_with(init.line, "braced-init-list"))
	{
		if (bare->kind == TypeKind::Record)
			return record_has_constructor(type);
		if (bare->kind == TypeKind::Array)
		{
			for (size_t i = 0; i < init.children.size(); ++i)
				if (global_needs_runtime_init(bare->base, init.children[i]))
					return true;
		}
		return false;
	}
	if (bare->kind == TypeKind::Record || bare->kind == TypeKind::Array)
		return true;
	if (pa11::strip_cv(type)->kind == TypeKind::Pointer &&
	    starts_with(init.line, "id-expression") &&
	    init.binding != NULL &&
	    pa11::strip_cv(init.binding->type)->kind == TypeKind::Array)
		return false;
	return !global_static_scalar_initializer(init);
}

void collect_direct_calls(const Node& node, set<const Binding*>& out)
{
	if (node.direct_call != NULL)
		out.insert(node.direct_call);
	for (size_t i = 0; i < node.children.size(); ++i)
		collect_direct_calls(node.children[i], out);
}

bool contains_call_expression(const Node& node)
{
	if (starts_with(node.line, "call-expression"))
		return true;
	for (size_t i = 0; i < node.children.size(); ++i)
		if (contains_call_expression(node.children[i]))
			return true;
	return false;
}

bool early_hidden_friend_definition(const Node& node,
                                    const set<const Binding*>& direct_calls)
{
	if (node.binding == NULL || !node.binding->is_hidden_friend)
		return false;
	return !contains_call_expression(node) ||
	       direct_calls.find(node.binding) != direct_calls.end();
}

bool generated_copy_move_constructor_node(const Node& node)
{
	return node.binding != NULL &&
	       node.binding->is_generated_copy_move_constructor;
}

bool is_class_constructor(const Binding* binding)
{
	return binding != NULL &&
	       binding->owner != NULL &&
	       binding->owner->kind == ScopeKind::Class &&
	       binding->name == binding->owner->name;
}

FunctionOut make_constructor_base_entry(const FunctionOut& lowered,
                                        const string& name)
{
	FunctionOut base_entry = lowered;
	string from = "function @" + name + "(";
	string to = "function @" + name + "__base_entry(";
	size_t pos = base_entry.header.find(from);
	if (pos != string::npos)
		base_entry.header.replace(pos, from.size(), to);
	return base_entry;
}

const Binding* first_base_default_constructor(const Binding* binding)
{
	if (binding == NULL || binding->name.empty() || binding->name[0] != '~' ||
	    binding->owner == NULL)
		return NULL;
	TypePtr record = pa11::record_type_for_scope(binding->owner);
	if (record.get() == NULL)
		return NULL;
	pa11::layout_record_type(record);
	if (!record->fields.empty())
		return NULL;
	for (TypePtr base = record->base; base.get() != NULL;
	     base = pa11::strip_cv(base)->base)
	{
		TypePtr bare = pa11::strip_cv(base);
		if (bare->kind != TypeKind::Record || bare->scope == NULL)
			return NULL;
		map<string, vector<Binding*> >::const_iterator found =
			bare->scope->members.find(bare->scope->name);
		if (found != bare->scope->members.end())
			for (size_t i = 0; i < found->second.size(); ++i)
				if (found->second[i]->kind == BindingKind::Function &&
				    found->second[i]->type->kind == TypeKind::Function &&
				    found->second[i]->type->parameters.size() == 1)
					return found->second[i];
	}
	return NULL;
}

}  // namespace

ProgramLowerer::ProgramLowerer()
	: needs_empty_init_function(false),
	  needs_eh_declarations(false),
	  generated_assignment_emit_depth(0)
{
}

string ProgramLowerer::global_scalar_initializer(TypePtr type, const Node& init)
{
	TypePtr bare = pa11::strip_cv(strip_for_value(type));
	if (starts_with(init.line, "literal") && init.token_text == "nullptr")
		return "zero";
	if (starts_with(init.line, "literal") &&
	    init.token_text.size() > 0 &&
	    init.token_text[init.token_text.size() - 1] == '"')
		return "addr @" + string_symbol(init.token_text);
	if (starts_with(init.line, "id-expression") && init.binding != NULL &&
	    scalar_lowir_type(type) == "ptr")
		return "addr @" + symbol_for(init.binding);
	if (starts_with(init.line, "unary-expression") && init.has_op &&
	    init.op == OP_PLUS && !init.children.empty())
		return global_scalar_initializer(type, init.children[0]);
	if (starts_with(init.line, "binary-expression") && init.has_op &&
	    (init.op == OP_PLUS || init.op == OP_MINUS) &&
	    init.children.size() == 2)
	{
		const Node& lhs = init.children[0];
		const Node& rhs = init.children[1];
		const Node* base = lhs.binding != NULL ? &lhs : &rhs;
		const Node* off = lhs.binding != NULL ? &rhs : &lhs;
		if (base->binding != NULL && off->has_constant_value)
		{
			uint64_t scale = 1;
			TypePtr ptr = strip_for_value(base->type);
			if (pa11::strip_cv(ptr)->kind == TypeKind::Pointer)
				scale = pa11::type_size(pa11::strip_cv(ptr)->base);
			int64_t addend = static_cast<int64_t>(off->constant_value * scale);
			if (init.op == OP_MINUS)
				addend = -addend;
			ostringstream out;
			out << "addr @" << symbol_for(base->binding);
			if (addend > 0)
				out << " + " << addend;
			else if (addend < 0)
				out << " - " << -addend;
			return out.str();
		}
	}
	(void)bare;
	return lowir_literal(type, init);
}

string ProgramLowerer::global_data_item(TypePtr elem, const Node& init)
{
	if (scalar_lowir_type(elem) == "ptr")
	{
		string value = global_scalar_initializer(elem, init);
		if (value == "zero")
			return "zero 8";
		return "ptr " + value;
	}
	return scalar_lowir_type(elem) + " " + lowir_literal(elem, init);
}

void ProgramLowerer::emit_global(const Node& node)
{
	if (node.binding == NULL)
		return;
	string name = symbol_for(node.binding);
	defined_globals.insert(name);
	if (node.binding->is_thread_local)
		ensure_thread_local_wrapper(name);
	TypePtr type = node.binding->type;
	ostringstream out;
	TypePtr bare = pa11::strip_cv(type);
	bool runtime_init =
		!node.children.empty() &&
		global_needs_runtime_init(type, node.children[0]);
	if (runtime_init)
		global_init_variables.push_back(node);
	if (record_has_destructor(type))
		global_fini_variables.push_back(node);
	if (bare->kind == TypeKind::Array || bare->kind == TypeKind::Record)
	{
		vector<string> metadata;
		if (node.binding->is_thread_local)
			metadata.push_back("storage=thread_local");
		if (node.binding->language_linkage == "c")
			metadata.push_back("linkage=c");
		metadata.push_back("binding=strong");
		out << "global @" << name << metadata_suffix(metadata) << " = {\n";
		if (runtime_init)
			out << "  zero " << pa11::type_size(type) << "\n";
		else if (bare->kind == TypeKind::Record)
		{
			out << "  zero " << pa11::type_size(type) << "\n";
			needs_empty_init_function = true;
		}
		else
		{
			TypePtr elem = bare->base;
			if (!node.children.empty() &&
			    starts_with(node.children[0].line, "braced-init-list"))
			{
				for (size_t i = 0; i < node.children[0].children.size(); ++i)
					out << "  " << global_data_item(elem, node.children[0].children[i])
					    << "\n";
				if (!bare->unknown_bound)
					for (size_t i = node.children[0].children.size(); i < bare->bound; ++i)
						out << "  zero " << pa11::type_size(elem) << "\n";
			}
			else
				out << "  zero " << pa11::type_size(type) << "\n";
		}
		out << "}";
	}
	else
	{
		vector<string> metadata;
		if (node.binding->is_thread_local)
			metadata.push_back("storage=thread_local");
		if (node.binding->language_linkage == "c")
			metadata.push_back("linkage=c");
		metadata.push_back("binding=strong");
		out << "global @" << name << " : " << scalar_lowir_type(type)
		    << metadata_suffix(metadata) << " = ";
		if (is_reference(type))
		{
			out << "zero";
			if (!node.children.empty())
			{
				const Node& init = node.children[0];
				if (starts_with(init.line, "id-expression") &&
				    init.binding != NULL)
					init_actions.push_back(
						InitAction(name, "addr", symbol_for(init.binding)));
				else if (starts_with(init.line, "unary-expression") &&
				         init.has_op && init.op == OP_STAR &&
				         !init.children.empty() &&
				         init.children[0].binding != NULL)
					init_actions.push_back(
						InitAction(name,
						           "load_ptr",
						           symbol_for(init.children[0].binding)));
			}
		}
		else if (runtime_init || node.children.empty())
			out << "zero";
		else if (starts_with(node.children[0].line, "literal") &&
		         node.children[0].token_text == "nullptr")
			out << "zero";
		else
			out << global_scalar_initializer(type, node.children[0]);
	}
	globals.push_back(out.str());
}

void ProgramLowerer::demand_global_declaration(const Binding* binding)
{
	if (binding == NULL)
		return;
	string name = symbol_for(binding);
	if (binding->is_thread_local)
		ensure_thread_local_wrapper(name);
	if (defined_globals.find(name) != defined_globals.end() ||
	    declared_globals.find(name) != declared_globals.end())
		return;
	ostringstream out;
	out << "declare global @" << name;
	vector<string> metadata;
	if (binding->is_thread_local)
		metadata.push_back("storage=thread_local");
	if (binding->language_linkage == "c")
		metadata.push_back("linkage=c");
	out << metadata_suffix(metadata);
	declared_globals.insert(name);
	global_declares.push_back(out.str());
}

void ProgramLowerer::ensure_thread_local_wrapper(const string& global_name)
{
	string name = global_name + "__tls_wrapper";
	if (declared_functions.find(name) != declared_functions.end() ||
	    defined_functions.find(name) != defined_functions.end())
		return;
	declared_functions.insert(name);
	declares.push_back("declare function @" + name + "() -> ptr");
}

void ProgramLowerer::ensure_eh_declarations()
{
	if (needs_eh_declarations)
		return;
	needs_eh_declarations = true;
	if (declared_functions.insert("__cppgm_eh_resume").second)
		declares.push_back(
			"declare function @__cppgm_eh_resume() -> void [role=eh_resume]");
	if (declared_functions.insert("__cppgm_eh_personality").second)
		declares.push_back(
			"declare function @__cppgm_eh_personality() -> void [role=eh_personality]");
}

namespace {

string typeinfo_name_symbol(TypePtr record)
{
	TypePtr bare = pa11::strip_cv(record);
	return "__typeinfo_name__" + bare->tag + "_" + record_lowir_name(bare);
}

string typeinfo_name_spelling(TypePtr record)
{
	TypePtr bare = pa11::strip_cv(record);
	return to_string(bare->name.size()) + bare->name;
}

void append_typeinfo_name_global(vector<string>& globals, TypePtr record)
{
	ostringstream out;
	out << "global @" << typeinfo_name_symbol(record)
	    << " [storage=readonly, binding=weak] = {\n";
	string name = typeinfo_name_spelling(record);
	for (size_t i = 0; i < name.size(); ++i)
		out << "  i8 " << static_cast<unsigned>(
			static_cast<unsigned char>(name[i])) << "\n";
	out << "  i8 0\n";
	out << "}";
	globals.push_back(out.str());
}

}  // namespace

void ProgramLowerer::emit_rtti(TypePtr record)
{
	TypePtr bare = pa11::strip_cv(record);
	if (bare->kind != TypeKind::Record)
		return;
	if (emitted_rtti.find(bare.get()) != emitted_rtti.end())
		return;
	emitted_rtti.insert(bare.get());
	if (declared_globals.insert("__external_rtti_vtable____class_type_info").second)
		global_declares.push_back(
			"declare global @__external_rtti_vtable____class_type_info "
			"[binding=strong]");
	TypePtr direct_base =
		bare->base.get() != NULL ? pa11::strip_cv(bare->base) : TypePtr();
	if (direct_base.get() != NULL && direct_base->kind == TypeKind::Record)
	{
		emit_rtti(direct_base);
		if (declared_globals.insert(
			    "__external_rtti_vtable____si_class_type_info").second)
			global_declares.push_back(
				"declare global @__external_rtti_vtable____si_class_type_info "
				"[binding=strong]");
	}
	append_typeinfo_name_global(globals, bare);
	ostringstream out;
	out << "global @" << rtti_symbol_for_record(bare)
	    << " [storage=readonly, binding=weak] = {\n";
	if (direct_base.get() != NULL && direct_base->kind == TypeKind::Record)
	{
		out << "  ptr addr @__external_rtti_vtable____si_class_type_info + 16\n";
		out << "  ptr addr @" << typeinfo_name_symbol(bare) << "\n";
		out << "  ptr addr @" << rtti_symbol_for_record(direct_base) << "\n";
	}
	else
	{
		out << "  ptr addr @__external_rtti_vtable____class_type_info + 16\n";
		out << "  ptr addr @" << typeinfo_name_symbol(bare) << "\n";
	}
	out << "}";
	globals.push_back(out.str());
}

void ProgramLowerer::emit_deleting_destructor_entry(const Binding* dtor)
{
	if (dtor == NULL || emitted_deleting_destructors.find(dtor) !=
	    emitted_deleting_destructors.end())
		return;
	emitted_deleting_destructors.insert(dtor);
	TypePtr record = class_record_for_member(dtor);
	if (record.get() == NULL)
		return;
	ensure_eh_declarations();
	demand_function_declaration(dtor);
	demand_inline_function(dtor);
	if (declared_functions.find("operator_delete") == declared_functions.end() &&
	    defined_functions.find("operator_delete") == defined_functions.end())
	{
		declared_functions.insert("operator_delete");
		declares.push_back(
			"declare function @operator_delete(%arg0 : ptr) -> void "
			"[unwind=no, binding=strong, object=cppgm_builtin_operator_delete]");
	}
	string name = symbol_for(dtor) + "__deleting_entry";
	if (defined_functions.find(name) != defined_functions.end())
		return;
	defined_functions.insert(name);
	FunctionOut out;
	out.header = "function @" + name + "(%this : ptr) -> void [binding=weak]";
	out.slots.push_back("  slot $this : ptr");
	Block block("entry");
	int temp = 1;
	block.instrs.push_back("    store ptr %this, $this");
	string self = "%t" + to_string(temp++);
	block.instrs.push_back("    " + self + " = load ptr $this");
	string vt = "%t" + to_string(temp++);
	block.instrs.push_back("    " + vt + " = addr @" +
	                       vtable_symbol_for_record(record));
	string addr_point = "%t" + to_string(temp++);
	block.instrs.push_back("    " + addr_point + " = index i8 " + vt + ", 16");
	block.instrs.push_back("    store ptr " + addr_point + ", " + self);
	TypePtr bare = pa11::strip_cv(record);
	if (bare->base.get() != NULL)
	{
		TypePtr base = pa11::strip_cv(bare->base);
		Binding* base_dtor = find_destructor(base);
		if (base_dtor != NULL && base_dtor->is_virtual)
		{
			demand_function_declaration(base_dtor);
			string base_callee = destructor_symbol_for(base_dtor, true);
			demand_inline_function(base_dtor, false);
			string reload = "%t" + to_string(temp++);
			block.instrs.push_back("    " + reload + " = load ptr $this");
			string base_addr = "%t" + to_string(temp++);
			block.instrs.push_back(
				"    " + base_addr +
				" = index i8 [projection=base_subobject] " +
				reload + ", " +
				to_string(base_subobject_offset(record, base)));
			block.instrs.push_back("    call void @" + base_callee +
			                       "(" + base_addr + ")");
		}
	}
	string del_arg = "%t" + to_string(temp++);
	block.instrs.push_back("    " + del_arg + " = load ptr $this");
	block.instrs.push_back("    call void @operator_delete(" + del_arg + ")");
	block.instrs.push_back("    return void");
	block.terminated = true;
	out.blocks.push_back(block);
	functions.push_back(out);
}

void ProgramLowerer::demand_vtable(TypePtr record)
{
	TypePtr bare = pa11::strip_cv(record);
	if (bare->kind != TypeKind::Record || !bare->is_polymorphic)
		return;
	if (emitted_vtables.find(bare.get()) != emitted_vtables.end())
		return;
	TypePtr direct_base =
		bare->base.get() != NULL ? pa11::strip_cv(bare->base) : TypePtr();
	if (direct_base.get() != NULL &&
	    direct_base->kind == TypeKind::Record &&
	    direct_base->is_polymorphic)
		demand_vtable(direct_base);
	emitted_vtables.insert(bare.get());
	emit_rtti(bare);
	ostringstream out;
	out << "global @" << vtable_symbol_for_record(bare)
	    << " [storage=readonly, binding=weak] = {\n";
	out << "  i64 0\n";
	out << "  ptr addr @" << rtti_symbol_for_record(bare) << "\n";
	for (size_t i = 0; i < bare->virtual_entries.size(); ++i)
	{
		Binding* fn = bare->virtual_entries[i].function;
		if (fn == NULL)
			continue;
		if (fn->is_pure_virtual)
		{
			string ret = scalar_lowir_type(fn->type->base);
			string sig = "__cxa_pure_virtual " + ret;
			if (declared_pure_virtual_signatures.insert(sig).second &&
			    declared_functions.insert("__cxa_pure_virtual").second)
				declares.push_back(
					"declare function @__cxa_pure_virtual(%arg0 : ptr) -> " +
					ret +
					" [effects=readnone, unwind=no, return=noreturn, "
					"binding=strong]");
			out << "  ptr addr @__cxa_pure_virtual\n";
			continue;
		}
		if (bare->virtual_entries[i].deleting_entry)
		{
			emit_deleting_destructor_entry(fn);
			out << "  ptr addr @" << symbol_for(fn) << "__deleting_entry\n";
			continue;
		}
		demand_function_declaration(fn);
		demand_inline_function(fn);
		out << "  ptr addr @" << symbol_for(fn) << "\n";
	}
	out << "}";
	globals.push_back(out.str());
}

Binding* ProgramLowerer::demand_implicit_copy_assignment(TypePtr type, bool move)
{
	TypePtr record = pa11::strip_cv(type);
	if (record->kind != TypeKind::Record || record->scope == NULL)
		throw runtime_error("assignment target is not record");
	if (move)
		demand_implicit_copy_assignment(type, false);
	const void* key = record.get();
	map<const void*, Binding*>& cache =
		move ? implicit_move_assignments : implicit_copy_assignments;
	map<const void*, Binding*>::const_iterator found =
		cache.find(key);
	if (found != cache.end())
		return found->second;

	vector<TypePtr> params;
	params.push_back(pa11::make_pointer(record));
	params.push_back(move
		? pa11::make_rvalue_reference(record)
		: pa11::make_lvalue_reference(
			pa11::make_cv(record, pa11::CV_CONST)));
	TypePtr fn_type = pa11::make_function(pa11::make_pointer(record),
	                                      params,
	                                      false);
	synthetic_bindings.push_back(unique_ptr<Binding>(
		new Binding(BindingKind::Function, "operator=", record->scope)));
	Binding* binding = synthetic_bindings.back().get();
	binding->type = fn_type;
	binding->is_inline_definition = true;
	binding->is_generated_copy_move_assignment = true;
	cache[key] = binding;
	string name = symbol_for(binding);
	if (defined_functions.find(name) != defined_functions.end())
		return binding;
	defined_functions.insert(name);
	queue_synthetic_assignment_function(binding, record, move, name);
	return binding;
}

void ProgramLowerer::queue_synthetic_assignment_function(Binding* binding,
                                                         TypePtr record,
                                                         bool move,
                                                         const string& name)
{
	(void)binding;
	FunctionOut out;
	ostringstream header;
	header << "function @" << name
	       << "(%this : ptr, %other : ptr [pass=reference]) -> ptr";
	vector<string> metadata;
	metadata.push_back("binding=weak");
	header << metadata_suffix(metadata);
	out.header = header.str();
	out.slots.push_back("  slot $this : ptr");
	out.slots.push_back("  slot $other : ptr");
	Block block("entry");
	block.instrs.push_back("    store ptr %this, $this");
	block.instrs.push_back("    store ptr %other, $other");
	pa11::layout_record_type(record);
	bool has_bitfield = false;
	for (size_t i = 0; i < record->fields.size(); ++i)
		if (record->fields[i]->is_bit_field)
			has_bitfield = true;
	if (has_bitfield)
	{
		set<uint64_t> copied_units;
		int temp = 1;
		for (size_t i = 0; i < record->fields.size(); ++i)
		{
			Binding* field = record->fields[i];
			if (!field->is_bit_field ||
			    copied_units.find(field->member_offset) != copied_units.end())
				continue;
			copied_units.insert(field->member_offset);
			string other = "%t" + to_string(temp++);
			string other_field = "%t" + to_string(temp++);
			string value = "%t" + to_string(temp++);
			string self = "%t" + to_string(temp++);
			string self_field = "%t" + to_string(temp++);
			string low_type = scalar_lowir_type(field->type);
			block.instrs.push_back("    " + other + " = load ptr $other");
			block.instrs.push_back("    " + other_field +
			                       " = index i8 " + other + ", " +
			                       to_string(field->member_offset));
			block.instrs.push_back("    " + value + " = load " +
			                       low_type + " " + other_field);
			block.instrs.push_back("    " + self + " = load ptr $this");
			block.instrs.push_back("    " + self_field +
			                       " = index i8 " + self + ", " +
			                       to_string(field->member_offset));
			block.instrs.push_back("    store " + low_type + " " +
			                       value + ", " + self_field);
		}
		block.instrs.push_back("    %t" + to_string(temp) +
		                       " = load ptr $this");
		block.instrs.push_back("    return ptr %t" + to_string(temp));
	}
	else
	{
		vector<pair<Binding*, Binding*> > field_ops;
		uint64_t prefix_size = pa11::type_size(record);
		for (size_t i = 0; i < record->fields.size(); ++i)
		{
			Binding* op = find_assignment_binding(record->fields[i]->type, move);
			if (op == NULL && move)
				op = find_assignment_binding(record->fields[i]->type, false);
			if (op == NULL || !op->is_inline_definition)
				continue;
			if (field_ops.empty())
				prefix_size = record->fields[i]->member_offset;
			field_ops.push_back(make_pair(record->fields[i], op));
		}
		int temp = 1;
		string self = "%t" + to_string(temp++);
		string other = "%t" + to_string(temp++);
		block.instrs.push_back("    " + self + " = load ptr $this");
		block.instrs.push_back("    " + other + " = load ptr $other");
		if (prefix_size != 0)
			block.instrs.push_back(
				"    copyobj " + to_string(prefix_size) +
				"x" + to_string(pa11::type_align(record)) + " " +
				other + ", " + self);
		for (size_t i = 0; i < field_ops.size(); ++i)
		{
			Binding* field = field_ops[i].first;
			Binding* op = field_ops[i].second;
			demand_function_declaration(op);
			demand_inline_function(op);
			string self_field = "%t" + to_string(temp++);
			string other_field = "%t" + to_string(temp++);
			block.instrs.push_back("    " + self_field +
			                       " = index i8 " + self + ", " +
			                       to_string(field->member_offset));
			block.instrs.push_back("    " + other_field +
			                       " = index i8 " + other + ", " +
			                       to_string(field->member_offset));
			string ignored = "%t" + to_string(temp++);
			block.instrs.push_back("    " + ignored + " = call ptr @" +
			                       symbol_for(op) + "(" + self_field +
			                       ", " + other_field + ")");
		}
		string ret = "%t" + to_string(temp++);
		block.instrs.push_back("    " + ret + " = load ptr $this");
		block.instrs.push_back("    return ptr " + ret);
	}
	block.terminated = true;
	out.blocks.push_back(block);
	pending_synthetic_assignment_functions.push_back(out);
}

void ProgramLowerer::emit_pending_synthetic_assignment_functions()
{
	if (pending_synthetic_assignment_functions.empty())
		return;
	functions.insert(functions.end(),
	                 pending_synthetic_assignment_functions.begin(),
	                 pending_synthetic_assignment_functions.end());
	pending_synthetic_assignment_functions.clear();
}

void ProgramLowerer::collect_node(const Node& node)
{
	if (starts_with(node.line, "namespace-definition"))
	{
		for (size_t i = 0; i < node.children.size(); ++i)
			collect_node(node.children[i]);
		return;
	}
	if (starts_with(node.line, "variable "))
	{
		if (node.binding != NULL &&
		    ((node.binding->owner != NULL &&
		      node.binding->owner->kind == ScopeKind::Namespace) ||
		     node.binding->is_static_member))
			emit_global(node);
		return;
	}
	if (starts_with(node.line, "function-declaration "))
	{
		if (node.token_text == "deleted")
			return;
		register_function_declaration(node);
		return;
	}
	if (starts_with(node.line, "function-definition "))
	{
		if (node.binding != NULL && node.binding->is_virtual)
		{
			TypePtr record = class_record_for_member(node.binding);
			if (record.get() != NULL)
				demand_vtable(record);
		}
		if (node.binding != NULL && node.binding->is_inline_definition)
		{
			register_inline_definition(node);
			return;
		}
		if (node.binding != NULL)
			defined_functions.insert(symbol_for(node.binding));
		FunctionLowerer lowerer(*this, node);
		FunctionOut lowered = lowerer.lower();
		if (is_class_constructor(node.binding))
		{
			string name = symbol_for(node.binding);
			functions.push_back(make_constructor_base_entry(lowered, name));
		}
		if (node.binding != NULL &&
		    node.binding->owner != NULL &&
		    node.binding->owner->kind == ScopeKind::Class &&
		    !node.binding->name.empty() &&
		    node.binding->name[0] == '~' &&
		    node.binding->is_noop_destructor)
		{
			FunctionOut noop_entry = lowered;
			string name = symbol_for(node.binding);
			string from = "function @" + name + "(";
			string to = "function @" + name + "__noop_entry(";
			size_t pos = noop_entry.header.find(from);
			if (pos != string::npos)
				noop_entry.header.replace(pos, from.size(), to);
			functions.push_back(noop_entry);
		}
		functions.push_back(lowered);
		emit_pending_synthetic_assignment_functions();
		return;
	}
	for (size_t i = 0; i < node.children.size(); ++i)
		collect_node(node.children[i]);
}

void ProgramLowerer::register_function_declaration(const Node& node)
{
	Binding* binding = node.binding;
	if (binding == NULL)
		return;
	string name = symbol_for(binding);
	if (function_declarations_by_binding.find(binding) !=
	    function_declarations_by_binding.end())
		return;
	bool indirect_result =
		pa11::strip_cv(binding->type->base)->kind == TypeKind::Record &&
		record_return_by_address(binding->type->base);
	ostringstream out;
	out << "declare function @" << name << "(";
	if (indirect_result)
		out << "%ret : ptr [pass=indirect_result]";
	for (size_t i = 0; i < binding->type->parameters.size(); ++i)
	{
		if (i != 0 || indirect_result)
			out << ", ";
		out << "%arg" << i << " : "
		    << lowir_parameter(binding->type->parameters[i]);
	}
	out << ") -> " << (indirect_result ? "void" :
	                    scalar_lowir_type(binding->type->base));
	vector<string> metadata;
	if (binding->type->variadic)
		metadata.push_back("arity=variadic");
	if (binding->language_linkage == "c")
		metadata.push_back("linkage=c");
	if (binding->unwind_no)
		metadata.push_back("unwind=no");
	metadata.push_back("binding=strong");
	out << metadata_suffix(metadata);
	function_declarations_by_binding[binding] = out.str();
}

void ProgramLowerer::register_inline_definition(const Node& node)
{
	if (node.binding == NULL)
		return;
	symbol_for(node.binding);
	if (inline_definition_ranks.find(node.binding) == inline_definition_ranks.end())
		inline_definition_ranks[node.binding] = inline_definition_ranks.size();
	inline_definitions[node.binding] = &node;
}

void ProgramLowerer::demand_function_declaration(const Binding* binding)
{
	if (binding == NULL)
		return;
	string name = symbol_for(binding);
	if (defined_functions.find(name) != defined_functions.end() ||
	    declared_functions.find(name) != declared_functions.end())
		return;
	map<const Binding*, string>::const_iterator found =
		function_declarations_by_binding.find(binding);
	if (found == function_declarations_by_binding.end())
	{
		if (binding->name == "__builtin_strlen")
		{
			declared_functions.insert(name);
			declares.push_back(
				"declare function @__builtin_strlen(%arg0 : ptr "
				"[capture=nocapture, access=read]) -> i64 "
				"[effects=readonly, unwind=no, binding=strong, "
				"object=cppgm_builtin_strlen]");
		}
		else if (binding->name == "__builtin_unreachable")
		{
			declared_functions.insert(name);
			declares.push_back(
				"declare function @__builtin_unreachable() -> void "
				"[effects=readnone, unwind=no, return=noreturn, "
				"binding=strong, object=cppgm_builtin_unreachable]");
		}
		else if (binding->name == "__builtin_memcpy")
		{
			declared_functions.insert(name);
			declares.push_back(
				"declare function @__builtin_memcpy(%arg0 : ptr "
				"[capture=nocapture, access=write, alias=noalias], "
				"%arg1 : ptr [capture=nocapture, access=read, alias=noalias], "
				"%arg2 : i64) -> ptr [effects=readwrite, unwind=no, "
				"binding=strong, object=cppgm_builtin_memcpy]");
		}
		else if (binding->name == "__builtin_memmove")
		{
			declared_functions.insert(name);
			declares.push_back(
				"declare function @__builtin_memmove(%arg0 : ptr "
				"[capture=nocapture, access=readwrite], "
				"%arg1 : ptr [capture=nocapture, access=read], "
				"%arg2 : i64) -> ptr [effects=readwrite, unwind=no, "
				"binding=strong, object=cppgm_builtin_memmove]");
		}
		else if (binding->owner != NULL &&
		         binding->owner->parent == NULL &&
		         binding->name == "operatornew")
		{
			declared_functions.insert(name);
			declares.push_back(
				"declare function @operator_new(%arg0 : i64) -> ptr "
				"[binding=strong, object=cppgm_builtin_operator_new]");
		}
		else if (binding->owner != NULL &&
		         binding->owner->parent == NULL &&
		         binding->name == "operatordelete")
		{
			declared_functions.insert(name);
			declares.push_back(
				"declare function @operator_delete(%arg0 : ptr) -> void "
				"[unwind=no, binding=strong, object=cppgm_builtin_operator_delete]");
		}
		else if (binding->owner != NULL &&
		         binding->owner->parent == NULL &&
		         binding->name == "operatornew[]")
		{
			declared_functions.insert(name);
			declares.push_back(
				"declare function @operator_new__(%arg0 : i64) -> ptr "
				"[binding=strong, object=cppgm_builtin_operator_new_array]");
		}
		else if (binding->owner != NULL &&
		         binding->owner->parent == NULL &&
		         binding->name == "operatordelete[]")
		{
			declared_functions.insert(name);
			declares.push_back(
				"declare function @operator_delete__(%arg0 : ptr) -> void "
				"[unwind=no, binding=strong, object=cppgm_builtin_operator_delete_array]");
		}
		else
		{
			bool indirect_result =
				pa11::strip_cv(binding->type->base)->kind == TypeKind::Record &&
				record_return_by_address(binding->type->base);
			ostringstream out;
			out << "declare function @" << name << "(";
			if (indirect_result)
				out << "%ret : ptr [pass=indirect_result]";
			for (size_t i = 0; i < binding->type->parameters.size(); ++i)
			{
				if (i != 0 || indirect_result)
					out << ", ";
				out << "%arg" << i << " : "
				    << lowir_parameter(binding->type->parameters[i]);
			}
			out << ") -> " << (indirect_result ? "void" :
			                    scalar_lowir_type(binding->type->base));
			vector<string> metadata;
			if (binding->type->variadic)
				metadata.push_back("arity=variadic");
			if (binding->language_linkage == "c")
				metadata.push_back("linkage=c");
			if (binding->unwind_no)
				metadata.push_back("unwind=no");
			metadata.push_back("binding=strong");
			out << metadata_suffix(metadata);
			declared_functions.insert(name);
			declares.push_back(out.str());
		}
		return;
	}
	declared_functions.insert(name);
	declares.push_back(found->second);
}

void ProgramLowerer::demand_inline_function(const Binding* binding,
                                            bool complete_entry)
{
	if (binding == NULL || !binding->is_inline_definition)
		return;
	bool class_ctor = is_class_constructor(binding);
	bool class_dtor = is_class_destructor_binding(binding);
	if (complete_entry)
		demanded_inline_complete_entries.insert(binding);
	else if (!class_ctor && !class_dtor)
		return;
	demand_move_assignment_copy_dependency(binding);
	string name = symbol_for(binding);
	if (complete_entry && defined_functions.find(name) != defined_functions.end())
		return;
	if (!complete_entry &&
	    defined_functions.find(name + "__base_entry") != defined_functions.end())
		return;
	for (size_t i = 0; i < pending_inline_definitions.size(); ++i)
		if (pending_inline_definitions[i] == binding)
			return;
	map<const Binding*, const Node*>::const_iterator found =
		inline_definitions.find(binding);
	if (found != inline_definitions.end())
		insert_pending_inline_definition(binding);
}

void ProgramLowerer::demand_move_assignment_copy_dependency(
	const Binding* binding)
{
	if (binding == NULL ||
	    !binding->is_generated_copy_move_assignment ||
	    binding->type->kind != TypeKind::Function ||
	    binding->type->parameters.size() != 2 ||
	    binding->type->parameters[1]->kind != TypeKind::RValueReference ||
	    binding->owner == NULL)
		return;
	map<string, vector<Binding*> >::const_iterator found =
		binding->owner->members.find("operator=");
	if (found == binding->owner->members.end())
		return;
	for (size_t i = 0; i < found->second.size(); ++i)
	{
		Binding* candidate = found->second[i];
		if (candidate->is_generated_copy_move_assignment &&
		    candidate->type->kind == TypeKind::Function &&
		    candidate->type->parameters.size() == 2 &&
		    candidate->type->parameters[1]->kind == TypeKind::LValueReference)
		{
			demand_inline_function(candidate);
			break;
		}
	}
}

void ProgramLowerer::insert_pending_inline_definition(const Binding* binding)
{
	vector<const Binding*>::iterator pos = pending_inline_definitions.end();
	if (binding->is_generated_copy_move_assignment &&
	    binding->type->kind == TypeKind::Function &&
	    binding->type->parameters.size() == 2 &&
	    binding->type->parameters[1]->kind == TypeKind::LValueReference)
		for (vector<const Binding*>::iterator it =
		     pending_inline_definitions.begin();
		     it != pending_inline_definitions.end(); ++it)
			if ((*it)->is_generated_copy_move_assignment &&
			    (*it)->type->kind == TypeKind::Function &&
			    (*it)->type->parameters.size() == 2 &&
			    (*it)->type->parameters[1]->kind == TypeKind::RValueReference)
			{
				pos = it;
				break;
			}
	if (binding->name == "operator=" &&
	    !binding->is_generated_copy_move_assignment &&
	    binding->owner != NULL)
		for (vector<const Binding*>::iterator it =
		     pending_inline_definitions.begin();
		     it != pending_inline_definitions.end(); ++it)
			if ((*it)->owner == binding->owner &&
			    (*it)->name != binding->owner->name)
			{
				pos = it;
				break;
			}
	if (binding->owner != NULL && binding->name == binding->owner->name)
		for (vector<const Binding*>::iterator it =
		     pending_inline_definitions.begin();
		     it != pending_inline_definitions.end(); ++it)
			if ((*it)->owner == binding->owner &&
			    ((*it)->name == "operator=" ||
			     (*it)->name.compare(0, 9, "operator ") == 0))
			{
				pos = it;
				break;
			}
	bool binding_const_conversion =
		binding->name.compare(0, 9, "operator ") == 0 &&
		binding->type->kind == TypeKind::Function &&
		!binding->type->parameters.empty() &&
		pa11::strip_cv(binding->type->parameters[0])->kind ==
			TypeKind::Pointer &&
		(pa11::strip_cv(binding->type->parameters[0])->base->cv &
		 pa11::CV_CONST) != 0;
	if (binding_const_conversion && binding->owner != NULL)
		for (vector<const Binding*>::iterator it =
		     pending_inline_definitions.begin();
		     it != pending_inline_definitions.end(); ++it)
		{
			bool pending_conversion =
				(*it)->name.compare(0, 9, "operator ") == 0 &&
				(*it)->type->kind == TypeKind::Function &&
				!(*it)->type->parameters.empty() &&
				pa11::strip_cv((*it)->type->parameters[0])->kind ==
					TypeKind::Pointer;
			bool pending_const =
				pending_conversion &&
				(pa11::strip_cv((*it)->type->parameters[0])->base->cv &
				 pa11::CV_CONST) != 0;
			if ((*it)->owner == binding->owner &&
			    pending_conversion && !pending_const)
			{
				pos = it;
				break;
			}
		}
	map<const Binding*, size_t>::const_iterator binding_rank =
		inline_definition_ranks.find(binding);
	bool operator_function = binding->name.compare(0, 8, "operator") == 0;
	if (binding_rank != inline_definition_ranks.end() &&
	    binding->owner != NULL &&
	    !binding->is_generated_copy_move_assignment &&
	    !operator_function)
		for (vector<const Binding*>::iterator it =
		     pending_inline_definitions.begin();
		     it != pending_inline_definitions.end(); ++it)
		{
			map<const Binding*, size_t>::const_iterator pending_rank =
				inline_definition_ranks.find(*it);
			if (pending_rank != inline_definition_ranks.end() &&
			    (*it)->owner == binding->owner &&
			    !(*it)->is_generated_copy_move_assignment &&
			    pending_rank->second > binding_rank->second)
			{
				pos = it;
				break;
			}
		}
	if (binding->name != "operator[]" &&
	    (binding->name.empty() || binding->name[0] != '~'))
		for (vector<const Binding*>::iterator it =
		     pending_inline_definitions.begin();
		     it != pending_inline_definitions.end(); ++it)
			if ((*it)->name == "operator[]" ||
			    (generated_assignment_emit_depth == 0 &&
			     (*it)->is_generated_copy_move_assignment) ||
			    (!(*it)->name.empty() && (*it)->name[0] == '~'))
			{
				pos = it;
				break;
			}
	pending_inline_definitions.insert(pos, binding);
}

void ProgramLowerer::emit_pending_inline_definitions()
{
	while (!pending_inline_definitions.empty())
	{
		const Binding* binding = pending_inline_definitions.front();
		pending_inline_definitions.erase(pending_inline_definitions.begin());
		map<const Binding*, const Node*>::const_iterator found =
			inline_definitions.find(binding);
		if (found == inline_definitions.end())
			continue;
		const Binding* base_ctor = first_base_default_constructor(binding);
		string base_ctor_name;
		bool base_ctor_complete = false;
		if (base_ctor != NULL)
		{
			base_ctor_complete = !base_ctor->is_generated_default_constructor;
			base_ctor_name = base_ctor_complete
				? symbol_for(base_ctor)
				: constructor_symbol_for(base_ctor, true);
		}
		if (base_ctor != NULL &&
		    defined_functions.find(base_ctor_name) ==
		    defined_functions.end() &&
		    inline_definitions.find(base_ctor) != inline_definitions.end())
		{
			pending_inline_definitions.insert(pending_inline_definitions.begin(),
			                                  binding);
			demand_inline_function(base_ctor, base_ctor_complete);
			continue;
		}
		string name = symbol_for(binding);
		bool class_ctor = is_class_constructor(binding);
		bool class_dtor = is_class_destructor_binding(binding);
		bool need_complete =
			!class_ctor ||
			demanded_inline_complete_entries.find(binding) !=
			demanded_inline_complete_entries.end();
		bool need_base =
			(class_ctor &&
			 demanded_constructor_base_entries.find(binding) !=
			 demanded_constructor_base_entries.end()) ||
			(class_dtor &&
			 demanded_destructor_base_entries.find(binding) !=
			 demanded_destructor_base_entries.end());
		if (defined_functions.find(name) != defined_functions.end())
			need_complete = false;
		if (defined_functions.find(name + "__base_entry") !=
		    defined_functions.end())
			need_base = false;
		if (!need_complete && !need_base)
			continue;
		if (need_complete)
			defined_functions.insert(name);
		if (need_base)
			defined_functions.insert(name + "__base_entry");
		FunctionLowerer lowerer(*this, *found->second);
		if (binding->is_generated_copy_move_assignment)
			++generated_assignment_emit_depth;
		FunctionOut lowered = lowerer.lower();
		if (binding->is_generated_copy_move_assignment)
			--generated_assignment_emit_depth;
		if (!binding->name.empty() && binding->name[0] == '~')
			emit_pending_inline_definitions();
		if (need_base)
			functions.push_back(make_constructor_base_entry(lowered, name));
		if (need_complete)
			functions.push_back(lowered);
		emit_pending_synthetic_assignment_functions();
	}
}

void ProgramLowerer::emit_global_lifecycle_functions()
{
	TypePtr void_type = pa11::make_fundamental(FT_VOID);
	TypePtr fn_type = pa11::make_function(void_type, vector<TypePtr>(), false);
	if (!global_init_variables.empty())
	{
		synthetic_bindings.push_back(unique_ptr<Binding>(
			new Binding(BindingKind::Function, "__cppgm_init", NULL)));
		Binding* binding = synthetic_bindings.back().get();
		binding->type = fn_type;
		Node fn("function-definition __cppgm_init " +
		        pa11::describe_type(fn_type));
		fn.binding = binding;
		fn.type = fn_type;
		Node body("compound-statement");
		for (size_t i = 0; i < global_init_variables.size(); ++i)
		{
			Node action("global-init-variable");
			pa12::internal::add_child(action, global_init_variables[i]);
			pa12::internal::add_child(body, action);
		}
		pa12::internal::add_child(fn, body);
		string name = symbol_for(binding);
		defined_functions.insert(name);
		FunctionLowerer lowerer(*this, fn);
		functions.push_back(lowerer.lower());
		emit_pending_inline_definitions();
	}
	if (!global_fini_variables.empty())
	{
		synthetic_bindings.push_back(unique_ptr<Binding>(
			new Binding(BindingKind::Function, "__cppgm_fini", NULL)));
		Binding* binding = synthetic_bindings.back().get();
		binding->type = fn_type;
		Node fn("function-definition __cppgm_fini " +
		        pa11::describe_type(fn_type));
		fn.binding = binding;
		fn.type = fn_type;
		Node body("compound-statement");
		for (size_t n = 0; n < global_fini_variables.size(); ++n)
		{
			size_t i = global_fini_variables.size() - 1 - n;
			Node action("global-fini-variable");
			pa12::internal::add_child(action, global_fini_variables[i]);
			pa12::internal::add_child(body, action);
		}
		pa12::internal::add_child(fn, body);
		string name = symbol_for(binding);
		defined_functions.insert(name);
		FunctionLowerer lowerer(*this, fn);
		functions.push_back(lowerer.lower());
		emit_pending_inline_definitions();
	}
}

void ProgramLowerer::collect_translation_unit(const Node& root)
{
	for (size_t i = 0; i < root.children.size(); ++i)
		collect_node(root.children[i]);
	emit_pending_inline_definitions();
}

void ProgramLowerer::write(const string& outfile) const
{
	ofstream out(outfile.c_str());
	if (!out)
		throw runtime_error("cannot open output file");
	for (size_t i = 0; i < declares.size(); ++i)
	{
		size_t at = declares[i].find('@');
		size_t lp = declares[i].find('(', at);
		string name = (at == string::npos || lp == string::npos)
			? "" : declares[i].substr(at + 1, lp - at - 1);
		if (defined_functions.find(name) == defined_functions.end())
			out << declares[i] << "\n\n";
	}
	for (size_t i = 0; i < string_defs.size(); ++i)
	{
		out << "global @" << string_defs[i].first << " [binding=internal] = {\n";
		for (size_t j = 0; j < string_defs[i].second.size(); ++j)
			out << "  i8 " << static_cast<unsigned>(string_defs[i].second[j]) << "\n";
		out << "}\n\n";
	}
	for (size_t i = 0; i < global_declares.size(); ++i)
	{
		size_t at = global_declares[i].find('@');
		size_t end = global_declares[i].find_first_of(" [", at);
		string name = (at == string::npos || end == string::npos)
			? "" : global_declares[i].substr(at + 1, end - at - 1);
		if (defined_globals.find(name) == defined_globals.end())
			out << global_declares[i] << "\n\n";
	}
	for (size_t i = 0; i < globals.size(); ++i)
		out << globals[i] << "\n\n";
	for (size_t i = 0; i < functions.size(); ++i)
	{
		out << functions[i].header << " {\n";
		for (size_t j = 0; j < functions[i].slots.size(); ++j)
			out << functions[i].slots[j] << "\n";
		if (!functions[i].slots.empty())
			out << "\n";
		for (size_t j = 0; j < functions[i].blocks.size(); ++j)
		{
			if (j != 0)
				out << "\n";
			out << "  block ^" << functions[i].blocks[j].name << ":\n";
			for (size_t k = 0; k < functions[i].blocks[j].instrs.size(); ++k)
				out << functions[i].blocks[j].instrs[k] << "\n";
		}
		out << "}";
		if (i + 1 != functions.size())
			out << "\n\n";
		else
			out << "\n";
	}
	if ((needs_empty_init_function || !init_actions.empty()) &&
	    defined_functions.find("__cppgm_init") == defined_functions.end())
	{
		if (!functions.empty())
			out << "\n";
		out << "function @__cppgm_init() -> void [role=init, binding=internal] {\n";
		out << "  block ^entry:\n";
		int temp = 0;
		for (size_t i = 0; i < init_actions.size(); ++i)
		{
			++temp;
			string tmp = "%t" + to_string(temp);
			if (init_actions[i].kind == "load_ptr")
				out << "    " << tmp << " = load ptr @"
				    << init_actions[i].symbol << "\n";
			else
				out << "    " << tmp << " = addr @"
				    << init_actions[i].symbol << "\n";
			out << "    store ptr " << tmp << ", @"
			    << init_actions[i].target << "\n";
		}
		out << "    return void\n";
		out << "}\n";
	}
}


}  // namespace internal

void emit_lowir(const vector<string>& srcfiles,
                const string& outfile,
                const Options& options)
{
	internal::ProgramLowerer program;
	vector<unique_ptr<pa12::internal::Parser> > parsers;
	for (size_t i = 0; i < srcfiles.size(); ++i)
	{
		pa12::Options pa12_options;
		pa12_options.preprocess = options.preprocess;
		unique_ptr<pa12::internal::Parser> parser(
			new pa12::internal::Parser(srcfiles[i], pa12_options));
		parser->parse_translation_unit();
		const vector<internal::Node>& extra = parser->extra_lowir_nodes();
		set<const pa11::Binding*> direct_calls;
		internal::collect_direct_calls(parser->root(), direct_calls);
		for (size_t j = 0; j < extra.size(); ++j)
			program.register_inline_definition(extra[j]);
		for (size_t j = 0; j < extra.size(); ++j)
		{
			if (!internal::early_hidden_friend_definition(extra[j], direct_calls))
				continue;
			program.demand_inline_function(extra[j].binding);
			program.emit_pending_inline_definitions();
		}
		program.collect_translation_unit(parser->root());
		for (size_t j = 0; j < extra.size(); ++j)
		{
			if (!internal::generated_copy_move_constructor_node(extra[j]))
				continue;
			set<const pa11::Binding*> generated_calls;
			internal::collect_direct_calls(extra[j], generated_calls);
			for (set<const pa11::Binding*>::const_iterator it =
			     generated_calls.begin();
			     it != generated_calls.end();
			     ++it)
				program.demand_inline_function(*it);
		}
		program.emit_pending_inline_definitions();
		program.emit_pending_synthetic_assignment_functions();
		parsers.push_back(std::move(parser));
	}
	program.emit_global_lifecycle_functions();
	program.write(outfile);
}


}  // namespace pa14
