#include "pa14_lowir_internal.h"

#include <sstream>

namespace pa14 {
namespace internal {

namespace {

void ensure_operator_delete_declaration(ProgramLowerer& program)
{
	if (program.declared_functions.find("operator_delete") !=
	        program.declared_functions.end() ||
	    program.defined_functions.find("operator_delete") !=
	        program.defined_functions.end())
		return;
	program.declared_functions.insert("operator_delete");
	program.declares.push_back(
		"declare function @operator_delete(%arg0 : ptr) -> void "
		"[unwind=no, binding=strong, object=" +
		string(program.native_lowering
		       ? "_ZdlPv" : "cppgm_builtin_operator_delete") + "]");
}

string deleting_destructor_object_symbol(const Binding* dtor)
{
	string object = !dtor->function_specialization_symbol.empty()
		? dtor->function_specialization_symbol : global_object_symbol(dtor);
	if (object.empty() &&
	    dtor->aliased_binding != NULL &&
	    !dtor->aliased_binding->function_specialization_symbol.empty())
		object = dtor->aliased_binding->function_specialization_symbol;
	size_t dtor_entry = object.rfind("D1E");
	if (dtor_entry != string::npos)
		object.replace(dtor_entry, 3, "D0E");
	return object;
}

const Node* deleting_destructor_inline_node(ProgramLowerer& program,
                                            const Binding* dtor)
{
	map<const Binding*, const Node*>::const_iterator found =
		program.inline_definitions.find(dtor);
	if (found != program.inline_definitions.end())
		return found->second;
	if (dtor->aliased_binding == NULL)
		return NULL;
	found = program.inline_definitions.find(dtor->aliased_binding);
	return found != program.inline_definitions.end() ? found->second : NULL;
}

void emit_deleting_entry_vptr_stores(Block& block, TypePtr record, int& temp)
{
	block.instrs.push_back("    store ptr %this, $this");
	string self = "%t" + to_string(temp++);
	block.instrs.push_back("    " + self + " = load ptr $this");
	string vt = "%t" + to_string(temp++);
	block.instrs.push_back("    " + vt + " = addr @" +
	                       vtable_symbol_for_record(record));
	string addr_point = "%t" + to_string(temp++);
	block.instrs.push_back("    " + addr_point + " = index i8 " + vt + ", " +
	                       to_string(vtable_address_point_offset(record)));
	block.instrs.push_back("    store ptr " + addr_point + ", " + self);
	TypePtr bare = pa11::strip_cv(record);
	vector<pair<TypePtr, uint64_t> > views = vtt_ordered_vtable_views(bare);
	set<uint64_t> stored_view_offsets;
	for (size_t i = 0; i < views.size(); ++i)
	{
		if (!stored_view_offsets.insert(views[i].second).second)
			continue;
		string reload = "%t" + to_string(temp++);
		block.instrs.push_back("    " + reload + " = load ptr $this");
		string base_addr = "%t" + to_string(temp++);
		block.instrs.push_back(
			"    " + base_addr +
			" = index i8 [projection=base_subobject] " +
			reload + ", " + to_string(views[i].second));
		string view = "%t" + to_string(temp++);
		block.instrs.push_back(
			"    " + view + " = addr @" +
			vtable_view_symbol_for_record(bare, views[i].first, views[i].second));
		if (vtable_address_point_offset(bare) != 16)
		{
			string view_addr = "%t" + to_string(temp++);
			block.instrs.push_back("    " + view_addr + " = index i8 " +
			                       view + ", " +
			                       to_string(vtable_address_point_offset(bare)));
			view = view_addr;
		}
		block.instrs.push_back("    store ptr " + view + ", " + base_addr);
	}
}

void append_base_vtt_argument(ProgramLowerer& program,
                              Block& block,
                              TypePtr record,
                              TypePtr base,
                              vector<string>& args,
                              int& temp)
{
	if (program.native_lowering ||
	    !base->is_polymorphic ||
	    !record_uses_virtual_base_vtt(base))
		return;
	size_t vtt_slot = construction_vtt_slot_for_direct_base(record, base);
	if (vtt_slot == static_cast<size_t>(-1))
		return;
	string vtt_base = "%t" + to_string(temp++);
	block.instrs.push_back("    " + vtt_base + " = addr @" +
	                       vtt_symbol_for_record(record));
	string vtt_arg = vtt_base;
	if (vtt_slot != 0)
	{
		vtt_arg = "%t" + to_string(temp++);
		block.instrs.push_back("    " + vtt_arg + " = index i8 " +
		                       vtt_base + ", " + to_string(vtt_slot * 8));
	}
	args.push_back(vtt_arg);
}

void append_base_hidden_virtual_arguments(Block& block,
                                          TypePtr record,
                                          TypePtr base,
                                          vector<string>& args,
                                          int& temp)
{
	vector<TypePtr> vbases = hidden_virtual_bases_for_record(base);
	for (size_t v = 0; v < vbases.size(); ++v)
	{
		string hidden;
		if (record_has_base_subobject(record, vbases[v]))
		{
			string this_ptr = "%t" + to_string(temp++);
			block.instrs.push_back("    " + this_ptr + " = load ptr $this");
			uint64_t offset = base_subobject_offset(record, vbases[v]);
			if (offset == 0)
				hidden = this_ptr;
			else
			{
				hidden = "%t" + to_string(temp++);
				block.instrs.push_back("    " + hidden + " = index i8 " +
				                       this_ptr + ", " + to_string(offset));
			}
		}
		args.push_back(hidden.empty() ? string("0") : hidden);
	}
}

void emit_base_destructor_call(ProgramLowerer& program,
                               Block& block,
                               TypePtr record,
                               TypePtr base,
                               int& temp)
{
	Binding* base_dtor = find_destructor(base);
	if (base_dtor == NULL || !base_dtor->is_virtual)
		return;
	program.demand_function_declaration(base_dtor);
	string base_callee = program.destructor_symbol_for(base_dtor, true);
	program.demand_inline_function(base_dtor, false);
	string reload = "%t" + to_string(temp++);
	block.instrs.push_back("    " + reload + " = load ptr $this");
	string base_addr = "%t" + to_string(temp++);
	block.instrs.push_back(
		"    " + base_addr +
		" = index i8 [projection=base_subobject] " +
		reload + ", " + to_string(base_subobject_offset(record, base)));
	vector<string> args;
	args.push_back(base_addr);
	append_base_vtt_argument(program, block, record, base, args, temp);
	if (!program.native_lowering && base->is_polymorphic &&
	    record_uses_virtual_base_vtt(base))
		append_base_hidden_virtual_arguments(block, record, base, args, temp);
	ostringstream call;
	call << "    call void @" << base_callee << "(";
	for (size_t a = 0; a < args.size(); ++a)
	{
		if (a != 0)
			call << ", ";
		call << args[a];
	}
	call << ")";
	block.instrs.push_back(call.str());
}

void emit_base_destructor_calls(ProgramLowerer& program,
                                Block& block,
                                TypePtr record,
                                int& temp)
{
	TypePtr bare = pa11::strip_cv(record);
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
		emit_base_destructor_call(program, block, record, base, temp);
	}
}

}  // namespace

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
	ensure_operator_delete_declaration(*this);
	string name = symbol_for(dtor) + "__deleting_entry";
	if (defined_functions.find(name) != defined_functions.end())
		return;
	defined_functions.insert(name);
	FunctionOut out;
	out.binding = dtor;
	out.name = name;
	out.header = "function @" + name + "(%this : ptr) -> void [binding=weak";
	string object = deleting_destructor_object_symbol(dtor);
	if (!object.empty())
		out.header += ", object=" + object;
	out.header += "]";
	const Node* inline_node = deleting_destructor_inline_node(*this, dtor);
	if (inline_node != NULL)
	{
		FunctionLowerer lowerer(*this, *inline_node);
		functions.push_back(
			lowerer.lower_deleting_destructor_entry(name, out.header));
		return;
	}
	out.slots.push_back("  slot $this : ptr");
	Block block("entry");
	int temp = 1;
	emit_deleting_entry_vptr_stores(block, record, temp);
	emit_base_destructor_calls(*this, block, record, temp);
	string del_arg = "%t" + to_string(temp++);
	block.instrs.push_back("    " + del_arg + " = load ptr $this");
	block.instrs.push_back("    call void @operator_delete(" + del_arg + ")");
	block.instrs.push_back("    return void");
	block.terminated = true;
	out.blocks.push_back(block);
	functions.push_back(out);
}

}  // namespace internal
}  // namespace pa14
