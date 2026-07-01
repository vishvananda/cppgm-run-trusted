#include "pa14_lowir_internal.h"

#include <sstream>
#include <utility>

namespace pa14 {
namespace internal {

void append_assignment_dependency_members(TypePtr record, vector<Binding*>& members);
uint64_t assignment_storage_copy_limit(TypePtr record);
uint64_t assignment_member_storage_end(Binding* member);

namespace {

void append_synthetic_copyobj(Block& block,
                              int& temp,
                              const string& self,
                              const string& other,
                              uint64_t offset,
                              uint64_t bytes,
                              uint64_t align)
{
	if (bytes == 0)
		return;
	if (offset == 0)
	{
		block.instrs.push_back("    copyobj " + to_string(bytes) + "x" +
		                       to_string(align) + " " + other + ", " + self);
		return;
	}
	string self_chunk = "%t" + to_string(temp++);
	string other_chunk = "%t" + to_string(temp++);
	block.instrs.push_back("    " + self_chunk + " = index i8 " + self +
	                       ", " + to_string(offset));
	block.instrs.push_back("    " + other_chunk + " = index i8 " + other +
	                       ", " + to_string(offset));
	block.instrs.push_back("    copyobj " + to_string(bytes) + "x1 " +
	                       other_chunk + ", " + self_chunk);
}

Binding* synthetic_constructor_member_ctor(ProgramLowerer& program,
                                           Binding* member,
                                           bool move)
{
	TypePtr field_type = pa11::strip_cv(member->type);
	if (field_type->kind != TypeKind::Record)
		return NULL;
	Binding* ctor = find_copy_move_constructor(field_type, move);
	if (ctor == NULL && move)
		ctor = find_copy_move_constructor(field_type, false);
	if (ctor != NULL)
		return ctor;
	if (!type_needs_destructor(field_type))
		return NULL;
	return program.demand_implicit_copy_constructor(field_type, move);
}

vector<pair<Binding*, Binding*> > synthetic_constructor_field_ops(
	ProgramLowerer& program,
	TypePtr record,
	bool move,
	uint64_t& prefix_size)
{
	vector<pair<Binding*, Binding*> > out;
	vector<Binding*> members;
	append_assignment_dependency_members(record, members);
	prefix_size = record->fields.empty() ? 0 : pa11::type_size(record);
	for (size_t i = 0; i < members.size(); ++i)
	{
		Binding* member = members[i];
		if (member == NULL)
			continue;
		Binding* ctor = synthetic_constructor_member_ctor(program,
		                                                  member,
		                                                  move);
		if (ctor == NULL)
			continue;
		if (out.empty())
			prefix_size = member->member_offset;
		out.push_back(make_pair(member, ctor));
	}
	return out;
}

void append_synthetic_constructor_call(ProgramLowerer& program,
                                       Block& block,
                                       int& temp,
                                       Binding* field,
                                       Binding* ctor)
{
	program.demand_function_declaration(ctor);
	if (ctor->is_inline_definition ||
	    lowir_synthesizable_hosted_inline_body(ctor))
		program.demand_inline_function(ctor);
	string self_base = "%t" + to_string(temp++);
	string self_field = "%t" + to_string(temp++);
	string other_base = "%t" + to_string(temp++);
	string other_field = "%t" + to_string(temp++);
	block.instrs.push_back("    " + self_base + " = load ptr $this");
	block.instrs.push_back("    " + self_field + " = index i8 " +
	                       self_base + ", " + to_string(field->member_offset));
	block.instrs.push_back("    " + other_base + " = load ptr $other");
	block.instrs.push_back("    " + other_field + " = index i8 " +
	                       other_base + ", " + to_string(field->member_offset));
	block.instrs.push_back("    call void @" + program.symbol_for(ctor) +
	                       "(" + self_field + ", " + other_field + ")");
}

void append_synthetic_storage_constructor(ProgramLowerer& program,
                                          Block& block,
                                          TypePtr record,
                                          bool move)
{
	uint64_t prefix_size = 0;
	vector<pair<Binding*, Binding*> > field_ops =
		synthetic_constructor_field_ops(program, record, move, prefix_size);
	int temp = 1;
	string self = "%t" + to_string(temp++);
	string other = "%t" + to_string(temp++);
	block.instrs.push_back("    " + self + " = load ptr $this");
	block.instrs.push_back("    " + other + " = load ptr $other");
	append_synthetic_copyobj(block, temp, self, other, 0, prefix_size,
	                         pa11::type_align(record));
	uint64_t cursor = prefix_size;
	for (size_t i = 0; i < field_ops.size(); ++i)
	{
		Binding* field = field_ops[i].first;
		uint64_t offset = field->member_offset;
		append_synthetic_copyobj(block, temp, self, other, cursor,
		                         offset > cursor ? offset - cursor : 0, 1);
		append_synthetic_constructor_call(program, block, temp, field,
		                                  field_ops[i].second);
		uint64_t end = assignment_member_storage_end(field);
		if (end > cursor)
			cursor = end;
	}
	uint64_t total = field_ops.empty()
		? pa11::type_size(record)
		: assignment_storage_copy_limit(record);
	append_synthetic_copyobj(block, temp, self, other, cursor,
	                         total > cursor ? total - cursor : 0, 1);
	block.instrs.push_back("    return void");
}

}  // namespace

Binding* ProgramLowerer::demand_implicit_copy_constructor(TypePtr type, bool move)
{
	TypePtr record = pa11::strip_cv(type);
	if (record->kind != TypeKind::Record || record->scope == NULL)
		throw runtime_error("constructor target is not record");
	const void* key = record.get();
	map<const void*, Binding*>& cache =
		move ? implicit_move_constructors : implicit_copy_constructors;
	map<const void*, Binding*>::const_iterator found = cache.find(key);
	if (found != cache.end())
		return found->second;
	Binding* declared = find_copy_move_constructor(record, move);
	if (declared == NULL && move)
		declared = find_copy_move_constructor(record, false);
	if (declared != NULL)
	{
		cache[key] = declared;
		demand_function_declaration(declared);
		if (declared->is_inline_definition ||
		    lowir_synthesizable_hosted_inline_body(declared))
			demand_inline_function(declared);
		return declared;
	}
	if (!implicit_copy_constructor_synthesizable_record(record, move))
		return NULL;
	vector<TypePtr> params;
	params.push_back(pa11::make_pointer(record));
	params.push_back(move
		? pa11::make_rvalue_reference(record)
		: pa11::make_lvalue_reference(
			pa11::make_cv(record, pa11::CV_CONST)));
	TypePtr fn_type = pa11::make_function(pa11::make_fundamental(FT_VOID),
	                                      params,
	                                      false);
	synthetic_bindings.push_back(unique_ptr<Binding>(
		new Binding(BindingKind::Function, record->scope->name, record->scope)));
	Binding* binding = synthetic_bindings.back().get();
	binding->type = fn_type;
	binding->is_inline_definition = true;
	binding->is_generated_copy_move_constructor = true;
	binding->is_defaulted = true;
	cache[key] = binding;
	string name = symbol_for(binding);
	if (defined_functions.find(name) != defined_functions.end())
		return binding;
	defined_functions.insert(name);
	queue_synthetic_constructor_function(binding, record, move, name);
	return binding;
}

void ProgramLowerer::queue_synthetic_constructor_function(Binding* binding,
                                                          TypePtr record,
                                                          bool move,
                                                          const string& name)
{
	FunctionOut out;
	out.binding = binding;
	out.name = name;
	ostringstream header;
	header << "function @" << name
	       << "(%this : ptr, %other : ptr [pass=reference]) -> void";
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
	append_synthetic_storage_constructor(*this, block, record, move);
	block.terminated = true;
	out.blocks.push_back(block);
	pending_synthetic_constructor_functions.push_back(out);
}

}  // namespace internal
}  // namespace pa14
