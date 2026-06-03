#include "lowir2cy86.h"

#include <algorithm>
#include <set>
#include <stdexcept>

using namespace std;

namespace lowir2cy86 {
namespace {

size_t align_up(size_t value, size_t align)
{
	if (align <= 1)
		return value;
	const size_t rem = value % align;
	return rem == 0 ? value : value + (align - rem);
}

bool one_of(const string& value, const vector<string>& values)
{
	return find(values.begin(), values.end(), value) != values.end();
}

void require_unique_insert(set<string>& seen, const string& name)
{
	if (!seen.insert(name).second)
		throw runtime_error("duplicate LowIR name");
}

bool is_terminator(InstrKind kind)
{
	return kind == InstrKind::Jump || kind == InstrKind::Branch ||
	       kind == InstrKind::Switch || kind == InstrKind::Return ||
	       kind == InstrKind::Throw || kind == InstrKind::Resume;
}

void require_block(const set<string>& blocks, const string& target);
void validate_instruction_operands(Function& fn,
                                   const Program& program,
                                   const Instruction& ins,
                                   const set<string>& blocks);
void validate_block(Function& fn,
                    const Program& program,
                    const Block& block,
                    const set<string>& blocks);
size_t allocate_stack_slot(size_t& offset, const Type& type);
void assign_singleton(string& slot, const string& value);
void require_role_owner(map<string, string>& owners,
                        const string& role,
                        const string& name);

bool is_function_role(const string& role)
{
	return one_of(role, {"entry", "init", "fini", "eh_unhandled",
	                    "eh_allocate_exception", "eh_begin_catch",
	                    "eh_call_unexpected", "eh_current_exception_type",
	                    "eh_end_catch", "eh_rethrow", "eh_throw",
	                    "eh_personality", "eh_resume"});
}

bool is_global_role(const string& role)
{
	return one_of(role, {"eh_top", "eh_value", "eh_type"});
}

void validate_function_metadata(const Metadata& metadata)
{
	for (size_t i = 0; i < metadata.size(); ++i)
	{
		const string& key = metadata[i].key;
		const string& value = metadata[i].value;
		if (key == "role")
			continue;
		if (key == "linkage" && one_of(value, {"c", "cpp"}))
			continue;
		if (key == "binding" && one_of(value, {"internal", "strong", "weak"}))
			continue;
		if (key == "object" || key == "tls_for")
			continue;
		if ((key == "keep_alias" || key == "prefer_local") &&
		    one_of(value, {"yes", "no"}))
			continue;
		if (key == "arity" &&
		    one_of(value, {"fixed", "variadic", "prototype_relaxed"}))
			continue;
		if (key == "effects" &&
		    one_of(value, {"readnone", "readonly", "readwrite"}))
			continue;
		if (key == "unwind" && one_of(value, {"may", "no"}))
			continue;
		if (key == "return" && one_of(value, {"returns", "noreturn"}))
			continue;
		throw runtime_error("invalid function metadata");
	}
}

void validate_call_signature_metadata(const Metadata& metadata)
{
	for (size_t i = 0; i < metadata.size(); ++i)
	{
		const string& key = metadata[i].key;
		const string& value = metadata[i].value;
		if (key == "arity" &&
		    one_of(value, {"fixed", "variadic", "prototype_relaxed"}))
			continue;
		if (key == "effects" &&
		    one_of(value, {"readnone", "readonly", "readwrite"}))
			continue;
		if (key == "unwind" && one_of(value, {"may", "no"}))
			continue;
		if (key == "return" && one_of(value, {"returns", "noreturn"}))
			continue;
		throw runtime_error("invalid call-signature metadata");
	}
}

void validate_global_metadata(const Metadata& metadata)
{
	for (size_t i = 0; i < metadata.size(); ++i)
	{
		const string& key = metadata[i].key;
		const string& value = metadata[i].value;
		if (key == "role")
			continue;
		if (key == "linkage" && one_of(value, {"c", "cpp"}))
			continue;
		if (key == "binding" && one_of(value, {"internal", "strong", "weak"}))
			continue;
		if (key == "object")
			continue;
		if (key == "storage" && one_of(value, {"readonly", "thread_local"}))
			continue;
		throw runtime_error("invalid global metadata");
	}
}

void validate_parameter_metadata(const Parameter& param, const Type& ret, size_t index)
{
	bool has_access = false;
	bool has_capture = false;
	for (size_t i = 0; i < param.metadata.size(); ++i)
	{
		const string& key = param.metadata[i].key;
		const string& value = param.metadata[i].value;
		if (key == "pass")
		{
			if (!one_of(value, {"direct", "indirect_result", "by_address",
			                   "reference", "decay"}))
				throw runtime_error("invalid pass metadata");
			if (value != "direct" && !is_ptr_type(param.type))
				throw runtime_error("non-pointer pass metadata");
			if (value == "indirect_result" && (index != 0 || !is_void_type(ret)))
				throw runtime_error("invalid indirect result metadata");
		}
		else if (key == "capture")
		{
			has_capture = true;
			if (!one_of(value, {"nocapture", "maycapture"}) || !is_ptr_type(param.type))
				throw runtime_error("invalid capture metadata");
		}
		else if (key == "access")
		{
			has_access = true;
			if (!one_of(value, {"none", "read", "write", "readwrite"}) ||
			    !is_ptr_type(param.type))
				throw runtime_error("invalid access metadata");
		}
		else if (key == "alias")
		{
			if (value != "noalias" || !is_ptr_type(param.type))
				throw runtime_error("invalid alias metadata");
		}
		else
			throw runtime_error("unknown parameter metadata");
	}
	if (has_access && !has_capture)
		throw runtime_error("access metadata requires explicit capture");
}

Type value_type(const Function& fn, const Program& program, const Value& value)
{
	if (value.kind == ValueKind::Temp)
	{
		map<string, Type>::const_iterator pit = fn.param_types.find(value.text);
		if (pit != fn.param_types.end())
			return pit->second;
		map<string, Type>::const_iterator it = fn.temp_types.find(value.text);
		if (it == fn.temp_types.end())
			throw runtime_error("undefined temporary");
		return it->second;
	}
	if (value.kind == ValueKind::Slot)
	{
		map<string, Type>::const_iterator it = fn.slot_types.find(value.text);
		if (it == fn.slot_types.end())
			throw runtime_error("undefined slot");
		return it->second;
	}
	if (value.kind == ValueKind::Global)
	{
		map<string, size_t>::const_iterator it = program.global_by_name.find(value.text);
		if (it == program.global_by_name.end() &&
		    program.function_by_name.find(value.text) != program.function_by_name.end())
			return parse_type_text("ptr");
		if (it == program.global_by_name.end())
			throw runtime_error("undefined global");
		const Global& global = program.globals[it->second];
		return global.has_type ? global.type : parse_type_text("ptr");
	}
	if (value.kind == ValueKind::Function)
		return parse_type_text("ptr");
	return Type();
}

void validate_symbol_value(const Function& fn, const Program& program, const Value& value)
{
	if (value.kind == ValueKind::Temp || value.kind == ValueKind::Slot ||
	    value.kind == ValueKind::Global)
		(void)value_type(fn, program, value);
}

void validate_addressable(const Function& fn, const Program& program, const Value& value)
{
	if (value.kind == ValueKind::Slot || value.kind == ValueKind::Global)
	{
		if (value.kind == ValueKind::Global &&
		    program.global_by_name.find(value.text) == program.global_by_name.end() &&
		    program.function_by_name.find(value.text) == program.function_by_name.end())
			throw runtime_error("undefined addressable");
		if (value.kind != ValueKind::Global ||
		    program.global_by_name.find(value.text) != program.global_by_name.end())
			validate_symbol_value(fn, program, value);
	}
	else
		throw runtime_error("invalid addressable");
}

void validate_projection(const string& projection)
{
	if (projection.empty())
		return;
	if (!one_of(projection, {"array_element", "field", "base_subobject",
	                        "reference_field"}))
		throw runtime_error("invalid index projection");
}

void validate_conversion(const Instruction& ins)
{
	const bool dst_int = is_integer_type(ins.type);
	const bool src_int = is_integer_type(ins.src_type);
	const bool dst_float = is_float_type(ins.type);
	const bool src_float = is_float_type(ins.src_type);
	if (ins.op == "sext" || ins.op == "zext")
	{
		if (!dst_int || !src_int || ins.src_type.bits >= ins.type.bits)
			throw runtime_error("invalid integer extension");
	}
	else if (ins.op == "trunc")
	{
		if (!dst_int || !src_int || ins.src_type.bits <= ins.type.bits)
			throw runtime_error("invalid integer truncation");
	}
	else if (ins.op == "sitofp" || ins.op == "uitofp")
	{
		if (!dst_float || !src_int)
			throw runtime_error("invalid int-float conversion");
	}
	else if (ins.op == "fptosi" || ins.op == "fptoui")
	{
		if (!dst_int || !src_float)
			throw runtime_error("invalid float-int conversion");
	}
	else if (ins.op == "fpext")
	{
		if (!dst_float || !src_float || ins.src_type.bits >= ins.type.bits)
			throw runtime_error("invalid float extension");
	}
	else if (ins.op == "fptrunc")
	{
		if (!dst_float || !src_float || ins.src_type.bits <= ins.type.bits)
			throw runtime_error("invalid float truncation");
	}
	else
		throw runtime_error("unknown conversion");
}

Type instruction_result_type(const Instruction& ins)
{
	if (ins.kind == InstrKind::Addr || ins.kind == InstrKind::Index)
		return parse_type_text("ptr");
	if (ins.kind == InstrKind::Cmp)
		return ins.type;
	if (ins.kind == InstrKind::Exception)
		return ins.type;
	if (ins.kind == InstrKind::Call || ins.kind == InstrKind::Convert ||
	    ins.kind == InstrKind::Const || ins.kind == InstrKind::Copy ||
	    ins.kind == InstrKind::Load || ins.kind == InstrKind::AtomicLoad ||
	    ins.kind == InstrKind::AtomicExchange ||
	    ins.kind == InstrKind::AtomicCompareExchange ||
	    ins.kind == InstrKind::AtomicAddFetch || ins.kind == InstrKind::Unary ||
	    ins.kind == InstrKind::Binary)
		return ins.kind == InstrKind::AtomicCompareExchange ? parse_type_text("i64")
		                                                    : ins.type;
	return Type();
}

void reject_unsupported_f80_surface(const Instruction& ins)
{
	if (ins.kind == InstrKind::Convert)
		return;
	if (is_f80_type(ins.type) || is_f80_type(ins.src_type))
		throw runtime_error("unsupported f80 surface");
}

void validate_call(const Function& fn, const Program& program, const Instruction& ins)
{
	if (ins.a.kind != ValueKind::Function && !ins.signature.present)
		throw runtime_error("indirect call missing signature");
	if (ins.a.kind == ValueKind::Function &&
	    program.function_by_name.find(ins.a.text) == program.function_by_name.end())
		throw runtime_error("undefined function");
	for (size_t i = 0; i < ins.args.size(); ++i)
		validate_symbol_value(fn, program, ins.args[i]);
	for (size_t i = 0; i < ins.signature.params.size(); ++i)
		validate_parameter_metadata(ins.signature.params[i], ins.signature.ret, i);
	validate_call_signature_metadata(ins.signature.metadata);
}

void validate_pointer_or_slot_destination(const Function& fn,
                                          const Program& program,
                                          const Value& value,
                                          const Span& span,
                                          const string& context)
{
	const Type type = value_type(fn, program, value);
	if (is_ptr_type(type))
		return;
	if (value.kind == ValueKind::Slot && stack_storage_size(type) >= span.bytes)
		return;
	throw runtime_error(context + " must be pointer-valued or addressable slot");
}

void validate_copyobj(const Function& fn,
                      const Program& program,
                      const Instruction& ins)
{
	const Type src = value_type(fn, program, ins.a);
	const bool direct_object =
	    is_obj_type(src) && src.obj_size == ins.span.bytes &&
	    src.obj_align == ins.span.align;
	if (!is_ptr_type(src) && !direct_object)
		throw runtime_error("copyobj source must be pointer or matching object");
	validate_pointer_or_slot_destination(fn, program, ins.b, ins.span,
	                                     "copyobj destination");
}

void validate_zeroinit(const Function& fn,
                       const Program& program,
                       const Instruction& ins)
{
	validate_pointer_or_slot_destination(fn, program, ins.a, ins.span,
	                                     "zeroinit destination");
}

void validate_instruction(Function& fn,
                          const Program& program,
                          const Instruction& ins,
                          const set<string>& blocks)
{
	reject_unsupported_f80_surface(ins);
	if (ins.kind == InstrKind::Addr)
		validate_addressable(fn, program, ins.a);
	else if (ins.kind == InstrKind::Jump || ins.kind == InstrKind::EhTry ||
	         ins.kind == InstrKind::EhCleanup)
		require_block(blocks, ins.target);
	else
		validate_instruction_operands(fn, program, ins, blocks);
	if (ins.has_dest)
	{
		if (fn.temp_types.find(ins.dest) != fn.temp_types.end() ||
		    fn.param_types.find(ins.dest) != fn.param_types.end())
			throw runtime_error("duplicate temporary");
		fn.temp_types[ins.dest] = instruction_result_type(ins);
		fn.temp_order.push_back(ins.dest);
	}
}

void require_block(const set<string>& blocks, const string& target)
{
	if (blocks.find(target) == blocks.end())
		throw runtime_error("undefined block");
}

void validate_instruction_operands(Function& fn,
                                   const Program& program,
                                   const Instruction& ins,
                                   const set<string>& blocks)
{
	switch (ins.kind)
	{
	case InstrKind::Const:
		break;
	case InstrKind::Copy:
	case InstrKind::Load:
	case InstrKind::AtomicLoad:
	case InstrKind::Unary:
	case InstrKind::Exception:
	case InstrKind::Throw:
	case InstrKind::Return:
		validate_symbol_value(fn, program, ins.a);
		break;
	case InstrKind::Store:
	case InstrKind::AtomicStore:
	case InstrKind::Index:
	case InstrKind::Binary:
	case InstrKind::Cmp:
	case InstrKind::AtomicExchange:
	case InstrKind::AtomicAddFetch:
		validate_symbol_value(fn, program, ins.a);
		validate_symbol_value(fn, program, ins.b);
		break;
	case InstrKind::AtomicCompareExchange:
		validate_symbol_value(fn, program, ins.a);
		validate_symbol_value(fn, program, ins.b);
		validate_symbol_value(fn, program, ins.c);
		break;
	case InstrKind::Convert:
		validate_symbol_value(fn, program, ins.a);
		validate_conversion(ins);
		fn.needs_convert_scratch = true;
		break;
	case InstrKind::Call:
		validate_call(fn, program, ins);
		break;
	case InstrKind::Branch:
		validate_symbol_value(fn, program, ins.a);
		require_block(blocks, ins.target);
		require_block(blocks, ins.target_false);
		break;
	case InstrKind::Switch:
		validate_symbol_value(fn, program, ins.a);
		require_block(blocks, ins.target);
		for (size_t i = 0; i < ins.switch_cases.size(); ++i)
		{
			validate_symbol_value(fn, program, ins.switch_cases[i].value);
			require_block(blocks, ins.switch_cases[i].target);
		}
		break;
	case InstrKind::CopyObj:
		validate_copyobj(fn, program, ins);
		break;
	case InstrKind::ZeroInit:
		validate_zeroinit(fn, program, ins);
		break;
	case InstrKind::AtomicThreadFence:
	case InstrKind::AtomicSignalFence:
	case InstrKind::EhEnd:
	case InstrKind::Resume:
		break;
	case InstrKind::Addr:
	case InstrKind::Jump:
	case InstrKind::EhTry:
	case InstrKind::EhCleanup:
		break;
	}
	if (ins.kind == InstrKind::Unary && ins.op == "decay" && !is_ptr_type(ins.type))
		throw runtime_error("decay requires pointer");
	if (ins.kind == InstrKind::Index)
		validate_projection(ins.op);
}

void collect_function_locals(Function& fn)
{
	set<string> seen;
	for (size_t i = 0; i < fn.params.size(); ++i)
	{
		require_unique_insert(seen, fn.params[i].name);
		validate_parameter_metadata(fn.params[i], fn.ret, i);
		fn.param_types[fn.params[i].name] = fn.params[i].type;
		if (is_f80_type(fn.params[i].type))
			throw runtime_error("unsupported f80 parameter");
	}
	seen.clear();
	for (size_t i = 0; i < fn.slots.size(); ++i)
	{
		require_unique_insert(seen, fn.slots[i].name);
		fn.slot_types[fn.slots[i].name] = fn.slots[i].type;
	}
}

void validate_function(Function& fn, const Program& program)
{
	validate_function_metadata(fn.metadata);
	if (is_f80_type(fn.ret))
		throw runtime_error("unsupported f80 return");
	collect_function_locals(fn);
	if (fn.declaration)
		return;
	set<string> block_names;
	for (size_t i = 0; i < fn.blocks.size(); ++i)
		require_unique_insert(block_names, fn.blocks[i].name);
	if (fn.blocks.empty())
		throw runtime_error("function without blocks");
	for (size_t i = 0; i < fn.blocks.size(); ++i)
		validate_block(fn, program, fn.blocks[i], block_names);
}

void validate_block(Function& fn,
                    const Program& program,
                    const Block& block,
                    const set<string>& blocks)
{
	bool terminated = false;
	for (size_t i = 0; i < block.instructions.size(); ++i)
	{
		if (terminated)
			throw runtime_error("instruction after terminator");
		validate_instruction(fn, program, block.instructions[i], blocks);
		terminated = is_terminator(block.instructions[i].kind);
		if (block.instructions[i].kind == InstrKind::EhTry ||
		    block.instructions[i].kind == InstrKind::EhCleanup ||
		    block.instructions[i].kind == InstrKind::Throw ||
		    block.instructions[i].kind == InstrKind::Exception ||
		    block.instructions[i].kind == InstrKind::Resume ||
		    block.instructions[i].kind == InstrKind::EhEnd)
			fn.needs_convert_scratch = fn.needs_convert_scratch;
	}
	if (!terminated)
		throw runtime_error("block missing terminator");
}

void assign_layout(Function& fn)
{
	size_t offset = 0;
	if (is_obj_type(fn.ret) && !fn.declaration)
		fn.hidden_result_offset = allocate_stack_slot(offset, parse_type_text("ptr"));
	for (size_t i = 0; i < fn.params.size(); ++i)
	{
		fn.params[i].offset = allocate_stack_slot(offset, fn.params[i].type);
		fn.param_offsets[fn.params[i].name] = fn.params[i].offset;
	}
	for (size_t i = 0; i < fn.slots.size(); ++i)
	{
		fn.slots[i].offset = allocate_stack_slot(offset, fn.slots[i].type);
		fn.slot_offsets[fn.slots[i].name] = fn.slots[i].offset;
	}
	for (size_t i = 0; i < fn.temp_order.size(); ++i)
	{
		const string& name = fn.temp_order[i];
		fn.temp_offsets[name] = allocate_stack_slot(offset, fn.temp_types[name]);
	}
	if (fn.needs_convert_scratch)
	{
		fn.convert_scratch_offset = offset + 16;
		offset += 64;
	}
	fn.stack_size = offset;
}

size_t allocate_stack_slot(size_t& offset, const Type& type)
{
	const size_t align = is_obj_type(type) ? type.align : 8;
	offset = align_up(offset, align);
	offset += stack_storage_size(type);
	return offset;
}

void collect_top_level(Program& program)
{
	set<string> symbols;
	for (size_t i = 0; i < program.globals.size(); ++i)
	{
		require_unique_insert(symbols, program.globals[i].name);
		program.global_by_name[program.globals[i].name] = i;
		validate_global_metadata(program.globals[i].metadata);
		if (program.globals[i].has_type && is_f80_type(program.globals[i].type))
			throw runtime_error("unsupported f80 global");
	}
	for (size_t i = 0; i < program.functions.size(); ++i)
	{
		require_unique_insert(symbols, program.functions[i].name);
		program.function_by_name[program.functions[i].name] = i;
	}
	set<string> aliases;
	for (size_t i = 0; i < program.aliases.size(); ++i)
	{
		require_unique_insert(aliases, program.aliases[i].object);
		if (symbols.find(program.aliases[i].target) == symbols.end())
			throw runtime_error("undefined alias target");
	}
}

void resolve_roles(Program& program)
{
	map<string, string> role_owners;
	for (size_t i = 0; i < program.globals.size(); ++i)
	{
		const string role = metadata_value(program.globals[i].metadata, "role");
		if (role.empty())
			continue;
		if (!is_global_role(role))
			throw runtime_error("invalid global role");
		require_role_owner(role_owners, role, program.globals[i].name);
	}
	for (size_t i = 0; i < program.functions.size(); ++i)
	{
		const string role = metadata_value(program.functions[i].metadata, "role");
		if (role.empty())
			continue;
		if (!is_function_role(role))
			throw runtime_error("invalid function role");
		require_role_owner(role_owners, role, program.functions[i].name);
		if (role == "entry")
			assign_singleton(program.entry_function, program.functions[i].name);
		else if (role == "init")
			assign_singleton(program.init_function, program.functions[i].name);
		else if (role == "fini")
			assign_singleton(program.fini_function, program.functions[i].name);
	}
	if (program.entry_function.empty() &&
	    program.function_by_name.find("@main") != program.function_by_name.end())
		program.entry_function = "@main";
	if (program.init_function.empty() &&
	    program.function_by_name.find("@__cppgm_init") != program.function_by_name.end())
		program.init_function = "@__cppgm_init";
	if (program.fini_function.empty() &&
	    program.function_by_name.find("@__cppgm_fini") != program.function_by_name.end())
		program.fini_function = "@__cppgm_fini";
	if (program.entry_function.empty())
		throw runtime_error("missing entry function");
}

void assign_singleton(string& slot, const string& value)
{
	if (!slot.empty())
		throw runtime_error("duplicate singleton role");
	slot = value;
}

void require_role_owner(map<string, string>& owners,
                        const string& role,
                        const string& name)
{
	if (!owners.insert(make_pair(role, name)).second)
		throw runtime_error("duplicate singleton role");
}

void validate_tls_wrappers(const Program& program)
{
	set<string> wrapped;
	for (size_t i = 0; i < program.functions.size(); ++i)
	{
		const string target = metadata_value(program.functions[i].metadata, "tls_for");
		if (target.empty())
			continue;
		map<string, size_t>::const_iterator it = program.global_by_name.find(target);
		if (it == program.global_by_name.end())
			throw runtime_error("unknown tls target");
		if (metadata_value(program.globals[it->second].metadata, "storage") !=
		    "thread_local")
			throw runtime_error("tls target is not thread local");
		require_unique_insert(wrapped, target);
	}
}

bool function_uses_eh(const Function& fn)
{
	for (size_t i = 0; i < fn.blocks.size(); ++i)
	{
		for (size_t j = 0; j < fn.blocks[i].instructions.size(); ++j)
		{
			const InstrKind kind = fn.blocks[i].instructions[j].kind;
			if (kind == InstrKind::EhTry || kind == InstrKind::EhCleanup ||
			    kind == InstrKind::EhEnd || kind == InstrKind::Throw ||
			    kind == InstrKind::Exception || kind == InstrKind::Resume)
				return true;
		}
	}
	return false;
}

}  // namespace

void validate_and_layout(Program& program)
{
	collect_top_level(program);
	resolve_roles(program);
	validate_tls_wrappers(program);
	for (size_t i = 0; i < program.functions.size(); ++i)
	{
		validate_function(program.functions[i], program);
		if (!program.functions[i].declaration)
			assign_layout(program.functions[i]);
		program.needs_eh_runtime =
		    program.needs_eh_runtime || function_uses_eh(program.functions[i]);
	}
}

}  // namespace lowir2cy86
