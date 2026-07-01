#include "lowiropt.h"

#include <fstream>
#include <map>
#include <set>
#include <sstream>
#include <stdexcept>

using namespace std;

namespace lowiropt {
namespace {

using lowir2cy86::Block;
using lowir2cy86::CallSignature;
using lowir2cy86::Function;
using lowir2cy86::Global;
using lowir2cy86::GlobalDataItem;
using lowir2cy86::GlobalInit;
using lowir2cy86::InstrKind;
using lowir2cy86::Instruction;
using lowir2cy86::Metadata;
using lowir2cy86::ObjectAlias;
using lowir2cy86::Parameter;
using lowir2cy86::Program;
using lowir2cy86::Slot;
using lowir2cy86::Span;
using lowir2cy86::SwitchCase;
using lowir2cy86::Type;
using lowir2cy86::Value;
using lowir2cy86::ValueKind;

string metadata_text(const Metadata& metadata)
{
	if (metadata.empty())
		return "";
	ostringstream out;
	out << " [";
	for (size_t i = 0; i < metadata.size(); ++i)
	{
		if (i != 0)
			out << ", ";
		out << metadata[i].key << "=" << metadata[i].value;
	}
	out << "]";
	return out.str();
}

string type_text(const Type& type)
{
	return lowir2cy86::is_void_type(type) ? "void" : type.text;
}

string value_text(const Value& value)
{
	return value.text;
}

string span_text(const Span& span)
{
	if (span.align <= 1)
		return to_string(span.bytes);
	return to_string(span.bytes) + "x" + to_string(span.align);
}

string param_text(const Parameter& param)
{
	return param.name + " : " + type_text(param.type) + metadata_text(param.metadata);
}

string params_text(const vector<Parameter>& params)
{
	ostringstream out;
	for (size_t i = 0; i < params.size(); ++i)
	{
		if (i != 0)
			out << ", ";
		out << param_text(params[i]);
	}
	return out.str();
}

string call_signature_text(const CallSignature& sig)
{
	if (!sig.present)
		return "";
	return " as (" + params_text(sig.params) + ") -> " + type_text(sig.ret) +
	       metadata_text(sig.metadata);
}

string call_args_text(const vector<Value>& args)
{
	ostringstream out;
	for (size_t i = 0; i < args.size(); ++i)
	{
		if (i != 0)
			out << ", ";
		out << value_text(args[i]);
	}
	return out.str();
}

bool emit_atomic_instruction(ostringstream& out, const Instruction& ins)
{
	switch (ins.kind)
	{
	case InstrKind::AtomicLoad:
		out << "atomic_load " << type_text(ins.type) << " " << value_text(ins.a)
		    << ", " << ins.order_a;
		return true;
	case InstrKind::AtomicStore:
		out << "atomic_store " << type_text(ins.type) << " " << value_text(ins.a)
		    << ", " << value_text(ins.b) << ", " << ins.order_a;
		return true;
	case InstrKind::AtomicExchange:
		out << "atomic_exchange " << type_text(ins.type) << " " << value_text(ins.a)
		    << ", " << value_text(ins.b) << ", " << ins.order_a;
		return true;
	case InstrKind::AtomicCompareExchange:
		out << "atomic_compare_exchange " << type_text(ins.type) << " "
		    << value_text(ins.a) << ", " << value_text(ins.b) << ", "
		    << value_text(ins.c) << ", " << ins.order_a << ", "
		    << ins.order_b;
		return true;
	case InstrKind::AtomicAddFetch:
		out << "atomic_add_fetch " << type_text(ins.type) << " " << value_text(ins.a)
		    << ", " << value_text(ins.b) << ", " << ins.order_a;
		return true;
	case InstrKind::AtomicThreadFence:
		out << "atomic_thread_fence " << ins.order_a;
		return true;
	case InstrKind::AtomicSignalFence:
		out << "atomic_signal_fence " << ins.order_a;
		return true;
	default:
		return false;
	}
}

bool emit_memory_instruction(ostringstream& out, const Instruction& ins)
{
	switch (ins.kind)
	{
	case InstrKind::Load:
		out << "load " << type_text(ins.type) << " " << value_text(ins.a);
		return true;
	case InstrKind::Store:
		out << "store " << type_text(ins.type) << " " << value_text(ins.a)
		    << ", " << value_text(ins.b);
		return true;
	case InstrKind::Index:
		out << "index " << type_text(ins.type);
		if (!ins.op.empty() &&
		    !(ins.op == "array_element" && ins.type.text == "i8" &&
		      ins.b.kind == ValueKind::Literal))
			out << " [projection=" << ins.op << "]";
		out << " " << value_text(ins.a) << ", " << value_text(ins.b);
		return true;
	case InstrKind::CopyObj:
		out << "copyobj " << span_text(ins.span) << " " << value_text(ins.a)
		    << ", " << value_text(ins.b);
		return true;
	case InstrKind::ZeroInit:
		out << "zeroinit " << span_text(ins.span) << " " << value_text(ins.a);
		return true;
	case InstrKind::StackAlloc:
		out << "stackalloc " << ins.src_type.text << " " << value_text(ins.a);
		return true;
	default:
		return false;
	}
}

bool emit_value_instruction(ostringstream& out, const Instruction& ins)
{
	switch (ins.kind)
	{
	case InstrKind::Const:
		out << "const " << type_text(ins.type) << " " << value_text(ins.a);
		return true;
	case InstrKind::Copy:
		out << "copy " << type_text(ins.type) << " " << value_text(ins.a);
		return true;
	case InstrKind::Addr:
		out << "addr " << value_text(ins.a);
		return true;
	case InstrKind::Unary:
		out << "unary " << ins.op << " " << type_text(ins.type) << " "
		    << value_text(ins.a);
		return true;
	case InstrKind::Binary:
		out << "binary " << ins.op << " " << type_text(ins.type) << " "
		    << value_text(ins.a) << ", " << value_text(ins.b);
		return true;
	case InstrKind::Cmp:
		out << "cmp " << ins.op << " " << type_text(ins.type) << " "
		    << value_text(ins.a) << ", " << value_text(ins.b);
		return true;
	case InstrKind::Convert:
		out << "convert " << ins.op << " " << type_text(ins.type) << " "
		    << type_text(ins.src_type) << " " << value_text(ins.a);
		return true;
	case InstrKind::Call:
		out << "call " << type_text(ins.type) << " " << value_text(ins.a)
		    << "(" << call_args_text(ins.args) << ")"
		    << call_signature_text(ins.signature);
		return true;
	case InstrKind::VaStart:
		out << "va_start " << value_text(ins.a);
		return true;
	case InstrKind::VaArg:
		out << "va_arg " << type_text(ins.type) << " " << value_text(ins.a);
		return true;
	case InstrKind::VaEnd:
		out << "va_end " << value_text(ins.a);
		return true;
	default:
		return false;
	}
}

bool emit_eh_instruction(ostringstream& out, const Instruction& ins)
{
	switch (ins.kind)
	{
	case InstrKind::EhTry:
		out << "eh_try";
		if (!ins.target.empty())
			out << " " << ins.target;
		return true;
	case InstrKind::EhCleanup:
		out << "eh_cleanup";
		if (!ins.target.empty())
			out << " " << ins.target;
		return true;
	case InstrKind::EhCatch:
		out << "eh_catch " << value_text(ins.a);
		if (ins.order_a != 1)
			out << ", " << ins.order_a;
		return true;
	case InstrKind::EhCatchAll:
		out << "eh_catch_all";
		if (ins.order_a != 1)
			out << ", " << ins.order_a;
		return true;
	case InstrKind::EhFilter:
		out << "eh_filter";
		for (size_t i = 0; i < ins.args.size(); ++i)
			out << (i == 0 ? " " : ", ") << value_text(ins.args[i]);
		if (ins.order_a != 1)
			out << ", " << ins.order_a;
		return true;
	case InstrKind::EhEnd:
		out << "eh_end";
		return true;
	case InstrKind::Throw:
		out << "throw " << type_text(ins.type) << " " << value_text(ins.a);
		return true;
	case InstrKind::Exception:
		out << "exception " << type_text(ins.type);
		return true;
	case InstrKind::ExceptionSelector:
		out << "exception_selector " << type_text(ins.type);
		return true;
	case InstrKind::Resume:
		out << "resume";
		return true;
	default:
		return false;
	}
}

bool emit_control_instruction(ostringstream& out, const Instruction& ins)
{
	switch (ins.kind)
	{
	case InstrKind::Jump:
		out << "jump " << ins.target;
		return true;
	case InstrKind::Branch:
		out << "branch " << value_text(ins.a) << ", " << ins.target
		    << ", " << ins.target_false;
		return true;
	case InstrKind::Switch:
		out << "switch " << value_text(ins.a) << ", " << ins.target;
		for (size_t i = 0; i < ins.switch_cases.size(); ++i)
			out << ", " << value_text(ins.switch_cases[i].value) << ":"
			    << ins.switch_cases[i].target;
		return true;
	case InstrKind::Return:
		out << "return " << type_text(ins.type);
		if (!lowir2cy86::is_void_type(ins.type))
			out << " " << value_text(ins.a);
		return true;
	default:
		return false;
	}
}

string instruction_body_text(const Instruction& ins)
{
	ostringstream out;
	if (emit_value_instruction(out, ins) ||
	    emit_memory_instruction(out, ins) ||
	    emit_atomic_instruction(out, ins) ||
	    emit_eh_instruction(out, ins) ||
	    emit_control_instruction(out, ins))
		return out.str();
	throw runtime_error("unknown LowIR instruction kind");
	return out.str();
}

string instruction_text(const Instruction& ins)
{
	string out;
	if (ins.has_dest)
		out += ins.dest + " = ";
	out += instruction_body_text(ins);
	if (!ins.debug.empty())
		out += " " + ins.debug;
	return out;
}

void emit_global_init(ostream& out, const GlobalInit& init)
{
	if (init.kind == "zero")
		out << "zero";
	else if (init.kind == "addr")
	{
		out << "addr " << init.target;
		if (init.has_addend)
			out << (init.addend < 0 ? " - " : " + ")
			    << (init.addend < 0 ? -init.addend : init.addend);
	}
	else
		out << init.literal;
}

void emit_global_data_item(ostream& out, const GlobalDataItem& item)
{
	if (item.kind == "zero")
		out << "  zero " << item.zero_bytes << "\n";
	else if (item.kind == "addr")
	{
		out << "  ptr addr " << item.target;
		if (item.has_addend)
			out << (item.addend < 0 ? " - " : " + ")
			    << (item.addend < 0 ? -item.addend : item.addend);
		out << "\n";
	}
	else
		out << "  " << item.type.text << " " << item.literal << "\n";
}

void emit_global(ostream& out, const Global& global)
{
	if (global.declaration)
	{
		out << "declare global " << global.name;
		if (global.has_type)
			out << " : " << type_text(global.type);
		out << metadata_text(global.metadata) << "\n";
		return;
	}
	out << "global " << global.name;
	if (global.has_type)
	{
		out << " : " << type_text(global.type) << metadata_text(global.metadata)
		    << " = ";
		emit_global_init(out, global.init);
		out << "\n";
	}
	else
	{
		out << metadata_text(global.metadata) << " = {\n";
		for (size_t i = 0; i < global.data.size(); ++i)
			emit_global_data_item(out, global.data[i]);
		out << "}\n";
	}
}

void emit_function(ostream& out, const Function& fn)
{
	out << (fn.declaration ? "declare function " : "function ")
	    << fn.name << "(" << params_text(fn.params) << ") -> "
		    << type_text(fn.ret) << metadata_text(fn.metadata);
	if (!fn.debug.empty())
		out << " " << fn.debug;
	if (fn.declaration)
	{
		out << "\n";
		return;
	}
	out << " {\n";
	for (size_t i = 0; i < fn.slots.size(); ++i)
		out << "  slot " << fn.slots[i].name << " : "
		    << type_text(fn.slots[i].type) << "\n";
	if (!fn.slots.empty() && !fn.blocks.empty())
		out << "\n";
	for (size_t b = 0; b < fn.blocks.size(); ++b)
	{
		if (b != 0)
			out << "\n";
		out << "  block " << fn.blocks[b].name << ":\n";
		for (size_t i = 0; i < fn.blocks[b].instructions.size(); ++i)
			out << "    " << instruction_text(fn.blocks[b].instructions[i])
			    << "\n";
	}
	out << "}\n";
}

}  // namespace

bool same_type(const Type& a, const Type& b)
{
	return a.text == b.text;
}

bool is_terminator(InstrKind kind)
{
	return kind == InstrKind::Jump || kind == InstrKind::Branch ||
	       kind == InstrKind::Switch || kind == InstrKind::Return ||
	       kind == InstrKind::Throw || kind == InstrKind::Resume;
}

Type instruction_result_type(const Instruction& ins)
{
	if (ins.kind == InstrKind::Addr || ins.kind == InstrKind::Index)
		return lowir2cy86::parse_type_text("ptr");
	if (ins.kind == InstrKind::AtomicCompareExchange)
		return lowir2cy86::parse_type_text("i64");
	if (ins.kind == InstrKind::Cmp || ins.kind == InstrKind::Exception ||
	    ins.kind == InstrKind::ExceptionSelector || ins.kind == InstrKind::Call ||
	    ins.kind == InstrKind::Convert || ins.kind == InstrKind::Const ||
	    ins.kind == InstrKind::Copy || ins.kind == InstrKind::Load ||
	    ins.kind == InstrKind::AtomicLoad ||
	    ins.kind == InstrKind::AtomicExchange ||
	    ins.kind == InstrKind::AtomicAddFetch || ins.kind == InstrKind::Unary ||
	    ins.kind == InstrKind::Binary || ins.kind == InstrKind::VaArg ||
	    ins.kind == InstrKind::StackAlloc)
		return ins.type;
	return Type();
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
			throw runtime_error("undefined LowIR temp");
		return it->second;
	}
	if (value.kind == ValueKind::Slot)
	{
		map<string, Type>::const_iterator it = fn.slot_types.find(value.text);
		if (it == fn.slot_types.end())
			throw runtime_error("undefined LowIR slot");
		return it->second;
	}
	if (value.kind == ValueKind::Global)
	{
		map<string, size_t>::const_iterator it =
		    program.global_by_name.find(value.text);
		if (it == program.global_by_name.end())
			return lowir2cy86::parse_type_text("ptr");
		return program.globals[it->second].has_type
		           ? program.globals[it->second].type
		           : lowir2cy86::parse_type_text("ptr");
	}
	if (value.kind == ValueKind::Function)
		return lowir2cy86::parse_type_text("ptr");
	return Type();
}

void rebuild_program(Program& program)
{
	program.global_by_name.clear();
	program.function_by_name.clear();
	program.needs_eh_runtime = false;
	program.entry_function.clear();
	program.init_function.clear();
	program.fini_function.clear();

	set<string> top_names;
	for (size_t i = 0; i < program.globals.size(); ++i)
	{
		if (!top_names.insert(program.globals[i].name).second)
			throw runtime_error("duplicate LowIR top-level name");
		program.global_by_name[program.globals[i].name] = i;
	}
	for (size_t i = 0; i < program.functions.size(); ++i)
	{
		if (!top_names.insert(program.functions[i].name).second)
			throw runtime_error("duplicate LowIR top-level name");
		program.function_by_name[program.functions[i].name] = i;
	}

	for (size_t f = 0; f < program.functions.size(); ++f)
		rebuild_function(program.functions[f]);
}

void rebuild_function(Function& fn)
{
	fn.temp_order.clear();
	fn.temp_types.clear();
	fn.temp_offsets.clear();
	fn.slot_offsets.clear();
	fn.slot_types.clear();
	fn.param_types.clear();
	fn.param_offsets.clear();
	for (size_t i = 0; i < fn.params.size(); ++i)
		fn.param_types[fn.params[i].name] = fn.params[i].type;
	for (size_t i = 0; i < fn.slots.size(); ++i)
		fn.slot_types[fn.slots[i].name] = fn.slots[i].type;
	for (size_t b = 0; b < fn.blocks.size(); ++b)
	{
		if (fn.blocks[b].instructions.empty() ||
		    !is_terminator(fn.blocks[b].instructions.back().kind))
			throw runtime_error("LowIR block missing terminator");
		for (size_t i = 0; i < fn.blocks[b].instructions.size(); ++i)
		{
			Instruction& ins = fn.blocks[b].instructions[i];
			if (!ins.has_dest)
				continue;
			if (fn.temp_types.find(ins.dest) != fn.temp_types.end() ||
			    fn.param_types.find(ins.dest) != fn.param_types.end())
				throw runtime_error("duplicate LowIR temp");
			fn.temp_types[ins.dest] = instruction_result_type(ins);
			fn.temp_order.push_back(ins.dest);
		}
	}
}

string emit_lowir(const Program& program)
{
	ostringstream out;
	bool first_phase = true;
	for (int pass = 0; pass < 5; ++pass)
	{
		ostringstream phase;
		bool any = false;
		if (pass == 0 || pass == 2)
		{
			for (size_t i = 0; i < program.globals.size(); ++i)
			{
				const bool want_decl = pass == 0;
				if (program.globals[i].declaration != want_decl)
					continue;
				emit_global(phase, program.globals[i]);
				any = true;
			}
		}
		else if (pass == 1 || pass == 3)
		{
			for (size_t i = 0; i < program.functions.size(); ++i)
			{
				const bool want_decl = pass == 1;
				if (program.functions[i].declaration != want_decl)
					continue;
				emit_function(phase, program.functions[i]);
				any = true;
			}
		}
		else
		{
			for (size_t i = 0; i < program.aliases.size(); ++i)
			{
				phase << "alias object " << program.aliases[i].object
				    << " = " << program.aliases[i].target << "\n";
				any = true;
			}
		}
		if (!any)
			continue;
		if (!first_phase && pass != 4)
			out << "\n";
		out << phase.str();
		first_phase = false;
	}
	return out.str();
}

void write_lowir_file(const string& outfile, const string& text)
{
	ofstream out(outfile.c_str());
	if (!out)
		throw runtime_error("cannot open output file");
	out << text;
	out.close();
	if (!out)
		throw runtime_error("cannot write output file");
}

void optimize_files_to_file(const vector<string>& srcfiles,
                            const Options& options)
{
	Program program = lowir2cy86::parse_files(srcfiles);
	program = optimize_program(program,
	                           options.optimization_level,
	                           options.prune_unreachable_weak);
	write_lowir_file(options.outfile, emit_lowir(program));
}

}  // namespace lowiropt
