#include "lowir2cy86_runtime_emit.h"

#include <ostream>
#include <sstream>

using namespace std;

namespace lowir2cy86 {
namespace {

struct RuntimeEmitter
{
	ostream& out;
	int& eh_label_counter;

	RuntimeEmitter(ostream& output, int& counter)
	    : out(output), eh_label_counter(counter) {}

	void line(const string& text) { out << '\t' << text << ";\n"; }
	void label(const string& text) { out << text << ":\n"; }

	string next_label(const string& prefix)
	{
		return prefix + to_string(eh_label_counter++);
	}

	string i128_helper_label(const string& op) const
	{
		return function_label("@__cppgm_i128_" + op);
	}

	void emit_eh_dispatch()
	{
		line("move64 x64 [g____cppgm_eh_top]");
		line("ieq64 z8 x64 0");
		const string handler = next_label("__eh_handler__");
		const string unhandled = next_label("__eh_unhandled__");
		line("jumpif z8 " + unhandled);
		label(handler);
		line("move64 y64 [x64]");
		line("move64 [g____cppgm_eh_top] y64");
		line("move64 z64 [x64+8]");
		line("move64 bp [x64+16]");
		line("move64 sp [x64+24]");
		line("jump z64");
		label(unhandled);
		line("move64 x64 [g____cppgm_eh_value]");
		line("call fn____cppgm_eh_unhandled");
		line("syscall1 t64 60 x64");
		out << "\n";
	}

	void emit_i128_shift_function(const string& op)
	{
		const string base = i128_helper_label(op);
		const string done = base + "__done";
		const string zero = base + "__zero";
		const string ge64 = base + "__ge64";
		label(base);
		line("ieq64 t8 z64 0");
		line("jumpif t8 " + done);
		line("uge64 t8 z64 128");
		line("jumpif t8 " + zero);
		line("uge64 t8 z64 64");
		line("jumpif t8 " + ge64);
		if (op == "shl")
		{
			line("move64 t64 64");
			line("isub64 t64 t64 z64");
			line("urshift64 t64 x64 t8");
			line("lshift64 y64 y64 z8");
			line("or64 y64 y64 t64");
			line("lshift64 x64 x64 z8");
		}
		else if (op == "ushr")
		{
			line("move64 t64 64");
			line("isub64 t64 t64 z64");
			line("lshift64 t64 y64 t8");
			line("urshift64 x64 x64 z8");
			line("or64 x64 x64 t64");
			line("urshift64 y64 y64 z8");
		}
		else
		{
			line("move64 t64 64");
			line("isub64 t64 t64 z64");
			line("lshift64 t64 y64 t8");
			line("urshift64 x64 x64 z8");
			line("or64 x64 x64 t64");
			line("srshift64 y64 y64 z8");
		}
		line("ret");
		label(ge64);
		line("isub64 z64 z64 64");
		if (op == "shl")
		{
			line("lshift64 y64 x64 z8");
			line("move64 x64 0");
		}
		else if (op == "ushr")
		{
			line("urshift64 x64 y64 z8");
			line("move64 y64 0");
		}
		else
		{
			line("srshift64 x64 y64 z8");
			line("move8 z8 63");
			line("srshift64 y64 y64 z8");
		}
		line("ret");
		label(zero);
		if (op == "shr")
		{
			line("move8 z8 63");
			line("srshift64 y64 y64 z8");
			line("move64 x64 y64");
		}
		else
		{
			line("move64 x64 0");
			line("move64 y64 0");
		}
		label(done);
		line("ret");
		out << "\n";
	}

	void emit_i128_mul_function()
	{
		const string base = i128_helper_label("mul");
		const string loop = base + "__loop";
		const string noadd = base + "__noadd";
		const string done = base + "__done";
		label(base);
		line("isub64 sp sp 48");
		line("move64 [sp] x64");
		line("move64 [sp+8] y64");
		line("move64 [sp+16] z64");
		line("move64 [sp+24] t64");
		line("move64 [sp+32] 0");
		line("move64 [sp+40] 0");
		label(loop);
		line("or64 x64 [sp+16] [sp+24]");
		line("ieq64 x8 x64 0");
		line("jumpif x8 " + done);
		line("and64 x64 [sp+16] 1");
		line("ieq64 x8 x64 0");
		line("jumpif x8 " + noadd);
		line("move64 x64 [sp+32]");
		line("move64 y64 [sp+40]");
		line("move64 z64 [sp]");
		line("move64 t64 [sp+8]");
		line("iadd64 x64 x64 z64");
		line("ult64 z8 x64 z64");
		line("iadd64 y64 y64 t64");
		line("move64 t64 0");
		line("move8 t8 z8");
		line("iadd64 y64 y64 t64");
		line("move64 [sp+32] x64");
		line("move64 [sp+40] y64");
		label(noadd);
		line("move64 x64 [sp]");
		line("move8 t8 63");
		line("urshift64 z64 x64 t8");
		line("lshift64 x64 x64 1");
		line("move64 [sp] x64");
		line("move64 y64 [sp+8]");
		line("lshift64 y64 y64 1");
		line("or64 y64 y64 z64");
		line("move64 [sp+8] y64");
		line("move64 x64 [sp+24]");
		line("and64 z64 x64 1");
		line("urshift64 x64 x64 1");
		line("move64 [sp+24] x64");
		line("move64 y64 [sp+16]");
		line("urshift64 y64 y64 1");
		line("lshift64 z64 z64 63");
		line("or64 y64 y64 z64");
		line("move64 [sp+16] y64");
		line("jump " + loop);
		label(done);
		line("move64 x64 [sp+32]");
		line("move64 y64 [sp+40]");
		line("iadd64 sp sp 48");
		line("ret");
		out << "\n";
	}

	void emit_i128_divmod_function(const string& op, bool return_remainder)
	{
		const string base = i128_helper_label(op);
		const string loop = base + "__loop";
		const string highbit = base + "__highbit";
		const string afterbit = base + "__afterbit";
		const string nosub = base + "__nosub";
		const string sub = base + "__sub";
		const string qhigh = base + "__qhigh";
		const string afterq = base + "__afterq";
		const string done = base + "__done";
		const string divzero = base + "__divzero";
		label(base);
		line("isub64 sp sp 72");
		line("move64 [sp] x64");
		line("move64 [sp+8] y64");
		line("move64 [sp+16] z64");
		line("move64 [sp+24] t64");
		line("move64 [sp+32] 0");
		line("move64 [sp+40] 0");
		line("move64 [sp+48] 0");
		line("move64 [sp+56] 0");
		line("move64 [sp+64] 128");
		label(loop);
		line("isub64 [sp+64] [sp+64] 1");
		line("move64 x64 [sp+48]");
		line("move8 t8 63");
		line("urshift64 z64 x64 t8");
		line("lshift64 x64 x64 1");
		line("move64 [sp+48] x64");
		line("move64 y64 [sp+56]");
		line("lshift64 y64 y64 1");
		line("or64 y64 y64 z64");
		line("move64 [sp+56] y64");
		line("uge64 x8 [sp+64] 64");
		line("jumpif x8 " + highbit);
		line("move64 z64 [sp+64]");
		line("move64 x64 [sp]");
		line("urshift64 x64 x64 z8");
		line("and64 x64 x64 1");
		line("or64 [sp+48] [sp+48] x64");
		line("jump " + afterbit);
		label(highbit);
		line("move64 z64 [sp+64]");
		line("isub64 z64 z64 64");
		line("move64 x64 [sp+8]");
		line("urshift64 x64 x64 z8");
		line("and64 x64 x64 1");
		line("or64 [sp+48] [sp+48] x64");
		label(afterbit);
		line("ugt64 x8 [sp+56] [sp+24]");
		line("jumpif x8 " + sub);
		line("ult64 x8 [sp+56] [sp+24]");
		line("jumpif x8 " + nosub);
		line("uge64 x8 [sp+48] [sp+16]");
		line("jumpif x8 " + sub);
		line("jump " + nosub);
		label(sub);
		line("ult64 x8 [sp+48] [sp+16]");
		line("move64 y64 0");
		line("move8 y8 x8");
		line("isub64 x64 [sp+48] [sp+16]");
		line("move64 [sp+48] x64");
		line("isub64 x64 [sp+56] [sp+24]");
		line("isub64 x64 x64 y64");
		line("move64 [sp+56] x64");
		line("move64 x64 1");
		line("uge64 z8 [sp+64] 64");
		line("jumpif z8 " + qhigh);
		line("move64 z64 [sp+64]");
		line("lshift64 x64 x64 z8");
		line("or64 [sp+32] [sp+32] x64");
		line("jump " + afterq);
		label(qhigh);
		line("move64 z64 [sp+64]");
		line("isub64 z64 z64 64");
		line("lshift64 x64 x64 z8");
		line("or64 [sp+40] [sp+40] x64");
		label(afterq);
		label(nosub);
		line("ine64 x8 [sp+64] 0");
		line("jumpif x8 " + loop);
		line(string("move64 x64 ") + (return_remainder ? "[sp+48]" : "[sp+32]"));
		line(string("move64 y64 ") + (return_remainder ? "[sp+56]" : "[sp+40]"));
		line("iadd64 sp sp 72");
		line("ret");
		label(divzero);
		line("move64 x64 0");
		line("move64 y64 0");
		label(done);
		line("ret");
		out << "\n";
	}

	void emit_i128_runtime_functions()
	{
		emit_i128_shift_function("shl");
		emit_i128_shift_function("ushr");
		emit_i128_shift_function("shr");
		emit_i128_mul_function();
		emit_i128_divmod_function("udiv", false);
		emit_i128_divmod_function("umod", true);
	}

	void emit_pure_virtual_runtime_function()
	{
		label(function_label("@__cxa_pure_virtual"));
		line("syscall1 t64 60 86");
		line("ret");
		out << "\n";
	}

	void emit_operator_delete_runtime_function(const string& name)
	{
		label(function_label(name));
		line("ret");
		out << "\n";
	}

	void emit_allocator_runtime_function(const string& name)
	{
		label(function_label(name));
		line("move64 z64 x64");
		line("iadd64 z64 z64 15");
		line("and64 z64 z64 -16");
		line("move64 y64 [g____cppgm_alloc_bump]");
		line("move64 x64 g____cppgm_alloc_pool");
		line("iadd64 x64 x64 y64");
		line("iadd64 y64 y64 z64");
		line("move64 [g____cppgm_alloc_bump] y64");
		line("ret");
		out << "\n";
	}

	void emit_bad_cast_runtime_function()
	{
		label(function_label("@__external_runtime____cxa_bad_cast"));
		line("syscall1 t64 60 86");
		line("ret");
		out << "\n";
	}

	void emit_dynamic_cast_runtime_function(const Program& program)
	{
		const string dyn = function_label("@__external_runtime____dynamic_cast");
		const string exact = dyn + "__exact";
		const string scan = dyn + "__scan";
		const string loop = dyn + "__loop";
		const string found = dyn + "__found";
		const string fail = dyn + "__fail";
		const string fail_no_stack = dyn + "__fail_no_stack";
		const string not_vmi = dyn + "__not_vmi";
		const string vmi_global = "@__external_rtti_vtable____vmi_class_type_info";
		label(dyn);
		line("ieq64 t8 x64 0");
		line("jumpif t8 " + fail_no_stack);
		line("move64 t64 [x64]");
		line("move64 y64 [t64-16]");
		line("iadd64 x64 x64 y64");
		line("move64 t64 [t64-8]");
		line("ieq64 y8 t64 z64");
		line("jumpif y8 " + exact);
		if (program.global_by_name.find(vmi_global) == program.global_by_name.end())
		{
			line("move64 x64 0");
			line("ret");
			out << "\n";
			return;
		}
		line("isub64 sp sp 8");
		line("move64 [sp] x64");
		line("move64 x64 " + global_label(vmi_global));
		line("iadd64 x64 x64 16");
		line("move64 y64 [t64]");
		line("ieq64 y8 y64 x64");
		line("jumpif y8 " + scan);
		label(not_vmi);
		line("move64 x64 0");
		line("iadd64 sp sp 8");
		line("ret");
		label(scan);
		line("move64 y64 0");
		line("move32 y32 [t64+20]");
		line("iadd64 t64 t64 24");
		label(loop);
		line("ieq64 x8 y64 0");
		line("jumpif x8 " + fail);
		line("move64 x64 [t64]");
		line("ieq64 x8 x64 z64");
		line("jumpif x8 " + found);
		line("iadd64 t64 t64 16");
		line("isub64 y64 y64 1");
		line("jump " + loop);
		label(found);
		line("move64 y64 [t64+8]");
		line("move8 x8 8");
		line("srshift64 y64 y64 x8");
		line("move64 x64 [sp]");
		line("iadd64 x64 x64 y64");
		line("iadd64 sp sp 8");
		line("ret");
		label(fail);
		line("move64 x64 0");
		line("iadd64 sp sp 8");
		line("ret");
		label(fail_no_stack);
		line("move64 x64 0");
		line("ret");
		label(exact);
		line("ret");
		out << "\n";
	}

	void emit_eh_runtime_function(bool native_output)
	{
		label("fn____cppgm_eh_unhandled");
		line("syscall1 t64 60 x64");
		out << "\n";
		if (!native_output)
			return;
		label(function_label("@__external_runtime____cxa_allocate_exception"));
		line("move64 x64 g____cppgm_eh_object_pool");
		line("move64 y64 [g____cppgm_eh_alloc]");
		line("iadd64 x64 x64 y64");
		line("iadd64 y64 y64 256");
		line("move64 [g____cppgm_eh_alloc] y64");
		line("ret");
		out << "\n";
		label(function_label("@__external_runtime____cxa_throw"));
		line("move64 [g____cppgm_eh_value] x64");
		line("move64 [g____cppgm_eh_type] y64");
		line("move64 [g____cppgm_eh_dtor] z64");
		line("move64 [g____cppgm_eh_selector] 0");
		emit_eh_dispatch();
		out << "\n";
		label(function_label("@__external_runtime____cxa_begin_catch"));
		line("ret");
		out << "\n";
		label(function_label("@__external_runtime____cxa_end_catch"));
		line("move64 y64 [g____cppgm_eh_dtor]");
		line("ieq64 z8 y64 0");
		const string no_dtor = next_label("__eh_end_catch_no_dtor__");
		line("jumpif z8 " + no_dtor);
		line("move64 x64 [g____cppgm_eh_value]");
		line("call y64");
		label(no_dtor);
		line("move64 [g____cppgm_eh_dtor] 0");
		line("ret");
		out << "\n";
		label(function_label("@__external_runtime____cxa_rethrow"));
		emit_eh_dispatch();
		out << "\n";
		label(function_label("@__external_runtime___Unwind_Resume"));
		emit_eh_dispatch();
		out << "\n";
		label(function_label("@__external_runtime____gxx_personality_v0"));
		line("ret");
		out << "\n";
		label(function_label("@__external_runtime____cxa_call_unexpected"));
		emit_eh_dispatch();
		out << "\n";
	}

	void emit_eh_runtime_globals(bool native_output)
	{
		label("g____cppgm_eh_top");
		line("data64 0");
		out << "\n";
		label("g____cppgm_eh_value");
		line("data64 0");
		out << "\n";
		if (!native_output)
			return;
		label("g____cppgm_eh_type");
		line("data64 0");
		out << "\n";
		label("g____cppgm_eh_selector");
		line("data64 0");
		out << "\n";
		label("g____cppgm_eh_dtor");
		line("data64 0");
		out << "\n";
		label("g____cppgm_eh_alloc");
		line("data64 0");
		out << "\n";
		label("g____cppgm_eh_object_pool");
		for (size_t i = 0; i < 4096; i += 8)
			line("data64 0");
		out << "\n";
	}

	void emit_allocator_runtime_globals()
	{
		label("g____cppgm_alloc_bump");
		line("data64 0");
		out << "\n";
		label("g____cppgm_alloc_pool");
		for (size_t i = 0; i < 65536; i += 8)
			line("data64 0");
		out << "\n";
	}
};

bool global_definition_for_object(const Program& program, const Global& decl)
{
	const string object = metadata_value(decl.metadata, "object");
	for (size_t i = 0; i < program.globals.size(); ++i)
	{
		const Global& candidate = program.globals[i];
		if (!candidate.declaration &&
		    (candidate.name == decl.name ||
		     (!object.empty() && metadata_value(candidate.metadata, "object") == object)))
			return true;
	}
	return false;
}

}  // namespace

bool program_needs_declared_runtime_function(const Program& program,
                                             const string& name)
{
	for (size_t i = 0; i < program.functions.size(); ++i)
		if (program.functions[i].name == name && program.functions[i].declaration)
			return true;
	return false;
}

bool program_needs_allocator_runtime(const Program& program)
{
	return program_needs_declared_runtime_function(program, "@malloc") ||
	       program_needs_declared_runtime_function(program, "@operator_new") ||
	       program_needs_declared_runtime_function(program, "@operator_new__");
}

string emit_i128_runtime_cy86()
{
	ostringstream out;
	int counter = 0;
	RuntimeEmitter(out, counter).emit_i128_runtime_functions();
	return out.str();
}

void append_required_abi_runtime_cy86(ostream& out,
                                      const Program& program,
                                      int& eh_label_counter)
{
	RuntimeEmitter emitter(out, eh_label_counter);
	if (program_needs_declared_runtime_function(program, "@__cxa_pure_virtual"))
		emitter.emit_pure_virtual_runtime_function();
	if (program_needs_declared_runtime_function(program, "@malloc"))
		emitter.emit_allocator_runtime_function("@malloc");
	if (program_needs_declared_runtime_function(program, "@operator_new"))
		emitter.emit_allocator_runtime_function("@operator_new");
	if (program_needs_declared_runtime_function(program, "@operator_new__"))
		emitter.emit_allocator_runtime_function("@operator_new__");
	if (program_needs_declared_runtime_function(program, "@free"))
		emitter.emit_operator_delete_runtime_function("@free");
	if (program_needs_declared_runtime_function(program, "@operator_delete"))
		emitter.emit_operator_delete_runtime_function("@operator_delete");
	if (program_needs_declared_runtime_function(program, "@operator_delete__"))
		emitter.emit_operator_delete_runtime_function("@operator_delete__");
	if (program_needs_declared_runtime_function(
		    program, "@__external_runtime____dynamic_cast"))
		emitter.emit_dynamic_cast_runtime_function(program);
	if (program_needs_declared_runtime_function(
		    program, "@__external_runtime____cxa_bad_cast"))
		emitter.emit_bad_cast_runtime_function();
}

void append_eh_runtime_cy86(ostream& out,
                            bool native_output,
                            int& eh_label_counter)
{
	RuntimeEmitter(out, eh_label_counter).emit_eh_runtime_function(native_output);
}

void append_eh_runtime_globals_cy86(ostream& out, bool native_output)
{
	int counter = 0;
	RuntimeEmitter(out, counter).emit_eh_runtime_globals(native_output);
}

void append_allocator_runtime_globals_cy86(ostream& out)
{
	int counter = 0;
	RuntimeEmitter(out, counter).emit_allocator_runtime_globals();
}

void append_external_rtti_vtable_stubs_cy86(ostream& out,
                                            const Program& program)
{
	for (size_t i = 0; i < program.globals.size(); ++i)
	{
		const Global& global = program.globals[i];
		if (!global.declaration ||
		    global.name.compare(0, 23, "@__external_rtti_vtable") != 0 ||
		    global_definition_for_object(program, global))
			continue;
		out << global_label(global.name) << ":\n";
		out << "\tdata64 0;\n\tdata64 0;\n\tdata64 0;\n\n";
	}
	if (program.needs_eh_runtime &&
	    program.global_by_name.find(
		    "@__external_rtti_vtable____si_class_type_info") ==
	    program.global_by_name.end())
	{
		out << global_label("@__external_rtti_vtable____si_class_type_info")
		    << ":\n";
		out << "\tdata64 0;\n\tdata64 0;\n\tdata64 0;\n\n";
	}
}

}  // namespace lowir2cy86
