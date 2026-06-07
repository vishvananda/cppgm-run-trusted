#include "pa14_lowir_internal.h"

#include <sstream>

namespace pa14 {
namespace internal {
namespace {

void ensure_eh_runtime_declarations(ProgramLowerer& program)
{
	if (program.declared_functions.insert(
		    "__external_runtime___Unwind_Resume").second)
		program.declares.push_back(
			"declare function @__external_runtime___Unwind_Resume() -> void "
			"[return=noreturn, role=eh_resume, linkage=c, "
			"binding=strong, object=_Unwind_Resume]");
	if (program.declared_functions.insert(
		    "__external_runtime____gxx_personality_v0").second)
		program.declares.push_back(
			"declare function @__external_runtime____gxx_personality_v0() "
			"-> void [role=eh_personality, linkage=c, binding=strong, "
			"object=__gxx_personality_v0]");
}

}  // namespace

void FunctionLowerer::ensure_throw_runtime_declarations()
{
	ensure_eh_runtime_declarations(program_);
	if (program_.declared_functions.insert(
		    "__external_runtime____cxa_allocate_exception").second)
		program_.declares.push_back(
			"declare function @__external_runtime____cxa_allocate_exception"
			"(%arg0 : i64) -> ptr [role=eh_allocate_exception, linkage=c, "
			"binding=strong, object=__cxa_allocate_exception]");
	if (program_.declared_functions.insert(
		    "__external_runtime____cxa_throw").second)
		program_.declares.push_back(
			"declare function @__external_runtime____cxa_throw"
			"(%arg0 : ptr, %arg1 : ptr, %arg2 : ptr) -> void "
			"[return=noreturn, role=eh_throw, linkage=c, binding=strong, "
			"object=__cxa_throw]");
}

void FunctionLowerer::ensure_rethrow_runtime_declaration()
{
	ensure_eh_runtime_declarations(program_);
	if (program_.declared_functions.insert(
		    "__external_runtime____cxa_rethrow").second)
		program_.declares.push_back(
			"declare function @__external_runtime____cxa_rethrow() -> void "
			"[return=noreturn, role=eh_rethrow, linkage=c, "
			"binding=strong, object=__cxa_rethrow]");
}

void FunctionLowerer::emit_rethrow()
{
	instr("call void @__external_runtime____cxa_rethrow()");
	TypePtr ret = fn_.binding != NULL && fn_.binding->type.get() != NULL
		? fn_.binding->type->base : pa11::make_fundamental(FT_VOID);
	if (pa11::is_void_type(ret) ||
	    pa11::strip_cv(ret)->kind == TypeKind::Record)
		terminate("return void");
	else
		terminate("return " + scalar_lowir_type(ret) + " 0");
}

string FunctionLowerer::ensure_exception_object_global(TypePtr object)
{
	string local_rtti = program_.typeid_rtti_symbol(object);
	string eh_part = local_rtti.compare(0, 7, "__rtti_") == 0
		? local_rtti.substr(7) : pa11::describe_type(object);
	for (size_t i = 0; i < eh_part.size(); ++i)
		if (eh_part[i] == ' ')
			eh_part[i] = '_';
	string ehobj = "__ehobj_" + eh_part;
	if (program_.defined_globals.insert(ehobj).second)
	{
		ostringstream out;
		out << "global @" << ehobj << " [binding=weak, object=@"
		    << ehobj << "] = {\n";
		out << "  zero " << pa11::type_size(object) << "\n";
		out << "}";
		program_.globals.push_back(out.str());
	}
	return ehobj;
}

string FunctionLowerer::emit_exception_allocation(TypePtr object,
                                                  bool protect_throw,
                                                  string& throw_dispatch)
{
	string alloc = fresh_temp();
	if (!protect_throw)
	{
		instr(alloc +
		      " = call ptr @__external_runtime____cxa_allocate_exception(" +
		      to_string(pa11::type_size(object)) + ")");
		return alloc;
	}
	string throw_alloc_slot = fresh_aux_slot("throw_alloc", "ptr");
	throw_dispatch = fresh_block("call_unwind_dispatch");
	string throw_alloc_end = fresh_block("throw_alloc_unwind_end");
	instr("eh_try ^" + throw_dispatch);
	++eh_try_depth_;
	instr(alloc +
	      " = call ptr @__external_runtime____cxa_allocate_exception(" +
	      to_string(pa11::type_size(object)) + ")");
	instr("store ptr " + alloc + ", $" + throw_alloc_slot);
	--eh_try_depth_;
	instr("eh_end");
	terminate("jump ^" + throw_alloc_end);
	start_block(throw_dispatch);
	emit_active_catch_clause(active_catches_.back());
	instr("eh_cleanup");
	emit_unwind_cleanups();
	instr("eh_end");
	terminate("jump ^" + active_catches_.back().entry);
	start_block(throw_alloc_end);
	string loaded_alloc = fresh_temp();
	instr(loaded_alloc + " = load ptr $" + throw_alloc_slot);
	return loaded_alloc;
}

void FunctionLowerer::lower_throw_operand(Value allocation,
                                          TypePtr object,
                                          const Node& operand)
{
	if (object->kind == TypeKind::Record)
	{
		Binding* copy_ctor =
			find_copy_move_constructor(object,
			                           operand.category == ValueCategory::XValue);
		if (copy_ctor == NULL && operand.category == ValueCategory::XValue)
			copy_ctor = find_copy_move_constructor(object, false);
		if (copy_ctor != NULL)
		{
			program_.demand_function_declaration(copy_ctor);
			program_.demand_inline_function(copy_ctor);
		}
		function<Value()> addr_for = [allocation]() { return allocation; };
		lower_object_init(addr_for, object, operand);
		return;
	}
	Value raw = emit_rvalue(operand);
	Value converted = convert_value(raw, operand.type, object);
	instr("store " + scalar_lowir_type(object) + " " + converted.text +
	      ", " + allocation.text);
}

string FunctionLowerer::throw_destructor_argument(TypePtr object)
{
	if (object->kind != TypeKind::Record)
		return "0";
	Binding* dtor = find_destructor(object);
	if (dtor == NULL)
		return "0";
	program_.demand_function_declaration(dtor);
	program_.demand_inline_function(dtor);
	string dtor_arg = fresh_temp();
	instr(dtor_arg + " = addr @" + program_.symbol_for(dtor));
	return dtor_arg;
}

void FunctionLowerer::emit_throw_runtime_call(const string& allocation,
                                              const string& rtti,
                                              TypePtr object,
                                              bool protect_throw,
                                              const string& throw_dispatch)
{
	if (protect_throw)
	{
		instr("eh_try ^" + throw_dispatch);
		++eh_try_depth_;
	}
	string rtti_addr = fresh_temp();
	instr(rtti_addr + " = addr @" + rtti);
	string dtor_arg = throw_destructor_argument(object);
	instr("call void @__external_runtime____cxa_throw(" + allocation +
	      ", " + rtti_addr + ", " + dtor_arg + ")");
	if (protect_throw)
	{
		--eh_try_depth_;
		instr("eh_end");
	}
}

Value FunctionLowerer::emit_throw(const Node& expr)
{
	if (expr.children.empty())
	{
		ensure_rethrow_runtime_declaration();
		emit_rethrow();
		return Value("void", "");
	}
	ensure_throw_runtime_declarations();
	const Node& operand = expr.children[0];
	TypePtr object = pa11::strip_cv(object_type(operand.type));
	program_.emit_typeinfo(object);
	string rtti = program_.catch_rtti_symbol(object);
	if (rtti.empty())
		rtti = program_.typeid_rtti_symbol(object);
	if (rtti.empty())
		throw runtime_error("unsupported throw type");
	ensure_exception_object_global(object);
	bool protect_throw =
		object->kind == TypeKind::Record && !active_catches_.empty() &&
		eh_try_depth_ > 0 && has_active_cleanups();
	string throw_dispatch;
	string alloc =
		emit_exception_allocation(object, protect_throw, throw_dispatch);
	lower_throw_operand(Value("ptr", alloc), object, operand);
	emit_throw_runtime_call(alloc, rtti, object, protect_throw,
	                        throw_dispatch);
	return Value("void", "");
}

}  // namespace internal
}  // namespace pa14
