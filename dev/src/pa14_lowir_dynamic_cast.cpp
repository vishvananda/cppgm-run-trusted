#include "pa14_lowir_internal.h"

namespace pa14 {
namespace internal {

namespace {

bool record_has_virtual_base_subobject(TypePtr record, TypePtr base)
{
	TypePtr bare = record.get() != NULL ? pa11::strip_cv(record) : TypePtr();
	TypePtr wanted = base.get() != NULL ? pa11::strip_cv(base) : TypePtr();
	if (bare.get() == NULL || wanted.get() == NULL ||
	    bare->kind != TypeKind::Record || wanted->kind != TypeKind::Record)
		return false;
	vector<TypePtr> vbases = pa11::record_virtual_bases(bare);
	for (size_t i = 0; i < vbases.size(); ++i)
		if (pa11::same_type(pa11::strip_cv(vbases[i]), wanted))
			return true;
	return false;
}

int64_t virtual_base_offset_slot(TypePtr record, TypePtr base)
{
	TypePtr bare = record.get() != NULL ? pa11::strip_cv(record) : TypePtr();
	TypePtr wanted = base.get() != NULL ? pa11::strip_cv(base) : TypePtr();
	if (bare.get() == NULL || wanted.get() == NULL ||
	    bare->kind != TypeKind::Record || wanted->kind != TypeKind::Record)
		return 0;
	vector<TypePtr> vbases = pa11::record_virtual_bases(bare);
	for (size_t i = 0; i < vbases.size(); ++i)
		if (pa11::same_type(pa11::strip_cv(vbases[i]), wanted))
			return static_cast<int64_t>(i * 8) -
			       static_cast<int64_t>(vtable_address_point_offset(bare));
	return 0;
}

}  // namespace

Value FunctionLowerer::emit_dynamic_cast(const Node& expr,
                                         bool reference_result)
{
	if (expr.children.empty())
		throw runtime_error("dynamic_cast missing operand");
	const Node& operand = expr.children[0];
	TypePtr target_type = pa11::strip_cv(expr.type);
	TypePtr target_object;
	if (target_type->kind == TypeKind::Pointer ||
	    target_type->kind == TypeKind::LValueReference ||
	    target_type->kind == TypeKind::RValueReference)
		target_object = pa11::strip_cv(target_type->base);
	TypePtr source_object;
	Value source_ptr;
	if (reference_result)
	{
		source_object = pa11::strip_cv(object_type(operand.type));
		source_ptr = ensure_pointer(emit_lvalue_addr(operand));
	}
	else
	{
		TypePtr source_type = pa11::strip_cv(strip_for_value(operand.type));
		if (source_type->kind != TypeKind::Pointer)
			throw runtime_error("dynamic_cast source is not pointer");
		source_object = pa11::strip_cv(source_type->base);
		source_ptr = ensure_pointer(emit_rvalue(operand));
	}
	bool target_void_pointer =
		!reference_result &&
		target_type->kind == TypeKind::Pointer &&
		target_object.get() != NULL &&
		target_object->kind == TypeKind::Fundamental &&
		target_object->fundamental == FT_VOID;
	if (target_void_pointer)
	{
		if (source_object.get() == NULL ||
		    source_object->kind != TypeKind::Record ||
		    !source_object->is_polymorphic)
			throw runtime_error("unsupported dynamic_cast type");
		string slot = fresh_aux_slot("dyn_cast", "ptr");
		instr("store ptr 0, $" + slot);
		string is_null = fresh_temp();
		instr(is_null + " = cmp eq ptr " + source_ptr.text + ", 0");
		string scan = fresh_block("dyn_cast_scan");
		string end = fresh_block("dyn_cast_end");
		terminate("branch " + is_null + ", ^" + end + ", ^" + scan);
		start_block(scan);
		string vptr = fresh_temp();
		instr(vptr + " = load ptr " + source_ptr.text);
		string offset_addr = fresh_temp();
		instr(offset_addr + " = index i8 " + vptr + ", -16");
		string offset = fresh_temp();
		instr(offset + " = load i64 " + offset_addr);
		string top = fresh_temp();
		instr(top + " = index i8 " + source_ptr.text + ", " + offset);
		instr("store ptr " + top + ", $" + slot);
		terminate("jump ^" + end);
		start_block(end);
		string loaded = fresh_temp();
		instr(loaded + " = load ptr $" + slot);
		return Value("ptr", loaded);
	}
	if (source_object.get() != NULL && target_object.get() != NULL &&
	    source_object->kind == TypeKind::Record &&
	    target_object->kind == TypeKind::Record &&
	    record_has_base_subobject(source_object, target_object))
	{
		string slot = fresh_aux_slot("dyn_cast", "ptr");
		instr("store ptr 0, $" + slot);
		string is_null = fresh_temp();
		instr(is_null + " = cmp eq ptr " + source_ptr.text + ", 0");
		string adjust = fresh_block("dyn_cast_upcast");
		string end = fresh_block("dyn_cast_end");
		terminate("branch " + is_null + ", ^" + end + ", ^" + adjust);
		start_block(adjust);
		string adjusted = source_ptr.text;
		if (record_has_virtual_base_subobject(source_object, target_object))
		{
			string vptr = fresh_temp();
			instr(vptr + " = load ptr " + source_ptr.text);
			string offset_addr = fresh_temp();
			instr(offset_addr + " = index i8 " + vptr + ", " +
			      to_string(virtual_base_offset_slot(source_object,
			                                         target_object)));
			string offset = fresh_temp();
			instr(offset + " = load i64 " + offset_addr);
			adjusted = fresh_temp();
			instr(adjusted + " = index i8 " + source_ptr.text + ", " +
			      offset);
		}
		else
		{
			uint64_t offset =
				base_subobject_offset(source_object, target_object);
			if (offset != 0)
			{
				adjusted = fresh_temp();
				instr(adjusted + " = index i8 " + source_ptr.text +
				      ", " + to_string(offset));
			}
		}
		instr("store ptr " + adjusted + ", $" + slot);
		terminate("jump ^" + end);
		start_block(end);
		string loaded = fresh_temp();
		instr(loaded + " = load ptr $" + slot);
		return Value("ptr", loaded);
	}
	if (reference_result)
	{
		if (program_.declared_functions.insert(
			    "__external_runtime___Unwind_Resume").second)
			program_.declares.push_back(
				"declare function @__external_runtime___Unwind_Resume() -> void "
				"[return=noreturn, role=eh_resume, linkage=c, "
				"binding=strong, object=_Unwind_Resume]");
		if (program_.declared_functions.insert(
			    "__external_runtime____gxx_personality_v0").second)
			program_.declares.push_back(
				"declare function @__external_runtime____gxx_personality_v0() "
				"-> void [role=eh_personality, linkage=c, binding=strong, "
				"object=__gxx_personality_v0]");
	}
	if (program_.declared_functions.insert(
		    "__external_runtime____dynamic_cast").second)
		program_.declares.push_back(
			"declare function @__external_runtime____dynamic_cast"
			"(%arg0 : ptr, %arg1 : ptr, %arg2 : ptr, %arg3 : i64) -> ptr "
			"[linkage=c, binding=strong, object=__dynamic_cast]");
	if (reference_result &&
	    program_.declared_functions.insert(
		    "__external_runtime____cxa_bad_cast").second)
		program_.declares.push_back(
			"declare function @__external_runtime____cxa_bad_cast() -> void "
			"[effects=readnone, unwind=may, return=noreturn, linkage=c, "
			"binding=strong, object=__cxa_bad_cast]");
	if (source_object.get() == NULL || target_object.get() == NULL ||
	    source_object->kind != TypeKind::Record ||
	    target_object->kind != TypeKind::Record)
		throw runtime_error("unsupported dynamic_cast type");
	program_.emit_rtti(source_object);
	program_.emit_rtti(target_object);
	program_.demand_vtable(target_object, false);
	string source_rtti = program_.typeid_rtti_symbol(source_object);
	string target_rtti = program_.typeid_rtti_symbol(target_object);
	if (source_rtti.empty() || target_rtti.empty())
		throw runtime_error("unsupported dynamic_cast rtti");
	string slot = fresh_aux_slot("dyn_cast", "ptr");
	instr("store ptr 0, $" + slot);
	string is_null = fresh_temp();
	instr(is_null + " = cmp eq ptr " + source_ptr.text + ", 0");
	string scan = fresh_block("dyn_cast_scan");
	string end = fresh_block("dyn_cast_end");
	terminate("branch " + is_null + ", ^" + end + ", ^" + scan);
	start_block(scan);
	string source_addr = fresh_temp();
	instr(source_addr + " = addr @" + source_rtti);
	string target_addr = fresh_temp();
	instr(target_addr + " = addr @" + target_rtti);
	string result = fresh_temp();
	int64_t hint = -2;
	if (record_has_base_subobject(target_object, source_object) &&
	    !record_has_virtual_base_subobject(target_object, source_object))
		hint = static_cast<int64_t>(
			base_subobject_offset(target_object, source_object));
	instr(result + " = call ptr @__external_runtime____dynamic_cast(" +
	      source_ptr.text + ", " + source_addr + ", " + target_addr +
	      ", " + to_string(hint) + ")");
	instr("store ptr " + result + ", $" + slot);
	if (reference_result)
	{
		string failed = fresh_temp();
		instr(failed + " = cmp eq ptr " + result + ", 0");
		string fail = fresh_block("dyn_cast_fail");
		string found = fresh_block("dyn_cast_found");
		terminate("branch " + failed + ", ^" + fail + ", ^" + found);
		start_block(fail);
		instr("call void @__external_runtime____cxa_bad_cast()");
		TypePtr ret = fn_.binding != NULL && fn_.binding->type.get() != NULL
			? fn_.binding->type->base : pa11::make_fundamental(FT_VOID);
		if (pa11::is_void_type(ret) ||
		    pa11::strip_cv(ret)->kind == TypeKind::Record)
			terminate("return void");
		else
			terminate("return " + scalar_lowir_type(ret) + " 0");
		start_block(found);
		terminate("jump ^" + end);
		start_block(fresh_block("block"));
		terminate("jump ^" + end);
	}
	else
		terminate("jump ^" + end);
	start_block(end);
	string loaded = fresh_temp();
	instr(loaded + " = load ptr $" + slot);
	return Value("ptr", loaded);
}

}  // namespace internal
}  // namespace pa14
