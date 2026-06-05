#include "pa14_lowir_internal.h"

#include <sstream>

namespace pa14 {
namespace internal {

namespace {

string typeinfo_name_symbol(TypePtr record)
{
	TypePtr bare = pa11::strip_cv(record);
	if (template_record_uses_abi_global_symbol(bare))
		return "__typeinfo_name_" + template_record_global_symbol_part(bare);
	return "__typeinfo_name__" + bare->tag + "_" + record_lowir_name(bare);
}

string typeinfo_builtin_code(EFundamentalType type)
{
	if (type == FT_BOOL)
		return "b";
	if (type == FT_CHAR)
		return "c";
	if (type == FT_SIGNED_CHAR)
		return "a";
	if (type == FT_UNSIGNED_CHAR)
		return "h";
	if (type == FT_SHORT_INT)
		return "s";
	if (type == FT_UNSIGNED_SHORT_INT)
		return "t";
	if (type == FT_INT)
		return "i";
	if (type == FT_UNSIGNED_INT)
		return "j";
	if (type == FT_LONG_INT)
		return "l";
	if (type == FT_UNSIGNED_LONG_INT)
		return "m";
	if (type == FT_LONG_LONG_INT)
		return "x";
	if (type == FT_UNSIGNED_LONG_LONG_INT)
		return "y";
	if (type == FT_WCHAR_T)
		return "w";
	if (type == FT_CHAR16_T)
		return "Ds";
	if (type == FT_CHAR32_T)
		return "Di";
	return "";
}

string typeinfo_component_for_type(TypePtr type);

string template_value_typeinfo_component(TypePtr type, uint64_t value)
{
	TypePtr bare = type.get() != NULL ? pa11::strip_cv(type) : TypePtr();
	if (bare.get() != NULL && bare->kind == TypeKind::Enum)
	{
		string enum_name = bare->name;
		return "L" + to_string(enum_name.size()) + enum_name +
		       to_string(value) + "E";
	}
	string code = typeinfo_component_for_type(type);
	if (code.empty())
		code = "i";
	return "L" + code + to_string(value) + "E";
}

string template_value_typeinfo_component(
	const pa11::TemplateInstanceArgument& arg)
{
	if (!arg.value_name.empty())
	{
		string code = typeinfo_component_for_type(arg.type);
		if (code.empty())
			code = "i";
		return "L" + code + "_" + arg.value_name + "E";
	}
	return template_value_typeinfo_component(arg.type, arg.value);
}

string typeinfo_component_for_argument(
	const pa11::TemplateInstanceArgument& arg)
{
	if (arg.kind == pa11::TemplateInstanceArgumentKind::Type)
		return typeinfo_component_for_type(arg.type);
	if (arg.kind == pa11::TemplateInstanceArgumentKind::Value)
	{
		if (arg.dependent)
			return "Lii0E";
		return template_value_typeinfo_component(arg);
	}
	if (arg.kind == pa11::TemplateInstanceArgumentKind::Template)
		return to_string(arg.template_name.size()) + arg.template_name;
	string out;
	for (size_t i = 0; i < arg.pack.size(); ++i)
		out += typeinfo_component_for_argument(arg.pack[i]);
	return out;
}

string template_typeinfo_component(TypePtr record)
{
	TypePtr bare = pa11::strip_cv(record);
	string primary = !bare->template_primary_name.empty()
		? bare->template_primary_name
		: (bare->scope != NULL ? bare->scope->name : bare->name);
	string out = to_string(primary.size()) + primary + "I";
	for (size_t i = 0; i < bare->template_arguments.size(); ++i)
		out += typeinfo_component_for_argument(bare->template_arguments[i]);
	out += "E";
	return out;
}

string typeinfo_component_for_type(TypePtr type)
{
	if (type.get() == NULL)
		return "";
	if (type->kind == TypeKind::Cv)
	{
		string prefix;
		if ((type->cv & pa11::CV_CONST) != 0)
			prefix += "K";
		if ((type->cv & pa11::CV_VOLATILE) != 0)
			prefix += "V";
		return prefix + typeinfo_component_for_type(type->base);
	}
	if (type->kind == TypeKind::LValueReference)
		return "R" + typeinfo_component_for_type(type->base);
	if (type->kind == TypeKind::RValueReference)
		return "O" + typeinfo_component_for_type(type->base);
	if (type->kind == TypeKind::Pointer)
		return "P" + typeinfo_component_for_type(type->base);
	if (type->kind == TypeKind::Array)
		return "A" +
		       (type->unknown_bound ? string("") : to_string(type->bound)) +
		       "_" + typeinfo_component_for_type(type->base);
	TypePtr bare = pa11::strip_cv(type);
	if (bare->kind == TypeKind::Fundamental)
	{
		string code = typeinfo_builtin_code(bare->fundamental);
		if (!code.empty())
			return code;
	}
	if (bare->kind == TypeKind::Record &&
	    record_is_template_specialization(bare))
		return template_typeinfo_component(bare);
	if (bare->kind == TypeKind::Record || bare->kind == TypeKind::Enum)
		return to_string(bare->name.size()) + bare->name;
	string name = pa11::describe_type(bare);
	return to_string(name.size()) + name;
}

string typeinfo_name_spelling(TypePtr record)
{
	TypePtr bare = pa11::strip_cv(record);
	vector<string> parts;
	for (Scope* s = bare->scope; s != NULL; s = s->parent)
	{
		if (s->kind != ScopeKind::Namespace && s->kind != ScopeKind::Class)
			continue;
		if (s->name.empty())
			continue;
		if (s->kind == ScopeKind::Class)
		{
			TypePtr scope_record = pa11::record_type_for_scope(s);
			if (scope_record.get() != NULL &&
			    record_is_template_specialization(scope_record))
			{
				parts.push_back(template_typeinfo_component(scope_record));
				continue;
			}
		}
		string name = s->name == "<unnamed>" ? "_GLOBAL__N_1" : s->name;
		parts.push_back(to_string(name.size()) + name);
	}
	if (parts.size() <= 1)
		return typeinfo_component_for_type(bare);
	string out = "N";
	for (size_t i = parts.size(); i > 0; --i)
		out += parts[i - 1];
	out += "E";
	return out;
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
				ostringstream sig;
				sig << "__cxa_pure_virtual " << ret;
				for (size_t j = 0; j < fn->type->parameters.size(); ++j)
					sig << " " << lowir_parameter(fn->type->parameters[j]);
				if (declared_pure_virtual_signatures.insert(sig.str()).second)
				{
					ostringstream decl;
					decl << "declare function @__cxa_pure_virtual(";
					for (size_t j = 0; j < fn->type->parameters.size(); ++j)
					{
						if (j != 0)
							decl << ", ";
						decl << "%arg" << j << " : " <<
							lowir_parameter(fn->type->parameters[j]);
					}
					decl << ") -> " << ret
					     << " [effects=readnone, unwind=no, return=noreturn, "
					     << "binding=strong]";
					declares.push_back(decl.str());
				}
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

}  // namespace internal
}  // namespace pa14
