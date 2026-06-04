#include "pa14_lowir_internal.h"

#include <cctype>
#include <sstream>

namespace pa14 {
namespace internal {

namespace {

string typeinfo_name_symbol(TypePtr record)
{
	TypePtr bare = pa11::strip_cv(record);
	return "__typeinfo_name__" + bare->tag + "_" + record_lowir_name(bare);
}

string trim_template_part(const string& text)
{
	size_t first = 0;
	while (first < text.size() &&
	       isspace(static_cast<unsigned char>(text[first])))
		++first;
	size_t last = text.size();
	while (last > first &&
	       isspace(static_cast<unsigned char>(text[last - 1])))
		--last;
	return text.substr(first, last - first);
}

vector<string> split_template_display_arguments(const string& text)
{
	vector<string> out;
	size_t start = 0;
	int depth = 0;
	for (size_t i = 0; i < text.size(); ++i)
	{
		if (text[i] == '<')
			++depth;
		else if (text[i] == '>')
			--depth;
		else if (text[i] == ',' && depth == 0)
		{
			out.push_back(trim_template_part(text.substr(start, i - start)));
			start = i + 1;
		}
	}
	out.push_back(trim_template_part(text.substr(start)));
	return out;
}

bool decimal_template_value(const string& text)
{
	if (text.empty())
		return false;
	size_t i = text[0] == '-' ? 1 : 0;
	if (i == text.size())
		return false;
	for (; i < text.size(); ++i)
		if (!isdigit(static_cast<unsigned char>(text[i])))
			return false;
	return true;
}

string typeinfo_type_code(const string& type)
{
	if (type == "bool")
		return "b";
	if (type == "char")
		return "c";
	if (type == "signed char")
		return "a";
	if (type == "unsigned char")
		return "h";
	if (type == "short int" || type == "short")
		return "s";
	if (type == "unsigned short int" || type == "unsigned short")
		return "t";
	if (type == "int")
		return "i";
	if (type == "unsigned int" || type == "unsigned")
		return "j";
	if (type == "long int" || type == "long")
		return "l";
	if (type == "unsigned long int" || type == "unsigned long")
		return "m";
	if (type == "long long int" || type == "long long")
		return "x";
	if (type == "unsigned long long int" ||
	    type == "unsigned long long")
		return "y";
	return to_string(type.size()) + type;
}

string template_typeinfo_component(const string& part)
{
	size_t lt = part.find('<');
	size_t gt = part.rfind('>');
	if (lt == string::npos || gt == string::npos || gt < lt)
		return to_string(part.size()) + part;
	string base = part.substr(0, lt);
	vector<string> args =
		split_template_display_arguments(part.substr(lt + 1, gt - lt - 1));
	string out = to_string(base.size()) + base + "I";
	string previous_type_code;
	for (size_t i = 0; i < args.size(); ++i)
	{
		size_t space = args[i].rfind(' ');
		if (space != string::npos && space + 1 < args[i].size())
		{
			string enum_type = trim_template_part(args[i].substr(0, space));
			string value = trim_template_part(args[i].substr(space + 1));
			if (!enum_type.empty() && decimal_template_value(value))
			{
				out += "L" + to_string(enum_type.size()) +
				       enum_type + value + "E";
				continue;
			}
		}
		if (decimal_template_value(args[i]))
		{
			string code = previous_type_code.empty()
				? "i" : previous_type_code;
			out += "L" + code + args[i] + "E";
			continue;
		}
		string code = typeinfo_type_code(args[i]);
		out += code;
		previous_type_code = code;
	}
	out += "E";
	return out;
}

string typeinfo_name_spelling(TypePtr record)
{
	TypePtr bare = pa11::strip_cv(record);
	vector<string> parts;
	size_t start = 0;
	for (;;)
	{
		size_t pos = bare->name.find("::", start);
		string part = pos == string::npos
			? bare->name.substr(start)
			: bare->name.substr(start, pos - start);
		if (!part.empty())
			parts.push_back(part);
		if (pos == string::npos)
			break;
		start = pos + 2;
	}
	if (parts.size() <= 1)
		return template_typeinfo_component(bare->name);
	string out = "N";
	for (size_t i = 0; i < parts.size(); ++i)
		out += template_typeinfo_component(parts[i]);
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
