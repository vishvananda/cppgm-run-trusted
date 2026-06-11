#include "pa14_lowir_internal.h"

#include <cctype>
#include <sstream>

namespace pa14 {
namespace internal {

namespace {

string typeinfo_name_symbol(TypePtr record)
{
	TypePtr bare = pa11::strip_cv(record);
	if (template_record_uses_abi_global_symbol(bare))
		return "__typeinfo_name_" + template_record_global_symbol_part(bare);
	return "__typeinfo_name__" + bare->tag + "_" +
	       rtti_record_symbol_part(bare);
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
	if (type == FT_INT128)
		return "n";
	if (type == FT_UNSIGNED_INT128)
		return "o";
	if (type == FT_FLOAT)
		return "f";
	if (type == FT_DOUBLE)
		return "d";
	if (type == FT_LONG_DOUBLE)
		return "e";
	if (type == FT_WCHAR_T)
		return "w";
	if (type == FT_CHAR16_T)
		return "Ds";
	if (type == FT_CHAR32_T)
		return "Di";
	return "";
}

string typeinfo_builtin_part(TypePtr type)
{
	string part = pa11::describe_type(pa11::strip_cv(type));
	for (size_t i = 0; i < part.size(); ++i)
		if (part[i] == ' ')
			part[i] = '_';
	return part;
}

string typeinfo_component_for_type(TypePtr type);

bool typeinfo_argument_incomplete(
	const pa11::TemplateInstanceArgument& arg);

bool typeinfo_type_incomplete(TypePtr type)
{
	if (type.get() == NULL)
		return false;
	TypePtr bare = pa11::strip_cv(type);
	if (bare->kind == TypeKind::Array)
		return bare->unknown_bound || typeinfo_type_incomplete(bare->base);
	if (bare->kind == TypeKind::Pointer ||
	    bare->kind == TypeKind::LValueReference ||
	    bare->kind == TypeKind::RValueReference)
		return typeinfo_type_incomplete(bare->base);
	if (bare->kind == TypeKind::Record)
	{
		if (!bare->complete)
			return true;
		for (size_t i = 0; i < bare->template_arguments.size(); ++i)
			if (typeinfo_argument_incomplete(bare->template_arguments[i]))
				return true;
	}
	return false;
}

bool typeinfo_argument_incomplete(
	const pa11::TemplateInstanceArgument& arg)
{
	if (arg.kind == pa11::TemplateInstanceArgumentKind::Type)
		return typeinfo_type_incomplete(arg.type);
	for (size_t i = 0; i < arg.pack.size(); ++i)
		if (typeinfo_argument_incomplete(arg.pack[i]))
			return true;
	return false;
}

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
	string out = "J";
	for (size_t i = 0; i < arg.pack.size(); ++i)
		out += typeinfo_component_for_argument(arg.pack[i]);
	out += "E";
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

string lambda_typeinfo_name_spelling(TypePtr record)
{
	TypePtr bare = pa11::strip_cv(record);
	if (bare.get() == NULL ||
	    bare->kind != TypeKind::Record ||
	    bare->scope == NULL ||
	    bare->scope->name.compare(0, 8, "__lambda") != 0)
		return "";
	map<string, vector<Binding*> >::const_iterator found =
		bare->scope->members.find("operator()");
	if (found == bare->scope->members.end())
		return "";
	for (size_t i = 0; i < found->second.size(); ++i)
	{
		Binding* op = found->second[i];
		if (op == NULL ||
		    op->function_specialization_symbol.compare(0, 3, "_ZZ") != 0)
			continue;
		string symbol = op->function_specialization_symbol;
		size_t call = symbol.rfind("_clE");
		if (call == string::npos)
			continue;
		string prefix = symbol.substr(3, call - 3);
		size_t lambda = prefix.rfind("Ul");
		if (lambda == string::npos)
			continue;
		string context;
		if (lambda >= 3 &&
		    prefix.compare(lambda - 3, 3, "ENK") == 0)
			context = prefix.substr(0, lambda - 2);
		else if (lambda >= 2 &&
		         prefix.compare(lambda - 2, 2, "EN") == 0)
			context = prefix.substr(0, lambda - 1);
		else
			continue;
		string lambda_component = prefix.substr(lambda);
		if (lambda_component.empty() ||
		    lambda_component[lambda_component.size() - 1] != '_')
			lambda_component += "_";
		return "Z" + context + lambda_component;
	}
	return "";
}

string typeinfo_name_spelling(TypePtr record)
{
	TypePtr bare = pa11::strip_cv(record);
	string lambda_name = lambda_typeinfo_name_spelling(bare);
	if (!lambda_name.empty())
		return lambda_name;
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

bool typeinfo_object_metadata_safe(const string& spelling)
{
	if (spelling.empty())
		return false;
	for (size_t i = 0; i < spelling.size(); ++i)
		if (std::isspace(static_cast<unsigned char>(spelling[i])) ||
		    spelling[i] == ',' ||
		    spelling[i] == ']')
			return false;
	return true;
}

void append_typeinfo_name_global(vector<string>& globals, TypePtr record)
{
	string name = typeinfo_name_spelling(record);
	ostringstream out;
	out << "global @" << typeinfo_name_symbol(record)
	    << " [storage=readonly, binding=weak";
	if (typeinfo_object_metadata_safe(name))
		out << ", object=_ZTS" << name;
	out << "] = {\n";
	for (size_t i = 0; i < name.size(); ++i)
		out << "  i8 " << static_cast<unsigned>(
			static_cast<unsigned char>(name[i])) << "\n";
	out << "  i8 0\n";
	out << "}";
	globals.push_back(out.str());
}

string typeinfo_name_symbol_for_type(TypePtr type)
{
	TypePtr bare = pa11::strip_cv(type);
	if (bare->kind == TypeKind::Record)
		return typeinfo_name_symbol(bare);
	if (bare->kind == TypeKind::Fundamental)
		return "__typeinfo_name__" + typeinfo_builtin_part(bare);
	return "__typeinfo_name_type_" + typeinfo_component_for_type(bare);
}

void append_typeinfo_name_global_for_type(vector<string>& globals,
                                          TypePtr type)
{
	TypePtr bare = pa11::strip_cv(type);
	string spelling = typeinfo_component_for_type(bare);
	ostringstream out;
	out << "global @" << typeinfo_name_symbol_for_type(bare)
	    << " [storage=readonly, binding=weak";
	if (typeinfo_object_metadata_safe(spelling))
		out << ", object=_ZTS" << spelling;
	out << "] = {\n";
	for (size_t i = 0; i < spelling.size(); ++i)
		out << "  i8 " << static_cast<unsigned>(
			static_cast<unsigned char>(spelling[i])) << "\n";
	out << "  i8 0\n";
	out << "}";
	globals.push_back(out.str());
}

void emit_incomplete_record_typeinfo(ProgramLowerer& program, TypePtr record)
{
	TypePtr bare = pa11::strip_cv(record);
	if (bare->kind != TypeKind::Record)
		return;
	string rtti_symbol = rtti_symbol_for_record(bare);
	if (!program.defined_globals.insert(rtti_symbol).second)
		return;
	if (program.declared_globals.insert(
		    "__external_rtti_vtable____class_type_info").second)
		program.global_declares.push_back(
			"declare global @__external_rtti_vtable____class_type_info "
			"[binding=strong, object=_ZTVN10__cxxabiv117__class_type_infoE]");
	if (program.defined_globals.insert(typeinfo_name_symbol(bare)).second)
		append_typeinfo_name_global(program.globals, bare);
	ostringstream out;
	string spelling = typeinfo_name_spelling(bare);
	out << "global @" << rtti_symbol
	    << " [storage=readonly, binding=weak";
	if (typeinfo_object_metadata_safe(spelling))
		out << ", object=_ZTI" << spelling;
	out << "] = {\n";
	out << "  ptr addr @__external_rtti_vtable____class_type_info + 16\n";
	out << "  ptr addr @" << typeinfo_name_symbol(bare) << "\n";
	out << "}";
	program.globals.push_back(out.str());
}

}  // namespace

void ProgramLowerer::emit_rtti(TypePtr record)
{
	TypePtr bare = pa11::strip_cv(record);
	if (bare->kind != TypeKind::Record)
		return;
	string rtti_symbol = rtti_symbol_for_record(bare);
	if (!defined_globals.insert(rtti_symbol).second)
		return;
	if (declared_globals.insert("__external_rtti_vtable____class_type_info").second)
		global_declares.push_back(
			"declare global @__external_rtti_vtable____class_type_info "
			"[binding=strong, object=_ZTVN10__cxxabiv117__class_type_infoE]");
	pa11::layout_record_type(bare);
	vector<TypePtr> direct_bases = pa11::record_direct_bases(bare);
	vector<TypePtr> record_bases;
	for (size_t i = 0; i < direct_bases.size(); ++i)
	{
		TypePtr base = direct_bases[i].get() != NULL
			? pa11::strip_cv(direct_bases[i]) : TypePtr();
		if (base.get() != NULL && base->kind == TypeKind::Record)
			record_bases.push_back(base);
	}
	bool static_downcast_needs_base_offset = false;
	for (size_t i = 0; i < record_bases.size(); ++i)
		if (pa11::record_direct_base_offset(bare, record_bases[i]) != 0 &&
		    is_static_downcast_source_record(record_bases[i]))
			static_downcast_needs_base_offset = true;
	bool use_si = record_bases.size() == 1 &&
	              !static_downcast_needs_base_offset &&
	              (bare->direct_base_virtuals.empty() ||
	               !bare->direct_base_virtuals[0]);
	if (use_si)
	{
		if (declared_globals.insert(
			    "__external_rtti_vtable____si_class_type_info").second)
			global_declares.push_back(
				"declare global @__external_rtti_vtable____si_class_type_info "
				"[binding=strong, object=_ZTVN10__cxxabiv120__si_class_type_infoE]");
	}
	else if (!record_bases.empty())
	{
		if (declared_globals.insert(
			    "__external_rtti_vtable____vmi_class_type_info").second)
			global_declares.push_back(
				"declare global @__external_rtti_vtable____vmi_class_type_info "
				"[binding=strong, object=_ZTVN10__cxxabiv121__vmi_class_type_infoE]");
	}
	if (defined_globals.insert(typeinfo_name_symbol(bare)).second)
		append_typeinfo_name_global(globals, bare);
	for (size_t i = 0; i < record_bases.size(); ++i)
		emit_rtti(record_bases[i]);
	ostringstream out;
	string spelling = typeinfo_name_spelling(bare);
	out << "global @" << rtti_symbol
	    << " [storage=readonly, binding=weak";
	if (typeinfo_object_metadata_safe(spelling))
		out << ", object=_ZTI" << spelling;
	out << "] = {\n";
	if (use_si)
	{
		out << "  ptr addr @__external_rtti_vtable____si_class_type_info + 16\n";
		out << "  ptr addr @" << typeinfo_name_symbol(bare) << "\n";
		out << "  ptr addr @" << rtti_symbol_for_record(record_bases[0]) << "\n";
	}
	else if (!record_bases.empty())
	{
		out << "  ptr addr @__external_rtti_vtable____vmi_class_type_info + 16\n";
		out << "  ptr addr @" << typeinfo_name_symbol(bare) << "\n";
		out << "  i32 0\n";
		out << "  i32 " << record_bases.size() << "\n";
		for (size_t i = 0; i < record_bases.size(); ++i)
		{
			uint64_t offset =
				pa11::record_direct_base_offset(bare, record_bases[i]);
			bool is_virtual = i < bare->direct_base_virtuals.size() &&
			                  bare->direct_base_virtuals[i];
			int64_t flags = is_virtual ? -6141 :
			                static_cast<int64_t>(offset * 256 + 2);
			out << "  ptr addr @" << rtti_symbol_for_record(record_bases[i])
			    << "\n";
			out << "  i64 " << flags << "\n";
		}
	}
	else
	{
		out << "  ptr addr @__external_rtti_vtable____class_type_info + 16\n";
		out << "  ptr addr @" << typeinfo_name_symbol(bare) << "\n";
	}
	out << "}";
	globals.push_back(out.str());
}

void ProgramLowerer::emit_typeinfo(TypePtr type)
{
	TypePtr bare = pa11::strip_cv(type);
	if (bare->kind == TypeKind::Record)
	{
		emit_rtti(bare);
		return;
	}
	if (bare->kind == TypeKind::Pointer)
	{
		string component = typeinfo_component_for_type(bare);
		string rtti_symbol = "__rtti_type_" + component;
		if (!defined_globals.insert(rtti_symbol).second)
			return;
		if (declared_globals.insert(
			    "__external_rtti_vtable____pointer_type_info").second)
			global_declares.push_back(
				"declare global @__external_rtti_vtable____pointer_type_info "
				"[binding=strong, object=_ZTVN10__cxxabiv119__pointer_type_infoE]");
		string name_symbol = typeinfo_name_symbol_for_type(bare);
		if (defined_globals.insert(name_symbol).second)
			append_typeinfo_name_global_for_type(globals, bare);
		bool incomplete_pointee = typeinfo_type_incomplete(bare->base);
		TypePtr pointee = pa11::strip_cv(bare->base);
		if (incomplete_pointee &&
		    pointee->kind == TypeKind::Record)
			emit_incomplete_record_typeinfo(*this, pointee);
		else
			emit_typeinfo(bare->base);
		ostringstream rtti;
		rtti << "global @" << rtti_symbol
		     << " [storage=readonly, binding=weak, object=_ZTI"
		     << component << "] = {\n";
		rtti << "  ptr addr @__external_rtti_vtable____pointer_type_info + 16\n";
		rtti << "  ptr addr @" << name_symbol << "\n";
		rtti << "  i32 " << (incomplete_pointee ? 8 : 0) << "\n";
		rtti << "  ptr addr @" << typeid_rtti_symbol(bare->base) << "\n";
		rtti << "}";
		globals.push_back(rtti.str());
		return;
	}
	if (bare->kind == TypeKind::Fundamental)
	{
		string code = typeinfo_builtin_code(bare->fundamental);
		if (code.empty())
			return;
		string part = typeinfo_builtin_part(bare);
		string rtti_symbol = "__rtti_" + part;
		if (!defined_globals.insert(rtti_symbol).second)
			return;
		if (declared_globals.insert(
			    "__external_rtti_vtable____fundamental_type_info").second)
			global_declares.push_back(
				"declare global @__external_rtti_vtable____fundamental_type_info "
				"[binding=strong, "
				"object=_ZTVN10__cxxabiv123__fundamental_type_infoE]");
		string name_symbol = "__typeinfo_name__" + part;
		if (defined_globals.insert(name_symbol).second)
		{
			ostringstream name;
			name << "global @" << name_symbol
			     << " [storage=readonly, binding=weak, object=_ZTS" << code
			     << "] = {\n";
			for (size_t i = 0; i < code.size(); ++i)
				name << "  i8 " << static_cast<unsigned>(
					static_cast<unsigned char>(code[i])) << "\n";
			name << "  i8 0\n}";
			globals.push_back(name.str());
		}
		ostringstream rtti;
		rtti << "global @" << rtti_symbol
		     << " [storage=readonly, binding=weak, object=_ZTI" << code
		     << "] = {\n";
		rtti << "  ptr addr @__external_rtti_vtable____fundamental_type_info + 16\n";
		rtti << "  ptr addr @" << name_symbol << "\n";
		rtti << "}";
		globals.push_back(rtti.str());
	}
}

string ProgramLowerer::typeid_rtti_symbol(TypePtr type)
{
	TypePtr bare = pa11::strip_cv(type);
	if (bare->kind == TypeKind::Record)
		return rtti_symbol_for_record(bare);
	if (bare->kind == TypeKind::Fundamental)
		return "__rtti_" + typeinfo_builtin_part(bare);
	if (bare->kind == TypeKind::Pointer)
		return "__rtti_type_" + typeinfo_component_for_type(bare);
	return "";
}

string ProgramLowerer::catch_rtti_symbol(TypePtr type)
{
	TypePtr bare = pa11::strip_cv(type);
	if (bare->kind == TypeKind::Record)
		return rtti_symbol_for_record(bare);
	if (bare->kind == TypeKind::Fundamental)
	{
		string code = typeinfo_builtin_code(bare->fundamental);
		if (code.empty())
			return "";
		string external = "__external_rtti__" + typeinfo_builtin_part(bare);
		if (declared_globals.insert(external).second)
			global_declares.push_back(
				"declare global @" + external +
				" [binding=strong, object=_ZTI" + code + "]");
		return "__external_rtti__" + typeinfo_builtin_part(bare);
	}
	return "";
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
	out.binding = dtor;
	out.name = name;
	string object = !dtor->function_specialization_symbol.empty()
		? dtor->function_specialization_symbol : global_object_symbol(dtor);
	if (object.empty() &&
	    dtor->aliased_binding != NULL &&
	    !dtor->aliased_binding->function_specialization_symbol.empty())
		object = dtor->aliased_binding->function_specialization_symbol;
	size_t dtor_entry = object.rfind("D1E");
	if (dtor_entry != string::npos)
		object.replace(dtor_entry, 3, "D0E");
	out.header = "function @" + name + "(%this : ptr) -> void [binding=weak";
	if (!object.empty())
		out.header += ", object=" + object;
	out.header += "]";
	const Node* inline_node = NULL;
	map<const Binding*, const Node*>::const_iterator found_inline =
		inline_definitions.find(dtor);
	if (found_inline != inline_definitions.end())
		inline_node = found_inline->second;
	else if (dtor->aliased_binding != NULL)
	{
		found_inline = inline_definitions.find(dtor->aliased_binding);
		if (found_inline != inline_definitions.end())
			inline_node = found_inline->second;
	}
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
			vtable_view_symbol_for_record(bare,
			                              views[i].first,
			                              views[i].second));
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
			vector<string> args;
			args.push_back(base_addr);
			if (base.get() != NULL &&
			    base->kind == TypeKind::Record &&
			    base->is_polymorphic &&
			    record_uses_virtual_base_vtt(base))
			{
				size_t vtt_slot =
					construction_vtt_slot_for_direct_base(record, base);
				if (vtt_slot != static_cast<size_t>(-1))
				{
					string vtt_base = "%t" + to_string(temp++);
					block.instrs.push_back(
						"    " + vtt_base + " = addr @" +
						vtt_symbol_for_record(record));
					string vtt_arg = vtt_base;
					if (vtt_slot != 0)
					{
						vtt_arg = "%t" + to_string(temp++);
						block.instrs.push_back(
							"    " + vtt_arg +
							" = index i8 " + vtt_base +
							", " + to_string(vtt_slot * 8));
					}
					args.push_back(vtt_arg);
				}
			}
			vector<TypePtr> vbases = hidden_virtual_bases_for_record(base);
			for (size_t v = 0; v < vbases.size(); ++v)
			{
				string hidden = "0";
				if (record_has_base_subobject(record, vbases[v]))
				{
					string this_ptr = "%t" + to_string(temp++);
					block.instrs.push_back("    " + this_ptr +
					                       " = load ptr $this");
					uint64_t offset = base_subobject_offset(record,
					                                        vbases[v]);
					if (offset == 0)
						hidden = this_ptr;
					else
					{
						hidden = "%t" + to_string(temp++);
						block.instrs.push_back("    " + hidden +
						                       " = index i8 " +
						                       this_ptr + ", " +
						                       to_string(offset));
					}
				}
				args.push_back(hidden);
			}
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
	}
	string del_arg = "%t" + to_string(temp++);
	block.instrs.push_back("    " + del_arg + " = load ptr $this");
	block.instrs.push_back("    call void @operator_delete(" + del_arg + ")");
	block.instrs.push_back("    return void");
	block.terminated = true;
	out.blocks.push_back(block);
	functions.push_back(out);
}

namespace {

bool vtable_signature_matches(const Binding* base, const Binding* derived)
{
	if (base == NULL || derived == NULL ||
	    base->type.get() == NULL || derived->type.get() == NULL ||
	    base->type->kind != TypeKind::Function ||
	    derived->type->kind != TypeKind::Function)
		return false;
	if (is_class_destructor_binding(base) && is_class_destructor_binding(derived))
		return true;
	if (base->name != derived->name ||
	    base->type->parameters.size() != derived->type->parameters.size())
		return false;
	for (size_t i = 1; i < base->type->parameters.size(); ++i)
		if (!pa11::same_type(base->type->parameters[i],
		                     derived->type->parameters[i]))
			return false;
	return pa11::same_type(base->type->base, derived->type->base);
}

Binding* find_vtable_overrider(TypePtr record, Binding* fn)
{
	TypePtr bare = pa11::strip_cv(record);
	if (bare->kind != TypeKind::Record || bare->scope == NULL)
		return fn;
	Binding* best = fn;
	for (size_t i = 0; i < bare->scope->binding_order.size(); ++i)
	{
		Binding* member = bare->scope->binding_order[i];
		if (member == NULL ||
		    member->kind != BindingKind::Function ||
		    member->is_static_member ||
		    member->name == bare->scope->name)
			continue;
		if (vtable_signature_matches(fn, member))
			best = member;
	}
	return best;
}

string pure_virtual_entry(ProgramLowerer& program, Binding* fn)
{
	if (program.declared_functions.insert("__cxa_pure_virtual").second)
	{
		string ret = scalar_lowir_type(fn->type->base);
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
		program.declares.push_back(decl.str());
	}
	return "__cxa_pure_virtual";
}

string emit_adjustor_thunk(ProgramLowerer& program,
                           Binding* fn,
                           int64_t delta,
                           bool deleting_entry)
{
	string callee = deleting_entry
		? program.symbol_for(fn) + "__deleting_entry"
		: program.symbol_for(fn);
	string name = "_" + callee + "__vtable_return_adjust";
	if (program.defined_functions.find(name) != program.defined_functions.end())
		return name;
	program.defined_functions.insert(name);
	if (deleting_entry)
		program.emit_deleting_destructor_entry(fn);
	else
	{
		program.demand_function_declaration(fn);
		program.demand_inline_function(fn);
	}
	FunctionOut out;
	out.binding = fn;
	out.name = name;
	TypePtr fn_type = fn->type;
	string ret = scalar_lowir_type(fn_type->base);
	out.header = "function @" + name + "(";
	for (size_t i = 0; i < fn_type->parameters.size(); ++i)
	{
		if (i != 0)
			out.header += ", ";
		out.header += "%arg" + to_string(i) + " : " +
		              lowir_parameter(fn_type->parameters[i]);
	}
	out.header += ") -> " + ret + " [binding=weak]";
	Block block("entry");
	string adjusted = "%t1";
	ostringstream index;
	index << "    " << adjusted << " = index i8 %arg0, ";
	if (delta < 0)
		index << "-" << static_cast<uint64_t>(-delta);
	else
		index << static_cast<uint64_t>(delta);
	block.instrs.push_back(index.str());
	ostringstream call;
	if (ret != "void")
		call << "    %t2 = ";
	else
		call << "    ";
	call << "call " << ret << " @" << callee << "(" << adjusted;
	for (size_t i = 1; i < fn_type->parameters.size(); ++i)
		call << ", %arg" << i;
	call << ")";
	block.instrs.push_back(call.str());
	if (ret == "void")
		block.instrs.push_back("    return void");
	else
		block.instrs.push_back("    return " + ret + " %t2");
	block.terminated = true;
	out.blocks.push_back(block);
	program.functions.push_back(out);
	return name;
}

string vtable_entry_symbol(ProgramLowerer& program,
                           TypePtr record,
                           TypePtr view_base,
                           uint64_t view_offset,
                           const pa11::VirtualTableEntry& entry,
                           bool separate_adjustment_word)
{
	Binding* fn = entry.function;
	if (fn == NULL)
		return "";
	Binding* target = find_vtable_overrider(record, fn);
	if (target->is_pure_virtual)
		return pure_virtual_entry(program, target);
	TypePtr owner = class_record_for_member(target);
	owner = owner.get() != NULL ? pa11::strip_cv(owner) : TypePtr();
	uint64_t owner_offset = 0;
	if (owner.get() != NULL &&
	    owner->kind == TypeKind::Record &&
	    !pa11::same_type(owner, pa11::strip_cv(record)))
		owner_offset = base_subobject_offset(record, owner);
	int64_t delta = static_cast<int64_t>(owner_offset) -
	                static_cast<int64_t>(view_offset);
	if (entry.deleting_entry)
	{
		if (delta != 0 && !separate_adjustment_word)
			return emit_adjustor_thunk(program, target, delta, true);
		program.emit_deleting_destructor_entry(target);
		return program.symbol_for(target) + "__deleting_entry";
	}
	if (delta != 0 && !separate_adjustment_word)
		return emit_adjustor_thunk(program, target, delta, false);
	program.demand_function_declaration(target);
	program.demand_inline_function(target);
	return program.symbol_for(target);
}

bool record_uses_virtual_base_vtable_shape(TypePtr record)
{
	TypePtr bare = record.get() != NULL ? pa11::strip_cv(record) : TypePtr();
	return bare.get() != NULL && bare->kind == TypeKind::Record &&
	       !pa11::record_virtual_bases(bare).empty();
}

uint64_t first_virtual_base_offset(TypePtr record)
{
	TypePtr bare = record.get() != NULL ? pa11::strip_cv(record) : TypePtr();
	if (bare.get() == NULL || bare->kind != TypeKind::Record)
		return 0;
	vector<TypePtr> vbases = pa11::record_virtual_bases(bare);
	if (vbases.empty())
		return 0;
	return pa11::record_virtual_base_offset(bare, vbases[0]);
}

bool entry_owner_is_virtual_base_slot(TypePtr record,
                                      const pa11::VirtualTableEntry& entry)
{
	if (entry.function == NULL)
		return false;
	TypePtr owner = class_record_for_member(entry.function);
	owner = owner.get() != NULL ? pa11::strip_cv(owner) : TypePtr();
	TypePtr bare = record.get() != NULL ? pa11::strip_cv(record) : TypePtr();
	if (owner.get() == NULL || owner->kind != TypeKind::Record ||
	    bare.get() == NULL || bare->kind != TypeKind::Record)
		return false;
	vector<TypePtr> vbases = pa11::record_virtual_bases(bare);
	for (size_t i = 0; i < vbases.size(); ++i)
	{
		TypePtr vbase = pa11::strip_cv(vbases[i]);
		if (pa11::same_type(vbase, owner) ||
		    record_has_base_subobject(vbase, owner))
			return true;
	}
	return false;
}

void emit_vtable_entries(ProgramLowerer& program,
                         ostringstream& out,
                         TypePtr dispatch_record,
                         TypePtr view_base,
                         uint64_t view_offset,
                         bool virtual_base_shape,
                         bool primary_view)
{
	for (size_t i = 0; i < view_base->virtual_entries.size(); ++i)
	{
		bool skip_virtual_base_slot =
			virtual_base_shape &&
			(primary_view ||
			 !pa11::record_virtual_bases(view_base).empty()) &&
			entry_owner_is_virtual_base_slot(primary_view
			                                ? dispatch_record
			                                : view_base,
			                                view_base->virtual_entries[i]);
		if (skip_virtual_base_slot)
			continue;
		bool separate_adjustment_word =
			virtual_base_shape &&
			!pa11::record_virtual_bases(view_base).empty();
		string entry = vtable_entry_symbol(program,
		                                   dispatch_record,
		                                   view_base,
		                                   view_offset,
		                                   view_base->virtual_entries[i],
		                                   separate_adjustment_word);
		if (!entry.empty())
		{
			out << "  ptr addr @" << entry << "\n";
			if (separate_adjustment_word)
				out << "  i64 " << (view_offset == 0 ? 0 :
				                    -static_cast<int64_t>(view_offset))
				    << "\n";
		}
	}
}

bool record_is_virtual_base_of(TypePtr record, TypePtr base)
{
	TypePtr bare = record.get() != NULL ? pa11::strip_cv(record) : TypePtr();
	TypePtr wanted = base.get() != NULL ? pa11::strip_cv(base) : TypePtr();
	if (bare.get() == NULL || bare->kind != TypeKind::Record ||
	    wanted.get() == NULL || wanted->kind != TypeKind::Record)
		return false;
	vector<TypePtr> vbases = pa11::record_virtual_bases(bare);
	for (size_t i = 0; i < vbases.size(); ++i)
		if (pa11::same_type(pa11::strip_cv(vbases[i]), wanted))
			return true;
	return false;
}

uint64_t construction_view_complete_offset(TypePtr complete,
                                           TypePtr subobject,
                                           uint64_t subobject_offset,
                                           TypePtr view_base,
                                           uint64_t local_view_offset)
{
	TypePtr complete_bare = pa11::strip_cv(complete);
	if (record_is_virtual_base_of(subobject, view_base))
	{
		vector<TypePtr> vbases = pa11::record_virtual_bases(complete_bare);
		for (size_t i = 0; i < vbases.size(); ++i)
			if (pa11::same_type(pa11::strip_cv(vbases[i]),
			                    pa11::strip_cv(view_base)))
				return pa11::record_virtual_base_offset(complete_bare,
				                                        view_base);
	}
	return subobject_offset + local_view_offset;
}

void append_address_point_reference(vector<string>& refs,
                                    TypePtr table_record,
                                    const string& symbol)
{
	refs.push_back(symbol + " + " +
	               to_string(vtable_address_point_offset(table_record)));
}

void emit_construction_primary_vtable(ProgramLowerer& program,
                                      TypePtr complete,
                                      TypePtr subobject,
                                      uint64_t subobject_offset)
{
	TypePtr complete_bare = pa11::strip_cv(complete);
	TypePtr sub_bare = pa11::strip_cv(subobject);
	string symbol = construction_vtable_symbol_for_record(complete_bare,
	                                                      sub_bare,
	                                                      subobject_offset,
	                                                      0);
	if (!program.defined_globals.insert(symbol).second)
		return;
	program.emit_rtti(sub_bare);
	ostringstream out;
	out << "global @" << symbol
	    << " [storage=readonly, binding=weak] = {\n";
	int64_t first = static_cast<int64_t>(
		first_virtual_base_offset(complete_bare)) -
		static_cast<int64_t>(subobject_offset);
	out << "  i64 " << first << "\n";
	out << "  i64 " << (subobject_offset == 0 ? 0 :
	                    -static_cast<int64_t>(subobject_offset)) << "\n";
	out << "  ptr addr @" << rtti_symbol_for_record(sub_bare) << "\n";
	emit_vtable_entries(program,
	                    out,
	                    sub_bare,
	                    sub_bare,
	                    0,
	                    true,
	                    true);
	out << "}";
	program.globals.push_back(out.str());
}

void emit_construction_view_vtable(ProgramLowerer& program,
                                   TypePtr complete,
                                   TypePtr subobject,
                                   uint64_t subobject_offset,
                                   TypePtr view_base,
                                   uint64_t local_view_offset,
                                   size_t slice)
{
	TypePtr complete_bare = pa11::strip_cv(complete);
	TypePtr sub_bare = pa11::strip_cv(subobject);
	TypePtr view_bare = pa11::strip_cv(view_base);
	uint64_t complete_view_offset =
		construction_view_complete_offset(complete_bare,
		                                  sub_bare,
		                                  subobject_offset,
		                                  view_bare,
		                                  local_view_offset);
	string symbol = construction_vtable_symbol_for_record(complete_bare,
	                                                      sub_bare,
	                                                      subobject_offset,
	                                                      slice);
	if (!program.defined_globals.insert(symbol).second)
		return;
	program.emit_rtti(view_bare);
	ostringstream out;
	out << "global @" << symbol
	    << " [storage=readonly, binding=weak] = {\n";
	int64_t first = record_is_virtual_base_of(sub_bare, view_bare)
		? 0
		: static_cast<int64_t>(first_virtual_base_offset(complete_bare)) -
		  static_cast<int64_t>(complete_view_offset);
	out << "  i64 " << first << "\n";
	out << "  i64 " << (complete_view_offset == 0 ? 0 :
	                    -static_cast<int64_t>(complete_view_offset))
	    << "\n";
	out << "  ptr addr @" << rtti_symbol_for_record(view_bare) << "\n";
	emit_vtable_entries(program,
	                    out,
	                    sub_bare,
	                    view_bare,
	                    local_view_offset,
	                    true,
	                    false);
	out << "}";
	program.globals.push_back(out.str());
}

void append_construction_vtable_group(ProgramLowerer& program,
                                      TypePtr complete,
                                      TypePtr subobject,
                                      uint64_t subobject_offset,
                                      vector<string>& refs)
{
	TypePtr sub_bare = pa11::strip_cv(subobject);
	if (!record_uses_virtual_base_vtable_shape(sub_bare) ||
	    !sub_bare->is_polymorphic)
		return;
	emit_construction_primary_vtable(program,
	                                 complete,
	                                 sub_bare,
	                                 subobject_offset);
	append_address_point_reference(
		refs,
		sub_bare,
		construction_vtable_symbol_for_record(complete,
		                                      sub_bare,
		                                      subobject_offset,
		                                      0));
	vector<TypePtr> direct_bases = pa11::record_direct_bases(sub_bare);
	for (size_t i = 0; i < direct_bases.size(); ++i)
	{
		if (pa11::record_direct_base_is_virtual(sub_bare, i))
			continue;
		TypePtr direct = direct_bases[i].get() != NULL
			? pa11::strip_cv(direct_bases[i]) : TypePtr();
		if (direct.get() == NULL || direct->kind != TypeKind::Record ||
		    !direct->is_polymorphic ||
		    !record_uses_virtual_base_vtable_shape(direct))
			continue;
		uint64_t direct_offset = subobject_offset +
			pa11::record_direct_base_offset(sub_bare, direct);
		append_construction_vtable_group(program,
		                                 complete,
		                                 direct,
		                                 direct_offset,
		                                 refs);
	}
	vector<pair<TypePtr, uint64_t> > views =
		vtt_ordered_vtable_views(sub_bare);
	for (size_t i = 0; i < views.size(); ++i)
	{
		emit_construction_view_vtable(program,
		                              complete,
		                              sub_bare,
		                              subobject_offset,
		                              views[i].first,
		                              views[i].second,
		                              i + 1);
		append_address_point_reference(
			refs,
			sub_bare,
			construction_vtable_symbol_for_record(complete,
			                                      sub_bare,
			                                      subobject_offset,
			                                      i + 1));
	}
}

void emit_vtt(ProgramLowerer& program, TypePtr record)
{
	TypePtr bare = pa11::strip_cv(record);
	if (!record_uses_virtual_base_vtable_shape(bare) ||
	    !bare->is_polymorphic)
		return;
	string symbol = vtt_symbol_for_record(bare);
	if (!program.defined_globals.insert(symbol).second)
		return;
	vector<string> refs;
	append_address_point_reference(refs, bare, vtable_symbol_for_record(bare));
	vector<TypePtr> direct_bases = pa11::record_direct_bases(bare);
	for (size_t i = 0; i < direct_bases.size(); ++i)
	{
		if (pa11::record_direct_base_is_virtual(bare, i))
			continue;
		TypePtr direct = direct_bases[i].get() != NULL
			? pa11::strip_cv(direct_bases[i]) : TypePtr();
		if (direct.get() == NULL || direct->kind != TypeKind::Record ||
		    !direct->is_polymorphic ||
		    !record_uses_virtual_base_vtable_shape(direct))
			continue;
		uint64_t offset = pa11::record_direct_base_offset(bare, direct);
		append_construction_vtable_group(program,
		                                 bare,
		                                 direct,
		                                 offset,
		                                 refs);
	}
	vector<pair<TypePtr, uint64_t> > views = vtt_ordered_vtable_views(bare);
	for (size_t i = 0; i < views.size(); ++i)
		append_address_point_reference(
			refs,
			bare,
			vtable_view_symbol_for_record(bare,
			                              views[i].first,
			                              views[i].second));
	ostringstream out;
	out << "global @" << symbol << " [storage=readonly, binding=weak] = {\n";
	for (size_t i = 0; i < refs.size(); ++i)
		out << "  ptr addr @" << refs[i] << "\n";
	out << "}";
	program.globals.push_back(out.str());
}

}  // namespace

void ProgramLowerer::demand_vtable(TypePtr record, bool include_bases)
{
	TypePtr bare = pa11::strip_cv(record);
	if (bare->kind != TypeKind::Record || !bare->is_polymorphic)
		return;
	if (emitted_vtables.find(bare.get()) != emitted_vtables.end())
		return;
	vector<TypePtr> direct_bases = pa11::record_direct_bases(bare);
	if (include_bases)
	{
		for (size_t i = 0; i < direct_bases.size(); ++i)
		{
			TypePtr direct_base = direct_bases[i].get() != NULL
				? pa11::strip_cv(direct_bases[i]) : TypePtr();
			if (direct_base.get() != NULL &&
			    direct_base->kind == TypeKind::Record &&
			    direct_base->is_polymorphic)
				demand_vtable(direct_base);
		}
	}
	emitted_vtables.insert(bare.get());
	Binding* virtual_dtor = find_destructor(bare);
	if (virtual_dtor != NULL &&
	    virtual_dtor->is_virtual &&
	    record_uses_virtual_base_vtt(bare))
	{
		destructor_symbol_for(virtual_dtor, true);
		demand_inline_function(virtual_dtor, false);
		if (bare->scope != NULL)
		{
			map<string, vector<Binding*> >::const_iterator ctors =
				bare->scope->members.find(bare->scope->name);
			if (ctors != bare->scope->members.end())
				for (size_t i = 0; i < ctors->second.size(); ++i)
					if (is_class_constructor_binding(ctors->second[i]))
					{
						constructor_symbol_for(ctors->second[i], true);
						demand_inline_function(ctors->second[i], false);
					}
		}
	}
	emit_rtti(bare);
	bool virtual_base_shape = record_uses_virtual_base_vtable_shape(bare);
	ostringstream out;
	out << "global @" << vtable_symbol_for_record(bare)
	    << " [storage=readonly, binding=weak] = {\n";
	if (virtual_base_shape)
		out << "  i64 " << first_virtual_base_offset(bare) << "\n";
	out << "  i64 0\n";
	out << "  ptr addr @" << rtti_symbol_for_record(bare) << "\n";
	emit_vtable_entries(*this, out, bare, bare, 0, virtual_base_shape, true);
	out << "}";
	globals.push_back(out.str());
	vector<pair<TypePtr, uint64_t> > views = polymorphic_vtable_views(bare);
	for (size_t v = 0; v < views.size(); ++v)
	{
		TypePtr view_base = pa11::strip_cv(views[v].first);
		uint64_t view_offset = views[v].second;
		ostringstream view;
		view << "global @"
		     << vtable_view_symbol_for_record(bare, view_base, view_offset)
		     << " [storage=readonly, binding=weak, object=@"
		     << vtable_view_symbol_for_record(bare, view_base, view_offset)
		     << "] = {\n";
		if (virtual_base_shape)
		{
			uint64_t vbase_offset = first_virtual_base_offset(bare);
			bool virtual_view = false;
			vector<TypePtr> vbases = pa11::record_virtual_bases(bare);
			for (size_t i = 0; i < vbases.size(); ++i)
				if (pa11::same_type(pa11::strip_cv(vbases[i]), view_base))
					virtual_view = true;
			int64_t first = virtual_view ? 0 :
				static_cast<int64_t>(vbase_offset) -
				static_cast<int64_t>(view_offset);
			view << "  i64 " << first << "\n";
			view << "  i64 -" << view_offset << "\n";
			view << "  ptr addr @" << rtti_symbol_for_record(bare) << "\n";
		}
		emit_vtable_entries(*this,
		                    view,
		                    bare,
		                    view_base,
		                    view_offset,
		                    virtual_base_shape,
		                    false);
		view << "}";
		globals.push_back(view.str());
	}
	emit_vtt(*this, bare);
}

}  // namespace internal
}  // namespace pa14
