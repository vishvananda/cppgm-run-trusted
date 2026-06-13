#include "pa14_lowir_internal.h"
#include "pa12_templates_function_support.h"

#include <algorithm>
#include <cctype>
#include <fstream>
#include <set>

namespace pa14 {
namespace internal {

namespace {

bool generated_empty_constructor_binding(const Binding* binding)
{
	return binding != NULL &&
	       (binding->is_generated_default_constructor ||
	        binding->is_generated_aggregate_constructor) &&
	       is_class_constructor_binding(binding) &&
	       binding->type.get() != NULL &&
	       binding->type->kind == TypeKind::Function &&
	       binding->type->parameters.size() == 1;
}

void emit_empty_this_function(ProgramLowerer& program,
                              const string& name,
                              const Binding* binding)
{
	if (binding == NULL ||
	    binding->type.get() == NULL ||
	    binding->type->kind != TypeKind::Function)
		return;
	Node node("function-definition");
	node.binding = const_cast<Binding*>(binding);
	node.type = binding->type;
	const Binding* parameter_name_binding = binding;
	if (parameter_name_binding->function_parameter_names.empty() &&
	    binding->aliased_binding != NULL)
		parameter_name_binding = binding->aliased_binding;
	for (size_t i = 0; i < binding->type->parameters.size(); ++i)
	{
		string pname =
			i < parameter_name_binding->function_parameter_names.size()
			? parameter_name_binding->function_parameter_names[i] : string();
		if (pname.empty())
			pname = i == 0 ? "this" : "__param" + to_string(i);
		Node param("parameter " + pname + " " +
		           pa11::describe_type(binding->type->parameters[i]));
		param.type = binding->type->parameters[i];
		node.children.push_back(param);
	}
	node.children.push_back(Node("compound-statement"));
	FunctionLowerer lowerer(program, node);
	FunctionOut lowered = lowerer.lower();
	lowered.name = name;
	string from = "function @" + program.symbol_for(binding) + "(";
	string to = "function @" + name + "(";
	size_t pos = lowered.header.find(from);
	if (pos != string::npos)
		lowered.header.replace(pos, from.size(), to);
	program.functions.push_back(lowered);
}

bool demand_builtin_declaration(ProgramLowerer& program,
                                const Binding* binding,
                                const string& name)
{
	string declaration;
	if (binding->name == "__builtin_strlen")
		declaration =
			"declare function @__builtin_strlen(%arg0 : ptr "
			"[capture=nocapture, access=read]) -> i64 "
			"[effects=readonly, unwind=no, linkage=c, binding=strong, "
			"object=strlen]";
	else if (binding->name == "__builtin_unreachable")
		declaration =
			"declare function @__builtin_unreachable() -> void "
			"[effects=readnone, unwind=no, return=noreturn, "
			"linkage=c, binding=strong, object=abort]";
	else if (binding->name == "__builtin_memcpy")
		declaration =
			"declare function @__builtin_memcpy(%arg0 : ptr "
			"[capture=nocapture, access=write, alias=noalias], "
			"%arg1 : ptr [capture=nocapture, access=read, alias=noalias], "
			"%arg2 : i64) -> ptr [effects=readwrite, unwind=no, "
			"linkage=c, binding=strong, object=memcpy]";
	else if (binding->name == "__builtin_memmove")
		declaration =
			"declare function @__builtin_memmove(%arg0 : ptr "
			"[capture=nocapture, access=readwrite], "
			"%arg1 : ptr [capture=nocapture, access=read], "
			"%arg2 : i64) -> ptr [effects=readwrite, unwind=no, "
			"linkage=c, binding=strong, object=memmove]";
	else if (binding->name == "__builtin_memset")
		declaration =
			"declare function @__builtin_memset(%arg0 : ptr "
			"[capture=nocapture, access=write], %arg1 : i32, "
			"%arg2 : i64) -> ptr [effects=readwrite, unwind=no, "
			"linkage=c, binding=strong, object=memset]";
	else if (binding->name == "__builtin_strcmp")
		declaration =
			"declare function @__builtin_strcmp(%arg0 : ptr "
			"[capture=nocapture, access=read], "
			"%arg1 : ptr [capture=nocapture, access=read]) -> i32 "
			"[effects=readonly, unwind=no, linkage=c, binding=strong, "
			"object=strcmp]";
	else if (binding->name == "__builtin_memcmp")
		declaration =
			"declare function @__builtin_memcmp(%arg0 : ptr "
			"[capture=nocapture, access=read], "
			"%arg1 : ptr [capture=nocapture, access=read], "
			"%arg2 : i64) -> i32 [effects=readonly, unwind=no, "
			"linkage=c, binding=strong, object=memcmp]";
	else if (binding->name == "__builtin_memchr")
		declaration =
			"declare function @__builtin_memchr(%arg0 : ptr "
			"[capture=nocapture, access=read], %arg1 : i32, "
			"%arg2 : i64) -> ptr [effects=readonly, unwind=no, "
			"linkage=c, binding=strong, object=memchr]";
	else if (binding->name == "__builtin_strchr")
		declaration =
			"declare function @__builtin_strchr(%arg0 : ptr "
			"[capture=nocapture, access=read], %arg1 : i32) -> ptr "
			"[effects=readonly, unwind=no, linkage=c, binding=strong, "
			"object=strchr]";
	else if (binding->name == "__builtin_bzero")
		declaration =
			"declare function @__builtin_bzero(%arg0 : ptr "
			"[capture=nocapture, access=write], %arg1 : i64) -> void "
			"[effects=readwrite, unwind=no, linkage=c, binding=strong, "
			"object=bzero]";
	else if (binding->name.compare(0, 10, "__builtin_") == 0)
	{
		string object = binding->name.substr(10);
		if (object == "fabsf128")
			object = "fabsl";
		ostringstream out;
		out << "declare function @" << name << "(";
		for (size_t i = 0; i < binding->type->parameters.size(); ++i)
		{
			if (i != 0)
				out << ", ";
			out << "%arg" << i << " : "
			    << lowir_parameter(binding->type->parameters[i]);
		}
		out << ") -> " << scalar_lowir_type(binding->type->base)
		    << " [unwind=no, linkage=c, binding=strong, object="
		    << object << "]";
		declaration = out.str();
	}
	else if (binding->owner != NULL && binding->owner->parent == NULL &&
	         binding->name == "operatornew" &&
	         binding->type->parameters.size() == 1)
		declaration =
			"declare function @operator_new(%arg0 : i64) -> ptr "
			"[binding=strong, object=" +
			string(program.native_lowering
			       ? "_Znwm" : "cppgm_builtin_operator_new") + "]";
	else if (binding->owner != NULL && binding->owner->parent == NULL &&
	         binding->name == "operatordelete" &&
	         binding->type->parameters.size() == 1)
		declaration =
			"declare function @operator_delete(%arg0 : ptr) -> void "
			"[unwind=no, binding=strong, object=" +
			string(program.native_lowering
			       ? "_ZdlPv" : "cppgm_builtin_operator_delete") + "]";
	else if (binding->owner != NULL && binding->owner->parent == NULL &&
	         binding->name == "operatornew[]" &&
	         binding->type->parameters.size() == 1)
		declaration =
			"declare function @operator_new__(%arg0 : i64) -> ptr "
			"[binding=strong, object=" +
			string(program.native_lowering
			       ? "_Znam" : "cppgm_builtin_operator_new_array") + "]";
	else if (binding->owner != NULL && binding->owner->parent == NULL &&
	         binding->name == "operatordelete[]" &&
	         binding->type->parameters.size() == 1)
		declaration =
			"declare function @operator_delete__(%arg0 : ptr) -> void "
			"[unwind=no, binding=strong, object=" +
			string(program.native_lowering
			       ? "_ZdaPv" : "cppgm_builtin_operator_delete_array") + "]";
	else
		return false;
	program.declared_functions.insert(name);
	program.declares.push_back(declaration);
	return true;
}

bool demand_generated_empty_constructor(ProgramLowerer& program,
                                        const Binding* binding,
                                        const string& name)
{
	if (!generated_empty_constructor_binding(binding))
		return false;
	if (binding->is_generated_default_constructor &&
	    binding->is_noop_constructor &&
	    !binding->is_object_root)
		return false;
	if (binding->is_inline_definition &&
	    program.inline_definitions.find(binding) != program.inline_definitions.end())
	{
		program.demand_inline_function(binding);
		return true;
	}
	program.emit_generated_empty_constructor(binding, name);
	return true;
}

string ordinary_function_declaration(ProgramLowerer& program,
                                     const Binding* binding,
                                     const string& name)
{
	bool indirect_result =
		pa11::strip_cv(binding->type->base)->kind == TypeKind::Record &&
		record_return_by_address(binding->type->base);
	ostringstream out;
	out << "declare function @" << name << "(";
	if (indirect_result)
		out << "%ret : ptr [pass=indirect_result]";
	for (size_t i = 0; i < binding->type->parameters.size(); ++i)
	{
		if (i != 0 || indirect_result)
			out << ", ";
		out << "%arg" << i << " : "
		    << lowir_parameter(binding->type->parameters[i]);
	}
	size_t hidden_pvb_index = 0;
	bool member_this_param =
		binding->owner != NULL &&
		binding->owner->kind == ScopeKind::Class &&
		!binding->is_static_member &&
		!binding->type->parameters.empty();
	for (size_t i = member_this_param ? 1 : 0;
	     i < binding->type->parameters.size();
	     ++i)
	{
		vector<TypePtr> vbases =
			program.hidden_virtual_bases_for_function_parameter(
				binding, i, binding->type->parameters[i]);
		for (size_t v = 0; v < vbases.size(); ++v)
		{
			if (hidden_pvb_index != 0 ||
			    !binding->type->parameters.empty() ||
			    indirect_result)
				out << ", ";
			out << "%__pvbptr" << hidden_pvb_index++ << " : ptr";
		}
	}
	vector<TypePtr> this_vbases =
		member_this_param &&
		!is_class_constructor_binding(binding) &&
		!is_class_destructor_binding(binding)
		? (binding->is_virtual
		   ? program.hidden_virtual_bases_for_function_parameter(
			   binding, 0, binding->type->parameters[0])
		   : hidden_virtual_bases_for_record(class_record_for_member(binding)))
		: vector<TypePtr>();
	for (size_t v = 0; v < this_vbases.size(); ++v)
	{
		if (hidden_pvb_index != 0 ||
		    !binding->type->parameters.empty() ||
		    indirect_result || v != 0)
			out << ", ";
		out << "%__vbptr" << v << " : ptr";
	}
	out << ") -> " << (indirect_result ? "void" :
	                    scalar_lowir_type(binding->type->base));
	vector<string> metadata;
	if (binding->type->variadic)
		metadata.push_back("arity=variadic");
	if (binding->language_linkage == "c")
		metadata.push_back("linkage=c");
	if (binding->unwind_no)
		metadata.push_back("unwind=no");
	metadata.push_back(binding_has_internal_linkage(binding)
	                   ? "binding=internal" : "binding=strong");
	if (binding->name != "main")
	{
		string object_symbol = binding->language_linkage == "c"
			? binding->name
			: pa12::internal::abi_binding_symbol(
				binding, map<string, size_t>());
		metadata.push_back("object=" + object_symbol);
	}
	out << metadata_suffix(metadata);
	return out.str();
}

string lifecycle_base_entry_declaration(ProgramLowerer& program,
                                        const Binding* binding,
                                        const string& name)
{
	string declaration = ordinary_function_declaration(program, binding, name);
	size_t close = declaration.find(") ->");
	TypePtr record = class_record_for_member(binding);
	record = record.get() != NULL ? pa11::strip_cv(record) : TypePtr();
	if ((is_class_constructor_binding(binding) ||
	     (!program.native_lowering &&
	      is_class_destructor_binding(binding))) &&
	    record.get() != NULL &&
	    record->kind == TypeKind::Record &&
	    record->is_polymorphic &&
	    record_uses_virtual_base_vtt(record))
	{
		size_t this_pos = declaration.find("%arg0 : ptr");
		if (this_pos != string::npos)
			declaration.insert(this_pos + string("%arg0 : ptr").size(),
			                   ", %__vtt : ptr");
		close = declaration.find(") ->");
		vector<TypePtr> vbases = hidden_virtual_bases_for_record(record);
		if (close != string::npos)
		{
			ostringstream hidden;
			for (size_t i = 0; i < vbases.size(); ++i)
				hidden << ", %__vbptr" << i << " : ptr";
			declaration.insert(close, hidden.str());
		}
	}
	size_t object_pos = declaration.find("object=");
	if (object_pos != string::npos)
	{
		const char* complete = is_class_constructor_binding(binding)
			? "C1" : "D1";
		const char* base = is_class_constructor_binding(binding)
			? "C2" : "D2";
		size_t entry_pos = declaration.find(complete, object_pos);
		if (entry_pos != string::npos)
			declaration.replace(entry_pos, 2, base);
	}
	return declaration;
}

void write_function_out(ostream& out, const FunctionOut& fn)
{
	out << fn.header << " {\n";
	for (size_t j = 0; j < fn.slots.size(); ++j)
		out << fn.slots[j] << "\n";
	if (!fn.slots.empty())
		out << "\n";
	for (size_t j = 0; j < fn.blocks.size(); ++j)
	{
		if (j != 0)
			out << "\n";
		out << "  block ^" << fn.blocks[j].name << ":\n";
		for (size_t k = 0; k < fn.blocks[j].instrs.size(); ++k)
			out << fn.blocks[j].instrs[k] << "\n";
	}
	out << "}";
}

bool lowir_symbol_char(char ch)
{
	return std::isalnum(static_cast<unsigned char>(ch)) || ch == '_';
}

bool text_references_symbol(const string& text, const string& name)
{
	string needle = "@" + name;
	size_t pos = 0;
	while ((pos = text.find(needle, pos)) != string::npos)
	{
		size_t after = pos + needle.size();
		if (after == text.size() || !lowir_symbol_char(text[after]))
			return true;
		pos = after;
	}
	return false;
}

bool output_references_function(const ProgramLowerer& program,
                                const string& name,
                                size_t self_index)
{
	for (size_t i = 0; i < program.globals.size(); ++i)
		if (text_references_symbol(program.globals[i], name))
			return true;
	for (size_t i = 0; i < program.functions.size(); ++i)
	{
		if (i == self_index)
			continue;
		const FunctionOut& fn = program.functions[i];
		for (size_t b = 0; b < fn.blocks.size(); ++b)
			for (size_t j = 0; j < fn.blocks[b].instrs.size(); ++j)
				if (text_references_symbol(fn.blocks[b].instrs[j],
				                           name))
					return true;
	}
	return false;
}

bool output_uses_record_as_base(const ProgramLowerer& program,
                                TypePtr base_record)
{
	base_record = base_record.get() != NULL
		? pa11::strip_cv(base_record) : TypePtr();
	if (base_record.get() == NULL || base_record->kind != TypeKind::Record)
		return false;
	for (size_t i = 0; i < program.functions.size(); ++i)
	{
		TypePtr owner = class_record_for_member(program.functions[i].binding);
		owner = owner.get() != NULL ? pa11::strip_cv(owner) : TypePtr();
		if (owner.get() == NULL ||
		    owner->kind != TypeKind::Record ||
		    pa11::same_type(owner, base_record))
			continue;
		if (record_has_base_subobject(owner, base_record))
			return true;
	}
	return false;
}

bool skip_unreferenced_base_entry(const ProgramLowerer& program,
                                  size_t function_index)
{
	if (function_index >= program.functions.size())
		return false;
	const FunctionOut& fn = program.functions[function_index];
	const string& name = fn.name;
	bool generated_lifecycle =
		fn.binding != NULL &&
		(fn.binding->is_generated_default_constructor ||
		 fn.binding->is_generated_aggregate_constructor ||
		 fn.binding->is_generated_default_destructor);
	bool reference_constructor = false;
	if (fn.binding != NULL &&
	    fn.binding->type.get() != NULL &&
	    fn.binding->type->kind == TypeKind::Function)
		for (size_t i = 1; i < fn.binding->type->parameters.size(); ++i)
			if (is_reference(fn.binding->type->parameters[i]))
				reference_constructor = true;
	TypePtr base_constructor_record =
		fn.binding != NULL ? class_record_for_member(fn.binding) : TypePtr();
	base_constructor_record = base_constructor_record.get() != NULL
		? pa11::strip_cv(base_constructor_record) : TypePtr();
	bool template_base_constructor =
		base_constructor_record.get() != NULL &&
		base_constructor_record->kind == TypeKind::Record &&
		base_constructor_record->is_template_specialization;
	bool default_base_constructor =
		fn.binding != NULL &&
		fn.binding->type.get() != NULL &&
		fn.binding->type->kind == TypeKind::Function &&
		fn.binding->type->parameters.size() == 1;
	bool reference_base_constructor =
		reference_constructor && !template_base_constructor;
	bool preserve_base_constructor =
		fn.binding != NULL &&
		is_class_constructor_binding(fn.binding) &&
		fn.binding->type.get() != NULL &&
		fn.binding->type->kind == TypeKind::Function &&
		(!generated_lifecycle ||
		 fn.binding->type->parameters.size() > 1) &&
		((default_base_constructor &&
		  (program.native_lowering || template_base_constructor)) ||
		 reference_base_constructor) &&
		output_uses_record_as_base(program, base_constructor_record);
	return name.find("__base_entry") != string::npos &&
	       fn.binding != NULL &&
	       fn.header.find("binding=weak") != string::npos &&
	       !preserve_base_constructor &&
	       !output_references_function(program, name, function_index);
}

string function_object_symbol(const string& header)
{
	size_t pos = header.find("object=");
	if (pos == string::npos)
		return "";
	pos += 7;
	size_t end = pos;
	while (end < header.size() &&
	       header[end] != ',' &&
	       header[end] != ']')
		++end;
	return header.substr(pos, end - pos);
}

string complete_lifecycle_alias_object(const FunctionOut& fn)
{
	if (fn.name.find("__base_entry") != string::npos ||
	    fn.name.find("__noop_entry") != string::npos ||
	    fn.binding == NULL)
		return "";
	bool ctor = is_class_constructor_binding(fn.binding);
	bool dtor = is_class_destructor_binding(fn.binding);
	if (!ctor && !dtor)
		return "";
	string object = function_object_symbol(fn.header);
	string alias = object;
	string from = ctor ? "C1" : "D1";
	string to = ctor ? "C2" : "D2";
	size_t pos = alias.find(from);
	if (pos == string::npos)
		return "";
	alias.replace(pos, from.size(), to);
	return alias == object ? string() : alias;
}

bool skip_unreferenced_generated_copy_move(const ProgramLowerer& program,
                                           size_t function_index)
{
	if (function_index >= program.functions.size())
		return false;
	const FunctionOut& fn = program.functions[function_index];
	TypePtr record = class_record_for_member(fn.binding);
	record = record.get() != NULL ? pa11::strip_cv(record) : TypePtr();
	return fn.binding != NULL &&
	       fn.binding->is_generated_copy_move_constructor &&
	       record.get() != NULL &&
	       record->is_polymorphic &&
	       !output_references_function(program, fn.name, function_index);
}

string function_header_symbol(const FunctionOut& fn)
{
	size_t at = fn.header.find('@');
	size_t lp = fn.header.find('(', at);
	if (at == string::npos || lp == string::npos || lp <= at + 1)
		return fn.name;
	return fn.header.substr(at + 1, lp - at - 1);
}

bool skip_unreferenced_generated_noop_default(const ProgramLowerer& program,
                                              size_t function_index)
{
	if (function_index >= program.functions.size())
		return false;
	const FunctionOut& fn = program.functions[function_index];
	string symbol = function_header_symbol(fn);
	bool referenced = output_references_function(program,
	                                            symbol,
	                                            function_index);
	return fn.binding != NULL &&
	       fn.binding->is_generated_default_constructor &&
	       !fn.binding->is_defaulted &&
	       fn.binding->is_noop_constructor &&
	       !fn.binding->is_object_root &&
	       !referenced;
}

}  // namespace

void ProgramLowerer::emit_generated_empty_constructor(const Binding* binding,
                                                      const string& name)
{
	if (defined_functions.insert(name).second)
		emit_empty_this_function(*this, name, binding);
}

void ProgramLowerer::demand_function_declaration(const Binding* binding)
{
	if (binding == NULL)
		return;
	if (binding->kind == BindingKind::Function &&
	    binding->aliased_binding != NULL)
	{
		bool binding_has_body =
			inline_definitions.find(binding) != inline_definitions.end() ||
			synthetic_inline_definitions.find(binding) !=
				synthetic_inline_definitions.end();
		bool alias_has_body =
			inline_definitions.find(binding->aliased_binding) !=
				inline_definitions.end() ||
			synthetic_inline_definitions.find(binding->aliased_binding) !=
				synthetic_inline_definitions.end();
		if (binding->aliased_binding->is_inline_definition ||
		    (!binding_has_body && alias_has_body))
			binding = binding->aliased_binding;
	}
	if (inline_definitions.find(binding) == inline_definitions.end() &&
	    synthetic_inline_definitions.find(binding) ==
		    synthetic_inline_definitions.end())
	{
		string wanted_name = symbol_for(binding);
		for (map<const Binding*, const Node*>::const_iterator it =
			     inline_definitions.begin();
		     it != inline_definitions.end();
		     ++it)
		{
			if (it->first == NULL ||
			    it->first->kind != BindingKind::Function ||
			    symbol_for(it->first) != wanted_name)
				continue;
			binding = it->first;
			break;
		}
	}
	if (binding->is_inline_definition)
	{
		demand_inline_function(binding, true);
		string name = symbol_for(binding);
		if (defined_functions.find(name) != defined_functions.end() ||
		    inline_definitions.find(binding) != inline_definitions.end() ||
		    find(pending_inline_definitions.begin(),
		         pending_inline_definitions.end(),
		         binding) != pending_inline_definitions.end())
			return;
		if (declared_functions.find(name) != declared_functions.end())
			return;
		if (demand_builtin_declaration(*this, binding, name))
			return;
		declared_functions.insert(name);
		declares.push_back(ordinary_function_declaration(*this, binding, name));
		return;
	}
	if (inline_definitions.find(binding) != inline_definitions.end())
	{
		demanded_inline_complete_entries.insert(binding);
		insert_pending_inline_definition(binding);
		return;
	}
	string name = symbol_for(binding);
	if (defined_functions.find(name) != defined_functions.end() ||
	    declared_functions.find(name) != declared_functions.end())
		return;
	if (demand_builtin_declaration(*this, binding, name))
		return;
	map<const Binding*, string>::const_iterator found =
		function_declarations_by_binding.find(binding);
	if (found == function_declarations_by_binding.end())
	{
		if (demand_generated_empty_constructor(*this, binding, name))
			return;
		declared_functions.insert(name);
		declares.push_back(ordinary_function_declaration(*this, binding, name));
		return;
	}
	if (demand_generated_empty_constructor(*this, binding, name))
		return;
	declared_functions.insert(name);
	declares.push_back(ordinary_function_declaration(*this, binding, name));
}

void ProgramLowerer::demand_lifecycle_base_entry_declaration(
	const Binding* binding)
{
	if (binding == NULL ||
	    (!is_class_constructor_binding(binding) &&
	     !is_class_destructor_binding(binding)))
		return;
	string name = is_class_constructor_binding(binding)
		? constructor_symbol_for(binding, true)
		: destructor_symbol_for(binding, true);
	if (defined_functions.find(name) != defined_functions.end() ||
	    declared_functions.find(name) != declared_functions.end())
		return;
	if (find(pending_inline_definitions.begin(),
	         pending_inline_definitions.end(),
	         binding) != pending_inline_definitions.end())
		return;
	declared_functions.insert(name);
	declares.push_back(
		lifecycle_base_entry_declaration(*this, binding, name));
}



void ProgramLowerer::emit_global_lifecycle_functions()
{
	TypePtr void_type = pa11::make_fundamental(FT_VOID);
	TypePtr fn_type = pa11::make_function(void_type, vector<TypePtr>(), false);
	for (size_t i = 0; i < thread_local_init_variables.size(); ++i)
	{
		const Node& var = thread_local_init_variables[i];
		if (var.binding == NULL)
			continue;
		string guard = symbol_for(var.binding) + "__tls_guard";
		ensure_thread_local_wrapper(guard);
		globals.push_back("global @" + guard +
		                  " : i64 [storage=thread_local] = zero");
		synthetic_bindings.push_back(unique_ptr<Binding>(
			new Binding(BindingKind::Function,
			            symbol_for(var.binding) + "__tls_init",
			            NULL)));
		Binding* binding = synthetic_bindings.back().get();
		binding->type = fn_type;
		Node fn("function-definition " + binding->name + " " +
		        pa11::describe_type(fn_type));
		fn.binding = binding;
		fn.type = fn_type;
		Node body("compound-statement");
		Node action("thread-local-init-variable");
		action.token_text = guard;
		pa12::internal::add_child(action, var);
		pa12::internal::add_child(body, action);
		pa12::internal::add_child(fn, body);
		string name = symbol_for(binding);
		defined_functions.insert(name);
		FunctionLowerer lowerer(*this, fn);
		functions.push_back(lowerer.lower());
		emit_pending_inline_definitions();
	}
	if (!global_init_variables.empty())
	{
		synthetic_bindings.push_back(unique_ptr<Binding>(
			new Binding(BindingKind::Function, "__cppgm_init", NULL)));
		Binding* binding = synthetic_bindings.back().get();
		binding->type = fn_type;
		Node fn("function-definition __cppgm_init " +
		        pa11::describe_type(fn_type));
		fn.binding = binding;
		fn.type = fn_type;
		Node body("compound-statement");
		for (size_t i = 0; i < global_init_variables.size(); ++i)
		{
			Node action("global-init-variable");
			pa12::internal::add_child(action, global_init_variables[i]);
			pa12::internal::add_child(body, action);
		}
		pa12::internal::add_child(fn, body);
		string name = symbol_for(binding);
		defined_functions.insert(name);
		FunctionLowerer lowerer(*this, fn);
		functions.push_back(lowerer.lower());
		emit_pending_inline_definitions();
	}
	if (!global_fini_variables.empty())
	{
		synthetic_bindings.push_back(unique_ptr<Binding>(
			new Binding(BindingKind::Function, "__cppgm_fini", NULL)));
		Binding* binding = synthetic_bindings.back().get();
		binding->type = fn_type;
		Node fn("function-definition __cppgm_fini " +
		        pa11::describe_type(fn_type));
		fn.binding = binding;
		fn.type = fn_type;
		Node body("compound-statement");
		for (size_t n = 0; n < global_fini_variables.size(); ++n)
		{
			size_t i = global_fini_variables.size() - 1 - n;
			Node action("global-fini-variable");
			pa12::internal::add_child(action, global_fini_variables[i]);
			pa12::internal::add_child(body, action);
		}
		pa12::internal::add_child(fn, body);
		string name = symbol_for(binding);
		defined_functions.insert(name);
		FunctionLowerer lowerer(*this, fn);
		functions.push_back(lowerer.lower());
		emit_pending_inline_definitions();
	}
}

void ProgramLowerer::collect_translation_unit(const Node& root)
{
	for (size_t i = 0; i < root.children.size(); ++i)
		collect_node(root.children[i]);
	emit_pending_inline_definitions();
}

void ProgramLowerer::write(const string& outfile) const
{
	ofstream out(outfile.c_str());
	if (!out)
		throw runtime_error("cannot open output file");
	for (size_t i = 0; i < declares.size(); ++i)
	{
		size_t at = declares[i].find('@');
		size_t lp = declares[i].find('(', at);
		string name = (at == string::npos || lp == string::npos)
			? "" : declares[i].substr(at + 1, lp - at - 1);
		if (defined_functions.find(name) == defined_functions.end())
			out << declares[i] << "\n\n";
	}
	for (size_t i = 0; i < string_defs.size(); ++i)
	{
		out << "global @" << string_defs[i].first << " [binding=internal] = {\n";
		map<string, string>::const_iterator type =
			string_literal_types.find(string_defs[i].first);
		string item_type = type == string_literal_types.end()
			? "i8" : type->second;
		for (size_t j = 0; j < string_defs[i].second.size(); ++j)
			out << "  " << item_type << " " << string_defs[i].second[j] << "\n";
		out << "}\n\n";
	}
	for (size_t i = 0; i < global_declares.size(); ++i)
	{
		size_t at = global_declares[i].find('@');
		size_t end = global_declares[i].find_first_of(" [", at);
		string name = (at == string::npos || end == string::npos)
			? "" : global_declares[i].substr(at + 1, end - at - 1);
		if (defined_globals.find(name) == defined_globals.end())
			out << global_declares[i] << "\n\n";
	}
	for (size_t i = 0; i < globals.size(); ++i)
		out << globals[i] << "\n\n";
	vector<size_t> function_order = ordered_function_indices(*this);
	bool wrote_function = false;
	vector<string> object_aliases;
	set<string> emitted_object_aliases;
	for (size_t order_i = 0; order_i < function_order.size(); ++order_i)
	{
		if (skip_unreferenced_base_entry(*this, function_order[order_i]))
			continue;
		if (skip_unreferenced_generated_copy_move(*this,
		                                          function_order[order_i]))
			continue;
		if (skip_unreferenced_generated_noop_default(*this,
		                                             function_order[order_i]))
			continue;
		if (wrote_function)
			out << "\n";
		const FunctionOut& fn = functions[function_order[order_i]];
		write_function_out(out, fn);
		string alias = complete_lifecycle_alias_object(fn);
		if (!alias.empty() && emitted_object_aliases.insert(alias).second)
			object_aliases.push_back("alias object " + alias +
			                         " = @" + fn.name);
		wrote_function = true;
	}
	if (wrote_function)
		out << "\n";
	for (size_t i = 0; i < object_aliases.size(); ++i)
		out << object_aliases[i] << "\n";
	if ((needs_empty_init_function || !init_actions.empty()) &&
	    defined_functions.find("__cppgm_init") == defined_functions.end())
	{
			if (!functions.empty())
				out << "\n";
			out << "function @__cppgm_init() -> void [role=init, binding=internal] {\n";
		out << "  block ^entry:\n";
		int temp = 0;
		for (size_t i = 0; i < init_actions.size(); ++i)
		{
			++temp;
			string tmp = "%t" + to_string(temp);
				if (init_actions[i].kind == "load_ptr")
					out << "    " << tmp << " = load ptr @" << init_actions[i].symbol << "\n";
				else
					out << "    " << tmp << " = addr @" << init_actions[i].symbol << "\n";
				out << "    store ptr " << tmp << ", @" << init_actions[i].target << "\n";
		}
		out << "    return void\n";
		out << "}\n";
	}
}


}  // namespace internal
}  // namespace pa14
