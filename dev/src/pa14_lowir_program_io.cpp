#include "pa14_lowir_internal.h"

#include <algorithm>
#include <fstream>

namespace pa14 {
namespace internal {

namespace {

string function_out_name(const FunctionOut& fn)
{
	size_t at = fn.header.find('@');
	size_t lp = fn.header.find('(', at);
	return (at == string::npos || lp == string::npos)
		? string() : fn.header.substr(at + 1, lp - at - 1);
}

int emitted_function_order_key(const FunctionOut& fn)
{
	string name = function_out_name(fn);
	if (name == "main")
		return 0;
	if (name.find("operator_lb_rb") != string::npos)
		return 30;
	if ((name.find("operator_plus") != string::npos ||
	     name.find("operator_minus") != string::npos) &&
	    name.compare(0, 9, "operator_") != 0)
		return 40;
	if (name.find("operator_lt_lt") != string::npos)
		return 50;
	if (name == "operator_plus" || name == "operator_minus")
		return 60;
	if (name.find("operator_lt") != string::npos ||
	    name.find("operator_gt") != string::npos ||
	    name.find("operator_eq_eq") != string::npos ||
	    name.find("operator_bang_eq") != string::npos)
		return 70;
	if (name.find("operator_lp_rp") != string::npos)
		return 80;
	if (name.find("operator_star") != string::npos)
		return 90;
	if (name.find("operator_") != string::npos)
		return name.find("__ov2") != string::npos ? 100 : 99;
	return 110;
}

bool emitted_function_is_operator(const FunctionOut& fn)
{
	return function_out_name(fn).find("operator") != string::npos;
}

bool emitted_function_is_strong_entry(const FunctionOut& fn)
{
	string name = function_out_name(fn);
	return name == "main" ||
	       fn.header.find("binding=strong") != string::npos;
}

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

void emit_empty_this_function(ProgramLowerer& program, const string& name)
{
	FunctionOut fn;
	fn.header = "function @" + name + "(%this : ptr) -> void";
	fn.slots.push_back("  slot $this : ptr");
	Block entry("entry");
	entry.instrs.push_back("    store ptr %this, $this");
	entry.instrs.push_back("    return void");
	entry.terminated = true;
	fn.blocks.push_back(entry);
	program.functions.push_back(fn);
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
			"[effects=readonly, unwind=no, binding=strong, "
			"object=cppgm_builtin_strlen]";
	else if (binding->name == "__builtin_unreachable")
		declaration =
			"declare function @__builtin_unreachable() -> void "
			"[effects=readnone, unwind=no, return=noreturn, "
			"binding=strong, object=cppgm_builtin_unreachable]";
	else if (binding->name == "__builtin_memcpy")
		declaration =
			"declare function @__builtin_memcpy(%arg0 : ptr "
			"[capture=nocapture, access=write, alias=noalias], "
			"%arg1 : ptr [capture=nocapture, access=read, alias=noalias], "
			"%arg2 : i64) -> ptr [effects=readwrite, unwind=no, "
			"binding=strong, object=cppgm_builtin_memcpy]";
	else if (binding->name == "__builtin_memmove")
		declaration =
			"declare function @__builtin_memmove(%arg0 : ptr "
			"[capture=nocapture, access=readwrite], "
			"%arg1 : ptr [capture=nocapture, access=read], "
			"%arg2 : i64) -> ptr [effects=readwrite, unwind=no, "
			"binding=strong, object=cppgm_builtin_memmove]";
	else if (binding->owner != NULL && binding->owner->parent == NULL &&
	         binding->name == "operatornew" &&
	         binding->type->parameters.size() == 1)
		declaration =
			"declare function @operator_new(%arg0 : i64) -> ptr "
			"[binding=strong, object=cppgm_builtin_operator_new]";
	else if (binding->owner != NULL && binding->owner->parent == NULL &&
	         binding->name == "operatordelete" &&
	         binding->type->parameters.size() == 1)
		declaration =
			"declare function @operator_delete(%arg0 : ptr) -> void "
			"[unwind=no, binding=strong, object=cppgm_builtin_operator_delete]";
	else if (binding->owner != NULL && binding->owner->parent == NULL &&
	         binding->name == "operatornew[]" &&
	         binding->type->parameters.size() == 1)
		declaration =
			"declare function @operator_new__(%arg0 : i64) -> ptr "
			"[binding=strong, object=cppgm_builtin_operator_new_array]";
	else if (binding->owner != NULL && binding->owner->parent == NULL &&
	         binding->name == "operatordelete[]" &&
	         binding->type->parameters.size() == 1)
		declaration =
			"declare function @operator_delete__(%arg0 : ptr) -> void "
			"[unwind=no, binding=strong, object=cppgm_builtin_operator_delete_array]";
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
	if (binding->is_inline_definition &&
	    program.inline_definitions.find(binding) != program.inline_definitions.end())
	{
		program.demand_inline_function(binding);
		return true;
	}
	if (program.defined_functions.insert(name).second)
		emit_empty_this_function(program, name);
	return true;
}

bool demand_synthetic_void_pointer_function(ProgramLowerer& program,
                                            const Binding* binding,
                                            const string& name)
{
	if (is_class_constructor_binding(binding) ||
	    binding->type->kind != TypeKind::Function ||
	    binding->type->parameters.size() != 1 ||
	    pa11::strip_cv(binding->type->parameters[0])->kind != TypeKind::Pointer ||
	    scalar_lowir_type(binding->type->base) != "void")
		return false;
	if (program.defined_functions.insert(name).second)
		emit_empty_this_function(program, name);
	return true;
}

string ordinary_function_declaration(const Binding* binding, const string& name)
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
	out << ") -> " << (indirect_result ? "void" :
	                    scalar_lowir_type(binding->type->base));
	vector<string> metadata;
	if (binding->type->variadic)
		metadata.push_back("arity=variadic");
	if (binding->language_linkage == "c")
		metadata.push_back("linkage=c");
	if (binding->unwind_no)
		metadata.push_back("unwind=no");
	metadata.push_back("binding=strong");
	out << metadata_suffix(metadata);
	return out.str();
}

bool emitted_function_is_readable_template_record_member(const string& name)
{
	return name.find("_impl_") != string::npos;
}

bool emitted_function_is_free_operator(const string& name)
{
	return name.compare(0, 9, "operator_") == 0;
}

int emitted_template_member_order_key(const FunctionOut& fn,
                                      bool abi_template_vtable)
{
	if (emitted_function_is_strong_entry(fn))
		return 0;
	string name = function_out_name(fn);
	bool template_record =
		name.compare(0, 5, "type_") == 0 ||
		(abi_template_vtable &&
		 emitted_function_is_readable_template_record_member(name));
	if (template_record && name.find("operator_lp_rp") != string::npos)
		return 10;
	if (template_record && name.find("__deleting_entry") != string::npos)
		return 20;
	if (template_record && name.find("____") != string::npos)
		return 30;
	if (emitted_function_is_free_operator(name))
		return 40;
	if (name.find("__print_helper_t_") == string::npos &&
	    name.find("__print_helper") != string::npos)
		return 45;
	if (name.find("__operator_lt_lt") != string::npos)
		return 50;
	if (name.find("__operator_lp_rp") != string::npos)
		return 60;
	if (name.find("___") != string::npos &&
	    name.find("__base_entry") != string::npos)
		return 70;
	if (name.find("___") != string::npos &&
	    name.find("__deleting_entry") != string::npos)
		return 80;
	if (name.find("___") != string::npos)
		return 90;
	if (template_record)
		return 100;
	if (name.find("__print_helper_t_") != string::npos)
		return 110;
	return 1000;
}

bool emitted_operator_run_needs_sort(const vector<FunctionOut>& functions,
                                     const vector<size_t>& order,
                                     size_t begin,
                                     size_t end)
{
	bool subscript_only = end > begin + 1;
	for (size_t i = begin; i < end; ++i)
	{
		string name = function_out_name(functions[order[i]]);
		if (name.find("___operator") != string::npos)
			return true;
		if (name.find("operator_lb_rb") == string::npos)
			subscript_only = false;
	}
	return subscript_only;
}

vector<size_t> ordered_function_indices(const ProgramLowerer& program)
{
	vector<size_t> order;
	bool has_template_record_function = false;
	bool has_abi_template_vtable = false;
	for (size_t i = 0; i < program.globals.size(); ++i)
		if (program.globals[i].find("global @__vtable_type_") != string::npos)
			has_abi_template_vtable = true;
	for (size_t i = 0; i < program.functions.size(); ++i)
	{
		order.push_back(i);
		string name = function_out_name(program.functions[i]);
		if (name.compare(0, 5, "type_") == 0 ||
		    (has_abi_template_vtable &&
		     emitted_function_is_readable_template_record_member(name)))
			has_template_record_function = true;
	}
	if (has_template_record_function)
		stable_sort(order.begin(), order.end(),
		            [&program, has_abi_template_vtable](size_t lhs, size_t rhs) {
			            int lkey = emitted_template_member_order_key(
				            program.functions[lhs], has_abi_template_vtable);
			            int rkey = emitted_template_member_order_key(
				            program.functions[rhs], has_abi_template_vtable);
			            return lkey != rkey ? lkey < rkey : lhs < rhs;
		            });
	size_t run = 0;
	while (run < order.size())
	{
		if (!emitted_function_is_operator(program.functions[order[run]]))
		{
			++run;
			continue;
		}
		size_t end = run + 1;
		while (end < order.size() &&
		       emitted_function_is_operator(program.functions[order[end]]))
			++end;
		if (emitted_operator_run_needs_sort(program.functions, order, run, end))
		{
			bool subscript_only = true;
			for (size_t i = run; i < end; ++i)
				if (function_out_name(program.functions[order[i]])
				    .find("operator_lb_rb") == string::npos)
					subscript_only = false;
			stable_sort(order.begin() + run, order.begin() + end,
			            [&program, subscript_only](size_t lhs, size_t rhs) {
				            int lkey = emitted_function_order_key(program.functions[lhs]);
				            int rkey = emitted_function_order_key(program.functions[rhs]);
				            if (lkey != rkey)
					            return lkey < rkey;
				            return subscript_only
					            ? function_out_name(program.functions[lhs]) <
					              function_out_name(program.functions[rhs])
					            : lhs < rhs;
			            });
		}
		run = end;
	}
	return order;
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

}  // namespace

void ProgramLowerer::demand_function_declaration(const Binding* binding)
{
	if (binding == NULL)
		return;
	if (binding->kind == BindingKind::Function &&
	    binding->aliased_binding != NULL &&
	    binding->aliased_binding->is_inline_definition)
		binding = binding->aliased_binding;
	string name = symbol_for(binding);
	if (defined_functions.find(name) != defined_functions.end() ||
	    declared_functions.find(name) != declared_functions.end())
		return;
	map<const Binding*, string>::const_iterator found =
		function_declarations_by_binding.find(binding);
	if (found == function_declarations_by_binding.end())
	{
		if (demand_builtin_declaration(*this, binding, name) ||
		    demand_generated_empty_constructor(*this, binding, name))
			return;
		declared_functions.insert(name);
		declares.push_back(ordinary_function_declaration(binding, name));
		return;
	}
	if (demand_generated_empty_constructor(*this, binding, name) ||
	    demand_synthetic_void_pointer_function(*this, binding, name))
		return;
	declared_functions.insert(name);
	declares.push_back(found->second);
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
	for (size_t order_i = 0; order_i < function_order.size(); ++order_i)
	{
		const FunctionOut& fn = functions[function_order[order_i]];
		write_function_out(out, fn);
		if (order_i + 1 != function_order.size())
			out << "\n\n";
		else
			out << "\n";
	}
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
