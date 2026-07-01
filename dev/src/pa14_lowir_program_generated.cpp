#include "pa14_lowir_internal.h"
#include "pa14_lowir_function_internal.h"

#include <cctype>
#include <map>
#include <memory>
#include <sstream>

using namespace std;

namespace pa14 {
namespace internal {
namespace {

bool lowir_symbol_char_local(char ch)
{
	return std::isalnum(static_cast<unsigned char>(ch)) ||
	       ch == '_' ||
	       ch == '$';
}

bool text_references_symbol_local(const string& text, const string& name)
{
	string needle = "@" + name;
	size_t pos = 0;
	while ((pos = text.find(needle, pos)) != string::npos)
	{
		size_t after = pos + needle.size();
		if (after == text.size() || !lowir_symbol_char_local(text[after]))
			return true;
		pos = after;
	}
	return false;
}

bool output_references_function_uncached(const ProgramLowerer& program,
                                         const string& name,
                                         size_t self_index)
{
	for (size_t i = 0; i < program.globals.size(); ++i)
		if (text_references_symbol_local(program.globals[i], name))
			return true;
	for (size_t i = 0; i < program.functions.size(); ++i)
	{
		if (i == self_index)
			continue;
		const FunctionOut& fn = program.functions[i];
		for (size_t b = 0; b < fn.blocks.size(); ++b)
			for (size_t j = 0; j < fn.blocks[b].instrs.size(); ++j)
				if (text_references_symbol_local(fn.blocks[b].instrs[j], name))
					return true;
	}
	return false;
}

string function_header_symbol(const FunctionOut& fn)
{
	size_t at = fn.header.find('@');
	size_t lp = fn.header.find('(', at);
	if (at == string::npos || lp == string::npos || lp <= at + 1)
		return fn.name;
	return fn.header.substr(at + 1, lp - at - 1);
}

bool inline_local_static_binding(const Binding* binding)
{
	return binding != NULL &&
	       binding->is_local_static &&
	       binding->local_static_function_owner != NULL &&
	       binding->local_static_function_owner->is_inline_definition;
}

}  // namespace

namespace {
bool function_out_empty_constructor_body(const FunctionOut& fn)
{
	if (fn.blocks.size() != 1)
		return false;
	for (size_t i = 0; i < fn.blocks[0].instrs.size(); ++i)
	{
		const string& raw = fn.blocks[0].instrs[i];
		size_t first = raw.find_first_not_of(' ');
		const string instr =
			first == string::npos ? string() : raw.substr(first);
		if (instr == "return void")
			continue;
		if (starts_with(instr, "store "))
			continue;
		return false;
	}
	return true;
}

bool noop_base_entry_synthesizable_from_complete(const FunctionOut& fn)
{
	if (!function_out_empty_constructor_body(fn))
		return false;
	const string complete_name = function_header_symbol(fn);
	if (complete_name.empty() ||
	    complete_name.find("__base_entry") != string::npos)
		return false;
	size_t object_pos = fn.header.find("object=");
	if (object_pos == string::npos ||
	    fn.header.find("C1", object_pos) == string::npos)
		return false;
	if (fn.binding == NULL)
		return true;
	if (!is_class_constructor_binding(fn.binding))
		return false;
	TypePtr owner = class_record_for_member(fn.binding);
	owner = owner.get() != NULL ? pa11::strip_cv(owner) : TypePtr();
	if (owner.get() == NULL ||
	    owner->kind != TypeKind::Record ||
	    owner->is_polymorphic ||
	    !pa11::record_virtual_bases(owner).empty())
		return false;
	return fn.binding->is_noop_constructor ||
	       lowir_synthesizable_noop_constructor(fn.binding) ||
	       function_out_empty_constructor_body(fn);
}

bool output_has_function_header_named(const ProgramLowerer& program,
                                      const string& name)
{
	for (size_t i = 0; i < program.functions.size(); ++i)
		if (function_header_symbol(program.functions[i]) == name)
			return true;
	return false;
}

bool allocator_constructor_symbol(const string& name)
{
	return starts_with(name, "_ZNSa") &&
	       name.find("__base_entry") == string::npos &&
	       (name.find("C1") != string::npos ||
	        name.find("C2") != string::npos);
}

bool extract_call_symbol_and_arity(const string& instr,
                                   string& symbol,
                                   size_t& arity)
{
	size_t call = instr.find("call ");
	if (call == string::npos)
		return false;
	size_t at = instr.find('@', call);
	size_t lp = instr.find('(', at);
	size_t rp = instr.find(')', lp);
	if (at == string::npos ||
	    lp == string::npos ||
	    rp == string::npos ||
	    lp <= at + 1)
		return false;
	symbol = instr.substr(at + 1, lp - at - 1);
	string args = instr.substr(lp + 1, rp - lp - 1);
	size_t first = args.find_first_not_of(" \t");
	if (first == string::npos)
	{
		arity = 0;
		return true;
	}
	arity = 1;
	for (size_t pos = first; pos < args.size(); ++pos)
		if (args[pos] == ',')
			++arity;
	return true;
}

void collect_missing_allocator_constructor_calls(const ProgramLowerer& program,
                                                 map<string, size_t>& out)
{
	for (size_t i = 0; i < program.functions.size(); ++i)
		for (size_t b = 0; b < program.functions[i].blocks.size(); ++b)
			for (size_t j = 0;
			     j < program.functions[i].blocks[b].instrs.size();
			     ++j)
			{
				string symbol;
				size_t arity = 0;
				if (!extract_call_symbol_and_arity(
					    program.functions[i].blocks[b].instrs[j],
					    symbol,
					    arity))
					continue;
				if (!allocator_constructor_symbol(symbol))
					continue;
				if (program.declared_functions.find(symbol) !=
					    program.declared_functions.end() ||
				    output_has_function_header_named(program, symbol))
					continue;
				out[symbol] = arity;
			}
}

FunctionOut make_allocator_noop_constructor(const string& name, size_t arity)
{
	if (arity == 0)
		arity = 1;
	FunctionOut out;
	out.name = name;
	ostringstream header;
	header << "function @" << name << "(";
	for (size_t i = 0; i < arity; ++i)
	{
		if (i != 0)
			header << ", ";
		header << (i == 0 ? "%this" : "%__a" + to_string(i))
		       << " : ptr";
		if (i != 0)
			header << " [pass=reference]";
	}
	header << ") -> void [unwind=no, binding=weak, object=" << name << "]";
	out.header = header.str();
	Block block("entry");
	block.instrs.push_back("    return void");
	block.terminated = true;
	out.blocks.push_back(block);
	return out;
}

}  // namespace

void ProgramLowerer::emit_referenced_allocator_noop_constructors()
{
	if (!host_object_lowering)
		return;
	map<string, size_t> missing;
	collect_missing_allocator_constructor_calls(*this, missing);
	for (map<string, size_t>::const_iterator it = missing.begin();
	     it != missing.end();
	     ++it)
	{
		if (declared_functions.find(it->first) !=
			    declared_functions.end() ||
		    output_has_function_header_named(*this, it->first))
			continue;
		defined_functions.insert(it->first);
		functions.push_back(
			make_allocator_noop_constructor(it->first, it->second));
	}
}

namespace {
FunctionOut make_noop_constructor_base_entry_from_complete(
	const FunctionOut& complete,
	const string& complete_name,
	const string& base_name)
{
	FunctionOut out = complete;
	out.name = base_name;
	string from = "function @" + complete_name + "(";
	string to = "function @" + base_name + "(";
	size_t pos = out.header.find(from);
	if (pos != string::npos)
		out.header.replace(pos, from.size(), to);
	size_t object_pos = out.header.find("object=");
	if (object_pos != string::npos)
	{
		size_t ctor_pos = out.header.find("C1", object_pos);
		if (ctor_pos != string::npos)
			out.header.replace(ctor_pos, 2, "C2");
	}
	return out;
}
}  // namespace

void ProgramLowerer::emit_referenced_noop_constructor_base_entries()
{
	if (!host_object_lowering)
		return;
	bool changed = true;
	while (changed)
	{
		changed = false;
		const size_t count = functions.size();
		for (size_t i = 0; i < count; ++i)
		{
			const FunctionOut& fn = functions[i];
			if (!noop_base_entry_synthesizable_from_complete(fn))
				continue;
			const string complete_name = function_header_symbol(fn);
			if (complete_name.empty())
				continue;
			const string base_name = complete_name + "__base_entry";
			if (output_has_function_header_named(*this, base_name))
				continue;
			if (!output_references_function_uncached(*this, base_name, i))
				continue;
			defined_functions.insert(base_name);
			functions.push_back(
				make_noop_constructor_base_entry_from_complete(
					fn, complete_name, base_name));
			changed = true;
		}
	}
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
		bool inline_local_static = inline_local_static_binding(var.binding);
		string guard = symbol_for(var.binding) + "__tls_guard";
		ensure_thread_local_wrapper(guard);
		vector<string> guard_metadata;
		guard_metadata.push_back("storage=thread_local");
		if (inline_local_static)
			guard_metadata.push_back("binding=weak");
		globals.push_back("global @" + guard + " : i64 " +
		                  metadata_suffix(guard_metadata) + " = zero");
		synthetic_bindings.push_back(unique_ptr<Binding>(
			new Binding(BindingKind::Function,
			            symbol_for(var.binding) + "__tls_init",
			            NULL)));
		Binding* binding = synthetic_bindings.back().get();
		binding->type = fn_type;
		if (inline_local_static)
			binding->is_inline_definition = true;
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
}  // namespace internal
}  // namespace pa14
