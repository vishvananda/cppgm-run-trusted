#include "pa14_lowir_internal.h"

#include <fstream>

namespace pa14 {
namespace internal {
namespace {

bool record_has_constructor(TypePtr type)
{
	TypePtr bare = pa11::strip_cv(type);
	if (bare->kind != TypeKind::Record || bare->scope == NULL)
		return false;
	map<string, vector<Binding*> >::const_iterator found =
		bare->scope->members.find(bare->scope->name);
	if (found == bare->scope->members.end())
		return false;
	for (size_t i = 0; i < found->second.size(); ++i)
		if (found->second[i]->kind == BindingKind::Function &&
		    found->second[i]->type->kind == TypeKind::Function)
			return true;
	return false;
}

bool record_has_destructor(TypePtr type)
{
	TypePtr bare = pa11::strip_cv(type);
	if (bare->kind == TypeKind::Array)
		return record_has_destructor(bare->base);
	if (bare->kind != TypeKind::Record)
		return false;
	if (bare->scope != NULL)
	{
		string dtor_name = "~" + bare->scope->name;
		map<string, vector<Binding*> >::const_iterator found =
			bare->scope->members.find(dtor_name);
		if (found != bare->scope->members.end())
			return true;
	}
	pa11::layout_record_type(bare);
	if (bare->base.get() != NULL && record_has_destructor(bare->base))
		return true;
	for (size_t i = 0; i < bare->fields.size(); ++i)
		if (record_has_destructor(bare->fields[i]->type))
			return true;
	return false;
}

bool global_static_scalar_initializer(const Node& init)
{
	if (starts_with(init.line, "literal"))
		return true;
	if (starts_with(init.line, "unary-expression") && init.has_op &&
	    init.op == OP_PLUS && !init.children.empty())
		return global_static_scalar_initializer(init.children[0]);
	if (starts_with(init.line, "binary-expression") && init.has_op &&
	    (init.op == OP_PLUS || init.op == OP_MINUS) &&
	    init.children.size() == 2)
	{
		const Node& lhs = init.children[0];
		const Node& rhs = init.children[1];
		return (lhs.binding != NULL && rhs.has_constant_value) ||
		       (rhs.binding != NULL && lhs.has_constant_value);
	}
	return init.has_constant_value;
}

bool global_needs_runtime_init(TypePtr type, const Node& init)
{
	TypePtr bare = pa11::strip_cv(type);
	if (starts_with(init.line, "constructor-action"))
		return true;
	if (starts_with(init.line, "braced-init-list"))
	{
		if (bare->kind == TypeKind::Record)
			return record_has_constructor(type);
		if (bare->kind == TypeKind::Array)
		{
			for (size_t i = 0; i < init.children.size(); ++i)
				if (global_needs_runtime_init(bare->base, init.children[i]))
					return true;
		}
		return false;
	}
	if (bare->kind == TypeKind::Record || bare->kind == TypeKind::Array)
		return true;
	if (pa11::strip_cv(type)->kind == TypeKind::Pointer &&
	    starts_with(init.line, "id-expression") &&
	    init.binding != NULL &&
	    pa11::strip_cv(init.binding->type)->kind == TypeKind::Array)
		return false;
	return !global_static_scalar_initializer(init);
}

void collect_direct_calls(const Node& node, set<const Binding*>& out)
{
	if (node.direct_call != NULL)
		out.insert(node.direct_call);
	for (size_t i = 0; i < node.children.size(); ++i)
		collect_direct_calls(node.children[i], out);
}

bool contains_call_expression(const Node& node)
{
	if (starts_with(node.line, "call-expression"))
		return true;
	for (size_t i = 0; i < node.children.size(); ++i)
		if (contains_call_expression(node.children[i]))
			return true;
	return false;
}

bool early_hidden_friend_definition(const Node& node,
                                    const set<const Binding*>& direct_calls)
{
	if (node.binding == NULL || !node.binding->is_hidden_friend)
		return false;
	return !contains_call_expression(node) ||
	       direct_calls.find(node.binding) != direct_calls.end();
}

const Binding* first_base_default_constructor(const Binding* binding)
{
	if (binding == NULL || binding->name.empty() || binding->name[0] != '~' ||
	    binding->owner == NULL)
		return NULL;
	TypePtr record = pa11::record_type_for_scope(binding->owner);
	if (record.get() == NULL)
		return NULL;
	pa11::layout_record_type(record);
	if (!record->fields.empty())
		return NULL;
	for (TypePtr base = record->base; base.get() != NULL;
	     base = pa11::strip_cv(base)->base)
	{
		TypePtr bare = pa11::strip_cv(base);
		if (bare->kind != TypeKind::Record || bare->scope == NULL)
			return NULL;
		map<string, vector<Binding*> >::const_iterator found =
			bare->scope->members.find(bare->scope->name);
		if (found != bare->scope->members.end())
			for (size_t i = 0; i < found->second.size(); ++i)
				if (found->second[i]->kind == BindingKind::Function &&
				    found->second[i]->type->kind == TypeKind::Function &&
				    found->second[i]->type->parameters.size() == 1)
					return found->second[i];
	}
	return NULL;
}

}  // namespace

ProgramLowerer::ProgramLowerer()
	: needs_empty_init_function(false),
	  needs_eh_declarations(false)
{
}

string ProgramLowerer::global_scalar_initializer(TypePtr type, const Node& init)
{
	TypePtr bare = pa11::strip_cv(strip_for_value(type));
	if (starts_with(init.line, "literal") && init.token_text == "nullptr")
		return "zero";
	if (starts_with(init.line, "literal") &&
	    init.token_text.size() > 0 &&
	    init.token_text[init.token_text.size() - 1] == '"')
		return "addr @" + string_symbol(init.token_text);
	if (starts_with(init.line, "id-expression") && init.binding != NULL &&
	    scalar_lowir_type(type) == "ptr")
		return "addr @" + symbol_for(init.binding);
	if (starts_with(init.line, "unary-expression") && init.has_op &&
	    init.op == OP_PLUS && !init.children.empty())
		return global_scalar_initializer(type, init.children[0]);
	if (starts_with(init.line, "binary-expression") && init.has_op &&
	    (init.op == OP_PLUS || init.op == OP_MINUS) &&
	    init.children.size() == 2)
	{
		const Node& lhs = init.children[0];
		const Node& rhs = init.children[1];
		const Node* base = lhs.binding != NULL ? &lhs : &rhs;
		const Node* off = lhs.binding != NULL ? &rhs : &lhs;
		if (base->binding != NULL && off->has_constant_value)
		{
			uint64_t scale = 1;
			TypePtr ptr = strip_for_value(base->type);
			if (pa11::strip_cv(ptr)->kind == TypeKind::Pointer)
				scale = pa11::type_size(pa11::strip_cv(ptr)->base);
			int64_t addend = static_cast<int64_t>(off->constant_value * scale);
			if (init.op == OP_MINUS)
				addend = -addend;
			ostringstream out;
			out << "addr @" << symbol_for(base->binding);
			if (addend > 0)
				out << " + " << addend;
			else if (addend < 0)
				out << " - " << -addend;
			return out.str();
		}
	}
	(void)bare;
	return lowir_literal(type, init);
}

string ProgramLowerer::global_data_item(TypePtr elem, const Node& init)
{
	if (scalar_lowir_type(elem) == "ptr")
	{
		string value = global_scalar_initializer(elem, init);
		if (value == "zero")
			return "zero 8";
		return "ptr " + value;
	}
	return scalar_lowir_type(elem) + " " + lowir_literal(elem, init);
}

void ProgramLowerer::emit_global(const Node& node)
{
	if (node.binding == NULL)
		return;
	string name = symbol_for(node.binding);
	defined_globals.insert(name);
	if (node.binding->is_thread_local)
		ensure_thread_local_wrapper(name);
	TypePtr type = node.binding->type;
	ostringstream out;
	TypePtr bare = pa11::strip_cv(type);
	bool runtime_init =
		!node.children.empty() &&
		global_needs_runtime_init(type, node.children[0]);
	if (runtime_init)
		global_init_variables.push_back(node);
	if (record_has_destructor(type))
		global_fini_variables.push_back(node);
	if (bare->kind == TypeKind::Array || bare->kind == TypeKind::Record)
	{
		vector<string> metadata;
		if (node.binding->is_thread_local)
			metadata.push_back("storage=thread_local");
		if (node.binding->language_linkage == "c")
			metadata.push_back("linkage=c");
		metadata.push_back("binding=strong");
		out << "global @" << name << metadata_suffix(metadata) << " = {\n";
		if (runtime_init)
			out << "  zero " << pa11::type_size(type) << "\n";
		else if (bare->kind == TypeKind::Record)
		{
			out << "  zero " << pa11::type_size(type) << "\n";
			needs_empty_init_function = true;
		}
		else
		{
			TypePtr elem = bare->base;
			if (!node.children.empty() &&
			    starts_with(node.children[0].line, "braced-init-list"))
			{
				for (size_t i = 0; i < node.children[0].children.size(); ++i)
					out << "  " << global_data_item(elem, node.children[0].children[i])
					    << "\n";
				if (!bare->unknown_bound)
					for (size_t i = node.children[0].children.size(); i < bare->bound; ++i)
						out << "  zero " << pa11::type_size(elem) << "\n";
			}
			else
				out << "  zero " << pa11::type_size(type) << "\n";
		}
		out << "}";
	}
	else
	{
		vector<string> metadata;
		if (node.binding->is_thread_local)
			metadata.push_back("storage=thread_local");
		if (node.binding->language_linkage == "c")
			metadata.push_back("linkage=c");
		metadata.push_back("binding=strong");
		out << "global @" << name << " : " << scalar_lowir_type(type)
		    << metadata_suffix(metadata) << " = ";
		if (is_reference(type))
		{
			out << "zero";
			if (!node.children.empty())
			{
				const Node& init = node.children[0];
				if (starts_with(init.line, "id-expression") &&
				    init.binding != NULL)
					init_actions.push_back(
						InitAction(name, "addr", symbol_for(init.binding)));
				else if (starts_with(init.line, "unary-expression") &&
				         init.has_op && init.op == OP_STAR &&
				         !init.children.empty() &&
				         init.children[0].binding != NULL)
					init_actions.push_back(
						InitAction(name,
						           "load_ptr",
						           symbol_for(init.children[0].binding)));
			}
		}
		else if (runtime_init || node.children.empty())
			out << "zero";
		else if (starts_with(node.children[0].line, "literal") &&
		         node.children[0].token_text == "nullptr")
			out << "zero";
		else
			out << global_scalar_initializer(type, node.children[0]);
	}
	globals.push_back(out.str());
}

void ProgramLowerer::demand_global_declaration(const Binding* binding)
{
	if (binding == NULL)
		return;
	string name = symbol_for(binding);
	if (binding->is_thread_local)
		ensure_thread_local_wrapper(name);
	if (defined_globals.find(name) != defined_globals.end() ||
	    declared_globals.find(name) != declared_globals.end())
		return;
	ostringstream out;
	out << "declare global @" << name;
	vector<string> metadata;
	if (binding->is_thread_local)
		metadata.push_back("storage=thread_local");
	if (binding->language_linkage == "c")
		metadata.push_back("linkage=c");
	out << metadata_suffix(metadata);
	declared_globals.insert(name);
	global_declares.push_back(out.str());
}

void ProgramLowerer::ensure_thread_local_wrapper(const string& global_name)
{
	string name = global_name + "__tls_wrapper";
	if (declared_functions.find(name) != declared_functions.end() ||
	    defined_functions.find(name) != defined_functions.end())
		return;
	declared_functions.insert(name);
	declares.push_back("declare function @" + name + "() -> ptr");
}

void ProgramLowerer::ensure_eh_declarations()
{
	if (needs_eh_declarations)
		return;
	needs_eh_declarations = true;
	if (declared_functions.insert("__cppgm_eh_resume").second)
		declares.push_back(
			"declare function @__cppgm_eh_resume() -> void [role=eh_resume]");
	if (declared_functions.insert("__cppgm_eh_personality").second)
		declares.push_back(
			"declare function @__cppgm_eh_personality() -> void [role=eh_personality]");
}

void ProgramLowerer::collect_node(const Node& node)
{
	if (starts_with(node.line, "namespace-definition"))
	{
		for (size_t i = 0; i < node.children.size(); ++i)
			collect_node(node.children[i]);
		return;
	}
	if (starts_with(node.line, "variable "))
	{
		if (node.binding != NULL &&
		    ((node.binding->owner != NULL &&
		      node.binding->owner->kind == ScopeKind::Namespace) ||
		     node.binding->is_static_member))
			emit_global(node);
		return;
	}
	if (starts_with(node.line, "function-declaration "))
	{
		if (node.token_text == "deleted")
			return;
		register_function_declaration(node);
		return;
	}
	if (starts_with(node.line, "function-definition "))
	{
		if (node.binding != NULL && node.binding->is_inline_definition)
		{
			register_inline_definition(node);
			return;
		}
		if (node.binding != NULL)
			defined_functions.insert(symbol_for(node.binding));
		FunctionLowerer lowerer(*this, node);
		FunctionOut lowered = lowerer.lower();
		if (node.binding != NULL &&
		    node.binding->owner != NULL &&
		    node.binding->owner->kind == ScopeKind::Class &&
		    node.binding->name == node.binding->owner->name)
		{
			FunctionOut base_entry = lowered;
			string name = symbol_for(node.binding);
			string from = "function @" + name + "(";
			string to = "function @" + name + "__base_entry(";
			size_t pos = base_entry.header.find(from);
			if (pos != string::npos)
				base_entry.header.replace(pos, from.size(), to);
			functions.push_back(base_entry);
		}
		functions.push_back(lowered);
		emit_pending_inline_definitions();
		return;
	}
	for (size_t i = 0; i < node.children.size(); ++i)
		collect_node(node.children[i]);
}

void ProgramLowerer::register_function_declaration(const Node& node)
{
	Binding* binding = node.binding;
	if (binding == NULL)
		return;
	string name = symbol_for(binding);
	if (function_declarations_by_binding.find(binding) !=
	    function_declarations_by_binding.end())
		return;
	ostringstream out;
	out << "declare function @" << name << "(";
	for (size_t i = 0; i < binding->type->parameters.size(); ++i)
	{
		if (i != 0)
			out << ", ";
		out << "%arg" << i << " : "
		    << lowir_parameter(binding->type->parameters[i]);
	}
	out << ") -> " << scalar_lowir_type(binding->type->base);
	vector<string> metadata;
	if (binding->type->variadic)
		metadata.push_back("arity=variadic");
	if (binding->language_linkage == "c")
		metadata.push_back("linkage=c");
	if (binding->unwind_no)
		metadata.push_back("unwind=no");
	metadata.push_back("binding=strong");
	out << metadata_suffix(metadata);
	function_declarations_by_binding[binding] = out.str();
}

void ProgramLowerer::register_inline_definition(const Node& node)
{
	if (node.binding == NULL)
		return;
	symbol_for(node.binding);
	inline_definitions[node.binding] = &node;
}

void ProgramLowerer::demand_function_declaration(const Binding* binding)
{
	if (binding == NULL)
		return;
	string name = symbol_for(binding);
	if (defined_functions.find(name) != defined_functions.end() ||
	    declared_functions.find(name) != declared_functions.end())
		return;
	map<const Binding*, string>::const_iterator found =
		function_declarations_by_binding.find(binding);
	if (found == function_declarations_by_binding.end())
	{
		if (binding->name == "__builtin_strlen")
		{
			declared_functions.insert(name);
			declares.push_back(
				"declare function @__builtin_strlen(%arg0 : ptr "
				"[capture=nocapture, access=read]) -> i64 "
				"[effects=readonly, unwind=no, binding=strong, "
				"object=cppgm_builtin_strlen]");
		}
		else if (binding->name == "__builtin_unreachable")
		{
			declared_functions.insert(name);
			declares.push_back(
				"declare function @__builtin_unreachable() -> void "
				"[effects=readnone, unwind=no, return=noreturn, "
				"binding=strong, object=cppgm_builtin_unreachable]");
		}
		else if (binding->name == "__builtin_memcpy")
		{
			declared_functions.insert(name);
			declares.push_back(
				"declare function @__builtin_memcpy(%arg0 : ptr "
				"[capture=nocapture, access=write, alias=noalias], "
				"%arg1 : ptr [capture=nocapture, access=read, alias=noalias], "
				"%arg2 : i64) -> ptr [effects=readwrite, unwind=no, "
				"binding=strong, object=cppgm_builtin_memcpy]");
		}
		else if (binding->name == "__builtin_memmove")
		{
			declared_functions.insert(name);
			declares.push_back(
				"declare function @__builtin_memmove(%arg0 : ptr "
				"[capture=nocapture, access=readwrite], "
				"%arg1 : ptr [capture=nocapture, access=read], "
				"%arg2 : i64) -> ptr [effects=readwrite, unwind=no, "
				"binding=strong, object=cppgm_builtin_memmove]");
		}
		else
		{
			ostringstream out;
			out << "declare function @" << name << "(";
			for (size_t i = 0; i < binding->type->parameters.size(); ++i)
			{
				if (i != 0)
					out << ", ";
				out << "%arg" << i << " : "
				    << lowir_parameter(binding->type->parameters[i]);
			}
			out << ") -> " << scalar_lowir_type(binding->type->base);
			vector<string> metadata;
			if (binding->type->variadic)
				metadata.push_back("arity=variadic");
			if (binding->language_linkage == "c")
				metadata.push_back("linkage=c");
			if (binding->unwind_no)
				metadata.push_back("unwind=no");
			metadata.push_back("binding=strong");
			out << metadata_suffix(metadata);
			declared_functions.insert(name);
			declares.push_back(out.str());
		}
		return;
	}
	declared_functions.insert(name);
	declares.push_back(found->second);
}

void ProgramLowerer::demand_inline_function(const Binding* binding)
{
	if (binding == NULL || !binding->is_inline_definition)
		return;
	string name = symbol_for(binding);
	if (defined_functions.find(name) != defined_functions.end())
		return;
	for (size_t i = 0; i < pending_inline_definitions.size(); ++i)
		if (pending_inline_definitions[i] == binding)
			return;
	map<const Binding*, const Node*>::const_iterator found =
		inline_definitions.find(binding);
	if (found != inline_definitions.end())
	{
		vector<const Binding*>::iterator pos = pending_inline_definitions.end();
		if (binding->name != "operator[]" &&
		    (binding->name.empty() || binding->name[0] != '~'))
			for (vector<const Binding*>::iterator it =
			     pending_inline_definitions.begin();
			     it != pending_inline_definitions.end(); ++it)
				if ((*it)->name == "operator[]" ||
				    (!(*it)->name.empty() && (*it)->name[0] == '~'))
				{
					pos = it;
					break;
				}
		pending_inline_definitions.insert(pos, binding);
	}
}

void ProgramLowerer::emit_pending_inline_definitions()
{
	while (!pending_inline_definitions.empty())
	{
		const Binding* binding = pending_inline_definitions.front();
		pending_inline_definitions.erase(pending_inline_definitions.begin());
		map<const Binding*, const Node*>::const_iterator found =
			inline_definitions.find(binding);
		if (found == inline_definitions.end())
			continue;
		const Binding* base_ctor = first_base_default_constructor(binding);
		if (base_ctor != NULL &&
		    defined_functions.find(symbol_for(base_ctor)) ==
		    defined_functions.end() &&
		    inline_definitions.find(base_ctor) != inline_definitions.end())
		{
			pending_inline_definitions.insert(pending_inline_definitions.begin(),
			                                  binding);
			demand_inline_function(base_ctor);
			continue;
		}
		string name = symbol_for(binding);
		if (defined_functions.find(name) != defined_functions.end())
			continue;
		defined_functions.insert(name);
		FunctionLowerer lowerer(*this, *found->second);
		functions.push_back(lowerer.lower());
	}
}

void ProgramLowerer::emit_global_lifecycle_functions()
{
	TypePtr void_type = pa11::make_fundamental(FT_VOID);
	TypePtr fn_type = pa11::make_function(void_type, vector<TypePtr>(), false);
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
		for (size_t j = 0; j < string_defs[i].second.size(); ++j)
			out << "  i8 " << static_cast<unsigned>(string_defs[i].second[j]) << "\n";
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
	for (size_t i = 0; i < functions.size(); ++i)
	{
		out << functions[i].header << " {\n";
		for (size_t j = 0; j < functions[i].slots.size(); ++j)
			out << functions[i].slots[j] << "\n";
		if (!functions[i].slots.empty())
			out << "\n";
		for (size_t j = 0; j < functions[i].blocks.size(); ++j)
		{
			if (j != 0)
				out << "\n";
			out << "  block ^" << functions[i].blocks[j].name << ":\n";
			for (size_t k = 0; k < functions[i].blocks[j].instrs.size(); ++k)
				out << functions[i].blocks[j].instrs[k] << "\n";
		}
		out << "}";
		if (i + 1 != functions.size())
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
				out << "    " << tmp << " = load ptr @"
				    << init_actions[i].symbol << "\n";
			else
				out << "    " << tmp << " = addr @"
				    << init_actions[i].symbol << "\n";
			out << "    store ptr " << tmp << ", @"
			    << init_actions[i].target << "\n";
		}
		out << "    return void\n";
		out << "}\n";
	}
}


}  // namespace internal

void emit_lowir(const vector<string>& srcfiles,
                const string& outfile,
                const Options& options)
{
	internal::ProgramLowerer program;
	vector<unique_ptr<pa12::internal::Parser> > parsers;
	for (size_t i = 0; i < srcfiles.size(); ++i)
	{
		pa12::Options pa12_options;
		pa12_options.preprocess = options.preprocess;
		unique_ptr<pa12::internal::Parser> parser(
			new pa12::internal::Parser(srcfiles[i], pa12_options));
		parser->parse_translation_unit();
		const vector<internal::Node>& extra = parser->extra_lowir_nodes();
		set<const pa11::Binding*> direct_calls;
		internal::collect_direct_calls(parser->root(), direct_calls);
		for (size_t j = 0; j < extra.size(); ++j)
			program.register_inline_definition(extra[j]);
		for (size_t j = 0; j < extra.size(); ++j)
		{
			if (!internal::early_hidden_friend_definition(extra[j], direct_calls))
				continue;
			program.demand_inline_function(extra[j].binding);
			program.emit_pending_inline_definitions();
		}
		program.collect_translation_unit(parser->root());
		parsers.push_back(std::move(parser));
	}
	program.emit_global_lifecycle_functions();
	program.write(outfile);
}


}  // namespace pa14
