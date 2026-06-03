#include "pa14_lowir_internal.h"

#include <fstream>

namespace pa14 {
namespace internal {

ProgramLowerer::ProgramLowerer()
	: needs_empty_init_function(false)
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
	if (starts_with(init.line, "id-expression") && init.binding != NULL)
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
	TypePtr type = node.binding->type;
	ostringstream out;
	TypePtr bare = pa11::strip_cv(type);
	if (bare->kind == TypeKind::Array || bare->kind == TypeKind::Record)
	{
		vector<string> metadata;
		if (node.binding->language_linkage == "c")
			metadata.push_back("linkage=c");
		metadata.push_back("binding=strong");
		out << "global @" << name << metadata_suffix(metadata) << " = {\n";
		if (bare->kind == TypeKind::Record)
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
		else if (node.children.empty())
			out << "zero";
		else if (starts_with(node.children[0].line, "literal") &&
		         node.children[0].token_text == "nullptr")
			out << "zero";
		else
			out << global_scalar_initializer(type, node.children[0]);
	}
	globals.push_back(out.str());
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
		    node.binding->owner != NULL &&
		    node.binding->owner->kind == ScopeKind::Namespace)
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
		functions.push_back(lowerer.lower());
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
	metadata.push_back("binding=strong");
	out << metadata_suffix(metadata);
	function_declarations_by_binding[binding] = out.str();
}

void ProgramLowerer::register_inline_definition(const Node& node)
{
	if (node.binding == NULL)
		return;
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
		return;
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
		pending_inline_definitions.push_back(binding);
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
		string name = symbol_for(binding);
		if (defined_functions.find(name) != defined_functions.end())
			continue;
		defined_functions.insert(name);
		FunctionLowerer lowerer(*this, *found->second);
		functions.push_back(lowerer.lower());
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
	for (size_t i = 0; i < srcfiles.size(); ++i)
	{
		pa12::Options pa12_options;
		pa12_options.preprocess = options.preprocess;
		pa12::internal::Parser parser(srcfiles[i], pa12_options);
		parser.parse_translation_unit();
		const vector<internal::Node>& extra = parser.extra_lowir_nodes();
		for (size_t j = 0; j < extra.size(); ++j)
			program.register_inline_definition(extra[j]);
		program.collect_translation_unit(parser.root());
	}
	program.write(outfile);
}


}  // namespace pa14
