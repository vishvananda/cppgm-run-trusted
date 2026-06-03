#include "pa14_lowir_internal.h"

#include <fstream>

namespace pa14 {
namespace internal {

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
	if (bare->kind == TypeKind::Array)
	{
		out << "global @" << name << " [binding=strong] = {\n";
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
		out << "}";
	}
	else
	{
		out << "global @" << name << " : " << scalar_lowir_type(type)
		    << " [binding=strong] = ";
		if (node.children.empty())
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
		Binding* binding = node.binding;
		if (binding == NULL)
			return;
		string name = symbol_for(binding);
		ostringstream out;
		out << "declare function @" << name << "(";
		for (size_t i = 0; i < binding->type->parameters.size(); ++i)
		{
			if (i != 0)
				out << ", ";
			out << "%arg" << i << " : "
			    << scalar_lowir_type(binding->type->parameters[i]);
		}
		out << ") -> " << scalar_lowir_type(binding->type->base);
		if (binding->type->variadic)
			out << " [arity=variadic]";
		declares.push_back(out.str());
		return;
	}
	if (starts_with(node.line, "function-definition "))
	{
		if (node.binding != NULL)
			defined_functions.insert(symbol_for(node.binding));
		FunctionLowerer lowerer(*this, node);
		functions.push_back(lowerer.lower());
		return;
	}
	for (size_t i = 0; i < node.children.size(); ++i)
		collect_node(node.children[i]);
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
		program.collect_translation_unit(parser.root());
	}
	program.write(outfile);
}


}  // namespace pa14
