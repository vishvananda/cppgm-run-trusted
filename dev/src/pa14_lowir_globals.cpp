#include "pa14_lowir_internal.h"

#include <sstream>

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
	if (starts_with(init.line, "id-expression") &&
	    init.binding != NULL &&
	    init.binding->kind == BindingKind::Function)
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
		if (bare->kind == TypeKind::Record &&
		    init.direct_call != NULL &&
		    init.direct_call->is_defaulted &&
		    init.direct_call->unwind_no &&
		    init.direct_call->type->kind == TypeKind::Function &&
		    init.direct_call->type->parameters.size() == 1)
			return false;
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
	if (starts_with(init.line, "id-expression") &&
	    init.binding != NULL &&
	    init.binding->is_static_member)
		return true;
	return !global_static_scalar_initializer(init);
}

vector<string> global_metadata(const Binding* binding, bool weak_constexpr)
{
	vector<string> items;
	if (binding->is_thread_local)
		items.push_back("storage=thread_local");
	if (binding->language_linkage == "c")
		items.push_back("linkage=c");
	if (binding->is_static_member &&
	    (binding->is_template_static_member_definition ||
	     binding_has_template_specialization_context(binding)))
		items.push_back("binding=weak");
	else if (weak_constexpr &&
	         binding->is_static_member &&
	         binding->is_constexpr)
		items.push_back("binding=weak");
	else
		items.push_back(binding->is_local_static ||
		                binding->is_namespace_static ||
		                binding->is_constexpr
		                ? "binding=internal" : "binding=strong");
	string object = global_object_symbol(binding);
	if (!object.empty())
		items.push_back("object=" + object);
	return items;
}

bool global_runtime_init(ProgramLowerer& program,
                         const Node& node,
                         TypePtr type,
                         TypePtr bare)
{
	bool runtime_init =
		!node.children.empty() &&
		global_needs_runtime_init(type, node.children[0]);
	if (!runtime_init &&
	    node.children.empty() &&
	    bare->kind == TypeKind::Record)
	{
		Binding* ctor = find_constructor(type, 0);
		runtime_init = ctor != NULL && !ctor->is_noop_constructor;
	}
	if (runtime_init &&
	    node.binding->is_namespace_static &&
	    !node.children.empty() &&
	    starts_with(node.children[0].line, "no-op-initializer"))
		runtime_init = false;
	bool static_member_id_init =
		!node.children.empty() &&
		starts_with(node.children[0].line, "id-expression") &&
		node.children[0].binding != NULL &&
		node.children[0].binding->is_static_member;
	bool static_member_id_has_storage = false;
	if (static_member_id_init)
	{
		const Binding* source = node.children[0].binding;
		static_member_id_has_storage =
			program.deferred_global_definitions.find(source) !=
			program.deferred_global_definitions.end();
		if (!static_member_id_has_storage)
		{
			string source_name = program.symbol_for(source);
			static_member_id_has_storage =
				program.defined_globals.find(source_name) !=
				program.defined_globals.end();
		}
		if (!static_member_id_has_storage)
			runtime_init = false;
	}
	if (node.binding->has_constant &&
	    !(static_member_id_init && static_member_id_has_storage))
	{
		TypePtr object = strip_for_value(type);
		TypePtr object_bare = pa11::strip_cv(object);
		if (object_bare->kind != TypeKind::Array &&
		    object_bare->kind != TypeKind::Record)
			runtime_init = false;
	}
	if (node.binding->is_constexpr &&
	    bare->kind == TypeKind::Array &&
	    !node.children.empty() &&
	    starts_with(node.children[0].line, "braced-init-list"))
		runtime_init = false;
	if (!runtime_init &&
	    node.binding->is_constexpr &&
	    bare->kind == TypeKind::Array &&
	    !node.children.empty())
		program.demand_initializer_type_calls(node.binding->type,
		                                      node.children[0]);
	if (!runtime_init &&
	    !node.children.empty() &&
	    node.children[0].direct_call != NULL &&
	    node.children[0].direct_call->is_defaulted &&
	    is_class_constructor_binding(node.children[0].direct_call))
		program.demand_inline_function(node.children[0].direct_call);
	if (runtime_init && node.binding->is_thread_local)
		program.thread_local_init_variables.push_back(node);
	else if (runtime_init && !node.binding->is_local_static)
	{
		Node runtime_node = node;
		if (static_member_id_init &&
		    static_member_id_has_storage &&
		    !runtime_node.children.empty())
		{
			runtime_node.children[0].has_constant_value = false;
			runtime_node.children[0].constant_value = 0;
		}
		program.global_init_variables.push_back(runtime_node);
	}
	if (record_has_destructor(type))
		program.global_fini_variables.push_back(node);
	return runtime_init;
}

void emit_static_constant_member_globals(ProgramLowerer& program, TypePtr bare)
{
	if (bare->kind != TypeKind::Record ||
	    !record_is_template_specialization(bare) ||
	    bare->scope == NULL)
		return;
	for (size_t i = 0; i < bare->scope->binding_order.size(); ++i)
	{
		Binding* member = bare->scope->binding_order[i];
		if (member == NULL ||
		    member->kind != BindingKind::Variable ||
		    !member->is_static_member ||
		    !member->has_constant)
			continue;
		TypePtr member_bare = pa11::strip_cv(strip_for_value(member->type));
		if (member_bare->kind == TypeKind::Array ||
		    member_bare->kind == TypeKind::Record)
			continue;
		Node member_node("variable " + member->name + " " +
		                 pa11::describe_type(member->type));
		member_node.binding = member;
		member_node.type = member->type;
		program.emit_global(member_node);
	}
}

void write_enum_global(ostringstream& out,
                       const Node& node,
                       const string& name)
{
	vector<string> metadata = global_metadata(node.binding, false);
	out << "global @" << name << metadata_suffix(metadata) << " = {\n";
	out << "  zero " << pa11::type_size(node.binding->type) << "\n";
	out << "}";
}

void write_aggregate_global(ProgramLowerer& program,
                            ostringstream& out,
                            const Node& node,
                            const string& name,
                            TypePtr bare,
                            bool runtime_init)
{
	vector<string> metadata = global_metadata(node.binding, true);
	out << "global @" << name << metadata_suffix(metadata) << " = {\n";
	if (runtime_init)
		out << "  zero " << pa11::type_size(node.binding->type) << "\n";
	else if (bare->kind == TypeKind::Record)
	{
		out << "  zero " << pa11::type_size(node.binding->type) << "\n";
		if (!node.binding->is_static_member &&
		    !node.binding->is_local_static &&
		    !node.binding->is_namespace_static)
			program.needs_empty_init_function = true;
	}
	else
	{
		TypePtr elem = bare->base;
		if (!node.children.empty() &&
		    starts_with(node.children[0].line, "braced-init-list"))
		{
			for (size_t i = 0; i < node.children[0].children.size(); ++i)
				program.write_global_data_items(out,
				                                elem,
				                                node.children[0].children[i]);
			if (!bare->unknown_bound)
				for (size_t i = node.children[0].children.size();
				     i < bare->bound;
				     ++i)
					program.write_global_zero_items(out, elem);
		}
		else
			out << "  zero " << pa11::type_size(node.binding->type) << "\n";
	}
	out << "}";
}

string normalized_float_literal(string value)
{
	if (!value.empty())
	{
		char last = value[value.size() - 1];
		if (last == 'f' || last == 'F' || last == 'l' || last == 'L')
			value.resize(value.size() - 1);
	}
	if (value.size() > 2 && value.compare(value.size() - 2, 2, ".0") == 0)
		value.resize(value.size() - 2);
	return value;
}

bool write_reference_global(ProgramLowerer& program,
                            ostringstream& out,
                            const Node& node,
                            const string& name)
{
	if (!is_reference(node.binding->type))
		return false;
	out << "zero";
	if (node.children.empty())
		return true;
	const Node& init = node.children[0];
	if (starts_with(init.line, "id-expression") && init.binding != NULL)
		program.init_actions.push_back(
			InitAction(name, "addr", program.symbol_for(init.binding)));
	else if (starts_with(init.line, "unary-expression") &&
	         init.has_op && init.op == OP_STAR &&
	         !init.children.empty() &&
	         init.children[0].binding != NULL)
		program.init_actions.push_back(
			InitAction(name, "load_ptr",
			           program.symbol_for(init.children[0].binding)));
	return true;
}

void write_scalar_global(ProgramLowerer& program,
                         ostringstream& out,
                         const Node& node,
                         const string& name,
                         bool runtime_init)
{
	TypePtr type = node.binding->type;
	vector<string> metadata = global_metadata(node.binding, true);
	out << "global @" << name << " : " << scalar_lowir_type(type)
	    << metadata_suffix(metadata) << " = ";
	if (write_reference_global(program, out, node, name))
		return;
	if (runtime_init)
		out << "zero";
	else if (node.children.empty() && node.binding->has_constant &&
	    pa11::strip_cv(type)->kind != TypeKind::Enum)
		out << node.binding->constant_value;
	else if (node.binding->has_constant &&
	         pa11::is_integral_or_bool_type(type) &&
	         pa11::strip_cv(type)->kind != TypeKind::Enum)
		out << node.binding->constant_value;
	else if (!node.children.empty() &&
	         starts_with(node.children[0].line, "literal") &&
	         is_float_type(type))
		out << normalized_float_literal(node.children[0].token_text);
	else if (runtime_init || node.children.empty())
		out << "zero";
	else if (starts_with(node.children[0].line, "literal") &&
	         node.children[0].token_text == "nullptr")
		out << "zero";
	else
		out << program.global_scalar_initializer(type, node.children[0]);
}

}  // namespace

void ProgramLowerer::emit_global(const Node& node)
{
	if (node.binding == NULL)
		return;
	string name = symbol_for(node.binding);
	if (!defined_globals.insert(name).second)
		return;
	global_definition_bindings.push_back(node.binding);
	global_definition_nodes[node.binding] = node;
	if (node.binding->is_thread_local)
		ensure_thread_local_wrapper(name);
	TypePtr type = node.binding->type;
	TypePtr bare = pa11::strip_cv(type);
	bool runtime_init = global_runtime_init(*this, node, type, bare);
	emit_static_constant_member_globals(*this, bare);
	ostringstream out;
	if (bare->kind == TypeKind::Enum && node.binding->has_constant)
		write_enum_global(out, node, name);
	else if (bare->kind == TypeKind::Array || bare->kind == TypeKind::Record)
		write_aggregate_global(*this, out, node, name, bare, runtime_init);
	else
		write_scalar_global(*this, out, node, name, runtime_init);
	globals.push_back(out.str());
}

}  // namespace internal
}  // namespace pa14
