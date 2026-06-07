#include "pa14_lowir_internal.h"

#include <algorithm>
#include <cctype>
#include <fstream>

namespace pa14 {
namespace internal {
namespace {

Binding* find_assignment_binding(TypePtr type, bool move)
{
	TypePtr bare = pa11::strip_cv(type);
	if (bare->kind != TypeKind::Record || bare->scope == NULL)
		return NULL;
	map<string, vector<Binding*> >::const_iterator found =
		bare->scope->members.find("operator=");
	if (found == bare->scope->members.end())
		return NULL;
	for (size_t i = 0; i < found->second.size(); ++i)
	{
		Binding* op = found->second[i];
		if (op->kind != BindingKind::Function ||
		    op->type->kind != TypeKind::Function ||
		    op->type->parameters.size() != 2)
			continue;
		TypePtr param = op->type->parameters[1];
		if (!move &&
		    param->kind == TypeKind::LValueReference &&
		    pa11::same_type(pa11::strip_cv(param->base), bare))
			return op;
		if (move &&
		    param->kind == TypeKind::RValueReference &&
		    pa11::same_type(pa11::strip_cv(param->base), bare))
			return op;
	}
	return NULL;
}

bool defer_static_constexpr_member_definition(const Node& node)
{
	if (node.binding == NULL)
		return false;
	if (!node.binding->is_static_member)
		return false;
	TypePtr object = strip_for_value(node.binding->type);
	TypePtr bare = pa11::strip_cv(object);
	return bare->kind == TypeKind::Array || bare->kind == TypeKind::Record;
}

bool synthesizable_defaulted_storage_copy_constructor(const Binding* binding)
{
	if (binding == NULL ||
	    !binding->is_generated_copy_move_constructor ||
	    !binding->is_defaulted ||
	    !binding->is_inline_definition ||
	    binding->type.get() == NULL ||
	    binding->type->kind != TypeKind::Function ||
	    binding->type->parameters.size() != 2 ||
	    !is_reference(binding->type->parameters[1]))
		return false;
	TypePtr record = class_record_for_member(binding);
	record = record.get() != NULL ? pa11::strip_cv(record) : TypePtr();
	if (record.get() == NULL ||
	    record->kind != TypeKind::Record ||
	    !record_has_storage_copy(record))
		return false;
	TypePtr source = pa11::strip_cv(binding->type->parameters[1]->base);
	if (!pa11::same_type(source, record))
		return false;
	return !defaulted_copy_move_constructor_needs_helper(
		const_cast<Binding*>(binding), record);
}

Node make_defaulted_storage_copy_constructor_node(const Binding* binding)
{
	Node fn("function-definition");
	fn.binding = const_cast<Binding*>(binding);
	fn.type = binding->type;
	Node this_param("parameter this");
	this_param.type = binding->type->parameters[0];
	fn.children.push_back(this_param);
	Node other_param("parameter __param1");
	other_param.type = binding->type->parameters[1];
	fn.children.push_back(other_param);
	fn.children.push_back(Node("compound-statement"));
	return fn;
}

bool is_class_constructor(const Binding* binding)
{
	return binding != NULL &&
	       binding->owner != NULL &&
	       binding->owner->kind == ScopeKind::Class &&
	       binding->name == binding->owner->name;
}

}  // namespace

FunctionOut make_constructor_base_entry(const FunctionOut& lowered,
                                        const string& name)
{
	FunctionOut base_entry = lowered;
	base_entry.name = name + "__base_entry";
	string from = "function @" + name + "(";
	string to = "function @" + name + "__base_entry(";
	size_t pos = base_entry.header.find(from);
	if (pos != string::npos)
		base_entry.header.replace(pos, from.size(), to);
	return base_entry;
}

ProgramLowerer::ProgramLowerer()
	: active_inline_definition(NULL),
	  active_inline_dependency_insert_count(0),
	  needs_empty_init_function(false),
	  needs_eh_declarations(false),
	  generated_assignment_emit_depth(0)
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
	{
		if (init.binding->kind == BindingKind::Function &&
		    init.binding->is_inline_definition)
			demand_inline_function(init.binding);
		return "addr @" + symbol_for(init.binding);
	}
	if (starts_with(init.line, "unary-expression") && init.has_op &&
	    init.op == OP_PLUS && !init.children.empty())
		return global_scalar_initializer(type, init.children[0]);
	if (starts_with(init.line, "unary-expression") && init.has_op &&
	    init.op == OP_AMP && !init.children.empty() &&
	    init.children[0].binding != NULL &&
	    init.children[0].binding->kind == BindingKind::Function)
	{
		if (init.children[0].binding->is_inline_definition)
			demand_inline_function(init.children[0].binding);
		return "addr @" + symbol_for(init.children[0].binding);
	}
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

void ProgramLowerer::demand_initializer_calls(const Node& node)
{
	if (node.direct_call != NULL && node.direct_call->is_inline_definition)
		demand_inline_function(node.direct_call);
	for (size_t i = 0; i < node.children.size(); ++i)
		demand_initializer_calls(node.children[i]);
}

void ProgramLowerer::demand_initializer_type_calls(TypePtr type, const Node& node)
{
	if (type.get() == NULL)
		return;
	TypePtr bare = pa11::strip_cv(type);
	if (bare->kind == TypeKind::Array)
	{
		for (size_t i = 0; i < node.children.size(); ++i)
			demand_initializer_type_calls(bare->base, node.children[i]);
		return;
	}
	if (bare->kind == TypeKind::Record &&
	    starts_with(node.line, "braced-init-list"))
	{
		Binding* ctor = find_constructor(bare, node.children.size());
		if (ctor != NULL &&
		    ctor->is_inline_definition &&
		    !ctor->is_generated_aggregate_constructor)
			demand_inline_function(ctor);
		for (size_t i = 0; i < node.children.size(); ++i)
			demand_initializer_type_calls(TypePtr(), node.children[i]);
	}
}

void ProgramLowerer::write_global_zero_items(ostringstream& out, TypePtr elem)
{
	TypePtr bare = pa11::strip_cv(elem);
	if (bare->kind == TypeKind::Array && !bare->unknown_bound)
	{
		for (size_t i = 0; i < bare->bound; ++i)
			write_global_zero_items(out, bare->base);
		return;
	}
	out << "  zero " << pa11::type_size(elem) << "\n";
}

void ProgramLowerer::write_global_data_items(ostringstream& out,
                                             TypePtr elem,
                                             const Node& init)
{
	TypePtr bare = pa11::strip_cv(elem);
	if (bare->kind == TypeKind::Array &&
	    starts_with(init.line, "braced-init-list"))
	{
		size_t count = bare->unknown_bound ? init.children.size() : bare->bound;
		for (size_t i = 0; i < count; ++i)
		{
			if (i < init.children.size())
				write_global_data_items(out, bare->base, init.children[i]);
			else
				write_global_zero_items(out, bare->base);
		}
		return;
	}
	if (bare->kind == TypeKind::Record &&
	    starts_with(init.line, "braced-init-list"))
	{
		pa11::layout_record_type(bare);
		size_t index = 0;
		for (size_t i = 0; i < bare->fields.size(); ++i)
		{
			Binding* field = bare->fields[i];
			if (field == NULL || field->is_static_member)
				continue;
			if (index < init.children.size())
				write_global_data_items(out, field->type, init.children[index++]);
			else
				write_global_zero_items(out, field->type);
		}
		return;
	}
	out << "  " << global_data_item(elem, init) << "\n";
}

string ProgramLowerer::ensure_local_static_guard(const Binding* binding)
{
	string name = symbol_for(binding) + "__guard";
	if (defined_globals.insert(name).second)
		globals.push_back("global @" + name +
		                  " : i64 [binding=internal] = zero");
	return name;
}

void ProgramLowerer::demand_global_declaration(const Binding* binding)
{
	if (binding == NULL)
		return;
	const Binding* matching_definition = NULL;
	for (size_t i = 0; i < global_definition_bindings.size(); ++i)
		if (template_static_member_definition_matches(
			    binding,
			    global_definition_bindings[i]))
		{
			if (matching_definition != NULL &&
			    matching_definition != global_definition_bindings[i])
				return;
			matching_definition = global_definition_bindings[i];
		}
	for (map<const Binding*, Node>::iterator it =
		     deferred_global_definitions.begin();
	     it != deferred_global_definitions.end();
	     ++it)
		if (template_static_member_definition_matches(binding, it->first))
		{
			if (matching_definition != NULL &&
			    matching_definition != it->first)
				return;
			matching_definition = it->first;
		}
	if (matching_definition != NULL)
	{
		symbols[binding] = symbol_for(matching_definition);
		map<const Binding*, Node>::iterator deferred =
			deferred_global_definitions.find(matching_definition);
		if (deferred != deferred_global_definitions.end())
		{
			Node node = deferred->second;
			deferred_global_definitions.erase(deferred);
			emit_global(node);
		}
		return;
	}
	string name = symbol_for(binding);
	if (binding->is_thread_local)
		ensure_thread_local_wrapper(name);
	if (defined_globals.find(name) != defined_globals.end())
		return;
	map<const Binding*, Node>::iterator deferred =
		deferred_global_definitions.find(binding);
	if (deferred != deferred_global_definitions.end())
	{
		Node node = deferred->second;
		deferred_global_definitions.erase(deferred);
		emit_global(node);
		return;
	}
	if (declared_globals.find(name) != declared_globals.end())
		return;
	ostringstream out;
	out << "declare global @" << name;
	TypePtr object = strip_for_value(binding->type);
	TypePtr bare = pa11::strip_cv(object);
	if (bare->kind != TypeKind::Array && bare->kind != TypeKind::Record)
		out << " : " << scalar_lowir_type(object);
	vector<string> metadata;
	if (binding->is_thread_local)
		metadata.push_back("storage=thread_local");
	if (binding->language_linkage == "c")
		metadata.push_back("linkage=c");
	string object_symbol = global_object_symbol(binding);
	if (!object_symbol.empty())
		metadata.push_back("object=" + object_symbol);
	out << metadata_suffix(metadata);
	declared_globals.insert(name);
	global_declares.push_back(out.str());
}

bool ProgramLowerer::demand_deferred_global_definition(const Binding* binding)
{
	if (binding == NULL)
		return false;
	string name = symbol_for(binding);
	if (defined_globals.find(name) != defined_globals.end())
		return true;
	map<const Binding*, Node>::iterator deferred =
		deferred_global_definitions.find(binding);
	if (deferred == deferred_global_definitions.end())
		return false;
	Node node = deferred->second;
	deferred_global_definitions.erase(deferred);
	emit_global(node);
	return true;
}

bool ProgramLowerer::template_static_member_constant_load_required(
	const Binding* binding) const
{
	if (binding == NULL || !binding->is_template_static_member_definition)
		return false;
	return binding->is_template_static_member_explicit_definition;
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


Binding* ProgramLowerer::demand_implicit_copy_assignment(TypePtr type, bool move)
{
	TypePtr record = pa11::strip_cv(type);
	if (record->kind != TypeKind::Record || record->scope == NULL)
		throw runtime_error("assignment target is not record");
	const void* key = record.get();
	map<const void*, Binding*>& cache =
		move ? implicit_move_assignments : implicit_copy_assignments;
	map<const void*, Binding*>::const_iterator found =
		cache.find(key);
	if (found != cache.end())
		return found->second;
	Binding* declared = find_assignment_binding(record, move);
	if (declared != NULL)
	{
		cache[key] = declared;
		if (!declared->is_generated_copy_move_assignment)
		{
			demand_function_declaration(declared);
			return declared;
		}
		if (declared->is_inline_definition &&
		    inline_definitions.find(declared) != inline_definitions.end())
		{
			demand_inline_function(declared);
			return declared;
		}
		string name = symbol_for(declared);
		if (defined_functions.find(name) == defined_functions.end())
		{
			defined_functions.insert(name);
			queue_synthetic_assignment_function(declared, record, move, name);
		}
		return declared;
	}
	vector<TypePtr> params;
	params.push_back(pa11::make_pointer(record));
	params.push_back(move
		? pa11::make_rvalue_reference(record)
		: pa11::make_lvalue_reference(
			pa11::make_cv(record, pa11::CV_CONST)));
	TypePtr fn_type = pa11::make_function(pa11::make_pointer(record),
	                                      params,
	                                      false);
	synthetic_bindings.push_back(unique_ptr<Binding>(
		new Binding(BindingKind::Function, "operator=", record->scope)));
	Binding* binding = synthetic_bindings.back().get();
	binding->type = fn_type;
	binding->is_inline_definition = true;
	binding->is_generated_copy_move_assignment = true;
	cache[key] = binding;
	string name = symbol_for(binding);
	if (defined_functions.find(name) != defined_functions.end())
		return binding;
	defined_functions.insert(name);
	queue_synthetic_assignment_function(binding, record, move, name);
	return binding;
}

void ProgramLowerer::queue_synthetic_assignment_function(Binding* binding,
                                                         TypePtr record,
                                                         bool move,
                                                         const string& name)
{
	FunctionOut out;
	out.binding = binding;
	out.name = name;
	out.returns_pointer_result = true;
	ostringstream header;
	header << "function @" << name
	       << "(%this : ptr, %other : ptr [pass=reference]) -> ptr";
	vector<string> metadata;
	metadata.push_back("binding=weak");
	header << metadata_suffix(metadata);
	out.header = header.str();
	out.slots.push_back("  slot $this : ptr");
	out.slots.push_back("  slot $other : ptr");
	Block block("entry");
	block.instrs.push_back("    store ptr %this, $this");
	block.instrs.push_back("    store ptr %other, $other");
	pa11::layout_record_type(record);
	bool has_bitfield = false;
	for (size_t i = 0; i < record->fields.size(); ++i)
		if (record->fields[i]->is_bit_field)
			has_bitfield = true;
	if (has_bitfield)
	{
		set<uint64_t> copied_units;
		int temp = 1;
		for (size_t i = 0; i < record->fields.size(); ++i)
		{
			Binding* field = record->fields[i];
			if (!field->is_bit_field ||
			    copied_units.find(field->member_offset) != copied_units.end())
				continue;
			copied_units.insert(field->member_offset);
			string other = "%t" + to_string(temp++);
			string other_field = "%t" + to_string(temp++);
			string value = "%t" + to_string(temp++);
			string self = "%t" + to_string(temp++);
			string self_field = "%t" + to_string(temp++);
			string low_type = scalar_lowir_type(field->type);
			block.instrs.push_back("    " + other + " = load ptr $other");
			block.instrs.push_back("    " + other_field +
			                       " = index i8 " + other + ", " +
			                       to_string(field->member_offset));
			block.instrs.push_back("    " + value + " = load " +
			                       low_type + " " + other_field);
			block.instrs.push_back("    " + self + " = load ptr $this");
			block.instrs.push_back("    " + self_field +
			                       " = index i8 " + self + ", " +
			                       to_string(field->member_offset));
			block.instrs.push_back("    store " + low_type + " " +
			                       value + ", " + self_field);
		}
		block.instrs.push_back("    %t" + to_string(temp) +
		                       " = load ptr $this");
		block.instrs.push_back("    return ptr %t" + to_string(temp));
	}
	else
	{
		vector<pair<Binding*, Binding*> > field_ops;
		uint64_t prefix_size = pa11::type_size(record);
		for (size_t i = 0; i < record->fields.size(); ++i)
		{
			Binding* op = find_assignment_binding(record->fields[i]->type, move);
			if (op == NULL && move)
				op = find_assignment_binding(record->fields[i]->type, false);
			if (op == NULL ||
			    (op->is_generated_copy_move_assignment &&
			     !op->is_inline_definition))
				continue;
			if (field_ops.empty())
				prefix_size = record->fields[i]->member_offset;
			field_ops.push_back(make_pair(record->fields[i], op));
		}
		int temp = 1;
		string self = "%t" + to_string(temp++);
		string other = "%t" + to_string(temp++);
		block.instrs.push_back("    " + self + " = load ptr $this");
		block.instrs.push_back("    " + other + " = load ptr $other");
		if (prefix_size != 0)
			block.instrs.push_back(
				"    copyobj " + to_string(prefix_size) +
				"x" + to_string(pa11::type_align(record)) + " " +
				other + ", " + self);
		for (size_t i = 0; i < field_ops.size(); ++i)
		{
			Binding* field = field_ops[i].first;
			Binding* op = field_ops[i].second;
			demand_function_declaration(op);
			if (op->is_inline_definition)
				demand_inline_function(op);
			string self_base = "%t" + to_string(temp++);
			block.instrs.push_back("    " + self_base + " = load ptr $this");
			string self_field = "%t" + to_string(temp++);
			block.instrs.push_back("    " + self_field +
			                       " = index i8 " + self_base + ", " +
			                       to_string(field->member_offset));
			string other_base = "%t" + to_string(temp++);
			block.instrs.push_back("    " + other_base + " = load ptr $other");
			string other_field = "%t" + to_string(temp++);
			block.instrs.push_back("    " + other_field +
			                       " = index i8 " + other_base + ", " +
			                       to_string(field->member_offset));
			string ignored = "%t" + to_string(temp++);
			block.instrs.push_back("    " + ignored + " = call ptr @" +
			                       symbol_for(op) + "(" + self_field +
			                       ", " + other_field + ")");
		}
		string ret = "%t" + to_string(temp++);
		block.instrs.push_back("    " + ret + " = load ptr $this");
		block.instrs.push_back("    return ptr " + ret);
	}
	block.terminated = true;
	out.blocks.push_back(block);
	pending_synthetic_assignment_functions.push_back(out);
}

void ProgramLowerer::emit_pending_synthetic_assignment_functions()
{
	if (pending_synthetic_assignment_functions.empty())
		return;
	emit_pending_generated_aggregate_constructors();
	if (pending_synthetic_assignment_functions.empty())
		return;
	functions.insert(functions.end(),
	                 pending_synthetic_assignment_functions.begin(),
	                 pending_synthetic_assignment_functions.end());
	pending_synthetic_assignment_functions.clear();
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
			    node.binding->is_dependent_template_artifact)
				return;
			if (node.binding != NULL &&
			    ((node.binding->owner != NULL &&
			      node.binding->owner->kind == ScopeKind::Namespace) ||
			     node.binding->is_static_member))
			{
				if (defer_static_constexpr_member_definition(node))
				{
					deferred_global_definitions[node.binding] = node;
					return;
				}
				TypePtr object = strip_for_value(node.binding->type);
				TypePtr bare = pa11::strip_cv(object);
			if (node.binding->is_static_member &&
			    node.binding->has_constant &&
			    bare->kind != TypeKind::Array &&
			    bare->kind != TypeKind::Record)
			{
				if (bare->kind == TypeKind::Fundamental &&
				    bare->fundamental == FT_BOOL &&
				    !node.binding->is_constexpr)
				{
					emit_global(node);
					return;
				}
				if (node.token_text ==
				        "template-static-member-definition" &&
				    binding_has_template_specialization_context(node.binding) &&
				    node.binding
					    ->is_template_static_member_explicit_definition)
				{
					emit_global(node);
					return;
				}
				deferred_global_definitions[node.binding] = node;
				return;
			}
			emit_global(node);
		}
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
		if (node.binding != NULL && node.binding->is_virtual)
		{
			TypePtr record = class_record_for_member(node.binding);
			if (record.get() != NULL)
				demand_vtable(record);
		}
		if (node.binding != NULL && node.binding->is_inline_definition)
		{
			register_inline_definition(node);
			return;
		}
		if (node.binding != NULL)
			defined_functions.insert(symbol_for(node.binding));
		FunctionLowerer lowerer(*this, node);
		FunctionOut lowered = lowerer.lower();
		if (is_class_constructor(node.binding))
		{
			string name = symbol_for(node.binding);
			functions.push_back(make_constructor_base_entry(lowered, name));
		}
		if (node.binding != NULL &&
		    node.binding->owner != NULL &&
		    node.binding->owner->kind == ScopeKind::Class &&
		    !node.binding->name.empty() &&
		    node.binding->name[0] == '~' &&
		    node.binding->is_noop_destructor)
		{
			FunctionOut noop_entry = lowered;
			string name = symbol_for(node.binding);
			noop_entry.name = name + "__noop_entry";
			string from = "function @" + name + "(";
			string to = "function @" + name + "__noop_entry(";
			size_t pos = noop_entry.header.find(from);
			if (pos != string::npos)
				noop_entry.header.replace(pos, from.size(), to);
			functions.push_back(noop_entry);
		}
		functions.push_back(lowered);
		emit_pending_synthetic_assignment_functions();
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
	function_declarations_by_binding[binding] = out.str();
}

void ProgramLowerer::register_inline_definition(const Node& node)
{
	if (node.binding == NULL)
		return;
	bool copy_move_helper =
		node.binding->is_generated_copy_move_constructor ||
		node.token_text == "copy-move-helper";
	if (node.binding->owner != NULL &&
	    node.binding->owner->kind == ScopeKind::Class)
	{
		TypePtr owner_record = pa11::record_type_for_scope(node.binding->owner);
		bool class_template_specialization =
			record_is_template_specialization(owner_record);
		if (!class_template_specialization &&
		    !copy_move_helper &&
		    !binding_has_template_specialization_context(node.binding))
			symbol_for(node.binding);
	}
	if (!copy_move_helper &&
	    inline_definition_ranks.find(node.binding) == inline_definition_ranks.end())
		inline_definition_ranks[node.binding] = inline_definition_ranks.size();
	if (inline_definitions.find(node.binding) == inline_definitions.end() ||
	    binding_has_template_specialization_context(node.binding))
		inline_definitions[node.binding] = &node;
}

void ProgramLowerer::demand_inline_function(const Binding* binding,
                                            bool complete_entry)
{
	if (binding != NULL &&
	    binding->kind == BindingKind::Function &&
	    binding->aliased_binding != NULL &&
	    binding->aliased_binding->is_inline_definition)
		binding = binding->aliased_binding;
	if (binding == NULL || !binding->is_inline_definition)
		return;
	bool class_ctor = is_class_constructor(binding);
	bool class_dtor = is_class_destructor_binding(binding);
	if (complete_entry)
		demanded_inline_complete_entries.insert(binding);
	else if (!class_ctor && !class_dtor)
		return;
	demand_move_assignment_copy_dependency(binding);
	string name = symbol_for(binding);
	if (complete_entry && defined_functions.find(name) != defined_functions.end())
		return;
	if (!complete_entry &&
	    defined_functions.find(name + "__base_entry") != defined_functions.end())
		return;
	for (size_t i = 0; i < pending_inline_definitions.size(); ++i)
		if (pending_inline_definitions[i] == binding)
			return;
	map<const Binding*, const Node*>::const_iterator found =
		inline_definitions.find(binding);
	if (found == inline_definitions.end() &&
	    synthesizable_defaulted_storage_copy_constructor(binding))
	{
		synthetic_inline_definitions[binding] =
			make_defaulted_storage_copy_constructor_node(binding);
		inline_definitions[binding] =
			&synthetic_inline_definitions[binding];
		found = inline_definitions.find(binding);
	}
	if (found != inline_definitions.end())
		insert_pending_inline_definition(binding);
}


}  // namespace internal

}  // namespace pa14
