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
	bool qualified_member_definition =
		node.binding->owner != NULL &&
		node.binding->owner->kind == ScopeKind::Namespace &&
		node.binding->name.find("::") != string::npos;
	if (!node.binding->is_static_member && !qualified_member_definition)
		return false;
	TypePtr object = strip_for_value(node.binding->type);
	TypePtr bare = pa11::strip_cv(object);
	return bare->kind == TypeKind::Array || bare->kind == TypeKind::Record;
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
	if (starts_with(node.line, "call-expression") ||
	    starts_with(node.line, "constructor-action") ||
	    node.direct_call != NULL)
		return true;
	for (size_t i = 0; i < node.children.size(); ++i)
		if (contains_call_expression(node.children[i]))
			return true;
	return false;
}

bool generated_copy_move_constructor_node(const Node& node)
{
	if (node.binding == NULL ||
	    (!node.binding->is_generated_copy_move_constructor &&
	     node.token_text != "copy-move-helper"))
		return false;
	if (node.token_text == "copy-move-helper")
	{
		bool empty_body = !node.children.empty() &&
		                  starts_with(node.children.back().line,
		                              "compound-statement") &&
		                  node.children.back().children.empty();
		if (empty_body)
			return false;
	}
	bool template_context = false;
	for (Scope* scope = node.binding->owner; scope != NULL; scope = scope->parent)
	{
		if (scope->kind != ScopeKind::Class)
			continue;
		TypePtr record = pa11::record_type_for_scope(scope);
		record = record.get() != NULL ? pa11::strip_cv(record) : TypePtr();
		if (record_is_template_specialization(record))
		{
			template_context = true;
			break;
		}
	}
	if (!template_context)
		return false;
	if (node.binding->is_defaulted &&
	    node.binding->owner != NULL &&
	    node.binding->owner->kind == ScopeKind::Class)
	{
		TypePtr record = pa11::record_type_for_scope(node.binding->owner);
		record = record.get() != NULL ? pa11::strip_cv(record) : TypePtr();
		if (record.get() != NULL)
		{
			pa11::layout_record_type(record);
			for (size_t i = 0; i < record->fields.size(); ++i)
				if (pa11::is_reference_type(record->fields[i]->type))
					return false;
		}
	}
	return true;
}

bool is_class_constructor(const Binding* binding)
{
	return binding != NULL &&
	       binding->owner != NULL &&
	       binding->owner->kind == ScopeKind::Class &&
	       binding->name == binding->owner->name;
}

TypePtr function_record_result(const Binding* binding)
{
	if (binding == NULL ||
	    binding->type.get() == NULL ||
	    binding->type->kind != TypeKind::Function)
		return TypePtr();
	TypePtr result = pa11::strip_cv(binding->type->base);
	return result.get() != NULL && result->kind == TypeKind::Record
		? result
		: TypePtr();
}

bool function_returns_record(const Binding* binding)
{
	return function_record_result(binding).get() != NULL;
}

bool constructor_has_by_value_record_parameter(const Binding* binding)
{
	if (!is_class_constructor(binding) ||
	    binding->type.get() == NULL ||
	    binding->type->kind != TypeKind::Function)
		return false;
	for (size_t i = 1; i < binding->type->parameters.size(); ++i)
	{
		TypePtr param = pa11::strip_cv(binding->type->parameters[i]);
		if (param.get() != NULL && param->kind == TypeKind::Record)
			return true;
	}
	return false;
}

bool constructor_has_no_explicit_parameters(const Binding* binding)
{
	return is_class_constructor(binding) &&
	       binding->type.get() != NULL &&
	       binding->type->kind == TypeKind::Function &&
	       binding->type->parameters.size() == 1;
}

bool constructor_has_by_value_record_parameter(TypePtr record,
                                               const Binding* binding)
{
	if (record.get() == NULL ||
	    !is_class_constructor(binding) ||
	    binding->type.get() == NULL ||
	    binding->type->kind != TypeKind::Function)
		return false;
	for (size_t i = 1; i < binding->type->parameters.size(); ++i)
	{
		TypePtr param = pa11::strip_cv(binding->type->parameters[i]);
		if (param.get() != NULL &&
		    param->kind == TypeKind::Record &&
		    pa11::same_type(param, record))
			return true;
	}
	return false;
}

bool function_has_by_value_record_parameter(const Binding* binding,
                                            TypePtr record)
{
	if (binding == NULL ||
	    binding->type.get() == NULL ||
	    binding->type->kind != TypeKind::Function ||
	    record.get() == NULL)
		return false;
	for (size_t i = 0; i < binding->type->parameters.size(); ++i)
	{
		TypePtr param = pa11::strip_cv(binding->type->parameters[i]);
		if (param.get() != NULL &&
		    param->kind == TypeKind::Record &&
		    pa11::same_type(param, record))
			return true;
	}
	return false;
}

bool pending_record_return_feeds_constructor(
	const Binding* binding,
	const vector<const Binding*>& pending_inline_definitions)
{
	if (!constructor_has_by_value_record_parameter(binding))
		return false;
	for (size_t i = 0; i < pending_inline_definitions.size(); ++i)
	{
		TypePtr result = function_record_result(pending_inline_definitions[i]);
		if (constructor_has_by_value_record_parameter(result, binding))
			return true;
	}
	return false;
}

bool type_mentions_template_specialization(TypePtr type)
{
	type = type.get() != NULL ? pa11::strip_cv(type) : TypePtr();
	if (type.get() == NULL)
		return false;
	if (record_is_template_specialization(type))
		return true;
	if (type->kind == TypeKind::Pointer ||
	    type->kind == TypeKind::LValueReference ||
	    type->kind == TypeKind::RValueReference ||
	    type->kind == TypeKind::Array ||
	    type->kind == TypeKind::MemberPointer)
		return type_mentions_template_specialization(type->base) ||
		       type_mentions_template_specialization(type->member_class);
	if (type->kind == TypeKind::Function)
	{
		if (type_mentions_template_specialization(type->base))
			return true;
		for (size_t i = 0; i < type->parameters.size(); ++i)
			if (type_mentions_template_specialization(type->parameters[i]))
				return true;
	}
	return false;
}

bool binding_mentions_template_specialization(const Binding* binding)
{
	return binding != NULL &&
	       type_mentions_template_specialization(binding->type);
}

bool same_binding_or_alias(const Binding* left, const Binding* right)
{
	return left == right ||
	       (left != NULL && left->aliased_binding == right) ||
	       (right != NULL && right->aliased_binding == left);
}

bool early_hidden_friend_definition(const Node& node,
                                    const set<const Binding*>& direct_calls)
{
	if (node.binding == NULL || !node.binding->is_hidden_friend)
		return false;
	for (set<const Binding*>::const_iterator it = direct_calls.begin();
	     it != direct_calls.end();
	     ++it)
		if (same_binding_or_alias(node.binding, *it))
			return true;
	if (node.binding->is_constexpr)
		return false;
	return !contains_call_expression(node) &&
	       !binding_mentions_template_specialization(node.binding);
}

TypePtr first_this_record(const Binding* binding)
{
	if (binding == NULL ||
	    binding->type.get() == NULL ||
	    binding->type->kind != TypeKind::Function ||
	    binding->type->parameters.empty())
		return TypePtr();
	TypePtr first = pa11::strip_cv(binding->type->parameters[0]);
	if (first->kind != TypeKind::Pointer)
		return TypePtr();
	TypePtr record = pa11::strip_cv(first->base);
	return record->kind == TypeKind::Record ? record : TypePtr();
}

bool function_touches_record(const Binding* binding, TypePtr record)
{
	if (binding == NULL ||
	    binding->type.get() == NULL ||
	    binding->type->kind != TypeKind::Function ||
	    record.get() == NULL)
		return false;
	for (size_t i = 0; i < binding->type->parameters.size(); ++i)
	{
		TypePtr param = pa11::strip_cv(binding->type->parameters[i]);
		if (param->kind == TypeKind::Pointer ||
		    param->kind == TypeKind::LValueReference ||
		    param->kind == TypeKind::RValueReference)
			param = pa11::strip_cv(param->base);
		if (param->kind == TypeKind::Record &&
		    pa11::same_type(param, record))
			return true;
	}
	return false;
}

FunctionOut make_constructor_base_entry(const FunctionOut& lowered,
                                        const string& name)
{
	FunctionOut base_entry = lowered;
	string from = "function @" + name + "(";
	string to = "function @" + name + "__base_entry(";
	size_t pos = base_entry.header.find(from);
	if (pos != string::npos)
		base_entry.header.replace(pos, from.size(), to);
	return base_entry;
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


Binding* ProgramLowerer::demand_implicit_copy_assignment(TypePtr type, bool move)
{
	TypePtr record = pa11::strip_cv(type);
	if (record->kind != TypeKind::Record || record->scope == NULL)
		throw runtime_error("assignment target is not record");
	if (move)
		demand_implicit_copy_assignment(type, false);
	const void* key = record.get();
	map<const void*, Binding*>& cache =
		move ? implicit_move_assignments : implicit_copy_assignments;
	map<const void*, Binding*>::const_iterator found =
		cache.find(key);
	if (found != cache.end())
		return found->second;

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
	(void)binding;
	FunctionOut out;
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
			if (op == NULL || !op->is_inline_definition)
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
			demand_inline_function(op);
			string self_field = "%t" + to_string(temp++);
			string other_field = "%t" + to_string(temp++);
			block.instrs.push_back("    " + self_field +
			                       " = index i8 " + self + ", " +
			                       to_string(field->member_offset));
			block.instrs.push_back("    " + other_field +
			                       " = index i8 " + other + ", " +
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
			    node.binding->is_constexpr &&
			    node.binding->has_constant &&
			    bare->kind != TypeKind::Array &&
			    bare->kind != TypeKind::Record)
				return;
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
	if (found != inline_definitions.end())
		insert_pending_inline_definition(binding);
}

void ProgramLowerer::demand_move_assignment_copy_dependency(
	const Binding* binding)
{
	if (binding == NULL ||
	    !binding->is_generated_copy_move_assignment ||
	    binding->type->kind != TypeKind::Function ||
	    binding->type->parameters.size() != 2 ||
	    binding->type->parameters[1]->kind != TypeKind::RValueReference ||
	    binding->owner == NULL)
		return;
	map<string, vector<Binding*> >::const_iterator found =
		binding->owner->members.find("operator=");
	if (found == binding->owner->members.end())
		return;
	for (size_t i = 0; i < found->second.size(); ++i)
	{
		Binding* candidate = found->second[i];
		if (candidate->is_generated_copy_move_assignment &&
		    candidate->type->kind == TypeKind::Function &&
		    candidate->type->parameters.size() == 2 &&
		    candidate->type->parameters[1]->kind == TypeKind::LValueReference)
		{
			demand_inline_function(candidate);
			break;
		}
	}
}

void ProgramLowerer::place_lvalue_assignment_before_rvalue_assignment(
	const Binding* binding, ProgramLowerer::PendingInlineIterator& pos)
{
	if (!binding->is_generated_copy_move_assignment ||
	    binding->type->kind != TypeKind::Function ||
	    binding->type->parameters.size() != 2 ||
	    binding->type->parameters[1]->kind != TypeKind::LValueReference)
		return;
	for (PendingInlineIterator it = pending_inline_definitions.begin();
	     it != pending_inline_definitions.end(); ++it)
		if ((*it)->is_generated_copy_move_assignment &&
		    (*it)->type->kind == TypeKind::Function &&
		    (*it)->type->parameters.size() == 2 &&
		    (*it)->type->parameters[1]->kind == TypeKind::RValueReference)
		{
			pos = it;
			break;
		}
}

void ProgramLowerer::place_user_assignment_before_owner_members(
	const Binding* binding, ProgramLowerer::PendingInlineIterator& pos)
{
	if (binding->name != "operator=" ||
	    binding->is_generated_copy_move_assignment ||
	    binding->owner == NULL)
		return;
	for (PendingInlineIterator it = pending_inline_definitions.begin();
	     it != pending_inline_definitions.end(); ++it)
		if ((*it)->owner == binding->owner &&
		    (*it)->name != binding->owner->name)
		{
			pos = it;
			break;
		}
}

void ProgramLowerer::place_record_return_before_matching_constructor(
	const Binding* binding, ProgramLowerer::PendingInlineIterator& pos)
{
	if (!function_returns_record(binding))
		return;
	TypePtr result = function_record_result(binding);
	for (PendingInlineIterator it = pending_inline_definitions.begin();
	     it != pending_inline_definitions.end(); ++it)
	{
		const Binding* pending = *it;
		if (!is_class_constructor(pending) ||
		    pending->type.get() == NULL ||
		    pending->type->kind != TypeKind::Function ||
		    pending->type->parameters.size() < 2)
			continue;
		TypePtr param = pa11::strip_cv(
			object_type(pending->type->parameters[1]));
		if (param.get() != NULL &&
		    param->kind == TypeKind::Record &&
		    pa11::same_type(param, result))
		{
			pos = it;
			break;
		}
	}
}

void ProgramLowerer::place_record_return_before_owner_scalar_member(
	const Binding* binding, ProgramLowerer::PendingInlineIterator& pos)
{
	if (!function_returns_record(binding) ||
	    binding->owner == NULL ||
	    !binding_has_template_specialization_context(binding))
		return;
	for (PendingInlineIterator it = pending_inline_definitions.begin();
	     it != pending_inline_definitions.end(); ++it)
	{
		const Binding* pending = *it;
		bool pending_operator =
			pending->name.compare(0, 8, "operator") == 0 ||
			pending->name.compare(0, 9, "operator ") == 0;
		if (pending->owner == binding->owner &&
		    !is_class_constructor(pending) &&
		    !pending_operator &&
		    !function_returns_record(pending))
		{
			pos = it;
			break;
		}
	}
}

void ProgramLowerer::place_constructor_inline_definition(
	const Binding* binding, ProgramLowerer::PendingInlineIterator& pos)
{
	if (binding->owner == NULL || binding->name != binding->owner->name)
		return;

	for (PendingInlineIterator it = pending_inline_definitions.begin();
	     it != pending_inline_definitions.end(); ++it)
	{
		bool pending_ctor =
			(*it)->owner != NULL &&
			(*it)->owner->kind == ScopeKind::Class &&
			(*it)->name == (*it)->owner->name;
		if (pending_ctor &&
		    binding->type.get() != NULL &&
		    (*it)->type.get() != NULL &&
		    binding->type->kind == TypeKind::Function &&
		    (*it)->type->kind == TypeKind::Function &&
		    binding->type->parameters.size() < (*it)->type->parameters.size())
		{
			pos = it;
			break;
		}
	}

	if (pos == pending_inline_definitions.end() &&
	    binding_has_template_specialization_context(binding))
	{
		for (PendingInlineIterator it = pending_inline_definitions.begin();
		     it != pending_inline_definitions.end(); ++it)
		{
			const Binding* pending = *it;
			bool pending_operator =
				pending->name.compare(0, 8, "operator") == 0 ||
				pending->name.compare(0, 9, "operator ") == 0;
			if (pending->owner == binding->owner &&
			    !is_class_constructor(pending) &&
			    !pending_operator)
			{
				pos = it;
				break;
			}
		}
	}

	if (pos == pending_inline_definitions.end() &&
	    constructor_has_no_explicit_parameters(binding))
	{
		TypePtr record = first_this_record(binding);
		for (PendingInlineIterator it = pending_inline_definitions.begin();
		     it != pending_inline_definitions.end(); ++it)
			if (function_returns_record(*it) &&
			    function_has_by_value_record_parameter(*it, record))
			{
				pos = it;
				break;
			}
	}

	if (pos == pending_inline_definitions.end() &&
	    !pending_record_return_feeds_constructor(
		    binding, pending_inline_definitions))
		for (PendingInlineIterator it = pending_inline_definitions.begin();
		     it != pending_inline_definitions.end(); ++it)
			if ((*it)->owner != NULL &&
			    (*it)->owner->kind == ScopeKind::Namespace)
			{
				pos = it;
				break;
			}

	for (PendingInlineIterator it = pending_inline_definitions.begin();
	     it != pending_inline_definitions.end() &&
	     pos == pending_inline_definitions.end(); ++it)
		if ((*it)->owner == binding->owner &&
		    ((*it)->name == "operator=" ||
		     (*it)->name.compare(0, 9, "operator ") == 0))
		{
			pos = it;
			break;
		}

	if (active_inline_definition != NULL &&
	    is_class_constructor(active_inline_definition) &&
	    binding_has_template_specialization_context(active_inline_definition))
	{
		TypePtr active_record = first_this_record(active_inline_definition);
		for (PendingInlineIterator it = pending_inline_definitions.begin();
		     it != pending_inline_definitions.end() &&
		     pos == pending_inline_definitions.end(); ++it)
		{
			if (!is_class_constructor(*it))
				continue;
			TypePtr pending_record = first_this_record(*it);
			if (active_record.get() != NULL &&
			    pending_record.get() != NULL &&
			    record_has_base(active_record, pending_record))
				continue;
			pos = it;
			break;
		}
	}
}

void ProgramLowerer::place_destructor_inline_definition(
	const Binding* binding, ProgramLowerer::PendingInlineIterator& pos)
{
	if (binding->name.empty() || binding->name[0] != '~' ||
	    binding->owner == NULL)
		return;

	TypePtr destroyed_record = first_this_record(binding);
	for (PendingInlineIterator it = pending_inline_definitions.begin();
	     it != pending_inline_definitions.end(); ++it)
	{
		TypePtr pending_this = first_this_record(*it);
		bool pending_destroyed_record_ctor =
			binding_has_template_specialization_context(binding) &&
			is_class_constructor(*it) &&
			pending_this.get() != NULL &&
			destroyed_record.get() != NULL &&
			pa11::same_type(pending_this, destroyed_record);
		if (((*it)->owner == binding->owner &&
		     (*it)->name != binding->owner->name) ||
		    (!pending_destroyed_record_ctor &&
		     function_touches_record(*it, destroyed_record)))
		{
			pos = it;
			break;
		}
	}
}

void ProgramLowerer::place_const_conversion_before_mutable_conversion(
	const Binding* binding, ProgramLowerer::PendingInlineIterator& pos)
{
	bool binding_const_conversion =
		binding->name.compare(0, 9, "operator ") == 0 &&
		binding->type->kind == TypeKind::Function &&
		!binding->type->parameters.empty() &&
		pa11::strip_cv(binding->type->parameters[0])->kind ==
			TypeKind::Pointer &&
		(pa11::strip_cv(binding->type->parameters[0])->base->cv &
		 pa11::CV_CONST) != 0;
	if (!binding_const_conversion || binding->owner == NULL)
		return;

	for (PendingInlineIterator it = pending_inline_definitions.begin();
	     it != pending_inline_definitions.end(); ++it)
	{
		bool pending_conversion =
			(*it)->name.compare(0, 9, "operator ") == 0 &&
			(*it)->type->kind == TypeKind::Function &&
			!(*it)->type->parameters.empty() &&
			pa11::strip_cv((*it)->type->parameters[0])->kind ==
				TypeKind::Pointer;
		bool pending_const =
			pending_conversion &&
			(pa11::strip_cv((*it)->type->parameters[0])->base->cv &
			 pa11::CV_CONST) != 0;
		if ((*it)->owner == binding->owner &&
		    pending_conversion && !pending_const)
		{
			pos = it;
			break;
		}
	}
}

void ProgramLowerer::place_specialized_conversion_before_base_conversion(
	const Binding* binding, ProgramLowerer::PendingInlineIterator& pos)
{
	if (binding->name.compare(0, 9, "operator ") == 0 &&
	    binding->owner != NULL &&
	    binding_has_template_specialization_context(binding))
	{
		TypePtr owner_record = class_record_for_member(binding);
		for (PendingInlineIterator it = pending_inline_definitions.begin();
		     it != pending_inline_definitions.end() &&
		     pos == pending_inline_definitions.end(); ++it)
		{
			if ((*it)->name.compare(0, 9, "operator ") != 0 ||
			    (*it)->owner == NULL)
				continue;
			TypePtr pending_record = class_record_for_member(*it);
			if (owner_record.get() != NULL &&
			    pending_record.get() != NULL &&
			    record_has_base(owner_record, pending_record))
			{
				pos = it;
				break;
			}
		}
	}
}

void ProgramLowerer::place_ranked_owner_member(
	const Binding* binding, ProgramLowerer::PendingInlineIterator& pos)
{
	map<const Binding*, size_t>::const_iterator binding_rank =
		inline_definition_ranks.find(binding);
	bool operator_function = binding->name.compare(0, 8, "operator") == 0;
	if (binding_rank != inline_definition_ranks.end() &&
	    binding->owner != NULL &&
	    !binding->is_generated_copy_move_assignment &&
	    !operator_function)
		for (PendingInlineIterator it = pending_inline_definitions.begin();
		     it != pending_inline_definitions.end(); ++it)
		{
			map<const Binding*, size_t>::const_iterator pending_rank =
				inline_definition_ranks.find(*it);
			if (pending_rank != inline_definition_ranks.end() &&
			    (*it)->owner == binding->owner &&
			    !(*it)->is_generated_copy_move_assignment &&
			    pending_rank->second > binding_rank->second)
			{
				pos = it;
				break;
			}
		}
}

void ProgramLowerer::place_before_late_operator_or_generated_assignment(
	const Binding* binding, ProgramLowerer::PendingInlineIterator& pos)
{
	if (binding->name != "operator[]" &&
	    (binding->name.empty() || binding->name[0] != '~'))
		for (PendingInlineIterator it = pending_inline_definitions.begin();
		     it != pending_inline_definitions.end(); ++it)
			if ((*it)->name == "operator[]" ||
			    (generated_assignment_emit_depth == 0 &&
			     (*it)->is_generated_copy_move_assignment))
			{
				pos = it;
				break;
	}
}

void ProgramLowerer::place_subscript_before_pending_operators(
	const Binding* binding,
	ProgramLowerer::PendingInlineIterator& pos)
{
	if (binding->name != "operator[]")
		return;
	for (PendingInlineIterator it = pending_inline_definitions.begin();
	     it != pending_inline_definitions.end(); ++it)
		if ((*it)->name.compare(0, 8, "operator") == 0)
		{
			pos = it;
			break;
		}
}

void ProgramLowerer::place_active_destructor_dependency(
	const Binding* binding, ProgramLowerer::PendingInlineIterator& pos)
{
	if (active_inline_definition != NULL &&
	    active_inline_definition->name.size() > 0 &&
	    active_inline_definition->name[0] == '~' &&
	    binding != active_inline_definition &&
	    binding_has_template_specialization_context(active_inline_definition))
	{
		size_t index = active_inline_dependency_insert_count;
		if (index > pending_inline_definitions.size())
			index = pending_inline_definitions.size();
		pos = pending_inline_definitions.begin() + index;
		++active_inline_dependency_insert_count;
	}
}

void ProgramLowerer::insert_pending_inline_definition(const Binding* binding)
{
	PendingInlineIterator pos = pending_inline_definitions.end();
	place_lvalue_assignment_before_rvalue_assignment(binding, pos);
	place_user_assignment_before_owner_members(binding, pos);
	place_record_return_before_matching_constructor(binding, pos);
	place_record_return_before_owner_scalar_member(binding, pos);
	place_constructor_inline_definition(binding, pos);
	place_destructor_inline_definition(binding, pos);
	place_const_conversion_before_mutable_conversion(binding, pos);
	place_specialized_conversion_before_base_conversion(binding, pos);
	place_ranked_owner_member(binding, pos);
	place_subscript_before_pending_operators(binding, pos);
	place_before_late_operator_or_generated_assignment(binding, pos);
	place_active_destructor_dependency(binding, pos);
	pending_inline_definitions.insert(pos, binding);
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
		string base_ctor_name;
		bool base_ctor_complete = false;
		if (base_ctor != NULL)
		{
			base_ctor_complete = !base_ctor->is_generated_default_constructor;
			base_ctor_name = base_ctor_complete
				? symbol_for(base_ctor)
				: constructor_symbol_for(base_ctor, true);
		}
		if (base_ctor != NULL &&
		    defined_functions.find(base_ctor_name) ==
		    defined_functions.end() &&
		    inline_definitions.find(base_ctor) != inline_definitions.end())
		{
			demand_inline_function(base_ctor, base_ctor_complete);
			vector<const Binding*>::iterator retry =
				find(pending_inline_definitions.begin(),
				     pending_inline_definitions.end(),
				     base_ctor);
			if (retry != pending_inline_definitions.end())
				++retry;
			else
				retry = pending_inline_definitions.begin();
			pending_inline_definitions.insert(retry, binding);
			continue;
		}
		string name = symbol_for(binding);
		bool class_ctor = is_class_constructor(binding);
		bool class_dtor = is_class_destructor_binding(binding);
		bool need_complete =
			!class_ctor ||
			demanded_inline_complete_entries.find(binding) !=
			demanded_inline_complete_entries.end();
		bool need_base =
			(class_ctor &&
			 demanded_constructor_base_entries.find(binding) !=
			 demanded_constructor_base_entries.end()) ||
			(class_dtor &&
			 demanded_destructor_base_entries.find(binding) !=
			 demanded_destructor_base_entries.end());
		if (defined_functions.find(name) != defined_functions.end())
			need_complete = false;
		if (defined_functions.find(name + "__base_entry") !=
		    defined_functions.end())
			need_base = false;
		if (!need_complete && !need_base)
			continue;
		if (need_complete)
			defined_functions.insert(name);
		if (need_base)
			defined_functions.insert(name + "__base_entry");
		const Binding* saved_active = active_inline_definition;
		size_t saved_dependency_insert_count =
			active_inline_dependency_insert_count;
		active_inline_definition = binding;
		active_inline_dependency_insert_count = 0;
		FunctionLowerer lowerer(*this, *found->second);
		if (binding->is_generated_copy_move_assignment)
			++generated_assignment_emit_depth;
		FunctionOut lowered = lowerer.lower();
		if (binding->is_generated_copy_move_assignment)
			--generated_assignment_emit_depth;
		active_inline_definition = saved_active;
		active_inline_dependency_insert_count = saved_dependency_insert_count;
		if (!binding->name.empty() && binding->name[0] == '~' &&
		    !binding_has_template_specialization_context(binding))
			emit_pending_inline_definitions();
		if (need_base)
			functions.push_back(make_constructor_base_entry(lowered, name));
		if (need_complete)
			functions.push_back(lowered);
		emit_pending_synthetic_assignment_functions();
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
				if (internal::starts_with(extra[j].line, "variable "))
				{
					if (extra[j].binding != NULL)
					{
						pa11::TypePtr node_type =
							extra[j].type.get() != NULL
							? extra[j].type : extra[j].binding->type;
							pa11::TypePtr object = internal::strip_for_value(node_type);
						pa11::TypePtr bare = pa11::strip_cv(object);
							bool braced_storage = !extra[j].children.empty() &&
								internal::starts_with(extra[j].children[0].line,
								                      "braced-init-list");
						if (extra[j].binding->is_dependent_template_artifact &&
						    (bare->kind == pa11::TypeKind::Array ||
						     bare->kind == pa11::TypeKind::Record ||
						     braced_storage))
							continue;
						if (bare->kind == pa11::TypeKind::Array ||
						    bare->kind == pa11::TypeKind::Record ||
						    braced_storage)
								program.deferred_global_definitions[extra[j].binding] = extra[j];
						else
							program.collect_node(extra[j]);
					}
				}
			for (size_t j = 0; j < extra.size(); ++j)
			{
				if (extra[j].binding == NULL ||
				    !extra[j].binding->is_object_root)
				continue;
			program.demand_inline_function(extra[j].binding);
			program.emit_pending_inline_definitions();
		}
		for (size_t j = 0; j < extra.size(); ++j)
		{
			if (!internal::early_hidden_friend_definition(extra[j], direct_calls))
				continue;
			program.demand_inline_function(extra[j].binding);
			program.emit_pending_inline_definitions();
			}
			program.collect_translation_unit(parser->root());
			for (size_t j = 0; j < extra.size(); ++j)
			{
			if (!internal::generated_copy_move_constructor_node(extra[j]))
				continue;
			program.demand_inline_function(extra[j].binding);
			set<const pa11::Binding*> generated_calls;
			internal::collect_direct_calls(extra[j], generated_calls);
				for (set<const pa11::Binding*>::const_iterator it = generated_calls.begin();
				     it != generated_calls.end(); ++it)
				program.demand_inline_function(*it);
		}
		program.emit_pending_inline_definitions();
		program.emit_pending_synthetic_assignment_functions();
		parsers.push_back(std::move(parser));
	}
	program.emit_global_lifecycle_functions();
	program.write(outfile);
}
}  // namespace pa14
