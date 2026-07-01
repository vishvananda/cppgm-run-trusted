#include "pa14_lowir_internal.h"
#include "pa14_lowir_function_internal.h"
#include "pa12_templates_function_support.h"
#include "pa12_types_support.h"

#include <algorithm>
#include <cctype>
#include <fstream>
#include <utility>

namespace pa14 {
namespace internal {

void append_assignment_dependency_members(TypePtr record, vector<Binding*>& members);
uint64_t assignment_storage_copy_limit(TypePtr record);
uint64_t assignment_member_storage_end(Binding* member);

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

bool lowir_signature_needs_incomplete_record_layout(TypePtr type)
{
	if (type.get() == NULL)
		return false;
	if (is_reference(type))
		return false;
	TypePtr bare = pa11::strip_cv(type);
	return bare->kind == TypeKind::Record && !bare->complete;
}

bool lowir_signature_needs_incomplete_record_layout(const Binding* binding)
{
	if (binding == NULL ||
	    binding->type.get() == NULL ||
	    binding->type->kind != TypeKind::Function)
		return false;
	if (lowir_signature_needs_incomplete_record_layout(binding->type->base))
		return true;
	for (size_t i = 0; i < binding->type->parameters.size(); ++i)
		if (lowir_signature_needs_incomplete_record_layout(
			    binding->type->parameters[i]))
			return true;
	return false;
}

bool lowir_skip_function_definition_node(const Node& node)
{
	return node.token_text == "deleted" ||
	       (node.binding != NULL &&
	        !pa12::internal::substituted_type_is_valid(node.binding->type));
}

bool record_vector_contains(const vector<TypePtr>& records, TypePtr record)
{
	record = record.get() != NULL ? pa11::strip_cv(record) : TypePtr();
	if (record.get() == NULL || record->kind != TypeKind::Record)
		return false;
	for (size_t i = 0; i < records.size(); ++i)
		if (pa11::same_type(records[i], record))
			return true;
	return false;
}

void collect_template_specialization_records(TypePtr type,
                                             vector<TypePtr>& out)
{
	if (type.get() == NULL)
		return;
	TypePtr bare = pa11::strip_cv(type);
	if (bare->kind == TypeKind::Record &&
	    record_is_template_specialization(bare))
	{
		if (!record_vector_contains(out, bare))
			out.push_back(bare);
		return;
	}
	if (bare->kind == TypeKind::Pointer ||
	    bare->kind == TypeKind::LValueReference ||
	    bare->kind == TypeKind::RValueReference ||
	    bare->kind == TypeKind::Array)
	{
		collect_template_specialization_records(bare->base, out);
		return;
	}
	if (bare->kind == TypeKind::MemberPointer)
	{
		collect_template_specialization_records(bare->member_class, out);
		collect_template_specialization_records(bare->base, out);
		return;
	}
	if (bare->kind == TypeKind::Function)
	{
		collect_template_specialization_records(bare->base, out);
		for (size_t i = 0; i < bare->parameters.size(); ++i)
			collect_template_specialization_records(bare->parameters[i],
			                                        out);
	}
}

void collect_owner_template_specialization_records(const Binding* binding,
                                                   vector<TypePtr>& out)
{
	if (binding == NULL)
		return;
	for (Scope* scope = binding->owner; scope != NULL; scope = scope->parent)
	{
		if (scope->kind != ScopeKind::Class)
			continue;
		TypePtr record = pa11::record_type_for_scope(scope);
		record = record.get() != NULL ? pa11::strip_cv(record) : TypePtr();
		if (record_is_template_specialization(record) &&
		    !record_vector_contains(out, record))
			out.push_back(record);
	}
}

string static_member_demand_order_key(const Binding* binding)
{
	if (binding == NULL)
		return string();
	string object = global_object_symbol(binding);
	if (!object.empty())
		return "O:" + object;
	return "N:" + binding->name + ":" +
	       (binding->type.get() != NULL ? pa11::describe_type(binding->type)
	                                    : string());
}

bool static_member_demand_less(const Binding* left, const Binding* right)
{
	string lkey = static_member_demand_order_key(left);
	string rkey = static_member_demand_order_key(right);
	return lkey != rkey ? lkey < rkey : false;
}

bool binding_set_contains_constructor_or_alias(
	const set<const Binding*>& bindings,
	const Binding* binding)
{
	if (binding == NULL)
		return false;
	if (bindings.count(binding) != 0)
		return true;
	const Binding* canonical = canonical_constructor_binding(binding);
	if (canonical != NULL && bindings.count(canonical) != 0)
		return true;
	if (binding->aliased_binding != NULL &&
	    bindings.count(binding->aliased_binding) != 0)
		return true;
	if (canonical != NULL &&
	    canonical->aliased_binding != NULL &&
	    bindings.count(canonical->aliased_binding) != 0)
		return true;
	if (binding->kind != BindingKind::Function)
		return false;
	string object = global_object_symbol(binding);
	string specialization = binding->function_specialization_symbol;
	if (specialization.empty() && binding->aliased_binding != NULL)
		specialization =
			binding->aliased_binding->function_specialization_symbol;
	for (set<const Binding*>::const_iterator it = bindings.begin();
	     it != bindings.end();
	     ++it)
	{
		const Binding* candidate = *it;
		if (candidate == NULL || candidate->kind != BindingKind::Function)
			continue;
		string candidate_object = global_object_symbol(candidate);
		if (!object.empty() && object == candidate_object)
			return true;
		string candidate_specialization =
			candidate->function_specialization_symbol;
		if (candidate_specialization.empty() &&
		    candidate->aliased_binding != NULL)
			candidate_specialization =
				candidate->aliased_binding
					->function_specialization_symbol;
		if (!specialization.empty() &&
		    specialization == candidate_specialization)
			return true;
	}
	return false;
}

void demand_complete_static_downcast_source_constructors(
	ProgramLowerer& program,
	TypePtr record)
{
	if (record.get() == NULL ||
	    record->kind != TypeKind::Record)
		return;
	vector<const Binding*> demanded;
	for (set<const Binding*>::const_iterator it =
		     program.demanded_constructor_base_entries.begin();
	     it != program.demanded_constructor_base_entries.end();
	     ++it)
	{
		const Binding* ctor = *it;
		if (!is_class_constructor_binding(ctor))
			continue;
		TypePtr owner = class_record_for_member(ctor);
		owner = owner.get() != NULL ? pa11::strip_cv(owner) : TypePtr();
		if (owner.get() != NULL &&
		    owner->kind == TypeKind::Record &&
		    pa11::same_type(owner, record))
			demanded.push_back(ctor);
	}
	for (size_t i = 0; i < demanded.size(); ++i)
		program.demand_inline_function(demanded[i], true);
	if (record->scope == NULL)
		return;
	map<string, vector<Binding*> >::const_iterator ctors =
		record->scope->members.find(record->scope->name);
	if (ctors == record->scope->members.end())
		return;
	for (size_t i = 0; i < ctors->second.size(); ++i)
	{
		Binding* ctor = ctors->second[i];
		if (!is_class_constructor_binding(ctor))
			continue;
		TypePtr owner = class_record_for_member(ctor);
		owner = owner.get() != NULL ? pa11::strip_cv(owner) : TypePtr();
		if (owner.get() == NULL || !pa11::same_type(owner, record))
			continue;
		if (binding_set_contains_constructor_or_alias(
			    program.demanded_constructor_base_entries, ctor))
			program.demand_inline_function(ctor, true);
	}
}

}  // namespace

ProgramLowerer::ProgramLowerer(bool native, bool host_object)
	: inline_definition_lookup_cache_size(0),
	  inline_definition_member_lookup_cache_size(0),
	  emitting_inline_definitions(false),
	  active_inline_definition(NULL),
	  active_inline_dependency_insert_count(0),
	  native_lowering(native),
	  host_object_lowering(host_object),
	  needs_empty_init_function(false),
	  needs_eh_declarations(false),
	  generated_assignment_emit_depth(0)
{
}

void rank_inline_definition(ProgramLowerer& program, const Binding* binding)
{
	if (binding == NULL)
		return;
	if (program.inline_definition_ranks.find(binding) ==
	    program.inline_definition_ranks.end())
		program.inline_definition_ranks[binding] =
			program.inline_definition_ranks.size();
}

void ProgramLowerer::mark_static_downcast_source_record(TypePtr record)
{
	TypePtr bare = record.get() != NULL ? pa11::strip_cv(record) : TypePtr();
	if (bare.get() == NULL || bare->kind != TypeKind::Record)
		return;
	bool inserted = static_downcast_source_records.insert(bare.get()).second;
	TypePtr scoped = bare->scope != NULL
		? pa11::record_type_for_scope(bare->scope) : TypePtr();
	scoped = scoped.get() != NULL ? pa11::strip_cv(scoped) : TypePtr();
	if (scoped.get() != NULL && scoped->kind == TypeKind::Record)
		inserted = static_downcast_source_records.insert(scoped.get()).second ||
			inserted;
	if (inserted)
	{
		demand_complete_static_downcast_source_constructors(*this, bare);
		if (scoped.get() != NULL && scoped.get() != bare.get())
			demand_complete_static_downcast_source_constructors(*this,
			                                                    scoped);
	}
}

bool ProgramLowerer::is_static_downcast_source_record(TypePtr record) const
{
	TypePtr bare = record.get() != NULL ? pa11::strip_cv(record) : TypePtr();
	if (bare.get() == NULL || bare->kind != TypeKind::Record)
		return false;
	if (static_downcast_source_records.find(bare.get()) !=
	    static_downcast_source_records.end())
		return true;
	for (set<const void*>::const_iterator it =
		     static_downcast_source_records.begin();
	     it != static_downcast_source_records.end();
	     ++it)
	{
		const pa11::Type* marked =
			static_cast<const pa11::Type*>(*it);
		if (marked == NULL || marked->kind != TypeKind::Record)
			continue;
		if (marked->scope != NULL && marked->scope == bare->scope)
			return true;
		if (marked->scope == NULL)
			continue;
		TypePtr marked_record = pa11::record_type_for_scope(marked->scope);
		marked_record = marked_record.get() != NULL
			? pa11::strip_cv(marked_record) : TypePtr();
		if (marked_record.get() != NULL &&
		    marked_record->kind == TypeKind::Record &&
		    pa11::same_type(marked_record, bare))
			return true;
	}
	return false;
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
	if (scalar_lowir_type(type) == "ptr" &&
	    starts_with(init.line, "literal") &&
	    init.has_constant_value &&
	    init.constant_value == 0)
		return "zero";
	if (starts_with(init.line, "id-expression") && init.binding != NULL &&
	    scalar_lowir_type(type) == "ptr")
	{
		if (init.binding->kind == BindingKind::Function &&
		    init.binding->is_inline_definition)
			demand_inline_function(init.binding);
		if (init.binding->kind == BindingKind::Function)
			demand_function_declaration(init.binding);
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
		demand_function_declaration(init.children[0].binding);
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
		if (value == "zero" || value == "0" || value == "nullptr")
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
	{
		if (template_static_member_definition_matches(binding, it->first))
		{
			if (matching_definition != NULL &&
			    matching_definition != it->first)
				return;
			matching_definition = it->first;
		}
	}
	if (matching_definition != NULL)
	{
		map<const Binding*, Node>::iterator deferred =
			deferred_global_definitions.find(matching_definition);
		if (deferred != deferred_global_definitions.end())
		{
			Node node = deferred->second;
			deferred_global_definitions.erase(deferred);
			if (matching_definition != binding &&
			    matching_definition->is_dependent_template_artifact)
			{
				node.binding = const_cast<Binding*>(binding);
				node.type = binding->type;
				node.line = "variable " + binding->name + " " +
				            pa11::describe_type(binding->type);
			}
			else
				symbols[binding] = symbol_for(matching_definition);
			emit_global(node);
		}
		else
			symbols[binding] = symbol_for(matching_definition);
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
	TypePtr object = strip_for_value(binding->type);
	TypePtr bare = pa11::strip_cv(object);
	if (binding->is_static_member &&
	    binding->is_template_static_member_definition &&
	    (bare->kind == TypeKind::Array || bare->kind == TypeKind::Record))
	{
		Node node("variable " + binding->name + " " +
		          pa11::describe_type(binding->type));
		node.binding = const_cast<Binding*>(binding);
		node.type = binding->type;
		emit_global(node);
		return;
	}
	if (declared_globals.find(name) != declared_globals.end())
		return;
	ostringstream out;
	out << "declare global @" << name;
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
	const Binding* matching_definition = NULL;
	for (map<const Binding*, Node>::const_iterator it =
		     deferred_global_definitions.begin();
	     it != deferred_global_definitions.end();
	     ++it)
		if (template_static_member_definition_matches(binding, it->first))
		{
			if (matching_definition != NULL &&
			    matching_definition != it->first)
				return false;
			matching_definition = it->first;
		}
	if (matching_definition != NULL && matching_definition != binding)
	{
		bool instantiate_dependent_initializer =
			matching_definition->is_dependent_template_artifact;
		if (!instantiate_dependent_initializer)
		{
			symbols[binding] = symbol_for(matching_definition);
			binding = matching_definition;
			name = symbol_for(binding);
		}
		if (defined_globals.find(name) != defined_globals.end())
			return true;
	}
	map<const Binding*, Node>::iterator deferred =
		deferred_global_definitions.find(
			matching_definition != NULL &&
			matching_definition->is_dependent_template_artifact
				? matching_definition : binding);
	if (deferred == deferred_global_definitions.end())
	{
		pending_deferred_global_definition_demands.insert(binding);
		return false;
	}
	Node node = deferred->second;
	deferred_global_definitions.erase(deferred);
	if (matching_definition != NULL &&
	    matching_definition != binding &&
	    matching_definition->is_dependent_template_artifact)
	{
		node.binding = const_cast<Binding*>(binding);
		node.type = binding->type;
		node.line = "variable " + binding->name + " " +
		            pa11::describe_type(binding->type);
	}
	emit_global(node);
	return true;
}

bool ProgramLowerer::deferred_global_definition_demanded(
	const Binding* binding) const
{
	if (binding == NULL)
		return false;
	for (set<const Binding*>::const_iterator it =
		     pending_deferred_global_definition_demands.begin();
	     it != pending_deferred_global_definition_demands.end();
	     ++it)
		if (*it == binding ||
		    template_static_member_definition_matches(*it, binding))
			return true;
	return false;
}

bool ProgramLowerer::template_static_member_constant_load_required(
	const Binding* binding) const
{
	if (binding == NULL || !binding->is_template_static_member_definition)
		return false;
	return binding->is_template_static_member_explicit_definition;
}

void ProgramLowerer::demand_template_static_member_definitions_for_function(
	const Binding* binding)
{
	if (binding == NULL ||
	    binding->kind != BindingKind::Function)
		return;
	vector<TypePtr> associated_records;
	if (!is_class_constructor_binding(binding) &&
	    !is_class_destructor_binding(binding))
		collect_owner_template_specialization_records(binding,
		                                              associated_records);
	if (binding->is_hidden_friend && binding->type.get() != NULL)
		collect_template_specialization_records(binding->type,
		                                        associated_records);
	if (associated_records.empty())
		return;
	vector<const Binding*> demands;
	for (map<const Binding*, Node>::const_iterator it =
		     deferred_global_definitions.begin();
	     it != deferred_global_definitions.end();
	     ++it)
	{
		const Binding* member = it->first;
		if (member == NULL ||
		    !member->is_static_member ||
		    !member->is_template_static_member_definition)
			continue;
		TypePtr member_object = strip_for_value(member->type);
		TypePtr member_bare = pa11::strip_cv(member_object);
		if (member->is_constexpr &&
		    member_bare->kind != TypeKind::Array &&
		    member_bare->kind != TypeKind::Record)
			continue;
		TypePtr owner = class_record_for_member(member);
		if (record_vector_contains(associated_records, owner))
			demands.push_back(member);
	}
	stable_sort(demands.begin(), demands.end(), static_member_demand_less);
	for (size_t i = 0; i < demands.size(); ++i)
		demand_deferred_global_definition(demands[i]);
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

void ProgramLowerer::ensure_atexit_declaration()
{
	if (!declared_functions.insert("__external_runtime_atexit").second)
		return;
	declares.push_back(
		"declare function @__external_runtime_atexit"
		"(%arg0 : ptr) -> i32 [unwind=no, linkage=c, "
		"binding=strong, object=atexit]");
}

void ProgramLowerer::ensure_eh_declarations()
{
	if (needs_eh_declarations)
		return;
	needs_eh_declarations = true;
	if (declared_functions.insert("__external_runtime___Unwind_Resume").second)
		declares.push_back(
			"declare function @__external_runtime___Unwind_Resume() -> void "
			"[return=noreturn, role=eh_resume, linkage=c, binding=strong, "
			"object=_Unwind_Resume]");
	if (declared_functions.insert("__external_runtime____gxx_personality_v0").second)
		declares.push_back(
			"declare function @__external_runtime____gxx_personality_v0() "
			"-> void [role=eh_personality, linkage=c, binding=strong, "
			"object=__gxx_personality_v0]");
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

bool synthetic_assignment_has_bitfield(TypePtr record)
{
	for (size_t i = 0; i < record->fields.size(); ++i)
		if (record->fields[i]->is_bit_field)
			return true;
	return false;
}

void append_synthetic_bitfield_assignment(Block& block, TypePtr record)
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
		block.instrs.push_back("    " + other_field + " = index i8 " +
		                       other + ", " + to_string(field->member_offset));
		block.instrs.push_back("    " + value + " = load " + low_type +
		                       " " + other_field);
		block.instrs.push_back("    " + self + " = load ptr $this");
		block.instrs.push_back("    " + self_field + " = index i8 " +
		                       self + ", " + to_string(field->member_offset));
		block.instrs.push_back("    store " + low_type + " " + value +
		                       ", " + self_field);
	}
	block.instrs.push_back("    %t" + to_string(temp) + " = load ptr $this");
	block.instrs.push_back("    return ptr %t" + to_string(temp));
}

Binding* synthetic_assignment_member_op(ProgramLowerer& program,
                                        Binding* member,
                                        bool move)
{
	TypePtr field_type = pa11::strip_cv(member->type);
	Binding* op = field_type->kind == TypeKind::Record
		? program.demand_implicit_copy_assignment(field_type, move)
		: find_assignment_binding(member->type, move);
	if (op == NULL && move)
		op = field_type->kind == TypeKind::Record
			? program.demand_implicit_copy_assignment(field_type, false)
			: find_assignment_binding(member->type, false);
	return op;
}

vector<pair<Binding*, Binding*> > synthetic_assignment_field_ops(
	ProgramLowerer& program,
	TypePtr record,
	bool move,
	uint64_t& prefix_size)
{
	vector<pair<Binding*, Binding*> > out;
	vector<Binding*> members;
	append_assignment_dependency_members(record, members);
	prefix_size = record->fields.empty() ? 0 : pa11::type_size(record);
	for (size_t i = 0; i < members.size(); ++i)
	{
		Binding* op = synthetic_assignment_member_op(program, members[i], move);
		if (op == NULL)
			continue;
		if (out.empty())
			prefix_size = members[i]->member_offset;
		out.push_back(make_pair(members[i], op));
	}
	return out;
}

void append_synthetic_copyobj(Block& block,
                              int& temp,
                              const string& self,
                              const string& other,
                              uint64_t offset,
                              uint64_t bytes,
                              uint64_t align)
{
	if (bytes == 0)
		return;
	if (offset == 0)
	{
		block.instrs.push_back("    copyobj " + to_string(bytes) + "x" +
		                       to_string(align) + " " + other + ", " + self);
		return;
	}
	string self_chunk = "%t" + to_string(temp++);
	string other_chunk = "%t" + to_string(temp++);
	block.instrs.push_back("    " + self_chunk + " = index i8 " + self +
	                       ", " + to_string(offset));
	block.instrs.push_back("    " + other_chunk + " = index i8 " + other +
	                       ", " + to_string(offset));
	block.instrs.push_back("    copyobj " + to_string(bytes) + "x1 " +
	                       other_chunk + ", " + self_chunk);
}

void append_synthetic_assignment_call(ProgramLowerer& program,
                                      Block& block,
                                      int& temp,
                                      Binding* field,
                                      Binding* op)
{
	program.demand_function_declaration(op);
	if (op->is_inline_definition)
		program.demand_inline_function(op);
	string self_base = "%t" + to_string(temp++);
	string self_field = "%t" + to_string(temp++);
	string other_base = "%t" + to_string(temp++);
	string other_field = "%t" + to_string(temp++);
	string ignored = "%t" + to_string(temp++);
	block.instrs.push_back("    " + self_base + " = load ptr $this");
	block.instrs.push_back("    " + self_field + " = index i8 " +
	                       self_base + ", " + to_string(field->member_offset));
	block.instrs.push_back("    " + other_base + " = load ptr $other");
	block.instrs.push_back("    " + other_field + " = index i8 " +
	                       other_base + ", " + to_string(field->member_offset));
	block.instrs.push_back("    " + ignored + " = call ptr @" +
	                       program.symbol_for(op) + "(" + self_field +
	                       ", " + other_field + ")");
}

void append_synthetic_storage_assignment(ProgramLowerer& program,
                                         Block& block,
                                         TypePtr record,
                                         bool move)
{
	uint64_t prefix_size = 0;
	vector<pair<Binding*, Binding*> > field_ops =
		synthetic_assignment_field_ops(program, record, move, prefix_size);
	int temp = 1;
	string self = "%t" + to_string(temp++);
	string other = "%t" + to_string(temp++);
	block.instrs.push_back("    " + self + " = load ptr $this");
	block.instrs.push_back("    " + other + " = load ptr $other");
	append_synthetic_copyobj(block, temp, self, other, 0, prefix_size,
	                         pa11::type_align(record));
	uint64_t cursor = prefix_size;
	for (size_t i = 0; i < field_ops.size(); ++i)
	{
		Binding* field = field_ops[i].first;
		uint64_t offset = field->member_offset;
		append_synthetic_copyobj(block, temp, self, other, cursor,
		                         offset > cursor ? offset - cursor : 0, 1);
		append_synthetic_assignment_call(program, block, temp, field,
		                                 field_ops[i].second);
		uint64_t end = assignment_member_storage_end(field);
		if (end > cursor)
			cursor = end;
	}
	uint64_t total = field_ops.empty()
		? pa11::type_size(record)
		: assignment_storage_copy_limit(record);
	append_synthetic_copyobj(block, temp, self, other, cursor,
	                         total > cursor ? total - cursor : 0, 1);
	string ret = "%t" + to_string(temp++);
	block.instrs.push_back("    " + ret + " = load ptr $this");
	block.instrs.push_back("    return ptr " + ret);
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
	if (synthetic_assignment_has_bitfield(record))
		append_synthetic_bitfield_assignment(block, record);
	else
		append_synthetic_storage_assignment(*this, block, record, move);
	block.terminated = true;
	out.blocks.push_back(block);
	pending_synthetic_assignment_functions.push_back(out);
}

void ProgramLowerer::emit_pending_synthetic_assignment_functions()
{
	if (pending_synthetic_constructor_functions.empty() &&
	    pending_synthetic_assignment_functions.empty())
		return;
	emit_pending_generated_aggregate_constructors();
	if (pending_synthetic_constructor_functions.empty() &&
	    pending_synthetic_assignment_functions.empty())
		return;
	functions.insert(functions.end(),
	                 pending_synthetic_constructor_functions.begin(),
	                 pending_synthetic_constructor_functions.end());
	pending_synthetic_constructor_functions.clear();
	functions.insert(functions.end(),
	                 pending_synthetic_assignment_functions.begin(),
	                 pending_synthetic_assignment_functions.end());
	pending_synthetic_assignment_functions.clear();
}

namespace {

void collect_variable_node(ProgramLowerer& program, const Node& node)
{
	if (node.binding != NULL &&
	    node.binding->is_dependent_template_artifact)
	{
		if (node.binding->is_static_member && !node.children.empty())
			program.deferred_global_definitions[node.binding] = node;
		return;
	}
	if (node.binding != NULL &&
	    ((node.binding->owner != NULL &&
	      node.binding->owner->kind == ScopeKind::Namespace) ||
	     node.binding->is_static_member))
	{
		if (defer_static_constexpr_member_definition(node))
		{
			string name = program.symbol_for(node.binding);
			if (program.defined_globals.find(name) !=
			        program.defined_globals.end() ||
			    program.deferred_global_definition_demanded(node.binding))
				program.emit_global(node);
			else
				program.deferred_global_definitions[node.binding] = node;
			return;
		}
		if (node.binding->is_template_static_member_definition &&
		    node.children.empty())
		{
			TypePtr object = strip_for_value(node.binding->type);
			TypePtr bare = pa11::strip_cv(object);
			if (bare->kind == TypeKind::Array ||
			    bare->kind == TypeKind::Record)
			{
				program.emit_global(node);
				return;
			}
			string name = program.symbol_for(node.binding);
			if (program.declared_globals.find(name) !=
			    program.declared_globals.end())
			{
				program.emit_global(node);
				return;
			}
			if (program.deferred_global_definition_demanded(node.binding))
				program.emit_global(node);
			else
				program.deferred_global_definitions[node.binding] = node;
			return;
		}
		TypePtr object = strip_for_value(node.binding->type);
		TypePtr bare = pa11::strip_cv(object);
		if (node.binding->is_static_member &&
		    node.binding->has_constant &&
		    bare->kind != TypeKind::Array &&
		    bare->kind != TypeKind::Record)
		{
			string name = program.symbol_for(node.binding);
			if (program.declared_globals.find(name) !=
			    program.declared_globals.end())
			{
				program.emit_global(node);
				return;
			}
			if (bare->kind == TypeKind::Fundamental &&
			    bare->fundamental == FT_BOOL &&
			    !node.binding->is_constexpr)
			{
				program.emit_global(node);
				return;
			}
			if (program.deferred_global_definition_demanded(node.binding))
				program.emit_global(node);
			else
				program.deferred_global_definitions[node.binding] = node;
			return;
		}
		program.emit_global(node);
	}
}

void collect_function_definition_node(ProgramLowerer& program,
                                      const Node& node)
{
	if (lowir_skip_function_definition_node(node))
		return;
	if (node.binding != NULL &&
	    node.binding->is_inline_definition &&
	    !node.binding->is_explicit_defaulted_definition)
	{
		program.register_inline_definition(node);
		if (node.binding->is_virtual)
		{
			TypePtr record = class_record_for_member(node.binding);
			if (record.get() != NULL)
				program.demand_vtable(record);
		}
		return;
	}
	if (node.binding != NULL)
	{
		string function_name = program.symbol_for(node.binding);
		if (program.defined_functions.find(function_name) !=
		    program.defined_functions.end())
			return;
		program.defined_functions.insert(function_name);
	}
	if (node.binding != NULL && node.binding->is_virtual)
	{
		TypePtr record = class_record_for_member(node.binding);
		if (record.get() != NULL)
			program.demand_vtable(record);
	}
	FunctionLowerer lowerer(program, node);
	FunctionOut lowered = lowerer.lower();
	if (is_class_constructor_binding(node.binding))
	{
		string name = program.symbol_for(node.binding);
		string base_name = name + "__base_entry";
		if (program.defined_functions.insert(base_name).second)
			program.functions.push_back(
				make_constructor_base_entry(lowered, name));
	}
	if (is_class_destructor_binding(node.binding))
	{
		string name = program.symbol_for(node.binding);
		string base_name = name + "__base_entry";
		if (program.defined_functions.insert(base_name).second)
		{
			FunctionLowerer base_lowerer(program, node, true);
			FunctionOut base_lowered = base_lowerer.lower();
			program.functions.push_back(
				make_destructor_base_entry(base_lowered,
				                           name,
				                           program.native_lowering));
		}
	}
	if (node.binding != NULL &&
	    node.binding->owner != NULL &&
	    node.binding->owner->kind == ScopeKind::Class &&
	    !node.binding->name.empty() &&
	    node.binding->name[0] == '~' &&
	    node.binding->is_noop_destructor &&
	    program.native_lowering)
	{
		FunctionOut noop_entry = lowered;
		string name = program.symbol_for(node.binding);
		noop_entry.name = name + "__noop_entry";
		string from = "function @" + name + "(";
		string to = "function @" + name + "__noop_entry(";
		size_t pos = noop_entry.header.find(from);
		if (pos != string::npos)
			noop_entry.header.replace(pos, from.size(), to);
		program.functions.push_back(noop_entry);
	}
	program.functions.push_back(lowered);
	program.emit_pending_synthetic_assignment_functions();
}

}  // namespace

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
		collect_variable_node(*this, node);
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
		collect_function_definition_node(*this, node);
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
	if (lowir_signature_needs_incomplete_record_layout(binding))
		return;
	if (!pa12::internal::substituted_type_is_valid(binding->type))
		return;
	string name = symbol_for(binding);
	if (function_declarations_by_binding.find(binding) !=
	    function_declarations_by_binding.end())
		return;
	if (lowir_synthesizable_hosted_inline_body(binding) &&
	    synthetic_inline_definitions.find(binding) ==
		    synthetic_inline_definitions.end() &&
	    inline_definitions.find(binding) == inline_definitions.end())
	{
		synthetic_inline_definitions[binding] =
			lowir_make_hosted_inline_body_node(binding);
		rank_inline_definition(*this, binding);
		inline_definitions[binding] =
			&synthetic_inline_definitions[binding];
		demanded_inline_complete_entries.insert(binding);
		insert_pending_inline_definition(binding);
	}
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
			hidden_virtual_bases_for_function_parameter(
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
		   ? hidden_virtual_bases_for_function_parameter(
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
		string object_symbol = global_object_symbol(binding);
		metadata.push_back("object=" + object_symbol);
	}
	out << metadata_suffix(metadata);
	function_declarations_by_binding[binding] = out.str();
}

namespace {
bool function_definition_has_compound_body(const Node& node)
{
	for (size_t i = 0; i < node.children.size(); ++i)
		if (starts_with(node.children[i].line, "compound-statement"))
			return true;
	return false;
}

bool function_definition_has_parameter_nodes(const Node& node)
{
	if (node.binding == NULL ||
	    node.binding->type.get() == NULL ||
	    node.binding->type->kind != TypeKind::Function)
		return function_definition_has_compound_body(node);
	size_t parameters = 0;
	for (size_t i = 0; i < node.children.size(); ++i)
		if (starts_with(node.children[i].line, "parameter "))
			++parameters;
	return parameters >= node.binding->type->parameters.size();
}

bool function_definition_is_complete_body(const Node& node)
{
	return function_definition_has_compound_body(node) &&
	       function_definition_has_parameter_nodes(node);
}

bool function_definition_compound_body_empty(const Node& node)
{
	if (node.children.empty() ||
	    !starts_with(node.children.back().line, "compound-statement") ||
	    !node.children.back().children.empty())
		return false;
	for (size_t i = 0; i + 1 < node.children.size(); ++i)
		if (starts_with(node.children[i].line, "base-init-action") ||
		    starts_with(node.children[i].line, "member-init-action"))
			return false;
	return true;
}

bool synthesized_default_constructor_should_replace(const Node& current,
                                                    const Node& candidate)
{
	Binding* binding = candidate.binding;
	if (binding == NULL ||
	    binding != current.binding ||
	    !binding->is_generated_default_constructor ||
	    !binding->is_defaulted ||
	    binding->owner == NULL ||
	    binding->owner->kind != ScopeKind::Class ||
	    binding->name != binding->owner->name)
		return false;
	return function_definition_compound_body_empty(current) &&
	       !function_definition_compound_body_empty(candidate) &&
	       function_definition_is_complete_body(candidate);
}

bool synthesized_copy_move_constructor_should_replace(const Node& current,
                                                      const Node& candidate)
{
	Binding* binding = candidate.binding;
	if (binding == NULL ||
	    binding != current.binding ||
	    (!binding->is_generated_copy_move_constructor &&
	     candidate.token_text != "copy-move-helper") ||
	    !binding->is_defaulted ||
	    binding->owner == NULL ||
	    binding->owner->kind != ScopeKind::Class ||
	    binding->name != binding->owner->name)
		return false;
	return function_definition_compound_body_empty(current) &&
	       !function_definition_compound_body_empty(candidate) &&
	       function_definition_is_complete_body(candidate);
}
}

void ProgramLowerer::register_inline_definition(const Node& node)
{
	if (node.binding == NULL)
		return;
	if (lowir_skip_function_definition_node(node))
		return;
	if (lowir_extern_template_class_external_binding(node.binding) ||
	    (host_object_lowering &&
	     hosted_external_stream_function_binding(node.binding)))
		return;
	if (node.binding->owner != NULL &&
	    node.binding->owner->kind == ScopeKind::Class &&
	    node.binding->name == node.binding->owner->name)
	{
		if (function_definition_compound_body_empty(node))
		{
			node.binding->is_noop_constructor = true;
			node.binding->unwind_no = true;
		}
		else
			node.binding->is_noop_constructor = false;
	}
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
	rank_inline_definition(*this, node.binding);
	map<const Binding*, const Node*>::iterator existing =
		inline_definitions.find(node.binding);
	if (existing == inline_definitions.end() ||
	    synthesized_default_constructor_should_replace(*existing->second,
	                                                    node) ||
	    synthesized_copy_move_constructor_should_replace(*existing->second,
	                                                     node) ||
	    (binding_has_template_specialization_context(node.binding) &&
	     (!function_definition_is_complete_body(*existing->second) ||
	      function_definition_is_complete_body(node))))
		inline_definitions[node.binding] = &node;
	if (demanded_inline_complete_entries.find(node.binding) !=
	    demanded_inline_complete_entries.end())
		demand_inline_function(node.binding);
	if (demanded_constructor_base_entries.find(node.binding) !=
	        demanded_constructor_base_entries.end() ||
	    demanded_destructor_base_entries.find(node.binding) !=
	        demanded_destructor_base_entries.end())
		demand_inline_function(node.binding, false);
	if (declared_functions.find(symbol_for(node.binding)) != declared_functions.end())
		demand_inline_function(node.binding);
}




}  // namespace internal

}  // namespace pa14
