#include "pa14_lowir_internal.h"
#include "pa12_templates_function_support.h"

namespace pa14 {
namespace internal {

bool constructor_record_contains_hosted_subobject(const Binding* binding); bool hosted_addressed_function_needs_body(const Binding* binding);
Binding* addressed_function_binding(const Node& node); TypePtr function_return_type(const Binding* binding);
bool empty_defaulted_copy_move_constructor_needs_helper(const Node& node);
Binding* call_expression_callee_binding(const Node& node);
bool hosted_bit_const_iterator_deref_binding(const Binding* binding);
bool hosted_bit_const_iterator_preincrement_binding(const Binding* binding);
bool same_binding_or_alias(const Binding* left, const Binding* right);
void collect_global_defaulted_constructor_demands(const Node& node, set<const Binding*>& out, bool in_function);
void collect_explicit_defaulted_definitions(ProgramLowerer& program, const Node& node, const set<const Binding*>* demanded);
bool constructor_set_contains_binding_or_alias(const set<const Binding*>& bindings, const Binding* binding);
void collect_constructor_base_entry_references(ProgramLowerer& program, const Node& node);
void collect_complete_constructor_entry_references(const Node& node, set<const Binding*>& out);
void collect_static_downcast_sources(ProgramLowerer& program, const Node& node);
void append_assignment_dependency_members(TypePtr record, vector<Binding*>& members);
bool should_mark_direct_call_object_root(const Binding* binding,
                                         bool hosted_compatibility);
void collect_hosted_vector_bool_algorithm_dependencies(
	const Binding* binding,
	set<const Binding*>& out);
void collect_node_lowered_constructor_calls(const Node& node,
                                            set<const Binding*>& out);
void collect_body_demand_calls_impl(const Node& node,
                                    set<const Binding*>& out,
                                    bool skip_inline_function_bodies,
                                    TypePtr return_type,
                                    bool skip_return_copy = false);

bool lowir_skip_function_definition_node(const Node& node);
bool default_constructor_call(const Binding* binding);
bool hosted_nested_helper_body_root(const Binding* binding);
void collect_direct_calls(const Node& node, set<const Binding*>& out);
void collect_translation_unit_direct_calls(const Node& node, set<const Binding*>& out);
void collect_addressed_functions(const Node& node, set<const Binding*>& out);
void collect_translation_unit_addressed_functions(const Node& node, set<const Binding*>& out);
void collect_hosted_helper_function_references(const Node& node, set<const Binding*>& out);
void collect_node_implicit_lifecycle_calls(const Node& node, set<const Binding*>& out);
void collect_implicit_lifecycle_calls(const Node& node, set<const Binding*>& out);
void collect_lowered_constructor_calls(const Node& node, set<const Binding*>& out);
void collect_translation_unit_body_demand_calls(const Node& node, set<const Binding*>& out);
void collect_global_variable_constructor_demands(const Node& node, set<const Binding*>& out, bool in_function = false);
void mark_object_root_bindings(const set<const Binding*>& bindings, bool hosted_compatibility, bool body_demand_roots = false);
void note_function_definitions(ProgramLowerer& program, const Node& node);
void collect_base_constructor_calls(const Node& node, set<const Binding*>& out);
bool contains_call_expression(const Node& node);

namespace {
bool generated_copy_move_constructor_node(const Node& node)
{
	if (node.binding == NULL ||
	    (!node.binding->is_generated_copy_move_constructor &&
	     node.token_text != "copy-move-helper"))
		return false;
	if (node.token_text == "copy-move-helper" &&
	    !node.children.empty() &&
	    starts_with(node.children.back().line, "compound-statement") &&
	    node.children.back().children.empty())
		return false;
	bool template_context = false;
	TypePtr owner_record =
		node.binding->owner != NULL &&
		node.binding->owner->kind == ScopeKind::Class
			? pa11::record_type_for_scope(node.binding->owner)
			: TypePtr();
	owner_record = owner_record.get() != NULL
		? pa11::strip_cv(owner_record) : TypePtr();
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
	bool virtual_base_bookkeeping =
		owner_record.get() != NULL &&
		owner_record->kind == TypeKind::Record &&
		!hidden_virtual_bases_for_record(owner_record).empty();
	if (!template_context && !virtual_base_bookkeeping)
		return false;
	if (node.binding->is_defaulted && !contains_call_expression(node))
	{
		TypePtr record = pa11::record_type_for_scope(node.binding->owner);
		record = record.get() != NULL ? pa11::strip_cv(record) : TypePtr();
		if (record.get() != NULL &&
		    !virtual_base_bookkeeping &&
		    !defaulted_copy_move_constructor_needs_helper(
			    node.binding,
			    record))
			return false;
	}
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
					if (pa11::is_reference_type(record->fields[i]->type) ||
					    record->fields[i]->is_reference_member)
						return false;
			}
		}
	return true;
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
struct BindingReferenceIndex
{
	set<const Binding*> bindings;
	set<string> object_symbols;
};
void add_binding_reference(BindingReferenceIndex& index,
                           const Binding* binding)
{
	if (binding == NULL)
		return;
	index.bindings.insert(binding);
	if (binding->aliased_binding != NULL)
		index.bindings.insert(binding->aliased_binding);
	if (binding->kind != BindingKind::Function)
		return;
	string object = global_object_symbol(binding);
	if (!object.empty())
		index.object_symbols.insert(object);
	if (binding->aliased_binding != NULL)
	{
		object = global_object_symbol(binding->aliased_binding);
		if (!object.empty())
			index.object_symbols.insert(object);
	}
}
BindingReferenceIndex make_binding_reference_index(
	const set<const Binding*>& bindings)
{
	BindingReferenceIndex index;
	for (set<const Binding*>::const_iterator it = bindings.begin();
	     it != bindings.end();
	     ++it)
		add_binding_reference(index, *it);
	return index;
}
bool binding_reference_index_contains(const BindingReferenceIndex& index,
                                      const Binding* binding)
{
	if (binding == NULL)
		return false;
	if (index.bindings.count(binding) != 0)
		return true;
	if (binding->aliased_binding != NULL &&
	    index.bindings.count(binding->aliased_binding) != 0)
		return true;
	if (binding->kind != BindingKind::Function)
		return false;
	string object = global_object_symbol(binding);
	if (object.empty() && binding->aliased_binding != NULL)
		object = global_object_symbol(binding->aliased_binding);
	return !object.empty() && index.object_symbols.count(object) != 0;
}
bool early_hidden_friend_definition(const Node& node,
                                    const BindingReferenceIndex& direct_index)
{
	if (node.binding == NULL || !node.binding->is_hidden_friend)
		return false;
	if (binding_reference_index_contains(direct_index, node.binding))
		return true;
	if (node.binding->is_constexpr)
		return false;
	return !contains_call_expression(node) &&
	       !binding_mentions_template_specialization(node.binding);
}
bool extra_variable_has_deferred_storage(const Node& node)
{
	if (node.binding == NULL)
		return false;
	pa11::TypePtr node_type =
		node.type.get() != NULL ? node.type : node.binding->type;
	pa11::TypePtr object = strip_for_value(node_type);
	pa11::TypePtr bare = pa11::strip_cv(object);
	bool braced_storage = !node.children.empty() &&
	                      starts_with(node.children[0].line, "braced-init-list");
	if (node.binding->is_dependent_template_artifact &&
	    (bare->kind == pa11::TypeKind::Array ||
	     bare->kind == pa11::TypeKind::Record ||
	     braced_storage))
		return false;
	return bare->kind == pa11::TypeKind::Array ||
	       bare->kind == pa11::TypeKind::Record ||
	       braced_storage;
}
void collect_extra_variable(ProgramLowerer& program, const Node& node)
{
	if (!starts_with(node.line, "variable ") || node.binding == NULL)
		return;
	if (extra_variable_has_deferred_storage(node))
		program.deferred_global_definitions[node.binding] = node;
	else
		program.collect_node(node);
}
const Node* extra_node_for_binding(const vector<Node>& extra,
                                   const Binding* binding);
	bool referenced_extra_function(const Node& node,
	                               const BindingReferenceIndex& direct_index,
	                               bool hosted_compatibility)
	{
		if (!starts_with(node.line, "function-definition ") ||
		    node.binding == NULL ||
		    lowir_skip_function_definition_node(node) ||
		    node.binding->is_inline_definition)
			return false;
		if (hosted_compatibility &&
		    hosted_library_binding(node.binding) &&
		    !node.binding->is_object_root)
			return false;
		if (node.binding->is_object_root)
			return true;
	return binding_reference_index_contains(direct_index, node.binding);
}
void collect_referenced_extra_function_node(
	ProgramLowerer& program,
	const Node& node,
	const BindingReferenceIndex& direct_index,
	bool hosted_compatibility,
	set<string>& collected)
{
	if (!referenced_extra_function(node,
	                               direct_index,
	                               hosted_compatibility))
		return;
	string name = program.symbol_for(node.binding);
	if (program.defined_functions.find(name) !=
	        program.defined_functions.end() ||
	    !collected.insert(name).second)
		return;
	program.collect_node(node);
}
	void collect_referenced_extra_functions(ProgramLowerer& program,
	                                        const vector<Node>& extra,
	                                        const set<const Binding*>& direct_calls,
	                                        bool hosted_compatibility)
	{
		BindingReferenceIndex direct_index =
			make_binding_reference_index(direct_calls);
		set<string> collected;
		for (size_t i = 0; i < extra.size(); ++i)
		{
			if (extra[i].binding == NULL ||
			    !extra[i].binding->is_object_root)
				continue;
			collect_referenced_extra_function_node(program,
			                                       extra[i],
			                                       direct_index,
			                                       hosted_compatibility,
			                                       collected);
		}
		for (set<const Binding*>::const_iterator it = direct_calls.begin();
		     it != direct_calls.end();
		     ++it)
		{
			const Node* node = extra_node_for_binding(extra, *it);
			if (node == NULL)
				continue;
			collect_referenced_extra_function_node(program,
			                                       *node,
			                                       direct_index,
			                                       hosted_compatibility,
			                                       collected);
		}
	}
	void demand_object_roots(ProgramLowerer& program,
	                         const vector<Node>& extra,
	                         const set<const Binding*>& root_definitions)
	{
		for (size_t i = 0; i < extra.size(); ++i)
		{
			if (extra[i].binding == NULL ||
			    (!extra[i].binding->is_object_root &&
			     extra[i].token_text != "inline-object-root"))
				continue;
			if (extra[i].token_text != "inline-object-root" &&
			    root_definitions.count(extra[i].binding) != 0)
				continue;
			program.demand_inline_function(extra[i].binding);
			program.emit_pending_inline_definitions();
		}
	}
	bool skip_hosted_function_definition(const Node& node,
	                                     bool hosted_compatibility)
	{
		return hosted_compatibility &&
		       starts_with(node.line, "function-definition ") &&
		       hosted_library_binding(node.binding) &&
		       !node.binding->is_object_root &&
		       node.token_text != "inline-object-root";
	}
	void collect_filtered_node(ProgramLowerer& program,
	                           const Node& node,
	                           bool hosted_compatibility)
	{
		if (skip_hosted_function_definition(node, hosted_compatibility))
			return;
		if (starts_with(node.line, "namespace-definition"))
		{
			for (size_t i = 0; i < node.children.size(); ++i)
				collect_filtered_node(program,
				                      node.children[i],
				                      hosted_compatibility);
			return;
		}
		if (starts_with(node.line, "variable ") ||
		    starts_with(node.line, "function-declaration ") ||
		    starts_with(node.line, "function-definition "))
		{
			program.collect_node(node);
			return;
		}
		for (size_t i = 0; i < node.children.size(); ++i)
			collect_filtered_node(program,
			                      node.children[i],
			                      hosted_compatibility);
	}
	void collect_translation_unit_filtered(ProgramLowerer& program,
	                                       const Node& root,
	                                       bool hosted_compatibility)
	{
		for (size_t i = 0; i < root.children.size(); ++i)
			collect_filtered_node(program,
			                      root.children[i],
			                      hosted_compatibility);
		program.emit_pending_inline_definitions();
	}
	void demand_early_hidden_friends(ProgramLowerer& program,
		                                 const vector<Node>& extra,
		                                 const set<const Binding*>& direct_calls)
{
	BindingReferenceIndex direct_index =
		make_binding_reference_index(direct_calls);
	for (size_t i = 0; i < extra.size(); ++i)
	{
		if (!early_hidden_friend_definition(extra[i], direct_index))
			continue;
		program.demand_inline_function(extra[i].binding);
		program.emit_pending_inline_definitions();
		}
	}
	void collect_generated_copy_move_field_constructors(
		const Binding* binding,
		set<const Binding*>& out);
	void demand_referenced_inline_definitions(
		ProgramLowerer& program,
		const set<const Binding*>& direct_calls,
		const set<const Binding*>& complete_constructor_entries)
	{
		for (set<const Binding*>::const_iterator it = direct_calls.begin();
		     it != direct_calls.end();
		     ++it)
		{
			const Binding* binding = *it;
			if (binding == NULL)
				continue;
			if (binding->is_generated_copy_move_constructor)
			{
				set<const Binding*> generated_constructor_deps;
				collect_generated_copy_move_field_constructors(
					binding,
					generated_constructor_deps);
				for (set<const Binding*>::const_iterator dep =
					     generated_constructor_deps.begin();
				     dep != generated_constructor_deps.end();
				     ++dep)
					program.demand_inline_function(*dep);
			}
			bool explicit_noninline_specialization =
				binding->is_explicit_specialization_member &&
				!binding->is_inline_definition;
			bool inline_body =
				binding->is_inline_definition ||
				(binding->aliased_binding != NULL &&
				 binding->aliased_binding->is_inline_definition) ||
				(!explicit_noninline_specialization &&
				 binding_has_template_specialization_context(binding)) ||
				(!explicit_noninline_specialization &&
				 !binding->function_specialization_symbol.empty()) ||
				(binding->aliased_binding != NULL &&
				 !binding->aliased_binding
					  ->is_explicit_specialization_member &&
				 !binding->aliased_binding
					  ->function_specialization_symbol.empty());
			if (inline_body &&
			    is_class_constructor_binding(binding) &&
			    constructor_set_contains_binding_or_alias(
				    program.referenced_constructor_base_entries,
				    binding) &&
			    !constructor_set_contains_binding_or_alias(
				    complete_constructor_entries,
				    binding))
			{
				program.constructor_symbol_for(binding, true);
				program.demand_inline_function(binding, false);
				continue;
			}
			if (inline_body &&
			    hosted_library_binding(binding) &&
			    !hosted_library_body_candidate(binding))
				continue;
			if (inline_body && hosted_library_body_candidate(binding))
			{
				if (is_class_constructor_binding(binding) &&
				    constructor_set_contains_binding_or_alias(
					    program.constructor_base_entry_only_references,
					    binding) &&
				    !constructor_set_contains_binding_or_alias(
					    complete_constructor_entries,
					    binding))
				{
					program.constructor_symbol_for(binding, true);
					program.demand_inline_function(binding, false);
					continue;
				}
					program.demand_inline_function(binding);
			}
			else if (inline_body)
			{
				program.demand_inline_function(binding);
			}
		}
		program.emit_pending_inline_definitions();
	}
	void demand_generated_copy_move_dependencies(ProgramLowerer& program,
	                                             const vector<Node>& extra,
                                             bool hosted_compatibility)
{
	for (size_t i = 0; i < extra.size(); ++i)
	{
		if (!generated_copy_move_constructor_node(extra[i]))
			continue;
		if (hosted_compatibility &&
		    hosted_library_binding(extra[i].binding) &&
		    !extra[i].binding->is_object_root)
			continue;
		program.demand_inline_function(extra[i].binding);
		set<const Binding*> generated_calls;
		collect_direct_calls(extra[i], generated_calls);
		collect_lowered_constructor_calls(extra[i], generated_calls);
		collect_generated_copy_move_field_constructors(extra[i].binding,
		                                               generated_calls);
		for (set<const Binding*>::const_iterator it = generated_calls.begin();
		     it != generated_calls.end(); ++it)
			program.demand_inline_function(*it);
	}
}
void collect_copy_move_member_constructors_for_record(
	TypePtr record,
	bool move,
	set<const Binding*>& out,
	set<const pa11::Type*>& seen_records)
{
	TypePtr bare = record.get() != NULL ? pa11::strip_cv(record) : TypePtr();
	if (bare.get() == NULL ||
	    bare->kind != TypeKind::Record ||
	    !seen_records.insert(bare.get()).second)
		return;
	pa11::layout_record_type(bare);
	vector<TypePtr> bases = pa11::record_direct_bases(bare);
	for (size_t i = 0; i < bases.size(); ++i)
	{
		TypePtr base = bases[i].get() != NULL
			? pa11::strip_cv(bases[i]) : TypePtr();
		if (base.get() == NULL || base->kind != TypeKind::Record)
			continue;
		Binding* ctor = find_copy_move_constructor(base, move);
		if (ctor == NULL && move)
			ctor = find_copy_move_constructor(base, false);
		if (ctor != NULL)
		{
			out.insert(ctor);
			collect_copy_move_member_constructors_for_record(base,
			                                                 move,
			                                                 out,
			                                                 seen_records);
		}
	}
	vector<Binding*> members;
	append_assignment_dependency_members(bare, members);
	for (size_t i = 0; i < members.size(); ++i)
	{
		if (members[i] == NULL)
			continue;
		TypePtr member_type = pa11::strip_cv(members[i]->type);
		if (member_type.get() == NULL ||
		    member_type->kind != TypeKind::Record)
			continue;
		Binding* ctor = find_copy_move_constructor(member_type, move);
		if (ctor == NULL && move)
			ctor = find_copy_move_constructor(member_type, false);
		if (ctor != NULL)
		{
			out.insert(ctor);
			collect_copy_move_member_constructors_for_record(member_type,
			                                                 move,
			                                                 out,
			                                                 seen_records);
		}
	}
}
void collect_generated_copy_move_field_constructors(
	const Binding* binding,
	set<const Binding*>& out)
{
	if (binding == NULL ||
	    !binding->is_generated_copy_move_constructor ||
	    binding->type.get() == NULL ||
	    binding->type->kind != TypeKind::Function ||
	    binding->type->parameters.size() != 2 ||
	    !is_reference(binding->type->parameters[1]))
		return;
	TypePtr record = class_record_for_member(binding);
	bool move = binding->type->parameters[1]->kind == TypeKind::RValueReference;
	set<const pa11::Type*> seen_records;
	collect_copy_move_member_constructors_for_record(record,
	                                                 move,
	                                                 out,
	                                                 seen_records);
}
void collect_generated_copy_move_body_demands(const vector<Node>& extra,
                                              set<const Binding*>& out,
                                              bool hosted_compatibility)
{
	for (size_t i = 0; i < extra.size(); ++i)
	{
		if (!generated_copy_move_constructor_node(extra[i]))
			continue;
		if (hosted_compatibility &&
		    hosted_library_binding(extra[i].binding) &&
		    !extra[i].binding->is_object_root)
			continue;
		if (extra[i].binding != NULL)
			out.insert(extra[i].binding);
		collect_direct_calls(extra[i], out);
		collect_addressed_functions(extra[i], out);
		collect_implicit_lifecycle_calls(extra[i], out);
		collect_lowered_constructor_calls(extra[i], out);
		collect_generated_copy_move_field_constructors(extra[i].binding,
		                                               out);
	}
}
struct ExtraNodeLookupIndex
{
	size_t indexed_size;
	map<const Binding*, size_t> by_binding;
	map<string, size_t> by_symbol;
	map<string, size_t> by_object;

	ExtraNodeLookupIndex() : indexed_size(0) {}
};
typedef pair<const vector<Node>*, pair<size_t, const Binding*> >
	ExtraNodeCacheKey;
map<const vector<Node>*, ExtraNodeLookupIndex>& extra_node_lookup_indexes()
{
	static map<const vector<Node>*, ExtraNodeLookupIndex> indexes;
	return indexes;
}
map<ExtraNodeCacheKey, size_t>& extra_node_lookup_hits()
{
	static map<ExtraNodeCacheKey, size_t> hits;
	return hits;
}
set<ExtraNodeCacheKey>& extra_node_lookup_misses()
{
	static set<ExtraNodeCacheKey> misses;
	return misses;
}
void clear_extra_node_lookup_cache()
{
	extra_node_lookup_indexes().clear();
	extra_node_lookup_hits().clear();
	extra_node_lookup_misses().clear();
}
	const Node* extra_node_for_binding(const vector<Node>& extra,
	                                   const Binding* binding)
{
	map<const vector<Node>*, ExtraNodeLookupIndex>& indexes =
		extra_node_lookup_indexes();
	ExtraNodeLookupIndex& index = indexes[&extra];
	if (index.indexed_size > extra.size())
	{
		index.by_binding.clear();
		index.by_symbol.clear();
		index.by_object.clear();
		index.indexed_size = 0;
	}
	if (index.indexed_size < extra.size())
	{
		for (size_t i = index.indexed_size; i < extra.size(); ++i)
		{
			const Binding* node_binding = extra[i].binding;
			if (node_binding == NULL)
				continue;
			index.by_binding[node_binding] = i;
			if (node_binding->aliased_binding != NULL)
				index.by_binding[node_binding->aliased_binding] = i;
			const string* symbol = &node_binding->function_specialization_symbol;
			if (symbol->empty() && node_binding->aliased_binding != NULL)
				symbol = &node_binding->aliased_binding
					          ->function_specialization_symbol;
			if (!symbol->empty())
				index.by_symbol[*symbol] = i;
			string object = global_object_symbol(node_binding);
			if (!object.empty())
				index.by_object[object] = i;
			if (node_binding->aliased_binding != NULL)
			{
				object = global_object_symbol(node_binding->aliased_binding);
				if (!object.empty())
					index.by_object[object] = i;
			}
		}
		index.indexed_size = extra.size();
	}
	if (binding != NULL)
	{
		map<const Binding*, size_t>::const_iterator exact =
			index.by_binding.find(binding);
		if (exact != index.by_binding.end() && exact->second < extra.size())
			return &extra[exact->second];
		const string* symbol = &binding->function_specialization_symbol;
		if (symbol->empty() && binding->aliased_binding != NULL)
			symbol = &binding->aliased_binding->function_specialization_symbol;
		if (!symbol->empty())
		{
			map<string, size_t>::const_iterator found_symbol =
				index.by_symbol.find(*symbol);
			if (found_symbol != index.by_symbol.end() &&
			    found_symbol->second < extra.size())
				return &extra[found_symbol->second];
		}
		string object = global_object_symbol(binding);
		if (object.empty() && binding->aliased_binding != NULL)
			object = global_object_symbol(binding->aliased_binding);
		if (!object.empty())
		{
			map<string, size_t>::const_iterator found_object =
				index.by_object.find(object);
			if (found_object != index.by_object.end() &&
			    found_object->second < extra.size())
				return &extra[found_object->second];
		}
	}
	map<ExtraNodeCacheKey, size_t>& hits = extra_node_lookup_hits();
	set<ExtraNodeCacheKey>& misses = extra_node_lookup_misses();
	ExtraNodeCacheKey key =
		make_pair(&extra, make_pair(extra.size(), binding));
	map<ExtraNodeCacheKey, size_t>::const_iterator cached = hits.find(key);
	if (cached != hits.end() &&
	    cached->second < extra.size() &&
	    same_binding_or_alias(extra[cached->second].binding, binding))
		return &extra[cached->second];
	if (misses.find(key) != misses.end())
		return NULL;
	for (size_t i = 0; i < extra.size(); ++i)
		if (same_binding_or_alias(extra[i].binding, binding))
		{
			hits[key] = i;
			return &extra[i];
		}
	misses.insert(key);
	return NULL;
}
void demand_noop_generated_default_dependencies(
	ProgramLowerer& program,
	const vector<Node>& extra,
	const Binding* binding,
	set<const Binding*>& seen)
{
	if (binding == NULL || !seen.insert(binding).second)
		return;
	Binding* mutable_binding = const_cast<Binding*>(binding);
	TypePtr owner = class_record_for_member(binding);
	if (!binding->is_generated_default_constructor ||
	    owner.get() == NULL ||
	    !no_op_generated_default_constructor(mutable_binding, owner))
		return;
	const Node* node = extra_node_for_binding(extra, binding);
	if (node == NULL)
		return;
	set<const Binding*> generated_calls;
	collect_direct_calls(*node, generated_calls);
	set<const Binding*> base_constructor_calls;
	collect_base_constructor_calls(*node, base_constructor_calls);
	for (set<const Binding*>::const_iterator it = generated_calls.begin();
	     it != generated_calls.end();
	     ++it)
	{
		if (*it == NULL)
			continue;
		if ((*it)->is_generated_default_constructor)
		{
			demand_noop_generated_default_dependencies(program,
			                                           extra,
			                                           *it,
			                                           seen);
		}
		else
		{
			if (base_constructor_calls.count(*it) != 0 &&
			    is_class_constructor_binding(*it))
				program.constructor_symbol_for(*it, true);
			program.demand_inline_function(*it);
		}
	}
}
void demand_noop_generated_default_dependencies(
	ProgramLowerer& program,
	const vector<Node>& extra,
	const set<const Binding*>& direct_calls)
{
	set<const Binding*> seen;
	for (set<const Binding*>::const_iterator it = direct_calls.begin();
	     it != direct_calls.end();
	     ++it)
		demand_noop_generated_default_dependencies(program,
		                                           extra,
		                                           *it,
		                                           seen);
}
string hosted_demand_key(const Binding* binding)
{
	if (binding == NULL)
		return string();
	string symbol = global_object_symbol(binding);
	if (symbol.empty() && binding->aliased_binding != NULL)
		symbol = global_object_symbol(binding->aliased_binding);
	if (!symbol.empty())
		return symbol;
	return binding->name + ":" +
	       (binding->type.get() != NULL ? pa11::describe_type(binding->type)
	                                    : string());
}
bool demand_parser_direct_call_body(pa12::internal::Parser& parser,
                                    const Binding* call,
                                    set<const Binding*>& direct_calls,
                                    set<const Binding*>& processed,
                                    set<string>& processed_hosted,
                                    set<const Binding*>& scanned_bodies,
                                    bool hosted_compatibility)
	{
		if (!processed.insert(call).second)
			return false;
	if (hosted_compatibility && hosted_library_binding(call))
	{
		string key = hosted_demand_key(call);
		if (!key.empty() && !processed_hosted.insert(key).second)
			return false;
	}
	Binding* object_root_call = const_cast<Binding*>(call);
	if (hosted_compatibility &&
	    should_mark_direct_call_object_root(object_root_call,
	                                        hosted_compatibility))
	{
		object_root_call->is_object_root = true;
		if (object_root_call->aliased_binding != NULL)
			object_root_call->aliased_binding->is_object_root = true;
	}
	const Binding* hosted_alias =
		hosted_compatibility
		? hosted_map_base_lvalue_operator_index_alias(call) : NULL;
	if (hosted_alias != NULL)
	{
		Binding* alias_root = const_cast<Binding*>(hosted_alias);
		alias_root->is_object_root = true;
		if (alias_root->aliased_binding != NULL)
			alias_root->aliased_binding->is_object_root = true;
		direct_calls.insert(hosted_alias);
		return true;
	}
	if (hosted_compatibility)
		collect_hosted_vector_bool_algorithm_dependencies(call,
		                                                   direct_calls);
		bool can_demand = parser.can_demand_lowir_function_body(const_cast<Binding*>(call));
		bool hosted_external_stream_call = hosted_compatibility && hosted_external_stream_function_binding(call);
		bool hosted_synthetic_inline = hosted_compatibility &&
			lowir_synthesizable_hosted_inline_body(call);
		bool hosted_body_root =
			object_root_call != NULL && object_root_call->is_object_root;
		bool candidate = !hosted_compatibility || !hosted_library_binding(call) ||
			(hosted_body_root &&
			 hosted_library_body_candidate(call) && !hosted_synthetic_inline) ||
			(hosted_body_root &&
			 hosted_nested_helper_body_root(call) &&
			 !hosted_synthetic_inline) ||
			(default_constructor_call(call) && !hosted_external_stream_call) ||
			(!hosted_library_binding(call) &&
			 can_demand && !hosted_synthetic_inline);
				if (candidate)
					parser.demand_lowir_function_body(const_cast<Binding*>(call));
	const vector<Node>& function_extra = parser.extra_lowir_nodes();
	const Node* body = extra_node_for_binding(function_extra, call);
	if (body == NULL && call->aliased_binding != NULL)
		body = extra_node_for_binding(function_extra, call->aliased_binding);
	if (body != NULL &&
	    body->binding != NULL &&
	    object_root_call != NULL &&
	    object_root_call->is_object_root)
	{
		body->binding->is_object_root = true;
		if (body->binding->aliased_binding != NULL)
			body->binding->aliased_binding->is_object_root = true;
	}
	if (body != NULL &&
	    body->binding != NULL &&
	    hosted_compatibility &&
	    !hosted_library_binding(body->binding))
	{
		body->binding->is_object_root = true;
		if (body->binding->aliased_binding != NULL)
			body->binding->aliased_binding->is_object_root = true;
	}
	if (body != NULL &&
	    body->binding != NULL &&
	    scanned_bodies.insert(body->binding).second)
	{
		bool hosted_nonroot_body =
			hosted_compatibility &&
			hosted_library_binding(body->binding) &&
			!body->binding->is_object_root;
		if (hosted_nonroot_body)
			return true;
		collect_direct_calls(*body, direct_calls);
		collect_addressed_functions(*body, direct_calls);
		collect_implicit_lifecycle_calls(*body, direct_calls);
		collect_lowered_constructor_calls(*body, direct_calls);
		if (hosted_compatibility)
			collect_hosted_helper_function_references(*body,
			                                          direct_calls);
	}
	return true;
}
void demand_parser_direct_call_bodies(pa12::internal::Parser& parser,
                                      set<const Binding*>& direct_calls,
                                      bool hosted_compatibility)
{
	set<const Binding*> processed;
	set<string> processed_hosted;
	set<const Binding*> scanned_bodies;
	size_t scanned_extra =
		hosted_compatibility ? 0 : parser.extra_lowir_nodes().size();
	for (;;)
	{
		bool progress = false;
		vector<const Binding*> calls(direct_calls.begin(), direct_calls.end());
		for (size_t i = 0; i < calls.size(); ++i)
		{
			if (demand_parser_direct_call_body(parser,
			                                   calls[i],
			                                   direct_calls,
			                                   processed,
			                                   processed_hosted,
			                                   scanned_bodies,
			                                   hosted_compatibility))
				progress = true;
		}
		const vector<Node>& extra = parser.extra_lowir_nodes();
		while (scanned_extra < extra.size())
		{
			const Node& node = extra[scanned_extra];
			bool scan_extra = !hosted_compatibility;
			if (!scan_extra &&
			    node.binding != NULL &&
			    node.binding->is_object_root)
				scan_extra = true;
			if (!scan_extra &&
			    node.binding != NULL &&
			    direct_calls.count(node.binding) != 0)
				scan_extra = true;
			if (!scan_extra &&
			    node.binding != NULL &&
			    node.binding->aliased_binding != NULL &&
			    direct_calls.count(node.binding->aliased_binding) != 0)
				scan_extra = true;
			if (scan_extra)
			{
				collect_direct_calls(node, direct_calls);
				collect_addressed_functions(node, direct_calls);
				collect_implicit_lifecycle_calls(node, direct_calls);
				collect_lowered_constructor_calls(node, direct_calls);
				if (hosted_compatibility)
					collect_hosted_helper_function_references(
						node,
						direct_calls);
				progress = true;
			}
			++scanned_extra;
		}
		if (!progress)
			break;
		}
	}
	void demand_referenced_extra_body_closure(
		pa12::internal::Parser& parser,
		const vector<Node>& extra,
		set<const Binding*>& direct_calls,
		bool hosted_compatibility)
	{
		set<const Binding*> scanned;
		for (;;)
		{
			set<const Binding*> discovered;
			BindingReferenceIndex direct_index =
				make_binding_reference_index(direct_calls);
			for (set<const Binding*>::const_iterator it = direct_calls.begin();
			     it != direct_calls.end();
			     ++it)
			{
				const Node* extra_node = extra_node_for_binding(extra, *it);
				if (extra_node == NULL)
					continue;
				const Node& node = *extra_node;
				if (!starts_with(node.line, "function-definition ") ||
				    node.binding == NULL)
					continue;
				bool referenced =
					binding_reference_index_contains(direct_index,
					                                 node.binding);
				if (!referenced || !scanned.insert(node.binding).second)
					continue;
				if (hosted_compatibility &&
				    hosted_library_binding(node.binding) &&
				    !node.binding->is_object_root)
					continue;
				collect_node_implicit_lifecycle_calls(node, discovered);
				collect_node_lowered_constructor_calls(node, discovered);
				TypePtr return_type = function_return_type(node.binding);
				for (size_t child = 0; child < node.children.size(); ++child)
					collect_body_demand_calls_impl(node.children[child],
					                               discovered,
					                               false,
					                               return_type);
			}
			if (discovered.empty())
				break;
			if (hosted_compatibility)
				mark_object_root_bindings(discovered,
				                          hosted_compatibility,
				                          true);
			demand_parser_direct_call_bodies(parser,
			                                 discovered,
			                                 hosted_compatibility);
			size_t before = direct_calls.size();
			direct_calls.insert(discovered.begin(), discovered.end());
			if (direct_calls.size() == before)
				break;
		}
	}
	void collect_parser_direct_demands(pa12::internal::Parser& parser,
	                                   const vector<Node>& extra,
	                                   bool hosted_compatibility,
	                                   set<const Binding*>& direct_calls)
	{
		set<const Binding*> body_demands;
		if (hosted_compatibility)
			collect_translation_unit_body_demand_calls(parser.root(),
			                                           direct_calls);
		else
		{
			collect_translation_unit_direct_calls(parser.root(),
			                                      direct_calls);
			collect_translation_unit_addressed_functions(parser.root(),
			                                             direct_calls);
			collect_global_defaulted_constructor_demands(parser.root(),
			                                             direct_calls,
			                                             false);
		}
		collect_global_variable_constructor_demands(parser.root(),
		                                            direct_calls);
		if (hosted_compatibility)
			mark_object_root_bindings(direct_calls,
			                          hosted_compatibility,
			                          true);
		demand_parser_direct_call_bodies(parser,
		                                 direct_calls,
		                                 hosted_compatibility);
		collect_translation_unit_body_demand_calls(parser.root(),
		                                           body_demands);
		if (hosted_compatibility)
			mark_object_root_bindings(body_demands,
			                          hosted_compatibility,
			                          true);
		demand_parser_direct_call_bodies(parser,
		                                 body_demands,
		                                 hosted_compatibility);
		direct_calls.insert(body_demands.begin(), body_demands.end());
		if (hosted_compatibility)
		{
			set<const Binding*> virtual_body_demands;
			collect_hosted_streambuf_virtual_body_demands(
				extra,
				virtual_body_demands);
			mark_object_root_bindings(virtual_body_demands,
			                          hosted_compatibility,
			                          true);
			demand_parser_direct_call_bodies(parser,
			                                 virtual_body_demands,
			                                 hosted_compatibility);
			direct_calls.insert(virtual_body_demands.begin(),
			                    virtual_body_demands.end());
		}
		if (hosted_compatibility)
		{
			set<const Binding*> generated_copy_move_demands;
			collect_generated_copy_move_body_demands(
				extra,
				generated_copy_move_demands,
				hosted_compatibility);
			mark_object_root_bindings(generated_copy_move_demands,
			                          hosted_compatibility,
			                          true);
			demand_parser_direct_call_bodies(parser,
			                                 generated_copy_move_demands,
			                                 hosted_compatibility);
			direct_calls.insert(generated_copy_move_demands.begin(),
			                    generated_copy_move_demands.end());
		}
		demand_referenced_extra_body_closure(parser,
		                                    extra,
		                                    direct_calls,
		                                    hosted_compatibility);
	}

		void collect_parser_definition_metadata(
		ProgramLowerer& program,
		pa12::internal::Parser& parser,
		const vector<Node>& extra,
		const set<const Binding*>& direct_calls,
		set<const Binding*>& root_definitions,
		set<const Binding*>& complete_constructor_entries)
		{
			parser.complete_static_member_initializer_replays();
			collect_static_downcast_sources(program, parser.root());
		for (size_t i = 0; i < extra.size(); ++i)
			collect_static_downcast_sources(program, extra[i]);
		note_function_definitions(program, parser.root());
		root_definitions = program.function_definition_bindings;
		for (size_t i = 0; i < extra.size(); ++i)
			note_function_definitions(program, extra[i]);
		collect_complete_constructor_entry_references(
			parser.root(),
			complete_constructor_entries);
		for (size_t i = 0; i < extra.size(); ++i)
		{
			collect_constructor_base_entry_references(program, extra[i]);
			collect_complete_constructor_entry_references(
				extra[i],
				complete_constructor_entries);
		}
		for (size_t i = 0; i < extra.size(); ++i)
			if (!empty_defaulted_copy_move_constructor_needs_helper(extra[i]))
				program.register_inline_definition(extra[i]);
		for (size_t i = 0; i < extra.size(); ++i)
			collect_extra_variable(program, extra[i]);
		demand_referenced_inline_definitions(program,
		                                     direct_calls,
		                                     complete_constructor_entries);
		demand_object_roots(program, extra, root_definitions);
	}
	void collect_parser_translation_unit(ProgramLowerer& program,
	                                     pa12::internal::Parser& parser,
	                                     bool hosted_compatibility)
	{
		if (hosted_compatibility)
			collect_translation_unit_filtered(program,
			                                  parser.root(),
			                                  hosted_compatibility);
		else
			program.collect_translation_unit(parser.root());
	}
	void collect_parser_late_demands(
		ProgramLowerer& program,
		pa12::internal::Parser& parser,
		const vector<Node>& extra,
		const set<const Binding*>& direct_calls,
		const set<const Binding*>& root_definitions,
		const set<const Binding*>& complete_constructor_entries,
		bool hosted_compatibility)
	{
		set<const Binding*> defaulted_definition_demands = direct_calls;
		collect_global_defaulted_constructor_demands(
			parser.root(),
			defaulted_definition_demands,
			false);
		collect_explicit_defaulted_definitions(program,
		                                      parser.root(),
		                                      &defaulted_definition_demands);
		for (size_t i = 0; i < extra.size(); ++i)
			if (extra[i].token_text == "defaulted-definition")
				collect_explicit_defaulted_definitions(
					program,
					extra[i],
					&defaulted_definition_demands);
		collect_referenced_extra_functions(program,
		                                   extra,
		                                   direct_calls,
		                                   hosted_compatibility);
		demand_noop_generated_default_dependencies(program,
		                                           extra,
		                                           direct_calls);
		demand_generated_copy_move_dependencies(program,
		                                        extra,
		                                        hosted_compatibility);
		for (size_t i = 0; i < extra.size(); ++i)
			if (!empty_defaulted_copy_move_constructor_needs_helper(extra[i]))
				program.register_inline_definition(extra[i]);
		demand_object_roots(program, extra, root_definitions);
		demand_referenced_inline_definitions(program,
		                                     direct_calls,
		                                     complete_constructor_entries);
		program.emit_pending_inline_definitions();
		program.emit_pending_synthetic_assignment_functions();
	}
	void collect_parser_output(ProgramLowerer& program,
	                           pa12::internal::Parser& parser,
	                           bool hosted_compatibility)
	{
		NativeLifecycleDemandScope native_lifecycle_scope(
			program.native_lowering);
		const vector<Node>& extra = parser.extra_lowir_nodes();
		set<const Binding*> direct_calls;
		set<const Binding*> root_definitions;
		set<const Binding*> complete_constructor_entries;
		collect_parser_direct_demands(parser,
		                              extra,
		                              hosted_compatibility,
		                              direct_calls);
		collect_parser_definition_metadata(program,
		                                   parser,
		                                   extra,
		                                   direct_calls,
		                                   root_definitions,
		                                   complete_constructor_entries);
		demand_early_hidden_friends(program, extra, direct_calls);
		collect_parser_translation_unit(program, parser, hosted_compatibility);
		collect_parser_late_demands(program,
		                            parser,
		                            extra,
		                            direct_calls,
		                            root_definitions,
		                            complete_constructor_entries,
		                            hosted_compatibility);
}
}  // namespace
void clear_lowir_emit_caches()
{
	clear_extra_node_lookup_cache();
	clear_global_object_symbol_cache();
	clear_same_binding_or_alias_cache();
	clear_lowir_emit_root_caches();
	clear_lowir_function_order_caches();
	clear_lowir_function_order_early_caches();
	clear_lowir_inline_order_caches();
	clear_lowir_inline_order_ranked_caches();
}
}  // namespace internal
void emit_lowir(const vector<string>& srcfiles,
                const string& outfile,
                const Options& options)
{
	internal::clear_lowir_emit_caches();
	internal::ProgramLowerer program(options.native_lowering,
	                                 options.host_object_lowering);
	vector<unique_ptr<pa12::internal::Parser> > parsers;
	for (size_t i = 0; i < srcfiles.size(); ++i)
	{
		pa12::Options pa12_options;
		pa12_options.preprocess = options.preprocess;
		pa12_options.hosted_compatibility = options.hosted_compatibility;
		unique_ptr<pa12::internal::Parser> parser(
			new pa12::internal::Parser(srcfiles[i], pa12_options));
		parser->parse_translation_unit();
		internal::collect_parser_output(program,
		                                *parser,
		                                options.hosted_compatibility);
		parsers.push_back(std::move(parser));
	}
	program.emit_global_lifecycle_functions();
	program.emit_referenced_allocator_noop_constructors();
	program.emit_referenced_noop_constructor_base_entries();
	program.write(outfile);
	internal::clear_lowir_emit_caches();
}
}  // namespace pa14
