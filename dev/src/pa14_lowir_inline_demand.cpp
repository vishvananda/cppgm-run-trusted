#include "pa14_lowir_internal.h"
#include "pa12_templates_function_support.h"
#include "pa12_types_support.h"
#include <algorithm>
namespace pa14 {
namespace internal {
namespace {
bool hidden_vbase_vector_contains(const vector<TypePtr>& bases, TypePtr record)
{
	TypePtr bare = record.get() != NULL ? pa11::strip_cv(record) : TypePtr();
	for (size_t i = 0; i < bases.size(); ++i)
		if (pa11::same_type(pa11::strip_cv(bases[i]), bare))
			return true;
	return false;
}
void collect_parameter_virtual_base_member_uses(const Node& node,
                                                const Binding* parameter,
                                                const vector<TypePtr>& all_vbases,
                                                vector<TypePtr>& used)
{
	if (starts_with(node.line, "member-expression") &&
	    node.binding != NULL &&
	    !node.children.empty() &&
	    starts_with(node.children[0].line, "id-expression") &&
	    node.children[0].binding == parameter)
	{
		Binding* member =
			node.binding->aliased_binding != NULL &&
			node.binding->target_scope != NULL
			? node.binding->aliased_binding : node.binding;
		if (!member->is_static_member && member->owner != NULL)
		{
			TypePtr owner = pa11::record_type_for_scope(member->owner);
			owner = owner.get() != NULL ? pa11::strip_cv(owner) : TypePtr();
			for (size_t i = 0; i < all_vbases.size(); ++i)
			{
				TypePtr vbase = pa11::strip_cv(all_vbases[i]);
				if (owner.get() != NULL &&
				    (pa11::same_type(vbase, owner) ||
				     record_has_base_subobject(vbase, owner)) &&
				    !hidden_vbase_vector_contains(used, vbase))
					used.push_back(vbase);
			}
		}
	}
	for (size_t i = 0; i < node.children.size(); ++i)
		collect_parameter_virtual_base_member_uses(node.children[i],
		                                           parameter,
		                                           all_vbases,
		                                           used);
}
}  // namespace

const Binding* resolve_inline_alias_demand_binding(ProgramLowerer& program,
                                                   const Binding* binding);
const Node* inline_alias_recorded_body(const ProgramLowerer& program,
                                       const Binding* binding);
const Binding* inline_alias_lookup_binding(ProgramLowerer& program,
                                           const string& name,
                                           const string& object);
bool inline_alias_concrete_body_needs_own_definition(const Binding* binding);

vector<TypePtr> ProgramLowerer::hidden_virtual_bases_for_function_parameter(
	const Binding* binding,
	size_t parameter_index,
	TypePtr type)
{
	vector<TypePtr> defaults = hidden_virtual_bases_for_parameter(type);
	if (defaults.empty() || binding == NULL)
		return defaults;
	pair<const Binding*, size_t> key(binding, parameter_index);
	map<pair<const Binding*, size_t>, vector<TypePtr> >::const_iterator cached =
		hidden_parameter_virtual_bases.find(key);
	if (cached != hidden_parameter_virtual_bases.end())
		return cached->second;
	vector<TypePtr> selected = defaults;
	const Node* fn = NULL;
	map<const Binding*, const Node*>::const_iterator found =
		inline_definitions.find(binding);
	if (found != inline_definitions.end())
		fn = found->second;
	map<const Binding*, Node>::const_iterator synthetic =
		synthetic_inline_definitions.find(binding);
	if (fn == NULL && synthetic != synthetic_inline_definitions.end())
		fn = &synthetic->second;
	if (fn != NULL)
	{
		Binding* param_binding = NULL;
		size_t param = 0;
		for (size_t i = 0; i < fn->children.size(); ++i)
		{
			if (!starts_with(fn->children[i].line, "parameter "))
				continue;
			if (param == parameter_index)
			{
				param_binding = fn->children[i].binding;
				break;
			}
			++param;
		}
		TypePtr bare = pa11::strip_cv(type);
		bool record_reference =
			(bare->kind == TypeKind::LValueReference ||
			 bare->kind == TypeKind::RValueReference) &&
			pa11::strip_cv(bare->base)->kind == TypeKind::Record;
		bool record_pointer =
			bare->kind == TypeKind::Pointer &&
			pa11::strip_cv(bare->base)->kind == TypeKind::Record;
		if (param_binding != NULL && (record_reference || record_pointer))
		{
			vector<TypePtr> used;
			collect_parameter_virtual_base_member_uses(*fn,
			                                           param_binding,
			                                           defaults,
			                                           used);
			if (record_pointer)
				selected = used;
			else if (!used.empty())
				selected = used;
		}
	}
	hidden_parameter_virtual_bases[key] = selected;
	return selected;
}
	void ProgramLowerer::demand_inline_function(const Binding* binding,
	                                            bool complete_entry)
	{
		bool requested_hosted_synthetic =
			lowir_synthesizable_hosted_inline_body(binding);
		if (!requested_hosted_synthetic)
			binding = resolve_inline_alias_demand_binding(*this, binding);
		if (binding == NULL)
			return;
		if (!complete_entry)
		{
			if (is_class_constructor_binding(binding))
				demanded_constructor_base_entries.insert(binding);
			else if (is_class_destructor_binding(binding))
				demanded_destructor_base_entries.insert(binding);
		}
		bool hosted_synthetic =
			lowir_synthesizable_hosted_inline_body(binding);
		if (!hosted_synthetic &&
		    function_signature_has_unresolved_storage(binding))
			return;
	bool noop_synthetic = lowir_synthesizable_noop_constructor(binding);
	if (!hosted_synthetic &&
	    lowir_extern_template_class_external_binding(binding))
	{
		demand_function_declaration(binding);
		return;
	}
	if (host_object_lowering &&
	    !hosted_synthetic &&
	    !noop_synthetic &&
	    hosted_external_stream_function_binding(binding))
	{
		demand_function_declaration(binding);
		return;
	}
		bool has_recorded_body =
			inline_definitions.find(binding) != inline_definitions.end() ||
			synthetic_inline_definitions.find(binding) !=
				synthetic_inline_definitions.end();
	if (hosted_synthetic)
	{
		synthetic_inline_definitions[binding] =
			lowir_make_hosted_inline_body_node(binding);
		rank_inline_definition(*this, binding);
		inline_definitions[binding] =
			&synthetic_inline_definitions[binding];
		has_recorded_body = true;
	}
		if (!has_recorded_body)
	{
		string wanted_name = symbol_for(binding);
		string wanted_object = global_object_symbol(binding);
			const Binding* inline_match =
				inline_alias_lookup_binding(*this,
				                            wanted_name,
				                            wanted_object);
		if (inline_match != NULL)
		{
			if (inline_match != binding)
				symbols[binding] = symbol_for(inline_match);
			binding = inline_match;
			has_recorded_body = true;
		}
	}
	if (!has_recorded_body &&
	    lowir_synthesizable_hosted_inline_body(binding))
	{
		synthetic_inline_definitions[binding] =
			lowir_make_hosted_inline_body_node(binding);
		rank_inline_definition(*this, binding);
		inline_definitions[binding] =
			&synthetic_inline_definitions[binding];
		has_recorded_body = true;
	}
	if (!binding->is_inline_definition)
	{
		if (!has_recorded_body &&
		    lowir_synthesizable_noop_constructor(binding))
		{
			string name = symbol_for(binding);
			emit_generated_empty_constructor(
				binding,
				complete_entry ? name : name + "__base_entry");
		}
		if (!has_recorded_body)
			return;
	}
	bool class_ctor = is_class_constructor_binding(binding);
	bool class_dtor = is_class_destructor_binding(binding);
	if (complete_entry)
		demanded_inline_complete_entries.insert(binding);
	else if (!class_ctor && !class_dtor)
		return;
	else if (class_ctor &&
	         !binding->is_generated_default_constructor &&
	         !binding->is_generated_aggregate_constructor &&
	         !binding->is_generated_copy_move_constructor)
	{
		TypePtr active_record =
			active_inline_definition != NULL
			? class_record_for_member(active_inline_definition)
			: TypePtr();
		active_record = active_record.get() != NULL
			? pa11::strip_cv(active_record) : TypePtr();
		if (active_record.get() != NULL &&
		    active_record->kind == TypeKind::Record &&
		    !pa11::record_virtual_bases(active_record).empty())
			demanded_inline_complete_entries.insert(binding);
	}
	demand_move_assignment_copy_dependency(binding);
	string name = symbol_for(binding);
	if (complete_entry && defined_functions.find(name) != defined_functions.end())
	{
		demand_template_static_member_definitions_for_function(binding);
		return;
	}
	if (!complete_entry &&
	    defined_functions.find(name + "__base_entry") != defined_functions.end())
		return;
		for (size_t i = 0; i < pending_inline_definitions.size(); ++i)
			if (pending_inline_definitions[i] == binding)
				return;
		map<const Binding*, const Node*>::const_iterator found =
			inline_definitions.find(binding);
		if (found == inline_definitions.end())
		{
			string object = global_object_symbol(binding);
			const Binding* inline_match =
					inline_alias_lookup_binding(*this,
					                            string(),
					                            object);
			if (inline_match != NULL)
				{
					rank_inline_definition(*this, binding);
					inline_definitions[binding] =
						inline_alias_recorded_body(*this, inline_match);
				found = inline_definitions.find(binding);
			}
		}
		if (found == inline_definitions.end() &&
		    lowir_synthesizable_noop_constructor(binding))
	{
		emit_generated_empty_constructor(
			binding,
			complete_entry ? name : name + "__base_entry");
		return;
	}
	if (found == inline_definitions.end() &&
	    lowir_synthesizable_defaulted_storage_copy_constructor(binding))
	{
		synthetic_inline_definitions[binding] =
			lowir_make_defaulted_storage_copy_constructor_node(binding);
		rank_inline_definition(*this, binding);
		inline_definitions[binding] =
			&synthetic_inline_definitions[binding];
		found = inline_definitions.find(binding);
	}
	if (found == inline_definitions.end() &&
	    lowir_synthesizable_hosted_inline_body(binding))
	{
		synthetic_inline_definitions[binding] =
			lowir_make_hosted_inline_body_node(binding);
		rank_inline_definition(*this, binding);
		inline_definitions[binding] =
			&synthetic_inline_definitions[binding];
		found = inline_definitions.find(binding);
	}
		if (found != inline_definitions.end())
		{
			bool concrete_alias_body =
				inline_alias_concrete_body_needs_own_definition(binding) &&
				synthetic_inline_definitions.find(binding) !=
					synthetic_inline_definitions.end();
			if (binding_has_template_specialization_context(binding) ||
			    !binding->function_specialization_symbol.empty())
				demand_template_static_member_definitions_for_function(binding);
				bool unresolved_body =
					!concrete_alias_body &&
					node_tree_has_unresolved_storage(*found->second);
				bool concrete_function_template_body =
					!binding->function_specialization_symbol.empty() ||
					(binding->aliased_binding != NULL &&
					 !binding->aliased_binding
						  ->function_specialization_symbol.empty());
					bool concrete_user_body =
						!hosted_library_binding(binding) &&
						((!binding_has_template_specialization_context(binding) &&
						  binding->function_specialization_symbol.empty() &&
						  (binding->aliased_binding == NULL ||
						   binding->aliased_binding
							   ->function_specialization_symbol.empty())) ||
						 concrete_function_template_body);
					if (unresolved_body && concrete_user_body)
						unresolved_body = false;
						if (unresolved_body)
							return;
					demand_template_static_member_definitions_for_function(binding);
					insert_pending_inline_definition(binding);
		}
	}
}  // namespace internal
}  // namespace pa14
