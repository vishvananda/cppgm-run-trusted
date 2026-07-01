#include "pa14_lowir_internal.h"

namespace pa14 {
namespace internal {

bool hosted_addressed_function_needs_body(const Binding* binding)
{
	return binding != NULL;
}

Binding* addressed_function_binding(const Node& node)
{
	if (starts_with(node.line, "unary-expression") &&
	    node.has_op &&
	    node.op == OP_AMP &&
	    !node.children.empty() &&
	    node.children[0].binding != NULL &&
	    node.children[0].binding->kind == BindingKind::Function)
		return node.children[0].binding;
	if (node.binding != NULL &&
	    node.binding->kind == BindingKind::Function &&
	    node.category == ValueCategory::LValue)
		return node.binding;
	return NULL;
}

TypePtr function_return_type(const Binding* binding)
{
	if (binding == NULL ||
	    binding->type.get() == NULL ||
	    binding->type->kind != TypeKind::Function)
		return TypePtr();
	return binding->type->base;
}

Binding* call_expression_callee_binding(const Node& node)
{
	if (!starts_with(node.line, "call-expression") ||
	    node.children.empty())
		return NULL;
	const Node& callee = node.children[0];
	if (callee.binding != NULL &&
	    callee.binding->kind == BindingKind::Function &&
	    (!function_signature_has_unresolved_storage(callee.binding) ||
	     hosted_std_function_swap_binding(callee.binding)))
		return callee.binding;
	if ((starts_with(callee.line, "unary-expression") ||
	     starts_with(callee.line, "cast-expression")) &&
	    callee.children.size() == 1 &&
	    callee.children[0].binding != NULL &&
	    callee.children[0].binding->kind == BindingKind::Function &&
	    (!function_signature_has_unresolved_storage(
		     callee.children[0].binding) ||
	     hosted_std_function_swap_binding(callee.children[0].binding)))
		return callee.children[0].binding;
	return NULL;
}

namespace {

map<const Binding*, string>& binding_alias_key_cache()
{
	static map<const Binding*, string> cache;
	return cache;
}

const string& binding_alias_key(const Binding* binding)
{
	static const string empty;
	if (binding == NULL || binding->kind != BindingKind::Function)
		return empty;
	map<const Binding*, string>& cache = binding_alias_key_cache();
	map<const Binding*, string>::const_iterator found = cache.find(binding);
	if (found != cache.end())
		return found->second;
	return cache.insert(make_pair(binding, global_object_symbol(binding)))
		.first->second;
}

}  // namespace

void clear_same_binding_or_alias_cache()
{
	binding_alias_key_cache().clear();
}

bool same_binding_or_alias(const Binding* left, const Binding* right)
{
	if (left == right ||
	    (left != NULL && left->aliased_binding == right) ||
	    (right != NULL && right->aliased_binding == left))
		return true;
	const string& left_key = binding_alias_key(left);
	const string& right_key = binding_alias_key(right);
	return !left_key.empty() && left_key == right_key;
}

namespace {

bool function_definition_compound_body_empty_local(const Node& node)
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

}  // namespace

bool empty_defaulted_copy_move_constructor_needs_helper(const Node& node)
{
	Binding* binding = node.binding;
	if (!starts_with(node.line, "function-definition ") ||
	    binding == NULL ||
	    !binding->is_defaulted ||
	    binding->is_generated_copy_move_constructor ||
	    binding->owner == NULL ||
	    binding->owner->kind != ScopeKind::Class ||
	    binding->name != binding->owner->name ||
	    binding->type.get() == NULL ||
	    binding->type->kind != TypeKind::Function ||
	    binding->type->parameters.size() != 2 ||
	    !is_reference(binding->type->parameters[1]) ||
	    !function_definition_compound_body_empty_local(node))
		return false;
	TypePtr record = pa11::record_type_for_scope(binding->owner);
	record = record.get() != NULL ? pa11::strip_cv(record) : TypePtr();
	return record.get() != NULL &&
	       defaulted_copy_move_constructor_needs_helper(binding, record);
}

void collect_defaulted_constructor_action_demands(const Node& node,
                                                  set<const Binding*>& out)
{
	Binding* direct = node.direct_call;
	if (direct == NULL &&
	    starts_with(node.line, "constructor-action") &&
	    !node.children.empty())
		direct = node.children[0].direct_call;
	if (direct == NULL &&
	    starts_with(node.line, "constructor-action") &&
	    !node.children.empty())
		direct = call_expression_callee_binding(node.children[0]);
	if (direct != NULL &&
	    direct->is_explicit_defaulted_definition &&
	    direct->is_defaulted)
		out.insert(direct);
	for (size_t i = 0; i < node.children.size(); ++i)
		collect_defaulted_constructor_action_demands(node.children[i],
		                                             out);
}

void collect_global_defaulted_constructor_demands(const Node& node,
                                                 set<const Binding*>& out,
                                                 bool in_function)
{
	bool child_in_function =
		in_function || starts_with(node.line, "function-definition ");
	if (!in_function &&
	    starts_with(node.line, "variable ") &&
	    node.binding != NULL)
		collect_defaulted_constructor_action_demands(node, out);
	for (size_t i = 0; i < node.children.size(); ++i)
		collect_global_defaulted_constructor_demands(
			node.children[i],
			out,
			child_in_function);
}

void collect_explicit_defaulted_definitions(ProgramLowerer& program,
                                            const Node& node,
                                            const set<const Binding*>* demanded)
{
	if (starts_with(node.line, "function-definition ") &&
	    ((node.binding != NULL &&
	      node.binding->is_explicit_defaulted_definition) ||
	     node.token_text == "defaulted-definition"))
	{
		if (demanded != NULL &&
		    (node.binding == NULL ||
		     demanded->find(node.binding) == demanded->end()))
			return;
		if (empty_defaulted_copy_move_constructor_needs_helper(node))
			return;
		program.collect_node(node);
		return;
	}
	for (size_t i = 0; i < node.children.size(); ++i)
		collect_explicit_defaulted_definitions(program,
		                                      node.children[i],
		                                      demanded);
}

void insert_constructor_binding_aliases(set<const Binding*>& out,
                                        const Binding* binding)
{
	if (binding == NULL)
		return;
	out.insert(binding);
	const Binding* canonical = canonical_constructor_binding(binding);
	if (canonical != NULL)
		out.insert(canonical);
	if (binding->aliased_binding != NULL)
		out.insert(binding->aliased_binding);
	if (canonical != NULL && canonical->aliased_binding != NULL)
		out.insert(canonical->aliased_binding);
}

bool constructor_set_contains_binding_or_alias(
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
	for (set<const Binding*>::const_iterator it = bindings.begin();
	     it != bindings.end();
	     ++it)
		if (same_binding_or_alias(*it, binding))
			return true;
	return false;
}

const Binding* first_class_constructor_direct_call(const Node& node)
{
	if (node.direct_call != NULL &&
	    is_class_constructor_binding(node.direct_call))
		return node.direct_call;
	for (size_t i = 0; i < node.children.size(); ++i)
	{
		const Binding* found =
			first_class_constructor_direct_call(node.children[i]);
		if (found != NULL)
			return found;
	}
	return NULL;
}

const Binding* base_init_action_constructor_call(const Node& node)
{
	if (!starts_with(node.line, "base-init-action"))
		return NULL;
	if (node.direct_call != NULL &&
	    is_class_constructor_binding(node.direct_call))
		return node.direct_call;
	if (!node.children.empty())
		return first_class_constructor_direct_call(node.children[0]);
	return NULL;
}

void collect_constructor_base_entry_references(ProgramLowerer& program,
                                               const Node& node)
{
	const Binding* base_ctor = base_init_action_constructor_call(node);
	if (base_ctor != NULL)
	{
		insert_constructor_binding_aliases(
			program.referenced_constructor_base_entries,
			base_ctor);
		if (node.token_text == "inherited-constructor")
			insert_constructor_binding_aliases(
				program.constructor_base_entry_only_references,
				base_ctor);
	}
	for (size_t i = 0; i < node.children.size(); ++i)
		collect_constructor_base_entry_references(program, node.children[i]);
}

void collect_complete_constructor_entry_references_impl(
	const Node& node,
	set<const Binding*>& out,
	const Binding* suppressed_base_init_ctor)
{
	const Binding* suppressed = suppressed_base_init_ctor;
	if (starts_with(node.line, "base-init-action"))
	{
		const Binding* base_ctor =
			base_init_action_constructor_call(node);
		if (base_ctor != NULL)
			suppressed = base_ctor;
	}
	if (node.direct_call != NULL &&
	    is_class_constructor_binding(node.direct_call) &&
	    (suppressed == NULL ||
	     !same_binding_or_alias(node.direct_call, suppressed)))
		insert_constructor_binding_aliases(out, node.direct_call);
	for (size_t i = 0; i < node.children.size(); ++i)
		collect_complete_constructor_entry_references_impl(
			node.children[i],
			out,
			suppressed);
}

void collect_complete_constructor_entry_references(
	const Node& node,
	set<const Binding*>& out)
{
	collect_complete_constructor_entry_references_impl(node, out, NULL);
}

void collect_static_downcast_sources(ProgramLowerer& program, const Node& node)
{
	if (starts_with(node.line, "cast-expression") &&
	    !node.is_dynamic_cast_expression &&
	    !node.children.empty())
	{
		TypePtr source = pa11::strip_cv(node.children[0].type);
		TypePtr target = pa11::strip_cv(node.type);
		if (source.get() != NULL &&
		    target.get() != NULL &&
		    source->kind == TypeKind::Pointer &&
		    target->kind == TypeKind::Pointer)
		{
			TypePtr source_record = pa11::strip_cv(source->base);
			TypePtr target_record = pa11::strip_cv(target->base);
			if (source_record.get() != NULL &&
			    target_record.get() != NULL &&
			    source_record->kind == TypeKind::Record &&
			    target_record->kind == TypeKind::Record &&
			    record_has_base_subobject(target_record, source_record))
				program.mark_static_downcast_source_record(source_record);
		}
		if (target.get() != NULL &&
		    is_reference(target))
		{
			TypePtr source_record =
				source.get() != NULL && is_reference(source)
					? pa11::strip_cv(source->base)
					: source;
			TypePtr target_record = pa11::strip_cv(target->base);
			if (source_record.get() != NULL &&
			    target_record.get() != NULL &&
			    source_record->kind == TypeKind::Record &&
			    target_record->kind == TypeKind::Record &&
			    record_has_base_subobject(target_record, source_record))
				program.mark_static_downcast_source_record(source_record);
		}
	}
	for (size_t i = 0; i < node.children.size(); ++i)
		collect_static_downcast_sources(program, node.children[i]);
}

}  // namespace internal
}  // namespace pa14
