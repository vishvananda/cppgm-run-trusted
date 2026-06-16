#include "pa14_lowir_internal.h"

namespace pa14 {
namespace internal {

bool constructor_record_contains_hosted_subobject(const Binding* binding);

namespace {
	bool hosted_addressed_function_needs_body(const Binding* binding)
	{
		if (binding == NULL || !hosted_library_binding(binding))
			return true;
		if (!binding->function_specialization_symbol.empty() ||
		    (binding->aliased_binding != NULL &&
		     !binding->aliased_binding->function_specialization_symbol.empty()))
			return true;
		TypePtr owner = class_record_for_member(binding);
		owner = owner.get() != NULL ? pa11::strip_cv(owner) : TypePtr();
		return record_is_template_specialization(owner);
	}
	Binding* call_expression_callee_binding(const Node& node)
	{
		if (!starts_with(node.line, "call-expression") ||
		    node.children.empty())
			return NULL;
		const Node& callee = node.children[0];
		if (callee.binding != NULL &&
		    callee.binding->kind == BindingKind::Function &&
		    !function_signature_has_unresolved_storage(callee.binding))
			return callee.binding;
		if ((starts_with(callee.line, "unary-expression") ||
		     starts_with(callee.line, "cast-expression")) &&
		    callee.children.size() == 1 &&
		    callee.children[0].binding != NULL &&
		    callee.children[0].binding->kind == BindingKind::Function &&
		    !function_signature_has_unresolved_storage(
			    callee.children[0].binding))
			return callee.children[0].binding;
		return NULL;
	}
				bool suppress_generated_aggregate_constructor_call(
					const Binding* binding)
			{
				return binding != NULL &&
				       binding->is_generated_aggregate_constructor;
			}
				bool suppress_generated_trivial_copy_move_constructor_call(
					const Binding* binding)
				{
					if (binding == NULL ||
					    !binding->is_defaulted ||
					    !binding->is_inline_definition ||
					    binding->is_object_root ||
					    binding->type.get() == NULL ||
					    binding->type->kind != TypeKind::Function ||
					    binding->type->parameters.size() != 2 ||
					    !is_reference(binding->type->parameters[1]))
						return false;
					TypePtr record = class_record_for_member(binding);
					record = record.get() != NULL ? pa11::strip_cv(record) : TypePtr();
					TypePtr param =
						pa11::strip_cv(binding->type->parameters[1]->base);
					return record.get() != NULL &&
					       record->kind == TypeKind::Record &&
					       param.get() != NULL &&
					       param->kind == TypeKind::Record &&
					       pa11::same_type(record, param) &&
					       !defaulted_copy_move_constructor_needs_helper(
						       const_cast<Binding*>(binding),
						       record);
				}
			bool suppress_prelowered_constructor_body_demand(
				const Binding* binding)
			{
				bool specialized =
					binding_has_template_specialization_context(binding) ||
					(binding != NULL &&
					 !binding->function_specialization_symbol.empty()) ||
					(binding != NULL &&
					 binding->aliased_binding != NULL &&
					 (binding_has_template_specialization_context(
						  binding->aliased_binding) ||
					  !binding->aliased_binding
						   ->function_specialization_symbol.empty()));
				return binding != NULL &&
				       is_class_constructor_binding(binding) &&
				       binding->is_inline_definition &&
				       !hosted_library_binding(binding) &&
				       !constructor_record_contains_hosted_subobject(binding) &&
				       !binding->is_object_root &&
				       (!binding->is_generated_copy_move_constructor ||
				        suppress_generated_trivial_copy_move_constructor_call(
					        binding)) &&
				       !specialized;
			}
			bool suppress_prelowered_constructor_body_demand_for_type(
				const Binding* binding,
				TypePtr constructed_type)
			{
				TypePtr bare = constructed_type.get() != NULL
					? pa11::strip_cv(constructed_type) : TypePtr();
				if (record_is_template_specialization(bare))
					return false;
				return suppress_prelowered_constructor_body_demand(binding);
			}
		bool default_constructor_call(const Binding* binding)
		{
			return binding != NULL &&
			       binding->owner != NULL &&
			       binding->owner->kind == ScopeKind::Class &&
			       binding->name == binding->owner->name &&
			       binding->type.get() != NULL &&
			       binding->type->kind == TypeKind::Function &&
			       binding->type->parameters.size() == 1;
		}
	bool constant_evaluation_only_subtree(const Node& node)
	{
		if (starts_with(node.line, "static-assert-declaration"))
			return true;
		return starts_with(node.line, "variable ") &&
		       node.binding != NULL &&
		       (node.binding->is_constexpr || node.binding->has_constant);
	}
	bool skip_translation_unit_call_subtree(const Node& node)
	{
		if (constant_evaluation_only_subtree(node))
			return true;
		return starts_with(node.line, "function-definition ") &&
		       node.binding != NULL &&
		       node.binding->is_inline_definition;
	}
		void collect_direct_calls_impl(const Node& node,
		                               set<const Binding*>& out,
		                               bool skip_inline_function_bodies)
	{
		if (constant_evaluation_only_subtree(node) ||
		    (skip_inline_function_bodies &&
		     skip_translation_unit_call_subtree(node)))
			return;
		Binding* callee = node.direct_call != NULL
			? node.direct_call : call_expression_callee_binding(node);
		if (callee != NULL &&
		    !suppress_generated_aggregate_constructor_call(callee) &&
		    !suppress_prelowered_constructor_body_demand(callee) &&
		    !suppress_noop_generated_constructor_call(node))
			out.insert(callee);
		for (size_t i = 0; i < node.children.size(); ++i)
			collect_direct_calls_impl(node.children[i],
			                          out,
			                          skip_inline_function_bodies);
	}
		void collect_direct_calls(const Node& node, set<const Binding*>& out)
	{
		collect_direct_calls_impl(node, out, false);
	}
	void collect_translation_unit_direct_calls(const Node& node,
	                                           set<const Binding*>& out)
	{
		collect_direct_calls_impl(node, out, true);
	}
	void collect_addressed_functions_impl(const Node& node,
	                                      set<const Binding*>& out,
	                                      bool skip_inline_function_bodies)
	{
		if (constant_evaluation_only_subtree(node) ||
		    (skip_inline_function_bodies &&
		     skip_translation_unit_call_subtree(node)))
			return;
		if (starts_with(node.line, "unary-expression") &&
		    node.has_op &&
		    node.op == OP_AMP &&
		    !node.children.empty() &&
		    node.children[0].binding != NULL &&
		    node.children[0].binding->kind == BindingKind::Function &&
		    hosted_addressed_function_needs_body(node.children[0].binding))
			out.insert(node.children[0].binding);
		for (size_t i = 0; i < node.children.size(); ++i)
			collect_addressed_functions_impl(node.children[i],
			                                 out,
			                                 skip_inline_function_bodies);
	}
	void collect_addressed_functions(const Node& node,
	                                 set<const Binding*>& out)
	{
		collect_addressed_functions_impl(node, out, false);
	}
	void collect_translation_unit_addressed_functions(const Node& node,
	                                                  set<const Binding*>& out)
	{
		collect_addressed_functions_impl(node, out, true);
	}
	void collect_destructor_demands_for_type(TypePtr type,
	                                         set<const Binding*>& out,
	                                         set<const pa11::Type*>& seen)
	{
		if (type.get() == NULL)
			return;
		TypePtr bare = pa11::strip_cv(type);
		if (bare->kind == TypeKind::Array)
		{
			collect_destructor_demands_for_type(bare->base, out, seen);
			return;
		}
		if (bare->kind != TypeKind::Record)
			return;
		if (!seen.insert(bare.get()).second)
			return;
		Binding* dtor = find_destructor(bare);
		if (dtor != NULL && (dtor->is_virtual || !dtor->is_noop_destructor))
			out.insert(dtor);
		try
		{
			pa11::layout_record_type(bare);
		}
		catch (const runtime_error& err)
		{
			string message = err.what();
			if (message == "incomplete class type" ||
			    message == "incomplete object type")
				return;
			throw;
		}
		vector<TypePtr> bases = pa11::record_direct_bases(bare);
		for (size_t i = 0; i < bases.size(); ++i)
			collect_destructor_demands_for_type(bases[i], out, seen);
		for (size_t i = 0; i < bare->fields.size(); ++i)
			collect_destructor_demands_for_type(bare->fields[i]->type,
			                                    out,
			                                    seen);
	}
	void collect_destructor_demands_for_type(TypePtr type,
	                                         set<const Binding*>& out)
	{
		set<const pa11::Type*> seen;
		collect_destructor_demands_for_type(type, out, seen);
	}
	void collect_vtable_demands_for_type(TypePtr type,
	                                     set<const Binding*>& out,
	                                     set<const pa11::Type*>& seen)
	{
		if (type.get() == NULL)
			return;
		TypePtr bare = pa11::strip_cv(type);
		if (bare->kind == TypeKind::Array)
		{
			collect_vtable_demands_for_type(bare->base, out, seen);
			return;
		}
		if (bare->kind != TypeKind::Record)
			return;
		if (!seen.insert(bare.get()).second)
			return;
		if (!bare->is_polymorphic)
			return;
		try
		{
			pa11::layout_record_type(bare);
		}
		catch (const runtime_error& err)
		{
			string message = err.what();
			if (message == "incomplete class type" ||
			    message == "incomplete object type")
				return;
			throw;
		}
		for (size_t i = 0; i < bare->virtual_entries.size(); ++i)
			if (bare->virtual_entries[i].function != NULL)
				out.insert(bare->virtual_entries[i].function);
		vector<TypePtr> bases = pa11::record_direct_bases(bare);
		for (size_t i = 0; i < bases.size(); ++i)
			collect_vtable_demands_for_type(bases[i], out, seen);
	}
	void collect_vtable_demands_for_type(TypePtr type,
	                                     set<const Binding*>& out)
	{
		set<const pa11::Type*> seen;
		collect_vtable_demands_for_type(type, out, seen);
	}
	void collect_implicit_demands_for_type(TypePtr type,
	                                       set<const Binding*>& out)
	{
		collect_destructor_demands_for_type(type, out);
		collect_vtable_demands_for_type(type, out);
	}
	void collect_node_implicit_lifecycle_calls(const Node& node,
	                                          set<const Binding*>& out)
	{
		if (starts_with(node.line, "variable ") && node.binding != NULL)
			collect_implicit_demands_for_type(node.binding->type, out);
		if (starts_with(node.line, "member-init-action") &&
		    node.binding != NULL)
			collect_implicit_demands_for_type(node.binding->type, out);
		if (starts_with(node.line, "base-init-action") &&
		    node.type.get() != NULL)
			collect_implicit_demands_for_type(node.type, out);
		if (node.type.get() != NULL && node.category != ValueCategory::LValue)
			collect_implicit_demands_for_type(object_type(node.type), out);
	}
	void collect_implicit_lifecycle_calls(const Node& node,
	                                      set<const Binding*>& out)
	{
		collect_node_implicit_lifecycle_calls(node, out);
		for (size_t i = 0; i < node.children.size(); ++i)
			collect_implicit_lifecycle_calls(node.children[i], out);
	}
	void collect_copy_move_constructor_for_init(TypePtr target,
	                                            const Node& init,
	                                            set<const Binding*>& out)
	{
		if (target.get() == NULL || init.type.get() == NULL ||
		    (init.category != ValueCategory::LValue &&
		     init.category != ValueCategory::XValue))
			return;
		TypePtr dst = pa11::strip_cv(target);
		TypePtr src = pa11::strip_cv(object_type(init.type));
		if (dst->kind != TypeKind::Record ||
		    src->kind != TypeKind::Record ||
		    !(pa11::same_type(src, dst) ||
		      record_has_base_subobject(src, dst)))
			return;
		Binding* copy_move =
			find_copy_move_constructor(target,
			                           init.category == ValueCategory::XValue);
		if (copy_move == NULL && init.category == ValueCategory::XValue)
			copy_move = find_copy_move_constructor(target, false);
		if (copy_move == NULL &&
		    init.category == ValueCategory::XValue &&
		    dst->is_template_specialization)
		{
			Binding* any = find_any_copy_move_constructor(target, true);
			if (any != NULL && !any->is_defaulted)
				copy_move = any;
		}
			if (copy_move != NULL &&
			    !suppress_generated_trivial_copy_move_constructor_call(
				    copy_move) &&
			    !no_op_generated_default_constructor(copy_move, target))
				out.insert(copy_move);
	}
	void collect_node_lowered_constructor_calls(const Node& node,
	                                           set<const Binding*>& out)
	{
		if (starts_with(node.line, "base-init-action") &&
		    node.type.get() != NULL &&
		    !node.children.empty())
		{
			const Node& init = node.children[0];
			Binding* direct = node.direct_call != NULL
				? node.direct_call : init.direct_call;
			if (direct != NULL &&
			    !suppress_generated_aggregate_constructor_call(direct) &&
			    !suppress_prelowered_constructor_body_demand_for_type(
				    direct,
				    node.type) &&
			    !no_op_generated_default_constructor(direct, node.type))
				out.insert(direct);
			const Node& copy_source =
				starts_with(init.line, "braced-init-list") &&
				init.children.size() == 1
					? init.children[0]
					: init;
			collect_copy_move_constructor_for_init(node.type,
			                                       copy_source,
			                                       out);
		}
			if (starts_with(node.line, "member-init-action") &&
			    node.binding != NULL &&
			    !node.children.empty())
		{
			Binding* direct = node.direct_call != NULL
				? node.direct_call : node.children[0].direct_call;
			if (direct != NULL &&
			    !suppress_generated_aggregate_constructor_call(direct) &&
			    !suppress_prelowered_constructor_body_demand_for_type(
				    direct,
				    node.binding->type) &&
			    !no_op_generated_default_constructor(direct,
			                                         node.binding->type))
				out.insert(direct);
				collect_copy_move_constructor_for_init(node.binding->type,
				                                       node.children[0],
				                                       out);
			}
			if (starts_with(node.line, "braced-init-list") &&
			    node.type.get() != NULL)
			{
				TypePtr bare = pa11::strip_cv(node.type);
				if (bare->kind == TypeKind::Record)
				{
					Binding* ctor = node.direct_call != NULL
						? node.direct_call
						: find_constructor(bare,
						                   node.children.size());
					if (ctor != NULL &&
					    !suppress_generated_aggregate_constructor_call(ctor) &&
					    !suppress_prelowered_constructor_body_demand_for_type(
						    ctor,
						    bare) &&
					    !no_op_generated_default_constructor(ctor, bare))
						out.insert(ctor);
				}
			}
		}
	void collect_lowered_constructor_calls(const Node& node,
	                                       set<const Binding*>& out)
	{
		collect_node_lowered_constructor_calls(node, out);
		for (size_t i = 0; i < node.children.size(); ++i)
			collect_lowered_constructor_calls(node.children[i], out);
	}
	void collect_defaulted_assignment_field_calls(const Binding* binding,
	                                             set<const Binding*>& out)
	{
		if (binding == NULL ||
		    binding->name != "operator=" ||
		    binding->type.get() == NULL ||
		    binding->type->kind != TypeKind::Function ||
		    binding->type->parameters.size() != 2)
			return;
		bool generated_or_defaulted =
			binding->is_generated_copy_move_assignment ||
			binding->is_defaulted;
		if (!generated_or_defaulted)
			return;
		bool move =
			binding->type->parameters[1]->kind ==
			TypeKind::RValueReference;
		TypePtr record = class_record_for_member(binding);
		record = record.get() != NULL ? pa11::strip_cv(record) : TypePtr();
		if (record.get() == NULL || record->kind != TypeKind::Record)
			return;
		pa11::layout_record_type(record);
		for (size_t i = 0; i < record->fields.size(); ++i)
		{
			Binding* op = find_record_copy_move_assignment(
				record->fields[i]->type, move);
			if (op == NULL && move)
				op = find_record_copy_move_assignment(
					record->fields[i]->type, false);
				if (op != NULL)
				{
					out.insert(op);
				}
		}
	}
	void collect_body_demand_calls_impl(const Node& node,
	                                    set<const Binding*>& out,
	                                    bool skip_inline_function_bodies)
	{
		if (constant_evaluation_only_subtree(node) ||
		    (skip_inline_function_bodies &&
		     skip_translation_unit_call_subtree(node)))
			return;
		if (starts_with(node.line, "function-definition ") &&
		    hosted_library_binding(node.binding) &&
		    !node.binding->is_object_root)
			return;
		Binding* callee = node.direct_call != NULL
			? node.direct_call : call_expression_callee_binding(node);
		if (callee != NULL &&
		    !suppress_generated_aggregate_constructor_call(callee) &&
		    !suppress_prelowered_constructor_body_demand(callee) &&
		    !suppress_noop_generated_constructor_call(node))
			out.insert(callee);
		if (starts_with(node.line, "unary-expression") &&
		    node.has_op &&
		    node.op == OP_AMP &&
		    !node.children.empty() &&
		    node.children[0].binding != NULL &&
			node.children[0].binding->kind == BindingKind::Function &&
		    hosted_addressed_function_needs_body(node.children[0].binding))
			out.insert(node.children[0].binding);
		if (callee != NULL)
			collect_defaulted_assignment_field_calls(callee, out);
		collect_node_implicit_lifecycle_calls(node, out);
		collect_node_lowered_constructor_calls(node, out);
		if (starts_with(node.line, "function-definition "))
			collect_defaulted_assignment_field_calls(node.binding, out);
		for (size_t i = 0; i < node.children.size(); ++i)
			collect_body_demand_calls_impl(node.children[i],
			                               out,
			                               skip_inline_function_bodies);
	}
	void collect_body_demand_calls(const Node& node,
	                               set<const Binding*>& out)
	{
		collect_body_demand_calls_impl(node, out, false);
	}
	void collect_translation_unit_body_demand_calls(const Node& node,
	                                                set<const Binding*>& out)
	{
		collect_body_demand_calls_impl(node, out, true);
	}
	void mark_object_root_bindings(const set<const Binding*>& bindings,
	                               bool hosted_compatibility)
	{
		for (set<const Binding*>::const_iterator it = bindings.begin();
		     it != bindings.end();
		     ++it)
		{
			Binding* binding = const_cast<Binding*>(*it);
			if (binding == NULL)
				continue;
			if (hosted_compatibility && hosted_library_binding(binding))
				continue;
			binding->is_object_root = true;
			if (binding->aliased_binding != NULL)
				binding->aliased_binding->is_object_root = true;
		}
	}
	void note_function_definitions(ProgramLowerer& program, const Node& node)
	{
		if (starts_with(node.line, "function-definition ") &&
		    node.binding != NULL)
		{
			program.function_definition_bindings.insert(node.binding);
			if (node.binding->is_inline_definition &&
			    !node.binding->is_explicit_defaulted_definition)
				program.register_inline_definition(node);
		}
		for (size_t i = 0; i < node.children.size(); ++i)
			note_function_definitions(program, node.children[i]);
	}
void collect_base_constructor_calls(const Node& node, set<const Binding*>& out)
{
	if (node.direct_call != NULL && starts_with(node.line, "base-init-action"))
		out.insert(node.direct_call);
	for (size_t i = 0; i < node.children.size(); ++i)
		collect_base_constructor_calls(node.children[i], out);
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
bool same_binding_or_alias(const Binding* left, const Binding* right)
{
	if (left == right ||
	    (left != NULL && left->aliased_binding == right) ||
	    (right != NULL && right->aliased_binding == left))
		return true;
	if (left == NULL || right == NULL ||
	    left->kind != BindingKind::Function ||
	    right->kind != BindingKind::Function)
		return false;
	string left_object = global_object_symbol(left);
	string right_object = global_object_symbol(right);
	if (!left_object.empty() && left_object == right_object)
		return true;
	string left_symbol = left->function_specialization_symbol;
	string right_symbol = right->function_specialization_symbol;
	if (left_symbol.empty() && left->aliased_binding != NULL)
		left_symbol = left->aliased_binding->function_specialization_symbol;
	if (right_symbol.empty() && right->aliased_binding != NULL)
		right_symbol = right->aliased_binding->function_specialization_symbol;
	return !left_symbol.empty() && left_symbol == right_symbol;
}
bool early_hidden_friend_definition(const Node& node,
                                    const set<const Binding*>& direct_calls)
{
	if (node.binding == NULL || !node.binding->is_hidden_friend)
		return false;
	for (set<const Binding*>::const_iterator it = direct_calls.begin();
	     it != direct_calls.end(); ++it)
		if (same_binding_or_alias(node.binding, *it))
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
	bool referenced_extra_function(const Node& node,
	                               const set<const Binding*>& direct_calls,
	                               bool hosted_compatibility)
	{
		if (!starts_with(node.line, "function-definition ") ||
		    node.binding == NULL ||
		    node.binding->is_inline_definition)
			return false;
		if (hosted_compatibility &&
		    hosted_library_binding(node.binding) &&
		    !node.binding->is_object_root)
			return false;
		if (node.binding->is_object_root)
			return true;
	for (set<const Binding*>::const_iterator it = direct_calls.begin();
	     it != direct_calls.end(); ++it)
		if (same_binding_or_alias(node.binding, *it))
			return true;
	return false;
}
	void collect_referenced_extra_functions(ProgramLowerer& program,
	                                        const vector<Node>& extra,
	                                        const set<const Binding*>& direct_calls,
	                                        bool hosted_compatibility)
	{
		set<string> collected;
		for (size_t i = 0; i < extra.size(); ++i)
		{
			if (!referenced_extra_function(extra[i],
			                               direct_calls,
			                               hosted_compatibility))
				continue;
			string name = program.symbol_for(extra[i].binding);
		if (program.defined_functions.find(name) !=
		        program.defined_functions.end() ||
		    !collected.insert(name).second)
			continue;
		program.collect_node(extra[i]);
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
		program.collect_node(node);
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
	void collect_explicit_defaulted_definitions(ProgramLowerer& program,
	                                            const Node& node)
	{
		if (starts_with(node.line, "function-definition ") &&
		    ((node.binding != NULL &&
		      node.binding->is_explicit_defaulted_definition) ||
		     node.token_text == "defaulted-definition"))
		{
			program.collect_node(node);
			return;
		}
		for (size_t i = 0; i < node.children.size(); ++i)
			collect_explicit_defaulted_definitions(program, node.children[i]);
	}
	void demand_early_hidden_friends(ProgramLowerer& program,
		                                 const vector<Node>& extra,
		                                 const set<const Binding*>& direct_calls)
{
	for (size_t i = 0; i < extra.size(); ++i)
	{
		if (!early_hidden_friend_definition(extra[i], direct_calls))
			continue;
		program.demand_inline_function(extra[i].binding);
		program.emit_pending_inline_definitions();
		}
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
			bool inline_body =
				binding->is_inline_definition ||
				(binding->aliased_binding != NULL &&
				 binding->aliased_binding->is_inline_definition) ||
				binding_has_template_specialization_context(binding) ||
				!binding->function_specialization_symbol.empty() ||
				(binding->aliased_binding != NULL &&
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
		for (set<const Binding*>::const_iterator it = generated_calls.begin();
		     it != generated_calls.end(); ++it)
			program.demand_inline_function(*it);
	}
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
	}
}
void emit_deferred_constant_template_static_members(ProgramLowerer& program)
{
	vector<const Binding*> ready;
	for (map<const Binding*, Node>::const_iterator it =
		     program.deferred_global_definitions.begin();
	     it != program.deferred_global_definitions.end();
	     ++it)
	{
		const Binding* binding = it->first;
		if (binding == NULL ||
		    !binding->is_template_static_member_definition ||
		    !binding->has_constant)
			continue;
		TypePtr object = strip_for_value(binding->type);
		TypePtr bare = pa11::strip_cv(object);
		if (bare->kind == TypeKind::Array ||
		    bare->kind == TypeKind::Record)
			continue;
		ready.push_back(binding);
	}
	for (size_t i = 0; i < ready.size(); ++i)
		program.demand_deferred_global_definition(ready[i]);
}
	const Node* extra_node_for_binding(const vector<Node>& extra,
	                                   const Binding* binding)
{
	for (size_t i = 0; i < extra.size(); ++i)
		if (same_binding_or_alias(extra[i].binding, binding))
			return &extra[i];
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
	    object_root_call != NULL &&
	    !hosted_library_binding(object_root_call))
	{
		object_root_call->is_object_root = true;
		if (object_root_call->aliased_binding != NULL)
			object_root_call->aliased_binding->is_object_root = true;
	}
	bool candidate =
		!hosted_compatibility ||
		hosted_library_body_candidate(call) ||
		default_constructor_call(call);
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
		bool hosted_root_template_body =
			hosted_compatibility &&
			hosted_library_binding(body->binding) &&
			body->binding->is_object_root &&
			binding_has_template_specialization_context(body->binding);
		if (hosted_root_template_body &&
		    body->binding->name == "operator=")
			return true;
		collect_direct_calls(*body, direct_calls);
		collect_addressed_functions(*body, direct_calls);
		collect_implicit_lifecycle_calls(*body, direct_calls);
		if (!hosted_nonroot_body)
			collect_lowered_constructor_calls(*body, direct_calls);
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
				if (scan_extra &&
				    hosted_compatibility &&
				    node.binding != NULL &&
				    hosted_library_binding(node.binding) &&
				    node.binding->is_object_root &&
				    binding_has_template_specialization_context(node.binding) &&
				    node.binding->name == "operator=")
					scan_extra = false;
			if (scan_extra)
			{
				collect_direct_calls(node, direct_calls);
				collect_addressed_functions(node, direct_calls);
				collect_implicit_lifecycle_calls(node, direct_calls);
				collect_lowered_constructor_calls(node, direct_calls);
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
			for (size_t i = 0; i < extra.size(); ++i)
			{
				const Node& node = extra[i];
				if (!starts_with(node.line, "function-definition ") ||
				    node.binding == NULL)
					continue;
				bool referenced = false;
				for (set<const Binding*>::const_iterator it =
					     direct_calls.begin();
				     it != direct_calls.end();
				     ++it)
					if (same_binding_or_alias(node.binding, *it))
					{
						referenced = true;
						break;
					}
				if (!referenced || !scanned.insert(node.binding).second)
					continue;
				collect_node_implicit_lifecycle_calls(node, discovered);
				collect_node_lowered_constructor_calls(node, discovered);
				for (size_t child = 0; child < node.children.size(); ++child)
					collect_body_demand_calls(node.children[child],
					                          discovered);
			}
			if (discovered.empty())
				break;
			if (hosted_compatibility)
				mark_object_root_bindings(discovered,
				                          hosted_compatibility);
			demand_parser_direct_call_bodies(parser,
			                                 discovered,
			                                 hosted_compatibility);
			size_t before = direct_calls.size();
			direct_calls.insert(discovered.begin(), discovered.end());
			if (direct_calls.size() == before)
				break;
		}
	}
	void collect_parser_output(ProgramLowerer& program,
	                           pa12::internal::Parser& parser,
	                           bool hosted_compatibility)
	{
		const vector<Node>& extra = parser.extra_lowir_nodes();
		set<const Binding*> direct_calls;
		set<const Binding*> body_demands;
		set<const Binding*> root_definitions;
		set<const Binding*> complete_constructor_entries;
		if (hosted_compatibility)
			collect_translation_unit_body_demand_calls(parser.root(),
			                                           direct_calls);
		else
		{
			collect_translation_unit_direct_calls(parser.root(),
			                                      direct_calls);
			collect_translation_unit_addressed_functions(parser.root(),
			                                             direct_calls);
		}
		if (hosted_compatibility)
			mark_object_root_bindings(direct_calls, hosted_compatibility);
		demand_parser_direct_call_bodies(parser,
		                                 direct_calls,
		                                 hosted_compatibility);
		collect_translation_unit_body_demand_calls(parser.root(),
		                                           body_demands);
		if (hosted_compatibility)
			mark_object_root_bindings(body_demands, hosted_compatibility);
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
			                          hosted_compatibility);
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
		parser.complete_static_member_initializer_replays();
		collect_static_downcast_sources(program, parser.root());
		for (size_t i = 0; i < extra.size(); ++i)
			collect_static_downcast_sources(program, extra[i]);
		note_function_definitions(program, parser.root());
		root_definitions = program.function_definition_bindings;
		for (size_t i = 0; i < extra.size(); ++i)
			note_function_definitions(program, extra[i]);
		collect_complete_constructor_entry_references(parser.root(),
		                                              complete_constructor_entries);
		for (size_t i = 0; i < extra.size(); ++i)
		{
			collect_constructor_base_entry_references(program, extra[i]);
			collect_complete_constructor_entry_references(
				extra[i],
				complete_constructor_entries);
		}
			for (size_t i = 0; i < extra.size(); ++i)
				program.register_inline_definition(extra[i]);
			for (size_t i = 0; i < extra.size(); ++i)
				collect_extra_variable(program, extra[i]);
			demand_referenced_inline_definitions(
				program,
				direct_calls,
				complete_constructor_entries);
			demand_object_roots(program, extra, root_definitions);
		demand_early_hidden_friends(program, extra, direct_calls);
		if (hosted_compatibility)
			collect_translation_unit_filtered(program,
			                                  parser.root(),
			                                  hosted_compatibility);
		else
			program.collect_translation_unit(parser.root());
		if (hosted_compatibility)
			emit_deferred_constant_template_static_members(program);
			collect_explicit_defaulted_definitions(program, parser.root());
			collect_referenced_extra_functions(program,
			                                   extra,
			                                   direct_calls,
		                                   hosted_compatibility);
	demand_noop_generated_default_dependencies(program, extra, direct_calls);
	demand_generated_copy_move_dependencies(program,
	                                        extra,
	                                        hosted_compatibility);
	program.emit_pending_inline_definitions();
	program.emit_pending_synthetic_assignment_functions();
}
}  // namespace
}  // namespace internal
void emit_lowir(const vector<string>& srcfiles,
                const string& outfile,
                const Options& options)
{
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
	program.write(outfile);
}
}  // namespace pa14
