#include "pa14_lowir_internal.h"
#include "pa12_templates_function_support.h"

namespace pa14 {
namespace internal {

bool constructor_record_contains_hosted_subobject(const Binding* binding);
bool hosted_addressed_function_needs_body(const Binding* binding);
Binding* addressed_function_binding(const Node& node);
TypePtr function_return_type(const Binding* binding);
bool empty_defaulted_copy_move_constructor_needs_helper(const Node& node);
Binding* call_expression_callee_binding(const Node& node);
bool hosted_bit_const_iterator_deref_binding(const Binding* binding);
bool hosted_bit_const_iterator_preincrement_binding(const Binding* binding);

namespace {
bool native_lifecycle_demands_enabled = false;
}

NativeLifecycleDemandScope::NativeLifecycleDemandScope(bool enabled)
	: previous_(native_lifecycle_demands_enabled)
{
	native_lifecycle_demands_enabled = enabled;
}

NativeLifecycleDemandScope::~NativeLifecycleDemandScope()
{
	native_lifecycle_demands_enabled = previous_;
}

	bool lowir_skip_function_definition_node(const Node& node)
	{
		return node.token_text == "deleted" ||
		       (node.binding != NULL &&
		        !pa12::internal::substituted_type_is_valid(
			        node.binding->type));
	}

				bool suppress_generated_aggregate_constructor_call(const Binding* binding)
			{
				return binding != NULL &&
				       binding->is_generated_aggregate_constructor;
			}
				bool suppress_generated_trivial_copy_move_constructor_call(const Binding* binding)
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
					if (hosted_library_binding(binding))
					{
						string symbol = global_object_symbol(binding);
						if (symbol.find("12_Vector_impl") != string::npos &&
						    (symbol.find("C1EOS") != string::npos ||
						     symbol.find("C2EOS") != string::npos))
							return false;
					}
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
			bool suppress_prelowered_constructor_body_demand(const Binding* binding)
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
				       binding->is_generated_copy_move_constructor &&
				       suppress_generated_trivial_copy_move_constructor_call(
					       binding) &&
				       !specialized;
			}
			bool suppress_prelowered_constructor_body_demand_for_type(const Binding* binding, TypePtr constructed_type)
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
	string unqualified_hosted_record_primary(TypePtr record)
	{
		TypePtr bare = record.get() != NULL ? pa11::strip_cv(record)
		                                    : TypePtr();
		if (bare.get() == NULL || bare->kind != TypeKind::Record)
			return "";
		string primary = bare->template_primary_name.empty()
			? bare->name : bare->template_primary_name;
		size_t args = primary.find('<');
		if (args != string::npos)
			primary = primary.substr(0, args);
		size_t scope = primary.rfind("::");
		if (scope != string::npos)
			primary = primary.substr(scope + 2);
		return primary;
	}
	bool hosted_record_has_namespace(TypePtr record, const string& name)
	{
		TypePtr bare = record.get() != NULL ? pa11::strip_cv(record)
		                                    : TypePtr();
		for (Scope* scope = bare.get() != NULL ? bare->scope : NULL;
		     scope != NULL;
		     scope = scope->parent)
			if (scope->kind == ScopeKind::Namespace &&
			    scope->name == name)
				return true;
		return false;
	}
	bool hosted_normal_iterator_helper_body_root(const Binding* binding)
	{
		TypePtr record = class_record_for_member(binding);
		if (!hosted_record_has_namespace(record, "__gnu_cxx") ||
		    unqualified_hosted_record_primary(record) !=
			    pa11::abi_private_name("_normal_iterator"))
			return false;
		return binding->name == "base" ||
		       binding->name == "operator*" ||
		       binding->name == "operator++" ||
		       binding->name == "operator--" ||
		       binding->name == "operator+" ||
		       binding->name == "operator-" ||
		       is_class_destructor_binding(binding) ||
		       is_class_constructor_binding(binding);
	}
	void collect_hosted_normal_iterator_destructor_dependency(
		const Binding* binding,
		set<const Binding*>& out)
	{
		TypePtr record = class_record_for_member(binding);
		if (!hosted_record_has_namespace(record, "__gnu_cxx") ||
		    unqualified_hosted_record_primary(record) !=
			    pa11::abi_private_name("_normal_iterator"))
			return;
		Binding* dtor = find_destructor(record);
		if (dtor != NULL)
			out.insert(dtor);
	}
	bool hosted_move_iterator_helper_body_root(const Binding* binding)
	{
		string symbol = global_object_symbol(binding);
		if (symbol.find("St13move_iterator") != string::npos &&
		    (symbol.find("4baseEv") != string::npos ||
		     symbol.find("deEv") != string::npos ||
		     symbol.find("ppEv") != string::npos ||
		     symbol.find("EC1") != string::npos ||
		     symbol.find("EC2") != string::npos))
			return true;
		TypePtr record = class_record_for_member(binding);
		if (!hosted_record_has_namespace(record, "std") ||
		    unqualified_hosted_record_primary(record) != "move_iterator")
			return false;
		return binding->name == "base" ||
		       binding->name == "operator*" ||
		       binding->name == "operator++" ||
		       is_class_constructor_binding(binding);
	}
	bool hosted_uninit_destroy_guard_helper_body_root(const Binding* binding)
	{
		string symbol = global_object_symbol(binding);
		if (symbol.find("St19_UninitDestroyGuard") != string::npos &&
		    (symbol.find("7releaseEv") != string::npos ||
		     symbol.find("EC1") != string::npos ||
		     symbol.find("EC2") != string::npos))
			return true;
		TypePtr record = class_record_for_member(binding);
		if (!hosted_record_has_namespace(record, "std") ||
		    unqualified_hosted_record_primary(record) !=
			    pa11::abi_private_name("UninitDestroyGuard"))
			return false;
		return binding->name == "release" ||
		       is_class_constructor_binding(binding);
	}
	bool hosted_vector_impl_default_constructor_body_root(
		const Binding* binding)
	{
		string symbol = global_object_symbol(binding);
		if (symbol.find("12_Vector_impl") != string::npos &&
		    (symbol.find("C1EOS") != string::npos ||
		     symbol.find("C2EOS") != string::npos ||
		     symbol.find("C1Ev") != string::npos ||
		     symbol.find("C2Ev") != string::npos))
			return true;
		TypePtr record = class_record_for_member(binding);
		return hosted_record_has_namespace(record, "std") &&
		       unqualified_hosted_record_primary(record) ==
			       pa11::abi_private_name("Vector_impl") &&
		       is_class_constructor_binding(binding) &&
		       binding->type.get() != NULL &&
		       binding->type->kind == TypeKind::Function &&
		       (binding->type->parameters.size() == 1 ||
		        binding->type->parameters.size() == 2);
	}
	bool hosted_allocator_traits_helper_body_root(const Binding* binding)
	{
		string symbol = global_object_symbol(binding);
		if (symbol.find("St16allocator_traits") != string::npos &&
		    symbol.find("7destroy") != string::npos)
			return true;
		TypePtr record = class_record_for_member(binding);
		string primary = unqualified_hosted_record_primary(record);
		if (hosted_record_has_namespace(record, "std") &&
		    primary == "allocator_traits" &&
		    binding->name == "destroy")
			return true;
		if (hosted_record_has_namespace(record, "__gnu_cxx") &&
		    primary == pa11::abi_private_name("_alloc_traits") &&
		    binding->name == pa11::abi_private_name("S_select_on_copy"))
			return true;
		return false;
	}
	bool hosted_allocator_rebind_constructor_body_root(const Binding* binding)
	{
		if (!is_class_constructor_binding(binding) ||
		    binding->type.get() == NULL ||
		    binding->type->kind != TypeKind::Function ||
		    binding->type->parameters.size() != 2 ||
		    binding->type->parameters[1].get() == NULL ||
		    binding->type->parameters[1]->kind != TypeKind::LValueReference)
			return false;
		TypePtr record = class_record_for_member(binding);
		record = record.get() != NULL ? pa11::strip_cv(record) : TypePtr();
		TypePtr param =
			pa11::strip_cv(binding->type->parameters[1]->base);
		if (record.get() == NULL ||
		    param.get() == NULL ||
		    record->kind != TypeKind::Record ||
		    param->kind != TypeKind::Record ||
		    !hosted_record_has_namespace(record, "std") ||
		    !hosted_record_has_namespace(param, "std"))
			return false;
		string primary = unqualified_hosted_record_primary(record);
		string param_primary = unqualified_hosted_record_primary(param);
		return (primary == "allocator" && param_primary == "allocator") ||
		       (primary == "__new_allocator" &&
		        param_primary == "__new_allocator");
	}
	bool hosted_uninitialized_algorithm_body_root(const Binding* binding)
	{
		string symbol = global_object_symbol(binding);
		return starts_with(symbol, "_ZSt16__do_uninit_copy") ||
		       starts_with(symbol, "_ZSt25__uninitialized_default_n") ||
		       starts_with(symbol, "_ZSt27__uninitialized_default_n_a") ||
		       starts_with(symbol, "_ZSt29__lexicographical_compare_aux") ||
		       starts_with(symbol, "_ZSt30__lexicographical_compare_aux1") ||
		       starts_with(symbol, "_ZNSt25__lexicographical_compareILb0EE4__lc") ||
		       starts_with(symbol, "_ZSt18uninitialized_copy") ||
		       starts_with(symbol, "_ZSt22__uninitialized_copy_a") ||
		       starts_with(symbol, "_ZSt19__relocate_object_a") ||
		       starts_with(symbol, "_ZSt14__relocate_a_1") ||
		       symbol.find("__uninitialized_default_n_1") != string::npos ||
		       starts_with(symbol,
		                   "_ZSt32__make_move_if_noexcept_iterator") ||
		       ((starts_with(symbol, "_ZSteq") ||
		         starts_with(symbol, "_ZStne")) &&
		        symbol.find("St13move_iterator") != string::npos);
	}
	bool hosted_rbtree_helper_body_root(const Binding* binding)
	{
		string symbol = global_object_symbol(binding);
		if (symbol.find("St15_Rb_tree_header") != string::npos)
			return symbol.find("8_M_resetEv") != string::npos ||
			       symbol.find("12_M_move_dataERS_") != string::npos ||
			       symbol.find("C1Ev") != string::npos ||
			       symbol.find("C2Ev") != string::npos ||
			       symbol.find("C1EOS_") != string::npos ||
			       symbol.find("C2EOS_") != string::npos;
		if (symbol.find("St20_Rb_tree_key_compare") != string::npos)
			return symbol.find("C1EOS_") != string::npos ||
			       symbol.find("C2EOS_") != string::npos;
		if (symbol.find("St23_Rb_tree_const_iterator") != string::npos)
			return symbol.find("C1EPSt18_Rb_tree_node_base") !=
			           string::npos ||
			       symbol.find("C2EPSt18_Rb_tree_node_base") !=
			           string::npos;
		if (symbol.find("St8_Rb_tree") != string::npos)
			return symbol.find("14_M_create_node") != string::npos ||
			       symbol.find("13_Rb_tree_impl") != string::npos ||
			       symbol.find("aSERK") != string::npos ||
			       symbol.find("aSEO") != string::npos ||
			       symbol.find("C1Ev") != string::npos ||
			       symbol.find("C2Ev") != string::npos ||
			       symbol.find("C1ERKS") != string::npos ||
			       symbol.find("C2ERKS") != string::npos ||
			       symbol.find("C1EOS") != string::npos ||
			       symbol.find("C2EOS") != string::npos;
		return false;
	}
	bool hosted_basic_string_resize_overwrite_body_root(
		const Binding* binding)
	{
		string symbol = global_object_symbol(binding);
		return binding != NULL &&
		       (binding->name == "__resize_and_overwrite" ||
		        symbol.find("22__resize_and_overwrite") != string::npos);
	}
	bool hosted_vector_bool_helper_body_root(const Binding* binding)
	{
		string symbol = global_object_symbol(binding);
		if (symbol.find("St13_Bvector_base") != string::npos &&
		    symbol.find("13_Bvector_impl") != string::npos &&
		    (symbol.find("C1Ev") != string::npos ||
		     symbol.find("C2Ev") != string::npos))
			return true;
		if (hosted_bit_const_iterator_deref_binding(binding) ||
		    hosted_bit_const_iterator_preincrement_binding(binding))
			return true;
		if (starts_with(symbol, "_ZNSt7__equalILb0EE5equal"))
			return true;
		return false;
	}
	TypePtr hosted_dependency_record_type(TypePtr type)
	{
		TypePtr bare = type.get() != NULL ? pa11::strip_cv(type)
		                                  : TypePtr();
		if (bare.get() != NULL && is_reference(bare))
			bare = pa11::strip_cv(bare->base);
		return bare.get() != NULL && bare->kind == TypeKind::Record
			? bare : TypePtr();
	}
	bool hosted_bit_const_iterator_dependency_record(TypePtr type)
	{
		TypePtr record = hosted_dependency_record_type(type);
		if (!hosted_record_has_namespace(record, "std"))
			return false;
		if (record.get() == NULL ||
		    record->kind != TypeKind::Record)
			return false;
		vector<TypePtr> bases = pa11::record_direct_bases(record);
		for (size_t i = 0; i < bases.size(); ++i)
		{
			TypePtr base = pa11::strip_cv(bases[i]);
			if (base.get() != NULL &&
			    base->kind == TypeKind::Record &&
			    hosted_record_has_namespace(base, "std") &&
			    unqualified_hosted_record_primary(base) ==
				    pa11::abi_private_name("Bit_iterator_base"))
				return true;
		}
		return false;
	}
	void collect_hosted_member_named(TypePtr record,
	                                 const string& name,
	                                 set<const Binding*>& out)
	{
		record = hosted_dependency_record_type(record);
		if (record.get() == NULL || record->scope == NULL)
			return;
		map<string, vector<Binding*> >::const_iterator it =
			record->scope->members.find(name);
		if (it == record->scope->members.end())
			return;
		for (size_t i = 0; i < it->second.size(); ++i)
			if (hosted_vector_bool_helper_body_root(it->second[i]))
				out.insert(it->second[i]);
	}
	void collect_hosted_vector_bool_algorithm_dependencies(
		const Binding* binding,
		set<const Binding*>& out)
	{
		string symbol = global_object_symbol(binding);
		if (!starts_with(symbol, "_ZSt12__assign_one") &&
		    !starts_with(symbol, "_ZSt13__copy_move_a") &&
		    !starts_with(symbol, "_ZSt14__copy_move_a1") &&
		    !starts_with(symbol, "_ZSt14__copy_move_a2"))
			return;
		if (binding == NULL ||
		    binding->type.get() == NULL ||
		    binding->type->kind != TypeKind::Function)
			return;
		for (size_t i = 0; i < binding->type->parameters.size(); ++i)
		{
			TypePtr param = binding->type->parameters[i];
			if (!hosted_bit_const_iterator_dependency_record(param))
				continue;
			TypePtr record = hosted_dependency_record_type(param);
			collect_hosted_member_named(record, "operator*", out);
			collect_hosted_member_named(record, "operator++", out);
		}
	}
	map<const Binding*, bool>& hosted_nested_helper_body_root_cache()
	{
		static map<const Binding*, bool> cache;
		return cache;
	}
	bool hosted_nested_helper_body_root(const Binding* binding)
	{
		map<const Binding*, bool>& cache =
			hosted_nested_helper_body_root_cache();
		map<const Binding*, bool>::const_iterator found = cache.find(binding);
		if (found != cache.end())
			return found->second;
		bool result = binding != NULL &&
		       binding->type.get() != NULL &&
		       binding->type->kind == TypeKind::Function &&
		       pa12::internal::substituted_type_is_valid(binding->type) &&
		       (hosted_normal_iterator_helper_body_root(binding) ||
		        hosted_move_iterator_helper_body_root(binding) ||
		        hosted_uninit_destroy_guard_helper_body_root(binding) ||
		        hosted_vector_impl_default_constructor_body_root(binding) ||
		        hosted_allocator_traits_helper_body_root(binding) ||
		        hosted_allocator_rebind_constructor_body_root(binding) ||
		        hosted_uninitialized_algorithm_body_root(binding) ||
		        hosted_rbtree_helper_body_root(binding) ||
		        hosted_basic_string_resize_overwrite_body_root(binding) ||
		        hosted_vector_bool_helper_body_root(binding));
		cache[binding] = result;
		return result;
	}
	bool should_mark_direct_call_object_root(const Binding* binding,
	                                         bool hosted_compatibility)
	{
		if (binding == NULL)
			return false;
		if (!hosted_compatibility || !hosted_library_binding(binding))
			return true;
		return hosted_library_body_candidate(binding) ||
		       hosted_unordered_map_body_root(binding) ||
		       lowir_synthesizable_hosted_inline_body(binding) ||
		       lowir_synthesizable_hosted_hashtable_range_constructor(binding) ||
		       lowir_synthesizable_hosted_vector_copy_constructor(binding) ||
		       lowir_synthesizable_hosted_vector_copy_assignment(binding) ||
		       lowir_synthesizable_hosted_vector_range_insert(binding) ||
		       lowir_synthesizable_hosted_vector_realloc_insert(binding) ||
		       lowir_synthesizable_hosted_vector_initializer_realloc_insert(
			       binding) ||
		       lowir_synthesizable_hosted_initializer_list_allocator_construct(
			       binding) ||
		       lowir_synthesizable_hosted_unique_ptr_allocator_copy_construct(
			       binding) ||
		       lowir_synthesizable_hosted_unique_ptr_copy_helper(binding) ||
		       hosted_nested_helper_body_root(binding);
	}
	bool should_mark_body_demand_object_root(const Binding* binding,
	                                         bool hosted_compatibility)
	{
		if (binding == NULL)
			return false;
		if (!hosted_compatibility || !hosted_library_binding(binding))
			return true;
		return hosted_library_body_candidate(binding) ||
		       lowir_synthesizable_hosted_inline_body(binding);
	}
	bool constant_evaluation_only_subtree(const Node& node)
	{
		if (starts_with(node.line, "static-assert-declaration"))
			return true;
		if (!starts_with(node.line, "variable ") ||
		    node.binding == NULL ||
		    (!node.binding->is_constexpr && !node.binding->has_constant))
			return false;
		TypePtr object = strip_for_value(node.binding->type);
		TypePtr bare = pa11::strip_cv(object);
		return bare->kind != TypeKind::Array &&
		       bare->kind != TypeKind::Record;
	}
	bool skip_translation_unit_call_subtree(const Node& node)
	{
		if (constant_evaluation_only_subtree(node))
			return true;
		return starts_with(node.line, "function-definition ") &&
		       node.binding != NULL &&
		       node.binding->is_inline_definition;
	}
		void collect_direct_calls_impl(const Node& node, set<const Binding*>& out, bool skip_inline_function_bodies)
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
	void collect_translation_unit_direct_calls(const Node& node, set<const Binding*>& out)
	{
			collect_direct_calls_impl(node, out, true);
		}
		void collect_addressed_functions_impl(const Node& node, set<const Binding*>& out, bool skip_inline_function_bodies)
		{
			if (constant_evaluation_only_subtree(node) ||
			    (skip_inline_function_bodies &&
			     skip_translation_unit_call_subtree(node)))
				return;
			Binding* addressed = addressed_function_binding(node);
			if (addressed != NULL &&
			    hosted_addressed_function_needs_body(addressed))
				out.insert(addressed);
			for (size_t i = 0; i < node.children.size(); ++i)
				collect_addressed_functions_impl(node.children[i],
				                                 out,
				                                 skip_inline_function_bodies);
	}
	void collect_addressed_functions(const Node& node, set<const Binding*>& out)
	{
		collect_addressed_functions_impl(node, out, false);
	}
	void collect_translation_unit_addressed_functions(const Node& node, set<const Binding*>& out)
	{
		collect_addressed_functions_impl(node, out, true);
	}
	void collect_hosted_helper_function_references(const Node& node,
	                                               set<const Binding*>& out)
	{
		Binding* direct = node.direct_call != NULL
			? node.direct_call : call_expression_callee_binding(node);
		if (hosted_nested_helper_body_root(direct))
		{
			out.insert(direct);
			collect_hosted_normal_iterator_destructor_dependency(direct,
			                                                     out);
		}
		if (node.binding != NULL &&
		    node.binding->kind == BindingKind::Function &&
		    hosted_nested_helper_body_root(node.binding))
		{
			out.insert(node.binding);
			collect_hosted_normal_iterator_destructor_dependency(
				node.binding,
				out);
		}
		for (size_t i = 0; i < node.children.size(); ++i)
			collect_hosted_helper_function_references(node.children[i],
			                                          out);
	}
	void collect_destructor_demands_for_type(TypePtr type,
	                                         set<const Binding*>& out,
	                                         set<const pa11::Type*>& seen,
	                                         bool parameter_cleanup)
	{
		if (type.get() == NULL)
			return;
		TypePtr bare = pa11::strip_cv(type);
		if (bare->kind == TypeKind::Array)
		{
			collect_destructor_demands_for_type(bare->base,
			                                    out,
			                                    seen,
			                                    parameter_cleanup);
			return;
		}
		if (bare->kind != TypeKind::Record)
			return;
		if (!seen.insert(bare.get()).second)
			return;
		Binding* dtor = find_destructor(bare);
		if (dtor != NULL &&
		    (dtor->is_virtual ||
		     !dtor->is_noop_destructor ||
		     (native_lifecycle_demands_enabled &&
		      !dtor->is_generated_default_destructor &&
		      !dtor->is_defaulted) ||
		     (parameter_cleanup &&
		      !dtor->is_generated_default_destructor)))
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
		vector<Binding*> members;
		append_assignment_dependency_members(bare, members);
		vector<TypePtr> bases = pa11::record_direct_bases(bare);
		for (size_t i = 0; i < bases.size(); ++i)
			collect_destructor_demands_for_type(bases[i],
			                                    out,
			                                    seen,
			                                    parameter_cleanup);
		for (size_t i = 0; i < members.size(); ++i)
			collect_destructor_demands_for_type(members[i]->type,
			                                    out,
			                                    seen,
			                                    parameter_cleanup);
	}
	void collect_destructor_demands_for_type(TypePtr type, set<const Binding*>& out)
	{
		set<const pa11::Type*> seen;
		collect_destructor_demands_for_type(type, out, seen, false);
	}
	void collect_parameter_destructor_demands_for_type(TypePtr type,
	                                                   set<const Binding*>& out)
	{
		set<const pa11::Type*> seen;
		collect_destructor_demands_for_type(type, out, seen, true);
	}
	void collect_vtable_demands_for_type(TypePtr type, set<const Binding*>& out, set<const pa11::Type*>& seen)
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
	void collect_vtable_demands_for_type(TypePtr type, set<const Binding*>& out)
	{
		set<const pa11::Type*> seen;
		collect_vtable_demands_for_type(type, out, seen);
	}
	void collect_implicit_demands_for_type(TypePtr type, set<const Binding*>& out)
	{
		collect_destructor_demands_for_type(type, out);
		collect_vtable_demands_for_type(type, out);
	}
	void collect_node_implicit_lifecycle_calls(const Node& node, set<const Binding*>& out)
	{
		if (starts_with(node.line, "parameter ") && node.type.get() != NULL)
			collect_parameter_destructor_demands_for_type(node.type, out);
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
	void collect_implicit_lifecycle_calls(const Node& node, set<const Binding*>& out)
	{
		collect_node_implicit_lifecycle_calls(node, out);
		for (size_t i = 0; i < node.children.size(); ++i)
			collect_implicit_lifecycle_calls(node.children[i], out);
	}
	void collect_copy_move_constructor_for_init(TypePtr target, const Node& init, set<const Binding*>& out)
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
	void collect_return_copy_move_constructor(const Node& node, TypePtr return_type, set<const Binding*>& out)
	{
		if (!starts_with(node.line, "return-statement") ||
		    node.children.empty() ||
		    return_type.get() == NULL)
			return;
		TypePtr bare_return = pa11::strip_cv(return_type);
		if (bare_return.get() == NULL || bare_return->kind != TypeKind::Record)
			return;
		collect_copy_move_constructor_for_init(return_type,
		                                       node.children[0],
		                                       out);
	}
	bool return_slot_reuse_return_child(const Node& node,
	                                    size_t index,
	                                    TypePtr return_type)
	{
		if (!starts_with(node.line, "compound-statement") ||
		    index == 0 ||
		    index >= node.children.size() ||
		    return_type.get() == NULL ||
		    pa11::strip_cv(return_type)->kind != TypeKind::Record ||
		    !record_return_by_address(return_type))
			return false;
		const Node& decl = node.children[index - 1];
		const Node& ret = node.children[index];
		if (!starts_with(decl.line, "simple-declaration") ||
		    !starts_with(ret.line, "return-statement") ||
		    decl.children.size() != 1 ||
		    !starts_with(decl.children[0].line, "variable ") ||
		    decl.children[0].binding == NULL ||
		    ret.children.empty())
			return false;
		Binding* binding = decl.children[0].binding;
		const Node& ret_expr = ret.children[0];
		if (ret_expr.binding == binding)
			return true;
		string suffix = " " + binding->name;
		return starts_with(ret_expr.line, "id-expression") &&
		       ret_expr.line.size() >= suffix.size() &&
		       ret_expr.line.compare(ret_expr.line.size() - suffix.size(),
		                             suffix.size(),
		                             suffix) == 0;
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
	                                    bool skip_inline_function_bodies,
	                                    TypePtr return_type,
	                                    bool skip_return_copy = false)
	{
		if (constant_evaluation_only_subtree(node) ||
		    (skip_inline_function_bodies &&
		     skip_translation_unit_call_subtree(node)))
			return;
		if (starts_with(node.line, "function-definition ") &&
		    hosted_library_binding(node.binding) &&
		    !node.binding->is_object_root)
			return;
		TypePtr active_return_type = return_type;
		if (starts_with(node.line, "function-definition "))
			active_return_type = function_return_type(node.binding);
		Binding* callee = node.direct_call != NULL
			? node.direct_call : call_expression_callee_binding(node);
		if (callee != NULL &&
		    !suppress_generated_aggregate_constructor_call(callee) &&
		    !suppress_prelowered_constructor_body_demand(callee) &&
		    !suppress_noop_generated_constructor_call(node))
			out.insert(callee);
		if (callee == NULL &&
		    starts_with(node.line, "braced-init-list") &&
		    node.type.get() != NULL &&
		    pa11::strip_cv(node.type)->kind == TypeKind::Record)
		{
			Binding* ctor = find_constructor(node.type,
			                                 node.children.size());
			if (ctor != NULL &&
			    !suppress_generated_aggregate_constructor_call(ctor) &&
			    !suppress_prelowered_constructor_body_demand(ctor))
				out.insert(ctor);
		}
			Binding* addressed = addressed_function_binding(node);
			if (addressed != NULL &&
			    hosted_addressed_function_needs_body(addressed))
				out.insert(addressed);
		if (callee != NULL)
			collect_defaulted_assignment_field_calls(callee, out);
		collect_node_implicit_lifecycle_calls(node, out);
		collect_node_lowered_constructor_calls(node, out);
		if (!skip_return_copy)
			collect_return_copy_move_constructor(node, active_return_type, out);
		if (starts_with(node.line, "function-definition "))
			collect_defaulted_assignment_field_calls(node.binding, out);
		for (size_t i = 0; i < node.children.size(); ++i)
			collect_body_demand_calls_impl(node.children[i],
			                               out,
			                               skip_inline_function_bodies,
			                               active_return_type,
			                               return_slot_reuse_return_child(
				                               node,
				                               i,
				                               active_return_type));
	}
	void collect_translation_unit_body_demand_calls(const Node& node,
	                                                set<const Binding*>& out)
	{
		collect_body_demand_calls_impl(node, out, true, TypePtr());
	}
	void collect_global_init_constructor_demands(TypePtr type,
	                                            const Node& init,
	                                            set<const Binding*>& out)
	{
		TypePtr bare = type.get() != NULL ? pa11::strip_cv(type) : TypePtr();
		if (bare.get() == NULL)
			return;
		if (bare->kind == TypeKind::Array)
		{
			for (size_t i = 0; i < init.children.size(); ++i)
				collect_global_init_constructor_demands(bare->base,
				                                        init.children[i],
				                                        out);
			return;
		}
		if (bare->kind != TypeKind::Record)
			return;
		Binding* ctor = init.direct_call;
		if (ctor == NULL &&
		    (starts_with(init.line, "braced-init-list") ||
		     starts_with(init.line, "constructor-action")))
			ctor = find_constructor(type, init.children.size());
		if (ctor != NULL &&
		    !suppress_generated_aggregate_constructor_call(ctor) &&
		    !suppress_prelowered_constructor_body_demand(ctor) &&
		    !suppress_noop_generated_constructor_call(init))
			out.insert(ctor);
	}
	void collect_global_variable_constructor_demands(const Node& node,
	                                                set<const Binding*>& out,
	                                                bool in_function = false)
	{
		bool child_in_function =
			in_function || starts_with(node.line, "function-definition ");
		if (!in_function &&
		    starts_with(node.line, "variable ") &&
		    node.binding != NULL &&
		    !node.children.empty())
			collect_global_init_constructor_demands(node.binding->type,
			                                        node.children[0],
			                                        out);
		for (size_t i = 0; i < node.children.size(); ++i)
			collect_global_variable_constructor_demands(node.children[i],
			                                           out,
			                                           child_in_function);
	}
	void mark_object_root_bindings(const set<const Binding*>& bindings,
	                               bool hosted_compatibility,
	                               bool body_demand_roots = false)
	{
		for (set<const Binding*>::const_iterator it = bindings.begin();
		     it != bindings.end();
		     ++it)
		{
			Binding* binding = const_cast<Binding*>(*it);
			if (binding == NULL)
				continue;
			bool mark = body_demand_roots
				? should_mark_body_demand_object_root(
					  binding, hosted_compatibility)
				: should_mark_direct_call_object_root(
					  binding, hosted_compatibility);
			if (!mark)
				continue;
			binding->is_object_root = true;
			if (binding->aliased_binding != NULL)
				binding->aliased_binding->is_object_root = true;
		}
	}
	void note_function_definitions(ProgramLowerer& program, const Node& node)
	{
		if (starts_with(node.line, "function-definition ") &&
		    node.binding != NULL &&
		    !lowir_skip_function_definition_node(node))
		{
			program.function_definition_bindings.insert(node.binding);
			if (node.binding->is_inline_definition &&
			    !node.binding->is_explicit_defaulted_definition &&
			    !empty_defaulted_copy_move_constructor_needs_helper(node))
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

void clear_lowir_emit_root_caches()
{
	hosted_nested_helper_body_root_cache().clear();
}

}  // namespace internal
}  // namespace pa14
