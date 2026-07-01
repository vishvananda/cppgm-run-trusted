#include "pa14_lowir_hosted_inline_internal.h"
#include "pa12_templates_function_support.h"

namespace pa14 {
namespace internal {

bool hosted_tuple_record(TypePtr record)
{
	TypePtr bare = record.get() != NULL ? pa11::strip_cv(record) : TypePtr();
	return bare.get() != NULL &&
	       bare->kind == TypeKind::Record &&
	       record_in_namespace(bare, "std") &&
	       hosted_record_primary(bare) == "tuple";
}

bool hosted_single_type_template_argument(
	const vector<pa11::TemplateInstanceArgument>& args,
	TypePtr* type_out)
{
	if (args.size() != 1)
		return false;
	const pa11::TemplateInstanceArgument* arg = &args[0];
	if (arg->kind == pa11::TemplateInstanceArgumentKind::Pack)
	{
		if (arg->pack.size() != 1)
			return false;
		arg = &arg->pack[0];
	}
	if (arg->kind != pa11::TemplateInstanceArgumentKind::Type)
		return false;
	if (type_out != NULL)
		*type_out = arg->type;
	return true;
}

bool hosted_tuple_reference_constructor_binding(const Binding* binding,
                                                TypePtr* element_out)
{
	if (!is_class_constructor_binding(binding) ||
	    binding->type.get() == NULL ||
	    binding->type->kind != TypeKind::Function ||
	    binding->type->parameters.size() != 2 ||
	    !is_reference(binding->type->parameters[1]))
		return false;
	TypePtr record = hosted_member_owner_record(binding);
	record = record.get() != NULL ? pa11::strip_cv(record) : TypePtr();
	TypePtr element;
	if (!hosted_tuple_record(record) ||
	    !hosted_single_type_template_argument(record->template_arguments,
	                                         &element))
		return false;
	if (!is_reference(element) ||
	    !pa11::same_type(pa11::strip_cv(element),
	                     pa11::strip_cv(binding->type->parameters[1])))
		return false;
	if (element_out != NULL)
		*element_out = element;
	return true;
}

bool hosted_index_tuple_record(TypePtr record)
{
	TypePtr bare = record.get() != NULL ? pa11::strip_cv(record) : TypePtr();
	return bare.get() != NULL &&
	       bare->kind == TypeKind::Record &&
	       record_in_namespace(bare, "std") &&
	       hosted_record_primary(bare) == "_Index_tuple";
}

bool hosted_pair_piecewise_constructor_symbol(const Binding* binding)
{
	string symbol = global_object_symbol(binding);
	return starts_with(symbol, "_ZNSt4pair") &&
	       (symbol.find("EC1") != string::npos ||
	        symbol.find("EC2") != string::npos) &&
	       symbol.find("St5tuple") != string::npos &&
	       (symbol.find("St12_Index_tuple") != string::npos ||
	        symbol.find("St21piecewise_construct_t") != string::npos);
}

bool hosted_pair_piecewise_index_constructor_binding(const Binding* binding)
{
	if (binding == NULL ||
	    binding->type.get() == NULL ||
	    binding->type->kind != TypeKind::Function ||
	    (binding->type->parameters.size() != 4 &&
	     binding->type->parameters.size() != 5))
		return false;
	if (hosted_pair_piecewise_constructor_symbol(binding))
		return true;
	if (!is_class_constructor_binding(binding))
		return false;
	TypePtr record = hosted_member_owner_record(binding);
	if (!hosted_pair_record(record))
		return false;
	Binding* first = hosted_pair_field(record, "first", 0);
	Binding* second = hosted_pair_field(record, "second", 1);
	if ((first == NULL && hosted_pair_argument(record, 0).get() == NULL) ||
	    (second == NULL && hosted_pair_argument(record, 1).get() == NULL))
		return false;
	if (hosted_pair_piecewise_constructor_symbol(binding))
		return true;
	bool public_piecewise = binding->type->parameters.size() == 4;
	size_t tuple1_index = public_piecewise ? 2 : 1;
	size_t tuple2_index = binding->type->parameters.size() == 4 ? 3 : 2;
	TypePtr tuple1 = object_type(binding->type->parameters[tuple1_index]);
	TypePtr tuple2 = object_type(binding->type->parameters[tuple2_index]);
	tuple1 = tuple1.get() != NULL ? pa11::strip_cv(tuple1) : TypePtr();
	tuple2 = tuple2.get() != NULL ? pa11::strip_cv(tuple2) : TypePtr();
	if (binding->type->parameters.size() == 4)
		return hosted_tuple_record(tuple1) &&
		       hosted_tuple_record(tuple2) &&
		       tuple1->template_arguments.size() == 1 &&
		       tuple2->template_arguments.empty();
	TypePtr indexes1 = object_type(binding->type->parameters[3]);
	TypePtr indexes2 = object_type(binding->type->parameters[4]);
	indexes1 = indexes1.get() != NULL ? pa11::strip_cv(indexes1) : TypePtr();
	indexes2 = indexes2.get() != NULL ? pa11::strip_cv(indexes2) : TypePtr();
	return hosted_tuple_record(tuple1) &&
	       hosted_tuple_record(tuple2) &&
	       hosted_index_tuple_record(indexes1) &&
	       hosted_index_tuple_record(indexes2) &&
	       tuple1->template_arguments.size() == 1 &&
	       tuple2->template_arguments.empty();
}

bool hosted_pair_constructor_binding(const Binding* binding)
{
	if (!is_class_constructor_binding(binding) ||
	    binding->type.get() == NULL ||
	    binding->type->kind != TypeKind::Function ||
	    binding->type->parameters.size() != 3)
		return false;
	TypePtr record = class_record_for_member(binding);
	if (!hosted_pair_record(record))
		return false;
	Binding* first = hosted_pair_field(record, "first", 0);
	Binding* second = hosted_pair_field(record, "second", 1);
	if (first == NULL || second == NULL)
		return false;
	TypePtr first_arg = object_type(binding->type->parameters[1]);
	TypePtr second_arg = object_type(binding->type->parameters[2]);
	return pa11::same_type(pa11::strip_cv(first->type),
	                       pa11::strip_cv(first_arg)) &&
	       pa11::same_type(pa11::strip_cv(second->type),
	                       pa11::strip_cv(second_arg));
}

bool hosted_pair_default_constructor_binding(const Binding* binding)
{
	return is_class_constructor_binding(binding) &&
	       binding->type.get() != NULL &&
	       binding->type->kind == TypeKind::Function &&
	       binding->type->parameters.size() == 1 &&
	       hosted_pair_record(hosted_member_owner_record(binding));
}

bool hosted_pair_assignment_binding(const Binding* binding)
{
	if (binding == NULL ||
	    binding->name != "operator=" ||
	    binding->type.get() == NULL ||
	    binding->type->kind != TypeKind::Function ||
	    binding->type->parameters.size() != 2 ||
	    !is_reference(binding->type->parameters[1]))
		return false;
	TypePtr record = hosted_member_owner_record(binding);
	TypePtr source = pa11::strip_cv(binding->type->parameters[1]->base);
	return hosted_pair_record(record) &&
	       source.get() != NULL &&
	       source->kind == TypeKind::Record &&
	       pa11::same_type(pa11::strip_cv(record), source);
}

bool hosted_allocator_rebind_constructor_binding(const Binding* binding)
{
	if (!is_class_constructor_binding(binding) ||
	    binding->type.get() == NULL ||
	    binding->type->kind != TypeKind::Function ||
	    binding->type->parameters.size() != 2 ||
	    binding->type->parameters[1].get() == NULL ||
	    !is_reference(binding->type->parameters[1]))
		return false;
	TypePtr record = hosted_member_owner_record(binding);
	record = record.get() != NULL ? pa11::strip_cv(record) : TypePtr();
	TypePtr param = pa11::strip_cv(binding->type->parameters[1]->base);
	if (record.get() != NULL &&
	    param.get() != NULL &&
	    record->kind == TypeKind::Record &&
	    param->kind == TypeKind::Record &&
	    record_in_namespace(record, "std") &&
	    record_in_namespace(param, "std"))
	{
		string primary = hosted_record_primary(record);
		string param_primary = hosted_record_primary(param);
		if ((primary == "allocator" && param_primary == "allocator") ||
		    (primary == "__new_allocator" &&
		     param_primary == "__new_allocator"))
			return true;
	}
	string symbol = global_object_symbol(binding);
	return (starts_with(symbol, "_ZNSaI") &&
	        (symbol.find("EC1ERKSaI") != string::npos ||
	         symbol.find("EC2ERKSaI") != string::npos)) ||
	       (starts_with(symbol, "_ZNSt15__new_allocatorI") &&
	        (symbol.find("EC1ERKS0_") != string::npos ||
	         symbol.find("EC2ERKS0_") != string::npos ||
	         symbol.find("EC1ERKS_") != string::npos ||
	         symbol.find("EC2ERKS_") != string::npos));
}

Binding* hosted_pair_field(TypePtr record, const string& name, size_t fallback)
{
	TypePtr bare = record.get() != NULL ? pa11::strip_cv(record) : TypePtr();
	if (bare.get() == NULL || bare->kind != TypeKind::Record)
		return NULL;
	pa11::layout_record_type(bare);
	for (size_t i = 0; i < bare->fields.size(); ++i)
		if (bare->fields[i] != NULL &&
		    bare->fields[i]->name == name)
			return bare->fields[i];
	return fallback < bare->fields.size() ? bare->fields[fallback] : NULL;
}

bool hosted_alloc_traits_propagate_on_move_assign_binding(
	const Binding* binding)
{
	if (binding == NULL ||
	    (binding->name != pa11::abi_private_name("S_propagate_on_move_assign") &&
	     binding->name != pa11::abi_private_name("S_always_equal")) ||
	    binding->type.get() == NULL ||
	    binding->type->kind != TypeKind::Function ||
	    !binding->type->parameters.empty() ||
	     !pa11::same_type(pa11::strip_cv(binding->type->base),
	                      pa11::make_fundamental(FT_BOOL)))
		return false;
	TypePtr record = hosted_member_owner_record(binding);
	return record.get() != NULL &&
	       hosted_record_primary(record) == "__alloc_traits" &&
	       record_in_namespace(record, "__gnu_cxx");
}

bool hosted_allocator_destroy_binding(const Binding* binding,
                                      TypePtr* object_out,
                                      size_t* pointer_index_out)
{
	if (binding == NULL ||
	    binding->name != "destroy" ||
	    binding->type.get() == NULL ||
	    binding->type->kind != TypeKind::Function ||
	    !pa11::is_void_type(binding->type->base))
		return false;
	TypePtr record = hosted_member_owner_record(binding);
	record = record.get() != NULL ? pa11::strip_cv(record) : TypePtr();
	string primary = hosted_record_primary(record);
	if (record.get() == NULL ||
	    !record_in_namespace(record, "std") ||
	    (primary != "__new_allocator" &&
	     primary != "allocator_traits"))
	{
		string symbol = global_object_symbol(binding);
		if ((symbol.find("St15__new_allocator") == string::npos &&
		     symbol.find("St16allocator_traits") == string::npos) ||
		    symbol.find("7destroy") == string::npos)
			return false;
	}
	for (size_t i = binding->type->parameters.size(); i > 0; --i)
	{
		size_t index = i - 1;
		TypePtr param = pa11::strip_cv(
			object_type(binding->type->parameters[index]));
		if (param.get() == NULL || param->kind != TypeKind::Pointer)
			continue;
		TypePtr object = pa11::strip_cv(param->base);
		if (object.get() == NULL)
			return false;
		if (object_out != NULL)
			*object_out = object;
		if (pointer_index_out != NULL)
			*pointer_index_out = index;
		return true;
	}
	return false;
}

bool hosted_rbtree_assignment_binding(const Binding* binding)
{
	if (binding == NULL ||
	    binding->name != "operator=" ||
	    binding->type.get() == NULL ||
	    binding->type->kind != TypeKind::Function ||
	    binding->type->parameters.size() != 2)
		return false;
	TypePtr record = hosted_member_owner_record(binding);
	record = record.get() != NULL ? pa11::strip_cv(record) : TypePtr();
	if (record.get() == NULL ||
	    record->kind != TypeKind::Record ||
	    hosted_record_primary(record) != pa11::abi_private_name("Rb_tree") ||
	    !record_in_namespace(record, "std"))
		return false;
	TypePtr source = binding->type->parameters[1];
	if (source.get() == NULL || !is_reference(source))
		return false;
	source = pa11::strip_cv(source->base);
	return source.get() != NULL &&
	       source->kind == TypeKind::Record &&
	       pa11::same_type(record, source);
}

bool hosted_rbtree_copy_constructor_binding(const Binding* binding)
{
	if (!is_class_constructor_binding(binding) ||
	    binding->type.get() == NULL ||
	    binding->type->kind != TypeKind::Function ||
	    binding->type->parameters.size() != 2 ||
	    !is_reference(binding->type->parameters[1]))
		return false;
	TypePtr record = hosted_member_owner_record(binding);
	record = record.get() != NULL ? pa11::strip_cv(record) : TypePtr();
	if (record.get() == NULL ||
	    record->kind != TypeKind::Record ||
	    hosted_record_primary(record) != pa11::abi_private_name("Rb_tree") ||
	    !record_in_namespace(record, "std"))
		return false;
	TypePtr source = pa11::strip_cv(binding->type->parameters[1]->base);
	return source.get() != NULL &&
	       source->kind == TypeKind::Record &&
	       pa11::same_type(record, source);
}

bool hosted_rbtree_const_iterator_node_constructor_binding(
	const Binding* binding)
{
	if (!is_class_constructor_binding(binding) ||
	    binding->type.get() == NULL ||
	    binding->type->kind != TypeKind::Function ||
	    binding->type->parameters.size() != 2)
		return false;
	TypePtr record = hosted_member_owner_record(binding);
	record = record.get() != NULL ? pa11::strip_cv(record) : TypePtr();
	if (record.get() == NULL ||
	    record->kind != TypeKind::Record ||
	    hosted_record_primary(record) !=
		    pa11::abi_private_name("Rb_tree_const_iterator") ||
	    !record_in_namespace(record, "std"))
		return false;
	TypePtr node_ptr = pa11::strip_cv(binding->type->parameters[1]);
	if (node_ptr.get() == NULL || node_ptr->kind != TypeKind::Pointer)
		return false;
	TypePtr node = pa11::strip_cv(node_ptr->base);
	return node.get() != NULL &&
	       node->kind == TypeKind::Record &&
	       hosted_record_primary(node) ==
		       pa11::abi_private_name("Rb_tree_node_base") &&
	       record_in_namespace(node, "std");
}

bool hosted_tree_container_default_record(TypePtr record)
{
	TypePtr bare = record.get() != NULL ? pa11::strip_cv(record) : TypePtr();
	if (bare.get() == NULL ||
	    bare->kind != TypeKind::Record ||
	    !record_in_namespace(bare, "std"))
		return false;
	string primary = hosted_record_primary(bare);
	return primary == "set" ||
	       primary == "multiset" ||
	       primary == "map" ||
	       primary == "multimap" ||
	       primary == pa11::abi_private_name("Rb_tree") ||
	       primary == pa11::abi_private_name("Rb_tree_impl") ||
	       primary == pa11::abi_private_name("Rb_tree_header");
}

bool hosted_temporary_buffer_constructor_binding(const Binding* binding)
{
	return is_class_constructor_binding(binding) &&
	       binding->type.get() != NULL &&
	       binding->type->kind == TypeKind::Function &&
	       binding->type->parameters.size() == 3 &&
	       hosted_record_primary(hosted_member_owner_record(binding)) ==
		       pa11::abi_private_name("Temporary_buffer") &&
	       record_in_namespace(hosted_member_owner_record(binding), "std");
}

bool hosted_sp_counted_base_record(TypePtr record)
{
	TypePtr bare = record.get() != NULL ? pa11::strip_cv(record) : TypePtr();
	return bare.get() != NULL &&
	       bare->kind == TypeKind::Record &&
	       record_in_namespace(bare, "std") &&
	       hosted_record_primary(bare) == "_Sp_counted_base";
}

bool hosted_sp_counted_ptr_record(TypePtr record)
{
	TypePtr bare = record.get() != NULL ? pa11::strip_cv(record) : TypePtr();
	return bare.get() != NULL &&
	       bare->kind == TypeKind::Record &&
	       record_in_namespace(bare, "std") &&
	       (hosted_record_primary(bare) == "_Sp_counted_ptr" ||
	        hosted_record_primary(bare) == "_Sp_counted_ptr_inplace");
}

bool hosted_sp_counted_base_constructor_binding(const Binding* binding)
{
	return is_class_constructor_binding(binding) &&
	       binding->type.get() != NULL &&
	       binding->type->kind == TypeKind::Function &&
	       binding->type->parameters.size() == 1 &&
	       hosted_sp_counted_base_record(hosted_member_owner_record(binding));
}

bool hosted_sp_counted_base_destructor_binding(const Binding* binding)
{
	return is_class_destructor_binding(binding) &&
	       binding->type.get() != NULL &&
	       binding->type->kind == TypeKind::Function &&
	       binding->type->parameters.size() == 1 &&
	       hosted_sp_counted_base_record(hosted_member_owner_record(binding));
}

bool hosted_sp_counted_base_add_ref_binding(const Binding* binding)
{
	return binding != NULL &&
	       binding->name == pa11::abi_private_name("M_add_ref_copy") &&
	       binding->type.get() != NULL &&
	       binding->type->kind == TypeKind::Function &&
	       binding->type->parameters.size() == 1 &&
	       hosted_sp_counted_base_record(hosted_member_owner_record(binding));
}

bool hosted_sp_counted_base_release_binding(const Binding* binding)
{
	return binding != NULL &&
	       (binding->name == pa11::abi_private_name("M_release") ||
	        binding->name == pa11::abi_private_name("M_release_last_use_cold") ||
	        binding->name == pa11::abi_private_name("M_release_last_use")) &&
	       binding->type.get() != NULL &&
	       binding->type->kind == TypeKind::Function &&
	       binding->type->parameters.size() == 1 &&
	       pa11::is_void_type(binding->type->base) &&
	       hosted_sp_counted_base_record(hosted_member_owner_record(binding));
}

bool hosted_sp_counted_base_destroy_binding(const Binding* binding)
{
	return binding != NULL &&
	       binding->name == pa11::abi_private_name("M_destroy") &&
	       binding->type.get() != NULL &&
	       binding->type->kind == TypeKind::Function &&
	       binding->type->parameters.size() == 1 &&
	       pa11::is_void_type(binding->type->base) &&
	       hosted_sp_counted_base_record(hosted_member_owner_record(binding));
}

bool hosted_sp_counted_ptr_virtual_binding(const Binding* binding)
{
	if (binding == NULL ||
	    binding->type.get() == NULL ||
	    binding->type->kind != TypeKind::Function ||
	    !hosted_sp_counted_ptr_record(hosted_member_owner_record(binding)))
		return false;
	if ((binding->name == pa11::abi_private_name("M_dispose") ||
	     binding->name == pa11::abi_private_name("M_destroy")) &&
	    binding->type->parameters.size() == 1)
		return true;
	return binding->name == pa11::abi_private_name("M_get_deleter") &&
	       binding->type->parameters.size() == 2;
}

bool hosted_sp_counted_ptr_destructor_binding(const Binding* binding)
{
	return is_class_destructor_binding(binding) &&
	       binding->type.get() != NULL &&
	       binding->type->kind == TypeKind::Function &&
	       binding->type->parameters.size() == 1 &&
	       hosted_sp_counted_ptr_record(hosted_member_owner_record(binding));
}

bool hosted_sp_counted_control_binding(const Binding* binding)
{
	return hosted_sp_counted_base_constructor_binding(binding) ||
	       hosted_sp_counted_base_destructor_binding(binding) ||
	       hosted_sp_counted_ptr_destructor_binding(binding) ||
	       hosted_sp_counted_base_add_ref_binding(binding) ||
	       hosted_sp_counted_base_release_binding(binding) ||
	       hosted_sp_counted_base_destroy_binding(binding) ||
	       hosted_sp_counted_ptr_virtual_binding(binding);
}

Binding* hosted_sp_counted_base_member_function(TypePtr record,
                                                const string& name)
{
	TypePtr bare = record.get() != NULL ? pa11::strip_cv(record) : TypePtr();
	if (!hosted_sp_counted_base_record(bare) || bare->scope == NULL)
		return NULL;
	map<string, vector<Binding*> >::const_iterator found =
		bare->scope->members.find(name);
	if (found == bare->scope->members.end())
		return NULL;
	for (size_t i = 0; i < found->second.size(); ++i)
	{
		Binding* candidate = found->second[i];
		if (candidate != NULL &&
		    candidate->kind == BindingKind::Function &&
		    candidate->type.get() != NULL &&
		    candidate->type->kind == TypeKind::Function &&
		    candidate->type->parameters.size() == 1)
			return candidate;
	}
	return NULL;
}

bool hosted_record_has_parent_primary(TypePtr record, const string& primary)
{
	TypePtr bare = record.get() != NULL ? pa11::strip_cv(record) : TypePtr();
	Scope* parent = bare.get() != NULL && bare->scope != NULL
		? bare->scope->parent : NULL;
	for (Scope* scope = parent; scope != NULL; scope = scope->parent)
	{
		if (scope->kind != ScopeKind::Class)
			continue;
		TypePtr owner = pa11::record_type_for_scope(scope);
		if (hosted_record_primary(owner) == primary)
			return true;
	}
	return false;
}

bool hosted_vector_guard_elts_record(TypePtr record, TypePtr* element_out)
{
	TypePtr bare = record.get() != NULL ? pa11::strip_cv(record) : TypePtr();
	if (bare.get() == NULL ||
	    bare->kind != TypeKind::Record ||
	    bare->scope == NULL ||
	    bare->scope->name.find("Guard_elts__local_type") ==
		    string::npos)
		return false;
	pa11::layout_record_type(bare);
	if (bare->fields.size() < 2)
		return false;
	TypePtr first = pa11::strip_cv(bare->fields[0]->type);
	TypePtr last = pa11::strip_cv(bare->fields[1]->type);
	if (first.get() == NULL ||
	    last.get() == NULL ||
	    first->kind != TypeKind::Pointer ||
	    last->kind != TypeKind::Pointer ||
	    !pa11::same_type(first, last))
		return false;
	if (element_out != NULL)
		*element_out = pa11::strip_cv(first->base);
	return first->base.get() != NULL;
}

bool hosted_vector_guard_elts_destructor_binding(const Binding* binding)
{
	if (!is_class_destructor_binding(binding) ||
	    binding->type.get() == NULL ||
	    binding->type->kind != TypeKind::Function ||
	    binding->type->parameters.size() != 1)
		return false;
	string object = global_object_symbol(binding);
	if (object.compare(0, string("_ZNSt6vector").size(),
	                   "_ZNSt6vector") == 0 &&
	    object.find("Guard_elts__local_type") != string::npos &&
	    (object.find("D1Ev") != string::npos ||
	     object.find("D2Ev") != string::npos))
		return true;
	return hosted_vector_guard_elts_record(class_record_for_member(binding),
	                                       NULL);
}

bool hosted_hashtable_local_guard_destructor_binding(const Binding* binding)
{
	if (!is_class_destructor_binding(binding) ||
	    binding->type.get() == NULL ||
	    binding->type->kind != TypeKind::Function ||
	    binding->type->parameters.size() != 1)
		return false;
	string object = global_object_symbol(binding);
	string hashtable_prefix = "_ZNSt10_Hashtable";
	if (object.compare(0, hashtable_prefix.size(),
	                   hashtable_prefix) == 0 &&
	    object.find("Guard__local_type") != string::npos &&
	    (object.find("D1Ev") != string::npos ||
	     object.find("D2Ev") != string::npos))
		return true;
	TypePtr record = class_record_for_member(binding);
	record = record.get() != NULL ? pa11::strip_cv(record) : TypePtr();
	if (record.get() == NULL ||
	    record->kind != TypeKind::Record ||
	    record->scope == NULL ||
	    (record->scope->name.find("_Guard__local_type") == string::npos &&
	     record->scope->name.find("Guard__local_type") == string::npos) ||
	    !record_in_namespace(record, "std"))
		return false;
	return hosted_record_has_parent_primary(
		record, pa11::abi_private_name("Hashtable"));
}

bool hosted_hashtable_ebo_helper_record(TypePtr record)
{
	TypePtr bare = record.get() != NULL ? pa11::strip_cv(record) : TypePtr();
	return bare.get() != NULL &&
	       bare->kind == TypeKind::Record &&
	       record_in_namespace(bare, "std") &&
	       hosted_record_primary(bare) ==
		       pa11::abi_private_name("Hashtable_ebo_helper");
}

bool hosted_same_record_reference(TypePtr type, TypePtr record)
{
	TypePtr object = type.get() != NULL ? type : TypePtr();
	if (object.get() != NULL && is_reference(object))
		object = object->base;
	object = object.get() != NULL ? pa11::strip_cv(object) : TypePtr();
	TypePtr bare = record.get() != NULL ? pa11::strip_cv(record) : TypePtr();
	return object.get() != NULL &&
	       bare.get() != NULL &&
	       pa11::same_type(object, bare);
}

bool hosted_hashtable_ebo_helper_copy_constructor_binding(
	const Binding* binding)
{
	if (!is_class_constructor_binding(binding) ||
	    binding->type.get() == NULL ||
	    binding->type->kind != TypeKind::Function ||
	    binding->type->parameters.size() != 2)
		return false;
	TypePtr record = class_record_for_member(binding);
	return hosted_hashtable_ebo_helper_record(record) &&
	       hosted_same_record_reference(binding->type->parameters[1], record);
}

bool hosted_hashtable_allocator_move_constructor_binding(
	const Binding* binding)
{
	if (!is_class_constructor_binding(binding) ||
	    binding->type.get() == NULL ||
	    binding->type->kind != TypeKind::Function ||
	    binding->type->parameters.size() < 4)
		return false;
	string object = global_object_symbol(binding);
	string hashtable_prefix = "_ZNSt10_Hashtable";
	if (object.compare(0, hashtable_prefix.size(),
	                   hashtable_prefix) == 0 &&
	    object.find("C1EO") != string::npos &&
	    object.find("OSa") != string::npos &&
	    object.find("St17integral_constant") != string::npos)
		return true;
	TypePtr record = class_record_for_member(binding);
	return hosted_record_primary(record) ==
		       pa11::abi_private_name("Hashtable") &&
	       hosted_same_record_reference(binding->type->parameters[1],
	                                    record);
}

bool hosted_shared_count_member_symbol(const Binding* binding)
{
	string object = global_object_symbol(binding);
	string record_name = string("__") + "shared_count";
	return object.find(record_name) != string::npos;
}

bool hosted_shared_count_copy_constructor_binding(const Binding* binding)
{
	if (!is_class_constructor_binding(binding) ||
	    binding->type.get() == NULL ||
	    binding->type->kind != TypeKind::Function ||
	    binding->type->parameters.size() != 2)
		return false;
	TypePtr record = class_record_for_member(binding);
	return hosted_shared_count_member_symbol(binding) &&
	       hosted_same_record_reference(binding->type->parameters[1], record);
}

bool hosted_shared_count_assignment_binding(const Binding* binding)
{
	if (binding == NULL ||
	    binding->name != "operator=" ||
	    binding->type.get() == NULL ||
	    binding->type->kind != TypeKind::Function ||
	    binding->type->parameters.size() != 2)
		return false;
	TypePtr record = class_record_for_member(binding);
	return hosted_shared_count_member_symbol(binding) &&
	       hosted_same_record_reference(binding->type->parameters[1], record);
}

bool hosted_shared_ptr_assignment_binding(const Binding* binding)
{
	if (binding == NULL ||
	    binding->name != "operator=" ||
	    binding->type.get() == NULL ||
	    binding->type->kind != TypeKind::Function ||
	    binding->type->parameters.size() != 2 ||
	    !is_reference(binding->type->parameters[1]))
		return false;
	TypePtr record = hosted_member_owner_record(binding);
	TypePtr source = pa11::strip_cv(binding->type->parameters[1]->base);
	return hosted_shared_ptr_record(record) &&
	       hosted_shared_ptr_record(source) &&
	       pa11::type_size(pa11::strip_cv(record)) ==
		       pa11::type_size(source);
}

Binding* hosted_shared_ptr_count_field(TypePtr record)
{
	TypePtr bare = record.get() != NULL ? pa11::strip_cv(record) : TypePtr();
	if (!hosted_shared_ptr_record(bare))
		return NULL;
	pa11::layout_record_type(bare);
	for (size_t i = 0; i < bare->fields.size(); ++i)
		if (bare->fields[i]->member_offset == 8)
			return bare->fields[i];
	vector<TypePtr> bases = pa11::record_direct_bases(bare);
	for (size_t i = 0; i < bases.size(); ++i)
	{
		Binding* field = hosted_shared_ptr_count_field(bases[i]);
		if (field != NULL)
			return field;
	}
	return NULL;
}

TypePtr hosted_shared_count_control_record_from_type(TypePtr count)
{
	TypePtr record = count.get() != NULL ? pa11::strip_cv(count) : TypePtr();
	if (record.get() == NULL || record->kind != TypeKind::Record)
		return TypePtr();
	pa11::layout_record_type(record);
	Binding* field = NULL;
	for (size_t i = 0; i < record->fields.size(); ++i)
		if (record->fields[i]->name == pa11::abi_private_name("M_pi"))
			field = record->fields[i];
	if (field == NULL && !record->fields.empty())
		field = record->fields[0];
	TypePtr pointer = field != NULL ? pa11::strip_cv(field->type) : TypePtr();
	if (pointer.get() == NULL || pointer->kind != TypeKind::Pointer)
		return TypePtr();
	return pa11::strip_cv(pointer->base);
}

Binding* hosted_shared_control_function_from_record(TypePtr control,
                                                    const string& name)
{
	TypePtr record = control.get() != NULL ? pa11::strip_cv(control) : TypePtr();
	if (record.get() == NULL || record->scope == NULL)
		return NULL;
	map<string, vector<Binding*> >::const_iterator found =
		record->scope->members.find(name);
	if (found == record->scope->members.end())
		return NULL;
	for (size_t i = 0; i < found->second.size(); ++i)
	{
		Binding* candidate = found->second[i];
		if (candidate != NULL &&
		    candidate->kind == BindingKind::Function &&
		    candidate->type.get() != NULL &&
		    candidate->type->kind == TypeKind::Function &&
		    candidate->type->parameters.size() == 1)
			return candidate;
	}
	return NULL;
}

TypePtr hosted_shared_count_control_record(const Binding* binding)
{
	TypePtr record = class_record_for_member(binding);
	record = record.get() != NULL ? pa11::strip_cv(record) : TypePtr();
	if (record.get() == NULL || record->kind != TypeKind::Record)
		return TypePtr();
	pa11::layout_record_type(record);
	Binding* field = NULL;
	for (size_t i = 0; i < record->fields.size(); ++i)
		if (record->fields[i]->name == pa11::abi_private_name("M_pi"))
			field = record->fields[i];
	if (field == NULL && !record->fields.empty())
		field = record->fields[0];
	TypePtr pointer = field != NULL ? pa11::strip_cv(field->type) : TypePtr();
	if (pointer.get() == NULL || pointer->kind != TypeKind::Pointer)
		return TypePtr();
	return pa11::strip_cv(pointer->base);
}

Binding* hosted_shared_count_control_function(const Binding* binding,
                                              const string& name)
{
	TypePtr control = hosted_shared_count_control_record(binding);
	if (control.get() == NULL || control->scope == NULL)
		return NULL;
	map<string, vector<Binding*> >::const_iterator found =
		control->scope->members.find(name);
	if (found == control->scope->members.end())
		return NULL;
	for (size_t i = 0; i < found->second.size(); ++i)
	{
		Binding* candidate = found->second[i];
		if (candidate != NULL &&
		    candidate->kind == BindingKind::Function &&
		    candidate->type.get() != NULL &&
		    candidate->type->kind == TypeKind::Function &&
		    candidate->type->parameters.size() == 1)
			return candidate;
	}
	return NULL;
}

bool hosted_exception_ptr_record(TypePtr record)
{
	TypePtr bare = record.get() != NULL ? pa11::strip_cv(record) : TypePtr();
	return bare.get() != NULL &&
	       bare->kind == TypeKind::Record &&
	       bare->scope != NULL &&
	       bare->scope->name == "exception_ptr" &&
	       record_in_namespace(bare, "std");
}

bool hosted_make_exception_ptr_binding(const Binding* binding)
{
	if (binding == NULL ||
	    binding->type.get() == NULL ||
	    binding->type->kind != TypeKind::Function ||
	    binding->type->parameters.size() != 1 ||
	    !hosted_exception_ptr_record(binding->type->base))
		return false;
	string object = global_object_symbol(binding);
	bool named_function =
		binding->name == "make_exception_ptr" &&
		binding_in_namespace(binding, "std");
	bool abi_function =
		object.compare(0, 24, "_ZSt18make_exception_ptr") == 0;
	return named_function || abi_function;
}

TypePtr stoa_conversion_function_type(const Binding* binding)
{
	if (binding == NULL ||
	    binding->type.get() == NULL ||
	    binding->type->kind != TypeKind::Function ||
	    binding->type->parameters.size() < 4)
		return TypePtr();
	TypePtr conv = pa11::strip_cv(binding->type->parameters[0]);
	if (conv.get() == NULL || conv->kind != TypeKind::Pointer)
		return TypePtr();
	TypePtr fn = pa11::strip_cv(conv->base);
	if (fn.get() == NULL || fn->kind != TypeKind::Function)
		return TypePtr();
	return fn;
}

bool hosted_stoa_binding(const Binding* binding)
{
	TypePtr conv_fn = stoa_conversion_function_type(binding);
	if (conv_fn.get() == NULL ||
	    !pa11::is_integral_or_bool_type(conv_fn->base) ||
	    !pa11::is_integral_or_bool_type(binding->type->base))
		return false;
	string object = global_object_symbol(binding);
	bool named_function =
		binding->name == "__stoa" &&
		binding_in_namespace(binding, "__gnu_cxx");
	bool abi_function =
		object.compare(0, 18, "_ZN9__gnu_cxx6__stoa") == 0;
	return named_function || abi_function;
}

Binding* hosted_exception_ptr_void_constructor(TypePtr record)
{
	TypePtr bare = record.get() != NULL ? pa11::strip_cv(record) : TypePtr();
	if (!hosted_exception_ptr_record(bare) || bare->scope == NULL)
		return NULL;
	map<string, vector<Binding*> >::const_iterator found =
		bare->scope->members.find(bare->scope->name);
	if (found == bare->scope->members.end())
		return NULL;
	for (size_t i = 0; i < found->second.size(); ++i)
	{
		Binding* candidate = found->second[i];
		if (candidate != NULL &&
		    is_class_constructor_binding(candidate) &&
		    candidate->type.get() != NULL &&
		    candidate->type->kind == TypeKind::Function &&
		    candidate->type->parameters.size() == 2 &&
		    pointer_object_type(candidate->type->parameters[1]))
			return candidate;
	}
	return NULL;
}

void ensure_make_exception_ptr_runtime_declarations(ProgramLowerer& program)
{
	if (program.declared_functions.insert(
		    "__external_runtime____cxa_init_primary_exception").second)
		program.declares.push_back(
			"declare function @__external_runtime____cxa_init_primary_exception"
			"(%arg0 : ptr, %arg1 : ptr, %arg2 : ptr) -> ptr "
			"[linkage=c, binding=strong, object=__cxa_init_primary_exception]");
}

void ensure_stoa_runtime_declarations(ProgramLowerer& program)
{
	if (program.declared_functions.insert(
		    "__external_runtime___errno_location").second)
		program.declares.push_back(
			"declare function @__external_runtime___errno_location() "
			"-> ptr [effects=readonly, unwind=no, linkage=c, "
			"binding=strong, object=__errno_location]");
	if (program.declared_functions.insert(
		    "__external_std___throw_invalid_argument").second)
		program.declares.push_back(
			"declare function @__external_std___throw_invalid_argument"
			"(%arg0 : ptr) -> void [return=noreturn, unwind=may, "
			"binding=strong, object=_ZSt24__throw_invalid_argumentPKc]");
	if (program.declared_functions.insert(
		    "__external_std___throw_out_of_range").second)
		program.declares.push_back(
			"declare function @__external_std___throw_out_of_range"
			"(%arg0 : ptr) -> void [return=noreturn, unwind=may, "
			"binding=strong, object=_ZSt20__throw_out_of_rangePKc]");
}

void ensure_hosted_operator_delete_declaration(ProgramLowerer& program)
{
	if (program.declared_functions.insert("operator_delete").second)
		program.declares.push_back(
			"declare function @operator_delete(%arg0 : ptr) -> void "
			"[unwind=no, binding=strong, object=" +
			string(program.native_lowering
			       ? "_ZdlPv" : "cppgm_builtin_operator_delete") + "]");
}

void ensure_hosted_operator_new_declaration(ProgramLowerer& program)
{
	if (program.declared_functions.insert("operator_new").second)
		program.declares.push_back(
			"declare function @operator_new(%arg0 : i64) -> ptr "
			"[binding=strong, object=" +
			string(program.native_lowering
			       ? "_Znwm" : "cppgm_builtin_operator_new") + "]");
}

void ensure_hosted_rbtree_runtime_declarations(ProgramLowerer& program)
{
	if (program.declared_functions.insert(
		    "std___Rb_tree_insert_and_rebalance").second)
		program.declares.push_back(
			"declare function @std___Rb_tree_insert_and_rebalance"
			"(%arg0 : u8, %arg1 : ptr, %arg2 : ptr, "
			"%arg3 : ptr [pass=reference]) -> void "
			"[unwind=no, binding=strong, "
			"object=_ZSt29_Rb_tree_insert_and_rebalancebPSt18_Rb_tree_node_baseS0_RS_]");
	if (program.declared_functions.insert(
		    "std___Rb_tree_increment").second)
		program.declares.push_back(
			"declare function @std___Rb_tree_increment"
			"(%arg0 : ptr) -> ptr [unwind=no, binding=strong, "
			"object=_ZSt18_Rb_tree_incrementPSt18_Rb_tree_node_base]");
}

Binding* hosted_basic_string_release_function(TypePtr string_record)
{
	TypePtr bare = string_record.get() != NULL
		? pa11::strip_cv(string_record) : TypePtr();
	if (!hosted_basic_string_record(bare) || bare->scope == NULL)
		return NULL;
	Binding* match = NULL;
	for (size_t i = 0; i < bare->scope->binding_order.size(); ++i)
	{
		Binding* candidate = bare->scope->binding_order[i];
		if (candidate != NULL &&
		    candidate->kind == BindingKind::Function &&
		    candidate->is_private &&
		    !candidate->is_static_member &&
		    candidate->type.get() != NULL &&
		    candidate->type->kind == TypeKind::Function &&
		    candidate->type->parameters.size() == 1 &&
		    pa11::is_void_type(candidate->type->base))
		{
			if (match != NULL)
				return NULL;
			match = candidate;
		}
	}
	return match;
}

Node make_hosted_parameter_node(const Binding* binding,
                                size_t index,
                                const string& fallback)
{
	string name = fallback;
	if (index < binding->function_parameter_names.size() &&
	    !binding->function_parameter_names[index].empty())
		name = binding->function_parameter_names[index];
	Node param("parameter " + name);
	param.type = binding->type->parameters[index];
	return param;
}

Node make_empty_hosted_function_node(const Binding* binding,
                                     const vector<string>& names)
{
	Node fn("function-definition");
	fn.binding = const_cast<Binding*>(binding);
	fn.type = binding->type;
	for (size_t i = 0; i < binding->type->parameters.size(); ++i)
	{
		string name = i < names.size()
			? names[i] : "__param" + to_string(i);
		fn.children.push_back(
			make_hosted_parameter_node(binding, i, name));
	}
	fn.children.push_back(Node("compound-statement"));
	return fn;
}

string parameter_name(const FunctionOut& out, size_t index,
                      const string& fallback)
{
	return index < out.parameter_names.size()
		? out.parameter_names[index] : fallback;
}

}  // namespace internal
}  // namespace pa14
