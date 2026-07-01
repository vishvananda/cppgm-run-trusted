#include "pa14_lowir_hosted_inline_internal.h"
#include "pa12_templates_function_support.h"

namespace pa14 {
namespace internal {

bool binding_in_namespace(const Binding* binding, const string& name)
{
	for (const Scope* scope = binding != NULL ? binding->owner : NULL;
	     scope != NULL;
	     scope = scope->parent)
		if (scope->kind == ScopeKind::Namespace && scope->name == name)
			return true;
	return false;
}

bool record_in_namespace(TypePtr record, const string& name)
{
	TypePtr bare = record.get() != NULL ? pa11::strip_cv(record) : TypePtr();
	for (const Scope* scope = bare.get() != NULL ? bare->scope : NULL;
	     scope != NULL;
	     scope = scope->parent)
		if (scope->kind == ScopeKind::Namespace && scope->name == name)
			return true;
	return false;
}

bool pointer_object_type(TypePtr type)
{
	TypePtr bare = type.get() != NULL ? pa11::strip_cv(type) : TypePtr();
	return bare.get() != NULL && bare->kind == TypeKind::Pointer;
}

string hosted_record_primary(TypePtr record)
{
	TypePtr bare = record.get() != NULL ? pa11::strip_cv(record) : TypePtr();
	if (bare.get() == NULL)
		return "";
	string primary = bare->template_primary_name.empty()
		? bare->name : bare->template_primary_name;
	size_t args = primary.find('<');
	if (args != string::npos)
		primary = primary.substr(0, args);
	size_t pos = primary.rfind("::");
	if (pos != string::npos)
		primary = primary.substr(pos + 2);
	return primary;
}

bool hosted_vector_bool_record_for_inline(TypePtr record)
{
	TypePtr bare = record.get() != NULL ? pa11::strip_cv(record) : TypePtr();
	if (bare.get() == NULL ||
	    bare->kind != TypeKind::Record ||
	    !bare->is_template_specialization ||
	    hosted_record_primary(bare) != "vector" ||
	    bare->template_arguments.empty() ||
	    bare->template_arguments[0].kind !=
		    pa11::TemplateInstanceArgumentKind::Type ||
	    !record_in_namespace(bare, "std"))
		return false;
	TypePtr element = pa11::strip_cv(bare->template_arguments[0].type);
	return element.get() != NULL &&
	       element->kind == TypeKind::Fundamental &&
	       element->fundamental == FT_BOOL;
}

bool hosted_vector_bool_s_nword_binding(const Binding* binding)
{
	return binding != NULL &&
	       binding->name == pa11::abi_private_name("S_nword") &&
	       binding->type.get() != NULL &&
	       binding->type->kind == TypeKind::Function &&
	       binding->type->parameters.size() == 1 &&
	       pa11::is_integral_or_bool_type(binding->type->base) &&
	       pa11::is_integral_or_bool_type(binding->type->parameters[0]) &&
	       hosted_vector_bool_record_for_inline(
		       class_record_for_member(binding));
}

bool hosted_to_address_binding(const Binding* binding)
{
	if (binding == NULL ||
	    binding->type.get() == NULL ||
	    binding->type->kind != TypeKind::Function ||
	    binding->type->parameters.size() != 1 ||
	    scalar_lowir_type(binding->type->base) != "ptr")
		return false;
	string object_symbol = global_object_symbol(binding);
	bool named_to_address =
		binding->name == "__to_address" &&
		binding_in_namespace(binding, "std");
	bool abi_to_address =
		object_symbol.compare(0, 16, "_ZSt12__to_address") == 0;
	bool named_niter_base =
		binding->name == "__niter_base" &&
		binding_in_namespace(binding, "std");
	bool abi_niter_base =
		object_symbol.compare(0, 16, "_ZSt12__niter_base") == 0;
	if (!named_to_address && !abi_to_address &&
	    !named_niter_base && !abi_niter_base)
		return false;
	TypePtr param = binding->type->parameters[0];
	TypePtr object = is_reference(param) ? param->base : param;
	return abi_to_address || abi_niter_base || pointer_object_type(object);
}

bool std_type_info_record(TypePtr record)
{
	TypePtr bare = record.get() != NULL ? pa11::strip_cv(record) : TypePtr();
	return bare.get() != NULL &&
	       bare->kind == TypeKind::Record &&
	       bare->scope != NULL &&
	       bare->scope->name == "type_info" &&
	       record_in_namespace(bare, "std");
}

bool type_info_reference(TypePtr type)
{
	TypePtr bare = type.get() != NULL ? pa11::strip_cv(type) : TypePtr();
	return bare.get() != NULL &&
	       bare->kind == TypeKind::LValueReference &&
	       std_type_info_record(bare->base);
}

bool hosted_type_info_comparison_binding(const Binding* binding)
{
	if (binding == NULL ||
	    binding->type.get() == NULL ||
	    binding->type->kind != TypeKind::Function ||
	    binding->type->parameters.size() != 2 ||
	    !pa11::same_type(pa11::strip_cv(binding->type->base),
	                     pa11::make_fundamental(FT_BOOL)))
		return false;
	string object = global_object_symbol(binding);
	bool named_comparison =
		binding->name == "operator==" || binding->name == "operator!=";
	bool type_info_member = std_type_info_record(class_record_for_member(binding));
	bool abi_type_info =
		object == "_ZNKSt9type_infoeqERKS_" ||
		object == "_ZNKSt9type_infoneERKS_";
	if ((!named_comparison || !type_info_member) && !abi_type_info)
		return false;
	return abi_type_info || type_info_reference(binding->type->parameters[1]);
}

bool hosted_basic_string_record(TypePtr record)
{
	TypePtr bare = record.get() != NULL ? pa11::strip_cv(record) : TypePtr();
	if (bare.get() == NULL ||
	    bare->kind != TypeKind::Record ||
	    !record_in_namespace(bare, "std"))
		return false;
	string primary = bare->template_primary_name.empty()
		? bare->name : bare->template_primary_name;
	size_t pos = primary.rfind("::");
	if (pos != string::npos)
		primary = primary.substr(pos + 2);
	return primary == "basic_string";
}

TypePtr hosted_equal_iterator_string_record(TypePtr type)
{
	TypePtr bare = type.get() != NULL ? pa11::strip_cv(type) : TypePtr();
	if (bare.get() == NULL)
		return TypePtr();
	if (bare->kind == TypeKind::Pointer &&
	    hosted_basic_string_record(pa11::strip_cv(bare->base)))
		return pa11::strip_cv(bare->base);
	if (bare->kind != TypeKind::Record)
		return TypePtr();
	try
	{
		pa11::layout_record_type(bare);
	}
	catch (const runtime_error&)
	{
		return TypePtr();
	}
	if (bare->fields.empty())
		return TypePtr();
	TypePtr field = pa11::strip_cv(bare->fields[0]->type);
	if (field.get() == NULL ||
	    field->kind != TypeKind::Pointer ||
	    !hosted_basic_string_record(pa11::strip_cv(field->base)))
		return TypePtr();
	return pa11::strip_cv(field->base);
}

bool hosted_equal_aux_basic_string_binding(const Binding* binding)
{
	if (binding == NULL ||
	    binding->type.get() == NULL ||
	    binding->type->kind != TypeKind::Function ||
	    binding->type->parameters.size() != 3 ||
	    !pa11::same_type(pa11::strip_cv(binding->type->base),
	                     pa11::make_fundamental(FT_BOOL)) ||
	    !binding_in_namespace(binding, "std"))
		return false;
	string object = global_object_symbol(binding);
	if (!starts_with(object, "_ZSt11__equal_aux") ||
	    object.find("NSt7__cxx1112basic_string") == string::npos)
		return false;
	TypePtr first = hosted_equal_iterator_string_record(
		binding->type->parameters[0]);
	TypePtr last = hosted_equal_iterator_string_record(
		binding->type->parameters[1]);
	TypePtr second = hosted_equal_iterator_string_record(
		binding->type->parameters[2]);
	return first.get() != NULL &&
	       last.get() != NULL &&
	       second.get() != NULL &&
	       pa11::same_type(first, last) &&
	       pa11::same_type(first, second);
}

bool hosted_int_object_type(TypePtr type)
{
	TypePtr bare = type.get() != NULL ? pa11::strip_cv(type) : TypePtr();
	return bare.get() != NULL &&
	       bare->kind == TypeKind::Fundamental &&
	       bare->fundamental == FT_INT;
}

TypePtr hosted_int_iterator_value_type(TypePtr type)
{
	TypePtr bare = type.get() != NULL ? pa11::strip_cv(type) : TypePtr();
	if (bare.get() == NULL)
		return TypePtr();
	if (bare->kind == TypeKind::Pointer &&
	    hosted_int_object_type(bare->base))
		return pa11::strip_cv(bare->base);
	if (bare->kind != TypeKind::Record)
		return TypePtr();
	try
	{
		pa11::layout_record_type(bare);
	}
	catch (const runtime_error&)
	{
		return TypePtr();
	}
	if (bare->fields.empty())
		return TypePtr();
	TypePtr field = pa11::strip_cv(bare->fields[0]->type);
	if (field.get() == NULL ||
	    field->kind != TypeKind::Pointer ||
	    !hosted_int_object_type(field->base))
		return TypePtr();
	return pa11::strip_cv(field->base);
}

bool hosted_lexicographical_compare_int_binding(const Binding* binding)
{
	if (binding == NULL ||
	    binding->type.get() == NULL ||
	    binding->type->kind != TypeKind::Function ||
	    binding->type->parameters.size() != 4 ||
	    !pa11::same_type(pa11::strip_cv(binding->type->base),
	                     pa11::make_fundamental(FT_BOOL)) ||
	    !binding_in_namespace(binding, "std"))
		return false;
	string object = global_object_symbol(binding);
	if (!starts_with(object, "_ZSt29__lexicographical_compare_aux") &&
	    !starts_with(object, "_ZSt30__lexicographical_compare_aux1") &&
	    !starts_with(object, "_ZNSt25__lexicographical_compareILb0EE4__lc"))
		return false;
	for (size_t i = 0; i < 4; ++i)
		if (hosted_int_iterator_value_type(
			    binding->type->parameters[i]).get() == NULL)
			return false;
	return true;
}

bool hosted_uninitialized_default_n_trivial_binding(const Binding* binding)
{
	if (binding == NULL ||
	    binding->name != pa11::abi_private_name("_uninit_default_n") ||
	    binding->type.get() == NULL ||
	    binding->type->kind != TypeKind::Function ||
	    binding->type->parameters.size() != 2 ||
	    scalar_lowir_type(binding->type->base) != "ptr" ||
	    !binding_in_namespace(binding, "std"))
		return false;
	string object = global_object_symbol(binding);
	if (object.find("__uninitialized_default_n_1ILb1EE") == string::npos)
		return false;
	TypePtr first = pa11::strip_cv(binding->type->parameters[0]);
	TypePtr result = pa11::strip_cv(binding->type->base);
	if (first.get() == NULL ||
	    result.get() == NULL ||
	    first->kind != TypeKind::Pointer ||
	    result->kind != TypeKind::Pointer ||
	    !pa11::same_type(pa11::strip_cv(first->base),
	                     pa11::strip_cv(result->base)))
		return false;
	TypePtr element = pa11::strip_cv(first->base);
	return element.get() != NULL && element->kind != TypeKind::Record;
}

bool hosted_default_allocator_record(TypePtr allocator, TypePtr element)
{
	TypePtr alloc = allocator.get() != NULL
		? pa11::strip_cv(allocator) : TypePtr();
	TypePtr elem = element.get() != NULL
		? pa11::strip_cv(element) : TypePtr();
	if (alloc.get() == NULL ||
	    alloc->kind != TypeKind::Record ||
	    elem.get() == NULL ||
	    !record_in_namespace(alloc, "std") ||
	    hosted_record_primary(alloc) != "allocator" ||
	    alloc->template_arguments.empty() ||
	    alloc->template_arguments[0].kind !=
		    pa11::TemplateInstanceArgumentKind::Type)
		return false;
	return pa11::same_type(
		pa11::strip_cv(alloc->template_arguments[0].type), elem);
}

bool hosted_vector_base_record(TypePtr record, TypePtr* element_out)
{
	TypePtr bare = record.get() != NULL ? pa11::strip_cv(record) : TypePtr();
	if (bare.get() == NULL ||
	    bare->kind != TypeKind::Record ||
	    !record_in_namespace(bare, "std") ||
	    hosted_record_primary(bare) != "_Vector_base" ||
	    bare->template_arguments.size() < 2 ||
	    bare->template_arguments[0].kind !=
		    pa11::TemplateInstanceArgumentKind::Type ||
	    bare->template_arguments[1].kind !=
		    pa11::TemplateInstanceArgumentKind::Type)
		return false;
	TypePtr element = pa11::strip_cv(bare->template_arguments[0].type);
	if (!hosted_default_allocator_record(
		    bare->template_arguments[1].type, element))
		return false;
	if (element_out != NULL)
		*element_out = element;
	return true;
}

bool hosted_vector_record(TypePtr record, TypePtr* element_out)
{
	TypePtr bare = record.get() != NULL ? pa11::strip_cv(record) : TypePtr();
	if (bare.get() == NULL ||
	    bare->kind != TypeKind::Record ||
	    !record_in_namespace(bare, "std") ||
	    hosted_record_primary(bare) != "vector" ||
	    bare->template_arguments.size() < 2 ||
	    bare->template_arguments[0].kind !=
		    pa11::TemplateInstanceArgumentKind::Type ||
	    bare->template_arguments[1].kind !=
		    pa11::TemplateInstanceArgumentKind::Type)
		return false;
	TypePtr element = pa11::strip_cv(bare->template_arguments[0].type);
	if (!hosted_default_allocator_record(
		    bare->template_arguments[1].type, element))
		return false;
	if (element_out != NULL)
		*element_out = element;
	return true;
}

TypePtr hosted_guard_alloc_vector_record(TypePtr guard_record)
{
	TypePtr guard = guard_record.get() != NULL
		? pa11::strip_cv(guard_record) : TypePtr();
	for (Scope* scope = guard.get() != NULL && guard->scope != NULL
	     ? guard->scope->parent : NULL;
	     scope != NULL;
	     scope = scope->parent)
	{
		if (scope->kind != ScopeKind::Class)
			continue;
		TypePtr owner = pa11::record_type_for_scope(scope);
		if (hosted_vector_record(owner, NULL))
			return pa11::strip_cv(owner);
	}
	return TypePtr();
}

Binding* basic_string_guarded_field(TypePtr record)
{
	TypePtr bare = record.get() != NULL ? pa11::strip_cv(record) : TypePtr();
	if (bare.get() == NULL || bare->kind != TypeKind::Record)
		return NULL;
	pa11::layout_record_type(bare);
	Binding* match = NULL;
	for (size_t i = 0; i < bare->fields.size(); ++i)
	{
		Binding* field = bare->fields[i];
		if (field == NULL)
			continue;
		TypePtr field_type = pa11::strip_cv(field->type);
		if (field_type.get() == NULL ||
		    field_type->kind != TypeKind::Pointer ||
		    !hosted_basic_string_record(field_type->base))
			continue;
		if (match != NULL)
			return NULL;
		match = field;
	}
	return match;
}

bool hosted_basic_string_guard_destructor_binding(const Binding* binding)
{
	if (!is_class_destructor_binding(binding) ||
	    binding->type.get() == NULL ||
	    binding->type->kind != TypeKind::Function ||
	    binding->type->parameters.size() != 1)
		return false;
	TypePtr record = class_record_for_member(binding);
	record = record.get() != NULL ? pa11::strip_cv(record) : TypePtr();
	if (record.get() == NULL ||
	    record->kind != TypeKind::Record ||
	    record->scope == NULL ||
	    record->scope->name.find("_Guard") == string::npos ||
	    !record_in_namespace(record, "std"))
		return false;
	return basic_string_guarded_field(record) != NULL;
}

bool hosted_uninit_destroy_guard_record(TypePtr record, TypePtr* iterator_out)
{
	TypePtr bare = record.get() != NULL ? pa11::strip_cv(record) : TypePtr();
	if (bare.get() == NULL ||
	    bare->kind != TypeKind::Record ||
	    !record_in_namespace(bare, "std") ||
	    hosted_record_primary(bare) != "_UninitDestroyGuard" ||
	    bare->template_arguments.size() < 2 ||
	    bare->template_arguments[0].kind !=
		    pa11::TemplateInstanceArgumentKind::Type ||
	    bare->template_arguments[1].kind !=
		    pa11::TemplateInstanceArgumentKind::Type ||
	    !pa11::is_void_type(
		    pa11::strip_cv(bare->template_arguments[1].type)))
		return false;
	TypePtr iterator = pa11::strip_cv(bare->template_arguments[0].type);
	if (!pointer_object_type(iterator))
		return false;
	if (iterator_out != NULL)
		*iterator_out = iterator;
	return true;
}

bool hosted_uninit_destroy_guard_destructor_binding(const Binding* binding)
{
	if (!is_class_destructor_binding(binding) ||
	    binding->type.get() == NULL ||
	    binding->type->kind != TypeKind::Function ||
	    binding->type->parameters.size() != 1)
		return false;
	return hosted_uninit_destroy_guard_record(
		class_record_for_member(binding), NULL);
}

bool hosted_vector_base_deallocate_binding(const Binding* binding)
{
	if (binding == NULL ||
	    binding->name != pa11::abi_private_name("M_deallocate") ||
	    binding->type.get() == NULL ||
	    binding->type->kind != TypeKind::Function ||
	    binding->type->parameters.size() != 3 ||
	    !pa11::is_void_type(binding->type->base) ||
	    scalar_lowir_type(binding->type->parameters[1]) != "ptr")
		return false;
	TypePtr record = class_record_for_member(binding);
	return hosted_vector_base_record(record, NULL);
}

bool hosted_vector_impl_move_constructor_binding(const Binding* binding)
{
	if (!is_class_constructor_binding(binding) ||
	    binding->type.get() == NULL ||
	    binding->type->kind != TypeKind::Function ||
	    binding->type->parameters.size() != 2 ||
	    binding->type->parameters[1].get() == NULL ||
	    binding->type->parameters[1]->kind != TypeKind::RValueReference)
		return false;
	string symbol = global_object_symbol(binding);
	if (symbol.find("12_Vector_impl") != string::npos &&
	    (symbol.find("C1EOS") != string::npos ||
	     symbol.find("C2EOS") != string::npos))
		return true;
	TypePtr record = class_record_for_member(binding);
	record = record.get() != NULL ? pa11::strip_cv(record) : TypePtr();
	return record.get() != NULL &&
	       record->kind == TypeKind::Record &&
	       record->scope != NULL &&
	       record->scope->name == pa11::abi_private_name("Vector_impl") &&
	       record_in_namespace(record, "std");
}

bool hosted_vector_guard_alloc_record(TypePtr record)
{
	TypePtr bare = record.get() != NULL ? pa11::strip_cv(record) : TypePtr();
	return bare.get() != NULL &&
	       bare->kind == TypeKind::Record &&
	       bare->scope != NULL &&
	       bare->scope->name == pa11::abi_private_name("Guard_alloc") &&
	       hosted_guard_alloc_vector_record(bare).get() != NULL;
}

bool hosted_vector_guard_alloc_destructor_binding(const Binding* binding)
{
	if (!is_class_destructor_binding(binding) ||
	    binding->type.get() == NULL ||
	    binding->type->kind != TypeKind::Function ||
	    binding->type->parameters.size() != 1)
		return false;
	return hosted_vector_guard_alloc_record(class_record_for_member(binding));
}

bool hosted_pair_record(TypePtr record)
{
	TypePtr bare = record.get() != NULL ? pa11::strip_cv(record) : TypePtr();
	return bare.get() != NULL &&
	       bare->kind == TypeKind::Record &&
	       record_in_namespace(bare, "std") &&
	       hosted_record_primary(bare) == "pair";
}

Binding* hosted_pair_field(TypePtr record, const string& name, size_t fallback);

TypePtr hosted_pair_argument(TypePtr record, size_t index)
{
	TypePtr bare = record.get() != NULL ? pa11::strip_cv(record) : TypePtr();
	if (!hosted_pair_record(bare) ||
	    bare->template_arguments.size() <= index ||
	    bare->template_arguments[index].kind !=
		    pa11::TemplateInstanceArgumentKind::Type)
		return TypePtr();
	return bare->template_arguments[index].type;
}

uint64_t hosted_pair_align_up(uint64_t value, uint64_t align)
{
	if (align <= 1)
		return value;
	uint64_t rem = value % align;
	return rem == 0 ? value : value + (align - rem);
}

TypePtr hosted_member_owner_record(const Binding* binding)
{
	TypePtr record = class_record_for_member(binding);
	record = record.get() != NULL ? pa11::strip_cv(record) : TypePtr();
	if (record.get() != NULL)
		return record;
	if (binding != NULL &&
	    binding->type.get() != NULL &&
	    binding->type->kind == TypeKind::Function &&
	    !binding->type->parameters.empty())
	{
		TypePtr self = binding->type->parameters[0];
		TypePtr object;
		if (self.get() != NULL && self->kind == TypeKind::Pointer)
			object = self->base;
		else if (is_reference(self))
			object = self->base;
		object = object.get() != NULL ? pa11::strip_cv(object) : TypePtr();
		if (object.get() != NULL && object->kind == TypeKind::Record)
			return object;
	}
	for (Scope* scope = binding != NULL ? binding->owner : NULL;
	     scope != NULL;
	     scope = scope->parent)
	{
		if (scope->kind != ScopeKind::Class)
			continue;
		record = pa11::record_type_for_scope(scope);
		record = record.get() != NULL ? pa11::strip_cv(record) : TypePtr();
		if (record.get() != NULL)
			return record;
	}
	return TypePtr();
}

Binding* hosted_field_named(TypePtr record, const string& name)
{
	TypePtr bare = record.get() != NULL ? pa11::strip_cv(record) : TypePtr();
	if (bare.get() == NULL || bare->kind != TypeKind::Record)
		return NULL;
	pa11::layout_record_type(bare);
	for (size_t i = 0; i < bare->fields.size(); ++i)
		if (bare->fields[i] != NULL &&
		    bare->fields[i]->name == name)
			return bare->fields[i];
	return NULL;
}

uint64_t hosted_field_offset_or_zero(TypePtr record, const string& name)
{
	TypePtr bare = record.get() != NULL ? pa11::strip_cv(record) : TypePtr();
	if (bare.get() == NULL || bare->kind != TypeKind::Record)
		return 0;
	pa11::layout_record_type(bare);
	Binding* named = hosted_field_named(bare, name);
	if (named != NULL)
		return named->member_offset;
	return bare->fields.empty() || bare->fields[0] == NULL
		? 0 : bare->fields[0]->member_offset;
}

bool hosted_tuple_storage_record(TypePtr record)
{
	TypePtr bare = record.get() != NULL ? pa11::strip_cv(record) : TypePtr();
	if (bare.get() == NULL ||
	    bare->kind != TypeKind::Record ||
	    !record_in_namespace(bare, "std"))
		return false;
	string primary = hosted_record_primary(bare);
	return primary == pa11::abi_private_name("Tuple_impl") ||
	       primary == pa11::abi_private_name("Head_base");
}

bool hosted_tuple_storage_default_constructor_binding(const Binding* binding)
{
	return is_class_constructor_binding(binding) &&
	       binding->type.get() != NULL &&
	       binding->type->kind == TypeKind::Function &&
	       binding->type->parameters.size() == 1 &&
	       hosted_tuple_storage_record(hosted_member_owner_record(binding));
}

bool hosted_tuple_storage_head_binding(const Binding* binding)
{
	if (binding == NULL ||
	    binding->name != pa11::abi_private_name("M_head") ||
	    binding->type.get() == NULL ||
	    binding->type->kind != TypeKind::Function ||
	    binding->type->parameters.size() != 1 ||
	    scalar_lowir_type(binding->type->base) != "ptr")
		return false;
	TypePtr record = hosted_member_owner_record(binding);
	TypePtr param = binding->type->parameters[0];
	if (is_reference(param))
		param = param->base;
	param = param.get() != NULL ? pa11::strip_cv(param) : TypePtr();
	return hosted_tuple_storage_record(record) &&
	       param.get() != NULL &&
	       param->kind == TypeKind::Record &&
	       pa11::same_type(pa11::strip_cv(record), param);
}

bool hosted_unique_ptr_impl_record(TypePtr record)
{
	TypePtr bare = record.get() != NULL ? pa11::strip_cv(record) : TypePtr();
	return bare.get() != NULL &&
	       bare->kind == TypeKind::Record &&
	       record_in_namespace(bare, "std") &&
	       (hosted_record_primary(bare) ==
		        pa11::abi_private_name("uniq_ptr_impl") ||
	        hosted_record_primary(bare) ==
		        pa11::abi_private_name("_uniq_ptr_impl"));
}

bool hosted_unique_ptr_record(TypePtr record)
{
	TypePtr bare = record.get() != NULL ? pa11::strip_cv(record) : TypePtr();
	return bare.get() != NULL &&
	       bare->kind == TypeKind::Record &&
	       record_in_namespace(bare, "std") &&
	       hosted_record_primary(bare) == "unique_ptr";
}

bool hosted_default_delete_record(TypePtr record)
{
	TypePtr bare = record.get() != NULL ? pa11::strip_cv(record) : TypePtr();
	return bare.get() != NULL &&
	       bare->kind == TypeKind::Record &&
	       record_in_namespace(bare, "std") &&
	       hosted_record_primary(bare) == "default_delete";
}

bool hosted_unique_ptr_destructor_binding(const Binding* binding,
                                          TypePtr* element_out)
{
	if (!is_class_destructor_binding(binding))
		return false;
	TypePtr record = hosted_member_owner_record(binding);
	record = record.get() != NULL ? pa11::strip_cv(record) : TypePtr();
	if (!hosted_unique_ptr_record(record) ||
	    record->template_arguments.empty() ||
	    record->template_arguments[0].kind !=
		    pa11::TemplateInstanceArgumentKind::Type)
		return false;
	if (record->template_arguments.size() > 1 &&
	    record->template_arguments[1].kind ==
		    pa11::TemplateInstanceArgumentKind::Type &&
	    !hosted_default_delete_record(
		    pa11::strip_cv(record->template_arguments[1].type)))
		return false;
	TypePtr element = pa11::strip_cv(record->template_arguments[0].type);
	if (element.get() != NULL &&
	    element->kind == TypeKind::Record &&
	    element->is_polymorphic)
		return false;
	if (element_out != NULL)
		*element_out = element;
	return element.get() != NULL;
}

bool hosted_unique_ptr_impl_pointer_constructor_binding(const Binding* binding)
{
	if (!is_class_constructor_binding(binding) ||
	    binding->type.get() == NULL ||
	    binding->type->kind != TypeKind::Function ||
	    binding->type->parameters.size() != 2)
		return false;
	TypePtr arg = pa11::strip_cv(binding->type->parameters[1]);
	return hosted_unique_ptr_impl_record(hosted_member_owner_record(binding)) &&
	       arg.get() != NULL &&
	       arg->kind == TypeKind::Pointer;
}

bool hosted_unique_ptr_impl_move_constructor_binding(const Binding* binding)
{
	if (!is_class_constructor_binding(binding) ||
	    binding->type.get() == NULL ||
	    binding->type->kind != TypeKind::Function ||
	    binding->type->parameters.size() != 2 ||
	    binding->type->parameters[1].get() == NULL ||
	    binding->type->parameters[1]->kind != TypeKind::RValueReference)
		return false;
	TypePtr record = hosted_member_owner_record(binding);
	TypePtr source = pa11::strip_cv(binding->type->parameters[1]->base);
	return hosted_unique_ptr_impl_record(record) &&
	       source.get() != NULL &&
	       source->kind == TypeKind::Record &&
	       pa11::same_type(pa11::strip_cv(record), source);
}

bool hosted_unique_ptr_impl_move_assignment_binding(const Binding* binding)
{
	if (binding == NULL ||
	    binding->name != "operator=" ||
	    binding->type.get() == NULL ||
	    binding->type->kind != TypeKind::Function ||
	    binding->type->parameters.size() != 2 ||
	    binding->type->parameters[1].get() == NULL ||
	    binding->type->parameters[1]->kind != TypeKind::RValueReference)
		return false;
	TypePtr record = hosted_member_owner_record(binding);
	TypePtr source = pa11::strip_cv(binding->type->parameters[1]->base);
	return hosted_unique_ptr_impl_record(record) &&
	       source.get() != NULL &&
	       source->kind == TypeKind::Record &&
	       pa11::same_type(pa11::strip_cv(record), source);
}

bool hosted_unique_ptr_impl_constructor_binding(const Binding* binding)
{
	return hosted_unique_ptr_impl_pointer_constructor_binding(binding) ||
	       hosted_unique_ptr_impl_move_constructor_binding(binding);
}

bool hosted_iter_equals_val_constructor_binding(const Binding* binding)
{
	if (!is_class_constructor_binding(binding) ||
	    binding->type.get() == NULL ||
	    binding->type->kind != TypeKind::Function ||
	    binding->type->parameters.size() != 2 ||
	    !is_reference(binding->type->parameters[1]))
		return false;
	TypePtr record = hosted_member_owner_record(binding);
	return record.get() != NULL &&
	       record->kind == TypeKind::Record &&
	       record_in_namespace(record, "__gnu_cxx") &&
	       hosted_record_primary(record) ==
		       pa11::abi_private_name("Iter_equals_val");
}

bool hosted_normal_iterator_record(TypePtr record, TypePtr* iterator_out)
{
	TypePtr bare = record.get() != NULL ? pa11::strip_cv(record) : TypePtr();
	if (bare.get() == NULL ||
	    bare->kind != TypeKind::Record ||
	    !record_in_namespace(bare, "__gnu_cxx") ||
	    hosted_record_primary(bare) !=
		    pa11::abi_private_name("_normal_iterator") ||
	    bare->template_arguments.empty() ||
	    bare->template_arguments[0].kind !=
		    pa11::TemplateInstanceArgumentKind::Type)
		return false;
	TypePtr iterator = pa11::strip_cv(bare->template_arguments[0].type);
	if (iterator.get() == NULL || iterator->kind != TypeKind::Pointer)
		return false;
	if (iterator_out != NULL)
		*iterator_out = iterator;
	return true;
}

bool hosted_normal_iterator_member_binding(const Binding* binding)
{
	if (binding == NULL ||
	    binding->type.get() == NULL ||
	    binding->type->kind != TypeKind::Function)
		return false;
	TypePtr iterator;
	if (!hosted_normal_iterator_record(hosted_member_owner_record(binding),
	                                   &iterator))
		return false;
	if ((binding->name == "base" || binding->name == "operator*") &&
	    binding->type->parameters.size() == 1 &&
	    scalar_lowir_type(binding->type->base) == "ptr")
		return true;
	if ((binding->name == "operator++" ||
	     binding->name == "operator--") &&
	    binding->type->parameters.size() == 1 &&
	    scalar_lowir_type(binding->type->base) == "ptr")
		return true;
	if ((binding->name == "operator+" ||
	     binding->name == "operator-") &&
	    binding->type->parameters.size() == 2)
	{
		TypePtr result = pa11::strip_cv(binding->type->base);
		TypePtr n = pa11::strip_cv(binding->type->parameters[1]);
		return result.get() != NULL &&
		       result->kind == TypeKind::Record &&
		       pa11::same_type(result,
		                       pa11::strip_cv(hosted_member_owner_record(binding))) &&
		       pa11::is_integral_or_bool_type(n);
	}
	return false;
}

bool hosted_normal_iterator_difference_binding(const Binding* binding,
                                               TypePtr* element_out)
{
	if (binding == NULL ||
	    binding->name != "operator-" ||
	    binding->type.get() == NULL ||
	    binding->type->kind != TypeKind::Function ||
	    binding->type->parameters.size() != 2 ||
	    !pa11::is_integral_or_bool_type(binding->type->base) ||
	    !binding_in_namespace(binding, "__gnu_cxx"))
		return false;
	TypePtr lhs = binding->type->parameters[0];
	TypePtr rhs = binding->type->parameters[1];
	if (is_reference(lhs))
		lhs = lhs->base;
	if (is_reference(rhs))
		rhs = rhs->base;
	lhs = pa11::strip_cv(lhs);
	rhs = pa11::strip_cv(rhs);
	TypePtr lhs_iterator;
	TypePtr rhs_iterator;
	if (!hosted_normal_iterator_record(lhs, &lhs_iterator) ||
	    !hosted_normal_iterator_record(rhs, &rhs_iterator) ||
	    !pa11::same_type(lhs, rhs) ||
	    !pa11::same_type(lhs_iterator, rhs_iterator))
		return false;
	TypePtr element = pa11::strip_cv(lhs_iterator->base);
	if (element.get() == NULL)
		return false;
	if (element_out != NULL)
		*element_out = element;
	return true;
}

bool hosted_ops_compare_record(TypePtr record)
{
	TypePtr bare = record.get() != NULL ? pa11::strip_cv(record) : TypePtr();
	if (bare.get() == NULL ||
	    bare->kind != TypeKind::Record ||
	    !record_in_namespace(bare, "__gnu_cxx"))
		return false;
	string primary = hosted_record_primary(bare);
	return primary == pa11::abi_private_name("Iter_comp_iter") ||
	       primary == pa11::abi_private_name("Val_comp_iter") ||
	       primary == pa11::abi_private_name("Iter_comp_val");
}

bool hosted_ops_compare_constructor_binding(const Binding* binding)
{
	if (!is_class_constructor_binding(binding) ||
	    binding->type.get() == NULL ||
	    binding->type->kind != TypeKind::Function ||
	    binding->type->parameters.size() != 2)
		return false;
	return hosted_ops_compare_record(hosted_member_owner_record(binding));
}

bool hosted_uninit_destroy_guard_constructor_binding(const Binding* binding)
{
	if (!is_class_constructor_binding(binding) ||
	    binding->type.get() == NULL ||
	    binding->type->kind != TypeKind::Function ||
	    binding->type->parameters.size() != 2 ||
	    !is_reference(binding->type->parameters[1]))
		return false;
	TypePtr iterator;
	if (!hosted_uninit_destroy_guard_record(
		    hosted_member_owner_record(binding), &iterator))
		return false;
	TypePtr param = pa11::strip_cv(binding->type->parameters[1]->base);
	return param.get() != NULL && pa11::same_type(param, iterator);
}

bool hosted_uninit_destroy_guard_release_binding(const Binding* binding)
{
	return binding != NULL &&
	       binding->name == "release" &&
	       binding->type.get() != NULL &&
	       binding->type->kind == TypeKind::Function &&
	       binding->type->parameters.size() == 1 &&
	       pa11::is_void_type(binding->type->base) &&
	       hosted_uninit_destroy_guard_record(
		       hosted_member_owner_record(binding), NULL);
}

}  // namespace internal
}  // namespace pa14
