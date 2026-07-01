#include "pa14_lowir_internal.h"

namespace pa14 {
namespace internal {
namespace {

bool copy_move_constructor_binding(const Binding* binding)
{
	if (binding == NULL ||
	    !is_class_constructor_binding(binding) ||
	    binding->type.get() == NULL ||
	    binding->type->kind != TypeKind::Function ||
	    binding->type->parameters.size() != 2 ||
	    !is_reference(binding->type->parameters[1]))
		return false;
	TypePtr record = class_record_for_member(binding);
	record = record.get() != NULL ? pa11::strip_cv(record) : TypePtr();
	TypePtr source = pa11::strip_cv(binding->type->parameters[1]->base);
	return record.get() != NULL &&
	       record->kind == TypeKind::Record &&
	       source.get() != NULL &&
	       source->kind == TypeKind::Record &&
	       pa11::same_type(record, source);
}

bool extern_template_class_binding(const Binding* binding)
{
	if (binding == NULL)
		return false;
	for (Scope* scope = binding->owner; scope != NULL; scope = scope->parent)
	{
		if (scope->kind != ScopeKind::Class)
			continue;
		TypePtr record = pa11::record_type_for_scope(scope);
		record = record.get() != NULL ? pa11::strip_cv(record) : TypePtr();
		if (record.get() != NULL &&
		    record->kind == TypeKind::Record &&
		    record->is_extern_template_instantiation)
			return true;
	}
	return false;
}

string unqualified_template_primary(TypePtr type)
{
	TypePtr bare = type.get() != NULL ? pa11::strip_cv(type) : TypePtr();
	if (bare.get() == NULL)
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

bool record_is_in_std_namespace(TypePtr record)
{
	record = record.get() != NULL ? pa11::strip_cv(record) : TypePtr();
	Scope* scope = record.get() != NULL ? record->scope : NULL;
	for (Scope* cur = scope; cur != NULL; cur = cur->parent)
		if (cur->kind == ScopeKind::Namespace && cur->name == "std")
			return true;
	return false;
}

bool implicit_copy_constructor_synthesizable_type(
	TypePtr type,
	bool move,
	set<const pa11::Type*>& seen_records);

bool implicit_copy_constructor_synthesizable_record_impl(
	TypePtr type,
	bool move,
	set<const pa11::Type*>& seen_records)
{
	TypePtr record = type.get() != NULL ? pa11::strip_cv(type) : TypePtr();
	if (record.get() == NULL ||
	    record->kind != TypeKind::Record ||
	    record->scope == NULL ||
	    record->is_polymorphic ||
	    record->tag == "union" ||
	    record_is_in_std_namespace(record) ||
	    !pa11::record_virtual_bases(record).empty() ||
	    !pa11::record_direct_bases(record).empty())
		return false;
	if (!seen_records.insert(record.get()).second)
		return true;
	pa11::layout_record_type(record);
	for (size_t i = 0; i < record->fields.size(); ++i)
	{
		Binding* field = record->fields[i];
		if (field == NULL || field->is_bit_field)
			continue;
		if (!implicit_copy_constructor_synthesizable_type(field->type,
		                                                  move,
		                                                  seen_records))
			return false;
	}
	return true;
}

bool implicit_copy_constructor_synthesizable_type(
	TypePtr type,
	bool move,
	set<const pa11::Type*>& seen_records)
{
	TypePtr bare = type.get() != NULL ? pa11::strip_cv(type) : TypePtr();
	if (bare.get() == NULL)
		return false;
	if (bare->kind == TypeKind::Array)
		return implicit_copy_constructor_synthesizable_type(bare->base,
		                                                    move,
		                                                    seen_records);
	if (bare->kind != TypeKind::Record)
		return true;
	Binding* ctor = find_copy_move_constructor(bare, move);
	if (ctor == NULL && move)
		ctor = find_copy_move_constructor(bare, false);
	if (ctor != NULL || !type_needs_destructor(bare))
		return true;
	return implicit_copy_constructor_synthesizable_record_impl(
		bare,
		move,
		seen_records);
}

TypePtr member_owner_record(const Binding* binding)
{
	TypePtr record = class_record_for_member(binding);
	record = record.get() != NULL ? pa11::strip_cv(record) : TypePtr();
	if (record.get() != NULL)
		return record;
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

bool hosted_vector_member_element(const Binding* binding, TypePtr* element_out)
{
	TypePtr record = member_owner_record(binding);
	if (record.get() == NULL ||
	    record->kind != TypeKind::Record ||
	    unqualified_template_primary(record) != "vector" ||
	    !record_is_in_std_namespace(record) ||
	    record->template_arguments.empty() ||
	    record->template_arguments[0].kind !=
		    pa11::TemplateInstanceArgumentKind::Type)
		return false;
	TypePtr element = pa11::strip_cv(record->template_arguments[0].type);
	if (element.get() == NULL || element->kind == TypeKind::Array)
		return false;
	if (element_out != NULL)
		*element_out = element;
	return true;
}

bool hosted_vector_bool_element(TypePtr element)
{
	element = element.get() != NULL ? pa11::strip_cv(element) : TypePtr();
	return element.get() != NULL &&
	       element->kind == TypeKind::Fundamental &&
	       element->fundamental == FT_BOOL;
}

}  // namespace

bool implicit_copy_constructor_synthesizable_record(TypePtr type, bool move)
{
	set<const pa11::Type*> seen_records;
	return implicit_copy_constructor_synthesizable_record_impl(type,
	                                                           move,
	                                                           seen_records);
}

bool lowir_synthesizable_noop_constructor(const Binding* binding)
{
	if (binding == NULL ||
	    !is_class_constructor_binding(binding) ||
	    binding->type.get() == NULL ||
	    binding->type->kind != TypeKind::Function ||
	    binding->type->parameters.empty())
		return false;
	TypePtr record = class_record_for_member(binding);
	record = record.get() != NULL ? pa11::strip_cv(record) : TypePtr();
	if (record.get() == NULL || record->kind != TypeKind::Record)
		return false;
	if (binding->is_generated_default_constructor &&
	    binding->is_noop_constructor &&
	    !binding->is_object_root)
		return false;
	string primary = record->template_primary_name.empty()
		? (record->scope != NULL ? record->scope->name : record->name)
		: record->template_primary_name;
	size_t qpos = primary.rfind("::");
	if (qpos != string::npos)
		primary = primary.substr(qpos + 2);
	bool hosted_allocator_ctor =
		primary == "allocator" &&
		(binding->type->parameters.size() == 1 ||
		 binding->type->parameters.size() == 2);
	bool hosted_exception_default_ctor =
		binding->type->parameters.size() == 1 &&
		hosted_exception_record(record);
	bool hosted_empty_tuple_storage_ctor = false;
	if ((primary == pa11::abi_private_name("Tuple_impl") ||
	     primary == pa11::abi_private_name("Head_base")) &&
	    record_is_in_std_namespace(record) &&
	    !record->is_polymorphic &&
	    pa11::record_virtual_bases(record).empty() &&
	    pa11::type_size(record) <= 1 &&
	    (binding->type->parameters.size() == 1 ||
	     binding->type->parameters.size() == 2))
		hosted_empty_tuple_storage_ctor = true;
	if (!hosted_allocator_ctor &&
	    !hosted_exception_default_ctor &&
	    !hosted_empty_tuple_storage_ctor)
		return false;
	return hosted_exception_default_ctor ||
	       hosted_empty_tuple_storage_ctor ||
	       (!record->is_polymorphic &&
	        pa11::record_virtual_bases(record).empty() &&
	        pa11::record_direct_bases(record).empty());
}

bool lowir_synthesizable_defaulted_storage_copy_constructor(
	const Binding* binding)
{
	if (binding == NULL ||
	    binding->type.get() == NULL ||
	    binding->type->kind != TypeKind::Function ||
	    binding->type->parameters.size() != 2 ||
	    !is_reference(binding->type->parameters[1]))
		return false;
	bool defaulted_copy_move =
		binding->is_generated_copy_move_constructor &&
		binding->is_defaulted &&
		binding->is_inline_definition;
	bool same_record_template_constructor =
		!binding->function_specialization_symbol.empty() &&
		is_class_constructor_binding(binding) &&
		!binding->is_inline_definition;
	if (!defaulted_copy_move && !same_record_template_constructor)
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
	if (same_record_template_constructor)
		return !record->is_polymorphic &&
		       pa11::record_virtual_bases(record).empty();
	return !defaulted_copy_move_constructor_needs_helper(
		const_cast<Binding*>(binding), record);
}

bool lowir_hosted_tree_copy_move_constructor(const Binding* binding)
{
	if (!copy_move_constructor_binding(binding))
		return false;
	TypePtr record = class_record_for_member(binding);
	record = record.get() != NULL ? pa11::strip_cv(record) : TypePtr();
	return record.get() != NULL &&
	       record->kind == TypeKind::Record &&
	       record->scope != NULL &&
	       record->scope->name == pa11::abi_private_name("Rb_tree");
}

bool lowir_synthesizable_hosted_hashtable_count_constructor(
	const Binding* binding)
{
	if (binding == NULL ||
	    !is_class_constructor_binding(binding) ||
	    binding->type.get() == NULL ||
	    binding->type->kind != TypeKind::Function ||
	    binding->type->parameters.size() != 5)
		return false;
	TypePtr record = class_record_for_member(binding);
	record = record.get() != NULL ? pa11::strip_cv(record) : TypePtr();
	return record.get() != NULL &&
	       record->kind == TypeKind::Record &&
	       unqualified_template_primary(record) == pa11::abi_private_name("Hashtable") &&
	       record_is_in_std_namespace(record);
}

bool lowir_synthesizable_hosted_hashtable_range_constructor(
	const Binding* binding)
{
	if (binding == NULL ||
	    !is_class_constructor_binding(binding) ||
	    binding->type.get() == NULL ||
	    binding->type->kind != TypeKind::Function ||
	    binding->type->parameters.size() != 8)
		return false;
	TypePtr record = class_record_for_member(binding);
	record = record.get() != NULL ? pa11::strip_cv(record) : TypePtr();
	if (record.get() == NULL ||
	    record->kind != TypeKind::Record ||
	    unqualified_template_primary(record) != pa11::abi_private_name("Hashtable") ||
	    !record_is_in_std_namespace(record))
		return false;
	TypePtr first = binding->type->parameters[1].get() != NULL
		? pa11::strip_cv(binding->type->parameters[1]) : TypePtr();
	TypePtr last = binding->type->parameters[2].get() != NULL
		? pa11::strip_cv(binding->type->parameters[2]) : TypePtr();
	bool cached_hash = false;
	if (record->template_arguments.size() > 9 &&
	    record->template_arguments[9].kind ==
		    pa11::TemplateInstanceArgumentKind::Type)
	{
		TypePtr traits = pa11::strip_cv(record->template_arguments[9].type);
		if (traits.get() != NULL &&
		    traits->kind == TypeKind::Record &&
		    !traits->template_arguments.empty() &&
		    traits->template_arguments[0].kind ==
			    pa11::TemplateInstanceArgumentKind::Value)
			cached_hash = traits->template_arguments[0].value != 0;
	}
	return cached_hash &&
	       first.get() != NULL &&
	       last.get() != NULL &&
	       first->kind == TypeKind::Pointer &&
	       last->kind == TypeKind::Pointer &&
	       pa11::same_type(first, last);
}

bool lowir_synthesizable_hosted_hash_code_base_hash_code(
	const Binding* binding)
{
	if (binding == NULL ||
	    binding->name != pa11::abi_private_name("M_hash_code") ||
	    binding->type.get() == NULL ||
	    binding->type->kind != TypeKind::Function ||
	    binding->type->parameters.size() != 2 ||
	    scalar_lowir_type(binding->type->base) != "i64" ||
	    !is_reference(binding->type->parameters[1]))
		return false;
	TypePtr record = member_owner_record(binding);
	record = record.get() != NULL ? pa11::strip_cv(record) : TypePtr();
	TypePtr key = pa11::strip_cv(binding->type->parameters[1]->base);
	return record.get() != NULL &&
	       record->kind == TypeKind::Record &&
	       unqualified_template_primary(record) ==
		       pa11::abi_private_name("Hash_code_base") &&
	       record_is_in_std_namespace(record) &&
	       key.get() != NULL &&
	       key->kind == TypeKind::Record &&
	       unqualified_template_primary(key) == "basic_string" &&
	       record_is_in_std_namespace(key);
}

bool lowir_synthesizable_hosted_vector_copy_assignment(
	const Binding* binding)
{
	if (binding == NULL ||
	    binding->name != "operator=" ||
	    binding->type.get() == NULL ||
	    binding->type->kind != TypeKind::Function ||
	    binding->type->parameters.size() != 2 ||
	    scalar_lowir_type(binding->type->base) != "ptr")
		return false;
	TypePtr element;
	if (!hosted_vector_member_element(binding, &element))
		return false;
	TypePtr source = binding->type->parameters[1];
	if (source.get() == NULL || source->kind != TypeKind::LValueReference)
		return false;
	TypePtr record = member_owner_record(binding);
	TypePtr source_record = pa11::strip_cv(source->base);
	if (source_record.get() == NULL ||
	    source_record->kind != TypeKind::Record ||
	    !pa11::same_type(record, source_record))
		return false;
	if (element->kind != TypeKind::Record)
		return true;
	return (find_copy_move_constructor(element, false) != NULL ||
	        !type_needs_destructor(element) ||
	        implicit_copy_constructor_synthesizable_record(element, false)) &&
	       (find_record_copy_move_assignment(element, false) != NULL ||
	        !type_needs_destructor(element));
}

bool lowir_synthesizable_hosted_vector_copy_constructor(
	const Binding* binding)
{
	if (binding == NULL ||
	    !is_class_constructor_binding(binding) ||
	    binding->type.get() == NULL ||
	    binding->type->kind != TypeKind::Function ||
	    binding->type->parameters.size() != 2)
		return false;
	TypePtr element;
	if (!hosted_vector_member_element(binding, &element))
		return false;
	TypePtr source = binding->type->parameters[1];
	if (source.get() == NULL || source->kind != TypeKind::LValueReference)
		return false;
	TypePtr record = member_owner_record(binding);
	TypePtr source_record = pa11::strip_cv(source->base);
	if (source_record.get() == NULL ||
	    source_record->kind != TypeKind::Record ||
	    !pa11::same_type(record, source_record))
		return false;
	if (element->kind != TypeKind::Record)
		return true;
	return find_copy_move_constructor(element, false) != NULL ||
	       !type_needs_destructor(element) ||
	       implicit_copy_constructor_synthesizable_record(element, false);
}

bool lowir_synthesizable_hosted_vector_range_insert(
	const Binding* binding)
{
	if (binding == NULL ||
	    binding->name != "insert" ||
	    binding->type.get() == NULL ||
	    binding->type->kind != TypeKind::Function)
		return false;
	string symbol = global_object_symbol(binding);
	if (binding->type->parameters.size() == 3 &&
	    symbol.find("St6vector") != string::npos &&
	    symbol.find("6insert") != string::npos &&
	    symbol.find("St16initializer_list") != string::npos)
		return true;
	TypePtr record = class_record_for_member(binding);
	record = record.get() != NULL ? pa11::strip_cv(record) : TypePtr();
	if (record.get() == NULL ||
	    record->kind != TypeKind::Record ||
	    unqualified_template_primary(record) != "vector" ||
	    !record_is_in_std_namespace(record) ||
	    record->template_arguments.empty() ||
	    record->template_arguments[0].kind !=
		    pa11::TemplateInstanceArgumentKind::Type)
		return false;
	TypePtr element = pa11::strip_cv(record->template_arguments[0].type);
	if (element.get() == NULL || element->kind == TypeKind::Array)
		return false;
	if (hosted_vector_bool_element(element))
		return false;
	if (binding->type->parameters.size() == 3)
	{
		TypePtr param = binding->type->parameters[2];
		if (is_reference(param))
			param = param->base;
		TypePtr list_element;
		if (is_initializer_list_type(pa11::strip_cv(param), &list_element) &&
		    pa11::same_type(pa11::strip_cv(element),
		                    pa11::strip_cv(list_element)))
			return true;
		return symbol.find("St16initializer_list") != string::npos;
	}
	if (binding->type->parameters.size() != 4)
		return false;
	if (element->kind != TypeKind::Record)
		return true;
	return find_copy_move_constructor(element, false) != NULL ||
	       !type_needs_destructor(element);
}

bool lowir_synthesizable_hosted_vector_realloc_insert(
	const Binding* binding)
{
	if (binding == NULL ||
	    binding->name != pa11::abi_private_name("M_realloc_insert") ||
	    binding->type.get() == NULL ||
	    binding->type->kind != TypeKind::Function ||
	    binding->type->parameters.size() != 3)
		return false;
	TypePtr record = class_record_for_member(binding);
	record = record.get() != NULL ? pa11::strip_cv(record) : TypePtr();
	if (record.get() == NULL ||
	    record->kind != TypeKind::Record ||
	    unqualified_template_primary(record) != "vector" ||
	    !record_is_in_std_namespace(record) ||
	    record->template_arguments.empty() ||
	    record->template_arguments[0].kind !=
		    pa11::TemplateInstanceArgumentKind::Type)
		return false;
	TypePtr element = pa11::strip_cv(record->template_arguments[0].type);
	TypePtr arg = pa11::strip_cv(binding->type->parameters[2]);
	if (element.get() == NULL || arg.get() == NULL ||
	    element->kind != TypeKind::Record ||
	    unqualified_template_primary(element) != "unique_ptr" ||
	    !record_is_in_std_namespace(element) ||
	    !is_reference(arg) ||
	    !pa11::same_type(element, pa11::strip_cv(arg->base)))
		return false;
	return find_copy_move_constructor(element, true) != NULL ||
	       find_copy_move_constructor(element, false) != NULL ||
	       !type_needs_destructor(element);
}

bool lowir_synthesizable_hosted_vector_initializer_realloc_insert(
	const Binding* binding)
{
	if (binding == NULL ||
	    binding->name != pa11::abi_private_name("M_realloc_insert") ||
	    binding->type.get() == NULL ||
	    binding->type->kind != TypeKind::Function ||
	    binding->type->parameters.size() != 3)
		return false;
	TypePtr element;
	if (hosted_vector_member_element(binding, &element) &&
	    hosted_vector_bool_element(element))
		return false;
	string symbol = global_object_symbol(binding);
	return symbol.find("St6vector") != string::npos &&
	       symbol.find("17_M_realloc_insert") != string::npos &&
	       symbol.find("St16initializer_list") != string::npos;
}

bool lowir_synthesizable_hosted_vector_relocate(const Binding* binding)
{
	if (binding == NULL ||
	    binding->name != pa11::abi_private_name("S_relocate") ||
	    binding->type.get() == NULL ||
	    binding->type->kind != TypeKind::Function ||
	    binding->type->parameters.size() != 4)
		return false;
	TypePtr result = binding->type->base.get() != NULL
		? pa11::strip_cv(binding->type->base) : TypePtr();
	if (result.get() == NULL || result->kind != TypeKind::Pointer)
		return false;
	TypePtr element;
	if (!hosted_vector_member_element(binding, &element))
		return false;
	if (hosted_vector_bool_element(element))
		return false;
	if (element->kind != TypeKind::Record)
		return true;
	return find_copy_move_constructor(element, true) != NULL ||
	       find_copy_move_constructor(element, false) != NULL ||
	       !type_needs_destructor(element);
}

bool lowir_synthesizable_hosted_initializer_list_allocator_construct(
	const Binding* binding)
{
	if (binding == NULL ||
	    binding->name != "construct" ||
	    binding->type.get() == NULL ||
	    binding->type->kind != TypeKind::Function ||
	    binding->type->parameters.size() != 3)
		return false;
	string symbol = global_object_symbol(binding);
	return symbol.find("9construct") != string::npos &&
	       symbol.find("St16initializer_list") != string::npos &&
	       (symbol.find("St15__new_allocator") != string::npos ||
	        symbol.find("St16allocator_traits") != string::npos);
}

bool lowir_synthesizable_hosted_unique_ptr_allocator_copy_construct(
	const Binding* binding)
{
	if (binding == NULL ||
	    binding->name != "construct" ||
	    binding->type.get() == NULL ||
	    binding->type->kind != TypeKind::Function ||
	    binding->type->parameters.size() != 3)
		return false;
	string symbol = global_object_symbol(binding);
	if (symbol.find("9construct") == string::npos ||
	    (symbol.find("St15__new_allocator") == string::npos &&
	     symbol.find("St16allocator_traits") == string::npos))
		return false;
	TypePtr arg = pa11::strip_cv(binding->type->parameters[2]);
	if (arg.get() == NULL ||
	    arg->kind != TypeKind::LValueReference)
		return false;
	TypePtr record = pa11::strip_cv(arg->base);
	return record.get() != NULL &&
	       record->kind == TypeKind::Record &&
	       unqualified_template_primary(record) == "unique_ptr" &&
	       record_is_in_std_namespace(record);
}

bool lowir_synthesizable_hosted_unique_ptr_copy_helper(const Binding* binding)
{
	if (binding == NULL ||
	    binding->owner == NULL ||
	    binding->owner->kind != ScopeKind::Namespace ||
	    binding->owner->name != "std" ||
	    (binding->name != "_Construct" &&
	     binding->name != "fill" &&
	     binding->name != "__fill_a" &&
	     binding->name != "__fill_a1") ||
	    binding->type.get() == NULL ||
	    binding->type->kind != TypeKind::Function)
		return false;
	return global_object_symbol(binding).find("St10unique_ptr") != string::npos;
}

Node lowir_make_defaulted_storage_copy_constructor_node(
	const Binding* binding)
{
	TypePtr record = class_record_for_member(binding);
	record = record.get() != NULL ? pa11::strip_cv(record) : TypePtr();
	TypePtr source = pa11::strip_cv(binding->type->parameters[1]->base);
	string other_name = "other";
	if (binding->function_parameter_names.size() > 1 &&
	    !binding->function_parameter_names[1].empty())
		other_name = binding->function_parameter_names[1];
	Scope* function_scope =
		pa11::create_child_scope(binding->owner,
		                         ScopeKind::Function,
		                         binding->name);
	Binding* this_binding =
		pa11::add_binding(function_scope,
		                  BindingKind::Parameter,
		                  "this",
		                  binding->type->parameters[0]);
	Binding* other_binding =
		pa11::add_binding(function_scope,
		                  BindingKind::Parameter,
		                  other_name,
		                  binding->type->parameters[1]);
	Node fn("function-definition");
	fn.binding = const_cast<Binding*>(binding);
	fn.type = binding->type;
	Node this_param("parameter this");
	this_param.binding = this_binding;
	this_param.type = binding->type->parameters[0];
	fn.children.push_back(this_param);
	Node other_param("parameter " + other_name);
	other_param.binding = other_binding;
	other_param.type = binding->type->parameters[1];
	fn.children.push_back(other_param);
	Node other("id-expression lvalue " + pa11::describe_type(source) +
	           " " + other_name);
	other.binding = other_binding;
	other.type = source;
	other.category = ValueCategory::LValue;
	Node action("storage-copy-action");
	action.type = record;
	action.has_constant_value = true;
	action.constant_value = pa11::type_size(record);
	pa12::internal::add_child(action, other);
	Node body("compound-statement");
	pa12::internal::add_child(body, action);
	fn.children.push_back(body);
	return fn;
}

Node lowir_make_hosted_hashtable_count_constructor_node(
	const Binding* binding)
{
	Node fn("function-definition");
	fn.binding = const_cast<Binding*>(binding);
	fn.type = binding->type;
	static const char* names[] = {
		"this",
		"__bkt_count_hint",
		"__h",
		"__eq",
		"__a"
	};
	for (size_t i = 0; i < binding->type->parameters.size(); ++i)
	{
		Node param(string("parameter ") + names[i]);
		param.type = binding->type->parameters[i];
		fn.children.push_back(param);
	}
	fn.children.push_back(Node("compound-statement"));
	return fn;
}

Node lowir_make_hosted_vector_range_insert_node(
	const Binding* binding)
{
	Node fn("function-definition");
	fn.binding = const_cast<Binding*>(binding);
	fn.type = binding->type;
	static const char* names[] = {
		"this",
		"__position",
		"__first",
		"__last"
	};
	for (size_t i = 0; i < binding->type->parameters.size(); ++i)
	{
		Node param(string("parameter ") + names[i]);
		param.type = binding->type->parameters[i];
		fn.children.push_back(param);
	}
	fn.children.push_back(Node("compound-statement"));
	return fn;
}

bool lowir_extern_template_class_external_binding(const Binding* binding)
{
	TypePtr record = class_record_for_member(binding);
	record = record.get() != NULL ? pa11::strip_cv(record) : TypePtr();
	if (record.get() == NULL)
		return false;
	bool hosted_string =
		unqualified_template_primary(record) == "basic_string" &&
		record_is_in_std_namespace(record);
	if (hosted_string)
		return hosted_basic_string_external_member(binding) ||
		       (!binding_has_function_template_specialization_symbol(binding) &&
		       (is_class_constructor_binding(binding) ||
		        is_class_destructor_binding(binding) ||
		        binding->name == "operator="));
	if (!extern_template_class_binding(binding))
		return false;
	return record_uses_hosted_external_stream_vtable(record);
}

}  // namespace internal
}  // namespace pa14
