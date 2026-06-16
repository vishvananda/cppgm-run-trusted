#include "pa11_internal.h"
#include <algorithm>
#include <stdexcept>
using namespace std;

namespace pa11 {

bool type_uses_object_storage(TypePtr type);

namespace {

bool scope_has_namespace_named(Scope* scope, const string& name)
{
	for (Scope* cur = scope; cur != NULL; cur = cur->parent)
		if (cur->kind == ScopeKind::Namespace && cur->name == name)
			return true;
	return false;
}

string unqualified_template_primary_name(TypePtr type)
{
	TypePtr bare = type.get() != NULL ? strip_cv(type) : TypePtr();
	if (bare.get() == NULL)
		return "";
	string primary = bare->template_primary_name.empty()
		? bare->name : bare->template_primary_name;
	size_t pos = primary.rfind("::");
	return pos == string::npos ? primary : primary.substr(pos + 2);
}

void set_scope_variable_offset(Scope* scope,
                               const string& name,
                               uint64_t offset)
{
	if (scope == NULL)
		return;
	map<string, vector<Binding*> >::iterator found = scope->members.find(name);
	if (found == scope->members.end())
		return;
	for (size_t i = 0; i < found->second.size(); ++i)
	{
		Binding* binding = found->second[i];
		if (binding == NULL ||
		    binding->kind != BindingKind::Variable ||
		    binding->is_static_member)
			continue;
		binding->member_offset = offset;
		if (binding->aliased_binding != NULL)
			binding->aliased_binding->member_offset = offset;
	}
}

bool scope_has_nonstatic_variable(Scope* scope, const string& name)
{
	if (scope == NULL)
		return false;
	map<string, vector<Binding*> >::iterator found = scope->members.find(name);
	if (found == scope->members.end())
		return false;
	for (size_t i = 0; i < found->second.size(); ++i)
	{
		Binding* binding = found->second[i];
		if (binding != NULL &&
		    binding->kind == BindingKind::Variable &&
		    !binding->is_static_member)
			return true;
	}
	return false;
}

void set_scope_variable_offset_by_prefix(Scope* scope,
                                         const string& prefix,
                                         uint64_t offset)
{
	if (scope == NULL)
		return;
	for (map<string, vector<Binding*> >::iterator it = scope->members.begin();
	     it != scope->members.end();
	     ++it)
	{
		if (it->first.find(prefix) != 0)
			continue;
		for (size_t i = 0; i < it->second.size(); ++i)
		{
			Binding* binding = it->second[i];
			if (binding == NULL ||
			    binding->kind != BindingKind::Variable ||
			    binding->is_static_member)
				continue;
			binding->member_offset = offset;
		}
	}
}

bool complete_hosted_shared_ptr_layout(TypePtr type)
{
	TypePtr bare = type.get() != NULL ? strip_cv(type) : TypePtr();
	if (bare.get() == NULL ||
	    bare->kind != TypeKind::Record ||
	    !bare->is_template_specialization ||
	    !scope_has_namespace_named(bare->scope, "std"))
		return false;
	string primary = unqualified_template_primary_name(bare);
	if (primary != "shared_ptr" && primary != "__shared_ptr")
		return false;
	bare->complete = true;
	bare->fields.clear();
	bare->direct_bases.clear();
	bare->direct_base_offsets.clear();
	bare->direct_base_virtuals.clear();
	bare->virtual_bases.clear();
	bare->virtual_base_offsets.clear();
	bare->direct_base_offset = 0;
	bare->record_size = 16;
	bare->record_align = 8;
	bare->nonvirtual_size = 16;
	bare->nonvirtual_align = 8;
	bare->layout_valid = true;
	bare->hosted_layout_synthesized = true;
	return true;
}

bool complete_hosted_hashtable_ebo_helper_layout(TypePtr type)
{
	TypePtr bare = type.get() != NULL ? strip_cv(type) : TypePtr();
	if (bare.get() == NULL ||
	    bare->kind != TypeKind::Record ||
	    !bare->is_template_specialization ||
	    !scope_has_namespace_named(bare->scope, "std") ||
	    unqualified_template_primary_name(bare) != "_Hashtable_ebo_helper")
		return false;
	bool use_no_unique_storage = true;
	TypePtr object_type;
	if (!bare->template_arguments.empty() &&
	    bare->template_arguments[0].kind == TemplateInstanceArgumentKind::Type)
		object_type = bare->template_arguments[0].type;
	if (bare->template_arguments.size() > 1 &&
	    bare->template_arguments[1].kind == TemplateInstanceArgumentKind::Value &&
	    !bare->template_arguments[1].dependent)
		use_no_unique_storage = bare->template_arguments[1].value != 0;
	uint64_t size = 1;
	uint64_t align = 1;
	TypePtr object_bare =
		object_type.get() != NULL ? strip_cv(object_type) : TypePtr();
	bool concrete_object =
		object_bare.get() != NULL &&
		!object_bare->is_dependent_typename &&
		object_bare->kind != TypeKind::TemplateParameter &&
		object_bare->kind != TypeKind::TemplateTemplateParameter &&
		(object_bare->kind != TypeKind::Record || object_bare->complete);
	bool object_has_storage =
		concrete_object && type_uses_object_storage(object_type);
	if (concrete_object && (!use_no_unique_storage || object_has_storage))
	{
		size = max<uint64_t>(uint64_t(1), type_size(object_type));
		align = max<uint64_t>(uint64_t(1), type_align(object_type));
	}
	bare->complete = true;
	bare->fields.clear();
	bare->direct_bases.clear();
	bare->direct_base_offsets.clear();
	bare->direct_base_virtuals.clear();
	bare->virtual_bases.clear();
	bare->virtual_base_offsets.clear();
	bare->direct_base_offset = 0;
	bare->record_size = size;
	bare->record_align = align;
	bare->nonvirtual_size = size;
	bare->nonvirtual_align = align;
	bare->layout_valid = true;
	bare->hosted_layout_synthesized = true;
	return true;
}

bool complete_hosted_empty_record_layout(TypePtr type, const string& primary)
{
	TypePtr bare = type.get() != NULL ? strip_cv(type) : TypePtr();
	if (bare.get() == NULL ||
	    bare->kind != TypeKind::Record ||
	    !bare->is_template_specialization ||
	    !scope_has_namespace_named(bare->scope, "std") ||
	    unqualified_template_primary_name(bare) != primary)
		return false;
	bare->complete = true;
	bare->fields.clear();
	bare->direct_bases.clear();
	bare->direct_base_offsets.clear();
	bare->direct_base_virtuals.clear();
	bare->virtual_bases.clear();
	bare->virtual_base_offsets.clear();
	bare->direct_base_offset = 0;
	bare->record_size = 1;
	bare->record_align = 1;
	bare->nonvirtual_size = 1;
	bare->nonvirtual_align = 1;
	bare->layout_valid = true;
	bare->hosted_layout_synthesized = true;
	return true;
}

void complete_hosted_synthesized_record_layout(TypePtr bare,
                                               uint64_t size,
                                               uint64_t align)
{
	bare->complete = true;
	bare->fields.clear();
	bare->direct_bases.clear();
	bare->direct_base_offsets.clear();
	bare->direct_base_virtuals.clear();
	bare->virtual_bases.clear();
	bare->virtual_base_offsets.clear();
	bare->direct_base_offset = 0;
	bare->record_size = size;
	bare->record_align = align;
	bare->nonvirtual_size = size;
	bare->nonvirtual_align = align;
	bare->layout_valid = true;
	bare->hosted_layout_synthesized = true;
}

uint64_t hosted_align_up(uint64_t value, uint64_t align)
{
	return align == 0 ? value : ((value + align - 1) / align) * align;
}

void sync_hosted_record_fields_from_scope(TypePtr bare)
{
	if (bare->scope == NULL)
		return;
	vector<Binding*> fields;
	for (size_t i = 0; i < bare->scope->binding_order.size(); ++i)
	{
		Binding* member = bare->scope->binding_order[i];
		if (member == NULL ||
		    member->kind != BindingKind::Variable ||
		    member->is_static_member ||
		    member->aliased_binding != NULL)
			continue;
		member->bit_offset = 0;
		member->is_bit_field = false;
		fields.push_back(member);
	}
	bare->fields = fields;
}

void set_hosted_record_layout_preserving_fields(TypePtr bare,
                                                uint64_t size,
                                                uint64_t align)
{
	bare->complete = true;
	sync_hosted_record_fields_from_scope(bare);
	bare->direct_base_offset = 0;
	bare->direct_base_offsets.assign(bare->direct_bases.size(), 0);
	bare->virtual_bases.clear();
	bare->virtual_base_offsets.clear();
	bare->record_size = size;
	bare->record_align = align;
	bare->nonvirtual_size = size;
	bare->nonvirtual_align = align;
	bare->layout_valid = true;
	bare->hosted_layout_synthesized = true;
}

bool hosted_type_size_align(TypePtr type, uint64_t& size, uint64_t& align)
{
	try
	{
		size = max<uint64_t>(uint64_t(1), type_size(type));
		align = max<uint64_t>(uint64_t(1), type_align(type));
		return true;
	}
	catch (const runtime_error&)
	{
		TypePtr bare = type.get() != NULL ? strip_cv(type) : TypePtr();
		if (bare.get() != NULL &&
		    (bare->is_dependent_typename ||
		     bare->kind == TypeKind::TemplateParameter ||
		     bare->kind == TypeKind::Pointer ||
		     bare->kind == TypeKind::LValueReference ||
		     bare->kind == TypeKind::RValueReference))
		{
			size = 8;
			align = 8;
			return true;
		}
	}
	return false;
}

bool complete_hosted_allocator_layout(TypePtr type)
{
	return complete_hosted_empty_record_layout(type, "allocator");
}

bool complete_hosted_hashtable_layout(TypePtr type)
{
	TypePtr bare = type.get() != NULL ? strip_cv(type) : TypePtr();
	if (bare.get() == NULL ||
	    bare->kind != TypeKind::Record ||
	    !bare->is_template_specialization ||
	    !scope_has_namespace_named(bare->scope, "std") ||
	    unqualified_template_primary_name(bare) != "_Hashtable")
		return false;
	if (!scope_has_nonstatic_variable(bare->scope, "_M_buckets") ||
	    !scope_has_nonstatic_variable(bare->scope, "_M_bucket_count"))
		return false;
	bare->complete = true;
	bare->direct_base_offset = 0;
	bare->direct_base_offsets.assign(bare->direct_bases.size(), 0);
	bare->virtual_bases.clear();
	bare->virtual_base_offsets.clear();
	bare->record_size = 56;
	bare->record_align = 8;
	bare->nonvirtual_size = 56;
	bare->nonvirtual_align = 8;
	bare->layout_valid = true;
	bare->hosted_layout_synthesized = true;
	set_scope_variable_offset(bare->scope, "_M_buckets", 0);
	set_scope_variable_offset(bare->scope, "_M_bucket_count", 8);
	set_scope_variable_offset(bare->scope, "_M_before_begin", 16);
	set_scope_variable_offset(bare->scope, "_M_element_count", 24);
	set_scope_variable_offset(bare->scope, "_M_rehash_policy", 32);
	set_scope_variable_offset(bare->scope, "_M_single_bucket", 48);
	return true;
}

bool complete_hosted_hashtable_empty_policy_layout(TypePtr type)
{
	TypePtr bare = type.get() != NULL ? strip_cv(type) : TypePtr();
	if (bare.get() == NULL ||
	    bare->kind != TypeKind::Record ||
	    !bare->is_template_specialization ||
	    !scope_has_namespace_named(bare->scope, "std"))
		return false;
	string primary = unqualified_template_primary_name(bare);
	if (primary != "_Rehash_base" &&
	    primary != "_Map_base" &&
	    primary != "_Insert" &&
	    primary != "_Equality")
		return false;
	complete_hosted_synthesized_record_layout(bare, 1, 1);
	return true;
}

bool complete_hosted_hashtable_alloc_node_layout(TypePtr type)
{
	TypePtr bare = type.get() != NULL ? strip_cv(type) : TypePtr();
	if (bare.get() == NULL ||
	    bare->kind != TypeKind::Record ||
	    !bare->is_template_specialization ||
	    !scope_has_namespace_named(bare->scope, "std"))
		return false;
	string primary = unqualified_template_primary_name(bare);
	if (primary == "_AllocNode")
		complete_hosted_synthesized_record_layout(bare, 8, 8);
	else if (primary == "_ReuseOrAllocNode")
		complete_hosted_synthesized_record_layout(bare, 16, 8);
	else
		return false;
	return true;
}

bool complete_hosted_uninit_destroy_guard_layout(TypePtr type)
{
	TypePtr bare = type.get() != NULL ? strip_cv(type) : TypePtr();
	if (bare.get() == NULL ||
	    bare->kind != TypeKind::Record ||
	    !bare->is_template_specialization ||
	    !scope_has_namespace_named(bare->scope, "std") ||
	    unqualified_template_primary_name(bare) != "_UninitDestroyGuard")
		return false;
	TypePtr iterator_type;
	if (!bare->template_arguments.empty() &&
	    bare->template_arguments[0].kind == TemplateInstanceArgumentKind::Type)
		iterator_type = bare->template_arguments[0].type;
	uint64_t iterator_size = 8;
	uint64_t iterator_align = 8;
	if (iterator_type.get() != NULL &&
	    !is_dependent_typename_type(iterator_type))
	{
		iterator_size = max<uint64_t>(uint64_t(1), type_size(iterator_type));
		iterator_align = max<uint64_t>(uint64_t(1), type_align(iterator_type));
	}
	bool has_allocator = true;
	if (bare->template_arguments.size() > 1 &&
	    bare->template_arguments[1].kind == TemplateInstanceArgumentKind::Type)
	{
		TypePtr allocator_type = bare->template_arguments[1].type;
		has_allocator =
			allocator_type.get() == NULL ||
			!is_void_type(strip_cv(allocator_type));
	}
	uint64_t align = max<uint64_t>(iterator_align, uint64_t(8));
	uint64_t size = iterator_size;
	size = (size + 7) & ~uint64_t(7);
	size += 8;
	if (has_allocator)
		size += 8;
	size = (size + align - 1) / align * align;
	complete_hosted_synthesized_record_layout(bare, size, align);
	return true;
}

struct HostedStreamLayout
{
	uint64_t size;
	uint64_t nonvirtual_size;
	uint64_t basic_ios_offset;
	uint64_t stringbuf_offset;

	HostedStreamLayout()
		: size(0),
		  nonvirtual_size(0),
		  basic_ios_offset(static_cast<uint64_t>(-1)),
		  stringbuf_offset(static_cast<uint64_t>(-1))
	{
	}
};

bool hosted_stream_record_layout(TypePtr type, HostedStreamLayout& layout)
{
	TypePtr bare = type.get() != NULL ? strip_cv(type) : TypePtr();
	if (bare.get() == NULL ||
	    bare->kind != TypeKind::Record ||
	    !scope_has_namespace_named(bare->scope, "std"))
		return false;
	string primary = unqualified_template_primary_name(bare);
	if (primary == "ios_base")
		layout.size = layout.nonvirtual_size = 216;
	else if (primary == "basic_ios")
		layout.size = layout.nonvirtual_size = 264;
	else if (primary == "basic_streambuf")
		layout.size = layout.nonvirtual_size = 64;
	else if (primary == "basic_ostream")
		layout.size = 272, layout.nonvirtual_size = 8,
		layout.basic_ios_offset = 8;
	else if (primary == "basic_istream")
		layout.size = 280, layout.nonvirtual_size = 16,
		layout.basic_ios_offset = 16;
	else if (primary == "basic_iostream")
		layout.size = 288, layout.nonvirtual_size = 24,
		layout.basic_ios_offset = 24;
	else if (primary == "basic_stringbuf")
		layout.size = layout.nonvirtual_size = 104;
	else if (primary == "basic_ostringstream")
		layout.size = 376, layout.nonvirtual_size = 112,
		layout.basic_ios_offset = 112, layout.stringbuf_offset = 8;
	else if (primary == "basic_istringstream")
		layout.size = 384, layout.nonvirtual_size = 120,
		layout.basic_ios_offset = 120, layout.stringbuf_offset = 16;
	else if (primary == "basic_stringstream")
		layout.size = 392, layout.nonvirtual_size = 128,
		layout.basic_ios_offset = 128, layout.stringbuf_offset = 24;
	else
		return false;
	return true;
}

bool type_primary_is(TypePtr type, const string& name)
{
	TypePtr bare = type.get() != NULL ? strip_cv(type) : TypePtr();
	return bare.get() != NULL &&
	       bare->kind == TypeKind::Record &&
	       unqualified_template_primary_name(bare) == name;
}

void set_direct_base_offset_by_primary(TypePtr record,
                                       const string& primary,
                                       uint64_t offset)
{
	TypePtr bare = strip_cv(record);
	for (size_t i = 0; i < bare->direct_bases.size(); ++i)
		if (type_primary_is(bare->direct_bases[i], primary) &&
		    i < bare->direct_base_offsets.size())
			bare->direct_base_offsets[i] = offset;
}

void set_virtual_base_offset_by_primary(TypePtr record,
                                        const string& primary,
                                        uint64_t offset)
{
	TypePtr bare = strip_cv(record);
	for (size_t i = 0; i < bare->virtual_bases.size(); ++i)
		if (type_primary_is(bare->virtual_bases[i], primary) &&
		    i < bare->virtual_base_offsets.size())
			bare->virtual_base_offsets[i] = offset;
}

bool complete_hosted_pair_layout(TypePtr type)
{
	TypePtr bare = type.get() != NULL ? strip_cv(type) : TypePtr();
	if (bare.get() == NULL ||
	    bare->kind != TypeKind::Record ||
	    !bare->is_template_specialization ||
	    !scope_has_namespace_named(bare->scope, "std") ||
	    unqualified_template_primary_name(bare) != "pair" ||
	    bare->template_arguments.size() < 2 ||
	    bare->template_arguments[0].kind != TemplateInstanceArgumentKind::Type ||
	    bare->template_arguments[1].kind != TemplateInstanceArgumentKind::Type)
		return false;
	uint64_t first_size = 1;
	uint64_t first_align = 1;
	uint64_t second_size = 1;
	uint64_t second_align = 1;
	if (!hosted_type_size_align(bare->template_arguments[0].type,
	                            first_size,
	                            first_align) ||
	    !hosted_type_size_align(bare->template_arguments[1].type,
	                            second_size,
	                            second_align))
		return false;
	uint64_t second_offset = hosted_align_up(first_size, second_align);
	uint64_t align = max(first_align, second_align);
	uint64_t size = hosted_align_up(second_offset + second_size, align);
	set_hosted_record_layout_preserving_fields(bare, size, align);
	set_scope_variable_offset(bare->scope, "first", 0);
	set_scope_variable_offset(bare->scope, "second", second_offset);
	return true;
}

bool complete_hosted_rbtree_layout(TypePtr type)
{
	TypePtr bare = type.get() != NULL ? strip_cv(type) : TypePtr();
	if (bare.get() == NULL ||
	    bare->kind != TypeKind::Record ||
	    !scope_has_namespace_named(bare->scope, "std"))
		return false;
	string primary = unqualified_template_primary_name(bare);
	if (primary == "_Rb_tree_node_base")
	{
		set_hosted_record_layout_preserving_fields(bare, 32, 8);
		set_scope_variable_offset(bare->scope, "_M_color", 0);
		set_scope_variable_offset(bare->scope, "_M_parent", 8);
		set_scope_variable_offset(bare->scope, "_M_left", 16);
		set_scope_variable_offset(bare->scope, "_M_right", 24);
		return true;
	}
	if (primary == "_Rb_tree_header")
	{
		set_hosted_record_layout_preserving_fields(bare, 40, 8);
		set_scope_variable_offset(bare->scope, "_M_header", 0);
		set_scope_variable_offset(bare->scope, "_M_node_count", 32);
		return true;
	}
	if (primary == "_Rb_tree_impl")
	{
		set_hosted_record_layout_preserving_fields(bare, 48, 8);
		set_direct_base_offset_by_primary(bare, "_Rb_tree_key_compare", 0);
		set_direct_base_offset_by_primary(bare, "_Rb_tree_header", 8);
		set_scope_variable_offset(bare->scope, "_M_key_compare", 0);
		set_scope_variable_offset(bare->scope, "_M_header", 8);
		set_scope_variable_offset(bare->scope, "_M_node_count", 40);
		return true;
	}
	if (primary == "_Rb_tree")
	{
		set_hosted_record_layout_preserving_fields(bare, 48, 8);
		set_scope_variable_offset(bare->scope, "_M_impl", 0);
		return true;
	}
	if (primary == "_Rb_tree_node")
	{
		uint64_t value_size = 1;
		uint64_t value_align = 1;
		if (!bare->template_arguments.empty() &&
		    bare->template_arguments[0].kind ==
			    TemplateInstanceArgumentKind::Type)
			hosted_type_size_align(bare->template_arguments[0].type,
			                       value_size,
			                       value_align);
		uint64_t align = max<uint64_t>(uint64_t(8), value_align);
		uint64_t storage_offset = hosted_align_up(uint64_t(32), value_align);
		uint64_t size = hosted_align_up(storage_offset + value_size, align);
		set_hosted_record_layout_preserving_fields(bare, size, align);
		set_scope_variable_offset(bare->scope, "_M_storage", storage_offset);
		set_scope_variable_offset(bare->scope, "_M_value_field",
		                          storage_offset);
		return true;
	}
	return false;
}

bool hosted_basic_string_record(TypePtr type)
{
	TypePtr bare = type.get() != NULL ? strip_cv(type) : TypePtr();
	return bare.get() != NULL &&
	       bare->kind == TypeKind::Record &&
	       bare->is_template_specialization &&
	       scope_has_namespace_named(bare->scope, "std") &&
	       unqualified_template_primary_name(bare) == "basic_string";
}

Binding* anonymous_alias_target(Binding* binding)
{
	if (binding == NULL ||
	    binding->aliased_binding == NULL ||
	    binding->target_scope == NULL)
		return NULL;
	map<string, vector<Binding*> >::iterator found =
		binding->target_scope->members.find(binding->name);
	if (found == binding->target_scope->members.end())
		return NULL;
	for (size_t i = 0; i < found->second.size(); ++i)
		if (found->second[i]->kind == BindingKind::Variable &&
		    !found->second[i]->is_static_member)
			return found->second[i];
	return NULL;
}

}  // namespace

bool complete_hosted_record_layout(TypePtr type)
{
	return complete_hosted_shared_ptr_layout(type) ||
	       complete_hosted_pair_layout(type) ||
	       complete_hosted_rbtree_layout(type) ||
	       complete_hosted_hashtable_layout(type) ||
	       complete_hosted_hashtable_ebo_helper_layout(type) ||
	       complete_hosted_allocator_layout(type) ||
	       complete_hosted_hashtable_empty_policy_layout(type) ||
	       complete_hosted_hashtable_alloc_node_layout(type) ||
	       complete_hosted_uninit_destroy_guard_layout(type);
}

void propagate_anonymous_alias_member_offsets(TypePtr type)
{
	TypePtr bare = type.get() != NULL ? strip_cv(type) : TypePtr();
	if (bare.get() == NULL || bare->scope == NULL)
		return;
	for (size_t i = 0; i < bare->scope->binding_order.size(); ++i)
	{
		Binding* binding = bare->scope->binding_order[i];
		Binding* target = anonymous_alias_target(binding);
		if (target == NULL)
			continue;
		binding->member_offset =
			binding->aliased_binding->member_offset + target->member_offset;
		binding->bit_offset = target->bit_offset;
		binding->is_bit_field = target->is_bit_field;
		binding->bit_width = target->bit_width;
	}
}

void adjust_hosted_stream_layout(TypePtr type)
{
	HostedStreamLayout layout;
	if (!hosted_stream_record_layout(type, layout))
		return;
	TypePtr bare = strip_cv(type);
	bare->record_align = max<uint64_t>(bare->record_align, 8);
	bare->nonvirtual_align = max<uint64_t>(bare->nonvirtual_align, 8);
	bare->record_size = layout.size;
	bare->nonvirtual_size = layout.nonvirtual_size;
	string primary = unqualified_template_primary_name(bare);
	if (primary == "basic_iostream" || primary == "basic_stringstream")
		set_direct_base_offset_by_primary(bare, "basic_ostream", 16);
	if (layout.basic_ios_offset != static_cast<uint64_t>(-1))
	{
		set_direct_base_offset_by_primary(bare,
		                                  "basic_ios",
		                                  layout.basic_ios_offset);
		set_virtual_base_offset_by_primary(bare,
		                                   "basic_ios",
		                                   layout.basic_ios_offset);
	}
	if (layout.stringbuf_offset != static_cast<uint64_t>(-1))
		set_scope_variable_offset(bare->scope,
		                          "_M_stringbuf",
		                          layout.stringbuf_offset);
}

void adjust_hosted_basic_string_layout(TypePtr type)
{
	if (!hosted_basic_string_record(type))
		return;
	TypePtr bare = strip_cv(type);
	bare->record_align = max<uint64_t>(bare->record_align, 8);
	bare->nonvirtual_align = max<uint64_t>(bare->nonvirtual_align, 8);
	for (size_t i = 0; bare->scope != NULL &&
	     i < bare->scope->binding_order.size(); ++i)
	{
		Binding* field = bare->scope->binding_order[i];
		if (field->kind != BindingKind::Variable ||
		    field->is_static_member)
			continue;
		if (field->name == "_M_dataplus")
			field->member_offset = 0;
		else if (field->name == "_M_string_length")
			field->member_offset = 8;
		else if (field->name.find("__anonymous_union_storage__") == 0)
			field->member_offset = 16;
	}
	set_scope_variable_offset(bare->scope, "_M_dataplus", 0);
	set_scope_variable_offset(bare->scope, "_M_string_length", 8);
	set_scope_variable_offset(bare->scope, "_M_local_buf", 16);
	set_scope_variable_offset(bare->scope, "_M_allocated_capacity", 16);
	set_scope_variable_offset_by_prefix(bare->scope,
	                                    "__anonymous_union_storage__",
	                                    16);
	propagate_anonymous_alias_member_offsets(bare);
	if (bare->record_size < 32)
		bare->record_size = 32;
	if (bare->nonvirtual_size < 32)
		bare->nonvirtual_size = 32;
}

bool layout_hosted_basic_string_record(TypePtr type)
{
	if (!hosted_basic_string_record(type))
		return false;
	TypePtr bare = strip_cv(type);
	bare->fields.clear();
	bare->direct_base_offsets.clear();
	bare->virtual_bases.clear();
	bare->virtual_base_offsets.clear();
	bare->direct_base_offset = 0;
	if (bare->scope != NULL)
	{
		for (size_t i = 0; i < bare->scope->binding_order.size(); ++i)
		{
			Binding* field = bare->scope->binding_order[i];
			if (field->kind != BindingKind::Variable ||
			    field->is_static_member ||
			    field->aliased_binding != NULL)
				continue;
			field->bit_offset = 0;
			field->is_bit_field = false;
			if (field->name == "_M_dataplus")
				field->member_offset = 0;
			else if (field->name == "_M_string_length")
				field->member_offset = 8;
			else if (field->name.find("__anonymous_union_storage__") == 0)
				field->member_offset = 16;
			else
				continue;
			bare->fields.push_back(field);
		}
	}
	bare->record_size = 32;
	bare->record_align = 8;
	bare->nonvirtual_size = 32;
	bare->nonvirtual_align = 8;
	adjust_hosted_basic_string_layout(bare);
	bare->layout_valid = true;
	return true;
}

}  // namespace pa11
