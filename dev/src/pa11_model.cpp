#include "pa11_internal.h"

#include <algorithm>
#include <sstream>
#include <stdexcept>
#include <utility>

using namespace std;

namespace pa11 {
namespace {

TypePtr new_type(TypeKind kind)
{
	return TypePtr(new Type(kind));
}

uint64_t fundamental_size(EFundamentalType type)
{
	switch (type)
	{
	case FT_SIGNED_CHAR:
	case FT_UNSIGNED_CHAR:
	case FT_CHAR:
	case FT_BOOL:
		return 1;
	case FT_SHORT_INT:
	case FT_UNSIGNED_SHORT_INT:
	case FT_CHAR16_T:
		return 2;
	case FT_INT:
	case FT_UNSIGNED_INT:
	case FT_WCHAR_T:
	case FT_CHAR32_T:
	case FT_FLOAT:
		return 4;
	case FT_LONG_INT:
	case FT_LONG_LONG_INT:
	case FT_UNSIGNED_LONG_INT:
	case FT_UNSIGNED_LONG_LONG_INT:
	case FT_DOUBLE:
	case FT_NULLPTR_T:
		return 8;
	case FT_INT128:
	case FT_UNSIGNED_INT128:
	case FT_LONG_DOUBLE:
		return 16;
	case FT_VOID:
		break;
	}
	throw runtime_error("incomplete object type");
}

bool same_function_type(const TypePtr& left, const TypePtr& right)
{
	if (left->ref_qualifier != right->ref_qualifier ||
	    left->variadic != right->variadic ||
	    left->parameters.size() != right->parameters.size() ||
	    !same_type(left->base, right->base))
		return false;
	for (size_t i = 0; i < left->parameters.size(); ++i)
	{
		if (!same_type(left->parameters[i], right->parameters[i]))
			return false;
	}
	return true;
}

string join_parameter_types(const vector<TypePtr>& parameters, bool variadic)
{
	ostringstream out;
	for (size_t i = 0; i < parameters.size(); ++i)
	{
		if (i != 0)
			out << ", ";
		out << describe_type(parameters[i]);
	}
	if (variadic)
	{
		if (!parameters.empty())
			out << ", ";
		out << "...";
	}
	return out.str();
}

bool lookup_seen_insert(set<Scope*>& seen, Scope* scope)
{
	return scope != NULL && seen.insert(scope).second;
}

Binding* lookup_in_scope(Scope* scope,
                         const string& name,
                         int mask,
                         set<Scope*>& seen)
{
	if (!lookup_seen_insert(seen, scope))
		return NULL;
	map<string, vector<Binding*> >::iterator it = scope->members.find(name);
	if (it != scope->members.end())
	{
		for (size_t i = 0; i < it->second.size(); ++i)
		{
			if (binding_matches(it->second[i], mask))
				return it->second[i];
		}
	}
	for (size_t i = 0; i < scope->using_directives.size(); ++i)
	{
		Binding* found = lookup_in_scope(scope->using_directives[i],
		                                 name,
		                                 mask,
		                                 seen);
		if (found != NULL)
			return found;
	}
	TypePtr record = record_type_for_scope(scope);
	vector<TypePtr> bases = record.get() != NULL
		? record_direct_bases(record) : vector<TypePtr>();
	for (size_t i = 0; i < bases.size(); ++i)
	{
		TypePtr base = bases[i].get() != NULL ? strip_cv(bases[i]) : TypePtr();
		if (base.get() != NULL && base->kind == TypeKind::Record &&
		    base->scope != NULL)
		{
			Binding* found = lookup_in_scope(base->scope, name, mask, seen);
			if (found != NULL)
				return found;
		}
	}
	return NULL;
}

}  // namespace

Type::Type(TypeKind k)
	: kind(k),
	  fundamental(FT_INT),
	  cv(CV_NONE),
	  ref_qualifier(0),
	  member_class(),
	  unknown_bound(false),
	  bound(0),
	  variadic(false),
	  scoped_enum(false),
	  complete(true),
	  is_template_specialization(false),
	  is_dependent_typename(false),
	  dependent_typename_qualified(false),
	  dependent_typename_template_id(false),
	  dependent_typename_decltype(false),
	  enum_underlying(FT_INT),
	  scope(NULL),
	  record_size(0),
	  record_align(1),
	  record_forced_align(0),
	  nonvirtual_size(0),
	  nonvirtual_align(1),
	  direct_base_offset(0),
	  direct_base_virtuals(),
	  layout_valid(false),
	  is_polymorphic(false),
	  introduces_vptr(false)
{
}

Binding::Binding(BindingKind k, const string& n, Scope* o)
	: kind(k),
	  name(n),
	  owner(o),
	  target_scope(NULL),
	  aliased_binding(NULL),
	  language_linkage("cpp"),
	  has_constant(false),
	  constant_value(0),
	  is_constexpr(false),
	  is_static_member(false),
	  is_local_static(false),
	  is_namespace_static(false),
	  local_static_function_owner(NULL),
	  is_inline_definition(false),
	  is_generated_default_constructor(false),
	  is_generated_aggregate_constructor(false),
	  is_generated_copy_move_constructor(false),
	  is_generated_copy_move_assignment(false),
		  is_generated_default_destructor(false),
		  is_defaulted(false),
		  is_explicit(false),
		  has_default_arguments(false),
		  is_private(false),
	  is_protected_member(false),
	  is_mutable_member(false),
	  is_reference_member(false),
	  is_hidden_friend(false),
	  is_thread_local(false),
	  is_object_root(false),
	  is_dependent_template_artifact(false),
	  is_template_static_member_definition(false),
	  is_template_static_member_explicit_definition(false),
	  reserve_primary_function_symbol(false),
	  is_virtual(false),
	  is_override_specified(false),
	  is_final_virtual(false),
	  is_pure_virtual(false),
	  overrides_virtual(NULL),
	  virtual_slot_index(-1),
	  virtual_slot_width(0),
	  unwind_no(false),
	  ref_qualifier(0),
	  is_noop_constructor(false),
	  is_noop_destructor(false),
	  is_cleanup_only_destructor(false),
	  member_offset(0),
	  is_bit_field(false),
	  bit_width(0),
	  bit_offset(0)
{
}

Scope::Scope(ScopeKind k, const string& n, Scope* p)
	: kind(k),
	  name(n),
	  parent(p),
	  unnamed_namespace(NULL),
	  is_inline_namespace(false)
{
}

TranslationUnit::TranslationUnit() : anonymous_counter(0)
{
}

VirtualTableEntry::VirtualTableEntry()
	: function(NULL), deleting_entry(false)
{
}

VirtualTableEntry::VirtualTableEntry(Binding* f, bool d)
	: function(f), deleting_entry(d)
{
}

TemplateInstanceArgument::TemplateInstanceArgument()
	: kind(TemplateInstanceArgumentKind::Type),
	  value_expr_begin(0),
	  value_expr_end(0),
	  value(0),
	  dependent(false),
	  value_negated(false)
{
}

TemplateInstanceArgument TemplateInstanceArgument::type_arg(TypePtr type)
{
	TemplateInstanceArgument arg;
	arg.kind = TemplateInstanceArgumentKind::Type;
	arg.type = type;
	return arg;
}

TemplateInstanceArgument TemplateInstanceArgument::value_arg(TypePtr type,
                                                             uint64_t value)
{
	TemplateInstanceArgument arg;
	arg.kind = TemplateInstanceArgumentKind::Value;
	arg.type = type;
	arg.value = value;
	return arg;
}

TemplateInstanceArgument TemplateInstanceArgument::dependent_value_arg(
	TypePtr type)
{
	TemplateInstanceArgument arg;
	arg.kind = TemplateInstanceArgumentKind::Value;
	arg.type = type;
	arg.dependent = true;
	return arg;
}

TemplateInstanceArgument TemplateInstanceArgument::template_arg(
	const string& name)
{
	TemplateInstanceArgument arg;
	arg.kind = TemplateInstanceArgumentKind::Template;
	arg.template_name = name;
	return arg;
}

TemplateInstanceArgument TemplateInstanceArgument::pack_arg(
	const vector<TemplateInstanceArgument>& values)
{
	TemplateInstanceArgument arg;
	arg.kind = TemplateInstanceArgumentKind::Pack;
	arg.pack = values;
	return arg;
}

TypePtr make_fundamental(EFundamentalType fundamental)
{
	TypePtr type = new_type(TypeKind::Fundamental);
	type->fundamental = fundamental;
	return type;
}

TypePtr make_cv(TypePtr base, unsigned cv)
{
	if (cv == CV_NONE)
		return base;
	if (is_reference_type(base) || base->kind == TypeKind::Function)
		return base;
	if (base->kind == TypeKind::Array)
		return make_array(make_cv(base->base, cv),
		                  base->unknown_bound,
		                  base->bound);
	if (base->kind == TypeKind::Cv)
	{
		TypePtr type = new_type(TypeKind::Cv);
		type->cv = base->cv | cv;
		type->base = base->base;
		return type;
	}
	TypePtr type = new_type(TypeKind::Cv);
	type->cv = cv;
	type->base = base;
	return type;
}

TypePtr make_pointer(TypePtr base)
{
	if (is_reference_type(base))
		throw runtime_error("invalid pointer to reference");
	TypePtr type = new_type(TypeKind::Pointer);
	type->base = base;
	return type;
}

TypePtr make_lvalue_reference(TypePtr base)
{
	if (is_reference_type(base) || is_void_type(base))
		throw runtime_error("invalid reference type");
	TypePtr type = new_type(TypeKind::LValueReference);
	type->base = base;
	return type;
}

TypePtr make_rvalue_reference(TypePtr base)
{
	if (is_reference_type(base) || is_void_type(base))
		throw runtime_error("invalid reference type");
	TypePtr type = new_type(TypeKind::RValueReference);
	type->base = base;
	return type;
}

TypePtr make_array(TypePtr element, bool unknown, uint64_t bound)
{
	if (is_void_type(element) ||
	    element->kind == TypeKind::Function ||
	    is_reference_type(element))
		throw runtime_error("invalid array element type");
	TypePtr type = new_type(TypeKind::Array);
	type->base = element;
	type->unknown_bound = unknown;
	type->bound = bound;
	return type;
}

TypePtr make_function(TypePtr result,
                      const vector<TypePtr>& parameters,
                      bool variadic)
{
	vector<TypePtr> normalized = parameters;
	if (!variadic && normalized.size() == 1 && is_void_type(normalized[0]))
		normalized.clear();
	TypePtr type = new_type(TypeKind::Function);
	type->base = result;
	type->parameters = normalized;
	type->variadic = variadic;
	return type;
}

TypePtr make_member_pointer(TypePtr class_type, TypePtr member_type)
{
	TypePtr bare = strip_cv(class_type);
	if (bare->kind != TypeKind::Record &&
	    bare->kind != TypeKind::TemplateParameter &&
	    !bare->is_dependent_typename)
		throw runtime_error("member pointer class type is not a record");
	TypePtr type = new_type(TypeKind::MemberPointer);
	type->member_class = bare;
	type->base = member_type;
	return type;
}

TypePtr make_record_type(const string& name,
                         const string& tag,
                         bool complete,
                         Scope* scope)
{
	TypePtr type = new_type(TypeKind::Record);
	type->name = name;
	type->tag = tag;
	type->complete = complete;
	type->scope = scope;
	return type;
}

TypePtr make_enum_type(const string& name,
                       bool scoped,
                       EFundamentalType underlying,
                       bool complete,
                       Scope* scope)
{
	TypePtr type = new_type(TypeKind::Enum);
	type->name = name;
	type->scoped_enum = scoped;
	type->enum_underlying = underlying;
	type->complete = complete;
	type->scope = scope;
	return type;
}

TypePtr make_template_parameter_type(const string& name)
{
	TypePtr type = new_type(TypeKind::TemplateParameter);
	type->name = name;
	return type;
}

TypePtr make_dependent_typename_type(const string& name,
                                     bool qualified,
                                     bool template_id,
                                     bool decltype_id)
{
	TypePtr type = make_template_parameter_type(name);
	type->is_dependent_typename = true;
	type->dependent_typename_qualified = qualified;
	type->dependent_typename_template_id = template_id;
	type->dependent_typename_decltype = decltype_id;
	return type;
}

TypePtr make_template_template_parameter_type(const string& name)
{
	TypePtr type = new_type(TypeKind::TemplateTemplateParameter);
	type->name = name;
	return type;
}

bool is_deducible_template_parameter_type(const TypePtr& type)
{
	return type.get() != NULL &&
	       type->kind == TypeKind::TemplateParameter &&
	       !type->is_dependent_typename;
}

bool is_dependent_typename_type(const TypePtr& type)
{
	return type.get() != NULL &&
	       type->kind == TypeKind::TemplateParameter &&
	       type->is_dependent_typename;
}

TypePtr strip_top_level_cv(TypePtr type)
{
	if (type->kind == TypeKind::Cv)
		return type->base;
	return type;
}

TypePtr strip_cv(TypePtr type)
{
	while (type->kind == TypeKind::Cv)
		type = type->base;
	return type;
}

bool type_has_const(const TypePtr& type)
{
	if (type->kind == TypeKind::Cv)
		return (type->cv & CV_CONST) != 0 || type_has_const(type->base);
	if (type->kind == TypeKind::Array)
		return type_has_const(type->base);
	return false;
}

bool is_void_type(const TypePtr& type)
{
	TypePtr bare = strip_cv(type);
	return bare->kind == TypeKind::Fundamental && bare->fundamental == FT_VOID;
}

bool is_reference_type(const TypePtr& type)
{
	return type->kind == TypeKind::LValueReference ||
	       type->kind == TypeKind::RValueReference;
}

bool is_integral_or_bool_type(const TypePtr& type)
{
	TypePtr bare = strip_cv(type);
	if (bare->kind == TypeKind::Enum)
		return true;
	if (bare->kind != TypeKind::Fundamental)
		return false;
	switch (bare->fundamental)
	{
	case FT_SIGNED_CHAR:
	case FT_SHORT_INT:
	case FT_INT:
	case FT_LONG_INT:
	case FT_LONG_LONG_INT:
	case FT_INT128:
	case FT_UNSIGNED_CHAR:
	case FT_UNSIGNED_SHORT_INT:
	case FT_UNSIGNED_INT:
	case FT_UNSIGNED_LONG_INT:
	case FT_UNSIGNED_LONG_LONG_INT:
	case FT_UNSIGNED_INT128:
	case FT_WCHAR_T:
	case FT_CHAR:
	case FT_CHAR16_T:
	case FT_CHAR32_T:
	case FT_BOOL:
		return true;
	default:
		return false;
	}
}

bool same_type(const TypePtr& left, const TypePtr& right)
{
	if (left->kind != right->kind)
		return false;
	if (left->kind == TypeKind::Fundamental)
		return left->fundamental == right->fundamental;
	if (left->kind == TypeKind::Cv)
		return left->cv == right->cv && same_type(left->base, right->base);
	if (left->kind == TypeKind::Array)
		return left->unknown_bound == right->unknown_bound &&
		       left->bound == right->bound &&
		       same_type(left->base, right->base);
	if (left->kind == TypeKind::Function)
		return left->cv == right->cv && same_function_type(left, right);
	if (left->kind == TypeKind::MemberPointer)
		return same_type(left->member_class, right->member_class) &&
		       same_type(left->base, right->base);
	if (left->kind == TypeKind::Record ||
	    left->kind == TypeKind::Enum ||
	    left->kind == TypeKind::TemplateParameter ||
	    left->kind == TypeKind::TemplateTemplateParameter)
		return left->name == right->name && left->scope == right->scope;
	return same_type(left->base, right->base);
}

string describe_type(const TypePtr& type)
{
	switch (type->kind)
	{
	case TypeKind::Fundamental:
		return FundamentalTypeToStringMap.at(type->fundamental);
	case TypeKind::Cv:
		if (type->cv == (CV_CONST | CV_VOLATILE))
			return "const volatile " + describe_type(type->base);
		if (type->cv == CV_CONST)
			return "const " + describe_type(type->base);
		return "volatile " + describe_type(type->base);
	case TypeKind::Pointer:
		return "pointer to " + describe_type(type->base);
	case TypeKind::LValueReference:
		return "lvalue-reference to " + describe_type(type->base);
	case TypeKind::RValueReference:
		return "rvalue-reference to " + describe_type(type->base);
	case TypeKind::Array:
		if (type->unknown_bound)
			return "array of unknown bound of " + describe_type(type->base);
		return "array of " + to_string(type->bound) + " " +
		       describe_type(type->base);
	case TypeKind::Function:
		return "function of (" +
		       join_parameter_types(type->parameters, type->variadic) +
		       ")" +
		       (type->cv == CV_CONST ? " const" :
		        (type->cv == CV_VOLATILE ? " volatile" :
		         (type->cv == (CV_CONST | CV_VOLATILE) ?
		          " const volatile" : ""))) +
		       (type->ref_qualifier == 1 ? " &" :
		        (type->ref_qualifier == 2 ? " &&" : "")) +
		       " returning " + describe_type(type->base);
	case TypeKind::MemberPointer:
		return "member-pointer of " + describe_type(type->member_class) +
		       " to " + describe_type(type->base);
	case TypeKind::Record:
		return type->tag + " " + type->name;
	case TypeKind::Enum:
		return string(type->scoped_enum ? "enum class " : "enum ") +
		       type->name;
	case TypeKind::TemplateParameter:
		return "typename " + type->name;
	case TypeKind::TemplateTemplateParameter:
		return "template-parameter " + type->name;
	}
	throw logic_error("unknown type kind");
}

uint64_t type_size(const TypePtr& type)
{
	TypePtr bare = strip_cv(type);
	if (bare->kind == TypeKind::Fundamental)
		return fundamental_size(bare->fundamental);
	if (bare->kind == TypeKind::Pointer || is_reference_type(bare))
		return 8;
	if (bare->kind == TypeKind::MemberPointer)
		return strip_cv(bare->base)->kind == TypeKind::Function ? 16 : 8;
	if (bare->kind == TypeKind::Array)
	{
		if (bare->unknown_bound)
			throw runtime_error("incomplete array type");
		return bare->bound * type_size(bare->base);
	}
	if (bare->kind == TypeKind::Enum)
		return fundamental_size(bare->enum_underlying);
	if (bare->kind == TypeKind::Record)
	{
		if (!bare->complete)
			throw runtime_error("incomplete class type");
		if (!bare->layout_valid)
			layout_record_type(bare);
		return bare->record_size;
	}
	throw runtime_error("incomplete object type");
}

uint64_t type_align(const TypePtr& type)
{
	TypePtr bare = strip_cv(type);
	if (bare->kind == TypeKind::Array)
		return type_align(bare->base);
	if (bare->kind == TypeKind::Record)
	{
		if (!bare->complete)
			throw runtime_error("incomplete class type");
		if (!bare->layout_valid)
			layout_record_type(bare);
		return bare->record_align;
	}
	if (bare->kind == TypeKind::MemberPointer)
		return 8;
	return type_size(bare);
}

namespace {

bool record_uses_object_storage(TypePtr type)
{
	TypePtr bare = strip_cv(type);
	if (bare->kind != TypeKind::Record)
		return false;
	if (bare->is_polymorphic)
		return true;
	if (!bare->fields.empty())
		return true;
	vector<TypePtr> bases = bare->direct_bases;
	if (bases.empty() && bare->base.get() != NULL)
		bases.push_back(bare->base);
	for (size_t i = 0; i < bases.size(); ++i)
		if (bases[i].get() != NULL && record_uses_object_storage(bases[i]))
			return true;
	return false;
}

}  // namespace

static bool direct_base_is_virtual(TypePtr record, size_t index)
{
	TypePtr bare = strip_cv(record);
	return index < bare->direct_base_virtuals.size() &&
	       bare->direct_base_virtuals[index];
}

static uint64_t align_up(uint64_t offset, uint64_t align)
{
	if (align == 0)
		align = 1;
	uint64_t padding = offset % align;
	return padding == 0 ? offset : offset + align - padding;
}

static bool type_vector_contains(const vector<TypePtr>& types, TypePtr type)
{
	TypePtr wanted = strip_cv(type);
	for (size_t i = 0; i < types.size(); ++i)
		if (types[i].get() != NULL &&
		    same_type(strip_cv(types[i]), wanted))
			return true;
	return false;
}

static void collect_record_virtual_bases(TypePtr record,
                                         vector<TypePtr>& out)
{
	TypePtr bare = record.get() != NULL ? strip_cv(record) : TypePtr();
	if (bare.get() == NULL || bare->kind != TypeKind::Record)
		return;
	vector<TypePtr> bases = record_direct_bases(bare);
	for (size_t i = 0; i < bases.size(); ++i)
	{
		TypePtr direct = bases[i].get() != NULL
			? strip_cv(bases[i]) : TypePtr();
		if (direct.get() == NULL || direct->kind != TypeKind::Record)
			continue;
		if (direct_base_is_virtual(bare, i) &&
		    !type_vector_contains(out, direct))
			out.push_back(direct);
		collect_record_virtual_bases(direct, out);
	}
}

static uint64_t record_nonvirtual_subobject_size(TypePtr type)
{
	TypePtr bare = strip_cv(type);
	layout_record_type(bare);
	uint64_t size = bare->nonvirtual_size != 0
		? bare->nonvirtual_size : bare->record_size;
	if (size == 0)
		size = 1;
	return align_up(size, bare->record_align);
}

static uint64_t record_virtual_subobject_size(TypePtr type)
{
	TypePtr bare = strip_cv(type);
	layout_record_type(bare);
	return bare->nonvirtual_size != 0 ? bare->nonvirtual_size : 1;
}

static uint64_t record_virtual_subobject_align(TypePtr type)
{
	TypePtr bare = strip_cv(type);
	layout_record_type(bare);
	return bare->nonvirtual_align != 0 ? bare->nonvirtual_align : 1;
}

static size_t primary_polymorphic_base_index(TypePtr record,
                                             const vector<TypePtr>& bases)
{
	for (size_t i = 0; i < bases.size(); ++i)
	{
		if (direct_base_is_virtual(record, i))
			continue;
		TypePtr base = bases[i].get() != NULL ? strip_cv(bases[i]) : TypePtr();
		if (base.get() != NULL &&
		    base->kind == TypeKind::Record &&
		    base->is_polymorphic)
			return i;
	}
	return static_cast<size_t>(-1);
}

struct RecordLayoutCursor
{
	uint64_t offset;
	uint64_t align;
	uint64_t nonvirtual_align;

	explicit RecordLayoutCursor(uint64_t forced_align)
		: offset(0),
		  align(max<uint64_t>(1, forced_align)),
		  nonvirtual_align(align)
	{
	}
};

static vector<size_t> direct_base_layout_order(size_t primary_base,
                                               size_t base_count)
{
	vector<size_t> layout_order;
	if (primary_base != static_cast<size_t>(-1))
		layout_order.push_back(primary_base);
	for (size_t b = 0; b < base_count; ++b)
		if (b != primary_base)
			layout_order.push_back(b);
	return layout_order;
}

static void layout_record_direct_bases(TypePtr bare,
                                       const vector<TypePtr>& direct_bases,
                                       size_t primary_base,
                                       bool introduces_vptr,
                                       RecordLayoutCursor& cursor)
{
	vector<size_t> layout_order =
		direct_base_layout_order(primary_base, direct_bases.size());
	for (size_t order_i = 0; order_i < layout_order.size(); ++order_i)
	{
		size_t b = layout_order[order_i];
		if (direct_base_is_virtual(bare, b))
			continue;
		TypePtr direct_base = direct_bases[b].get() != NULL
			? strip_cv(direct_bases[b]) : TypePtr();
		if (direct_base.get() == NULL || direct_base->kind != TypeKind::Record)
		{
			bare->direct_base_offsets[b] = 0;
			continue;
		}
		layout_record_type(direct_base);
		uint64_t base_align = type_align(direct_base);
		cursor.align = max<uint64_t>(cursor.align, base_align);
		cursor.nonvirtual_align =
			max<uint64_t>(cursor.nonvirtual_align, base_align);
		uint64_t base_offset = 0;
		if (b == 0 && introduces_vptr &&
		    record_uses_object_storage(direct_base))
		{
			cursor.offset = 8;
			cursor.offset = align_up(cursor.offset, base_align);
			base_offset = cursor.offset;
			cursor.offset += record_nonvirtual_subobject_size(direct_base);
		}
		else if (!record_uses_object_storage(direct_base) &&
		         direct_base->virtual_bases.empty())
			base_offset = 0;
		else
		{
			cursor.offset = align_up(cursor.offset, base_align);
			base_offset = cursor.offset;
			cursor.offset += record_nonvirtual_subobject_size(direct_base);
		}
		bare->direct_base_offsets[b] = base_offset;
		if (b == 0)
			bare->direct_base_offset = base_offset;
	}
}

static void layout_record_member(TypePtr bare,
                                 Binding* member,
                                 RecordLayoutCursor& cursor,
                                 uint64_t& bit_unit_offset,
                                 uint64_t& bit_unit_size,
                                 uint64_t& bit_used)
{
	uint64_t member_align = type_align(member->type);
	uint64_t member_size = type_size(member->type);
	if (member_align == 0)
		member_align = 1;
	if (bare->tag == "union")
	{
		member->member_offset = 0;
		member->bit_offset = 0;
		bare->fields.push_back(member);
		cursor.offset = max<uint64_t>(cursor.offset, member_size);
		cursor.align = max<uint64_t>(cursor.align, member_align);
		cursor.nonvirtual_align =
			max<uint64_t>(cursor.nonvirtual_align, member_align);
		return;
	}
	if (member->is_bit_field)
	{
		uint64_t unit_bits = member_size * 8;
		if (member->bit_width == 0)
		{
			if (bit_used != 0)
				cursor.offset = bit_unit_offset + bit_unit_size;
			uint64_t padding = cursor.offset % member_align;
			if (padding != 0)
				cursor.offset += member_align - padding;
			bit_used = 0;
			bit_unit_size = 0;
			cursor.align = max(cursor.align, member_align);
			cursor.nonvirtual_align =
				max(cursor.nonvirtual_align, member_align);
			return;
		}
		if (bit_used == 0)
		{
			cursor.offset = align_up(cursor.offset, member_align);
			bit_unit_offset = cursor.offset;
			bit_unit_size = member_size;
		}
		if (bit_used + member->bit_width > unit_bits)
		{
			cursor.offset = bit_unit_offset + bit_unit_size;
			cursor.offset = align_up(cursor.offset, member_align);
			bit_unit_offset = cursor.offset;
			bit_unit_size = member_size;
			bit_used = 0;
		}
		member->member_offset = bit_unit_offset;
		member->bit_offset = bit_used;
		bare->fields.push_back(member);
		bit_used += member->bit_width;
		cursor.align = max(cursor.align, member_align);
		cursor.nonvirtual_align = max(cursor.nonvirtual_align, member_align);
		return;
	}
	if (bit_used != 0)
	{
		cursor.offset = bit_unit_offset + bit_unit_size;
		bit_used = 0;
		bit_unit_size = 0;
	}
	cursor.offset = align_up(cursor.offset, member_align);
	member->member_offset = cursor.offset;
	bare->fields.push_back(member);
	cursor.offset += member_size;
	cursor.align = max(cursor.align, member_align);
	cursor.nonvirtual_align = max(cursor.nonvirtual_align, member_align);
}

static void layout_record_members(TypePtr bare, RecordLayoutCursor& cursor)
{
	if (bare->scope == NULL)
		return;
	uint64_t bit_unit_offset = 0;
	uint64_t bit_unit_size = 0;
	uint64_t bit_used = 0;
	for (size_t i = 0; i < bare->scope->binding_order.size(); ++i)
	{
		Binding* member = bare->scope->binding_order[i];
		if (member->kind != BindingKind::Variable ||
		    member->is_static_member ||
		    member->aliased_binding != NULL)
			continue;
		layout_record_member(bare, member, cursor,
		                     bit_unit_offset, bit_unit_size, bit_used);
	}
	if (bit_used != 0)
		cursor.offset = bit_unit_offset + bit_unit_size;
}

static void layout_record_virtual_bases(TypePtr bare,
                                        RecordLayoutCursor& cursor)
{
	for (size_t i = 0; i < bare->virtual_bases.size(); ++i)
	{
		TypePtr vbase = strip_cv(bare->virtual_bases[i]);
		layout_record_type(vbase);
		uint64_t vbase_align = record_virtual_subobject_align(vbase);
		cursor.offset = align_up(cursor.offset, vbase_align);
		bare->virtual_base_offsets[i] = cursor.offset;
		cursor.offset += record_virtual_subobject_size(vbase);
		cursor.align = max<uint64_t>(cursor.align, type_align(vbase));
	}
}

static void assign_direct_virtual_base_offsets(
	TypePtr bare,
	const vector<TypePtr>& direct_bases)
{
	for (size_t i = 0; i < direct_bases.size(); ++i)
		if (direct_base_is_virtual(bare, i))
		{
			TypePtr direct = direct_bases[i].get() != NULL
				? strip_cv(direct_bases[i]) : TypePtr();
			if (direct.get() != NULL && direct->kind == TypeKind::Record)
				for (size_t v = 0; v < bare->virtual_bases.size(); ++v)
					if (same_type(strip_cv(bare->virtual_bases[v]), direct))
					{
						bare->direct_base_offsets[i] =
							bare->virtual_base_offsets[v];
						break;
					}
		}
}

void layout_record_type(TypePtr type)
{
	TypePtr bare = strip_cv(type);
	if (bare->kind != TypeKind::Record)
		throw runtime_error("layout target is not a record");
	if (!bare->complete)
		throw runtime_error("incomplete class type");
	if (bare->layout_valid)
		return;
	bare->fields.clear();
	bare->direct_base_offset = 0;
	bare->virtual_bases.clear();
	bare->virtual_base_offsets.clear();
	vector<TypePtr> direct_bases = bare->direct_bases;
	if (direct_bases.empty() && bare->base.get() != NULL)
		direct_bases.push_back(bare->base);
	bare->direct_base_offsets.assign(direct_bases.size(), 0);
	collect_record_virtual_bases(bare, bare->virtual_bases);
	bare->virtual_base_offsets.assign(bare->virtual_bases.size(), 0);
	RecordLayoutCursor cursor(bare->record_forced_align);
	size_t primary_base = primary_polymorphic_base_index(bare, direct_bases);
	TypePtr direct_base = primary_base != static_cast<size_t>(-1)
		? strip_cv(direct_bases[primary_base])
		: TypePtr();
	bool base_polymorphic =
		primary_base != static_cast<size_t>(-1) &&
		direct_base.get() != NULL &&
		direct_base->kind == TypeKind::Record &&
		direct_base->is_polymorphic;
	bool introduces_vptr = bare->is_polymorphic && !base_polymorphic;
	layout_record_direct_bases(bare, direct_bases, primary_base,
	                           introduces_vptr, cursor);
	if (introduces_vptr)
	{
		cursor.align = max<uint64_t>(cursor.align, 8);
		cursor.nonvirtual_align = max<uint64_t>(cursor.nonvirtual_align, 8);
		if (cursor.offset < 8)
			cursor.offset = 8;
	}
	layout_record_members(bare, cursor);
	if (cursor.offset == 0)
		cursor.offset = 1;
	bare->nonvirtual_size =
		align_up(cursor.offset, cursor.nonvirtual_align);
	bare->nonvirtual_align = cursor.nonvirtual_align;
	layout_record_virtual_bases(bare, cursor);
	assign_direct_virtual_base_offsets(bare, direct_bases);
	cursor.offset = align_up(cursor.offset, cursor.align);
	bare->record_size = cursor.offset;
	bare->record_align = cursor.align;
	bare->layout_valid = true;
}

vector<TypePtr> record_direct_bases(TypePtr type)
{
	vector<TypePtr> out;
	if (type.get() == NULL)
		return out;
	TypePtr bare = strip_cv(type);
	if (bare.get() == NULL || bare->kind != TypeKind::Record)
		return out;
	out = bare->direct_bases;
	if (out.empty() && bare->base.get() != NULL)
		out.push_back(bare->base);
	return out;
}

uint64_t record_direct_base_offset(TypePtr record, TypePtr direct_base)
{
	if (record.get() == NULL || direct_base.get() == NULL)
		return 0;
	TypePtr bare = strip_cv(record);
	TypePtr wanted = strip_cv(direct_base);
	if (bare.get() == NULL || wanted.get() == NULL ||
	    bare->kind != TypeKind::Record || wanted->kind != TypeKind::Record)
		return 0;
	layout_record_type(bare);
	vector<TypePtr> bases = record_direct_bases(bare);
	for (size_t i = 0; i < bases.size(); ++i)
	{
		TypePtr base = strip_cv(bases[i]);
		if (base.get() != NULL && same_type(base, wanted))
			return i < bare->direct_base_offsets.size()
				? bare->direct_base_offsets[i] : 0;
	}
	return 0;
}

bool record_direct_base_is_virtual(TypePtr record, size_t index)
{
	if (record.get() == NULL)
		return false;
	TypePtr bare = strip_cv(record);
	if (bare.get() == NULL || bare->kind != TypeKind::Record)
		return false;
	return direct_base_is_virtual(bare, index);
}

vector<TypePtr> record_virtual_bases(TypePtr type)
{
	vector<TypePtr> out;
	if (type.get() == NULL)
		return out;
	TypePtr bare = strip_cv(type);
	if (bare.get() == NULL || bare->kind != TypeKind::Record)
		return out;
	layout_record_type(bare);
	return bare->virtual_bases;
}

uint64_t record_virtual_base_offset(TypePtr record, TypePtr virtual_base)
{
	if (record.get() == NULL || virtual_base.get() == NULL)
		return 0;
	TypePtr bare = strip_cv(record);
	TypePtr wanted = strip_cv(virtual_base);
	if (bare.get() == NULL || wanted.get() == NULL ||
	    bare->kind != TypeKind::Record || wanted->kind != TypeKind::Record)
		return 0;
	layout_record_type(bare);
	for (size_t i = 0; i < bare->virtual_bases.size(); ++i)
		if (same_type(strip_cv(bare->virtual_bases[i]), wanted))
			return i < bare->virtual_base_offsets.size()
				? bare->virtual_base_offsets[i] : 0;
	return 0;
}

TypePtr record_type_for_scope(Scope* scope)
{
	if (scope == NULL || scope->kind != ScopeKind::Class || scope->parent == NULL)
		return TypePtr();
	for (size_t i = 0; i < scope->parent->binding_order.size(); ++i)
	{
		Binding* binding = scope->parent->binding_order[i];
		if (binding->kind != BindingKind::Type &&
		    binding->kind != BindingKind::TypeAlias)
			continue;
		if (binding->type.get() == NULL)
			continue;
		TypePtr bare = strip_cv(binding->type);
		if (bare->kind == TypeKind::Record && bare->scope == scope)
			return bare;
	}
	return TypePtr();
}

Scope* create_child_scope(Scope* parent, ScopeKind kind, const string& name)
{
	unique_ptr<Scope> scope(new Scope(kind, name, parent));
	Scope* raw = scope.get();
	parent->owned_scopes.push_back(std::move(scope));
	parent->child_order.push_back(raw);
	return raw;
}

Scope* get_or_create_namespace(Scope* parent,
                               const string& name,
                               bool is_inline)
{
	map<string, Scope*>::iterator found = parent->named_namespaces.find(name);
	if (found != parent->named_namespaces.end())
	{
		if (is_inline)
			add_using_directive(parent, found->second);
		return found->second;
	}
	Scope* scope = create_child_scope(parent, ScopeKind::Namespace, name);
	scope->is_inline_namespace = is_inline;
	parent->named_namespaces[name] = scope;
	Binding* binding = add_binding(parent, BindingKind::Namespace, name, TypePtr());
	binding->target_scope = scope;
	if (is_inline)
		add_using_directive(parent, scope);
	return scope;
}

Binding* add_binding(Scope* scope,
                     BindingKind kind,
                     const string& name,
                     TypePtr type)
{
	unique_ptr<Binding> binding(new Binding(kind, name, scope));
	binding->type = type;
	Binding* raw = binding.get();
	scope->owned_bindings.push_back(std::move(binding));
	scope->members[name].push_back(raw);
	if (kind != BindingKind::Namespace && kind != BindingKind::NamespaceAlias)
		scope->binding_order.push_back(raw);
	return raw;
}

Binding* add_namespace_alias(Scope* scope,
                             const string& name,
                             Scope* target)
{
	Binding* binding =
		add_binding(scope, BindingKind::NamespaceAlias, name, TypePtr());
	binding->target_scope = target;
	return binding;
}

void add_using_directive(Scope* scope, Scope* target)
{
	if (target == NULL)
		throw runtime_error("invalid using directive");
	if (find(scope->using_directives.begin(),
	         scope->using_directives.end(),
	         target) == scope->using_directives.end())
		scope->using_directives.push_back(target);
}

Binding* add_using_declaration(Scope* scope,
                               const string& name,
                               const Binding* target)
{
	if (target == NULL ||
	    target->kind == BindingKind::Namespace ||
	    target->kind == BindingKind::NamespaceAlias)
		throw runtime_error("invalid using declaration");
	Binding* binding = add_binding(scope, target->kind, name, target->type);
	binding->target_scope = target->target_scope;
	binding->aliased_binding = const_cast<Binding*>(target);
	binding->has_constant = target->has_constant;
	binding->constant_value = target->constant_value;
	binding->is_constexpr = target->is_constexpr;
	binding->is_static_member = target->is_static_member;
	binding->is_local_static = target->is_local_static;
	binding->is_namespace_static = target->is_namespace_static;
	binding->local_static_discriminator = target->local_static_discriminator;
	binding->local_static_function_owner =
		target->local_static_function_owner;
	binding->function_specialization_symbol =
		target->function_specialization_symbol;
	binding->is_generated_default_constructor =
		target->is_generated_default_constructor;
	binding->is_generated_aggregate_constructor =
		target->is_generated_aggregate_constructor;
	binding->is_generated_copy_move_constructor =
		target->is_generated_copy_move_constructor;
	binding->is_generated_copy_move_assignment =
		target->is_generated_copy_move_assignment;
	binding->is_generated_default_destructor =
		target->is_generated_default_destructor;
	binding->is_defaulted = target->is_defaulted;
	binding->is_mutable_member = target->is_mutable_member;
	binding->is_reference_member = target->is_reference_member;
	binding->is_thread_local = target->is_thread_local;
	binding->is_dependent_template_artifact =
		target->is_dependent_template_artifact;
	binding->ref_qualifier = target->ref_qualifier;
	binding->is_noop_constructor = target->is_noop_constructor;
	binding->is_noop_destructor = target->is_noop_destructor;
	binding->is_cleanup_only_destructor =
		target->is_cleanup_only_destructor;
	return binding;
}

Binding* find_owned_binding(Scope* scope,
                            const string& name,
                            BindingKind kind)
{
	map<string, vector<Binding*> >::iterator it = scope->members.find(name);
	if (it == scope->members.end())
		return NULL;
	for (size_t i = 0; i < it->second.size(); ++i)
	{
		Binding* binding = it->second[i];
		if (binding->owner == scope && binding->kind == kind)
			return binding;
	}
	return NULL;
}

bool binding_matches(const Binding* binding, int mask)
{
	if (binding == NULL)
		return false;
	if ((mask & LOOKUP_NAMESPACE) &&
	    (binding->kind == BindingKind::Namespace ||
	     binding->kind == BindingKind::NamespaceAlias))
		return true;
	if ((mask & LOOKUP_TYPE) &&
	    (binding->kind == BindingKind::Type ||
	     binding->kind == BindingKind::TypeAlias))
		return true;
	if ((mask & LOOKUP_VARIABLE) && binding->kind == BindingKind::Variable)
		return true;
	if ((mask & LOOKUP_FUNCTION) && binding->kind == BindingKind::Function)
		return true;
	if ((mask & LOOKUP_PARAMETER) && binding->kind == BindingKind::Parameter)
		return true;
	if ((mask & LOOKUP_ENUMERATOR) && binding->kind == BindingKind::Enumerator)
		return true;
	return false;
}

Binding* lookup_unqualified(Scope* start, const string& name, int mask)
{
	for (Scope* scope = start; scope != NULL; scope = scope->parent)
	{
		set<Scope*> seen;
		Binding* found = lookup_in_scope(scope, name, mask, seen);
		if (found != NULL)
			return found;
	}
	return NULL;
}

Binding* lookup_qualified(Scope* scope, const string& name, int mask)
{
	set<Scope*> seen;
	return lookup_in_scope(scope, name, mask, seen);
}

Scope* binding_qualifier_scope(const Binding* binding)
{
	if (binding == NULL)
		return NULL;
	if (binding->kind == BindingKind::Namespace ||
	    binding->kind == BindingKind::NamespaceAlias)
		return binding->target_scope;
	if ((binding->kind == BindingKind::Type ||
	     binding->kind == BindingKind::TypeAlias) &&
	    binding->type.get() != NULL)
	{
		TypePtr bare = strip_cv(binding->type);
		if (bare->scope != NULL)
			return bare->scope;
	}
	return NULL;
}

}  // namespace pa11
