#include "pa12_internal.h"
#include "pa12_templates_function_support.h"

#include <algorithm>

using namespace std;

namespace pa12 {
namespace internal {

bool is_destructor_binding(Binding* binding)
{
	return binding != NULL && !binding->name.empty() && binding->name[0] == '~';
}

bool hosted_library_namespace_scope(Scope* scope)
{
	for (Scope* cur = scope; cur != NULL; cur = cur->parent)
		if (cur->kind == ScopeKind::Namespace &&
		    (cur->name == "std" || cur->name == "__gnu_cxx"))
			return true;
	return false;
}

bool same_virtual_instance_type(TypePtr left, TypePtr right);

void append_normalized_virtual_instance_arguments(
	vector<pa11::TemplateInstanceArgument>& out,
	const vector<pa11::TemplateInstanceArgument>& arguments)
{
	for (size_t i = 0; i < arguments.size(); ++i)
	{
		if (arguments[i].kind == pa11::TemplateInstanceArgumentKind::Pack)
		{
			append_normalized_virtual_instance_arguments(
				out,
				arguments[i].pack);
			continue;
		}
		out.push_back(arguments[i]);
	}
}

bool same_virtual_instance_arguments(
	const vector<pa11::TemplateInstanceArgument>& left,
	const vector<pa11::TemplateInstanceArgument>& right);

bool same_virtual_instance_argument(
	const pa11::TemplateInstanceArgument& left,
	const pa11::TemplateInstanceArgument& right)
{
	if (left.kind != right.kind)
		return false;
	if (left.kind == pa11::TemplateInstanceArgumentKind::Type)
		return same_virtual_instance_type(left.type, right.type);
	if (left.kind == pa11::TemplateInstanceArgumentKind::Value)
		return left.dependent == right.dependent &&
		       left.value_negated == right.value_negated &&
		       left.value == right.value &&
		       left.value_name == right.value_name &&
		       left.value_owner_template_name ==
			       right.value_owner_template_name &&
		       left.value_member_name == right.value_member_name &&
		       same_virtual_instance_type(left.type, right.type) &&
		       same_virtual_instance_arguments(
			       left.value_owner_template_arguments,
			       right.value_owner_template_arguments);
	if (left.kind == pa11::TemplateInstanceArgumentKind::Template)
		return left.template_name == right.template_name &&
		       left.dependent == right.dependent;
	if (left.pack.size() != right.pack.size())
		return false;
	for (size_t i = 0; i < left.pack.size(); ++i)
		if (!same_virtual_instance_argument(left.pack[i], right.pack[i]))
			return false;
	return true;
}

bool same_virtual_instance_arguments(
	const vector<pa11::TemplateInstanceArgument>& left,
	const vector<pa11::TemplateInstanceArgument>& right)
{
	vector<pa11::TemplateInstanceArgument> flat_left;
	vector<pa11::TemplateInstanceArgument> flat_right;
	append_normalized_virtual_instance_arguments(flat_left, left);
	append_normalized_virtual_instance_arguments(flat_right, right);
	if (flat_left.size() != flat_right.size())
		return false;
	for (size_t i = 0; i < flat_left.size(); ++i)
		if (!same_virtual_instance_argument(flat_left[i], flat_right[i]))
			return false;
	return true;
}

bool same_virtual_instance_type(TypePtr left, TypePtr right)
{
	if (pa11::same_type(left, right))
		return true;
	TypePtr l = pa11::strip_cv(left);
	TypePtr r = pa11::strip_cv(right);
	return l->kind == pa11::TypeKind::Record &&
	       r->kind == pa11::TypeKind::Record &&
	       l->is_template_specialization &&
	       r->is_template_specialization &&
	       !l->template_primary_name.empty() &&
	       l->template_primary_name == r->template_primary_name &&
	       same_virtual_instance_arguments(l->template_arguments,
	                                       r->template_arguments);
}

bool same_virtual_completion_record(TypePtr left, TypePtr right)
{
	if (left.get() == NULL || right.get() == NULL)
		return left.get() == right.get();
	if (left.get() == right.get())
		return true;
	return same_virtual_instance_type(left, right);
}

bool virtual_completion_active(const vector<TypePtr>& active, TypePtr type)
{
	for (size_t i = 0; i < active.size(); ++i)
		if (same_virtual_completion_record(active[i], type))
			return true;
	return false;
}

unsigned pointed_record_cv(TypePtr ptr)
{
	TypePtr bare = pa11::strip_cv(ptr);
	if (bare->kind != pa11::TypeKind::Pointer)
		return pa11::CV_NONE;
	TypePtr pointee = bare->base;
	return pointee->kind == pa11::TypeKind::Cv ? pointee->cv : pa11::CV_NONE;
}

bool same_parameter_tail(const vector<TypePtr>& left,
                         const vector<TypePtr>& right)
{
	if (left.size() != right.size())
		return false;
	if (left.empty())
		return true;
	if (pointed_record_cv(left[0]) != pointed_record_cv(right[0]))
		return false;
	for (size_t i = 1; i < left.size(); ++i)
		if (!pa11::same_type(left[i], right[i]))
			return false;
	return true;
}

bool record_derives_from(TypePtr source, TypePtr target)
{
	TypePtr wanted = pa11::strip_cv(target);
	for (TypePtr cur = pa11::strip_cv(source);
	     cur.get() != NULL && cur->kind == pa11::TypeKind::Record;
	     cur = cur->base.get() != NULL ? pa11::strip_cv(cur->base) : TypePtr())
		if (pa11::same_type(cur, wanted))
			return true;
	return false;
}

bool covariant_return(TypePtr derived_return, TypePtr base_return)
{
	TypePtr d = pa11::strip_cv(derived_return);
	TypePtr b = pa11::strip_cv(base_return);
	if (d->kind == pa11::TypeKind::Pointer &&
	    b->kind == pa11::TypeKind::Pointer)
	{
		TypePtr dr = pa11::strip_cv(d->base);
		TypePtr br = pa11::strip_cv(b->base);
		return dr->kind == pa11::TypeKind::Record &&
		       br->kind == pa11::TypeKind::Record &&
		       record_derives_from(dr, br);
	}
	if (d->kind == pa11::TypeKind::LValueReference &&
	    b->kind == pa11::TypeKind::LValueReference)
	{
		TypePtr dr = pa11::strip_cv(d->base);
		TypePtr br = pa11::strip_cv(b->base);
		return dr->kind == pa11::TypeKind::Record &&
		       br->kind == pa11::TypeKind::Record &&
		       record_derives_from(dr, br);
	}
	return false;
}

bool virtual_signature_matches(Binding* base, Binding* derived)
{
	if (base == NULL || derived == NULL ||
	    base->type.get() == NULL || derived->type.get() == NULL ||
	    base->type->kind != pa11::TypeKind::Function ||
	    derived->type->kind != pa11::TypeKind::Function)
		return false;
	if (is_destructor_binding(base) || is_destructor_binding(derived))
		return is_destructor_binding(base) && is_destructor_binding(derived);
	if (base->name != derived->name ||
	    base->type->variadic != derived->type->variadic ||
	    !same_parameter_tail(base->type->parameters, derived->type->parameters))
		return false;
	if (pa11::same_type(base->type->base, derived->type->base))
		return true;
	return covariant_return(derived->type->base, base->type->base);
}

bool class_has_polymorphic_base(TypePtr type)
{
	TypePtr bare = pa11::strip_cv(type);
	vector<TypePtr> bases = pa11::record_direct_bases(bare);
	for (size_t i = 0; i < bases.size(); ++i)
	{
		TypePtr base = bases[i].get() != NULL
			? pa11::strip_cv(bases[i]) : TypePtr();
		if (base.get() != NULL &&
		    base->kind == pa11::TypeKind::Record &&
		    base->is_polymorphic)
			return true;
	}
	return false;
}

TypePtr primary_polymorphic_base(TypePtr type)
{
	TypePtr bare = pa11::strip_cv(type);
	vector<TypePtr> bases = pa11::record_direct_bases(bare);
	for (size_t i = 0; i < bases.size(); ++i)
	{
		TypePtr base = bases[i].get() != NULL
			? pa11::strip_cv(bases[i]) : TypePtr();
		if (base.get() != NULL &&
		    base->kind == pa11::TypeKind::Record &&
		    base->is_polymorphic)
			return base;
	}
	return TypePtr();
}

bool has_declared_destructor(TypePtr record)
{
	TypePtr bare = pa11::strip_cv(record);
	if (bare->kind != pa11::TypeKind::Record || bare->scope == NULL)
		return false;
	return bare->scope->members.find("~" + bare->scope->name) !=
	       bare->scope->members.end();
}

bool inherits_virtual_destructor(TypePtr record)
{
	TypePtr bare = pa11::strip_cv(record);
	vector<TypePtr> pending = pa11::record_direct_bases(bare);
	vector<TypePtr> seen;
	for (size_t pending_i = 0; pending_i < pending.size(); ++pending_i)
	{
		TypePtr cur = pending[pending_i].get() != NULL
			? pa11::strip_cv(pending[pending_i]) : TypePtr();
		if (cur.get() == NULL || cur->kind != pa11::TypeKind::Record)
			continue;
		bool already = false;
		for (size_t i = 0; i < seen.size(); ++i)
			if (pa11::same_type(seen[i], cur))
				already = true;
		if (already)
			continue;
		seen.push_back(cur);
		for (size_t i = 0; i < cur->virtual_entries.size(); ++i)
		{
			Binding* fn = cur->virtual_entries[i].function;
			if (fn != NULL && is_destructor_binding(fn))
				return true;
		}
		vector<TypePtr> bases = pa11::record_direct_bases(cur);
		pending.insert(pending.end(), bases.begin(), bases.end());
	}
	return false;
}

size_t local_static_decl_span_begin(const vector<Token>& tokens,
                                    size_t begin,
                                    size_t end)
{
	size_t pos = begin;
	while (pos < end && tokens[pos].kind == posttoken::TokenKind::Simple &&
	       (tokens[pos].type == KW_STATIC ||
	        tokens[pos].type == KW_THREAD_LOCAL ||
	        tokens[pos].type == KW_CONST ||
	        tokens[pos].type == KW_VOLATILE ||
	        tokens[pos].type == KW_CONSTEXPR))
		++pos;
	return pos;
}

}  // namespace internal
}  // namespace pa12
