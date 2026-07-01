#include "pa12_internal.h"
#include "pa12_types_support.h"
#include <stdexcept>
using namespace std; namespace pa12 { namespace internal {
static bool same_return_template_argument(
	const pa11::TemplateInstanceArgument& left,
	const pa11::TemplateInstanceArgument& right);
static bool same_return_template_arguments(
	const vector<pa11::TemplateInstanceArgument>& left,
	const vector<pa11::TemplateInstanceArgument>& right)
{ if (left.size() != right.size()) return false; for (size_t i = 0; i < left.size(); ++i) if (!same_return_template_argument(left[i], right[i])) return false; return true; }
static bool same_return_record_type(TypePtr left, TypePtr right);
static bool explicit_full_class_specialization_record(
	TypePtr record,
	const map<const void*, TemplateDeclaration*>& declarations)
{
	record = record.get() != NULL ? pa11::strip_cv(record) : TypePtr();
	if (record.get() == NULL || record->kind != pa11::TypeKind::Record)
		return false;
	map<const void*, TemplateDeclaration*>::const_iterator found =
		declarations.find(record.get());
	return found != declarations.end() &&
	       found->second != NULL &&
	       found->second->class_specialization &&
	       found->second->parameters.empty();
}
bool class_template_specialization_member(
	Binding* function,
	const map<const void*, TemplateDeclaration*>& declarations)
{
	if (function == NULL ||
	    function->owner == NULL ||
	    function->owner->kind != ScopeKind::Class)
		return false;
	TypePtr record = pa11::record_type_for_scope(function->owner);
	record = record.get() != NULL ? pa11::strip_cv(record) : TypePtr();
	return record.get() != NULL &&
	       record->kind == pa11::TypeKind::Record &&
	       record->is_template_specialization &&
	       !explicit_full_class_specialization_record(record, declarations);
}
bool explicit_full_class_specialization_member(
	Binding* function,
	const map<const void*, TemplateDeclaration*>& declarations)
{
	if (function == NULL ||
	    function->owner == NULL ||
	    function->owner->kind != ScopeKind::Class)
		return false;
	TypePtr record = pa11::record_type_for_scope(function->owner);
	return explicit_full_class_specialization_record(record, declarations);
}
bool same_replay_type(TypePtr left, TypePtr right)
{
	if (left.get() == right.get())
		return true;
	if (left.get() == NULL || right.get() == NULL)
		return false;
	if (pa11::same_type(left, right))
		return true;
	TypePtr l = pa11::strip_cv(left);
	TypePtr r = pa11::strip_cv(right);
	if (l->kind != r->kind)
		return false;
	switch (l->kind)
	{
	case pa11::TypeKind::Fundamental:
		return l->fundamental == r->fundamental;
	case pa11::TypeKind::Pointer:
	case pa11::TypeKind::LValueReference:
	case pa11::TypeKind::RValueReference:
		return same_replay_type(l->base, r->base);
	case pa11::TypeKind::Array:
		return l->unknown_bound == r->unknown_bound &&
		       (l->unknown_bound || l->bound == r->bound) &&
		       same_replay_type(l->base, r->base);
	case pa11::TypeKind::Function:
		if (l->variadic != r->variadic ||
		    l->ref_qualifier != r->ref_qualifier ||
		    l->parameters.size() != r->parameters.size() ||
		    !same_replay_type(l->base, r->base))
			return false;
		for (size_t i = 0; i < l->parameters.size(); ++i)
			if (!same_replay_type(l->parameters[i], r->parameters[i]))
				return false;
		return true;
	case pa11::TypeKind::MemberPointer:
		return same_replay_type(l->member_class, r->member_class) &&
		       same_replay_type(l->base, r->base);
	case pa11::TypeKind::Record:
		return same_return_record_type(l, r);
	case pa11::TypeKind::Enum:
		return l->name == r->name &&
		       l->enum_underlying == r->enum_underlying;
	case pa11::TypeKind::TemplateParameter:
	case pa11::TypeKind::TemplateTemplateParameter:
		return l->name == r->name;
	case pa11::TypeKind::Cv:
		return same_replay_type(l->base, r->base);
	}
	return false;
}
static bool same_scope_template_argument(
	const pa11::TemplateInstanceArgument& left,
	const pa11::TemplateInstanceArgument& right)
{
	if (left.kind != right.kind)
		return false;
	if (left.kind == pa11::TemplateInstanceArgumentKind::Type)
		return pa11::same_type(left.type, right.type);
	if (left.kind == pa11::TemplateInstanceArgumentKind::Value)
		return left.dependent == right.dependent &&
		       left.value_negated == right.value_negated &&
		       left.value == right.value &&
		       left.value_name == right.value_name &&
		       pa11::same_type(left.type, right.type);
	if (left.kind == pa11::TemplateInstanceArgumentKind::Template)
		return left.template_name == right.template_name &&
		       left.dependent == right.dependent;
	if (left.pack.size() != right.pack.size())
		return false;
	for (size_t i = 0; i < left.pack.size(); ++i)
		if (!same_scope_template_argument(left.pack[i], right.pack[i]))
			return false;
	return true;
}
static bool same_scope_record_type(TypePtr left, TypePtr right)
{
	TypePtr l = pa11::strip_cv(left);
	TypePtr r = pa11::strip_cv(right);
	if (l.get() == r.get())
		return true;
	if (l->kind == pa11::TypeKind::Record &&
	    r->kind == pa11::TypeKind::Record &&
	    (l->is_template_specialization || r->is_template_specialization))
	{
		if (!l->is_template_specialization ||
		    !r->is_template_specialization ||
		    l->template_primary_name.empty() ||
		    l->template_primary_name != r->template_primary_name ||
		    l->template_arguments.empty() ||
		    r->template_arguments.empty() ||
		    l->template_arguments.size() != r->template_arguments.size())
			return false;
		for (size_t i = 0; i < l->template_arguments.size(); ++i)
			if (!same_scope_template_argument(l->template_arguments[i],
			                                  r->template_arguments[i]))
				return false;
		return true;
	}
	if (pa11::same_type(l, r))
		return true;
	if (l->kind != pa11::TypeKind::Record ||
	    r->kind != pa11::TypeKind::Record ||
	    !l->is_template_specialization ||
	    !r->is_template_specialization ||
	    l->template_primary_name.empty() ||
	    l->template_primary_name != r->template_primary_name ||
	    l->template_arguments.size() != r->template_arguments.size())
		return false;
	for (size_t i = 0; i < l->template_arguments.size(); ++i)
		if (!same_scope_template_argument(l->template_arguments[i],
		                                  r->template_arguments[i]))
			return false;
	return true;
}

bool same_replay_scope(Scope* left, Scope* right)
{
	if (left == right)
		return true;
	if (left == NULL || right == NULL || left->kind != right->kind)
		return false;
	typedef pair<Scope*, Scope*> ScopePair;
	static map<ScopePair, bool> scope_cache;
	ScopePair key(left, right);
	map<ScopePair, bool>::const_iterator cached = scope_cache.find(key);
	if (cached != scope_cache.end())
		return cached->second;
	bool same = false;
	if (left->kind == ScopeKind::Class)
	{
		TypePtr left_record = pa11::record_type_for_scope(left);
		TypePtr right_record = pa11::record_type_for_scope(right);
		same = same_scope_record_type(left_record, right_record);
		scope_cache[key] = same;
		return same;
	}
	same = left->name == right->name &&
	       same_replay_scope(left->parent, right->parent);
	scope_cache[key] = same;
	return same;
}
static int object_parameter_cv(TypePtr type, TypePtr& object)
{
	TypePtr bare = type.get() != NULL ? pa11::strip_cv(type) : TypePtr();
	if (bare.get() == NULL || bare->kind != pa11::TypeKind::Pointer)
		return -1;
	TypePtr pointee = bare->base;
	int cv = 0;
	if (pointee.get() != NULL && pointee->kind == pa11::TypeKind::Cv)
	{
		cv = pointee->cv;
		pointee = pointee->base;
	}
	object = pointee.get() != NULL ? pa11::strip_cv(pointee) : TypePtr();
	return object.get() != NULL && object->kind == pa11::TypeKind::Record
		? cv : -1;
}
static bool same_implicit_object_parameter(TypePtr left, TypePtr right)
{
	TypePtr left_object;
	TypePtr right_object;
	int left_cv = object_parameter_cv(left, left_object);
	int right_cv = object_parameter_cv(right, right_object);
	return left_cv >= 0 &&
	       left_cv == right_cv &&
	       right_cv >= 0;
}
static bool class_member_implicit_object_parameter(Binding* left,
                                                   Binding* right,
                                                   size_t index,
                                                   bool same_scope)
{
	return index == 0 &&
	       same_scope &&
	       left != NULL &&
	       right != NULL &&
	       left->owner != NULL &&
	       right->owner != NULL &&
	       left->owner->kind == ScopeKind::Class &&
	       right->owner->kind == ScopeKind::Class &&
	       !left->is_static_member &&
	       !right->is_static_member;
}
static bool same_member_function_type(Binding* left,
                                      Binding* right,
                                      bool same_scope)
{
	if (left->type.get() == NULL || right->type.get() == NULL)
		return left->type.get() == right->type.get();
	if (left->type->kind != pa11::TypeKind::Function ||
	    right->type->kind != pa11::TypeKind::Function)
		return same_replay_type(left->type, right->type);
	TypePtr l = left->type;
	TypePtr r = right->type;
	if (l->variadic != r->variadic ||
	    l->cv != r->cv ||
	    l->ref_qualifier != r->ref_qualifier ||
	    l->parameters.size() != r->parameters.size() ||
	    !same_replay_type(l->base, r->base))
		return false;
	for (size_t i = 0; i < l->parameters.size(); ++i)
	{
		if (class_member_implicit_object_parameter(left, right, i, same_scope) &&
		    same_implicit_object_parameter(l->parameters[i], r->parameters[i]))
			continue;
		if (class_member_implicit_object_parameter(left, right, i, same_scope))
			return false;
		if (same_replay_type(l->parameters[i], r->parameters[i]))
			continue;
		return false;
	}
	return true;
}
bool same_member_function_signature(Binding* left, Binding* right)
{
	if (left == right)
		return true;
	if (left == NULL || right == NULL)
		return false;
	if (left->kind != BindingKind::Function ||
	    right->kind != BindingKind::Function)
		return false;
	if (left->name != right->name)
		return false;
	if ((left->owner != right->owner) &&
	    ((left->owner != NULL && left->owner->kind == ScopeKind::Class) ||
	     (right->owner != NULL && right->owner->kind == ScopeKind::Class)))
		return false;
	pair<Binding*, Binding*> key = left < right
		? make_pair(left, right) : make_pair(right, left);
	static map<pair<Binding*, Binding*>, bool> cache;
	map<pair<Binding*, Binding*>, bool>::const_iterator found =
		cache.find(key);
	if (found != cache.end())
		return found->second;
	bool same_scope = same_replay_scope(left->owner, right->owner);
	if (!same_scope)
	{
		cache[key] = false;
		return false;
	}
	bool same = same_member_function_type(left, right, same_scope);
	cache[key] = same;
	return same;
}
static bool same_return_template_argument(
	const pa11::TemplateInstanceArgument& left,
	const pa11::TemplateInstanceArgument& right)
{ if (left.kind != right.kind) return false; if (left.kind == pa11::TemplateInstanceArgumentKind::Type) return same_return_record_type(left.type, right.type); if (left.kind == pa11::TemplateInstanceArgumentKind::Value) { if (left.dependent != right.dependent) return same_return_record_type(left.type, right.type); return left.value_negated == right.value_negated && left.value == right.value && left.value_name == right.value_name && same_return_record_type(left.type, right.type); } if (left.kind == pa11::TemplateInstanceArgumentKind::Template) return left.template_name == right.template_name && left.dependent == right.dependent; return same_return_template_arguments(left.pack, right.pack); }
static bool same_return_record_type(TypePtr left, TypePtr right)
{
	TypePtr l = pa11::strip_cv(left);
	TypePtr r = pa11::strip_cv(right);
	if (l.get() == r.get())
		return true;
	if (l->kind == pa11::TypeKind::Record &&
	    r->kind == pa11::TypeKind::Record &&
	    (l->is_template_specialization || r->is_template_specialization))
		return l->is_template_specialization &&
		       r->is_template_specialization &&
		       !l->template_primary_name.empty() &&
		       l->template_primary_name == r->template_primary_name &&
		       !l->template_arguments.empty() &&
		       !r->template_arguments.empty() &&
		       same_return_template_arguments(l->template_arguments,
		                                      r->template_arguments);
	if (pa11::same_type(l, r))
		return true;
	return false;
}

}  // namespace internal
}  // namespace pa12
