#include "pa12_internal.h"

#include <algorithm>
#include <sstream>
#include <stdexcept>

using namespace std;

namespace pa12 {
namespace internal {
namespace {

bool seen_insert(set<Scope*>& seen, Scope* scope)
{
	return scope != NULL && seen.insert(scope).second;
}

void append_unique(vector<Binding*>& out, Binding* binding)
{
	if (binding == NULL)
		return;
	if (find(out.begin(), out.end(), binding) == out.end())
		out.push_back(binding);
}

void collect_direct_in_scope(Scope* scope,
                             const string& name,
                             int mask,
                             vector<Binding*>& out)
{
	if (scope == NULL)
		return;
	map<string, vector<Binding*> >::iterator it = scope->members.find(name);
	if (it == scope->members.end())
		return;
	for (size_t i = 0; i < it->second.size(); ++i)
	{
		if (!pa11::binding_matches(it->second[i], mask) ||
		    it->second[i]->is_hidden_friend)
			continue;
		append_unique(out, it->second[i]);
	}
}

void collect_in_scope(Scope* scope,
                      const string& name,
                      int mask,
                      set<Scope*>& seen,
                      vector<Binding*>& out)
{
	if (!seen_insert(seen, scope))
		return;
	collect_direct_in_scope(scope, name, mask, out);
	for (size_t i = 0; i < scope->using_directives.size(); ++i)
		collect_in_scope(scope->using_directives[i], name, mask, seen, out);
	if (!out.empty())
		return;
	TypePtr record = pa11::record_type_for_scope(scope);
	TypePtr base = record.get() != NULL && record->base.get() != NULL
		? pa11::strip_cv(record->base) : TypePtr();
	if (base.get() != NULL && base->kind == pa11::TypeKind::Record &&
	    base->scope != NULL)
		collect_in_scope(base->scope, name, mask, seen, out);
}

bool type_is_floating(TypePtr type)
{
	TypePtr bare = pa11::strip_cv(type);
	return bare->kind == pa11::TypeKind::Fundamental &&
	       (bare->fundamental == FT_FLOAT ||
	        bare->fundamental == FT_DOUBLE ||
	        bare->fundamental == FT_LONG_DOUBLE);
}

bool type_is_arithmetic(TypePtr type)
{
	return pa11::is_integral_or_bool_type(type) || type_is_floating(type);
}

int arithmetic_rank(TypePtr type)
{
	TypePtr bare = pa11::strip_cv(type);
	if (bare->kind == pa11::TypeKind::Enum)
		return 3;
	if (bare->kind != pa11::TypeKind::Fundamental)
		return 0;
	switch (bare->fundamental)
	{
	case FT_BOOL: return 1;
	case FT_SIGNED_CHAR: case FT_UNSIGNED_CHAR: case FT_CHAR: return 1;
	case FT_SHORT_INT: case FT_UNSIGNED_SHORT_INT: return 2;
	case FT_INT: case FT_UNSIGNED_INT: return 3;
	case FT_LONG_INT: case FT_UNSIGNED_LONG_INT: return 4;
	case FT_LONG_LONG_INT: case FT_UNSIGNED_LONG_LONG_INT: return 5;
	case FT_FLOAT: return 6;
	case FT_DOUBLE: return 7;
	case FT_LONG_DOUBLE: return 8;
	default: return 0;
	}
}

TypePtr integral_promotion(TypePtr type)
{
	TypePtr bare = pa11::strip_cv(type);
	if (bare->kind == pa11::TypeKind::Enum)
		return pa11::make_fundamental(FT_INT);
	if (pa11::is_integral_or_bool_type(type) && arithmetic_rank(type) < 3)
		return pa11::make_fundamental(FT_INT);
	return type;
}

bool type_is_pointer(TypePtr type)
{
	return pa11::strip_cv(type)->kind == pa11::TypeKind::Pointer;
}

unsigned cv_flags(TypePtr type)
{
	return type->kind == pa11::TypeKind::Cv ? type->cv : pa11::CV_NONE;
}

bool cv_contains(unsigned target, unsigned source)
{
	return (target & source) == source;
}

int record_base_distance_impl(TypePtr source, TypePtr target)
{
	TypePtr t = pa11::strip_cv(target);
	int distance = 0;
	for (TypePtr s = pa11::strip_cv(source);
	     s.get() != NULL && s->kind == pa11::TypeKind::Record;
	     s = s->base.get() != NULL ? pa11::strip_cv(s->base) : TypePtr())
	{
		if (pa11::same_type(s, t))
			return distance;
		++distance;
	}
	return 1000000;
}

bool qualification_compatible_impl(TypePtr target,
                                   TypePtr source,
                                   int pointer_depth,
                                   bool intermediate_const)
{
	unsigned target_cv = cv_flags(target);
	unsigned source_cv = cv_flags(source);
	TypePtr t = pa11::strip_cv(target);
	TypePtr s = pa11::strip_cv(source);
	if (!cv_contains(target_cv, source_cv))
		return false;
	if (pointer_depth > 1 && ((target_cv & ~source_cv) != 0) &&
	    !intermediate_const)
		return false;
	if (t->kind == pa11::TypeKind::Array && s->kind == pa11::TypeKind::Array)
		return t->unknown_bound == s->unknown_bound &&
		       t->bound == s->bound &&
		       qualification_compatible_impl(t->base,
		                                     s->base,
		                                     pointer_depth,
		                                     intermediate_const);
	if (t->kind == pa11::TypeKind::Pointer && s->kind == pa11::TypeKind::Pointer)
	{
		bool next_intermediate = intermediate_const;
		if (pointer_depth > 0)
			next_intermediate =
				next_intermediate && ((target_cv & pa11::CV_CONST) != 0);
		return qualification_compatible_impl(t->base,
		                                     s->base,
		                                     pointer_depth + 1,
		                                     next_intermediate);
	}
	if (pa11::same_type(t, s))
		return true;
	if (t->kind == pa11::TypeKind::Record && s->kind == pa11::TypeKind::Record)
		return record_base_distance_impl(s, t) < 1000000;
	return false;
}

bool qualification_compatible(TypePtr target, TypePtr source)
{
	return qualification_compatible_impl(target, source, 0, true);
}

}  // namespace

TypePtr Parser::apply_ptr_ops(TypePtr type, const vector<PtrOp>& ops)
{
	for (size_t i = 0; i < ops.size(); ++i)
	{
		if (ops[i].kind == PtrKind::Pointer)
			type = pa11::make_cv(pa11::make_pointer(type), ops[i].cv);
		else if (ops[i].kind == PtrKind::LValueReference)
		{
			if (type->kind == pa11::TypeKind::LValueReference ||
			    type->kind == pa11::TypeKind::RValueReference)
				type = pa11::make_lvalue_reference(type->base);
			else
				type = pa11::make_lvalue_reference(type);
		}
		else if (ops[i].kind == PtrKind::RValueReference)
		{
			if (type->kind == pa11::TypeKind::LValueReference)
				type = type;
			else if (type->kind == pa11::TypeKind::RValueReference)
				type = pa11::make_rvalue_reference(type->base);
			else
				type = pa11::make_rvalue_reference(type);
		}
		else
			type = pa11::make_cv(pa11::make_member_pointer(ops[i].member_class, type),
			                     ops[i].cv);
	}
	return type;
}

TypePtr Parser::apply_suffixes(TypePtr type, const vector<Suffix>& suffixes)
{
	for (size_t i = suffixes.size(); i > 0; --i)
	{
		const Suffix& suffix = suffixes[i - 1];
		if (suffix.kind == SuffixKind::Array)
			type = pa11::make_array(type, suffix.unknown_bound, suffix.bound);
		else
		{
			vector<TypePtr> params;
			for (size_t j = 0; j < suffix.parameters.size(); ++j)
				params.push_back(suffix.parameters[j].type);
			TypePtr result = suffix.trailing_return.get() != NULL
				? suffix.trailing_return : type;
			type = pa11::make_function(result, params, suffix.variadic);
			type->cv = suffix.function_cv;
		}
	}
	return type;
}

TypePtr Parser::apply_declarator(const Declarator& declarator, TypePtr base)
{
	TypePtr type = apply_ptr_ops(base, declarator.prefix);
	type = apply_suffixes(type, declarator.suffixes);
	if (declarator.inner.get() != NULL)
		return apply_declarator(*declarator.inner, type);
	return type;
}

const QualifiedName& Parser::declarator_name(const Declarator& declarator) const
{
	if (declarator.has_name)
		return declarator.name;
	if (declarator.inner.get() != NULL)
		return declarator_name(*declarator.inner);
	throw runtime_error("declarator has no name");
}

bool Parser::declarator_has_name(const Declarator& declarator) const
{
	return declarator.has_name ||
	       (declarator.inner.get() != NULL &&
	        declarator_has_name(*declarator.inner));
}

const Suffix* Parser::declarator_function_suffix(const Declarator& declarator) const
{
	for (size_t i = 0; i < declarator.suffixes.size(); ++i)
	{
		if (declarator.suffixes[i].kind == SuffixKind::Function)
			return &declarator.suffixes[i];
	}
	if (declarator.inner.get() != NULL)
		return declarator_function_suffix(*declarator.inner);
	return NULL;
}

Binding* Parser::add_alias(Scope* scope, const string& name, TypePtr type)
{
	Binding* binding = pa11::add_binding(scope, BindingKind::TypeAlias, name, type);
	binding->target_scope = type.get() != NULL ? type->scope : NULL;
	binding->is_private =
		scope->kind == ScopeKind::Class &&
		!class_private_access_.empty() &&
		class_private_access_.back();
	binding->is_protected_member =
		scope->kind == ScopeKind::Class &&
		!class_protected_access_.empty() &&
		class_protected_access_.back();
	return binding;
}

Binding* Parser::add_value(Scope* scope,
                           BindingKind kind,
                           const string& name,
                           TypePtr type)
{
	return pa11::add_binding(scope, kind, name, type);
}

Binding* Parser::add_function_binding(Scope* scope,
                                      const string& name,
                                      TypePtr type,
                                      bool hidden_friend)
{
	map<string, vector<Binding*> >::iterator it = scope->members.find(name);
	if (it != scope->members.end())
	{
		for (size_t i = 0; i < it->second.size(); ++i)
		{
			Binding* binding = it->second[i];
			if (binding->kind == BindingKind::Function &&
			    pa11::same_type(binding->type, type))
			{
				if (!hidden_friend)
					binding->is_hidden_friend = false;
				return binding;
			}
		}
	}
	Binding* binding = add_value(scope, BindingKind::Function, name, type);
	binding->is_hidden_friend = hidden_friend;
	return binding;
}

void Parser::add_friend_function(Scope* class_scope, Binding* function)
{
	vector<Binding*>& friends = class_friend_functions_[class_scope];
	if (find(friends.begin(), friends.end(), function) == friends.end())
		friends.push_back(function);
}

void Parser::add_friend_class(Scope* class_scope, TypePtr type)
{
	vector<TypePtr>& friends = class_friend_classes_[class_scope];
	for (size_t i = 0; i < friends.size(); ++i)
		if (pa11::same_type(pa11::strip_cv(friends[i]), pa11::strip_cv(type)))
			return;
	friends.push_back(type);
}

TypePtr Parser::add_record(Scope* scope,
                           const string& name,
                           const string& tag,
                           bool complete,
                           Scope* class_scope)
{
	Binding* existing = pa11::find_owned_binding(scope, name, BindingKind::Type);
	if (existing != NULL && existing->type->kind == pa11::TypeKind::Record)
	{
		existing->type->complete = existing->type->complete || complete;
		if (class_scope != NULL)
			existing->type->scope = class_scope;
		return existing->type;
	}
	TypePtr type =
		pa11::make_record_type(scoped_type_display_name(scope, name),
		                       tag,
		                       complete,
		                       class_scope);
	Binding* binding = pa11::add_binding(scope, BindingKind::Type, name, type);
	binding->target_scope = class_scope;
	return type;
}

TypePtr Parser::add_enum(Scope* scope,
                         const string& name,
                         bool scoped,
                         EFundamentalType underlying,
                         bool complete,
                         bool create_scope)
{
	Binding* existing = pa11::find_owned_binding(scope, name, BindingKind::Type);
	if (existing != NULL && existing->type->kind == pa11::TypeKind::Enum)
		return existing->type;
	Scope* enum_scope = create_scope
		? pa11::create_child_scope(scope, ScopeKind::Enum, name)
		: NULL;
	TypePtr type =
		pa11::make_enum_type(scoped_type_display_name(scope, name),
		                     scoped,
		                     underlying,
		                     complete,
		                     enum_scope);
	Binding* binding = pa11::add_binding(scope, BindingKind::Type, name, type);
	binding->target_scope = enum_scope;
	enum_owner_scopes_[type.get()] = scope;
	return type;
}

Scope* Parser::resolve_qualifier(Binding* binding)
{
	return pa11::binding_qualifier_scope(binding);
}

vector<Binding*> Parser::lookup_qualified_set(Scope* scope,
                                              const string& name,
                                              int mask)
{
	vector<Binding*> out;
	set<Scope*> seen;
	collect_in_scope(scope, name, mask, seen, out);
	return out;
}

vector<Binding*> Parser::lookup_unqualified_set(Scope* start,
                                                const string& name,
                                                int mask)
{
	for (Scope* scope = start; scope != NULL; scope = scope->parent)
	{
		vector<Binding*> direct;
		collect_direct_in_scope(scope, name, mask, direct);
		if (!direct.empty())
			return direct;
		vector<Binding*> via_using;
		for (size_t i = 0; i < scope->using_directives.size(); ++i)
		{
			vector<Binding*> one_directive;
			set<Scope*> seen;
			collect_in_scope(scope->using_directives[i],
			                 name,
			                 mask,
			                 seen,
			                 one_directive);
			via_using.insert(via_using.end(),
			                 one_directive.begin(),
			                 one_directive.end());
		}
		if (!via_using.empty())
			return via_using;
		TypePtr record = pa11::record_type_for_scope(scope);
		TypePtr base = record.get() != NULL && record->base.get() != NULL
			? pa11::strip_cv(record->base) : TypePtr();
		if (base.get() != NULL && base->kind == pa11::TypeKind::Record &&
		    base->scope != NULL &&
		    record_dependent_base_lookup_skips_.count(
			    pa11::strip_cv(record).get()) == 0)
		{
			vector<Binding*> base_found;
			set<Scope*> seen;
			collect_in_scope(base->scope, name, mask, seen, base_found);
			if (!base_found.empty())
				return base_found;
		}
	}
	return vector<Binding*>();
}

Scope* Parser::nearest_namespace_scope(Scope* scope) const
{
	for (Scope* cur = scope; cur != NULL; cur = cur->parent)
		if (cur->kind == ScopeKind::Namespace)
			return cur;
	return global_scope();
}

vector<Binding*> Parser::resolve_name_set(const QualifiedName& name, int mask)
{
	if (name.qualifier != NULL)
		return lookup_qualified_set(name.qualifier, name.name, mask);
	return lookup_unqualified_set(current_scope(), name.name, mask);
}

Binding* Parser::resolve_single_name(const QualifiedName& name, int mask)
{
	vector<Binding*> found = resolve_name_set(name, mask);
	if (found.empty())
		return NULL;
	for (size_t i = 0; i < found.size(); ++i)
	{
		if (found[i]->kind != BindingKind::Function)
			return found[i];
	}
	return found[0];
}

TypePtr Parser::expression_object_type(TypePtr type) const
{
	if (type->kind == pa11::TypeKind::LValueReference ||
	    type->kind == pa11::TypeKind::RValueReference)
		return type->base;
	return type;
}

TypePtr Parser::lvalue_to_rvalue_type(TypePtr type) const
{
	TypePtr object = expression_object_type(type);
	if (object->kind == pa11::TypeKind::Array)
		return pa11::make_pointer(object->base);
	if (object->kind == pa11::TypeKind::Function)
		return pa11::make_pointer(object);
	return pa11::strip_top_level_cv(object);
}

bool Parser::is_zero_literal(const Expr& expr) const
{
	return expr.null_pointer_constant;
}

bool Parser::types_reference_compatible(TypePtr target, TypePtr source) const
{
	return qualification_compatible(target, source);
}

int Parser::record_base_distance(TypePtr source, TypePtr target) const
{
	return record_base_distance_impl(source, target);
}

bool Parser::active_function_matches(Binding* function) const
{
	if (active_functions_.empty() || function == NULL)
		return false;
	Binding* active = active_functions_.back();
	if (active == function)
		return true;
	return active->owner == function->owner &&
	       active->name == function->name &&
	       pa11::same_type(active->type, function->type);
}

bool Parser::active_context_has_class_access(Scope* class_scope) const
{
	if (class_scope == NULL)
		return false;
	Binding* active = active_functions_.empty() ? NULL : active_functions_.back();
	Scope* active_class =
		active != NULL && active->owner != NULL &&
		active->owner->kind == ScopeKind::Class ? active->owner : NULL;
	if (active_class == class_scope)
		return true;
	for (Scope* parent = active_class != NULL ? active_class->parent : NULL;
	     parent != NULL;
	     parent = parent->parent)
	{
		if (parent == class_scope)
			return true;
	}
	TypePtr class_type = pa11::record_type_for_scope(class_scope);
	if (active_class != NULL && class_type.get() != NULL)
	{
		TypePtr active_type = pa11::record_type_for_scope(active_class);
		if (active_type.get() != NULL &&
		    record_base_distance(active_type, class_type) < 1000000)
			return true;
	}
	map<Scope*, vector<Binding*> >::const_iterator fit =
		class_friend_functions_.find(class_scope);
	if (fit != class_friend_functions_.end())
	{
		for (size_t i = 0; i < fit->second.size(); ++i)
			if (active_function_matches(fit->second[i]))
				return true;
	}
	if (active_class == NULL)
		return false;
	map<Scope*, vector<TypePtr> >::const_iterator cit =
		class_friend_classes_.find(class_scope);
	if (cit == class_friend_classes_.end())
		return false;
	for (size_t i = 0; i < cit->second.size(); ++i)
	{
		TypePtr friend_type = pa11::strip_cv(cit->second[i]);
		if (friend_type->kind == pa11::TypeKind::Record &&
		    friend_type->scope == active_class)
			return true;
	}
	return false;
}

bool Parser::member_access_allowed(Binding* member, TypePtr object_record) const
{
	if (member == NULL)
		return true;
	if (member->is_private && !active_context_has_class_access(member->owner))
		return false;
	if (!member->is_protected_member)
		return true;
	if (active_context_has_class_access(member->owner))
		return true;
	TypePtr object = object_record.get() != NULL
		? pa11::strip_cv(object_record) : TypePtr();
	if (object.get() != NULL && object->kind == pa11::TypeKind::Record &&
	    active_context_has_class_access(object->scope))
		return true;
	return false;
}

bool Parser::type_can_bind_reference(TypePtr target, const Expr& expr) const
{
	TypePtr source = expression_object_type(expr.type);
	if (target->kind == pa11::TypeKind::LValueReference)
	{
		if (types_reference_compatible(target->base, source))
		{
			if (expr.category == ValueCategory::LValue)
				return true;
			return pa11::type_has_const(target->base);
		}
		return false;
	}
	if (target->kind == pa11::TypeKind::RValueReference)
	{
		if (expr.category == ValueCategory::LValue)
			return false;
		return types_reference_compatible(target->base, source);
	}
	return false;
}

bool Parser::pointer_conversion_viable(TypePtr source, TypePtr target) const
{
	TypePtr src = pa11::strip_cv(source);
	TypePtr dst = pa11::strip_cv(target);
	if (src->kind != pa11::TypeKind::Pointer ||
	    dst->kind != pa11::TypeKind::Pointer)
		return false;
	TypePtr src_pointee = src->base;
	TypePtr dst_pointee = dst->base;
	if (qualification_compatible(target, source))
		return true;
	TypePtr bare_dst = pa11::strip_cv(dst_pointee);
	if (bare_dst->kind != pa11::TypeKind::Fundamental ||
	    bare_dst->fundamental != FT_VOID)
		return false;
	return cv_contains(cv_flags(dst_pointee), cv_flags(src_pointee));
}

int Parser::scalar_conversion_rank(TypePtr source, TypePtr target) const
{
	TypePtr src = lvalue_to_rvalue_type(source);
	TypePtr dst = pa11::strip_top_level_cv(target);
	if (pa11::same_type(src, dst))
		return 0;
	TypePtr src_bare = pa11::strip_cv(src);
	TypePtr dst_bare = pa11::strip_cv(dst);
	if (dst_bare->kind == pa11::TypeKind::Enum)
		return 1000000;
	if (src_bare->kind == pa11::TypeKind::Enum && src_bare->scoped_enum)
		return 1000000;
	if (pa11::is_integral_or_bool_type(src) &&
	    dst_bare->kind == pa11::TypeKind::Fundamental &&
	    dst_bare->fundamental == FT_INT)
		return 1;
	if (pa11::is_integral_or_bool_type(src) && pa11::is_integral_or_bool_type(dst))
		return 2;
	if (type_is_arithmetic(src) && type_is_arithmetic(dst))
		return 2;
	if (type_is_pointer(src) && type_is_pointer(dst))
	{
		if (pointer_conversion_viable(src, dst))
		{
			TypePtr src_pointee = pa11::strip_cv(src)->base;
			TypePtr dst_pointee = pa11::strip_cv(dst)->base;
			int cv_rank =
				(cv_flags(dst_pointee) & ~cv_flags(src_pointee)) != 0 ? 1 : 0;
			int distance = record_base_distance(src_pointee, dst_pointee);
			if (distance < 1000000)
				return distance + cv_rank;
			return 4 + cv_rank;
		}
	}
	if (type_is_pointer(src) &&
	    pa11::strip_cv(dst)->kind == pa11::TypeKind::Fundamental &&
	    pa11::strip_cv(dst)->fundamental == FT_BOOL)
		return 6;
	return 1000000;
}

TypePtr Parser::usual_arithmetic_type(TypePtr left, TypePtr right) const
{
	TypePtr l = lvalue_to_rvalue_type(left);
	TypePtr r = lvalue_to_rvalue_type(right);
	l = integral_promotion(l);
	r = integral_promotion(r);
	if (pa11::same_type(l, r))
		return l;
	if (type_is_floating(l))
	{
		if (type_is_floating(r) && arithmetic_rank(r) > arithmetic_rank(l))
			return r;
		return l;
	}
	if (type_is_floating(r))
		return r;
	if (pa11::strip_cv(l)->kind == pa11::TypeKind::Enum &&
	    pa11::strip_cv(r)->kind == pa11::TypeKind::Enum)
		return pa11::make_fundamental(FT_INT);
	if (pa11::strip_cv(l)->kind == pa11::TypeKind::Enum)
		return pa11::is_integral_or_bool_type(r) ? r :
			pa11::make_fundamental(FT_INT);
	if (pa11::strip_cv(r)->kind == pa11::TypeKind::Enum)
		return pa11::is_integral_or_bool_type(l) ? l :
			pa11::make_fundamental(FT_INT);
	if (pa11::is_integral_or_bool_type(l) && pa11::is_integral_or_bool_type(r))
	{
		if (arithmetic_rank(r) > arithmetic_rank(l))
			return r;
		return l;
	}
	return l;
}

ValueCategory Parser::call_category(TypePtr result) const
{
	if (result->kind == pa11::TypeKind::LValueReference)
		return ValueCategory::LValue;
	if (result->kind == pa11::TypeKind::RValueReference)
		return ValueCategory::XValue;
	return ValueCategory::PRValue;
}

string Parser::value_category_name(ValueCategory category) const
{
	if (category == ValueCategory::LValue)
		return "lvalue";
	if (category == ValueCategory::XValue)
		return "xvalue";
	return "prvalue";
}

string Parser::qualified_decl_name(const Binding* binding) const
{
	if (binding->aliased_binding != NULL)
		binding = binding->aliased_binding;
	vector<string> parts;
	for (Scope* s = binding->owner; s != NULL; s = s->parent)
	{
		if ((s->kind == ScopeKind::Namespace || s->kind == ScopeKind::Class) &&
		    !s->name.empty() && s->name != "<unnamed>")
			parts.push_back(s->name);
	}
	ostringstream out;
	for (size_t i = parts.size(); i > 0; --i)
		out << parts[i - 1] << "::";
	out << binding->name;
	return out.str();
}

string Parser::scoped_type_display_name(Scope* owner, const string& name) const
{
	vector<string> parts;
	for (Scope* s = owner; s != NULL; s = s->parent)
	{
		if (s->kind == ScopeKind::Namespace &&
		    !s->name.empty() && s->name != "<unnamed>")
			parts.push_back(s->name);
	}
	string out;
	for (size_t i = parts.size(); i > 0; --i)
		out += parts[i - 1] + "::";
	return out + name;
}

string Parser::class_tag(ETokenType key) const
{
	if (key == KW_CLASS)
		return "class";
	if (key == KW_UNION)
		return "union";
	return "struct";
}

string Parser::make_local_type_name(const string& prefix)
{
	++local_type_counter_;
	return prefix + to_string(local_type_counter_);
}

string Parser::op_leaf(ETokenType type, const string& source) const
{
	return TokenTypeToStringMap.at(type) + ":" + source;
}

}  // namespace internal
}  // namespace pa12
