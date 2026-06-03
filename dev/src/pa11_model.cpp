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
	case FT_LONG_DOUBLE:
		return 16;
	case FT_VOID:
		break;
	}
	throw runtime_error("incomplete object type");
}

bool same_function_type(const TypePtr& left, const TypePtr& right)
{
	if (left->variadic != right->variadic ||
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
	return NULL;
}

}  // namespace

Type::Type(TypeKind k)
	: kind(k),
	  fundamental(FT_INT),
	  cv(CV_NONE),
	  unknown_bound(false),
	  bound(0),
	  variadic(false),
	  scoped_enum(false),
	  complete(true),
	  enum_underlying(FT_INT),
	  scope(NULL)
{
}

Binding::Binding(BindingKind k, const string& n, Scope* o)
	: kind(k),
	  name(n),
	  owner(o),
	  target_scope(NULL),
	  has_constant(false),
	  constant_value(0)
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
	if (is_reference_type(base))
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

TypePtr make_template_template_parameter_type(const string& name)
{
	TypePtr type = new_type(TypeKind::TemplateTemplateParameter);
	type->name = name;
	return type;
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
	case FT_UNSIGNED_CHAR:
	case FT_UNSIGNED_SHORT_INT:
	case FT_UNSIGNED_INT:
	case FT_UNSIGNED_LONG_INT:
	case FT_UNSIGNED_LONG_LONG_INT:
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
		return same_function_type(left, right);
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
		       ") returning " + describe_type(type->base);
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
		return 1;
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
		return 1;
	}
	return type_size(bare);
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
	binding->has_constant = target->has_constant;
	binding->constant_value = target->constant_value;
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
