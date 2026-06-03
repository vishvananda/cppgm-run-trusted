#include "nsinit_internal.h"

#include <algorithm>
#include <sstream>
#include <stdexcept>
#include <utility>

using namespace std;

namespace nsinit {
namespace {

TypePtr new_type(TypeKind kind)
{
	return TypePtr(new Type(kind));
}

bool entity_matches(Entity* entity, int mask)
{
	if (entity == NULL)
		return false;
	if ((mask & LOOKUP_NAMESPACE) &&
	    (entity->kind == EntityKind::Namespace ||
	     entity->kind == EntityKind::NamespaceAlias))
		return true;
	if ((mask & LOOKUP_TYPE) && entity->kind == EntityKind::TypeAlias)
		return true;
	if ((mask & LOOKUP_VARIABLE) && entity->kind == EntityKind::Variable)
		return true;
	if ((mask & LOOKUP_FUNCTION) && entity->kind == EntityKind::Function)
		return true;
	return false;
}

bool has_any_member(Namespace* ns, const string& name)
{
	map<string, vector<Entity*> >::const_iterator it = ns->members.find(name);
	return it != ns->members.end() && !it->second.empty();
}

bool has_conflicting_non_namespace_member(Namespace* ns, const string& name)
{
	map<string, vector<Entity*> >::const_iterator it = ns->members.find(name);
	if (it == ns->members.end())
		return false;
	for (size_t i = 0; i < it->second.size(); ++i)
	{
		if (it->second[i]->kind != EntityKind::Namespace)
			return true;
	}
	return false;
}

Entity* find_owned_member(Namespace* ns, const string& name, EntityKind kind)
{
	map<string, vector<Entity*> >::iterator it = ns->members.find(name);
	if (it == ns->members.end())
		return NULL;
	for (size_t i = 0; i < it->second.size(); ++i)
	{
		Entity* entity = it->second[i];
		if (entity->owner == ns && entity->kind == kind)
			return entity;
	}
	return NULL;
}

Entity* new_entity(TranslationUnit& tu,
                   Namespace* ns,
                   EntityKind kind,
                   const string& name,
                   size_t order)
{
	unique_ptr<Entity> entity(new Entity(kind, name, ns));
	entity->order = order;
	Entity* raw = entity.get();
	tu.entities.push_back(std::move(entity));
	ns->members[name].push_back(raw);
	return raw;
}

bool lookup_seen_insert(set<Namespace*>& seen, Namespace* ns)
{
	return ns != NULL && seen.insert(ns).second;
}

Entity* lookup_in_namespace(Namespace* ns,
                            const string& name,
                            int mask,
                            set<Namespace*>& seen)
{
	if (!lookup_seen_insert(seen, ns))
		return NULL;
	map<string, vector<Entity*> >::iterator it = ns->members.find(name);
	if (it != ns->members.end())
	{
		for (size_t i = 0; i < it->second.size(); ++i)
		{
			if (entity_matches(it->second[i], mask))
				return it->second[i];
		}
	}
	for (size_t i = 0; i < ns->using_directives.size(); ++i)
	{
		Entity* found = lookup_in_namespace(ns->using_directives[i],
		                                    name,
		                                    mask,
		                                    seen);
		if (found != NULL)
			return found;
	}
	return NULL;
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

bool same_parameter_function_type(const TypePtr& left, const TypePtr& right)
{
	return left->kind == TypeKind::Function &&
	       right->kind == TypeKind::Function &&
	       same_type(left, right);
}

bool is_const_default_forbidden(const TypePtr& type)
{
	if (is_reference_type(type))
		return true;
	if (type->kind == TypeKind::Array)
		return is_const_default_forbidden(type->base);
	return type_has_const(type);
}

size_t fundamental_size(EFundamentalType type)
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

}  // namespace

Type::Type(TypeKind k)
	: kind(k),
	  fundamental(FT_INT),
	  cv(CV_NONE),
	  unknown_bound(false),
	  bound(0),
	  variadic(false)
{
}

QualifiedName::QualifiedName() : qualifier(NULL)
{
}

Expr::Expr(ExprKind k)
	: kind(k),
	  bool_value(false),
	  lookup_scope(NULL),
	  string_literal(NULL)
{
}

InitPlan::InitPlan()
	: address_entity(NULL),
	  address_string(NULL),
	  address_temporary(NULL)
{
}

Entity::Entity(EntityKind k, const string& n, Namespace* o)
	: kind(k),
	  name(n),
	  owner(o),
	  target_namespace(NULL),
	  storage(StorageClass::None),
	  declared_extern(false),
	  is_constexpr(false),
	  is_inline(false),
	  is_definition(false),
	  has_initializer(false),
	  order(0),
	  linked(NULL),
	  evaluating_constant(false),
	  constant_ready(false),
	  constant_valid(false),
	  constant_integer(0),
	  constant_pointer_ready(false),
	  constant_pointer_valid(false),
	  constant_pointer_entity(NULL),
	  constant_pointer_string(NULL)
{
}

Namespace::Namespace(const string& n, bool has_name, bool inline_ns, Namespace* p)
	: name(n),
	  named(has_name),
	  is_inline(inline_ns),
	  contains_unnamed(!has_name && p != NULL),
	  parent(p),
	  unnamed_namespace(NULL)
{
}

StringLiteral::StringLiteral()
	: element_type(FT_CHAR), elements(0), order(0), offset(0)
{
}

LinkedEntity::LinkedEntity()
	: kind(EntityKind::Variable),
	  first(NULL),
	  order(0),
	  has_definition(false),
	  definition(NULL),
	  non_inline_definition_seen(false),
	  emitted(false),
	  offset(0)
{
}

Temporary::Temporary() : order(0), offset(0)
{
}

Program::Program() : next_order(0)
{
}

ExprValue::ExprValue()
	: category(ValueCategory::Prvalue),
	  valid(false),
	  known_integer(false),
	  integer(0),
	  known_floating(false),
	  floating_type(FT_DOUBLE),
	  is_null_pointer(false),
	  address_entity(NULL),
	  address_string(NULL),
	  string_literal(false)
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
		throw runtime_error("invalid reference declarator");
	TypePtr type = new_type(TypeKind::Pointer);
	type->base = base;
	return type;
}

TypePtr make_lvalue_reference(TypePtr base)
{
	if (is_reference_type(base) || is_void_type(base))
		throw runtime_error("invalid reference declarator");
	TypePtr type = new_type(TypeKind::LValueReference);
	type->base = base;
	return type;
}

TypePtr make_rvalue_reference(TypePtr base)
{
	if (is_reference_type(base) || is_void_type(base))
		throw runtime_error("invalid reference declarator");
	TypePtr type = new_type(TypeKind::RValueReference);
	type->base = base;
	return type;
}

TypePtr make_array(TypePtr element, bool unknown, uint64_t bound)
{
	if (is_void_type(element) || element->kind == TypeKind::Function ||
	    is_reference_type(element))
		throw runtime_error("invalid array declarator");
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
	vector<TypePtr> adjusted;
	for (size_t i = 0; i < parameters.size(); ++i)
		adjusted.push_back(adjust_parameter_type(parameters[i]));
	if (!variadic && adjusted.size() == 1 && is_void_type(adjusted[0]))
		adjusted.clear();
	TypePtr type = new_type(TypeKind::Function);
	type->base = result;
	type->parameters = adjusted;
	type->variadic = variadic;
	return type;
}

TypePtr adjust_parameter_type(TypePtr type)
{
	type = strip_top_level_cv(type);
	if (type->kind == TypeKind::Array)
		return make_pointer(type->base);
	if (type->kind == TypeKind::Function)
		return make_pointer(type);
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

bool is_floating_type(const TypePtr& type)
{
	TypePtr bare = strip_cv(type);
	return bare->kind == TypeKind::Fundamental &&
	       (bare->fundamental == FT_FLOAT ||
	        bare->fundamental == FT_DOUBLE ||
	        bare->fundamental == FT_LONG_DOUBLE);
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
	}
	throw logic_error("unknown type kind");
}

size_t type_size(const TypePtr& type)
{
	if (type->kind == TypeKind::Cv)
		return type_size(type->base);
	if (type->kind == TypeKind::Fundamental)
		return fundamental_size(type->fundamental);
	if (type->kind == TypeKind::Pointer || is_reference_type(type))
		return 8;
	if (type->kind == TypeKind::Function)
		return 4;
	if (type->kind == TypeKind::Array)
	{
		if (type->unknown_bound)
			throw runtime_error("incomplete object type");
		return static_cast<size_t>(type->bound) * type_size(type->base);
	}
	throw logic_error("unknown type kind");
}

size_t type_align(const TypePtr& type)
{
	if (type->kind == TypeKind::Cv)
		return type_align(type->base);
	if (type->kind == TypeKind::Array)
		return type_align(type->base);
	if (type->kind == TypeKind::Pointer || is_reference_type(type))
		return 8;
	if (type->kind == TypeKind::Function)
		return 4;
	return type_size(type);
}

bool is_complete_object_type(const TypePtr& type)
{
	TypePtr bare = strip_cv(type);
	if (bare->kind == TypeKind::Fundamental)
		return bare->fundamental != FT_VOID;
	if (bare->kind == TypeKind::Array)
		return !bare->unknown_bound && is_complete_object_type(bare->base);
	if (bare->kind == TypeKind::Function)
		return true;
	if (bare->kind == TypeKind::Pointer || is_reference_type(bare))
		return true;
	return is_complete_object_type(bare->base);
}

bool can_default_initialize(const TypePtr& type)
{
	return !is_const_default_forbidden(type);
}

Namespace* get_or_create_named_namespace(TranslationUnit& tu,
                                         Namespace* parent,
                                         const string& name,
                                         bool is_inline)
{
	if (has_conflicting_non_namespace_member(parent, name))
		throw runtime_error("namespace alias misuse");
	map<string, Namespace*>::iterator existing =
		parent->named_namespaces.find(name);
	if (existing != parent->named_namespaces.end())
	{
		if (is_inline && !existing->second->is_inline)
			throw runtime_error("extension namespace cannot be inline");
		if (is_inline)
			add_using_directive(parent, existing->second);
		return existing->second;
	}
	unique_ptr<Namespace> child(new Namespace(name, true, is_inline, parent));
	Namespace* raw = child.get();
	parent->owned_namespaces.push_back(std::move(child));
	parent->namespace_order.push_back(raw);
	parent->named_namespaces[name] = raw;
	Entity* entity = new_entity(tu, parent, EntityKind::Namespace, name, 0);
	entity->target_namespace = raw;
	if (is_inline)
		add_using_directive(parent, raw);
	return raw;
}

Namespace* create_unnamed_namespace(TranslationUnit&,
                                    Namespace* parent,
                                    bool is_inline)
{
	if (parent->unnamed_namespace != NULL)
	{
		if (is_inline)
			parent->unnamed_namespace->is_inline = true;
		return parent->unnamed_namespace;
	}
	unique_ptr<Namespace> child(new Namespace("", false, is_inline, parent));
	Namespace* raw = child.get();
	parent->owned_namespaces.push_back(std::move(child));
	parent->namespace_order.push_back(raw);
	parent->unnamed_namespace = raw;
	for (Namespace* ns = raw; ns != NULL; ns = ns->parent)
		ns->contains_unnamed = true;
	add_using_directive(parent, raw);
	return raw;
}

Entity* add_type_alias(TranslationUnit& tu,
                       Namespace* ns,
                       const string& name,
                       TypePtr type,
                       size_t order)
{
	if (has_any_member(ns, name) &&
	    find_owned_member(ns, name, EntityKind::TypeAlias) == NULL)
		throw runtime_error("namespace alias misuse");
	Entity* existing = find_owned_member(ns, name, EntityKind::TypeAlias);
	if (existing != NULL)
	{
		existing->type = type;
		return existing;
	}
	Entity* entity = new_entity(tu, ns, EntityKind::TypeAlias, name, order);
	entity->type = type;
	return entity;
}

Entity* add_variable(TranslationUnit& tu,
                     Namespace* ns,
                     const string& name,
                     TypePtr type,
                     StorageClass storage,
                     bool is_constexpr,
                     bool is_definition,
                     const Initializer* initializer,
                     size_t order)
{
	if (has_any_member(ns, name) &&
	    find_owned_member(ns, name, EntityKind::Variable) == NULL)
		throw runtime_error("namespace alias misuse");
	Entity* existing = find_owned_member(ns, name, EntityKind::Variable);
	if (existing != NULL)
	{
		if (!same_type(existing->type, type))
		{
			const bool old_unknown =
				existing->type->kind == TypeKind::Array &&
				existing->type->unknown_bound;
			const bool new_complete =
				type->kind == TypeKind::Array &&
				!type->unknown_bound &&
				same_type(existing->type->base, type->base);
			if (!old_unknown || !new_complete)
				throw runtime_error("conflicting variable declaration");
			existing->type = type;
		}
		existing->declared_extern =
			existing->declared_extern || storage == StorageClass::Extern;
		existing->is_constexpr = existing->is_constexpr || is_constexpr;
		if (is_definition)
		{
			if (existing->is_definition)
				throw runtime_error("duplicate variable definition");
			existing->is_definition = true;
			existing->storage = storage;
			existing->has_initializer = initializer != NULL;
			if (initializer != NULL)
				existing->initializer = *initializer;
		}
		return existing;
	}
	Entity* entity = new_entity(tu, ns, EntityKind::Variable, name, order);
	entity->type = type;
	entity->storage = storage;
	entity->declared_extern = storage == StorageClass::Extern;
	entity->is_constexpr = is_constexpr;
	entity->is_definition = is_definition;
	entity->has_initializer = initializer != NULL;
	if (initializer != NULL)
		entity->initializer = *initializer;
	return entity;
}

Entity* add_function(TranslationUnit& tu,
                     Namespace* ns,
                     const string& name,
                     TypePtr type,
                     StorageClass storage,
                     bool is_inline,
                     bool is_definition,
                     size_t order)
{
	if (has_any_member(ns, name))
	{
		map<string, vector<Entity*> >::iterator it = ns->members.find(name);
		for (size_t i = 0; i < it->second.size(); ++i)
		{
			if (it->second[i]->kind != EntityKind::Function)
				throw runtime_error("namespace alias misuse");
		}
	}
	map<string, vector<Entity*> >::iterator it = ns->members.find(name);
	if (it != ns->members.end())
	{
		for (size_t i = 0; i < it->second.size(); ++i)
		{
			Entity* existing = it->second[i];
			if (existing->owner == ns &&
			    existing->kind == EntityKind::Function &&
			    same_parameter_function_type(existing->type, type))
			{
				existing->declared_extern =
					existing->declared_extern ||
					storage == StorageClass::Extern;
				existing->is_inline = existing->is_inline || is_inline;
				if (is_definition)
				{
					if (existing->is_definition &&
					    !(existing->is_inline || is_inline))
						throw runtime_error("duplicate function definition");
					existing->is_definition = true;
				}
				return existing;
			}
		}
	}
	Entity* entity = new_entity(tu, ns, EntityKind::Function, name, order);
	entity->type = type;
	entity->storage = storage;
	entity->declared_extern = storage == StorageClass::Extern;
	entity->is_inline = is_inline;
	entity->is_definition = is_definition;
	return entity;
}

Entity* add_namespace_alias(TranslationUnit& tu,
                            Namespace* ns,
                            const string& name,
                            Namespace* target,
                            size_t order)
{
	(void)target;
	if (has_any_member(ns, name))
		throw runtime_error("namespace alias misuse");
	Entity* entity = new_entity(tu, ns, EntityKind::NamespaceAlias, name, order);
	entity->target_namespace = target;
	return entity;
}

void add_using_declaration(Namespace* ns, const string& name, Entity* entity)
{
	if (entity == NULL || entity->kind == EntityKind::Namespace ||
	    entity->kind == EntityKind::NamespaceAlias)
		throw runtime_error("namespace alias misuse");
	ns->members[name].push_back(entity);
}

void add_using_directive(Namespace* ns, Namespace* target)
{
	if (find(ns->using_directives.begin(),
	         ns->using_directives.end(),
	         target) == ns->using_directives.end())
		ns->using_directives.push_back(target);
}

Namespace* resolve_namespace(Entity* entity)
{
	if (entity == NULL)
		return NULL;
	if (entity->kind == EntityKind::Namespace ||
	    entity->kind == EntityKind::NamespaceAlias)
		return entity->target_namespace;
	return NULL;
}

Entity* lookup_qualified(Namespace* ns, const string& name, int mask)
{
	set<Namespace*> seen;
	return lookup_in_namespace(ns, name, mask, seen);
}

Entity* lookup_unqualified(Namespace* start, const string& name, int mask)
{
	for (Namespace* ns = start; ns != NULL; ns = ns->parent)
	{
		set<Namespace*> seen;
		Entity* found = lookup_in_namespace(ns, name, mask, seen);
		if (found != NULL)
			return found;
	}
	return NULL;
}

bool namespace_encloses(Namespace* possible_encloser, Namespace* child)
{
	for (Namespace* ns = child; ns != NULL; ns = ns->parent)
	{
		if (ns == possible_encloser)
			return true;
	}
	return false;
}

bool namespace_has_internal_linkage(Namespace* ns)
{
	for (Namespace* current = ns; current != NULL; current = current->parent)
	{
		if (!current->named && current->parent != NULL)
			return true;
	}
	return false;
}

StringLiteral* add_string_literal(TranslationUnit& tu,
                                  const string& source,
                                  size_t order)
{
	StringLiteralInfo info;
	if (!AnalyzeStringLiteral(source, info) || !info.ud_suffix.empty())
		throw runtime_error("invalid string literal");
	unique_ptr<StringLiteral> literal(new StringLiteral());
	literal->source = source;
	literal->element_type = info.type;
	literal->elements = info.elements;
	literal->bytes = info.bytes;
	literal->type = make_array(make_fundamental(info.type),
	                           false,
	                           static_cast<uint64_t>(info.elements));
	literal->order = order;
	StringLiteral* raw = literal.get();
	tu.string_literals.push_back(std::move(literal));
	return raw;
}

void append_zeroes(vector<unsigned char>& out, size_t count)
{
	out.insert(out.end(), count, 0);
}

void append_integer_le(vector<unsigned char>& out, uint64_t value, size_t size)
{
	const size_t old = out.size();
	out.resize(old + size);
	write_integer_le(out, old, value, size);
}

void write_integer_le(vector<unsigned char>& out,
                      size_t offset,
                      uint64_t value,
                      size_t size)
{
	if (out.size() < offset + size)
		out.resize(offset + size, 0);
	for (size_t i = 0; i < size; ++i)
		out[offset + i] =
			static_cast<unsigned char>((value >> (i * 8)) & 0xff);
}

}  // namespace nsinit
