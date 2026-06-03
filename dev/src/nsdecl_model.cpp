#include "nsdecl_internal.h"

#include <algorithm>
#include <set>
#include <sstream>
#include <stdexcept>
#include <utility>

using namespace std;

namespace nsdecl {
namespace {

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
                   const string& name)
{
	unique_ptr<Entity> entity(new Entity(kind, name, ns));
	Entity* raw = entity.get();
	tu.entities.push_back(std::move(entity));
	ns->members[name].push_back(raw);
	return raw;
}

TypePtr new_type(TypeKind kind)
{
	return TypePtr(new Type(kind));
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

TypePtr strip_top_level_cv(TypePtr type)
{
	if (type->kind == TypeKind::Cv)
		return type->base;
	return type;
}

bool is_unknown_array(const TypePtr& type)
{
	return type->kind == TypeKind::Array && type->unknown_bound;
}

bool should_update_variable_type(const TypePtr& old_type, const TypePtr& new_type)
{
	if (same_type(old_type, new_type))
		return false;
	if (is_unknown_array(old_type) &&
	    new_type->kind == TypeKind::Array &&
	    same_type(old_type->base, new_type->base))
		return true;
	return false;
}

void emit_namespace(const Namespace& ns, ostream& out)
{
	if (ns.named)
		out << "start namespace " << ns.name << '\n';
	else
		out << "start unnamed namespace\n";
	if (ns.is_inline)
		out << "inline namespace\n";
	for (size_t i = 0; i < ns.variable_order.size(); ++i)
	{
		Entity* entity = ns.variable_order[i];
		out << "variable " << entity->name << ' '
		    << describe_type(entity->type) << '\n';
	}
	for (size_t i = 0; i < ns.function_order.size(); ++i)
	{
		Entity* entity = ns.function_order[i];
		out << "function " << entity->name << ' '
		    << describe_type(entity->type) << '\n';
	}
	for (size_t i = 0; i < ns.namespace_order.size(); ++i)
		emit_namespace(*ns.namespace_order[i], out);
	out << "end namespace\n";
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

Entity::Entity(EntityKind k, const string& n, Namespace* o)
	: kind(k), name(n), owner(o), target_namespace(NULL)
{
}

Namespace::Namespace(const string& n, bool has_name, bool inline_ns, Namespace* p)
	: name(n),
	  named(has_name),
	  is_inline(inline_ns),
	  parent(p),
	  unnamed_namespace(NULL)
{
}

QualifiedName::QualifiedName() : qualifier(NULL)
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
	if (base->kind == TypeKind::LValueReference ||
	    base->kind == TypeKind::RValueReference)
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
	TypePtr type = new_type(TypeKind::Pointer);
	type->base = base;
	return type;
}

TypePtr make_lvalue_reference(TypePtr base)
{
	if (base->kind == TypeKind::LValueReference)
		return base;
	if (base->kind == TypeKind::RValueReference)
		base = base->base;
	TypePtr type = new_type(TypeKind::LValueReference);
	type->base = base;
	return type;
}

TypePtr make_rvalue_reference(TypePtr base)
{
	if (base->kind == TypeKind::LValueReference ||
	    base->kind == TypeKind::RValueReference)
		return base;
	TypePtr type = new_type(TypeKind::RValueReference);
	type->base = base;
	return type;
}

TypePtr make_array(TypePtr element, bool unknown, unsigned long long bound)
{
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

bool is_void_type(const TypePtr& type)
{
	return type->kind == TypeKind::Fundamental && type->fundamental == FT_VOID;
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

Namespace* get_or_create_named_namespace(TranslationUnit& tu,
                                         Namespace* parent,
                                         const string& name,
                                         bool is_inline)
{
	map<string, Namespace*>::iterator existing =
		parent->named_namespaces.find(name);
	if (existing != parent->named_namespaces.end())
	{
		if (is_inline)
		{
			existing->second->is_inline = true;
			add_using_directive(parent, existing->second);
		}
		return existing->second;
	}
	unique_ptr<Namespace> child(new Namespace(name, true, is_inline, parent));
	Namespace* raw = child.get();
	parent->owned_namespaces.push_back(std::move(child));
	parent->namespace_order.push_back(raw);
	parent->named_namespaces[name] = raw;
	Entity* entity = new_entity(tu, parent, EntityKind::Namespace, name);
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
	add_using_directive(parent, raw);
	return raw;
}

Entity* add_type_alias(TranslationUnit& tu,
                       Namespace* ns,
                       const string& name,
                       TypePtr type)
{
	Entity* existing = find_owned_member(ns, name, EntityKind::TypeAlias);
	if (existing != NULL)
	{
		existing->type = type;
		return existing;
	}
	Entity* entity = new_entity(tu, ns, EntityKind::TypeAlias, name);
	entity->type = type;
	return entity;
}

Entity* add_variable(TranslationUnit& tu,
                     Namespace* ns,
                     const string& name,
                     TypePtr type)
{
	Entity* existing = find_owned_member(ns, name, EntityKind::Variable);
	if (existing != NULL)
	{
		if (should_update_variable_type(existing->type, type))
			existing->type = type;
		return existing;
	}
	Entity* entity = new_entity(tu, ns, EntityKind::Variable, name);
	entity->type = type;
	ns->variable_order.push_back(entity);
	return entity;
}

Entity* add_function(TranslationUnit& tu,
                     Namespace* ns,
                     const string& name,
                     TypePtr type)
{
	Entity* existing = find_owned_member(ns, name, EntityKind::Function);
	if (existing != NULL)
	{
		existing->type = type;
		return existing;
	}
	Entity* entity = new_entity(tu, ns, EntityKind::Function, name);
	entity->type = type;
	ns->function_order.push_back(entity);
	return entity;
}

Entity* add_namespace_alias(TranslationUnit& tu,
                            Namespace* ns,
                            const string& name,
                            Namespace* target)
{
	Entity* existing = find_owned_member(ns, name, EntityKind::NamespaceAlias);
	if (existing != NULL)
	{
		existing->target_namespace = target;
		return existing;
	}
	Entity* entity = new_entity(tu, ns, EntityKind::NamespaceAlias, name);
	entity->target_namespace = target;
	return entity;
}

void add_using_declaration(Namespace* ns, const string& name, Entity* entity)
{
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

void emit_translation_unit(const TranslationUnit& tu, ostream& out)
{
	out << "start translation unit " << tu.srcfile << '\n';
	emit_namespace(*tu.global_namespace, out);
	out << "end translation unit\n";
}

}  // namespace nsdecl
