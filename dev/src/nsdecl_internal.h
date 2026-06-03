#pragma once

#include <iosfwd>
#include <map>
#include <memory>
#include <string>
#include <vector>

#include "nsdecl_support.h"
#include "posttoken_pipeline.h"
#include "posttoken_support.h"

using namespace std;

namespace nsdecl {

enum CvFlags
{
	CV_NONE = 0,
	CV_CONST = 1,
	CV_VOLATILE = 2
};

enum class TypeKind
{
	Fundamental,
	Cv,
	Pointer,
	LValueReference,
	RValueReference,
	Array,
	Function
};

struct Type;
typedef shared_ptr<Type> TypePtr;

struct Type
{
	TypeKind kind;
	EFundamentalType fundamental;
	unsigned cv;
	TypePtr base;
	bool unknown_bound;
	unsigned long long bound;
	vector<TypePtr> parameters;
	bool variadic;

	explicit Type(TypeKind k);
};

enum class EntityKind
{
	Namespace,
	NamespaceAlias,
	TypeAlias,
	Variable,
	Function
};

struct Namespace;

struct Entity
{
	EntityKind kind;
	string name;
	Namespace* owner;
	TypePtr type;
	Namespace* target_namespace;

	Entity(EntityKind k, const string& n, Namespace* o);
};

struct Namespace
{
	string name;
	bool named;
	bool is_inline;
	Namespace* parent;
	vector<unique_ptr<Namespace> > owned_namespaces;
	vector<Namespace*> namespace_order;
	map<string, Namespace*> named_namespaces;
	Namespace* unnamed_namespace;
	map<string, vector<Entity*> > members;
	vector<Entity*> variable_order;
	vector<Entity*> function_order;
	vector<Namespace*> using_directives;

	Namespace(const string& n, bool has_name, bool inline_ns, Namespace* p);
};

struct TranslationUnit
{
	string srcfile;
	unique_ptr<Namespace> global_namespace;
	vector<unique_ptr<Entity> > entities;
};

enum LookupMask
{
	LOOKUP_NAMESPACE = 1,
	LOOKUP_TYPE = 2,
	LOOKUP_VARIABLE = 4,
	LOOKUP_FUNCTION = 8,
	LOOKUP_VALUE = LOOKUP_VARIABLE | LOOKUP_FUNCTION,
	LOOKUP_ANY = LOOKUP_NAMESPACE | LOOKUP_TYPE | LOOKUP_VARIABLE | LOOKUP_FUNCTION
};

struct QualifiedName
{
	Namespace* qualifier;
	string name;

	QualifiedName();
};

TypePtr make_fundamental(EFundamentalType fundamental);
TypePtr make_cv(TypePtr base, unsigned cv);
TypePtr make_pointer(TypePtr base);
TypePtr make_lvalue_reference(TypePtr base);
TypePtr make_rvalue_reference(TypePtr base);
TypePtr make_array(TypePtr element, bool unknown, unsigned long long bound);
TypePtr make_function(TypePtr result,
                      const vector<TypePtr>& parameters,
                      bool variadic);
TypePtr adjust_parameter_type(TypePtr type);
bool is_void_type(const TypePtr& type);
bool same_type(const TypePtr& left, const TypePtr& right);
string describe_type(const TypePtr& type);

Namespace* get_or_create_named_namespace(TranslationUnit& tu,
                                         Namespace* parent,
                                         const string& name,
                                         bool is_inline);
Namespace* create_unnamed_namespace(TranslationUnit& tu,
                                    Namespace* parent,
                                    bool is_inline);
Entity* add_type_alias(TranslationUnit& tu,
                       Namespace* ns,
                       const string& name,
                       TypePtr type);
Entity* add_variable(TranslationUnit& tu,
                     Namespace* ns,
                     const string& name,
                     TypePtr type);
Entity* add_function(TranslationUnit& tu,
                     Namespace* ns,
                     const string& name,
                     TypePtr type);
Entity* add_namespace_alias(TranslationUnit& tu,
                            Namespace* ns,
                            const string& name,
                            Namespace* target);
void add_using_declaration(Namespace* ns, const string& name, Entity* entity);
void add_using_directive(Namespace* ns, Namespace* target);
Namespace* resolve_namespace(Entity* entity);
Entity* lookup_unqualified(Namespace* start, const string& name, int mask);
Entity* lookup_qualified(Namespace* ns, const string& name, int mask);

TranslationUnit parse_source_file(const string& srcfile, const Options& options);
void emit_translation_unit(const TranslationUnit& tu, ostream& out);

}  // namespace nsdecl
