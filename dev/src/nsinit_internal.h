#pragma once

#include <cstddef>
#include <cstdint>
#include <map>
#include <memory>
#include <set>
#include <string>
#include <vector>

#include "nsinit_support.h"
#include "posttoken_pipeline.h"
#include "posttoken_support.h"

using namespace std;

namespace nsinit {

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
	uint64_t bound;
	vector<TypePtr> parameters;
	bool variadic;

	explicit Type(TypeKind k);
};

enum class StorageClass
{
	None,
	Static,
	ThreadLocal,
	Extern
};

enum class EntityKind
{
	Namespace,
	NamespaceAlias,
	TypeAlias,
	Variable,
	Function
};

enum class ExprKind
{
	BoolLiteral,
	NullptrLiteral,
	Literal,
	Id,
	Paren
};

enum class ValueCategory
{
	Prvalue,
	Lvalue,
	Xvalue
};

struct Namespace;
struct Entity;
struct LinkedEntity;
struct StringLiteral;
struct Temporary;

struct QualifiedName
{
	Namespace* qualifier;
	string name;

	QualifiedName();
};

struct Expr
{
	ExprKind kind;
	bool bool_value;
	string literal_source;
	QualifiedName name;
	Namespace* lookup_scope;
	shared_ptr<Expr> inner;
	StringLiteral* string_literal;

	explicit Expr(ExprKind k);
};

struct Initializer
{
	shared_ptr<Expr> expr;
};

struct InitPlan
{
	vector<unsigned char> bytes;
	Entity* address_entity;
	StringLiteral* address_string;
	Temporary* address_temporary;

	InitPlan();
};

struct Entity
{
	EntityKind kind;
	string name;
	Namespace* owner;
	TypePtr type;
	Namespace* target_namespace;
	StorageClass storage;
	bool declared_extern;
	bool is_constexpr;
	bool is_inline;
	bool is_definition;
	bool has_initializer;
	Initializer initializer;
	size_t order;
	LinkedEntity* linked;
	bool evaluating_constant;
	bool constant_ready;
	bool constant_valid;
	uint64_t constant_integer;
	bool constant_pointer_ready;
	bool constant_pointer_valid;
	Entity* constant_pointer_entity;
	StringLiteral* constant_pointer_string;

	Entity(EntityKind k, const string& n, Namespace* o);
};

struct Namespace
{
	string name;
	bool named;
	bool is_inline;
	bool contains_unnamed;
	Namespace* parent;
	vector<unique_ptr<Namespace> > owned_namespaces;
	vector<Namespace*> namespace_order;
	map<string, Namespace*> named_namespaces;
	Namespace* unnamed_namespace;
	map<string, vector<Entity*> > members;
	vector<Namespace*> using_directives;

	Namespace(const string& n, bool has_name, bool inline_ns, Namespace* p);
};

struct StringLiteral
{
	string source;
	TypePtr type;
	EFundamentalType element_type;
	size_t elements;
	vector<unsigned char> bytes;
	size_t order;
	size_t offset;

	StringLiteral();
};

struct TranslationUnit
{
	string srcfile;
	unique_ptr<Namespace> global_namespace;
	vector<unique_ptr<Entity> > entities;
	vector<unique_ptr<StringLiteral> > string_literals;
};

struct LinkedEntity
{
	EntityKind kind;
	string key;
	Entity* first;
	TypePtr type;
	size_t order;
	bool has_definition;
	Entity* definition;
	bool non_inline_definition_seen;
	bool emitted;
	size_t offset;
	InitPlan init;

	LinkedEntity();
};

struct Temporary
{
	TypePtr type;
	InitPlan init;
	size_t order;
	size_t offset;

	Temporary();
};

struct Program
{
	vector<unique_ptr<TranslationUnit> > translation_units;
	vector<unique_ptr<LinkedEntity> > linked_entities;
	vector<LinkedEntity*> image_entities;
	vector<unique_ptr<Temporary> > temporaries;
	vector<StringLiteral*> string_literals;
	size_t next_order;

	Program();
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

struct ExprValue
{
	TypePtr type;
	ValueCategory category;
	bool valid;
	bool known_integer;
	uint64_t integer;
	bool known_floating;
	string floating_source;
	EFundamentalType floating_type;
	bool is_null_pointer;
	Entity* address_entity;
	StringLiteral* address_string;
	bool string_literal;

	ExprValue();
};

TypePtr make_fundamental(EFundamentalType fundamental);
TypePtr make_cv(TypePtr base, unsigned cv);
TypePtr make_pointer(TypePtr base);
TypePtr make_lvalue_reference(TypePtr base);
TypePtr make_rvalue_reference(TypePtr base);
TypePtr make_array(TypePtr element, bool unknown, uint64_t bound);
TypePtr make_function(TypePtr result,
                      const vector<TypePtr>& parameters,
                      bool variadic);
TypePtr adjust_parameter_type(TypePtr type);
TypePtr strip_top_level_cv(TypePtr type);
TypePtr strip_cv(TypePtr type);
bool type_has_const(const TypePtr& type);
bool is_void_type(const TypePtr& type);
bool is_reference_type(const TypePtr& type);
bool is_integral_or_bool_type(const TypePtr& type);
bool is_floating_type(const TypePtr& type);
bool same_type(const TypePtr& left, const TypePtr& right);
string describe_type(const TypePtr& type);
size_t type_size(const TypePtr& type);
size_t type_align(const TypePtr& type);
bool is_complete_object_type(const TypePtr& type);
bool can_default_initialize(const TypePtr& type);

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
                       TypePtr type,
                       size_t order);
Entity* add_variable(TranslationUnit& tu,
                     Namespace* ns,
                     const string& name,
                     TypePtr type,
                     StorageClass storage,
                     bool is_constexpr,
                     bool is_definition,
                     const Initializer* initializer,
                     size_t order);
Entity* add_function(TranslationUnit& tu,
                     Namespace* ns,
                     const string& name,
                     TypePtr type,
                     StorageClass storage,
                     bool is_inline,
                     bool is_definition,
                     size_t order);
Entity* add_namespace_alias(TranslationUnit& tu,
                            Namespace* ns,
                            const string& name,
                            Namespace* target,
                            size_t order);
void add_using_declaration(Namespace* ns, const string& name, Entity* entity);
void add_using_directive(Namespace* ns, Namespace* target);
Namespace* resolve_namespace(Entity* entity);
Entity* lookup_unqualified(Namespace* start, const string& name, int mask);
Entity* lookup_qualified(Namespace* ns, const string& name, int mask);
bool namespace_encloses(Namespace* possible_encloser, Namespace* child);
bool namespace_has_internal_linkage(Namespace* ns);

StringLiteral* add_string_literal(TranslationUnit& tu,
                                  const string& source,
                                  size_t order);

unique_ptr<TranslationUnit> parse_source_file(const string& srcfile,
                                              const Options& options,
                                              Program& program);
void link_program(Program& program);
void analyze_program_initializers(Program& program);
void write_program_image(Program& program, vector<char>& image);

ExprValue eval_expression(const shared_ptr<Expr>& expr);
bool expr_value_to_integer_constant(const ExprValue& value, uint64_t& out);
bool expr_value_to_pointer_target(const ExprValue& value,
                                  Entity*& entity,
                                  StringLiteral*& literal,
                                  bool& is_null);
bool eval_array_bound(const shared_ptr<Expr>& expr, uint64_t& bound);
bool eval_static_assert_condition(const shared_ptr<Expr>& expr);
bool eval_entity_integer_constant(Entity* entity, uint64_t& value);
bool eval_entity_pointer_constant(Entity* entity,
                                  Entity*& address_entity,
                                  StringLiteral*& address_string,
                                  bool& is_null);

void append_zeroes(vector<unsigned char>& out, size_t count);
void append_integer_le(vector<unsigned char>& out, uint64_t value, size_t size);
void write_integer_le(vector<unsigned char>& out,
                      size_t offset,
                      uint64_t value,
                      size_t size);

}  // namespace nsinit
