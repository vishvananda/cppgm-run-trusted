#pragma once

#include <cstdint>
#include <iosfwd>
#include <map>
#include <memory>
#include <set>
#include <string>
#include <vector>

#include "pa11_types.h"
#include "posttoken_support.h"

using namespace std;

namespace pa11 {

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
	Function,
	MemberPointer,
	Record,
	Enum,
	TemplateParameter,
	TemplateTemplateParameter
};

struct Scope;
struct Binding;
struct Type;
typedef shared_ptr<Type> TypePtr;

struct Type
{
	TypeKind kind;
	EFundamentalType fundamental;
	unsigned cv;
	TypePtr base;
	TypePtr member_class;
	bool unknown_bound;
	uint64_t bound;
	vector<TypePtr> parameters;
	bool variadic;
	string name;
	string tag;
	bool scoped_enum;
	bool complete;
	EFundamentalType enum_underlying;
	Scope* scope;
	vector<Binding*> fields;
	uint64_t record_size;
	uint64_t record_align;
	bool layout_valid;

	explicit Type(TypeKind k);
};

enum class BindingKind
{
	Namespace,
	NamespaceAlias,
	Type,
	TypeAlias,
	Variable,
	Function,
	Parameter,
	Enumerator
};

struct Binding
{
	BindingKind kind;
	string name;
	TypePtr type;
	Scope* owner;
	Scope* target_scope;
	Binding* aliased_binding;
	string language_linkage;
	bool has_constant;
	uint64_t constant_value;
	bool is_static_member;
	bool is_inline_definition;
	bool is_generated_default_constructor;
	bool is_explicit;
	bool is_private;
	bool is_protected_member;
	bool is_mutable_member;
	bool is_hidden_friend;
	bool is_thread_local;
	bool unwind_no;
	uint64_t member_offset;
	bool is_bit_field;
	uint64_t bit_width;
	uint64_t bit_offset;

	Binding(BindingKind k, const string& n, Scope* o);
};

enum class ScopeKind
{
	Namespace,
	TemplateParameters,
	Class,
	Enum,
	Function,
	Block
};

struct Scope
{
	ScopeKind kind;
	string name;
	Scope* parent;
	vector<unique_ptr<Scope> > owned_scopes;
	vector<Scope*> child_order;
	vector<unique_ptr<Binding> > owned_bindings;
	vector<Binding*> binding_order;
	map<string, vector<Binding*> > members;
	map<string, Scope*> named_namespaces;
	Scope* unnamed_namespace;
	vector<Scope*> using_directives;
	bool is_inline_namespace;

	Scope(ScopeKind k, const string& n, Scope* p);
};

struct TranslationUnit
{
	string srcfile;
	unique_ptr<Scope> global_scope;
	size_t anonymous_counter;

	TranslationUnit();
};

enum LookupMask
{
	LOOKUP_NAMESPACE = 1,
	LOOKUP_TYPE = 2,
	LOOKUP_VARIABLE = 4,
	LOOKUP_FUNCTION = 8,
	LOOKUP_PARAMETER = 16,
	LOOKUP_ENUMERATOR = 32,
	LOOKUP_VALUE = LOOKUP_VARIABLE | LOOKUP_FUNCTION |
	               LOOKUP_PARAMETER | LOOKUP_ENUMERATOR,
	LOOKUP_QUALIFIER = LOOKUP_NAMESPACE | LOOKUP_TYPE,
	LOOKUP_ANY = LOOKUP_NAMESPACE | LOOKUP_TYPE | LOOKUP_VALUE
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
TypePtr make_member_pointer(TypePtr class_type, TypePtr member_type);
TypePtr make_record_type(const string& name,
                         const string& tag,
                         bool complete,
                         Scope* scope);
TypePtr make_enum_type(const string& name,
                       bool scoped,
                       EFundamentalType underlying,
                       bool complete,
                       Scope* scope);
TypePtr make_template_parameter_type(const string& name);
TypePtr make_template_template_parameter_type(const string& name);

TypePtr strip_top_level_cv(TypePtr type);
TypePtr strip_cv(TypePtr type);
bool type_has_const(const TypePtr& type);
bool is_void_type(const TypePtr& type);
bool is_reference_type(const TypePtr& type);
bool is_integral_or_bool_type(const TypePtr& type);
bool same_type(const TypePtr& left, const TypePtr& right);
string describe_type(const TypePtr& type);
uint64_t type_size(const TypePtr& type);
uint64_t type_align(const TypePtr& type);
void layout_record_type(TypePtr type);
TypePtr record_type_for_scope(Scope* scope);

Scope* create_child_scope(Scope* parent,
                          ScopeKind kind,
                          const string& name);
Scope* get_or_create_namespace(Scope* parent,
                               const string& name,
                               bool is_inline);
Binding* add_binding(Scope* scope,
                     BindingKind kind,
                     const string& name,
                     TypePtr type);
Binding* add_namespace_alias(Scope* scope,
                             const string& name,
                             Scope* target);
void add_using_directive(Scope* scope, Scope* target);
Binding* add_using_declaration(Scope* scope,
                               const string& name,
                               const Binding* target);
Binding* find_owned_binding(Scope* scope,
                            const string& name,
                            BindingKind kind);
Binding* lookup_unqualified(Scope* start, const string& name, int mask);
Binding* lookup_qualified(Scope* scope, const string& name, int mask);
Scope* binding_qualifier_scope(const Binding* binding);
bool binding_matches(const Binding* binding, int mask);

bool is_cv_token(ETokenType type);
bool is_storage_or_function_specifier(ETokenType type);
bool is_builtin_type_token(ETokenType type);
EFundamentalType fundamental_from_specs(const vector<ETokenType>& specs);

TranslationUnit analyze_source_file(const string& srcfile,
                                    const Options& options);
void emit_translation_unit(const TranslationUnit& tu, ostream& out);

}  // namespace pa11
