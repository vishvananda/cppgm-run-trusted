#pragma once

#include <cstddef>
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
struct VirtualTableEntry;
struct Type;
typedef shared_ptr<Type> TypePtr;

enum class TemplateInstanceArgumentKind
{
	Type,
	Value,
	Template,
	Pack
};

struct TemplateInstanceArgument
{
	TemplateInstanceArgumentKind kind;
	TypePtr type;
	string template_name;
	string value_name;
	string value_owner_template_name;
	string value_member_name;
	size_t value_expr_begin;
	size_t value_expr_end;
	uint64_t value;
	bool dependent;
	bool value_negated;
	vector<TemplateInstanceArgument> pack;
	vector<TemplateInstanceArgument> value_owner_template_arguments;

	TemplateInstanceArgument();
	static TemplateInstanceArgument type_arg(TypePtr type);
	static TemplateInstanceArgument value_arg(TypePtr type, uint64_t value);
	static TemplateInstanceArgument dependent_value_arg(TypePtr type);
	static TemplateInstanceArgument template_arg(const string& name);
	static TemplateInstanceArgument pack_arg(
		const vector<TemplateInstanceArgument>& values);
};

struct VirtualTableEntry
{
	Binding* function;
	bool deleting_entry;

	VirtualTableEntry();
	VirtualTableEntry(Binding* f, bool d);
};

struct Type
{
	TypeKind kind;
	EFundamentalType fundamental;
	unsigned cv;
	int ref_qualifier;
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
	bool is_template_specialization;
	bool is_dependent_typename;
	bool dependent_typename_qualified;
	bool dependent_typename_template_id;
	bool dependent_typename_decltype;
	string template_primary_name;
	vector<TemplateInstanceArgument> template_arguments;
	vector<vector<TemplateInstanceArgument> >
		dependent_typename_template_argument_lists;
	EFundamentalType enum_underlying;
	Scope* scope;
	vector<Binding*> fields;
	uint64_t record_size;
	uint64_t record_align;
	uint64_t record_forced_align;
	uint64_t nonvirtual_size;
	uint64_t nonvirtual_align;
	uint64_t direct_base_offset;
	vector<TypePtr> direct_bases;
	vector<uint64_t> direct_base_offsets;
	vector<bool> direct_base_virtuals;
	vector<TypePtr> virtual_bases;
	vector<uint64_t> virtual_base_offsets;
	bool layout_valid;
	bool is_polymorphic;
	bool introduces_vptr;
	bool is_final_record;
	vector<VirtualTableEntry> virtual_entries;

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
	bool is_constexpr;
	bool is_static_member;
	bool is_local_static;
	bool is_namespace_static;
	string local_static_discriminator;
		Binding* local_static_function_owner;
	string function_specialization_symbol;
	vector<string> function_parameter_names;
	vector<string> abi_tags;
			bool is_inline_definition;
		bool is_declared_inline;
		bool is_generated_default_constructor;
	bool is_generated_aggregate_constructor;
	bool is_generated_copy_move_constructor;
	bool is_generated_copy_move_assignment;
	bool is_generated_default_destructor;
		bool is_defaulted;
		bool is_explicit;
		bool has_default_arguments;
		bool is_private;
	bool is_protected_member;
	bool is_mutable_member;
	bool is_no_unique_address;
	bool is_reference_member;
	bool is_hidden_friend;
	bool is_thread_local;
	bool is_object_root;
	bool is_dependent_template_artifact;
	bool is_template_static_member_definition;
	bool is_template_static_member_explicit_definition;
	bool reserve_primary_function_symbol;
	bool is_virtual;
	bool is_override_specified;
	bool is_final_virtual;
	bool is_pure_virtual;
	Binding* overrides_virtual;
	int virtual_slot_index;
	int virtual_slot_width;
	bool unwind_no;
	int ref_qualifier;
	bool is_noop_constructor;
	bool is_noop_destructor;
	bool is_cleanup_only_destructor;
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
	TypePtr record_type;

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
TypePtr make_gnu_vector(TypePtr element, uint64_t bytes);
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
TypePtr make_dependent_typename_type(const string& name,
                                     bool qualified,
                                     bool template_id,
                                     bool decltype_id);
TypePtr make_template_template_parameter_type(const string& name);
bool is_deducible_template_parameter_type(const TypePtr& type);
bool is_dependent_typename_type(const TypePtr& type);

TypePtr strip_top_level_cv(TypePtr type);
TypePtr strip_cv(TypePtr type);
bool type_has_const(const TypePtr& type);
bool is_void_type(const TypePtr& type);
bool is_reference_type(const TypePtr& type);
bool is_gnu_vector_type(const TypePtr& type);
bool is_integral_or_bool_type(const TypePtr& type);
bool same_type(const TypePtr& left, const TypePtr& right);
string describe_type(const TypePtr& type);
uint64_t type_size(const TypePtr& type);
uint64_t type_align(const TypePtr& type);
void layout_record_type(TypePtr type);
vector<TypePtr> record_direct_bases(TypePtr type);
uint64_t record_direct_base_offset(TypePtr record, TypePtr direct_base);
bool record_direct_base_is_virtual(TypePtr record, size_t index);
vector<TypePtr> record_virtual_bases(TypePtr type);
uint64_t record_virtual_base_offset(TypePtr record, TypePtr virtual_base);
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
size_t binding_generation();
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
