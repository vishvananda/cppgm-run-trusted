#pragma once
#include <map>
#include <memory>
#include <set>
#include <string>
#include <vector>
#include "pa10_parser_internal.h"
#include "pa11_internal.h"
#include "pa12_semantics.h"
#include "pa12_template_model.h"
using namespace std;
namespace pa12 {
namespace internal {
using pa10::internal::Token;
using pa11::Binding;
using pa11::BindingKind;
using pa11::Scope;
using pa11::ScopeKind;
using pa11::TypePtr;
enum class ValueCategory { LValue, PRValue, XValue };
enum class PtrKind { Pointer, LValueReference, RValueReference, MemberPointer };
enum class SuffixKind { Array, Function, Attribute };
struct Node
{
	string line;
	vector<Node> children;
	TypePtr type;
	ValueCategory category;
	Binding* binding;
	vector<Binding*> overloads;
	map<Binding*, vector<TemplateArgument> > explicit_template_arguments;
	Binding* direct_call;
	bool has_op; ETokenType op;
	string token_text;
	bool has_constant_value; uint64_t constant_value;
	string dependent_value_name;
	string dependent_value_owner_template_name;
	string dependent_value_member_name;
	bool dependent_value_negated; vector<pa11::TemplateInstanceArgument> dependent_value_owner_template_arguments;
	bool suppress_virtual_dispatch; bool virtual_dispatch;
	bool is_typeid_expression; bool is_dynamic_cast_expression;
	Node();
	explicit Node(const string& text);
};
struct QualifiedName
{
	Scope* qualifier;
	string name;
	string spelling;
	bool qualified;
	bool has_template_arguments;
	vector<TemplateArgument> template_arguments;
	QualifiedName();
};
struct Expr
{
	Node node;
	TypePtr type;
	ValueCategory category;
	Binding* binding;
	vector<Binding*> overloads;
	map<Binding*, vector<TemplateArgument> > explicit_template_arguments;
	bool pack_expansion; vector<Expr> pack;
	bool valid; bool null_pointer_constant; bool constant_expression;
	bool has_constant_value; uint64_t constant_value;
	bool builtin_constant_p; bool braced_init_list; bool copy_initialization;
	string dependent_value_name;
	string dependent_value_owner_template_name;
		string dependent_value_member_name;
		bool dependent_value_negated;
		vector<pa11::TemplateInstanceArgument> dependent_value_owner_template_arguments;
		size_t source_begin;
		size_t source_end;
		Expr();
	};
bool record_has_aggregate_blocking_constructor(TypePtr record);
bool string_literal_initializes_array(TypePtr type, const Expr& init, uint64_t* elements);
vector<Binding*> declared_instance_fields(TypePtr type);
struct DeclSpecs
{
	bool typedef_decl;
	bool constexpr_decl;
	bool static_decl;
	bool mutable_decl;
	bool friend_decl;
	bool extern_decl;
	bool thread_local_decl;
	bool auto_decl;
	bool virtual_decl;
	bool inline_decl;
	bool int128_decl;
	bool bitint_decl;
	bool no_unique_address_decl;
	uint64_t vector_size;
	unsigned cv;
	vector<ETokenType> builtin;
	TypePtr named_type;
	DeclSpecs();
};
struct PtrOp
{
	PtrKind kind;
	unsigned cv;
	TypePtr member_class;
	PtrOp(PtrKind k, unsigned flags);
	PtrOp(TypePtr class_type, unsigned flags);
};
struct ParameterInfo
{
	string name;
	TypePtr type;
	bool is_pack_expansion;
	string pack_name;
	string pack_expression_name;
	bool has_default;
	Expr default_value;
	ParameterInfo();
};
struct Suffix
{
	SuffixKind kind;
	bool unknown_bound;
	uint64_t bound;
	string array_bound_name;
	vector<ParameterInfo> parameters;
	bool variadic;
	unsigned function_cv;
	int ref_qualifier;
	bool noexcept_decl;
	bool dynamic_exception_spec;
	vector<TypePtr> dynamic_exception_types;
	bool override_decl;
	bool final_decl;
	TypePtr trailing_return;
	vector<string> abi_tags;
	string asm_label;
	uint64_t vector_size;
	explicit Suffix(SuffixKind k);
};
struct Declarator
{
	vector<PtrOp> prefix;
	vector<Suffix> suffixes;
	unique_ptr<Declarator> inner;
	bool has_name;
	QualifiedName name;
	string asm_label;
	Declarator();
	Declarator(Declarator&& other);
	Declarator& operator=(Declarator&& other);
};
struct PendingFunctionBody
{
	Binding* function;
	Node node;
	vector<ParameterInfo> parameters;
	size_t body_pos;
	bool constructor_body;
	bool prebuilt_node;
	TypePtr class_type;
	vector<Scope*> scopes;
	vector<Scope*> friend_class_scopes;
	vector<map<string, TypePtr> > type_substitutions;
	vector<map<string, TemplateArgument> > value_substitutions;
	vector<set<string> > pack_substitutions;
	PendingFunctionBody();
	PendingFunctionBody& operator=(const PendingFunctionBody& other);
};
struct ConstructorInitializerParse
{
	string name;
	vector<TemplateArgument> template_arguments;
	bool have_template_arguments;
	Binding* field;
	Expr init;
	vector<Expr> parsed_args;
	size_t parsed_args_begin;
	size_t parsed_args_end;
	bool have_paren_init;
	bool have_init;
	bool pack_expansion;
	ConstructorInitializerParse()
		: have_template_arguments(false),
		  field(NULL),
		  parsed_args_begin(0),
		  parsed_args_end(0),
		  have_paren_init(false),
		  have_init(false),
		  pack_expansion(false)
	{
	}
};
struct Conversion
{
	bool viable;
	int rank;
	Expr expr;
	Conversion();
	Conversion(bool ok, int cost, const Expr& converted);
};
struct ConstexprValue
{
	bool valid;
	bool is_float;
	bool is_object;
	bool is_pointer;
	uint64_t int_value;
	long double float_value;
	Binding* pointer_binding;
	long long pointer_index;
	TypePtr object_type;
	map<Binding*, ConstexprValue> fields;
	vector<ConstexprValue> elements;
	ConstexprValue();
	static ConstexprValue integer(uint64_t value);
	static ConstexprValue floating(long double value);
	static ConstexprValue object(TypePtr type);
	static ConstexprValue pointer(Binding* binding, long long index);
};
bool constexpr_zero_value_for_type(TypePtr type, ConstexprValue& out);
bool constexpr_integral_compare(ETokenType op, TypePtr left_type, const ConstexprValue& lhs, const ConstexprValue& rhs, ConstexprValue& out);
bool constexpr_string_literal_element(const Node& node, const ConstexprValue& index, ConstexprValue& out);
}  // namespace internal
}  // namespace pa12
