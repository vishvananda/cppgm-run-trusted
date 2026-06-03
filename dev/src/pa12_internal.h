#pragma once

#include <map>
#include <memory>
#include <set>
#include <string>
#include <vector>

#include "pa10_parser_internal.h"
#include "pa11_internal.h"
#include "pa12_semantics.h"

using namespace std;

namespace pa12 {
namespace internal {

using pa10::internal::Token;
using pa11::Binding;
using pa11::BindingKind;
using pa11::Scope;
using pa11::ScopeKind;
using pa11::TypePtr;

enum class ValueCategory
{
	LValue,
	PRValue,
	XValue
};

enum class PtrKind
{
	Pointer,
	LValueReference,
	RValueReference,
	MemberPointer
};

enum class SuffixKind
{
	Array,
	Function
};

struct Node
{
	string line;
	vector<Node> children;
	TypePtr type;
	ValueCategory category;
	Binding* binding;
	Binding* direct_call;
	bool has_op;
	ETokenType op;
	string token_text;
	bool has_constant_value;
	uint64_t constant_value;

	Node();
	explicit Node(const string& text);
};

struct QualifiedName
{
	Scope* qualifier;
	string name;
	string spelling;
	bool qualified;

	QualifiedName();
};

struct Expr
{
	Node node;
	TypePtr type;
	ValueCategory category;
	Binding* binding;
	vector<Binding*> overloads;
	bool valid;
	bool null_pointer_constant;
	bool constant_expression;
	bool has_constant_value;
	uint64_t constant_value;
	bool builtin_constant_p;
	bool braced_init_list;

	Expr();
};

struct DeclSpecs
{
	bool typedef_decl;
	bool constexpr_decl;
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
	bool has_default;
	Expr default_value;

	ParameterInfo();
};

struct Suffix
{
	SuffixKind kind;
	bool unknown_bound;
	uint64_t bound;
	vector<ParameterInfo> parameters;
	bool variadic;
	unsigned function_cv;

	explicit Suffix(SuffixKind k);
};

struct Declarator
{
	vector<PtrOp> prefix;
	vector<Suffix> suffixes;
	unique_ptr<Declarator> inner;
	bool has_name;
	QualifiedName name;

	Declarator();
};

struct Conversion
{
	bool viable;
	int rank;
	Expr expr;

	Conversion();
	Conversion(bool ok, int cost, const Expr& converted);
};

class Parser
{
public:
	Parser(const string& srcfile, const Options& options);

	void parse_translation_unit();
	const Node& root() const;
	const vector<Node>& generated_nodes() const;

private:
	vector<Token> tokens_;
	size_t pos_;
	pa11::TranslationUnit tu_;
	vector<Scope*> scopes_;
	vector<TypePtr> function_returns_;
	vector<string> language_linkages_;
	Node root_;
	vector<Node> generated_nodes_;
	int local_type_counter_;
	set<string> generated_default_ctors_;
	map<Binding*, vector<Expr> > default_arguments_;
	set<Binding*> deleted_functions_;

	Scope* current_scope() const;
	Scope* global_scope() const;
	TypePtr current_return_type() const;
	string current_language_linkage() const;

	bool at_eof() const;
	bool at_identifier() const;
	bool at_literal() const;
	bool at(ETokenType type) const;
	bool lookahead(ETokenType type, size_t offset) const;
	bool consume(ETokenType type);
	void expect(ETokenType type);
	void expect_eof();
	string consume_identifier();
	string consume_literal();
	string consume_operator_function_name();
	const Token& current() const;
	const Token& at_token(size_t index) const;

	void parse_declaration_into(Node& out);
	void parse_namespace_or_alias(Node& out);
	void parse_using_family(Node& out);
	void parse_linkage_specification(Node& out);
	void parse_template_declaration();
	void parse_simple_or_function_declaration(Node& out, bool emit_node);
	bool parse_constructor_like_member();
	void parse_class_body(Scope* class_scope);

	DeclSpecs parse_decl_specifier_seq(bool type_id_context);
	TypePtr type_from_decl_specs(const DeclSpecs& specs);
	TypePtr parse_type_id();
	TypePtr parse_decltype_specifier();
	TypePtr parse_class_specifier();
	TypePtr parse_enum_specifier();
	EFundamentalType parse_enum_underlying_type();
	bool try_parse_type_name(TypePtr& out);
	bool starts_declaration();
	bool starts_class_key() const;
	bool starts_ptr_operator() const;
	bool starts_declarator() const;
	bool starts_abstract_declarator() const;
	bool starts_parenthesized_abstract_declarator() const;
	bool at_simple_ignored_specifier() const;
	bool at_simple_cv() const;
	bool at_simple_builtin() const;
	unsigned consume_cv_flag();

	Declarator parse_declarator(bool abstract_allowed);
	Declarator parse_abstract_declarator();
	void parse_noptr_declarator_root(Declarator& declarator,
	                                 bool abstract_allowed);
	void parse_ptr_prefix(vector<PtrOp>& ops);
	void parse_suffixes(vector<Suffix>& suffixes);
	Suffix parse_array_suffix();
	Suffix parse_function_suffix();
	void parse_function_suffix_tail(Suffix& suffix);
	void parse_parameter_clause(vector<ParameterInfo>& parameters,
	                            bool& variadic);
	ParameterInfo parse_parameter_declaration();
	TypePtr apply_declarator(const Declarator& declarator, TypePtr base);
	TypePtr apply_ptr_ops(TypePtr type, const vector<PtrOp>& ops);
	TypePtr apply_suffixes(TypePtr type, const vector<Suffix>& suffixes);
	const QualifiedName& declarator_name(const Declarator& declarator) const;
	bool declarator_has_name(const Declarator& declarator) const;
	const Suffix* declarator_function_suffix(const Declarator& declarator) const;

	void parse_function_body(Binding* function,
	                         const Declarator& declarator,
	                         Node& function_node);
	Node parse_compound_statement();
	Node parse_block_item();
	Node parse_statement();
	Node parse_if_statement();
	Node parse_switch_statement();
	Node parse_while_statement();
	Node parse_do_statement();
	Node parse_for_statement();
	Node parse_jump_statement();
	Node parse_labeled_statement();
	Node parse_expression_statement();
	Node parse_condition();

	Expr parse_expression();
	Expr parse_assignment_expression();
	Expr parse_conditional_expression();
	Expr parse_binary_expression(int min_prec);
	Expr parse_unary_expression();
	Expr parse_postfix_expression();
	Expr parse_postfix_suffixes(Expr expr);
	Expr parse_primary_expression();
	Expr parse_literal_expression();
	Expr parse_cast_expression();
	Expr parse_type_trait_expression(ETokenType keyword);
	Expr parse_c_style_cast_or_parenthesized();
	Expr parse_functional_cast(TypePtr target);
	vector<Expr> parse_argument_list();

	Binding* declare_one(const DeclSpecs& specs,
	                     TypePtr base,
	                     const Declarator& declarator,
	                     const Expr* init,
	                     bool function_definition,
	                     Node& out);
	Binding* add_alias(Scope* scope, const string& name, TypePtr type);
	Binding* add_value(Scope* scope,
	                   BindingKind kind,
	                   const string& name,
	                   TypePtr type);
	TypePtr add_record(Scope* scope,
	                   const string& name,
	                   const string& tag,
	                   bool complete,
	                   Scope* class_scope);
	TypePtr add_enum(Scope* scope,
	                 const string& name,
	                 bool scoped,
	                 EFundamentalType underlying,
	                 bool complete,
	                 bool create_scope);
	void inject_anonymous_union_members(Scope* class_scope,
	                                    Binding* storage);
	void ensure_default_constructor(TypePtr type);
	TypePtr make_member_function_type(Scope* class_scope, TypePtr type);
	Node default_constructor_action(Binding* variable);

	QualifiedName parse_id_expression_name();
	Scope* parse_nested_name_specifier(string* spelling);
	Scope* parse_qualified_namespace_specifier();
	Scope* resolve_qualifier(Binding* binding);
	vector<Binding*> resolve_name_set(const QualifiedName& name, int mask);
	Binding* resolve_single_name(const QualifiedName& name, int mask);
	vector<Binding*> lookup_unqualified_set(Scope* start,
	                                        const string& name,
	                                        int mask);
	vector<Binding*> lookup_qualified_set(Scope* scope,
	                                      const string& name,
	                                      int mask);

	Conversion convert_to(const Expr& expr, TypePtr target);
	Conversion convert_reference(const Expr& expr, TypePtr target);
	Conversion convert_value(const Expr& expr, TypePtr target);
	Expr select_overload_expr(const Expr& expr, TypePtr target);
	Binding* resolve_call_candidate(const vector<Binding*>& overloads,
	                                const vector<Expr>& args,
	                                vector<Expr>& converted);
	Expr make_call_expr(Expr callee, vector<Expr> args);
	Expr make_id_expr(const QualifiedName& name);
	Expr make_binary_expr(ETokenType op, const string& text, Expr lhs, Expr rhs);
	Expr make_assignment_expr(ETokenType op,
	                          const string& text,
	                          Expr lhs,
	                          Expr rhs);
	Expr make_unary_expr(ETokenType op, const string& text, Expr inner);
	Expr make_postfix_expr(ETokenType op, const string& text, Expr inner);
	Expr make_subscript_expr(Expr lhs, Expr rhs);
	Expr make_member_expr(Expr object, const string& name, const string& op);
	Expr make_cast_expr(TypePtr target,
	                    const string& op_text,
	                    Expr inner);
	Expr make_sizeof_expr(uint64_t value);
	Expr make_address_expr(const string& text, Expr inner);
	Expr make_deref_expr(const string& text, Expr inner);

	bool is_assignment_operator(ETokenType& op) const;
	bool binary_operator(ETokenType& op, int& prec) const;
	bool expression_starts_type_name(TypePtr& type);
	bool is_zero_literal(const Expr& expr) const;
	bool type_can_bind_reference(TypePtr target, const Expr& expr) const;
	bool types_reference_compatible(TypePtr target, TypePtr source) const;
	bool pointer_conversion_viable(TypePtr source, TypePtr target) const;
	bool is_pointer_arithmetic(const Expr& lhs, const Expr& rhs) const;
	bool is_pointer_difference(const Expr& lhs, const Expr& rhs) const;
	int scalar_conversion_rank(TypePtr source, TypePtr target) const;
	bool ranks_better(const vector<int>& lhs, const vector<int>& rhs) const;
	TypePtr pointer_arithmetic_type(ETokenType op,
	                                const Expr& lhs,
	                                const Expr& rhs) const;
	TypePtr pointee_type_for_member(TypePtr type) const;
	TypePtr expression_object_type(TypePtr type) const;
	TypePtr lvalue_to_rvalue_type(TypePtr type) const;
	TypePtr usual_arithmetic_type(TypePtr left, TypePtr right) const;
	ValueCategory call_category(TypePtr result) const;

	string value_category_name(ValueCategory category) const;
	string qualified_decl_name(const Binding* binding) const;
	string scoped_type_display_name(Scope* owner, const string& name) const;
	string class_tag(ETokenType key) const;
	string make_local_type_name(const string& prefix);
	string op_leaf(ETokenType type, const string& source) const;
	void skip_balanced(ETokenType open, ETokenType close);
	void skip_template_parameter_clause();
};

void add_child(Node& parent, const Node& child);
void dump_node(ostream& out, const Node& node, int depth);
void annotate_expr_node(Expr& expr);

}  // namespace internal
}  // namespace pa12
