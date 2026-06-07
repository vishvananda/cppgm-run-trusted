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
	string dependent_value_name;
	string dependent_value_owner_template_name;
	string dependent_value_member_name;
	bool dependent_value_negated;
	vector<pa11::TemplateInstanceArgument> dependent_value_owner_template_arguments;
	bool suppress_virtual_dispatch;
	bool virtual_dispatch;

	Node();
	explicit Node(const string& text);
};

enum class TemplateParameterKind
{
	Type,
	NonType,
	TemplateTemplate
};

enum class TemplateArgumentKind
{
	Type,
	Value,
	Template,
	Pack
};

struct TemplateDeclaration;

struct TemplateArgument
{
	TemplateArgumentKind kind;
	TypePtr type;
	TemplateDeclaration* template_declaration;
	Binding* value_binding;
	string value_name;
	string value_owner_template_name;
	string value_member_name;
	uint64_t value;
	bool dependent;
	bool value_negated;
	bool pack_expansion;
	size_t value_expr_begin;
	size_t value_expr_end;
	vector<TemplateArgument> pack;
	vector<pa11::TemplateInstanceArgument> value_owner_template_arguments;

	TemplateArgument();
	static TemplateArgument type_arg(TypePtr type);
	static TemplateArgument value_arg(TypePtr type, uint64_t value);
	static TemplateArgument dependent_value_arg(TypePtr type);
	static TemplateArgument template_arg(TemplateDeclaration* declaration);
	static TemplateArgument pack_arg(const vector<TemplateArgument>& values);
};

bool template_argument_has_template_parameter( const TemplateArgument& arg, const map<const void*, vector<TemplateArgument> >& record_template_arguments);
bool template_instance_argument_has_template_parameter( const pa11::TemplateInstanceArgument& argument, const map<const void*, vector<TemplateArgument> >& record_template_arguments);
bool template_type_has_template_parameter_name(TypePtr type, string& name);
bool template_type_has_template_parameter( TypePtr type, const map<const void*, vector<TemplateArgument> >& record_template_arguments);

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
	bool pack_expansion;
	vector<Expr> pack;
	bool valid;
	bool null_pointer_constant;
	bool constant_expression;
	bool has_constant_value;
	uint64_t constant_value;
	bool builtin_constant_p;
	bool braced_init_list;
	bool copy_initialization;
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
	bool override_decl;
	bool final_decl;
	TypePtr trailing_return;

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
};

struct TemplateParameterInfo
{
	TemplateParameterKind kind;
	string name;
	TypePtr type;
	vector<TemplateParameterInfo> template_parameters;
	bool is_pack;
	bool has_default;
	size_t default_begin;
	size_t default_end;

	TemplateParameterInfo();
};

enum class TemplateDeclarationKind
{
	Unknown,
	Class,
	Function,
	Variable,
	Alias
};

struct TemplateDeclaration
{
	TemplateDeclarationKind kind;
	Scope* owner;
	Scope* lexical_scope;
	string name;
	string tag;
	vector<TemplateParameterInfo> parameters;
	size_t decl_begin;
	size_t decl_end;
		bool has_definition;
			bool constructor_template;
			bool class_template_member;
			bool class_specialization;
			bool hidden_friend;
			bool function_definition_validated;
			Scope* friend_class_scope;
	TypePtr generic_function_type;
	Binding* placeholder;
	Binding* inherited_constructor_base;
	TypePtr inherited_constructor_base_type;
	vector<map<string, TypePtr> > outer_type_substitutions;
	vector<map<string, TemplateArgument> > outer_value_substitutions;
	vector<TemplateArgument> class_specialization_pattern;
	vector<TemplateDeclaration*> class_specialization_declarations;
	map<string, TypePtr> class_specializations;
	map<string, Binding*> function_specializations;
	set<string> completing_specializations;
	set<string> emitted_variable_specializations;

		TemplateDeclaration();
	};

	string qualified_template_declaration_name( const TemplateDeclaration* declaration);

	struct ActiveClassInstantiation
{
	TemplateDeclaration* declaration;
	string specialization_name;
	TypePtr type;

	ActiveClassInstantiation();
	ActiveClassInstantiation(TemplateDeclaration* d, const string& n, TypePtr t);
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

struct TemplateValidationState;

class Parser
{
	friend struct TemplateValidationState;

public:
	Parser(const string& srcfile, const Options& options);

	void parse_translation_unit();
	const Node& root() const;
	const vector<Node>& generated_nodes() const;
	const vector<Node>& extra_lowir_nodes() const;
	TypePtr substitute_type_for_template_match( TypePtr type, const map<string, TemplateArgument>& deduced);
	TypePtr expand_alias_template_for_match( TypePtr type, const map<string, TemplateArgument>& deduced);
	bool template_value_argument_matches_for_template_match( TemplateDeclaration* specialization, const TemplateArgument& pattern, const TemplateArgument& actual, const map<string, TemplateArgument>& deduced);
	TemplateDeclaration* class_template_declaration_for_match( TypePtr type) const;

	private:
		vector<Token> tokens_;
		vector<Token> declaration_tokens_;
		size_t pos_;
	pa11::TranslationUnit tu_;
	vector<Scope*> scopes_;
	vector<TypePtr> function_returns_;
	vector<Binding*> active_functions_;
	vector<Scope*> active_friend_class_scopes_;
	vector<string> language_linkages_;
	vector<bool> class_private_access_;
	vector<bool> class_protected_access_;
	Node root_;
	vector<Node> generated_nodes_;
	vector<Node> extra_lowir_nodes_;
	int local_type_counter_;
	bool force_new_function_binding_;
	bool defer_function_template_bodies_;
	bool suppress_implicit_template_base_init_;
	bool parsing_base_specifier_;
	bool validating_template_definition_;
	bool override_function_parameter_names_;
	bool replaying_dependent_decltype_;
	bool parsing_default_template_argument_;
	int defer_class_template_completion_depth_;
		int function_template_candidate_instantiation_depth_;
		int template_argument_expression_depth_;
		int unevaluated_expression_depth_;
		int short_circuit_static_member_demand_depth_;
		set<const void*> generated_default_ctors_;
	set<pair<const void*, size_t> > generated_aggregate_ctors_;
	set<const void*> generated_copy_ctors_;
	set<const void*> generated_move_ctors_;
	set<const void*> generated_copy_assignments_;
	set<const void*> generated_move_assignments_;
	set<const void*> generated_dtors_;
	map<Binding*, Node> default_member_initializers_;
	map<Binding*, Node> static_member_initializers_;
	map<Binding*, vector<Expr> > default_arguments_;
	map<Binding*, vector<string> > function_parameter_names_;
	vector<string> function_parameter_name_override_;
	set<Binding*> override_function_parameter_name_bindings_;
	set<Binding*> deleted_functions_;
	map<const void*, Scope*> enum_owner_scopes_;
	map<Scope*, vector<Binding*> > class_friend_functions_;
	map<Scope*, vector<TypePtr> > class_friend_classes_;
	map<Scope*, vector<PendingFunctionBody> > pending_member_bodies_;
	map<Binding*, PendingFunctionBody> pending_function_bodies_;
	map<Scope*, vector<Scope*> > deferred_nested_member_body_scopes_;
	vector<Binding*> defaulted_move_assignments_;
	vector<unique_ptr<TemplateDeclaration> > template_declarations_;
	map<Scope*, map<string, TemplateDeclaration*> > class_templates_;
	map<Scope*, map<string, TemplateDeclaration*> > alias_templates_;
	map<Scope*, map<string, vector<TemplateDeclaration*> > > function_templates_;
	map<Scope*, map<string, vector<TemplateDeclaration*> > > variable_templates_;
	map<pair<TemplateDeclaration*, string>, TemplateDeclaration*> member_class_templates_;
		map<pair<TemplateDeclaration*, string>, vector<TemplateDeclaration*> > member_function_templates_;
		map<pair<TemplateDeclaration*, string>, vector<TemplateDeclaration*> > member_variable_templates_;
	map<Binding*, TemplateDeclaration*> function_template_placeholders_;
	map<Binding*, vector<TemplateArgument> > function_template_specialization_arguments_;
	map<const void*, TemplateDeclaration*> record_template_declarations_;
	map<const void*, vector<TemplateArgument> > record_template_arguments_;
		map<TemplateDeclaration*, map<string, Binding*> > variable_template_specializations_;
		set<pair<TemplateDeclaration*, string> > active_variable_template_specializations_;
		set<const void*> candidate_only_class_template_specializations_;
		set<const void*> demanded_class_template_specializations_;
		set<TemplateDeclaration*> class_templates_with_dependent_base_;
	set<const void*> record_dependent_base_lookup_skips_;
	vector<map<string, TypePtr> > template_type_substitutions_;
	vector<map<string, TemplateArgument> > template_value_substitutions_;
	vector<set<string> > template_type_parameter_packs_;
	vector<map<string, vector<Binding*> > > function_parameter_pack_substitutions_;
	vector<TemplateDeclaration*> completing_class_template_arguments_;
	vector<ActiveClassInstantiation> active_class_instantiations_;
	mutable vector<string> active_dependent_type_substitution_keys_;
	mutable vector<string> active_dependent_value_member_keys_;
	mutable vector<string> active_dependent_value_expression_keys_;
	vector<TypePtr> active_record_conversion_targets_;
	map<Binding*, Node> function_bodies_;

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
	TypePtr parse_conversion_type_id();
	string conversion_operator_name(TypePtr type) const;
	const Token& current() const;
	const Token& at_token(size_t index) const;

	void parse_declaration_into(Node& out);
	void parse_namespace_or_alias(Node& out);
	void parse_using_family(Node& out);
	void parse_static_assert_declaration();
		void parse_linkage_specification(Node& out);
			void parse_template_declaration();
			void parse_explicit_template_instantiation(bool extern_declaration);
		vector<TemplateParameterInfo> parse_template_parameter_clause();
		TemplateParameterInfo parse_template_parameter_info();
		void skip_template_parameter_default(TemplateParameterInfo& parameter);
					TemplateDeclaration* register_template_declaration( const vector<TemplateParameterInfo>& parameters, size_t decl_begin, size_t decl_end);
			void register_class_template(TemplateDeclaration* declaration);
			void register_alias_template(TemplateDeclaration* declaration);
			void register_function_template(TemplateDeclaration* declaration);
				void register_explicit_function_template_specialization( TemplateDeclaration* declaration, const QualifiedName& qname, TypePtr declared_type, size_t save_pos, const vector<map<string, TypePtr> >& save_subst, const vector<map<string, TemplateArgument> >& save_value_subst);
				bool register_conversion_function_template(TemplateDeclaration* declaration);
				bool register_constructor_template(TemplateDeclaration* declaration);
			bool register_dependent_nested_constructor_template( TemplateDeclaration* declaration);
			bool register_dependent_qualified_conversion_function_template( TemplateDeclaration* declaration);
			bool register_dependent_qualified_member_function_template( TemplateDeclaration* declaration);
			bool register_static_member_variable_template(TemplateDeclaration* declaration);
		size_t skip_template_declaration_body(size_t begin) const;
		bool find_template_type_substitution(const string& name, TypePtr& out) const;
			bool find_template_value_substitution(const string& name, TemplateArgument& out) const;
			bool active_type_parameter_pack(const string& name) const;
			bool type_substitution_hides_value_substitution( const string& name) const;
			bool parameter_pack_expansion_name(const string& name) const;
		bool find_function_parameter_pack_substitution(const string& name, vector<Binding*>& out) const;
		bool template_arguments_dependent( const vector<TemplateArgument>& arguments) const;
		bool active_class_instantiation_dependent() const;
			bool try_parse_template_template_argument(TemplateArgument& out);
			bool try_parse_dependent_qualified_non_type_template_argument( TemplateArgument& out);
				TemplateArgument parse_non_type_template_argument_expression();
				bool parse_template_argument_list(vector<TemplateArgument>& arguments);
				vector<TemplateArgument> expand_template_argument_pack(const TemplateArgument& argument) const;
			void append_completed_template_pack_argument( TemplateDeclaration* declaration, size_t parameter_index, TypePtr parameter_type, const vector<TemplateArgument>& explicit_expanded, size_t& explicit_index, vector<TemplateArgument>& out);
			TemplateArgument parse_default_template_argument( TemplateDeclaration* declaration, size_t parameter_index, const vector<TemplateArgument>& completed_args);
			vector<TemplateArgument> complete_template_arguments( TemplateDeclaration* declaration, const vector<TemplateArgument>& explicit_arguments);
		string template_argument_key( const vector<TemplateArgument>& arguments) const;
		string template_specialization_name( TemplateDeclaration* declaration, const vector<TemplateArgument>& arguments) const;
			TemplateDeclaration* find_class_template(Scope* scope, const string& name);
			TemplateDeclaration* find_alias_template(Scope* scope, const string& name);
			bool resolve_template_name_spelling(const string& spelling, Scope*& qualifier, string& name);
			TypePtr instantiate_alias_template(TemplateDeclaration* declaration, const vector<TemplateArgument>& arguments);
			TypePtr instantiate_class_template(TemplateDeclaration* declaration, const vector<TemplateArgument>& arguments);
	void complete_template_record(TypePtr type);
	void mark_template_specialization_demanded(TypePtr type);
	void mark_template_argument_demanded(const TemplateArgument& argument);
	void complete_member_class_template_record(Binding* binding);
			void instantiate_member_function_templates(TypePtr type, bool object_root = false);
	void instantiate_member_variable_templates(TypePtr type);
			void validate_class_template_definition(TemplateDeclaration* declaration);
			void validate_function_template_definition(TemplateDeclaration* declaration);
			bool type_is_template_dependent(TypePtr type) const;
			TypePtr substitute_template_type(TypePtr type) const;
			TypePtr substitute_template_type_in_scope(TypePtr type, Scope* scope) const;
				TypePtr substitute_function_template_type( TemplateDeclaration* declaration, TypePtr type) const;
			TypePtr resolve_dependent_typename_type(TypePtr type) const;
			bool try_resolve_type_pack_element( const vector<TemplateArgument>& arguments, TypePtr& out);
			bool dependent_typename_template_argument_list( TypePtr type, size_t& index, vector<TemplateArgument>& arguments) const;
			TemplateArgument template_argument_from_instance_argument( const pa11::TemplateInstanceArgument& argument) const;
			TemplateArgument substitute_template_argument( const TemplateArgument& arg) const;
			TypePtr make_integer_sequence_type( const vector<TemplateArgument>& arguments);
			bool try_evaluate_dependent_value_expression_argument( const TemplateArgument& arg, TemplateArgument& out);
		bool resolve_dependent_value_member_argument( const TemplateArgument& arg, TemplateArgument& out) const;
		TypePtr substitute_template_type_parameter(TypePtr type, const string& name, TypePtr replacement) const;
		TemplateArgument substitute_template_argument_type_parameter( const TemplateArgument& arg, const string& name, TypePtr replacement) const;
					vector<Binding*> instantiate_explicit_function_templates(const QualifiedName& name);
					void select_variable_template_specialization( TemplateDeclaration* declaration, const vector<TemplateArgument>& full_args, size_t explicit_arg_count, TemplateDeclaration*& selected_declaration, vector<TemplateArgument>& selected_args);
				Binding* instantiate_variable_template(TemplateDeclaration* declaration, const vector<TemplateArgument>& arguments);
				vector<TemplateDeclaration*> find_function_templates(const QualifiedName& name);
			bool visible_function_template_name(const QualifiedName& name);
			bool visible_variable_template_name(const QualifiedName& name);
				bool record_skips_dependent_base_unqualified_lookup( TypePtr record) const;
			bool constructor_name_matches_scope(Scope* class_scope, const string& name) const;
			Binding* instantiate_function_template( TemplateDeclaration* declaration, const vector<TemplateArgument>& arguments);
			bool deduce_function_template_arguments(TemplateDeclaration* declaration, const vector<Expr>& args, const vector<TemplateArgument>& explicit_arguments, vector<TemplateArgument>& out);
			bool deduce_function_template_target_type(TemplateDeclaration* declaration, TypePtr target, const vector<TemplateArgument>& explicit_arguments, vector<TemplateArgument>& out);
			bool deduce_template_type(TypePtr pattern, TypePtr argument, map<string, TypePtr>& deduced, const map<string, TypePtr>* fixed, map<string, TemplateArgument>* deduced_arguments = NULL) const;
		void parse_simple_or_function_declaration(Node& out, bool emit_node);
		bool parse_qualified_constructor_definition(Node& out, bool emit_node, bool inline_spec = false, bool constexpr_spec = false);
		bool parse_qualified_conversion_definition(Node& out, bool emit_node);
			bool parse_constructor_like_member(bool explicit_ctor = false, bool constexpr_ctor = false);
			bool parse_conversion_function_member(bool explicit_conv = false, bool constexpr_conv = false);
		bool parse_destructor_like_member();
		bool parse_friend_declaration();
		void parse_class_body(Scope* class_scope, bool default_private);

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
		void parse_noptr_declarator_root(Declarator& declarator, bool abstract_allowed);
	void parse_ptr_prefix(vector<PtrOp>& ops);
	void parse_suffixes(vector<Suffix>& suffixes);
	Suffix parse_array_suffix();
	Suffix parse_function_suffix();
	void parse_function_suffix_tail(Suffix& suffix);
		void parse_parameter_clause(vector<ParameterInfo>& parameters, bool& variadic);
	ParameterInfo parse_parameter_declaration();
	vector<ParameterInfo> expand_parameter_pack( const ParameterInfo& parameter) const;
	TypePtr apply_declarator(const Declarator& declarator, TypePtr base);
	TypePtr apply_ptr_ops(TypePtr type, const vector<PtrOp>& ops);
	TypePtr apply_suffixes(TypePtr type, const vector<Suffix>& suffixes);
	const QualifiedName& declarator_name(const Declarator& declarator) const;
	bool declarator_has_name(const Declarator& declarator) const;
	const Suffix* declarator_function_suffix(const Declarator& declarator) const;

		void parse_function_body(Binding* function, const Declarator& declarator, Node& function_node);
		void parse_function_body_from_parameters(Binding* function, const vector<ParameterInfo>& parameters, Node& function_node);
		void parse_constructor_body_from_parameters(Binding* function, TypePtr class_type, const vector<ParameterInfo>& parameters, Node& function_node);
	void remember_function_body(Binding* function, const Node& function_node);
	void enqueue_pending_member_body(Scope* class_scope, PendingFunctionBody pending);
	void enqueue_pending_function_body(PendingFunctionBody pending);
	void push_pending_owner_template_substitutions( const PendingFunctionBody& pending);
	void push_pending_function_template_substitutions( const PendingFunctionBody& pending);
	void parse_pending_member_body_now(const PendingFunctionBody& pending);
		bool parse_pending_function_body(Binding* function);
		bool parse_pending_member_body(Binding* function);
		void ensure_function_body_extra_node(Binding* function);
		void parse_pending_member_bodies(Scope* class_scope);
	void parse_deferred_nested_member_bodies(Scope* class_scope);
	Node parse_compound_statement();
	Node parse_block_item();
	Node parse_statement();
	Node parse_if_statement();
	Node parse_switch_statement();
	Node parse_while_statement();
		Node parse_do_statement();
		Node parse_for_statement();
		Node parse_jump_statement();
		Expr convert_return_expression(Expr expr, TypePtr result);
			Expr convert_aggregate_return_expression(Expr expr, TypePtr result, TypePtr result_record);
			Expr convert_record_constructor_return_expression(Expr expr, TypePtr result);
			void validate_same_record_return_expression(const Expr& expr, TypePtr result);
		Node parse_labeled_statement();
		Node parse_expression_statement();
		Node parse_condition(TypePtr target);

	Expr parse_expression();
	Expr parse_assignment_expression();
	Expr parse_conditional_expression();
	Expr parse_binary_expression(int min_prec);
	Expr parse_unary_expression();
	Expr parse_noexcept_expression();
	Expr parse_is_constructible_expression();
	bool is_constructible_type_trait(const vector<TypePtr>& types);
	Expr parse_postfix_expression();
	Expr parse_postfix_suffixes(Expr expr);
	Expr parse_primary_expression();
	Expr parse_new_expression();
	Expr parse_delete_expression();
	Expr parse_literal_expression();
	Expr parse_cast_expression();
	Expr parse_type_trait_expression(ETokenType keyword);
		Expr parse_c_style_cast_or_parenthesized();
		Expr parse_functional_cast(TypePtr target);
		Expr parse_braced_init_list();
		bool try_parse_static_member_pack_expansion(vector<Expr>& out);
		vector<Expr> parse_argument_list();

		Binding* declare_one(const DeclSpecs& specs, TypePtr base, const Declarator& declarator, const Expr* init, bool function_definition, Node& out);
			Binding* declare_function_entity(const DeclSpecs& specs, Scope* target, const string& name, TypePtr type, const Declarator& declarator, bool function_definition, bool nonstatic_member_function, bool hidden_friend, Node& out);
			Binding* finish_variable_declaration(const DeclSpecs& specs, Scope* target, Binding* variable, const QualifiedName& qname, TypePtr type, const Expr* init, Node& out);
				void complete_class_virtuals(TypePtr type);
			Binding* find_overridden_virtual(TypePtr record, Binding* function) const;
			void apply_variable_initializer(const DeclSpecs& specs, Scope* target, Binding* variable, TypePtr type, const Expr* init, Node& var);
				void apply_braced_variable_initializer(Scope* target, Binding* variable, TypePtr type, const Expr& init, Node& var);
				void apply_record_variable_initializer(Scope* target, Binding* variable, TypePtr type, const Expr& init, Node& var);
				void demand_empty_record_conversion_bodies(TypePtr src_record, TypePtr dst_record, const Node& conversion_node);
				bool record_copy_move_initializer_blocked(TypePtr dst_record, ValueCategory init_category) const;
				void apply_scalar_variable_initializer(const DeclSpecs& specs, Scope* target, Binding* variable, TypePtr type, const Expr& init, Node& var);
			void validate_record_copy_initialization(TypePtr type, const Expr& init);
		bool parse_qualified_destructor_definition(Node& out, bool emit_node);
		Binding* add_alias(Scope* scope, const string& name, TypePtr type);
		Binding* add_function_binding(Scope* scope, const string& name, TypePtr type, bool hidden_friend);
		void add_friend_function(Scope* class_scope, Binding* function);
		void add_friend_class(Scope* class_scope, TypePtr type);
	Binding* add_value(Scope* scope, BindingKind kind, const string& name, TypePtr type);
	TypePtr add_record(Scope* scope, const string& name, const string& tag, bool complete, Scope* class_scope);
	TypePtr add_enum(Scope* scope, const string& name, bool scoped, EFundamentalType underlying, bool complete, bool create_scope);
	void inject_anonymous_union_members(Scope* class_scope, Binding* storage);
	Binding* ensure_default_constructor(TypePtr type, bool force_trivial = false);
	Binding* ensure_aggregate_constructor(TypePtr type, size_t arg_count);
	void ensure_aggregate_constructors_for_init(TypePtr type, const Node& init);
	Binding* ensure_copy_move_constructor(TypePtr type, bool move);
	bool copy_move_constructor_available(TypePtr type, bool move);
	Binding* ensure_copy_move_assignment(TypePtr type, bool move);
	bool copy_move_assignment_available(TypePtr type, bool move);
	Binding* ensure_default_destructor(TypePtr type, bool force_trivial = false);
	Binding* find_default_constructor(TypePtr type) const;
		TypePtr make_member_function_type(Scope* class_scope, TypePtr type);
		Node make_member_init_action(Binding* field, const Node* init);
		Node make_base_init_action(TypePtr base, const Node* init);
		Node make_member_fini_action(Binding* field);
		Node make_base_fini_action(TypePtr base);
		void mark_suppressed_generated_constructor_dependencies(Binding* ctor);
		bool initializer_names_direct_base(Scope* class_scope, TypePtr direct_base, const string& name, const vector<TemplateArgument>* template_arguments = NULL);
		Node default_constructor_action(Binding* variable, bool force_trivial = false);
	void resolve_pending_member_initializers(Scope* class_scope, Node& node);

	QualifiedName parse_id_expression_name();
	Scope* parse_nested_name_specifier(string* spelling);
	Scope* parse_qualified_namespace_specifier();
	Scope* resolve_qualifier(Binding* binding);
	vector<Binding*> resolve_name_set(const QualifiedName& name, int mask);
	Binding* resolve_single_name(const QualifiedName& name, int mask);
	vector<Binding*> lookup_unqualified_set(Scope* start, const string& name, int mask);
	vector<Binding*> lookup_qualified_set(Scope* scope, const string& name, int mask);
	Scope* nearest_namespace_scope(Scope* scope) const;

	Conversion convert_to(const Expr& expr, TypePtr target);
		Conversion convert_reference(const Expr& expr, TypePtr target);
		Conversion try_reference_conversion_functions(const Expr& selected, TypePtr target);
		bool conversion_function_template_candidate(Binding* op) const;
			Binding* instantiate_conversion_function_template_candidate(Binding* op, TypePtr target);
			Conversion convert_value(const Expr& expr, TypePtr target);
			Expr select_overload_expr(const Expr& expr, TypePtr target);
			TemplateDeclaration* replacement_function_template_definition(TemplateDeclaration* declaration);
			Binding* instantiate_target_overload_candidate(Binding* candidate, TypePtr wanted, const map<Binding*, vector<TemplateArgument> >& explicit_template_arguments);
			bool make_call_pack_expr(const Expr& callee, const vector<Expr>& args, Expr& out);
		bool make_template_id_callee_pack_expr(const Expr& callee, Expr& out);
		bool try_expand_expression_pack_pattern(size_t begin, size_t end, vector<Expr>& out);
	Binding* resolve_call_candidate(const vector<Binding*>& overloads, const vector<Expr>& args, const map<Binding*, vector<TemplateArgument> >& explicit_template_arguments, vector<Expr>& converted);
		bool call_candidate_has_arguments(Binding* fn, size_t arg_count) const;
		bool convert_call_candidate_arguments(Binding* fn, const vector<Expr>& args, vector<Expr>& conv_args, vector<int>& ranks, int& object_rank);
		bool instantiate_function_default_argument(Binding* fn, const Expr& default_arg, TypePtr parameter_type, Expr& out);
		Binding* instantiate_template_call_candidate(Binding* fn, const map<Binding*, vector<TemplateArgument> >& explicit_template_arguments, const vector<Expr>& args);
	Binding* resolve_constructor_candidate(TypePtr type, const vector<Expr>& args, bool copy_initialization, vector<Expr>& converted);
	Expr make_constructor_init_expr(TypePtr type, const vector<Expr>& args, bool copy_initialization);
	Expr make_call_expr(Expr callee, vector<Expr> args);
	public:
		bool try_evaluate_constexpr_call(Binding* function, const vector<Node>& args, ConstexprValue& out);
		bool try_evaluate_constexpr_call_values(Binding* function, const vector<ConstexprValue>& args, ConstexprValue& out);
		bool try_evaluate_constexpr_constructor(Binding* function, TypePtr object_type, const vector<ConstexprValue>& args, ConstexprValue& out);
		bool try_evaluate_dependent_value_node(const Node& node, ConstexprValue& out);
		bool try_evaluate_constexpr_expr(const Node& node, ConstexprValue& out);
		bool try_evaluate_constexpr_binding(Binding* binding, ConstexprValue& out);
	private:
	void apply_constexpr_value(Expr& expr, const ConstexprValue& value);
		Expr make_dependent_call_expr(const Expr& callee, const vector<Expr>& args);
		Expr make_id_expr(const QualifiedName& name);
		Expr make_template_substitution_id_expr(const QualifiedName& name);
		vector<Binding*> resolve_id_expr_bindings(const QualifiedName& name, map<Binding*, vector<TemplateArgument> >& explicit_template_arguments);
			Expr make_builtin_id_expr(const QualifiedName& name);
		void synthesize_default_assignment_lookup(const QualifiedName& name, vector<Binding*>& found);
		Expr make_missing_id_expr(const QualifiedName& name);
		Expr make_aliased_member_variable_id_expr(Binding* binding);
		Expr make_enumerator_id_expr(Binding* binding);
		void prefer_static_qualified_overloads(const QualifiedName& name, Expr& out, Binding*& binding);
			Expr make_implicit_member_id_expr(const QualifiedName& name, const vector<Binding*>& found, Binding* binding, Binding* this_binding, const map<Binding*, vector<TemplateArgument> >* explicit_template_arguments = NULL);
		Expr make_binary_expr(ETokenType op, const string& text, Expr lhs, Expr rhs);
		bool make_binary_pack_expr(ETokenType op, const string& text, const Expr& lhs, const Expr& rhs, Expr& out);
	bool make_builtin_converted_binary_expr(ETokenType op, const string& text, const Expr& lhs, const Expr& rhs, Expr& out);
	bool binary_candidate_accepts_operands(Binding* fn, const Expr& lhs, const Expr& rhs) const;
	vector<Binding*> binary_operator_candidates(ETokenType op, const string& text, const Expr& lhs, const Expr& rhs);
	void collect_associated_hidden_friends(TypePtr type, const string& name, set<Scope*>& seen, vector<Binding*>& out) const;
	void collect_associated_namespace_functions(TypePtr type, const string& name, set<Scope*>& seen, vector<Binding*>& out);
		Expr make_assignment_expr(ETokenType op, const string& text, Expr lhs, Expr rhs);
		Expr make_overloaded_compound_assignment_expr(ETokenType op, const string& text, Expr lhs, Expr rhs, TypePtr lhs_bare);
		Expr make_record_assignment_expr(Expr lhs, Expr rhs, TypePtr lhs_bare);
	Expr make_unary_expr(ETokenType op, const string& text, Expr inner);
	Expr make_postfix_expr(ETokenType op, const string& text, Expr inner);
	Expr make_subscript_expr(Expr lhs, Expr rhs);
	Expr make_record_subscript_expr(TypePtr record, Expr lhs, Expr rhs);
	Expr make_member_expr(Expr object, const string& name, const string& op);
		Expr make_dependent_member_expr(const Expr& object, const string& name, const string& op);
		Expr make_cast_expr(TypePtr target, const string& op_text, Expr inner, bool suppress_target_pack = false);
		bool make_cast_pack_expr(TypePtr target, const string& op_text, const Expr& inner, bool suppress_target_pack, Expr& out);
	Expr make_sizeof_expr(uint64_t value);
	Expr make_dependent_sizeof_expr(ETokenType keyword, TypePtr operand);
	Expr make_dependent_sizeof_pack_expr(const string& name);
	Expr make_address_expr(const string& text, Expr inner);
	Expr make_deref_expr(const string& text, Expr inner);

	bool is_assignment_operator(ETokenType& op) const;
	bool binary_operator(ETokenType& op, int& prec) const;
	bool expression_starts_type_name(TypePtr& type);
	bool is_zero_literal(const Expr& expr) const;
		bool type_can_bind_reference(TypePtr target, const Expr& expr) const;
		bool types_reference_compatible(TypePtr target, TypePtr source) const;
		bool pointer_conversion_viable(TypePtr source, TypePtr target) const;
		int record_base_distance(TypePtr source, TypePtr target) const;
		bool active_function_matches(Binding* function) const;
		bool active_context_has_class_access(Scope* class_scope) const;
		bool member_access_allowed(Binding* member, TypePtr object_record) const;
		bool is_pointer_arithmetic(const Expr& lhs, const Expr& rhs) const;
	bool is_pointer_difference(const Expr& lhs, const Expr& rhs) const;
		int scalar_conversion_rank(TypePtr source, TypePtr target) const;
		bool ranks_better(const vector<int>& lhs, const vector<int>& rhs) const;
		void ensure_copy_move_constructor_for_single_arg( TypePtr record, const vector<Expr>& args);
		void add_variadic_argument_ranks(Binding* fn, size_t arg_count, vector<int>& ranks) const;
		void prepare_member_call(Expr& callee, vector<Expr>& args);
		TypePtr pointer_arithmetic_type(ETokenType op, const Expr& lhs, const Expr& rhs) const;
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
	string operator_function_name(ETokenType type, const string& source) const;
	void skip_balanced(ETokenType open, ETokenType close);
	void skip_template_parameter_clause();
};

void add_child(Node& parent, const Node& child);
void dump_node(ostream& out, const Node& node, int depth);
void annotate_expr_node(Expr& expr);

}  // namespace internal
}  // namespace pa12
