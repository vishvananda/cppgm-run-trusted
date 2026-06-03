#pragma once

#include <map>
#include <set>
#include <string>
#include <vector>

#include "pa10_internal.h"

using namespace std;

namespace pa10 {
namespace internal {

class Parser
{
public:
	explicit Parser(const vector<Token>& tokens);
	Ast parse_translation_unit();

private:
	const vector<Token>& tokens_;
	size_t pos_;
	vector<Scope> scopes_;
	vector<string> namespace_stack_;
	map<string, set<string> > namespace_types_;
	map<string, string> namespace_aliases_;
	map<string, set<string> > class_member_types_;
	vector<string> pending_compound_type_imports_;
	vector<string> pending_compound_type_names_;
	int class_depth_;
	int expression_angle_stop_;
	vector<string> class_stack_;

	const Token& current() const;
	const Token& at(size_t pos) const;
	bool eof() const;
	bool simple(ETokenType type) const;
	bool simple_at(size_t pos, ETokenType type) const;
	bool identifier() const;
	bool literal() const;
	bool consume(ETokenType type);
	bool consume_identifier(string& out);
	bool consume_literal(string& out);
	const Token& expect(ETokenType type);
	string expect_identifier();
	string expect_literal();
	void skip_attributes();
	bool starts_attribute() const;
	void skip_balanced(ETokenType open, ETokenType close);

	void push_scope();
	void push_template_scope();
	void push_namespace_scope(const string& name);
	void push_class_scope(const string& name);
	void pop_scope();
	void add_type_name(const string& name);
	void add_template_type_name(const string& name);
	void add_value_name(const string& name);
	void add_namespace_name(const string& name);
	bool is_type_name(const string& name) const;
	bool value_shadows_type(const string& name) const;
	string current_namespace_name() const;
	string qualify_namespace_name(const string& name) const;
	string resolve_namespace_name(const string& name) const;
	void import_namespace_types(const string& name);
	void record_namespace_alias(const string& name, const string& target);
	void import_class_member_types(const string& name);
	void queue_compound_type_imports_for_qualified_name(const string& name);
	void queue_compound_type_name_from_qualified_name(const string& name);

	Ast parse_declaration();
	Ast parse_block_item();
	Ast parse_namespace_definition();
	Ast parse_namespace_alias_definition();
	Ast parse_using();
	Ast parse_alias_declaration();
	Ast parse_template_declaration();
	Ast parse_template_parameter_clause();
	Ast parse_template_parameter();
	Ast parse_class_declaration();
	Ast parse_class_specifier(bool consume_semicolon);
	Ast parse_class_forward();
	Ast parse_enum_declaration();
	Ast parse_enum_specifier(bool consume_semicolon);
	Ast parse_static_assert_declaration();
	Ast parse_linkage_specification();
	Ast parse_explicit_instantiation();
	Ast parse_simple_or_function_declaration(bool member_context);
	Ast parse_special_member(bool member_context);
	Ast parse_member_declaration();
	Ast parse_bit_field_declaration(const DeclParse& specs);

	DeclParse parse_decl_specifier_seq(bool type_id_context);
	Ast parse_one_decl_specifier(bool type_id_context,
	                             DeclParse& out,
	                             bool& consumed);
	Ast parse_type_id();
	Ast parse_type_specifier_seq();
	Ast parse_type_specifier(bool& consumed);
	Ast parse_abstract_declarator();
	DeclaratorParse parse_declarator(bool abstract_allowed);
	DeclaratorParse parse_direct_declarator(bool abstract_allowed);
	void parse_ptr_operators(const Ast& node);
	Ast parse_parameter_clause();
	Ast parse_parameter_declaration();
	void parse_function_suffixes(const Ast& node);
	Ast parse_trailing_return_type();
	Ast parse_initializer();
	Ast parse_braced_init_list();
	void parse_initializer_items(const Ast& node, ETokenType close);

	Ast parse_statement();
	Ast parse_compound_statement();
	Ast parse_if_statement();
	Ast parse_switch_statement();
	Ast parse_while_statement();
	Ast parse_do_statement();
	Ast parse_for_statement();
	Ast parse_try_block();
	Ast parse_handler();
	Ast parse_exception_declaration();
	Ast parse_jump_statement();
	Ast parse_labeled_statement();
	Ast parse_expression_statement();
	Ast parse_condition();

	Ast parse_expression();
	Ast parse_assignment_expression();
	Ast parse_conditional_expression();
	Ast parse_binary_expression(int min_prec);
	Ast parse_unary_expression();
	Ast parse_postfix_expression();
	Ast parse_postfix_suffixes(Ast expr);
	Ast parse_primary_expression();
	Ast parse_lambda_expression();
	Ast parse_cast_expression();
	Ast parse_new_expression();
	Ast parse_delete_expression();
	Ast parse_type_trait_expression(ETokenType keyword);
	Ast parse_c_style_cast_or_parenthesized();
	Ast parse_argument_list(const string& node_name, ETokenType close);

	string parse_id_expression_text();
	string parse_unqualified_id_text(bool allow_template_id = true);
	string parse_template_id_text(const string& base);
	string parse_qualified_suffix_text(string base);
	string parse_type_name_text();
	string parse_balanced_text(ETokenType open, ETokenType close);
	bool consume_close_angle();
	bool starts_template_argument_list() const;
	bool starts_declaration() const;
	bool starts_type_id() const;
	bool id_expression_call_follows(size_t pos) const;
	bool current_less_starts_template_id() const;
	bool qualified_template_name_is_type(size_t name_pos) const;
	bool starts_parameter_declaration_at(size_t pos) const;
	bool starts_abstract_declarator_at(size_t pos) const;
	bool starts_special_member() const;
	bool starts_expression() const;
	bool is_assignment_operator(ETokenType& op) const;
	bool binary_operator(ETokenType& op, int& prec) const;
	Ast make_binary(ETokenType op, const string& text, Ast lhs, Ast rhs) const;
	Ast make_id_expression(const string& text) const;
};

}  // namespace internal
}  // namespace pa10
