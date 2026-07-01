#include "pa12_internal.h"
#include "pa12_types_support.h"
#include <stdexcept>
using namespace std;
namespace pa12 {
namespace internal {

static bool top_level_semicolon_before_rparen(const vector<Token>& tokens, size_t pos)
{ int paren = 0; int square = 0; int brace = 0; for (size_t i = pos; i < tokens.size(); ++i) { if (tokens[i].kind != posttoken::TokenKind::Simple) continue; ETokenType type = tokens[i].type;
if (type == OP_LPAREN) ++paren; else if (type == OP_RPAREN) { if (paren == 0 && square == 0 && brace == 0) return false; if (paren > 0) --paren; }
else if (type == OP_LSQUARE) ++square; else if (type == OP_RSQUARE) { if (square > 0) --square; }
else if (type == OP_LBRACE) ++brace; else if (type == OP_RBRACE) { if (brace > 0) --brace; }
else if (type == OP_SEMICOLON && paren == 0 && square == 0 && brace == 0) return true; } return false; }
static Expr expr_from_node(const Node& node) { Expr out; out.valid = true;
out.node = node; out.type = node.type; out.category = node.category; out.binding = node.binding;
out.overloads = node.overloads; out.explicit_template_arguments = node.explicit_template_arguments;
out.has_constant_value = node.has_constant_value; out.constant_value = node.constant_value; out.dependent_value_name = node.dependent_value_name; out.dependent_value_owner_template_name =
node.dependent_value_owner_template_name; out.dependent_value_member_name = node.dependent_value_member_name; out.dependent_value_negated = node.dependent_value_negated; out.dependent_value_owner_template_arguments =
node.dependent_value_owner_template_arguments; out.braced_init_list = node.line.compare(0, 16, "braced-init-list") == 0; return out;
	}

	Node Parser::parse_compound_statement() { expect(OP_LBRACE); Node node("compound-statement");
	vector<Scope*> saved_scopes = scopes_;
	Scope* block = pa11::create_child_scope(current_scope(), ScopeKind::Block, ""); scopes_.push_back(block); try { while (!at(OP_RBRACE)) {
	Node item = parse_block_item(); if (!item.line.empty()) add_child(node, item); }
	} catch (...) { scopes_ = saved_scopes; throw; }
	scopes_ = saved_scopes; expect(OP_RBRACE); return node; }
Node Parser::parse_block_item() { if (at(KW_USING)) {
Node node("compound-statement-placeholder"); parse_using_family(node); if (node.children.empty()) return Node();
return node.children[0]; } if (at(KW_NAMESPACE)) {
Node node; parse_namespace_or_alias(node); return Node(); }
if (at(KW_STATIC_ASSERT)) { parse_static_assert_declaration(); return Node();
} if (at_gnu_asm()) return parse_statement();
if (starts_declaration()) { size_t save = pos_;
size_t attr_save = pos_; skip_attributes(); bool definitely_declaration = at_simple_builtin() || at_simple_cv() || at(KW_TYPEDEF) ||
at(KW_CONSTEXPR) || at(KW_EXTERN) || at(KW_STATIC) || at(KW_DECLTYPE) ||
at(KW_TYPENAME) || starts_class_key() || at(KW_ENUM) || at(KW_STATIC_ASSERT) ||
(at_identifier() && (current().source == "__int128" || current().source == "_BitInt" || current().source == "_Atomic" || current().source == "__extension__" || current().source == "__decltype" || current().source == "__decltype__" || current().source == "__typeof" || current().source == "__typeof__" || current().source == "_Complex" || current().source == "__complex__" || current().source == "__complex")) ||
(at_identifier() && pos_ + 1 < tokens_.size() && tokens_[pos_ + 1].kind == posttoken::TokenKind::Identifier); pos_ = attr_save; if (definitely_declaration && at_identifier() && pos_ + 4 < tokens_.size() && tokens_[pos_ + 1].kind == posttoken::TokenKind::Identifier && tokens_[pos_ + 2].kind == posttoken::TokenKind::Simple && tokens_[pos_ + 2].type == OP_LPAREN && tokens_[pos_ + 3].kind == posttoken::TokenKind::Identifier && tokens_[pos_ + 4].kind == posttoken::TokenKind::Simple && tokens_[pos_ + 4].type == OP_RPAREN && pa11::lookup_unqualified(current_scope(), tokens_[pos_ + 3].source, pa11::LOOKUP_VALUE) != NULL) definitely_declaration = false; if (!definitely_declaration && (at_identifier() || at(OP_COLON2)))
{ size_t type_save = pos_; TypePtr type_probe; if (try_parse_type_name(type_probe) &&
(starts_declarator() || at_identifier())) { bool parenthesized_this_argument = at(OP_LPAREN) &&
pos_ + 2 < tokens_.size() && tokens_[pos_ + 1].kind == posttoken::TokenKind::Simple && (tokens_[pos_ + 1].type == OP_STAR || tokens_[pos_ + 1].type == OP_AMP) &&
	tokens_[pos_ + 2].kind == posttoken::TokenKind::Simple && tokens_[pos_ + 2].type == KW_THIS; bool empty_functional_temporary = at(OP_LPAREN) &&
	pos_ + 1 < tokens_.size() && tokens_[pos_ + 1].kind == posttoken::TokenKind::Simple && tokens_[pos_ + 1].type == OP_RPAREN; bool parenthesized_non_declarator = false;
	if (at(OP_LPAREN) && pos_ + 1 < tokens_.size() && tokens_[pos_ + 1].kind != posttoken::TokenKind::Identifier) { parenthesized_non_declarator = true;
	if (tokens_[pos_ + 1].kind == posttoken::TokenKind::Simple) { ETokenType next = tokens_[pos_ + 1].type;
	parenthesized_non_declarator = !(next == OP_STAR || next == OP_AMP || next == OP_LAND || next == OP_LPAREN || next == OP_COLON2); } }
	bool functional_temporary_member_access = false;
	if (at(OP_LPAREN))
	{
		size_t p = pos_;
		int paren_depth = 0;
		while (p < tokens_.size())
		{
			if (tokens_[p].kind == posttoken::TokenKind::Simple &&
			    tokens_[p].type == OP_LPAREN)
				++paren_depth;
			else if (tokens_[p].kind == posttoken::TokenKind::Simple &&
			         tokens_[p].type == OP_RPAREN)
			{
				--paren_depth;
				if (paren_depth == 0)
				{
					size_t after = p + 1;
					functional_temporary_member_access =
						after < tokens_.size() &&
						tokens_[after].kind ==
							posttoken::TokenKind::Simple &&
						(tokens_[after].type == OP_DOT ||
						 tokens_[after].type == OP_ARROW);
					break;
				}
			}
			++p;
		}
	}
	if (!parenthesized_this_argument &&
	    !empty_functional_temporary &&
	    !parenthesized_non_declarator &&
	    !functional_temporary_member_access)
		definitely_declaration = true; } pos_ = type_save;
	} vector<Scope*> declaration_scopes = scopes_; try { Node node;
	parse_simple_or_function_declaration(node, true); if (!node.children.empty()) return node.children[0]; return Node();
	} catch (const exception&) { pos_ = save; scopes_ = declaration_scopes;
	if (definitely_declaration) throw; } }
return parse_statement(); } Node Parser::parse_statement() {
skip_attributes(); if (at_gnu_asm()) { skip_gnu_asm(); expect(OP_SEMICOLON); return Node("expression-statement"); }
if (at(OP_LBRACE)) return parse_compound_statement(); if (at(KW_IF)) return parse_if_statement();
if (at(KW_SWITCH)) return parse_switch_statement(); if (at(KW_WHILE)) return parse_while_statement();
if (at(KW_DO)) return parse_do_statement(); if (at(KW_FOR)) return parse_for_statement();
if (at_try_keyword()) return parse_try_statement(); if (at(KW_RETURN) || at(KW_BREAK) || at(KW_CONTINUE) || at(KW_GOTO)) return parse_jump_statement();
if ((at_identifier() && lookahead(OP_COLON, 1)) || at(KW_CASE) || at(KW_DEFAULT)) return parse_labeled_statement(); return parse_expression_statement();
} void Parser::skip_constexpr_if_statement()
{ skip_attributes(); if (at(OP_LBRACE)) { skip_balanced(OP_LBRACE, OP_RBRACE); return; } if (at(KW_IF)) { ++pos_; if (at(KW_CONSTEXPR)) ++pos_; if (at(OP_LPAREN)) skip_balanced(OP_LPAREN, OP_RPAREN); skip_constexpr_if_statement(); if (consume(KW_ELSE)) skip_constexpr_if_statement(); return; }
if (at(KW_FOR) || at(KW_WHILE) || at(KW_SWITCH)) { ++pos_; if (at(OP_LPAREN)) skip_balanced(OP_LPAREN, OP_RPAREN); skip_constexpr_if_statement(); return; }
if (at(KW_DO)) { ++pos_; skip_constexpr_if_statement(); if (consume(KW_WHILE) && at(OP_LPAREN)) skip_balanced(OP_LPAREN, OP_RPAREN); consume(OP_SEMICOLON); return; }
if (at(KW_CASE) || at(KW_DEFAULT)) { ++pos_; while (!at_eof() && !consume(OP_COLON)) { if (at(OP_LPAREN)) skip_balanced(OP_LPAREN, OP_RPAREN); else ++pos_; } skip_constexpr_if_statement(); return; }
if (at_identifier() && lookahead(OP_COLON, 1)) { pos_ += 2; skip_constexpr_if_statement(); return; }
while (!at_eof()) { if (at(OP_LBRACE)) skip_balanced(OP_LBRACE, OP_RBRACE); else if (at(OP_LPAREN)) skip_balanced(OP_LPAREN, OP_RPAREN); else if (at(OP_LSQUARE)) skip_balanced(OP_LSQUARE, OP_RSQUARE); else if (consume(OP_SEMICOLON)) break; else ++pos_; } }
	Node Parser::parse_if_statement()
	{
		expect(KW_IF);
		bool constexpr_if = consume(KW_CONSTEXPR);
		Node node("if-statement");
		Scope* if_scope =
			pa11::create_child_scope(current_scope(), ScopeKind::Block, "");
		scopes_.push_back(if_scope);
		try
		{
			expect(OP_LPAREN);
			if (top_level_semicolon_before_rparen(tokens_, pos_))
			{
				Node init_node("if-init-statement");
				if (at(KW_USING))
					parse_using_family(init_node);
				else if (starts_declaration())
					parse_simple_or_function_declaration(init_node, true);
				else
					init_node = parse_expression_statement();
				add_child(node, parse_condition(pa11::make_fundamental(FT_BOOL)));
			}
			else
				add_child(node, parse_condition(pa11::make_fundamental(FT_BOOL)));
			expect(OP_RPAREN);
			if (constexpr_if && !node.children.empty() &&
			    !node.children[0].children.empty() &&
			    node.children[0].children[0].has_constant_value)
			{
				bool take_then =
					node.children[0].children[0].constant_value != 0;
				if (take_then)
				{
					Node selected = parse_statement();
					if (consume(KW_ELSE))
						skip_constexpr_if_statement();
					scopes_.pop_back();
					return selected;
				}
				skip_constexpr_if_statement();
				if (consume(KW_ELSE))
				{
					Node selected = parse_statement();
					scopes_.pop_back();
					return selected;
				}
				scopes_.pop_back();
				return Node("compound-statement");
			}
			Node then_node("then");
			add_child(then_node, parse_statement());
			add_child(node, then_node);
			if (consume(KW_ELSE))
			{
				Node else_node("else");
				add_child(else_node, parse_statement());
				add_child(node, else_node);
			}
			scopes_.pop_back();
			return node;
		}
		catch (...)
		{
			scopes_.pop_back();
			throw;
		}
	}
	Node Parser::parse_switch_statement()
	{
		expect(KW_SWITCH);
		Node node("switch-statement");
		Scope* switch_scope =
			pa11::create_child_scope(current_scope(), ScopeKind::Block, "");
		scopes_.push_back(switch_scope);
		try
		{
			expect(OP_LPAREN);
			add_child(node, parse_condition(pa11::make_fundamental(FT_INT)));
			expect(OP_RPAREN);
			add_child(node, parse_statement());
			scopes_.pop_back();
			return node;
		}
		catch (...)
		{
			scopes_.pop_back();
			throw;
		}
	}
	Node Parser::parse_while_statement()
	{
		expect(KW_WHILE);
		Node node("while-statement");
		Scope* while_scope =
			pa11::create_child_scope(current_scope(), ScopeKind::Block, "");
		scopes_.push_back(while_scope);
		try
		{
			expect(OP_LPAREN);
			add_child(node, parse_condition(pa11::make_fundamental(FT_BOOL)));
			expect(OP_RPAREN);
			add_child(node, parse_statement());
			scopes_.pop_back();
			return node;
		}
		catch (...)
		{
			scopes_.pop_back();
			throw;
		}
	}
	Node Parser::parse_do_statement()
{ expect(KW_DO); Node node("do-statement"); add_child(node, parse_statement());
expect(KW_WHILE); expect(OP_LPAREN); Node cond("condition"); Expr do_cond = parse_expression();
if (pa11::strip_cv(expression_object_type(do_cond.type))->kind == pa11::TypeKind::Record) { Conversion conv =
convert_to(do_cond, pa11::make_fundamental(FT_BOOL)); if (conv.viable) do_cond = conv.expr; }
add_child(cond, do_cond.node); add_child(node, cond); expect(OP_RPAREN); expect(OP_SEMICOLON);
return node; } Node Parser::parse_for_statement() {
expect(KW_FOR); expect(OP_LPAREN); Scope* for_scope = pa11::create_child_scope(current_scope(), ScopeKind::Block, "");
scopes_.push_back(for_scope); try { if (starts_declaration()) {
size_t save = pos_; try { Node range_for = parse_range_for_statement(); scopes_.pop_back(); return range_for;
} catch (const runtime_error& err) { pos_ = save;
if (string(err.what()) != "not range-for") throw; } }
Node node("for-statement"); Node init("for-init-statement"); if (starts_declaration()) add_child(init, parse_block_item());
else { if (!at(OP_SEMICOLON)) add_child(init, parse_expression().node);
expect(OP_SEMICOLON); } add_child(node, init); if (!at(OP_SEMICOLON))
add_child(node, parse_condition(pa11::make_fundamental(FT_BOOL))); expect(OP_SEMICOLON); if (!at(OP_RPAREN)) {
Node iter("iteration"); add_child(iter, parse_expression().node); add_child(node, iter); }
expect(OP_RPAREN); add_child(node, parse_statement()); scopes_.pop_back(); return node; } catch (...) { scopes_.pop_back(); throw; } }
Node Parser::parse_range_for_statement() { DeclSpecs specs = parse_decl_specifier_seq(false); TypePtr base = type_from_decl_specs(specs);
Declarator declarator = parse_declarator(false); if (!consume(OP_COLON)) throw runtime_error("not range-for"); Expr range = at(OP_LBRACE) ? parse_braced_init_list() : parse_expression();
bool hidden_range = false; bool initializer_list_range = false; TypePtr initializer_list_element; Node range_node; TypePtr range_array_type; if (range.braced_init_list && range.type.get() == NULL)
{ if (range.node.children.empty()) throw runtime_error("empty range braced-list"); Expr first = expr_from_node(range.node.children[0]);
TypePtr elem = lvalue_to_rvalue_type(first.type); range_array_type = pa11::make_array(elem, false, range.node.children.size()); Node typed("braced-init-list");
typed.type = range_array_type; typed.category = ValueCategory::PRValue; for (size_t i = 0; i < range.node.children.size(); ++i) {
Expr child = expr_from_node(range.node.children[i]); Conversion conv = convert_to(child, elem); if (!conv.viable) throw runtime_error("invalid range initializer");
add_child(typed, conv.expr.node); } range.node = typed; range.type = range_array_type;
range.category = ValueCategory::PRValue; annotate_expr_node(range); hidden_range = true; }
else { range_array_type = expression_object_type(range.type); TypePtr bare_range = pa11::strip_cv(range_array_type);
if (is_std_initializer_list_type(range_array_type, &initializer_list_element)) { normalize_std_initializer_list_type(range_array_type); initializer_list_range = true; }
else if (bare_range->kind == pa11::TypeKind::Record && bare_range->scope != NULL) { auto make_hidden_var =
[&](const string& prefix, const Expr& init) -> Node { string name = prefix + to_string(++range_for_counter_); Binding* binding = add_value(current_scope(), BindingKind::Variable,
name, init.type); Node var("variable " + name + " " + pa11::describe_type(init.type)); var.binding = binding;
var.type = init.type; add_child(var, init.node); return var; };
auto id_for_binding = [&](Binding* binding) -> Expr { Expr id; id.valid = true;
id.binding = binding; id.type = binding->type; id.category = ValueCategory::LValue; id.node = Node("id-expression lvalue " +
pa11::describe_type(id.type) + " " + binding->name); annotate_expr_node(id); return id;
}; auto make_begin_end_call = [&](const string& name) -> Expr { try
{ Expr member = make_member_expr(range, name, "."); return make_call_expr(member, vector<Expr>()); }
catch (const runtime_error&) { QualifiedName qname; qname.name = name;
qname.spelling = name; Expr callee = make_id_expr(qname); vector<Expr> args; args.push_back(range);
return make_call_expr(callee, args); } }; Expr begin_call = make_begin_end_call("begin");
Expr end_call = make_begin_end_call("end"); Node begin_var = make_hidden_var("__begin", begin_call); Node end_var = make_hidden_var("__end", end_call); Expr begin_id = id_for_binding(begin_var.binding);
Expr end_id = id_for_binding(end_var.binding); Expr deref = make_unary_expr(OP_STAR, "*", begin_id); Node loop_decl("simple-declaration"); Binding* loop_binding =
declare_one(specs, base, declarator, &deref, false, loop_decl); if (loop_binding == NULL || loop_decl.children.empty()) throw runtime_error("invalid range declaration"); Expr cond = make_binary_expr(OP_NE, "!=", begin_id, end_id);
Expr inc = make_unary_expr(OP_INC, "++", begin_id); expect(OP_RPAREN); Node node("range-for-statement"); node.token_text = "iterator";
add_child(node, begin_var); add_child(node, end_var); add_child(node, loop_decl.children[0]); add_child(node, cond.node);
add_child(node, deref.node); add_child(node, inc.node); add_child(node, parse_statement()); return node;
} if (!initializer_list_range && (bare_range->kind != pa11::TypeKind::Array || bare_range->unknown_bound)) throw runtime_error("unsupported range-for");
} TypePtr range_bare = pa11::strip_cv(range_array_type); TypePtr element_type = initializer_list_range ? initializer_list_element : range_bare->base; Expr element;
element.valid = true; element.type = element_type; element.category = ValueCategory::LValue; element.node = Node("range-element lvalue " +
pa11::describe_type(element_type)); annotate_expr_node(element); Node loop_decl("simple-declaration"); Binding* loop_binding =
declare_one(specs, base, declarator, &element, false, loop_decl); if (loop_binding == NULL || loop_decl.children.empty()) throw runtime_error("invalid range declaration"); Node loop_var = loop_decl.children[0];
if (hidden_range) { string range_name = "__range" + to_string(++range_for_counter_); Binding* range_binding =
add_value(current_scope(), BindingKind::Variable, range_name, range_array_type); range_node = Node("variable " + range_name + " " + pa11::describe_type(range_array_type));
range_node.binding = range_binding; range_node.type = range_array_type; add_child(range_node, range.node); }
else range_node = range.node; TypePtr int_type = pa11::make_fundamental(FT_INT); string idx_name = "__idx" + to_string(++range_for_counter_);
Binding* idx_binding = add_value(current_scope(), BindingKind::Variable, idx_name, int_type); Node idx_var("variable " + idx_name + " " + pa11::describe_type(int_type));
idx_var.binding = idx_binding; idx_var.type = int_type; Expr zero; zero.valid = true;
zero.type = int_type; zero.category = ValueCategory::PRValue; zero.constant_expression = true; zero.has_constant_value = true;
zero.constant_value = 0; zero.node = Node("literal prvalue " + pa11::describe_type(int_type) + " 0"); zero.node.token_text = "0";
annotate_expr_node(zero); add_child(idx_var, zero.node); expect(OP_RPAREN); Node node("range-for-statement"); if (initializer_list_range) node.token_text = "initializer-list";
add_child(node, range_node); add_child(node, idx_var); add_child(node, loop_var); add_child(node, parse_statement());
return node;
} } }  // namespace pa12::internal
