#include "pa12_internal.h"
#include "pa12_types_support.h"

#include <stdexcept>

using namespace std;

namespace pa12 {
namespace internal {

namespace {
bool same_return_template_argument(const pa11::TemplateInstanceArgument& left, const pa11::TemplateInstanceArgument& right);
bool same_return_template_arguments(const vector<pa11::TemplateInstanceArgument>& left, const vector<pa11::TemplateInstanceArgument>& right)
{ size_t common = min(left.size(), right.size()); for (size_t i = 0; i < common; ++i) if (!same_return_template_argument(left[i], right[i])) return false; return common == left.size() || common == right.size(); }
bool same_return_record_type(TypePtr left, TypePtr right) { TypePtr l = pa11::strip_cv(left); TypePtr r = pa11::strip_cv(right);
if (l.get() == NULL || r.get() == NULL) return l.get() == r.get(); if (pa11::same_type(l, r)) return true;
if (l->kind != pa11::TypeKind::Record || r->kind != pa11::TypeKind::Record) return false; if (!l->is_template_specialization || !r->is_template_specialization) return false;
if (l->template_primary_name != r->template_primary_name && l->name != r->name) return false; return same_return_template_arguments(l->template_arguments, r->template_arguments); }
bool same_return_template_argument(const pa11::TemplateInstanceArgument& left, const pa11::TemplateInstanceArgument& right)
{ if (left.kind != right.kind) return false; if (left.kind == pa11::TemplateInstanceArgumentKind::Type) return same_return_record_type(left.type, right.type); if (left.kind == pa11::TemplateInstanceArgumentKind::Value) { if (left.dependent != right.dependent) return same_return_record_type(left.type, right.type); return left.value_negated == right.value_negated && left.value == right.value && left.value_name == right.value_name && same_return_record_type(left.type, right.type); } if (left.kind == pa11::TemplateInstanceArgumentKind::Template) return left.template_name == right.template_name && left.dependent == right.dependent; return same_return_template_arguments(left.pack, right.pack); }
}  // namespace

Node Parser::parse_try_statement() {
expect_try_keyword(); Node node("try-statement"); Node try_block("try-block"); add_child(try_block, parse_compound_statement());
add_child(node, try_block); do { expect_catch_keyword();
expect(OP_LPAREN); Node catch_node("catch-clause"); string catch_name; Binding* catch_binding = NULL; if (consume(OP_DOTS)) catch_node.token_text = "catch-all";
else { TypePtr catch_type = parse_type_id(); if (at_identifier()) catch_name = consume_identifier(); catch_node.type = catch_type;
catch_node.line += " " + pa11::describe_type(catch_type); } expect(OP_RPAREN); expect(OP_LBRACE); Node body("compound-statement");
Scope* block = pa11::create_child_scope(current_scope(), ScopeKind::Block, ""); scopes_.push_back(block);
if (!catch_name.empty()) { catch_binding = add_value(block, BindingKind::Variable, catch_name, catch_node.type); catch_node.binding = catch_binding; }
while (!at(OP_RBRACE)) { Node item = parse_block_item(); if (!item.line.empty()) add_child(body, item); }
scopes_.pop_back(); expect(OP_RBRACE); add_child(catch_node, body);
add_child(node, catch_node); } while (at_catch_keyword()); return node;
} Expr Parser::convert_aggregate_return_expression(Expr expr, TypePtr result, TypePtr result_record)
{ expr.type = result; expr.node.type = result; ensure_aggregate_constructors_for_init(result, expr.node);
vector<Expr> args; for (size_t i = 0; i < expr.node.children.size(); ++i) { Expr arg;
arg.valid = true; arg.node = expr.node.children[i]; arg.type = arg.node.type; arg.category = arg.node.category;
arg.binding = arg.node.binding; arg.has_constant_value = arg.node.has_constant_value; arg.constant_value = arg.node.constant_value; arg.null_pointer_constant =
arg.has_constant_value && arg.constant_value == 0 && pa11::is_integral_or_bool_type(arg.type); args.push_back(arg);
	} prepare_constructor_template_candidates(result_record, args);
	bool aggregate_blocked = record_has_aggregate_blocking_constructor(result_record);
	if (!aggregate_blocked) complete_aggregate_constructor_args(result_record, args); Binding* aggregate_ctor = aggregate_blocked ? NULL : ensure_aggregate_constructor(result_record, args.size());
	if (aggregate_ctor == NULL && args.empty() && result_record->fields.empty() &&
	    pa11::record_direct_bases(result_record).empty() &&
	    !record_has_aggregate_blocking_constructor(result_record))
		return expr;
	if (aggregate_ctor == NULL) { try {
	return make_constructor_init_expr(result, args, true); } catch (const runtime_error& err) {
	(void)err;
	Binding* direct_ctor = NULL;
	map<string, vector<Binding*> >::const_iterator ctors =
		result_record->scope != NULL
		? result_record->scope->members.find(result_record->scope->name)
		: map<string, vector<Binding*> >::const_iterator();
	if (result_record->scope != NULL &&
	    ctors != result_record->scope->members.end())
		for (size_t ci = 0; ci < ctors->second.size(); ++ci) {
			Binding* candidate = ctors->second[ci];
			if (candidate->kind != BindingKind::Function ||
			    candidate->type.get() == NULL ||
			    candidate->type->kind != pa11::TypeKind::Function ||
			    candidate->type->parameters.size() != args.size() + 1 ||
			    candidate->is_generated_aggregate_constructor)
				continue;
			direct_ctor = candidate;
			if (candidate->is_inline_definition)
				break;
		}
	if (direct_ctor != NULL) {
		direct_ctor = instantiate_selected_constructor_body(direct_ctor);
		finalize_constructor_candidate(result_record, direct_ctor);
		Expr constructed; constructed.valid = true;
		constructed.type = result; constructed.category = ValueCategory::PRValue;
		constructed.braced_init_list = true; constructed.copy_initialization = true;
		constructed.node = Node("braced-init-list"); constructed.node.type = result;
		constructed.node.category = constructed.category;
		constructed.node.direct_call = direct_ctor;
		for (size_t i = 0; i < args.size(); ++i) {
			Conversion conv = convert_to(args[i], direct_ctor->type->parameters[i + 1]);
			add_child(constructed.node,
			          conv.viable ? conv.expr.node : args[i].node);
		}
		annotate_expr_node(constructed); constructed.node.direct_call = direct_ctor;
		return constructed;
	}
	Conversion conv = convert_to(expr, result); if (!conv.viable) {
		throw runtime_error("invalid return conversion");
	} return conv.expr;
} } Expr constructed; constructed.valid = true;
constructed.type = result; constructed.category = ValueCategory::PRValue; constructed.braced_init_list = true; constructed.copy_initialization = true;
constructed.node = Node("braced-init-list"); constructed.node.token_text = "force-constructor"; constructed.node.type = result; constructed.node.category = constructed.category;
constructed.node.direct_call = aggregate_ctor; for (size_t i = 0; i < args.size(); ++i) { Conversion conv =
	convert_to(args[i], aggregate_ctor->type->parameters[i + 1]); if (!conv.viable) {
		throw runtime_error("invalid return conversion");
	} add_child(constructed.node, conv.expr.node);
} annotate_expr_node(constructed); constructed.node.direct_call = aggregate_ctor; return constructed;
} Expr Parser::convert_record_constructor_return_expression(Expr expr, TypePtr result) {
vector<Expr> args; args.push_back(expr); try {
	return make_constructor_init_expr(result, args, true); } catch (const runtime_error&) {
	Conversion conv = convert_to(expr, result); if (!conv.viable) {
		throw runtime_error("invalid return conversion");
	} return conv.expr;
} } void Parser::validate_same_record_return_expression(const Expr& expr, TypePtr result)
{ bool local_return = expr.binding != NULL && expr.binding->kind == BindingKind::Variable &&
expr.binding->owner != NULL && expr.binding->owner->kind != ScopeKind::Namespace && expr.binding->owner->kind != ScopeKind::Class; bool use_move = expr.category != ValueCategory::LValue || local_return;
try { if (use_move && !copy_move_constructor_available(result, true)) use_move = false;
if (!copy_move_constructor_available(result, use_move)) {
	throw runtime_error("invalid return conversion");
} ensure_copy_move_constructor(result, use_move); }
catch (const runtime_error& err) { TypePtr record = pa11::strip_cv(result); if (string(err.what()) == "incomplete class type" &&
record.get() != NULL && record->kind == pa11::TypeKind::Record && record->is_template_specialization) return;
throw; } } Expr Parser::convert_return_expression(Expr expr, TypePtr result)
{ if (result.get() == NULL || pa11::is_void_type(result)) return expr; if (type_is_template_dependent(result) ||
type_is_template_dependent(expr.type)) return expr; TypePtr result_record = pa11::strip_cv(result); TypePtr expr_record = expr.type.get() != NULL
? pa11::strip_cv(expression_object_type(expr.type)) : TypePtr(); if (result_record->kind == pa11::TypeKind::Record) { if (expr.braced_init_list &&
expr_record.get() != NULL && same_return_record_type(result_record, expr_record)) { if (expr.node.direct_call == NULL &&
expr.node.children.size() == 1 && same_return_record_type( result_record, pa11::strip_cv(
expression_object_type( expr.node.children[0].type)))) { Expr child;
child.valid = true; child.node = expr.node.children[0]; child.type = child.node.type; child.category = child.node.category;
child.binding = child.node.binding; child.braced_init_list = child.node.line.compare(0, 16, "braced-init-list") == 0;
return child; } return expr; }
if (expr.braced_init_list && (expr_record.get() == NULL || same_return_record_type(result_record, expr_record))) return convert_aggregate_return_expression(expr,
result, result_record); if (expr_record.get() == NULL || expr_record->kind != pa11::TypeKind::Record ||
!same_return_record_type(result_record, expr_record)) return convert_record_constructor_return_expression(expr, result); if (!pa11::same_type(result_record, expr_record)) return expr; validate_same_record_return_expression(expr, result); if (expr.binding != NULL &&
expr.binding->kind == BindingKind::Variable && expr.binding->owner != NULL && expr.binding->owner->kind != ScopeKind::Namespace && expr.binding->owner->kind != ScopeKind::Class &&
copy_move_constructor_available(result, true)) { expr.category = ValueCategory::XValue; expr.type = pa11::make_rvalue_reference(result);
expr.node = Node("id-expression xvalue " + pa11::describe_type(expr.type) + " " + expr.binding->name); expr.node.binding = expr.binding;
annotate_expr_node(expr); } return expr; }
	Conversion conv = convert_to(expr, result); if (!conv.viable) throw runtime_error("invalid return conversion"); return conv.expr;
} Node Parser::parse_jump_statement() { if (consume(KW_BREAK))
{ expect(OP_SEMICOLON); return Node("break-statement"); }
if (consume(KW_CONTINUE)) { expect(OP_SEMICOLON); return Node("continue-statement");
} if (consume(KW_GOTO)) { string label = consume_identifier();
expect(OP_SEMICOLON); return Node("goto-statement " + label); } expect(KW_RETURN);
Node node("return-statement"); if (!at(OP_SEMICOLON)) { Binding* active_function = active_functions_.empty() ? NULL : active_functions_.back();
Expr expr = at(OP_LBRACE) ? parse_braced_init_list() : parse_expression();
TypePtr return_type = active_function != NULL &&
auto_return_functions_.count(active_function) != 0 ? deduce_auto_return_type(active_function, expr) : current_return_type(); expr = convert_return_expression(expr, return_type);
add_child(node, expr.node); } expect(OP_SEMICOLON); return node;
} Node Parser::parse_labeled_statement() { if (consume(KW_CASE))
{ Node node("case-statement"); add_child(node, parse_expression().node); expect(OP_COLON);
add_child(node, parse_block_item()); return node; } if (consume(KW_DEFAULT))
{ Node node("default-statement"); expect(OP_COLON); add_child(node, parse_block_item());
return node; } string label = consume_identifier(); expect(OP_COLON);
Node node("labeled-statement " + label); add_child(node, parse_block_item()); return node; }
Node Parser::parse_expression_statement() { Node node("expression-statement"); if (!at(OP_SEMICOLON))
add_child(node, parse_expression().node); expect(OP_SEMICOLON); return node; }
Node Parser::parse_condition(TypePtr target) { Node node("condition"); bool forced_declaration_condition = at(KW_AUTO); if (starts_declaration())
{ size_t save = pos_; try {
DeclSpecs specs = parse_decl_specifier_seq(false); TypePtr base = type_from_decl_specs(specs); Declarator declarator = parse_declarator(false); if (consume(OP_ASS))
{ Expr init = parse_expression(); Node wrapper("condition-declaration"); declare_one(specs, base, declarator, &init, false, wrapper);
if (!wrapper.children.empty() && wrapper.children[0].binding != NULL && target.get() != NULL && pa11::strip_cv(expression_object_type(
wrapper.children[0].binding->type))->kind == pa11::TypeKind::Record) { Binding* binding = wrapper.children[0].binding;
Expr ref; ref.valid = true; ref.binding = binding; ref.type = binding->type;
ref.category = ValueCategory::LValue; ref.node = Node("id-expression lvalue " + pa11::describe_type(binding->type) + " " + binding->name);
annotate_expr_node(ref); ++explicit_conversion_context_; Conversion conv; try
{ conv = convert_to(ref, target); } catch (...)
{ --explicit_conversion_context_; throw; }
--explicit_conversion_context_; if (conv.viable) add_child(wrapper, conv.expr.node); }
	if (!wrapper.children.empty()) add_child(node, wrapper); return node; }
	} catch (const exception& err) {
		if (forced_declaration_condition)
		throw;
	}
pos_ = save; } Expr expr = parse_expression(); if (target.get() != NULL &&
pa11::strip_cv(expression_object_type(expr.type))->kind == pa11::TypeKind::Record) { ++explicit_conversion_context_;
Conversion conv; try { conv = convert_to(expr, target);
} catch (...) { --explicit_conversion_context_;
throw; } --explicit_conversion_context_; if (conv.viable)
expr = conv.expr; } add_child(node, expr.node); return node;
}

}  // namespace internal
}  // namespace pa12
