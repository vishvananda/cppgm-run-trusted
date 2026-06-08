#include "pa12_internal.h"
#include <stdexcept>
using namespace std; namespace pa12 { namespace internal { static void mark_empty_destructor(Binding* function, const Node& fn);
static bool same_return_record_type(TypePtr left, TypePtr right) { TypePtr l = pa11::strip_cv(left); TypePtr r = pa11::strip_cv(right);
if (pa11::same_type(l, r)) return true; return l->kind == pa11::TypeKind::Record && r->kind == pa11::TypeKind::Record &&
l->is_template_specialization && r->is_template_specialization && l->name == r->name; }
static Expr expr_from_node(const Node& node) { Expr out; out.valid = true;
out.node = node; out.type = node.type; out.category = node.category; out.binding = node.binding;
out.overloads = node.overloads; out.explicit_template_arguments = node.explicit_template_arguments;
out.has_constant_value = node.has_constant_value; out.constant_value = node.constant_value; out.dependent_value_name = node.dependent_value_name; out.dependent_value_owner_template_name =
node.dependent_value_owner_template_name; out.dependent_value_member_name = node.dependent_value_member_name; out.dependent_value_negated = node.dependent_value_negated; out.dependent_value_owner_template_arguments =
node.dependent_value_owner_template_arguments; out.braced_init_list = node.line.compare(0, 16, "braced-init-list") == 0; return out;
} TypePtr Parser::deduce_auto_return_type(Binding* function, const Expr& expr) { map<Binding*, TypePtr>::const_iterator found =
auto_return_patterns_.find(function); if (found == auto_return_patterns_.end()) throw runtime_error("auto return pattern missing"); TypePtr pattern = found->second;
TypePtr bare = pa11::strip_cv(pattern); TypePtr deduced; if (bare->kind == pa11::TypeKind::LValueReference) deduced = pa11::make_lvalue_reference(
pa11::make_cv(expression_object_type(expr.type), pattern->base->kind == pa11::TypeKind::Cv ? pattern->base->cv : pa11::CV_NONE)); else if (bare->kind == pa11::TypeKind::RValueReference)
{ TypePtr object = expression_object_type(expr.type); if (expr.category == ValueCategory::LValue) deduced = pa11::make_lvalue_reference(object);
else deduced = pa11::make_rvalue_reference(object); } else
deduced = lvalue_to_rvalue_type(expr.type); map<Binding*, TypePtr>::const_iterator previous = auto_return_deduced_.find(function); if (previous == auto_return_deduced_.end())
auto_return_deduced_[function] = deduced; else if (!pa11::same_type(previous->second, deduced)) throw runtime_error("inconsistent auto return type"); return deduced;
} void Parser::parse_function_body(Binding* function, const Declarator& declarator, Node& function_node)
{ vector<ParameterInfo> parameters; const Suffix* suffix = declarator_function_suffix(declarator); if (suffix != NULL)
parameters = suffix->parameters; parse_function_body_from_parameters(function, parameters, function_node); } void Parser::parse_function_body_from_parameters(
Binding* function, const vector<ParameterInfo>& parameters, Node& function_node) {
if (function_node.children.empty()) throw runtime_error("missing function node"); Node& fn = function_node.children.back(); Scope* lexical_parent =
function->owner != NULL && function->owner->kind == ScopeKind::Class ? function->owner : current_scope(); Scope* function_scope = pa11::create_child_scope(lexical_parent, ScopeKind::Function, function->name);
if (function->owner != NULL && function->owner->kind == ScopeKind::Class && !function->is_static_member) {
if (function->type->parameters.empty()) throw runtime_error("member function missing this parameter"); TypePtr this_type = function->type->parameters[0]; Binding* this_binding =
pa11::add_binding(function_scope, BindingKind::Parameter, "this", this_type);
Node this_node("parameter this " + pa11::describe_type(this_type)); this_node.binding = this_binding; this_node.type = this_type; add_child(fn, this_node);
} map<Binding*, vector<string> >::const_iterator saved_names = function_parameter_names_.find(function); size_t saved_name_offset =
function->owner != NULL && function->owner->kind == ScopeKind::Class && !function->is_static_member ? 1 : 0; map<string, vector<Binding*> > parameter_packs;
for (size_t i = 0; i < parameters.size(); ++i) { if (!parameters[i].pack_expression_name.empty() && !parameters[i].pack_name.empty())
{ TemplateArgument subst; if (find_template_value_substitution(parameters[i].pack_name, subst) &&
subst.kind == TemplateArgumentKind::Pack && subst.pack.empty()) { parameter_packs[parameters[i].pack_expression_name];
continue; } } TypePtr parameter_type = parameters[i].type.get() != NULL
? substitute_template_type(parameters[i].type) : TypePtr(); if (parameter_type.get() == NULL) { if (!parameters[i].pack_expression_name.empty())
parameter_packs[parameters[i].pack_expression_name]; continue; } string name = parameters[i].name;
string node_name = name; size_t saved_name_index = saved_name_offset + i; bool force_saved_name = override_function_parameter_name_bindings_.count(function) != 0;
if ((force_saved_name || node_name.empty()) && saved_names != function_parameter_names_.end() && saved_name_index < saved_names->second.size() && !saved_names->second[saved_name_index].empty() &&
!(function->is_static_member && saved_name_index == 0 && saved_names->second[saved_name_index] == "this")) node_name = saved_names->second[saved_name_index];
string binding_name = !name.empty() ? name : node_name; if (!binding_name.empty()) { Binding* param =
pa11::add_binding(function_scope, BindingKind::Parameter, binding_name, parameter_type);
if (!parameters[i].pack_expression_name.empty()) parameter_packs[parameters[i].pack_expression_name] .push_back(param); Node param_node("parameter " + node_name + " " +
pa11::describe_type(parameter_type)); param_node.binding = param; param_node.type = parameter_type; add_child(fn, param_node);
} else { Node param_node("parameter " + node_name + " " +
pa11::describe_type(parameter_type)); param_node.type = parameter_type; add_child(fn, param_node); }
} scopes_.push_back(function_scope); bool auto_return = auto_return_functions_.count(function) != 0; function_returns_.push_back(auto_return ? TypePtr() : function->type->base);
active_functions_.push_back(function); function_parameter_pack_substitutions_.push_back(parameter_packs); add_child(fn, parse_compound_statement()); if (auto_return)
{ map<Binding*, TypePtr>::const_iterator deduced = auto_return_deduced_.find(function); if (deduced == auto_return_deduced_.end())
function->type->base = pa11::make_fundamental(FT_VOID); else function->type->base = deduced->second; fn.type = function->type;
} remember_function_body(function, fn); function_parameter_pack_substitutions_.pop_back(); active_functions_.pop_back();
function_returns_.pop_back(); scopes_.pop_back(); } void Parser::remember_function_body(Binding* function, const Node& function_node)
{ if (function != NULL) function_bodies_[function] = function_node; }
void Parser::enqueue_pending_member_body(Scope* class_scope, PendingFunctionBody pending) { pending.scopes = scopes_;
pending.friend_class_scopes = active_friend_class_scopes_; pending.type_substitutions = template_type_substitutions_; pending.value_substitutions = template_value_substitutions_; pending.pack_substitutions = template_type_parameter_packs_;
pending_member_bodies_[class_scope].push_back(pending); } void Parser::enqueue_pending_function_body(PendingFunctionBody pending) {
pending.scopes = scopes_; pending.friend_class_scopes = active_friend_class_scopes_; pending.type_substitutions = template_type_substitutions_; pending.value_substitutions = template_value_substitutions_;
pending.pack_substitutions = template_type_parameter_packs_; pending_function_bodies_[pending.function] = pending; } void Parser::push_pending_owner_template_substitutions(
const PendingFunctionBody& pending) { TypePtr owner_record = pending.function != NULL && pending.function->owner != NULL
? pa11::record_type_for_scope(pending.function->owner) : TypePtr(); owner_record = owner_record.get() != NULL ? pa11::strip_cv(owner_record) : TypePtr();
map<const void*, TemplateDeclaration*>::iterator owner_template = owner_record.get() != NULL ? record_template_declarations_.find(owner_record.get()) : record_template_declarations_.end();
map<const void*, vector<TemplateArgument> >::iterator owner_args = owner_record.get() != NULL ? record_template_arguments_.find(owner_record.get()) : record_template_arguments_.end();
if (owner_template == record_template_declarations_.end() || owner_args == record_template_arguments_.end()) return; map<string, TypePtr> subst;
map<string, TemplateArgument> value_subst; set<string> pack_subst; for (size_t i = 0; i < owner_args->second.size() &&
i < owner_template->second->parameters.size(); ++i) { const TemplateParameterInfo& parameter =
owner_template->second->parameters[i]; if (parameter.name.empty()) continue; if (parameter.kind == TemplateParameterKind::Type)
{ if (parameter.is_pack) { subst[parameter.name] =
pa11::make_template_parameter_type(parameter.name); value_subst[parameter.name] = owner_args->second[i]; pack_subst.insert(parameter.name); }
else subst[parameter.name] = owner_args->second[i].type; } else
value_subst[parameter.name] = owner_args->second[i]; } template_type_substitutions_.push_back(subst); template_value_substitutions_.push_back(value_subst);
template_type_parameter_packs_.push_back(pack_subst); } void Parser::push_pending_function_template_substitutions( const PendingFunctionBody& pending)
{ map<Binding*, TemplateDeclaration*>::iterator function_template = pending.function != NULL ? function_template_placeholders_.find(pending.function)
: function_template_placeholders_.end(); map<Binding*, vector<TemplateArgument> >::iterator function_args = pending.function != NULL ? function_template_specialization_arguments_.find(pending.function)
: function_template_specialization_arguments_.end(); if (function_template == function_template_placeholders_.end() || function_args == function_template_specialization_arguments_.end()) return;
TemplateDeclaration* declaration = function_template->second; map<string, TypePtr> subst; map<string, TemplateArgument> value_subst; set<string> pack_subst;
for (size_t i = 0; i < function_args->second.size() && i < declaration->parameters.size(); ++i)
{ const TemplateParameterInfo& parameter = declaration->parameters[i]; if (parameter.name.empty()) continue;
if (parameter.kind == TemplateParameterKind::Type) { if (parameter.is_pack) {
subst[parameter.name] = pa11::make_template_parameter_type(parameter.name); value_subst[parameter.name] = function_args->second[i]; pack_subst.insert(parameter.name);
} else subst[parameter.name] = function_args->second[i].type; }
else value_subst[parameter.name] = function_args->second[i]; } template_type_substitutions_.push_back(subst);
template_value_substitutions_.push_back(value_subst); template_type_parameter_packs_.push_back(pack_subst); } void Parser::parse_pending_member_body_now(const PendingFunctionBody& pending)
{ if (pending.prebuilt_node) { if (pending.function != NULL &&
pending.node.line.compare(0, 19, "function-definition") == 0) pending.function->is_inline_definition = true; extra_lowir_nodes_.push_back(pending.node); if (pending.node.line.compare(0, 19, "function-definition") == 0)
remember_function_body(pending.function, pending.node); return; } size_t saved_pos = pos_;
vector<Scope*> saved_scopes = scopes_; vector<Scope*> saved_friend_class_scopes = active_friend_class_scopes_; vector<map<string, TypePtr> > saved_type_substitutions = template_type_substitutions_;
vector<map<string, TemplateArgument> > saved_value_substitutions = template_value_substitutions_; vector<set<string> > saved_pack_substitutions = template_type_parameter_packs_;
pos_ = pending.body_pos; scopes_ = pending.scopes; active_friend_class_scopes_ = pending.friend_class_scopes; template_type_substitutions_ = pending.type_substitutions;
template_value_substitutions_ = pending.value_substitutions; template_type_parameter_packs_ = pending.pack_substitutions; push_pending_owner_template_substitutions(pending); push_pending_function_template_substitutions(pending);
Node wrapper; add_child(wrapper, pending.node); if (pending.function != NULL && pending.node.line.compare(0, 19, "function-definition") == 0)
pending.function->is_inline_definition = true; try { if (pending.constructor_body)
parse_constructor_body_from_parameters(pending.function, pending.class_type, pending.parameters, wrapper);
else parse_function_body_from_parameters(pending.function, pending.parameters, wrapper);
} catch (...) { template_value_substitutions_ = saved_value_substitutions;
template_type_substitutions_ = saved_type_substitutions; template_type_parameter_packs_ = saved_pack_substitutions; active_friend_class_scopes_ = saved_friend_class_scopes; scopes_ = saved_scopes;
pos_ = saved_pos; throw; } if (!wrapper.children.empty())
mark_empty_destructor(pending.function, wrapper.children.back()); if (!wrapper.children.empty()) extra_lowir_nodes_.push_back(wrapper.children.back()); template_value_substitutions_ = saved_value_substitutions;
template_type_substitutions_ = saved_type_substitutions; template_type_parameter_packs_ = saved_pack_substitutions; active_friend_class_scopes_ = saved_friend_class_scopes; scopes_ = saved_scopes;
pos_ = saved_pos; } bool Parser::parse_pending_function_body(Binding* function) {
if (function == NULL) return false; if (function_template_candidate_instantiation_depth_ != 0) return false;
map<Binding*, PendingFunctionBody>::iterator found = pending_function_bodies_.find(function); if (found == pending_function_bodies_.end()) return false;
PendingFunctionBody body = found->second; pending_function_bodies_.erase(found); parse_pending_member_body_now(body); return true;
} bool Parser::parse_pending_member_body(Binding* function) { if (function == NULL)
return false; if (function_template_candidate_instantiation_depth_ != 0) return false; for (map<Scope*, vector<PendingFunctionBody> >::iterator it =
pending_member_bodies_.begin(); it != pending_member_bodies_.end(); ++it) {
vector<PendingFunctionBody>& pending = it->second; for (size_t i = 0; i < pending.size(); ++i) { if (pending[i].function != function)
continue; PendingFunctionBody body = pending[i]; pending.erase(pending.begin() + i); if (pending.empty())
pending_member_bodies_.erase(it); parse_pending_member_body_now(body); return true; }
} return false; } void Parser::ensure_function_body_extra_node(Binding* function)
{ if (function == NULL) return; if (function_bodies_.find(function) == function_bodies_.end())
{ map<Binding*, TemplateDeclaration*>::iterator template_it = function_template_placeholders_.find(function); map<Binding*, vector<TemplateArgument> >::iterator args_it =
function_template_specialization_arguments_.find(function); if (template_it != function_template_placeholders_.end() && args_it != function_template_specialization_arguments_.end()) {
TemplateDeclaration* declaration = template_it->second; if (!declaration->has_definition && declaration->placeholder != NULL) {
map<Binding*, TemplateDeclaration*>::iterator placeholder = function_template_placeholders_.find( declaration->placeholder); if (placeholder != function_template_placeholders_.end() &&
placeholder->second->has_definition) declaration = placeholder->second; } if (declaration->has_definition)
{ function_template_placeholders_[function] = declaration; vector<TemplateArgument> selected_args = args_it->second; Binding* instantiated =
instantiate_function_template(declaration, selected_args); if (instantiated != NULL && instantiated != function) {
function->aliased_binding = instantiated; function = instantiated; } }
} } for (size_t i = 0; i < extra_lowir_nodes_.size(); ++i) if (extra_lowir_nodes_[i].binding == function)
return; map<Binding*, Node>::const_iterator found = function_bodies_.find(function); if (found == function_bodies_.end() &&
function->aliased_binding != NULL) found = function_bodies_.find(function->aliased_binding); if (found != function_bodies_.end()) extra_lowir_nodes_.push_back(found->second);
} static bool function_body_empty(const Node& fn) { if (fn.children.empty())
return true; const Node& body = fn.children.back(); return body.line == "compound-statement" && body.children.empty(); }
static void mark_empty_destructor(Binding* function, const Node& fn) { if (function == NULL || function->name.empty() ||
function->name[0] != '~' || function->is_virtual || !function_body_empty(fn)) return;
function->is_noop_destructor = true; Scope* owner = function->owner; if (owner == NULL) return;
map<string, vector<Binding*> >::iterator found = owner->members.find(function->name); if (found == owner->members.end()) return;
for (size_t i = 0; i < found->second.size(); ++i) { Binding* candidate = found->second[i]; if (candidate->kind == BindingKind::Function &&
pa11::same_type(candidate->type, function->type)) candidate->is_noop_destructor = true; } }
void Parser::parse_pending_member_bodies(Scope* class_scope) { map<Scope*, vector<PendingFunctionBody> >::iterator found = pending_member_bodies_.find(class_scope);
if (found == pending_member_bodies_.end()) return; if (!active_class_instantiations_.empty() && !validating_template_definition_)
return; vector<PendingFunctionBody> pending = found->second; pending_member_bodies_.erase(found); vector<PendingFunctionBody> still_pending;
for (size_t i = 0; i < pending.size(); ++i) { if (pending[i].function != NULL && function_template_placeholders_.find(pending[i].function) !=
function_template_placeholders_.end()) { still_pending.push_back(pending[i]); continue;
} parse_pending_member_body_now(pending[i]); } if (!still_pending.empty())
pending_member_bodies_[class_scope] = still_pending; } void Parser::parse_deferred_nested_member_bodies(Scope* class_scope) {
map<Scope*, vector<Scope*> >::iterator found = deferred_nested_member_body_scopes_.find(class_scope); if (found == deferred_nested_member_body_scopes_.end()) return;
vector<Scope*> nested = found->second; deferred_nested_member_body_scopes_.erase(found); for (size_t i = 0; i < nested.size(); ++i) {
parse_pending_member_bodies(nested[i]); parse_deferred_nested_member_bodies(nested[i]); } }
Node Parser::parse_compound_statement() { expect(OP_LBRACE); Node node("compound-statement");
Scope* block = pa11::create_child_scope(current_scope(), ScopeKind::Block, ""); scopes_.push_back(block); while (!at(OP_RBRACE)) {
Node item = parse_block_item(); if (!item.line.empty()) add_child(node, item); }
scopes_.pop_back(); expect(OP_RBRACE); return node; }
Node Parser::parse_block_item() { if (at(KW_USING)) {
Node node("compound-statement-placeholder"); parse_using_family(node); if (node.children.empty()) return Node();
return node.children[0]; } if (at(KW_NAMESPACE)) {
Node node; parse_namespace_or_alias(node); return Node(); }
if (at(KW_STATIC_ASSERT)) { parse_static_assert_declaration(); return Node();
} if (starts_declaration()) { size_t save = pos_;
bool definitely_declaration = at_simple_builtin() || at_simple_cv() || at(KW_TYPEDEF) ||
at(KW_CONSTEXPR) || at(KW_EXTERN) || at(KW_STATIC) || at(KW_DECLTYPE) ||
at(KW_TYPENAME) || starts_class_key() || at(KW_ENUM) || at(KW_STATIC_ASSERT) ||
(at_identifier() && pos_ + 1 < tokens_.size() && tokens_[pos_ + 1].kind == posttoken::TokenKind::Identifier); if (!definitely_declaration && (at_identifier() || at(OP_COLON2)))
{ size_t type_save = pos_; TypePtr type_probe; if (try_parse_type_name(type_probe) &&
(starts_declarator() || at_identifier())) { bool parenthesized_this_argument = at(OP_LPAREN) &&
pos_ + 2 < tokens_.size() && tokens_[pos_ + 1].kind == posttoken::TokenKind::Simple && (tokens_[pos_ + 1].type == OP_STAR || tokens_[pos_ + 1].type == OP_AMP) &&
tokens_[pos_ + 2].kind == posttoken::TokenKind::Simple && tokens_[pos_ + 2].type == KW_THIS; bool empty_functional_temporary = at(OP_LPAREN) &&
pos_ + 1 < tokens_.size() && tokens_[pos_ + 1].kind == posttoken::TokenKind::Simple && tokens_[pos_ + 1].type == OP_RPAREN; if (!parenthesized_this_argument &&
!empty_functional_temporary) definitely_declaration = true; } pos_ = type_save;
} try { Node node;
parse_simple_or_function_declaration(node, true); if (!node.children.empty()) return node.children[0]; return Node();
} catch (const exception&) { pos_ = save;
if (definitely_declaration) throw; } }
return parse_statement(); } Node Parser::parse_statement() {
if (at(OP_LBRACE)) return parse_compound_statement(); if (at(KW_IF)) return parse_if_statement();
if (at(KW_SWITCH)) return parse_switch_statement(); if (at(KW_WHILE)) return parse_while_statement();
if (at(KW_DO)) return parse_do_statement(); if (at(KW_FOR)) return parse_for_statement();
if (at(KW_TRY)) return parse_try_statement(); if (at(KW_RETURN) || at(KW_BREAK) || at(KW_CONTINUE) || at(KW_GOTO)) return parse_jump_statement();
if ((at_identifier() && lookahead(OP_COLON, 1)) || at(KW_CASE) || at(KW_DEFAULT)) return parse_labeled_statement(); return parse_expression_statement();
} Node Parser::parse_if_statement() { expect(KW_IF);
Node node("if-statement"); expect(OP_LPAREN); add_child(node, parse_condition(pa11::make_fundamental(FT_BOOL))); expect(OP_RPAREN);
Node then_node("then"); add_child(then_node, parse_statement()); add_child(node, then_node); if (consume(KW_ELSE))
{ Node else_node("else"); add_child(else_node, parse_statement()); add_child(node, else_node);
} return node; } Node Parser::parse_switch_statement()
{ expect(KW_SWITCH); Node node("switch-statement"); expect(OP_LPAREN);
add_child(node, parse_condition(pa11::make_fundamental(FT_INT))); expect(OP_RPAREN); add_child(node, parse_statement()); return node;
} Node Parser::parse_while_statement() { expect(KW_WHILE);
Node node("while-statement"); expect(OP_LPAREN); add_child(node, parse_condition(pa11::make_fundamental(FT_BOOL))); expect(OP_RPAREN);
add_child(node, parse_statement()); return node; } Node Parser::parse_do_statement()
{ expect(KW_DO); Node node("do-statement"); add_child(node, parse_statement());
expect(KW_WHILE); expect(OP_LPAREN); Node cond("condition"); Expr do_cond = parse_expression();
if (pa11::strip_cv(expression_object_type(do_cond.type))->kind == pa11::TypeKind::Record) { Conversion conv =
convert_to(do_cond, pa11::make_fundamental(FT_BOOL)); if (conv.viable) do_cond = conv.expr; }
add_child(cond, do_cond.node); add_child(node, cond); expect(OP_RPAREN); expect(OP_SEMICOLON);
return node; } Node Parser::parse_for_statement() {
expect(KW_FOR); expect(OP_LPAREN); if (starts_declaration()) {
size_t save = pos_; try { return parse_range_for_statement();
} catch (const runtime_error& err) { pos_ = save;
if (string(err.what()) != "not range-for") throw; } }
Node node("for-statement"); Node init("for-init-statement"); if (starts_declaration()) add_child(init, parse_block_item());
else { if (!at(OP_SEMICOLON)) add_child(init, parse_expression().node);
expect(OP_SEMICOLON); } add_child(node, init); if (!at(OP_SEMICOLON))
add_child(node, parse_condition(pa11::make_fundamental(FT_BOOL))); expect(OP_SEMICOLON); if (!at(OP_RPAREN)) {
Node iter("iteration"); add_child(iter, parse_expression().node); add_child(node, iter); }
expect(OP_RPAREN); add_child(node, parse_statement()); return node; }
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
return node; } Node Parser::parse_try_statement() {
expect(KW_TRY); Node node("try-statement"); Node try_block("try-block"); add_child(try_block, parse_compound_statement());
add_child(node, try_block); do { expect(KW_CATCH);
expect(OP_LPAREN); Node catch_node("catch-clause"); string catch_name; Binding* catch_binding = NULL; if (consume(OP_DOTS)) catch_node.token_text = "catch-all";
else { TypePtr catch_type = parse_type_id(); if (at_identifier()) catch_name = consume_identifier(); catch_node.type = catch_type;
catch_node.line += " " + pa11::describe_type(catch_type); } expect(OP_RPAREN); expect(OP_LBRACE); Node body("compound-statement");
Scope* block = pa11::create_child_scope(current_scope(), ScopeKind::Block, ""); scopes_.push_back(block);
if (!catch_name.empty()) { catch_binding = add_value(block, BindingKind::Variable, catch_name, catch_node.type); catch_node.binding = catch_binding; }
while (!at(OP_RBRACE)) { Node item = parse_block_item(); if (!item.line.empty()) add_child(body, item); }
scopes_.pop_back(); expect(OP_RBRACE); add_child(catch_node, body);
add_child(node, catch_node); } while (at(KW_CATCH)); return node;
} Expr Parser::convert_aggregate_return_expression(Expr expr, TypePtr result, TypePtr result_record)
{ expr.type = result; expr.node.type = result; ensure_aggregate_constructors_for_init(result, expr.node);
vector<Expr> args; for (size_t i = 0; i < expr.node.children.size(); ++i) { Expr arg;
arg.valid = true; arg.node = expr.node.children[i]; arg.type = arg.node.type; arg.category = arg.node.category;
arg.binding = arg.node.binding; arg.has_constant_value = arg.node.has_constant_value; arg.constant_value = arg.node.constant_value; arg.null_pointer_constant =
arg.has_constant_value && arg.constant_value == 0 && pa11::is_integral_or_bool_type(arg.type); args.push_back(arg);
} complete_aggregate_constructor_args(result_record, args); Binding* aggregate_ctor = ensure_aggregate_constructor(result_record, args.size());
if (aggregate_ctor == NULL) { try {
return make_constructor_init_expr(result, args, true); } catch (const runtime_error&) {
Conversion conv = convert_to(expr, result); if (!conv.viable) throw runtime_error("invalid return conversion"); return conv.expr;
} } Expr constructed; constructed.valid = true;
constructed.type = result; constructed.category = ValueCategory::PRValue; constructed.braced_init_list = true; constructed.copy_initialization = true;
constructed.node = Node("braced-init-list"); constructed.node.token_text = "force-constructor"; constructed.node.type = result; constructed.node.category = constructed.category;
constructed.node.direct_call = aggregate_ctor; for (size_t i = 0; i < args.size(); ++i) { Conversion conv =
convert_to(args[i], aggregate_ctor->type->parameters[i + 1]); if (!conv.viable) throw runtime_error("invalid return conversion"); add_child(constructed.node, conv.expr.node);
} annotate_expr_node(constructed); constructed.node.direct_call = aggregate_ctor; return constructed;
} Expr Parser::convert_record_constructor_return_expression(Expr expr, TypePtr result) {
vector<Expr> args; args.push_back(expr); try {
return make_constructor_init_expr(result, args, true); } catch (const runtime_error&) {
Conversion conv = convert_to(expr, result); if (!conv.viable) throw runtime_error("invalid return conversion"); return conv.expr;
} } void Parser::validate_same_record_return_expression(const Expr& expr, TypePtr result)
{ bool local_return = expr.binding != NULL && expr.binding->kind == BindingKind::Variable &&
expr.binding->owner != NULL && expr.binding->owner->kind != ScopeKind::Namespace && expr.binding->owner->kind != ScopeKind::Class; bool use_move = expr.category != ValueCategory::LValue || local_return;
try { if (use_move && !copy_move_constructor_available(result, true)) use_move = false;
if (!copy_move_constructor_available(result, use_move)) throw runtime_error("invalid return conversion"); ensure_copy_move_constructor(result, use_move); }
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
!same_return_record_type(result_record, expr_record)) return convert_record_constructor_return_expression(expr, result); validate_same_record_return_expression(expr, result); if (expr.binding != NULL &&
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
Node node("return-statement"); if (!at(OP_SEMICOLON)) { Expr expr = at(OP_LBRACE) ? parse_braced_init_list() : parse_expression();
Binding* active_function = active_functions_.empty() ? NULL : active_functions_.back(); TypePtr return_type = active_function != NULL &&
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
Node Parser::parse_condition(TypePtr target) { Node node("condition"); if (starts_declaration())
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
} catch (const exception&) { }
pos_ = save; } Expr expr = parse_expression(); if (target.get() != NULL &&
pa11::strip_cv(expression_object_type(expr.type))->kind == pa11::TypeKind::Record) { ++explicit_conversion_context_;
Conversion conv; try { conv = convert_to(expr, target);
} catch (...) { --explicit_conversion_context_;
throw; } --explicit_conversion_context_; if (conv.viable)
expr = conv.expr; } add_child(node, expr.node); return node;
}
}  // namespace internal
}  // namespace pa12
