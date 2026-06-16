#include "pa12_expr_parser_support.h"
#include "pa12_templates_function_abi_internal.h"
#include "pa12_templates_function_support.h"
#include <algorithm>
#include <cctype>
#include <stdexcept>
using namespace std; namespace pa12 { namespace internal { namespace {
struct LambdaCapture { string name; bool by_reference;
bool is_this; Binding* binding; Binding* field; TypePtr field_type;
Node initializer; LambdaCapture() : by_reference(false), is_this(false), binding(NULL), field(NULL) {
} }; bool node_starts_with(const Node& node, const string& prefix) {
return node.line.compare(0, prefix.size(), prefix) == 0; } void rewrite_bindings(Node& node, const map<Binding*, Binding*>& replacements) {
map<Binding*, Binding*>::const_iterator binding = replacements.find(node.binding); if (binding != replacements.end()) node.binding = binding->second;
for (size_t i = 0; i < node.children.size(); ++i) rewrite_bindings(node.children[i], replacements); } string lambda_abi_fundamental(EFundamentalType type)
{ switch (type) { case FT_VOID: return "v";
case FT_BOOL: return "b"; case FT_CHAR: return "c"; case FT_SIGNED_CHAR: return "a"; case FT_UNSIGNED_CHAR: return "h";
case FT_SHORT_INT: return "s"; case FT_UNSIGNED_SHORT_INT: return "t"; case FT_INT: return "i"; case FT_UNSIGNED_INT: return "j";
case FT_LONG_INT: return "l"; case FT_UNSIGNED_LONG_INT: return "m"; case FT_LONG_LONG_INT: return "x"; case FT_UNSIGNED_LONG_LONG_INT: return "y"; case FT_INT128: return "n"; case FT_UNSIGNED_INT128: return "o";
case FT_FLOAT: return "f"; case FT_DOUBLE: return "d"; default: return "i"; }
} string lambda_abi_source_name(const string& name) { return to_string(name.size()) + name;
} string lambda_abi_type(TypePtr type) { if (type.get() == NULL)
return "v"; try { return abi_type(type, map<string, size_t>(), NULL); } catch (const exception&) {}
if (type->kind == pa11::TypeKind::Cv) { string out;
if ((type->cv & pa11::CV_CONST) != 0) out += "K"; if ((type->cv & pa11::CV_VOLATILE) != 0) out += "V";
return out + lambda_abi_type(type->base); } if (type->kind == pa11::TypeKind::LValueReference) return "R" + lambda_abi_type(type->base);
if (type->kind == pa11::TypeKind::RValueReference) return "O" + lambda_abi_type(type->base); if (type->kind == pa11::TypeKind::Pointer) return "P" + lambda_abi_type(type->base);
if (type->kind == pa11::TypeKind::Array) return "A" + (type->unknown_bound ? string("_") : to_string(type->bound) + "_") + lambda_abi_type(type->base);
if (type->kind == pa11::TypeKind::Fundamental) return lambda_abi_fundamental(type->fundamental); if (type->kind == pa11::TypeKind::Record || type->kind == pa11::TypeKind::Enum)
{ string name = type->name; size_t pos = name.rfind("::"); if (pos != string::npos)
name = name.substr(pos + 2); return lambda_abi_source_name(name); } return "i";
} string lambda_abi_base36(size_t value) { static const char digits[] = "0123456789ABCDEFGHIJKLMNOPQRSTUVWXYZ"; string out;
do { out.insert(out.begin(), digits[value % 36]); value /= 36; } while (value != 0); return out;
} string lambda_abi_substitution_code(size_t index) { return index == 0 ? string("S_") : "S" + lambda_abi_base36(index - 1) + "_";
} size_t lambda_abi_find_substitution(const vector<string>& substitutions, const string& encoded)
{ for (size_t i = 0; i < substitutions.size(); ++i) if (substitutions[i] == encoded) return i; return static_cast<size_t>(-1);
} void lambda_abi_add_substitution(vector<string>& substitutions, const string& encoded)
{ if (encoded.empty() || lambda_abi_find_substitution(substitutions, encoded) != static_cast<size_t>(-1)) return; substitutions.push_back(encoded);
} void lambda_abi_record_type(TypePtr type, vector<string>& substitutions) { if (type.get() == NULL) return;
if (type->kind == pa11::TypeKind::Cv || type->kind == pa11::TypeKind::Pointer || type->kind == pa11::TypeKind::LValueReference || type->kind == pa11::TypeKind::RValueReference || type->kind == pa11::TypeKind::Array)
{ lambda_abi_record_type(type->base, substitutions); lambda_abi_add_substitution(substitutions, lambda_abi_type(type)); return; }
if (type->kind == pa11::TypeKind::Record || type->kind == pa11::TypeKind::Enum) lambda_abi_add_substitution(substitutions, lambda_abi_type(type));
} string lambda_abi_parameter_list(const vector<ParameterInfo>& parameters, vector<string>* substitutions = NULL, bool prefer_substitution = false) { string out;
for (size_t i = 0; i < parameters.size(); ++i) if (parameters[i].type.get() != NULL) { string encoded = lambda_abi_type(parameters[i].type); if (substitutions != NULL && prefer_substitution) { size_t found = lambda_abi_find_substitution(*substitutions, encoded); if (found != static_cast<size_t>(-1)) { out += lambda_abi_substitution_code(found); continue; } } out += encoded; if (substitutions != NULL) lambda_abi_record_type(parameters[i].type, *substitutions); } return out.empty() ? string("v") : out;
} size_t lambda_abi_context_substitution_seed(const string& encoded_context) { size_t count = 0;
for (size_t i = 0; i < encoded_context.size(); ++i) { if (!isdigit(static_cast<unsigned char>(encoded_context[i]))) continue; size_t j = i; size_t len = 0; while (j < encoded_context.size() && isdigit(static_cast<unsigned char>(encoded_context[j]))) { len = len * 10 + static_cast<size_t>(encoded_context[j] - '0'); ++j; } if (len != 0 && j + len <= encoded_context.size()) { ++count; i = j + len - 1; } } return count;
} string lambda_abi_local_source_name(size_t ordinal) { string name = "$_" + to_string(ordinal);
return to_string(name.size()) + name; } string lambda_specialization_name_part(const TemplateArgument& arg) {
string text; if (arg.kind == TemplateArgumentKind::Type && arg.type.get() != NULL) text = pa11::describe_type(pa11::strip_cv(arg.type));
else if (arg.kind == TemplateArgumentKind::Value) text = arg.value_name.empty() ? to_string(arg.value) : arg.value_name;
else if (arg.kind == TemplateArgumentKind::Pack) { for (size_t i = 0; i < arg.pack.size(); ++i) text += "__" + lambda_specialization_name_part(arg.pack[i]); return text; }
else text = "template"; string out; for (size_t i = 0; i < text.size(); ++i) { unsigned char ch = static_cast<unsigned char>(text[i]); if (isalnum(ch)) out.push_back(text[i]); else if (!out.empty() && out[out.size() - 1] != '_') out.push_back('_'); }
while (!out.empty() && out[out.size() - 1] == '_') out.resize(out.size() - 1); return out.empty() ? string("arg") : out; } bool lambda_capture_binding_candidate(Binding* binding) {
return binding != NULL && (binding->kind == BindingKind::Variable || binding->kind == BindingKind::Parameter) && binding->owner != NULL &&
(binding->owner->kind == ScopeKind::Function || binding->owner->kind == ScopeKind::Block); } bool node_is_parameter_decl(const Node& node)
{ return node.line.compare(0, 10, "parameter ") == 0; } bool node_is_variable_decl(const Node& node)
{ return node.line.compare(0, 9, "variable ") == 0; } bool scope_is_lambda_closure(Scope* scope)
{ return scope != NULL && scope->kind == ScopeKind::Class && scope->name.compare(0, 8, "__lambda") == 0;
} TypePtr this_binding_record_type(Binding* binding) { if (binding == NULL || binding->type.get() == NULL)
return TypePtr(); TypePtr object = pa11::strip_cv(binding->type); if (object.get() != NULL && (object->kind == pa11::TypeKind::LValueReference ||
object->kind == pa11::TypeKind::RValueReference)) object = pa11::strip_cv(object->base); if (object.get() != NULL && object->kind == pa11::TypeKind::Pointer) object = pa11::strip_cv(object->base);
if (object.get() == NULL || object->kind != pa11::TypeKind::Record) return TypePtr(); return object; }
Binding* find_enclosing_nonlambda_this(Scope* start) { for (Scope* scope = start; scope != NULL; scope = scope->parent) {
map<string, vector<Binding*> >::iterator it = scope->members.find("this"); if (it == scope->members.end()) continue;
for (size_t i = 0; i < it->second.size(); ++i) { TypePtr record = this_binding_record_type(it->second[i]); if (record.get() != NULL &&
record->scope != NULL && !scope_is_lambda_closure(record->scope)) return it->second[i]; }
} return NULL; } void collect_lambda_local_bindings(const Node& node, set<Binding*>& out)
{ if ((node_is_parameter_decl(node) || node_is_variable_decl(node)) && node.binding != NULL) out.insert(node.binding);
for (size_t i = 0; i < node.children.size(); ++i) collect_lambda_local_bindings(node.children[i], out); } void collect_lambda_capture_uses(const Node& node,
set<Binding*>& excluded, set<Binding*>& out) { if (!node_is_parameter_decl(node) && node_starts_with(node, "member-expression") && node.binding != NULL && node.binding->owner != NULL && scope_is_lambda_closure(node.binding->owner)) { out.insert(node.binding); return; } if (!node_is_parameter_decl(node) &&
lambda_capture_binding_candidate(node.binding) && excluded.count(node.binding) == 0) out.insert(node.binding); for (size_t i = 0; i < node.children.size(); ++i)
collect_lambda_capture_uses(node.children[i], excluded, out); } Node lambda_capture_id_node(Binding* binding) {
Node node("id-expression lvalue " + pa11::describe_type(binding->type) + " " + binding->name); node.binding = binding; node.type = binding->type;
node.category = ValueCategory::LValue; return node; } Node lambda_capture_member_node(Binding* field,
Binding* this_binding, TypePtr this_type) { Node this_node("id-expression prvalue " + pa11::describe_type(this_type) +
" this"); this_node.binding = this_binding; this_node.type = this_type; this_node.category = ValueCategory::PRValue;
Node member("member-expression lvalue " + pa11::describe_type(field->type) + " OP_ARROW:" + field->name); member.binding = field; member.type = field->type;
member.category = ValueCategory::LValue; member.has_op = true; member.op = OP_ARROW; member.token_text = field->name;
add_child(member, this_node); return member; } void rewrite_lambda_captures(Node& node,
const map<Binding*, Binding*>& fields, Binding* this_binding, TypePtr this_type) {
if (!node_is_parameter_decl(node)) { map<Binding*, Binding*>::const_iterator found = fields.find(node.binding);
if (found != fields.end()) { node = lambda_capture_member_node(found->second, this_binding,
this_type); return; } }
for (size_t i = 0; i < node.children.size(); ++i) rewrite_lambda_captures(node.children[i], fields, this_binding,
this_type); }
}  // namespace
Expr Parser::parse_primary_expression() { if (consume(KW_TRUE)) {
Expr out; out.type = pa11::make_fundamental(FT_BOOL); out.valid = true; out.constant_expression = true;
out.has_constant_value = true; out.constant_value = 1; out.node = Node("literal prvalue bool KW_TRUE:true"); out.node.token_text = "true";
annotate_expr_node(out); return out; } if (consume(KW_FALSE))
{ Expr out; out.type = pa11::make_fundamental(FT_BOOL); out.valid = true;
out.constant_expression = true; out.has_constant_value = true; out.constant_value = 0; out.node = Node("literal prvalue bool KW_FALSE:false");
out.node.token_text = "false"; annotate_expr_node(out); return out; }
if (consume(KW_NULLPTR)) { Expr out; out.type = pa11::make_fundamental(FT_NULLPTR_T);
out.valid = true; out.constant_expression = true; out.has_constant_value = true; out.constant_value = 0;
out.node = Node("literal prvalue nullptr_t KW_NULLPTR:nullptr"); out.node.token_text = "nullptr"; annotate_expr_node(out); return out;
} if (at(OP_LSQUARE)) return parse_lambda_expression(); if (consume(KW_TYPEID))
{ expect(OP_LPAREN); size_t operand_begin = pos_; TypePtr operand_type;
Node operand_node; bool parsed_type_operand = false; try {
operand_type = parse_type_id(); expect(OP_RPAREN); parsed_type_operand = true; operand_node = Node("type-id " + pa11::describe_type(operand_type));
operand_node.type = operand_type; } catch (const exception&) {
pos_ = operand_begin; } if (!parsed_type_operand) {
Expr operand = parse_expression(); expect(OP_RPAREN); operand_type = expression_object_type(operand.type); operand_node = operand.node;
} TypePtr type_info_type; Binding* std_binding = pa11::lookup_qualified(global_scope(),
"std", pa11::LOOKUP_NAMESPACE); Scope* std_scope = std_binding != NULL ? std_binding->target_scope : NULL;
Binding* type_info = std_scope != NULL ? pa11::lookup_qualified(std_scope, "type_info",
pa11::LOOKUP_TYPE) : NULL; if (type_info != NULL && type_info->type.get() != NULL) type_info_type = pa11::make_cv(type_info->type, pa11::CV_CONST);
	else throw runtime_error("typeid requires declared std::type_info"); Expr out;
	out.valid = true; out.type = type_info_type; out.category = ValueCategory::LValue; out.node = Node("typeid-expression lvalue " +
	pa11::describe_type(out.type)); out.node.type = out.type; out.node.category = out.category; out.node.token_text = pa11::describe_type(operand_type);
	out.node.is_typeid_expression = true;
	add_child(out.node, operand_node); annotate_expr_node(out); return out; }
if (consume(KW_THIS)) { Binding* binding = find_enclosing_nonlambda_this(current_scope()); if (binding == NULL)
binding = pa11::lookup_unqualified(current_scope(), "this", pa11::LOOKUP_PARAMETER);
if (binding == NULL) throw runtime_error("this outside member function"); Expr out; out.binding = binding;
out.type = binding->type; out.category = ValueCategory::LValue; out.valid = true; out.node = Node("id-expression lvalue " + pa11::describe_type(out.type) +
" this"); annotate_expr_node(out); return out; }
if (at_identifier() &&
    (current().source == "__func__" ||
     current().source == "__FUNCTION__" ||
     current().source == "__PRETTY_FUNCTION__"))
{
	string marker = current().source;
	++pos_;
	string name;
	if (!active_functions_.empty())
	{
		Binding* function = active_functions_.back();
		name = marker == "__PRETTY_FUNCTION__"
			? qualified_decl_name(function) + "()"
			: function->name;
	}
	return make_string_literal_expr(name);
}
if (at_identifier() && current().source == "__null")
{
	++pos_;
	Expr out = make_integer_literal_expr(FT_LONG_INT, 0);
	out.null_pointer_constant = true;
	return out;
}
	if (at_literal()) return parse_literal_expression(); if (consume(OP_LPAREN)) {
	if (at(OP_LBRACE)) { Node body = parse_compound_statement(); expect(OP_RPAREN); Expr out;
	out.valid = true; out.type = pa11::make_fundamental(FT_VOID); out.category = ValueCategory::PRValue;
	if (!body.children.empty() && node_starts_with(body.children.back(), "expression-statement") && !body.children.back().children.empty()) {
	const Node& result = body.children.back().children[0]; out.type = result.type; out.category = result.category; }
	out.node = Node("statement-expression " + value_category_name(out.category) + " " + pa11::describe_type(out.type));
	out.node.type = out.type; out.node.category = out.category; add_child(out.node, body); annotate_expr_node(out); return out; }
	size_t compound_save = pos_;
	try {
		TypePtr compound_type = parse_type_id();
		expect(OP_RPAREN);
		if (at(OP_LBRACE)) {
			Expr init = parse_braced_init_list();
			init.type = compound_type;
			init.category = ValueCategory::PRValue;
			init.node.type = compound_type;
			init.node.category = init.category;
			TypePtr bare = pa11::strip_cv(compound_type);
			if (bare->kind == pa11::TypeKind::Record) {
				if (!type_is_template_dependent(compound_type)) {
					complete_template_record(bare);
					ensure_aggregate_constructors_for_init(compound_type,
					                                       init.node);
					ensure_default_destructor(compound_type,
					                          !pa11::record_direct_bases(bare).empty());
				}
			}
			annotate_expr_node(init);
			return parse_postfix_suffixes(init);
		}
		pos_ = compound_save;
	}
	catch (const exception&) {
		pos_ = compound_save;
	}
	Expr inner = parse_expression(); expect(OP_RPAREN); return inner; }
{ size_t save = pos_; TemplateArgument dependent; if (try_parse_dependent_qualified_non_type_template_argument(dependent))
{ Expr out; out.valid = true; out.type = dependent.type.get() != NULL
? dependent.type : pa11::make_fundamental(FT_INT); out.category = ValueCategory::PRValue; out.constant_expression = true;
out.dependent_value_name = dependent.value_name; out.dependent_value_owner_template_name = dependent.value_owner_template_name; out.dependent_value_member_name =
dependent.value_member_name; out.dependent_value_owner_template_arguments = dependent.value_owner_template_arguments; out.dependent_value_negated = dependent.value_negated;
out.node = Node("id-expression prvalue " + pa11::describe_type(out.type) + " " + dependent.value_name); out.node.token_text = dependent.value_name;
annotate_expr_node(out); return out; } pos_ = save;
} return make_id_expr(parse_id_expression_name()); } Expr Parser::parse_lambda_expression()
{ expect(OP_LSQUARE); vector<LambdaCapture> captures; bool default_capture = false;
bool default_by_reference = false; if (!at(OP_RSQUARE)) { for (;;)
{ if (consume(OP_AMP)) { if (at(OP_RSQUARE))
{ default_capture = true; default_by_reference = true; }
else { LambdaCapture capture; capture.by_reference = true;
capture.name = consume_identifier(); capture.binding = pa11::lookup_unqualified(current_scope(), capture.name,
pa11::LOOKUP_VALUE); if (capture.binding == NULL) throw runtime_error("unknown lambda capture"); captures.push_back(capture);
} } else if (consume(OP_ASS)) {
default_capture = true; default_by_reference = false; } else if (consume(KW_THIS))
{ LambdaCapture capture; capture.name = "__this"; capture.by_reference = false;
capture.is_this = true; capture.binding = find_enclosing_nonlambda_this(current_scope()); if (capture.binding == NULL) capture.binding =
pa11::lookup_unqualified(current_scope(), "this", pa11::LOOKUP_PARAMETER); if (capture.binding == NULL)
throw runtime_error("this outside member function"); captures.push_back(capture); } else
{ LambdaCapture capture; capture.by_reference = false; capture.name = consume_identifier();
capture.binding = pa11::lookup_unqualified(current_scope(), capture.name, pa11::LOOKUP_VALUE);
if (capture.binding == NULL) throw runtime_error("unknown lambda capture"); captures.push_back(capture); }
if (!consume(OP_COMMA)) break; } }
size_t close_bracket_token = pos_ + 1; expect(OP_RSQUARE); vector<map<string, TypePtr> > lambda_save_subst = template_type_substitutions_;
vector<map<string, TemplateArgument> > lambda_save_value_subst = template_value_substitutions_;
vector<set<string> > lambda_save_pack_subst = template_type_parameter_packs_;
vector<TemplateParameterInfo> lambda_parameters;
bool lambda_template_scope = false; if (at(OP_LT)) { lambda_parameters = parse_template_parameter_clause();
map<string, TypePtr> parameter_types; map<string, TemplateArgument> parameter_values; set<string> pack_names;
for (size_t i = 0; i < lambda_parameters.size(); ++i) { const TemplateParameterInfo& parameter = lambda_parameters[i]; if (parameter.name.empty()) continue;
if (parameter.kind == TemplateParameterKind::Type) { parameter_types[parameter.name] = pa11::make_template_parameter_type(parameter.name); if (parameter.is_pack) pack_names.insert(parameter.name); }
else { TemplateArgument arg = TemplateArgument::dependent_value_arg(parameter.type.get() != NULL ? parameter.type : pa11::make_fundamental(FT_INT)); arg.value_name = parameter.name;
if (parameter.is_pack) { vector<TemplateArgument> pack; pack.push_back(arg); parameter_values[parameter.name] = TemplateArgument::pack_arg(pack); } else parameter_values[parameter.name] = arg; } }
template_type_substitutions_.push_back(parameter_types); template_value_substitutions_.push_back(parameter_values); template_type_parameter_packs_.push_back(pack_names); lambda_template_scope = true; }
Suffix suffix(SuffixKind::Function); if (at(OP_LPAREN))
suffix = parse_function_suffix(); bool mutable_lambda = consume(KW_MUTABLE); if (!at(OP_LBRACE)) throw runtime_error("lambda missing body");
size_t signature_end_token = pos_; TypePtr result = suffix.trailing_return.get() != NULL ? suffix.trailing_return : pa11::make_fundamental(FT_VOID);
vector<TypePtr> params; for (size_t i = 0; i < suffix.parameters.size(); ++i) params.push_back(suffix.parameters[i].type); TypePtr function_type =
pa11::make_function(result, params, suffix.variadic); function_type->cv = suffix.function_cv; string name = "__lambda"; if (!active_functions_.empty())
{ Binding* active = active_functions_.back(); name += "_" + qualified_decl_name(active); map<Binding*, vector<TemplateArgument> >::const_iterator spec_args = function_template_specialization_arguments_.find(active); if (spec_args != function_template_specialization_arguments_.end()) for (size_t ai = 0; ai < spec_args->second.size(); ++ai) name += "__" + lambda_specialization_name_part(spec_args->second[ai]); } name += "_t" + to_string(close_bracket_token) + "_" + to_string(signature_end_token); Binding* context_function =
active_functions_.empty() ? NULL : active_functions_.back(); size_t ordinal = lambda_counts_[context_function]++; Scope* closure_parent = current_scope(); Scope* closure_scope =
pa11::create_child_scope(closure_parent, ScopeKind::Class, name); TypePtr closure = add_record(closure_parent, name, "class", true, closure_scope); TypePtr operator_function_type = pa11::make_function(result,
params, suffix.variadic); operator_function_type->cv = mutable_lambda ? pa11::CV_NONE :
suffix.function_cv == pa11::CV_NONE ? pa11::CV_CONST : suffix.function_cv; TypePtr operator_type = make_member_function_type(closure_scope, operator_function_type);
Binding* call_op = add_function_binding(closure_scope, "operator()", operator_type,
false); call_op->language_linkage = current_language_linkage(); call_op->is_inline_definition = true; call_op->unwind_no = suffix.noexcept_decl; call_op->dynamic_exception_spec = suffix.dynamic_exception_spec; call_op->dynamic_exception_types = suffix.dynamic_exception_types;
call_op->ref_qualifier = suffix.ref_qualifier; vector<string> operator_names(1, "this"); vector<Expr> operator_defaults(1);
for (size_t i = 0; i < suffix.parameters.size(); ++i) { operator_names.push_back(suffix.parameters[i].name); operator_defaults.push_back(suffix.parameters[i].default_value); }
function_parameter_names_[call_op] = operator_names; if (lambda_template_scope) lambda_template_parameters_[call_op] = lambda_parameters;
default_arguments_[call_op] = operator_defaults; string context_abi = context_function != NULL ? (context_function->function_specialization_symbol.empty() ? abi_binding_symbol(context_function, map<string, size_t>())
: context_function->function_specialization_symbol) : string("_Z0v"); string encoded_context = context_abi.compare(0, 2, "_Z") == 0
? context_abi.substr(2) : context_abi; bool template_or_member_context = context_function != NULL &&
((context_function->owner != NULL && context_function->owner->kind == ScopeKind::Class) || !context_function->function_specialization_symbol.empty()); string closure_abi;
string params_abi = lambda_abi_parameter_list(suffix.parameters); string call_params_abi = params_abi;
if (template_or_member_context) { vector<string> lambda_substitutions(lambda_abi_context_substitution_seed(encoded_context), string()); params_abi = lambda_abi_parameter_list(suffix.parameters, &lambda_substitutions, false); call_params_abi = lambda_abi_parameter_list(suffix.parameters, &lambda_substitutions, true); string lambda_component = "Ul" + params_abi + "E"; if (ordinal != 0)
lambda_component += to_string(ordinal - 1) + "_"; closure_abi = "_ZZ" + encoded_context + "EN" + (operator_function_type->cv & pa11::CV_CONST ? "K" : "") +
lambda_component + "_clE" + call_params_abi; } else {
closure_abi = "_ZZ" + encoded_context + "EN" + (operator_function_type->cv & pa11::CV_CONST ? "K" : "") + lambda_abi_local_source_name(ordinal) +
"clE" + params_abi; } call_op->function_specialization_symbol = closure_abi; map<Binding*, Binding*> capture_fields;
vector<Node> capture_initializers; for (size_t i = 0; i < captures.size(); ++i) { LambdaCapture& capture = captures[i];
TypePtr object = capture.is_this ? capture.binding->type : expression_object_type(capture.binding->type); capture.field_type = capture.by_reference || capture.is_this
? (capture.is_this ? object : pa11::make_lvalue_reference(object)) : lvalue_to_rvalue_type(capture.binding->type);
capture.field = add_value(closure_scope, BindingKind::Variable, capture.name,
capture.field_type); capture.field->is_reference_member = capture.by_reference && !capture.is_this; capture_fields[capture.binding] = capture.field;
capture.initializer = lambda_capture_id_node(capture.binding); capture_initializers.push_back(capture.initializer); } int local_type_count_before = local_type_counter_;
if (suffix.trailing_return.get() == NULL) { auto_return_functions_.insert(call_op); auto_return_patterns_[call_op] = result;
} Node operator_wrapper; Node operator_node("function-definition " + qualified_decl_name(call_op) + " " + pa11::describe_type(operator_type));
operator_node.binding = call_op; operator_node.type = operator_type; add_child(operator_wrapper, operator_node); parse_function_body_from_parameters(call_op,
suffix.parameters, operator_wrapper); if (suffix.trailing_return.get() == NULL) {
result = call_op->type->base; auto_return_functions_.erase(call_op); auto_return_patterns_.erase(call_op); auto_return_deduced_.erase(call_op);
} Node& parsed_operator_for_captures = operator_wrapper.children.back(); if (default_capture) {
set<Binding*> excluded; collect_lambda_local_bindings(parsed_operator_for_captures, excluded); set<Binding*> used;
collect_lambda_capture_uses(parsed_operator_for_captures, excluded, used); for (set<Binding*>::const_iterator it = used.begin();
it != used.end(); ++it) { if (capture_fields.find(*it) != capture_fields.end())
continue; LambdaCapture capture; capture.binding = *it; capture.is_this = (*it)->name == "this";
capture.name = capture.is_this ? "__this" : (*it)->name; capture.by_reference = capture.is_this ? false : default_by_reference; TypePtr object = capture.is_this
? (*it)->type : expression_object_type((*it)->type); capture.field_type = capture.is_this ? object
: (default_by_reference ? pa11::make_lvalue_reference(object) : lvalue_to_rvalue_type((*it)->type)); capture.field =
add_value(closure_scope, BindingKind::Variable, capture.name, capture.field_type);
capture.field->is_reference_member = default_by_reference && !capture.is_this; capture_fields[*it] = capture.field; capture_initializers.push_back(lambda_capture_id_node(*it));
} } if (!capture_fields.empty() && !parsed_operator_for_captures.children.empty())
{ Binding* this_binding = parsed_operator_for_captures.children[0].binding; TypePtr this_type =
parsed_operator_for_captures.children[0].type; rewrite_lambda_captures(parsed_operator_for_captures, capture_fields, this_binding,
this_type); remember_function_body(call_op, parsed_operator_for_captures); } if (!lambda_template_scope) extra_lowir_nodes_.push_back(operator_wrapper.children.back());
function_type->base = result; Scope* target = nearest_namespace_scope(current_scope()); Binding* function = add_value(target, BindingKind::Function, name, function_type);
function->language_linkage = current_language_linkage(); function->is_inline_definition = true; function->is_namespace_static = true; function->unwind_no = suffix.noexcept_decl; function->dynamic_exception_spec = suffix.dynamic_exception_spec; function->dynamic_exception_types = suffix.dynamic_exception_types;
function->ref_qualifier = suffix.ref_qualifier; Node fn("function-definition " + qualified_decl_name(function) + " " + pa11::describe_type(function_type)); fn.binding = function;
fn.type = function_type; Scope* function_scope = pa11::create_child_scope(current_scope(), ScopeKind::Function, name); map<Binding*, Binding*> replacements;
vector<string> helper_names; const Node& parsed_operator = operator_wrapper.children.back(); size_t operator_param_index = 1; for (size_t i = 0; i < suffix.parameters.size(); ++i)
{ string pname = suffix.parameters[i].name; if (operator_param_index < parsed_operator.children.size() && node_starts_with(parsed_operator.children[operator_param_index],
"parameter ")) { string line = parsed_operator.children[operator_param_index].line; string text = line.substr(10);
size_t space = text.find(' '); if (pname.empty()) pname = space == string::npos ? text : text.substr(0, space);
} helper_names.push_back(pname); Binding* param_binding = NULL; if (!pname.empty())
param_binding = pa11::add_binding(function_scope, BindingKind::Parameter, pname,
params[i]); Node param("parameter " + pname + " " + pa11::describe_type(params[i])); param.binding = param_binding;
param.type = params[i]; add_child(fn, param); if (operator_param_index < parsed_operator.children.size()) {
Binding* old_binding = parsed_operator.children[operator_param_index].binding; if (old_binding != NULL && param_binding != NULL) replacements[old_binding] = param_binding;
} ++operator_param_index; } if (!parsed_operator.children.empty())
{ Node body = parsed_operator.children.back(); rewrite_bindings(body, replacements); add_child(fn, body);
} vector<Expr> helper_defaults; for (size_t i = 0; i < suffix.parameters.size(); ++i) helper_defaults.push_back(suffix.parameters[i].default_value);
function_parameter_names_[function] = helper_names; if (lambda_template_scope) lambda_template_parameters_[function] = lambda_parameters;
default_arguments_[function] = helper_defaults; remember_function_body(function, fn); if (!lambda_template_scope) extra_lowir_nodes_.push_back(fn);
lambda_closure_types_[function] = closure; lambda_call_operators_[function] = call_op; lambda_ordinals_[function] = ordinal; if (!capture_initializers.empty())
lambda_capture_initializers_[function] = capture_initializers; if (local_type_counter_ != local_type_count_before || !captures.empty() || default_capture) lambda_requires_closure_object_.insert(function);
Expr out; out.valid = true; out.binding = function; out.type = function->type;
out.category = ValueCategory::LValue; out.node = Node("id-expression lvalue " + pa11::describe_type(function->type) + " " + name); out.node.binding = function;
annotate_expr_node(out); if (lambda_template_scope) { template_type_substitutions_ = lambda_save_subst; template_value_substitutions_ = lambda_save_value_subst; template_type_parameter_packs_ = lambda_save_pack_subst; } if (!captures.empty() || default_capture) return lambda_closure_expr(out); return out;
} bool Parser::is_lambda_helper_expr(const Expr& expr) const { Binding* binding = expr.binding != NULL ? expr.binding : expr.node.binding;
return binding != NULL && lambda_closure_types_.find(binding) != lambda_closure_types_.end(); } Expr Parser::lambda_closure_expr(const Expr& expr)
{ Binding* binding = expr.binding != NULL ? expr.binding : expr.node.binding; map<Binding*, TypePtr>::const_iterator found = lambda_closure_types_.find(binding);
if (found == lambda_closure_types_.end()) return expr; TypePtr closure = found->second; Expr out;
out.valid = true; out.type = closure; out.category = ValueCategory::PRValue; out.braced_init_list = true;
out.node = Node("braced-init-list"); out.node.type = closure; out.node.category = ValueCategory::PRValue; out.node.token_text = "lambda-closure";
map<Binding*, vector<Node> >::const_iterator init = lambda_capture_initializers_.find(binding); if (init != lambda_capture_initializers_.end()) for (size_t i = 0; i < init->second.size(); ++i)
add_child(out.node, init->second[i]); annotate_expr_node(out); return out; }
bool Parser::call_has_function_template_candidate(const Expr& callee) const { if (!callee.explicit_template_arguments.empty()) return true;
for (size_t i = 0; i < callee.overloads.size(); ++i) { Binding* binding = callee.overloads[i]; if (function_template_placeholders_.find(binding) !=
function_template_placeholders_.end()) return true; if (binding != NULL && binding->aliased_binding != NULL && function_template_placeholders_.find(binding->aliased_binding) !=
function_template_placeholders_.end()) return true; } if (callee.binding != NULL &&
function_template_placeholders_.find(callee.binding) != function_template_placeholders_.end()) return true; return false;
} void Parser::materialize_template_lambda_arguments(const Expr& callee, vector<Expr>& args) {
if (!call_has_function_template_candidate(callee)) return; for (size_t i = 0; i < args.size(); ++i) if (is_lambda_helper_expr(args[i]))
args[i] = lambda_closure_expr(args[i]); } Expr Parser::parse_new_expression() {
if (consume(OP_COLON2)) { } expect(KW_NEW);
Expr placement; bool have_placement = false; if (consume(OP_LPAREN)) {
vector<Expr> args; if (!at(OP_RPAREN)) args = parse_argument_list(); expect(OP_RPAREN);
if (args.size() != 1) throw runtime_error("unsupported placement new"); placement = args[0]; have_placement = true;
} TypePtr type; if (!try_parse_type_name(type)) {
if (!at_simple_builtin() && !at_simple_cv()) throw runtime_error("expected new type"); DeclSpecs specs = parse_decl_specifier_seq(false); type = type_from_decl_specs(specs);
} type = substitute_template_type(type); bool array_new = false; Expr bound;
if (consume(OP_LSQUARE)) { array_new = true; bound = parse_expression();
expect(OP_RSQUARE); } vector<Expr> args; bool have_initializer_parens = false;
if (consume(OP_LPAREN)) { have_initializer_parens = true; if (!at(OP_RPAREN))
args = parse_argument_list(); expect(OP_RPAREN); } TypePtr record = pa11::strip_cv(type);
Binding* ctor = NULL; if (!array_new && record->kind == pa11::TypeKind::Record && record->scope != NULL) { bool dependent_new_args = false; for (size_t i = 0; i < args.size(); ++i) if (type_is_template_dependent(args[i].type) ||
args[i].pack_expansion) dependent_new_args = true; if (!type_is_template_dependent(record) && !dependent_new_args) { vector<Expr> converted; ctor = resolve_constructor_candidate(record, args, false, converted); args = converted;
} else if (args.empty()) ctor = ensure_default_constructor(record, true); if (ctor != NULL && unevaluated_expression_depth_ == 0)
{ parse_pending_function_body(ctor); parse_pending_member_body(ctor); }
} Binding* opnew = NULL; if (have_placement) {
	vector<Binding*> news = lookup_unqualified_set(current_scope(),
		array_new ? "operatornew[]" : "operatornew",
		pa11::LOOKUP_FUNCTION);
	Expr size_arg;
	size_arg.valid = true;
	size_arg.type = pa11::make_fundamental(FT_UNSIGNED_LONG_INT);
	size_arg.category = ValueCategory::PRValue;
	size_arg.constant_expression = true;
	size_arg.has_constant_value = true;
	size_arg.constant_value = 0;
	size_arg.node = Node("literal prvalue " +
		pa11::describe_type(size_arg.type) + " 0");
	vector<Expr> new_args;
	new_args.push_back(size_arg);
	new_args.push_back(placement);
	vector<Expr> converted_new_args;
	map<Binding*, vector<TemplateArgument> > explicit_template_arguments;
	opnew = resolve_call_candidate(news,
	                               new_args,
	                               explicit_template_arguments,
	                               converted_new_args);
} Expr out;
out.valid = true; out.binding = opnew; out.type = pa11::make_pointer(type); out.category = ValueCategory::PRValue;
out.node = Node(string("new-expression prvalue ") + pa11::describe_type(out.type) + (array_new ? " array" : "")); out.node.direct_call = ctor;
out.node.binding = opnew; if (have_initializer_parens) out.node.token_text = "paren-init"; if (have_placement)
add_child(out.node, placement.node); if (array_new) add_child(out.node, bound.node); for (size_t i = 0; i < args.size(); ++i)
add_child(out.node, args[i].node); annotate_expr_node(out); return out; }
Expr Parser::parse_delete_expression() { consume(OP_COLON2); expect(KW_DELETE);
bool array_delete = false; if (consume(OP_LSQUARE)) { expect(OP_RSQUARE);
array_delete = true; } Expr operand = parse_unary_expression(); TypePtr ptr_type = pa11::strip_cv(expression_object_type(operand.type));
if (ptr_type->kind != pa11::TypeKind::Pointer) throw runtime_error("delete operand is not pointer"); QualifiedName opname; opname.name = array_delete ? "operatordelete[]" : "operatordelete";
opname.spelling = array_delete ? "::operatordelete[]" : "::operatordelete"; opname.qualified = true; opname.qualifier = global_scope(); Expr op = make_builtin_id_expr(opname);
if (!op.valid || op.binding == NULL) throw runtime_error("operator delete not found"); Expr out; out.valid = true;
out.binding = op.binding; out.type = pa11::make_fundamental(FT_VOID); out.category = ValueCategory::PRValue; out.node = Node(string("delete-expression prvalue void") +
(array_delete ? " array" : "")); out.node.binding = op.binding; add_child(out.node, operand.node); annotate_expr_node(out);
return out; } Expr Parser::parse_literal_expression() {
string source = consume_literal(); Expr out; out.valid = true; if (!source.empty() && source[0] == '"' &&
!(source.size() >= 2 && source[source.size() - 1] == '"')) { size_t close = source.rfind('"'); if (close == string::npos || close == 0)
throw runtime_error("invalid string literal"); string quoted = source.substr(0, close + 1); string suffix = source.substr(close + 1); QualifiedName name;
name.name = "operator\"\"" + suffix; name.spelling = name.name; Expr callee = make_id_expr(name); StringLiteralInfo info;
if (!AnalyzeStringLiteral(quoted, info)) throw runtime_error("invalid string literal"); Expr text; text.valid = true;
text.type = pa11::make_array(pa11::make_cv(pa11::make_fundamental(info.type), pa11::CV_CONST), false, ordinary_string_elements(quoted,
info.elements)); text.category = ValueCategory::LValue; text.constant_expression = true; text.node = Node("literal lvalue " + pa11::describe_type(text.type) +
" " + quoted); text.node.token_text = quoted; annotate_expr_node(text); Expr size;
size.valid = true; size.type = pa11::make_fundamental(FT_INT); size.category = ValueCategory::PRValue; size.constant_expression = true;
size.has_constant_value = true; size.constant_value = ordinary_string_elements(quoted, info.elements) - 1; size.node = Node("literal prvalue int " + to_string(size.constant_value));
size.node.token_text = to_string(size.constant_value); annotate_expr_node(size); vector<Expr> args; args.push_back(text);
args.push_back(size); return make_call_expr(callee, args); } if (!source.empty() && source[source.size() - 1] == '"')
{ StringLiteralInfo info; if (!AnalyzeStringLiteral(source, info)) throw runtime_error("invalid string literal");
TypePtr type = pa11::make_array(pa11::make_cv(pa11::make_fundamental(info.type), pa11::CV_CONST), false, ordinary_string_elements(source,
info.elements)); out.type = type; out.category = ValueCategory::LValue; out.constant_expression = true;
out.node = Node("literal lvalue " + pa11::describe_type(type) + " " + source); out.node.token_text = source; annotate_expr_node(out); return out;
} if (is_float_literal_text(source)) { out.type = floating_literal_type(source);
out.constant_expression = true; } else if (!source.empty() && source[source.size() - 1] == '\'') {
CharacterLiteralInfo info; if (!AnalyzeCharacterLiteral(source, false, info)) throw runtime_error("invalid character literal"); out.type = pa11::make_fundamental(info.type);
out.constant_expression = true; out.has_constant_value = true; out.constant_value = info.code_point; out.null_pointer_constant = false;
} else { IntegerLiteralInfo info;
if (!AnalyzeIntegerLiteral(source, info)) throw runtime_error("invalid integer literal"); if (info.user_defined) {
QualifiedName name; name.name = "operator\"\"" + info.ud_suffix; name.spelling = name.name; name.has_template_arguments = true;
vector<TemplateArgument> chars; TypePtr char_type = pa11::make_fundamental(FT_CHAR); for (size_t i = 0; i < info.prefix.size(); ++i) chars.push_back(TemplateArgument::value_arg(
char_type, static_cast<unsigned char>(info.prefix[i]))); name.template_arguments.push_back( TemplateArgument::pack_arg(chars));
Expr callee = make_id_expr(name); return make_call_expr(callee, vector<Expr>()); } out.type = pa11::make_fundamental(info.type);
out.constant_expression = true; out.has_constant_value = true; out.constant_value = info.value; out.null_pointer_constant = info.value == 0;
} out.node = Node("literal prvalue " + pa11::describe_type(out.type) + " " + source); out.node.token_text = source;
annotate_expr_node(out); return out; } Expr Parser::parse_cast_expression()
{ ETokenType kw = current().type; string text = current().source; ++pos_;
expect(OP_LT); size_t target_begin = pos_; TypePtr target = parse_type_id(); size_t target_end = pos_;
expect(OP_GT); expect(OP_LPAREN); Expr inner; try
{ inner = parse_expression(); } catch (const runtime_error& err)
{ if (!replaying_dependent_decltype_ || string(err.what()).compare(0, 16, "name not found: ") != 0) throw;
TypePtr object = target; TypePtr bare = pa11::strip_cv(target); if (bare->kind == pa11::TypeKind::LValueReference || bare->kind == pa11::TypeKind::RValueReference)
object = bare->base; inner.valid = true; inner.type = object; inner.category = ValueCategory::LValue;
inner.node = Node("id-expression lvalue " + pa11::describe_type(object) + " <dependent-cast-operand>"); annotate_expr_node(inner);
} expect(OP_RPAREN); Expr cast = make_cast_expr(target, op_leaf(kw, text), inner); if (!cast.pack_expansion && at(OP_DOTS))
{ string visible_pack_name; bool target_still_mentions_pack = type_contains_template_parameter_name(target, visible_pack_name) &&
parameter_pack_expansion_name(visible_pack_name); if (!target_still_mentions_pack) { for (size_t i = target_begin; i < target_end; ++i)
if (parameter_pack_expansion_name(tokens_[i].source)) { visible_pack_name = tokens_[i].source; break;
} TemplateArgument subst; if (!visible_pack_name.empty() && find_template_value_substitution(visible_pack_name, subst) &&
subst.kind == TemplateArgumentKind::Pack && subst.pack.size() == 1) { Expr pack;
pack.valid = true; pack.pack_expansion = true; pack.type = target; pack.category = cast.category;
pack.node = Node("pack-expression cast"); pack.pack.push_back(cast); add_child(pack.node, cast.node); annotate_expr_node(pack);
return pack; } } }
return cast; } Expr Parser::parse_type_trait_expression(ETokenType keyword) {
const bool is_sizeof = keyword == KW_SIZEOF; ++pos_; if (is_sizeof && consume(OP_DOTS)) {
expect(OP_LPAREN); string name = consume_identifier(); expect(OP_RPAREN); vector<Binding*> pack;
if (!find_function_parameter_pack_substitution(name, pack)) { TemplateArgument subst; if (find_template_value_substitution(name, subst) &&
subst.kind == TemplateArgumentKind::Pack) { if (validating_template_definition_ && active_type_parameter_pack(name))
return make_dependent_sizeof_pack_expr(name); return make_sizeof_expr(subst.pack.size()); } if (active_type_parameter_pack(name))
return make_dependent_sizeof_pack_expr(name); throw runtime_error("parameter pack not found"); } return make_sizeof_expr(pack.size());
} expect(OP_LPAREN); size_t save = pos_; uint64_t value = 0;
bool parsed_type_operand = false; try { TypePtr type = parse_type_id();
expect(OP_RPAREN); parsed_type_operand = true; if (type_is_template_dependent(type)) return make_dependent_sizeof_expr(keyword, type);
try { TypePtr bare = pa11::strip_cv(type); if (!type_is_template_dependent(type) &&
bare->kind == pa11::TypeKind::Record) complete_template_record(bare); value = is_sizeof ? pa11::type_size(type) : pa11::type_align(type); }
catch (const runtime_error& err) { if (!type_is_template_dependent(type) || (string(err.what()) != "incomplete object type" &&
string(err.what()) != "incomplete class type")) throw; value = 8; }
} catch (const exception&) { if (parsed_type_operand)
throw; pos_ = save; ++unevaluated_expression_depth_; Expr expr;
try { expr = parse_expression(); }
catch (...) { --unevaluated_expression_depth_; throw;
} --unevaluated_expression_depth_; expect(OP_RPAREN); TypePtr object_type = expression_object_type(expr.type);
if (type_is_template_dependent(object_type)) return make_dependent_sizeof_expr(keyword, object_type); try {
TypePtr bare = pa11::strip_cv(object_type); if (!type_is_template_dependent(object_type) && bare->kind == pa11::TypeKind::Record) complete_template_record(bare);
value = is_sizeof ? pa11::type_size(object_type) : pa11::type_align(object_type); } catch (const runtime_error& err)
{ if (!type_is_template_dependent(object_type) || (string(err.what()) != "incomplete object type" && string(err.what()) != "incomplete class type"))
throw; value = 8; } }
return make_sizeof_expr(value); } Expr Parser::parse_c_style_cast_or_parenthesized() {
size_t save = pos_; expect(OP_LPAREN); TypePtr target; bool parsed_type_id = false;
if (at(OP_LBRACE)) { Node body = parse_compound_statement(); expect(OP_RPAREN); Expr out;
out.valid = true; out.type = pa11::make_fundamental(FT_VOID); out.category = ValueCategory::PRValue;
if (!body.children.empty() && node_starts_with(body.children.back(), "expression-statement") && !body.children.back().children.empty()) {
const Node& result = body.children.back().children[0]; out.type = result.type; out.category = result.category; }
out.node = Node("statement-expression " + value_category_name(out.category) + " " + pa11::describe_type(out.type));
out.node.type = out.type; out.node.category = out.category; add_child(out.node, body); annotate_expr_node(out); return parse_postfix_suffixes(out); }
try { target = parse_type_id(); expect(OP_RPAREN);
parsed_type_id = true; } catch (const exception&) {
} if (parsed_type_id && at(OP_LBRACE)) {
	Expr init = parse_braced_init_list(); init.type = target;
	init.category = ValueCategory::PRValue; init.node.type = target;
	init.node.category = init.category; TypePtr bare = pa11::strip_cv(target);
	if (bare->kind == pa11::TypeKind::Record && !type_is_template_dependent(target))
		{
		complete_template_record(bare);
		ensure_aggregate_constructors_for_init(target, init.node);
		ensure_default_destructor(target, !pa11::record_direct_bases(bare).empty());
		}
	annotate_expr_node(init); return parse_postfix_suffixes(init);
} if (!parsed_type_id || at(OP_RPAREN) || at(OP_COMMA) ||
at(OP_SEMICOLON) || at(OP_RSQUARE) || at(OP_RBRACE)) {
pos_ = save; expect(OP_LPAREN); int save_template_argument_depth = template_argument_expression_depth_; template_argument_expression_depth_ = 0;
Expr inner; try { inner = parse_expression();
expect(OP_RPAREN); } catch (...) {
template_argument_expression_depth_ = save_template_argument_depth; throw; }
template_argument_expression_depth_ = save_template_argument_depth; return parse_postfix_suffixes(inner); } Expr inner = parse_unary_expression();
return make_cast_expr(target, "OP_LPAREN:", inner); } Expr Parser::parse_functional_cast(TypePtr target) {
	expect(OP_LPAREN);
	try
	{
		target = substitute_template_type(target);
	}
	catch (const runtime_error&)
	{
		if (!type_is_template_dependent(target))
			throw;
	}
	if (pa11::strip_cv(target)->kind == pa11::TypeKind::Record) { vector<Expr> args;
	if (!at(OP_RPAREN)) args = parse_argument_list(); expect(OP_RPAREN); bool dependent_args = false;
	for (size_t i = 0; i < args.size(); ++i)
	if (type_is_template_dependent(args[i].type) || args[i].pack_expansion)
	dependent_args = true;
	if (!type_is_template_dependent(target) && !dependent_args)
{ TypePtr target_record = pa11::strip_cv(target); bool active_incomplete_default = false; if (target_record->kind == pa11::TypeKind::Record)
{ try { complete_template_record(target_record);
} catch (const runtime_error& err) { if (!args.empty() ||
(string(err.what()) != "incomplete class type" && string(err.what()) != "incomplete object type") || active_class_instantiations_.empty()) throw;
	active_incomplete_default = true; } } if (!args.empty()) {
	try { return make_constructor_init_expr(target, args, false); }
	catch (const runtime_error& err) {
	if (args.size() != 1 || string(err.what()) != "no matching constructor") throw;
	++explicit_conversion_context_; Conversion conv;
	try { conv = convert_to(args[0], target); }
	catch (...) { --explicit_conversion_context_; throw; }
	--explicit_conversion_context_; if (!conv.viable) throw; return conv.expr; } } Expr init; init.valid = true; init.type = target;
init.category = ValueCategory::PRValue; init.braced_init_list = true; init.node = Node("braced-init-list"); if (!active_incomplete_default)
{ try { init.node.direct_call =
ensure_default_constructor(target, true); } catch (const runtime_error& err) {
if ((string(err.what()) != "incomplete class type" && string(err.what()) != "incomplete object type") || active_class_instantiations_.empty()) throw;
active_incomplete_default = true; } } if (init.node.direct_call == NULL &&
!active_incomplete_default) throw runtime_error("no matching constructor"); bool force_dtor = !pa11::record_direct_bases(pa11::strip_cv(target)).empty();
try { ensure_default_destructor(target, force_dtor); }
catch (const runtime_error& err) { if ((string(err.what()) != "incomplete class type" && string(err.what()) != "incomplete object type") ||
active_class_instantiations_.empty()) throw; } annotate_expr_node(init);
return init; } Expr init; init.valid = true;
init.type = target; init.category = ValueCategory::PRValue; init.braced_init_list = true; init.node = Node("braced-init-list");
for (size_t i = 0; i < args.size(); ++i) add_child(init.node, args[i].node); annotate_expr_node(init); return init;
} if (consume(OP_RPAREN)) { string pack_name;
TemplateArgument subst; if (type_contains_template_parameter_name(target, pack_name) && find_template_value_substitution(pack_name, subst) && subst.kind == TemplateArgumentKind::Pack)
{ Expr out; out.valid = true; out.pack_expansion = true;
out.type = target; out.category = ValueCategory::PRValue; out.node = Node("pack-expression functional-cast"); for (size_t i = 0; i < subst.pack.size(); ++i)
{ if (subst.pack[i].kind != TemplateArgumentKind::Type) throw runtime_error("type pack required"); TypePtr element_type =
substitute_template_type_parameter(target, pack_name, subst.pack[i].type); Expr elem;
elem.type = element_type; elem.valid = true; elem.category = ValueCategory::PRValue; elem.constant_expression = true;
if (pa11::is_integral_or_bool_type(element_type)) { elem.has_constant_value = true; elem.constant_value = 0;
} elem.node = Node("literal prvalue " + pa11::describe_type(element_type) + " 0");
elem.node.token_text = "0"; annotate_expr_node(elem); out.pack.push_back(elem); add_child(out.node, elem.node);
} annotate_expr_node(out); return out; }
Expr zero; zero.type = target; zero.valid = true; zero.constant_expression = true;
if (pa11::is_integral_or_bool_type(target)) { zero.has_constant_value = true; zero.constant_value = 0;
} zero.node = Node("literal prvalue " + pa11::describe_type(target) + " 0"); if (type_is_pointer(target)) {
zero.null_pointer_constant = true; zero.node.token_text = "nullptr"; } else
zero.node.token_text = "0"; annotate_expr_node(zero); return zero; }
Expr inner = parse_expression(); expect(OP_RPAREN); return make_cast_expr(target, "", inner); }
Expr Parser::parse_braced_init_list() { expect(OP_LBRACE); Expr init;
init.valid = true; init.braced_init_list = true; init.node = Node("braced-init-list"); while (!at(OP_RBRACE))
	{
	if (consume(OP_DOT))
		{
		string name = consume_identifier(); expect(OP_ASS);
		Expr child = at(OP_LBRACE) ? parse_braced_init_list() : parse_assignment_expression();
		Node designator("designated-init " + name); designator.type = child.type;
		designator.category = child.category; designator.binding = child.binding;
		add_child(designator, child.node); add_child(init.node, designator);
		}
	else if (at(OP_LBRACE)) add_child(init.node, parse_braced_init_list().node);
	else
		{
		vector<Expr> expanded; if (try_parse_static_member_pack_expansion(expanded))
			{
			for (size_t i = 0; i < expanded.size(); ++i) add_child(init.node, expanded[i].node);
			if (!consume(OP_COMMA)) break; continue;
			}
		size_t child_begin = pos_; Expr child = parse_assignment_expression();
		size_t child_end = pos_; if (consume(OP_DOTS)) { if (!child.pack_expansion)
		{ vector<Expr> pattern_expansion; if (!try_expand_expression_pack_pattern( child_begin,
		child_end, pattern_expansion)) throw runtime_error( "pack expansion requires a pack");
		for (size_t i = 0; i < pattern_expansion.size(); ++i) add_child(init.node, pattern_expansion[i].node); if (!consume(OP_COMMA)) break;
		continue; } for (size_t i = 0; i < child.pack.size(); ++i) add_child(init.node, child.pack[i].node);
		if (!consume(OP_COMMA)) break; continue; }
		if (child.category == ValueCategory::PRValue) { TypePtr object = pa11::strip_cv(expression_object_type(child.type));
		if (object->kind == pa11::TypeKind::Record && !pa11::record_direct_bases(object).empty()) ensure_default_destructor(object, true); }
		add_child(init.node, child.node);
		}
	if (!consume(OP_COMMA)) break;
	}
expect(OP_RBRACE); return init; }
bool Parser::try_parse_static_member_pack_expansion(vector<Expr>& out) { size_t save = pos_; out.clear();
if (!at_identifier()) return false; string root = consume_identifier(); string pack_name;
TemplateDeclaration* owner_template = NULL; vector<TemplateArgument> owner_arguments; bool owner_is_template_id = false; size_t owner_arguments_begin = 0;
size_t owner_arguments_end = 0; if (at(OP_LT)) { owner_is_template_id = true;
owner_arguments_begin = pos_; try { parse_template_argument_list(owner_arguments);
owner_arguments_end = pos_; } catch (const exception&) {
pos_ = save; return false; } TemplateArgument template_subst;
if (find_template_value_substitution(root, template_subst) && template_subst.kind == TemplateArgumentKind::Template && template_subst.template_declaration != NULL) owner_template = template_subst.template_declaration;
if (owner_template == NULL) owner_template = find_alias_template(NULL, root); if (owner_template == NULL) owner_template = find_class_template(NULL, root);
if (owner_template == NULL) { pos_ = save; return false;
} } if (!consume(OP_COLON2) || !at_identifier()) {
pos_ = save; return false; } string member_name = consume_identifier();
if (!consume(OP_DOTS)) { pos_ = save; return false;
} if (owner_is_template_id) { vector<string> owner_parameter_names;
for (size_t i = 0; i < owner_arguments.size(); ++i) collect_template_parameter_names_from_argument( owner_arguments[i], owner_parameter_names);
for (size_t i = 0; i < owner_parameter_names.size(); ++i) if (parameter_pack_expansion_name(owner_parameter_names[i])) { pack_name = owner_parameter_names[i];
break; } for (size_t i = 0; i < owner_arguments.size(); ++i) {
if (!pack_name.empty()) break; if (template_argument_contains_template_parameter_name( owner_arguments[i],
pack_name)) break; } if (pack_name.empty())
for (size_t i = owner_arguments_begin; i < owner_arguments_end; ++i) if (parameter_pack_expansion_name(tokens_[i].source))
{ pack_name = tokens_[i].source; break; }
if (pack_name.empty()) { TypePtr owner_type = owner_template->kind == TemplateDeclarationKind::Alias
? instantiate_alias_template(owner_template, owner_arguments) : instantiate_class_template(owner_template, owner_arguments); type_contains_template_parameter_name(owner_type, pack_name); }
} else { pack_name = root;
} if (pack_name.empty()) { pos_ = save;
return false; } if (validating_template_definition_ && active_type_parameter_pack(pack_name))
{ Expr elem; elem.valid = true; elem.pack_expansion = true;
elem.type = pa11::make_fundamental(FT_INT); elem.category = ValueCategory::PRValue; elem.dependent_value_name = root + "::" + member_name; elem.dependent_value_owner_template_name = root;
elem.dependent_value_member_name = member_name; for (size_t i = 0; i < owner_arguments.size(); ++i) elem.dependent_value_owner_template_arguments.push_back( expr_template_instance_argument(owner_arguments[i]));
elem.node = Node("pack-expression " + elem.dependent_value_name); elem.node.token_text = elem.dependent_value_name; annotate_expr_node(elem); out.push_back(elem);
return true; } TemplateArgument subst; if (!find_template_value_substitution(pack_name, subst) ||
subst.kind != TemplateArgumentKind::Pack) { pos_ = save; return false;
} for (size_t i = 0; i < subst.pack.size(); ++i) { if (subst.pack[i].kind != TemplateArgumentKind::Type)
throw runtime_error("type pack required"); TypePtr record; if (owner_is_template_id) {
vector<TemplateArgument> element_arguments; for (size_t j = 0; j < owner_arguments.size(); ++j) { TemplateArgument element_argument =
substitute_template_argument_type_parameter( owner_arguments[j], pack_name, subst.pack[i].type);
if (element_argument.kind == TemplateArgumentKind::Type) { TypePtr arg_type = pa11::strip_cv(element_argument.type); if (arg_type.get() != NULL &&
arg_type->kind == pa11::TypeKind::Record && arg_type->is_template_specialization && arg_type->scope == NULL && !arg_type->template_primary_name.empty())
{ TemplateArgument template_subst; bool have_template_subst = find_template_value_substitution(
arg_type->template_primary_name, template_subst) && template_subst.kind == TemplateArgumentKind::Template &&
template_subst.template_declaration != NULL; if (!have_template_subst) for (size_t ai = active_class_instantiations_.size();
ai > 0 && !have_template_subst; --ai) { TemplateDeclaration* active_decl =
active_class_instantiations_[ai - 1]. declaration; TypePtr active_type = pa11::strip_cv( active_class_instantiations_[ai - 1].
type); map<const void*, vector<TemplateArgument> >::const_iterator active_args =
record_template_arguments_.find( active_type.get()); if (active_decl == NULL || active_args ==
record_template_arguments_.end()) continue; for (size_t pi = 0; pi < active_decl->parameters.size() &&
pi < active_args->second.size(); ++pi) if (active_decl->parameters[pi].kind == TemplateParameterKind::
TemplateTemplate && active_decl->parameters[pi].name == arg_type->template_primary_name) {
template_subst = substitute_template_argument( active_args->second[pi]); have_template_subst =
template_subst.kind == TemplateArgumentKind:: Template && template_subst.
template_declaration != NULL; if (!have_template_subst) for (size_t si = 0; si < active_decl->
class_specialization_pattern. size() && si < active_type-> template_arguments.size();
++si) { const TemplateArgument& pattern_arg =
active_decl-> class_specialization_pattern [si]; if (pattern_arg.kind !=
TemplateArgumentKind:: Template || pattern_arg. template_declaration !=
NULL || pattern_arg.value_name != arg_type-> template_primary_name)
continue; template_subst = substitute_template_argument( template_argument_from_instance_argument(
active_type-> template_arguments [si])); have_template_subst =
template_subst.kind == TemplateArgumentKind:: Template && template_subst.
template_declaration != NULL; if (have_template_subst) break;
} break; } }
if (have_template_subst) { vector<TemplateArgument> nested_arguments; for (size_t ti = 0;
ti < arg_type->template_arguments.size(); ++ti) nested_arguments.push_back( substitute_template_argument(
template_argument_from_instance_argument( arg_type-> template_arguments[ti]))); element_argument =
TemplateArgument::type_arg( template_subst.template_declaration-> kind == TemplateDeclarationKind::Alias
? instantiate_alias_template( template_subst. template_declaration, nested_arguments)
: instantiate_class_template( template_subst. template_declaration, nested_arguments));
} } } element_arguments.push_back(
substitute_template_argument(element_argument)); } TypePtr pack_record = pa11::strip_cv(subst.pack[i].type); map<const void*, vector<TemplateArgument> >::iterator
saved_pack_record_args = record_template_arguments_.end(); vector<TemplateArgument> pack_record_args; bool restore_pack_record_args = false;
if (pack_record.get() != NULL && pack_record->kind == pa11::TypeKind::Record && !pack_record->is_template_specialization && !pack_record->is_dependent_typename &&
pack_record->scope != NULL && pack_record->complete && pack_record->template_arguments.empty()) {
saved_pack_record_args = record_template_arguments_.find(pack_record.get()); if (saved_pack_record_args != record_template_arguments_.end())
{ pack_record_args = saved_pack_record_args->second; restore_pack_record_args = true; record_template_arguments_.erase(
saved_pack_record_args); } } try
{ record = owner_template->kind == TemplateDeclarationKind::Alias ? instantiate_alias_template(owner_template,
element_arguments) : instantiate_class_template(owner_template, element_arguments); }
catch (...) { if (restore_pack_record_args) record_template_arguments_[pack_record.get()] =
pack_record_args; throw; } if (restore_pack_record_args)
record_template_arguments_[pack_record.get()] = pack_record_args; } else
record = subst.pack[i].type; try { record = substitute_template_type(record);
} catch (const runtime_error&) { }
record = pa11::strip_cv(record); complete_template_record(record); if (record->kind != pa11::TypeKind::Record || record->scope == NULL) {
if (validating_template_definition_ && active_class_instantiation_dependent()) { Expr elem;
elem.valid = true; elem.type = pa11::make_fundamental(FT_INT); elem.category = ValueCategory::PRValue; elem.node = Node("id-expression prvalue " +
pa11::describe_type(elem.type) + " " + member_name); elem.node.token_text = member_name; annotate_expr_node(elem);
out.push_back(elem); return true; } if (active_class_instantiation_dependent())
{ pos_ = save; out.clear(); return false;
} throw runtime_error("pack expansion qualifier is not a record"); } vector<Binding*> found =
lookup_qualified_set(record->scope, member_name, pa11::LOOKUP_VALUE); if (found.empty()) throw runtime_error("pack expansion member not found"); out.push_back(make_static_member_pack_element(found[0]));
} return true; }
static size_t top_level_argument_ellipsis(const vector<Token>& tokens,
                                          size_t begin)
{
	int paren = 0;
	int square = 0;
	int brace = 0;
	int angle = 0;
	for (size_t i = begin; i < tokens.size(); ++i)
	{
		if (tokens[i].kind != posttoken::TokenKind::Simple)
			continue;
		ETokenType type = tokens[i].type;
		if (type == OP_LPAREN)
			++paren;
		else if (type == OP_RPAREN)
		{
			if (paren == 0 && square == 0 && brace == 0 && angle == 0)
				break;
			if (paren > 0)
				--paren;
		}
		else if (type == OP_LSQUARE)
			++square;
		else if (type == OP_RSQUARE && square > 0)
			--square;
		else if (type == OP_LBRACE)
			++brace;
		else if (type == OP_RBRACE && brace > 0)
			--brace;
		else if (type == OP_LT && paren == 0 && square == 0 && brace == 0)
			++angle;
		else if (type == OP_GT && angle > 0)
			--angle;
		else if (type == OP_COMMA && paren == 0 && square == 0 &&
		         brace == 0 && angle == 0)
			break;
		else if (type == OP_DOTS && paren == 0 && square == 0 &&
		         brace == 0 && angle == 0)
			return i;
	}
	return tokens.size();
}
vector<Expr> Parser::parse_argument_list()
{ vector<Expr> args; for (;;) {
vector<Scope*> saved_arg_scopes = scopes_;
vector<Expr> expanded; bool expanded_member_pack = false; try {
expanded_member_pack = try_parse_static_member_pack_expansion(expanded);
} catch (...) { scopes_ = saved_arg_scopes; throw; }
scopes_ = saved_arg_scopes; if (expanded_member_pack) { args.insert(args.end(), expanded.begin(), expanded.end());
if (!consume(OP_COMMA)) break; continue; }
saved_arg_scopes = scopes_;
size_t arg_begin = pos_; Expr arg; try {
arg = at(OP_LBRACE) ? parse_braced_init_list() : parse_assignment_expression();
} catch (...) { scopes_ = saved_arg_scopes; size_t ellipsis = top_level_argument_ellipsis(tokens_, arg_begin);
if (ellipsis != tokens_.size()) { vector<Expr> pattern_expansion; pos_ = ellipsis + 1;
if (try_expand_expression_pack_pattern(arg_begin, ellipsis, pattern_expansion)) {
args.insert(args.end(), pattern_expansion.begin(), pattern_expansion.end()); if (!consume(OP_COMMA))
break; continue; } }
throw; }
scopes_ = saved_arg_scopes;
size_t arg_end = pos_; if (consume(OP_DOTS)) { if (arg.pack_expansion)
args.insert(args.end(), arg.pack.begin(), arg.pack.end()); else { vector<Expr> pattern_expansion;
if (try_expand_expression_pack_pattern(arg_begin, arg_end, pattern_expansion)) {
args.insert(args.end(), pattern_expansion.begin(), pattern_expansion.end()); if (!consume(OP_COMMA))
break; continue; } string pack_name;
TemplateArgument subst; if (!type_contains_template_parameter_name(arg.type, pack_name) || (!find_template_value_substitution(pack_name, subst) ||
subst.kind != TemplateArgumentKind::Pack)) { if (pack_name.empty()) for (size_t i = arg_begin;
i < arg_end && i < tokens_.size(); ++i) if (parameter_pack_expansion_name( tokens_[i].source))
{ pack_name = tokens_[i].source; break; }
if (!pack_name.empty() && find_template_value_substitution(pack_name, subst) && subst.kind == TemplateArgumentKind::Pack) ;
else if (!pack_name.empty() && parameter_pack_expansion_name(pack_name)) { arg.pack_expansion = true;
arg.pack.clear(); args.push_back(arg); if (!consume(OP_COMMA)) break;
continue; } else throw runtime_error(
"pack expansion requires a pack"); } for (size_t i = 0; i < subst.pack.size(); ++i) {
if (subst.pack[i].kind != TemplateArgumentKind::Type) throw runtime_error("type pack required"); Expr elem = arg; elem.pack_expansion = false;
elem.pack.clear(); elem.type = substitute_template_type_parameter(arg.type, pack_name,
subst.pack[i].type); elem.node.type = elem.type; args.push_back(elem); }
} } else args.push_back(arg);
if (!consume(OP_COMMA)) break; } return args;
}
}  // namespace internal
}  // namespace pa12
