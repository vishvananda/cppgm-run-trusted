#include "pa12_expr_semantics_support.h"
#include <functional>
#include <stdexcept>
using namespace std; namespace pa12 { namespace internal { namespace {
bool signed_integral_fundamental(TypePtr type) { TypePtr bare = type.get() != NULL ? pa11::strip_cv(type) : TypePtr(); if (bare.get() == NULL || bare->kind != pa11::TypeKind::Fundamental)
return false; switch (bare->fundamental) { case FT_SIGNED_CHAR:
case FT_SHORT_INT: case FT_INT: case FT_LONG_INT: case FT_LONG_LONG_INT: case FT_INT128:
return true; default: return false; }
} bool signed_integral_widening(TypePtr source, TypePtr target) { TypePtr src_object = source;
if (src_object->kind == pa11::TypeKind::LValueReference || src_object->kind == pa11::TypeKind::RValueReference) src_object = src_object->base; TypePtr dst_object = target;
if (dst_object->kind == pa11::TypeKind::LValueReference || dst_object->kind == pa11::TypeKind::RValueReference) dst_object = dst_object->base; TypePtr src = pa11::strip_cv(src_object);
TypePtr dst = pa11::strip_cv(dst_object); return signed_integral_fundamental(src) && signed_integral_fundamental(dst) && pa11::type_size(dst) >= pa11::type_size(src);
} bool floating_fundamental(TypePtr type) { TypePtr bare = type.get() != NULL ? pa11::strip_cv(type) : TypePtr();
if (bare.get() == NULL || bare->kind != pa11::TypeKind::Fundamental) return false; return bare->fundamental == FT_FLOAT || bare->fundamental == FT_DOUBLE ||
bare->fundamental == FT_LONG_DOUBLE; } bool braced_scalar_narrows(TypePtr source, TypePtr target) {
TypePtr src_object = source; if (src_object->kind == pa11::TypeKind::LValueReference || src_object->kind == pa11::TypeKind::RValueReference) src_object = src_object->base;
TypePtr dst_object = target; if (dst_object->kind == pa11::TypeKind::LValueReference || dst_object->kind == pa11::TypeKind::RValueReference) dst_object = dst_object->base;
TypePtr src = pa11::strip_cv(src_object); TypePtr dst = pa11::strip_cv(dst_object); if (floating_fundamental(src) && pa11::is_integral_or_bool_type(dst)) return true;
if (floating_fundamental(src) && floating_fundamental(dst) && pa11::type_size(dst) < pa11::type_size(src)) return true; return false;
}
}  // namespace
void Parser::apply_braced_variable_initializer(Scope* target, Binding* variable, TypePtr type, const Expr& init,
Node& var) { Node list = init.node; TypePtr record = pa11::strip_cv(type);
if (init.type.get() == NULL && is_std_initializer_list_type(type, NULL))
{ Expr converted = make_initializer_list_expr(init, type); if (target->kind == ScopeKind::Class && !variable->is_static_member) default_member_initializers_[variable] = converted.node; add_child(var, converted.node); return; }
if (record->kind != pa11::TypeKind::Record && record->kind != pa11::TypeKind::Array) { if (type_is_template_dependent(type))
{ list.line += " lvalue " + pa11::describe_type(type); list.type = type; if (target->kind == ScopeKind::Class && !variable->is_static_member)
default_member_initializers_[variable] = list; add_child(var, list); return; }
TypePtr init_object = init.type.get() == NULL ? TypePtr() : pa11::strip_cv(expression_object_type(init.type)); TypePtr target_object = pa11::strip_cv(type); if (init.node.children.empty() &&
(init_object.get() == NULL || pa11::same_type(init_object, target_object))) { Expr zero;
zero.valid = true; zero.type = type; zero.category = ValueCategory::PRValue; zero.constant_expression = true;
zero.has_constant_value = true; zero.constant_value = 0; zero.null_pointer_constant = pa11::strip_cv(type)->kind == pa11::TypeKind::Pointer;
zero.node = Node("literal prvalue " + pa11::describe_type(type) + " 0"); zero.node.token_text = "0"; annotate_expr_node(zero);
if (target->kind == ScopeKind::Class && !variable->is_static_member) default_member_initializers_[variable] = zero.node; add_child(var, zero.node); if (pa11::type_has_const(type))
{ variable->has_constant = true; variable->constant_value = 0; }
return; } Expr scalar_init = init; if (!init.node.children.empty())
{ if (init.node.children.size() != 1) throw runtime_error("invalid initializer conversion"); scalar_init.valid = true;
scalar_init.node = init.node.children[0]; scalar_init.type = scalar_init.node.type; scalar_init.category = scalar_init.node.category; scalar_init.binding = scalar_init.node.binding;
scalar_init.overloads = scalar_init.node.overloads; scalar_init.explicit_template_arguments = scalar_init.node.explicit_template_arguments;
scalar_init.has_constant_value = scalar_init.node.has_constant_value; scalar_init.constant_value = scalar_init.node.constant_value; }
if (braced_scalar_narrows(scalar_init.type, type)) { throw runtime_error("narrowing conversion in braced initializer"); }
Conversion conv = convert_to(scalar_init, type); if (!conv.viable) throw runtime_error("invalid initializer conversion"); if (target->kind == ScopeKind::Class && !variable->is_static_member)
default_member_initializers_[variable] = conv.expr.node; add_child(var, conv.expr.node); if (pa11::type_has_const(type) && conv.expr.has_constant_value) {
variable->has_constant = true; variable->constant_value = conv.expr.constant_value; } return;
} if (record->kind == pa11::TypeKind::Record && record_has_aggregate_blocking_constructor(record)) {
	bool list_constructed = false; if (!init.node.children.empty()) { try { Expr constructed = make_constructor_list_init_expr(type, init, init.copy_initialization); list = constructed.node; list_constructed = true; } catch (const runtime_error& err) { if (string(err.what()) != "no matching constructor") throw; } }
	if (!list_constructed) { vector<Expr> args; for (size_t i = 0; i < init.node.children.size(); ++i) { Expr arg;
	arg.valid = true; arg.node = init.node.children[i]; arg.type = arg.node.type; arg.category = arg.node.category;
	arg.binding = arg.node.binding; arg.overloads = arg.node.overloads; arg.explicit_template_arguments = arg.node.explicit_template_arguments; if (arg.category == ValueCategory::PRValue &&
	arg.type.get() != NULL && pa11::strip_cv(expression_object_type(arg.type))->kind == pa11::TypeKind::Record) { TypePtr arg_record = pa11::strip_cv(expression_object_type(arg.type));
	ensure_default_destructor(arg_record, !pa11::record_direct_bases(arg_record).empty()); } args.push_back(arg); } try
{ Expr constructed = make_constructor_init_expr(type, args, init.copy_initialization); list = constructed.node;
} catch (const runtime_error& err) { if (string(err.what()) != "no matching constructor")
throw; } } } if (record->kind == pa11::TypeKind::Record &&
init.node.children.empty() && record->base.get() != NULL) { Binding* ctor = ensure_default_constructor(record, true);
if (ctor != NULL) { add_child(var, default_constructor_action(variable, true)); return;
} } if (record->kind == pa11::TypeKind::Array)
{
	function<Expr(const Node&)> expr_from_node = [&](const Node& node) {
		Expr out;
		out.valid = true;
		out.node = node;
		out.type = node.type;
		out.category = node.category;
		out.binding = node.binding;
		out.overloads = node.overloads;
		out.explicit_template_arguments = node.explicit_template_arguments;
		out.has_constant_value = node.has_constant_value;
		out.constant_value = node.constant_value;
		out.dependent_value_name = node.dependent_value_name;
		out.dependent_value_owner_template_name =
			node.dependent_value_owner_template_name;
		out.dependent_value_member_name = node.dependent_value_member_name;
		out.dependent_value_negated = node.dependent_value_negated;
		out.dependent_value_owner_template_arguments =
			node.dependent_value_owner_template_arguments;
		out.braced_init_list =
			node.line.compare(0, 16, "braced-init-list") == 0;
		return out;
	};
		function<void(Node&, TypePtr)> convert_array_initializer =
			[&](Node& array_node, TypePtr array_type) {
				TypePtr bare_array = pa11::strip_cv(array_type);
				if (bare_array->kind != pa11::TypeKind::Array)
					return;
			if (!bare_array->unknown_bound &&
			    array_node.children.size() > bare_array->bound)
				throw runtime_error("too many array initializers");
			TypePtr elem = bare_array->base;
			for (size_t i = 0; i < array_node.children.size(); ++i)
			{
				Node& child = array_node.children[i];
				TypePtr bare_elem = pa11::strip_cv(elem);
				if (child.line.compare(0, 16, "braced-init-list") == 0 &&
				    bare_elem->kind == pa11::TypeKind::Array)
				{
					convert_array_initializer(child, elem);
					continue;
				}
				if (child.line.compare(0, 16, "braced-init-list") == 0 &&
				    bare_elem->kind == pa11::TypeKind::Record)
					continue;
				Conversion conv = convert_to(expr_from_node(child), elem);
				if (!conv.viable)
					throw runtime_error("invalid initializer conversion");
					child = conv.expr.node;
				}
			};
		bool braced_string_array_initializer = false;
		if (list.children.size() == 1)
		{
			Expr string_child = expr_from_node(list.children[0]);
			braced_string_array_initializer =
				string_literal_initializes_array(type,
				                                 string_child,
				                                 NULL);
		}
		if (!braced_string_array_initializer)
			convert_array_initializer(list, type);
	} if (record->kind == pa11::TypeKind::Record && init.node.children.empty() &&
record->fields.empty() && record->base.get() == NULL && init.node.token_text != "lambda-closure") {
add_child(var, Node("no-op-initializer")); return; } if (record->kind == pa11::TypeKind::Record && !record_has_aggregate_blocking_constructor(record)) {
pa11::layout_record_type(record); size_t child_index = 0; for (size_t i = 0; i < record->fields.size() && child_index < list.children.size(); ++i) {
Binding* field = record->fields[i]; if (field == NULL || field->is_static_member) continue; Node& child = list.children[child_index++];
if (child.line.compare(0, 16, "braced-init-list") == 0) continue; Expr child_expr; child_expr.valid = true; child_expr.node = child; child_expr.type = child.type;
child_expr.category = child.category; child_expr.binding = child.binding; child_expr.has_constant_value = child.has_constant_value; child_expr.constant_value = child.constant_value;
child_expr.overloads = child.overloads; child_expr.explicit_template_arguments = child.explicit_template_arguments;
try { Conversion field_conv = convert_to(child_expr, field->type); if (field_conv.viable) child = field_conv.expr.node; } catch (const runtime_error&) { } } } ensure_aggregate_constructors_for_init(type, list);
list.line += " lvalue " + pa11::describe_type(type); list.type = type; if (target->kind == ScopeKind::Class && !variable->is_static_member) default_member_initializers_[variable] = list;
add_child(var, list); } void Parser::demand_empty_record_conversion_bodies(TypePtr src_record, TypePtr dst_record,
const Node& conversion_node) { function<void(Binding*)> demand_body = [&](Binding* fn) {
if (fn == NULL || fn->kind != BindingKind::Function) return; parse_pending_function_body(fn); parse_pending_member_body(fn);
ensure_function_body_extra_node(fn); }; function<void(Binding*)> demand_inline_without_object_root = [&](Binding* fn) {
if (fn == NULL || fn->kind != BindingKind::Function) return; fn->is_object_root = false; for (size_t i = 0; i < extra_lowir_nodes_.size(); ++i)
if (extra_lowir_nodes_[i].binding == fn) extra_lowir_nodes_[i].token_text = "inline-object-root"; }; if (src_record->kind == pa11::TypeKind::Record && src_record->scope != NULL)
{ instantiate_member_function_templates(src_record, true); for (map<string, vector<Binding*> >::const_iterator it = src_record->scope->members.begin();
it != src_record->scope->members.end(); ++it) { if (it->first.compare(0, 9, "operator ") != 0)
continue; for (size_t i = 0; i < it->second.size(); ++i) { Binding* concrete = it->second[i];
if (concrete == NULL || concrete->kind != BindingKind::Function || concrete->type.get() == NULL || concrete->type->kind != pa11::TypeKind::Function ||
!pa11::same_type(pa11::strip_cv(concrete->type->base), dst_record)) continue; demand_body(concrete);
demand_inline_without_object_root(concrete); for (Binding* fn = concrete->aliased_binding; fn != NULL && fn->kind == BindingKind::Function; fn = fn->aliased_binding)
{ demand_body(fn); demand_inline_without_object_root(fn); }
} } } function<void(const Node&)> demand_direct_calls =
[&](const Node& node) { if (node.direct_call != NULL) demand_body(node.direct_call); for (size_t i = 0; i < node.children.size(); ++i)
demand_direct_calls(node.children[i]); }; demand_direct_calls(conversion_node); }
bool Parser::record_copy_move_initializer_blocked(TypePtr dst_record, ValueCategory init_category) const {
bool declared_copy_or_move = false; bool trivial_defaulted_match = false; if (dst_record->scope == NULL) return false;
map<string, vector<Binding*> >::const_iterator found = dst_record->scope->members.find(dst_record->scope->name); if (found == dst_record->scope->members.end()) return false;
for (size_t i = 0; i < found->second.size(); ++i) { Binding* ctor = found->second[i]; if (ctor->kind != BindingKind::Function ||
ctor->type->kind != pa11::TypeKind::Function || ctor->type->parameters.size() != 2 || !pa11::is_reference_type(ctor->type->parameters[1])) continue;
TypePtr param = ctor->type->parameters[1]; if (!pa11::same_type(pa11::strip_cv(param->base), dst_record) && !same_template_specialization_record(param->base, dst_record)) continue;
if (ctor->is_defaulted && !ctor->is_inline_definition && ((init_category == ValueCategory::XValue && param->kind == pa11::TypeKind::RValueReference) ||
(init_category != ValueCategory::XValue && param->kind == pa11::TypeKind::LValueReference))) trivial_defaulted_match = true; else
declared_copy_or_move = true; } return declared_copy_or_move && !trivial_defaulted_match; }
bool Parser::parse_trailing_declarator_initializer(TypePtr declared_type,
                                                   Expr& init) {
if (consume(OP_ASS)) {
init = at(OP_LBRACE) ? parse_braced_init_list() : parse_expression();
init.copy_initialization = true; return true; }
if (consume(OP_LBRACE)) { --pos_; init = parse_braced_init_list(); return true; }
if (!at(OP_LPAREN) || declared_type->kind == pa11::TypeKind::Function) return false;
expect(OP_LPAREN); if (at(OP_RPAREN)) { expect(OP_RPAREN); return false; }
vector<Expr> args = parse_argument_list();
if (pa11::strip_cv(declared_type)->kind == pa11::TypeKind::Record) {
try { init = make_constructor_init_expr(declared_type, args, false); }
catch (const runtime_error& err) {
if (string(err.what()) != "no matching constructor" || args.size() != 1) throw;
TypePtr src_record = pa11::strip_cv(expression_object_type(args[0].type));
TypePtr dst_record = pa11::strip_cv(declared_type);
if (src_record->kind != pa11::TypeKind::Record || !pa11::same_type(src_record, dst_record)) throw;
ensure_copy_move_constructor(dst_record, args[0].category == ValueCategory::XValue);
init = args[0]; } }
else if (args.size() == 1) init = args[0];
else throw runtime_error("unsupported direct initializer");
expect(OP_RPAREN); return true; }
void Parser::apply_record_variable_initializer(Scope* target, Binding* variable, TypePtr type, const Expr& init,
Node& var) { Expr constructed; TypePtr src_record = pa11::strip_cv(expression_object_type(init.type));
TypePtr dst_record = pa11::strip_cv(type); bool same_record = src_record->kind == pa11::TypeKind::Record && (pa11::same_type(src_record, dst_record) ||
same_template_specialization_record(src_record, dst_record)); if (same_record && init.category == ValueCategory::PRValue) { constructed = init;
if (target->kind == ScopeKind::Class && !variable->is_static_member) default_member_initializers_[variable] = constructed.node; add_child(var, constructed.node); return;
} try { vector<Expr> args;
args.push_back(init); constructed = make_constructor_init_expr(type, args, init.copy_initialization);
} catch (const runtime_error& err) { if (string(err.what()) != "no matching constructor")
throw; Conversion conv = convert_to(init, type); if (conv.viable) {
if (dst_record->kind == pa11::TypeKind::Record && dst_record->fields.empty() && dst_record->base.get() == NULL && !record_has_aggregate_blocking_constructor(dst_record))
{ demand_empty_record_conversion_bodies(src_record, dst_record, conv.expr.node);
Binding* ctor = ensure_default_constructor(dst_record, true); if (ctor != NULL) add_child(var, default_constructor_action(variable, true)); else
add_child(var, Node("no-op-initializer")); return; } constructed = conv.expr;
if (target->kind == ScopeKind::Class && !variable->is_static_member) default_member_initializers_[variable] = constructed.node; add_child(var, constructed.node);
return; } if (!same_record) throw;
if (record_copy_move_initializer_blocked(dst_record, init.category)) throw; constructed = init; }
if (target->kind == ScopeKind::Class && !variable->is_static_member) default_member_initializers_[variable] = constructed.node; add_child(var, constructed.node); }
void Parser::apply_scalar_variable_initializer(const DeclSpecs& specs, Scope* target, Binding* variable, TypePtr type,
const Expr& init, Node& var) { bool allow_explicit = !init.copy_initialization;
if (allow_explicit) ++explicit_conversion_context_; Conversion conv; try
{ conv = convert_to(init, type); } catch (...)
{ if (allow_explicit) --explicit_conversion_context_; throw;
} if (allow_explicit) --explicit_conversion_context_; if (!conv.viable)
throw runtime_error("invalid initializer conversion"); if (conv.expr.has_constant_value && signed_integral_widening(init.type, type)) {
conv.expr.type = pa11::strip_top_level_cv(type); conv.expr.category = ValueCategory::PRValue; conv.expr.node.type = conv.expr.type; conv.expr.node.category = conv.expr.category;
annotate_expr_node(conv.expr); } if (target->kind == ScopeKind::Class && !variable->is_static_member) default_member_initializers_[variable] = conv.expr.node;
add_child(var, conv.expr.node); if ((specs.constexpr_decl || pa11::type_has_const(type)) && conv.expr.has_constant_value) {
variable->has_constant = true; variable->constant_value = conv.expr.constant_value; } else if (specs.constexpr_decl || pa11::type_has_const(type))
{ ConstexprValue value; if (try_evaluate_constexpr_expr(conv.expr.node, value) && !value.is_object &&
!value.is_pointer) { variable->has_constant = true; variable->constant_value = value.int_value;
} } if (specs.constexpr_decl && !variable->has_constant) {
ConstexprValue value; TypePtr bare = pa11::strip_cv(type); if (!conv.expr.dependent_value_name.empty()) return;
if (pa11::is_reference_type(type)) { if (conv.expr.binding != NULL) return;
if (try_evaluate_constexpr_expr(conv.expr.node, value) && (value.is_object || value.is_pointer)) return; }
if (bare->kind == pa11::TypeKind::Pointer && try_evaluate_constexpr_expr(conv.expr.node, value) && value.is_pointer) return;
throw runtime_error("constexpr initializer is not constant"); } } void Parser::apply_variable_initializer(const DeclSpecs& specs,
	Scope* target, Binding* variable, TypePtr type, const Expr* init,
	Node& var) { TypePtr target_record = pa11::strip_cv(type); bool lambda_closure_conversion = false;
	if (init != NULL && init->braced_init_list && init->node.token_text == "lambda-closure" &&
	    target_record->kind == pa11::TypeKind::Record) {
		TypePtr init_record = init->type.get() != NULL ? pa11::strip_cv(expression_object_type(init->type)) : TypePtr();
		lambda_closure_conversion = init_record.get() != NULL &&
			init_record->kind == pa11::TypeKind::Record &&
			!pa11::same_type(init_record, target_record);
	}
	if (init != NULL && init->copy_initialization &&
	target_record->kind == pa11::TypeKind::Record && !lambda_closure_conversion) validate_record_copy_initialization(type, *init); if (init != NULL) {
	if (init->braced_init_list && !lambda_closure_conversion) { apply_braced_variable_initializer(target, variable, type, *init, var); return;
	} if (target_record->kind == pa11::TypeKind::Record) { apply_record_variable_initializer(target, variable, type, *init, var);
	return; } if (string_literal_initializes_array(type, *init, NULL)) {
add_child(var, init->node); return; } apply_scalar_variable_initializer(specs, target, variable, type, *init, var);
	} else if (target->kind == ScopeKind::Class && !variable->is_static_member) { return;
	} else if (pa11::strip_cv(type)->kind == pa11::TypeKind::Record) { TypePtr record = pa11::strip_cv(type);
	if (record_has_aggregate_blocking_constructor(record)) { vector<Expr> args; Expr constructed = make_constructor_init_expr(type, args, false);
	if (constructed.node.direct_call != NULL && constructed.node.direct_call->is_defaulted &&
	    constructed.node.direct_call->type.get() != NULL && constructed.node.direct_call->type->kind == pa11::TypeKind::Function &&
	    constructed.node.direct_call->type->parameters.size() == 1) ensure_default_constructor(type);
	add_child(var, constructed.node); return; } if (ensure_default_constructor(type) != NULL)
	{ add_child(var, default_constructor_action(variable)); } } }
}  // namespace internal
}  // namespace pa12
