#include "pa12_internal.h"

#include <functional>
#include <stdexcept>

using namespace std;

namespace pa12 {
namespace internal {
namespace {

bool signed_integral_fundamental(TypePtr type)
{
	TypePtr bare = type.get() != NULL ? pa11::strip_cv(type) : TypePtr();
	if (bare.get() == NULL || bare->kind != pa11::TypeKind::Fundamental)
		return false;
	switch (bare->fundamental)
	{
	case FT_SIGNED_CHAR:
	case FT_SHORT_INT:
	case FT_INT:
	case FT_LONG_INT:
	case FT_LONG_LONG_INT:
		return true;
	default:
		return false;
	}
}

bool signed_integral_widening(TypePtr source, TypePtr target)
{
	TypePtr src_object = source;
	if (src_object->kind == pa11::TypeKind::LValueReference ||
	    src_object->kind == pa11::TypeKind::RValueReference)
		src_object = src_object->base;
	TypePtr dst_object = target;
	if (dst_object->kind == pa11::TypeKind::LValueReference ||
	    dst_object->kind == pa11::TypeKind::RValueReference)
		dst_object = dst_object->base;
	TypePtr src = pa11::strip_cv(src_object);
	TypePtr dst = pa11::strip_cv(dst_object);
	return signed_integral_fundamental(src) &&
	       signed_integral_fundamental(dst) &&
	       pa11::type_size(dst) >= pa11::type_size(src);
}

bool same_template_instance_argument(
	const pa11::TemplateInstanceArgument& left,
	const pa11::TemplateInstanceArgument& right)
{
	if (left.kind != right.kind ||
	    left.value != right.value ||
	    left.value_name != right.value_name ||
	    left.template_name != right.template_name ||
	    left.dependent != right.dependent ||
	    left.type.get() != right.type.get() ||
	    left.pack.size() != right.pack.size())
		return false;
	for (size_t i = 0; i < left.pack.size(); ++i)
		if (!same_template_instance_argument(left.pack[i], right.pack[i]))
			return false;
	return true;
}

bool same_template_specialization_record(TypePtr left, TypePtr right)
{
	TypePtr l = pa11::strip_cv(left);
	TypePtr r = pa11::strip_cv(right);
	if (l->kind != pa11::TypeKind::Record ||
	    r->kind != pa11::TypeKind::Record ||
	    !l->is_template_specialization ||
	    !r->is_template_specialization)
		return false;
	if (l->name == r->name)
		return true;
	if (l->template_primary_name.empty() ||
	    l->template_primary_name != r->template_primary_name ||
	    l->template_arguments.size() != r->template_arguments.size())
		return false;
	for (size_t i = 0; i < l->template_arguments.size(); ++i)
		if (!same_template_instance_argument(l->template_arguments[i],
		                                     r->template_arguments[i]))
			return false;
	return true;
}

}  // namespace

void Parser::apply_braced_variable_initializer(Scope* target,
                                               Binding* variable,
                                               TypePtr type,
                                               const Expr& init,
                                               Node& var)
{
	Node list = init.node;
	TypePtr record = pa11::strip_cv(type);
	if (record->kind != pa11::TypeKind::Record &&
	    record->kind != pa11::TypeKind::Array)
	{
		if (type_is_template_dependent(type))
		{
			list.line += " lvalue " + pa11::describe_type(type);
			list.type = type;
			if (target->kind == ScopeKind::Class && !variable->is_static_member)
				default_member_initializers_[variable] = list;
			add_child(var, list);
			return;
		}
		TypePtr init_object = init.type.get() == NULL
			? TypePtr() : pa11::strip_cv(expression_object_type(init.type));
		TypePtr target_object = pa11::strip_cv(type);
		if (init.node.children.empty() &&
		    (init_object.get() == NULL ||
		     pa11::same_type(init_object, target_object)))
		{
			Expr zero;
			zero.valid = true;
			zero.type = type;
			zero.category = ValueCategory::PRValue;
			zero.constant_expression = true;
			zero.has_constant_value = true;
			zero.constant_value = 0;
			zero.null_pointer_constant =
				pa11::strip_cv(type)->kind == pa11::TypeKind::Pointer;
			zero.node = Node("literal prvalue " +
			                 pa11::describe_type(type) + " 0");
			zero.node.token_text = "0";
			annotate_expr_node(zero);
			if (target->kind == ScopeKind::Class && !variable->is_static_member)
				default_member_initializers_[variable] = zero.node;
			add_child(var, zero.node);
			if (pa11::type_has_const(type))
			{
				variable->has_constant = true;
				variable->constant_value = 0;
			}
			return;
		}
			Conversion conv = convert_to(init, type);
			if (!conv.viable)
				throw runtime_error("invalid initializer conversion");
		if (target->kind == ScopeKind::Class && !variable->is_static_member)
			default_member_initializers_[variable] = conv.expr.node;
		add_child(var, conv.expr.node);
		if (pa11::type_has_const(type) && conv.expr.has_constant_value)
		{
			variable->has_constant = true;
			variable->constant_value = conv.expr.constant_value;
		}
		return;
	}
	if (record->kind == pa11::TypeKind::Record &&
	    record_has_aggregate_blocking_constructor(record))
	{
		vector<Expr> args;
		for (size_t i = 0; i < init.node.children.size(); ++i)
		{
			Expr arg;
			arg.valid = true;
			arg.node = init.node.children[i];
			arg.type = arg.node.type;
			arg.category = arg.node.category;
			arg.binding = arg.node.binding;
			args.push_back(arg);
		}
		try
		{
			Expr constructed =
				make_constructor_init_expr(type, args, init.copy_initialization);
			list = constructed.node;
		}
		catch (const runtime_error& err)
		{
			if (string(err.what()) != "no matching constructor")
				throw;
		}
	}
	if (record->kind == pa11::TypeKind::Record &&
	    init.node.children.empty() &&
	    record->base.get() != NULL)
	{
		Binding* ctor = ensure_default_constructor(record, true);
		if (ctor != NULL)
		{
			add_child(var, default_constructor_action(variable, true));
			return;
		}
	}
	if (record->kind == pa11::TypeKind::Record &&
	    init.node.children.empty() &&
	    record->fields.empty() &&
	    record->base.get() == NULL)
	{
		add_child(var, Node("no-op-initializer"));
		return;
	}
	ensure_aggregate_constructors_for_init(type, list);
	list.line += " lvalue " + pa11::describe_type(type);
	list.type = type;
	if (target->kind == ScopeKind::Class && !variable->is_static_member)
		default_member_initializers_[variable] = list;
	add_child(var, list);
}

void Parser::apply_record_variable_initializer(Scope* target,
                                               Binding* variable,
                                               TypePtr type,
                                               const Expr& init,
                                               Node& var)
{ Expr constructed; TypePtr src_record = pa11::strip_cv(expression_object_type(init.type)); TypePtr dst_record = pa11::strip_cv(type); if (src_record->kind == pa11::TypeKind::Record &&
(pa11::same_type(src_record, dst_record) || same_template_specialization_record(src_record, dst_record)) && init.category == ValueCategory::PRValue) { constructed = init;
if (target->kind == ScopeKind::Class && !variable->is_static_member) default_member_initializers_[variable] = constructed.node; add_child(var, constructed.node); return; } try { vector<Expr> args; args.push_back(init);
constructed = make_constructor_init_expr(type, args, init.copy_initialization); } catch (const runtime_error& err) { if (string(err.what()) != "no matching constructor") throw; Conversion conv = convert_to(init, type);
if (conv.viable) { if (dst_record->kind == pa11::TypeKind::Record && dst_record->fields.empty() && dst_record->base.get() == NULL && !record_has_aggregate_blocking_constructor(dst_record)) {
function<void(Binding*)> demand_body = [&](Binding* fn) { if (fn == NULL || fn->kind != BindingKind::Function) return; parse_pending_function_body(fn); parse_pending_member_body(fn); ensure_function_body_extra_node(fn);
}; function<void(Binding*)> demand_inline_without_object_root = [&](Binding* fn) { if (fn == NULL || fn->kind != BindingKind::Function) return; fn->is_object_root = false;
for (size_t i = 0; i < extra_lowir_nodes_.size(); ++i) if (extra_lowir_nodes_[i].binding == fn) extra_lowir_nodes_[i].token_text = "inline-object-root"; }; if (src_record->kind == pa11::TypeKind::Record &&
src_record->scope != NULL) { instantiate_member_function_templates(src_record, true); for (map<string, vector<Binding*> >::const_iterator it = src_record->scope->members.begin(); it != src_record->scope->members.end();
++it) { if (it->first.compare(0, 9, "operator ") != 0) continue; for (size_t i = 0; i < it->second.size(); ++i) { Binding* concrete = it->second[i]; if (concrete == NULL || concrete->kind != BindingKind::Function ||
concrete->type.get() == NULL || concrete->type->kind != pa11::TypeKind::Function || !pa11::same_type( pa11::strip_cv(concrete->type->base), dst_record)) continue; demand_body(concrete);
demand_inline_without_object_root(concrete); Binding* fn = concrete->aliased_binding; while (fn != NULL && fn->kind == BindingKind::Function) { demand_body(fn); demand_inline_without_object_root(fn);
fn = fn->aliased_binding; } } } } function<void(const Node&)> emit_direct_calls = [&](const Node& node) { if (node.direct_call != NULL) demand_body(node.direct_call); for (size_t i = 0; i < node.children.size(); ++i)
emit_direct_calls(node.children[i]); }; emit_direct_calls(conv.expr.node); Binding* ctor = ensure_default_constructor(dst_record, true); if (ctor != NULL) add_child(var, default_constructor_action(variable, true)); else
add_child(var, Node("no-op-initializer")); return; } constructed = conv.expr; if (target->kind == ScopeKind::Class && !variable->is_static_member) default_member_initializers_[variable] = constructed.node;
add_child(var, constructed.node); return; } if (src_record->kind != pa11::TypeKind::Record || (!pa11::same_type(src_record, dst_record) && !same_template_specialization_record(src_record, dst_record))) throw;
bool declared_copy_or_move = false; bool trivial_defaulted_match = false; if (dst_record->scope != NULL) { map<string, vector<Binding*> >::const_iterator found = dst_record->scope->members.find(dst_record->scope->name);
if (found != dst_record->scope->members.end()) for (size_t i = 0; i < found->second.size(); ++i) { Binding* ctor = found->second[i]; if (ctor->kind == BindingKind::Function &&
ctor->type->kind == pa11::TypeKind::Function && ctor->type->parameters.size() == 2 && pa11::is_reference_type(ctor->type->parameters[1]) && (pa11::same_type( pa11::strip_cv(ctor->type->parameters[1]->base),
dst_record) || same_template_specialization_record( ctor->type->parameters[1]->base, dst_record))) { TypePtr param = ctor->type->parameters[1]; if (ctor->is_defaulted && !ctor->is_inline_definition &&
((init.category == ValueCategory::XValue && param->kind == pa11::TypeKind::RValueReference) || (init.category != ValueCategory::XValue && param->kind == pa11::TypeKind::LValueReference))) trivial_defaulted_match = true;
else declared_copy_or_move = true; } } } if (declared_copy_or_move && !trivial_defaulted_match) throw; constructed = init; } if (target->kind == ScopeKind::Class && !variable->is_static_member)
default_member_initializers_[variable] = constructed.node; add_child(var, constructed.node); }

void Parser::apply_scalar_variable_initializer(const DeclSpecs& specs,
                                               Scope* target,
                                               Binding* variable,
                                               TypePtr type,
                                               const Expr& init,
                                               Node& var)
{
	Conversion conv = convert_to(init, type);
	if (!conv.viable)
		throw runtime_error("invalid initializer conversion");
	if (conv.expr.has_constant_value &&
	    signed_integral_widening(init.type, type))
	{
		conv.expr.type = pa11::strip_top_level_cv(type);
		conv.expr.category = ValueCategory::PRValue;
		conv.expr.node.type = conv.expr.type;
		conv.expr.node.category = conv.expr.category;
		annotate_expr_node(conv.expr);
	}
	if (target->kind == ScopeKind::Class && !variable->is_static_member)
		default_member_initializers_[variable] = conv.expr.node;
	add_child(var, conv.expr.node);
	if ((specs.constexpr_decl || pa11::type_has_const(type)) &&
	    conv.expr.has_constant_value)
	{
		variable->has_constant = true;
		variable->constant_value = conv.expr.constant_value;
	}
	else if (specs.constexpr_decl || pa11::type_has_const(type))
	{
		ConstexprValue value;
		if (try_evaluate_constexpr_expr(conv.expr.node, value) &&
		    !value.is_object &&
		    !value.is_pointer)
		{
			variable->has_constant = true;
			variable->constant_value = value.int_value;
		}
	}
	if (specs.constexpr_decl && !variable->has_constant)
	{
		ConstexprValue value;
		TypePtr bare = pa11::strip_cv(type);
		if (!conv.expr.dependent_value_name.empty())
			return;
		if (pa11::is_reference_type(type))
		{
			if (conv.expr.binding != NULL)
				return;
			if (try_evaluate_constexpr_expr(conv.expr.node, value) &&
			    (value.is_object || value.is_pointer))
				return;
		}
		if (bare->kind == pa11::TypeKind::Pointer &&
		    try_evaluate_constexpr_expr(conv.expr.node, value) &&
		    value.is_pointer)
			return;
		throw runtime_error("constexpr initializer is not constant");
	}
}

void Parser::apply_variable_initializer(const DeclSpecs& specs,
                                        Scope* target,
                                        Binding* variable,
                                        TypePtr type,
                                        const Expr* init,
                                        Node& var)
{
	if (init != NULL &&
	    init->copy_initialization &&
	    pa11::strip_cv(type)->kind == pa11::TypeKind::Record)
		validate_record_copy_initialization(type, *init);
	if (init != NULL)
	{
		if (init->braced_init_list)
		{
			apply_braced_variable_initializer(target, variable, type, *init, var);
			return;
		}
		if (pa11::strip_cv(type)->kind == pa11::TypeKind::Record)
		{
			apply_record_variable_initializer(target, variable, type, *init, var);
			return;
		}
		if (string_literal_initializes_array(type, *init, NULL))
		{
			add_child(var, init->node);
			return;
		}
		apply_scalar_variable_initializer(specs, target, variable, type, *init, var);
	}
	else if (target->kind == ScopeKind::Class && !variable->is_static_member)
	{
		return;
	}
	else if (pa11::strip_cv(type)->kind == pa11::TypeKind::Record)
	{
		TypePtr record = pa11::strip_cv(type);
		if (record_has_aggregate_blocking_constructor(record))
		{
			vector<Expr> args;
			Expr constructed = make_constructor_init_expr(type, args, false);
			add_child(var, constructed.node);
			return;
		}
		if (ensure_default_constructor(type) != NULL)
			add_child(var, default_constructor_action(variable));
	}
}

}  // namespace internal
}  // namespace pa12
