#include "pa12_internal.h"

#include <stdexcept>

using namespace std;

namespace pa12 {
namespace internal {

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
{
	Expr constructed;
	TypePtr src_record = pa11::strip_cv(expression_object_type(init.type));
	TypePtr dst_record = pa11::strip_cv(type);
	if (src_record->kind == pa11::TypeKind::Record &&
	    pa11::same_type(src_record, dst_record) &&
	    init.category == ValueCategory::PRValue)
	{
		constructed = init;
		if (target->kind == ScopeKind::Class && !variable->is_static_member)
			default_member_initializers_[variable] = constructed.node;
		add_child(var, constructed.node);
		return;
	}
	try
	{
		vector<Expr> args;
		args.push_back(init);
		constructed = make_constructor_init_expr(type, args, init.copy_initialization);
	}
	catch (const runtime_error& err)
	{
		if (string(err.what()) != "no matching constructor")
			throw;
		if (src_record->kind != pa11::TypeKind::Record ||
		    !pa11::same_type(src_record, dst_record))
			throw;
		bool declared_copy_or_move = false;
		bool trivial_defaulted_match = false;
		if (dst_record->scope != NULL)
		{
			map<string, vector<Binding*> >::const_iterator found =
				dst_record->scope->members.find(dst_record->scope->name);
			if (found != dst_record->scope->members.end())
				for (size_t i = 0; i < found->second.size(); ++i)
				{
					Binding* ctor = found->second[i];
					if (ctor->kind == BindingKind::Function &&
					    ctor->type->kind == pa11::TypeKind::Function &&
					    ctor->type->parameters.size() == 2 &&
					    pa11::is_reference_type(ctor->type->parameters[1]) &&
					    pa11::same_type(
						    pa11::strip_cv(ctor->type->parameters[1]->base),
						    dst_record))
					{
						TypePtr param = ctor->type->parameters[1];
						if (ctor->is_defaulted &&
						    !ctor->is_inline_definition &&
						    ((init.category == ValueCategory::XValue &&
						      param->kind == pa11::TypeKind::RValueReference) ||
						     (init.category != ValueCategory::XValue &&
						      param->kind == pa11::TypeKind::LValueReference)))
							trivial_defaulted_match = true;
						else
							declared_copy_or_move = true;
					}
				}
		}
		if (declared_copy_or_move && !trivial_defaulted_match)
			throw;
		constructed = init;
	}
	if (target->kind == ScopeKind::Class && !variable->is_static_member)
		default_member_initializers_[variable] = constructed.node;
	add_child(var, constructed.node);
}

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
	else if (pa11::strip_cv(type)->kind == pa11::TypeKind::Record &&
	         ensure_default_constructor(type) != NULL)
	{
		add_child(var, default_constructor_action(variable));
	}
}

}  // namespace internal
}  // namespace pa12
