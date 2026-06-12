#include "pa12_internal.h"

#include <stdexcept>

using namespace std;

namespace pa12 {
namespace internal {

bool Parser::is_pointer_arithmetic(const Expr& lhs, const Expr& rhs) const
{
	TypePtr left = lvalue_to_rvalue_type(lhs.type);
	TypePtr right = lvalue_to_rvalue_type(rhs.type);
	return (pa11::strip_cv(left)->kind == pa11::TypeKind::Pointer &&
	        pa11::is_integral_or_bool_type(right)) ||
	       (pa11::strip_cv(right)->kind == pa11::TypeKind::Pointer &&
	        pa11::is_integral_or_bool_type(left));
}

bool Parser::is_pointer_difference(const Expr& lhs, const Expr& rhs) const
{
	return pa11::strip_cv(lvalue_to_rvalue_type(lhs.type))->kind ==
	           pa11::TypeKind::Pointer &&
	       pa11::strip_cv(lvalue_to_rvalue_type(rhs.type))->kind ==
	           pa11::TypeKind::Pointer;
}

TypePtr Parser::pointer_arithmetic_type(ETokenType op,
                                        const Expr& lhs,
                                        const Expr& rhs) const
{
	(void)op;
	TypePtr left = lvalue_to_rvalue_type(lhs.type);
	TypePtr right = lvalue_to_rvalue_type(rhs.type);
	if (pa11::strip_cv(left)->kind == pa11::TypeKind::Pointer)
		return left;
	return right;
}

TypePtr Parser::pointee_type_for_member(TypePtr type) const
{
	TypePtr bare = pa11::strip_cv(expression_object_type(type));
	if (bare->kind != pa11::TypeKind::Pointer)
		throw runtime_error("arrow on non-pointer");
	return bare->base;
}

Expr Parser::make_address_expr(const string& text, Expr inner)
{
	if (!inner.pack_expansion &&
	    inner.binding != NULL &&
	    inner.binding->kind == BindingKind::Function &&
	    inner.binding->owner != NULL &&
	    inner.binding->owner->kind == ScopeKind::Class)
		{
			TypePtr owner_record = pa11::record_type_for_scope(inner.binding->owner);
			owner_record = owner_record.get() == NULL ? TypePtr()
				: pa11::strip_cv(owner_record);
			map<const void*, vector<TemplateArgument> >::const_iterator args_it =
				owner_record.get() == NULL ? record_template_arguments_.end()
				: record_template_arguments_.find(owner_record.get());
			map<const void*, TemplateDeclaration*>::const_iterator decl_it =
				owner_record.get() == NULL ? record_template_declarations_.end()
				: record_template_declarations_.find(owner_record.get());
		string pack_name;
		TemplateArgument pack_subst;
		bool owner_has_pack = false;
		if (args_it != record_template_arguments_.end() &&
		    decl_it != record_template_declarations_.end())
			for (size_t i = 0; i < args_it->second.size(); ++i)
				if (args_it->second[i].kind == TemplateArgumentKind::Type &&
				    args_it->second[i].type.get() != NULL &&
					    template_type_has_template_parameter_name(
						    args_it->second[i].type, pack_name) &&
					    find_template_value_substitution(pack_name, pack_subst) &&
				    pack_subst.kind == TemplateArgumentKind::Pack)
				{
					owner_has_pack = true;
					break;
				}
		if (owner_has_pack)
		{
			vector<TemplateArgument> explicit_args;
			if (!inner.explicit_template_arguments.empty())
				explicit_args = inner.explicit_template_arguments.begin()->second;
			Expr out;
			out.valid = true;
			out.pack_expansion = true;
			out.category = ValueCategory::PRValue;
			out.node = Node("pack-expression address");
			for (size_t i = 0; i < pack_subst.pack.size(); ++i)
			{
				if (pack_subst.pack[i].kind != TemplateArgumentKind::Type)
					throw runtime_error("type pack required");
				vector<TemplateArgument> owner_args;
				for (size_t j = 0; j < args_it->second.size(); ++j)
				{
					if (args_it->second[j].kind == TemplateArgumentKind::Pack)
					{
						owner_args.push_back(pack_subst.pack[i]);
						continue;
					}
					owner_args.push_back(
						substitute_template_argument_type_parameter(
							args_it->second[j],
							pack_name,
							pack_subst.pack[i].type));
				}
				TypePtr element_owner =
					instantiate_class_template(decl_it->second, owner_args);
				element_owner = pa11::strip_cv(element_owner);
				vector<TemplateDeclaration*> templates;
					map<Scope*, map<string, vector<TemplateDeclaration*> > >::iterator
						sit = function_templates_.find(element_owner->scope);
				if (sit != function_templates_.end())
				{
					map<string, vector<TemplateDeclaration*> >::iterator fit =
						sit->second.find(inner.binding->name);
					if (fit != sit->second.end())
						templates = fit->second;
				}
					if (templates.empty())
					{
						map<pair<TemplateDeclaration*, string>,
						    vector<TemplateDeclaration*> >::iterator mit =
							member_function_templates_.find(
								make_pair(decl_it->second, inner.binding->name));
						if (mit != member_function_templates_.end())
							templates = mit->second;
					}
							if (templates.empty())
								throw runtime_error("function template not found");
				Binding* selected = NULL;
				for (size_t j = 0; j < templates.size(); ++j)
				{
					vector<TemplateArgument> full_args;
					try
					{
						full_args = complete_template_arguments(
							templates[j],
							explicit_args);
						selected = instantiate_function_template(
							templates[j],
							full_args);
						break;
					}
					catch (const runtime_error&)
					{
					}
				}
						if (selected == NULL)
							throw runtime_error("function template not found");
				Expr elem_inner;
				elem_inner.valid = true;
				elem_inner.binding = selected;
				elem_inner.type = selected->type;
				elem_inner.category = ValueCategory::LValue;
				elem_inner.node = Node("id-expression lvalue " +
				                       pa11::describe_type(selected->type) +
				                       " " + qualified_decl_name(selected));
				elem_inner.node.binding = selected;
				annotate_expr_node(elem_inner);
				Expr elem = make_address_expr(text, elem_inner);
				if (i == 0)
					out.type = elem.type;
				out.pack.push_back(elem);
				add_child(out.node, elem.node);
			}
			if (pack_subst.pack.empty())
				out.type = inner.type;
			annotate_expr_node(out);
			return out;
		}
	}
	if (!inner.pack_expansion &&
	    inner.binding != NULL &&
	    inner.binding->kind == BindingKind::Function &&
	    unevaluated_expression_depth_ == 0)
	{
		parse_pending_function_body(inner.binding);
		parse_pending_member_body(inner.binding);
	}
	Expr out;
	out.valid = true;
	out.category = ValueCategory::PRValue;
	out.overloads = inner.overloads;
	out.explicit_template_arguments = inner.explicit_template_arguments;
	bool bound_member_access =
		inner.node.has_op &&
		(inner.node.op == OP_DOT || inner.node.op == OP_ARROW) &&
		!inner.node.suppress_virtual_dispatch;
	bool class_scope_member_id =
		inner.node.line.compare(0, 13, "id-expression") == 0 &&
		inner.binding != NULL &&
		inner.binding->owner != NULL &&
		inner.binding->owner->kind == ScopeKind::Class &&
		inner.binding->kind == BindingKind::Variable &&
		!inner.binding->is_static_member &&
		inner.node.token_text == inner.binding->name &&
		(current_scope() == inner.binding->owner ||
		 unevaluated_expression_depth_ > 0);
	if (inner.binding == NULL)
	{
		out.dependent_value_name = inner.dependent_value_name;
		out.dependent_value_owner_template_name =
			inner.dependent_value_owner_template_name;
		out.dependent_value_member_name =
			inner.dependent_value_member_name;
		out.dependent_value_negated = inner.dependent_value_negated;
		out.dependent_value_owner_template_arguments =
			inner.dependent_value_owner_template_arguments;
	}
	if (inner.binding != NULL &&
	    inner.binding->owner != NULL &&
	    inner.binding->owner->kind == ScopeKind::Class &&
	    !inner.binding->is_static_member &&
	    inner.binding->type->kind == pa11::TypeKind::Function)
	{
		if (bound_member_access)
			throw runtime_error("address of bound member function");
		TypePtr fn = inner.binding->type;
		TypePtr this_type = fn->parameters.empty() ? TypePtr() : fn->parameters[0];
		TypePtr class_type = this_type.get() == NULL ? TypePtr() :
			pa11::strip_cv(pa11::strip_cv(this_type)->base);
		vector<TypePtr> params;
		for (size_t i = 1; i < fn->parameters.size(); ++i)
			params.push_back(fn->parameters[i]);
		TypePtr member_fn = pa11::make_function(fn->base, params, fn->variadic);
		if (this_type.get() != NULL &&
		    pa11::strip_cv(this_type)->kind == pa11::TypeKind::Pointer)
			member_fn->cv = pa11::strip_cv(this_type)->base->kind ==
				pa11::TypeKind::Cv ? this_type->base->cv : pa11::CV_NONE;
		out.type = pa11::make_member_pointer(class_type, member_fn);
	}
	else if (inner.binding != NULL &&
	         inner.binding->owner != NULL &&
	     inner.binding->owner->kind == ScopeKind::Class &&
	     !inner.binding->is_static_member &&
	     inner.binding->kind == BindingKind::Variable &&
	     !bound_member_access &&
	     !class_scope_member_id)
	{
		if (inner.binding->is_bit_field)
			throw runtime_error("address of bit-field");
		TypePtr class_type = pa11::record_type_for_scope(inner.binding->owner);
		out.type = pa11::make_member_pointer(
			class_type,
			expression_object_type(inner.binding->type));
		out.binding = inner.binding;
	}
	else if (inner.binding != NULL &&
	         inner.binding->owner != NULL &&
	         inner.binding->owner->kind == ScopeKind::Class &&
	         !inner.binding->is_static_member &&
	         inner.binding->kind == BindingKind::Variable &&
	         inner.binding->is_bit_field)
		throw runtime_error("address of bit-field");
	else if (inner.type->kind == pa11::TypeKind::Function)
	{
		out.type = pa11::make_pointer(inner.type);
		out.binding = inner.binding;
	}
	else
		out.type = pa11::make_pointer(expression_object_type(inner.type));
	out.node = Node("unary-expression prvalue " + pa11::describe_type(out.type) +
	                " OP_AMP:" + text);
	add_child(out.node, inner.node);
	out.node.has_op = true;
	out.node.op = OP_AMP;
	out.node.token_text = text;
	annotate_expr_node(out);
	return out;
}

Expr Parser::make_deref_expr(const string& text, Expr inner)
{
	TypePtr object = expression_object_type(inner.type);
	TypePtr bare = pa11::strip_cv(object);
	if (bare->kind == pa11::TypeKind::Pointer)
		object = bare->base;
	else if (bare->kind == pa11::TypeKind::Array)
		object = bare->base;
	else if (type_is_template_dependent(object))
		object = pa11::make_dependent_typename_type("__dependent_deref",
		                                            false,
		                                            false,
		                                            false);
	else
		throw runtime_error("deref of non-pointer");
	Expr out;
	out.type = object;
	out.category = ValueCategory::LValue;
	out.valid = true;
	out.node = Node("unary-expression lvalue " + pa11::describe_type(object) +
	                " OP_STAR:" + text);
	add_child(out.node, inner.node);
	out.node.has_op = true;
	out.node.op = OP_STAR;
	out.node.token_text = text;
	annotate_expr_node(out);
	return out;
}

}  // namespace internal
}  // namespace pa12
