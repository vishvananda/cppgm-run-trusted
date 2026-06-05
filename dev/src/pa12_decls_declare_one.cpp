#include "pa12_internal.h"

using namespace std;

namespace pa12 {
namespace internal {
namespace {

bool array_redeclaration_compatible(TypePtr existing, TypePtr redeclared)
{
	TypePtr lhs = pa11::strip_cv(existing);
	TypePtr rhs = pa11::strip_cv(redeclared);
	if (lhs->kind == pa11::TypeKind::Array && rhs->kind == pa11::TypeKind::Array)
	{
		if (!lhs->unknown_bound && !rhs->unknown_bound &&
		    lhs->bound != rhs->bound)
			return false;
		return array_redeclaration_compatible(lhs->base, rhs->base);
	}
	return pa11::same_type(lhs, rhs);
}

}  // namespace

Binding* Parser::declare_one(const DeclSpecs& specs,
                             TypePtr base,
                             const Declarator& declarator,
                             const Expr* init,
                             bool function_definition,
                             Node& out)
{
	const QualifiedName& qname = declarator_name(declarator);
	Scope* target = qname.qualifier != NULL ? qname.qualifier : current_scope();
	Scope* friend_class_scope =
		specs.friend_decl && current_scope()->kind == ScopeKind::Class
		? current_scope() : NULL;
	bool hidden_friend =
		friend_class_scope != NULL && qname.qualifier == NULL;
	if (friend_class_scope != NULL && qname.qualifier == NULL)
		target = nearest_namespace_scope(friend_class_scope);
	TypePtr type = apply_declarator(declarator, base);
	if (specs.typedef_decl)
	{
		Binding* alias = add_alias(target, qname.name, type);
		add_child(out, Node("type-alias " + qname.name + " " +
		                    pa11::describe_type(alias->type)));
		return alias;
	}

	if (specs.constexpr_decl &&
	    !pa11::is_reference_type(type) &&
	    type->kind != pa11::TypeKind::Function)
		type = pa11::make_cv(type, pa11::CV_CONST);
	if (init != NULL &&
	    init->braced_init_list &&
	    type->kind == pa11::TypeKind::Array &&
	    type->unknown_bound)
		type = pa11::make_array(type->base, false, init->node.children.size());
	if (init != NULL && type->kind == pa11::TypeKind::Array && type->unknown_bound)
	{
		uint64_t elements = 0;
		if (string_literal_initializes_array(type, *init, &elements))
			type = pa11::make_array(type->base, false, elements);
	}
	bool existing_static_member_function = false;
	if (target->kind == ScopeKind::Class &&
	    type->kind == pa11::TypeKind::Function &&
	    !specs.static_decl)
	{
		map<string, vector<Binding*> >::iterator found =
			target->members.find(qname.name);
		if (found != target->members.end())
			for (size_t i = 0; i < found->second.size(); ++i)
			{
				Binding* candidate = found->second[i];
				if (candidate->kind == BindingKind::Function &&
				    candidate->is_static_member &&
				    pa11::same_type(candidate->type, type))
				{
					existing_static_member_function = true;
					break;
				}
			}
	}
	bool nonstatic_member_function =
		target->kind == ScopeKind::Class &&
		type->kind == pa11::TypeKind::Function &&
		!specs.static_decl &&
		!existing_static_member_function;
	if (nonstatic_member_function)
		type = make_member_function_type(target, type);
	if (type->kind == pa11::TypeKind::Function || function_definition)
	{
		Binding* function =
			declare_function_entity(specs,
			                        target,
			                        qname.name,
			                        type,
			                        declarator,
			                        function_definition,
			                        nonstatic_member_function,
			                        hidden_friend,
			                        out);
		if (specs.friend_decl && friend_class_scope != NULL)
			add_friend_function(friend_class_scope, function);
		return function;
	}

	Binding* variable = NULL;
	if ((target->kind == ScopeKind::Namespace ||
	     target->kind == ScopeKind::Class) &&
	    (qname.qualifier != NULL || target->kind == ScopeKind::Namespace))
	{
		Binding* existing =
			pa11::find_owned_binding(target, qname.name, BindingKind::Variable);
		if (existing != NULL &&
		    (pa11::same_type(existing->type, type) ||
		     array_redeclaration_compatible(existing->type, type)))
		{
			variable = existing;
			type = existing->type;
		}
	}
	if (variable == NULL)
		variable = add_value(target, BindingKind::Variable, qname.name, type);
	if (target->kind == ScopeKind::Class &&
	    pa11::is_reference_type(pa11::strip_cv(type)))
		variable->is_reference_member = true;
	return finish_variable_declaration(specs,
	                                   target,
	                                   variable,
	                                   qname,
	                                   type,
	                                   init,
	                                   out);
}

}  // namespace internal
}  // namespace pa12
