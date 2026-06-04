#include "pa12_internal.h"

using namespace std;

namespace pa12 {
namespace internal {

Binding* Parser::finish_variable_declaration(const DeclSpecs& specs,
                                             Scope* target,
                                             Binding* variable,
                                             const QualifiedName& qname,
                                             TypePtr type,
                                             const Expr* init,
                                             Node& out)
{
	variable->language_linkage = current_language_linkage();
	variable->is_constexpr = variable->is_constexpr || specs.constexpr_decl;
	variable->is_static_member =
		variable->is_static_member ||
		(target->kind == ScopeKind::Class &&
		 (specs.static_decl || qname.qualifier != NULL));
	variable->is_local_static =
		variable->is_local_static ||
		(specs.static_decl &&
		 target->kind != ScopeKind::Namespace &&
		 target->kind != ScopeKind::Class);
	variable->is_thread_local =
		variable->is_thread_local || specs.thread_local_decl;
	if (target->kind == ScopeKind::Class)
	{
		TypePtr owner_record = pa11::record_type_for_scope(target);
		variable->is_dependent_template_artifact =
			owner_record.get() != NULL &&
			type_is_template_dependent(owner_record);
	}
	variable->is_mutable_member =
		target->kind == ScopeKind::Class && specs.mutable_decl;
	variable->is_private =
		target->kind == ScopeKind::Class &&
		!class_private_access_.empty() &&
		class_private_access_.back();
	variable->is_protected_member =
		target->kind == ScopeKind::Class &&
		!class_protected_access_.empty() &&
		class_protected_access_.back();
	if (target->kind == ScopeKind::Class)
	{
		TypePtr record = pa11::record_type_for_scope(target);
		if (record.get() != NULL)
			record->layout_valid = false;
	}
	ensure_default_destructor(type);
	Node var("variable " + qname.name + " " + pa11::describe_type(type));
	var.binding = variable;
	var.type = type;
	if (specs.extern_decl && target->kind == ScopeKind::Namespace && init == NULL)
		return variable;
	apply_variable_initializer(specs, target, variable, type, init, var);
	if (target->kind == ScopeKind::Class && variable->is_static_member)
	{
		if (init != NULL && !var.children.empty())
		{
			static_member_initializers_[variable] = var.children[0];
			if (!active_class_instantiations_.empty() &&
			    active_class_instantiations_.back().specialization_name.find(
				    "dependent") == string::npos &&
			    pa11::strip_cv(variable->type)->kind == pa11::TypeKind::Array)
				extra_lowir_nodes_.push_back(var);
		}
		else if (init == NULL && var.children.empty())
		{
			map<Binding*, Node>::const_iterator found =
				static_member_initializers_.find(variable);
			if (found != static_member_initializers_.end())
				add_child(var, found->second);
		}
	}
	else if (variable->is_constexpr && init != NULL && !var.children.empty())
		static_member_initializers_[variable] = var.children[0];
	add_child(out, var);
	return variable;
}

}  // namespace internal
}  // namespace pa12
