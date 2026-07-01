#include "pa12_internal.h"
#include "pa12_templates_instance_support.h"

using namespace std;

namespace pa12 {
namespace internal {
namespace {

bool template_record_owner_name_match(TypePtr left, TypePtr right)
{
	left = left.get() != NULL ? pa11::strip_cv(left) : TypePtr();
	right = right.get() != NULL ? pa11::strip_cv(right) : TypePtr();
	if (left.get() == NULL ||
	    right.get() == NULL ||
	    left->kind != pa11::TypeKind::Record ||
	    right->kind != pa11::TypeKind::Record ||
	    left->name != right->name)
		return false;
	string left_primary = !left->template_primary_name.empty()
		? left->template_primary_name : left->name;
	string right_primary = !right->template_primary_name.empty()
		? right->template_primary_name : right->name;
	return left_primary == right_primary &&
	       (left->is_template_specialization ||
	        right->is_template_specialization);
}

map<Binding*, Node>::const_iterator find_static_member_initializer(
	const map<Binding*, Node>& initializers,
	Binding* binding)
{
	map<Binding*, Node>::const_iterator found = initializers.find(binding);
	if (found != initializers.end())
		return found;
	if (binding != NULL && binding->aliased_binding != NULL)
	{
		found = initializers.find(binding->aliased_binding);
		if (found != initializers.end())
			return found;
	}
	for (map<Binding*, Node>::const_iterator it = initializers.begin();
	     it != initializers.end();
	     ++it)
	{
		Binding* candidate = it->first;
		if (candidate == NULL ||
		    binding == NULL ||
		    candidate->name != binding->name)
			continue;
		bool same_owner = false;
		bool template_owner_match = false;
		same_owner = candidate->owner == binding->owner;
		if (!same_owner &&
		    candidate->owner != NULL &&
		    binding->owner != NULL &&
		    candidate->owner->kind == ScopeKind::Class &&
		    binding->owner->kind == ScopeKind::Class)
		{
			TypePtr candidate_record =
				pa11::record_type_for_scope(candidate->owner);
			TypePtr binding_record =
				pa11::record_type_for_scope(binding->owner);
			template_owner_match =
				candidate_record.get() != NULL &&
				binding_record.get() != NULL &&
				(same_template_record_type(candidate_record,
				                           binding_record) ||
				 template_record_owner_name_match(candidate_record,
				                                  binding_record));
			same_owner = template_owner_match;
		}
		TypePtr candidate_type =
			candidate->type.get() != NULL
			? pa11::strip_cv(candidate->type) : TypePtr();
		TypePtr binding_type =
			binding->type.get() != NULL
			? pa11::strip_cv(binding->type) : TypePtr();
		bool compatible_array_redeclaration =
			candidate_type.get() != NULL &&
			binding_type.get() != NULL &&
			candidate_type->kind == pa11::TypeKind::Array &&
			binding_type->kind == pa11::TypeKind::Array &&
			(candidate_type->unknown_bound ||
			 binding_type->unknown_bound ||
			 candidate_type->bound == binding_type->bound) &&
			pa11::same_type(candidate_type->base, binding_type->base);
		bool same_declared_type =
			candidate->type.get() != NULL &&
			binding->type.get() != NULL &&
			(pa11::same_type(candidate->type, binding->type) ||
			 compatible_array_redeclaration);
		if (!same_owner)
			continue;
		if (template_owner_match || same_declared_type)
			return it;
	}
	return initializers.end();
}

bool static_member_constant_usable(Binding* binding)
{
	return binding != NULL &&
	       binding->is_static_member &&
	       !binding->is_thread_local &&
	       (binding->is_constexpr || pa11::type_has_const(binding->type));
}

bool incomplete_template_object_error(const runtime_error& err)
{
	string message = err.what();
	return message == "incomplete object type" ||
	       message == "incomplete class type" ||
	       message == "incomplete array type";
}

void complete_static_member_array_type_from_initializer(Binding* variable,
                                                        Node& node,
                                                        Binding* source)
{
	TypePtr source_type =
		source != NULL && source->type.get() != NULL
		? pa11::strip_cv(source->type) : TypePtr();
	TypePtr variable_type =
		variable != NULL && variable->type.get() != NULL
		? pa11::strip_cv(variable->type) : TypePtr();
	if (source_type.get() == NULL ||
	    variable_type.get() == NULL ||
	    source_type->kind != pa11::TypeKind::Array ||
	    variable_type->kind != pa11::TypeKind::Array ||
	    !variable_type->unknown_bound ||
	    source_type->unknown_bound ||
	    !pa11::same_type(source_type->base, variable_type->base))
		return;
	variable->type = source->type;
	node.type = variable->type;
	node.line = "variable " + variable->name + " " +
	            pa11::describe_type(variable->type);
}

}  // namespace

void Parser::initialize_variable_declaration_flags(const DeclSpecs& specs,
                                                   Scope* target,
                                                   Binding* variable,
                                                   const QualifiedName& qname,
                                                   TypePtr type)
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
	variable->is_namespace_static =
		variable->is_namespace_static ||
		(specs.static_decl && target->kind == ScopeKind::Namespace);
	if (target->kind == ScopeKind::Namespace)
		variable->is_extern_declaration =
			variable->is_extern_declaration || specs.extern_decl;
	if (variable->is_local_static && !active_functions_.empty())
		variable->local_static_function_owner = active_functions_.back();
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
}

void Parser::finish_static_member_variable_initializer(
	Binding* variable,
	const Expr* init,
	Node& var,
	bool defer_static_template_member)
{
	if (init != NULL && !var.children.empty())
	{
		static_member_initializers_[variable] = var.children[0];
		ConstexprValue value;
		bool eval_ok = false;
		try
		{
			eval_ok = try_evaluate_constexpr_expr(var.children[0], value);
		}
		catch (const runtime_error& err)
		{
			if (!(defer_static_template_member &&
			      incomplete_template_object_error(err)))
				throw;
		}
		if (static_member_constant_usable(variable) &&
		    !variable->has_constant &&
		    eval_ok &&
		    !value.is_object &&
		    !value.is_pointer)
		{
			variable->has_constant = true;
			variable->constant_value = value.int_value;
		}
		if (!active_class_instantiations_.empty() &&
		    !active_class_instantiation_dependent() &&
		    pa11::strip_cv(variable->type)->kind == pa11::TypeKind::Array)
			extra_lowir_nodes_.push_back(var);
	}
	else if (init == NULL && var.children.empty())
	{
		map<Binding*, Node>::const_iterator found =
			find_static_member_initializer(static_member_initializers_,
			                               variable);
		if (found != static_member_initializers_.end())
		{
			complete_static_member_array_type_from_initializer(
				variable,
				var,
				found->first);
			add_child(var, found->second);
		}
	}
}

Binding* Parser::finish_variable_declaration(const DeclSpecs& specs,
                                             Scope* target,
                                             Binding* variable,
                                             const QualifiedName& qname,
                                             TypePtr type,
                                             const Expr* init,
                                             Node& out)
{
	initialize_variable_declaration_flags(specs, target, variable, qname, type);
	TypePtr object_type = pa11::strip_cv(type);
	while (object_type.get() != NULL &&
	       object_type->kind == pa11::TypeKind::Array)
		object_type = pa11::strip_cv(object_type->base);
	bool defer_static_template_member =
		variable->is_static_member &&
		target->kind == ScopeKind::Class &&
		!active_class_instantiations_.empty();
	if (!defer_static_template_member &&
	    object_type.get() != NULL &&
	    object_type->kind == pa11::TypeKind::Record)
	{
		mark_template_specialization_demanded(object_type);
		if (!type_is_template_dependent(object_type))
			complete_template_record(object_type);
	}
	if (!defer_static_template_member)
		ensure_default_destructor(type);
		Node var("variable " + qname.name + " " + pa11::describe_type(type));
	var.binding = variable;
	var.type = type;
	if ((specs.extern_decl || single_linkage_specification_declaration_) &&
	    target->kind == ScopeKind::Namespace &&
	    init == NULL)
		return variable;
	try
	{
		apply_variable_initializer(specs, target, variable, type, init, var);
	}
	catch (const runtime_error& err)
	{
		if (!(variable->is_static_member &&
		      target->kind == ScopeKind::Class &&
		      !active_class_instantiations_.empty() &&
		      incomplete_template_object_error(err)))
			throw;
	}
	if (variable->is_static_member)
		finish_static_member_variable_initializer(
			variable,
			init,
			var,
			defer_static_template_member);
	else if (variable->is_constexpr && !var.children.empty())
		static_member_initializers_[variable] = var.children[0];
	add_child(out, var);
	return variable;
}

void Parser::complete_static_member_initializer_replays(Node& node)
{
	if (node.binding != NULL &&
	    node.binding->is_static_member &&
	    node.children.empty() &&
	    node.line.compare(0, 9, "variable ") == 0)
	{
			map<Binding*, Node>::const_iterator found =
				find_static_member_initializer(static_member_initializers_,
				                               node.binding);
			if (found != static_member_initializers_.end())
			{
				complete_static_member_array_type_from_initializer(
					node.binding,
					node,
					found->first);
				add_child(node, found->second);
			}
		}
	if (node.binding != NULL &&
	    node.binding->is_static_member &&
	    static_member_constant_usable(node.binding) &&
	    !node.binding->has_constant &&
	    !node.children.empty() &&
	    node.line.compare(0, 9, "variable ") == 0)
	{
		ConstexprValue value;
		if (try_evaluate_constexpr_expr(node.children[0], value) &&
		    !value.is_object &&
		    !value.is_pointer)
		{
			node.binding->has_constant = true;
			node.binding->constant_value = value.int_value;
		}
	}
	for (size_t i = 0; i < node.children.size(); ++i)
		complete_static_member_initializer_replays(node.children[i]);
}

void Parser::complete_static_member_initializer_replays()
{
	complete_static_member_initializer_replays(root_);
	for (size_t i = 0; i < extra_lowir_nodes_.size(); ++i)
		complete_static_member_initializer_replays(extra_lowir_nodes_[i]);
}

}  // namespace internal
}  // namespace pa12
