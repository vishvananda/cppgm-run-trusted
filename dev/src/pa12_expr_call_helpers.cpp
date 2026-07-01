#include "pa12_expr_semantics_support.h"
#include "pa12_types_support.h"

#include <algorithm>
#include <memory>
#include <stdexcept>

using namespace std;

namespace pa12 {
namespace internal {
namespace {

bool is_function_pointer(TypePtr type)
{
	TypePtr bare = pa11::strip_cv(type);
	return bare->kind == pa11::TypeKind::Pointer &&
	       bare->base->kind == pa11::TypeKind::Function;
}

bool is_function_reference(TypePtr type)
{
	return (type->kind == pa11::TypeKind::LValueReference ||
	        type->kind == pa11::TypeKind::RValueReference) &&
	       pa11::strip_cv(type->base)->kind == pa11::TypeKind::Function;
}

bool concrete_outer_template_substitutions(
	const TemplateDeclaration* declaration)
{
	if (declaration == NULL ||
	    (declaration->outer_type_substitutions.empty() &&
	     declaration->outer_value_substitutions.empty()))
		return false;
	for (size_t i = 0; i < declaration->outer_type_substitutions.size(); ++i)
		for (map<string, TypePtr>::const_iterator it =
			     declaration->outer_type_substitutions[i].begin();
		     it != declaration->outer_type_substitutions[i].end();
		     ++it)
			if (type_structurally_dependent(it->second))
				return false;
	for (size_t i = 0; i < declaration->outer_value_substitutions.size(); ++i)
		for (map<string, TemplateArgument>::const_iterator it =
			     declaration->outer_value_substitutions[i].begin();
		     it != declaration->outer_value_substitutions[i].end();
		     ++it)
			if (it->second.dependent)
				return false;
	return true;
}

bool is_member_function_pointer(TypePtr type)
{
	TypePtr bare = pa11::strip_cv(type);
	return bare->kind == pa11::TypeKind::MemberPointer &&
	       bare->base.get() != NULL &&
	       bare->base->kind == pa11::TypeKind::Function;
}

bool template_parameter_lists_match_local(
	const vector<TemplateParameterInfo>& left,
	const vector<TemplateParameterInfo>& right)
{
	if (left.size() != right.size())
		return false;
	for (size_t i = 0; i < left.size(); ++i)
	{
		if (left[i].kind != right[i].kind ||
		    left[i].is_pack != right[i].is_pack ||
		    left[i].template_parameters.size() !=
			    right[i].template_parameters.size())
			return false;
		for (size_t j = 0; j < left[i].template_parameters.size(); ++j)
			if (left[i].template_parameters[j].kind !=
				    right[i].template_parameters[j].kind ||
			    left[i].template_parameters[j].is_pack !=
				    right[i].template_parameters[j].is_pack)
				return false;
	}
	return true;
}

bool same_function_template_signature_type(TypePtr left, TypePtr right)
{
	if (left.get() == NULL || right.get() == NULL)
		return left.get() == right.get();
	if (left->kind == pa11::TypeKind::TemplateParameter &&
	    right->kind == pa11::TypeKind::TemplateParameter)
		return true;
	if (pa11::same_type(left, right))
		return true;
	if (left->kind != right->kind)
		return false;
	switch (left->kind)
	{
	case pa11::TypeKind::Cv:
		return left->cv == right->cv &&
		       same_function_template_signature_type(left->base,
		                                             right->base);
	case pa11::TypeKind::Pointer:
	case pa11::TypeKind::LValueReference:
	case pa11::TypeKind::RValueReference:
		return same_function_template_signature_type(left->base,
		                                             right->base);
	case pa11::TypeKind::Array:
		return left->unknown_bound == right->unknown_bound &&
		       left->bound == right->bound &&
		       same_function_template_signature_type(left->base,
		                                             right->base);
	case pa11::TypeKind::Function:
		if (left->cv != right->cv ||
		    left->variadic != right->variadic ||
		    left->parameters.size() != right->parameters.size() ||
		    !same_function_template_signature_type(left->base,
		                                           right->base))
			return false;
		for (size_t i = 0; i < left->parameters.size(); ++i)
			if (!same_function_template_signature_type(
				    left->parameters[i],
				    right->parameters[i]))
				return false;
		return true;
	case pa11::TypeKind::MemberPointer:
		return same_function_template_signature_type(left->member_class,
		                                             right->member_class) &&
		       same_function_template_signature_type(left->base,
		                                             right->base);
	default:
		return false;
	}
}

bool replacement_template_signature_component_compatible(TypePtr left,
                                                        TypePtr right)
{
	return same_function_template_signature_type(left, right) ||
	       type_structurally_dependent(left) ||
	       type_structurally_dependent(right);
}

bool replacement_member_function_template_signature_compatible(TypePtr left,
                                                              TypePtr right)
{
	if (left.get() == NULL || right.get() == NULL)
		return left.get() == right.get();
	if (left->kind != pa11::TypeKind::Function ||
	    right->kind != pa11::TypeKind::Function)
		return replacement_template_signature_component_compatible(left,
		                                                           right);
	if (left->cv != right->cv ||
	    left->variadic != right->variadic ||
	    left->parameters.size() != right->parameters.size() ||
	    !replacement_template_signature_component_compatible(left->base,
	                                                         right->base))
		return false;
	for (size_t i = 0; i < left->parameters.size(); ++i)
		if (!replacement_template_signature_component_compatible(
			    left->parameters[i],
			    right->parameters[i]))
			return false;
	return true;
}

TypePtr member_function_pointer_type(Binding* binding)
{
	if (binding == NULL ||
	    binding->owner == NULL ||
	    binding->owner->kind != ScopeKind::Class ||
	    binding->type.get() == NULL ||
	    binding->type->kind != pa11::TypeKind::Function ||
	    binding->type->parameters.empty())
		return TypePtr();
	TypePtr this_type = binding->type->parameters[0];
	TypePtr class_type = this_type.get() == NULL ? TypePtr() :
		pa11::strip_cv(pa11::strip_cv(this_type)->base);
	vector<TypePtr> params;
	for (size_t i = 1; i < binding->type->parameters.size(); ++i)
		params.push_back(binding->type->parameters[i]);
	TypePtr member_fn =
		pa11::make_function(binding->type->base,
		                    params,
		                    binding->type->variadic);
	if (this_type.get() != NULL &&
	    pa11::strip_cv(this_type)->kind == pa11::TypeKind::Pointer)
		member_fn->cv = pa11::strip_cv(this_type)->base->kind ==
			pa11::TypeKind::Cv ? this_type->base->cv : pa11::CV_NONE;
	member_fn->ref_qualifier = binding->ref_qualifier;
	return pa11::make_member_pointer(class_type, member_fn);
}

TypePtr replacement_owner_record(TemplateDeclaration* declaration)
{
	if (declaration == NULL)
		return TypePtr();
	TypePtr owner_record =
		declaration->placeholder != NULL &&
		declaration->placeholder->owner != NULL &&
		declaration->placeholder->owner->kind == ScopeKind::Class
		? pa11::record_type_for_scope(declaration->placeholder->owner)
		: (declaration->owner != NULL &&
		   declaration->owner->kind == ScopeKind::Class
		   ? pa11::record_type_for_scope(declaration->owner) : TypePtr());
	return owner_record.get() != NULL
		? pa11::strip_cv(owner_record) : TypePtr();
}

}  // namespace

TemplateDeclaration* Parser::replacement_owner_template(
	TypePtr owner_record) const
{
	TemplateDeclaration* owner_template =
		class_template_declaration_for_match(owner_record);
	if (owner_template != NULL || owner_record.get() == NULL)
		return owner_template;
	map<const void*, TemplateDeclaration*>::const_iterator found =
		record_template_declarations_.find(owner_record.get());
	return found != record_template_declarations_.end()
		? found->second : NULL;
}

TemplateDeclaration* Parser::replacement_member_function_template_definition(
	TemplateDeclaration* declaration,
	TypePtr owner_record,
	TemplateDeclaration* owner_template,
	bool declaration_has_body)
{
	if (owner_template == NULL ||
	    (declaration_has_body && !declaration->class_template_member))
		return NULL;
	bool prefer_concrete_owner =
		owner_record.get() != NULL &&
		owner_record->kind == pa11::TypeKind::Record &&
		owner_record->is_template_specialization &&
		!type_structurally_dependent(owner_record);
	TemplateDeclaration* fallback_replacement = NULL;
	map<pair<TemplateDeclaration*, string>,
	    vector<TemplateDeclaration*> >::iterator mit =
		member_function_templates_.find(
			make_pair(owner_template, declaration->name));
	if (mit != member_function_templates_.end())
	{
		for (size_t j = 0; j < mit->second.size(); ++j)
		{
			TemplateDeclaration* replacement = mit->second[j];
			bool same_template_parameters =
				replacement != NULL &&
				template_parameter_lists_match_local(
					replacement->parameters,
					declaration->parameters);
			bool same_signature =
				replacement != NULL &&
				replacement->generic_function_type.get() != NULL &&
				same_function_template_signature_type(
					replacement->generic_function_type,
					declaration->generic_function_type);
			bool same_arity = false;
			if (replacement != NULL &&
			    replacement->generic_function_type.get() != NULL &&
			    declaration->generic_function_type.get() != NULL &&
			    replacement->generic_function_type->kind ==
				    pa11::TypeKind::Function &&
			    declaration->generic_function_type->kind ==
				    pa11::TypeKind::Function)
				same_arity =
					replacement->generic_function_type
						->parameters.size() ==
					declaration->generic_function_type
						->parameters.size();
			bool compatible =
				same_signature ||
				(replacement != NULL &&
				 declaration->class_template_member &&
				 replacement->class_template_member &&
				 same_template_parameters &&
				 same_arity &&
				 replacement_member_function_template_signature_compatible(
					 replacement->generic_function_type,
					 declaration->generic_function_type));
			if (replacement == declaration ||
			    !template_declaration_has_body(declaration_tokens_,
			                                   replacement) ||
			    replacement->generic_function_type.get() == NULL ||
			    !compatible)
				continue;
			if (!same_signature)
			{
				TemplateDeclaration* result = NULL;
				for (size_t ti = 0; ti < template_declarations_.size(); ++ti)
				{
					TemplateDeclaration* candidate =
						template_declarations_[ti].get();
					if (candidate != NULL &&
					    candidate != replacement &&
					    candidate->name == replacement->name &&
					    candidate->owner == replacement->owner &&
					    candidate->decl_begin ==
						    replacement->decl_begin &&
					    candidate->decl_end ==
						    replacement->decl_end &&
					    candidate->placeholder ==
						    declaration->placeholder &&
					    candidate->generic_function_type.get() != NULL &&
					    same_function_template_signature_type(
						    candidate->generic_function_type,
						    declaration->generic_function_type))
					{
						result = candidate;
						break;
					}
				}
				if (result != NULL)
					return result;
				unique_ptr<TemplateDeclaration> adjusted(
					new TemplateDeclaration(*replacement));
				adjusted->generic_function_type =
					declaration->generic_function_type;
				adjusted->placeholder = declaration->placeholder;
				adjusted->function_parameter_names =
					declaration->function_parameter_names;
				result = adjusted.get();
				template_declarations_.push_back(std::move(adjusted));
				if (prefer_concrete_owner &&
				    !concrete_outer_template_substitutions(result))
				{
					if (fallback_replacement == NULL)
						fallback_replacement = result;
					continue;
				}
				return result;
			}
			if (prefer_concrete_owner &&
			    !concrete_outer_template_substitutions(replacement))
			{
				if (fallback_replacement == NULL)
					fallback_replacement = replacement;
				continue;
			}
			return replacement;
		}
	}
	return fallback_replacement;
}

TemplateDeclaration* Parser::replacement_free_function_template_definition(
	TemplateDeclaration* declaration,
	bool declaration_has_body)
{
	if (declaration_has_body)
		return declaration;
	map<Scope*, map<string, vector<TemplateDeclaration*> > >::iterator sit =
		function_templates_.find(declaration->owner);
	if (sit == function_templates_.end())
		return declaration;
	map<string, vector<TemplateDeclaration*> >::iterator it =
		sit->second.find(declaration->name);
	if (it == sit->second.end())
		return declaration;
	for (size_t j = 0; j < it->second.size(); ++j)
	{
		TemplateDeclaration* replacement = it->second[j];
		if (replacement == declaration ||
		    !replacement->has_definition ||
		    replacement->generic_function_type.get() == NULL ||
		    !same_function_template_signature_type(
			    replacement->generic_function_type,
			    declaration->generic_function_type) ||
		    !template_parameter_lists_match_local(replacement->parameters,
		                                          declaration->parameters))
			continue;
		return replacement;
	}
	return declaration;
}

TemplateDeclaration* Parser::replacement_function_template_definition(
	TemplateDeclaration* declaration)
{
	if (declaration == NULL)
		return declaration;
	pair<TemplateDeclaration*, pair<size_t, size_t> > cache_key =
		make_pair(declaration,
		          make_pair(member_function_template_generation_,
		                    template_declarations_.size()));
	map<pair<TemplateDeclaration*, pair<size_t, size_t> >,
	    TemplateDeclaration*>::iterator cached =
		replacement_function_template_definition_cache_.find(cache_key);
	if (cached != replacement_function_template_definition_cache_.end())
		return cached->second;
	bool declaration_has_body =
		template_declaration_has_body(declaration_tokens_, declaration);
	TypePtr owner_record = replacement_owner_record(declaration);
	TemplateDeclaration* member =
		replacement_member_function_template_definition(
			declaration,
			owner_record,
			replacement_owner_template(owner_record),
			declaration_has_body);
	TemplateDeclaration* replacement = member != NULL
		? member
		: replacement_free_function_template_definition(
			declaration,
			declaration_has_body);
	replacement_function_template_definition_cache_[cache_key] = replacement;
	return replacement;
}

void collect_owner_template_context(
	Binding* candidate,
	const map<const void*, TemplateDeclaration*>& record_template_declarations,
	const map<const void*, vector<TemplateArgument> >& record_template_arguments,
	map<string, TypePtr>& owner_subst,
	map<string, TemplateArgument>& owner_value_subst,
	set<string>& owner_pack_subst)
{
	TypePtr owner_record = candidate->owner != NULL &&
	                       candidate->owner->kind == ScopeKind::Class
		? pa11::record_type_for_scope(candidate->owner)
		: TypePtr();
	owner_record = owner_record.get() != NULL
		? pa11::strip_cv(owner_record) : TypePtr();
	map<const void*, TemplateDeclaration*>::const_iterator owner_decl =
		owner_record.get() != NULL
		? record_template_declarations.find(owner_record.get())
		: record_template_declarations.end();
	map<const void*, vector<TemplateArgument> >::const_iterator owner_args =
		owner_record.get() != NULL
		? record_template_arguments.find(owner_record.get())
		: record_template_arguments.end();
	if (owner_decl == record_template_declarations.end() ||
	    owner_args == record_template_arguments.end())
		return;
	for (size_t i = 0;
	     i < owner_decl->second->parameters.size() &&
	     i < owner_args->second.size();
	     ++i)
	{
		const TemplateParameterInfo& parameter =
			owner_decl->second->parameters[i];
		if (parameter.name.empty())
			continue;
		const TemplateArgument& owner_arg = owner_args->second[i];
		if (parameter.kind == TemplateParameterKind::Type)
		{
			if (parameter.is_pack)
			{
				owner_subst[parameter.name] =
					template_parameter_placeholder_type(parameter);
				owner_value_subst[parameter.name] = owner_arg;
				owner_pack_subst.insert(parameter.name);
			}
			else if (owner_arg.kind == TemplateArgumentKind::Type)
				owner_subst[parameter.name] = owner_arg.type;
		}
		else
			owner_value_subst[parameter.name] = owner_arg;
	}
}

void validate_member_function_pointer_overload_owner(const Expr& expr)
{
	Scope* member_owner = NULL;
	for (size_t i = 0; i < expr.overloads.size(); ++i)
	{
		Binding* candidate = expr.overloads[i];
		if (candidate == NULL ||
		    candidate->owner == NULL ||
		    candidate->owner->kind != ScopeKind::Class ||
		    candidate->is_static_member)
			continue;
		if (member_owner == NULL)
			member_owner = candidate->owner;
		else if (member_owner != candidate->owner)
			throw runtime_error("ambiguous overloaded member id");
	}
}

bool overload_expr_is_address(const Expr& expr)
{
	return expr.node.line.compare(0, 16, "unary-expression") == 0 &&
	       expr.node.has_op &&
	       expr.node.op == OP_AMP &&
	       !expr.node.children.empty();
}

Expr selected_overload_expr_result(const Expr& expr,
                                   Binding* found,
                                   bool target_member_function_pointer,
                                   const string& found_name)
{
	Expr out = expr;
	out.overloads.clear();
	out.binding = found;
	bool address_expr = overload_expr_is_address(expr);
	Expr selected_id;
	selected_id.valid = true;
	selected_id.binding = found;
	selected_id.type = found->type;
	selected_id.category = ValueCategory::LValue;
	selected_id.node = Node("id-expression lvalue " +
	                        pa11::describe_type(found->type) + " " +
	                        found_name);
	selected_id.node.binding = found;
	annotate_expr_node(selected_id);
	if (address_expr)
	{
		out.type = target_member_function_pointer
			? member_function_pointer_type(found)
			: pa11::make_pointer(found->type);
		out.category = ValueCategory::PRValue;
		out.node = Node("unary-expression prvalue " +
		                pa11::describe_type(out.type) + " OP_AMP:&");
		add_child(out.node, selected_id.node);
		out.node.has_op = true;
		out.node.op = OP_AMP;
		out.node.token_text = "&";
	}
	else
	{
		out.type = found->type;
		out.category = ValueCategory::LValue;
		out.node = selected_id.node;
	}
	annotate_expr_node(out);
	return out;
}

Binding* Parser::instantiate_target_overload_candidate(
	Binding* candidate,
	TypePtr wanted,
	const map<Binding*, vector<TemplateArgument> >& explicit_template_arguments)
{
	map<Binding*, TemplateDeclaration*>::iterator template_it =
		function_template_placeholders_.find(candidate);
	Binding* placeholder = candidate->aliased_binding != NULL
		? candidate->aliased_binding : candidate;
	if (template_it == function_template_placeholders_.end())
		return candidate;
	bool has_specialization_args =
		function_template_specialization_arguments_.find(candidate) !=
			function_template_specialization_arguments_.end() ||
		function_template_specialization_arguments_.find(placeholder) !=
			function_template_specialization_arguments_.end();
	if (template_it->second->placeholder != placeholder &&
	    has_specialization_args)
		return candidate;

	TemplateDeclaration* declaration =
		replacement_function_template_definition(template_it->second);
	vector<TemplateArgument> explicit_args;
	map<Binding*, vector<TemplateArgument> >::const_iterator eit =
		explicit_template_arguments.find(candidate);
	if (eit != explicit_template_arguments.end())
		explicit_args = eit->second;
	vector<map<string, TypePtr> > save_subst = template_type_substitutions_;
	vector<map<string, TemplateArgument> > save_value_subst =
		template_value_substitutions_;
	vector<set<string> > save_pack_subst = template_type_parameter_packs_;
	map<string, TypePtr> owner_subst;
	map<string, TemplateArgument> owner_value_subst;
	set<string> owner_pack_subst;
	collect_owner_template_context(candidate,
	                               record_template_declarations_,
	                               record_template_arguments_,
	                               owner_subst,
	                               owner_value_subst,
	                               owner_pack_subst);
	if (!owner_subst.empty() ||
	    !owner_value_subst.empty() ||
	    !owner_pack_subst.empty())
	{
		template_type_substitutions_.push_back(owner_subst);
		template_value_substitutions_.push_back(owner_value_subst);
		template_type_parameter_packs_.push_back(owner_pack_subst);
	}
	TypePtr deduce_wanted = wanted;
	TypePtr wanted_function = wanted.get() != NULL
		? pa11::strip_cv(wanted) : TypePtr();
	if (candidate->owner != NULL &&
	    candidate->owner->kind == ScopeKind::Class &&
	    !candidate->is_static_member &&
	    wanted_function.get() != NULL &&
	    wanted_function->kind == pa11::TypeKind::Function)
	{
		TypePtr class_type = pa11::record_type_for_scope(candidate->owner);
		class_type = class_type.get() != NULL
			? pa11::strip_cv(class_type) : TypePtr();
		if (class_type.get() != NULL)
		{
			if (wanted_function->cv != pa11::CV_NONE)
				class_type = pa11::make_cv(class_type,
				                           wanted_function->cv);
			vector<TypePtr> params;
			params.push_back(pa11::make_pointer(class_type));
			params.insert(params.end(),
			              wanted_function->parameters.begin(),
			              wanted_function->parameters.end());
			deduce_wanted = pa11::make_function(wanted_function->base,
			                                    params,
			                                    wanted_function->variadic);
		}
	}
	vector<TemplateArgument> deduced;
	if (!deduce_function_template_target_type(declaration,
	                                          deduce_wanted,
	                                          explicit_args,
	                                          deduced))
	{
		template_type_substitutions_ = save_subst;
		template_value_substitutions_ = save_value_subst;
		template_type_parameter_packs_ = save_pack_subst;
		return NULL;
	}
	Binding* instantiated = NULL;
	try
	{
		instantiated = instantiate_function_template(declaration, deduced);
	}
	catch (...)
	{
		template_type_substitutions_ = save_subst;
		template_value_substitutions_ = save_value_subst;
		template_type_parameter_packs_ = save_pack_subst;
		throw;
	}
	template_type_substitutions_ = save_subst;
	template_value_substitutions_ = save_value_subst;
	template_type_parameter_packs_ = save_pack_subst;
	return instantiated;
}

Expr Parser::select_overload_expr(const Expr& expr, TypePtr target)
{
	if (expr.overloads.empty())
		return expr;
	TypePtr target_object = target;
	if (target_object->kind == pa11::TypeKind::LValueReference ||
	    target_object->kind == pa11::TypeKind::RValueReference)
		target_object = target_object->base;
	TypePtr wanted = target_object;
	bool target_member_function_pointer = false;
	if (is_function_pointer(target_object))
		wanted = pa11::strip_cv(target_object)->base;
	else if (is_function_reference(target))
		wanted = pa11::strip_cv(target->base);
	else if (is_member_function_pointer(target_object))
		target_member_function_pointer = true;
	else
		throw runtime_error("overloaded function id needs target");
	if (target_member_function_pointer)
		validate_member_function_pointer_overload_owner(expr);

	Binding* found = NULL;
	vector<Binding*> considered;
	TypePtr wanted_member_pointer = target_member_function_pointer ? pa11::strip_cv(target_object) : TypePtr();
	for (size_t i = 0; i < expr.overloads.size(); ++i)
	{
		TypePtr candidate_wanted = target_member_function_pointer
			? pa11::strip_cv(target_object)->base
			: wanted;
		if (i != 0 && expr.overloads[i] != NULL)
			expr.overloads[i]->reserve_primary_function_symbol = true;
		Binding* candidate = instantiate_target_overload_candidate(
			expr.overloads[i],
			candidate_wanted,
			expr.explicit_template_arguments);
		if (candidate == NULL)
			continue;
		if (i != 0)
			candidate->reserve_primary_function_symbol = true;

		Binding* duplicate = NULL;
		for (size_t j = 0; j < considered.size(); ++j)
			if (pa11::same_type(considered[j]->type, candidate->type) &&
			    considered[j]->is_static_member == candidate->is_static_member)
			{
				duplicate = considered[j];
				break;
			}
		if (duplicate != NULL)
		{
			if (!(candidate->is_inline_definition &&
			      !duplicate->is_inline_definition))
				continue;
			vector<Binding*>::iterator pos =
				find(considered.begin(), considered.end(), duplicate);
			if (pos != considered.end())
				*pos = candidate;
			if (found == duplicate)
				found = NULL;
		}
		else
			considered.push_back(candidate);

		TypePtr candidate_member_pointer = target_member_function_pointer
			? member_function_pointer_type(candidate) : TypePtr();
		bool matches = target_member_function_pointer
			? (candidate_member_pointer.get() != NULL &&
			   pa11::same_type(candidate_member_pointer,
			                   wanted_member_pointer))
			: pa11::same_type(candidate->type, wanted);
		if (matches)
		{
			if (found != NULL)
				throw runtime_error("ambiguous overloaded function id");
			found = candidate;
		}
	}
	if (found == NULL)
		throw runtime_error("no overloaded function id target");
	if (unevaluated_expression_depth_ == 0 &&
	    !defer_hosted_function_body(found))
	{
		parse_pending_function_body(found);
		parse_pending_member_body(found);
		ensure_function_body_extra_node(found);
	}
	return selected_overload_expr_result(expr,
	                                     found,
	                                     target_member_function_pointer,
	                                     qualified_decl_name(found));
}

Expr Parser::make_dependent_call_expr(const Expr& callee,
                                      const vector<Expr>& args)
{
	if (replaying_dependent_decltype_)
	{
		for (map<Binding*, vector<TemplateArgument> >::const_iterator it =
			     callee.explicit_template_arguments.begin();
		     it != callee.explicit_template_arguments.end();
		     ++it)
		{
			Binding* binding = it->first;
			Binding* placeholder =
				binding != NULL && binding->aliased_binding != NULL
				? binding->aliased_binding : binding;
			if (function_template_placeholders_.find(placeholder) !=
			    function_template_placeholders_.end())
				placeholder->reserve_primary_function_symbol = true;
		}
	}
	Expr out;
	TypePtr result;
	TypePtr callee_type = callee.type.get() != NULL
		? pa11::strip_cv(expression_object_type(callee.type)) : TypePtr();
	if (callee_type.get() != NULL &&
	    callee_type->kind == pa11::TypeKind::Function)
		result = callee_type->base;
	if (result.get() != NULL && !callee.explicit_template_arguments.empty())
	{
		map<Binding*, vector<TemplateArgument> >::const_iterator explicit_it =
			callee.explicit_template_arguments.begin();
		Binding* binding = explicit_it->first;
		Binding* placeholder =
			binding != NULL && binding->aliased_binding != NULL
			? binding->aliased_binding : binding;
		map<Binding*, TemplateDeclaration*>::const_iterator decl =
			function_template_placeholders_.find(placeholder);
		if (decl == function_template_placeholders_.end() && binding != NULL)
			decl = function_template_placeholders_.find(binding);
		if (decl != function_template_placeholders_.end())
		{
			const vector<TemplateArgument>& explicit_args =
				explicit_it->second;
			for (size_t i = 0; i < explicit_args.size() &&
			     i < decl->second->parameters.size(); ++i)
			{
				const TemplateParameterInfo& parameter =
					decl->second->parameters[i];
				if (parameter.kind == TemplateParameterKind::Type &&
				    !parameter.name.empty() &&
				    explicit_args[i].kind == TemplateArgumentKind::Type)
					result = substitute_template_type_parameter(
						result,
						parameter.name,
						explicit_args[i].type);
			}
		}
	}
	out.type = result.get() != NULL
		? result
		: replaying_dependent_decltype_
		? pa11::make_fundamental(FT_INT)
		: pa11::make_dependent_typename_type("__dependent_call",
		                                     false,
		                                     false,
		                                     false);
	out.category = call_category(out.type);
	out.node = Node("call-expression " + value_category_name(out.category) +
	                " " + pa11::describe_type(out.type));
	add_child(out.node, callee.node);
	for (size_t i = 0; i < args.size(); ++i)
		add_child(out.node, args[i].node);
	out.valid = true;
	annotate_expr_node(out);
	return out;
}

void Parser::ensure_copy_move_constructor_for_single_arg(
	TypePtr record,
	const vector<Expr>& args)
{
	if (args.size() != 1)
		return;
	if (args[0].type.get() == NULL)
		return;
	TypePtr arg_record = pa11::strip_cv(expression_object_type(args[0].type));
	if (arg_record->kind != pa11::TypeKind::Record ||
	    (!pa11::same_type(arg_record, record) &&
	     !same_template_specialization_record(arg_record, record) &&
	     record_base_distance(arg_record, record) >= 1000000))
		return;
	if (args[0].category != ValueCategory::LValue)
		ensure_copy_move_constructor(record, true);
	ensure_copy_move_constructor(record, false);
}

void Parser::add_variadic_argument_ranks(Binding* fn,
                                         size_t arg_count,
                                         vector<int>& ranks) const
{
	if (fn == NULL ||
	    fn->type->kind != pa11::TypeKind::Function ||
	    !fn->type->variadic ||
	    arg_count <= fn->type->parameters.size())
		return;
	for (size_t i = fn->type->parameters.size(); i < arg_count; ++i)
		ranks.push_back(100);
}

void Parser::prepare_member_call(Expr& callee, vector<Expr>& args)
{
	bool needs_this = false;
	Expr object;
	object.node = callee.node.children[0];
	object.type = object.node.type;
	object.category = object.node.category;
	object.binding = object.node.binding;
	object.valid = true;
	vector<Binding*> viable_overloads;
	vector<Binding*> nonstatic_overloads;
	for (size_t i = 0; i < callee.overloads.size(); ++i)
	{
		Binding* candidate = callee.overloads[i];
		if (candidate->owner != NULL &&
		    candidate->owner->kind == ScopeKind::Class &&
		    !candidate->is_static_member)
		{
			TypePtr this_param =
				candidate->type->parameters.empty()
				? TypePtr() : candidate->type->parameters[0];
			TypePtr this_object =
				this_param.get() != NULL &&
				pa11::strip_cv(this_param)->kind ==
				pa11::TypeKind::Pointer
				? pa11::strip_cv(this_param)->base : TypePtr();
				TypePtr object_type = expression_object_type(object.type);
				TypePtr object_bare = object_type.get() != NULL
					? pa11::strip_cv(object_type) : TypePtr();
				if (object_bare.get() != NULL &&
				    object_bare->kind == pa11::TypeKind::Pointer)
					object_type = object_bare->base;
				TypePtr object_record = object_type;
				TypePtr object_record_bare =
					object_record.get() != NULL
					? pa11::strip_cv(object_record) : TypePtr();
				TypePtr this_record =
					this_object.get() != NULL
					? pa11::strip_cv(this_object) : TypePtr();
				if (object_record_bare.get() != NULL &&
				    this_record.get() != NULL &&
				    object_record_bare->kind == pa11::TypeKind::Record &&
				    this_record->kind == pa11::TypeKind::Record)
				{
					bool same_primary_specialization =
						object_record_bare->is_template_specialization &&
						this_record->is_template_specialization &&
						!object_record_bare->template_primary_name.empty() &&
						object_record_bare->template_primary_name ==
							this_record->template_primary_name;
					bool object_matches =
						pa11::same_type(object_record_bare, this_record) ||
						(!same_primary_specialization &&
						 same_template_specialization_record(object_record_bare,
						                                     this_record)) ||
						record_base_distance(object_record_bare, this_record) <
							1000000;
					if (!object_matches)
						continue;
				}
				if (this_object.get() != NULL &&
				    object_type.get() != NULL &&
				    pa11::type_has_const(object_type) &&
			    !pa11::type_has_const(this_object))
				continue;
			if (candidate->ref_qualifier == 1 &&
			    object.category != ValueCategory::LValue)
			{
				if (this_object.get() == NULL ||
				    !pa11::type_has_const(this_object))
					continue;
			}
			if (candidate->ref_qualifier == 2 &&
			    object.category == ValueCategory::LValue)
				continue;
			needs_this = true;
			nonstatic_overloads.push_back(candidate);
		}
		viable_overloads.push_back(candidate);
	}
	if (!nonstatic_overloads.empty())
		viable_overloads = nonstatic_overloads;
	if (viable_overloads.empty())
		throw runtime_error("cannot resolve call overload");
	callee.overloads = viable_overloads;
	if (needs_this)
	{
		Expr this_arg;
		if (callee.node.has_op && callee.node.op == OP_ARROW)
			this_arg = object;
		else if (object.node.line.compare(0, 17, "member-expression") == 0)
		{
			this_arg.valid = true;
			this_arg.type = pa11::make_pointer(
				expression_object_type(object.type));
			this_arg.category = ValueCategory::PRValue;
			this_arg.node = Node("unary-expression prvalue " +
			                     pa11::describe_type(this_arg.type) +
			                     " OP_AMP:&");
			add_child(this_arg.node, object.node);
			this_arg.node.has_op = true;
			this_arg.node.op = OP_AMP;
			this_arg.node.token_text = "&";
			annotate_expr_node(this_arg);
		}
		else
			this_arg = make_address_expr("&", object);
		args.insert(args.begin(), this_arg);
	}
}

bool Parser::ranks_better(const vector<int>& lhs, const vector<int>& rhs) const
{
	if (rhs.empty())
		return false;
	if (lhs.size() != rhs.size())
		return false;
	bool any = false;
	for (size_t i = 0; i < lhs.size(); ++i)
	{
		if (lhs[i] > rhs[i])
			return false;
		if (lhs[i] < rhs[i])
			any = true;
	}
	return any;
}

}  // namespace internal
}  // namespace pa12
