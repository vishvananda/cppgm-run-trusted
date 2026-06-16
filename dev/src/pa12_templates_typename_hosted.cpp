#include "pa12_templates_instance_support.h"
#include "pa12_types_support.h"

#include <stdexcept>

using namespace std;

namespace pa12 {
namespace internal {

TypePtr Parser::hosted_hash_node_value_type(TypePtr node_type) const
{
	if (node_type.get() == NULL)
		return TypePtr();
	try
	{
		node_type = substitute_template_type(node_type);
	}
	catch (const runtime_error&)
	{
	}
	TypePtr bare = pa11::strip_cv(node_type);
	if (bare.get() == NULL ||
	    bare->kind != pa11::TypeKind::Record)
		return TypePtr();
	string primary = bare->template_primary_name.empty()
		? bare->name : bare->template_primary_name;
	size_t sep = primary.rfind("::");
	if (sep != string::npos)
		primary = primary.substr(sep + 2);
	size_t args_pos = primary.find('<');
	if (args_pos != string::npos)
		primary = primary.substr(0, args_pos);
	if (primary != "_Hash_node")
		return TypePtr();
	vector<TemplateArgument> args;
	map<const void*, vector<TemplateArgument> >::const_iterator stored =
		record_template_arguments_.find(bare.get());
	if (stored != record_template_arguments_.end())
		args = stored->second;
	else
		for (size_t i = 0; i < bare->template_arguments.size(); ++i)
			args.push_back(template_argument_from_instance_argument(
				bare->template_arguments[i]));
	if (args.empty())
		return TypePtr();
	TemplateArgument value_arg = substitute_template_argument(args[0]);
	return value_arg.kind == TemplateArgumentKind::Type
		? value_arg.type : TypePtr();
}

TypePtr Parser::hosted_lookup_type_member(Scope* scope,
                                          const string& name) const
{
	if (scope == NULL)
		return TypePtr();
	try
	{
		vector<Binding*> found =
			const_cast<Parser*>(this)->lookup_qualified_set(
				scope,
				name,
				pa11::LOOKUP_TYPE);
		if (found.empty() || found[0]->type.get() == NULL)
			return TypePtr();
		return substitute_template_type_in_scope(found[0]->type, scope);
	}
	catch (const runtime_error&)
	{
		return TypePtr();
	}
}

TypePtr Parser::hosted_allocator_member_type(TypePtr allocator_type,
                                             const string& member_name) const
{
	try
	{
		allocator_type = substitute_template_type(allocator_type);
	}
	catch (const runtime_error&)
	{
	}
	TypePtr bare = allocator_type.get() != NULL
		? pa11::strip_cv(allocator_type) : TypePtr();
	if (bare.get() == NULL ||
	    bare->kind != pa11::TypeKind::Record ||
	    bare->scope == NULL)
		return TypePtr();
	try
	{
		const_cast<Parser*>(this)->complete_template_record(bare);
	}
	catch (const runtime_error&)
	{
	}
	return hosted_lookup_type_member(bare->scope, member_name);
}

TypePtr Parser::hosted_allocator_value_type(TypePtr allocator_type) const
{
	return hosted_allocator_member_type(allocator_type, "value_type");
}

TypePtr Parser::hosted_get_value_type_from_context() const
{
	if (!hosted_compatibility_)
		return TypePtr();
	for (size_t i = active_class_instantiations_.size(); i > 0; --i)
	{
		const ActiveClassInstantiation& active =
			active_class_instantiations_[i - 1];
		TypePtr active_record = active.type.get() != NULL
			? pa11::strip_cv(active.type) : TypePtr();
		if (active_record.get() == NULL ||
		    active_record->kind != pa11::TypeKind::Record)
			continue;
		TypePtr node_type = hosted_lookup_type_member(active_record->scope,
		                                              "__node_type");
		TypePtr value_type = hosted_hash_node_value_type(node_type);
		if (value_type.get() != NULL)
			return value_type;
		map<const void*, vector<TemplateArgument> >::const_iterator args =
			record_template_arguments_.find(active_record.get());
		if (active.declaration == NULL ||
		    args == record_template_arguments_.end())
			continue;
		for (size_t pi = 0;
		     pi < active.declaration->parameters.size() &&
		     pi < args->second.size();
		     ++pi)
		{
			if (active.declaration->parameters[pi].name != "_NodeAlloc" ||
			    args->second[pi].kind != TemplateArgumentKind::Type)
				continue;
			node_type = hosted_allocator_value_type(args->second[pi].type);
			value_type = hosted_hash_node_value_type(node_type);
			if (value_type.get() != NULL)
				return value_type;
		}
	}
	for (Scope* scope = current_scope(); scope != NULL; scope = scope->parent)
	{
		TypePtr node_type = hosted_lookup_type_member(scope, "__node_type");
		TypePtr value_type = hosted_hash_node_value_type(node_type);
		if (value_type.get() != NULL)
			return value_type;
	}
	for (size_t si = template_type_substitutions_.size(); si > 0; --si)
	{
		map<string, TypePtr>::const_iterator node_alloc =
			template_type_substitutions_[si - 1].find("_NodeAlloc");
		if (node_alloc == template_type_substitutions_[si - 1].end())
			continue;
		TypePtr node_type = hosted_allocator_value_type(node_alloc->second);
		TypePtr value_type = hosted_hash_node_value_type(node_type);
		if (value_type.get() != NULL)
			return value_type;
	}
	return TypePtr();
}

TypePtr Parser::hosted_allocator_rebind_value_type() const
{
	if (!hosted_compatibility_)
		return TypePtr();
	const char* allocator_names[] = {"_Alloc", "_NodeAlloc"};
	for (size_t ni = 0;
	     ni < sizeof(allocator_names) / sizeof(allocator_names[0]);
	     ++ni)
	{
		for (size_t si = template_type_substitutions_.size(); si > 0; --si)
		{
			map<string, TypePtr>::const_iterator it =
				template_type_substitutions_[si - 1].find(
					allocator_names[ni]);
			if (it == template_type_substitutions_[si - 1].end())
				continue;
			TypePtr value_type = hosted_allocator_value_type(it->second);
			if (value_type.get() != NULL)
				return value_type;
		}
	}
	const char* names[] = {"_Tp", "_Up", "_Val", "T"};
	for (size_t ni = 0; ni < sizeof(names) / sizeof(names[0]); ++ni)
	{
		for (size_t si = template_type_substitutions_.size(); si > 0; --si)
		{
			map<string, TypePtr>::const_iterator it =
				template_type_substitutions_[si - 1].find(names[ni]);
			if (it == template_type_substitutions_[si - 1].end())
				continue;
			try
			{
				return substitute_template_type(it->second);
			}
			catch (const runtime_error&)
			{
				return it->second;
			}
		}
	}
	return TypePtr();
}

TypePtr Parser::hosted_active_template_parameter_type(
	const string& parameter_name) const
{
	if (!hosted_compatibility_ || parameter_name.empty())
		return TypePtr();
	TypePtr subst;
	if (find_template_type_substitution(parameter_name, subst))
	{
		TypePtr bare_subst = subst.get() != NULL
			? pa11::strip_cv(subst) : TypePtr();
		if (bare_subst.get() != NULL &&
		    !bare_subst->is_dependent_typename &&
		    bare_subst->kind != pa11::TypeKind::TemplateParameter)
			return subst;
	}
	for (size_t ai = active_class_instantiations_.size(); ai > 0; --ai)
	{
		const ActiveClassInstantiation& active =
			active_class_instantiations_[ai - 1];
		if (active.declaration == NULL)
			continue;
		size_t param_index = active.declaration->parameters.size();
		for (size_t pi = 0; pi < active.declaration->parameters.size(); ++pi)
			if (active.declaration->parameters[pi].name == parameter_name)
			{
				param_index = pi;
				break;
			}
		if (param_index == active.declaration->parameters.size())
			continue;
		TypePtr active_record = active.type.get() != NULL
			? pa11::strip_cv(active.type) : TypePtr();
		if (active_record.get() == NULL ||
		    active_record->kind != pa11::TypeKind::Record)
			continue;
		vector<TemplateArgument> active_args;
		map<const void*, vector<TemplateArgument> >::const_iterator stored =
			record_template_arguments_.find(active_record.get());
		if (stored != record_template_arguments_.end())
			active_args = stored->second;
		else
			for (size_t ti = 0;
			     ti < active_record->template_arguments.size();
			     ++ti)
				active_args.push_back(
					template_argument_from_instance_argument(
						active_record->template_arguments[ti]));
		active_args = flatten_template_argument_packs(active_args);
		if (param_index < active_args.size() &&
		    active_args[param_index].kind == TemplateArgumentKind::Type)
		{
			TypePtr candidate = active_args[param_index].type;
			TypePtr bare_candidate = candidate.get() != NULL
				? pa11::strip_cv(candidate) : TypePtr();
			if (bare_candidate.get() != NULL &&
			    !bare_candidate->is_dependent_typename &&
			    bare_candidate->kind != pa11::TypeKind::TemplateParameter)
				return candidate;
		}
	}
	return TypePtr();
}

TypePtr Parser::hosted_rebind_allocator_type(TypePtr allocator_type,
                                             TypePtr rebound_type) const
{
	if (!hosted_compatibility_ ||
	    allocator_type.get() == NULL ||
	    rebound_type.get() == NULL)
		return TypePtr();
	try
	{
		allocator_type = substitute_template_type(allocator_type);
		rebound_type = substitute_template_type(rebound_type);
	}
	catch (const runtime_error&)
	{
	}
	TypePtr allocator_record = allocator_type.get() != NULL
		? pa11::strip_cv(allocator_type) : TypePtr();
	if (allocator_record.get() == NULL ||
	    allocator_record->kind != pa11::TypeKind::Record)
		return TypePtr();
	vector<TemplateArgument> allocator_args;
	map<const void*, vector<TemplateArgument> >::const_iterator stored =
		record_template_arguments_.find(allocator_record.get());
	if (stored != record_template_arguments_.end())
		allocator_args = stored->second;
	else
		for (size_t ai = 0; ai < allocator_record->template_arguments.size(); ++ai)
			allocator_args.push_back(template_argument_from_instance_argument(
				allocator_record->template_arguments[ai]));
	allocator_args = flatten_template_argument_packs(allocator_args);
	size_t first_type_arg = allocator_args.size();
	for (size_t ai = 0; ai < allocator_args.size(); ++ai)
	{
		allocator_args[ai] = substitute_template_argument(allocator_args[ai]);
		if (first_type_arg == allocator_args.size() &&
		    allocator_args[ai].kind == TemplateArgumentKind::Type)
			first_type_arg = ai;
	}
	if (first_type_arg == allocator_args.size())
		return TypePtr();
	allocator_args[first_type_arg] = TemplateArgument::type_arg(rebound_type);
	TemplateDeclaration* declaration = NULL;
	map<const void*, TemplateDeclaration*>::const_iterator stored_decl =
		record_template_declarations_.find(allocator_record.get());
	if (stored_decl != record_template_declarations_.end())
		declaration = stored_decl->second;
	if (declaration != NULL && declaration->class_specialization)
	{
		TemplateDeclaration* primary =
			const_cast<Parser*>(this)->find_class_template(
				declaration->owner,
				declaration->name);
		if (primary != NULL)
			declaration = primary;
	}
	if (declaration == NULL)
	{
		string primary_name = allocator_record->template_primary_name;
		if (!primary_name.empty())
		{
			Scope* qualifier = NULL;
			string lookup_name = primary_name;
			const_cast<Parser*>(this)->resolve_template_name_spelling(
				primary_name,
				qualifier,
				lookup_name);
			declaration = const_cast<Parser*>(this)->
				find_class_template(qualifier, lookup_name);
		}
	}
	if (declaration == NULL ||
	    declaration->kind != TemplateDeclarationKind::Class)
		return TypePtr();
	try
	{
		return const_cast<Parser*>(this)->instantiate_class_template(
			declaration,
			allocator_args);
	}
	catch (const runtime_error&)
	{
		return TypePtr();
	}
}

TypePtr Parser::hosted_allocator_rebind_member_type(
	const string& member_name) const
{
	if (!hosted_compatibility_)
		return TypePtr();
	const char* allocator_names[] = {"_Alloc", "_NodeAlloc"};
	for (size_t ni = 0;
	     ni < sizeof(allocator_names) / sizeof(allocator_names[0]);
	     ++ni)
	{
		for (size_t si = template_type_substitutions_.size(); si > 0; --si)
		{
			map<string, TypePtr>::const_iterator it =
				template_type_substitutions_[si - 1].find(
					allocator_names[ni]);
			if (it == template_type_substitutions_[si - 1].end())
				continue;
			TypePtr member =
				hosted_allocator_member_type(it->second, member_name);
			if (member.get() != NULL)
				return member;
		}
	}
	if (member_name == "value_type")
		return hosted_allocator_rebind_value_type();
	if (member_name == "size_type")
		return pa11::make_fundamental(FT_UNSIGNED_LONG_INT);
	if (member_name == "difference_type")
		return pa11::make_fundamental(FT_LONG_INT);
	return TypePtr();
}

TypePtr Parser::hosted_bool_constant_type(bool value) const
{
	TemplateDeclaration* integral =
		const_cast<Parser*>(this)->find_class_template(NULL,
		                                               "integral_constant");
	if (integral == NULL)
		return TypePtr();
	vector<TemplateArgument> args;
	args.push_back(
		TemplateArgument::type_arg(pa11::make_fundamental(FT_BOOL)));
	args.push_back(
		TemplateArgument::value_arg(pa11::make_fundamental(FT_BOOL),
		                            value ? 1 : 0));
	return const_cast<Parser*>(this)->instantiate_class_template(integral,
	                                                            args);
}

bool Parser::hosted_invoke_result_call_types(
	TypePtr invoke_result,
	vector<TypePtr>& call_types) const
{
	TypePtr bare = invoke_result.get() != NULL
		? pa11::strip_cv(invoke_result) : TypePtr();
	if (bare.get() == NULL ||
	    bare->kind != pa11::TypeKind::Record)
		return false;
	string primary = bare->template_primary_name.empty()
		? bare->name : bare->template_primary_name;
	size_t sep = primary.rfind("::");
	if (sep != string::npos)
		primary = primary.substr(sep + 2);
	size_t arg_pos = primary.find('<');
	if (arg_pos != string::npos)
		primary = primary.substr(0, arg_pos);
	if (primary != "__invoke_result")
		return false;
	vector<TemplateArgument> args;
	map<const void*, vector<TemplateArgument> >::const_iterator stored =
		record_template_arguments_.find(bare.get());
	if (stored != record_template_arguments_.end())
		args = stored->second;
	else
		for (size_t ai = 0; ai < bare->template_arguments.size(); ++ai)
			args.push_back(template_argument_from_instance_argument(
				bare->template_arguments[ai]));
	args = flatten_template_argument_packs(args);
	for (size_t ai = 0; ai < args.size(); ++ai)
	{
		TemplateArgument arg = substitute_template_argument(args[ai]);
		if (arg.kind == TemplateArgumentKind::Pack)
		{
			for (size_t pi = 0; pi < arg.pack.size(); ++pi)
			{
				TemplateArgument elem =
					substitute_template_argument(arg.pack[pi]);
				if (elem.kind != TemplateArgumentKind::Type)
					return false;
				call_types.push_back(
					resolve_hosted_invoke_call_type(elem.type));
			}
			continue;
		}
		if (arg.kind != TemplateArgumentKind::Type)
			return false;
		call_types.push_back(resolve_hosted_invoke_call_type(arg.type));
	}
	return !call_types.empty();
}

TypePtr Parser::hosted_call_result_type(
	const vector<TypePtr>& call_types) const
{
	if (call_types.empty())
		return TypePtr();
	Expr call;
	if (const_cast<Parser*>(this)->try_make_invocable_type_trait_call(
		    call_types,
		    call))
		return call.type;
	return TypePtr();
}

TypePtr Parser::hosted_invoke_result_type(TypePtr invoke_result) const
{
	vector<TypePtr> call_types;
	if (!hosted_invoke_result_call_types(invoke_result, call_types))
		return TypePtr();
	return hosted_call_result_type(call_types);
}

TypePtr Parser::resolve_hosted_invoke_call_type(TypePtr call_type) const
{
	try
	{
		call_type = substitute_template_type(call_type);
	}
	catch (const runtime_error&)
	{
	}
	if (call_type.get() == NULL)
		return call_type;
	if (call_type->kind == pa11::TypeKind::LValueReference ||
	    call_type->kind == pa11::TypeKind::RValueReference)
	{
		TypePtr base = call_type->base;
		try
		{
			base = substitute_template_type(base);
		}
		catch (const runtime_error&)
		{
		}
		if (base.get() != NULL && base->is_dependent_typename)
		{
			TypePtr resolved = resolve_dependent_typename_type(base);
			if (resolved.get() != NULL)
			{
				try
				{
					base = substitute_template_type(resolved);
				}
				catch (const runtime_error&)
				{
					base = resolved;
				}
			}
		}
		if (base != call_type->base)
			return call_type->kind == pa11::TypeKind::LValueReference
				? pa11::make_lvalue_reference(base)
				: pa11::make_rvalue_reference(base);
		return call_type;
	}
	if (call_type->is_dependent_typename)
	{
		TypePtr resolved = resolve_dependent_typename_type(call_type);
		if (resolved.get() != NULL)
		{
			try
			{
				return substitute_template_type(resolved);
			}
			catch (const runtime_error&)
			{
				return resolved;
			}
		}
	}
	return call_type;
}

}  // namespace internal
}  // namespace pa12
