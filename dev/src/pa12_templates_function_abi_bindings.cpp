#include "pa12_templates_function_abi_internal.h"
#include "pa12_templates_instance_support.h"

#include <algorithm>
#include <stdexcept>

using namespace std;

namespace pa12 {
namespace internal {

vector<Scope*> abi_binding_scope_path_outer_first(const Binding* binding)
{
	return abi_scope_path_outer_first(binding != NULL ? binding->owner : NULL);
}

bool abi_binding_has_only_std_namespace(const vector<Scope*>& scopes)
{
	return scopes.size() == 1 && abi_scope_is_std_namespace(scopes[0]);
}

bool abi_terminal_std_class_scope(Scope* scope, AbiSubstitutionContext& ctx)
{
	if (scope == NULL || scope->kind != ScopeKind::Class)
		return false;
	TypePtr record = pa11::record_type_for_scope(scope);
	string abbreviation = abi_std_abbreviation(record, &ctx);
	return abi_std_abbreviation_is_terminal(abbreviation);
}

void abi_filter_terminal_std_class_scope(vector<Scope*>& scopes,
                                         AbiSubstitutionContext& ctx)
{
	if (scopes.size() >= 2 &&
	    abi_scope_is_std_namespace(scopes[0]) &&
	    abi_terminal_std_class_scope(scopes[1], ctx))
		scopes.erase(scopes.begin());
}

vector<Scope*> abi_dependent_typename_scope_prefix_for_binding(
	const Binding* binding)
{
	if (binding == NULL || binding->owner == NULL ||
	    (binding->owner->kind != ScopeKind::Namespace &&
	     binding->owner->kind != ScopeKind::Class))
		return vector<Scope*>();
	return abi_scope_path_outer_first(binding->owner);
}

bool abi_binding_alias_preserves_owner(const Binding* binding)
{
	if (binding == NULL ||
	    binding->kind != BindingKind::Function ||
	    binding->aliased_binding == NULL ||
	    binding->owner == NULL ||
	    binding->owner->kind != ScopeKind::Class)
		return false;
	TypePtr record = pa11::record_type_for_scope(binding->owner);
	record = record.get() != NULL ? pa11::strip_cv(record) : TypePtr();
	return record.get() != NULL &&
	       record->kind == pa11::TypeKind::Record &&
	       record->is_template_specialization;
}

bool abi_binding_alias_symbol_equivalent(const Binding* binding)
{
	if (binding == NULL || binding->aliased_binding == NULL)
		return false;
	const Binding* alias = binding->aliased_binding;
	if (binding->kind != BindingKind::Function ||
	    alias->kind != BindingKind::Function)
		return true;
	if (!binding->function_specialization_symbol.empty() ||
	    !alias->function_specialization_symbol.empty())
		return true;
	if (binding->owner != alias->owner ||
	    binding->name != alias->name ||
	    binding->is_static_member != alias->is_static_member)
		return true;
	return pa11::same_type(binding->type, alias->type);
}

void abi_append_member_function_name_qualifiers(string& encoded,
                                                const Binding* binding,
                                                TypePtr fn_type)
{
	if (binding == NULL ||
	    binding->kind != BindingKind::Function ||
	    binding->owner == NULL ||
	    binding->owner->kind != ScopeKind::Class ||
	    binding->is_static_member ||
	    fn_type.get() == NULL ||
	    fn_type->kind != pa11::TypeKind::Function)
		return;
	bool const_member = (fn_type->cv & pa11::CV_CONST) != 0;
	bool volatile_member = (fn_type->cv & pa11::CV_VOLATILE) != 0;
	if (!fn_type->parameters.empty() &&
	    pa11::strip_cv(fn_type->parameters[0])->kind ==
		    pa11::TypeKind::Pointer)
	{
		TypePtr self = pa11::strip_cv(fn_type->parameters[0])->base;
		const_member = const_member || pa11::type_has_const(self);
	}
	if (const_member)
		encoded += "K";
	if (volatile_member)
		encoded += "V";
	int ref_qualifier =
		binding->ref_qualifier != 0
		? binding->ref_qualifier : fn_type->ref_qualifier;
	if (ref_qualifier == 1)
		encoded += "R";
	else if (ref_qualifier == 2)
		encoded += "O";
}

string abi_encode_binding_name_with_substitutions(
	const Binding* binding,
	AbiSubstitutionContext& ctx)
{
	string leaf = abi_binding_source_name(binding);
	vector<Scope*> scopes = abi_binding_scope_path_outer_first(binding);
	abi_filter_terminal_std_class_scope(scopes, ctx);
	string encoded;
	if (scopes.empty())
		encoded = leaf;
	else if (abi_binding_has_only_std_namespace(scopes))
		encoded = "St" + leaf;
	else
	{
		encoded = "N";
		abi_append_member_function_name_qualifiers(
			encoded, binding, binding != NULL ? binding->type : TypePtr());
		encoded += abi_scope_prefix_with_substitutions(scopes, ctx);
		encoded += leaf;
		encoded += "E";
	}
	return encoded;
}

string abi_encode_function_template_name_with_substitutions(
	TemplateDeclaration* declaration,
	const vector<TemplateArgument>& full_args,
	Binding* binding,
	AbiSubstitutionContext& ctx)
{
	vector<Scope*> scopes = abi_binding_scope_path_outer_first(binding);
	abi_filter_terminal_std_class_scope(scopes, ctx);
	string scope_prefix;
	if (!scopes.empty() && !abi_binding_has_only_std_namespace(scopes))
		scope_prefix = abi_scope_prefix_with_substitutions(scopes, ctx);
	string name = binding != NULL
		? abi_binding_source_name(binding)
		: abi_source_name(declaration->name);
	if (scopes.empty())
		abi_add_substitution(ctx, name);
	string leaf = name + "I";
	bool saved_function_template_argument_list =
		ctx.function_template_argument_list;
	size_t saved_function_template_argument_substitution_floor =
		ctx.function_template_argument_substitution_floor;
	ctx.function_template_argument_list = true;
	ctx.function_template_argument_substitution_floor =
		ctx.substitutions.size();
	for (size_t i = 0; i < full_args.size(); ++i)
	{
		if (i < declaration->parameters.size())
			leaf += abi_template_argument_for_parameter_with_substitutions(
				declaration->parameters[i], full_args[i], ctx);
		else
			leaf += abi_template_argument_with_substitutions(full_args[i],
			                                                ctx);
	}
	ctx.function_template_argument_list =
		saved_function_template_argument_list;
	ctx.function_template_argument_substitution_floor =
		saved_function_template_argument_substitution_floor;
	leaf += "E";
	string encoded;
	if (scopes.empty())
		encoded = leaf;
	else if (abi_binding_has_only_std_namespace(scopes))
		encoded = "St" + leaf;
	else
		encoded = "N" + scope_prefix + leaf + "E";
	if (!scopes.empty())
		abi_add_substitution(ctx, encoded);
	return encoded;
}

void abi_append_template_argument_list_with_substitutions(
	string& out,
	TemplateDeclaration* declaration,
	const vector<TemplateArgument>& full_args,
	AbiSubstitutionContext& ctx)
{
	bool saved_function_template_argument_list =
		ctx.function_template_argument_list;
	size_t saved_function_template_argument_substitution_floor =
		ctx.function_template_argument_substitution_floor;
	ctx.function_template_argument_list = true;
	ctx.function_template_argument_substitution_floor =
		ctx.substitutions.size();
	for (size_t i = 0; i < full_args.size(); ++i)
	{
		if (i < declaration->parameters.size())
			out += abi_template_argument_for_parameter_with_substitutions(
				declaration->parameters[i], full_args[i], ctx);
		else
			out += abi_template_argument_with_substitutions(full_args[i], ctx);
	}
	ctx.function_template_argument_list =
		saved_function_template_argument_list;
	ctx.function_template_argument_substitution_floor =
		saved_function_template_argument_substitution_floor;
}

void abi_append_raw_template_argument_list_with_substitutions(
	string& out,
	const vector<TemplateArgument>& full_args,
	AbiSubstitutionContext& ctx)
{
	bool saved_function_template_argument_list =
		ctx.function_template_argument_list;
	size_t saved_function_template_argument_substitution_floor =
		ctx.function_template_argument_substitution_floor;
	ctx.function_template_argument_list = true;
	ctx.function_template_argument_substitution_floor =
		ctx.substitutions.size();
	for (size_t i = 0; i < full_args.size(); ++i)
		out += abi_template_argument_with_substitutions(full_args[i], ctx);
	ctx.function_template_argument_list =
		saved_function_template_argument_list;
	ctx.function_template_argument_substitution_floor =
		saved_function_template_argument_substitution_floor;
}

TypePtr abi_owner_record_for_special_member(const Binding* binding)
{
	TypePtr owner_record = pa11::record_type_for_scope(binding->owner);
	owner_record = owner_record.get() != NULL
		? pa11::strip_cv(owner_record) : TypePtr();
	if (binding->type->parameters.empty())
		return owner_record;
	TypePtr this_type = pa11::strip_cv(binding->type->parameters[0]);
	if (this_type.get() == NULL || this_type->kind != pa11::TypeKind::Pointer)
		return owner_record;
	TypePtr this_record = pa11::strip_cv(this_type->base);
	if (this_record.get() != NULL &&
	    this_record->kind == pa11::TypeKind::Record &&
	    this_record->is_template_specialization &&
	    !this_record->template_primary_name.empty() &&
	    (binding->name == this_record->template_primary_name ||
	     binding->name == binding->owner->name))
		return this_record;
	return owner_record;
}

size_t abi_local_find_substitution(const AbiSubstitutionContext& ctx,
                                   const string& encoded)
{
	map<string, size_t>::const_iterator alias =
		ctx.substitution_aliases.find(encoded);
	if (alias != ctx.substitution_aliases.end())
		return alias->second;
	for (size_t i = 0; i < ctx.substitutions.size(); ++i)
		if (ctx.substitutions[i] == encoded)
			return i;
	return static_cast<size_t>(-1);
}

void abi_seed_member_owner_type_substitution(const Binding* binding,
                                             AbiSubstitutionContext& ctx)
{
	if (binding == NULL ||
	    binding->kind != BindingKind::Function ||
	    binding->owner == NULL ||
	    binding->owner->kind != ScopeKind::Class ||
	    binding->is_static_member)
		return;
	TypePtr owner_record = pa11::record_type_for_scope(binding->owner);
	owner_record = owner_record.get() != NULL
		? pa11::strip_cv(owner_record) : TypePtr();
	if (owner_record.get() == NULL ||
	    owner_record->kind != pa11::TypeKind::Record)
		return;
	map<string, size_t> empty_template_parameters;
	AbiSubstitutionContext clean_ctx(empty_template_parameters, NULL, NULL);
	string canonical_owner =
		abi_record_type_with_substitutions(owner_record, clean_ctx, true);
	size_t existing = abi_local_find_substitution(ctx, canonical_owner);
	if (existing != static_cast<size_t>(-1))
	{
		string substituted_probe =
			abi_record_type_probe_with_substitutions(owner_record,
			                                        ctx,
			                                        true);
		if (!substituted_probe.empty())
			ctx.substitution_aliases[substituted_probe] = existing;
		return;
	}
	abi_record_type_with_substitutions(owner_record, ctx, true);
}

	string abi_special_member_symbol_with_substitutions(
		const Binding* binding,
		AbiSubstitutionContext& ctx)
	{
	if (binding->kind != BindingKind::Function ||
	    binding->owner == NULL ||
	    binding->owner->kind != ScopeKind::Class ||
	    binding->type.get() == NULL ||
	    binding->type->kind != pa11::TypeKind::Function)
		return "";
	TypePtr owner_record = abi_owner_record_for_special_member(binding);
	bool constructor =
		binding->name == binding->owner->name ||
		(owner_record.get() != NULL &&
		 owner_record->is_template_specialization &&
		 !owner_record->template_primary_name.empty() &&
		 binding->name == owner_record->template_primary_name);
		bool destructor = !binding->name.empty() && binding->name[0] == '~';
		if (owner_record.get() == NULL || (!constructor && !destructor))
			return "";
		string abi_tags;
		for (size_t i = 0; i < binding->abi_tags.size(); ++i)
			abi_tags += "B" + abi_source_name(binding->abi_tags[i]);
		string owner_name =
			abi_record_type_with_substitutions(owner_record, ctx, true);
		string encoded_name;
	if (owner_name.size() >= 2 &&
	    owner_name[0] == 'N' &&
		    owner_name[owner_name.size() - 1] == 'E')
			encoded_name = owner_name.substr(0, owner_name.size() - 1) +
			               (constructor ? "C1" : "D1") + abi_tags + "E";
		else
			encoded_name = "N" + owner_name +
			               (constructor ? "C1" : "D1") + abi_tags + "E";
	string bare;
	for (size_t i = 1; i < binding->type->parameters.size(); ++i)
		bare += abi_function_parameter_type_with_substitutions(
			binding->type->parameters[i], ctx);
	if (binding->type->parameters.size() == 1)
		bare += "v";
	return "_Z" + encoded_name + bare;
}

string abi_constructor_template_specialization_symbol(
	TemplateDeclaration* declaration,
	const vector<TemplateArgument>& full_args,
	Binding* binding,
	AbiSubstitutionContext& ctx,
	const string& encoded_prefix,
	TypePtr fn_type)
{
	TypePtr owner_record = pa11::record_type_for_scope(binding->owner);
	bool emit_template_args =
		!declaration->class_template_member ||
		!template_arguments_match_owner_record(owner_record, full_args);
	string encoded_name = encoded_prefix + "C1";
	if (emit_template_args)
	{
		encoded_name += "I";
		abi_append_template_argument_list_with_substitutions(
			encoded_name, declaration, full_args, ctx);
		encoded_name += "E";
	}
	encoded_name += "E";
	string bare;
	TypePtr bare_fn_type =
		fn_type.get() != NULL &&
		fn_type->kind == pa11::TypeKind::Function
		? fn_type : binding->type;
	size_t first_param = 1;
	for (size_t i = first_param; i < bare_fn_type->parameters.size(); ++i)
	{
		string encoded_param = abi_function_parameter_type_with_substitutions(
			bare_fn_type->parameters[i], ctx);
		string pack_name;
		bare += function_parameter_pack_name(declaration,
		                                     bare_fn_type->parameters[i],
		                                     pack_name)
			? "Dp" + encoded_param : encoded_param;
	}
	if (bare_fn_type->parameters.size() == first_param)
		bare += "v";
	string symbol = "_Z" + encoded_name + bare;
	return symbol;
}

string abi_binding_symbol_with_substitutions(
	const Binding* binding,
	const map<string, size_t>& template_parameters)
{
	if (binding == NULL)
		return "_Z0v";
	if (binding->aliased_binding != NULL &&
	    !abi_binding_alias_preserves_owner(binding) &&
	    abi_binding_alias_symbol_equivalent(binding))
		binding = binding->aliased_binding;
	if (binding->kind == BindingKind::Function &&
	    !binding->function_specialization_symbol.empty())
		return binding->function_specialization_symbol;
	if (binding->kind != BindingKind::Function &&
	    (binding->owner == NULL ||
	     (binding->owner->kind == ScopeKind::Namespace &&
	      binding->owner->name.empty())))
		return binding->name;
	AbiSubstitutionContext ctx(template_parameters, NULL, NULL);
	ctx.dependent_typename_scope_prefix =
		abi_dependent_typename_scope_prefix_for_binding(binding);
	string special_member =
		abi_special_member_symbol_with_substitutions(binding, ctx);
	if (!special_member.empty())
		return special_member;
	if (binding->kind != BindingKind::Function ||
	    binding->type.get() == NULL ||
	    binding->type->kind != pa11::TypeKind::Function)
	{
		string encoded_name =
			abi_encode_binding_name_with_substitutions(binding, ctx);
		return "_Z" + encoded_name;
	}
	string encoded_name;
	if (binding->name.compare(0, 9, "operator ") == 0)
	{
		if (binding->owner != NULL &&
		    binding->owner->kind == ScopeKind::Class)
		{
			vector<Scope*> scopes =
				abi_binding_scope_path_outer_first(binding);
			encoded_name = "N";
			abi_append_member_function_name_qualifiers(
				encoded_name, binding, binding->type);
			encoded_name += abi_scope_prefix_with_substitutions(scopes, ctx);
			encoded_name += "cv" +
				abi_type_with_substitutions(binding->type->base,
				                            ctx);
			encoded_name += "E";
		}
		else
			encoded_name = "cv" +
				abi_type_with_substitutions(binding->type->base,
				                            ctx);
	}
	else
		encoded_name =
			abi_encode_binding_name_with_substitutions(binding, ctx);
	abi_seed_member_owner_type_substitution(binding, ctx);
	string bare;
	size_t first_param =
		binding->owner != NULL &&
		binding->owner->kind == ScopeKind::Class &&
		!binding->is_static_member ? 1 : 0;
	for (size_t i = first_param; i < binding->type->parameters.size(); ++i)
		bare += abi_function_parameter_type_with_substitutions(
			binding->type->parameters[i], ctx);
	if (binding->type->variadic)
		bare += "z";
	else if (binding->type->parameters.size() == first_param)
		bare += "v";
	return "_Z" + encoded_name + bare;
}

string abi_function_template_specialization_symbol_with_substitutions(
	TemplateDeclaration* declaration,
	const vector<TemplateArgument>& full_args,
	Binding* binding,
	const vector<Token>* expression_tokens)
{
	map<string, size_t> template_parameters;
	for (size_t i = 0; i < declaration->parameters.size(); ++i)
		if (!declaration->parameters[i].name.empty())
			template_parameters[declaration->parameters[i].name] = i;
	const vector<string>* parameter_names =
		declaration->function_parameter_names.empty()
		? binding != NULL && !binding->function_parameter_names.empty()
		  ? &binding->function_parameter_names
		  : NULL
		: &declaration->function_parameter_names;
	AbiSubstitutionContext ctx(template_parameters,
	                           expression_tokens,
	                           parameter_names);
	ctx.actual_template_arguments = full_args;
	ctx.dependent_typename_scope_prefix =
		abi_dependent_typename_scope_prefix_for_binding(binding);
	string encoded_name;
	TypePtr fn_type = declaration->generic_function_type;
	bool constructor_template =
		binding != NULL &&
		binding->owner != NULL &&
		binding->owner->kind == ScopeKind::Class &&
		binding->name == binding->owner->name;
	bool conversion_operator_template =
		declaration->name.compare(0, 9, "operator ") == 0 &&
		fn_type.get() != NULL &&
		fn_type->kind == pa11::TypeKind::Function;
	if (binding != NULL &&
	    binding->owner != NULL &&
	    binding->owner->kind == ScopeKind::Class)
	{
		TypePtr owner_record = pa11::record_type_for_scope(binding->owner);
		encoded_name = "N";
		abi_append_member_function_name_qualifiers(
			encoded_name, binding, fn_type);
		string owner_name =
			abi_record_type_with_substitutions(owner_record, ctx, true);
		if (owner_name.size() >= 2 &&
		    owner_name[0] == 'N' &&
		    owner_name[owner_name.size() - 1] == 'E')
			encoded_name += owner_name.substr(1, owner_name.size() - 2);
		else
			encoded_name += owner_name;
	}
	if (constructor_template)
	{
		return abi_constructor_template_specialization_symbol(
			declaration, full_args, binding, ctx, encoded_name, fn_type);
	}
	if (conversion_operator_template)
	{
		if (encoded_name.empty())
			encoded_name = "cv" +
				abi_type_with_substitutions(fn_type->base, ctx) + "I";
		else
			encoded_name += "cv" +
				abi_type_with_substitutions(fn_type->base, ctx) + "I";
		abi_append_raw_template_argument_list_with_substitutions(
			encoded_name, full_args, ctx);
		encoded_name += "E";
		if (binding != NULL &&
		    binding->owner != NULL &&
		    binding->owner->kind == ScopeKind::Class)
			encoded_name += "E";
	}
	else if (binding != NULL &&
	         binding->owner != NULL &&
	         binding->owner->kind == ScopeKind::Class)
	{
		string member_name = abi_binding_source_name(binding);
		encoded_name += member_name + "I";
		abi_append_template_argument_list_with_substitutions(
			encoded_name, declaration, full_args, ctx);
		encoded_name += "EE";
	}
	else
		encoded_name =
			abi_encode_function_template_name_with_substitutions(
				declaration, full_args, binding, ctx);
	string bare = abi_function_return_type_with_substitutions(fn_type->base,
	                                                         ctx);
	size_t first_param =
		binding != NULL &&
		binding->owner != NULL &&
		binding->owner->kind == ScopeKind::Class &&
		!binding->is_static_member ? 1 : 0;
	for (size_t i = first_param; i < fn_type->parameters.size(); ++i)
	{
		TypePtr param = fn_type->parameters[i];
		TypePtr bare_param = param.get() != NULL ? pa11::strip_cv(param) : TypePtr();
		if (bare_param.get() != NULL &&
		    bare_param->kind == pa11::TypeKind::TemplateParameter &&
		    ctx.actual_template_parameter_substitutions.find(
			    bare_param->name) !=
			    ctx.actual_template_parameter_substitutions.end())
		{
			bool saved = ctx.use_actual_template_parameter_types;
			ctx.use_actual_template_parameter_types = true;
			bare += abi_function_parameter_type_with_substitutions(
				param, ctx);
			ctx.use_actual_template_parameter_types = saved;
		}
		else
			bare += abi_function_parameter_type_with_substitutions(
				param, ctx);
	}
	if (fn_type->variadic)
		bare += "z";
	else if (fn_type->parameters.size() == first_param)
		bare += "v";
	return "_Z" + encoded_name + bare;
}

string abi_function_template_specialization_symbol(
	TemplateDeclaration* declaration,
	const vector<TemplateArgument>& full_args,
	Binding* binding,
	const vector<Token>* expression_tokens)
{
	return abi_function_template_specialization_symbol_with_substitutions(
		declaration, full_args, binding, expression_tokens);
}


}  // namespace internal
}  // namespace pa12
