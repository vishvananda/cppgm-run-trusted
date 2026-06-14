#include "pa12_templates_function_instantiation_engine.h"

#include <stdexcept>

using namespace std;

namespace pa12 {
namespace internal {

namespace {

bool scope_has_namespace_named(Scope* scope, const string& name)
{
	for (Scope* cur = scope; cur != NULL; cur = cur->parent)
		if (cur->kind == ScopeKind::Namespace && cur->name == name)
			return true;
	return false;
}

bool hosted_std_template_declaration(const TemplateDeclaration* declaration,
                                     const string& name)
{
	if (declaration == NULL || declaration->name != name)
		return false;
	Scope* scope = declaration->placeholder != NULL
		? declaration->placeholder->owner : declaration->owner;
	return scope_has_namespace_named(scope, "std");
}

string unqualified_template_primary_name(TypePtr type)
{
	TypePtr bare = type.get() != NULL ? pa11::strip_cv(type) : TypePtr();
	if (bare.get() == NULL)
		return "";
	string primary = bare->template_primary_name.empty()
		? bare->name : bare->template_primary_name;
	size_t pos = primary.rfind("::");
	return pos == string::npos ? primary : primary.substr(pos + 2);
}

bool hosted_std_template_record(TypePtr type, const string& primary)
{
	TypePtr bare = type.get() != NULL ? pa11::strip_cv(type) : TypePtr();
	return bare.get() != NULL &&
	       bare->kind == pa11::TypeKind::Record &&
	       bare->is_template_specialization &&
	       unqualified_template_primary_name(bare) == primary &&
	       scope_has_namespace_named(bare->scope, "std");
}

bool hosted_std_member_template_declaration(
	const TemplateDeclaration* declaration,
	const string& owner_primary,
	const string& name)
{
	if (declaration == NULL || declaration->name != name ||
	    declaration->owner == NULL ||
	    declaration->owner->kind != ScopeKind::Class)
		return false;
	return hosted_std_template_record(
		pa11::record_type_for_scope(declaration->owner),
		owner_primary);
}

TypePtr hosted_forwarding_argument_parameter(TypePtr argument)
{
	if (argument.get() == NULL)
		return argument;
	TypePtr bare = pa11::strip_cv(argument);
	if (bare->kind == pa11::TypeKind::LValueReference ||
	    bare->kind == pa11::TypeKind::RValueReference)
		return argument;
	return pa11::make_rvalue_reference(argument);
}

}  // namespace

Binding* FunctionTemplateInstantiationEngine::instantiate_with_substitutions(
	bool full_args_dependent)
{
	(void)full_args_dependent;
	bool argument_dependent = instantiated_arguments_are_dependent();
	if (argument_dependent)
		return instantiate_dependent_signature();
	if (!declaration->constructor_template &&
	    should_create_candidate_signature(has_template_parameter_default()))
		return instantiate_candidate_signature(argument_dependent);
	if (declaration->constructor_template &&
	    p.function_template_candidate_instantiation_depth_ != 0)
		return instantiate_constructor_candidate();
	Binding* member_body = instantiate_deferred_member_body();
	if (member_body != NULL)
		return member_body;
	return replay_function_template();
}

TypePtr FunctionTemplateInstantiationEngine::substitute_dependent_signature_type()
{
	try
	{
		return p.substitute_function_template_type(
			declaration,
			declaration->generic_function_type);
	}
	catch (const runtime_error& err)
	{
		if (p.function_template_candidate_instantiation_depth_ == 0 ||
		    string(err.what()) != "dependent typename not resolved" ||
		    declaration->generic_function_type.get() == NULL ||
		    declaration->generic_function_type->kind != pa11::TypeKind::Function)
			throw;
		vector<TypePtr> params;
		for (size_t i = 0;
		     i < declaration->generic_function_type->parameters.size(); ++i)
			params.push_back(p.substitute_template_type(
				declaration->generic_function_type->parameters[i]));
		TypePtr type = pa11::make_function(
			declaration->generic_function_type->base,
			params,
			declaration->generic_function_type->variadic);
		type->cv = declaration->generic_function_type->cv;
		type->ref_qualifier =
			declaration->generic_function_type->ref_qualifier;
		return type;
	}
}

Binding* FunctionTemplateInstantiationEngine::instantiate_dependent_signature()
{
	TypePtr type = substitute_dependent_signature_type();
	Binding* binding = create_specialization_binding(type, false);
	copy_placeholder_properties(binding, true);
	assign_specialization_symbol(binding, false);
	register_specialization(binding, true);
	return finish_with_restore(binding);
}

TypePtr FunctionTemplateInstantiationEngine::generic_return_type() const
{
	return declaration->generic_function_type.get() != NULL &&
	       declaration->generic_function_type->kind == pa11::TypeKind::Function
		? pa11::strip_cv(declaration->generic_function_type->base)
		: TypePtr();
}

bool FunctionTemplateInstantiationEngine::generic_return_is_decltype() const
{
	TypePtr result = generic_return_type();
	return result.get() != NULL && result->is_dependent_typename &&
	       result->dependent_typename_decltype;
}

bool FunctionTemplateInstantiationEngine::has_template_parameter_default() const
{
	for (size_t i = 0; i < declaration->parameters.size(); ++i)
		if (declaration->parameters[i].has_default)
			return true;
	return false;
}

bool FunctionTemplateInstantiationEngine::should_create_candidate_signature(
	bool has_template_default) const
{
	bool replay_candidate_signature =
		p.function_template_candidate_instantiation_depth_ != 0 &&
		declaration->has_definition &&
		declaration->decl_begin < declaration->decl_end &&
		has_template_default;
	if (replay_candidate_signature)
		return false;
	if (!declaration->has_definition &&
	    (p.replaying_dependent_decltype_ ||
	     (p.function_template_candidate_instantiation_depth_ != 0 &&
	      !generic_return_is_decltype())))
		return true;
	return p.function_template_candidate_instantiation_depth_ != 0;
}

TypePtr FunctionTemplateInstantiationEngine::substitute_candidate_signature_type(
	bool generic_return_is_decltype,
	bool& deferred_candidate_return)
{
	deferred_candidate_return =
		p.function_template_candidate_instantiation_depth_ != 0 &&
		generic_return_is_decltype &&
		instantiated_arguments_are_dependent() &&
		declaration->generic_function_type.get() != NULL &&
		declaration->generic_function_type->kind == pa11::TypeKind::Function;
	if (deferred_candidate_return)
	{
		vector<TypePtr> params;
		for (size_t i = 0;
		     i < declaration->generic_function_type->parameters.size(); ++i)
		{
			TypePtr pattern = declaration->generic_function_type->parameters[i];
			string pack_name;
			TemplateArgument pack_subst;
			if (function_parameter_pack_name(declaration, pattern, pack_name) &&
			    p.find_template_value_substitution(pack_name, pack_subst) &&
			    pack_subst.kind == TemplateArgumentKind::Pack)
			{
				for (size_t pidx = 0; pidx < pack_subst.pack.size(); ++pidx)
				{
					if (pack_subst.pack[pidx].kind !=
					    TemplateArgumentKind::Type)
						throw runtime_error("type parameter pack required");
					TypePtr element = p.substitute_template_type_parameter(
						pattern,
						pack_name,
						pack_subst.pack[pidx].type);
					params.push_back(p.substitute_template_type(element));
				}
				continue;
			}
			params.push_back(p.substitute_template_type(pattern));
		}
		TypePtr type = pa11::make_function(
			declaration->generic_function_type->base,
			params,
			declaration->generic_function_type->variadic);
		type->cv = declaration->generic_function_type->cv;
		type->ref_qualifier =
			declaration->generic_function_type->ref_qualifier;
		return type;
	}
	try
	{
		return p.substitute_function_template_type(
			declaration,
			declaration->generic_function_type);
	}
	catch (const runtime_error& err)
	{
		string message = err.what();
		if (p.function_template_candidate_instantiation_depth_ == 0 ||
		    !generic_return_is_decltype ||
		    message.compare(0, 16, "name not found: ") != 0 ||
		    declaration->generic_function_type.get() == NULL ||
		    declaration->generic_function_type->kind != pa11::TypeKind::Function)
			throw;
		vector<TypePtr> params;
		for (size_t i = 0;
		     i < declaration->generic_function_type->parameters.size(); ++i)
			params.push_back(p.substitute_template_type(
				declaration->generic_function_type->parameters[i]));
		TypePtr type = pa11::make_function(
			declaration->generic_function_type->base,
			params,
			declaration->generic_function_type->variadic);
		type->cv = declaration->generic_function_type->cv;
		type->ref_qualifier =
			declaration->generic_function_type->ref_qualifier;
		deferred_candidate_return = true;
		return type;
	}
}

Binding* FunctionTemplateInstantiationEngine::instantiate_candidate_signature(
	bool argument_dependent)
{
	bool deferred_candidate_return = false;
	TypePtr type = substitute_candidate_signature_type(
		generic_return_is_decltype(),
		deferred_candidate_return);
	(void)argument_dependent;
	model_hosted_candidate_type(type);
	if (invalid_candidate_signature(type, deferred_candidate_return))
		throw runtime_error("invalid substituted function type");
	Binding* binding = create_specialization_binding(type, false);
	copy_placeholder_properties(binding, true);
	if (replaced_specialization != NULL && replaced_specialization != binding)
		replaced_specialization->aliased_binding = binding;
	assign_specialization_symbol(binding, true);
	register_specialization(binding, false);
	return finish_with_restore(binding);
}

bool FunctionTemplateInstantiationEngine::invalid_candidate_signature(
	TypePtr type,
	bool deferred_candidate_return) const
{
	bool invalid = deferred_candidate_return
		? !substituted_function_parameter_types_are_valid(type)
		: !substituted_type_is_valid(type);
	if (invalid &&
	    p.function_template_candidate_instantiation_depth_ != 0 &&
	    type.get() != NULL &&
	    type->kind == pa11::TypeKind::Function &&
	    deferred_candidate_return &&
	    ((p.type_is_template_dependent(type->base) &&
	      substituted_function_parameter_types_are_valid(type)) ||
	     substituted_candidate_function_parameter_types_are_valid(type)))
		invalid = false;
	return invalid;
}

void FunctionTemplateInstantiationEngine::model_hosted_candidate_type(
	TypePtr& type)
{
	model_hosted_write_type(type);
	model_hosted_function_assignment_type(type);
	model_hosted_vector_insert_type(type);
}

void FunctionTemplateInstantiationEngine::model_hosted_write_type(TypePtr& type)
{
	if (!p.hosted_compatibility_ ||
	    p.function_template_candidate_instantiation_depth_ == 0 ||
	    !hosted_std_template_declaration(declaration, "__write") ||
	    type.get() == NULL || type->kind != pa11::TypeKind::Function ||
	    (!type_structurally_dependent(type) && substituted_type_is_valid(type)) ||
	    full_args.empty() || full_args[0].kind != TemplateArgumentKind::Type ||
	    full_args[0].type.get() == NULL ||
	    type_structurally_dependent(full_args[0].type))
		return;
	TypePtr char_type = full_args[0].type;
	TypePtr out_iter;
	if (full_args.size() == 1)
	{
		TemplateDeclaration* iter_template =
			p.find_class_template(declaration->owner,
			                      "ostreambuf_iterator");
		if (iter_template != NULL)
		{
			vector<TemplateArgument> iter_args;
			iter_args.push_back(TemplateArgument::type_arg(char_type));
			try
			{
				out_iter = p.instantiate_class_template(iter_template,
				                                       iter_args);
			}
			catch (const exception&)
			{
				out_iter = TypePtr();
			}
		}
	}
	else if (full_args.size() >= 2 &&
	         full_args[1].kind == TemplateArgumentKind::Type &&
	         full_args[1].type.get() != NULL &&
	         !type_structurally_dependent(full_args[1].type))
		out_iter = full_args[1].type;
	if (out_iter.get() == NULL || type_structurally_dependent(out_iter))
		return;
	vector<TypePtr> params;
	params.push_back(out_iter);
	params.push_back(pa11::make_pointer(
		pa11::make_cv(char_type, pa11::CV_CONST)));
	params.push_back(pa11::make_fundamental(FT_INT));
	TypePtr modeled = pa11::make_function(out_iter, params, false);
	modeled->cv = type->cv;
	modeled->ref_qualifier = type->ref_qualifier;
	type = modeled;
}

void FunctionTemplateInstantiationEngine::
model_hosted_function_assignment_type(TypePtr& type)
{
	if (!p.hosted_compatibility_ ||
	    p.function_template_candidate_instantiation_depth_ == 0 ||
	    type.get() == NULL || type->kind != pa11::TypeKind::Function ||
	    (!type_structurally_dependent(type) && substituted_type_is_valid(type)) ||
	    !hosted_std_member_template_declaration(declaration,
	                                            "function",
	                                            "operator=") ||
	    full_args.empty() || full_args[0].kind != TemplateArgumentKind::Type ||
	    full_args[0].type.get() == NULL ||
	    type_structurally_dependent(full_args[0].type))
		return;
	TypePtr owner_record = pa11::record_type_for_scope(declaration->owner);
	owner_record = owner_record.get() != NULL
		? pa11::strip_cv(owner_record) : TypePtr();
	if (!hosted_std_template_record(owner_record, "function") ||
	    type->parameters.size() != 2)
		return;
	vector<TypePtr> params;
	params.push_back(type->parameters[0]);
	params.push_back(hosted_forwarding_argument_parameter(full_args[0].type));
	TypePtr modeled = pa11::make_function(
		pa11::make_lvalue_reference(owner_record),
		params,
		false);
	modeled->cv = type->cv;
	modeled->ref_qualifier = type->ref_qualifier;
	type = modeled;
}

void FunctionTemplateInstantiationEngine::model_hosted_vector_insert_type(
	TypePtr& type)
{
	if (!p.hosted_compatibility_ ||
	    p.function_template_candidate_instantiation_depth_ == 0 ||
	    type.get() == NULL || type->kind != pa11::TypeKind::Function ||
	    (!type_structurally_dependent(type) && substituted_type_is_valid(type)) ||
	    !hosted_std_member_template_declaration(declaration,
	                                            "vector",
	                                            "insert") ||
	    full_args.empty() || full_args[0].kind != TemplateArgumentKind::Type ||
	    full_args[0].type.get() == NULL ||
	    type_structurally_dependent(full_args[0].type) ||
	    type->parameters.size() != 4)
		return;
	vector<TypePtr> params = type->parameters;
	params[2] = full_args[0].type;
	params[3] = full_args[0].type;
	TypePtr modeled = pa11::make_function(type->base, params, false);
	modeled->cv = type->cv;
	modeled->ref_qualifier = type->ref_qualifier;
	if (!type_structurally_dependent(modeled))
		type = modeled;
}

TypePtr FunctionTemplateInstantiationEngine::substitute_constructor_candidate_type()
{
	return p.substitute_function_template_type(
		declaration,
		declaration->generic_function_type);
}

Binding* FunctionTemplateInstantiationEngine::instantiate_constructor_candidate()
{
	TypePtr type = substitute_constructor_candidate_type();
	if (!substituted_type_is_valid(type))
		throw runtime_error("invalid substituted constructor type");
	Binding* binding = create_specialization_binding(type, true);
	copy_placeholder_properties(binding, false);
	if (replaced_specialization != NULL && replaced_specialization != binding)
		replaced_specialization->aliased_binding = binding;
	assign_specialization_symbol(binding, true);
	register_specialization(binding, true);
	return finish_with_restore(binding);
}

Binding* FunctionTemplateInstantiationEngine::create_specialization_binding(
	TypePtr type,
	bool force_value)
{
	bool distinct_conversion_template =
		declaration->name.compare(0, 9, "operator ") == 0 &&
		!declaration->class_template_member;
	Binding* binding =
		force_value ||
		p.function_template_candidate_instantiation_depth_ != 0 ||
		distinct_conversion_template
		? p.add_value(declaration->owner,
		              BindingKind::Function,
		              declaration->name,
		              type)
		: p.add_function_binding(declaration->owner,
		                         declaration->name,
		                         type,
		                         declaration->hidden_friend);
	binding->is_hidden_friend = declaration->hidden_friend;
	return binding;
}

void FunctionTemplateInstantiationEngine::copy_placeholder_properties(
	Binding* binding,
	bool copy_defaults)
{
	if (declaration->placeholder == NULL)
		return;
	binding->is_static_member = declaration->placeholder->is_static_member;
	binding->is_constexpr = declaration->placeholder->is_constexpr;
	binding->is_explicit = declaration->placeholder->is_explicit;
	binding->is_private = declaration->placeholder->is_private;
	binding->is_protected_member =
		declaration->placeholder->is_protected_member;
	binding->ref_qualifier = declaration->placeholder->ref_qualifier;
	binding->unwind_no = declaration->placeholder->unwind_no;
	if (declaration->placeholder->reserve_primary_function_symbol)
		binding->reserve_primary_function_symbol = true;
	if (!copy_defaults)
		return;
	map<Binding*, vector<Expr> >::const_iterator defaults =
		p.default_arguments_.find(declaration->placeholder);
	if (defaults != p.default_arguments_.end())
		p.default_arguments_[binding] = defaults->second;
}

void FunctionTemplateInstantiationEngine::assign_specialization_symbol(
	Binding* binding,
	bool include_non_member)
{
	if (declaration->class_template_member)
		binding->function_specialization_symbol =
			constructor_template_function_template_symbol(declaration) ||
			class_template_member_function_template_symbol(declaration)
			? abi_function_template_specialization_symbol(
				declaration,
				full_args,
				binding,
				&p.declaration_tokens_)
			: abi_binding_symbol(binding, map<string, size_t>());
	else if (include_non_member)
		binding->function_specialization_symbol =
			abi_function_template_specialization_symbol(
				declaration,
				full_args,
				binding,
				&p.declaration_tokens_);
}

void FunctionTemplateInstantiationEngine::assign_aliased_class_member_symbol(
	Binding* binding)
{
	if (!declaration->class_template_member ||
	    binding == NULL || binding->aliased_binding == NULL)
		return;
	binding->aliased_binding->function_specialization_symbol =
		constructor_template_function_template_symbol(declaration) ||
		class_template_member_function_template_symbol(declaration)
		? abi_function_template_specialization_symbol(
			declaration,
			full_args,
			binding->aliased_binding,
			&p.declaration_tokens_)
		: abi_binding_symbol(binding->aliased_binding,
		                     map<string, size_t>());
}

void FunctionTemplateInstantiationEngine::register_specialization(
	Binding* binding,
	bool keep_placeholder_for_member)
{
	declaration->function_specializations[key] = binding;
	if (declaration->friend_class_scope != NULL)
		p.add_friend_function(declaration->friend_class_scope, binding);
	if (keep_placeholder_for_member ||
	    !declaration->class_template_member ||
	    p.function_template_candidate_instantiation_depth_ != 0)
	{
		p.function_template_placeholders_[binding] = declaration;
		p.function_template_specialization_arguments_[binding] = full_args;
	}
}

}  // namespace internal
}  // namespace pa12
