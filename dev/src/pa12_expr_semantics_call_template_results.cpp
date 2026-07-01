#include "pa12_expr_semantics_call_template_instantiator.h"
#include "pa12_expr_semantics_support.h"
#include "pa12_templates_function_support.h"
#include "pa12_types_support.h"

#include <algorithm>
#include <cstdint>
#include <stdexcept>

using namespace std;

namespace pa12 {
namespace internal {

namespace {
string call_template_unqualified_primary(TypePtr type)
{
	TypePtr bare = type.get() != NULL ? pa11::strip_cv(type) : TypePtr();
	if (bare.get() == NULL)
		return "";
	string primary = bare->template_primary_name.empty()
		? bare->name : bare->template_primary_name;
	size_t pos = primary.rfind("::");
	return pos == string::npos ? primary : primary.substr(pos + 2);
}

bool invalid_enable_if_return_candidate(Binding* binding)
{
	if (binding == NULL ||
	    binding->type.get() == NULL ||
	    binding->type->kind != pa11::TypeKind::Function ||
	    substituted_type_is_valid(binding->type))
		return false;
	TypePtr result = binding->type->base.get() != NULL
		? pa11::strip_cv(binding->type->base) : TypePtr();
	if (result.get() == NULL || !result->is_dependent_typename)
		return false;
	string primary = call_template_unqualified_primary(result);
	return primary == "enable_if" ||
	       primary == "enable_if_t" ||
	       primary == "__enable_if_t";
}

void apply_hosted_invoke_return_type(const TemplateDeclaration* declaration,
                                     Binding* instantiated,
                                     const vector<TemplateArgument>& arguments)
{
	if ((!hosted_std_function_template_declaration(declaration,
	                                               "__invoke_impl") &&
	     !hosted_std_function_template_declaration(declaration,
	                                               "__invoke_r")) ||
	    instantiated == NULL ||
	    instantiated->type.get() == NULL ||
	    instantiated->type->kind != pa11::TypeKind::Function ||
	    arguments.empty() ||
	    arguments[0].kind != TemplateArgumentKind::Type ||
	    arguments[0].type.get() == NULL)
		return;
	TypePtr modeled = pa11::make_function(arguments[0].type,
	                                      instantiated->type->parameters,
	                                      instantiated->type->variadic);
	modeled->cv = instantiated->type->cv;
	modeled->ref_qualifier = instantiated->type->ref_qualifier;
	instantiated->type = modeled;
}

}  // namespace

void TemplateCallCandidateInstantiator::add_recovered_friend_bindings()
{
	if (declaration == original_declaration || declaration->placeholder == NULL)
		return;
	if (p.hosted_compatibility_ &&
	    p.function_template_candidate_instantiation_depth_ != 0 &&
	    declaration->constructor_template &&
	    p.hosted_library_function(declaration->placeholder))
		return;
	pair<pair<TemplateDeclaration*, TemplateDeclaration*>, size_t> cache_key =
		make_pair(make_pair(original_declaration, declaration),
		          p.class_friend_function_generation_);
	if (!p.recovered_friend_binding_scans_.insert(cache_key).second)
		return;
	for (map<Scope*, vector<Binding*> >::const_iterator it =
		     p.class_friend_functions_.begin();
	     it != p.class_friend_functions_.end(); ++it)
		for (size_t i = 0; i < it->second.size(); ++i)
		{
			Binding* friend_binding = it->second[i];
			bool same_friend = original_declaration->placeholder != NULL &&
				friend_binding == original_declaration->placeholder;
			if (!same_friend && friend_binding->kind == BindingKind::Function &&
			    friend_binding->name == declaration->name &&
			    same_template_signature_type(friend_binding->type,
			                                 declaration->generic_function_type))
				same_friend = true;
			if (same_friend)
				p.add_friend_function(it->first, declaration->placeholder);
		}
}

void TemplateCallCandidateInstantiator::apply_basic_string_result(
	Binding* instantiated)
{
	if (!p.hosted_compatibility_ ||
	    !hosted_std_basic_string_operator_template_declaration(declaration) ||
	    instantiated == NULL || instantiated->type.get() == NULL ||
	    instantiated->type->kind != pa11::TypeKind::Function ||
	    !type_structurally_dependent(instantiated->type) ||
	    declaration->generic_function_type.get() == NULL ||
	    declaration->generic_function_type->kind != pa11::TypeKind::Function ||
	    declaration->generic_function_type->parameters.size() != args.size())
		return;
	TypePtr string_type;
	for (size_t ai = 0; ai < args.size(); ++ai)
	{
		TypePtr object = pa11::strip_cv(p.expression_object_type(args[ai].type));
		if (hosted_basic_string_type(object) &&
		    !type_structurally_dependent(object))
		{
			string_type = object;
			break;
		}
	}
	TypePtr char_type;
	if (string_type.get() != NULL)
	{
		TypePtr bare_string = pa11::strip_cv(string_type);
		if (!bare_string->template_arguments.empty() &&
		    bare_string->template_arguments[0].kind ==
			    pa11::TemplateInstanceArgumentKind::Type)
			char_type = bare_string->template_arguments[0].type;
		else
		{
			map<const void*, vector<TemplateArgument> >::const_iterator found =
				p.record_template_arguments_.find(bare_string.get());
			if (found != p.record_template_arguments_.end() &&
			    !found->second.empty() &&
			    found->second[0].kind == TemplateArgumentKind::Type)
				char_type = found->second[0].type;
		}
	}
	bool has_pattern =
		hosted_basic_string_pattern(declaration->generic_function_type->base);
	vector<TypePtr> params;
	if (string_type.get() != NULL && char_type.get() != NULL)
		for (size_t pi = 0;
		     pi < declaration->generic_function_type->parameters.size(); ++pi)
		{
			TypePtr pattern = declaration->generic_function_type->parameters[pi];
			if (hosted_basic_string_pattern(pattern))
				has_pattern = true;
			params.push_back(substitute_hosted_basic_string_operator_type(
				pattern, string_type, char_type));
		}
	if (!has_pattern ||
	    params.size() != declaration->generic_function_type->parameters.size())
		return;
	TypePtr result = substitute_hosted_basic_string_operator_type(
		declaration->generic_function_type->base, string_type, char_type);
	TypePtr modeled = pa11::make_function(result, params, false);
	modeled->cv = declaration->generic_function_type->cv;
	modeled->ref_qualifier = declaration->generic_function_type->ref_qualifier;
	if (!type_structurally_dependent(modeled))
		instantiated->type = modeled;
}

void TemplateCallCandidateInstantiator::apply_std_function_assignment_result(
	Binding* instantiated)
{
	if (!p.hosted_compatibility_ ||
	    !hosted_std_function_member_template_declaration(declaration,
	                                                     "operator=") ||
	    instantiated == NULL || instantiated->type.get() == NULL ||
	    instantiated->type->kind != pa11::TypeKind::Function ||
	    !type_structurally_dependent(instantiated->type) ||
	    declaration->generic_function_type.get() == NULL ||
	    declaration->generic_function_type->kind != pa11::TypeKind::Function ||
	    declaration->generic_function_type->parameters.size() != 2 ||
	    args.size() != 2 || args[1].type.get() == NULL ||
	    instantiated->owner == NULL ||
	    !hosted_forwarding_template_parameter(
		    declaration->generic_function_type->parameters[1]))
		return;
	TypePtr owner_record = pa11::record_type_for_scope(instantiated->owner);
	owner_record = owner_record.get() != NULL ? pa11::strip_cv(owner_record) : TypePtr();
	TypePtr functor_object = p.expression_object_type(args[1].type);
	TypePtr functor_param = args[1].category == ValueCategory::LValue
		? pa11::make_lvalue_reference(functor_object)
		: pa11::make_rvalue_reference(p.lvalue_to_rvalue_type(args[1].type));
	if (owner_record.get() == NULL ||
	    !hosted_std_function_type(owner_record) ||
	    type_structurally_dependent(owner_record) ||
	    functor_object.get() == NULL ||
	    type_structurally_dependent(functor_object))
		return;
	vector<TypePtr> params;
	params.push_back(instantiated->type->parameters.empty()
	                 ? pa11::make_pointer(owner_record)
	                 : instantiated->type->parameters[0]);
	params.push_back(functor_param);
	TypePtr modeled =
		pa11::make_function(pa11::make_lvalue_reference(owner_record),
		                    params, false);
	modeled->cv = declaration->generic_function_type->cv;
	modeled->ref_qualifier = declaration->generic_function_type->ref_qualifier;
	if (!type_structurally_dependent(modeled))
		instantiated->type = modeled;
}

void TemplateCallCandidateInstantiator::record_replacement(Binding* instantiated)
{
	if (declaration == original_declaration ||
	    !member_call_owner_matches(instantiated))
		return;
	if (recovered_effective_declaration)
	{
		if (original_declaration->placeholder != NULL &&
		    original_declaration->placeholder != instantiated)
			original_declaration->placeholder->aliased_binding = instantiated;
	}
	else
	{
		++p.function_template_candidate_instantiation_depth_;
		vector<TemplateArgument> original_deduced;
		try
		{
			original_deduced =
				p.complete_template_arguments(original_declaration, deduced);
		}
		catch (...)
		{
			--p.function_template_candidate_instantiation_depth_;
			throw;
		}
		--p.function_template_candidate_instantiation_depth_;
		string key = p.template_argument_key(original_deduced);
		map<string, Binding*>::iterator existing =
			original_declaration->function_specializations.find(key);
		if (existing != original_declaration->function_specializations.end() &&
		    existing->second != instantiated)
			existing->second->aliased_binding = instantiated;
		original_declaration->function_specializations[key] = instantiated;
	}
	if (fn != instantiated)
		fn->aliased_binding = instantiated;
}

Binding* TemplateCallCandidateInstantiator::instantiate_deduced()
{
	Scope* saved_friend_class_scope = declaration->friend_class_scope;
	if (declaration->friend_class_scope == NULL &&
	    original_declaration->friend_class_scope != NULL)
		declaration->friend_class_scope =
			original_declaration->friend_class_scope;
	add_recovered_friend_bindings();
	bool entered = false;
	try
	{
		++p.function_template_candidate_instantiation_depth_;
		entered = true;
		Binding* instantiated =
			p.instantiate_function_template(declaration, deduced);
		--p.function_template_candidate_instantiation_depth_;
		entered = false;
		declaration->friend_class_scope = saved_friend_class_scope;
		if (invalid_enable_if_return_candidate(instantiated))
			return NULL;
		if (p.hosted_compatibility_)
			apply_hosted_invoke_return_type(declaration, instantiated, deduced);
		apply_basic_string_result(instantiated);
		apply_std_function_assignment_result(instantiated);
		if (invalid_enable_if_return_candidate(instantiated))
			return NULL;
		if (!member_call_owner_matches(instantiated))
			return NULL;
		record_replacement(instantiated);
		if (instantiated != NULL && instantiated != fn &&
		    p.function_bodies_.find(fn) != p.function_bodies_.end() &&
		    p.function_bodies_.find(instantiated) == p.function_bodies_.end() &&
		    fn->type.get() != NULL && instantiated->type.get() != NULL &&
		    pa11::same_type(fn->type, instantiated->type))
		{
			if (fn->aliased_binding == instantiated)
				fn->aliased_binding = NULL;
			instantiated->aliased_binding = fn;
		}
		if (original_declaration->friend_class_scope != NULL)
			p.add_friend_function(original_declaration->friend_class_scope,
			                      instantiated);
		return instantiated;
	}
	catch (const runtime_error&)
	{
		if (entered)
			--p.function_template_candidate_instantiation_depth_;
		declaration->friend_class_scope = saved_friend_class_scope;
		return NULL;
	}
}

Binding* TemplateCallCandidateInstantiator::run()
{
	if (!member_call_owner_matches(fn))
		return NULL;
	Binding* stored = NULL;
	if (try_stored_concrete_specialization(stored))
		return stored;
	if (!load_template_declaration())
		return fn;
	choose_declaration_with_body();
	recover_effective_declaration();
	select_explicit_arguments();
	Binding* explicit_specialization = NULL;
	if (try_explicit_specialization_for_call(explicit_specialization))
		return explicit_specialization;
	if (!fn_type_dependent && explicit_args.empty() &&
	    !template_declaration_has_body(p.tokens_, declaration))
		return canonical_call_binding(fn);
	if (specialization_candidate && !placeholder_candidate &&
	    declaration == original_declaration && !have_call_explicit_args &&
	    explicit_args.empty())
		return explicit_template_arguments.empty()
			? canonical_call_binding(fn) : NULL;
	Binding* modeled = NULL;
	if (try_modeled_hosted_candidate(modeled))
		return modeled;
	if (!deduce_arguments())
		return NULL;
	return instantiate_deduced();
}

Binding* Parser::instantiate_template_call_candidate(
	Binding* fn,
	const map<Binding*, vector<TemplateArgument> >& explicit_template_arguments,
	const vector<Expr>& args)
{
	TemplateCallCandidateInstantiator instantiator(
		*this, fn, explicit_template_arguments, args);
	return instantiator.run();
}

}  // namespace internal
}  // namespace pa12
