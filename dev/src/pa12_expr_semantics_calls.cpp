#include "pa12_expr_semantics_support.h"
#include "pa12_types_support.h"

#include <algorithm>
#include <stdexcept>

using namespace std;

namespace pa12 {
namespace internal {

namespace {

bool same_parameter_family_ignoring_pointer_cv(TypePtr left, TypePtr right)
{
	if (same_template_signature_type(left, right))
		return true;
	TypePtr l = pa11::strip_cv(left);
	TypePtr r = pa11::strip_cv(right);
	if (l->kind == pa11::TypeKind::Pointer &&
	    r->kind == pa11::TypeKind::Pointer)
		return same_template_signature_type(pa11::strip_cv(l->base),
		                                    pa11::strip_cv(r->base));
	return false;
}

pa11::TemplateInstanceArgument normalize_recovered_template_parameter(
	const pa11::TemplateInstanceArgument& argument,
	const set<string>& names,
	set<const void*>& active);

bool recovered_template_parameter_name_in_argument(
	const pa11::TemplateInstanceArgument& argument,
	const set<string>& names,
	set<const void*>& active);

bool recovered_template_parameter_name_in_type(TypePtr type,
                                               const set<string>& names,
                                               set<const void*>& active)
{
	if (type.get() == NULL || names.empty())
		return false;
	type = pa11::strip_cv(type);
	if (!active.insert(type.get()).second)
		return false;
	if ((type->kind == pa11::TypeKind::TemplateParameter ||
	     type->kind == pa11::TypeKind::TemplateTemplateParameter) &&
	    names.count(type->name) != 0)
		return true;
	if (type->base.get() != NULL &&
	    recovered_template_parameter_name_in_type(type->base, names, active))
		return true;
	if (type->member_class.get() != NULL &&
	    recovered_template_parameter_name_in_type(type->member_class,
	                                             names,
	                                             active))
		return true;
	for (size_t i = 0; i < type->parameters.size(); ++i)
		if (recovered_template_parameter_name_in_type(type->parameters[i],
		                                              names,
		                                              active))
			return true;
	for (size_t i = 0; i < type->template_arguments.size(); ++i)
		if (recovered_template_parameter_name_in_argument(
			    type->template_arguments[i],
			    names,
			    active))
			return true;
	for (size_t i = 0;
	     i < type->dependent_typename_template_argument_lists.size();
	     ++i)
		for (size_t j = 0;
		     j < type->dependent_typename_template_argument_lists[i].size();
		     ++j)
			if (recovered_template_parameter_name_in_argument(
				    type->dependent_typename_template_argument_lists[i][j],
				    names,
				    active))
				return true;
	return false;
}

bool recovered_template_parameter_name_in_type(TypePtr type,
                                               const set<string>& names)
{
	set<const void*> active;
	return recovered_template_parameter_name_in_type(type, names, active);
}

bool recovered_template_parameter_name_in_argument(
	const pa11::TemplateInstanceArgument& argument,
	const set<string>& names,
	set<const void*>& active)
{
	if (argument.kind == pa11::TemplateInstanceArgumentKind::Type)
		return recovered_template_parameter_name_in_type(argument.type,
		                                                 names,
		                                                 active);
	if (argument.kind == pa11::TemplateInstanceArgumentKind::Value)
	{
		if (names.count(argument.value_name) != 0 ||
		    names.count(argument.value_owner_template_name) != 0)
			return true;
		if (recovered_template_parameter_name_in_type(argument.type,
		                                              names,
		                                              active))
			return true;
		for (size_t i = 0;
		     i < argument.value_owner_template_arguments.size();
		     ++i)
			if (recovered_template_parameter_name_in_argument(
				    argument.value_owner_template_arguments[i],
				    names,
				    active))
				return true;
		return false;
	}
	if (argument.kind == pa11::TemplateInstanceArgumentKind::Template)
		return names.count(argument.template_name) != 0 ||
		       names.count(argument.value_name) != 0;
	for (size_t i = 0; i < argument.pack.size(); ++i)
		if (recovered_template_parameter_name_in_argument(argument.pack[i],
		                                                  names,
		                                                  active))
			return true;
	return false;
}

TypePtr normalize_recovered_template_parameter(TypePtr type,
                                               const set<string>& names,
                                               set<const void*>& active)
{
	if (type.get() == NULL || names.empty())
		return type;
	if (type->kind == pa11::TypeKind::Record &&
	    type->is_template_specialization &&
	    !recovered_template_parameter_name_in_type(type, names))
		return type;
	if (!active.insert(type.get()).second)
		return type;
	TypePtr out(new pa11::Type(*type));
	if (out->kind == pa11::TypeKind::TemplateParameter &&
	    names.count(out->name) != 0 &&
	    out->is_dependent_typename &&
	    !out->dependent_typename_qualified &&
	    !out->dependent_typename_template_id &&
	    !out->dependent_typename_decltype)
	{
		out->is_dependent_typename = false;
	}
	if (out->base.get() != NULL)
		out->base =
			normalize_recovered_template_parameter(out->base,
			                                       names,
			                                       active);
	if (out->member_class.get() != NULL)
		out->member_class =
			normalize_recovered_template_parameter(out->member_class,
			                                       names,
			                                       active);
	for (size_t i = 0; i < out->parameters.size(); ++i)
		out->parameters[i] =
			normalize_recovered_template_parameter(out->parameters[i],
			                                       names,
			                                       active);
	for (size_t i = 0; i < out->template_arguments.size(); ++i)
		out->template_arguments[i] =
			normalize_recovered_template_parameter(out->template_arguments[i],
			                                       names,
			                                       active);
	for (size_t i = 0;
	     i < out->dependent_typename_template_argument_lists.size();
	     ++i)
		for (size_t j = 0;
		     j < out->dependent_typename_template_argument_lists[i].size();
		     ++j)
			out->dependent_typename_template_argument_lists[i][j] =
				normalize_recovered_template_parameter(
					out->dependent_typename_template_argument_lists[i][j],
					names,
					active);
	active.erase(type.get());
	return out;
}

pa11::TemplateInstanceArgument normalize_recovered_template_parameter(
	const pa11::TemplateInstanceArgument& argument,
	const set<string>& names,
	set<const void*>& active)
{
	if (names.empty())
		return argument;
	pa11::TemplateInstanceArgument out = argument;
	if (out.kind == pa11::TemplateInstanceArgumentKind::Type)
		out.type =
			normalize_recovered_template_parameter(out.type,
			                                       names,
			                                       active);
	else if (out.kind == pa11::TemplateInstanceArgumentKind::Value)
	{
		out.type =
			normalize_recovered_template_parameter(out.type,
			                                       names,
			                                       active);
		for (size_t i = 0; i < out.value_owner_template_arguments.size(); ++i)
			out.value_owner_template_arguments[i] =
				normalize_recovered_template_parameter(
					out.value_owner_template_arguments[i],
					names,
					active);
	}
	else if (out.kind == pa11::TemplateInstanceArgumentKind::Pack)
	{
		for (size_t i = 0; i < out.pack.size(); ++i)
			out.pack[i] =
				normalize_recovered_template_parameter(out.pack[i],
				                                       names,
				                                       active);
	}
	return out;
}

TypePtr normalize_recovered_template_parameter(TypePtr type,
                                               const set<string>& names)
{
	set<const void*> active;
	return normalize_recovered_template_parameter(type, names, active);
}

void collect_direct_function_template_parameters(
	TypePtr function_type,
	const vector<TemplateParameterInfo>& existing_parameters,
	vector<TemplateParameterInfo>& recovered_parameters)
{
	if (function_type.get() == NULL ||
	    function_type->kind != pa11::TypeKind::Function)
		return;
	for (size_t pi = 0; pi < function_type->parameters.size(); ++pi)
	{
		TypePtr pattern = pa11::strip_cv(function_type->parameters[pi]);
		while (pattern.get() != NULL &&
		       (pattern->kind == pa11::TypeKind::LValueReference ||
		        pattern->kind == pa11::TypeKind::RValueReference ||
		        pattern->kind == pa11::TypeKind::Pointer ||
		        pattern->kind == pa11::TypeKind::Array))
			pattern = pa11::strip_cv(pattern->base);
		if (pattern.get() == NULL ||
		    pattern->kind != pa11::TypeKind::TemplateParameter ||
		    pattern->name.empty())
			continue;
		bool direct_dependent_parameter =
			pattern->is_dependent_typename &&
			!pattern->dependent_typename_qualified &&
			!pattern->dependent_typename_template_id &&
			!pattern->dependent_typename_decltype;
		if (!pa11::is_deducible_template_parameter_type(pattern) &&
		    !direct_dependent_parameter)
			continue;
		const TemplateParameterInfo* declared_parameter = NULL;
		for (size_t di = 0; di < existing_parameters.size(); ++di)
			if (existing_parameters[di].name == pattern->name)
				declared_parameter = &existing_parameters[di];
		bool already_recovered = false;
		for (size_t ri = 0; ri < recovered_parameters.size(); ++ri)
			if (recovered_parameters[ri].name == pattern->name)
				already_recovered = true;
		if (!already_recovered)
		{
			if (declared_parameter != NULL)
				recovered_parameters.push_back(*declared_parameter);
			else
			{
				TemplateParameterInfo parameter;
				parameter.kind = TemplateParameterKind::Type;
				parameter.name = pattern->name;
				recovered_parameters.push_back(parameter);
			}
		}
	}
}

void append_normalized_object_specialization_arguments(
	vector<pa11::TemplateInstanceArgument>& out,
	const vector<pa11::TemplateInstanceArgument>& arguments)
{
	for (size_t i = 0; i < arguments.size(); ++i)
	{
		if (arguments[i].kind == pa11::TemplateInstanceArgumentKind::Pack)
		{
			append_normalized_object_specialization_arguments(out,
			                                                 arguments[i].pack);
			continue;
		}
		out.push_back(arguments[i]);
	}
}

bool same_object_specialization_type(TypePtr left, TypePtr right);
bool same_object_specialization_arguments(
	const vector<pa11::TemplateInstanceArgument>& left,
	const vector<pa11::TemplateInstanceArgument>& right);

bool same_object_specialization_argument(
	const pa11::TemplateInstanceArgument& left,
	const pa11::TemplateInstanceArgument& right)
{
	if (left.kind != right.kind)
		return false;
	if (left.kind == pa11::TemplateInstanceArgumentKind::Type)
		return same_object_specialization_type(left.type, right.type);
	if (left.kind == pa11::TemplateInstanceArgumentKind::Value)
		return left.dependent == right.dependent &&
		       left.value_negated == right.value_negated &&
		       left.value == right.value &&
		       left.value_name == right.value_name &&
		       left.value_owner_template_name ==
			       right.value_owner_template_name &&
		       left.value_member_name == right.value_member_name &&
		       same_object_specialization_type(left.type, right.type) &&
		       same_object_specialization_arguments(
			       left.value_owner_template_arguments,
			       right.value_owner_template_arguments);
	if (left.kind == pa11::TemplateInstanceArgumentKind::Template)
		return left.template_name == right.template_name &&
		       left.dependent == right.dependent;
	if (left.pack.size() != right.pack.size())
		return false;
	for (size_t i = 0; i < left.pack.size(); ++i)
		if (!same_object_specialization_argument(left.pack[i],
		                                         right.pack[i]))
			return false;
	return true;
}

bool same_object_specialization_arguments(
	const vector<pa11::TemplateInstanceArgument>& left,
	const vector<pa11::TemplateInstanceArgument>& right)
{
	vector<pa11::TemplateInstanceArgument> flat_left;
	vector<pa11::TemplateInstanceArgument> flat_right;
	append_normalized_object_specialization_arguments(flat_left, left);
	append_normalized_object_specialization_arguments(flat_right, right);
	if (flat_left.size() != flat_right.size())
		return false;
	for (size_t i = 0; i < flat_left.size(); ++i)
		if (!same_object_specialization_argument(flat_left[i],
		                                         flat_right[i]))
			return false;
	return true;
}

bool same_object_specialization_type(TypePtr left, TypePtr right)
{
	if (left.get() == NULL || right.get() == NULL)
		return left.get() == right.get();
	if (pa11::same_type(left, right))
		return true;
	TypePtr l = pa11::strip_cv(left);
	TypePtr r = pa11::strip_cv(right);
	return l->kind == pa11::TypeKind::Record &&
	       r->kind == pa11::TypeKind::Record &&
	       l->is_template_specialization &&
	       r->is_template_specialization &&
	       !l->template_primary_name.empty() &&
	       l->template_primary_name == r->template_primary_name &&
	       same_object_specialization_arguments(l->template_arguments,
	                                            r->template_arguments);
}

bool scope_has_namespace_named(Scope* scope, const string& name)
{
	for (Scope* cur = scope; cur != NULL; cur = cur->parent)
		if (cur->kind == ScopeKind::Namespace && cur->name == name)
			return true;
	return false;
}

bool hosted_std_function_template_declaration(
	const TemplateDeclaration* declaration,
	const string& name)
{
	if (declaration == NULL || declaration->name != name)
		return false;
	Scope* scope =
		declaration->placeholder != NULL
		? declaration->placeholder->owner
		: declaration->owner;
	return scope_has_namespace_named(scope, "std");
}

bool hosted_basic_string_type(TypePtr type)
{
	TypePtr bare = type.get() != NULL ? pa11::strip_cv(type) : TypePtr();
	return bare.get() != NULL &&
	       bare->kind == pa11::TypeKind::Record &&
	       bare->is_template_specialization &&
	       bare->template_primary_name == "basic_string" &&
	       scope_has_namespace_named(bare->scope, "std");
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

bool hosted_basic_string_pattern(TypePtr type)
{
	TypePtr bare = type.get() != NULL ? pa11::strip_cv(type) : TypePtr();
	if (bare.get() == NULL)
		return false;
	if (bare->kind == pa11::TypeKind::LValueReference ||
	    bare->kind == pa11::TypeKind::RValueReference ||
	    bare->kind == pa11::TypeKind::Pointer ||
	    bare->kind == pa11::TypeKind::Cv)
		return hosted_basic_string_pattern(bare->base);
	return hosted_basic_string_type(bare);
}

TypePtr substitute_hosted_basic_string_operator_type(TypePtr pattern,
                                                     TypePtr string_type,
                                                     TypePtr char_type)
{
	if (pattern.get() == NULL)
		return pattern;
	if (pattern->kind == pa11::TypeKind::Cv)
		return pa11::make_cv(
			substitute_hosted_basic_string_operator_type(pattern->base,
			                                             string_type,
			                                             char_type),
			pattern->cv);
	if (pattern->kind == pa11::TypeKind::Pointer)
		return pa11::make_pointer(
			substitute_hosted_basic_string_operator_type(pattern->base,
			                                             string_type,
			                                             char_type));
	if (pattern->kind == pa11::TypeKind::LValueReference)
		return pa11::make_lvalue_reference(
			substitute_hosted_basic_string_operator_type(pattern->base,
			                                             string_type,
			                                             char_type));
	if (pattern->kind == pa11::TypeKind::RValueReference)
		return pa11::make_rvalue_reference(
			substitute_hosted_basic_string_operator_type(pattern->base,
			                                             string_type,
			                                             char_type));
	TypePtr bare = pa11::strip_cv(pattern);
	if (bare->kind == pa11::TypeKind::TemplateParameter &&
	    pa11::is_deducible_template_parameter_type(bare))
		return char_type;
	if (hosted_basic_string_type(pattern))
		return string_type;
	return pattern;
}

bool hosted_std_function_type(TypePtr type)
{
	TypePtr bare = type.get() != NULL ? pa11::strip_cv(type) : TypePtr();
	return bare.get() != NULL &&
	       bare->kind == pa11::TypeKind::Record &&
	       bare->is_template_specialization &&
	       unqualified_template_primary_name(bare) == "function" &&
	       scope_has_namespace_named(bare->scope, "std");
}

bool hosted_std_vector_type(TypePtr type)
{
	TypePtr bare = type.get() != NULL ? pa11::strip_cv(type) : TypePtr();
	return bare.get() != NULL &&
	       bare->kind == pa11::TypeKind::Record &&
	       bare->is_template_specialization &&
	       unqualified_template_primary_name(bare) == "vector" &&
	       scope_has_namespace_named(bare->scope, "std");
}

bool hosted_std_function_member_template_declaration(
	const TemplateDeclaration* declaration,
	const string& name)
{
	if (declaration == NULL || declaration->name != name ||
	    declaration->owner == NULL ||
	    declaration->owner->kind != ScopeKind::Class)
		return false;
	return hosted_std_function_type(
		pa11::record_type_for_scope(declaration->owner));
}

bool hosted_std_vector_member_template_declaration(
	const TemplateDeclaration* declaration,
	const string& name)
{
	if (declaration == NULL || declaration->name != name ||
	    declaration->owner == NULL ||
	    declaration->owner->kind != ScopeKind::Class)
		return false;
	return hosted_std_vector_type(
		pa11::record_type_for_scope(declaration->owner));
}

bool hosted_forwarding_template_parameter(TypePtr type)
{
	TypePtr bare = type.get() != NULL ? pa11::strip_cv(type) : TypePtr();
	if (bare.get() == NULL ||
	    bare->kind != pa11::TypeKind::RValueReference)
		return false;
	TypePtr base = pa11::strip_cv(bare->base);
	return base.get() != NULL &&
	       base->kind == pa11::TypeKind::TemplateParameter &&
	       pa11::is_deducible_template_parameter_type(base);
}

bool complete_hosted_template_argument_prefix(
	const TemplateDeclaration* declaration,
	vector<TemplateArgument>& arguments)
{
	if (declaration == NULL || arguments.size() > declaration->parameters.size())
		return false;
	for (size_t i = arguments.size(); i < declaration->parameters.size(); ++i)
	{
		const TemplateParameterInfo& parameter = declaration->parameters[i];
		if (!parameter.has_default)
			return false;
		if (parameter.kind == TemplateParameterKind::Type)
		{
			string name = parameter.name.empty()
				? declaration->name + "__default" + to_string(i)
				: parameter.name;
			arguments.push_back(TemplateArgument::type_arg(
				pa11::make_dependent_typename_type(name,
				                                   false,
				                                   false,
				                                   false)));
		}
		else
		{
			TypePtr type = parameter.type.get() != NULL
				? parameter.type : pa11::make_fundamental(FT_INT);
			arguments.push_back(TemplateArgument::dependent_value_arg(type));
		}
	}
	return true;
}

TypePtr hosted_expression_object_type(TypePtr type)
{
	if (type.get() != NULL &&
	    (type->kind == pa11::TypeKind::LValueReference ||
	     type->kind == pa11::TypeKind::RValueReference))
		return type->base;
	return type;
}

TypePtr hosted_lvalue_to_rvalue_type(TypePtr type)
{
	return hosted_expression_object_type(type);
}

bool hosted_template_parameter_name(TypePtr type, string& name)
{
	TypePtr bare = type.get() != NULL ? pa11::strip_cv(type) : TypePtr();
	while (bare.get() != NULL &&
	       (bare->kind == pa11::TypeKind::LValueReference ||
	        bare->kind == pa11::TypeKind::RValueReference ||
	        bare->kind == pa11::TypeKind::Pointer ||
	        bare->kind == pa11::TypeKind::Array))
		bare = pa11::strip_cv(bare->base);
	if (bare.get() == NULL || bare->name.empty())
		return false;
	if (bare->kind == pa11::TypeKind::TemplateParameter ||
	    bare->is_dependent_typename)
	{
		name = bare->name;
		return true;
	}
	return false;
}

TypePtr substitute_hosted_named_type(TypePtr type,
                                     const string& name,
                                     TypePtr value)
{
	if (type.get() == NULL || name.empty())
		return type;
	TypePtr bare = pa11::strip_cv(type);
	if ((bare->kind == pa11::TypeKind::TemplateParameter ||
	     bare->is_dependent_typename) &&
	    bare->name == name)
		return value;
	if (type->kind == pa11::TypeKind::Cv)
		return pa11::make_cv(
			substitute_hosted_named_type(type->base, name, value),
			type->cv);
	if (type->kind == pa11::TypeKind::Pointer)
		return pa11::make_pointer(
			substitute_hosted_named_type(type->base, name, value));
	if (type->kind == pa11::TypeKind::LValueReference)
		return pa11::make_lvalue_reference(
			substitute_hosted_named_type(type->base, name, value));
	if (type->kind == pa11::TypeKind::RValueReference)
		return pa11::make_rvalue_reference(
			substitute_hosted_named_type(type->base, name, value));
	if (type->kind == pa11::TypeKind::Function)
	{
		vector<TypePtr> params;
		for (size_t i = 0; i < type->parameters.size(); ++i)
			params.push_back(
				substitute_hosted_named_type(type->parameters[i],
				                             name,
				                             value));
		TypePtr out = pa11::make_function(
			substitute_hosted_named_type(type->base, name, value),
			params,
			type->variadic);
		out->cv = type->cv;
		out->ref_qualifier = type->ref_qualifier;
		return out;
	}
	return type;
}

TypePtr hosted_forwarding_parameter_for_argument(const Expr& arg)
{
	TypePtr object = hosted_expression_object_type(arg.type);
	if (arg.category == ValueCategory::LValue)
		return pa11::make_lvalue_reference(object);
	return pa11::make_rvalue_reference(hosted_lvalue_to_rvalue_type(arg.type));
}

TypePtr modeled_hosted_function_assignment_type(Binding* fn,
                                                const vector<Expr>& args,
                                                vector<TemplateArgument>& out)
{
	if (fn == NULL ||
	    fn->type.get() == NULL ||
	    fn->type->kind != pa11::TypeKind::Function ||
	    fn->owner == NULL ||
	    fn->owner->kind != ScopeKind::Class ||
	    fn->name != "operator=" ||
	    args.size() != 2 ||
	    args[1].type.get() == NULL ||
	    fn->type->parameters.size() != 2 ||
	    !hosted_std_function_type(pa11::record_type_for_scope(fn->owner)))
		return TypePtr();
	string parameter_name;
	if (!hosted_template_parameter_name(fn->type->parameters[1],
	                                    parameter_name))
		return TypePtr();
	TypePtr owner_record = pa11::strip_cv(pa11::record_type_for_scope(fn->owner));
	TypePtr functor_type = args[1].category == ValueCategory::LValue
		? hosted_expression_object_type(args[1].type)
		: hosted_lvalue_to_rvalue_type(args[1].type);
	if (owner_record.get() == NULL ||
	    functor_type.get() == NULL ||
	    type_structurally_dependent(functor_type))
		return TypePtr();
	vector<TypePtr> params;
	params.push_back(fn->type->parameters[0]);
	params.push_back(hosted_forwarding_parameter_for_argument(args[1]));
	TypePtr modeled = pa11::make_function(
		pa11::make_lvalue_reference(owner_record),
		params,
		false);
	modeled->cv = fn->type->cv;
	modeled->ref_qualifier = fn->type->ref_qualifier;
	out.clear();
	out.push_back(TemplateArgument::type_arg(functor_type));
	return modeled;
}

TypePtr modeled_hosted_vector_insert_type(Binding* fn,
                                          const vector<Expr>& args,
                                          vector<TemplateArgument>& out)
{
	if (fn == NULL ||
	    fn->type.get() == NULL ||
	    fn->type->kind != pa11::TypeKind::Function ||
	    fn->owner == NULL ||
	    fn->owner->kind != ScopeKind::Class ||
	    fn->name != "insert" ||
	    args.size() != 4 ||
	    args[2].type.get() == NULL ||
	    args[3].type.get() == NULL ||
	    fn->type->parameters.size() != 4 ||
	    !hosted_std_vector_type(pa11::record_type_for_scope(fn->owner)))
		return TypePtr();
	string parameter_name;
	if (!hosted_template_parameter_name(fn->type->parameters[2],
	                                    parameter_name))
		return TypePtr();
	string last_parameter_name;
	if (!hosted_template_parameter_name(fn->type->parameters[3],
	                                    last_parameter_name) ||
	    last_parameter_name != parameter_name)
		return TypePtr();
	TypePtr first = hosted_lvalue_to_rvalue_type(args[2].type);
	TypePtr last = hosted_lvalue_to_rvalue_type(args[3].type);
	if (first.get() == NULL ||
	    last.get() == NULL ||
	    !pa11::same_type(first, last) ||
	    type_structurally_dependent(first))
		return TypePtr();
	TypePtr modeled =
		substitute_hosted_named_type(fn->type, parameter_name, first);
	if (modeled.get() == NULL || type_structurally_dependent(modeled))
		return TypePtr();
	out.clear();
	out.push_back(TemplateArgument::type_arg(first));
	return modeled;
}

bool recover_hosted_call_template_arguments(
	const TemplateDeclaration* declaration,
	const vector<Expr>& args,
	vector<TemplateArgument>& deduced)
{
	if (hosted_std_function_member_template_declaration(declaration,
	                                                    "operator=") &&
	    args.size() == 2 &&
	    args[1].type.get() != NULL &&
	    !declaration->parameters.empty() &&
	    declaration->parameters[0].kind == TemplateParameterKind::Type)
	{
		deduced.clear();
		deduced.push_back(TemplateArgument::type_arg(
			args[1].category == ValueCategory::LValue
			? hosted_expression_object_type(args[1].type)
			: hosted_lvalue_to_rvalue_type(args[1].type)));
		return complete_hosted_template_argument_prefix(declaration, deduced);
	}
	if (hosted_std_vector_member_template_declaration(declaration, "insert") &&
	    args.size() == 4 &&
	    args[2].type.get() != NULL &&
	    args[3].type.get() != NULL &&
	    !declaration->parameters.empty() &&
	    declaration->parameters[0].kind == TemplateParameterKind::Type)
	{
		TypePtr first = hosted_lvalue_to_rvalue_type(args[2].type);
		TypePtr last = hosted_lvalue_to_rvalue_type(args[3].type);
		if (!pa11::same_type(first, last))
			return false;
		deduced.clear();
		deduced.push_back(TemplateArgument::type_arg(first));
		return complete_hosted_template_argument_prefix(declaration, deduced);
	}
	return false;
}

}  // namespace

bool Parser::call_candidate_has_arguments(Binding* fn, size_t arg_count) const
{
	if (arg_count < fn->type->parameters.size())
	{
		map<Binding*, vector<Expr> >::const_iterator dit =
			default_arguments_.find(fn);
		if (dit == default_arguments_.end())
			return false;
		for (size_t j = arg_count; j < fn->type->parameters.size(); ++j)
		{
			if (j >= dit->second.size() || !dit->second[j].valid)
				return false;
		}
	}
	if (!fn->type->variadic && arg_count != fn->type->parameters.size() &&
	    arg_count > fn->type->parameters.size())
		return false;
	return true;
}

bool Parser::instantiate_function_default_argument(Binding* fn,
                                                  const Expr& default_arg,
                                                  TypePtr parameter_type,
                                                  Expr& out)
{
	if (default_arg.source_end <= default_arg.source_begin)
		return false;
	map<Binding*, TemplateDeclaration*>::iterator template_it =
		function_template_placeholders_.find(fn);
	map<Binding*, vector<TemplateArgument> >::iterator args_it =
		function_template_specialization_arguments_.find(fn);
	if (template_it == function_template_placeholders_.end() ||
	    args_it == function_template_specialization_arguments_.end())
		return false;
	TemplateDeclaration* declaration = template_it->second;
	const vector<TemplateArgument>& full_args = args_it->second;

	size_t save_pos = pos_;
	bool tokens_are_declaration_tokens =
		tokens_.size() == declaration_tokens_.size() &&
		(tokens_.empty() ||
		 (tokens_.front().source == declaration_tokens_.front().source &&
		  tokens_.back().source == declaration_tokens_.back().source));
	vector<Token> save_tokens;
	if (!tokens_are_declaration_tokens)
		save_tokens = tokens_;
	vector<Scope*> save_scopes = scopes_;
	vector<map<string, TypePtr> > save_subst = template_type_substitutions_;
	vector<map<string, TemplateArgument> > save_value_subst =
		template_value_substitutions_;
	vector<set<string> > save_pack_subst = template_type_parameter_packs_;

	map<string, TypePtr> subst;
	map<string, TemplateArgument> value_subst;
	set<string> pack_subst;
	for (size_t i = 0; i < full_args.size() &&
	     i < declaration->parameters.size(); ++i)
	{
		const TemplateParameterInfo& parameter = declaration->parameters[i];
		if (parameter.name.empty())
			continue;
		if (parameter.kind == TemplateParameterKind::Type)
		{
			if (parameter.is_pack)
			{
				subst[parameter.name] =
					pa11::make_template_parameter_type(parameter.name);
				value_subst[parameter.name] = full_args[i];
				pack_subst.insert(parameter.name);
			}
			else if (full_args[i].kind == TemplateArgumentKind::Type)
				subst[parameter.name] = full_args[i].type;
		}
		else
			value_subst[parameter.name] = full_args[i];
	}

	bool ok = false;
	try
	{
		template_type_substitutions_.insert(
			template_type_substitutions_.end(),
			declaration->outer_type_substitutions.begin(),
			declaration->outer_type_substitutions.end());
		template_value_substitutions_.insert(
			template_value_substitutions_.end(),
			declaration->outer_value_substitutions.begin(),
			declaration->outer_value_substitutions.end());
		template_type_substitutions_.push_back(subst);
		template_value_substitutions_.push_back(value_subst);
		template_type_parameter_packs_.push_back(pack_subst);
		scopes_.clear();
		scopes_.push_back(declaration->lexical_scope != NULL
		                  ? declaration->lexical_scope
		                  : declaration->owner);
			if (!tokens_are_declaration_tokens)
				tokens_ = declaration_tokens_;
		pos_ = default_arg.source_begin;
		Expr expr = parse_assignment_expression();
		if (pos_ == default_arg.source_end)
		{
			Conversion conv = convert_to(expr, parameter_type);
			if (conv.viable)
			{
				out = conv.expr;
				ok = true;
			}
			else if (!type_is_template_dependent(expr.type))
			{
				out = expr;
				ok = true;
			}
		}
	}
	catch (const exception&)
	{
		ok = false;
	}

	template_type_substitutions_ = save_subst;
	template_value_substitutions_ = save_value_subst;
	template_type_parameter_packs_ = save_pack_subst;
	scopes_ = save_scopes;
	if (!tokens_are_declaration_tokens)
		tokens_ = save_tokens;
	pos_ = save_pos;
	return ok;
}

bool Parser::convert_call_candidate_arguments(Binding* fn,
                                              const vector<Expr>& args,
                                              vector<Expr>& conv_args,
                                              vector<int>& ranks,
                                              int& object_rank)
{
	conv_args = args;
	if (conv_args.size() < fn->type->parameters.size())
	{
		const vector<Expr>& defaults = default_arguments_[fn];
		for (size_t j = conv_args.size(); j < fn->type->parameters.size(); ++j)
			{
				Expr default_arg = defaults[j];
				if (default_arg.valid &&
				    type_is_template_dependent(default_arg.type) &&
				    !type_is_template_dependent(fn->type->parameters[j]))
				{
					Expr instantiated;
					if (instantiate_function_default_argument(
						    fn,
						    default_arg,
						    fn->type->parameters[j],
						    instantiated))
						default_arg = instantiated;
					else
					{
						default_arg.type = fn->type->parameters[j];
						annotate_expr_node(default_arg);
					}
				}
				conv_args.push_back(default_arg);
			}
	}
	object_rank = -1;
	for (size_t j = 0; j < fn->type->parameters.size(); ++j)
	{
		bool implicit_object_arg =
			j == 0 &&
			fn->owner != NULL &&
			fn->owner->kind == ScopeKind::Class &&
			!fn->is_static_member;
		Conversion conv;
		bool conversion_failed = false;
		try
		{
			conv = convert_to(conv_args[j], fn->type->parameters[j]);
		}
		catch (const runtime_error&)
		{
			conversion_failed = true;
		}
		if ((conversion_failed || !conv.viable) && implicit_object_arg)
		{
			bool constructor_object_arg =
				fn->owner != NULL &&
				fn->owner->kind == ScopeKind::Class &&
				fn->name == fn->owner->name;
			TypePtr source =
				pa11::strip_cv(lvalue_to_rvalue_type(conv_args[j].type));
			TypePtr target = pa11::strip_cv(fn->type->parameters[j]);
			if (!constructor_object_arg &&
			    source.get() != NULL &&
			    target.get() != NULL &&
			    source->kind == pa11::TypeKind::Pointer &&
			    target->kind == pa11::TypeKind::Pointer &&
				    source->base.get() != NULL &&
				    target->base.get() != NULL &&
				    same_object_specialization_type(source->base,
				                                    target->base))
			{
				unsigned source_cv = source->base->kind == pa11::TypeKind::Cv
					? source->base->cv : pa11::CV_NONE;
				unsigned target_cv = target->base->kind == pa11::TypeKind::Cv
					? target->base->cv : pa11::CV_NONE;
				if ((target_cv & source_cv) != source_cv)
					return false;
				unsigned added_cv = target_cv & ~source_cv;
				int rank = 0;
				if ((added_cv & pa11::CV_CONST) != 0)
					++rank;
				if ((added_cv & pa11::CV_VOLATILE) != 0)
					++rank;
				Expr converted = conv_args[j];
				converted.type = fn->type->parameters[j];
				converted.category = ValueCategory::PRValue;
				converted.node = Node("cast-expression prvalue " +
				                      pa11::describe_type(converted.type));
				add_child(converted.node, conv_args[j].node);
				annotate_expr_node(converted);
				conv = Conversion(true, rank, converted);
				conversion_failed = false;
			}
		}
		if (conversion_failed || !conv.viable)
			return false;
		bool supplied_arg = j < args.size();
		if (implicit_object_arg)
			object_rank = conv.rank;
		else if (supplied_arg)
			ranks.push_back(conv.rank);
		conv_args[j] = conv.expr;
	}
	return true;
	}

	int Parser::explicit_template_argument_match_score(
		Binding* fn,
		const map<Binding*, vector<TemplateArgument> >& explicit_template_arguments) const
	{
		if (fn == NULL || explicit_template_arguments.empty())
			return 0;
		Binding* placeholder = fn->aliased_binding != NULL ? fn->aliased_binding : fn;
		map<Binding*, vector<TemplateArgument> >::const_iterator explicit_it =
			explicit_template_arguments.find(fn);
		if (explicit_it == explicit_template_arguments.end() &&
		    placeholder != fn)
			explicit_it = explicit_template_arguments.find(placeholder);
		map<Binding*, TemplateDeclaration*>::const_iterator template_it =
			function_template_placeholders_.find(fn);
		if (template_it == function_template_placeholders_.end() &&
		    placeholder != fn)
			template_it = function_template_placeholders_.find(placeholder);
		if (explicit_it == explicit_template_arguments.end() &&
		    template_it != function_template_placeholders_.end() &&
		    template_it->second->placeholder != NULL)
			explicit_it =
				explicit_template_arguments.find(template_it->second->placeholder);
		if (explicit_it == explicit_template_arguments.end())
			return 0;
		map<Binding*, vector<TemplateArgument> >::const_iterator stored_it =
			function_template_specialization_arguments_.find(fn);
		if (stored_it == function_template_specialization_arguments_.end() &&
		    placeholder != fn)
			stored_it = function_template_specialization_arguments_.find(placeholder);
		if (stored_it == function_template_specialization_arguments_.end())
			return 0;
		const vector<TemplateArgument>& explicit_args = explicit_it->second;
		const vector<TemplateArgument>& stored_args = stored_it->second;
		int score = 0;
		for (size_t i = 0; i < explicit_args.size() &&
		     i < stored_args.size(); ++i)
		{
			vector<TemplateArgument> left(1, explicit_args[i]);
			vector<TemplateArgument> right(1, stored_args[i]);
			if (template_argument_key(left) != template_argument_key(right))
				break;
			++score;
		}
		return score;
	}

	Binding* Parser::resolve_call_candidate(const vector<Binding*>& overloads,
	                                        const vector<Expr>& args,
                                        const map<Binding*, vector<TemplateArgument> >& explicit_template_arguments,
                                        vector<Expr>& converted)
{
	Binding* best = NULL;
	vector<int> best_ranks;
	vector<Expr> best_args;
	int best_object_rank = 0;
	bool ambiguous = false;
	vector<Binding*> considered;
	set<const void*> remapped_member_template_owners;
	for (size_t i = 0; i < overloads.size(); ++i)
	{
		Binding* fn = overloads[i];
		if (fn == NULL ||
		    fn->owner == NULL ||
		    fn->owner->kind != ScopeKind::Class)
			continue;
		TypePtr owner_record = pa11::record_type_for_scope(fn->owner);
		owner_record = owner_record.get() != NULL
			? pa11::strip_cv(owner_record) : TypePtr();
		if (owner_record.get() == NULL ||
		    owner_record->kind != pa11::TypeKind::Record ||
		    !owner_record->is_template_specialization ||
		    !remapped_member_template_owners.insert(owner_record.get()).second)
			continue;
		instantiate_member_function_templates(owner_record);
	}
	for (size_t i = 0; i < overloads.size(); ++i)
	{
		Binding* fn = overloads[i];
		if (fn != NULL &&
		    fn->is_dependent_template_artifact &&
		    !validating_template_definition_ &&
		    explicit_template_arguments.empty() &&
		    type_is_template_dependent(fn->type))
			continue;
		if (!explicit_template_arguments.empty() &&
		    explicit_template_arguments.find(fn) == explicit_template_arguments.end())
		{
			map<Binding*, TemplateDeclaration*>::const_iterator tit =
				function_template_placeholders_.find(fn);
			Binding* placeholder = fn->aliased_binding != NULL ? fn->aliased_binding : fn;
			bool current_template_placeholder =
				tit != function_template_placeholders_.end() &&
				tit->second->placeholder == placeholder &&
				explicit_template_arguments.find(placeholder) != explicit_template_arguments.end();
			bool explicit_instantiated_specialization =
				function_template_specialization_arguments_.find(fn) !=
				function_template_specialization_arguments_.end();
			if (!current_template_placeholder &&
			    !explicit_instantiated_specialization)
				continue;
		}
			fn = instantiate_template_call_candidate(fn,
			                                         explicit_template_arguments,
			                                         args);
			if (fn == NULL)
				continue;
		if (fn->type->kind != pa11::TypeKind::Function)
			continue;
		Binding* duplicate = duplicate_function_candidate(considered, fn);
			if (duplicate != NULL)
			{
				bool fn_template =
				function_template_placeholders_.find(fn) !=
				function_template_placeholders_.end();
			bool duplicate_template =
				function_template_placeholders_.find(duplicate) !=
				function_template_placeholders_.end();
			TemplateDeclaration* fn_origin =
				function_template_origin(function_template_placeholders_, fn);
			TemplateDeclaration* duplicate_origin =
				function_template_origin(function_template_placeholders_,
				                         duplicate);
				if (fn_template && duplicate_template &&
				    fn_origin != duplicate_origin &&
				    !same_function_template_declaration_family(
					    fn_origin,
					    duplicate_origin) &&
				    !function_template_more_specialized(
					    function_template_placeholders_,
				    fn,
				    duplicate) &&
			    !function_template_more_specialized(
				    function_template_placeholders_,
				    duplicate,
				    fn))
				duplicate = NULL;
		}
		if (duplicate != NULL)
		{
			bool fn_template =
				function_template_placeholders_.find(fn) !=
				function_template_placeholders_.end();
			bool duplicate_template =
				function_template_placeholders_.find(duplicate) !=
				function_template_placeholders_.end();
				bool replace_duplicate =
					!fn_template && duplicate_template;
				int fn_explicit_score =
					explicit_template_argument_match_score(
						fn,
						explicit_template_arguments);
				int duplicate_explicit_score =
					explicit_template_argument_match_score(
						duplicate,
						explicit_template_arguments);
				if (!replace_duplicate &&
				    fn_explicit_score > duplicate_explicit_score)
					replace_duplicate = true;
				if (!replace_duplicate && fn_template && !duplicate_template)
					;
				else if (!replace_duplicate)
					replace_duplicate =
						fn->is_inline_definition && !duplicate->is_inline_definition;
				if (!replace_duplicate &&
				    fn_explicit_score >= duplicate_explicit_score &&
				    function_template_more_specialized(
					    function_template_placeholders_, fn, duplicate))
					replace_duplicate = true;
			if (!replace_duplicate)
				continue;
			considered.erase(find(considered.begin(),
			                      considered.end(),
			                      duplicate));
		}
			considered.push_back(fn);
		if (!call_candidate_has_arguments(fn, args.size()))
			continue;
				vector<int> ranks;
				vector<Expr> conv_args;
				int object_rank = -1;
				bool converted = false;
				try
				{
					converted = convert_call_candidate_arguments(fn,
					                                             args,
					                                             conv_args,
					                                             ranks,
					                                             object_rank);
				}
					catch (const runtime_error&)
					{
						converted = false;
					}
			if (!converted)
				continue;
							add_variadic_argument_ranks(fn, args.size(), ranks);
			if (object_rank < 0)
				object_rank = 0;
		bool better = best == NULL || ranks_better(ranks, best_ranks);
		if (!better && best != NULL && ranks == best_ranks &&
		    object_rank == best_object_rank)
		{
			bool fn_template =
				function_template_placeholders_.find(fn) !=
				function_template_placeholders_.end();
			bool best_template =
				function_template_placeholders_.find(best) !=
				function_template_placeholders_.end();
			if (fn->is_inline_definition && !best->is_inline_definition)
				better = true;
			else if (!fn->is_inline_definition && best->is_inline_definition)
				;
			else if (!fn_template && best_template)
				better = true;
			else if (fn_template == best_template &&
			         function_template_more_specialized_for_call(
				         function_template_placeholders_,
				         fn,
				         best,
				         args.size()))
				better = true;
			else if (fn_template == best_template &&
			         function_template_fewer_forwarding_lvalue_parameters_for_call(
				         function_template_placeholders_,
				         fn,
				         best,
				         args))
				better = true;
		}
			bool indistinguishable = false;
				if (best != NULL && !better && !ranks_better(best_ranks, ranks))
				{
					if (ranks == best_ranks)
					{
					if (object_rank < best_object_rank)
					better = true;
				else if (object_rank == best_object_rank &&
				         best->is_inline_definition &&
				         !fn->is_inline_definition)
					indistinguishable = false;
				else if (object_rank == best_object_rank &&
				         function_template_placeholders_.find(best) ==
				         function_template_placeholders_.end() &&
				         function_template_placeholders_.find(fn) !=
				         function_template_placeholders_.end())
					indistinguishable = false;
				else if (object_rank == best_object_rank &&
				         function_template_more_specialized_for_call(
					         function_template_placeholders_,
					         best,
					         fn,
					         args.size()))
					indistinguishable = false;
				else if (object_rank == best_object_rank &&
				         function_template_fewer_forwarding_lvalue_parameters_for_call(
					         function_template_placeholders_,
					         best,
					         fn,
					         args))
					indistinguishable = false;
					else if (object_rank == best_object_rank)
						indistinguishable = true;
				}
				else
				{
					bool tag_dispatch_better = false;
					bool tag_dispatch_ordered = false;
					if (best->name == fn->name &&
					    best->owner == fn->owner &&
					    best->type.get() != NULL &&
					    fn->type.get() != NULL &&
					    best->type->kind == pa11::TypeKind::Function &&
					    fn->type->kind == pa11::TypeKind::Function &&
					    best->type->parameters.size() ==
						    fn->type->parameters.size() &&
					    best->type->parameters.size() == args.size() &&
					    !args.empty())
					{
						size_t tag_index =
							best->type->parameters.size() - 1;
						bool leading_same_family = true;
						size_t first = best->owner != NULL &&
						               best->owner->kind == ScopeKind::Class &&
						               !best->is_static_member ? 1 : 0;
						for (size_t pi = first; pi < tag_index; ++pi)
							if (!same_parameter_family_ignoring_pointer_cv(
								    best->type->parameters[pi],
								    fn->type->parameters[pi]))
								leading_same_family = false;
						TypePtr arg_record =
							pa11::strip_cv(expression_object_type(args.back().type));
						TypePtr best_tag =
							pa11::strip_cv(best->type->parameters[tag_index]);
						TypePtr fn_tag =
							pa11::strip_cv(fn->type->parameters[tag_index]);
						if (leading_same_family &&
						    arg_record.get() != NULL &&
						    arg_record->kind == pa11::TypeKind::Record &&
						    best_tag.get() != NULL &&
						    best_tag->kind == pa11::TypeKind::Record &&
						    fn_tag.get() != NULL &&
						    fn_tag->kind == pa11::TypeKind::Record)
						{
							int best_tag_distance =
								record_base_distance(arg_record, best_tag);
							int fn_tag_distance =
								record_base_distance(arg_record, fn_tag);
							if (best_tag_distance < 1000000 &&
							    fn_tag_distance < 1000000 &&
							    best_tag_distance != fn_tag_distance)
							{
								tag_dispatch_ordered = true;
								tag_dispatch_better =
									fn_tag_distance < best_tag_distance;
							}
						}
					}
					if (tag_dispatch_better)
						better = true;
					else if (!tag_dispatch_ordered)
						indistinguishable = true;
				}
			}
		if (better)
		{
			best = fn;
			best_ranks = ranks;
			best_args = conv_args;
			best_object_rank = object_rank;
			ambiguous = false;
		}
		else if (indistinguishable)
			ambiguous = true;
	}
	if (best == NULL || ambiguous)
		throw runtime_error("cannot resolve call overload");
	if (best != NULL &&
	    best->owner != NULL &&
	    best->owner->kind == ScopeKind::Class)
	{
		TypePtr owner_record = pa11::record_type_for_scope(best->owner);
		owner_record = owner_record.get() != NULL
			? pa11::strip_cv(owner_record) : TypePtr();
		if (owner_record.get() != NULL &&
		    owner_record->kind == pa11::TypeKind::Record &&
		    owner_record->is_template_specialization)
			instantiate_member_function_templates(owner_record);
	}
	if (best != NULL && unevaluated_expression_depth_ == 0)
		mark_template_specialization_demanded(best->type);
	converted = best_args;
	bool selected_dependent_return =
		best != NULL &&
		best->type.get() != NULL &&
		best->type->kind == pa11::TypeKind::Function &&
		type_is_template_dependent(best->type->base);
	if (best != NULL &&
	    (unevaluated_expression_depth_ == 0 || selected_dependent_return) &&
	    (!best->is_inline_definition ||
	     function_bodies_.find(best) == function_bodies_.end() ||
	     selected_dependent_return))
	{
		map<Binding*, TemplateDeclaration*>::iterator template_it =
			function_template_placeholders_.find(best);
		map<Binding*, vector<TemplateArgument> >::iterator args_it =
			function_template_specialization_arguments_.find(best);
			bool selected_has_body =
				function_bodies_.find(best) != function_bodies_.end();
			TemplateDeclaration* replay_declaration =
				template_it != function_template_placeholders_.end()
				? template_it->second : NULL;
		if (replay_declaration != NULL &&
			    !template_declaration_has_body(declaration_tokens_,
			                                   replay_declaration))
		{
			TemplateDeclaration* compatible_body = NULL;
			for (map<Scope*, map<string, vector<TemplateDeclaration*> > >::iterator
				     sit = function_templates_.begin();
			     sit != function_templates_.end(); ++sit)
			{
				map<string, vector<TemplateDeclaration*> >::iterator nit =
					sit->second.find(replay_declaration->name);
				if (nit == sit->second.end())
					continue;
				for (size_t di = 0; di < nit->second.size(); ++di)
				{
					TemplateDeclaration* candidate = nit->second[di];
						if (candidate == replay_declaration ||
							    !template_declaration_has_body(
								    declaration_tokens_,
								    candidate) ||
						    candidate->generic_function_type.get() == NULL)
							continue;
						bool parameters_match =
							expr_template_parameter_lists_match(
								candidate->parameters,
								replay_declaration->parameters);
						bool signature_matches =
							same_template_signature_type(
								candidate->generic_function_type,
								replay_declaration->generic_function_type);
						if (!parameters_match && !signature_matches)
							continue;
						if (compatible_body == NULL)
							compatible_body = candidate;
						if (!signature_matches)
							continue;
						if (replay_declaration->class_template_member &&
						    !candidate->class_template_member)
							continue;
						if (args_it !=
						    function_template_specialization_arguments_.end())
						{
							size_t required_arguments = 0;
							for (size_t pi = 0;
							     pi < candidate->parameters.size();
							     ++pi)
								if (!candidate->parameters[pi].has_default &&
								    !candidate->parameters[pi].is_pack)
									++required_arguments;
							if (args_it->second.size() < required_arguments)
								continue;
							try
							{
								complete_template_arguments(candidate,
								                            args_it->second);
							}
							catch (const exception&)
							{
								continue;
							}
						}
						replay_declaration = candidate;
						break;
				}
					if (template_declaration_has_body(declaration_tokens_,
					                                  replay_declaration))
					break;
			}
					if (!template_declaration_has_body(declaration_tokens_,
					                                   replay_declaration) &&
				    compatible_body != NULL)
				{
				unique_ptr<TemplateDeclaration> clone(
					new TemplateDeclaration(*compatible_body));
				clone->owner = replay_declaration->owner;
				clone->placeholder = replay_declaration->placeholder;
				clone->class_template_member =
					replay_declaration->class_template_member;
				clone->outer_type_substitutions =
					replay_declaration->outer_type_substitutions;
				clone->outer_value_substitutions =
					replay_declaration->outer_value_substitutions;
				clone->function_specializations.clear();
				clone->completing_specializations.clear();
				TemplateDeclaration* clone_ptr = clone.get();
				template_declarations_.push_back(std::move(clone));
					replay_declaration = clone_ptr;
				}
					if (!template_declaration_has_body(declaration_tokens_,
					                                   replay_declaration) &&
				    args_it != function_template_specialization_arguments_.end())
				{
					for (size_t di = 0;
					     di < template_declarations_.size();
					     ++di)
					{
							TemplateDeclaration* candidate =
								template_declarations_[di].get();
							if (candidate == replay_declaration ||
							    candidate == NULL ||
						    candidate->name != replay_declaration->name ||
							    !template_declaration_has_body(
								    declaration_tokens_,
							                                   candidate))
							continue;
						Binding* instantiated = NULL;
						try
						{
							instantiated = instantiate_function_template(
								candidate,
								args_it->second);
						}
						catch (const exception&)
						{
							continue;
						}
						if (instantiated == NULL ||
						    instantiated->type.get() == NULL ||
						    best->type.get() == NULL ||
						    !pa11::same_type(instantiated->type,
						                     best->type))
						{
							continue;
						}
						if (best != instantiated)
							best->aliased_binding = instantiated;
						best = instantiated;
						replay_declaration = candidate;
						break;
					}
				}
			}
		if (template_it != function_template_placeholders_.end() &&
		    args_it != function_template_specialization_arguments_.end() &&
		    !(hosted_compatibility_ &&
			      replay_declaration != NULL &&
			      replay_declaration->has_definition &&
			      !best->is_object_root &&
			      !selected_dependent_return &&
			      selected_has_body) &&
			    (template_declaration_has_body(declaration_tokens_,
			                                   replay_declaration) ||
		     selected_dependent_return))
			{
				vector<TemplateArgument> selected_args = args_it->second;
				if (selected_args.size() <
				    replay_declaration->parameters.size())
			{
				++function_template_candidate_instantiation_depth_;
				try
				{
					selected_args =
						complete_template_arguments(replay_declaration,
						                            selected_args);
				}
			catch (...)
			{
				--function_template_candidate_instantiation_depth_;
				throw;
			}
				--function_template_candidate_instantiation_depth_;
			}
					Binding* instantiated = NULL;
					bool signature_only_replay =
						unevaluated_expression_depth_ != 0;
					if (signature_only_replay)
						++function_template_candidate_instantiation_depth_;
					try
					{
						instantiated =
							instantiate_function_template(replay_declaration,
							                              selected_args);
					}
					catch (...)
					{
						if (signature_only_replay)
							--function_template_candidate_instantiation_depth_;
						throw;
					}
						if (signature_only_replay)
							--function_template_candidate_instantiation_depth_;
					if (instantiated != NULL)
					{
				if (best != instantiated)
					best->aliased_binding = instantiated;
				best = instantiated;
			}
		}
	}
		if (best != NULL &&
		    unevaluated_expression_depth_ == 0 &&
		    function_template_candidate_instantiation_depth_ == 0 &&
		    !defer_hosted_function_body(best) &&
		    !(hosted_compatibility_ &&
	      best->is_inline_definition &&
	      !best->is_object_root))
	{
		parse_pending_function_body(best);
		parse_pending_member_body(best);
		ensure_function_body_extra_node(best);
		}
	return canonical_function_binding(best);
}

Binding* Parser::instantiate_template_call_candidate(
	Binding* fn,
	const map<Binding*, vector<TemplateArgument> >& explicit_template_arguments,
	const vector<Expr>& args)
{
		Binding* placeholder = fn;
		map<Binding*, TemplateDeclaration*>::iterator template_it =
			function_template_placeholders_.find(fn);
		if (template_it == function_template_placeholders_.end() &&
		    fn->aliased_binding != NULL)
		{
			placeholder = fn->aliased_binding;
			template_it = function_template_placeholders_.find(placeholder);
		}
	if (template_it == function_template_placeholders_.end())
		return fn;
	bool call_has_explicit_args =
		explicit_template_arguments.find(fn) !=
			explicit_template_arguments.end() ||
		(placeholder != fn &&
		 explicit_template_arguments.find(placeholder) !=
			 explicit_template_arguments.end());
	if (function_template_specialization_arguments_.find(fn) !=
	        function_template_specialization_arguments_.end() &&
	    !type_is_template_dependent(fn->type) &&
	    !call_has_explicit_args)
		return fn;
	TemplateDeclaration* original_declaration = template_it->second;
	bool placeholder_candidate = original_declaration->placeholder == placeholder;
	bool specialization_candidate = original_declaration->placeholder != NULL &&
		original_declaration->placeholder != fn;
	if (!placeholder_candidate && !specialization_candidate)
		return fn;
	TemplateDeclaration* declaration = original_declaration;
	if (!template_declaration_has_body(tokens_, declaration))
	{
		map<Scope*, map<string, vector<TemplateDeclaration*> > >::iterator sit =
			function_templates_.find(declaration->owner);
		if (sit != function_templates_.end())
		{
			map<string, vector<TemplateDeclaration*> >::iterator it =
				sit->second.find(declaration->name);
			if (it != sit->second.end())
			{
				for (size_t i = 0; i < it->second.size(); ++i)
				{
					TemplateDeclaration* candidate = it->second[i];
					if (candidate == declaration ||
					    !template_declaration_has_body(tokens_, candidate) ||
					    candidate->generic_function_type.get() == NULL ||
					    !same_template_signature_type(candidate->generic_function_type, declaration->generic_function_type) ||
					    !expr_template_parameter_lists_match(candidate->parameters, declaration->parameters))
						continue;
					declaration = candidate;
					break;
				}
			}
		}
	}
	bool recovered_effective_declaration = false;
	if (declaration->generic_function_type.get() != NULL &&
	    declaration->generic_function_type->kind == pa11::TypeKind::Function)
	{
		vector<TemplateParameterInfo> recovered_parameters;
		TypePtr recovered_function_type = declaration->generic_function_type;
		collect_direct_function_template_parameters(
			declaration->generic_function_type,
			declaration->parameters,
			recovered_parameters);
		if (recovered_parameters.empty() &&
		    fn != NULL &&
		    fn->type.get() != NULL &&
		    fn->type->kind == pa11::TypeKind::Function)
		{
			collect_direct_function_template_parameters(fn->type,
			                                            declaration->parameters,
			                                            recovered_parameters);
			if (!recovered_parameters.empty())
				recovered_function_type = fn->type;
		}
		bool recovered_only_declared_parameters =
			!declaration->parameters.empty();
		for (size_t ri = 0; ri < recovered_parameters.size(); ++ri)
		{
			bool declared = false;
			for (size_t di = 0; di < declaration->parameters.size(); ++di)
				if (declaration->parameters[di].name ==
				    recovered_parameters[ri].name)
					declared = true;
			if (!declared)
				recovered_only_declared_parameters = false;
		}
		if (!recovered_parameters.empty())
		{
			unique_ptr<TemplateDeclaration> effective_declaration(
				new TemplateDeclaration(*declaration));
			effective_declaration->parameters =
				recovered_only_declared_parameters
				? declaration->parameters : recovered_parameters;
			set<string> recovered_names;
			for (size_t ri = 0; ri < recovered_parameters.size(); ++ri)
				recovered_names.insert(recovered_parameters[ri].name);
			effective_declaration->generic_function_type =
				normalize_recovered_template_parameter(
					recovered_function_type,
					recovered_names);
			effective_declaration->function_specializations.clear();
			effective_declaration->completing_specializations.clear();
			declaration = effective_declaration.get();
			template_declarations_.push_back(std::move(effective_declaration));
			recovered_effective_declaration = true;
		}
	}
	vector<TemplateArgument> explicit_args;
	map<Binding*, vector<TemplateArgument> >::const_iterator eit =
		explicit_template_arguments.find(fn);
	if (eit == explicit_template_arguments.end() && placeholder != fn)
		eit = explicit_template_arguments.find(placeholder);
	if (eit == explicit_template_arguments.end() && original_declaration->placeholder != NULL)
		eit = explicit_template_arguments.find(original_declaration->placeholder);
	bool have_call_explicit_args = eit != explicit_template_arguments.end();
	if (eit != explicit_template_arguments.end())
		explicit_args = eit->second;
	else
	{
		map<Binding*, vector<TemplateArgument> >::const_iterator stored =
			function_template_specialization_arguments_.find(fn);
			if (!placeholder_candidate &&
			    stored != function_template_specialization_arguments_.end() &&
			    !template_arguments_dependent(stored->second))
				explicit_args = stored->second;
	}
	if (!type_is_template_dependent(fn->type) &&
	    explicit_args.empty() &&
	    !template_declaration_has_body(tokens_, declaration))
		return canonical_function_binding(fn);
	if (specialization_candidate && !placeholder_candidate &&
	    declaration == original_declaration &&
	    !have_call_explicit_args &&
	    explicit_args.empty())
		return explicit_template_arguments.empty()
			? canonical_function_binding(fn) : NULL;
	if (hosted_compatibility_ && explicit_args.empty())
	{
		vector<TemplateArgument> modeled_args;
		TypePtr modeled =
			modeled_hosted_function_assignment_type(fn, args, modeled_args);
		if (modeled.get() == NULL)
			modeled = modeled_hosted_vector_insert_type(fn,
			                                            args,
			                                            modeled_args);
		if (modeled.get() != NULL)
		{
			Scope* owner = fn->owner != NULL ? fn->owner : declaration->owner;
			if (owner == NULL)
				return NULL;
			map<string, vector<Binding*> >::iterator found =
				owner->members.find(fn->name);
			if (found != owner->members.end())
				for (size_t mi = 0; mi < found->second.size(); ++mi)
					if (found->second[mi] != NULL &&
					    found->second[mi]->kind == BindingKind::Function &&
					    found->second[mi] != fn &&
					    found->second[mi]->type.get() != NULL &&
					    found->second[mi]->type->kind ==
						    pa11::TypeKind::Function &&
					    pa11::same_type(found->second[mi]->type,
					                    modeled))
						return found->second[mi];
			Binding* binding = add_value(owner,
			                             BindingKind::Function,
			                             fn->name,
			                             modeled);
			binding->is_static_member = fn->is_static_member;
			binding->is_constexpr = fn->is_constexpr;
			binding->is_private = fn->is_private;
			binding->is_protected_member = fn->is_protected_member;
			binding->ref_qualifier = fn->ref_qualifier;
			binding->unwind_no = fn->unwind_no;
			function_template_specialization_arguments_[binding] =
				modeled_args;
			return binding;
		}
	}
	vector<TemplateArgument> deduced;
	bool deduction_depth_entered = false;
		try
		{
			++function_template_candidate_instantiation_depth_;
			deduction_depth_entered = true;
						bool helper_deduced =
							deduce_function_template_arguments(declaration,
							                                   args,
							                                   explicit_args,
							                                   deduced);
						if (!helper_deduced)
						{
						if (!hosted_compatibility_ ||
						    !recover_hosted_call_template_arguments(declaration,
						                                            args,
				                                            deduced))
				{
					--function_template_candidate_instantiation_depth_;
					deduction_depth_entered = false;
						return NULL;
					}
				}
			--function_template_candidate_instantiation_depth_;
		deduction_depth_entered = false;
			}
					catch (const runtime_error&)
					{
						if (deduction_depth_entered)
							--function_template_candidate_instantiation_depth_;
			if (!hosted_compatibility_ ||
			    !recover_hosted_call_template_arguments(declaration,
			                                            args,
			                                            deduced))
				return NULL;
	}
	Scope* saved_friend_class_scope = declaration->friend_class_scope;
	if (declaration->friend_class_scope == NULL &&
	    original_declaration->friend_class_scope != NULL)
		declaration->friend_class_scope =
			original_declaration->friend_class_scope;
	if (declaration != original_declaration &&
	    declaration->placeholder != NULL)
	{
		for (map<Scope*, vector<Binding*> >::const_iterator it =
			     class_friend_functions_.begin();
		     it != class_friend_functions_.end();
		     ++it)
			for (size_t i = 0; i < it->second.size(); ++i)
			{
				Binding* friend_binding = it->second[i];
				bool same_friend =
					original_declaration->placeholder != NULL &&
					friend_binding == original_declaration->placeholder;
				if (!same_friend &&
				    friend_binding->kind == BindingKind::Function &&
				    friend_binding->name == declaration->name &&
				    same_template_signature_type(
					    friend_binding->type,
					    declaration->generic_function_type))
					same_friend = true;
				if (same_friend)
					add_friend_function(it->first, declaration->placeholder);
			}
	}
	bool candidate_depth_entered = false;
		try
		{
			++function_template_candidate_instantiation_depth_;
			candidate_depth_entered = true;
					Binding* instantiated;
					instantiated =
						instantiate_function_template(declaration, deduced);
				--function_template_candidate_instantiation_depth_;
		candidate_depth_entered = false;
		declaration->friend_class_scope = saved_friend_class_scope;
		if (hosted_compatibility_ &&
		    hosted_std_function_template_declaration(declaration,
		                                             "operator+") &&
		    instantiated != NULL &&
		    instantiated->type.get() != NULL &&
		    instantiated->type->kind == pa11::TypeKind::Function &&
		    type_structurally_dependent(instantiated->type) &&
		    declaration->generic_function_type.get() != NULL &&
		    declaration->generic_function_type->kind == pa11::TypeKind::Function &&
		    declaration->generic_function_type->parameters.size() == args.size())
		{
			TypePtr string_type;
			for (size_t ai = 0; ai < args.size(); ++ai)
			{
				TypePtr object =
					pa11::strip_cv(expression_object_type(args[ai].type));
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
					map<const void*, vector<TemplateArgument> >::const_iterator
						found =
							record_template_arguments_.find(bare_string.get());
					if (found != record_template_arguments_.end() &&
					    !found->second.empty() &&
					    found->second[0].kind == TemplateArgumentKind::Type)
						char_type = found->second[0].type;
				}
			}
			bool has_basic_string_pattern =
				hosted_basic_string_pattern(
					declaration->generic_function_type->base);
			vector<TypePtr> params;
			if (string_type.get() != NULL && char_type.get() != NULL)
			{
				for (size_t pi = 0;
				     pi < declaration->generic_function_type->parameters.size();
				     ++pi)
				{
					TypePtr pattern =
						declaration->generic_function_type->parameters[pi];
					if (hosted_basic_string_pattern(pattern))
						has_basic_string_pattern = true;
					params.push_back(
						substitute_hosted_basic_string_operator_type(
							pattern,
							string_type,
							char_type));
				}
			}
			if (has_basic_string_pattern &&
			    params.size() ==
				    declaration->generic_function_type->parameters.size())
			{
				TypePtr modeled = pa11::make_function(string_type,
				                                      params,
				                                      false);
				modeled->cv = declaration->generic_function_type->cv;
				modeled->ref_qualifier =
					declaration->generic_function_type->ref_qualifier;
			if (!type_structurally_dependent(modeled))
				instantiated->type = modeled;
			}
		}
		if (hosted_compatibility_ &&
		    hosted_std_function_member_template_declaration(
			    declaration,
			    "operator=") &&
		    instantiated != NULL &&
		    instantiated->type.get() != NULL &&
		    instantiated->type->kind == pa11::TypeKind::Function &&
		    type_structurally_dependent(instantiated->type) &&
		    declaration->generic_function_type.get() != NULL &&
		    declaration->generic_function_type->kind == pa11::TypeKind::Function &&
		    declaration->generic_function_type->parameters.size() == 2 &&
		    args.size() == 2 &&
		    args[1].type.get() != NULL &&
		    instantiated->owner != NULL &&
		    hosted_forwarding_template_parameter(
			    declaration->generic_function_type->parameters[1]))
		{
			TypePtr owner_record =
				pa11::record_type_for_scope(instantiated->owner);
			owner_record = owner_record.get() != NULL
				? pa11::strip_cv(owner_record) : TypePtr();
			TypePtr functor_object =
				expression_object_type(args[1].type);
			TypePtr functor_param =
				args[1].category == ValueCategory::LValue
				? pa11::make_lvalue_reference(functor_object)
				: pa11::make_rvalue_reference(
					  lvalue_to_rvalue_type(args[1].type));
			if (owner_record.get() != NULL &&
			    hosted_std_function_type(owner_record) &&
			    !type_structurally_dependent(owner_record) &&
			    functor_object.get() != NULL &&
			    !type_structurally_dependent(functor_object))
			{
				vector<TypePtr> params;
				params.push_back(
					instantiated->type->parameters.empty()
					? pa11::make_pointer(owner_record)
					: instantiated->type->parameters[0]);
				params.push_back(functor_param);
				TypePtr modeled = pa11::make_function(
					pa11::make_lvalue_reference(owner_record),
					params,
					false);
				modeled->cv =
					declaration->generic_function_type->cv;
				modeled->ref_qualifier =
					declaration->generic_function_type->ref_qualifier;
				if (!type_structurally_dependent(modeled))
					instantiated->type = modeled;
			}
		}
		if (declaration != original_declaration)
		{
			if (recovered_effective_declaration)
			{
				if (original_declaration->placeholder != NULL &&
				    original_declaration->placeholder != instantiated)
					original_declaration->placeholder->aliased_binding =
						instantiated;
			}
			else
			{
				++function_template_candidate_instantiation_depth_;
				vector<TemplateArgument> original_deduced;
				try
				{
					original_deduced =
						complete_template_arguments(original_declaration,
						                            deduced);
				}
				catch (...)
				{
					--function_template_candidate_instantiation_depth_;
					throw;
				}
				--function_template_candidate_instantiation_depth_;
				string key = template_argument_key(original_deduced);
				map<string, Binding*>::iterator existing =
					original_declaration->function_specializations.find(key);
				if (existing !=
				    original_declaration->function_specializations.end() &&
				    existing->second != instantiated)
					existing->second->aliased_binding = instantiated;
				original_declaration->function_specializations[key] =
					instantiated;
			}
			if (fn != instantiated)
				fn->aliased_binding = instantiated;
		}
		if (instantiated != NULL &&
		    instantiated != fn &&
		    function_bodies_.find(fn) != function_bodies_.end() &&
		    function_bodies_.find(instantiated) == function_bodies_.end() &&
		    fn->type.get() != NULL &&
		    instantiated->type.get() != NULL &&
		    pa11::same_type(fn->type, instantiated->type))
		{
			if (fn->aliased_binding == instantiated)
				fn->aliased_binding = NULL;
			instantiated->aliased_binding = fn;
		}
		if (original_declaration->friend_class_scope != NULL)
			add_friend_function(original_declaration->friend_class_scope,
			                    instantiated);
		return instantiated;
		}
					catch (const runtime_error&)
					{
						if (candidate_depth_entered)
							--function_template_candidate_instantiation_depth_;
			declaration->friend_class_scope = saved_friend_class_scope;
		return NULL;
	}
}

}  // namespace internal
}  // namespace pa12
