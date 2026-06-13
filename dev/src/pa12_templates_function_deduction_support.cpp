#include "pa12_templates_function_support.h"

#include <algorithm>
#include <functional>
#include <stdexcept>

using namespace std;

namespace pa12 {
namespace internal {

bool declaration_parameter_is_pack(TemplateDeclaration* declaration,
                                   const string& name)
{
	for (size_t i = 0; i < declaration->parameters.size(); ++i)
		if (declaration->parameters[i].name == name &&
		    declaration->parameters[i].is_pack)
			return true;
	return false;
}

string generated_pack_parameter_name(const string& pack_name)
{
	if (pack_name.empty())
		return string();
	string out = pack_name;
	if (out[0] >= 'A' && out[0] <= 'Z')
		out[0] = char(out[0] - 'A' + 'a');
	return out;
}

bool template_instance_argument_has_explicit_pack(
	const pa11::TemplateInstanceArgument& argument)
{
	if (argument.kind == pa11::TemplateInstanceArgumentKind::Pack)
		return true;
	for (size_t i = 0;
	     i < argument.value_owner_template_arguments.size();
	     ++i)
		if (template_instance_argument_has_explicit_pack(
			    argument.value_owner_template_arguments[i]))
			return true;
	return false;
}

bool type_has_explicit_template_argument_pack(TypePtr type)
{
	if (type.get() == NULL)
		return false;
	TypePtr bare = pa11::strip_cv(type);
	if (bare->kind == pa11::TypeKind::Pointer ||
	    bare->kind == pa11::TypeKind::LValueReference ||
	    bare->kind == pa11::TypeKind::RValueReference ||
	    bare->kind == pa11::TypeKind::Array)
		return type_has_explicit_template_argument_pack(bare->base);
	if (bare->kind == pa11::TypeKind::Function)
	{
		if (type_has_explicit_template_argument_pack(bare->base))
			return true;
		for (size_t i = 0; i < bare->parameters.size(); ++i)
			if (type_has_explicit_template_argument_pack(
				    bare->parameters[i]))
				return true;
	}
	if (bare->kind == pa11::TypeKind::MemberPointer)
		return type_has_explicit_template_argument_pack(
			       bare->member_class) ||
		       type_has_explicit_template_argument_pack(bare->base);
	if (bare->kind == pa11::TypeKind::Record ||
	    bare->is_dependent_typename)
	{
		for (size_t i = 0; i < bare->template_arguments.size(); ++i)
			if (template_instance_argument_has_explicit_pack(
				    bare->template_arguments[i]))
				return true;
		for (size_t i = 0;
		     i < bare->dependent_typename_template_argument_lists.size();
		     ++i)
			for (size_t j = 0;
			     j < bare->dependent_typename_template_argument_lists[i].size();
			     ++j)
				if (template_instance_argument_has_explicit_pack(
					    bare->dependent_typename_template_argument_lists[i][j]))
					return true;
	}
	return false;
}

bool function_parameter_pack_name(TemplateDeclaration* declaration,
                                  TypePtr pattern,
                                  string& name)
{
	if (pattern.get() == NULL)
		return false;
	TypePtr bare = pa11::strip_cv(pattern);
	if (bare->kind == pa11::TypeKind::Pointer ||
	    bare->kind == pa11::TypeKind::LValueReference ||
	    bare->kind == pa11::TypeKind::RValueReference ||
	    bare->kind == pa11::TypeKind::Array)
		return function_parameter_pack_name(declaration, bare->base, name);
	if (bare->kind == pa11::TypeKind::Record &&
	    bare->is_template_specialization &&
	    !bare->template_primary_name.empty() &&
	    bare->scope == NULL)
		return false;
	if (bare->kind == pa11::TypeKind::TemplateParameter &&
	    pa11::is_deducible_template_parameter_type(bare) &&
	    declaration_parameter_is_pack(declaration, bare->name))
	{
		name = bare->name;
		return true;
	}
	if (bare->kind == pa11::TypeKind::Function)
	{
		if (function_parameter_pack_name(declaration, bare->base, name))
			return true;
		for (size_t i = 0; i < bare->parameters.size(); ++i)
			if (function_parameter_pack_name(declaration,
			                                 bare->parameters[i],
			                                 name))
				return true;
	}
	if (bare->kind == pa11::TypeKind::MemberPointer)
		return function_parameter_pack_name(declaration,
		                                    bare->member_class,
		                                    name) ||
		       function_parameter_pack_name(declaration,
		                                    bare->base,
		                                    name);
	if (type_has_explicit_template_argument_pack(pattern))
		return false;
	if (!template_type_has_template_parameter_name(pattern, name))
		return false;
	return declaration_parameter_is_pack(declaration, name);
}

bool bind_deduced_value_argument(map<string, TemplateArgument>& deduced,
                                 const string& name,
                                 const TemplateArgument& value)
{
	map<string, TemplateArgument>::iterator found = deduced.find(name);
	if (found == deduced.end())
	{
		deduced[name] = value;
		return true;
	}
	return found->second.kind == value.kind &&
	       found->second.kind == TemplateArgumentKind::Value &&
	       found->second.value == value.value;
}

bool match_or_deduce_value_argument(
	const TemplateArgument& pattern,
	const TemplateArgument& actual,
	map<string, TemplateArgument>* deduced)
{
	if (pattern.kind != TemplateArgumentKind::Value ||
	    actual.kind != TemplateArgumentKind::Value)
		return false;
	if (pattern.dependent && !pattern.value_name.empty() &&
	    !actual.dependent)
	{
		if (deduced == NULL)
			return true;
		return bind_deduced_value_argument(*deduced,
		                                   pattern.value_name,
		                                   actual);
	}
	if (pattern.dependent || actual.dependent)
		return true;
	return pattern.value == actual.value;
}

bool bind_deduced_template_argument(map<string, TemplateArgument>* deduced,
                                    const string& name,
                                    TemplateDeclaration* declaration)
{
	if (deduced == NULL || name.empty() || declaration == NULL)
		return declaration != NULL;
	TemplateArgument value = TemplateArgument::template_arg(declaration);
	map<string, TemplateArgument>::iterator found = deduced->find(name);
	if (found == deduced->end())
	{
		(*deduced)[name] = value;
		return true;
	}
	return found->second.kind == TemplateArgumentKind::Template &&
	       found->second.template_declaration == declaration;
}

bool same_deduced_template_argument(const TemplateArgument& left,
                                    const TemplateArgument& right)
{
	if (left.kind != right.kind)
		return false;
	if (left.kind == TemplateArgumentKind::Type)
		return left.type.get() == NULL || right.type.get() == NULL
			? left.type.get() == right.type.get()
			: pa11::same_type(left.type, right.type);
	if (left.kind == TemplateArgumentKind::Value)
		return left.dependent == right.dependent &&
		       left.value == right.value &&
		       (left.type.get() == NULL || right.type.get() == NULL
		        ? left.type.get() == right.type.get()
		        : pa11::same_type(left.type, right.type));
	if (left.kind == TemplateArgumentKind::Template)
		return left.template_declaration == right.template_declaration;
	if (left.pack.size() != right.pack.size())
		return false;
	for (size_t i = 0; i < left.pack.size(); ++i)
		if (!same_deduced_template_argument(left.pack[i],
		                                    right.pack[i]))
			return false;
	return true;
}

bool bind_deduced_pack_argument(map<string, TemplateArgument>* deduced,
                                const string& name,
                                const vector<TemplateArgument>& values)
{
	if (deduced == NULL || name.empty())
		return false;
	TemplateArgument value = TemplateArgument::pack_arg(values);
	map<string, TemplateArgument>::iterator found = deduced->find(name);
	if (found == deduced->end())
	{
		(*deduced)[name] = value;
		return true;
	}
	if (found->second.kind != TemplateArgumentKind::Pack &&
	    values.size() == 1 &&
	    same_deduced_template_argument(found->second, values[0]))
	{
		found->second = value;
		return true;
	}
	return same_deduced_template_argument(found->second, value);
}

bool template_argument_pack_parameter_name(const TemplateArgument& argument,
                                           string& name)
{
	TemplateArgument element = argument;
	if (argument.kind == TemplateArgumentKind::Pack)
	{
		if (argument.pack.size() != 1)
			return false;
		element = argument.pack[0];
	}
	if (element.kind != TemplateArgumentKind::Type)
	{
		if (element.kind == TemplateArgumentKind::Value &&
		    element.dependent &&
		    !element.value_name.empty())
		{
			name = element.value_name;
			return true;
		}
		if (element.kind == TemplateArgumentKind::Template &&
		    element.template_declaration == NULL &&
		    !element.value_name.empty())
		{
			name = element.value_name;
			return true;
		}
		return false;
	}
	TypePtr type = pa11::strip_cv(element.type);
	if (type->kind != pa11::TypeKind::TemplateParameter ||
	    !pa11::is_deducible_template_parameter_type(type))
		return false;
	name = type->name;
	return !name.empty();
}

bool deduce_array_bound_arguments(TypePtr pattern,
                                  TypePtr argument,
                                  map<string, TemplateArgument>& deduced)
{
	if (pattern.get() == NULL || argument.get() == NULL)
		return true;
	if (pattern->kind == pa11::TypeKind::LValueReference ||
	    pattern->kind == pa11::TypeKind::RValueReference)
		pattern = pattern->base;
	if (argument->kind == pa11::TypeKind::LValueReference ||
	    argument->kind == pa11::TypeKind::RValueReference)
		argument = argument->base;
	TypePtr p = pa11::strip_cv(pattern);
	TypePtr a = pa11::strip_cv(argument);
	if (p->kind == pa11::TypeKind::Array &&
	    a->kind == pa11::TypeKind::Array)
	{
		if (p->unknown_bound && !p->name.empty() && !a->unknown_bound)
		{
			TemplateArgument value =
				TemplateArgument::value_arg(pa11::make_fundamental(FT_INT),
				                            a->bound);
			if (!bind_deduced_value_argument(deduced, p->name, value))
				return false;
		}
		return deduce_array_bound_arguments(p->base, a->base, deduced);
	}
	if ((p->kind == pa11::TypeKind::Pointer &&
	     a->kind == pa11::TypeKind::Pointer) ||
	    (p->kind == pa11::TypeKind::LValueReference &&
	     a->kind == pa11::TypeKind::LValueReference) ||
	    (p->kind == pa11::TypeKind::RValueReference &&
	     a->kind == pa11::TypeKind::RValueReference))
		return deduce_array_bound_arguments(p->base, a->base, deduced);
	return true;
}

bool record_declares_pure_virtual(TypePtr type)
{
	TypePtr bare = pa11::strip_cv(type);
	if (bare->kind != pa11::TypeKind::Record || bare->scope == NULL)
		return false;
	if (bare->base.get() != NULL && record_declares_pure_virtual(bare->base))
		return true;
	for (size_t i = 0; i < bare->scope->binding_order.size(); ++i)
	{
		Binding* binding = bare->scope->binding_order[i];
		if (binding->kind == BindingKind::Function &&
		    binding->is_pure_virtual)
			return true;
	}
	return false;
}

bool substituted_type_is_valid(TypePtr type)
{
	if (type.get() == NULL)
		return true;
	TypePtr bare = pa11::strip_cv(type);
	if (bare->is_dependent_typename ||
	    bare->kind == pa11::TypeKind::TemplateParameter ||
	    bare->kind == pa11::TypeKind::TemplateTemplateParameter)
		return false;
	if (bare->kind == pa11::TypeKind::Array)
	{
		TypePtr element = pa11::strip_cv(bare->base);
		if (element->kind == pa11::TypeKind::Record &&
		    record_declares_pure_virtual(element))
			return false;
		return substituted_type_is_valid(bare->base);
	}
	if (bare->kind == pa11::TypeKind::Pointer ||
	    bare->kind == pa11::TypeKind::LValueReference ||
	    bare->kind == pa11::TypeKind::RValueReference)
		return substituted_type_is_valid(bare->base);
	if (bare->kind == pa11::TypeKind::Function)
	{
		if (!substituted_type_is_valid(bare->base))
			return false;
		for (size_t i = 0; i < bare->parameters.size(); ++i)
			if (!substituted_type_is_valid(bare->parameters[i]))
				return false;
	}
	if (bare->kind == pa11::TypeKind::MemberPointer)
		return substituted_type_is_valid(bare->member_class) &&
		       substituted_type_is_valid(bare->base);
	return true;
}

bool substituted_function_parameter_types_are_valid(TypePtr type)
{
	TypePtr bare = type.get() != NULL ? pa11::strip_cv(type) : TypePtr();
	if (bare.get() == NULL || bare->kind != pa11::TypeKind::Function)
		return substituted_type_is_valid(type);
	for (size_t i = 0; i < bare->parameters.size(); ++i)
		if (!substituted_type_is_valid(bare->parameters[i]))
			return false;
	return true;
}

bool substituted_candidate_parameter_type_is_valid(TypePtr type)
{
	if (type.get() == NULL)
		return true;
	TypePtr bare = pa11::strip_cv(type);
	if (bare->is_dependent_typename)
		return bare->dependent_typename_decltype;
	if (bare->kind == pa11::TypeKind::TemplateParameter ||
	    bare->kind == pa11::TypeKind::TemplateTemplateParameter)
		return false;
	if (bare->kind == pa11::TypeKind::Array)
	{
		TypePtr element = pa11::strip_cv(bare->base);
		if (element->kind == pa11::TypeKind::Record &&
		    record_declares_pure_virtual(element))
			return false;
		return substituted_candidate_parameter_type_is_valid(bare->base);
	}
	if (bare->kind == pa11::TypeKind::Pointer ||
	    bare->kind == pa11::TypeKind::LValueReference ||
	    bare->kind == pa11::TypeKind::RValueReference)
		return substituted_candidate_parameter_type_is_valid(bare->base);
	if (bare->kind == pa11::TypeKind::Function)
	{
		if (!substituted_candidate_parameter_type_is_valid(bare->base))
			return false;
		for (size_t i = 0; i < bare->parameters.size(); ++i)
			if (!substituted_candidate_parameter_type_is_valid(
				    bare->parameters[i]))
				return false;
	}
	if (bare->kind == pa11::TypeKind::MemberPointer)
		return substituted_candidate_parameter_type_is_valid(
			       bare->member_class) &&
		       substituted_candidate_parameter_type_is_valid(bare->base);
	return true;
}

bool substituted_candidate_function_parameter_types_are_valid(TypePtr type)
{
	TypePtr bare = type.get() != NULL ? pa11::strip_cv(type) : TypePtr();
	if (bare.get() == NULL || bare->kind != pa11::TypeKind::Function)
		return substituted_candidate_parameter_type_is_valid(type);
	for (size_t i = 0; i < bare->parameters.size(); ++i)
		if (!substituted_candidate_parameter_type_is_valid(
			    bare->parameters[i]))
			return false;
	return true;
}

bool template_parameter_lists_equivalent(
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

bool class_template_member_function_template_symbol(
	const TemplateDeclaration* declaration)
{
	return declaration != NULL &&
	       declaration->class_template_member &&
	       !declaration->constructor_template &&
	       !declaration->outer_type_substitutions.empty();
}

bool constructor_template_function_template_symbol(
	const TemplateDeclaration* declaration)
{
	return declaration != NULL &&
	       declaration->constructor_template &&
	       (!declaration->class_template_member ||
	        !declaration->outer_type_substitutions.empty() ||
	        !declaration->outer_value_substitutions.empty());
}

TypePtr remove_pattern_cv_from_argument(TypePtr argument, unsigned cv)
{
	if (argument.get() == NULL || cv == pa11::CV_NONE)
		return argument;
	if (argument->kind == pa11::TypeKind::Cv)
		return pa11::make_cv(argument->base, argument->cv & ~cv);
	if (argument->kind == pa11::TypeKind::Array)
	{
		TypePtr base = remove_pattern_cv_from_argument(argument->base, cv);
		if (base.get() == argument->base.get())
			return argument;
		TypePtr out = pa11::make_array(base,
		                               argument->unknown_bound,
		                               argument->bound);
		out->name = argument->name;
		out->tag = argument->tag;
		return out;
	}
	return argument;
}


}  // namespace internal
}  // namespace pa12
