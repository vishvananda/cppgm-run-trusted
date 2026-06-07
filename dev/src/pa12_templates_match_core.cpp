#include "pa12_templates_instance_support.h"

#include <algorithm>
#include <cstdint>
#include <sstream>
#include <stdexcept>
#include <utility>

#include "posttoken_pipeline.h"
#include "pp_token.h"

using namespace std;

namespace pa12 {
namespace internal {

bool same_template_argument_value(
	const TemplateArgument& left,
	const TemplateArgument& right,
	const map<const void*, vector<TemplateArgument> >& record_arguments);

bool merge_deduced_template_argument(
	map<string, TemplateArgument>& target,
	const string& name,
	const TemplateArgument& value,
	const map<const void*, vector<TemplateArgument> >& record_arguments);

bool match_template_type_pattern(
	TypePtr pattern,
	TypePtr actual,
	map<string, TemplateArgument>& deduced,
	const map<const void*, vector<TemplateArgument> >& record_arguments);

bool match_template_argument_pattern(
	const TemplateArgument& pattern,
	const TemplateArgument& actual,
	map<string, TemplateArgument>& deduced,
	const map<const void*, vector<TemplateArgument> >& record_arguments);

bool match_template_argument_sequence_pattern(
	const vector<TemplateArgument>& pattern,
	const vector<TemplateArgument>& actual,
	map<string, TemplateArgument>& deduced,
	const map<const void*, vector<TemplateArgument> >& record_arguments);

bool template_argument_sequence_has_pack_expansion(
	const vector<TemplateArgument>& pattern);

bool pack_argument_parameter_name(const TemplateArgument& pattern,
                                  string& name);

vector<TemplateArgument> flatten_template_argument_packs(
	const vector<TemplateArgument>& arguments);
vector<TemplateArgument> flatten_actual_template_argument_packs(
	const vector<TemplateArgument>& arguments);

bool template_argument_has_pack_expansion_recursive(
	const TemplateArgument& argument)
{
	if (argument.pack_expansion)
		return true;
	if (argument.kind != TemplateArgumentKind::Pack)
		return false;
	for (size_t i = 0; i < argument.pack.size(); ++i)
		if (template_argument_has_pack_expansion_recursive(argument.pack[i]))
			return true;
	return false;
}

bool template_arguments_have_pack_expansion_recursive(
	const vector<TemplateArgument>& arguments)
{
	for (size_t i = 0; i < arguments.size(); ++i)
		if (template_argument_has_pack_expansion_recursive(arguments[i]))
			return true;
	return false;
}

bool template_arguments_have_deducible_pattern(
	const vector<TemplateArgument>& arguments,
	const map<const void*, vector<TemplateArgument> >& record_arguments)
{
	for (size_t i = 0; i < arguments.size(); ++i)
	{
		string pack_name;
		if (arguments[i].pack_expansion ||
		    pack_argument_parameter_name(arguments[i], pack_name) ||
		    template_argument_has_template_parameter(arguments[i],
		                                            record_arguments))
			return true;
	}
	return false;
}

bool same_template_record_primary(TypePtr left, TypePtr right)
{
	if (!left->is_template_specialization ||
	    !right->is_template_specialization)
		return false;
	if (left->template_primary_name != right->template_primary_name)
		return false;
	Scope* left_owner = left->scope != NULL ? left->scope->parent : NULL;
	Scope* right_owner = right->scope != NULL ? right->scope->parent : NULL;
	return left_owner == right_owner;
}

bool deducible_template_parameter_type(TypePtr type)
{
	return pa11::is_deducible_template_parameter_type(type);
}

bool active_match_parameter_is_pack(const string& name)
{
	if (active_template_match_parameters == NULL)
		return false;
	for (size_t i = 0; i < active_template_match_parameters->size(); ++i)
	{
		const TemplateParameterInfo& parameter =
			(*active_template_match_parameters)[i];
		if (parameter.is_pack &&
		    parameter.name == name &&
		    (parameter.kind == TemplateParameterKind::Type ||
		     parameter.kind == TemplateParameterKind::NonType ||
		     parameter.kind == TemplateParameterKind::TemplateTemplate))
			return true;
	}
	return false;
}

bool active_match_parameter_is_type_parameter(const string& name)
{
	if (active_template_match_parameters == NULL)
		return false;
	for (size_t i = 0; i < active_template_match_parameters->size(); ++i)
	{
		const TemplateParameterInfo& parameter =
			(*active_template_match_parameters)[i];
		if (parameter.kind == TemplateParameterKind::Type &&
		    parameter.name == name)
			return true;
	}
	return false;
}

bool simple_active_dependent_type_parameter(TypePtr type, string& name)
{
	TypePtr bare = type.get() != NULL ? pa11::strip_cv(type) : TypePtr();
	if (bare.get() == NULL ||
	    bare->kind != pa11::TypeKind::TemplateParameter ||
	    !bare->is_dependent_typename ||
	    bare->dependent_typename_qualified ||
	    bare->dependent_typename_template_id ||
	    bare->dependent_typename_decltype ||
	    !bare->template_arguments.empty() ||
	    !bare->dependent_typename_template_argument_lists.empty() ||
	    !active_match_parameter_is_type_parameter(bare->name))
		return false;
	name = bare->name;
	return true;
}

bool active_match_parameter_is_template_template(const string& name)
{
	if (active_template_match_parameters == NULL)
		return false;
	for (size_t i = 0; i < active_template_match_parameters->size(); ++i)
	{
		const TemplateParameterInfo& parameter =
			(*active_template_match_parameters)[i];
		if (parameter.kind == TemplateParameterKind::TemplateTemplate &&
		    parameter.name == name)
			return true;
	}
	return false;
}

const TemplateParameterInfo* active_match_template_template_parameter(
	const string& name)
{
	if (active_template_match_parameters == NULL)
		return NULL;
	for (size_t i = 0; i < active_template_match_parameters->size(); ++i)
	{
		const TemplateParameterInfo& parameter =
			(*active_template_match_parameters)[i];
		if (parameter.kind == TemplateParameterKind::TemplateTemplate &&
		    parameter.name == name)
			return &parameter;
	}
	return NULL;
}

bool function_parameter_pack_name(TypePtr type, string& name)
{
	if (type.get() == NULL)
		return false;
	TypePtr bare = pa11::strip_cv(type);
	if (bare->kind == pa11::TypeKind::Pointer ||
	    bare->kind == pa11::TypeKind::LValueReference ||
	    bare->kind == pa11::TypeKind::RValueReference ||
	    bare->kind == pa11::TypeKind::Array)
		return function_parameter_pack_name(bare->base, name);
	if (bare->kind == pa11::TypeKind::TemplateParameter &&
	    deducible_template_parameter_type(bare) &&
	    active_match_parameter_is_pack(bare->name))
	{
		name = bare->name;
		return true;
	}
	if (bare->kind == pa11::TypeKind::Function)
	{
		if (function_parameter_pack_name(bare->base, name))
			return true;
		for (size_t i = 0; i < bare->parameters.size(); ++i)
			if (function_parameter_pack_name(bare->parameters[i], name))
				return true;
	}
	if (bare->kind == pa11::TypeKind::MemberPointer)
		return function_parameter_pack_name(bare->member_class, name) ||
		       function_parameter_pack_name(bare->base, name);
	return false;
}

bool match_function_parameter_pack_pattern(
	TypePtr pattern,
	const vector<TypePtr>& actual,
	size_t begin,
	size_t end,
	const string& pack_name,
	map<string, TemplateArgument>& deduced,
	const map<const void*, vector<TemplateArgument> >& record_arguments)
{
	map<string, TemplateArgument> local = deduced;
	vector<TemplateArgument> pack;
	for (size_t i = begin; i < end; ++i)
	{
		map<string, TemplateArgument> per_element = local;
		if (!match_template_type_pattern(pattern,
		                                 actual[i],
		                                 per_element,
		                                 record_arguments))
			return false;
		map<string, TemplateArgument>::iterator found =
			per_element.find(pack_name);
		if (found == per_element.end())
			return false;
		pack.push_back(found->second);
		per_element.erase(found);
		for (map<string, TemplateArgument>::const_iterator it =
			     per_element.begin();
		     it != per_element.end();
		     ++it)
			if (!merge_deduced_template_argument(local,
			                                     it->first,
			                                     it->second,
			                                     record_arguments))
				return false;
	}
	if (!merge_deduced_template_argument(local,
	                                     pack_name,
	                                     TemplateArgument::pack_arg(pack),
	                                     record_arguments))
		return false;
	deduced = local;
	return true;
}

bool match_function_parameter_type_sequence_from(
	const vector<TypePtr>& pattern,
	size_t pattern_index,
	const vector<TypePtr>& actual,
	size_t actual_index,
	map<string, TemplateArgument>& deduced,
	const map<const void*, vector<TemplateArgument> >& record_arguments)
{
	if (pattern_index == pattern.size())
		return actual_index == actual.size();
	string pack_name;
	if (function_parameter_pack_name(pattern[pattern_index], pack_name))
	{
		for (size_t end = actual_index; end <= actual.size(); ++end)
		{
			map<string, TemplateArgument> local = deduced;
			if (!match_function_parameter_pack_pattern(
				    pattern[pattern_index],
				    actual,
				    actual_index,
				    end,
				    pack_name,
				    local,
				    record_arguments))
				continue;
			if (match_function_parameter_type_sequence_from(
				    pattern,
				    pattern_index + 1,
				    actual,
				    end,
				    local,
				    record_arguments))
			{
				deduced = local;
				return true;
			}
		}
		return false;
	}
	if (actual_index == actual.size())
		return false;
	map<string, TemplateArgument> local = deduced;
	if (!match_template_type_pattern(pattern[pattern_index],
	                                 actual[actual_index],
	                                 local,
	                                 record_arguments))
		return false;
	if (!match_function_parameter_type_sequence_from(pattern,
	                                                 pattern_index + 1,
	                                                 actual,
	                                                 actual_index + 1,
	                                                 local,
	                                                 record_arguments))
		return false;
	deduced = local;
	return true;
}

bool match_function_parameter_type_sequence(
	const vector<TypePtr>& pattern,
	const vector<TypePtr>& actual,
	map<string, TemplateArgument>& deduced,
	const map<const void*, vector<TemplateArgument> >& record_arguments)
{
	return match_function_parameter_type_sequence_from(pattern,
	                                                   0,
	                                                   actual,
	                                                   0,
	                                                   deduced,
	                                                   record_arguments);
}

bool template_parameter_lists_match(const vector<TemplateParameterInfo>& left,
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
			if (left[i].kind == TemplateParameterKind::NonType &&
			    left[i].type.get() != NULL &&
			    right[i].type.get() != NULL &&
			    !pa11::same_type(left[i].type, right[i].type))
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

bool template_template_parameter_compatible(
	const TemplateParameterInfo& pattern,
	const TemplateParameterInfo& actual);

bool template_template_parameter_lists_compatible(
	const vector<TemplateParameterInfo>& pattern,
	const vector<TemplateParameterInfo>& actual)
{
	size_t actual_index = 0;
	for (size_t i = 0; i < pattern.size(); ++i)
	{
		const TemplateParameterInfo& parameter = pattern[i];
		if (parameter.is_pack)
		{
			while (actual_index < actual.size())
			{
				if (!template_template_parameter_compatible(
					    parameter,
					    actual[actual_index]))
					return false;
				++actual_index;
			}
			return true;
		}
		if (actual_index == actual.size())
			return parameter.has_default;
		if (!template_template_parameter_compatible(parameter,
		                                           actual[actual_index]))
			return false;
		++actual_index;
	}
	return actual_index == actual.size();
}

bool template_template_parameter_compatible(
	const TemplateParameterInfo& pattern,
	const TemplateParameterInfo& actual)
{
	if (pattern.kind != actual.kind)
		return false;
	if (!pattern.is_pack && actual.is_pack)
		return false;
	if (pattern.kind == TemplateParameterKind::NonType &&
	    pattern.type.get() != NULL &&
	    actual.type.get() != NULL &&
	    !pa11::same_type(pattern.type, actual.type))
		return false;
	if (pattern.kind == TemplateParameterKind::TemplateTemplate &&
	    !template_template_parameter_lists_compatible(
		    pattern.template_parameters,
		    actual.template_parameters))
		return false;
	return true;
}

void merge_template_parameter_defaults(
	vector<TemplateParameterInfo>& target,
	const vector<TemplateParameterInfo>& source)
{
	if (target.size() < source.size())
		target.resize(source.size());
	for (size_t i = 0; i < source.size(); ++i)
	{
		if (!source[i].has_default)
			continue;
		target[i].has_default = true;
		target[i].default_begin = source[i].default_begin;
		target[i].default_end = source[i].default_end;
	}
}

bool unsigned_integral_type(TypePtr type)
{
	TypePtr bare = type.get() != NULL ? pa11::strip_cv(type) : TypePtr();
	if (bare.get() == NULL)
		return false;
	if (bare->kind == pa11::TypeKind::Enum)
	{
		switch (bare->enum_underlying)
		{
		case FT_UNSIGNED_CHAR:
		case FT_UNSIGNED_SHORT_INT:
		case FT_UNSIGNED_INT:
		case FT_UNSIGNED_LONG_INT:
		case FT_UNSIGNED_LONG_LONG_INT:
			return true;
		default:
			return false;
		}
	}
	if (bare->kind != pa11::TypeKind::Fundamental)
		return false;
	switch (bare->fundamental)
	{
	case FT_BOOL:
	case FT_UNSIGNED_CHAR:
	case FT_UNSIGNED_SHORT_INT:
	case FT_UNSIGNED_INT:
	case FT_UNSIGNED_LONG_INT:
	case FT_UNSIGNED_LONG_LONG_INT:
	case FT_CHAR16_T:
	case FT_CHAR32_T:
		return true;
	default:
		return false;
	}
}

uint64_t canonical_template_value(TypePtr type, uint64_t value)
{
	TypePtr bare = type.get() != NULL ? pa11::strip_cv(type) : TypePtr();
	if (bare.get() != NULL &&
	    bare->kind == pa11::TypeKind::Fundamental &&
	    bare->fundamental == FT_BOOL)
		return value != 0 ? 1 : 0;
	size_t size = 0;
	try
	{
		if (type.get() != NULL)
			size = pa11::type_size(type);
	}
	catch (const runtime_error&)
	{
		size = 0;
	}
	if (size == 0 || size >= 8)
		return value;
	uint64_t mask = (uint64_t(1) << (size * 8)) - 1;
	value &= mask;
	if (!unsigned_integral_type(type))
	{
		uint64_t sign = uint64_t(1) << (size * 8 - 1);
		if ((value & sign) != 0)
			value |= ~mask;
	}
	return value;
}

bool compatible_template_value_types(TypePtr left, TypePtr right)
{
	if (left.get() == NULL || right.get() == NULL)
		return true;
	if (pa11::same_type(left, right))
		return true;
	return pa11::is_integral_or_bool_type(left) &&
	       pa11::is_integral_or_bool_type(right);
}

bool match_template_type_pattern(
	TypePtr pattern,
	TypePtr actual,
	map<string, TemplateArgument>& deduced,
	const map<const void*, vector<TemplateArgument> >& record_arguments)
{ if (pattern.get() == NULL || actual.get() == NULL) return pattern.get() == actual.get(); string active_dependent_parameter_name; if (simple_active_dependent_type_parameter(pattern, active_dependent_parameter_name)) {
TemplateArgument arg = TemplateArgument::type_arg(actual); map<string, TemplateArgument>::iterator found = deduced.find(active_dependent_parameter_name); if (found == deduced.end()) {
deduced[active_dependent_parameter_name] = arg; return true; } return same_template_argument_value(found->second, arg, record_arguments); } bool active_template_template_pattern = pattern->is_dependent_typename &&
pattern->dependent_typename_template_id && !pattern->template_primary_name.empty() && active_match_parameter_is_template_template( pattern->template_primary_name); if (pattern->is_dependent_typename &&
active_template_match_parser != NULL && !active_template_template_pattern) { try { TypePtr substituted = active_template_match_parser ->substitute_type_for_template_match(pattern, deduced);
if (substituted.get() != NULL && substituted.get() != pattern.get() && template_type_key(substituted) != template_type_key(pattern)) return match_template_type_pattern(substituted, actual, deduced, record_arguments); }
catch (const runtime_error&) { return false; } } if (active_template_template_pattern && active_template_match_parser != NULL) { if (actual->kind == pa11::TypeKind::Cv) return false; TemplateArgument actual_template =
TemplateArgument::template_arg( active_template_match_parser ->class_template_declaration_for_match(actual)); if (actual_template.template_declaration == NULL && actual->is_template_specialization &&
actual->scope == NULL) actual_template.value_name = actual->template_primary_name; if (actual_template.template_declaration == NULL && actual_template.value_name.empty()) return false;
const TemplateParameterInfo* template_parameter = active_match_template_template_parameter( pattern->template_primary_name); if (template_parameter != NULL && actual_template.template_declaration != NULL &&
!template_template_parameter_lists_compatible( template_parameter->template_parameters, actual_template.template_declaration->parameters)) return false; map<string, TemplateArgument>::iterator found =
deduced.find(pattern->template_primary_name); if (found == deduced.end()) deduced[pattern->template_primary_name] = actual_template; else if (!same_template_argument_value(found->second, actual_template,
record_arguments)) return false; map<const void*, vector<TemplateArgument> >::const_iterator ait = record_arguments.find(actual.get()); vector<TemplateArgument> pattern_args =
match_template_arguments_from_instance_arguments( pattern->template_arguments); vector<TemplateArgument> actual_args = !actual->template_arguments.empty() ? match_template_arguments_from_instance_arguments(
actual->template_arguments) : (ait != record_arguments.end() ? ait->second : vector<TemplateArgument>()); bool pattern_has_pack_pattern = false; for (size_t i = 0; i < pattern_args.size(); ++i) { string pack_name;
if (pattern_args[i].pack_expansion || pack_argument_parameter_name(pattern_args[i], pack_name)) pattern_has_pack_pattern = true; } if (pattern_has_pack_pattern) actual_args =
flatten_actual_template_argument_packs(actual_args); bool matched = match_template_argument_sequence_pattern( pattern_args, actual_args, deduced, record_arguments); return matched; }
if (deducible_template_parameter_type(pattern)) { TemplateArgument arg = TemplateArgument::type_arg(actual); map<string, TemplateArgument>::iterator found = deduced.find(pattern->name); if (found == deduced.end()) {
deduced[pattern->name] = arg; return true; } return same_template_argument_value(found->second, arg, record_arguments); } if (actual->is_dependent_typename && active_template_match_parser != NULL &&
!template_type_has_template_parameter(actual, record_arguments)) { try { TypePtr substituted = active_template_match_parser ->substitute_type_for_template_match(actual, deduced); if (substituted.get() != NULL &&
substituted.get() != actual.get() && template_type_key(substituted) != template_type_key(actual)) return match_template_type_pattern(pattern, substituted, deduced, record_arguments); } catch (const runtime_error&) { } }
if (pattern->kind != actual->kind) return false; switch (pattern->kind) { case pa11::TypeKind::Fundamental: return pattern->fundamental == actual->fundamental; case pa11::TypeKind::Cv: return pattern->cv == actual->cv &&
match_template_type_pattern(pattern->base, actual->base, deduced, record_arguments); case pa11::TypeKind::Pointer: case pa11::TypeKind::LValueReference: case pa11::TypeKind::RValueReference:
return match_template_type_pattern(pattern->base, actual->base, deduced, record_arguments); case pa11::TypeKind::Array: if (pattern->unknown_bound) { if (!actual->unknown_bound && !pattern->name.empty()) {
TemplateArgument bound = TemplateArgument::value_arg( pa11::make_fundamental(FT_UNSIGNED_LONG_INT), actual->bound); if (!merge_deduced_template_argument(deduced, pattern->name, bound, record_arguments)) return false; }
else if (!actual->unknown_bound) return false; } else if (actual->unknown_bound || pattern->bound != actual->bound) return false; return match_template_type_pattern(pattern->base, actual->base, deduced,
record_arguments); case pa11::TypeKind::Function: if (pattern->cv != actual->cv || pattern->ref_qualifier != actual->ref_qualifier || pattern->variadic != actual->variadic) return false;
if (!match_template_type_pattern(pattern->base, actual->base, deduced, record_arguments)) return false; return match_function_parameter_type_sequence( pattern->parameters, actual->parameters, deduced, record_arguments);
case pa11::TypeKind::MemberPointer: return match_template_type_pattern(pattern->member_class, actual->member_class, deduced, record_arguments) && match_template_type_pattern(pattern->base, actual->base, deduced,
record_arguments); case pa11::TypeKind::Record: { map<const void*, vector<TemplateArgument> >::const_iterator same_pit = record_arguments.find(pattern.get()); bool same_type_needs_deduction =
same_pit != record_arguments.end() && template_arguments_have_deducible_pattern(same_pit->second, record_arguments); if (pa11::same_type(pattern, actual) && !same_type_needs_deduction) return true;
if (pattern->is_template_specialization && !pattern->template_primary_name.empty() && active_template_match_parser != NULL && (pattern->scope == NULL || active_match_parameter_is_template_template(
pattern->template_primary_name))) { TemplateArgument actual_template = TemplateArgument::template_arg( active_template_match_parser ->class_template_declaration_for_match(actual));
if (actual_template.template_declaration == NULL && actual->is_template_specialization && actual->scope == NULL) actual_template.value_name = actual->template_primary_name;
if (actual_template.template_declaration == NULL && actual_template.value_name.empty()) return false; const TemplateParameterInfo* template_parameter = active_match_template_template_parameter(
pattern->template_primary_name); if (template_parameter != NULL && actual_template.template_declaration != NULL && !template_template_parameter_lists_compatible( template_parameter->template_parameters,
actual_template.template_declaration->parameters)) return false; map<string, TemplateArgument>::iterator found = deduced.find(pattern->template_primary_name); if (found == deduced.end())
deduced[pattern->template_primary_name] = actual_template; else if (!same_template_argument_value(found->second, actual_template, record_arguments)) return false;
map<const void*, vector<TemplateArgument> >::const_iterator pit = record_arguments.find(pattern.get()); map<const void*, vector<TemplateArgument> >::const_iterator ait = record_arguments.find(actual.get());
bool have_pattern_instance_args = !pattern->template_arguments.empty(); vector<TemplateArgument> pattern_instance_args = have_pattern_instance_args ? match_template_arguments_from_instance_arguments(
pattern->template_arguments) : vector<TemplateArgument>(); bool use_pattern_record_args = pit != record_arguments.end() && (!have_pattern_instance_args || pit->second.size() == pattern_instance_args.size()) &&
template_arguments_have_deducible_pattern( pit->second, record_arguments); vector<TemplateArgument> pattern_args = use_pattern_record_args ? pit->second : have_pattern_instance_args ? pattern_instance_args
: (pit != record_arguments.end() ? pit->second : vector<TemplateArgument>()); vector<TemplateArgument> actual_args = !actual->template_arguments.empty() ? match_template_arguments_from_instance_arguments(
actual->template_arguments) : (ait != record_arguments.end() ? ait->second : vector<TemplateArgument>()); bool pattern_has_pack_pattern = false; for (size_t i = 0; i < pattern_args.size(); ++i) { string pack_name;
if (pattern_args[i].pack_expansion || pack_argument_parameter_name(pattern_args[i], pack_name)) pattern_has_pack_pattern = true; } if (pattern_has_pack_pattern) actual_args =
flatten_actual_template_argument_packs(actual_args); return match_template_argument_sequence_pattern(pattern_args, actual_args, deduced, record_arguments); } if (!same_template_record_primary(pattern, actual))
return false; map<const void*, vector<TemplateArgument> >::const_iterator pit = record_arguments.find(pattern.get()); map<const void*, vector<TemplateArgument> >::const_iterator ait = record_arguments.find(actual.get());
if (pit == record_arguments.end()) return false; bool have_pattern_instance_args = !pattern->template_arguments.empty(); vector<TemplateArgument> pattern_instance_args = have_pattern_instance_args
? match_template_arguments_from_instance_arguments( pattern->template_arguments) : vector<TemplateArgument>(); bool compatible_pattern_record_args = !have_pattern_instance_args ||
pit->second.size() == pattern_instance_args.size(); bool use_pattern_record_args = compatible_pattern_record_args && (template_arguments_have_pack_expansion_recursive( pit->second) ||
template_arguments_have_deducible_pattern( pit->second, record_arguments)); vector<TemplateArgument> pattern_args = use_pattern_record_args ? pit->second : have_pattern_instance_args ? pattern_instance_args
: pit->second; vector<TemplateArgument> actual_args = ait != record_arguments.end() && template_arguments_have_pack_expansion_recursive(ait->second) ? ait->second : !actual->template_arguments.empty()
? match_template_arguments_from_instance_arguments( actual->template_arguments) : (ait != record_arguments.end() ? ait->second : vector<TemplateArgument>()); bool pattern_has_pack_pattern = false;
for (size_t i = 0; i < pattern_args.size(); ++i) { string pack_name; if (pattern_args[i].pack_expansion || pack_argument_parameter_name(pattern_args[i], pack_name)) pattern_has_pack_pattern = true; }
if (pattern_has_pack_pattern) actual_args = flatten_actual_template_argument_packs(actual_args); bool actual_has_template_arguments = !actual->template_arguments.empty() || ait != record_arguments.end();
if (actual_args.empty() && !actual_has_template_arguments) return false; bool matched = match_template_argument_sequence_pattern(pattern_args, actual_args, deduced, record_arguments); return matched; }
case pa11::TypeKind::Enum: case pa11::TypeKind::TemplateTemplateParameter: return pa11::same_type(pattern, actual); case pa11::TypeKind::TemplateParameter: return pa11::same_type(pattern, actual); }
throw logic_error("unknown type kind"); }

bool same_template_argument_value(
	const TemplateArgument& left,
	const TemplateArgument& right,
	const map<const void*, vector<TemplateArgument> >& record_arguments)
{
	if (left.kind != right.kind)
		return false;
	if (left.kind == TemplateArgumentKind::Type)
	{
		if (pa11::same_type(left.type, right.type))
			return true;
		map<string, TemplateArgument> deduced;
		return match_template_type_pattern(left.type,
		                                   right.type,
		                                   deduced,
		                                   record_arguments) &&
		       deduced.empty();
	}
	if (left.kind == TemplateArgumentKind::Value)
	{
		if (left.value_binding != NULL || right.value_binding != NULL)
			return left.value_binding == right.value_binding &&
			       (left.type.get() == NULL || right.type.get() == NULL ||
			        pa11::same_type(left.type, right.type));
		if (left.dependent && right.dependent &&
		    left.value_expr_end > left.value_expr_begin)
			return left.value_expr_begin == right.value_expr_begin &&
			       left.value_expr_end == right.value_expr_end &&
			       (left.type.get() == NULL || right.type.get() == NULL ||
			        pa11::same_type(left.type, right.type));
		if (left.dependent || right.dependent)
			return left.dependent && right.dependent &&
			       left.value_negated == right.value_negated &&
			       !left.value_name.empty() &&
			       left.value_name == right.value_name &&
			       (left.type.get() == NULL || right.type.get() == NULL ||
			        pa11::same_type(left.type, right.type));
		if (left.dependent || right.dependent)
			return false;
		if (!compatible_template_value_types(left.type, right.type))
			return false;
		TypePtr value_type = right.type.get() != NULL ? right.type : left.type;
		return canonical_template_value(value_type, left.value) ==
		       canonical_template_value(value_type, right.value);
	}
	if (left.kind == TemplateArgumentKind::Template)
	{
		if (left.template_declaration != NULL ||
		    right.template_declaration != NULL)
			return left.template_declaration == right.template_declaration;
		return !left.value_name.empty() &&
		       left.value_name == right.value_name;
	}
	if (left.pack.size() == right.pack.size())
	{
		bool exact = true;
		for (size_t i = 0; i < left.pack.size(); ++i)
			if (left.pack[i].pack_expansion !=
			        right.pack[i].pack_expansion ||
			    !same_template_argument_value(left.pack[i],
			                                  right.pack[i],
			                                  record_arguments))
				exact = false;
		if (exact)
			return true;
	}
	map<string, TemplateArgument> deduced;
	return match_template_argument_sequence_pattern(left.pack,
	                                                right.pack,
	                                                deduced,
	                                                record_arguments) &&
	       deduced.empty();
}

bool pack_argument_parameter_name(const TemplateArgument& pattern,
                                  string& name)
{
	if (pattern.kind != TemplateArgumentKind::Pack ||
	    pattern.pack.size() != 1)
		return false;
	const TemplateArgument& element = pattern.pack[0];
	if (element.kind == TemplateArgumentKind::Type &&
	    element.type.get() != NULL &&
	    (deducible_template_parameter_type(element.type) ||
	     simple_active_dependent_type_parameter(element.type, name)))
	{
		if (name.empty())
			name = element.type->name;
		return active_match_parameter_is_pack(name);
	}
	if (element.kind == TemplateArgumentKind::Value &&
	    !element.value_name.empty())
	{
		name = element.value_name;
		return active_match_parameter_is_pack(name);
	}
	if (element.kind == TemplateArgumentKind::Template &&
	    element.template_declaration == NULL &&
	    !element.value_name.empty())
	{
		name = element.value_name;
		return active_match_parameter_is_pack(name);
	}
	return false;
}

bool match_template_argument_pattern(
	const TemplateArgument& pattern,
	const TemplateArgument& actual,
	map<string, TemplateArgument>& deduced,
	const map<const void*, vector<TemplateArgument> >& record_arguments)
{
	if (!pattern.pack_expansion && actual.pack_expansion)
		return false;
	if (pattern.kind == TemplateArgumentKind::Type &&
	    pattern.type.get() != NULL &&
	    deducible_template_parameter_type(pattern.type))
	{
		map<string, TemplateArgument>::iterator found =
			deduced.find(pattern.type->name);
		if (found == deduced.end())
		{
			deduced[pattern.type->name] = actual;
			return true;
		}
		return same_template_argument_value(found->second,
		                                    actual,
		                                    record_arguments);
	}
	if (pattern.kind != actual.kind)
		return false;
	if (pattern.kind == TemplateArgumentKind::Pack)
	{
		string pack_name;
		if (pack_argument_parameter_name(pattern, pack_name))
		{
			map<string, TemplateArgument>::iterator found =
				deduced.find(pack_name);
			if (found == deduced.end())
			{
				deduced[pack_name] = actual;
				return true;
			}
			return same_template_argument_value(found->second,
			                                    actual,
			                                    record_arguments);
		}
	}
	if (pattern.kind == TemplateArgumentKind::Type)
	{
		return match_template_type_pattern(pattern.type,
		                                   actual.type,
		                                   deduced,
		                                   record_arguments);
	}
	if (pattern.kind == TemplateArgumentKind::Value)
	{
		if (pattern.dependent && !pattern.value_name.empty())
		{
			map<string, TemplateArgument>::iterator found =
				deduced.find(pattern.value_name);
			if (found == deduced.end())
			{
				deduced[pattern.value_name] = actual;
				return true;
			}
			return same_template_argument_value(found->second,
			                                    actual,
			                                    record_arguments);
		}
		if (pattern.dependent &&
		    pattern.value_expr_end > pattern.value_expr_begin)
		{
			if (actual.dependent)
				return same_template_argument_value(pattern,
				                                    actual,
				                                    record_arguments);
			return true;
		}
		if (pattern.value_binding != NULL || actual.value_binding != NULL)
			return pattern.value_binding == actual.value_binding;
		if (pattern.dependent || actual.dependent)
			return false;
		if (!compatible_template_value_types(pattern.type, actual.type))
			return false;
		TypePtr value_type =
			actual.type.get() != NULL ? actual.type : pattern.type;
		return canonical_template_value(value_type, pattern.value) ==
		       canonical_template_value(value_type, actual.value);
	}
	if (pattern.kind == TemplateArgumentKind::Template)
	{
		if (pattern.template_declaration == NULL &&
		    !pattern.value_name.empty())
		{
			map<string, TemplateArgument>::iterator found =
				deduced.find(pattern.value_name);
			if (found == deduced.end())
			{
				deduced[pattern.value_name] = actual;
				return true;
			}
			return same_template_argument_value(found->second,
			                                    actual,
			                                    record_arguments);
		}
		if (pattern.template_declaration != NULL ||
		    actual.template_declaration != NULL)
			return pattern.template_declaration == actual.template_declaration;
		return !pattern.value_name.empty() &&
		       pattern.value_name == actual.value_name;
	}
	return match_template_argument_sequence_pattern(pattern.pack,
	                                                actual.pack,
	                                                deduced,
	                                                record_arguments);
}

bool merge_deduced_template_argument(
	map<string, TemplateArgument>& target,
	const string& name,
	const TemplateArgument& value,
	const map<const void*, vector<TemplateArgument> >& record_arguments)
{
	map<string, TemplateArgument>::iterator found = target.find(name);
	if (found == target.end())
	{
		target[name] = value;
		return true;
	}
	return same_template_argument_value(found->second,
	                                    value,
	                                    record_arguments);
}

bool pack_expansion_parameter_name(const TemplateArgument& pattern,
                                   string& name)
{
	if (pattern.kind == TemplateArgumentKind::Pack)
		return pack_argument_parameter_name(pattern, name);
	if (!pattern.pack_expansion)
		return false;
	if (pattern.kind == TemplateArgumentKind::Type)
		return template_type_has_template_parameter_name(pattern.type, name) ||
		       simple_active_dependent_type_parameter(pattern.type, name);
	if (pattern.kind == TemplateArgumentKind::Value)
	{
		if (!pattern.value_name.empty())
		{
			name = pattern.value_name;
			return true;
		}
		return template_type_has_template_parameter_name(pattern.type, name);
	}
	return false;
}

bool simple_pack_expansion_pattern(const TemplateArgument& pattern,
                                   const string& name)
{
	if (pattern.kind == TemplateArgumentKind::Type &&
	    pattern.type.get() != NULL &&
	    pattern.type->kind == pa11::TypeKind::TemplateParameter &&
	    pattern.type->name == name)
		return true;
	if (pattern.kind == TemplateArgumentKind::Value &&
	    pattern.value_name == name)
		return true;
	return false;
}

}  // namespace internal
}  // namespace pa12
