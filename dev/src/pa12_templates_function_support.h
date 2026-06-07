#pragma once

#include <map>
#include <string>
#include <vector>

#include "pa12_internal.h"

namespace pa12 {
namespace internal {

std::string generated_pack_parameter_name(const std::string& pack_name);
bool function_parameter_pack_name(TemplateDeclaration* declaration,
                                  TypePtr pattern,
                                  std::string& name);
bool match_or_deduce_value_argument(
	const TemplateArgument& pattern,
	const TemplateArgument& actual,
	std::map<std::string, TemplateArgument>* deduced);
bool bind_deduced_template_argument(
	std::map<std::string, TemplateArgument>* deduced,
	const std::string& name,
	TemplateDeclaration* declaration);
bool same_deduced_template_argument(const TemplateArgument& left,
                                    const TemplateArgument& right);
bool bind_deduced_pack_argument(
	std::map<std::string, TemplateArgument>* deduced,
	const std::string& name,
	const std::vector<TemplateArgument>& values);
bool template_argument_pack_parameter_name(const TemplateArgument& argument,
                                           std::string& name);
bool deduce_array_bound_arguments(
	TypePtr pattern,
	TypePtr argument,
	std::map<std::string, TemplateArgument>& deduced);
bool substituted_type_is_valid(TypePtr type);
bool substituted_function_parameter_types_are_valid(TypePtr type);
bool substituted_candidate_function_parameter_types_are_valid(TypePtr type);
bool template_parameter_lists_equivalent(
	const std::vector<TemplateParameterInfo>& left,
	const std::vector<TemplateParameterInfo>& right);
bool class_template_member_function_template_symbol(
	const TemplateDeclaration* declaration);
TypePtr remove_pattern_cv_from_argument(TypePtr argument, unsigned cv);
std::string abi_binding_symbol(
	const Binding* binding,
	const std::map<std::string, size_t>& template_parameters);
std::string abi_function_template_specialization_symbol(
	TemplateDeclaration* declaration,
	const std::vector<TemplateArgument>& full_args,
	Binding* binding,
	const std::vector<Token>* expression_tokens);

}  // namespace internal
}  // namespace pa12
