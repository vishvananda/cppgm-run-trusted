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
bool constructor_template_function_template_symbol(
	const TemplateDeclaration* declaration);
TypePtr remove_pattern_cv_from_argument(TypePtr argument, unsigned cv);
size_t function_body_start(const std::vector<Token>& tokens,
                           size_t begin,
                           size_t end);
size_t constructor_body_start(const std::vector<Token>& tokens,
                              size_t begin,
                              size_t end);
std::vector<ParameterInfo> concrete_member_body_parameters(
	Binding* function,
	const std::map<Binding*, std::vector<std::string> >&
		function_parameter_names);
bool function_body_signature_matches(Binding* function, const Node& body);
bool matching_member_template_class_specialization(
	Parser* parser,
	TemplateDeclaration* primary,
	TemplateDeclaration* specialization,
	const std::vector<TemplateArgument>& primary_args,
	const std::map<const void*, std::vector<TemplateArgument> >&
		record_arguments);
bool member_template_set_has_class_specialization(
	Parser* parser,
	TemplateDeclaration* primary,
	const std::vector<TemplateDeclaration*>& declarations,
	const std::vector<TemplateArgument>& primary_args,
	const std::map<const void*, std::vector<TemplateArgument> >&
		record_arguments);
bool member_template_definition_matches_owner(
	Parser* parser,
	TemplateDeclaration* declared_owner,
	TemplateDeclaration* owner,
	TemplateDeclaration* primary,
	TemplateDeclaration* declaration,
	const std::vector<TemplateArgument>& primary_args,
	const std::map<const void*, std::vector<TemplateArgument> >&
		record_arguments);
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
