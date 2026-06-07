#pragma once

#include <map>
#include <string>
#include <vector>

#include "pa12_internal.h"

namespace pa12 {
namespace internal {

TypePtr decay_type(TypePtr type);
TypePtr remove_reference_type(TypePtr type);
TypePtr remove_cv_type(TypePtr type);
TypePtr remove_cvref_type(TypePtr type);
bool dependent_spelling_word_char(char c);
bool decltype_operand_is_parenthesized(const std::vector<Token>& tokens,
                                       size_t begin,
                                       size_t end);
bool type_structurally_dependent(TypePtr type);
bool instance_argument_structurally_dependent(
	const pa11::TemplateInstanceArgument& argument);
bool expr_node_structurally_dependent(const Node& node);
bool skip_template_id_syntax(const std::vector<Token>& tokens, size_t& pos);
bool internal_type_transform_name(const std::string& name);
TypePtr apply_internal_type_transform(const std::string& name, TypePtr inner);
pa11::TemplateInstanceArgument dependent_template_instance_argument(
	const TemplateArgument& argument);
std::vector<pa11::TemplateInstanceArgument>
dependent_template_instance_arguments(
	const std::vector<TemplateArgument>& arguments);
std::vector<std::vector<pa11::TemplateInstanceArgument> >
dependent_template_instance_argument_lists(
	const std::vector<std::vector<TemplateArgument> >& argument_lists);
bool angle_tokens_contain_decltype(const std::vector<Token>& tokens,
                                   size_t pos);
bool decltype_nested_name_specifier_ahead(const std::vector<Token>& tokens,
                                          size_t pos);
bool type_parse_mentions_active_record(
	TypePtr type,
	const std::vector<ActiveClassInstantiation>& active,
	const std::map<const void*, std::vector<TemplateArgument> >&
		record_template_arguments);
bool type_parse_template_argument_mentions_active_record(
	const TemplateArgument& argument,
	const std::vector<ActiveClassInstantiation>& active,
	const std::map<const void*, std::vector<TemplateArgument> >&
		record_template_arguments);
std::string dependent_token_spelling(const std::vector<Token>& tokens,
                                     size_t begin,
                                     size_t end);

}  // namespace internal
}  // namespace pa12
