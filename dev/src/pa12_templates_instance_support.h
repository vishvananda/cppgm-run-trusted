#pragma once

#include <map>
#include <set>
#include <string>
#include <vector>

#include "pa12_internal.h"

namespace pa12 {
namespace internal {

extern Parser* active_template_match_parser;
extern const std::vector<TemplateParameterInfo>*
	active_template_match_parameters;

struct TemplateMatchParserScope
{
	Parser* saved;

	explicit TemplateMatchParserScope(Parser* parser);
	~TemplateMatchParserScope();
};

struct TemplateMatchParameterScope
{
	const std::vector<TemplateParameterInfo>* saved;

	explicit TemplateMatchParameterScope(
		const std::vector<TemplateParameterInfo>* parameters);
	~TemplateMatchParameterScope();
};

bool same_template_record_type(TypePtr left, TypePtr right);
bool declaration_starts_class_key(const std::vector<Token>& tokens,
                                  const TemplateDeclaration* declaration);
bool same_constructor_type_for_owner(TypePtr candidate,
                                     TypePtr wanted,
                                     TypePtr owner);
bool same_static_member_type_with_owner_parameter(TypePtr candidate,
                                                  TypePtr wanted,
                                                  TypePtr owner);
bool type_contains_parameter_name(
	TypePtr type,
	const std::string& name,
	const std::map<const void*, std::vector<TemplateArgument> >&
		record_arguments);
void collect_type_parameter_names(
	TypePtr type,
	const std::map<const void*, std::vector<TemplateArgument> >&
		record_arguments,
	std::set<std::string>& names);
bool type_mentions_active_record(
	TypePtr type,
	const std::vector<ActiveClassInstantiation>& active);
std::map<Binding*, Node>::const_iterator
find_static_member_initializer_for_binding(
	const std::map<Binding*, Node>& initializers,
	Binding* binding);
bool collect_replay_tokens(const std::string& source,
                           std::vector<Token>& out);
bool node_calls_function_template(
	const Node& node,
	const std::map<Binding*, TemplateDeclaration*>& placeholders);

std::string template_type_spelling(TypePtr type);
std::string template_type_key(TypePtr type);
void clear_template_type_key_cache();
void discard_template_type_key_cache(TypePtr type);
std::string dependent_value_member_key(const TemplateArgument& arg);
std::string template_argument_spelling(const TemplateArgument& argument);
std::string template_argument_spelling(
	const std::vector<TemplateArgument>& arguments);
std::string template_argument_key_part(const TemplateArgument& argument);
pa11::TemplateInstanceArgument template_instance_argument(
	const TemplateArgument& argument);
std::vector<pa11::TemplateInstanceArgument> template_instance_arguments(
	const std::vector<TemplateArgument>& arguments);
bool single_instance_pack_element_is_expansion(
	const TemplateArgument& argument);
TemplateArgument template_argument_from_instance_argument(
	const pa11::TemplateInstanceArgument& argument);
TemplateArgument raw_template_argument_from_instance_argument(
	const pa11::TemplateInstanceArgument& argument);

bool template_argument_has_pack_expansion_recursive(
	const TemplateArgument& argument);
bool template_arguments_have_pack_expansion_recursive(
	const std::vector<TemplateArgument>& arguments);
bool template_arguments_have_deducible_pattern(
	const std::vector<TemplateArgument>& arguments,
	const std::map<const void*, std::vector<TemplateArgument> >&
		record_arguments);
bool template_arguments_have_template_template_parameter(
	const std::vector<TemplateArgument>& arguments);
bool same_template_record_primary(TypePtr pattern, TypePtr actual);
bool active_match_parameter_is_template_template(const std::string& name);
const TemplateParameterInfo* active_match_template_template_parameter(
	const std::string& name);
bool template_template_parameter_lists_compatible(
	const std::vector<TemplateParameterInfo>& pattern,
	const std::vector<TemplateParameterInfo>& actual);
bool template_parameter_lists_match(
	const std::vector<TemplateParameterInfo>& left,
	const std::vector<TemplateParameterInfo>& right);
void merge_template_parameter_defaults(
	std::vector<TemplateParameterInfo>& target,
	const std::vector<TemplateParameterInfo>& source);
bool deducible_template_parameter_type(TypePtr type);
std::vector<TemplateArgument> match_template_arguments_from_instance_arguments(
	const std::vector<pa11::TemplateInstanceArgument>& arguments);
bool same_template_argument_value(
	const TemplateArgument& left,
	const TemplateArgument& right,
	const std::map<const void*, std::vector<TemplateArgument> >&
		record_arguments);
bool merge_deduced_template_argument(
	std::map<std::string, TemplateArgument>& target,
	const std::string& name,
	const TemplateArgument& value,
	const std::map<const void*, std::vector<TemplateArgument> >&
		record_arguments);
bool match_template_type_pattern(
	TypePtr pattern,
	TypePtr actual,
	std::map<std::string, TemplateArgument>& deduced,
	const std::map<const void*, std::vector<TemplateArgument> >&
		record_arguments);
bool match_template_argument_pattern(
	const TemplateArgument& pattern,
	const TemplateArgument& actual,
	std::map<std::string, TemplateArgument>& deduced,
	const std::map<const void*, std::vector<TemplateArgument> >&
		record_arguments);
bool match_pack_expansion_pattern(
	const TemplateArgument& pattern,
	const std::vector<TemplateArgument>& actual,
	size_t begin,
	size_t end,
	std::map<std::string, TemplateArgument>& deduced,
	const std::map<const void*, std::vector<TemplateArgument> >&
		record_arguments);
bool pack_expansion_parameter_name(const TemplateArgument& pattern,
                                   std::string& name);
bool simple_pack_expansion_pattern(const TemplateArgument& pattern,
                                   const std::string& name);
bool match_dependent_alias_projection_argument(
	const TemplateArgument& pattern,
	const TemplateArgument& actual,
	std::map<std::string, TemplateArgument>& deduced,
	const std::map<const void*, std::vector<TemplateArgument> >&
		record_arguments);
bool match_dependent_alias_projection(
	const std::vector<TemplateArgument>& pattern,
	const std::vector<TemplateArgument>& actual,
	std::map<std::string, TemplateArgument>& deduced,
	const std::map<const void*, std::vector<TemplateArgument> >&
		record_arguments);
bool match_template_argument_sequence_pattern_from(
	const std::vector<TemplateArgument>& pattern,
	size_t pattern_index,
	const std::vector<TemplateArgument>& actual,
	size_t actual_index,
	std::map<std::string, TemplateArgument>& deduced,
	const std::map<const void*, std::vector<TemplateArgument> >&
		record_arguments);
bool match_template_argument_sequence_pattern(
	const std::vector<TemplateArgument>& pattern,
	const std::vector<TemplateArgument>& actual,
	std::map<std::string, TemplateArgument>& deduced,
	const std::map<const void*, std::vector<TemplateArgument> >&
		record_arguments);
bool template_argument_sequence_has_pack_expansion(
	const std::vector<TemplateArgument>& pattern);
bool pack_argument_parameter_name(const TemplateArgument& pattern,
                                  std::string& name);
std::vector<TemplateArgument> flatten_template_argument_packs(
	const std::vector<TemplateArgument>& arguments);
std::vector<TemplateArgument> flatten_actual_template_argument_packs(
	const std::vector<TemplateArgument>& arguments);
uint64_t canonical_template_value(TypePtr type, uint64_t value);
bool compatible_template_value_types(TypePtr left, TypePtr right);
bool template_value_patterns_match_after_deduction(
	Parser* parser,
	TemplateDeclaration* specialization,
	const TemplateArgument& pattern,
	const TemplateArgument& actual,
	const std::map<std::string, TemplateArgument>& deduced);
bool template_value_patterns_match_after_deduction(
	Parser* parser,
	TemplateDeclaration* specialization,
	const std::vector<TemplateArgument>& pattern,
	const std::vector<TemplateArgument>& actual,
	const std::map<std::string, TemplateArgument>& deduced);
bool match_class_specialization(
	TemplateDeclaration* primary,
	TemplateDeclaration* specialization,
	const std::vector<TemplateArgument>& full_args,
	size_t explicit_arg_count,
	std::vector<TemplateArgument>& selected_args,
	const std::map<const void*, std::vector<TemplateArgument> >&
		record_arguments);
bool class_specialization_more_specialized(
	TemplateDeclaration* left,
	TemplateDeclaration* right,
	const std::map<const void*, std::vector<TemplateArgument> >&
		record_arguments);
bool template_instance_arguments_have_pack(
	const std::vector<pa11::TemplateInstanceArgument>& arguments);

}  // namespace internal
}  // namespace pa12
