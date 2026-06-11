#pragma once

#include "pa12_templates_function_support.h"

#include <map>
#include <string>
#include <vector>

namespace pa12 {
namespace internal {

struct AbiTokenType
{
	std::string encoded;
	bool dependent;
	bool concrete;
	TypePtr concrete_type;

	AbiTokenType() : dependent(false), concrete(false) {}
};

struct AbiSubstitutionContext
{
	std::map<std::string, size_t> template_parameters;
	std::map<std::string, size_t> actual_template_parameter_substitutions;
	std::vector<TemplateArgument> actual_template_arguments;
	const std::vector<Token>* expression_tokens;
	const std::vector<std::string>* function_parameter_names;
	std::vector<std::string> substitutions;
	std::map<std::string, size_t> substitution_aliases;
	std::map<std::string, size_t> semantic_type_substitutions;
	bool use_actual_template_parameter_types;

	AbiSubstitutionContext(
		const std::map<std::string, size_t>& parameters,
		const std::vector<Token>* tokens,
		const std::vector<std::string>* parameter_names)
		: template_parameters(parameters),
		  expression_tokens(tokens),
		  function_parameter_names(parameter_names),
		  use_actual_template_parameter_types(false)
	{
	}
};

std::string abi_source_name(const std::string& name);
std::string abi_binding_source_name(const Binding* binding);
std::string abi_fundamental_type(EFundamentalType type);
std::string abi_type(TypePtr type,
                     const std::map<std::string, size_t>& template_parameters,
                     const std::vector<Token>* expression_tokens);
std::string abi_record_type(TypePtr type,
                            const std::map<std::string, size_t>& template_parameters,
                            const std::vector<Token>* expression_tokens,
                            bool include_namespace);
std::string abi_encoded_stable_value_name(const std::string& name);
std::vector<std::string> abi_split_qualified_name(const std::string& name);
std::string abi_template_name(const std::string& name);
std::string abi_unresolved_name_path(const std::string& name);
std::string abi_template_parameter_expression(
	const std::string& name,
	const std::map<std::string, size_t>& template_parameters);
bool abi_token_is_simple(const std::vector<Token>& tokens,
                         size_t index,
                         ETokenType type);
void abi_trim_wrapping_parens(const std::vector<Token>& tokens,
                              size_t& begin,
                              size_t& end);
bool abi_find_top_level_operator(const std::vector<Token>& tokens,
                                 size_t begin,
                                 size_t end,
                                 const std::vector<ETokenType>& operators,
                                 size_t& pos);
std::string abi_binary_operator_code(ETokenType type);
AbiTokenType abi_encode_type_tokens(
	const std::vector<Token>& tokens,
	size_t begin,
	size_t end,
	const std::map<std::string, size_t>& template_parameters);
std::string abi_literal_expression(const Token& token);
std::string abi_template_value_expression(
	const std::vector<Token>& tokens,
	size_t begin,
	size_t end,
	const std::map<std::string, size_t>& template_parameters);
std::string abi_template_instance_argument(
	const pa11::TemplateInstanceArgument& arg,
	const std::map<std::string, size_t>& template_parameters,
	const std::vector<Token>* expression_tokens);
std::string abi_dependent_typename_type(
	TypePtr type,
	const std::map<std::string, size_t>& template_parameters,
	const std::vector<Token>* expression_tokens,
	bool include_namespace);
std::string abi_template_argument(
	const TemplateArgument& arg,
	const std::map<std::string, size_t>& template_parameters,
	const std::vector<Token>* expression_tokens);
bool abi_type_is_dependent_parameter(TypePtr type);
bool template_arguments_match_owner_record(
	TypePtr owner_record,
	const std::vector<TemplateArgument>& args);
std::string abi_template_argument_for_parameter(
	const TemplateArgument& arg,
	TypePtr parameter,
	const std::map<std::string, size_t>& template_parameters,
	const std::vector<Token>* expression_tokens);
std::string abi_function_return_type(
	TypePtr type,
	const std::map<std::string, size_t>& template_parameters,
	const std::vector<Token>* expression_tokens);
std::string abi_type_with_substitutions(TypePtr type,
                                        AbiSubstitutionContext& ctx);
std::string abi_type_probe_with_substitutions(TypePtr type,
                                              AbiSubstitutionContext& ctx);
std::string abi_record_type_with_substitutions(TypePtr type,
                                               AbiSubstitutionContext& ctx,
                                               bool include_namespace);
std::string abi_record_type_probe_with_substitutions(
	TypePtr type,
	AbiSubstitutionContext& ctx,
	bool include_namespace);
std::string abi_template_argument_with_substitutions(
	const TemplateArgument& arg,
	AbiSubstitutionContext& ctx);
std::string abi_template_instance_argument_with_substitutions(
	const pa11::TemplateInstanceArgument& arg,
	AbiSubstitutionContext& ctx);
std::string abi_function_return_type_with_substitutions(
	TypePtr type,
	AbiSubstitutionContext& ctx);
void abi_add_substitution(AbiSubstitutionContext& ctx,
                          const std::string& encoded);
std::string abi_template_argument_for_parameter_with_substitutions(
	const TemplateParameterInfo& parameter,
	const TemplateArgument& arg,
	AbiSubstitutionContext& ctx);
std::vector<Scope*> abi_scope_path_outer_first(Scope* scope);
bool abi_scope_is_std_namespace(Scope* scope);
std::string abi_scope_prefix_with_substitutions(
	const std::vector<Scope*>& scopes,
	AbiSubstitutionContext& ctx);
std::string abi_binding_symbol_with_substitutions(
	const Binding* binding,
	const std::map<std::string, size_t>& template_parameters);
std::string abi_function_template_specialization_symbol_with_substitutions(
	TemplateDeclaration* declaration,
	const std::vector<TemplateArgument>& full_args,
	Binding* binding,
	const std::vector<Token>* expression_tokens);

}  // namespace internal
}  // namespace pa12
