#pragma once

#include <map>
#include <stdexcept>
#include <set>
#include <string>
#include <vector>

#include "pa12_internal.h"

namespace pa12 {
namespace internal {

bool template_declaration_has_body(const std::vector<Token>& tokens,
                                   const TemplateDeclaration* declaration);
bool record_has_base_type(TypePtr source, TypePtr target);
bool same_template_specialization_record(TypePtr left, TypePtr right);
bool same_template_specialization_family(TypePtr left, TypePtr right);
bool call_object_specialization_type_equivalent(TypePtr left, TypePtr right);
bool hosted_library_namespace_scope(Scope* scope);
bool no_matching_constructor_error(const std::runtime_error& err);
std::vector<Expr> default_arguments_for_binding(
	Binding* binding,
	const std::vector<Expr>& defaults);
bool exact_copy_reference_constructor_for_order_args(
	Binding* ctor,
	const std::vector<Expr>& template_order_args);
bool ranks_equal_allowing_copy_reference_rank(
	const std::vector<int>& copy_ranks,
	const std::vector<int>& other_ranks);
bool constructor_binding_for_record(TypePtr record, Binding* ctor);
std::string hosted_unqualified_primary(TypePtr type);
bool inherited_constructor_template_candidate(
	const std::map<Binding*, TemplateDeclaration*>& placeholders,
	Binding* binding);
bool record_has_conversion_function_candidate(TypePtr record,
                                              std::set<Scope*>& seen);
bool same_template_signature_type(
	TypePtr left,
	TypePtr right,
	std::map<std::string, std::string>& type_parameter_names);
bool same_template_signature_type(TypePtr left, TypePtr right);
Binding* duplicate_function_candidate(const std::vector<Binding*>& considered,
                                      Binding* candidate);
TemplateDeclaration* function_template_origin(
	const std::map<Binding*, TemplateDeclaration*>& origins,
	Binding* binding);
bool expr_template_parameter_lists_match(
	const std::vector<TemplateParameterInfo>& left,
	const std::vector<TemplateParameterInfo>& right);
bool function_template_more_specialized(
	const std::map<Binding*, TemplateDeclaration*>& origins,
	Binding* lhs,
	Binding* rhs);
bool function_template_declaration_more_specialized(TemplateDeclaration* lhs,
                                                    TemplateDeclaration* rhs);
bool same_function_template_declaration_family(TemplateDeclaration* left,
                                               TemplateDeclaration* right);
bool function_template_more_specialized_for_call(
	const std::map<Binding*, TemplateDeclaration*>& origins,
	Binding* lhs,
	Binding* rhs,
	size_t parameter_count);
bool function_template_fewer_forwarding_lvalue_parameters_for_call(
	const std::map<Binding*, TemplateDeclaration*>& origins,
	Binding* lhs,
	Binding* rhs,
	const std::vector<Expr>& args);
Binding* canonical_function_binding(Binding* binding);
void collect_conversion_functions(TypePtr record,
                                  std::set<Scope*>& seen,
                                  std::vector<Binding*>& out);
Expr make_builtin_constant_call(const std::vector<Expr>& args);
void filter_static_class_member_overloads(Expr& callee);
bool dependent_pointer_member_helper_candidate(Binding* fn,
                                               const std::vector<Expr>& args);
bool hosted_esft_argument_has_base(const std::vector<Expr>& args);
void model_dependent_pointer_member_helper_candidate(
	Binding* fn,
	const std::vector<Expr>& args);
bool hosted_std_function_template_declaration(
	const TemplateDeclaration* declaration,
	const std::string& name);
bool hosted_std_basic_string_operator_template_declaration(
	const TemplateDeclaration* declaration);
bool hosted_basic_string_type(TypePtr type);
bool hosted_basic_string_pattern(TypePtr type);
TypePtr substitute_hosted_basic_string_operator_type(TypePtr pattern,
                                                     TypePtr string_type,
                                                     TypePtr char_type);
bool hosted_std_function_type(TypePtr type);
bool hosted_std_function_member_template_declaration(
	const TemplateDeclaration* declaration,
	const std::string& name);
bool hosted_forwarding_template_parameter(TypePtr type);
TypePtr modeled_hosted_function_assignment_type(
	Binding* fn,
	const std::vector<Expr>& args,
	std::vector<TemplateArgument>& out);
TypePtr modeled_hosted_vector_insert_type(
	Binding* fn,
	const std::vector<Expr>& args,
	std::vector<TemplateArgument>& out);
TypePtr modeled_hosted_dependent_pointer_member_type(
	Binding* fn,
	const TemplateDeclaration* declaration,
	const std::vector<Expr>& args,
	std::vector<TemplateArgument>& out);
bool recover_hosted_call_template_arguments(
	const TemplateDeclaration* declaration,
	const std::vector<Expr>& args,
	std::vector<TemplateArgument>& deduced);

}  // namespace internal
}  // namespace pa12
