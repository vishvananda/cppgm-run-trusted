#pragma once

#include <map>
#include <set>
#include <vector>

#include "pa12_internal.h"

namespace pa12 {
namespace internal {

bool template_declaration_has_body(const std::vector<Token>& tokens,
                                   const TemplateDeclaration* declaration);
bool record_has_base_type(TypePtr source, TypePtr target);
bool same_template_specialization_family(TypePtr left, TypePtr right);
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

}  // namespace internal
}  // namespace pa12
