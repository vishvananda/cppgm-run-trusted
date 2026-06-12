#pragma once

#include <string>
#include <vector>

#include "pa12_internal.h"

namespace pa12 {
namespace internal {

bool is_float_literal_text(const std::string& source);
TypePtr floating_literal_type(const std::string& source);
bool type_is_pointer(TypePtr type);
bool type_contains_template_parameter_name(TypePtr type, std::string& name);
bool template_argument_contains_template_parameter_name(
	const TemplateArgument& argument,
	std::string& name);
void collect_template_parameter_names_from_argument(
	const TemplateArgument& argument,
	std::vector<std::string>& names);
pa11::TemplateInstanceArgument expr_template_instance_argument(
	const TemplateArgument& argument);
size_t ordinary_string_elements(const std::string& source, size_t fallback);
Expr make_static_member_pack_element(Binding* binding);
Expr make_bool_trait_expr(bool value);
bool node_is_noexcept(const Node& node);
TypePtr trait_object_type(TypePtr type);
bool trait_is_scalar(TypePtr type);
bool trait_record_is_empty(TypePtr record);
bool trait_record_has_virtual_destructor(TypePtr record);
bool trait_record_is_abstract(TypePtr record);
bool trait_record_has_nonpublic_field(TypePtr record);
bool trait_record_derives_from(TypePtr source, TypePtr target);
bool trait_record_has_user_copy_constructor(TypePtr record);
bool trait_record_has_user_assignment(TypePtr record);

}  // namespace internal
}  // namespace pa12
