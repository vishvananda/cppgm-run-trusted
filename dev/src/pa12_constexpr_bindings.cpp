#include "pa12_internal.h"
#include <iomanip>
#include <sstream>

using namespace std;
namespace pa12 {
namespace internal {
namespace {
string format_float(long double value)
{
	ostringstream out;
	out << setprecision(36) << value;
	return out.str();
}
}
bool Parser::try_evaluate_dependent_value_node(const Node& node,
                                               ConstexprValue& out)
{
	if (node.dependent_value_name.empty())
		return false;
	TemplateArgument arg =
		TemplateArgument::dependent_value_arg(expression_object_type(node.type));
	arg.value_name = node.dependent_value_name;
	arg.value_owner_template_name =
		node.dependent_value_owner_template_name;
	arg.value_member_name = node.dependent_value_member_name;
	arg.value_negated = node.dependent_value_negated;
	arg.value_owner_template_arguments =
		node.dependent_value_owner_template_arguments;
	TemplateArgument resolved;
	if (!resolve_dependent_value_member_argument(arg, resolved))
		return false;
	resolved = substitute_template_argument(resolved);
	if (resolved.kind != TemplateArgumentKind::Value ||
	    resolved.dependent ||
	    resolved.value_binding != NULL)
		return false;
	out = ConstexprValue::integer(resolved.value);
	return true;
}
void Parser::apply_constexpr_value(Expr& expr, const ConstexprValue& value)
{
	if (!value.valid || value.is_object || value.is_pointer)
		return;
	expr.constant_expression = true;
	expr.has_constant_value = true;
	expr.constant_value = value.int_value;
	expr.null_pointer_constant = value.int_value == 0 && !value.is_float;
	expr.node.has_constant_value = true;
	expr.node.constant_value = value.int_value;
	expr.node.token_text = value.is_float
		? format_float(value.float_value)
		: to_string(value.int_value);
}
}  // namespace internal
}  // namespace pa12
