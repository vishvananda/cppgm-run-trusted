#include "pa12_expr_semantics_support.h"

#include <cstdint>
#include <stdexcept>

using namespace std;

namespace pa12 {
namespace internal {

Expr Parser::make_builtin_va_arg_expr(Expr list, TypePtr result)
{
	Conversion conv = convert_to(
		list,
		pa11::make_pointer(pa11::make_fundamental(FT_VOID)));
	if (!conv.viable)
		throw runtime_error("invalid __builtin_va_arg list");
	Expr out;
	out.valid = true;
	out.type = result;
	out.category = call_category(result);
	out.node = Node("builtin-va-arg-expression " +
	                value_category_name(out.category) + " " +
	                pa11::describe_type(result));
	add_child(out.node, conv.expr.node);
	annotate_expr_node(out);
	return out;
}

Expr Parser::make_builtin_offsetof_expr(TypePtr record,
                                        const vector<string>& members)
{
	TypePtr cur = pa11::strip_cv(record);
	if (type_is_template_dependent(cur))
	{
		Expr out;
		out.valid = true;
		out.type = pa11::make_fundamental(FT_UNSIGNED_LONG_INT);
		out.category = ValueCategory::PRValue;
		out.constant_expression = true;
		out.dependent_value_name =
			"__builtin_offsetof(" + pa11::describe_type(record) + ")";
		out.node = Node("offsetof-expression prvalue unsigned long int");
		out.node.token_text = out.dependent_value_name;
		annotate_expr_node(out);
		return out;
	}
	uint64_t offset = 0;
	for (size_t i = 0; i < members.size(); ++i)
	{
		cur = pa11::strip_cv(cur);
		if (cur->kind != pa11::TypeKind::Record || cur->scope == NULL)
			throw runtime_error("__builtin_offsetof on non-record");
		complete_template_record(cur);
		pa11::layout_record_type(cur);
		vector<Binding*> found =
			lookup_qualified_set(cur->scope,
			                     members[i],
			                     pa11::LOOKUP_VARIABLE);
		if (found.empty())
			throw runtime_error("__builtin_offsetof member not found");
		Binding* field = found[0];
		if (field->is_bit_field)
			throw runtime_error("__builtin_offsetof on bit-field unsupported");
		offset += field->member_offset;
		cur = field->type;
	}
	return make_sizeof_expr(offset);
}

}  // namespace internal
}  // namespace pa12
