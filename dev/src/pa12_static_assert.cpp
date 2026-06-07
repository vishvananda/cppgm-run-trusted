#include "pa12_internal.h"

#include <stdexcept>

using namespace std;

namespace pa12 {
namespace internal {
namespace {

bool constexpr_value_truth(const ConstexprValue& value, uint64_t& out)
{
	if (value.is_object)
		return false;
	if (value.is_pointer)
		out = value.pointer_binding != NULL || value.pointer_index != 0 ? 1 : 0;
	else if (value.is_float)
		out = value.float_value != 0 ? 1 : 0;
	else
		out = value.int_value;
	return true;
}

}  // namespace

void Parser::parse_static_assert_declaration()
{
	expect(KW_STATIC_ASSERT);
	expect(OP_LPAREN);
	bool dependent_context = false;
	for (size_t i = 0; i < template_type_substitutions_.size(); ++i)
		for (map<string, TypePtr>::const_iterator it =
			     template_type_substitutions_[i].begin();
		     it != template_type_substitutions_[i].end();
		     ++it)
			if (type_is_template_dependent(it->second))
				dependent_context = true;
	for (size_t i = 0; i < template_value_substitutions_.size(); ++i)
		for (map<string, TemplateArgument>::const_iterator it =
			     template_value_substitutions_[i].begin();
		     it != template_value_substitutions_[i].end();
		     ++it)
			if (it->second.dependent ||
			    type_is_template_dependent(it->second.type))
				dependent_context = true;
	size_t condition_begin = pos_;
	Expr condition;
	try
	{
		condition = parse_assignment_expression();
	}
	catch (const exception&)
	{
		if (!dependent_context)
			throw;
		pos_ = condition_begin;
		int paren = 0;
		while (!at_eof())
		{
			if (paren == 0 && at(OP_RPAREN))
				break;
			if (at(OP_LPAREN))
				++paren;
			else if (at(OP_RPAREN))
				--paren;
			++pos_;
		}
		expect(OP_RPAREN);
		expect(OP_SEMICOLON);
		return;
	}
	string message;
	if (consume(OP_COMMA))
	{
		if (!at_literal())
			throw runtime_error("expected static_assert message");
		message = current().source;
		++pos_;
	}
	expect(OP_RPAREN);
	expect(OP_SEMICOLON);
	if (!condition.dependent_value_name.empty())
	{
		TemplateArgument arg =
			TemplateArgument::dependent_value_arg(condition.type);
		arg.value_name = condition.dependent_value_name;
		arg.value_owner_template_name =
			condition.dependent_value_owner_template_name;
		arg.value_member_name = condition.dependent_value_member_name;
		arg.value_negated = condition.dependent_value_negated;
		arg.value_owner_template_arguments =
			condition.dependent_value_owner_template_arguments;
		TemplateArgument resolved = substitute_template_argument(arg);
		if (resolved.kind == TemplateArgumentKind::Value &&
		    !resolved.dependent)
		{
			condition.has_constant_value = true;
			condition.constant_value = resolved.value;
		}
	}
	try
	{
		Conversion conv = convert_to(condition, pa11::make_fundamental(FT_BOOL));
		if (conv.viable)
			condition = conv.expr;
	}
	catch (const runtime_error&)
	{
		if (dependent_context)
			return;
		throw;
	}
	ConstexprValue value;
	if (try_evaluate_constexpr_expr(condition.node, value) && value.valid)
	{
		uint64_t truth = 0;
		if (constexpr_value_truth(value, truth))
		{
			condition.has_constant_value = true;
			condition.constant_value = truth;
		}
	}
	if (!condition.has_constant_value)
	{
		if (dependent_context)
			return;
		throw runtime_error("static_assert condition is not constant");
	}
	if (condition.constant_value == 0)
	{
		if (dependent_context)
			return;
		throw runtime_error("static_assert failed " + message);
	}
}

}  // namespace internal
}  // namespace pa12
