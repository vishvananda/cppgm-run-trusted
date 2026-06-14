#include "pa12_constexpr_eval.h"

using namespace std;

namespace pa12 {
namespace internal {
namespace {

bool starts_with(const string& text, const string& prefix)
{
	return text.compare(0, prefix.size(), prefix) == 0;
}

bool truthy(const ConstexprValue& value)
{
	if (value.is_pointer)
		return value.pointer_binding != NULL || value.pointer_index != 0;
	return value.is_float ? value.float_value != 0 : value.int_value != 0;
}

uint64_t integer_value(const ConstexprValue& value)
{
	if (value.is_pointer)
		return static_cast<uint64_t>(value.pointer_index);
	return value.is_float
		? static_cast<uint64_t>(value.float_value) : value.int_value;
}

bool adjust_value(ConstexprValue& value, long long delta)
{
	if (value.is_pointer)
	{
		value.pointer_index += delta;
		return true;
	}
	if (value.is_float)
		value = ConstexprValue::floating(value.float_value + delta);
	else
		value = ConstexprValue::integer(value.int_value + delta);
	return true;
}

EvalFlow eval_compound(Parser& parser,
                       const Node& node,
                       EvalState& state,
                       ConstexprValue& out)
{
	for (size_t i = 0; i < node.children.size(); ++i)
	{
		EvalFlow flow = eval_statement(parser, node.children[i], state, out);
		if (flow != EvalFlow::Normal)
			return flow;
	}
	return EvalFlow::Normal;
}

EvalFlow eval_branch_child(Parser& parser,
                           const Node& wrapper,
                           EvalState& state,
                           ConstexprValue& out)
{
	if (wrapper.children.empty())
		return EvalFlow::Normal;
	return eval_statement(parser, wrapper.children[0], state, out);
}

EvalFlow eval_loop_flow(EvalFlow flow)
{
	if (flow == EvalFlow::Return ||
	    flow == EvalFlow::Invalid)
		return flow;
	if (flow == EvalFlow::Break)
		return EvalFlow::Normal;
	return EvalFlow::Continue;
}

bool store_object_fields(EvalState& state, const ConstexprValue& value)
{
	for (map<Binding*, ConstexprValue>::iterator it = state.locals.begin();
	     it != state.locals.end();
	     ++it)
	{
		if (it->first == NULL || it->first->name != "this" ||
		    !it->second.is_object)
			continue;
		for (map<Binding*, ConstexprValue>::const_iterator fit =
			     value.fields.begin();
		     fit != value.fields.end();
		     ++fit)
			it->second.fields[fit->first] = fit->second;
		return true;
	}
	return false;
}

bool store_this_object(EvalState& state, const ConstexprValue& value)
{
	for (map<Binding*, ConstexprValue>::iterator it = state.locals.begin();
	     it != state.locals.end();
	     ++it)
		if (it->first != NULL && it->first->name == "this")
		{
			it->second = value;
			return true;
		}
	return false;
}

bool store_member_field(EvalState& state,
                        Binding* member,
                        const ConstexprValue& value)
{
	for (map<Binding*, ConstexprValue>::iterator it = state.locals.begin();
	     it != state.locals.end();
	     ++it)
	{
		if (it->first == NULL || it->first->name != "this" ||
		    !it->second.is_object)
			continue;
		it->second.fields[member] = value;
		return true;
	}
	return false;
}

EvalFlow eval_for_statement(Parser& parser,
                            const Node& node,
                            EvalState& state,
                            ConstexprValue& out)
{
	if (node.children.empty())
		return EvalFlow::Normal;
	size_t index = 0;
	if (starts_with(node.children[index].line, "for-init-statement"))
	{
		EvalFlow init_flow =
			eval_statement(parser, node.children[index], state, out);
		if (init_flow != EvalFlow::Normal)
			return init_flow;
		++index;
	}
	const Node* cond = NULL;
	const Node* iter = NULL;
	const Node* body = NULL;
	for (; index < node.children.size(); ++index)
	{
		if (starts_with(node.children[index].line, "condition"))
			cond = &node.children[index];
		else if (starts_with(node.children[index].line, "iteration"))
			iter = &node.children[index];
		else
			body = &node.children[index];
	}
	while (body != NULL)
	{
		if (cond != NULL)
		{
			ConstexprValue c;
			if (!constexpr_eval_node(parser, *cond, state, c))
				return EvalFlow::Invalid;
			if (!truthy(c))
				return EvalFlow::Normal;
		}
		EvalFlow flow = eval_statement(parser, *body, state, out);
		EvalFlow loop_flow = eval_loop_flow(flow);
		if (loop_flow != EvalFlow::Continue)
			return loop_flow;
		if (iter != NULL && !iter->children.empty() &&
		    !constexpr_eval_node(parser, iter->children[0], state, out))
			return EvalFlow::Invalid;
	}
	return EvalFlow::Normal;
}

}  // namespace

bool eval_postfix_node(Parser& parser,
                       const Node& node,
                       EvalState& state,
                       ConstexprValue& out)
{
	if (node.children.empty())
		return false;
	if (!constexpr_eval_node(parser, node.children[0], state, out))
		return false;
	if (node.op == OP_INC)
		adjust_value(out, 1);
	else if (node.op == OP_DEC)
		adjust_value(out, -1);
	else
		return false;
	return true;
}

	bool eval_condition_declaration(Parser& parser,
	                                const Node& node,
	                                EvalState& state,
	                                ConstexprValue& out)
{
	bool have_value = false;
	for (size_t i = 0; i < node.children.size(); ++i)
	{
		const Node& child = node.children[i];
		if (starts_with(child.line, "variable ") &&
		    child.binding != NULL)
		{
			ConstexprValue value;
			if (!constexpr_eval_variable_initializer(parser,
			                                         child,
			                                         state,
			                                         value))
				return false;
			state.locals[child.binding] = value;
			out = value;
			have_value = true;
		}
		else
		{
			if (!constexpr_eval_node(parser, child, state, out))
				return false;
			have_value = true;
		}
	}
		return have_value;
	}

	EvalFlow eval_for_init_statement(Parser& parser,
	                                 const Node& node,
	                                 EvalState& state,
	                                 ConstexprValue& out)
	{
		for (size_t i = 0; i < node.children.size(); ++i)
		{
			const Node& child = node.children[i];
			if (starts_with(child.line, "simple-declaration"))
			{
				EvalFlow flow = eval_statement(parser, child, state, out);
				if (flow != EvalFlow::Normal)
					return flow;
			}
			else if (!constexpr_eval_node(parser, child, state, out))
				return EvalFlow::Invalid;
		}
		return EvalFlow::Normal;
	}

	EvalFlow eval_simple_declaration_statement(Parser& parser,
	                                           const Node& node,
	                                           EvalState& state,
	                                           ConstexprValue& out)
	{
		for (size_t i = 0; i < node.children.size(); ++i)
		{
			const Node& var = node.children[i];
			if (!starts_with(var.line, "variable ") || var.binding == NULL)
				continue;
			ConstexprValue value;
			if (!constexpr_eval_variable_initializer(parser, var, state, value))
				return EvalFlow::Invalid;
			state.locals[var.binding] = value;
		}
		return EvalFlow::Normal;
	}

	EvalFlow eval_storage_copy_statement(Parser& parser,
	                                     const Node& node,
	                                     EvalState& state,
	                                     ConstexprValue& out)
	{
		if (node.children.empty())
			return EvalFlow::Invalid;
		ConstexprValue source;
		if (!constexpr_eval_node(parser, node.children[0], state, source) ||
		    !source.is_object)
			return EvalFlow::Invalid;
		return store_object_fields(state, source)
			? EvalFlow::Normal : EvalFlow::Invalid;
	}

	EvalFlow eval_base_init_statement(Parser& parser,
	                                  const Node& node,
	                                  EvalState& state,
	                                  ConstexprValue& out)
	{
		ConstexprValue value;
		if (!node.children.empty())
		{
			if (!constexpr_eval_node(parser, node.children[0], state, value))
				return EvalFlow::Invalid;
		}
		else if (node.direct_call != NULL)
		{
			vector<ConstexprValue> args;
			if (!parser.try_evaluate_constexpr_constructor(node.direct_call,
			                                               node.type,
			                                               args,
			                                               value))
				return EvalFlow::Invalid;
		}
		else if (!constexpr_zero_value_for_type(node.type, value))
			return EvalFlow::Invalid;
		return store_object_fields(state, value)
			? EvalFlow::Normal : EvalFlow::Invalid;
	}

	EvalFlow eval_delegating_init_statement(Parser& parser,
	                                        const Node& node,
	                                        EvalState& state,
	                                        ConstexprValue& out)
	{
		if (node.children.empty())
			return EvalFlow::Invalid;
		ConstexprValue value;
		if (!constexpr_eval_node(parser, node.children[0], state, value) ||
		    !value.is_object)
			return EvalFlow::Invalid;
		return store_this_object(state, value)
			? EvalFlow::Normal : EvalFlow::Invalid;
	}

	EvalFlow eval_member_init_statement(Parser& parser,
	                                    const Node& node,
	                                    EvalState& state,
	                                    ConstexprValue& out)
	{
		ConstexprValue value;
		if (!node.children.empty() &&
		    !constexpr_eval_node(parser, node.children[0], state, value))
			return EvalFlow::Invalid;
		else if (node.children.empty() && node.direct_call != NULL)
		{
			vector<ConstexprValue> args;
			if (!parser.try_evaluate_constexpr_constructor(node.direct_call,
			                                               node.binding->type,
			                                               args,
			                                               value))
				return EvalFlow::Invalid;
		}
		else if (node.children.empty() &&
		         !constexpr_zero_value_for_type(node.binding->type, value))
			return EvalFlow::Invalid;
		return store_member_field(state, node.binding, value)
			? EvalFlow::Normal : EvalFlow::Invalid;
	}

	EvalFlow eval_expression_statement(Parser& parser,
	                                   const Node& node,
	                                   EvalState& state,
	                                   ConstexprValue& out)
	{
		if (!node.children.empty() &&
		    !constexpr_eval_node(parser, node.children[0], state, out))
			return EvalFlow::Invalid;
		return EvalFlow::Normal;
	}

	EvalFlow eval_return_statement(Parser& parser,
	                               const Node& node,
	                               EvalState& state,
	                               ConstexprValue& out)
	{
		if (node.children.empty())
			out = ConstexprValue::integer(0);
		else if (!constexpr_eval_node(parser, node.children[0], state, out))
			return EvalFlow::Invalid;
		return EvalFlow::Return;
	}

	EvalFlow eval_if_statement(Parser& parser,
	                           const Node& node,
	                           EvalState& state,
	                           ConstexprValue& out)
	{
		if (node.children.size() < 2)
			return EvalFlow::Normal;
		ConstexprValue cond;
		if (!constexpr_eval_node(parser, node.children[0], state, cond))
			return EvalFlow::Invalid;
		if (truthy(cond))
			return eval_branch_child(parser, node.children[1], state, out);
		if (node.children.size() > 2)
			return eval_branch_child(parser, node.children[2], state, out);
		return EvalFlow::Normal;
	}

	EvalFlow eval_while_statement(Parser& parser,
	                              const Node& node,
	                              EvalState& state,
	                              ConstexprValue& out)
	{
		if (node.children.size() < 2)
			return EvalFlow::Normal;
		for (;;)
		{
			ConstexprValue cond;
			if (!constexpr_eval_node(parser, node.children[0], state, cond))
				return EvalFlow::Invalid;
			if (!truthy(cond))
				return EvalFlow::Normal;
			EvalFlow flow =
				eval_statement(parser, node.children[1], state, out);
			EvalFlow loop_flow = eval_loop_flow(flow);
			if (loop_flow != EvalFlow::Continue)
				return loop_flow;
		}
	}

	EvalFlow eval_do_statement(Parser& parser,
	                           const Node& node,
	                           EvalState& state,
	                           ConstexprValue& out)
	{
		if (node.children.size() < 2)
			return EvalFlow::Normal;
		for (;;)
		{
			EvalFlow flow =
				eval_statement(parser, node.children[0], state, out);
			EvalFlow loop_flow = eval_loop_flow(flow);
			if (loop_flow != EvalFlow::Continue)
				return loop_flow;
			ConstexprValue cond;
			if (!constexpr_eval_node(parser, node.children[1], state, cond))
				return EvalFlow::Invalid;
			if (!truthy(cond))
				return EvalFlow::Normal;
		}
	}

	EvalFlow eval_statement(Parser& parser,
	                        const Node& node,
	                        EvalState& state,
	                        ConstexprValue& out)
	{
		if (starts_with(node.line, "compound-statement"))
			return eval_compound(parser, node, state, out);
		if (starts_with(node.line, "for-init-statement"))
			return eval_for_init_statement(parser, node, state, out);
		if (starts_with(node.line, "simple-declaration"))
			return eval_simple_declaration_statement(parser, node, state, out);
		if (starts_with(node.line, "storage-copy-action"))
			return eval_storage_copy_statement(parser, node, state, out);
		if (starts_with(node.line, "base-init-action"))
			return eval_base_init_statement(parser, node, state, out);
		if (starts_with(node.line, "delegating-init-action"))
			return eval_delegating_init_statement(parser, node, state, out);
		if (starts_with(node.line, "member-init-action") && node.binding != NULL)
			return eval_member_init_statement(parser, node, state, out);
		if (starts_with(node.line, "expression-statement"))
			return eval_expression_statement(parser, node, state, out);
		if (starts_with(node.line, "return-statement"))
			return eval_return_statement(parser, node, state, out);
		if (starts_with(node.line, "if-statement"))
			return eval_if_statement(parser, node, state, out);
		if (starts_with(node.line, "while-statement"))
			return eval_while_statement(parser, node, state, out);
		if (starts_with(node.line, "do-statement"))
			return eval_do_statement(parser, node, state, out);
		if (starts_with(node.line, "for-statement"))
			return eval_for_statement(parser, node, state, out);
		if (starts_with(node.line, "break-statement"))
		return EvalFlow::Break;
	if (starts_with(node.line, "continue-statement"))
		return EvalFlow::Continue;
	return EvalFlow::Invalid;
}

}  // namespace internal
}  // namespace pa12
