#pragma once

#include "pa12_internal.h"

namespace pa12 {
namespace internal {

enum class EvalFlow
{
	Normal,
	Return,
	Break,
	Continue,
	Invalid
};

struct EvalState
{
	map<Binding*, ConstexprValue> locals;
	EvalState();
};

bool constexpr_eval_node(Parser& parser,
                         const Node& node,
                         EvalState& state,
                         ConstexprValue& out);
bool constexpr_eval_variable_initializer(Parser& parser,
                                         const Node& node,
                                         EvalState& state,
                                         ConstexprValue& out);
bool eval_postfix_node(Parser& parser,
                       const Node& node,
                       EvalState& state,
                       ConstexprValue& out);
bool eval_condition_declaration(Parser& parser,
                                const Node& node,
                                EvalState& state,
                                ConstexprValue& out);
EvalFlow eval_statement(Parser& parser,
                        const Node& node,
                        EvalState& state,
                        ConstexprValue& out);

}  // namespace internal
}  // namespace pa12
