#include "pa12_internal.h"

#include <algorithm>
#include <stdexcept>

using namespace std;

namespace pa12 {
namespace internal {
namespace {

bool is_pointer(TypePtr type)
{
	return pa11::strip_cv(type)->kind == pa11::TypeKind::Pointer;
}

bool is_function_pointer(TypePtr type)
{
	TypePtr bare = pa11::strip_cv(type);
	return bare->kind == pa11::TypeKind::Pointer &&
	       bare->base->kind == pa11::TypeKind::Function;
}

bool is_function_reference(TypePtr type)
{
	return (type->kind == pa11::TypeKind::LValueReference ||
	        type->kind == pa11::TypeKind::RValueReference) &&
	       type->base->kind == pa11::TypeKind::Function;
}

}  // namespace

Conversion Parser::convert_to(const Expr& expr, TypePtr target)
{
	if (target->kind == pa11::TypeKind::LValueReference ||
	    target->kind == pa11::TypeKind::RValueReference)
		return convert_reference(expr, target);
	return convert_value(expr, target);
}

Conversion Parser::convert_reference(const Expr& expr, TypePtr target)
{
	Expr selected = select_overload_expr(expr, target);
	if (!type_can_bind_reference(target, selected))
	{
		if (target->kind != pa11::TypeKind::LValueReference ||
		    !pa11::type_has_const(target->base))
			return Conversion();
		Conversion conv = convert_value(selected, target->base);
		if (!conv.viable)
			return Conversion();
		Expr converted = conv.expr;
		converted.type = target->base;
		converted.category = ValueCategory::PRValue;
		converted.node = Node("cast-expression prvalue " +
		                      pa11::describe_type(target->base));
		add_child(converted.node, selected.node);
		annotate_expr_node(converted);
		return Conversion(true, conv.rank + 1, converted);
	}
	int rank = pa11::same_type(expression_object_type(selected.type), target->base)
		? 0 : 1;
	if (target->kind == pa11::TypeKind::RValueReference &&
	    selected.category != ValueCategory::LValue)
		rank = 0;
	else if (target->kind == pa11::TypeKind::LValueReference &&
	         selected.category != ValueCategory::LValue)
		rank = 1;
	return Conversion(true, rank, selected);
}

Conversion Parser::convert_value(const Expr& expr, TypePtr target)
{
	Expr selected = select_overload_expr(expr, target);
	TypePtr src = lvalue_to_rvalue_type(selected.type);
	TypePtr dst = pa11::strip_top_level_cv(target);
	if (pa11::same_type(src, dst))
		return Conversion(true, 0, selected);
	if (selected.null_pointer_constant && is_pointer(dst))
	{
		selected.type = dst;
		selected.node = Node("literal prvalue " + pa11::describe_type(dst) + " 0");
		selected.constant_expression = true;
		selected.has_constant_value = false;
		selected.node.token_text = "0";
		annotate_expr_node(selected);
		return Conversion(true, 2, selected);
	}
	if (selected.null_pointer_constant &&
	    pa11::strip_cv(dst)->kind == pa11::TypeKind::Fundamental &&
	    pa11::strip_cv(dst)->fundamental == FT_NULLPTR_T)
	{
		selected.type = dst;
		selected.node = Node("literal prvalue nullptr_t 0");
		selected.constant_expression = true;
		selected.has_constant_value = true;
		selected.constant_value = 0;
		selected.node.token_text = "0";
		annotate_expr_node(selected);
		return Conversion(true, 2, selected);
	}
	if (pa11::strip_cv(src)->kind == pa11::TypeKind::Fundamental &&
	    pa11::strip_cv(src)->fundamental == FT_NULLPTR_T && is_pointer(dst))
		return Conversion(true, 2, selected);
	int rank = scalar_conversion_rank(selected.type, dst);
	if (rank < 1000000)
		return Conversion(true, rank, selected);
	return Conversion();
}

Expr Parser::select_overload_expr(const Expr& expr, TypePtr target)
{
	if (expr.overloads.empty())
		return expr;
	TypePtr wanted = target;
	if (is_function_pointer(target))
		wanted = pa11::strip_cv(target)->base;
	else if (is_function_reference(target))
		wanted = target->base;
	else
		throw runtime_error("overloaded function id needs target");

	Binding* found = NULL;
	for (size_t i = 0; i < expr.overloads.size(); ++i)
	{
		Binding* candidate = expr.overloads[i];
		if (pa11::same_type(candidate->type, wanted))
		{
			if (found != NULL)
				throw runtime_error("ambiguous overloaded function id");
			found = candidate;
		}
	}
	if (found == NULL)
		throw runtime_error("no overloaded function id target");

	Expr out = expr;
	out.overloads.clear();
	out.binding = found;
	out.type = found->type;
	out.category = ValueCategory::LValue;
	out.node = Node("id-expression lvalue " + pa11::describe_type(out.type) +
	                " " + found->name);
	annotate_expr_node(out);
	return out;
}

Binding* Parser::resolve_call_candidate(const vector<Binding*>& overloads,
                                        const vector<Expr>& args,
                                        vector<Expr>& converted)
{
	Binding* best = NULL;
	vector<int> best_ranks;
	vector<Expr> best_args;
	bool ambiguous = false;
	for (size_t i = 0; i < overloads.size(); ++i)
	{
		Binding* fn = overloads[i];
		if (fn->type->kind != pa11::TypeKind::Function)
			continue;
		bool duplicate = false;
		for (size_t j = 0; j < i; ++j)
		{
			if (overloads[j]->type->kind == pa11::TypeKind::Function &&
			    pa11::same_type(overloads[j]->type, fn->type))
				duplicate = true;
		}
		if (duplicate)
			continue;
		if (args.size() < fn->type->parameters.size())
		{
			map<Binding*, vector<Expr> >::const_iterator dit =
				default_arguments_.find(fn);
			if (dit == default_arguments_.end())
				continue;
			bool have_defaults = true;
			for (size_t j = args.size(); j < fn->type->parameters.size(); ++j)
			{
				if (j >= dit->second.size() || !dit->second[j].valid)
				{
					have_defaults = false;
					break;
				}
			}
			if (!have_defaults)
				continue;
		}
		if (!fn->type->variadic && args.size() != fn->type->parameters.size())
		{
			if (args.size() > fn->type->parameters.size())
				continue;
		}
		vector<int> ranks;
		vector<Expr> conv_args = args;
		if (conv_args.size() < fn->type->parameters.size())
		{
			const vector<Expr>& defaults = default_arguments_[fn];
			for (size_t j = conv_args.size(); j < fn->type->parameters.size(); ++j)
				conv_args.push_back(defaults[j]);
		}
		bool ok = true;
		for (size_t j = 0; j < fn->type->parameters.size(); ++j)
		{
			Conversion conv = convert_to(conv_args[j], fn->type->parameters[j]);
			if (!conv.viable)
			{
				ok = false;
				break;
			}
			ranks.push_back(conv.rank);
			conv_args[j] = conv.expr;
		}
		if (!ok)
			continue;
		if (best == NULL || ranks_better(ranks, best_ranks))
		{
			best = fn;
			best_ranks = ranks;
			best_args = conv_args;
			ambiguous = false;
		}
		else if (!ranks_better(best_ranks, ranks))
			ambiguous = true;
	}
	if (best == NULL || ambiguous)
		throw runtime_error("cannot resolve call overload");
	converted = best_args;
	return best;
}

Expr Parser::make_call_expr(Expr callee, vector<Expr> args)
{
	if (callee.builtin_constant_p)
	{
		if (args.size() != 1)
			throw runtime_error("wrong argument count");
		Expr out;
		out.type = pa11::make_fundamental(FT_INT);
		out.category = ValueCategory::PRValue;
		out.valid = true;
		const bool constant = args[0].constant_expression;
		out.node = Node(string("literal prvalue int ") + (constant ? "1" : "0"));
		out.constant_expression = true;
		out.has_constant_value = true;
		out.constant_value = constant ? 1 : 0;
		out.null_pointer_constant = constant ? false : true;
		out.node.token_text = constant ? "1" : "0";
		annotate_expr_node(out);
		return out;
	}
	vector<Expr> converted;
	Binding* direct = NULL;
	if (!callee.overloads.empty())
		direct = resolve_call_candidate(callee.overloads, args, converted);
	Expr out;
	if (direct != NULL)
	{
		if (deleted_functions_.find(direct) != deleted_functions_.end())
			throw runtime_error("call to deleted function");
		out.type = direct->type->base;
		out.category = call_category(out.type);
		out.node = Node("call-expression " + value_category_name(out.category) +
		                " " + pa11::describe_type(out.type));
		out.node.direct_call = direct;
		add_child(out.node, Node("callee " + qualified_decl_name(direct) +
		                         " " + pa11::describe_type(direct->type)));
	}
	else
	{
		TypePtr callee_type = expression_object_type(callee.type);
		if (callee_type->kind == pa11::TypeKind::Pointer)
			callee_type = callee_type->base;
		if (callee_type->kind != pa11::TypeKind::Function)
			throw runtime_error("called object is not callable");
		if (args.size() != callee_type->parameters.size() && !callee_type->variadic)
			throw runtime_error("wrong argument count");
		converted = args;
		for (size_t i = 0; i < callee_type->parameters.size(); ++i)
		{
			Conversion conv = convert_to(args[i], callee_type->parameters[i]);
			if (!conv.viable)
				throw runtime_error("invalid argument conversion");
			converted[i] = conv.expr;
		}
		out.type = callee_type->base;
		out.category = call_category(out.type);
		out.node = Node("call-expression " + value_category_name(out.category) +
		                " " + pa11::describe_type(out.type));
		add_child(out.node, callee.node);
	}
	for (size_t i = 0; i < converted.size(); ++i)
		add_child(out.node, converted[i].node);
	out.valid = true;
	annotate_expr_node(out);
	return out;
}

bool Parser::ranks_better(const vector<int>& lhs, const vector<int>& rhs) const
{
	if (rhs.empty())
		return true;
	bool any = false;
	for (size_t i = 0; i < lhs.size(); ++i)
	{
		if (lhs[i] > rhs[i])
			return false;
		if (lhs[i] < rhs[i])
			any = true;
	}
	return any;
}

}  // namespace internal
}  // namespace pa12
