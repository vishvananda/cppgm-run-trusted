#include "pa12_internal.h"

#include <algorithm>
#include <set>
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
	       pa11::strip_cv(type->base)->kind == pa11::TypeKind::Function;
}

bool is_member_function_pointer(TypePtr type)
{
	TypePtr bare = pa11::strip_cv(type);
	return bare->kind == pa11::TypeKind::MemberPointer &&
	       bare->base.get() != NULL &&
	       bare->base->kind == pa11::TypeKind::Function;
}

TypePtr member_function_pointer_type(Binding* binding)
{
	if (binding == NULL ||
	    binding->owner == NULL ||
	    binding->owner->kind != ScopeKind::Class ||
	    binding->type.get() == NULL ||
	    binding->type->kind != pa11::TypeKind::Function ||
	    binding->type->parameters.empty())
		return TypePtr();
	TypePtr this_type = binding->type->parameters[0];
	TypePtr class_type = this_type.get() == NULL ? TypePtr() :
		pa11::strip_cv(pa11::strip_cv(this_type)->base);
	vector<TypePtr> params;
	for (size_t i = 1; i < binding->type->parameters.size(); ++i)
		params.push_back(binding->type->parameters[i]);
	TypePtr member_fn =
		pa11::make_function(binding->type->base,
		                    params,
		                    binding->type->variadic);
	if (this_type.get() != NULL &&
	    pa11::strip_cv(this_type)->kind == pa11::TypeKind::Pointer)
		member_fn->cv = pa11::strip_cv(this_type)->base->kind ==
			pa11::TypeKind::Cv ? this_type->base->cv : pa11::CV_NONE;
	return pa11::make_member_pointer(class_type, member_fn);
}

Binding* duplicate_function_candidate(const vector<Binding*>& considered,
                                      Binding* candidate)
{
	for (size_t i = 0; i < considered.size(); ++i)
		if (pa11::same_type(considered[i]->type, candidate->type) &&
		    considered[i]->is_static_member == candidate->is_static_member)
			return considered[i];
	return NULL;
}

TemplateDeclaration* function_template_origin(
	const map<Binding*, TemplateDeclaration*>& origins,
	Binding* binding)
{
	map<Binding*, TemplateDeclaration*>::const_iterator found =
		origins.find(binding);
	return found != origins.end() ? found->second : NULL;
}

bool function_template_more_specialized(
	const map<Binding*, TemplateDeclaration*>& origins,
	Binding* lhs,
	Binding* rhs)
{
	TemplateDeclaration* left = function_template_origin(origins, lhs);
	TemplateDeclaration* right = function_template_origin(origins, rhs);
	if (left == NULL || right == NULL || left == right)
		return false;
	return left->parameters.size() < right->parameters.size();
}

Binding* canonical_function_binding(Binding* binding)
{
	while (binding != NULL &&
	       binding->kind == BindingKind::Function &&
	       binding->aliased_binding != NULL)
		binding = binding->aliased_binding;
	return binding;
}

void collect_conversion_functions(TypePtr record,
                                  set<Scope*>& seen,
                                  vector<Binding*>& out)
{
	TypePtr bare = pa11::strip_cv(record);
	if (bare->kind != pa11::TypeKind::Record ||
	    bare->scope == NULL ||
	    !seen.insert(bare->scope).second)
		return;
	for (map<string, vector<Binding*> >::const_iterator it =
	     bare->scope->members.begin();
	     it != bare->scope->members.end();
	     ++it)
	{
		if (it->first.compare(0, 9, "operator ") != 0)
			continue;
		out.insert(out.end(), it->second.begin(), it->second.end());
	}
	if (bare->base.get() != NULL)
		collect_conversion_functions(bare->base, seen, out);
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
		TypePtr selected_object =
			pa11::strip_cv(expression_object_type(selected.type));
		Conversion via_conversion =
			try_reference_conversion_functions(selected, target);
		if (via_conversion.viable)
			return via_conversion;
		bool lvalue_can_convert_to_prvalue =
			selected_object->kind == pa11::TypeKind::Array ||
			selected_object->kind == pa11::TypeKind::Function;
		if (target->kind == pa11::TypeKind::RValueReference &&
		    (selected.category != ValueCategory::LValue ||
		     lvalue_can_convert_to_prvalue))
		{
			TypePtr source_object = expression_object_type(selected.type);
			if ((source_object->cv & ~target->base->cv) != 0)
				return Conversion();
			Conversion conv = convert_value(selected, target->base);
			if (!conv.viable)
				return Conversion();
			Expr converted = conv.expr;
			converted.type = target->base;
			converted.category = ValueCategory::PRValue;
			if (!pa11::same_type(expression_object_type(selected.type),
			                     target->base))
			{
				converted.node = Node("cast-expression prvalue " +
				                      pa11::describe_type(target->base));
				add_child(converted.node, selected.node);
				annotate_expr_node(converted);
			}
			return Conversion(true, conv.rank + 1, converted);
		}
		TypePtr record = pa11::strip_cv(target->base);
		if (target->kind == pa11::TypeKind::LValueReference &&
		    pa11::type_has_const(target->base) &&
		    record->kind == pa11::TypeKind::Record &&
		    record->scope != NULL)
		{
			Conversion conv = convert_value(selected, target->base);
			if (conv.viable && type_can_bind_reference(target, conv.expr))
				return Conversion(true, conv.rank + 1, conv.expr);
			map<string, vector<Binding*> >::const_iterator found =
				record->scope->members.find(record->scope->name);
			if (found != record->scope->members.end())
			{
				for (size_t i = 0; i < found->second.size(); ++i)
				{
					Binding* ctor = found->second[i];
					if (ctor->kind != BindingKind::Function ||
					    ctor->is_explicit ||
					    ctor->type->parameters.size() != 2)
						continue;
					TypePtr ctor_param = ctor->type->parameters[1];
					if (pa11::is_reference_type(ctor_param) &&
					    pa11::same_type(pa11::strip_cv(ctor_param->base),
					                    record))
						continue;
					Conversion arg =
						convert_to(selected, ctor_param);
					if (!arg.viable)
						continue;
					Expr temporary;
					temporary.valid = true;
					temporary.type = target->base;
					temporary.category = ValueCategory::PRValue;
					temporary.braced_init_list = true;
					temporary.node = Node("braced-init-list");
					add_child(temporary.node, arg.expr.node);
					annotate_expr_node(temporary);
					return Conversion(true, arg.rank + 3, temporary);
				}
			}
		}
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
	int rank = record_base_distance(expression_object_type(selected.type),
	                                target->base);
	if (rank >= 1000000)
		rank = pa11::same_type(expression_object_type(selected.type),
		                       target->base) ? 0 : 1;
	if (target->kind == pa11::TypeKind::RValueReference &&
	    selected.category != ValueCategory::LValue)
		rank = 0;
	else if (target->kind == pa11::TypeKind::LValueReference &&
	         selected.category != ValueCategory::LValue)
		rank = 1;
	if (selected.category == ValueCategory::PRValue)
	{
		TypePtr source_object =
			pa11::strip_cv(expression_object_type(selected.type));
		if (source_object->kind == pa11::TypeKind::Record)
			ensure_default_destructor(
				source_object,
				source_object->base.get() != NULL);
	}
	return Conversion(true, rank, selected);
}

Conversion Parser::try_reference_conversion_functions(const Expr& selected,
                                                      TypePtr target)
{
	TypePtr selected_object =
		pa11::strip_cv(expression_object_type(selected.type));
	if (selected_object->kind != pa11::TypeKind::Record ||
	    selected_object->scope == NULL)
		return Conversion();
	Conversion best;
	vector<Binding*> conversions;
	set<Scope*> seen;
	collect_conversion_functions(selected_object, seen, conversions);
	for (size_t i = 0; i < conversions.size(); ++i)
	{
		Binding* op = conversions[i];
		if (op->kind != BindingKind::Function ||
		    op->type->kind != pa11::TypeKind::Function ||
		    op->type->parameters.size() != 1)
			continue;
		if (pa11::same_type(pa11::strip_cv(op->type->base),
		                    selected_object))
			continue;
		try
		{
			Expr member = make_member_expr(selected, op->name, ".");
			Expr call = make_call_expr(member, vector<Expr>());
			Conversion tail = convert_reference(call, target);
			if (!tail.viable)
				continue;
			tail.rank += 2;
			if (!best.viable || tail.rank < best.rank)
				best = tail;
			else if (best.viable && tail.rank == best.rank)
				throw runtime_error("ambiguous conversion function");
		}
		catch (const runtime_error&)
		{
		}
	}
	return best;
}

Conversion Parser::convert_value(const Expr& expr, TypePtr target)
{
	Expr selected = select_overload_expr(expr, target);
	TypePtr src = lvalue_to_rvalue_type(selected.type);
	TypePtr dst = pa11::strip_top_level_cv(target);
	if (pa11::same_type(src, dst))
		return Conversion(true, 0, selected);
	TypePtr src_record = pa11::strip_cv(src);
	TypePtr dst_record = pa11::strip_cv(dst);
	if (src_record->kind == pa11::TypeKind::Record &&
	    dst_record->kind == pa11::TypeKind::Record)
	{
		int distance = record_base_distance(src_record, dst_record);
		if (distance < 1000000)
		{
			Expr converted = selected;
			converted.type = dst;
			converted.category = ValueCategory::PRValue;
			converted.node = Node("cast-expression prvalue " +
			                      pa11::describe_type(dst));
			add_child(converted.node, selected.node);
			annotate_expr_node(converted);
			return Conversion(true, distance + 1, converted);
		}
	}
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
	if (src_record->kind == pa11::TypeKind::Record && src_record->scope != NULL)
	{
		Conversion best;
		vector<Binding*> conversions;
		set<Scope*> seen;
		collect_conversion_functions(src_record, seen, conversions);
		for (size_t i = 0; i < conversions.size(); ++i)
		{
				Binding* op = conversions[i];
				if (op->kind != BindingKind::Function ||
				    op->type->kind != pa11::TypeKind::Function ||
				    op->type->parameters.size() != 1)
					continue;
				if (pa11::same_type(pa11::strip_cv(op->type->base),
				                    src_record))
					continue;
				try
				{
					Expr member = make_member_expr(selected, op->name, ".");
					Expr call = make_call_expr(member, vector<Expr>());
					Conversion tail = convert_value(call, dst);
					if (!tail.viable)
						continue;
					tail.rank += 2;
					if (!best.viable || tail.rank < best.rank)
						best = tail;
					else if (best.viable && tail.rank == best.rank)
						throw runtime_error("ambiguous conversion function");
				}
				catch (const runtime_error&)
				{
				}
		}
		if (best.viable)
			return best;
	}
	return Conversion();
}

Expr Parser::select_overload_expr(const Expr& expr, TypePtr target)
{
	if (expr.overloads.empty())
		return expr;
	TypePtr wanted = target;
	bool target_member_function_pointer = false;
	if (is_function_pointer(target))
		wanted = pa11::strip_cv(target)->base;
	else if (is_function_reference(target))
		wanted = pa11::strip_cv(target->base);
	else if (is_member_function_pointer(target))
		target_member_function_pointer = true;
	else
		throw runtime_error("overloaded function id needs target");

	Binding* found = NULL;
	vector<Binding*> considered;
	for (size_t i = 0; i < expr.overloads.size(); ++i)
	{
		Binding* candidate = expr.overloads[i];
		map<Binding*, TemplateDeclaration*>::iterator template_it =
			function_template_placeholders_.find(candidate);
		Binding* placeholder = candidate->aliased_binding != NULL
			? candidate->aliased_binding : candidate;
		if (template_it != function_template_placeholders_.end() &&
		    template_it->second->placeholder == placeholder)
		{
			vector<TypePtr> explicit_args;
			map<Binding*, vector<TypePtr> >::const_iterator eit =
				expr.explicit_template_arguments.find(candidate);
			if (eit != expr.explicit_template_arguments.end())
				explicit_args = eit->second;
			vector<TypePtr> deduced;
			if (!deduce_function_template_target_type(template_it->second,
			                                          wanted,
			                                          explicit_args,
			                                          deduced))
				continue;
			candidate = instantiate_function_template(template_it->second,
			                                          deduced);
		}
		bool duplicate = false;
		for (size_t j = 0; j < considered.size(); ++j)
			if (pa11::same_type(considered[j]->type, candidate->type) &&
			    considered[j]->is_static_member == candidate->is_static_member)
				duplicate = true;
		if (duplicate)
			continue;
		considered.push_back(candidate);
		TypePtr candidate_member_pointer = target_member_function_pointer
			? member_function_pointer_type(candidate) : TypePtr();
		bool matches = target_member_function_pointer
			? (candidate_member_pointer.get() != NULL &&
			   pa11::same_type(candidate_member_pointer, target))
			: pa11::same_type(candidate->type, wanted);
		if (matches)
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
	bool address_expr =
		expr.node.line.compare(0, 16, "unary-expression") == 0 &&
		expr.node.has_op &&
		expr.node.op == OP_AMP &&
		!expr.node.children.empty();
	Expr selected_id;
	selected_id.valid = true;
	selected_id.binding = found;
	selected_id.type = found->type;
	selected_id.category = ValueCategory::LValue;
	selected_id.node = Node("id-expression lvalue " +
	                        pa11::describe_type(found->type) + " " +
	                        qualified_decl_name(found));
	selected_id.node.binding = found;
	annotate_expr_node(selected_id);
	if (address_expr)
	{
		out.type = target_member_function_pointer
			? member_function_pointer_type(found)
			: pa11::make_pointer(found->type);
		out.category = ValueCategory::PRValue;
		out.node = Node("unary-expression prvalue " +
		                pa11::describe_type(out.type) + " OP_AMP:&");
		add_child(out.node, selected_id.node);
		out.node.has_op = true;
		out.node.op = OP_AMP;
		out.node.token_text = "&";
	}
	else
	{
		out.type = found->type;
		out.category = ValueCategory::LValue;
		out.node = selected_id.node;
	}
	annotate_expr_node(out);
	return out;
}

bool Parser::call_candidate_has_arguments(Binding* fn, size_t arg_count) const
{
	if (arg_count < fn->type->parameters.size())
	{
		map<Binding*, vector<Expr> >::const_iterator dit =
			default_arguments_.find(fn);
		if (dit == default_arguments_.end())
			return false;
		for (size_t j = arg_count; j < fn->type->parameters.size(); ++j)
			if (j >= dit->second.size() || !dit->second[j].valid)
				return false;
	}
	if (!fn->type->variadic && arg_count != fn->type->parameters.size() &&
	    arg_count > fn->type->parameters.size())
		return false;
	return true;
}

bool Parser::convert_call_candidate_arguments(Binding* fn,
                                              const vector<Expr>& args,
                                              vector<Expr>& conv_args,
                                              vector<int>& ranks,
                                              int& object_rank)
{
	conv_args = args;
	if (conv_args.size() < fn->type->parameters.size())
	{
		const vector<Expr>& defaults = default_arguments_[fn];
		for (size_t j = conv_args.size(); j < fn->type->parameters.size(); ++j)
			conv_args.push_back(defaults[j]);
	}
	object_rank = -1;
	for (size_t j = 0; j < fn->type->parameters.size(); ++j)
	{
		Conversion conv;
		try
		{
			conv = convert_to(conv_args[j], fn->type->parameters[j]);
		}
		catch (const runtime_error&)
		{
			return false;
		}
		if (!conv.viable)
			return false;
		bool implicit_object_arg =
			j == 0 &&
			fn->owner != NULL &&
			fn->owner->kind == ScopeKind::Class &&
			!fn->is_static_member;
		if (implicit_object_arg)
			object_rank = conv.rank;
		else
			ranks.push_back(conv.rank);
		conv_args[j] = conv.expr;
	}
	return true;
}

Binding* Parser::resolve_call_candidate(const vector<Binding*>& overloads,
                                        const vector<Expr>& args,
                                        const map<Binding*, vector<TypePtr> >&
                                                explicit_template_arguments,
                                        vector<Expr>& converted)
{
	Binding* best = NULL;
	vector<int> best_ranks;
	vector<Expr> best_args;
	int best_object_rank = 0;
	bool ambiguous = false;
	vector<Binding*> considered;
	for (size_t i = 0; i < overloads.size(); ++i)
	{
		Binding* fn = overloads[i];
		fn = instantiate_template_call_candidate(fn,
		                                         explicit_template_arguments,
		                                         args);
		if (fn == NULL)
			continue;
		if (fn->type->kind != pa11::TypeKind::Function)
			continue;
		Binding* duplicate = duplicate_function_candidate(considered, fn);
		if (duplicate != NULL)
		{
			if (!function_template_more_specialized(
				    function_template_placeholders_, fn, duplicate))
				continue;
			considered.erase(find(considered.begin(),
			                      considered.end(),
			                      duplicate));
			}
			considered.push_back(fn);
			if (!call_candidate_has_arguments(fn, args.size()))
				continue;
			vector<int> ranks;
			vector<Expr> conv_args;
			int object_rank = -1;
			if (!convert_call_candidate_arguments(fn,
			                                      args,
			                                      conv_args,
			                                      ranks,
			                                      object_rank))
				continue;
		add_variadic_argument_ranks(fn, args.size(), ranks);
		if (object_rank < 0)
			object_rank = 0;
		bool better = best == NULL || ranks_better(ranks, best_ranks);
		if (!better && best != NULL && ranks == best_ranks &&
		    function_template_more_specialized(function_template_placeholders_,
		                                      fn,
		                                      best))
			better = true;
		bool indistinguishable = false;
		if (best != NULL && !better && !ranks_better(best_ranks, ranks))
		{
			if (ranks == best_ranks)
			{
				if (object_rank < best_object_rank)
					better = true;
				else if (object_rank == best_object_rank)
					indistinguishable = true;
			}
			else
				indistinguishable = true;
		}
		if (better)
		{
			best = fn;
			best_ranks = ranks;
			best_args = conv_args;
			best_object_rank = object_rank;
			ambiguous = false;
		}
		else if (indistinguishable)
			ambiguous = true;
	}
	if (best == NULL || ambiguous)
	{
		string detail;
		for (size_t i = 0; i < considered.size(); ++i)
		{
			if (!detail.empty())
				detail += "; ";
			detail += considered[i]->name + " " +
			          pa11::describe_type(considered[i]->type);
		}
		throw runtime_error("cannot resolve call overload " + detail);
	}
	converted = best_args;
	return canonical_function_binding(best);
}

Binding* Parser::instantiate_template_call_candidate(
	Binding* fn,
	const map<Binding*, vector<TypePtr> >& explicit_template_arguments,
	const vector<Expr>& args)
{
	map<Binding*, TemplateDeclaration*>::iterator template_it =
		function_template_placeholders_.find(fn);
	Binding* placeholder = fn->aliased_binding != NULL ? fn->aliased_binding : fn;
	if (template_it == function_template_placeholders_.end() ||
	    template_it->second->placeholder != placeholder)
		return fn;
	vector<TypePtr> explicit_args;
	map<Binding*, vector<TypePtr> >::const_iterator eit =
		explicit_template_arguments.find(fn);
	if (eit != explicit_template_arguments.end())
		explicit_args = eit->second;
	vector<TypePtr> deduced;
	if (!deduce_function_template_arguments(template_it->second,
	                                        args,
	                                        explicit_args,
	                                        deduced))
		return NULL;
	try
	{
		return instantiate_function_template(template_it->second, deduced);
	}
	catch (const runtime_error&)
	{
		return NULL;
	}
}

Binding* Parser::resolve_constructor_candidate(TypePtr type,
                                               const vector<Expr>& args,
                                               bool copy_initialization,
                                               vector<Expr>& converted)
{
	TypePtr record = pa11::strip_cv(type);
	if (record->kind != pa11::TypeKind::Record || record->scope == NULL)
		throw runtime_error("constructor target is not record");
	ensure_copy_move_constructor_for_single_arg(record, args);
	map<string, vector<Binding*> >::const_iterator found =
		record->scope->members.find(record->scope->name);
	if (found == record->scope->members.end())
		throw runtime_error("no matching constructor");

	Binding* best = NULL;
	vector<int> best_ranks;
	vector<Expr> best_args;
	bool ambiguous = false;
	for (size_t i = 0; i < found->second.size(); ++i)
	{
		Binding* ctor = found->second[i];
		if (ctor->kind != BindingKind::Function ||
		    ctor->type->kind != pa11::TypeKind::Function ||
		    ctor->type->parameters.empty())
			continue;
		if (copy_initialization && ctor->is_explicit)
			continue;
		size_t param_count = ctor->type->parameters.size() - 1;
		if (args.size() > param_count)
			continue;
		if (args.size() < param_count)
		{
			map<Binding*, vector<Expr> >::const_iterator defaults =
				default_arguments_.find(ctor);
			if (defaults == default_arguments_.end())
				continue;
			bool have_defaults = true;
			for (size_t j = args.size() + 1;
			     j < ctor->type->parameters.size();
			     ++j)
			{
				if (j >= defaults->second.size() || !defaults->second[j].valid)
				{
					have_defaults = false;
					break;
				}
			}
			if (!have_defaults)
				continue;
		}

		vector<int> ranks;
		vector<Expr> conv_args = args;
		bool ok = true;
		for (size_t j = 0; j < args.size(); ++j)
		{
			Conversion conv;
			try
			{
				conv = convert_to(args[j], ctor->type->parameters[j + 1]);
			}
			catch (const runtime_error&)
			{
				ok = false;
				break;
			}
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
		if (args.size() < param_count)
		{
			const vector<Expr>& defaults = default_arguments_[ctor];
			for (size_t j = args.size() + 1;
			     j < ctor->type->parameters.size();
			     ++j)
			{
				conv_args.push_back(defaults[j]);
				ranks.push_back(3);
			}
		}
		if (best == NULL || ranks_better(ranks, best_ranks))
		{
			best = ctor;
			best_ranks = ranks;
			best_args = conv_args;
			ambiguous = false;
		}
		else if (!ranks_better(best_ranks, ranks))
			ambiguous = true;
	}
	if (best == NULL || ambiguous)
		throw runtime_error("no matching constructor");
	best = canonical_function_binding(best);
	if (best->is_defaulted &&
	    best->type->kind == pa11::TypeKind::Function &&
	    best->type->parameters.size() == 2 &&
	    pa11::is_reference_type(best->type->parameters[1]) &&
	    pa11::same_type(pa11::strip_cv(best->type->parameters[1]->base),
	                    record))
		ensure_copy_move_constructor(
			record,
			best->type->parameters[1]->kind ==
				pa11::TypeKind::RValueReference);
	if (deleted_functions_.find(best) != deleted_functions_.end())
		throw runtime_error("call to deleted function");
	converted = best_args;
	return best;
}

Expr Parser::make_constructor_init_expr(TypePtr type,
                                        const vector<Expr>& args,
                                        bool copy_initialization)
{
	vector<Expr> converted;
	Binding* ctor =
		resolve_constructor_candidate(type, args, copy_initialization, converted);
	Expr out;
	out.valid = true;
	out.type = type;
	out.category = ValueCategory::PRValue;
	out.braced_init_list = true;
	out.copy_initialization = copy_initialization;
	out.node = Node("braced-init-list");
	out.node.type = type;
	out.node.category = out.category;
	out.node.direct_call = ctor;
	for (size_t i = 0; i < converted.size(); ++i)
		add_child(out.node, converted[i].node);
	annotate_expr_node(out);
	out.node.direct_call = ctor;
	return out;
}

Expr Parser::make_call_expr(Expr callee, vector<Expr> args)
{
	TypePtr callee_object = pa11::strip_cv(expression_object_type(callee.type));
	if (callee.overloads.empty() &&
	    callee_object->kind == pa11::TypeKind::Record &&
	    callee_object->scope != NULL)
	{
		vector<Binding*> members =
			lookup_qualified_set(callee_object->scope,
			                     "operator()",
			                     pa11::LOOKUP_FUNCTION);
		if (!members.empty())
		{
			Expr member = make_member_expr(callee, "operator()", ".");
			return make_call_expr(member, args);
		}
	}
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
	if (!callee.overloads.empty() &&
	    callee.node.line.compare(0, 17, "member-expression") == 0 &&
	    !callee.node.children.empty())
		prepare_member_call(callee, args);
	else if (!callee.overloads.empty() &&
	         callee.node.line.compare(0, 13, "id-expression") == 0)
	{
		vector<Binding*> static_overloads;
		bool has_class_member = false;
		for (size_t i = 0; i < callee.overloads.size(); ++i)
		{
			Binding* candidate = callee.overloads[i];
			if (candidate->owner != NULL &&
			    candidate->owner->kind == ScopeKind::Class)
			{
				has_class_member = true;
				if (candidate->is_static_member)
					static_overloads.push_back(candidate);
			}
		}
		if (has_class_member && !static_overloads.empty())
			callee.overloads = static_overloads;
	}
	vector<Expr> converted;
	Binding* direct = NULL;
	if (!callee.overloads.empty())
		direct = resolve_call_candidate(callee.overloads,
		                                args,
		                                callee.explicit_template_arguments,
		                                converted);
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
		out.node.virtual_dispatch =
			callee.node.line.compare(0, 17, "member-expression") == 0 &&
			direct->is_virtual &&
			!callee.node.suppress_virtual_dispatch;
		add_child(out.node, Node("callee " + qualified_decl_name(direct) +
		                         " " + pa11::describe_type(direct->type)));
	}
	else
	{
		TypePtr callee_type = expression_object_type(callee.type);
		callee_type = pa11::strip_cv(callee_type);
		if (callee_type->kind == pa11::TypeKind::Pointer)
			callee_type = callee_type->base;
		if (callee_type->kind != pa11::TypeKind::Function)
		{
			if (type_is_template_dependent(callee.type))
				return make_dependent_call_expr(callee, args);
			throw runtime_error("called object is not callable");
		}
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
	if (out.category == ValueCategory::PRValue &&
	    pa11::strip_cv(out.type)->kind == pa11::TypeKind::Record)
		ensure_default_destructor(out.type);
	out.valid = true;
	annotate_expr_node(out);
	return out;
}

Expr Parser::make_dependent_call_expr(const Expr& callee,
                                      const vector<Expr>& args)
{
	Expr out;
	out.type = pa11::make_template_parameter_type("__dependent_call");
	out.category = ValueCategory::PRValue;
	out.node = Node("call-expression prvalue " + pa11::describe_type(out.type));
	add_child(out.node, callee.node);
	for (size_t i = 0; i < args.size(); ++i)
		add_child(out.node, args[i].node);
	out.valid = true;
	annotate_expr_node(out);
	return out;
}

void Parser::ensure_copy_move_constructor_for_single_arg(
	TypePtr record,
	const vector<Expr>& args)
{
	if (args.size() != 1)
		return;
	TypePtr arg_record = pa11::strip_cv(expression_object_type(args[0].type));
	if (arg_record->kind != pa11::TypeKind::Record ||
	    !pa11::same_type(arg_record, record))
		return;
	if (args[0].category == ValueCategory::XValue)
		ensure_copy_move_constructor(record, true);
	ensure_copy_move_constructor(record, false);
}

void Parser::add_variadic_argument_ranks(Binding* fn,
                                         size_t arg_count,
                                         vector<int>& ranks) const
{
	if (fn == NULL ||
	    fn->type->kind != pa11::TypeKind::Function ||
	    !fn->type->variadic ||
	    arg_count <= fn->type->parameters.size())
		return;
	for (size_t i = fn->type->parameters.size(); i < arg_count; ++i)
		ranks.push_back(100);
}

void Parser::prepare_member_call(Expr& callee, vector<Expr>& args)
{
	bool needs_this = false;
	Expr object;
	object.node = callee.node.children[0];
	object.type = object.node.type;
	object.category = object.node.category;
	object.binding = object.node.binding;
	object.valid = true;
	vector<Binding*> viable_overloads;
	vector<Binding*> nonstatic_overloads;
	for (size_t i = 0; i < callee.overloads.size(); ++i)
	{
		Binding* candidate = callee.overloads[i];
		if (candidate->owner != NULL &&
		    candidate->owner->kind == ScopeKind::Class &&
		    !candidate->is_static_member)
		{
			if (candidate->ref_qualifier == 1 &&
			    object.category != ValueCategory::LValue)
			{
				TypePtr this_param =
					candidate->type->parameters.empty()
					? TypePtr() : candidate->type->parameters[0];
				TypePtr this_object =
					this_param.get() != NULL &&
					pa11::strip_cv(this_param)->kind ==
					pa11::TypeKind::Pointer
					? pa11::strip_cv(this_param)->base : TypePtr();
				if (this_object.get() == NULL ||
				    !pa11::type_has_const(this_object))
					continue;
			}
			if (candidate->ref_qualifier == 2 &&
			    object.category == ValueCategory::LValue)
				continue;
			needs_this = true;
			nonstatic_overloads.push_back(candidate);
		}
		viable_overloads.push_back(candidate);
	}
	if (!nonstatic_overloads.empty())
		viable_overloads = nonstatic_overloads;
	if (viable_overloads.empty())
		throw runtime_error("cannot resolve call overload");
	callee.overloads = viable_overloads;
	if (needs_this)
	{
		Expr this_arg = callee.node.has_op && callee.node.op == OP_ARROW
			? object : make_address_expr("&", object);
		args.insert(args.begin(), this_arg);
	}
}

bool Parser::ranks_better(const vector<int>& lhs, const vector<int>& rhs) const
{
	if (rhs.empty())
		return false;
	if (lhs.size() != rhs.size())
		return false;
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
