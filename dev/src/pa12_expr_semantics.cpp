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

bool template_declaration_has_body(const vector<Token>& tokens,
                                   const TemplateDeclaration* declaration)
{
	if (declaration == NULL || !declaration->has_definition)
		return false;
	for (size_t i = declaration->decl_begin;
	     i < declaration->decl_end && i < tokens.size();
	     ++i)
		if (tokens[i].kind == posttoken::TokenKind::Simple &&
		    tokens[i].type == OP_LBRACE)
			return true;
	return false;
}

bool same_template_specialization_record(TypePtr left, TypePtr right)
{
	TypePtr l = pa11::strip_cv(left);
	TypePtr r = pa11::strip_cv(right);
	return l->kind == pa11::TypeKind::Record &&
	       r->kind == pa11::TypeKind::Record &&
	       l->is_template_specialization &&
	       r->is_template_specialization &&
	       l->name == r->name;
}

bool same_template_signature_argument(
	const pa11::TemplateInstanceArgument& left,
	const pa11::TemplateInstanceArgument& right,
	map<string, string>& type_parameter_names);

bool same_template_signature_type(TypePtr left,
                                  TypePtr right,
                                  map<string, string>& type_parameter_names)
{
	if (left.get() == NULL || right.get() == NULL)
		return left.get() == right.get();
	if (left->kind == pa11::TypeKind::TemplateParameter &&
	    right->kind == pa11::TypeKind::TemplateParameter)
	{
		map<string, string>::iterator found =
			type_parameter_names.find(left->name);
		if (found == type_parameter_names.end())
		{
			type_parameter_names[left->name] = right->name;
			return true;
		}
		return found->second == right->name;
	}
	if (pa11::same_type(left, right) ||
	    same_template_specialization_record(left, right))
		return true;
	if (left->kind != right->kind)
		return false;
	if (left->kind == pa11::TypeKind::Record &&
	    left->is_template_specialization &&
	    right->is_template_specialization &&
	    left->template_primary_name == right->template_primary_name &&
	    left->template_arguments.size() == right->template_arguments.size())
	{
		for (size_t i = 0; i < left->template_arguments.size(); ++i)
			if (!same_template_signature_argument(
				    left->template_arguments[i],
				    right->template_arguments[i],
				    type_parameter_names))
				return false;
		return true;
	}
	switch (left->kind)
	{
	case pa11::TypeKind::Cv:
		return left->cv == right->cv &&
		       same_template_signature_type(left->base,
		                                    right->base,
		                                    type_parameter_names);
	case pa11::TypeKind::Pointer:
	case pa11::TypeKind::LValueReference:
	case pa11::TypeKind::RValueReference:
		return same_template_signature_type(left->base,
		                                    right->base,
		                                    type_parameter_names);
	case pa11::TypeKind::Array:
		return left->unknown_bound == right->unknown_bound &&
		       left->bound == right->bound &&
		       same_template_signature_type(left->base,
		                                    right->base,
		                                    type_parameter_names);
	case pa11::TypeKind::Function:
		if (left->cv != right->cv ||
		    left->variadic != right->variadic ||
		    left->parameters.size() != right->parameters.size() ||
		    !same_template_signature_type(left->base,
		                                  right->base,
		                                  type_parameter_names))
			return false;
		for (size_t i = 0; i < left->parameters.size(); ++i)
			if (!same_template_signature_type(left->parameters[i],
			                                  right->parameters[i],
			                                  type_parameter_names))
				return false;
		return true;
	case pa11::TypeKind::MemberPointer:
		return same_template_signature_type(left->member_class,
		                                    right->member_class,
		                                    type_parameter_names) &&
		       same_template_signature_type(left->base,
		                                    right->base,
		                                    type_parameter_names);
	default:
		return false;
	}
}

bool same_template_signature_argument(
	const pa11::TemplateInstanceArgument& left,
	const pa11::TemplateInstanceArgument& right,
	map<string, string>& type_parameter_names)
{
	if (left.kind != right.kind)
		return false;
	if (left.kind == pa11::TemplateInstanceArgumentKind::Type)
		return same_template_signature_type(left.type,
		                                    right.type,
		                                    type_parameter_names);
	if (left.kind == pa11::TemplateInstanceArgumentKind::Value)
		return left.dependent == right.dependent &&
		       (left.dependent ||
		        (left.value == right.value &&
		         (left.type.get() == NULL || right.type.get() == NULL ||
		          same_template_signature_type(left.type,
		                                       right.type,
		                                       type_parameter_names))));
	if (left.kind == pa11::TemplateInstanceArgumentKind::Template)
		return left.template_name == right.template_name;
	if (left.pack.size() != right.pack.size())
		return false;
	for (size_t i = 0; i < left.pack.size(); ++i)
		if (!same_template_signature_argument(left.pack[i],
		                                      right.pack[i],
		                                      type_parameter_names))
			return false;
	return true;
}

bool same_template_signature_type(TypePtr left, TypePtr right)
{
	map<string, string> type_parameter_names;
	return same_template_signature_type(left, right, type_parameter_names);
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

bool template_parameter_lists_match(const vector<TemplateParameterInfo>& left,
                                    const vector<TemplateParameterInfo>& right)
{
	if (left.size() != right.size())
		return false;
	for (size_t i = 0; i < left.size(); ++i)
	{
		if (left[i].kind != right[i].kind ||
		    left[i].is_pack != right[i].is_pack ||
		    left[i].template_parameters.size() !=
			    right[i].template_parameters.size())
			return false;
		for (size_t j = 0; j < left[i].template_parameters.size(); ++j)
			if (left[i].template_parameters[j].kind !=
				    right[i].template_parameters[j].kind ||
			    left[i].template_parameters[j].is_pack !=
				    right[i].template_parameters[j].is_pack)
				return false;
	}
	return true;
}

int template_argument_specificity(
	const pa11::TemplateInstanceArgument& argument);

int type_pattern_specificity(TypePtr type)
{
	if (type.get() == NULL)
		return 0;
	if (type->kind == pa11::TypeKind::TemplateParameter ||
	    type->kind == pa11::TypeKind::TemplateTemplateParameter)
		return 0;
	if (type->kind == pa11::TypeKind::Cv ||
	    type->kind == pa11::TypeKind::Pointer ||
	    type->kind == pa11::TypeKind::LValueReference ||
	    type->kind == pa11::TypeKind::RValueReference ||
	    type->kind == pa11::TypeKind::Array)
		return 1 + type_pattern_specificity(type->base);
	if (type->kind == pa11::TypeKind::Function)
	{
		int score = 1 + type_pattern_specificity(type->base);
		for (size_t i = 0; i < type->parameters.size(); ++i)
			score += type_pattern_specificity(type->parameters[i]);
		return score;
	}
	if (type->kind == pa11::TypeKind::MemberPointer)
		return 1 + type_pattern_specificity(type->member_class) +
		       type_pattern_specificity(type->base);
	if (type->kind == pa11::TypeKind::Record &&
	    type->is_template_specialization)
	{
		int score = 2;
		for (size_t i = 0; i < type->template_arguments.size(); ++i)
			score += template_argument_specificity(
				type->template_arguments[i]);
		return score;
	}
	return 1;
}

int template_argument_specificity(
	const pa11::TemplateInstanceArgument& argument)
{
	if (argument.kind == pa11::TemplateInstanceArgumentKind::Type)
		return type_pattern_specificity(argument.type);
	if (argument.kind == pa11::TemplateInstanceArgumentKind::Value)
		return argument.dependent ? 0 : 1;
	if (argument.kind == pa11::TemplateInstanceArgumentKind::Template)
		return 1;
	int score = 0;
	for (size_t i = 0; i < argument.pack.size(); ++i)
		score += template_argument_specificity(argument.pack[i]);
	return score;
}

int function_template_parameter_specificity(TemplateDeclaration* declaration)
{
	if (declaration == NULL ||
	    declaration->generic_function_type.get() == NULL ||
	    declaration->generic_function_type->kind != pa11::TypeKind::Function)
		return 0;
	int score = 0;
	for (size_t i = 0;
	     i < declaration->generic_function_type->parameters.size();
	     ++i)
		score += type_pattern_specificity(
			declaration->generic_function_type->parameters[i]);
	return score;
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
	int left_score = function_template_parameter_specificity(left);
	int right_score = function_template_parameter_specificity(right);
	if (left_score != right_score)
		return left_score > right_score;
	return left->parameters.size() < right->parameters.size();
}

Binding* canonical_function_binding(Binding* binding)
{
	while (binding != NULL &&
	       binding->kind == BindingKind::Function &&
	       binding->aliased_binding != NULL)
	{
		if (binding->is_inline_definition &&
		    !binding->aliased_binding->is_inline_definition)
			break;
		binding = binding->aliased_binding;
	}
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

Expr make_builtin_constant_call(const vector<Expr>& args)
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

void filter_static_class_member_overloads(Expr& callee)
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
	if (pa11::same_type(src, dst) ||
	    same_template_specialization_record(src, dst))
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
	if (dst_record->kind == pa11::TypeKind::Record &&
	    dst_record->scope != NULL)
	{
		Conversion best;
		Binding* best_ctor = NULL;
		Expr best_arg;
		bool ambiguous = false;
		map<string, vector<Binding*> >::const_iterator found =
			dst_record->scope->members.find(dst_record->scope->name);
		if (found != dst_record->scope->members.end())
		{
			for (size_t i = 0; i < found->second.size(); ++i)
			{
				Binding* ctor = found->second[i];
				if (ctor->kind != BindingKind::Function ||
				    ctor->is_explicit ||
				    ctor->type->kind != pa11::TypeKind::Function ||
				    ctor->type->parameters.size() != 2)
					continue;
				TypePtr param = ctor->type->parameters[1];
				if (pa11::is_reference_type(param) &&
				    (pa11::same_type(pa11::strip_cv(param->base),
				                     dst_record) ||
				     same_template_specialization_record(param->base,
				                                         dst_record)))
					continue;
				Conversion arg = convert_to(selected, param);
				if (!arg.viable)
					continue;
				if (!best.viable || arg.rank < best.rank)
				{
					best = arg;
					best_ctor = ctor;
					best_arg = arg.expr;
					ambiguous = false;
				}
				else if (best.viable && arg.rank == best.rank)
					ambiguous = true;
			}
		}
		if (best.viable && !ambiguous)
		{
			if (deleted_functions_.find(best_ctor) != deleted_functions_.end())
				throw runtime_error("call to deleted function");
			Expr constructed;
			constructed.valid = true;
			constructed.type = dst;
			constructed.category = ValueCategory::PRValue;
			constructed.braced_init_list = true;
			constructed.copy_initialization = true;
			constructed.node = Node("braced-init-list");
			constructed.node.type = dst;
			constructed.node.category = constructed.category;
			constructed.node.direct_call = best_ctor;
			add_child(constructed.node, best_arg.node);
			annotate_expr_node(constructed);
			return Conversion(true, best.rank + 3, constructed);
		}
	}
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
                                        const map<Binding*, vector<TemplateArgument> >&
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
			bool fn_template =
				function_template_placeholders_.find(fn) !=
				function_template_placeholders_.end();
			bool duplicate_template =
				function_template_placeholders_.find(duplicate) !=
				function_template_placeholders_.end();
			bool replace_duplicate =
				!fn_template && duplicate_template;
			if (!replace_duplicate && fn_template && !duplicate_template)
				;
			else if (!replace_duplicate)
				replace_duplicate =
					fn->is_inline_definition && !duplicate->is_inline_definition;
			if (!replace_duplicate &&
			    function_template_more_specialized(
				    function_template_placeholders_, fn, duplicate))
				replace_duplicate = true;
			if (!replace_duplicate)
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
		    object_rank == best_object_rank)
		{
			bool fn_template =
				function_template_placeholders_.find(fn) !=
				function_template_placeholders_.end();
			bool best_template =
				function_template_placeholders_.find(best) !=
				function_template_placeholders_.end();
			if (fn->is_inline_definition && !best->is_inline_definition)
				better = true;
			else if (!fn->is_inline_definition && best->is_inline_definition)
				;
			else if (!fn_template && best_template)
				better = true;
			else if (fn_template == best_template &&
			         function_template_more_specialized(
				         function_template_placeholders_,
				         fn,
				         best))
				better = true;
		}
		bool indistinguishable = false;
		if (best != NULL && !better && !ranks_better(best_ranks, ranks))
		{
			if (ranks == best_ranks)
			{
				if (object_rank < best_object_rank)
					better = true;
				else if (object_rank == best_object_rank &&
				         best->is_inline_definition &&
				         !fn->is_inline_definition)
					indistinguishable = false;
				else if (object_rank == best_object_rank &&
				         function_template_placeholders_.find(best) ==
				         function_template_placeholders_.end() &&
				         function_template_placeholders_.find(fn) !=
				         function_template_placeholders_.end())
					indistinguishable = false;
				else if (object_rank == best_object_rank &&
				         function_template_more_specialized(
					         function_template_placeholders_,
					         best,
					         fn))
					indistinguishable = false;
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
			if (detail.empty())
				detail = "";
			throw runtime_error("cannot resolve call overload " + detail);
		}
	converted = best_args;
	return canonical_function_binding(best);
}

Binding* Parser::instantiate_template_call_candidate(
	Binding* fn,
	const map<Binding*, vector<TemplateArgument> >& explicit_template_arguments,
	const vector<Expr>& args)
{
	map<Binding*, TemplateDeclaration*>::iterator template_it =
		function_template_placeholders_.find(fn);
	Binding* placeholder = fn->aliased_binding != NULL ? fn->aliased_binding : fn;
	if (template_it == function_template_placeholders_.end())
		return fn;
	TemplateDeclaration* original_declaration = template_it->second;
	bool placeholder_candidate = original_declaration->placeholder == placeholder;
	bool specialization_candidate =
		original_declaration->placeholder != NULL &&
		original_declaration->placeholder != fn;
	if (!placeholder_candidate && !specialization_candidate)
		return fn;
	TemplateDeclaration* declaration = original_declaration;
	if (!template_declaration_has_body(tokens_, declaration))
	{
		map<Scope*, map<string, vector<TemplateDeclaration*> > >::iterator sit =
			function_templates_.find(declaration->owner);
		if (sit != function_templates_.end())
		{
			map<string, vector<TemplateDeclaration*> >::iterator it =
				sit->second.find(declaration->name);
			if (it != sit->second.end())
			{
				for (size_t i = 0; i < it->second.size(); ++i)
				{
					TemplateDeclaration* candidate = it->second[i];
					if (candidate == declaration ||
					    !template_declaration_has_body(tokens_, candidate) ||
					    candidate->generic_function_type.get() == NULL ||
					    !same_template_signature_type(
						    candidate->generic_function_type,
						    declaration->generic_function_type) ||
					    !template_parameter_lists_match(candidate->parameters,
					                                    declaration->parameters))
						continue;
					declaration = candidate;
					break;
				}
			}
		}
	}
	if (specialization_candidate &&
	    !placeholder_candidate &&
	    declaration == original_declaration)
		return canonical_function_binding(fn);
	vector<TemplateArgument> explicit_args;
	map<Binding*, vector<TemplateArgument> >::const_iterator eit =
		explicit_template_arguments.find(fn);
	if (eit == explicit_template_arguments.end() && placeholder != fn)
		eit = explicit_template_arguments.find(placeholder);
	if (eit == explicit_template_arguments.end() &&
	    original_declaration->placeholder != NULL)
		eit = explicit_template_arguments.find(original_declaration->placeholder);
	if (eit != explicit_template_arguments.end())
		explicit_args = eit->second;
	vector<TemplateArgument> deduced;
	if (!deduce_function_template_arguments(declaration,
	                                        args,
	                                        explicit_args,
	                                        deduced))
		return NULL;
	Scope* saved_friend_class_scope = declaration->friend_class_scope;
	if (declaration->friend_class_scope == NULL &&
	    original_declaration->friend_class_scope != NULL)
		declaration->friend_class_scope =
			original_declaration->friend_class_scope;
	if (declaration != original_declaration &&
	    declaration->placeholder != NULL)
	{
		for (map<Scope*, vector<Binding*> >::const_iterator it =
			     class_friend_functions_.begin();
		     it != class_friend_functions_.end();
		     ++it)
			for (size_t i = 0; i < it->second.size(); ++i)
			{
				Binding* friend_binding = it->second[i];
				bool same_friend =
					original_declaration->placeholder != NULL &&
					friend_binding == original_declaration->placeholder;
				if (!same_friend &&
				    friend_binding->kind == BindingKind::Function &&
				    friend_binding->name == declaration->name &&
				    same_template_signature_type(
					    friend_binding->type,
					    declaration->generic_function_type))
					same_friend = true;
				if (same_friend)
					add_friend_function(it->first, declaration->placeholder);
			}
	}
	try
	{
		Binding* instantiated =
			instantiate_function_template(declaration, deduced);
		declaration->friend_class_scope = saved_friend_class_scope;
		if (declaration != original_declaration)
		{
			string key =
				template_argument_key(
					complete_template_arguments(original_declaration, deduced));
			map<string, Binding*>::iterator existing =
				original_declaration->function_specializations.find(key);
			if (existing !=
			    original_declaration->function_specializations.end() &&
			    existing->second != instantiated)
				existing->second->aliased_binding = instantiated;
			original_declaration->function_specializations[key] = instantiated;
			if (fn != instantiated)
				fn->aliased_binding = instantiated;
		}
		if (original_declaration->friend_class_scope != NULL)
			add_friend_function(original_declaration->friend_class_scope,
			                    instantiated);
		return instantiated;
	}
	catch (const runtime_error&)
	{
		declaration->friend_class_scope = saved_friend_class_scope;
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
	vector<Binding*> considered;
	for (size_t i = 0; i < found->second.size(); ++i)
	{
		Binding* ctor = found->second[i];
		map<Binding*, TemplateDeclaration*>::iterator template_it =
			function_template_placeholders_.find(ctor);
		if (template_it != function_template_placeholders_.end())
		{
			Expr this_arg;
			this_arg.valid = true;
			this_arg.type = pa11::make_pointer(record);
			this_arg.category = ValueCategory::PRValue;
			this_arg.node = Node("id-expression prvalue " +
			                     pa11::describe_type(this_arg.type) +
			                     " this");
			annotate_expr_node(this_arg);
			vector<Expr> deduction_args;
			deduction_args.push_back(this_arg);
			deduction_args.insert(deduction_args.end(),
			                      args.begin(),
			                      args.end());
			map<Binding*, vector<TemplateArgument> > explicit_args;
			ctor = instantiate_template_call_candidate(ctor,
			                                           explicit_args,
			                                           deduction_args);
			if (ctor == NULL)
				continue;
		}
		if (ctor->kind != BindingKind::Function ||
		    ctor->type->kind != pa11::TypeKind::Function ||
		    ctor->type->parameters.empty())
			continue;
		bool duplicate = false;
		for (size_t j = 0; j < considered.size(); ++j)
			if (pa11::same_type(considered[j]->type, ctor->type))
				duplicate = true;
		if (duplicate)
			continue;
		considered.push_back(ctor);
		if (copy_initialization && ctor->is_explicit)
			continue;
		size_t param_count = ctor->type->parameters.size() - 1;
		if (args.size() > param_count)
			continue;
		if (args.size() == 1 &&
		    ctor->type->parameters.size() == 2 &&
		    pa11::is_reference_type(ctor->type->parameters[1]) &&
		    (pa11::same_type(pa11::strip_cv(
			                      ctor->type->parameters[1]->base),
		                     record) ||
		     same_template_specialization_record(
			     ctor->type->parameters[1]->base,
			     record)))
		{
			TypePtr arg_record =
				pa11::strip_cv(expression_object_type(args[0].type));
			if (arg_record->kind == pa11::TypeKind::Record &&
			    !pa11::same_type(arg_record, record) &&
			    !same_template_specialization_record(arg_record, record) &&
			    record_base_distance(arg_record, record) >= 1000000)
				continue;
		}
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
	Expr pack;
	if (make_call_pack_expr(callee, args, pack))
		return pack;
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
		return make_builtin_constant_call(args);
	if (!callee.overloads.empty() &&
	    callee.node.line.compare(0, 17, "member-expression") == 0 &&
	    !callee.node.children.empty())
		prepare_member_call(callee, args);
	else if (!callee.overloads.empty() &&
	         callee.node.line.compare(0, 13, "id-expression") == 0)
		filter_static_class_member_overloads(callee);
	vector<Expr> converted;
	Binding* direct = NULL;
	if (!callee.overloads.empty())
		direct = resolve_call_candidate(callee.overloads,
		                                args,
		                                callee.explicit_template_arguments,
		                                converted);
	else if (callee.binding != NULL &&
	         callee.binding->kind == BindingKind::Function)
	{
		direct = callee.binding;
		converted = args;
	}
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
			Node callee_node("callee " + qualified_decl_name(direct) +
			                 " " + pa11::describe_type(direct->type));
			callee_node.binding = direct;
			callee_node.direct_call = direct;
			add_child(out.node, callee_node);
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
	if (direct != NULL)
	{
		vector<Node> constexpr_args;
		for (size_t i = 0; i < converted.size(); ++i)
			constexpr_args.push_back(converted[i].node);
		ConstexprValue constexpr_value;
		if (try_evaluate_constexpr_call(direct,
		                                constexpr_args,
		                                constexpr_value))
			apply_constexpr_value(out, constexpr_value);
	}
	annotate_expr_node(out);
	return out;
}

}  // namespace internal
}  // namespace pa12
