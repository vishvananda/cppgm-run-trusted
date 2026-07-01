#include "pa12_expr_semantics_support.h"
#include "pa12_templates_instance_support.h"
#include "pa12_types_support.h"

#include <algorithm>
#include <stdexcept>

using namespace std;

namespace pa12 {
namespace internal {

Binding* Parser::resolve_constructor_candidate(TypePtr type,
                                               const vector<Expr>& args,
                                               bool copy_initialization,
                                               vector<Expr>& converted)
{
	TypePtr record = pa11::strip_cv(type);
	if (record->kind != pa11::TypeKind::Record || record->scope == NULL)
		throw runtime_error("constructor target is not record");
	Binding* hosted_allocator_ctor = NULL;
	vector<Expr> hosted_allocator_args;
	bool hosted_allocator_ambiguous = false;
	if (use_hosted_allocator_constructor_fallback(record,
	                                             args,
	                                             hosted_allocator_ctor,
	                                             hosted_allocator_args,
	                                             hosted_allocator_ambiguous))
	{
		finalize_constructor_candidate(record, hosted_allocator_ctor);
		converted = hosted_allocator_args;
		return hosted_allocator_ctor;
	}
	if (args.size() == 1 && args[0].type.get() != NULL)
	{
		TypePtr source_record =
			pa11::strip_cv(expression_object_type(args[0].type));
		if (source_record.get() != NULL &&
		    source_record->kind == pa11::TypeKind::Record &&
		    (pa11::same_type(source_record, record) ||
		     same_template_specialization_record(source_record, record)))
		{
			bool move = args[0].category != ValueCategory::LValue;
			Binding* copy_move = ensure_copy_move_constructor(record, move);
			if (copy_move == NULL && move)
				copy_move = ensure_copy_move_constructor(record, false);
			if (copy_move != NULL &&
			    deleted_functions_.find(copy_move) == deleted_functions_.end())
			{
				finalize_constructor_candidate(record, copy_move);
				vector<int> ranks;
				map<pair<size_t, const void*>, Conversion> conversion_cache;
				if (!constructor_accepts_argument_count(copy_move,
				                                        args.size()) ||
				    !convert_constructor_candidate_arguments(copy_move,
				                                             args,
				                                             converted,
				                                             ranks,
				                                             conversion_cache))
					throw runtime_error("no matching constructor");
				return copy_move;
			}
		}
	}
	if (hosted_compatibility_ && hosted_library_namespace_scope(record->scope))
	{
		complete_template_record(record);
		ensure_hosted_pair_constructor(record, args);
		ensure_copy_move_constructor_for_single_arg(record, args);
		map<string, vector<Binding*> >::const_iterator hosted_found =
			record->scope->members.find(record->scope->name);
		if (hosted_found != record->scope->members.end())
		{
			vector<Binding*> ordinary_ctors;
			bool hosted_user_declared = false;
			for (size_t i = 0; i < hosted_found->second.size(); ++i)
			{
				Binding* ctor = hosted_found->second[i];
				if (ctor->kind != BindingKind::Function ||
				    !constructor_binding_for_record(record, ctor))
					continue;
				if (!ctor->is_generated_default_constructor &&
				    !ctor->is_generated_aggregate_constructor &&
				    !ctor->is_generated_copy_move_constructor)
					hosted_user_declared = true;
				if (function_template_placeholders_.find(ctor) !=
					    function_template_placeholders_.end() ||
				    function_template_specialization_arguments_.find(ctor) !=
					    function_template_specialization_arguments_.end() ||
				    (ctor->type.get() != NULL &&
				     type_structurally_dependent(ctor->type)))
					continue;
				ordinary_ctors.push_back(ctor);
			}
			if (!ordinary_ctors.empty())
			{
				Expr ordering_this_arg;
				ordering_this_arg.valid = true;
				ordering_this_arg.type = pa11::make_pointer(record);
				ordering_this_arg.category = ValueCategory::PRValue;
				ordering_this_arg.node =
					Node("id-expression prvalue " +
					     pa11::describe_type(ordering_this_arg.type) +
					     " this");
				vector<Expr> template_order_args;
				template_order_args.push_back(ordering_this_arg);
				template_order_args.insert(template_order_args.end(),
				                           args.begin(),
				                           args.end());
				Binding* hosted_best = NULL;
				vector<int> hosted_best_ranks;
				vector<Expr> hosted_best_args;
				bool hosted_ambiguous = false;
				select_constructor_candidate(record,
				                             args,
				                             copy_initialization,
				                             ordinary_ctors,
				                             hosted_user_declared,
				                             template_order_args,
				                             hosted_best,
				                             hosted_best_ranks,
				                             hosted_best_args,
				                             hosted_ambiguous);
				bool exact = hosted_best != NULL && !hosted_ambiguous;
				for (size_t i = 0; exact && i < hosted_best_ranks.size(); ++i)
					if (hosted_best_ranks[i] != 0)
						exact = false;
				if (exact)
				{
					finalize_constructor_candidate(record, hosted_best);
					converted = hosted_best_args;
					return hosted_best;
				}
			}
		}
	}
	prepare_constructor_template_candidates(record, args);
	ensure_copy_move_constructor_for_single_arg(record, args);
	if (!args.empty() && !record_has_aggregate_blocking_constructor(record))
	{
		validate_aggregate_braced_initialization(record);
		ensure_aggregate_constructor(record, args.size());
		}
				vector<Binding*> constructors =
					constructor_members_for_record(record);
				bool found_zero_arg_constructor = false;
		for (size_t i = 0; i < constructors.size(); ++i)
				if (constructors[i]->kind == BindingKind::Function &&
				    constructor_binding_for_record(record, constructors[i]) &&
				    constructors[i]->type.get() != NULL &&
				    constructors[i]->type->kind == pa11::TypeKind::Function &&
				    constructor_accepts_argument_count(constructors[i], 0))
					found_zero_arg_constructor = true;
		if (!found_zero_arg_constructor && args.empty())
		{
			ensure_default_constructor(record, true);
			constructors = constructor_members_for_record(record);
		}
	if (constructors.empty())
			throw runtime_error("no matching constructor");

	Expr ordering_this_arg;
	ordering_this_arg.valid = true;
	ordering_this_arg.type = pa11::make_pointer(record);
	ordering_this_arg.category = ValueCategory::PRValue;
	ordering_this_arg.node = Node("id-expression prvalue " +
	                              pa11::describe_type(ordering_this_arg.type) +
	                              " this");
	vector<Expr> template_order_args;
	template_order_args.push_back(ordering_this_arg);
	template_order_args.insert(template_order_args.end(),
	                           args.begin(),
	                           args.end());

	bool has_user_declared_constructor = false;
		for (size_t i = 0; i < constructors.size(); ++i)
		{
			Binding* ctor = constructors[i];
		if (ctor->kind == BindingKind::Function &&
		    constructor_binding_for_record(record, ctor) &&
		    !ctor->is_generated_default_constructor &&
		    !ctor->is_generated_aggregate_constructor &&
		    !ctor->is_generated_copy_move_constructor)
			has_user_declared_constructor = true;
	}

	Binding* best = NULL;
	vector<int> best_ranks;
	vector<Expr> best_args;
	bool ambiguous = false;
		select_constructor_candidate(record,
		                             args,
		                             copy_initialization,
		                             constructors,
	                             has_user_declared_constructor,
	                             template_order_args,
	                             best,
	                             best_ranks,
	                             best_args,
	                             ambiguous);
	if (best == NULL || ambiguous)
			use_hosted_allocator_constructor_fallback(record,
		                                          args,
		                                          best,
		                                          best_args,
		                                          ambiguous);
	if (best == NULL || ambiguous)
		throw runtime_error("no matching constructor");
	if (unevaluated_expression_depth_ == 0 &&
	    !constructor_selection_instantiation_can_be_delayed(record, best))
	{
		best = instantiate_selected_constructor_body(best);
		best = wrap_inherited_constructor_if_needed(record, best);
	}
	finalize_constructor_candidate(record, best);
	converted = best_args;
	return best;
}

Expr Parser::make_constructor_list_init_expr(TypePtr type,
                                             const Expr& init,
                                             bool copy_initialization)
{
	TypePtr record = pa11::strip_cv(type);
	if (!init.braced_init_list || init.node.children.empty() ||
	    record->kind != pa11::TypeKind::Record || record->scope == NULL)
	{
		throw runtime_error("no matching constructor");
	}
	vector<Binding*> constructors = constructor_members_for_record(record);
	if (constructors.empty() ||
	    (hosted_compatibility_ &&
	     hosted_library_namespace_scope(record->scope)))
	{
		complete_template_record(record);
		constructors = constructor_members_for_record(record);
	}
	if (constructors.empty())
	{
		throw runtime_error("no matching constructor");
	}
	for (size_t i = 0; i < constructors.size(); ++i)
	{
		Binding* ctor = constructors[i];
		if (ctor->kind != BindingKind::Function ||
		    ctor->type.get() == NULL ||
		    ctor->type->kind != pa11::TypeKind::Function ||
		    ctor->type->parameters.size() < 2 ||
		    !constructor_accepts_argument_count(ctor, 1))
			continue;
		TypePtr param = ctor->type->parameters[1];
		if (pa11::is_reference_type(param))
			param = param->base;
		param = pa11::strip_cv(param);
		if (!is_std_initializer_list_type(param, NULL))
			continue;
		try
		{
			Expr list = make_initializer_list_expr(init, param);
			vector<Expr> args;
			args.push_back(list);
			return make_constructor_init_expr(type,
			                                  args,
			                                  copy_initialization);
		}
		catch (const runtime_error&)
		{
		}
		if (init.node.children.size() != 1 ||
		    init.node.children[0].line.compare(0, 16,
		                                       "braced-init-list") != 0 ||
		    init.node.children[0].type.get() != NULL)
			continue;
		try
		{
			Expr unwrapped;
			unwrapped.valid = true;
			unwrapped.node = init.node.children[0];
			unwrapped.type = unwrapped.node.type;
			unwrapped.category = unwrapped.node.category;
			unwrapped.braced_init_list = true;
			Expr list = make_initializer_list_expr(unwrapped, param);
			vector<Expr> args;
			args.push_back(list);
			return make_constructor_init_expr(type,
			                                  args,
			                                  copy_initialization);
		}
		catch (const runtime_error&)
		{
		}
	}
	throw runtime_error("no matching constructor");
}

Expr Parser::make_constructor_init_expr(TypePtr type,
                                        const vector<Expr>& args,
                                        bool copy_initialization)
{
	vector<Expr> constructor_args;
	for (size_t i = 0; i < args.size(); ++i)
	{
		if (args[i].pack_expansion && !args[i].pack.empty())
			constructor_args.insert(constructor_args.end(), args[i].pack.begin(),
			                        args[i].pack.end());
		else
			constructor_args.push_back(args[i]);
	}
	for (size_t i = 0; i < constructor_args.size(); ++i)
		if (is_lambda_helper_expr(constructor_args[i]))
			constructor_args[i] = lambda_closure_expr(constructor_args[i]);
	TypePtr record = pa11::strip_cv(type);
	bool dependent_constructor_args = false;
	for (size_t i = 0; i < constructor_args.size(); ++i)
		if (type_structurally_dependent(constructor_args[i].type) ||
		    constructor_args[i].pack_expansion)
			dependent_constructor_args = true;
	bool concrete_record =
		record->kind == pa11::TypeKind::Record &&
		record->scope != NULL &&
		!record->is_dependent_typename &&
		!type_structurally_dependent(type);
	if (record->kind == pa11::TypeKind::Record &&
	    ((type_is_template_dependent(type) && !concrete_record) ||
	     dependent_constructor_args))
	{
		Expr out;
		out.valid = true;
		out.type = type;
		out.category = ValueCategory::PRValue;
		out.braced_init_list = true;
		out.copy_initialization = copy_initialization;
		out.node = Node("braced-init-list");
		out.node.type = type;
		out.node.category = out.category;
		for (size_t i = 0; i < constructor_args.size(); ++i)
			add_child(out.node, constructor_args[i].node);
		annotate_expr_node(out);
		return out;
	}
	if (record->kind == pa11::TypeKind::Record &&
	    !constructor_args.empty() &&
	    !record_has_aggregate_blocking_constructor(record))
		complete_aggregate_constructor_args(record, constructor_args);
	vector<Expr> converted;
	Binding* ctor = NULL;
	try
	{
		ctor = resolve_constructor_candidate(type, constructor_args,
		                                     copy_initialization, converted);
	}
	catch (const runtime_error& err)
	{
			if (!no_matching_constructor_error(err) ||
			    copy_initialization ||
			    constructor_args.size() != 1)
				throw;
		++explicit_conversion_context_;
		Conversion conv;
		try
		{
			conv = convert_value(constructor_args[0], type);
		}
		catch (...)
		{
			--explicit_conversion_context_;
			throw;
		}
		--explicit_conversion_context_;
		if (conv.viable)
			return conv.expr;
		throw;
	}
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
	if (ctor != NULL && ctor->is_generated_aggregate_constructor)
		out.node.token_text = "force-constructor";
	if (unevaluated_expression_depth_ == 0)
	{
		if (ctor != NULL &&
		    ctor->is_defaulted &&
		    ctor->type.get() != NULL &&
		    ctor->type->kind == pa11::TypeKind::Function &&
		    ctor->type->parameters.size() == 1)
		{
			Binding* synthesized = ensure_default_constructor(type);
			if (synthesized != NULL)
				ctor = synthesized;
			out.node.direct_call = ctor;
		}
		if (!constructor_body_can_be_delayed(record, ctor))
		{
			parse_pending_member_body(ctor);
			ensure_function_body_extra_node(ctor);
		}
		if (ctor != NULL &&
		    ctor->is_generated_default_constructor &&
		    !ctor->is_inline_definition)
			ensure_default_constructor(type, true);
		if (record->kind == pa11::TypeKind::Record &&
		    !type_is_template_dependent(type))
		{
			bool force_dtor = !pa11::record_direct_bases(record).empty();
			ensure_default_destructor(type, force_dtor);
		}
	}
	for (size_t i = 0; i < converted.size(); ++i)
		add_child(out.node, converted[i].node);
	annotate_expr_node(out);
	out.node.direct_call = ctor;
	return out;
}

}  // namespace internal
}  // namespace pa12
