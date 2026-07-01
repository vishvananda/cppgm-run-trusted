#include "pa12_expr_semantics_support.h"
#include "pa12_templates_instance_support.h"
#include "pa12_types_support.h"

#include <algorithm>
#include <stdexcept>

using namespace std;

namespace pa12 {
namespace internal {

Binding* Parser::find_duplicate_constructor_candidate(
	Binding* ctor,
	const vector<Binding*>& considered)
{
	for (size_t j = 0; j < considered.size(); ++j)
		if (pa11::same_type(considered[j]->type, ctor->type))
		{
			Binding* duplicate = considered[j];
			bool ctor_template =
				function_template_placeholders_.find(ctor) !=
				function_template_placeholders_.end();
			bool duplicate_template =
				function_template_placeholders_.find(duplicate) !=
				function_template_placeholders_.end();
			TemplateDeclaration* ctor_origin =
				function_template_origin(function_template_placeholders_, ctor);
			TemplateDeclaration* duplicate_origin =
				function_template_origin(function_template_placeholders_,
				                         duplicate);
			if (ctor_template && duplicate_template &&
			    ctor_origin != duplicate_origin &&
			    !same_function_template_declaration_family(ctor_origin,
			                                               duplicate_origin) &&
			    !function_template_more_specialized(
				    function_template_placeholders_, ctor, duplicate) &&
			    !function_template_more_specialized(
				    function_template_placeholders_, duplicate, ctor))
				duplicate = NULL;
			if (duplicate != NULL)
				return duplicate;
		}
	return NULL;
}

bool Parser::should_replace_duplicate_constructor(Binding* ctor,
                                                  Binding* duplicate)
{
	bool ctor_template =
		function_template_placeholders_.find(ctor) !=
		function_template_placeholders_.end();
	bool duplicate_template =
		function_template_placeholders_.find(duplicate) !=
		function_template_placeholders_.end();
	bool replace_duplicate = !ctor_template && duplicate_template;
	if (!replace_duplicate && ctor_template && !duplicate_template)
		return false;
	if (!replace_duplicate && ctor_template && duplicate_template &&
	    ctor->type.get() != NULL &&
	    duplicate->type.get() != NULL &&
	    !type_structurally_dependent(ctor->type) &&
	    type_structurally_dependent(duplicate->type))
		replace_duplicate = true;
	if (!replace_duplicate)
		replace_duplicate =
			ctor->is_inline_definition && !duplicate->is_inline_definition;
	if (!replace_duplicate &&
	    function_template_more_specialized(function_template_placeholders_,
	                                       ctor,
	                                       duplicate))
		replace_duplicate = true;
	return replace_duplicate;
}

	bool Parser::convert_constructor_candidate_arguments(
		Binding* ctor,
		const vector<Expr>& args,
		vector<Expr>& conv_args,
		vector<int>& ranks,
		map<pair<size_t, const void*>, Conversion>& conversion_cache)
{
	size_t param_count = ctor->type->parameters.size() - 1;
	conv_args = args;
	size_t fixed_count = args.size() < param_count ? args.size() : param_count;
		for (size_t j = 0; j < fixed_count; ++j)
		{
			TypePtr param = ctor->type->parameters[j + 1];
			if (pa11::is_reference_type(param))
			{
				TypePtr owner_record = ctor->owner != NULL &&
					ctor->owner->kind == ScopeKind::Class
					? pa11::strip_cv(pa11::record_type_for_scope(ctor->owner))
					: TypePtr();
				TypePtr param_record = pa11::strip_cv(param->base);
				if (owner_record.get() != NULL &&
				    owner_record->kind == pa11::TypeKind::Record &&
				    param_record->kind == pa11::TypeKind::Record &&
				    same_template_specialization_record(owner_record, param_record))
				{
					if (args[j].type.get() == NULL)
						return false;
					TypePtr source_record =
						pa11::strip_cv(expression_object_type(args[j].type));
					bool source_related =
						source_record.get() != NULL &&
						source_record->kind == pa11::TypeKind::Record &&
						(same_template_specialization_record(source_record,
						                                     param_record) ||
						 record_base_distance(source_record, param_record) <
							 1000000);
					if (!source_related)
					{
						if (source_record.get() == NULL ||
						    source_record->kind != pa11::TypeKind::Record ||
						    source_record->scope == NULL)
							return false;
						if (!type_is_template_dependent(source_record))
							instantiate_member_function_templates(source_record);
						set<Scope*> seen_conversions;
						if (!record_has_conversion_function_candidate(
							    source_record,
							    seen_conversions))
							return false;
					}
				}
				}
				Conversion conv;
					pair<size_t, const void*> cache_key(j, param.get());
					map<pair<size_t, const void*>, Conversion>::iterator cached =
						conversion_cache.find(cache_key);
				if (cached != conversion_cache.end())
					conv = cached->second;
				else
				{
					try
					{
						conv = convert_to(args[j], param);
					}
					catch (const runtime_error&)
					{
						conversion_cache[cache_key] = Conversion();
						return false;
					}
					conversion_cache[cache_key] = conv;
			}
			if (!conv.viable)
				return false;
		ranks.push_back(conv.rank);
		conv_args[j] = conv.expr;
	}
	for (size_t j = param_count; j < args.size(); ++j)
		ranks.push_back(100);
	if (args.size() < param_count)
	{
		const vector<Expr>& defaults = default_arguments_[ctor];
		for (size_t j = args.size() + 1;
		     j < ctor->type->parameters.size();
		     ++j)
			conv_args.push_back(defaults[j]);
	}
	return true;
}

bool Parser::constructor_candidate_better(
	Binding* ctor,
	Binding* best,
	const vector<int>& ranks,
	const vector<int>& best_ranks,
	const vector<Expr>& template_order_args)
{
	bool ctor_template =
		function_template_placeholders_.find(ctor) !=
			function_template_placeholders_.end() ||
		function_template_specialization_arguments_.find(ctor) !=
			function_template_specialization_arguments_.end();
	bool best_template =
		best != NULL &&
		(function_template_placeholders_.find(best) !=
			function_template_placeholders_.end() ||
		 function_template_specialization_arguments_.find(best) !=
			function_template_specialization_arguments_.end());
	bool ctor_inherited_template =
		inherited_constructor_template_candidate(
			function_template_placeholders_,
			ctor);
	bool best_inherited_template =
		inherited_constructor_template_candidate(
			function_template_placeholders_,
			best);
	if (best != NULL &&
	    ctor_template &&
	    !best_template &&
	    exact_copy_reference_constructor_for_order_args(best,
	                                                   template_order_args) &&
	    ranks_equal_allowing_copy_reference_rank(best_ranks, ranks))
		return false;
	if (best == NULL || ranks_better(ranks, best_ranks))
		return true;
	if (ranks != best_ranks)
	{
		if (!ctor_template &&
		    best_template &&
		    exact_copy_reference_constructor_for_order_args(ctor,
		                                                   template_order_args) &&
		    ranks_equal_allowing_copy_reference_rank(ranks, best_ranks))
			return true;
		return false;
	}
	if (ctor_inherited_template != best_inherited_template)
		return ctor_inherited_template;
	if (!ctor_template && best_template)
		return true;
	if (ctor_template != best_template)
		return false;
	return function_template_more_specialized_for_call(
			function_template_placeholders_, ctor, best, template_order_args.size()) ||
		function_template_fewer_forwarding_lvalue_parameters_for_call(
			function_template_placeholders_, ctor, best, template_order_args);
}

bool Parser::constructor_candidate_ambiguous(
	Binding* ctor,
	Binding* best,
	const vector<int>& ranks,
	const vector<int>& best_ranks,
	const vector<Expr>& template_order_args)
{
	if (best == NULL || ranks_better(best_ranks, ranks))
		return false;
	bool ctor_template =
		function_template_placeholders_.find(ctor) !=
			function_template_placeholders_.end() ||
		function_template_specialization_arguments_.find(ctor) !=
			function_template_specialization_arguments_.end();
	bool best_template =
		function_template_placeholders_.find(best) !=
			function_template_placeholders_.end() ||
		function_template_specialization_arguments_.find(best) !=
			function_template_specialization_arguments_.end();
	if (!best_template && ctor_template)
		return false;
	if (best_template != ctor_template)
		return true;
	if (function_template_more_specialized_for_call(
		    function_template_placeholders_, best, ctor, template_order_args.size()))
		return false;
	if (function_template_fewer_forwarding_lvalue_parameters_for_call(
		    function_template_placeholders_, best, ctor, template_order_args))
		return false;
	return true;
}

void Parser::select_constructor_candidate(
	TypePtr record,
	const vector<Expr>& args,
	bool copy_initialization,
	const vector<Binding*>& constructors,
	bool has_user_declared_constructor,
	const vector<Expr>& template_order_args,
	Binding*& best,
	vector<int>& best_ranks,
	vector<Expr>& best_args,
	bool& ambiguous)
{
	vector<Binding*> considered;
	map<pair<size_t, const void*>, Conversion> conversion_cache;
	for (size_t i = 0; i < constructors.size(); ++i)
	{
		Binding* ctor = constructors[i];
		if (has_user_declared_constructor &&
		    ctor->is_generated_default_constructor &&
		    !ctor->is_defaulted)
			continue;
		ctor = instantiate_constructor_template_candidate(record, ctor, args);
		if (ctor == NULL)
			continue;
		if (!constructor_binding_for_record(record, ctor))
			continue;
		if (active_function_matches(ctor))
			continue;
		if (ctor->kind != BindingKind::Function ||
		    ctor->type->kind != pa11::TypeKind::Function ||
		    ctor->type->parameters.empty())
			continue;
		Binding* duplicate =
			find_duplicate_constructor_candidate(ctor, considered);
		if (duplicate != NULL)
		{
			if (!should_replace_duplicate_constructor(ctor, duplicate))
			{
				bool ctor_template =
					function_template_placeholders_.find(ctor) !=
					function_template_placeholders_.end();
				bool duplicate_template =
					function_template_placeholders_.find(duplicate) !=
					function_template_placeholders_.end();
				if (ctor_template && !duplicate_template)
					continue;
				map<Binding*, TemplateDeclaration*>::iterator templ =
					function_template_placeholders_.find(ctor);
				map<Binding*, vector<TemplateArgument> >::iterator args_it =
					function_template_specialization_arguments_.find(ctor);
				if (templ != function_template_placeholders_.end() &&
				    function_template_placeholders_.find(duplicate) ==
					    function_template_placeholders_.end())
					function_template_placeholders_[duplicate] =
						templ->second;
				if (args_it !=
					    function_template_specialization_arguments_.end() &&
				    function_template_specialization_arguments_.find(duplicate) ==
					    function_template_specialization_arguments_.end())
					function_template_specialization_arguments_[duplicate] =
						args_it->second;
				if (duplicate->function_specialization_symbol.empty())
					duplicate->function_specialization_symbol =
						ctor->function_specialization_symbol;
				if (ctor->is_inline_definition)
					duplicate->is_inline_definition = true;
				if (default_arguments_.find(duplicate) ==
				    default_arguments_.end())
				{
						map<Binding*, vector<Expr> >::const_iterator defaults =
							default_arguments_.find(ctor);
						if (defaults != default_arguments_.end())
							default_arguments_[duplicate] =
								default_arguments_for_binding(duplicate,
								                              defaults->second);
					}
					if (function_parameter_names_.find(duplicate) ==
				    function_parameter_names_.end())
				{
					map<Binding*, vector<string> >::const_iterator names =
						function_parameter_names_.find(ctor);
					if (names != function_parameter_names_.end())
						function_parameter_names_[duplicate] = names->second;
				}
				continue;
			}
			considered.erase(find(considered.begin(),
			                      considered.end(),
			                      duplicate));
		}
		considered.push_back(ctor);
		if (copy_initialization && ctor->is_explicit)
			continue;
		if (!constructor_accepts_argument_count(ctor, args.size()))
			continue;
		vector<int> ranks;
		vector<Expr> conv_args;
				if (!convert_constructor_candidate_arguments(ctor,
				                                             args,
				                                             conv_args,
				                                             ranks,
				                                             conversion_cache))
					continue;
		if (constructor_candidate_better(ctor,
		                                 best,
		                                 ranks,
		                                 best_ranks,
		                                 template_order_args))
		{
			best = ctor;
			best_ranks = ranks;
			best_args = conv_args;
			ambiguous = false;
		}
		else if (best != NULL && pa11::same_type(best->type, ctor->type))
		{
			if (ctor->is_inline_definition && !best->is_inline_definition)
			{
				best = ctor;
				best_args = conv_args;
				ambiguous = false;
			}
		}
		else if (constructor_candidate_ambiguous(ctor,
		                                        best,
		                                        ranks,
		                                        best_ranks,
		                                        template_order_args))
			ambiguous = true;
	}
}

}  // namespace internal
}  // namespace pa12
