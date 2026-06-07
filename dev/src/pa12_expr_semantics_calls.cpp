#include "pa12_expr_semantics_support.h"

#include <algorithm>
#include <stdexcept>

using namespace std;

namespace pa12 {
namespace internal {

bool Parser::call_candidate_has_arguments(Binding* fn, size_t arg_count) const
{
	if (arg_count < fn->type->parameters.size())
	{
		map<Binding*, vector<Expr> >::const_iterator dit =
			default_arguments_.find(fn);
		if (dit == default_arguments_.end())
			return false;
		for (size_t j = arg_count; j < fn->type->parameters.size(); ++j)
		{
			if (j >= dit->second.size() || !dit->second[j].valid)
				return false;
		}
	}
	if (!fn->type->variadic && arg_count != fn->type->parameters.size() &&
	    arg_count > fn->type->parameters.size())
		return false;
	return true;
}

bool Parser::instantiate_function_default_argument(Binding* fn,
                                                  const Expr& default_arg,
                                                  TypePtr parameter_type,
                                                  Expr& out)
{
	if (default_arg.source_end <= default_arg.source_begin)
		return false;
	map<Binding*, TemplateDeclaration*>::iterator template_it =
		function_template_placeholders_.find(fn);
	map<Binding*, vector<TemplateArgument> >::iterator args_it =
		function_template_specialization_arguments_.find(fn);
	if (template_it == function_template_placeholders_.end() ||
	    args_it == function_template_specialization_arguments_.end())
		return false;
	TemplateDeclaration* declaration = template_it->second;
	const vector<TemplateArgument>& full_args = args_it->second;

	size_t save_pos = pos_;
	vector<Token> save_tokens = tokens_;
	vector<Scope*> save_scopes = scopes_;
	vector<map<string, TypePtr> > save_subst = template_type_substitutions_;
	vector<map<string, TemplateArgument> > save_value_subst =
		template_value_substitutions_;
	vector<set<string> > save_pack_subst = template_type_parameter_packs_;

	map<string, TypePtr> subst;
	map<string, TemplateArgument> value_subst;
	set<string> pack_subst;
	for (size_t i = 0; i < full_args.size() &&
	     i < declaration->parameters.size(); ++i)
	{
		const TemplateParameterInfo& parameter = declaration->parameters[i];
		if (parameter.name.empty())
			continue;
		if (parameter.kind == TemplateParameterKind::Type)
		{
			if (parameter.is_pack)
			{
				subst[parameter.name] =
					pa11::make_template_parameter_type(parameter.name);
				value_subst[parameter.name] = full_args[i];
				pack_subst.insert(parameter.name);
			}
			else if (full_args[i].kind == TemplateArgumentKind::Type)
				subst[parameter.name] = full_args[i].type;
		}
		else
			value_subst[parameter.name] = full_args[i];
	}

	bool ok = false;
	try
	{
		template_type_substitutions_.insert(
			template_type_substitutions_.end(),
			declaration->outer_type_substitutions.begin(),
			declaration->outer_type_substitutions.end());
		template_value_substitutions_.insert(
			template_value_substitutions_.end(),
			declaration->outer_value_substitutions.begin(),
			declaration->outer_value_substitutions.end());
		template_type_substitutions_.push_back(subst);
		template_value_substitutions_.push_back(value_subst);
		template_type_parameter_packs_.push_back(pack_subst);
		scopes_.clear();
		scopes_.push_back(declaration->lexical_scope != NULL
		                  ? declaration->lexical_scope
		                  : declaration->owner);
		tokens_ = declaration_tokens_;
		pos_ = default_arg.source_begin;
		Expr expr = parse_assignment_expression();
		if (pos_ == default_arg.source_end)
		{
			Conversion conv = convert_to(expr, parameter_type);
			if (conv.viable)
			{
				out = conv.expr;
				ok = true;
			}
			else if (!type_is_template_dependent(expr.type))
			{
				out = expr;
				ok = true;
			}
		}
	}
	catch (const exception&)
	{
		ok = false;
	}

	template_type_substitutions_ = save_subst;
	template_value_substitutions_ = save_value_subst;
	template_type_parameter_packs_ = save_pack_subst;
	scopes_ = save_scopes;
	tokens_ = save_tokens;
	pos_ = save_pos;
	return ok;
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
			{
				Expr default_arg = defaults[j];
				if (default_arg.valid &&
				    type_is_template_dependent(default_arg.type) &&
				    !type_is_template_dependent(fn->type->parameters[j]))
				{
					Expr instantiated;
					if (instantiate_function_default_argument(
						    fn,
						    default_arg,
						    fn->type->parameters[j],
						    instantiated))
						default_arg = instantiated;
					else
					{
						default_arg.type = fn->type->parameters[j];
						annotate_expr_node(default_arg);
					}
				}
				conv_args.push_back(default_arg);
			}
	}
	object_rank = -1;
	for (size_t j = 0; j < fn->type->parameters.size(); ++j)
	{
		bool implicit_object_arg =
			j == 0 &&
			fn->owner != NULL &&
			fn->owner->kind == ScopeKind::Class &&
			!fn->is_static_member;
		Conversion conv;
		bool conversion_failed = false;
		try
		{
			conv = convert_to(conv_args[j], fn->type->parameters[j]);
		}
		catch (const runtime_error&)
		{
			conversion_failed = true;
		}
		if ((conversion_failed || !conv.viable) && implicit_object_arg)
		{
			bool constructor_object_arg =
				fn->owner != NULL &&
				fn->owner->kind == ScopeKind::Class &&
				fn->name == fn->owner->name;
			TypePtr source =
				pa11::strip_cv(lvalue_to_rvalue_type(conv_args[j].type));
			TypePtr target = pa11::strip_cv(fn->type->parameters[j]);
			if (!constructor_object_arg &&
			    source.get() != NULL &&
			    target.get() != NULL &&
			    source->kind == pa11::TypeKind::Pointer &&
			    target->kind == pa11::TypeKind::Pointer &&
			    source->base.get() != NULL &&
			    target->base.get() != NULL &&
			    same_template_specialization_family(source->base,
			                                        target->base))
			{
				Expr converted = conv_args[j];
				converted.type = fn->type->parameters[j];
				converted.category = ValueCategory::PRValue;
				converted.node = Node("cast-expression prvalue " +
				                      pa11::describe_type(converted.type));
				add_child(converted.node, conv_args[j].node);
				annotate_expr_node(converted);
				conv = Conversion(true, 0, converted);
				conversion_failed = false;
			}
		}
		if (conversion_failed || !conv.viable)
			return false;
		bool supplied_arg = j < args.size();
		if (implicit_object_arg)
			object_rank = conv.rank;
		else if (supplied_arg)
			ranks.push_back(conv.rank);
		conv_args[j] = conv.expr;
	}
	return true;
}

Binding* Parser::resolve_call_candidate(const vector<Binding*>& overloads,
                                        const vector<Expr>& args,
                                        const map<Binding*, vector<TemplateArgument> >& explicit_template_arguments,
                                        vector<Expr>& converted)
{
	Binding* best = NULL;
	vector<int> best_ranks;
	vector<Expr> best_args;
	int best_object_rank = 0;
	bool ambiguous = false;
	vector<Binding*> considered;
	set<const void*> remapped_member_template_owners;
	for (size_t i = 0; i < overloads.size(); ++i)
	{
		Binding* fn = overloads[i];
		if (fn == NULL ||
		    fn->owner == NULL ||
		    fn->owner->kind != ScopeKind::Class)
			continue;
		TypePtr owner_record = pa11::record_type_for_scope(fn->owner);
		owner_record = owner_record.get() != NULL
			? pa11::strip_cv(owner_record) : TypePtr();
		if (owner_record.get() == NULL ||
		    owner_record->kind != pa11::TypeKind::Record ||
		    !owner_record->is_template_specialization ||
		    !remapped_member_template_owners.insert(owner_record.get()).second)
			continue;
		instantiate_member_function_templates(owner_record);
	}
	for (size_t i = 0; i < overloads.size(); ++i)
	{
		Binding* fn = overloads[i];
		if (fn != NULL &&
		    fn->is_dependent_template_artifact &&
		    !validating_template_definition_ &&
		    explicit_template_arguments.empty() &&
		    type_is_template_dependent(fn->type))
			continue;
		if (!explicit_template_arguments.empty() &&
		    explicit_template_arguments.find(fn) == explicit_template_arguments.end())
		{
			map<Binding*, TemplateDeclaration*>::const_iterator tit =
				function_template_placeholders_.find(fn);
			Binding* placeholder = fn->aliased_binding != NULL ? fn->aliased_binding : fn;
			bool current_template_placeholder =
				tit != function_template_placeholders_.end() &&
				tit->second->placeholder == placeholder &&
				explicit_template_arguments.find(placeholder) != explicit_template_arguments.end();
			bool explicit_instantiated_specialization =
				function_template_specialization_arguments_.find(fn) !=
				function_template_specialization_arguments_.end();
			if (!current_template_placeholder &&
			    !explicit_instantiated_specialization)
				continue;
		}
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
			TemplateDeclaration* fn_origin =
				function_template_origin(function_template_placeholders_, fn);
			TemplateDeclaration* duplicate_origin =
				function_template_origin(function_template_placeholders_,
				                         duplicate);
				if (fn_template && duplicate_template &&
				    fn_origin != duplicate_origin &&
				    !same_function_template_declaration_family(
					    fn_origin,
					    duplicate_origin) &&
				    !function_template_more_specialized(
					    function_template_placeholders_,
				    fn,
				    duplicate) &&
			    !function_template_more_specialized(
				    function_template_placeholders_,
				    duplicate,
				    fn))
				duplicate = NULL;
		}
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
			         function_template_more_specialized_for_call(
				         function_template_placeholders_,
				         fn,
				         best,
				         args.size()))
				better = true;
			else if (fn_template == best_template &&
			         function_template_fewer_forwarding_lvalue_parameters_for_call(
				         function_template_placeholders_,
				         fn,
				         best,
				         args))
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
				         function_template_more_specialized_for_call(
					         function_template_placeholders_,
					         best,
					         fn,
					         args.size()))
					indistinguishable = false;
				else if (object_rank == best_object_rank &&
				         function_template_fewer_forwarding_lvalue_parameters_for_call(
					         function_template_placeholders_,
					         best,
					         fn,
					         args))
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
		throw runtime_error("cannot resolve call overload " + detail);
	}
	if (best != NULL &&
	    best->owner != NULL &&
	    best->owner->kind == ScopeKind::Class)
	{
		TypePtr owner_record = pa11::record_type_for_scope(best->owner);
		owner_record = owner_record.get() != NULL
			? pa11::strip_cv(owner_record) : TypePtr();
		if (owner_record.get() != NULL &&
		    owner_record->kind == pa11::TypeKind::Record &&
		    owner_record->is_template_specialization)
			instantiate_member_function_templates(owner_record);
	}
	if (best != NULL && unevaluated_expression_depth_ == 0)
		mark_template_specialization_demanded(best->type);
	converted = best_args;
	if (best != NULL &&
	    unevaluated_expression_depth_ == 0 &&
	    (!best->is_inline_definition ||
	     function_bodies_.find(best) == function_bodies_.end()))
	{
		map<Binding*, TemplateDeclaration*>::iterator template_it =
			function_template_placeholders_.find(best);
		map<Binding*, vector<TemplateArgument> >::iterator args_it =
			function_template_specialization_arguments_.find(best);
		bool selected_dependent_return =
			best->type.get() != NULL &&
			best->type->kind == pa11::TypeKind::Function &&
			type_is_template_dependent(best->type->base);
		TemplateDeclaration* replay_declaration =
			template_it != function_template_placeholders_.end()
			? template_it->second : NULL;
		if (replay_declaration != NULL &&
		    !template_declaration_has_body(tokens_, replay_declaration))
		{
			TemplateDeclaration* compatible_body = NULL;
			for (map<Scope*, map<string, vector<TemplateDeclaration*> > >::iterator
				     sit = function_templates_.begin();
			     sit != function_templates_.end(); ++sit)
			{
				map<string, vector<TemplateDeclaration*> >::iterator nit =
					sit->second.find(replay_declaration->name);
				if (nit == sit->second.end())
					continue;
				for (size_t di = 0; di < nit->second.size(); ++di)
				{
					TemplateDeclaration* candidate = nit->second[di];
					if (candidate == replay_declaration ||
					    !template_declaration_has_body(tokens_, candidate) ||
					    candidate->generic_function_type.get() == NULL ||
					    !expr_template_parameter_lists_match(
						    candidate->parameters,
						    replay_declaration->parameters))
						continue;
					if (compatible_body == NULL)
						compatible_body = candidate;
					if (!same_template_signature_type(
						    candidate->generic_function_type,
						    replay_declaration->generic_function_type))
						continue;
					if (replay_declaration->class_template_member &&
					    !candidate->class_template_member)
						continue;
					replay_declaration = candidate;
					break;
				}
				if (template_declaration_has_body(tokens_,
				                                  replay_declaration))
					break;
			}
			if (!template_declaration_has_body(tokens_,
			                                   replay_declaration) &&
			    compatible_body != NULL)
			{
				unique_ptr<TemplateDeclaration> clone(
					new TemplateDeclaration(*compatible_body));
				clone->owner = replay_declaration->owner;
				clone->placeholder = replay_declaration->placeholder;
				clone->class_template_member =
					replay_declaration->class_template_member;
				clone->outer_type_substitutions =
					replay_declaration->outer_type_substitutions;
				clone->outer_value_substitutions =
					replay_declaration->outer_value_substitutions;
				clone->function_specializations.clear();
				clone->completing_specializations.clear();
				TemplateDeclaration* clone_ptr = clone.get();
				template_declarations_.push_back(std::move(clone));
				replay_declaration = clone_ptr;
			}
		}
		if (template_it != function_template_placeholders_.end() &&
		    args_it != function_template_specialization_arguments_.end() &&
		    (template_declaration_has_body(tokens_, replay_declaration) ||
		     selected_dependent_return))
		{
			vector<TemplateArgument> selected_args = args_it->second;
			if (selected_args.size() <
			    replay_declaration->parameters.size())
			{
				++function_template_candidate_instantiation_depth_;
				try
				{
					selected_args =
						complete_template_arguments(replay_declaration,
						                            selected_args);
				}
				catch (...)
				{
					--function_template_candidate_instantiation_depth_;
					throw;
				}
				--function_template_candidate_instantiation_depth_;
			}
			Binding* instantiated =
				instantiate_function_template(replay_declaration,
				                              selected_args);
			if (instantiated != NULL)
			{
				if (best != instantiated)
					best->aliased_binding = instantiated;
				best = instantiated;
			}
		}
	}
	if (best != NULL &&
	    unevaluated_expression_depth_ == 0 &&
	    function_template_candidate_instantiation_depth_ == 0)
	{
		parse_pending_function_body(best);
		parse_pending_member_body(best);
		ensure_function_body_extra_node(best);
	}
	return canonical_function_binding(best);
}

Binding* Parser::instantiate_template_call_candidate(
	Binding* fn,
	const map<Binding*, vector<TemplateArgument> >& explicit_template_arguments,
	const vector<Expr>& args)
{
	Binding* placeholder = fn->aliased_binding != NULL ? fn->aliased_binding : fn;
	map<Binding*, TemplateDeclaration*>::iterator template_it =
		function_template_placeholders_.find(fn);
	if (template_it == function_template_placeholders_.end() &&
	    placeholder != fn)
		template_it = function_template_placeholders_.find(placeholder);
	if (template_it == function_template_placeholders_.end())
		return fn;
	bool call_has_explicit_args =
		explicit_template_arguments.find(fn) !=
			explicit_template_arguments.end() ||
		(placeholder != fn &&
		 explicit_template_arguments.find(placeholder) !=
			 explicit_template_arguments.end());
	if (function_template_specialization_arguments_.find(fn) !=
	        function_template_specialization_arguments_.end() &&
	    !type_is_template_dependent(fn->type) &&
	    !call_has_explicit_args)
		return fn;
	TemplateDeclaration* original_declaration = template_it->second;
	bool placeholder_candidate = original_declaration->placeholder == placeholder;
	bool specialization_candidate = original_declaration->placeholder != NULL &&
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
					    !same_template_signature_type(candidate->generic_function_type, declaration->generic_function_type) ||
					    !expr_template_parameter_lists_match(candidate->parameters, declaration->parameters))
						continue;
					declaration = candidate;
					break;
				}
			}
		}
	}
	vector<TemplateArgument> explicit_args;
	map<Binding*, vector<TemplateArgument> >::const_iterator eit =
		explicit_template_arguments.find(fn);
	if (eit == explicit_template_arguments.end() && placeholder != fn)
		eit = explicit_template_arguments.find(placeholder);
	if (eit == explicit_template_arguments.end() && original_declaration->placeholder != NULL)
		eit = explicit_template_arguments.find(original_declaration->placeholder);
	bool have_call_explicit_args = eit != explicit_template_arguments.end();
	if (eit != explicit_template_arguments.end())
		explicit_args = eit->second;
	else
	{
		map<Binding*, vector<TemplateArgument> >::const_iterator stored =
			function_template_specialization_arguments_.find(fn);
		if (stored != function_template_specialization_arguments_.end())
			explicit_args = stored->second;
	}
	if (!type_is_template_dependent(fn->type) &&
	    explicit_args.empty() &&
	    !template_declaration_has_body(tokens_, declaration))
		return canonical_function_binding(fn);
	if (specialization_candidate && !placeholder_candidate &&
	    declaration == original_declaration &&
	    !have_call_explicit_args &&
	    explicit_args.empty())
		return explicit_template_arguments.empty()
			? canonical_function_binding(fn) : NULL;
	vector<TemplateArgument> deduced;
	bool deduction_depth_entered = false;
		try
		{
			++function_template_candidate_instantiation_depth_;
			deduction_depth_entered = true;
			if (!deduce_function_template_arguments(declaration,
			                                       args,
			                                       explicit_args,
			                                       deduced))
			{
				--function_template_candidate_instantiation_depth_;
				deduction_depth_entered = false;
				return NULL;
			}
		--function_template_candidate_instantiation_depth_;
		deduction_depth_entered = false;
		}
		catch (const runtime_error&)
		{
			if (deduction_depth_entered)
				--function_template_candidate_instantiation_depth_;
			return NULL;
		}
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
	bool candidate_depth_entered = false;
		try
		{
			++function_template_candidate_instantiation_depth_;
			candidate_depth_entered = true;
			Binding* instantiated;
			instantiated =
				instantiate_function_template(declaration, deduced);
			--function_template_candidate_instantiation_depth_;
		candidate_depth_entered = false;
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
		if (candidate_depth_entered)
			--function_template_candidate_instantiation_depth_;
		declaration->friend_class_scope = saved_friend_class_scope;
		return NULL;
	}
}

}  // namespace internal
}  // namespace pa12
