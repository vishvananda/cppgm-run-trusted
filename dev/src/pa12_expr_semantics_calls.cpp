#include "pa12_expr_semantics_support.h"
#include "pa12_templates_function_support.h"
#include "pa12_templates_instance_support.h"
#include "pa12_types_support.h"

#include <algorithm>
#include <stdexcept>

using namespace std;

namespace pa12 {
namespace internal {

size_t dependent_cache_template_argument_identity(
	const TemplateArgument& argument,
	int depth);
bool same_parameter_family_ignoring_pointer_cv(TypePtr left, TypePtr right);
bool unresolved_enable_if_typename(TypePtr type);
bool same_overload_parameter_signature(TypePtr left, TypePtr right);
bool function_template_candidate_binding(
	Binding* binding,
	const map<Binding*, TemplateDeclaration*>& placeholders,
	const map<Binding*, vector<TemplateArgument> >& specializations);
bool same_function_specialization_symbol(Binding* left, Binding* right);
int reference_binding_tie_break(Binding* candidate,
                                const vector<Expr>& candidate_args,
                                Binding* current,
                                const vector<Expr>& current_args);

int Parser::explicit_template_argument_match_score(
	Binding* fn,
	const map<Binding*, vector<TemplateArgument> >& explicit_template_arguments) const
	{
		if (fn == NULL || explicit_template_arguments.empty())
			return 0;
		Binding* placeholder = fn->aliased_binding != NULL ? fn->aliased_binding : fn;
		map<Binding*, vector<TemplateArgument> >::const_iterator explicit_it =
			explicit_template_arguments.find(fn);
		if (explicit_it == explicit_template_arguments.end() &&
		    placeholder != fn)
			explicit_it = explicit_template_arguments.find(placeholder);
		map<Binding*, TemplateDeclaration*>::const_iterator template_it =
			function_template_placeholders_.find(fn);
		if (template_it == function_template_placeholders_.end() &&
		    placeholder != fn)
			template_it = function_template_placeholders_.find(placeholder);
		if (explicit_it == explicit_template_arguments.end() &&
		    template_it != function_template_placeholders_.end() &&
		    template_it->second->placeholder != NULL)
			explicit_it =
				explicit_template_arguments.find(template_it->second->placeholder);
		if (explicit_it == explicit_template_arguments.end())
			return 0;
		map<Binding*, vector<TemplateArgument> >::const_iterator stored_it =
			function_template_specialization_arguments_.find(fn);
		if (stored_it == function_template_specialization_arguments_.end() &&
		    placeholder != fn)
			stored_it = function_template_specialization_arguments_.find(placeholder);
		if (stored_it == function_template_specialization_arguments_.end())
			return 0;
		const vector<TemplateArgument>& explicit_args = explicit_it->second;
		const vector<TemplateArgument>& stored_args = stored_it->second;
		int score = 0;
		for (size_t i = 0; i < explicit_args.size() &&
		     i < stored_args.size(); ++i)
		{
			vector<TemplateArgument> left(1, explicit_args[i]);
			vector<TemplateArgument> right(1, stored_args[i]);
			if (template_argument_key(left) != template_argument_key(right))
				break;
			++score;
	}
	return score;
}

struct CallResolver
{
	typedef pair<Binding*, Binding*> BindingAliasKey;
	typedef pair<bool, size_t> CandidateBucketKey;
	typedef pair<CandidateBucketKey, const void*> CandidateExactKey;

	Parser& p;
	const vector<Binding*>& overloads;
	const vector<Expr>& args;
	const map<Binding*, vector<TemplateArgument> >& explicit_args;
	Binding* best;
	vector<int> best_ranks;
	vector<Expr> best_args;
	int best_object_rank;
	bool ambiguous;
	bool saw_bad_arity;
	bool saw_conversion_failure;
	vector<Binding*> considered;
	map<const void*, bool> binding_type_dependency_cache;
	map<BindingAliasKey, bool> function_template_candidate_cache;
	map<BindingAliasKey, TemplateDeclaration*> function_template_origin_cache;
		map<CandidateBucketKey, vector<Binding*> > considered_candidate_buckets;
		map<CandidateBucketKey, vector<Binding*> > considered_dependent_candidate_buckets;
		map<CandidateExactKey, vector<Binding*> > considered_exact_candidate_buckets;
		map<pair<size_t, const void*>, Conversion> conversion_cache;

	CallResolver(
		Parser& parser,
		const vector<Binding*>& overload_set,
		const vector<Expr>& call_args,
		const map<Binding*, vector<TemplateArgument> >& explicit_template_args)
	  : p(parser), overloads(overload_set), args(call_args),
	    explicit_args(explicit_template_args), best(NULL),
	    best_object_rank(0), ambiguous(false),
	    saw_bad_arity(false), saw_conversion_failure(false)
	{
	}

	bool binding_type_structurally_dependent(Binding* binding)
	{
		if (binding == NULL || binding->type.get() == NULL)
			return false;
		const void* key = binding->type.get();
		map<const void*, bool>::const_iterator found =
			binding_type_dependency_cache.find(key);
		if (found != binding_type_dependency_cache.end())
			return found->second;
		bool dependent = type_structurally_dependent(binding->type);
		binding_type_dependency_cache[key] = dependent;
		return dependent;
	}

	bool binding_is_function_template_candidate(Binding* binding)
	{
		if (binding == NULL)
			return false;
		BindingAliasKey key = make_pair(binding, binding->aliased_binding);
		map<BindingAliasKey, bool>::const_iterator found =
			function_template_candidate_cache.find(key);
		if (found != function_template_candidate_cache.end())
			return found->second;
		bool value = function_template_candidate_binding(
			binding, p.function_template_placeholders_,
			p.function_template_specialization_arguments_);
		function_template_candidate_cache[key] = value;
		return value;
	}

	TemplateDeclaration* binding_function_template_origin(Binding* binding)
	{
		if (binding == NULL)
			return NULL;
		BindingAliasKey key = make_pair(binding, binding->aliased_binding);
		map<BindingAliasKey, TemplateDeclaration*>::const_iterator found =
			function_template_origin_cache.find(key);
		if (found != function_template_origin_cache.end())
			return found->second;
		size_t generation = p.function_template_placeholders_.size();
		map<BindingAliasKey,
		    pair<size_t, TemplateDeclaration*> >::const_iterator parser_found =
			p.function_template_origin_cache_.find(key);
		if (parser_found != p.function_template_origin_cache_.end() &&
		    parser_found->second.first == generation)
		{
			function_template_origin_cache[key] =
				parser_found->second.second;
			return parser_found->second.second;
		}
		TemplateDeclaration* origin =
			function_template_origin(p.function_template_placeholders_, binding);
		function_template_origin_cache[key] = origin;
		p.function_template_origin_cache_[key] = make_pair(generation, origin);
		return origin;
	}

	bool binding_template_origins_distinct(Binding* left, Binding* right)
	{
		TemplateDeclaration* left_origin =
			binding_function_template_origin(left);
		TemplateDeclaration* right_origin =
			binding_function_template_origin(right);
		return left_origin != NULL &&
		       right_origin != NULL &&
		       left_origin != right_origin &&
		       !same_function_template_declaration_family(left_origin,
		                                                  right_origin);
	}

	static CandidateBucketKey candidate_bucket_key(Binding* binding)
	{
		size_t arity = static_cast<size_t>(-1);
		if (binding != NULL &&
		    binding->type.get() != NULL &&
		    binding->type->kind == pa11::TypeKind::Function)
			arity = binding->type->parameters.size();
		return make_pair(binding != NULL && binding->is_static_member, arity);
	}

	CandidateExactKey candidate_exact_key(Binding* binding)
	{
		return make_pair(candidate_bucket_key(binding),
		                 binding != NULL ? binding->type.get() : NULL);
	}

	Binding* find_duplicate_candidate(Binding* candidate)
	{
		CandidateExactKey exact_key = candidate_exact_key(candidate);
		map<CandidateExactKey, vector<Binding*> >::const_iterator exact =
			considered_exact_candidate_buckets.find(exact_key);
		if (exact != considered_exact_candidate_buckets.end())
		{
			Binding* duplicate =
				duplicate_function_candidate(exact->second, candidate);
			if (duplicate != NULL)
				return duplicate;
		}
		CandidateBucketKey key = candidate_bucket_key(candidate);
		bool candidate_dependent =
			binding_type_structurally_dependent(candidate);
		map<CandidateBucketKey, vector<Binding*> >::const_iterator found =
			candidate_dependent
			? considered_candidate_buckets.find(key)
			: considered_dependent_candidate_buckets.find(key);
		map<CandidateBucketKey, vector<Binding*> >::const_iterator end =
			candidate_dependent
			? considered_candidate_buckets.end()
			: considered_dependent_candidate_buckets.end();
		if (found == end)
			return NULL;
		return duplicate_function_candidate(found->second, candidate);
	}

	void erase_from_bucket(vector<Binding*>& bucket, Binding* binding)
	{
		vector<Binding*>::iterator pos =
			find(bucket.begin(), bucket.end(), binding);
		if (pos != bucket.end())
			bucket.erase(pos);
	}

	bool erase_considered_candidate(Binding* binding)
	{
		vector<Binding*>::iterator pos =
			find(considered.begin(), considered.end(), binding);
		if (pos == considered.end())
			return false;
		considered.erase(pos);
		CandidateBucketKey key = candidate_bucket_key(binding);
		map<CandidateBucketKey, vector<Binding*> >::iterator found =
			considered_candidate_buckets.find(key);
		if (found != considered_candidate_buckets.end())
			erase_from_bucket(found->second, binding);
		map<CandidateBucketKey, vector<Binding*> >::iterator dep_found =
			considered_dependent_candidate_buckets.find(key);
		if (dep_found != considered_dependent_candidate_buckets.end())
			erase_from_bucket(dep_found->second, binding);
		CandidateExactKey exact_key = candidate_exact_key(binding);
		map<CandidateExactKey, vector<Binding*> >::iterator exact =
			considered_exact_candidate_buckets.find(exact_key);
		if (exact != considered_exact_candidate_buckets.end())
			erase_from_bucket(exact->second, binding);
		return true;
	}

	void add_considered_candidate(Binding* binding)
	{
		considered.push_back(binding);
		considered_candidate_buckets[
			candidate_bucket_key(binding)].push_back(binding);
		if (binding_type_structurally_dependent(binding))
			considered_dependent_candidate_buckets[
				candidate_bucket_key(binding)].push_back(binding);
		considered_exact_candidate_buckets[
			candidate_exact_key(binding)].push_back(binding);
	}

	void instantiate_member_template_owners()
	{
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
			p.instantiate_member_function_templates(owner_record);
		}
		}

		bool explicit_instantiated_specialization_allows(Binding* fn)
		{
			map<Binding*, vector<TemplateArgument> >::const_iterator stored =
				p.function_template_specialization_arguments_.find(fn);
			if (stored == p.function_template_specialization_arguments_.end() &&
			    fn != NULL && fn->aliased_binding != NULL)
				stored = p.function_template_specialization_arguments_.find(
					fn->aliased_binding);
			if (stored == p.function_template_specialization_arguments_.end())
				return false;
			TemplateDeclaration* declaration =
				binding_function_template_origin(fn);
			if (declaration == NULL)
				return false;
			map<Binding*, vector<TemplateArgument> >::const_iterator explicit_it =
				explicit_args.find(fn);
			if (explicit_it == explicit_args.end() && fn->aliased_binding != NULL)
				explicit_it = explicit_args.find(fn->aliased_binding);
			if (explicit_it == explicit_args.end() &&
			    declaration->placeholder != NULL)
				explicit_it = explicit_args.find(declaration->placeholder);
			if (explicit_it == explicit_args.end())
				return false;
			vector<TemplateArgument> full_args;
			bool entered = false;
			try
			{
				++p.function_template_candidate_instantiation_depth_;
				entered = true;
				full_args = p.complete_template_arguments(declaration,
				                                          explicit_it->second);
				--p.function_template_candidate_instantiation_depth_;
				entered = false;
			}
			catch (const runtime_error&)
			{
				if (entered)
					--p.function_template_candidate_instantiation_depth_;
				return false;
			}
			vector<TemplateArgument> explicit_compare =
				flatten_template_argument_packs(full_args);
			vector<TemplateArgument> stored_compare =
				flatten_template_argument_packs(stored->second);
			if (explicit_compare.size() > stored_compare.size())
				return false;
			for (size_t i = 0; i < explicit_compare.size(); ++i)
				if (dependent_cache_template_argument_identity(
					    explicit_compare[i],
					    0) !=
				    dependent_cache_template_argument_identity(
					    stored_compare[i],
					    0))
					return false;
			return true;
		}

		bool explicit_arguments_allow(Binding* fn)
		{
			if (explicit_args.empty() ||
			    explicit_args.find(fn) != explicit_args.end())
			return true;
		map<Binding*, TemplateDeclaration*>::const_iterator tit =
			p.function_template_placeholders_.find(fn);
		Binding* placeholder =
			fn->aliased_binding != NULL ? fn->aliased_binding : fn;
		bool current_template_placeholder =
			tit != p.function_template_placeholders_.end() &&
			tit->second->placeholder == placeholder &&
			explicit_args.find(placeholder) != explicit_args.end();
			bool explicit_instantiated_specialization =
				p.function_template_specialization_arguments_.find(fn) !=
				p.function_template_specialization_arguments_.end();
			return current_template_placeholder ||
			       (explicit_instantiated_specialization &&
			        explicit_instantiated_specialization_allows(fn));
		}

	Binding* instantiate_candidate(Binding* fn)
	{
		if (fn != NULL &&
		    fn->is_dependent_template_artifact &&
		    !p.validating_template_definition_ &&
		    explicit_args.empty() &&
		    p.type_is_template_dependent(fn->type))
			return NULL;
		if (!explicit_arguments_allow(fn))
			return NULL;
		return p.instantiate_template_call_candidate(fn, explicit_args, args);
	}

	struct TemplateSubstitutionScope
	{
		Parser& p;
		vector<map<string, TypePtr> > saved_types;
		vector<map<string, TemplateArgument> > saved_values;
		vector<set<string> > saved_packs;

		TemplateSubstitutionScope(Parser& parser,
		                          TemplateDeclaration* declaration,
		                          const vector<TemplateArgument>& full_args)
		  : p(parser),
		    saved_types(parser.template_type_substitutions_),
		    saved_values(parser.template_value_substitutions_),
		    saved_packs(parser.template_type_parameter_packs_)
		{
			map<string, TypePtr> types;
			map<string, TemplateArgument> values;
			set<string> packs;
			for (size_t i = 0;
			     i < full_args.size() && i < declaration->parameters.size();
			     ++i)
			{
				const TemplateParameterInfo& parameter =
					declaration->parameters[i];
				if (parameter.name.empty())
					continue;
				if (parameter.kind == TemplateParameterKind::Type)
				{
					if (parameter.is_pack)
					{
						types[parameter.name] =
							template_parameter_placeholder_type(
								parameter);
						values[parameter.name] = full_args[i];
						packs.insert(parameter.name);
					}
					else if (full_args[i].kind == TemplateArgumentKind::Type)
						types[parameter.name] = full_args[i].type;
				}
				else
					values[parameter.name] = full_args[i];
			}
			p.template_type_substitutions_.insert(
				p.template_type_substitutions_.end(),
				declaration->outer_type_substitutions.begin(),
				declaration->outer_type_substitutions.end());
			p.template_value_substitutions_.insert(
				p.template_value_substitutions_.end(),
				declaration->outer_value_substitutions.begin(),
				declaration->outer_value_substitutions.end());
			p.template_type_substitutions_.push_back(types);
			p.template_value_substitutions_.push_back(values);
			p.template_type_parameter_packs_.push_back(packs);
		}

		~TemplateSubstitutionScope()
		{
			p.template_type_substitutions_ = saved_types;
			p.template_value_substitutions_ = saved_values;
			p.template_type_parameter_packs_ = saved_packs;
		}
	};

	bool enable_if_condition_false(TypePtr parameter_type,
	                               const vector<TemplateArgument>& full_args)
	{
		TypePtr bare = parameter_type.get() != NULL
			? pa11::strip_cv(parameter_type) : TypePtr();
		if (bare.get() == NULL ||
		    !unresolved_enable_if_typename(bare) ||
		    bare->template_arguments.empty())
			return false;
		const pa11::TemplateInstanceArgument& condition =
			bare->template_arguments[0];
		if (condition.kind != pa11::TemplateInstanceArgumentKind::Value)
			return false;
		if (condition.dependent &&
		    condition.value_expr_end > condition.value_expr_begin &&
		    condition.value_name.find("()") != string::npos)
			return false;
		try
			{
				TemplateArgument arg =
					p.template_argument_from_instance_argument(condition);
				if (arg.kind != TemplateArgumentKind::Value)
					return false;
				if (arg.dependent &&
				    arg.value_expr_end > arg.value_expr_begin &&
				    arg.value_name.find("()") != string::npos)
					return false;
				if (arg.dependent &&
				    !arg.value_owner_template_name.empty() &&
				    !arg.value_member_name.empty())
			{
				TemplateArgument resolved;
				if (p.resolve_dependent_value_member_argument(arg,
				                                              resolved))
					arg = resolved;
			}
			arg = p.substitute_template_argument(arg);
			if (arg.kind == TemplateArgumentKind::Value &&
			    !arg.dependent)
				return arg.value == 0;
		}
		catch (const runtime_error&)
		{
			return false;
		}
		return false;
	}

	bool invalid_enable_if_default_argument(
		TemplateDeclaration* declaration,
		size_t parameter_index,
		const vector<TemplateArgument>& full_args)
	{
		if (declaration == NULL ||
		    parameter_index >= declaration->parameters.size())
			return false;
		const TemplateParameterInfo& parameter =
			declaration->parameters[parameter_index];
		if (parameter.kind != TemplateParameterKind::NonType ||
		    parameter.type.get() == NULL)
			return false;
		TemplateSubstitutionScope scope(p, declaration, full_args);
		return enable_if_condition_false(parameter.type, full_args);
	}

		bool invalid_nontype_template_argument_candidate(Binding* fn)
		{
			map<Binding*, vector<TemplateArgument> >::const_iterator found =
				p.function_template_specialization_arguments_.find(fn);
		if (found == p.function_template_specialization_arguments_.end() &&
		    fn != NULL && fn->aliased_binding != NULL)
			found = p.function_template_specialization_arguments_.find(
				fn->aliased_binding);
		if (found == p.function_template_specialization_arguments_.end())
			return false;
		TemplateDeclaration* declaration =
			binding_function_template_origin(fn);
			for (size_t i = 0; i < found->second.size(); ++i)
			{
				const TemplateArgument& arg = found->second[i];
				if (arg.kind == TemplateArgumentKind::Value &&
				    !substituted_type_is_valid(arg.type) &&
			    unresolved_enable_if_typename(arg.type))
				return invalid_enable_if_default_argument(
					declaration,
					i,
					found->second);
		}
		return false;
	}

	bool duplicate_candidate_handled(Binding* fn, Binding*& duplicate)
	{
		bool duplicate_handled = false;
		if (duplicate == NULL ||
		    duplicate->name != fn->name ||
		    duplicate->is_static_member != fn->is_static_member ||
		    !same_overload_parameter_signature(duplicate->type, fn->type))
			return false;
		if (fn->is_inline_definition &&
		    !duplicate->is_inline_definition &&
		    erase_considered_candidate(duplicate))
		{
			duplicate = NULL;
			return false;
		}
		bool fn_template = binding_is_function_template_candidate(fn);
		bool duplicate_template =
			binding_is_function_template_candidate(duplicate);
		if (fn_template && duplicate_template)
			duplicate_handled =
				template_duplicate_candidate_handled(fn, duplicate);
		else
			duplicate_handled = fn_template || !duplicate_template;
		if (p.hosted_compatibility_ &&
		    dependent_pointer_member_helper_candidate(fn, args))
			duplicate_handled = hosted_esft_argument_has_base(args);
		return duplicate_handled;
	}

	bool template_duplicate_candidate_handled(Binding* fn, Binding* duplicate)
	{
		TemplateDeclaration* fn_origin = binding_function_template_origin(fn);
		TemplateDeclaration* duplicate_origin =
			binding_function_template_origin(duplicate);
		bool fn_concrete_duplicate =
			fn->type.get() != NULL &&
			duplicate->type.get() != NULL &&
			!binding_type_structurally_dependent(fn) &&
			binding_type_structurally_dependent(duplicate);
		if (!fn_concrete_duplicate &&
		    same_function_specialization_symbol(fn, duplicate))
		{
			if (fn->is_explicit_specialization_member &&
			    !duplicate->is_explicit_specialization_member)
				return false;
			if (fn_origin != NULL &&
			    duplicate_origin != NULL &&
			    fn_origin != duplicate_origin &&
			    !same_function_template_declaration_family(fn_origin,
			                                               duplicate_origin))
				return function_template_more_specialized(
					       p.function_template_placeholders_,
					       duplicate, fn) &&
				       !function_template_more_specialized(
					       p.function_template_placeholders_,
					       fn, duplicate);
			return duplicate_origin != NULL || fn_origin == NULL;
		}
		return !fn_concrete_duplicate &&
		       (fn->aliased_binding == duplicate ||
		        duplicate->aliased_binding == fn ||
		        same_function_template_declaration_family(fn_origin,
		                                                  duplicate_origin));
	}

	void clear_unordered_template_duplicate(Binding* fn, Binding*& duplicate)
	{
		if (duplicate == NULL)
			return;
		bool fn_template = binding_is_function_template_candidate(fn);
		bool duplicate_template =
			binding_is_function_template_candidate(duplicate);
		if (fn_template &&
		    duplicate_template &&
		    binding_template_origins_distinct(fn, duplicate) &&
		    !function_template_more_specialized(
			    p.function_template_placeholders_, fn, duplicate) &&
		    !function_template_more_specialized(
			    p.function_template_placeholders_, duplicate, fn))
			duplicate = NULL;
	}

	bool should_replace_duplicate(Binding* fn, Binding* duplicate)
	{
		bool fn_template = binding_is_function_template_candidate(fn);
		bool duplicate_template =
			binding_is_function_template_candidate(duplicate);
		bool replace = !fn_template && duplicate_template;
		int fn_score =
			p.explicit_template_argument_match_score(fn, explicit_args);
		int duplicate_score =
			p.explicit_template_argument_match_score(duplicate, explicit_args);
		if (!replace &&
		    p.hosted_compatibility_ &&
		    dependent_pointer_member_helper_candidate(fn, args))
			replace = !hosted_esft_argument_has_base(args);
		if (!replace &&
		    fn->is_explicit_specialization_member &&
		    !duplicate->is_explicit_specialization_member &&
		    same_function_specialization_symbol(fn, duplicate))
			replace = true;
		if (!replace && fn_score > duplicate_score)
			replace = true;
		if (!replace &&
		    same_function_specialization_symbol(fn, duplicate) &&
		    binding_function_template_origin(fn) != NULL &&
		    binding_function_template_origin(duplicate) == NULL)
			replace = true;
		if (!replace && fn_template && !duplicate_template)
			;
		else if (!replace && fn_template && duplicate_template &&
		         fn->type.get() != NULL &&
		         duplicate->type.get() != NULL &&
		         !binding_type_structurally_dependent(fn) &&
		         binding_type_structurally_dependent(duplicate))
			replace = true;
		else if (!replace)
			replace =
				fn->is_inline_definition && !duplicate->is_inline_definition;
		if (!replace &&
		    fn_score >= duplicate_score &&
		    function_template_more_specialized(
			    p.function_template_placeholders_, fn, duplicate))
			replace = true;
		return replace;
	}

	bool accept_candidate_after_duplicate_check(Binding* fn)
	{
		Binding* duplicate = find_duplicate_candidate(fn);
		if (duplicate_candidate_handled(fn, duplicate))
			return false;
		clear_unordered_template_duplicate(fn, duplicate);
		if (duplicate == NULL)
			return true;
		if (!should_replace_duplicate(fn, duplicate))
			return false;
		erase_considered_candidate(duplicate);
		return true;
	}

	bool candidate_viable(Binding* fn,
	                      vector<int>& ranks,
	                      vector<Expr>& conv_args,
	                      int& object_rank)
	{
		if (!p.call_candidate_has_arguments(fn, args.size()))
		{
			saw_bad_arity = true;
			return false;
		}
		bool converted = false;
		try
		{
				converted = p.convert_call_candidate_arguments(
					fn, args, conv_args, ranks, object_rank, conversion_cache);
		}
		catch (const runtime_error&)
		{
			converted = false;
		}
		if (!converted)
		{
			saw_conversion_failure = true;
			return false;
		}
		p.add_variadic_argument_ranks(fn, args.size(), ranks);
		if (object_rank < 0)
			object_rank = 0;
		return true;
	}

	bool member_object_matches(Binding* binding) const
	{
		if (binding == NULL ||
		    binding->owner == NULL ||
		    binding->owner->kind != ScopeKind::Class ||
		    binding->is_static_member ||
		    binding->type.get() == NULL ||
		    binding->type->kind != pa11::TypeKind::Function ||
		    binding->type->parameters.empty() ||
		    args.empty())
			return true;
		TypePtr this_param = pa11::strip_cv(binding->type->parameters[0]);
		if (this_param.get() == NULL ||
		    this_param->kind != pa11::TypeKind::Pointer)
			return true;
		TypePtr object_type = p.expression_object_type(args[0].type);
		TypePtr object_bare = object_type.get() != NULL
			? pa11::strip_cv(object_type) : TypePtr();
		if (object_bare.get() != NULL &&
		    object_bare->kind == pa11::TypeKind::Pointer)
			object_type = object_bare->base;
		if (this_param->base.get() != NULL &&
		    object_type.get() != NULL &&
		    pa11::type_has_const(object_type) &&
		    !pa11::type_has_const(this_param->base))
			return false;
		TypePtr this_record = this_param->base.get() != NULL
			? pa11::strip_cv(this_param->base) : TypePtr();
		TypePtr object_record = object_type.get() != NULL
			? pa11::strip_cv(object_type) : TypePtr();
		if (this_record.get() == NULL ||
		    object_record.get() == NULL ||
		    this_record->kind != pa11::TypeKind::Record ||
		    object_record->kind != pa11::TypeKind::Record)
			return true;
		if (object_record->is_template_specialization &&
		    this_record->is_template_specialization &&
		    !object_record->template_primary_name.empty() &&
		    object_record->template_primary_name ==
			    this_record->template_primary_name)
			return pa11::same_type(object_record, this_record);
		if (pa11::same_type(object_record, this_record) ||
		    same_template_signature_type(object_record, this_record))
			return true;
		return p.record_base_distance(object_record, this_record) < 1000000;
	}

	Binding* canonical_selected_binding(Binding* binding) const
	{
		Binding* canonical = canonical_function_binding(binding);
		if (canonical != binding && !member_object_matches(canonical))
			return binding;
		return canonical;
	}

	bool better_on_equal_ranks(Binding* fn,
	                           const vector<Expr>& conv_args,
	                           int object_rank)
	{
		int reference_tie =
			reference_binding_tie_break(fn, conv_args, best, best_args);
		bool fn_template = binding_is_function_template_candidate(fn);
		bool best_template = binding_is_function_template_candidate(best);
		bool fn_concrete_template =
			fn_template && fn->type.get() != NULL &&
			!binding_type_structurally_dependent(fn);
		bool fn_dependent_template =
			fn_template && fn->type.get() != NULL &&
			binding_type_structurally_dependent(fn);
		bool best_concrete_template =
			best_template && best->type.get() != NULL &&
			!binding_type_structurally_dependent(best);
		bool best_dependent_template =
			best_template && best->type.get() != NULL &&
			binding_type_structurally_dependent(best);
		bool fn_dependent_type =
			fn->type.get() != NULL && binding_type_structurally_dependent(fn);
		bool best_dependent_type =
			best->type.get() != NULL &&
			binding_type_structurally_dependent(best);
		if (reference_tie > 0)
			return true;
		if (reference_tie < 0)
			return false;
		if (!fn_dependent_type && best_dependent_type)
			return true;
		if (fn_dependent_type && !best_dependent_type)
			return false;
		if (fn_concrete_template && best_dependent_template)
			return true;
		if (fn_dependent_template && best_concrete_template)
			return false;
		if (fn->is_inline_definition && !best->is_inline_definition)
			return true;
		if (!fn->is_inline_definition && best->is_inline_definition)
			return false;
		if (!fn_template && best_template)
			return true;
		if (fn_template == best_template &&
		    function_template_more_specialized_for_call(
			    p.function_template_placeholders_, fn, best, args.size()))
			return true;
		return fn_template == best_template &&
		       function_template_fewer_forwarding_lvalue_parameters_for_call(
			       p.function_template_placeholders_, fn, best, args);
	}

	bool tag_dispatch_order(Binding* fn, bool& ordered)
	{
		ordered = false;
		if (best->name != fn->name ||
		    best->owner != fn->owner ||
		    best->type.get() == NULL ||
		    fn->type.get() == NULL ||
		    best->type->kind != pa11::TypeKind::Function ||
		    fn->type->kind != pa11::TypeKind::Function ||
		    best->type->parameters.size() != fn->type->parameters.size() ||
		    best->type->parameters.size() != args.size() ||
		    args.empty())
			return false;
		size_t tag_index = best->type->parameters.size() - 1;
		bool leading_same_family = true;
		size_t first = best->owner != NULL &&
		               best->owner->kind == ScopeKind::Class &&
		               !best->is_static_member ? 1 : 0;
		for (size_t pi = first; pi < tag_index; ++pi)
			if (!same_parameter_family_ignoring_pointer_cv(
				    best->type->parameters[pi], fn->type->parameters[pi]))
				leading_same_family = false;
		TypePtr arg_record =
			pa11::strip_cv(p.expression_object_type(args.back().type));
		TypePtr best_tag = pa11::strip_cv(best->type->parameters[tag_index]);
		TypePtr fn_tag = pa11::strip_cv(fn->type->parameters[tag_index]);
		if (!leading_same_family ||
		    arg_record.get() == NULL ||
		    arg_record->kind != pa11::TypeKind::Record ||
		    best_tag.get() == NULL ||
		    best_tag->kind != pa11::TypeKind::Record ||
		    fn_tag.get() == NULL ||
		    fn_tag->kind != pa11::TypeKind::Record)
			return false;
		int best_distance = p.record_base_distance(arg_record, best_tag);
		int fn_distance = p.record_base_distance(arg_record, fn_tag);
		if (best_distance >= 1000000 ||
		    fn_distance >= 1000000 ||
		    best_distance == fn_distance)
			return false;
		ordered = true;
		return fn_distance < best_distance;
	}

	bool same_rank_indistinguishable(Binding* fn,
	                                 const vector<Expr>& conv_args,
	                                 int object_rank,
	                                 bool distinct_templates,
	                                 bool& better)
	{
		if (object_rank < best_object_rank)
		{
			better = true;
			return false;
		}
		if (object_rank != best_object_rank)
			return false;
		if (best->is_inline_definition && !fn->is_inline_definition)
			return false;
		if (same_overload_parameter_signature(best->type, fn->type) &&
		    !distinct_templates)
			return false;
		if (!binding_is_function_template_candidate(best) &&
		    binding_is_function_template_candidate(fn))
			return false;
		if (best->type.get() != NULL && fn->type.get() != NULL &&
		    !binding_type_structurally_dependent(best) &&
		    binding_type_structurally_dependent(fn))
			return false;
		if (best->type.get() != NULL && fn->type.get() != NULL &&
		    binding_type_structurally_dependent(best) &&
		    !binding_type_structurally_dependent(fn))
		{
			better = true;
			return false;
		}
		if (template_concrete_beats_dependent(fn, true, better))
			return false;
		if (function_template_more_specialized_for_call(
			    p.function_template_placeholders_, best, fn, args.size()))
			return false;
		if (function_template_fewer_forwarding_lvalue_parameters_for_call(
			    p.function_template_placeholders_, best, fn, args))
			return false;
		if (reference_binding_tie_break(best, best_args, fn, conv_args) > 0)
			return false;
		return true;
	}

	bool template_concrete_beats_dependent(Binding* fn,
	                                       bool best_first,
	                                       bool& better)
	{
		if (!binding_is_function_template_candidate(best) ||
		    !binding_is_function_template_candidate(fn) ||
		    best->type.get() == NULL ||
		    fn->type.get() == NULL)
			return false;
		bool best_dependent = binding_type_structurally_dependent(best);
		bool fn_dependent = binding_type_structurally_dependent(fn);
		if (best_first && !best_dependent && fn_dependent)
			return true;
		if (best_first && best_dependent && !fn_dependent)
		{
			better = true;
			return true;
		}
		return false;
	}

	bool candidate_indistinguishable(Binding* fn,
	                                 const vector<int>& ranks,
	                                 const vector<Expr>& conv_args,
	                                 int object_rank,
	                                 bool& better)
	{
		bool distinct_templates = binding_template_origins_distinct(fn, best);
		if (best == NULL ||
		    better ||
		    p.ranks_better(best_ranks, ranks))
			return false;
		if (ranks == best_ranks)
			return same_rank_indistinguishable(
				fn, conv_args, object_rank, distinct_templates, better);
		bool ordered = false;
		bool tag_better = tag_dispatch_order(fn, ordered);
		if (tag_better)
		{
			better = true;
			return false;
		}
		return !ordered;
	}

	void compare_candidate(Binding* fn,
	                       const vector<int>& ranks,
	                       const vector<Expr>& conv_args,
	                       int object_rank)
	{
		bool better = best == NULL || p.ranks_better(ranks, best_ranks);
		if (!better &&
		    best != NULL &&
		    ranks == best_ranks &&
		    object_rank == best_object_rank)
			better = better_on_equal_ranks(fn, conv_args, object_rank);
		bool indistinguishable =
			candidate_indistinguishable(fn, ranks, conv_args, object_rank,
			                            better);
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

	void process_candidate(Binding* original)
	{
		Binding* fn = instantiate_candidate(original);
		if (fn == NULL ||
		    fn->type->kind != pa11::TypeKind::Function)
			return;
		if (!member_object_matches(fn))
			return;
		if (invalid_nontype_template_argument_candidate(fn))
		{
			return;
		}
		if (p.hosted_compatibility_)
			model_dependent_pointer_member_helper_candidate(fn, args);
		if (!accept_candidate_after_duplicate_check(fn))
		{
			return;
		}
		add_considered_candidate(fn);
		vector<int> ranks;
		vector<Expr> conv_args;
		int object_rank = -1;
		if (!candidate_viable(fn, ranks, conv_args, object_rank))
		{
			return;
		}
		compare_candidate(fn, ranks, conv_args, object_rank);
	}

	void ensure_selected_member_templates(Binding* binding)
	{
		if (binding == NULL ||
		    binding->owner == NULL ||
		    binding->owner->kind != ScopeKind::Class)
			return;
		TypePtr owner_record = pa11::record_type_for_scope(binding->owner);
		owner_record = owner_record.get() != NULL
			? pa11::strip_cv(owner_record) : TypePtr();
		if (owner_record.get() != NULL &&
		    owner_record->kind == pa11::TypeKind::Record &&
		    owner_record->is_template_specialization)
			p.instantiate_member_function_templates(owner_record);
	}

	bool selected_dependent_return(Binding* binding)
	{
		return binding != NULL &&
		       binding->type.get() != NULL &&
		       binding->type->kind == pa11::TypeKind::Function &&
		       p.type_is_template_dependent(binding->type->base);
	}

	TemplateDeclaration* find_compatible_body_declaration(
		TemplateDeclaration* replay_declaration,
		map<Binding*, vector<TemplateArgument> >::iterator args_it,
		TemplateDeclaration*& compatible_body)
	{
		for (map<Scope*, map<string, vector<TemplateDeclaration*> > >::iterator
			     sit = p.function_templates_.begin();
		     sit != p.function_templates_.end(); ++sit)
		{
			map<string, vector<TemplateDeclaration*> >::iterator nit =
				sit->second.find(replay_declaration->name);
			if (nit == sit->second.end())
				continue;
			for (size_t di = 0; di < nit->second.size(); ++di)
			{
				TemplateDeclaration* candidate = nit->second[di];
				if (!compatible_replay_candidate(candidate, replay_declaration,
				                                 args_it, compatible_body))
					continue;
				replay_declaration = candidate;
				break;
			}
			if (template_declaration_has_body(p.declaration_tokens_,
			                                  replay_declaration))
				break;
		}
		return replay_declaration;
	}

	bool compatible_replay_candidate(
		TemplateDeclaration* candidate,
		TemplateDeclaration* replay_declaration,
		map<Binding*, vector<TemplateArgument> >::iterator args_it,
		TemplateDeclaration*& compatible_body)
	{
		if (candidate == replay_declaration ||
		    !template_declaration_has_body(p.declaration_tokens_, candidate) ||
		    candidate->generic_function_type.get() == NULL)
			return false;
		bool parameters_match =
			expr_template_parameter_lists_match(candidate->parameters,
			                                    replay_declaration->parameters);
		bool signature_matches =
			same_template_signature_type(candidate->generic_function_type,
			                             replay_declaration->generic_function_type);
		if (!parameters_match && !signature_matches)
			return false;
		if (compatible_body == NULL && signature_matches)
			compatible_body = candidate;
		if (!signature_matches)
			return false;
		if (replay_declaration->class_template_member &&
		    !candidate->class_template_member)
			return false;
		if (args_it == p.function_template_specialization_arguments_.end())
			return true;
		size_t required_arguments = 0;
		for (size_t pi = 0; pi < candidate->parameters.size(); ++pi)
			if (!candidate->parameters[pi].has_default &&
			    !candidate->parameters[pi].is_pack)
				++required_arguments;
		if (args_it->second.size() < required_arguments)
			return false;
		try
		{
			p.complete_template_arguments(candidate, args_it->second);
		}
		catch (const exception&)
		{
			return false;
		}
		return true;
	}

	TemplateDeclaration* clone_compatible_body(
		TemplateDeclaration* replay_declaration,
		TemplateDeclaration* compatible_body)
	{
		if (template_declaration_has_body(p.declaration_tokens_,
		                                  replay_declaration) ||
		    compatible_body == NULL)
			return replay_declaration;
		TemplateDeclaration* clone_ptr = find_existing_body_clone(
			replay_declaration, compatible_body);
		if (clone_ptr != NULL)
			return clone_ptr;
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
		clone_ptr = clone.get();
		p.template_declarations_.push_back(std::move(clone));
		return clone_ptr;
	}

	TemplateDeclaration* find_existing_body_clone(
		TemplateDeclaration* replay_declaration,
		TemplateDeclaration* compatible_body)
	{
		for (size_t ti = 0; ti < p.template_declarations_.size(); ++ti)
		{
			TemplateDeclaration* candidate = p.template_declarations_[ti].get();
			if (candidate != NULL &&
			    candidate != compatible_body &&
			    candidate->name == compatible_body->name &&
			    candidate->decl_begin == compatible_body->decl_begin &&
			    candidate->decl_end == compatible_body->decl_end &&
			    candidate->owner == replay_declaration->owner &&
			    candidate->placeholder == replay_declaration->placeholder &&
			    candidate->class_template_member ==
				    replay_declaration->class_template_member)
				return candidate;
		}
		return NULL;
	}

	TemplateDeclaration* instantiate_alternate_body(
		TemplateDeclaration* replay_declaration,
		map<Binding*, vector<TemplateArgument> >::iterator args_it,
		Binding*& selected)
	{
		if (template_declaration_has_body(p.declaration_tokens_,
		                                  replay_declaration) ||
		    args_it == p.function_template_specialization_arguments_.end())
			return replay_declaration;
		for (size_t di = 0; di < p.template_declarations_.size(); ++di)
		{
			TemplateDeclaration* candidate = p.template_declarations_[di].get();
			if (candidate == replay_declaration ||
			    candidate == NULL ||
			    candidate->name != replay_declaration->name ||
			    !template_declaration_has_body(p.declaration_tokens_,
			                                   candidate))
				continue;
			Binding* instantiated = instantiate_matching_body(candidate,
			                                                  args_it,
			                                                  selected);
			if (instantiated == NULL)
				continue;
			if (selected != instantiated)
				selected->aliased_binding = instantiated;
			selected = instantiated;
			return candidate;
		}
		return replay_declaration;
	}

	Binding* instantiate_matching_body(
		TemplateDeclaration* candidate,
		map<Binding*, vector<TemplateArgument> >::iterator args_it,
		Binding* selected)
	{
		Binding* instantiated = NULL;
		try
		{
			instantiated =
				p.instantiate_function_template(candidate, args_it->second);
		}
		catch (const exception&)
		{
			return NULL;
		}
		if (instantiated == NULL ||
		    instantiated->type.get() == NULL ||
		    selected->type.get() == NULL ||
		    !pa11::same_type(instantiated->type, selected->type))
			return NULL;
		if (!member_object_matches(instantiated))
			return NULL;
		return instantiated;
	}

	TemplateDeclaration* recover_replay_declaration(
		TemplateDeclaration* replay_declaration,
		map<Binding*, vector<TemplateArgument> >::iterator args_it,
		Binding*& selected)
	{
		if (replay_declaration == NULL ||
		    template_declaration_has_body(p.declaration_tokens_,
		                                  replay_declaration))
			return replay_declaration;
		TemplateDeclaration* compatible_body = NULL;
		replay_declaration = find_compatible_body_declaration(
			replay_declaration, args_it, compatible_body);
		replay_declaration = clone_compatible_body(replay_declaration,
		                                           compatible_body);
		return instantiate_alternate_body(replay_declaration, args_it,
		                                  selected);
	}

	void instantiate_selected_template_body(Binding*& selected,
	                                        bool dependent_return)
	{
		if (selected == NULL ||
		    !(p.unevaluated_expression_depth_ == 0 || dependent_return) ||
		    (selected->is_inline_definition &&
		     p.function_bodies_.find(selected) != p.function_bodies_.end() &&
		     !dependent_return))
			return;
		map<Binding*, TemplateDeclaration*>::iterator template_it =
			p.function_template_placeholders_.find(selected);
		map<Binding*, vector<TemplateArgument> >::iterator args_it =
			p.function_template_specialization_arguments_.find(selected);
		bool completion_active =
			template_it != p.function_template_placeholders_.end() &&
			args_it != p.function_template_specialization_arguments_.end() &&
			template_it->second->completing_specializations.count(
				p.template_argument_key(args_it->second)) != 0;
		bool selected_has_body =
			p.function_bodies_.find(selected) != p.function_bodies_.end();
		bool explicit_specialization_body =
			selected->is_explicit_specialization_member && selected_has_body;
		TemplateDeclaration* replay_declaration =
			template_it != p.function_template_placeholders_.end()
			? template_it->second : NULL;
		replay_declaration =
			recover_replay_declaration(replay_declaration, args_it, selected);
		if (!selected_template_body_should_replay(
			    selected, replay_declaration, template_it, args_it,
			    completion_active, explicit_specialization_body,
			    selected_has_body, dependent_return))
			return;
		bool signature_only_replay =
			dependent_return && p.unevaluated_expression_depth_ != 0;
		replay_selected_template(selected, replay_declaration, args_it,
		                         signature_only_replay);
	}

	bool selected_template_body_should_replay(
		Binding* selected,
		TemplateDeclaration* replay_declaration,
		map<Binding*, TemplateDeclaration*>::iterator template_it,
		map<Binding*, vector<TemplateArgument> >::iterator args_it,
		bool completion_active,
		bool explicit_specialization_body,
		bool selected_has_body,
		bool dependent_return)
	{
		bool hosted_nonroot_signature_replay =
			p.hosted_compatibility_ &&
			replay_declaration != NULL &&
			replay_declaration->has_definition &&
			selected != NULL &&
			p.hosted_library_function(selected) &&
			!selected->is_object_root &&
			!dependent_return &&
			p.constexpr_value_expression_depth_ == 0 &&
			p.template_argument_expression_depth_ == 0;
		return !completion_active &&
		       !explicit_specialization_body &&
		       template_it != p.function_template_placeholders_.end() &&
		       args_it != p.function_template_specialization_arguments_.end() &&
		       !hosted_nonroot_signature_replay &&
		       !(p.hosted_compatibility_ &&
		         replay_declaration != NULL &&
		         replay_declaration->has_definition &&
		         !selected->is_object_root &&
		         !dependent_return &&
		         selected_has_body) &&
		       (template_declaration_has_body(p.declaration_tokens_,
		                                      replay_declaration) ||
		        dependent_return);
	}

	void replay_selected_template(
		Binding*& selected,
		TemplateDeclaration* replay_declaration,
		map<Binding*, vector<TemplateArgument> >::iterator args_it,
		bool signature_only_replay)
	{
		vector<TemplateArgument> selected_args = args_it->second;
		if (selected_args.size() < replay_declaration->parameters.size())
		{
			++p.function_template_candidate_instantiation_depth_;
			try
			{
				selected_args = p.complete_template_arguments(
					replay_declaration, selected_args);
			}
			catch (...)
			{
				--p.function_template_candidate_instantiation_depth_;
				throw;
			}
			--p.function_template_candidate_instantiation_depth_;
		}
		Binding* instantiated =
			instantiate_selected_replay(replay_declaration, selected_args,
			                            signature_only_replay);
		if (!member_object_matches(instantiated))
			return;
		if (instantiated != NULL)
		{
			if (selected != instantiated)
				selected->aliased_binding = instantiated;
			selected = instantiated;
		}
	}

	Binding* instantiate_selected_replay(
		TemplateDeclaration* replay_declaration,
		const vector<TemplateArgument>& selected_args,
		bool signature_only_replay)
	{
		Binding* instantiated = NULL;
		bool saved_force_body_instantiation =
			p.force_function_template_body_instantiation_;
		if (!signature_only_replay)
			p.force_function_template_body_instantiation_ = true;
		try
		{
			instantiated =
				p.instantiate_function_template(replay_declaration,
				                                selected_args);
		}
		catch (...)
		{
			restore_replay_flags(false,
			                     saved_force_body_instantiation);
			throw;
		}
		restore_replay_flags(false,
		                     saved_force_body_instantiation);
		return instantiated;
	}

	void restore_replay_flags(bool signature_only_replay,
	                          bool saved_force_body_instantiation)
	{
		if (signature_only_replay)
			--p.function_template_candidate_instantiation_depth_;
		else
			p.force_function_template_body_instantiation_ =
				saved_force_body_instantiation;
	}

	bool final_completion_active(Binding* selected)
	{
		if (selected == NULL)
			return false;
		map<Binding*, TemplateDeclaration*>::iterator template_it =
			p.function_template_placeholders_.find(selected);
		map<Binding*, vector<TemplateArgument> >::iterator args_it =
			p.function_template_specialization_arguments_.find(selected);
		return template_it != p.function_template_placeholders_.end() &&
		       args_it != p.function_template_specialization_arguments_.end() &&
		       template_it->second->completing_specializations.count(
			       p.template_argument_key(args_it->second)) != 0;
	}

	void complete_selected_pending_body(Binding* selected)
	{
		if (final_completion_active(selected) ||
		    selected == NULL ||
		    p.unevaluated_expression_depth_ != 0 ||
		    p.function_template_candidate_instantiation_depth_ != 0 ||
		    selected->is_extern_template_instantiation ||
		    p.defer_hosted_function_body(selected) ||
		    (p.hosted_compatibility_ &&
		     p.hosted_library_function(selected) &&
		     selected->is_inline_definition &&
		     !selected->is_object_root))
			return;
		p.parse_pending_function_body(selected);
		p.parse_pending_member_body(selected);
		p.ensure_function_body_extra_node(selected);
		if (selected->aliased_binding != NULL)
		{
			p.parse_pending_function_body(selected->aliased_binding);
			p.parse_pending_member_body(selected->aliased_binding);
			p.ensure_function_body_extra_node(selected->aliased_binding);
		}
	}

	Binding* resolve(vector<Expr>& converted)
	{
		instantiate_member_template_owners();
		for (size_t i = 0; i < overloads.size(); ++i)
			process_candidate(overloads[i]);
		if (best == NULL || ambiguous)
			throw runtime_error("cannot resolve call overload");
		ensure_selected_member_templates(best);
		if (p.unevaluated_expression_depth_ == 0)
			p.mark_template_specialization_demanded(best->type);
		converted = best_args;
		bool dependent_return = selected_dependent_return(best);
		instantiate_selected_template_body(best, dependent_return);
		complete_selected_pending_body(best);
		return canonical_selected_binding(best);
	}
};

Binding* Parser::resolve_call_candidate(const vector<Binding*>& overloads,
                                        const vector<Expr>& args,
                                        const map<Binding*, vector<TemplateArgument> >& explicit_template_arguments,
                                        vector<Expr>& converted)
{
	CallResolver resolver(*this, overloads, args, explicit_template_arguments);
	return resolver.resolve(converted);
}

}  // namespace internal
}  // namespace pa12
