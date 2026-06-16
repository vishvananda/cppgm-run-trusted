#include "pa12_expr_semantics_support.h"
#include "pa12_types_support.h"

#include <algorithm>
#include <stdexcept>

using namespace std;

namespace pa12 {
namespace internal {

static bool constructor_this_matches_record(TypePtr record, Binding* ctor)
{
	if (record.get() == NULL ||
	    ctor == NULL ||
	    ctor->type.get() == NULL ||
	    ctor->type->kind != pa11::TypeKind::Function ||
	    ctor->type->parameters.empty())
		return false;
	TypePtr this_type = pa11::strip_cv(ctor->type->parameters[0]);
	if (this_type.get() == NULL ||
	    this_type->kind != pa11::TypeKind::Pointer)
		return false;
	TypePtr this_record = pa11::strip_cv(this_type->base);
	record = pa11::strip_cv(record);
	return this_record.get() != NULL &&
	       record.get() != NULL &&
	       this_record->kind == pa11::TypeKind::Record &&
	       record->kind == pa11::TypeKind::Record &&
	       (pa11::same_type(this_record, record) ||
	        same_template_specialization_record(this_record, record));
}

static bool record_has_conversion_function_candidate(TypePtr record,
                                                     set<Scope*>& seen)
{
	TypePtr bare = record.get() != NULL ? pa11::strip_cv(record) : TypePtr();
	if (bare.get() == NULL ||
	    bare->kind != pa11::TypeKind::Record ||
	    bare->scope == NULL ||
	    !seen.insert(bare->scope).second)
		return false;
	for (map<string, vector<Binding*> >::const_iterator it =
		     bare->scope->members.begin();
	     it != bare->scope->members.end();
	     ++it)
		if (it->first.compare(0, 9, "operator ") == 0)
			for (size_t i = 0; i < it->second.size(); ++i)
				if (it->second[i]->kind == BindingKind::Function)
					return true;
	vector<TypePtr> bases = pa11::record_direct_bases(bare);
	for (size_t i = 0; i < bases.size(); ++i)
		if (record_has_conversion_function_candidate(bases[i], seen))
			return true;
	return false;
}

static bool hosted_std_vector_record(TypePtr type)
{
	TypePtr bare = type.get() != NULL ? pa11::strip_cv(type) : TypePtr();
	if (bare.get() == NULL ||
	    bare->kind != pa11::TypeKind::Record ||
	    !bare->is_template_specialization ||
	    bare->scope == NULL)
		return false;
	string primary = bare->template_primary_name.empty()
		? bare->name : bare->template_primary_name;
	size_t sep = primary.rfind("::");
	if (sep != string::npos)
		primary = primary.substr(sep + 2);
	size_t args = primary.find('<');
	if (args != string::npos)
		primary = primary.substr(0, args);
	if (primary != "vector")
		return false;
	for (Scope* scope = bare->scope; scope != NULL; scope = scope->parent)
		if (scope->kind == ScopeKind::Namespace && scope->name == "std")
			return true;
	return false;
}

void Parser::prepare_constructor_template_candidates(TypePtr record,
                                                     const vector<Expr>& args)
{
	complete_template_record(record);
	if (record->is_template_specialization)
		instantiate_member_function_templates(record);
	if (record->scope != NULL &&
	    record->scope->parent != NULL &&
	    record->scope->parent->kind == ScopeKind::Class)
	{
		TypePtr owner_record = pa11::record_type_for_scope(record->scope->parent);
		owner_record = owner_record.get() != NULL
			? pa11::strip_cv(owner_record) : TypePtr();
		if (owner_record.get() != NULL &&
		    owner_record->kind == pa11::TypeKind::Record &&
		    owner_record->is_template_specialization)
			instantiate_member_function_templates(owner_record);
	}
	if (record->scope == NULL)
		return;
	vector<TypePtr> owners;
	set<const void*> seen_owners;
	for (map<pair<TemplateDeclaration*, string>,
	     vector<TemplateDeclaration*> >::iterator it =
		     member_function_templates_.begin();
	     it != member_function_templates_.end();
	     ++it)
	{
		if (it->first.second != record->scope->name)
			continue;
		bool constructor_template = false;
		for (size_t i = 0; i < it->second.size(); ++i)
			if (it->second[i]->constructor_template)
				constructor_template = true;
		if (!constructor_template || it->first.first == NULL)
			continue;
		for (map<string, TypePtr>::const_iterator spec =
			     it->first.first->class_specializations.begin();
		     spec != it->first.first->class_specializations.end();
		     ++spec)
		{
			TypePtr owner = pa11::strip_cv(spec->second);
			if (owner.get() == NULL ||
			    owner->kind != pa11::TypeKind::Record ||
			    owner->scope == NULL)
				continue;
			if (owner.get() != record.get() &&
			    !pa11::same_type(owner, record))
				continue;
			if (seen_owners.insert(owner.get()).second)
				owners.push_back(owner);
		}
	}
	for (size_t i = 0; i < owners.size(); ++i)
		instantiate_member_function_templates(owners[i]);

	Expr this_arg;
	this_arg.valid = true;
	this_arg.type = pa11::make_pointer(record);
	this_arg.category = ValueCategory::PRValue;
	this_arg.node = Node("id-expression prvalue " +
	                     pa11::describe_type(this_arg.type) + " this");
	annotate_expr_node(this_arg);
	vector<Expr> deduction_args;
	deduction_args.push_back(this_arg);
	deduction_args.insert(deduction_args.end(), args.begin(), args.end());
	map<Binding*, vector<TemplateArgument> > explicit_args;
	for (map<pair<TemplateDeclaration*, string>,
	     vector<TemplateDeclaration*> >::iterator it =
		     member_function_templates_.begin();
	     it != member_function_templates_.end();
	     ++it)
	{
		if (it->first.second != record->scope->name)
			continue;
		for (size_t i = 0; i < it->second.size(); ++i)
		{
			TemplateDeclaration* declaration = it->second[i];
			if (!declaration->constructor_template ||
			    declaration->placeholder == NULL)
				continue;
			map<Binding*, TemplateDeclaration*>::iterator saved =
				function_template_placeholders_.find(declaration->placeholder);
			TemplateDeclaration* saved_declaration =
				saved != function_template_placeholders_.end()
				? saved->second : NULL;
			function_template_placeholders_[declaration->placeholder] =
				declaration;
			instantiate_template_call_candidate(declaration->placeholder,
			                                    explicit_args,
			                                    deduction_args);
			if (saved_declaration != NULL)
				function_template_placeholders_[declaration->placeholder] =
					saved_declaration;
			else
				function_template_placeholders_.erase(declaration->placeholder);
		}
	}
}

Binding* Parser::instantiate_constructor_template_candidate(
	TypePtr record,
	Binding* ctor,
	const vector<Expr>& args)
{
	map<Binding*, TemplateDeclaration*>::iterator template_it =
		function_template_placeholders_.find(ctor);
	if (template_it == function_template_placeholders_.end() &&
	    ctor != NULL &&
	    ctor->type.get() != NULL &&
	    type_structurally_dependent(ctor->type))
	{
		for (map<Binding*, TemplateDeclaration*>::iterator it =
			     function_template_placeholders_.begin();
		     it != function_template_placeholders_.end();
		     ++it)
		{
			Binding* placeholder = it->first;
			TemplateDeclaration* declaration = it->second;
			if (placeholder == NULL ||
			    declaration == NULL ||
			    !declaration->constructor_template ||
			    placeholder->owner != ctor->owner ||
			    placeholder->name != ctor->name ||
			    placeholder->type.get() == NULL ||
			    !same_template_signature_type(placeholder->type,
			                                  ctor->type))
				continue;
			ctor = placeholder;
			template_it = it;
			break;
		}
	}
	if (template_it == function_template_placeholders_.end())
		return ctor;
	TemplateDeclaration* declaration = template_it->second;
	TypePtr bare_record = record.get() != NULL ? pa11::strip_cv(record) : TypePtr();
	map<const void*, TemplateDeclaration*>::iterator owner_template =
		bare_record.get() != NULL
		? record_template_declarations_.find(bare_record.get())
		: record_template_declarations_.end();
	if (declaration != NULL &&
	    declaration->constructor_template &&
	    declaration->class_template_member &&
	    owner_template != record_template_declarations_.end() &&
	    expr_template_parameter_lists_match(declaration->parameters,
	                                        owner_template->second->parameters))
		return ctor;
	Expr this_arg;
	this_arg.valid = true;
	this_arg.type = pa11::make_pointer(record);
	this_arg.category = ValueCategory::PRValue;
	this_arg.node = Node("id-expression prvalue " +
	                     pa11::describe_type(this_arg.type) + " this");
	annotate_expr_node(this_arg);
	vector<Expr> deduction_args;
	deduction_args.push_back(this_arg);
	deduction_args.insert(deduction_args.end(), args.begin(), args.end());
	map<Binding*, vector<TemplateArgument> > explicit_args;
	ctor = instantiate_template_call_candidate(ctor, explicit_args, deduction_args);
	if (ctor == NULL)
		return NULL;
	if (declaration != NULL &&
	    declaration->constructor_template &&
	    declaration->inherited_constructor_base == NULL &&
	    !constructor_this_matches_record(record, ctor))
		return NULL;
	if (default_arguments_.find(ctor) == default_arguments_.end())
	{
		map<Binding*, TemplateDeclaration*>::iterator instantiated_template =
			function_template_placeholders_.find(ctor);
		if (instantiated_template != function_template_placeholders_.end() &&
		    instantiated_template->second->placeholder != NULL)
		{
			map<Binding*, vector<Expr> >::const_iterator defaults =
				default_arguments_.find(
					instantiated_template->second->placeholder);
			if (defaults != default_arguments_.end())
				default_arguments_[ctor] = defaults->second;
		}
	}
	return ctor;
}

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

bool Parser::constructor_accepts_argument_count(Binding* ctor,
                                                size_t arg_count) const
{
	size_t param_count = ctor->type->parameters.size() - 1;
	if (arg_count > param_count && !ctor->type->variadic)
		return false;
	if (arg_count >= param_count)
		return true;
	map<Binding*, vector<Expr> >::const_iterator defaults =
		default_arguments_.find(ctor);
	if (defaults == default_arguments_.end())
		return false;
	for (size_t j = arg_count + 1; j < ctor->type->parameters.size(); ++j)
		if (j >= defaults->second.size() || !defaults->second[j].valid)
			return false;
	return true;
}

bool Parser::convert_constructor_candidate_arguments(
	Binding* ctor,
	const vector<Expr>& args,
	vector<Expr>& conv_args,
	vector<int>& ranks)
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
			try
			{
				conv = convert_to(args[j], param);
		}
		catch (const runtime_error&)
		{
			return false;
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
	if (best == NULL || ranks_better(ranks, best_ranks))
		return true;
	if (ranks != best_ranks)
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
						default_arguments_[duplicate] = defaults->second;
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
		                                             ranks))
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

bool Parser::use_hosted_allocator_constructor_fallback(
	TypePtr record,
	const vector<Expr>& args,
	Binding*& best,
	vector<Expr>& best_args,
	bool& ambiguous)
{
	if (best != NULL || ambiguous || !hosted_compatibility_ ||
	    args.size() != 1)
		return false;
	auto unqualified_primary = [](TypePtr t) {
		string primary = t.get() != NULL
			? (t->template_primary_name.empty()
			   ? t->name : t->template_primary_name)
			: string();
		size_t sep = primary.rfind("::");
		if (sep != string::npos)
			primary = primary.substr(sep + 2);
		size_t arg_pos = primary.find('<');
		if (arg_pos != string::npos)
			primary = primary.substr(0, arg_pos);
		return primary;
	};
	TypePtr source = expression_object_type(args[0].type);
	TypePtr source_record = source.get() != NULL
		? pa11::strip_cv(source) : TypePtr();
	if (!record->is_template_specialization ||
	    source_record.get() == NULL ||
	    source_record->kind != pa11::TypeKind::Record ||
	    !source_record->is_template_specialization ||
	    unqualified_primary(record) != "allocator" ||
	    unqualified_primary(source_record) != "allocator")
		return false;
	TypePtr param_type = pa11::make_lvalue_reference(
		pa11::make_cv(source_record, pa11::CV_CONST));
	vector<TypePtr> params;
	params.push_back(pa11::make_pointer(record));
	params.push_back(param_type);
	TypePtr fn_type = pa11::make_function(pa11::make_fundamental(FT_VOID),
	                                      params,
	                                      false);
	Binding* ctor = NULL;
	map<string, vector<Binding*> >::iterator existing =
		record->scope->members.find(record->scope->name);
	if (existing != record->scope->members.end())
		for (size_t ci = 0; ci < existing->second.size(); ++ci)
			if (existing->second[ci]->kind == BindingKind::Function &&
			    pa11::same_type(existing->second[ci]->type, fn_type))
				ctor = existing->second[ci];
	if (ctor == NULL)
	{
		ctor = add_value(record->scope,
		                 BindingKind::Function,
		                 record->scope->name,
		                 fn_type);
		ctor->is_inline_definition = true;
		ctor->is_defaulted = true;
		function_parameter_names_[ctor] = vector<string>(2, "this");
		function_parameter_names_[ctor][1] = "other";
	}
	best = ctor;
	best_args = args;
	ambiguous = false;
	return true;
}

Binding* Parser::instantiate_selected_constructor_body(Binding* best)
{
	if (best == NULL ||
	    unevaluated_expression_depth_ != 0)
		return best;
	map<Binding*, TemplateDeclaration*>::iterator template_it =
		function_template_placeholders_.find(best);
	map<Binding*, vector<TemplateArgument> >::iterator args_it =
		function_template_specialization_arguments_.find(best);
	if (template_it == function_template_placeholders_.end() &&
	    args_it == function_template_specialization_arguments_.end() &&
	    best->is_inline_definition &&
	    function_bodies_.find(best) != function_bodies_.end())
		return best;
	TemplateDeclaration* replay_declaration =
		template_it != function_template_placeholders_.end()
		? template_it->second : NULL;
	if (replay_declaration == NULL)
		return best;
	replay_declaration =
		replacement_function_template_definition(replay_declaration);
	if (!template_declaration_has_body(declaration_tokens_, replay_declaration))
	{
		TemplateDeclaration* compatible_body = NULL;
		for (map<pair<TemplateDeclaration*, string>,
		     vector<TemplateDeclaration*> >::iterator mit =
			     member_function_templates_.begin();
		     mit != member_function_templates_.end();
		     ++mit)
		{
			if (mit->first.second != replay_declaration->name)
				continue;
			for (size_t di = 0; di < mit->second.size(); ++di)
			{
				TemplateDeclaration* candidate = mit->second[di];
				if (candidate == replay_declaration ||
				    !candidate->constructor_template ||
				    !template_declaration_has_body(declaration_tokens_,
				                                   candidate) ||
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
				replay_declaration = candidate;
				break;
			}
			if (template_declaration_has_body(declaration_tokens_,
			                                  replay_declaration))
				break;
		}
		if (!template_declaration_has_body(declaration_tokens_,
		                                   replay_declaration) &&
		    compatible_body != NULL)
		{
			unique_ptr<TemplateDeclaration> clone(
				new TemplateDeclaration(*compatible_body));
			clone->owner = replay_declaration->owner;
			clone->placeholder = replay_declaration->placeholder;
			clone->class_template_member = replay_declaration->class_template_member;
			clone->outer_type_substitutions =
				replay_declaration->outer_type_substitutions;
			clone->outer_value_substitutions =
				replay_declaration->outer_value_substitutions;
			clone->function_specializations.clear();
			clone->completing_specializations.clear();
			replay_declaration = clone.get();
			template_declarations_.push_back(std::move(clone));
		}
	}
	if (template_it == function_template_placeholders_.end() ||
	    args_it == function_template_specialization_arguments_.end() ||
	    !template_declaration_has_body(declaration_tokens_, replay_declaration))
		return best;
	vector<TemplateArgument> selected_args = args_it->second;
	if (selected_args.size() < replay_declaration->parameters.size())
	{
		++function_template_candidate_instantiation_depth_;
		try
		{
			selected_args = complete_template_arguments(replay_declaration,
			                                           selected_args);
		}
		catch (...)
		{
			--function_template_candidate_instantiation_depth_;
			throw;
		}
		--function_template_candidate_instantiation_depth_;
	}
	bool saved_force_body_instantiation =
		force_function_template_body_instantiation_;
	force_function_template_body_instantiation_ = true;
	Binding* instantiated = NULL;
	try
	{
		instantiated =
			instantiate_function_template(replay_declaration, selected_args);
	}
	catch (...)
	{
		force_function_template_body_instantiation_ =
			saved_force_body_instantiation;
		throw;
	}
	force_function_template_body_instantiation_ =
		saved_force_body_instantiation;
	if (instantiated != NULL && best != instantiated)
		best->aliased_binding = instantiated;
	return instantiated != NULL ? instantiated : best;
}

Binding* Parser::wrap_inherited_constructor_if_needed(TypePtr record,
                                                      Binding* best)
{
	if (best == NULL ||
	    best->owner == NULL ||
	    best->owner->kind != ScopeKind::Class ||
	    best->type.get() == NULL ||
	    best->type->kind != pa11::TypeKind::Function ||
	    best->type->parameters.empty() ||
	    record->scope == NULL ||
	    best->owner == record->scope)
		return best;
	TypePtr base_record = pa11::record_type_for_scope(best->owner);
	base_record = base_record.get() != NULL
		? pa11::strip_cv(base_record) : TypePtr();
	if (base_record.get() == NULL ||
	    base_record->kind != pa11::TypeKind::Record ||
	    !record_has_base_type(record, base_record))
		return best;
	vector<TypePtr> params = best->type->parameters;
	params[0] = pa11::make_pointer(record);
	TypePtr fn_type = pa11::make_function(pa11::make_fundamental(FT_VOID),
	                                      params,
	                                      best->type->variadic);
	fn_type->cv = best->type->cv;
	fn_type->ref_qualifier = best->type->ref_qualifier;
	Binding* wrapper = NULL;
	map<string, vector<Binding*> >::iterator existing =
		record->scope->members.find(record->scope->name);
	if (existing != record->scope->members.end())
		for (size_t i = 0; i < existing->second.size(); ++i)
		{
			Binding* candidate = existing->second[i];
			if (candidate->kind == BindingKind::Function &&
			    candidate->owner == record->scope &&
			    candidate->type.get() != NULL &&
			    pa11::same_type(candidate->type, fn_type) &&
			    function_bodies_.find(candidate) != function_bodies_.end())
				return candidate;
		}
	wrapper = add_value(record->scope,
	                    BindingKind::Function,
	                    record->scope->name,
	                    fn_type);
	wrapper->is_inline_definition = true;
		wrapper->is_explicit = best->is_explicit;
		wrapper->is_constexpr = best->is_constexpr;
		wrapper->unwind_no = best->unwind_no;
		wrapper->dynamic_exception_spec = best->dynamic_exception_spec;
		wrapper->dynamic_exception_types = best->dynamic_exception_types;
		wrapper->ref_qualifier = best->ref_qualifier;
	vector<string> names(1, "this");
	map<Binding*, vector<string> >::const_iterator base_names =
		function_parameter_names_.find(best);
	for (size_t i = 1; i < params.size(); ++i)
		names.push_back(base_names != function_parameter_names_.end() &&
		                i < base_names->second.size() &&
		                !base_names->second[i].empty()
		                ? base_names->second[i]
		                : "__param" + to_string(i));
	function_parameter_names_[wrapper] = names;
	Node fn("function-definition " + qualified_decl_name(wrapper) + " " +
	        pa11::describe_type(fn_type));
	fn.binding = wrapper;
	fn.type = fn_type;
	Scope* function_scope =
		pa11::create_child_scope(record->scope, ScopeKind::Function, wrapper->name);
	Binding* this_binding =
		pa11::add_binding(function_scope, BindingKind::Parameter, "this", params[0]);
	Node this_node("parameter this " + pa11::describe_type(params[0]));
	this_node.binding = this_binding;
	this_node.type = params[0];
	add_child(fn, this_node);
	Node init("braced-init-list");
	for (size_t i = 1; i < params.size(); ++i)
	{
		Binding* param = pa11::add_binding(function_scope,
		                                   BindingKind::Parameter,
		                                   names[i],
		                                   params[i]);
		Node param_node("parameter " + names[i] + " " +
		                pa11::describe_type(params[i]));
		param_node.binding = param;
		param_node.type = params[i];
		add_child(fn, param_node);
		Node arg("id-expression lvalue " + pa11::describe_type(params[i]) +
		         " " + names[i]);
		arg.binding = param;
		arg.type = params[i];
		arg.category = ValueCategory::LValue;
		add_child(init, arg);
	}
	init.type = base_record;
	init.category = ValueCategory::LValue;
	Node body("compound-statement");
	Node base_action = make_base_init_action(base_record, &init);
	base_action.direct_call = best;
	base_action.token_text = "inherited-constructor";
	add_child(body, base_action);
	add_child(fn, body);
	remember_function_body(wrapper, fn);
	extra_lowir_nodes_.push_back(fn);
	return wrapper;
}

bool Parser::hosted_vector_initializer_list_constructor(TypePtr record,
                                                        Binding* ctor)
{
	bool hosted_vector = hosted_std_vector_record(record);
	bool function_type = ctor != NULL &&
	                     ctor->type.get() != NULL &&
	                     ctor->type->kind == pa11::TypeKind::Function;
	bool enough_params = function_type && ctor->type->parameters.size() >= 2;
	if (!hosted_compatibility_ ||
	    ctor == NULL ||
	    !hosted_vector ||
	    !function_type ||
	    !enough_params)
		return false;
	TypePtr param = ctor->type->parameters[1];
	if (pa11::is_reference_type(param))
		param = param->base;
	return is_std_initializer_list_type(pa11::strip_cv(param), NULL);
}

void Parser::finalize_constructor_candidate(TypePtr record, Binding*& best)
{
	bool hosted_vector_initializer_list_ctor =
		hosted_vector_initializer_list_constructor(record, best);
	bool defer_hosted_body =
		best != NULL &&
		!best->is_object_root &&
		(hosted_vector_initializer_list_ctor ||
		(hosted_extern_template_class_function(best) ||
		 (hosted_compatibility_ &&
		  best->is_inline_definition &&
		  !(best->owner != NULL &&
		    best->owner->kind == ScopeKind::Class &&
		    best->name == best->owner->name))));
	if (best != NULL &&
	    unevaluated_expression_depth_ == 0 &&
	    !defer_hosted_body)
	{
		parse_pending_function_body(best);
		parse_pending_member_body(best);
		ensure_function_body_extra_node(best);
	}
	best = canonical_function_binding(best);
	mark_template_specialization_demanded(best->type);
	if (best->is_defaulted &&
	    best->type->kind == pa11::TypeKind::Function &&
	    best->type->parameters.size() == 2 &&
	    pa11::is_reference_type(best->type->parameters[1]) &&
	    pa11::same_type(pa11::strip_cv(best->type->parameters[1]->base), record))
		ensure_copy_move_constructor(
			record,
			best->type->parameters[1]->kind == pa11::TypeKind::RValueReference);
	if (deleted_functions_.find(best) != deleted_functions_.end())
		throw runtime_error("call to deleted function");
}

Binding* Parser::resolve_constructor_candidate(TypePtr type,
                                               const vector<Expr>& args,
                                               bool copy_initialization,
                                               vector<Expr>& converted)
{
	TypePtr record = pa11::strip_cv(type);
	if (record->kind != pa11::TypeKind::Record || record->scope == NULL)
		throw runtime_error("constructor target is not record");
	prepare_constructor_template_candidates(record, args);
	ensure_copy_move_constructor_for_single_arg(record, args);
	if (!args.empty() && !record_has_aggregate_blocking_constructor(record))
	{
		validate_aggregate_braced_initialization(record);
		ensure_aggregate_constructor(record, args.size());
		}
			map<string, vector<Binding*> >::const_iterator found =
				record->scope->members.find(record->scope->name);
			bool found_zero_arg_constructor = false;
	if (found != record->scope->members.end())
		for (size_t i = 0; i < found->second.size(); ++i)
			if (found->second[i]->kind == BindingKind::Function &&
			    found->second[i]->type.get() != NULL &&
			    found->second[i]->type->kind == pa11::TypeKind::Function &&
			    constructor_accepts_argument_count(found->second[i], 0))
				found_zero_arg_constructor = true;
	if (!found_zero_arg_constructor && args.empty())
	{
		ensure_default_constructor(record, true);
		found = record->scope->members.find(record->scope->name);
	}
	if (found == record->scope->members.end())
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
	for (size_t i = 0; i < found->second.size(); ++i)
	{
		Binding* ctor = found->second[i];
		if (ctor->kind == BindingKind::Function &&
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
	                             found->second,
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
	{
		throw runtime_error("no matching constructor");
	}
	if (unevaluated_expression_depth_ == 0 &&
	    !hosted_vector_initializer_list_constructor(record, best))
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
		throw runtime_error("no matching constructor");
	map<string, vector<Binding*> >::const_iterator found =
		record->scope->members.find(record->scope->name);
	if (found == record->scope->members.end())
		throw runtime_error("no matching constructor");
	for (size_t i = 0; i < found->second.size(); ++i)
	{
		Binding* ctor = found->second[i];
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
	}
	throw runtime_error("no matching constructor");
}

Expr Parser::make_constructor_init_expr(TypePtr type,
                                        const vector<Expr>& args,
                                        bool copy_initialization)
{
	vector<Expr> constructor_args = args;
	for (size_t i = 0; i < constructor_args.size(); ++i)
		if (is_lambda_helper_expr(constructor_args[i]))
			constructor_args[i] = lambda_closure_expr(constructor_args[i]);
	TypePtr record = pa11::strip_cv(type);
	bool dependent_constructor_args = false;
	for (size_t i = 0; i < constructor_args.size(); ++i)
		if (type_is_template_dependent(constructor_args[i].type) ||
		    constructor_args[i].pack_expansion)
			dependent_constructor_args = true;
	if (record->kind == pa11::TypeKind::Record &&
	    (type_is_template_dependent(type) || dependent_constructor_args))
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
	Binding* ctor =
		resolve_constructor_candidate(type,
		                              constructor_args,
		                              copy_initialization,
		                              converted);
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
		if (!hosted_vector_initializer_list_constructor(record, ctor))
			parse_pending_member_body(ctor);
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

void Parser::substitute_lambda_helper_node_types(
	Node& node,
	const map<string, TypePtr>& substitutions,
	const map<Binding*, Binding*>& replacements) const
{
	map<Binding*, Binding*>::const_iterator binding =
		replacements.find(node.binding);
	if (binding != replacements.end())
		node.binding = binding->second;
	map<Binding*, Binding*>::const_iterator direct =
		replacements.find(node.direct_call);
	if (direct != replacements.end())
		node.direct_call = direct->second;
	for (map<string, TypePtr>::const_iterator it = substitutions.begin();
	     it != substitutions.end();
	     ++it)
		node.type = substitute_template_type_parameter(node.type,
		                                               it->first,
		                                               it->second);
	for (size_t i = 0; i < node.children.size(); ++i)
		substitute_lambda_helper_node_types(node.children[i],
		                                    substitutions,
		                                    replacements);
}

bool Parser::deduce_lambda_helper_substitutions(
	Binding* helper,
	const vector<Expr>& args,
	vector<TemplateArgument>& full_args,
	map<string, TypePtr>& substitutions,
	string& key)
{
	map<Binding*, vector<TemplateParameterInfo> >::const_iterator params_it =
		lambda_template_parameters_.find(helper);
	if (helper == NULL ||
	    helper->type.get() == NULL ||
	    helper->type->kind != pa11::TypeKind::Function ||
	    params_it == lambda_template_parameters_.end())
		return false;
	map<string, TypePtr> deduced;
	map<string, TypePtr> fixed;
	map<string, TemplateArgument> fixed_arguments;
	size_t deduce_count = min(args.size(), helper->type->parameters.size());
	for (size_t i = 0; i < deduce_count; ++i)
		if (!deduce_regular_template_call_argument(helper->type->parameters[i],
		                                           args[i],
		                                           deduced,
		                                           fixed,
		                                           fixed_arguments))
			return false;
	for (size_t i = 0; i < params_it->second.size(); ++i)
	{
		const TemplateParameterInfo& parameter = params_it->second[i];
		if (parameter.kind != TemplateParameterKind::Type ||
		    parameter.is_pack ||
		    parameter.name.empty())
			return false;
		map<string, TypePtr>::const_iterator found =
			deduced.find(parameter.name);
		if (found == deduced.end() || found->second.get() == NULL)
			return false;
		substitutions[parameter.name] = found->second;
		full_args.push_back(TemplateArgument::type_arg(found->second));
		key += "|";
		key += pa11::describe_type(found->second);
	}
	return true;
}

void Parser::materialize_lambda_helper_parameters(
	Binding* helper,
	Binding* binding,
	TypePtr concrete_type,
	Node& fn,
	Scope* function_scope,
	map<Binding*, Binding*>& replacements)
{
	vector<string> names;
	map<Binding*, vector<string> >::const_iterator old_names =
		function_parameter_names_.find(helper);
	for (size_t i = 0; i < concrete_type->parameters.size(); ++i)
	{
		string pname;
		if (old_names != function_parameter_names_.end() &&
		    i < old_names->second.size())
			pname = old_names->second[i];
		if (pname.empty())
			pname = "__param" + to_string(i);
		names.push_back(pname);
		Binding* param = pa11::add_binding(function_scope,
		                                   BindingKind::Parameter,
		                                   pname,
		                                   concrete_type->parameters[i]);
		if (i < fn.children.size())
		{
			if (fn.children[i].binding != NULL)
				replacements[fn.children[i].binding] = param;
			fn.children[i].line =
				"parameter " + pname + " " +
				pa11::describe_type(concrete_type->parameters[i]);
			fn.children[i].binding = param;
			fn.children[i].type = concrete_type->parameters[i];
		}
	}
	function_parameter_names_[binding] = names;
}

void Parser::substitute_lambda_helper_defaults(
	Binding* helper,
	Binding* binding,
	const map<string, TypePtr>& substitutions)
{
	map<Binding*, vector<Expr> >::const_iterator old_defaults =
		default_arguments_.find(helper);
	if (old_defaults == default_arguments_.end())
		return;
	vector<Expr> defaults = old_defaults->second;
	map<Binding*, Binding*> no_replacements;
	for (size_t i = 0; i < defaults.size(); ++i)
	{
		if (!defaults[i].valid)
			continue;
		for (map<string, TypePtr>::const_iterator it = substitutions.begin();
		     it != substitutions.end();
		     ++it)
			defaults[i].type =
				substitute_template_type_parameter(defaults[i].type,
				                                   it->first,
				                                   it->second);
		substitute_lambda_helper_node_types(defaults[i].node,
		                                    substitutions,
		                                    no_replacements);
		annotate_expr_node(defaults[i]);
	}
	default_arguments_[binding] = defaults;
}

Binding* Parser::instantiate_lambda_helper_call(Binding* helper,
                                                const vector<Expr>& args,
                                                vector<Expr>& converted)
{
	vector<TemplateArgument> full_args;
	map<string, TypePtr> substitutions;
	string key;
	if (!deduce_lambda_helper_substitutions(helper,
	                                       args,
	                                       full_args,
	                                       substitutions,
	                                       key))
		return NULL;

	pair<Binding*, string> cache_key(helper, key);
	map<pair<Binding*, string>, Binding*>::iterator cached =
		lambda_helper_specializations_.find(cache_key);
	if (cached != lambda_helper_specializations_.end())
	{
		vector<Binding*> overloads(1, cached->second);
		map<Binding*, vector<TemplateArgument> > no_explicit_args;
		return resolve_call_candidate(overloads,
		                              args,
		                              no_explicit_args,
		                              converted);
	}

	TypePtr concrete_type = helper->type;
	for (map<string, TypePtr>::const_iterator it = substitutions.begin();
	     it != substitutions.end();
	     ++it)
		concrete_type = substitute_template_type_parameter(concrete_type,
		                                                   it->first,
		                                                   it->second);

	string spec_name =
		helper->name + "__lambda_spec" +
		to_string(lambda_helper_specializations_.size());
	Binding* binding =
		add_value(helper->owner,
		          BindingKind::Function,
		          spec_name,
		          concrete_type);
	binding->language_linkage = helper->language_linkage;
	binding->is_inline_definition = true;
		binding->is_namespace_static = helper->is_namespace_static;
		binding->is_constexpr = helper->is_constexpr;
		binding->unwind_no = helper->unwind_no;
		binding->dynamic_exception_spec = helper->dynamic_exception_spec;
		binding->dynamic_exception_types = helper->dynamic_exception_types;
		binding->ref_qualifier = helper->ref_qualifier;
	function_template_specialization_arguments_[binding] = full_args;

	map<Binding*, Node>::const_iterator body_it = function_bodies_.find(helper);
	if (body_it == function_bodies_.end())
		throw runtime_error("missing lambda helper body");
	Node fn = body_it->second;
	fn.line = "function-definition " + qualified_decl_name(binding) + " " +
	          pa11::describe_type(concrete_type);
	fn.binding = binding;
	fn.type = concrete_type;

	Scope* function_scope =
		pa11::create_child_scope(helper->owner,
		                         ScopeKind::Function,
		                         spec_name);
	map<Binding*, Binding*> replacements;
	materialize_lambda_helper_parameters(helper,
	                                     binding,
	                                     concrete_type,
	                                     fn,
	                                     function_scope,
	                                     replacements);
	substitute_lambda_helper_node_types(fn, substitutions, replacements);
	substitute_lambda_helper_defaults(helper, binding, substitutions);

	remember_function_body(binding, fn);
	extra_lowir_nodes_.push_back(fn);
	lambda_helper_specializations_[cache_key] = binding;

	vector<Binding*> overloads(1, binding);
	map<Binding*, vector<TemplateArgument> > no_explicit_args;
	return resolve_call_candidate(overloads,
	                              args,
	                              no_explicit_args,
	                              converted);
}

Expr Parser::make_builtin_va_arg_expr(Expr list, TypePtr result)
{
	Conversion conv = convert_to(
		list,
		pa11::make_pointer(pa11::make_fundamental(FT_VOID)));
	if (!conv.viable)
		throw runtime_error("invalid __builtin_va_arg list");
	Expr out;
	out.valid = true;
	out.type = result;
	out.category = call_category(result);
	out.node = Node("builtin-va-arg-expression " +
	                value_category_name(out.category) + " " +
	                pa11::describe_type(result));
	add_child(out.node, conv.expr.node);
	annotate_expr_node(out);
	return out;
}

Expr Parser::make_builtin_offsetof_expr(TypePtr record,
                                        const vector<string>& members)
{
	TypePtr cur = pa11::strip_cv(record);
	if (type_is_template_dependent(cur))
	{
		Expr out;
		out.valid = true;
		out.type = pa11::make_fundamental(FT_UNSIGNED_LONG_INT);
		out.category = ValueCategory::PRValue;
		out.constant_expression = true;
		out.dependent_value_name =
			"__builtin_offsetof(" + pa11::describe_type(record) + ")";
		out.node = Node("offsetof-expression prvalue unsigned long int");
		out.node.token_text = out.dependent_value_name;
		annotate_expr_node(out);
		return out;
	}
	uint64_t offset = 0;
	for (size_t i = 0; i < members.size(); ++i)
	{
		cur = pa11::strip_cv(cur);
		if (cur->kind != pa11::TypeKind::Record || cur->scope == NULL)
			throw runtime_error("__builtin_offsetof on non-record");
		complete_template_record(cur);
		pa11::layout_record_type(cur);
		vector<Binding*> found =
			lookup_qualified_set(cur->scope,
			                     members[i],
			                     pa11::LOOKUP_VARIABLE);
		if (found.empty())
			throw runtime_error("__builtin_offsetof member not found");
		Binding* field = found[0];
		if (field->is_bit_field)
			throw runtime_error("__builtin_offsetof on bit-field unsupported");
		offset += field->member_offset;
		cur = field->type;
	}
	return make_sizeof_expr(offset);
}


}  // namespace internal
}  // namespace pa12
