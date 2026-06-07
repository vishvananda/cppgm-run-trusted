#include "pa12_expr_semantics_support.h"

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
	complete_template_record(record);
	if (record->is_template_specialization)
		instantiate_member_function_templates(record);
	if (record->scope != NULL &&
	    record->scope->parent != NULL &&
	    record->scope->parent->kind == ScopeKind::Class)
	{
		TypePtr owner_record =
			pa11::record_type_for_scope(record->scope->parent);
		owner_record = owner_record.get() != NULL
			? pa11::strip_cv(owner_record) : TypePtr();
		if (owner_record.get() != NULL &&
		    owner_record->kind == pa11::TypeKind::Record &&
		    owner_record->is_template_specialization)
			instantiate_member_function_templates(owner_record);
	}
	if (record->scope != NULL)
	{
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
				if (seen_owners.insert(owner.get()).second)
					owners.push_back(owner);
			}
		}
		for (size_t i = 0; i < owners.size(); ++i)
			instantiate_member_function_templates(owners[i]);
	}
	if (record->scope != NULL)
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
						function_template_placeholders_.find(
							declaration->placeholder);
					TemplateDeclaration* saved_declaration =
						saved != function_template_placeholders_.end()
						? saved->second : NULL;
					function_template_placeholders_[declaration->placeholder] =
						declaration;
					instantiate_template_call_candidate(
						declaration->placeholder,
						explicit_args,
						deduction_args);
					if (saved_declaration != NULL)
						function_template_placeholders_[declaration->placeholder] =
							saved_declaration;
					else
						function_template_placeholders_.erase(
							declaration->placeholder);
				}
			}
	}
	ensure_copy_move_constructor_for_single_arg(record, args);
	if (!args.empty() && !record_has_aggregate_blocking_constructor(record))
	{
		validate_aggregate_braced_initialization(record);
		ensure_aggregate_constructor(record, args.size());
	}
	map<string, vector<Binding*> >::const_iterator found =
		record->scope->members.find(record->scope->name);
	if (found == record->scope->members.end() && args.empty())
	{
		ensure_default_constructor(record, true);
		found = record->scope->members.find(record->scope->name);
	}
	if (found == record->scope->members.end())
		throw runtime_error("no matching constructor");

	Binding* best = NULL;
	vector<int> best_ranks;
	vector<Expr> best_args;
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
	bool ambiguous = false;
	vector<Binding*> considered;
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
	for (size_t i = 0; i < found->second.size(); ++i)
	{
		Binding* ctor = found->second[i];
		if (has_user_declared_constructor &&
		    ctor->is_generated_default_constructor)
			continue;
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
		}
		if (active_function_matches(ctor))
			continue;
		if (ctor->kind != BindingKind::Function ||
		    ctor->type->kind != pa11::TypeKind::Function ||
		    ctor->type->parameters.empty())
			continue;
		Binding* duplicate = NULL;
		for (size_t j = 0; j < considered.size(); ++j)
			if (pa11::same_type(considered[j]->type, ctor->type))
			{
				duplicate = considered[j];
				bool ctor_template =
					function_template_placeholders_.find(ctor) !=
					function_template_placeholders_.end();
				bool duplicate_template =
					function_template_placeholders_.find(duplicate) !=
					function_template_placeholders_.end();
				TemplateDeclaration* ctor_origin =
					function_template_origin(function_template_placeholders_,
					                         ctor);
				TemplateDeclaration* duplicate_origin =
					function_template_origin(function_template_placeholders_,
					                         duplicate);
				if (ctor_template && duplicate_template &&
				    ctor_origin != duplicate_origin &&
				    !same_function_template_declaration_family(
					    ctor_origin,
					    duplicate_origin) &&
				    !function_template_more_specialized(
					    function_template_placeholders_,
					    ctor,
					    duplicate) &&
				    !function_template_more_specialized(
					    function_template_placeholders_,
					    duplicate,
					    ctor))
					duplicate = NULL;
				if (duplicate != NULL)
					break;
			}
		if (duplicate != NULL)
		{
			bool ctor_template =
				function_template_placeholders_.find(ctor) !=
				function_template_placeholders_.end();
			bool duplicate_template =
				function_template_placeholders_.find(duplicate) !=
				function_template_placeholders_.end();
			bool replace_duplicate = !ctor_template && duplicate_template;
			if (!replace_duplicate && ctor_template && !duplicate_template)
				;
			else if (!replace_duplicate)
				replace_duplicate =
					ctor->is_inline_definition &&
					!duplicate->is_inline_definition;
			if (!replace_duplicate &&
			    function_template_more_specialized(
				    function_template_placeholders_,
				    ctor,
				    duplicate))
				replace_duplicate = true;
			if (!replace_duplicate)
				continue;
			considered.erase(find(considered.begin(),
			                      considered.end(),
			                      duplicate));
		}
		considered.push_back(ctor);
		if (copy_initialization && ctor->is_explicit)
			continue;
		size_t param_count = ctor->type->parameters.size() - 1;
		if (args.size() > param_count && !ctor->type->variadic)
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
		size_t fixed_count = args.size() < param_count
			? args.size() : param_count;
		for (size_t j = 0; j < fixed_count; ++j)
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
			for (size_t j = param_count; j < args.size(); ++j)
				ranks.push_back(100);
		if (args.size() < param_count)
		{
			const vector<Expr>& defaults = default_arguments_[ctor];
			for (size_t j = args.size() + 1;
			     j < ctor->type->parameters.size();
			     ++j)
			{
				conv_args.push_back(defaults[j]);
			}
		}
		bool better = best == NULL || ranks_better(ranks, best_ranks);
		if (!better && best != NULL && ranks == best_ranks)
		{
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
				better = true;
				else if (ctor_template == best_template &&
				         function_template_more_specialized_for_call(
					         function_template_placeholders_,
					         ctor,
					         best,
					         args.size() + 1))
					better = true;
				else if (ctor_template == best_template &&
				         function_template_fewer_forwarding_lvalue_parameters_for_call(
					         function_template_placeholders_,
					         ctor,
					         best,
					         template_order_args))
					better = true;
		}
		if (better)
		{
			best = ctor;
			best_ranks = ranks;
			best_args = conv_args;
			ambiguous = false;
		}
		else if (pa11::same_type(best->type, ctor->type))
		{
			if (ctor->is_inline_definition && !best->is_inline_definition)
			{
				best = ctor;
				best_args = conv_args;
				ambiguous = false;
			}
		}
		else if (!ranks_better(best_ranks, ranks))
		{
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
				;
				else if (best_template == ctor_template &&
				         function_template_more_specialized_for_call(
					         function_template_placeholders_,
					         best,
					         ctor,
					         args.size() + 1))
					;
				else if (best_template == ctor_template &&
				         function_template_fewer_forwarding_lvalue_parameters_for_call(
					         function_template_placeholders_,
					         best,
					         ctor,
					         template_order_args))
					;
				else
					ambiguous = true;
		}
	}
		if (best == NULL || ambiguous)
			throw runtime_error("no matching constructor");
	if (best != NULL &&
	    unevaluated_expression_depth_ == 0 &&
	    (!best->is_inline_definition ||
	     function_bodies_.find(best) == function_bodies_.end()))
	{
		map<Binding*, TemplateDeclaration*>::iterator template_it =
			function_template_placeholders_.find(best);
		map<Binding*, vector<TemplateArgument> >::iterator args_it =
			function_template_specialization_arguments_.find(best);
		TemplateDeclaration* replay_declaration =
			template_it != function_template_placeholders_.end()
			? template_it->second : NULL;
		if (replay_declaration != NULL &&
		    !template_declaration_has_body(tokens_, replay_declaration))
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
		    template_declaration_has_body(tokens_, replay_declaration))
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
	    best->owner != NULL &&
	    best->owner->kind == ScopeKind::Class &&
	    best->type.get() != NULL &&
	    best->type->kind == pa11::TypeKind::Function &&
	    !best->type->parameters.empty() &&
	    record->scope != NULL &&
	    best->owner != record->scope)
	{
		TypePtr base_record = pa11::record_type_for_scope(best->owner);
		base_record = base_record.get() != NULL
			? pa11::strip_cv(base_record) : TypePtr();
		if (base_record.get() != NULL &&
		    base_record->kind == pa11::TypeKind::Record &&
		    record_has_base_type(record, base_record))
		{
			vector<TypePtr> params = best->type->parameters;
			params[0] = pa11::make_pointer(record);
			TypePtr fn_type =
				pa11::make_function(pa11::make_fundamental(FT_VOID),
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
					    function_bodies_.find(candidate) !=
						    function_bodies_.end())
					{
						wrapper = candidate;
						break;
					}
				}
			if (wrapper == NULL)
			{
				wrapper = add_value(record->scope,
				                    BindingKind::Function,
				                    record->scope->name,
				                    fn_type);
				wrapper->is_inline_definition = true;
				wrapper->is_explicit = best->is_explicit;
				wrapper->is_constexpr = best->is_constexpr;
				wrapper->unwind_no = best->unwind_no;
				wrapper->ref_qualifier = best->ref_qualifier;
				vector<string> names(1, "this");
				map<Binding*, vector<string> >::const_iterator base_names =
					function_parameter_names_.find(best);
				for (size_t i = 1; i < params.size(); ++i)
				{
					if (base_names != function_parameter_names_.end() &&
					    i < base_names->second.size() &&
					    !base_names->second[i].empty())
						names.push_back(base_names->second[i]);
					else
						names.push_back("__param" + to_string(i));
				}
				function_parameter_names_[wrapper] = names;
				Node fn("function-definition " +
				        qualified_decl_name(wrapper) + " " +
				        pa11::describe_type(fn_type));
				fn.binding = wrapper;
				fn.type = fn_type;
				Scope* function_scope =
					pa11::create_child_scope(record->scope,
					                         ScopeKind::Function,
					                         wrapper->name);
				Binding* this_binding =
					pa11::add_binding(function_scope,
					                  BindingKind::Parameter,
					                  "this",
					                  params[0]);
				Node this_node("parameter this " +
				               pa11::describe_type(params[0]));
				this_node.binding = this_binding;
				this_node.type = params[0];
				add_child(fn, this_node);
				Node init("braced-init-list");
				for (size_t i = 1; i < params.size(); ++i)
				{
					Binding* param =
						pa11::add_binding(function_scope,
						                  BindingKind::Parameter,
						                  names[i],
						                  params[i]);
					Node param_node("parameter " + names[i] + " " +
					                pa11::describe_type(params[i]));
					param_node.binding = param;
					param_node.type = params[i];
					add_child(fn, param_node);
					Node arg("id-expression lvalue " +
					         pa11::describe_type(params[i]) + " " +
					         names[i]);
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
			}
			best = wrapper;
		}
	}
	if (best != NULL && unevaluated_expression_depth_ == 0)
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
	vector<Expr> constructor_args = args;
	TypePtr record = pa11::strip_cv(type);
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
		parse_pending_member_body(ctor);
		if (ctor != NULL &&
		    ctor->is_generated_default_constructor &&
		    !ctor->is_inline_definition)
			ensure_default_constructor(type, true);
	}
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
		vector<Binding*> conversions;
		set<Scope*> seen;
		collect_conversion_functions(callee_object, seen, conversions);
		Expr selected;
		bool ambiguous = false;
		for (size_t i = 0; i < conversions.size(); ++i)
		{
			Binding* op = conversions[i];
			if (op->kind != BindingKind::Function ||
			    op->type->kind != pa11::TypeKind::Function ||
			    op->type->parameters.size() != 1)
				continue;
			TypePtr result = pa11::strip_cv(op->type->base);
			if (result->kind != pa11::TypeKind::Pointer ||
			    result->base.get() == NULL ||
			    result->base->kind != pa11::TypeKind::Function)
				continue;
			try
			{
				Expr member = make_member_expr(callee, op->name, ".");
				member.overloads.clear();
				member.overloads.push_back(op);
				member.binding = op;
				member.type = op->type;
				Expr converted = make_call_expr(member, vector<Expr>());
				Expr call = make_call_expr(converted, args);
				if (!selected.valid)
					selected = call;
				else
					ambiguous = true;
			}
			catch (const runtime_error&)
			{
			}
		}
		if (selected.valid && !ambiguous)
			return selected;
		if (ambiguous)
			throw runtime_error("ambiguous surrogate call");
	}
	if (callee.builtin_constant_p)
		return make_builtin_constant_call(args);
	if (!callee.overloads.empty() &&
	    callee.node.line.compare(0, 17, "member-expression") == 0 &&
	    !callee.node.children.empty())
	{
		prepare_member_call(callee, args);
	}
	else if (!callee.overloads.empty() &&
	         callee.node.line.compare(0, 13, "id-expression") == 0)
		filter_static_class_member_overloads(callee);
	for (map<Binding*, vector<TemplateArgument> >::iterator it =
		     callee.explicit_template_arguments.begin();
	     it != callee.explicit_template_arguments.end();
	     ++it)
	{
		vector<TemplateArgument> substituted;
		for (size_t i = 0; i < it->second.size(); ++i)
		{
			vector<TemplateArgument> expanded =
				expand_template_argument_pack(it->second[i]);
			for (size_t j = 0; j < expanded.size(); ++j)
			{
				TemplateArgument arg =
					substitute_template_argument(expanded[j]);
				if (arg.kind == TemplateArgumentKind::Pack)
					substituted.insert(substituted.end(),
					                   arg.pack.begin(),
					                   arg.pack.end());
				else
					substituted.push_back(arg);
			}
		}
		it->second = substituted;
	}
	bool dependent_template_call = false;
	for (size_t i = 0; i < args.size(); ++i)
		if (args[i].overloads.empty() &&
		    type_is_template_dependent(args[i].type))
			dependent_template_call = true;
	for (map<Binding*, vector<TemplateArgument> >::const_iterator it =
		     callee.explicit_template_arguments.begin();
	     it != callee.explicit_template_arguments.end();
	     ++it)
		if (template_arguments_dependent(it->second))
			dependent_template_call = true;
	materialize_template_lambda_arguments(callee, args);
	if (dependent_template_call && !callee.overloads.empty())
		return make_dependent_call_expr(callee, args);
	vector<Expr> converted;
	Binding* direct = NULL;
	if (!callee.overloads.empty())
		direct = resolve_call_candidate(callee.overloads,
		                                args,
		                                callee.explicit_template_arguments,
		                                converted);
	else if (callee.binding != NULL &&
	         callee.binding->kind == BindingKind::Function &&
	         !is_lambda_helper_expr(callee))
	{
		direct = callee.binding;
		converted = args;
	}
	Expr out;
	if (direct != NULL)
	{
		if (deleted_functions_.find(direct) != deleted_functions_.end())
			throw runtime_error("call to deleted function");
		if (unevaluated_expression_depth_ == 0)
		{
			parse_pending_function_body(direct);
			parse_pending_member_body(direct);
		}
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
			if (!callee.dependent_value_name.empty())
				return make_dependent_call_expr(callee, args);
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
	if (unevaluated_expression_depth_ == 0 &&
	    out.category == ValueCategory::PRValue &&
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
