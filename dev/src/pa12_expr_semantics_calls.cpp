#include "pa12_expr_semantics_support.h"
#include "pa12_types_support.h"

#include <algorithm>
#include <stdexcept>

using namespace std;

namespace pa12 {
namespace internal {

namespace {

bool same_parameter_family_ignoring_pointer_cv(TypePtr left, TypePtr right)
{
	if (same_template_signature_type(left, right))
		return true;
	TypePtr l = pa11::strip_cv(left);
	TypePtr r = pa11::strip_cv(right);
	if (l->kind == pa11::TypeKind::Pointer &&
	    r->kind == pa11::TypeKind::Pointer)
		return same_template_signature_type(pa11::strip_cv(l->base),
		                                    pa11::strip_cv(r->base));
	return false;
}

bool same_overload_parameter_signature(TypePtr left, TypePtr right)
{
	if (left.get() == NULL || right.get() == NULL ||
	    left->kind != pa11::TypeKind::Function ||
	    right->kind != pa11::TypeKind::Function)
		return false;
	if (left->cv != right->cv ||
	    left->variadic != right->variadic ||
	    left->ref_qualifier != right->ref_qualifier ||
	    left->parameters.size() != right->parameters.size())
		return false;
	for (size_t i = 0; i < left->parameters.size(); ++i)
		if (!pa11::same_type(left->parameters[i], right->parameters[i]) &&
		    !same_template_signature_type(left->parameters[i],
		                                  right->parameters[i]))
			return false;
	return true;
}

bool function_template_candidate_binding(
	Binding* binding,
	const map<Binding*, TemplateDeclaration*>& placeholders,
	const map<Binding*, vector<TemplateArgument> >& specializations)
{
	if (binding == NULL)
		return false;
	if (placeholders.find(binding) != placeholders.end() ||
	    specializations.find(binding) != specializations.end() ||
	    !binding->function_specialization_symbol.empty())
		return true;
	Binding* alias = binding->aliased_binding;
	return alias != NULL &&
	       (placeholders.find(alias) != placeholders.end() ||
	        specializations.find(alias) != specializations.end() ||
	        !alias->function_specialization_symbol.empty());
}

bool same_function_specialization_symbol(Binding* left, Binding* right)
{
	return left != NULL &&
	       right != NULL &&
	       !left->function_specialization_symbol.empty() &&
	       left->function_specialization_symbol ==
		       right->function_specialization_symbol;
}

bool has_function_template_origin(
	Binding* binding,
	const map<Binding*, TemplateDeclaration*>& placeholders)
{
	return function_template_origin(placeholders, binding) != NULL;
}

void append_normalized_object_specialization_arguments(
	vector<pa11::TemplateInstanceArgument>& out,
	const vector<pa11::TemplateInstanceArgument>& arguments)
{
	for (size_t i = 0; i < arguments.size(); ++i)
	{
		if (arguments[i].kind == pa11::TemplateInstanceArgumentKind::Pack)
		{
			append_normalized_object_specialization_arguments(out,
			                                                 arguments[i].pack);
			continue;
		}
		out.push_back(arguments[i]);
	}
}

bool same_object_specialization_type(TypePtr left, TypePtr right);
bool same_object_specialization_arguments(
	const vector<pa11::TemplateInstanceArgument>& left,
	const vector<pa11::TemplateInstanceArgument>& right);

bool same_object_specialization_argument(
	const pa11::TemplateInstanceArgument& left,
	const pa11::TemplateInstanceArgument& right)
{
	if (left.kind != right.kind)
		return false;
	if (left.kind == pa11::TemplateInstanceArgumentKind::Type)
		return same_object_specialization_type(left.type, right.type);
	if (left.kind == pa11::TemplateInstanceArgumentKind::Value)
		return left.dependent == right.dependent &&
		       left.value_negated == right.value_negated &&
		       left.value == right.value &&
		       left.value_name == right.value_name &&
		       left.value_owner_template_name ==
			       right.value_owner_template_name &&
		       left.value_member_name == right.value_member_name &&
		       same_object_specialization_type(left.type, right.type) &&
		       same_object_specialization_arguments(
			       left.value_owner_template_arguments,
			       right.value_owner_template_arguments);
	if (left.kind == pa11::TemplateInstanceArgumentKind::Template)
		return left.template_name == right.template_name &&
		       left.dependent == right.dependent;
	if (left.pack.size() != right.pack.size())
		return false;
	for (size_t i = 0; i < left.pack.size(); ++i)
		if (!same_object_specialization_argument(left.pack[i],
		                                         right.pack[i]))
			return false;
	return true;
}

bool same_object_specialization_arguments(
	const vector<pa11::TemplateInstanceArgument>& left,
	const vector<pa11::TemplateInstanceArgument>& right)
{
	vector<pa11::TemplateInstanceArgument> flat_left;
	vector<pa11::TemplateInstanceArgument> flat_right;
	append_normalized_object_specialization_arguments(flat_left, left);
	append_normalized_object_specialization_arguments(flat_right, right);
	if (flat_left.size() != flat_right.size())
		return false;
	for (size_t i = 0; i < flat_left.size(); ++i)
		if (!same_object_specialization_argument(flat_left[i],
		                                         flat_right[i]))
			return false;
	return true;
}

bool same_object_specialization_type(TypePtr left, TypePtr right)
{
	if (left.get() == NULL || right.get() == NULL)
		return left.get() == right.get();
	if (pa11::same_type(left, right))
		return true;
	TypePtr l = pa11::strip_cv(left);
	TypePtr r = pa11::strip_cv(right);
	return l->kind == pa11::TypeKind::Record &&
	       r->kind == pa11::TypeKind::Record &&
	       l->is_template_specialization &&
	       r->is_template_specialization &&
	       !l->template_primary_name.empty() &&
	       l->template_primary_name == r->template_primary_name &&
	       same_object_specialization_arguments(l->template_arguments,
	                                            r->template_arguments);
}

TypePtr reference_binding_target(TypePtr type)
{
	TypePtr bare = type.get() != NULL ? pa11::strip_cv(type) : TypePtr();
	if (bare.get() == NULL ||
	    (bare->kind != pa11::TypeKind::LValueReference &&
	     bare->kind != pa11::TypeKind::RValueReference))
		return TypePtr();
	return pa11::strip_cv(bare->base);
}

bool same_reference_binding_target(TypePtr left, TypePtr right)
{
	TypePtr l = reference_binding_target(left);
	TypePtr r = reference_binding_target(right);
	return l.get() != NULL && r.get() != NULL &&
	       same_object_specialization_type(l, r);
}

int reference_binding_tie_break(Binding* candidate,
                                const vector<Expr>& candidate_args,
                                Binding* current,
                                const vector<Expr>& current_args)
{
	if (candidate == NULL || current == NULL ||
	    candidate->type.get() == NULL || current->type.get() == NULL ||
	    candidate->type->kind != pa11::TypeKind::Function ||
	    current->type->kind != pa11::TypeKind::Function ||
	    candidate->type->parameters.size() !=
		    current->type->parameters.size())
		return 0;
	int score = 0;
	size_t first =
		candidate->owner != NULL &&
		candidate->owner->kind == ScopeKind::Class &&
		!candidate->is_static_member ? 1 : 0;
	for (size_t i = first; i < candidate->type->parameters.size(); ++i)
	{
		if (i >= candidate_args.size() || i >= current_args.size())
			continue;
		TypePtr cparam = pa11::strip_cv(candidate->type->parameters[i]);
		TypePtr bparam = pa11::strip_cv(current->type->parameters[i]);
		if (!same_reference_binding_target(cparam, bparam))
			continue;
		bool candidate_rvalue =
			cparam->kind == pa11::TypeKind::RValueReference;
		bool current_rvalue =
			bparam->kind == pa11::TypeKind::RValueReference;
		if (candidate_rvalue == current_rvalue)
			continue;
		if (candidate_args[i].category == ValueCategory::LValue ||
		    current_args[i].category == ValueCategory::LValue)
			continue;
		score += candidate_rvalue ? 1 : -1;
	}
	if (score > 0)
		return 1;
	if (score < 0)
		return -1;
	return 0;
}
}  // namespace

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
	bool tokens_are_declaration_tokens =
		tokens_.size() == declaration_tokens_.size() &&
		(tokens_.empty() ||
		 (tokens_.front().source == declaration_tokens_.front().source &&
		  tokens_.back().source == declaration_tokens_.back().source));
	vector<Token> save_tokens;
	if (!tokens_are_declaration_tokens)
		save_tokens = tokens_;
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
			if (!tokens_are_declaration_tokens)
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
	if (!tokens_are_declaration_tokens)
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
			if (implicit_object_arg)
			{
				TypePtr source =
					pa11::strip_cv(lvalue_to_rvalue_type(conv_args[j].type));
				TypePtr target = pa11::strip_cv(fn->type->parameters[j]);
				if (source.get() != NULL &&
				    target.get() != NULL &&
				    source->kind == pa11::TypeKind::Pointer &&
				    target->kind == pa11::TypeKind::Pointer &&
				    source->base.get() != NULL &&
				    target->base.get() != NULL)
				{
					TypePtr source_record = pa11::strip_cv(source->base);
					TypePtr target_record = pa11::strip_cv(target->base);
					bool related_object =
						same_object_specialization_type(source->base,
						                                target->base);
					if (!related_object &&
					    source_record.get() != NULL &&
					    target_record.get() != NULL &&
					    source_record->kind == pa11::TypeKind::Record &&
					    target_record->kind == pa11::TypeKind::Record)
						related_object =
							record_base_distance(source_record,
							                     target_record) < 1000000;
					if (related_object)
					{
						unsigned source_cv =
							source->base->kind == pa11::TypeKind::Cv
							? source->base->cv : pa11::CV_NONE;
						if (source_cv == pa11::CV_NONE &&
						    conv_args[j].binding != NULL &&
						    conv_args[j].binding->name == "this")
						{
							for (size_t ai = active_functions_.size(); ai > 0; --ai)
							{
								Binding* active = active_functions_[ai - 1];
								if (active == NULL ||
								    active->type.get() == NULL ||
								    active->type->kind != pa11::TypeKind::Function ||
								    active->type->parameters.empty())
									continue;
								TypePtr active_this =
									pa11::strip_cv(active->type->parameters[0]);
								if (active_this.get() == NULL ||
								    active_this->kind != pa11::TypeKind::Pointer ||
								    active_this->base.get() == NULL)
									continue;
								TypePtr active_record =
									pa11::strip_cv(active_this->base);
								if (active_record.get() == NULL ||
								    source_record.get() == NULL ||
								    active_record->kind != pa11::TypeKind::Record ||
								    source_record->kind != pa11::TypeKind::Record ||
								    active_record->scope != source_record->scope)
									continue;
								source_cv =
									active_this->base->kind == pa11::TypeKind::Cv
									? active_this->base->cv : pa11::CV_NONE;
								break;
							}
						}
						unsigned target_cv =
							target->base->kind == pa11::TypeKind::Cv
							? target->base->cv : pa11::CV_NONE;
						if ((target_cv & source_cv) != source_cv)
							return false;
					}
				}
			}
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
				    same_object_specialization_type(source->base,
				                                    target->base))
			{
				unsigned source_cv = source->base->kind == pa11::TypeKind::Cv
					? source->base->cv : pa11::CV_NONE;
				unsigned target_cv = target->base->kind == pa11::TypeKind::Cv
					? target->base->cv : pa11::CV_NONE;
				if ((target_cv & source_cv) != source_cv)
					return false;
				unsigned added_cv = target_cv & ~source_cv;
				int rank = 0;
				if ((added_cv & pa11::CV_CONST) != 0)
					++rank;
				if ((added_cv & pa11::CV_VOLATILE) != 0)
					++rank;
				Expr converted = conv_args[j];
				converted.type = fn->type->parameters[j];
				converted.category = ValueCategory::PRValue;
				converted.node = Node("cast-expression prvalue " +
				                      pa11::describe_type(converted.type));
				add_child(converted.node, conv_args[j].node);
				annotate_expr_node(converted);
				conv = Conversion(true, rank, converted);
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
				{
					fn = instantiate_template_call_candidate(fn,
					                                         explicit_template_arguments,
					                                         args);
			}
		if (fn == NULL)
			continue;
		if (fn->type->kind != pa11::TypeKind::Function)
			continue;
			Binding* duplicate = duplicate_function_candidate(considered, fn);
		bool duplicate_handled = false;
		if (duplicate != NULL &&
		    duplicate->name == fn->name &&
		    duplicate->is_static_member == fn->is_static_member &&
		    same_overload_parameter_signature(duplicate->type, fn->type))
		{
			vector<Binding*>::iterator duplicate_pos =
				find(considered.begin(), considered.end(), duplicate);
			if (fn->is_inline_definition &&
			    !duplicate->is_inline_definition &&
			    duplicate_pos != considered.end())
			{
				considered.erase(duplicate_pos);
				duplicate = NULL;
			}
			else
			{
				bool fn_template =
					function_template_candidate_binding(
						fn,
						function_template_placeholders_,
						function_template_specialization_arguments_);
				bool duplicate_template =
					function_template_candidate_binding(
						duplicate,
						function_template_placeholders_,
						function_template_specialization_arguments_);
				if (fn_template && duplicate_template)
				{
					TemplateDeclaration* fn_origin =
						function_template_origin(
							function_template_placeholders_,
							fn);
					TemplateDeclaration* duplicate_origin =
						function_template_origin(
							function_template_placeholders_,
							duplicate);
					bool fn_concrete_duplicate =
						fn->type.get() != NULL &&
						duplicate->type.get() != NULL &&
						!type_structurally_dependent(fn->type) &&
						type_structurally_dependent(duplicate->type);
					if (!fn_concrete_duplicate &&
					    same_function_specialization_symbol(fn,
					                                        duplicate))
					{
						duplicate_handled =
							duplicate_origin != NULL ||
							fn_origin == NULL;
					}
					else
						duplicate_handled =
							!fn_concrete_duplicate &&
							(fn->aliased_binding == duplicate ||
							 duplicate->aliased_binding == fn ||
							 same_function_template_declaration_family(
								 fn_origin,
								 duplicate_origin));
				}
				else
					duplicate_handled = fn_template || !duplicate_template;
			}
		}
		if (duplicate_handled)
			continue;
		if (duplicate != NULL)
		{
			bool fn_template =
				function_template_candidate_binding(
					fn,
					function_template_placeholders_,
					function_template_specialization_arguments_);
			bool duplicate_template =
				function_template_candidate_binding(
					duplicate,
					function_template_placeholders_,
					function_template_specialization_arguments_);
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
				function_template_candidate_binding(
					fn,
					function_template_placeholders_,
					function_template_specialization_arguments_);
			bool duplicate_template =
				function_template_candidate_binding(
					duplicate,
					function_template_placeholders_,
					function_template_specialization_arguments_);
				bool replace_duplicate =
					!fn_template && duplicate_template;
				int fn_explicit_score =
					explicit_template_argument_match_score(
						fn,
						explicit_template_arguments);
				int duplicate_explicit_score =
					explicit_template_argument_match_score(
						duplicate,
						explicit_template_arguments);
				if (!replace_duplicate &&
				    fn_explicit_score > duplicate_explicit_score)
					replace_duplicate = true;
				if (!replace_duplicate &&
				    same_function_specialization_symbol(fn,
				                                        duplicate) &&
				    has_function_template_origin(
					    fn,
					    function_template_placeholders_) &&
				    !has_function_template_origin(
					    duplicate,
					    function_template_placeholders_))
					replace_duplicate = true;
				if (!replace_duplicate && fn_template && !duplicate_template)
					;
				else if (!replace_duplicate &&
				         fn_template &&
				         duplicate_template &&
				         fn->type.get() != NULL &&
				         duplicate->type.get() != NULL &&
				         !type_structurally_dependent(fn->type) &&
				         type_structurally_dependent(duplicate->type))
					replace_duplicate = true;
				else if (!replace_duplicate)
					replace_duplicate =
						fn->is_inline_definition && !duplicate->is_inline_definition;
				if (!replace_duplicate &&
				    fn_explicit_score >= duplicate_explicit_score &&
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
				bool converted = false;
				try
				{
					converted = convert_call_candidate_arguments(fn,
					                                             args,
					                                             conv_args,
					                                             ranks,
					                                             object_rank);
				}
					catch (const runtime_error&)
					{
						converted = false;
					}
			if (!converted)
				continue;
							add_variadic_argument_ranks(fn, args.size(), ranks);
			if (object_rank < 0)
				object_rank = 0;
		bool better = best == NULL || ranks_better(ranks, best_ranks);
		if (!better && best != NULL && ranks == best_ranks &&
		    object_rank == best_object_rank)
		{
			int reference_tie =
				reference_binding_tie_break(fn,
				                            conv_args,
				                            best,
				                            best_args);
			bool fn_template =
				function_template_candidate_binding(
					fn,
					function_template_placeholders_,
					function_template_specialization_arguments_);
			bool best_template =
				function_template_candidate_binding(
					best,
					function_template_placeholders_,
					function_template_specialization_arguments_);
			bool fn_concrete_template =
				fn_template &&
				fn->type.get() != NULL &&
				!type_structurally_dependent(fn->type);
			bool fn_dependent_template =
				fn_template &&
				fn->type.get() != NULL &&
				type_structurally_dependent(fn->type);
			bool best_concrete_template =
				best_template &&
				best->type.get() != NULL &&
				!type_structurally_dependent(best->type);
			bool best_dependent_template =
				best_template &&
				best->type.get() != NULL &&
				type_structurally_dependent(best->type);
			if (reference_tie > 0)
				better = true;
			else if (reference_tie < 0)
				;
			else if (fn_concrete_template && best_dependent_template)
				better = true;
			else if (fn_dependent_template && best_concrete_template)
				;
			else if (fn->is_inline_definition && !best->is_inline_definition)
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
				         !function_template_candidate_binding(
					         best,
					         function_template_placeholders_,
					         function_template_specialization_arguments_) &&
				         function_template_candidate_binding(
					         fn,
					         function_template_placeholders_,
					         function_template_specialization_arguments_))
					indistinguishable = false;
				else if (object_rank == best_object_rank &&
				         function_template_candidate_binding(
					         best,
					         function_template_placeholders_,
					         function_template_specialization_arguments_) &&
				         function_template_candidate_binding(
					         fn,
					         function_template_placeholders_,
					         function_template_specialization_arguments_) &&
				         best->type.get() != NULL &&
				         fn->type.get() != NULL &&
				         !type_structurally_dependent(best->type) &&
				         type_structurally_dependent(fn->type))
					indistinguishable = false;
				else if (object_rank == best_object_rank &&
				         function_template_candidate_binding(
					         best,
					         function_template_placeholders_,
					         function_template_specialization_arguments_) &&
				         function_template_candidate_binding(
					         fn,
					         function_template_placeholders_,
					         function_template_specialization_arguments_) &&
				         best->type.get() != NULL &&
				         fn->type.get() != NULL &&
				         type_structurally_dependent(best->type) &&
				         !type_structurally_dependent(fn->type))
					better = true;
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
					else if (object_rank == best_object_rank &&
					         reference_binding_tie_break(best,
					                                     best_args,
					                                     fn,
					                                     conv_args) > 0)
						indistinguishable = false;
						else if (object_rank == best_object_rank)
							indistinguishable = true;
				}
				else
				{
					bool tag_dispatch_better = false;
					bool tag_dispatch_ordered = false;
					if (best->name == fn->name &&
					    best->owner == fn->owner &&
					    best->type.get() != NULL &&
					    fn->type.get() != NULL &&
					    best->type->kind == pa11::TypeKind::Function &&
					    fn->type->kind == pa11::TypeKind::Function &&
					    best->type->parameters.size() ==
						    fn->type->parameters.size() &&
					    best->type->parameters.size() == args.size() &&
					    !args.empty())
					{
						size_t tag_index =
							best->type->parameters.size() - 1;
						bool leading_same_family = true;
						size_t first = best->owner != NULL &&
						               best->owner->kind == ScopeKind::Class &&
						               !best->is_static_member ? 1 : 0;
						for (size_t pi = first; pi < tag_index; ++pi)
							if (!same_parameter_family_ignoring_pointer_cv(
								    best->type->parameters[pi],
								    fn->type->parameters[pi]))
								leading_same_family = false;
						TypePtr arg_record =
							pa11::strip_cv(expression_object_type(args.back().type));
						TypePtr best_tag =
							pa11::strip_cv(best->type->parameters[tag_index]);
						TypePtr fn_tag =
							pa11::strip_cv(fn->type->parameters[tag_index]);
						if (leading_same_family &&
						    arg_record.get() != NULL &&
						    arg_record->kind == pa11::TypeKind::Record &&
						    best_tag.get() != NULL &&
						    best_tag->kind == pa11::TypeKind::Record &&
						    fn_tag.get() != NULL &&
						    fn_tag->kind == pa11::TypeKind::Record)
						{
							int best_tag_distance =
								record_base_distance(arg_record, best_tag);
							int fn_tag_distance =
								record_base_distance(arg_record, fn_tag);
							if (best_tag_distance < 1000000 &&
							    fn_tag_distance < 1000000 &&
							    best_tag_distance != fn_tag_distance)
							{
								tag_dispatch_ordered = true;
								tag_dispatch_better =
									fn_tag_distance < best_tag_distance;
							}
						}
					}
					if (tag_dispatch_better)
						better = true;
					else if (!tag_dispatch_ordered)
						indistinguishable = true;
				}
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
		throw runtime_error("cannot resolve call overload");
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
	bool selected_dependent_return =
		best != NULL &&
		best->type.get() != NULL &&
		best->type->kind == pa11::TypeKind::Function &&
		type_is_template_dependent(best->type->base);
	if (best != NULL &&
	    (unevaluated_expression_depth_ == 0 || selected_dependent_return) &&
	    (!best->is_inline_definition ||
	     function_bodies_.find(best) == function_bodies_.end() ||
	     selected_dependent_return))
	{
		map<Binding*, TemplateDeclaration*>::iterator template_it =
			function_template_placeholders_.find(best);
		map<Binding*, vector<TemplateArgument> >::iterator args_it =
			function_template_specialization_arguments_.find(best);
			bool selected_completion_active =
				template_it != function_template_placeholders_.end() &&
				args_it !=
					function_template_specialization_arguments_.end() &&
				template_it->second->completing_specializations.count(
					template_argument_key(args_it->second)) != 0;
			bool selected_has_body =
				function_bodies_.find(best) != function_bodies_.end();
			TemplateDeclaration* replay_declaration =
				template_it != function_template_placeholders_.end()
				? template_it->second : NULL;
		if (replay_declaration != NULL &&
			    !template_declaration_has_body(declaration_tokens_,
			                                   replay_declaration))
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
							    !template_declaration_has_body(
								    declaration_tokens_,
								    candidate) ||
						    candidate->generic_function_type.get() == NULL)
							continue;
						bool parameters_match =
							expr_template_parameter_lists_match(
								candidate->parameters,
								replay_declaration->parameters);
						bool signature_matches =
							same_template_signature_type(
								candidate->generic_function_type,
								replay_declaration->generic_function_type);
						if (!parameters_match && !signature_matches)
							continue;
						if (compatible_body == NULL && signature_matches)
							compatible_body = candidate;
						if (!signature_matches)
							continue;
						if (replay_declaration->class_template_member &&
						    !candidate->class_template_member)
							continue;
						if (args_it !=
						    function_template_specialization_arguments_.end())
						{
							size_t required_arguments = 0;
							for (size_t pi = 0;
							     pi < candidate->parameters.size();
							     ++pi)
								if (!candidate->parameters[pi].has_default &&
								    !candidate->parameters[pi].is_pack)
									++required_arguments;
							if (args_it->second.size() < required_arguments)
								continue;
							try
							{
								complete_template_arguments(candidate,
								                            args_it->second);
							}
							catch (const exception&)
							{
								continue;
							}
						}
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
				TemplateDeclaration* clone_ptr = NULL;
				for (size_t ti = 0; ti < template_declarations_.size(); ++ti)
				{
					TemplateDeclaration* candidate =
						template_declarations_[ti].get();
					if (candidate != NULL &&
					    candidate != compatible_body &&
					    candidate->name == compatible_body->name &&
					    candidate->decl_begin ==
						    compatible_body->decl_begin &&
					    candidate->decl_end ==
						    compatible_body->decl_end &&
					    candidate->owner == replay_declaration->owner &&
					    candidate->placeholder ==
						    replay_declaration->placeholder &&
					    candidate->class_template_member ==
						    replay_declaration
							    ->class_template_member)
					{
						clone_ptr = candidate;
						break;
					}
				}
				if (clone_ptr == NULL)
				{
					unique_ptr<TemplateDeclaration> clone(
						new TemplateDeclaration(*compatible_body));
					clone->owner = replay_declaration->owner;
					clone->placeholder =
						replay_declaration->placeholder;
					clone->class_template_member =
						replay_declaration->class_template_member;
					clone->outer_type_substitutions =
						replay_declaration->outer_type_substitutions;
					clone->outer_value_substitutions =
						replay_declaration->outer_value_substitutions;
					clone->function_specializations.clear();
					clone->completing_specializations.clear();
					clone_ptr = clone.get();
					template_declarations_.push_back(std::move(clone));
				}
					replay_declaration = clone_ptr;
				}
					if (!template_declaration_has_body(declaration_tokens_,
					                                   replay_declaration) &&
				    args_it != function_template_specialization_arguments_.end())
				{
					for (size_t di = 0;
					     di < template_declarations_.size();
					     ++di)
					{
							TemplateDeclaration* candidate =
								template_declarations_[di].get();
							if (candidate == replay_declaration ||
							    candidate == NULL ||
						    candidate->name != replay_declaration->name ||
							    !template_declaration_has_body(
								    declaration_tokens_,
							                                   candidate))
							continue;
						Binding* instantiated = NULL;
						try
						{
							instantiated = instantiate_function_template(
								candidate,
								args_it->second);
						}
						catch (const exception&)
						{
							continue;
						}
						if (instantiated == NULL ||
						    instantiated->type.get() == NULL ||
						    best->type.get() == NULL ||
						    !pa11::same_type(instantiated->type,
						                     best->type))
						{
							continue;
						}
						if (best != instantiated)
							best->aliased_binding = instantiated;
						best = instantiated;
						replay_declaration = candidate;
						break;
					}
				}
			}
		if (!selected_completion_active &&
		    template_it != function_template_placeholders_.end() &&
		    args_it != function_template_specialization_arguments_.end() &&
		    !(hosted_compatibility_ &&
			      replay_declaration != NULL &&
			      replay_declaration->has_definition &&
			      !best->is_object_root &&
			      !selected_dependent_return &&
			      selected_has_body) &&
			    (template_declaration_has_body(declaration_tokens_,
			                                   replay_declaration) ||
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
					Binding* instantiated = NULL;
					bool signature_only_replay =
						unevaluated_expression_depth_ != 0;
					bool saved_force_body_instantiation =
						force_function_template_body_instantiation_;
					if (signature_only_replay)
						++function_template_candidate_instantiation_depth_;
					else
						force_function_template_body_instantiation_ = true;
					try
					{
						instantiated =
							instantiate_function_template(replay_declaration,
							                              selected_args);
					}
					catch (...)
					{
						if (signature_only_replay)
							--function_template_candidate_instantiation_depth_;
						else
							force_function_template_body_instantiation_ =
								saved_force_body_instantiation;
						throw;
					}
						if (signature_only_replay)
							--function_template_candidate_instantiation_depth_;
						else
							force_function_template_body_instantiation_ =
								saved_force_body_instantiation;
					if (instantiated != NULL)
					{
				if (best != instantiated)
					best->aliased_binding = instantiated;
				best = instantiated;
			}
		}
	}
		bool final_completion_active = false;
		if (best != NULL)
		{
			map<Binding*, TemplateDeclaration*>::iterator template_it =
				function_template_placeholders_.find(best);
			map<Binding*, vector<TemplateArgument> >::iterator args_it =
				function_template_specialization_arguments_.find(best);
			final_completion_active =
				template_it != function_template_placeholders_.end() &&
				args_it !=
					function_template_specialization_arguments_.end() &&
				template_it->second->completing_specializations.count(
					template_argument_key(args_it->second)) != 0;
		}
		if (!final_completion_active &&
		    best != NULL &&
		    unevaluated_expression_depth_ == 0 &&
		    function_template_candidate_instantiation_depth_ == 0 &&
		    !defer_hosted_function_body(best) &&
		    !(hosted_compatibility_ &&
	      hosted_library_function(best) &&
	      best->is_inline_definition &&
	      !best->is_object_root))
	{
		parse_pending_function_body(best);
		parse_pending_member_body(best);
		ensure_function_body_extra_node(best);
		if (best->aliased_binding != NULL)
		{
			parse_pending_function_body(best->aliased_binding);
			parse_pending_member_body(best->aliased_binding);
			ensure_function_body_extra_node(best->aliased_binding);
		}
		}
	return canonical_function_binding(best);
}

}  // namespace internal
}  // namespace pa12
