#include "pa12_expr_semantics_support.h"

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
					template_parameter_placeholder_type(parameter);
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

}  // namespace internal
}  // namespace pa12
