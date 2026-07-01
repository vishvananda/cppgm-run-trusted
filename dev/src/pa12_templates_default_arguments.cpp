#include "pa12_internal.h"
#include "pa12_templates_instance_support.h"
#include "pa12_types_support.h"

#include <cstdint>
#include <stdexcept>

using namespace std;

namespace pa12 {
namespace internal {
size_t dependent_cache_hash_combine(size_t seed, size_t value);
size_t dependent_cache_string_hash(const string& value);
size_t dependent_cache_type_identity(TypePtr type);
size_t dependent_cache_template_argument_identity(
	const TemplateArgument& argument,
	int depth);

namespace {

void append_type_substitution_cache_key(
	size_t& key,
	const vector<map<string, TypePtr> >& substitutions)
{
	key = dependent_cache_hash_combine(key, substitutions.size());
	for (size_t i = 0; i < substitutions.size(); ++i)
	{
		key = dependent_cache_hash_combine(key, i);
		key = dependent_cache_hash_combine(key, substitutions[i].size());
		for (map<string, TypePtr>::const_iterator it = substitutions[i].begin();
		     it != substitutions[i].end();
		     ++it)
		{
			key = dependent_cache_hash_combine(
				key,
				dependent_cache_string_hash(it->first));
			key = dependent_cache_hash_combine(
				key,
				dependent_cache_type_identity(it->second));
		}
	}
}

void append_value_substitution_cache_key(
	size_t& key,
	const vector<map<string, TemplateArgument> >& substitutions)
{
	key = dependent_cache_hash_combine(key, substitutions.size());
	for (size_t i = 0; i < substitutions.size(); ++i)
	{
		key = dependent_cache_hash_combine(key, i);
		key = dependent_cache_hash_combine(key, substitutions[i].size());
		for (map<string, TemplateArgument>::const_iterator it =
			     substitutions[i].begin();
		     it != substitutions[i].end();
		     ++it)
		{
			key = dependent_cache_hash_combine(
				key,
				dependent_cache_string_hash(it->first));
			key = dependent_cache_hash_combine(
				key,
				dependent_cache_template_argument_identity(it->second,
				                                           0));
		}
	}
}

void append_pack_substitution_cache_key(
	size_t& key,
	const vector<set<string> >& substitutions)
{
	key = dependent_cache_hash_combine(key, substitutions.size());
	for (size_t i = 0; i < substitutions.size(); ++i)
	{
		key = dependent_cache_hash_combine(key, i);
		key = dependent_cache_hash_combine(key, substitutions[i].size());
		for (set<string>::const_iterator it = substitutions[i].begin();
		     it != substitutions[i].end();
		     ++it)
			key = dependent_cache_hash_combine(
				key,
				dependent_cache_string_hash(*it));
	}
}

bool template_argument_structurally_dependent(const TemplateArgument& arg)
{
	if (arg.kind == TemplateArgumentKind::Type)
		return type_structurally_dependent(arg.type);
	if (arg.kind == TemplateArgumentKind::Value)
		return arg.dependent || type_structurally_dependent(arg.type);
	if (arg.kind == TemplateArgumentKind::Template)
		return arg.template_declaration == NULL;
	for (size_t i = 0; i < arg.pack.size(); ++i)
		if (template_argument_structurally_dependent(arg.pack[i]))
			return true;
	return false;
}

}  // namespace

size_t Parser::default_template_argument_cache_key(
	TemplateDeclaration* declaration,
	size_t parameter_index,
	const vector<TemplateArgument>& completed_args) const
{
	size_t key = dependent_cache_hash_combine(
		0xd3f417,
		reinterpret_cast<uintptr_t>(declaration));
	key = dependent_cache_hash_combine(key, parameter_index);
	if (declaration != NULL)
	{
		key = dependent_cache_hash_combine(
			key,
			dependent_cache_string_hash(declaration->name));
		key = dependent_cache_hash_combine(
			key,
			reinterpret_cast<uintptr_t>(declaration->owner));
		key = dependent_cache_hash_combine(
			key,
			reinterpret_cast<uintptr_t>(declaration->lexical_scope));
		if (parameter_index < declaration->parameters.size())
		{
			const TemplateParameterInfo& parameter =
				declaration->parameters[parameter_index];
			key = dependent_cache_hash_combine(key, parameter.default_begin);
			key = dependent_cache_hash_combine(key, parameter.default_end);
			key = dependent_cache_hash_combine(
				key,
				dependent_cache_type_identity(parameter.type));
		}
	}
	key = dependent_cache_hash_combine(key, completed_args.size());
	for (size_t i = 0; i < completed_args.size(); ++i)
		key = dependent_cache_hash_combine(
			key,
			dependent_cache_template_argument_identity(completed_args[i],
			                                           0));
	append_type_substitution_cache_key(key, template_type_substitutions_);
	append_value_substitution_cache_key(key, template_value_substitutions_);
	append_pack_substitution_cache_key(key, template_type_parameter_packs_);
	key = dependent_cache_hash_combine(key, active_class_instantiations_.size());
	for (size_t i = 0; i < active_class_instantiations_.size(); ++i)
	{
		const ActiveClassInstantiation& active =
			active_class_instantiations_[i];
		key = dependent_cache_hash_combine(
			key,
			reinterpret_cast<uintptr_t>(active.declaration));
		key = dependent_cache_hash_combine(
			key,
			dependent_cache_string_hash(active.specialization_name));
		key = dependent_cache_hash_combine(
			key,
			dependent_cache_type_identity(active.type));
	}
	return dependent_cache_hash_combine(key,
	                                    member_function_template_generation_);
}

TemplateArgument Parser::parse_non_type_default_template_argument(
	const TemplateParameterInfo& parameter,
	const vector<TemplateArgument>& completed_args)
{
	bool default_dependent = type_is_template_dependent(parameter.type);
	for (size_t i = 0; i < completed_args.size(); ++i)
		if (template_argument_structurally_dependent(completed_args[i]))
			default_dependent = true;

	int save_expression_depth = template_argument_expression_depth_;
	++template_argument_expression_depth_;
	Expr expr;
	try
	{
		expr = parse_assignment_expression();
	}
	catch (...)
	{
		template_argument_expression_depth_ = save_expression_depth;
		if (!default_dependent)
			throw;
		expr = Expr();
	}
	template_argument_expression_depth_ = save_expression_depth;

	if (expr.valid && !expr.has_constant_value)
	{
		ConstexprValue value;
		if (try_evaluate_constexpr_expr(expr.node, value) && !value.is_object)
		{
			expr.has_constant_value = true;
			expr.constant_value = value.int_value;
			expr.node.has_constant_value = true;
			expr.node.constant_value = value.int_value;
		}
	}
	if (expr.valid && !expr.has_constant_value)
	{
		try
		{
			Conversion conv = convert_to(expr, pa11::make_fundamental(FT_BOOL));
			if (conv.viable && !conv.expr.has_constant_value)
			{
				ConstexprValue value;
				if (try_evaluate_constexpr_expr(conv.expr.node, value))
					apply_constexpr_value(conv.expr, value);
			}
			if (conv.viable && conv.expr.has_constant_value)
				expr = conv.expr;
		}
		catch (const runtime_error&)
		{
		}
	}
	if (!expr.has_constant_value &&
	    !default_dependent &&
	    expr.dependent_value_name.empty())
		throw runtime_error("invalid default template argument");

	if (expr.has_constant_value)
		return TemplateArgument::value_arg(expression_object_type(expr.type),
		                                   expr.constant_value);

	TemplateArgument arg = TemplateArgument::dependent_value_arg(parameter.type);
	if (expr.valid)
	{
		arg.value_name = expr.dependent_value_name;
		arg.value_owner_template_name =
			expr.dependent_value_owner_template_name;
		arg.value_member_name = expr.dependent_value_member_name;
		arg.value_negated = expr.dependent_value_negated;
		arg.value_owner_template_arguments =
			expr.dependent_value_owner_template_arguments;
	}
	return arg;
}

TemplateArgument Parser::parse_default_template_argument(
	TemplateDeclaration* declaration,
	size_t parameter_index,
	const vector<TemplateArgument>& completed_args)
{
	const TemplateParameterInfo& parameter =
		declaration->parameters[parameter_index];
	size_t cache_key =
		default_template_argument_cache_key(declaration,
		                                    parameter_index,
		                                    completed_args);
	map<size_t, TemplateArgument>::const_iterator cached =
		default_template_argument_cache_.find(cache_key);
	if (cached != default_template_argument_cache_.end())
		return cached->second;
	bool tokens_are_declaration_tokens =
		tokens_.size() == declaration_tokens_.size() &&
		(tokens_.empty() ||
		 (tokens_.front().source == declaration_tokens_.front().source &&
			  tokens_.back().source == declaration_tokens_.back().source));
	vector<Token> save_tokens;
	if (!tokens_are_declaration_tokens)
		save_tokens.swap(tokens_);
	size_t save_pos = pos_;
	vector<Scope*> save_scopes = scopes_;
	size_t save_type_subst_size = template_type_substitutions_.size();
	size_t save_value_subst_size = template_value_substitutions_.size();
	size_t save_pack_subst_size = template_type_parameter_packs_.size();
	bool save_default_argument = parsing_default_template_argument_;

	map<string, TypePtr> subst;
	map<string, TemplateArgument> value_subst;
	set<string> pack_subst;
	for (size_t i = 0; i < completed_args.size(); ++i)
	{
		if (declaration->parameters[i].name.empty())
			continue;
		const TemplateParameterInfo& completed_parameter =
			declaration->parameters[i];
		if (completed_parameter.is_pack)
		{
			subst[completed_parameter.name] =
				template_parameter_placeholder_type(
					completed_parameter);
			value_subst[completed_parameter.name] = completed_args[i];
			pack_subst.insert(completed_parameter.name);
		}
		else if (completed_parameter.kind == TemplateParameterKind::Type)
			subst[completed_parameter.name] = completed_args[i].type;
		else
			value_subst[completed_parameter.name] = completed_args[i];
	}

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
	pos_ = parameter.default_begin;
	parsing_default_template_argument_ = true;

	TemplateArgument arg;
	try
	{
		if (parameter.kind == TemplateParameterKind::Type)
		{
			arg = TemplateArgument::type_arg(parse_type_id());
			arg = substitute_template_argument(arg);
		}
		else if (parameter.kind == TemplateParameterKind::TemplateTemplate)
		{
			if (!try_parse_template_template_argument(arg))
				throw runtime_error("invalid default template argument");
		}
		else
		{
			arg = parse_non_type_default_template_argument(parameter,
			                                              completed_args);
		}
		if (pos_ != parameter.default_end)
			throw runtime_error("invalid default template argument");
	}
	catch (...)
	{
		if (!tokens_are_declaration_tokens)
			tokens_.swap(save_tokens);
		scopes_ = save_scopes;
		template_type_substitutions_.resize(save_type_subst_size);
		template_value_substitutions_.resize(save_value_subst_size);
		template_type_parameter_packs_.resize(save_pack_subst_size);
		parsing_default_template_argument_ = save_default_argument;
		pos_ = save_pos;
		throw;
	}

	if (!tokens_are_declaration_tokens)
		tokens_.swap(save_tokens);
	scopes_ = save_scopes;
	template_type_substitutions_.resize(save_type_subst_size);
	template_value_substitutions_.resize(save_value_subst_size);
	template_type_parameter_packs_.resize(save_pack_subst_size);
	parsing_default_template_argument_ = save_default_argument;
	pos_ = save_pos;
	default_template_argument_cache_[cache_key] = arg;
	return arg;
}

}  // namespace internal
}  // namespace pa12
