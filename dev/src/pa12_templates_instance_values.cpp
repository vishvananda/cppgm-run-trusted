#include "pa12_templates_instance_support.h"

#include <algorithm>
#include <cstdint>
#include <functional>
#include <sstream>
#include <stdexcept>
#include <utility>

#include "posttoken_pipeline.h"
#include "pp_token.h"

using namespace std;

namespace pa12 {
namespace internal {
namespace {

size_t value_eval_hash_combine(size_t seed, size_t value)
{
	return seed ^ (value + 0x9e3779b97f4a7c15ULL + (seed << 6) +
	               (seed >> 2));
}

size_t value_eval_string_hash(const string& value)
{
	return value_eval_hash_combine(value.size(), hash<string>()(value));
}

size_t value_eval_type_hash(TypePtr type)
{
	type = type.get() != NULL ? pa11::strip_cv(type) : TypePtr();
	if (type.get() == NULL)
		return 0;
	size_t out = reinterpret_cast<uintptr_t>(type.get());
	out = value_eval_hash_combine(out, static_cast<size_t>(type->kind));
	out = value_eval_hash_combine(out, type->is_template_specialization);
	out = value_eval_hash_combine(out, type->is_dependent_typename);
	out = value_eval_hash_combine(
		out,
		value_eval_string_hash(type->template_primary_name));
	return out;
}

size_t value_eval_instance_arg_hash(const pa11::TemplateInstanceArgument& arg,
                                    int depth);

size_t value_eval_template_arg_hash(const TemplateArgument& arg, int depth)
{
	size_t out = static_cast<size_t>(arg.kind);
	if (depth > 8)
		return value_eval_hash_combine(out, 0xace);
	out = value_eval_hash_combine(out, value_eval_type_hash(arg.type));
	out = value_eval_hash_combine(
		out,
		reinterpret_cast<uintptr_t>(arg.template_declaration));
	out = value_eval_hash_combine(
		out,
		reinterpret_cast<uintptr_t>(arg.value_binding));
	out = value_eval_hash_combine(out,
	                              value_eval_string_hash(arg.value_name));
	out = value_eval_hash_combine(
		out,
		value_eval_string_hash(arg.value_owner_template_name));
	out = value_eval_hash_combine(
		out,
		value_eval_string_hash(arg.value_member_name));
	out = value_eval_hash_combine(out, arg.value);
	out = value_eval_hash_combine(out, arg.dependent);
	out = value_eval_hash_combine(out, arg.value_negated);
	out = value_eval_hash_combine(out, arg.pack_expansion);
	out = value_eval_hash_combine(out, arg.value_expr_begin);
	out = value_eval_hash_combine(out, arg.value_expr_end);
	for (size_t i = 0; i < arg.value_owner_template_arguments.size(); ++i)
		out = value_eval_hash_combine(
			out,
			value_eval_instance_arg_hash(
				arg.value_owner_template_arguments[i],
				depth + 1));
	for (size_t i = 0; i < arg.pack.size(); ++i)
		out = value_eval_hash_combine(
			out,
			value_eval_template_arg_hash(arg.pack[i], depth + 1));
	return out;
}

size_t value_eval_instance_arg_hash(const pa11::TemplateInstanceArgument& arg,
                                    int depth)
{
	size_t out = static_cast<size_t>(arg.kind);
	if (depth > 8)
		return value_eval_hash_combine(out, 0xbad);
	out = value_eval_hash_combine(out, value_eval_type_hash(arg.type));
	out = value_eval_hash_combine(out,
	                              value_eval_string_hash(arg.template_name));
	out = value_eval_hash_combine(out,
	                              value_eval_string_hash(arg.value_name));
	out = value_eval_hash_combine(
		out,
		value_eval_string_hash(arg.value_owner_template_name));
	out = value_eval_hash_combine(
		out,
		value_eval_string_hash(arg.value_member_name));
	out = value_eval_hash_combine(out, arg.value);
	out = value_eval_hash_combine(out, arg.dependent);
	out = value_eval_hash_combine(out, arg.value_negated);
	out = value_eval_hash_combine(out, arg.value_expr_begin);
	out = value_eval_hash_combine(out, arg.value_expr_end);
	for (size_t i = 0; i < arg.value_owner_template_arguments.size(); ++i)
		out = value_eval_hash_combine(
			out,
			value_eval_instance_arg_hash(
				arg.value_owner_template_arguments[i],
				depth + 1));
	for (size_t i = 0; i < arg.pack.size(); ++i)
		out = value_eval_hash_combine(
			out,
			value_eval_instance_arg_hash(arg.pack[i], depth + 1));
	return out;
}

}  // namespace

bool Parser::template_value_argument_matches_for_template_match(
	TemplateDeclaration* specialization,
	const TemplateArgument& pattern,
	const TemplateArgument& actual,
	const map<string, TemplateArgument>& deduced)
{
	if (specialization == NULL ||
	    pattern.kind != TemplateArgumentKind::Value ||
	    actual.kind != TemplateArgumentKind::Value ||
	    pattern.value_expr_end <= pattern.value_expr_begin)
		return false;
	TemplateArgument typed_pattern = pattern;
	if (typed_pattern.type.get() == NULL && actual.type.get() != NULL)
		typed_pattern.type = actual.type;
	TemplateArgument evaluated;
	if (!try_evaluate_template_value_argument_for_template_match(
		    specialization,
		    typed_pattern,
		    deduced,
		    evaluated))
		return false;
	if (evaluated.kind != TemplateArgumentKind::Value ||
	    evaluated.dependent ||
	    actual.value_binding != NULL)
		return false;
	TypePtr expr_type = evaluated.type;
	if (!compatible_template_value_types(expr_type, actual.type))
		return false;
	TypePtr value_type =
		actual.type.get() != NULL ? actual.type : expr_type;
	return canonical_template_value(value_type, evaluated.value) ==
	       canonical_template_value(value_type, actual.value);
}

bool Parser::try_evaluate_template_value_argument_for_template_match(
	TemplateDeclaration* specialization,
	const TemplateArgument& pattern,
	const map<string, TemplateArgument>& deduced,
	TemplateArgument& out)
{
	if (specialization == NULL ||
	    pattern.kind != TemplateArgumentKind::Value ||
	    pattern.value_expr_end <= pattern.value_expr_begin)
		return false;
	size_t save_pos = pos_;
	vector<Scope*> save_scopes = scopes_;
	vector<map<string, TypePtr> > save_subst = template_type_substitutions_;
	vector<map<string, TemplateArgument> > save_value_subst =
		template_value_substitutions_;
	vector<set<string> > save_pack_subst = template_type_parameter_packs_;
	int save_expression_depth = template_argument_expression_depth_;

	map<string, TypePtr> subst;
	map<string, TemplateArgument> value_subst;
	set<string> pack_subst;
	for (size_t i = 0; i < specialization->parameters.size(); ++i)
	{
		const TemplateParameterInfo& parameter =
			specialization->parameters[i];
		if (parameter.name.empty())
			continue;
		map<string, TemplateArgument>::const_iterator found =
			deduced.find(parameter.name);
		if (found == deduced.end())
			continue;
		const TemplateArgument& arg = found->second;
		if (parameter.kind == TemplateParameterKind::Type)
		{
			if (parameter.is_pack)
			{
				subst[parameter.name] =
					pa11::make_template_parameter_type(parameter.name);
				value_subst[parameter.name] = arg;
				pack_subst.insert(parameter.name);
			}
			else if (arg.kind == TemplateArgumentKind::Type)
				subst[parameter.name] = arg.type;
			else
				return false;
		}
		else
			value_subst[parameter.name] = arg;
	}

	bool result = false;
	try
	{
		template_type_substitutions_.insert(
			template_type_substitutions_.end(),
			specialization->outer_type_substitutions.begin(),
			specialization->outer_type_substitutions.end());
		template_value_substitutions_.insert(
			template_value_substitutions_.end(),
			specialization->outer_value_substitutions.begin(),
			specialization->outer_value_substitutions.end());
		template_type_substitutions_.push_back(subst);
		template_value_substitutions_.push_back(value_subst);
		template_type_parameter_packs_.push_back(pack_subst);
		scopes_.clear();
		scopes_.push_back(specialization->lexical_scope != NULL
		                  ? specialization->lexical_scope
		                  : specialization->owner);
		result = try_evaluate_dependent_value_expression_argument(pattern,
		                                                          out);
	}
	catch (const runtime_error&)
	{
		result = false;
	}
	catch (const exception&)
	{
		result = false;
	}
	template_argument_expression_depth_ = save_expression_depth;
	template_type_substitutions_ = save_subst;
	template_value_substitutions_ = save_value_subst;
	template_type_parameter_packs_ = save_pack_subst;
	scopes_ = save_scopes;
	pos_ = save_pos;
	return result;
}

string Parser::dependent_value_expression_argument_cache_key(
	const TemplateArgument& arg)
{
	size_t cache_hash = value_eval_template_arg_hash(arg, 0);
	cache_hash = value_eval_hash_combine(
		cache_hash,
		reinterpret_cast<uintptr_t>(current_scope()));
	cache_hash = value_eval_hash_combine(cache_hash,
	                                     validating_template_definition_);
	cache_hash = value_eval_hash_combine(
		cache_hash,
		function_template_candidate_instantiation_depth_);
	for (size_t si = 0; si < template_type_substitutions_.size(); ++si)
	{
		cache_hash = value_eval_hash_combine(cache_hash, si);
		for (map<string, TypePtr>::const_iterator it =
			     template_type_substitutions_[si].begin();
		     it != template_type_substitutions_[si].end();
		     ++it)
		{
			cache_hash = value_eval_hash_combine(
				cache_hash,
				value_eval_string_hash(it->first));
			cache_hash = value_eval_hash_combine(
				cache_hash,
				value_eval_type_hash(it->second));
		}
	}
	for (size_t si = 0; si < template_value_substitutions_.size(); ++si)
	{
		cache_hash = value_eval_hash_combine(cache_hash, si);
		for (map<string, TemplateArgument>::const_iterator it =
			     template_value_substitutions_[si].begin();
		     it != template_value_substitutions_[si].end();
		     ++it)
		{
			cache_hash = value_eval_hash_combine(
				cache_hash,
				value_eval_string_hash(it->first));
			cache_hash = value_eval_hash_combine(
				cache_hash,
				value_eval_template_arg_hash(it->second, 0));
		}
	}
	return to_string(cache_hash);
}

bool Parser::setup_dependent_value_expression_tokens(
	const TemplateArgument& arg,
	const string& cache_key,
	vector<Token>& save_tokens,
	vector<Token>& replay_tokens,
	bool& switched_tokens,
	size_t& parse_begin,
	size_t& parse_end)
{
	switched_tokens = arg.value_expr_end > tokens_.size();
	if (switched_tokens)
	{
		if (arg.value_expr_end > declaration_tokens_.size())
		{
			dependent_value_expression_argument_fail_cache_.insert(cache_key);
			return false;
		}
		replay_tokens.reserve(arg.value_expr_end - arg.value_expr_begin + 1);
		for (size_t i = arg.value_expr_begin; i < arg.value_expr_end; ++i)
			replay_tokens.push_back(declaration_tokens_[i]);
		if (!declaration_tokens_.empty())
			replay_tokens.push_back(declaration_tokens_.back());
		tokens_.swap(save_tokens);
		tokens_.swap(replay_tokens);
	}
	parse_begin = switched_tokens ? 0 : arg.value_expr_begin;
	parse_end = switched_tokens
		? arg.value_expr_end - arg.value_expr_begin : arg.value_expr_end;
	return true;
}

void Parser::evaluate_constexpr_template_expression(Expr& expr)
{
	if (!expr.valid || expr.has_constant_value)
		return;
	ConstexprValue value;
	if (try_evaluate_constexpr_expr(expr.node, value) && !value.is_object)
		apply_constexpr_value(expr, value);
}

bool Parser::evaluate_dependent_value_pack_expression(
	const TemplateArgument& arg,
	const Expr& expr,
	TemplateArgument& out)
{
	if (!expr.pack_expansion)
		return false;
	vector<TemplateArgument> pack;
	bool pack_ok = true;
	for (size_t i = 0; i < expr.pack.size(); ++i)
	{
		Expr elem = expr.pack[i];
		evaluate_constexpr_template_expression(elem);
		if (elem.valid && !elem.has_constant_value && arg.type.get() != NULL)
		{
			try
			{
				TypePtr target = substitute_template_type(arg.type);
				Conversion conv = convert_to(elem, target);
				if (conv.viable)
				{
					evaluate_constexpr_template_expression(conv.expr);
					if (conv.expr.has_constant_value)
						elem = conv.expr;
				}
			}
			catch (const runtime_error&)
			{
			}
		}
		if (!elem.valid || !elem.has_constant_value)
		{
			pack_ok = false;
			break;
		}
		pack.push_back(TemplateArgument::value_arg(
			expression_object_type(elem.type),
			elem.constant_value));
	}
	if (!pack_ok)
		return false;
	out = TemplateArgument::pack_arg(pack);
	return true;
}

bool Parser::resolve_dependent_value_expression_argument(
	const TemplateArgument& arg,
	const Expr& expr,
	TemplateArgument& out)
{
	if (!expr.valid || expr.has_constant_value ||
	    expr.dependent_value_name.empty())
		return false;
	TemplateArgument dependent_value =
		TemplateArgument::dependent_value_arg(expression_object_type(expr.type));
	dependent_value.value_name = expr.dependent_value_name;
	dependent_value.value_owner_template_name =
		expr.dependent_value_owner_template_name;
	dependent_value.value_member_name = expr.dependent_value_member_name;
	dependent_value.value_owner_template_arguments =
		expr.dependent_value_owner_template_arguments;
	dependent_value.value_negated = expr.dependent_value_negated;
	dependent_value.value_expr_begin = arg.value_expr_begin;
	dependent_value.value_expr_end = arg.value_expr_end;
	TemplateArgument resolved_value;
	if (!resolve_dependent_value_member_argument(dependent_value,
	                                             resolved_value))
		return false;
	out = substitute_template_argument(resolved_value);
	return true;
}

bool Parser::convert_dependent_value_expression_argument(
	const TemplateArgument& arg,
	Expr& expr,
	TemplateArgument& out)
{
	bool member_pointer_address =
		expr.valid &&
		expr.node.has_op &&
		expr.node.op == OP_AMP &&
		!expr.node.children.empty() &&
		expr.node.children[0].binding != NULL;
	if (!expr.valid ||
	    arg.type.get() == NULL ||
	    (expr.has_constant_value && !member_pointer_address))
		return false;
	try
	{
		TypePtr target = substitute_template_type(arg.type);
		Conversion conv = convert_to(expr, target);
		if (!conv.viable)
			return false;
		TypePtr converted_bare =
			conv.expr.type.get() != NULL
			? pa11::strip_cv(expression_object_type(conv.expr.type))
			: TypePtr();
		if (converted_bare.get() != NULL &&
		    converted_bare->kind == pa11::TypeKind::MemberPointer &&
		    conv.expr.node.has_op &&
		    conv.expr.node.op == OP_AMP &&
		    !conv.expr.node.children.empty() &&
		    conv.expr.node.children[0].binding != NULL)
		{
			Binding* member = conv.expr.node.children[0].binding;
			if (member->aliased_binding != NULL &&
			    member->target_scope != NULL)
				member = member->aliased_binding;
			out = TemplateArgument::value_arg(
				expression_object_type(conv.expr.type),
				reinterpret_cast<uint64_t>(member));
			out.value_binding = member;
			return true;
		}
		evaluate_constexpr_template_expression(conv.expr);
		if (conv.expr.has_constant_value)
			expr = conv.expr;
	}
	catch (const runtime_error&)
	{
	}
	return false;
}

bool Parser::finish_dependent_value_expression_argument(
	const TemplateArgument& arg,
	Expr& expr,
	TemplateArgument& out)
{
	bool defer_template_call =
		expr.valid &&
		function_template_candidate_instantiation_depth_ != 0 &&
		node_calls_function_template(expr.node,
		                             function_template_placeholders_);
	if (defer_template_call)
	{
		out = arg;
		return true;
	}
	if (evaluate_dependent_value_pack_expression(arg, expr, out))
		return true;
	evaluate_constexpr_template_expression(expr);
	if (resolve_dependent_value_expression_argument(arg, expr, out))
		return true;
	if (convert_dependent_value_expression_argument(arg, expr, out))
		return true;
	if (!expr.valid || !expr.has_constant_value)
		return false;
	out = TemplateArgument::value_arg(expression_object_type(expr.type),
	                                  expr.constant_value);
	return true;
}

bool Parser::parse_dependent_value_expression_argument(
	const TemplateArgument& arg,
	size_t parse_begin,
	size_t parse_end,
	TemplateArgument& out)
{
	int save_expression_depth = template_argument_expression_depth_;
	bool result = false;
	try
	{
		pos_ = parse_begin;
		++template_argument_expression_depth_;
		Expr expr = parse_assignment_expression();
		template_argument_expression_depth_ = save_expression_depth;
		if (pos_ == parse_end)
			result = finish_dependent_value_expression_argument(arg, expr, out);
	}
	catch (const runtime_error&)
	{
		result = false;
	}
	catch (const exception&)
	{
		result = false;
	}
	template_argument_expression_depth_ = save_expression_depth;
	return result;
}

bool Parser::try_evaluate_dependent_value_expression_argument(
	const TemplateArgument& arg,
	TemplateArgument& out)
{
	if (arg.kind != TemplateArgumentKind::Value ||
	    !arg.dependent ||
	    arg.value_expr_end <= arg.value_expr_begin)
		return false;
	if (validating_template_definition_ &&
	    template_argument_has_template_parameter(arg,
	                                             record_template_arguments_))
		return false;
	string active_key =
		to_string(arg.value_expr_begin) + ":" + to_string(arg.value_expr_end);
	if (find(active_dependent_value_expression_keys_.begin(),
	         active_dependent_value_expression_keys_.end(),
	         active_key) != active_dependent_value_expression_keys_.end())
		return false;
	string cache_key = dependent_value_expression_argument_cache_key(arg);
	map<string, TemplateArgument>::const_iterator cached =
		dependent_value_expression_argument_cache_.find(cache_key);
	if (cached != dependent_value_expression_argument_cache_.end())
	{
		out = cached->second;
		return true;
	}
	if (dependent_value_expression_argument_fail_cache_.count(cache_key) != 0)
		return false;
	struct ActiveDependentValueExpression
	{
		vector<string>& keys;
		ActiveDependentValueExpression(vector<string>& k, const string& key)
		  : keys(k)
		{
			keys.push_back(key);
		}
		~ActiveDependentValueExpression()
		{
			keys.pop_back();
		}
	} active_dependent_value_expression(
		active_dependent_value_expression_keys_,
		active_key);
	size_t save_pos = pos_;
	vector<Token> save_tokens;
	vector<Token> replay_tokens;
	bool switched_tokens = false;
	size_t parse_begin = 0;
	size_t parse_end = 0;
	if (!setup_dependent_value_expression_tokens(arg,
	                                             cache_key,
	                                             save_tokens,
	                                             replay_tokens,
	                                             switched_tokens,
	                                             parse_begin,
	                                             parse_end))
		return false;
	bool result = parse_dependent_value_expression_argument(arg,
	                                                       parse_begin,
	                                                       parse_end,
	                                                       out);
	if (switched_tokens)
	{
		tokens_.swap(replay_tokens);
		tokens_.swap(save_tokens);
	}
	pos_ = save_pos;
	if (result)
		dependent_value_expression_argument_cache_[cache_key] = out;
	else
		dependent_value_expression_argument_fail_cache_.insert(cache_key);
	return result;
}

string Parser::template_argument_key(
	const vector<TemplateArgument>& arguments) const
{
	ostringstream out;
	for (size_t i = 0; i < arguments.size(); ++i)
	{
		if (i != 0)
			out << ",";
		out << template_argument_key_part(arguments[i]);
	}
	return out.str();
}

string Parser::template_specialization_name(
	TemplateDeclaration* declaration,
	const vector<TemplateArgument>& arguments) const
{
	return declaration->name + "<" + template_argument_spelling(arguments) + ">";
}

}  // namespace internal
}  // namespace pa12
