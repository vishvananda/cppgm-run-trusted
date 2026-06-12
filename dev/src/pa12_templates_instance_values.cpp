#include "pa12_templates_instance_support.h"

#include <algorithm>
#include <cstdint>
#include <sstream>
#include <stdexcept>
#include <utility>

#include "posttoken_pipeline.h"
#include "pp_token.h"

using namespace std;

namespace pa12 {
namespace internal {

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
	vector<Token> save_tokens = tokens_;
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
	tokens_ = save_tokens;
	pos_ = save_pos;
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
	vector<Token> save_tokens = tokens_;
	int save_expression_depth = template_argument_expression_depth_;
	bool result = false;
	try
		{
			if (arg.value_expr_end > tokens_.size())
				tokens_ = declaration_tokens_;
			pos_ = arg.value_expr_begin;
			++template_argument_expression_depth_;
			Expr expr = parse_assignment_expression();
			template_argument_expression_depth_ = save_expression_depth;
			if (pos_ == arg.value_expr_end)
			{
				if (expr.pack_expansion)
				{
				vector<TemplateArgument> pack;
				bool pack_ok = true;
				for (size_t i = 0; i < expr.pack.size(); ++i)
				{
					Expr elem = expr.pack[i];
					if (elem.valid && !elem.has_constant_value)
					{
						ConstexprValue value;
						if (try_evaluate_constexpr_expr(elem.node, value) &&
						    !value.is_object)
							apply_constexpr_value(elem, value);
					}
					if (elem.valid && !elem.has_constant_value &&
					    arg.type.get() != NULL)
					{
						try
						{
							TypePtr target =
								substitute_template_type(arg.type);
							Conversion conv = convert_to(elem, target);
							if (conv.viable &&
							    !conv.expr.has_constant_value)
							{
								ConstexprValue value;
								if (try_evaluate_constexpr_expr(
									    conv.expr.node,
									    value))
									apply_constexpr_value(conv.expr,
									                      value);
							}
							if (conv.viable &&
							    conv.expr.has_constant_value)
								elem = conv.expr;
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
				if (pack_ok)
				{
					out = TemplateArgument::pack_arg(pack);
					result = true;
				}
			}
				if (expr.valid && !expr.has_constant_value)
				{
					ConstexprValue value;
					if (try_evaluate_constexpr_expr(expr.node, value) &&
				    !value.is_object)
					apply_constexpr_value(expr, value);
			}
				bool defer_template_call =
					expr.valid &&
					!expr.has_constant_value &&
					function_template_candidate_instantiation_depth_ != 0 &&
					node_calls_function_template(
						expr.node,
						function_template_placeholders_);
				if (defer_template_call)
				{
					out = arg;
					result = true;
				}
				if (expr.valid && !expr.has_constant_value &&
				    !expr.dependent_value_name.empty())
				{
					TemplateArgument dependent_value =
						TemplateArgument::dependent_value_arg(
							expression_object_type(expr.type));
					dependent_value.value_name = expr.dependent_value_name;
					dependent_value.value_owner_template_name =
						expr.dependent_value_owner_template_name;
					dependent_value.value_member_name =
						expr.dependent_value_member_name;
						dependent_value.value_owner_template_arguments =
							expr.dependent_value_owner_template_arguments;
						dependent_value.value_negated = expr.dependent_value_negated;
						TemplateArgument resolved_value;
						bool resolved_dependent_value =
							resolve_dependent_value_member_argument(
								dependent_value,
								resolved_value);
						if (resolved_dependent_value)
						{
							out = substitute_template_argument(resolved_value);
							result = true;
						}
				}
				bool member_pointer_address =
					expr.valid &&
					expr.node.has_op &&
					expr.node.op == OP_AMP &&
					!expr.node.children.empty() &&
					expr.node.children[0].binding != NULL;
				if (expr.valid && arg.type.get() != NULL &&
				    (!expr.has_constant_value || member_pointer_address))
				{
				try
				{
					TypePtr target = substitute_template_type(arg.type);
					Conversion conv = convert_to(expr, target);
					if (conv.viable)
					{
						TypePtr converted_bare =
							conv.expr.type.get() != NULL
							? pa11::strip_cv(
								expression_object_type(conv.expr.type))
							: TypePtr();
						if (converted_bare.get() != NULL &&
						    converted_bare->kind ==
							    pa11::TypeKind::MemberPointer &&
						    conv.expr.node.has_op &&
						    conv.expr.node.op == OP_AMP &&
						    !conv.expr.node.children.empty() &&
						    conv.expr.node.children[0].binding != NULL)
						{
							Binding* member =
								conv.expr.node.children[0].binding;
							if (member->aliased_binding != NULL &&
							    member->target_scope != NULL)
								member = member->aliased_binding;
							out = TemplateArgument::value_arg(
								expression_object_type(conv.expr.type),
								reinterpret_cast<uint64_t>(member));
							out.value_binding = member;
							result = true;
						}
					}
					if (conv.viable && !conv.expr.has_constant_value)
					{
						ConstexprValue value;
						if (try_evaluate_constexpr_expr(conv.expr.node,
						                                value))
							apply_constexpr_value(conv.expr, value);
					}
					if (conv.viable && conv.expr.has_constant_value)
						expr = conv.expr;
				}
				catch (const runtime_error&)
				{
				}
			}
				if (!result && expr.valid && expr.has_constant_value)
				{
					out = TemplateArgument::value_arg(
						expression_object_type(expr.type),
						expr.constant_value);
					result = true;
				}
		}
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
	tokens_ = save_tokens;
	pos_ = save_pos;
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
