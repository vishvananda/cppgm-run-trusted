#include "pa12_templates_function_abi_internal.h"
#include "pa12_templates_instance_support.h"

#include <algorithm>
#include <stdexcept>

using namespace std;

namespace pa12 {
namespace internal {

string abi_base36_number(size_t value)
{
	static const char digits[] = "0123456789ABCDEFGHIJKLMNOPQRSTUVWXYZ";
	string encoded;
	do
	{
		encoded.insert(encoded.begin(), digits[value % 36]);
		value /= 36;
	}
	while (value != 0);
	return encoded;
}

string abi_substitution_code(size_t index)
{
	if (index == 0)
		return "S_";
	return "S" + abi_base36_number(index - 1) + "_";
}

size_t abi_find_substitution(const AbiSubstitutionContext& ctx,
                             const string& encoded)
{
	map<string, size_t>::const_iterator alias =
		ctx.substitution_aliases.find(encoded);
	if (alias != ctx.substitution_aliases.end())
		return alias->second;
	for (size_t i = 0; i < ctx.substitutions.size(); ++i)
		if (ctx.substitutions[i] == encoded)
			return i;
	return static_cast<size_t>(-1);
}

void abi_add_substitution_alias(AbiSubstitutionContext& ctx,
                                const string& alias,
                                const string& target)
{
	if (alias.empty() || alias == target)
		return;
	size_t found = abi_find_substitution(ctx, target);
	if (found == static_cast<size_t>(-1))
		return;
	ctx.substitution_aliases[alias] = found;
}

void abi_add_substitution(AbiSubstitutionContext& ctx, const string& encoded)
{
	if (encoded.empty() ||
	    abi_find_substitution(ctx, encoded) != static_cast<size_t>(-1))
		return;
	ctx.substitutions.push_back(encoded);
}

string abi_use_or_add_substitution(AbiSubstitutionContext& ctx,
                                   const string& encoded)
{
	size_t found = abi_find_substitution(ctx, encoded);
	if (found != static_cast<size_t>(-1))
		return abi_substitution_code(found);
	abi_add_substitution(ctx, encoded);
	return encoded;
}

string abi_type_with_substitutions(TypePtr type,
                                   AbiSubstitutionContext& ctx);
string abi_type_probe_with_substitutions(TypePtr type,
                                         AbiSubstitutionContext& ctx);

string abi_template_parameter_type_with_substitutions(
	const string& name,
	AbiSubstitutionContext& ctx)
{
	map<string, size_t>::const_iterator found =
		ctx.template_parameters.find(name);
	size_t index = found == ctx.template_parameters.end() ? 0 : found->second;
	if (ctx.use_actual_template_parameter_types &&
	    index < ctx.actual_template_arguments.size() &&
	    ctx.actual_template_arguments[index].kind == TemplateArgumentKind::Type)
	{
		map<string, size_t>::const_iterator existing =
			ctx.actual_template_parameter_substitutions.find(name);
		if (existing != ctx.actual_template_parameter_substitutions.end())
			return abi_substitution_code(existing->second);
		string encoded = abi_type_probe_with_substitutions(
			ctx.actual_template_arguments[index].type,
			ctx);
		size_t sub = ctx.substitutions.size();
		ctx.substitutions.push_back(encoded);
		ctx.actual_template_parameter_substitutions[name] = sub;
		return abi_substitution_code(sub);
	}
	string encoded = index == 0 ? string("T_") :
	                 string("T") + to_string(index - 1) + "_";
	return abi_use_or_add_substitution(ctx, encoded);
}

string abi_record_type_with_substitutions(TypePtr type,
                                          AbiSubstitutionContext& ctx,
                                          bool include_namespace);
string abi_record_type_probe_with_substitutions(TypePtr type,
                                                AbiSubstitutionContext& ctx,
                                                bool include_namespace);
string abi_scope_prefix_probe_with_substitutions(const vector<Scope*>& scopes,
                                                AbiSubstitutionContext& ctx);
string abi_template_argument_with_substitutions(
	const TemplateArgument& arg,
	AbiSubstitutionContext& ctx);
string abi_template_instance_argument_with_substitutions(
	const pa11::TemplateInstanceArgument& arg,
	AbiSubstitutionContext& ctx);

string abi_dependent_typename_type_with_substitutions(
	TypePtr type,
	AbiSubstitutionContext& ctx,
	bool include_typename_marker)
{
	vector<string> parts = abi_split_qualified_name(type->name);
	if (parts.empty())
		return abi_source_name(type->name);
	string out;
	if (type->dependent_typename_qualified)
		out = include_typename_marker ? "TnN" : "N";
	else
		out = include_typename_marker ? "Tn" : "";
	size_t list_index = 0;
	for (size_t i = 0; i < parts.size(); ++i)
	{
		string part = parts[i];
		size_t template_pos = part.find('<');
		bool has_template_id = template_pos != string::npos;
		if (has_template_id)
			part = part.substr(0, template_pos);
		string source = abi_source_name(part);
		if (has_template_id)
		{
			size_t source_sub = abi_find_substitution(ctx, source);
			if (source_sub != static_cast<size_t>(-1))
				source = abi_substitution_code(source_sub);
			else
				abi_add_substitution(ctx, source);
		}
		out += source;
		vector<pa11::TemplateInstanceArgument> arguments;
		if (has_template_id &&
		    list_index <
			    type->dependent_typename_template_argument_lists.size())
			arguments =
				type->dependent_typename_template_argument_lists[list_index++];
		else if (has_template_id && i == 0 &&
		         !type->template_arguments.empty())
			arguments = type->template_arguments;
		if (!arguments.empty())
		{
			out += "I";
			for (size_t j = 0; j < arguments.size(); ++j)
				out += abi_template_instance_argument_with_substitutions(
					arguments[j],
					ctx);
			out += "E";
		}
	}
	if (type->dependent_typename_qualified)
		out += "E";
	return out;
}

string abi_function_parameter_expression(const string& name,
                                         const AbiSubstitutionContext& ctx)
{
	if (ctx.function_parameter_names == NULL)
		return "";
	for (size_t i = 0; i < ctx.function_parameter_names->size(); ++i)
		if ((*ctx.function_parameter_names)[i] == name)
			return i == 0
				? string("fp_")
				: string("fp") + abi_base36_number(i - 1) + "_";
	return "";
}

bool abi_find_call_open(const vector<Token>& tokens,
                        size_t begin,
                        size_t end,
                        size_t& open)
{
	if (end <= begin + 2 || !abi_token_is_simple(tokens, end - 1, OP_RPAREN))
		return false;
	int depth = 0;
	for (size_t i = end; i > begin; --i)
	{
		size_t pos = i - 1;
		if (tokens[pos].kind != posttoken::TokenKind::Simple)
			continue;
		if (tokens[pos].type == OP_RPAREN)
			++depth;
		else if (tokens[pos].type == OP_LPAREN)
		{
			--depth;
			if (depth == 0)
			{
				open = pos;
				return open > begin;
			}
		}
	}
	return false;
}

bool abi_find_top_level_member_operator(const vector<Token>& tokens,
                                        size_t begin,
                                        size_t end,
                                        size_t& op)
{
	int paren = 0;
	int square = 0;
	int brace = 0;
	bool found = false;
	for (size_t i = begin; i < end; ++i)
	{
		if (tokens[i].kind != posttoken::TokenKind::Simple)
			continue;
		ETokenType type = tokens[i].type;
		if (type == OP_LPAREN)
			++paren;
		else if (type == OP_RPAREN)
			--paren;
		else if (type == OP_LSQUARE)
			++square;
		else if (type == OP_RSQUARE)
			--square;
		else if (type == OP_LBRACE)
			++brace;
		else if (type == OP_RBRACE)
			--brace;
		else if (paren == 0 && square == 0 && brace == 0 &&
		         (type == OP_DOT || type == OP_ARROW))
		{
			op = i;
			found = true;
		}
	}
	return found;
}

void abi_split_top_level_arguments(const vector<Token>& tokens,
                                   size_t begin,
                                   size_t end,
                                   vector<pair<size_t, size_t> >& out)
{
	int paren = 0;
	int square = 0;
	int brace = 0;
	size_t arg_begin = begin;
	for (size_t i = begin; i < end; ++i)
	{
		if (tokens[i].kind != posttoken::TokenKind::Simple)
			continue;
		ETokenType type = tokens[i].type;
		if (type == OP_LPAREN)
			++paren;
		else if (type == OP_RPAREN)
			--paren;
		else if (type == OP_LSQUARE)
			++square;
		else if (type == OP_RSQUARE)
			--square;
		else if (type == OP_LBRACE)
			++brace;
		else if (type == OP_RBRACE)
			--brace;
		else if (type == OP_COMMA && paren == 0 && square == 0 &&
		         brace == 0)
		{
			out.push_back(make_pair(arg_begin, i));
			arg_begin = i + 1;
		}
	}
	if (arg_begin < end)
		out.push_back(make_pair(arg_begin, end));
}

string abi_dependent_expression_with_substitutions(
	const vector<Token>& tokens,
	size_t begin,
	size_t end,
	AbiSubstitutionContext& ctx)
{
	if (end > tokens.size() || begin >= end)
		return "";
	abi_trim_wrapping_parens(tokens, begin, end);
	if (begin >= end)
		return "";
	static const ETokenType comma_ops[] = { OP_COMMA };
	static const ETokenType lor_ops[] = { OP_LOR };
	static const ETokenType land_ops[] = { OP_LAND };
	static const ETokenType equality_ops[] = { OP_EQ, OP_NE };
	static const ETokenType relational_ops[] = { OP_LT, OP_GT, OP_LE, OP_GE };
	static const ETokenType shift_ops[] = { OP_LSHIFT, OP_RSHIFT };
	static const ETokenType additive_ops[] = { OP_PLUS, OP_MINUS };
	static const ETokenType multiplicative_ops[] = { OP_STAR, OP_DIV, OP_MOD };
	static const ETokenType bit_and_ops[] = { OP_AMP };
	static const ETokenType bit_xor_ops[] = { OP_XOR };
	static const ETokenType bit_or_ops[] = { OP_BOR };
	const ETokenType* groups[] = {
		comma_ops, lor_ops, land_ops, bit_or_ops, bit_xor_ops,
		bit_and_ops, equality_ops, relational_ops, shift_ops,
		additive_ops, multiplicative_ops
	};
	const size_t group_sizes[] = {
		1, 1, 1, 1, 1, 1, 2, 4, 2, 2, 3
	};
	for (size_t g = 0; g < sizeof(groups) / sizeof(groups[0]); ++g)
	{
		vector<ETokenType> ops(groups[g], groups[g] + group_sizes[g]);
		size_t op = 0;
		if (!abi_find_top_level_operator(tokens, begin, end, ops, op))
			continue;
		string left = abi_dependent_expression_with_substitutions(
			tokens, begin, op, ctx);
		string right = abi_dependent_expression_with_substitutions(
			tokens, op + 1, end, ctx);
		string code = abi_binary_operator_code(tokens[op].type);
		if (!left.empty() && !right.empty() && !code.empty())
			return code + left + right;
		return "";
	}
	if (abi_token_is_simple(tokens, begin, OP_LNOT))
	{
		string inner = abi_dependent_expression_with_substitutions(
			tokens, begin + 1, end, ctx);
		return inner.empty() ? string("") : string("nt") + inner;
	}
	if (begin + 3 == end &&
	    abi_token_is_simple(tokens, begin + 1, OP_LPAREN) &&
	    abi_token_is_simple(tokens, begin + 2, OP_RPAREN))
	{
		AbiTokenType cast_type =
			abi_encode_type_tokens(tokens,
			                       begin,
			                       begin + 1,
			                       ctx.template_parameters);
		if (!cast_type.encoded.empty())
			return "cv" + cast_type.encoded + "_E";
	}
	size_t call_open = 0;
	if (abi_find_call_open(tokens, begin, end, call_open))
	{
		string callee = abi_dependent_expression_with_substitutions(
			tokens, begin, call_open, ctx);
		if (callee.empty())
			return "";
		string out = "cl" + callee;
		vector<pair<size_t, size_t> > args;
		abi_split_top_level_arguments(tokens, call_open + 1, end - 1, args);
		for (size_t i = 0; i < args.size(); ++i)
		{
			string arg = abi_dependent_expression_with_substitutions(
				tokens, args[i].first, args[i].second, ctx);
			if (arg.empty())
				return "";
			out += arg;
		}
		out += "E";
		return out;
	}
	size_t member_op = 0;
	if (abi_find_top_level_member_operator(tokens, begin, end, member_op) &&
	    member_op + 1 < end &&
	    tokens[member_op + 1].kind == posttoken::TokenKind::Identifier)
	{
		string object = abi_dependent_expression_with_substitutions(
			tokens, begin, member_op, ctx);
		if (object.empty())
			return "";
		return string(tokens[member_op].type == OP_ARROW ? "pt" : "dt") +
		       object + abi_source_name(tokens[member_op + 1].source);
	}
	if (end == begin + 1)
	{
		string literal = abi_literal_expression(tokens[begin]);
		if (!literal.empty())
			return literal;
		if (tokens[begin].kind == posttoken::TokenKind::Identifier)
		{
			string param =
				abi_function_parameter_expression(tokens[begin].source, ctx);
			if (!param.empty())
				return param;
			return abi_template_parameter_expression(tokens[begin].source,
			                                        ctx.template_parameters);
		}
	}
	return "";
}

string abi_dependent_decltype_type_with_substitutions(
	TypePtr type,
	AbiSubstitutionContext& ctx)
{
	if (type.get() == NULL ||
	    !type->dependent_typename_decltype ||
	    type->name.compare(0, 9, "decltype(") != 0)
		return "";
	vector<Token> tokens;
	size_t end = 0;
	if (!collect_replay_tokens(type->name, tokens) ||
	    tokens.size() < 4)
		return "";
	end = tokens.size();
	while (end > 0 && tokens[end - 1].kind == posttoken::TokenKind::EndOfFile)
		--end;
	if (end < 4 ||
	    !abi_token_is_simple(tokens, 0, KW_DECLTYPE) ||
	    !abi_token_is_simple(tokens, 1, OP_LPAREN) ||
	    !abi_token_is_simple(tokens, end - 1, OP_RPAREN))
		return "";
	string expression = abi_dependent_expression_with_substitutions(
		tokens, 2, end - 1, ctx);
	return expression.empty() ? string("") : string("DT") + expression + "E";
}

bool abi_scope_is_std_namespace(Scope* scope)
{
	return scope != NULL &&
	       scope->kind == ScopeKind::Namespace &&
	       scope->name == "std";
}

bool abi_record_in_std_namespace(TypePtr type)
{
	TypePtr bare = type.get() != NULL ? pa11::strip_cv(type) : TypePtr();
	if (bare.get() == NULL || bare->scope == NULL)
		return false;
	for (Scope* scope = bare->scope->parent; scope != NULL;
	     scope = scope->parent)
	{
		if (abi_scope_is_std_namespace(scope))
			return true;
		if (scope->kind == ScopeKind::Class)
			return false;
	}
	return false;
}

string abi_std_abbreviation(TypePtr type)
{
	TypePtr bare = type.get() != NULL ? pa11::strip_cv(type) : TypePtr();
	if (bare.get() == NULL || !abi_record_in_std_namespace(bare))
		return "";
	string name = bare->is_template_specialization &&
	              !bare->template_primary_name.empty()
		? bare->template_primary_name : bare->name;
	size_t args = name.find('<');
	if (args != string::npos)
		name = name.substr(0, args);
	if (name == "allocator")
		return "Sa";
	if (name == "basic_string")
		return "Sb";
	return "";
}

string abi_record_unscoped_with_substitutions(TypePtr type,
                                              AbiSubstitutionContext& ctx)
{
	TypePtr bare = type.get() != NULL ? pa11::strip_cv(type) : TypePtr();
	if (bare.get() == NULL)
		return abi_source_name("v");
	string special = abi_std_abbreviation(bare);
	string name = bare->is_template_specialization &&
	              !bare->template_primary_name.empty()
		? bare->template_primary_name : bare->name;
	size_t args = name.find('<');
	if (args != string::npos)
		name = name.substr(0, args);
	string primary = special.empty() ? abi_source_name(name) : special;
	string out = primary;
	if (bare->is_template_specialization)
	{
		if (special.empty())
		{
			size_t primary_sub = abi_find_substitution(ctx, primary);
			if (primary_sub != static_cast<size_t>(-1))
				out = abi_substitution_code(primary_sub);
			else
				abi_add_substitution(ctx, primary);
		}
		out += "I";
		for (size_t i = 0; i < bare->template_arguments.size(); ++i)
			out += abi_template_instance_argument_with_substitutions(
				bare->template_arguments[i], ctx);
		out += "E";
	}
	return out;
}

vector<Scope*> abi_scope_path_outer_first(Scope* scope)
{
	vector<Scope*> reversed;
	for (Scope* cur = scope; cur != NULL; cur = cur->parent)
	{
		if (cur->kind == ScopeKind::Namespace && !cur->name.empty())
			reversed.push_back(cur);
		else if (cur->kind == ScopeKind::Class &&
		         !cur->name.empty() &&
		         cur->name != "<unnamed>")
			reversed.push_back(cur);
	}
	return vector<Scope*>(reversed.rbegin(), reversed.rend());
}

string abi_scope_component_with_substitutions(Scope* scope,
                                             AbiSubstitutionContext& ctx)
{
	if (scope->kind == ScopeKind::Namespace)
	{
		if (scope->name == "std")
			return "St";
		string name = scope->name == "<unnamed>"
			? string("_GLOBAL__N_1") : scope->name;
		return abi_source_name(name);
	}
	if (scope->kind == ScopeKind::Class)
	{
		TypePtr record = pa11::record_type_for_scope(scope);
		return abi_record_unscoped_with_substitutions(record, ctx);
	}
	return "";
}

string abi_scope_prefix_with_substitutions(const vector<Scope*>& scopes,
                                          AbiSubstitutionContext& ctx)
{
	string out;
	string prefix_key;
	for (size_t i = 0; i < scopes.size(); ++i)
	{
		string component = abi_scope_component_with_substitutions(scopes[i],
		                                                         ctx);
		if (component.empty())
			continue;
		string key = prefix_key.empty()
			? component : string("N") + prefix_key + component + "E";
		if (component == "St")
		{
			out += component;
			prefix_key = key;
			continue;
		}
		size_t found = abi_find_substitution(ctx, key);
		if (found != static_cast<size_t>(-1))
			out += abi_substitution_code(found);
		else
		{
			out += component;
			abi_add_substitution(ctx, key);
		}
		prefix_key = key;
	}
	return out;
}

string abi_record_type_with_substitutions(TypePtr type,
                                          AbiSubstitutionContext& ctx,
                                          bool include_namespace)
{
	TypePtr bare = type.get() != NULL ? pa11::strip_cv(type) : TypePtr();
	if (bare.get() == NULL)
		return "v";
	if (!abi_std_abbreviation(bare).empty())
		return abi_use_or_add_substitution(
			ctx, abi_record_unscoped_with_substitutions(bare, ctx));
	vector<Scope*> scopes;
	string scope_prefix;
	if (include_namespace && bare->scope != NULL)
	{
		scopes = abi_scope_path_outer_first(bare->scope->parent);
		if (!scopes.empty() &&
		    !(scopes.size() == 1 && abi_scope_is_std_namespace(scopes[0])))
			scope_prefix = abi_scope_prefix_with_substitutions(scopes, ctx);
	}
	if (bare->is_template_specialization && !scopes.empty() &&
	    !(scopes.size() == 1 && abi_scope_is_std_namespace(scopes[0])))
	{
		string name = !bare->template_primary_name.empty()
			? bare->template_primary_name : bare->name;
		size_t pos = name.find('<');
		if (pos != string::npos)
			name = name.substr(0, pos);
		string source = abi_source_name(name);
		string qualified_prefix = "N" + scope_prefix + source + "E";
		size_t prefix_sub = abi_find_substitution(ctx, qualified_prefix);
		if (prefix_sub == static_cast<size_t>(-1))
			abi_add_substitution(ctx, qualified_prefix);
		abi_add_substitution_alias(
			ctx,
			"N" + abi_scope_prefix_probe_with_substitutions(scopes, ctx) +
				source + "E",
			qualified_prefix);
		string args = "I";
		for (size_t i = 0; i < bare->template_arguments.size(); ++i)
			args += abi_template_instance_argument_with_substitutions(
				bare->template_arguments[i], ctx);
		args += "E";
		string encoded = prefix_sub == static_cast<size_t>(-1)
			? "N" + scope_prefix + source + args + "E"
			: "N" + abi_substitution_code(prefix_sub) + args + "E";
		string result = abi_use_or_add_substitution(ctx, encoded);
		abi_add_substitution_alias(
			ctx,
			abi_record_type_probe_with_substitutions(bare,
			                                         ctx,
			                                         include_namespace),
			encoded);
		return result;
	}
	string leaf = abi_record_unscoped_with_substitutions(bare, ctx);
	string encoded = leaf;
	if (!scopes.empty())
	{
		if (scopes.size() == 1 && abi_scope_is_std_namespace(scopes[0]))
			encoded = "St" + leaf;
		else
			encoded = "N" + scope_prefix + leaf + "E";
	}
	string result = abi_use_or_add_substitution(ctx, encoded);
	abi_add_substitution_alias(
		ctx,
		abi_record_type_probe_with_substitutions(bare, ctx, include_namespace),
		encoded);
	return result;
}

string abi_template_instance_argument_with_substitutions(
	const pa11::TemplateInstanceArgument& arg,
	AbiSubstitutionContext& ctx)
{
	if (arg.kind == pa11::TemplateInstanceArgumentKind::Type)
		return abi_type_with_substitutions(arg.type, ctx);
	if (arg.kind == pa11::TemplateInstanceArgumentKind::Value)
	{
		if (arg.dependent)
		{
			if (!arg.value_owner_template_name.empty() &&
			    !arg.value_member_name.empty())
			{
				string owner_name = arg.value_owner_template_name;
				size_t owner_args = owner_name.find('<');
				if (owner_args != string::npos)
					owner_name = owner_name.substr(0, owner_args);
				string owner = abi_unresolved_name_path(owner_name);
				abi_add_substitution(ctx, owner);
				string out = "Xsr" + owner;
				bool owner_has_dependent_typename_argument = false;
				if (!arg.value_owner_template_arguments.empty())
				{
					out += "I";
					for (size_t i = 0;
					     i < arg.value_owner_template_arguments.size();
					     ++i)
					{
						const pa11::TemplateInstanceArgument& owner_arg =
							arg.value_owner_template_arguments[i];
						if (owner_arg.kind ==
						        pa11::TemplateInstanceArgumentKind::Type &&
						    owner_arg.type.get() != NULL &&
						    owner_arg.type->is_dependent_typename)
						{
							owner_has_dependent_typename_argument = true;
							out += abi_use_or_add_substitution(
								ctx,
								abi_dependent_typename_type_with_substitutions(
									owner_arg.type, ctx, false));
						}
						else
							out += abi_template_instance_argument_with_substitutions(
								owner_arg, ctx);
					}
					out += "E";
					out += "E";
				}
				out += abi_source_name(arg.value_member_name) + "E";
				if (arg.value_negated)
					out = "Xnt" + out.substr(1);
				if (owner_has_dependent_typename_argument)
					abi_add_substitution(ctx, out);
				return out;
			}
			if (ctx.expression_tokens != NULL &&
			    arg.value_expr_end > arg.value_expr_begin)
			{
				string expression = abi_template_value_expression(
					*ctx.expression_tokens,
					arg.value_expr_begin,
					arg.value_expr_end,
					ctx.template_parameters);
				if (!expression.empty())
					return "X" + expression + "E";
			}
			if (!arg.value_name.empty())
			{
				string parameter_expr =
					abi_template_parameter_expression(
						arg.value_name,
						ctx.template_parameters);
				if (!parameter_expr.empty())
					return "X" + parameter_expr + "E";
			}
		}
		if (!arg.value_name.empty())
			return "L" + abi_type_with_substitutions(arg.type, ctx) +
			       abi_encoded_stable_value_name(arg.value_name) + "E";
		if (abi_type_is_dependent_parameter(arg.type))
			return "Li" + to_string(arg.value) + "E";
		return "L" + abi_type_with_substitutions(arg.type, ctx) +
		       to_string(arg.value) + "E";
	}
	if (arg.kind == pa11::TemplateInstanceArgumentKind::Pack)
	{
		string out = "J";
		for (size_t i = 0; i < arg.pack.size(); ++i)
			out += abi_template_instance_argument_with_substitutions(
				arg.pack[i], ctx);
		out += "E";
		return out;
	}
	return abi_template_name(arg.template_name);
}

string abi_template_argument_with_substitutions(
	const TemplateArgument& arg,
	AbiSubstitutionContext& ctx)
{
	if (arg.kind == TemplateArgumentKind::Type)
		return abi_type_with_substitutions(arg.type, ctx);
	if (arg.kind == TemplateArgumentKind::Value)
	{
		if (arg.dependent)
		{
			if (!arg.value_owner_template_name.empty() &&
			    !arg.value_member_name.empty())
			{
				string owner_name = arg.value_owner_template_name;
				size_t owner_args = owner_name.find('<');
				if (owner_args != string::npos)
					owner_name = owner_name.substr(0, owner_args);
				string owner = abi_unresolved_name_path(owner_name);
				abi_add_substitution(ctx, owner);
				string out = "Xsr" + owner;
				bool owner_has_dependent_typename_argument = false;
				if (!arg.value_owner_template_arguments.empty())
				{
					out += "I";
					for (size_t i = 0;
					     i < arg.value_owner_template_arguments.size();
					     ++i)
					{
						const pa11::TemplateInstanceArgument& owner_arg =
							arg.value_owner_template_arguments[i];
						if (owner_arg.kind ==
						        pa11::TemplateInstanceArgumentKind::Type &&
						    owner_arg.type.get() != NULL &&
						    owner_arg.type->is_dependent_typename)
						{
							owner_has_dependent_typename_argument = true;
							out += abi_use_or_add_substitution(
								ctx,
								abi_dependent_typename_type_with_substitutions(
									owner_arg.type, ctx, false));
						}
						else
							out += abi_template_instance_argument_with_substitutions(
								owner_arg, ctx);
					}
					out += "E";
					out += "E";
				}
				out += abi_source_name(arg.value_member_name) + "E";
				if (arg.value_negated)
					out = "Xnt" + out.substr(1);
				if (owner_has_dependent_typename_argument)
					abi_add_substitution(ctx, out);
				return out;
			}
			if (ctx.expression_tokens != NULL &&
			    arg.value_expr_end > arg.value_expr_begin)
			{
				string expression = abi_template_value_expression(
					*ctx.expression_tokens,
					arg.value_expr_begin,
					arg.value_expr_end,
					ctx.template_parameters);
				if (!expression.empty())
					return "X" + expression + "E";
			}
			if (!arg.value_name.empty())
			{
				string parameter_expr =
					abi_template_parameter_expression(
						arg.value_name,
						ctx.template_parameters);
				if (!parameter_expr.empty())
					return "X" + parameter_expr + "E";
				return "X" + abi_encoded_stable_value_name(arg.value_name) +
				       "E";
			}
		}
		if (arg.value_binding != NULL)
			return "XadL" +
			       abi_binding_symbol_with_substitutions(
				       arg.value_binding,
				       ctx.template_parameters) +
			       "E";
		if (abi_type_is_dependent_parameter(arg.type))
			return "Li" + to_string(arg.value) + "E";
		return "L" + abi_type_with_substitutions(arg.type, ctx) +
		       to_string(arg.value) + "E";
	}
	if (arg.kind == TemplateArgumentKind::Pack)
	{
		string out = "J";
		for (size_t i = 0; i < arg.pack.size(); ++i)
			out += abi_template_argument_with_substitutions(arg.pack[i],
			                                               ctx);
		out += "E";
		return out;
	}
	string name = arg.template_declaration != NULL
		? qualified_template_declaration_name(arg.template_declaration)
		: !arg.value_name.empty()
		  ? arg.value_name
		  : string("v");
	return abi_template_name(name);
}

string abi_template_argument_for_parameter_with_substitutions(
	const TemplateParameterInfo& parameter,
	const TemplateArgument& arg,
	AbiSubstitutionContext& ctx)
{
	if (parameter.kind == TemplateParameterKind::NonType &&
	    parameter.type.get() != NULL &&
	    abi_type_is_dependent_parameter(parameter.type))
	{
		if (arg.kind == TemplateArgumentKind::Value)
			return abi_type_with_substitutions(parameter.type, ctx) +
			       abi_template_argument_with_substitutions(arg, ctx);
		if (arg.kind == TemplateArgumentKind::Pack)
		{
			string out = "J";
			for (size_t i = 0; i < arg.pack.size(); ++i)
			{
				if (arg.pack[i].kind == TemplateArgumentKind::Value)
					out += abi_type_with_substitutions(
						       parameter.type, ctx) +
					       abi_template_argument_with_substitutions(
						       arg.pack[i], ctx);
				else
					out += abi_template_argument_with_substitutions(
						arg.pack[i], ctx);
			}
			out += "E";
			return out;
		}
	}
	return abi_template_argument_with_substitutions(arg, ctx);
}

string abi_type_with_substitutions(TypePtr type,
                                   AbiSubstitutionContext& ctx)
{
	if (type.get() == NULL)
		return "v";
	string probe = abi_type_probe_with_substitutions(type, ctx);
	size_t whole = abi_find_substitution(ctx, probe);
	if (whole != static_cast<size_t>(-1))
		return abi_substitution_code(whole);
	if (type->is_dependent_typename)
		return abi_use_or_add_substitution(
			ctx,
			abi_dependent_typename_type_with_substitutions(type,
			                                               ctx,
			                                               true));
	if (type->kind == pa11::TypeKind::Cv)
	{
		string quals;
		if ((type->cv & pa11::CV_CONST) != 0)
			quals += "K";
		if ((type->cv & pa11::CV_VOLATILE) != 0)
			quals += "V";
		return abi_use_or_add_substitution(
			ctx, quals + abi_type_with_substitutions(type->base, ctx));
	}
	if (type->kind == pa11::TypeKind::Pointer)
		return abi_use_or_add_substitution(
			ctx, "P" + abi_type_with_substitutions(type->base, ctx));
	if (type->kind == pa11::TypeKind::LValueReference)
		return abi_use_or_add_substitution(
			ctx, "R" + abi_type_with_substitutions(type->base, ctx));
	if (type->kind == pa11::TypeKind::RValueReference)
		return abi_use_or_add_substitution(
			ctx, "O" + abi_type_with_substitutions(type->base, ctx));
	if (type->kind == pa11::TypeKind::Array)
		return abi_use_or_add_substitution(
			ctx,
			"A" + (type->unknown_bound ? string("") :
			       to_string(type->bound)) + "_" +
			abi_type_with_substitutions(type->base, ctx));
	if (type->kind == pa11::TypeKind::Function)
	{
		string out;
		if ((type->cv & pa11::CV_CONST) != 0)
			out += "K";
		if ((type->cv & pa11::CV_VOLATILE) != 0)
			out += "V";
		out += "F" + abi_type_with_substitutions(type->base, ctx);
		for (size_t i = 0; i < type->parameters.size(); ++i)
			out += abi_type_with_substitutions(type->parameters[i], ctx);
		if (type->parameters.empty())
			out += "v";
		out += "E";
		return abi_use_or_add_substitution(ctx, out);
	}
	if (type->kind == pa11::TypeKind::Record ||
	    type->kind == pa11::TypeKind::Enum)
		return abi_record_type_with_substitutions(type, ctx, true);
	if (type->kind == pa11::TypeKind::TemplateParameter ||
	    type->kind == pa11::TypeKind::TemplateTemplateParameter)
		return abi_template_parameter_type_with_substitutions(type->name,
		                                                      ctx);
	if (type->kind == pa11::TypeKind::MemberPointer)
	{
		string semantic_key =
			abi_type(type, ctx.template_parameters, ctx.expression_tokens);
		map<string, size_t>::const_iterator semantic =
			ctx.semantic_type_substitutions.find(semantic_key);
		if (semantic != ctx.semantic_type_substitutions.end())
			return abi_substitution_code(semantic->second);
		string member_class =
			abi_type_with_substitutions(type->member_class, ctx);
		string member_type = abi_type_with_substitutions(type->base, ctx);
		string encoded = "M" + member_class + member_type;
		string out = abi_use_or_add_substitution(ctx, encoded);
		size_t index = abi_find_substitution(ctx, encoded);
		if (index != static_cast<size_t>(-1))
			ctx.semantic_type_substitutions[semantic_key] = index;
		return out;
	}
	return abi_fundamental_type(type->fundamental);
}

string abi_function_return_type_with_substitutions(
	TypePtr type,
	AbiSubstitutionContext& ctx)
{
	if (type.get() != NULL && type->is_dependent_typename)
	{
		string decltype_type =
			abi_dependent_decltype_type_with_substitutions(type, ctx);
		if (!decltype_type.empty())
			return decltype_type;
		bool saved = ctx.use_actual_template_parameter_types;
		ctx.use_actual_template_parameter_types = true;
		string encoded =
			abi_dependent_typename_type_with_substitutions(type, ctx, false);
		ctx.use_actual_template_parameter_types = saved;
		return encoded;
	}
	return abi_type_with_substitutions(type, ctx);
}

string abi_type_probe_with_substitutions(TypePtr type,
                                         AbiSubstitutionContext& ctx);
string abi_record_type_probe_with_substitutions(TypePtr type,
                                                AbiSubstitutionContext& ctx,
                                                bool include_namespace);

string abi_scope_prefix_probe_with_substitutions(const vector<Scope*>& scopes,
                                                AbiSubstitutionContext& ctx)
{
	string out;
	string prefix_key;
	for (size_t i = 0; i < scopes.size(); ++i)
	{
		string component;
		if (scopes[i]->kind == ScopeKind::Namespace)
			component = abi_scope_component_with_substitutions(scopes[i],
			                                                  ctx);
		else if (scopes[i]->kind == ScopeKind::Class)
			component = abi_record_type_probe_with_substitutions(
				pa11::record_type_for_scope(scopes[i]), ctx, false);
		if (component.empty())
			continue;
		string key = prefix_key.empty()
			? component : string("N") + prefix_key + component + "E";
		size_t found = component == "St" ? static_cast<size_t>(-1) :
			abi_find_substitution(ctx, key);
		out += found == static_cast<size_t>(-1)
			? component : abi_substitution_code(found);
		prefix_key = key;
	}
	return out;
}

string abi_template_instance_argument_probe_with_substitutions(
	const pa11::TemplateInstanceArgument& arg,
	AbiSubstitutionContext& ctx)
{
	if (arg.kind == pa11::TemplateInstanceArgumentKind::Type)
		return abi_type_probe_with_substitutions(arg.type, ctx);
	if (arg.kind == pa11::TemplateInstanceArgumentKind::Value)
	{
		if (!arg.value_name.empty())
			return "L" + abi_type_probe_with_substitutions(arg.type, ctx) +
			       abi_encoded_stable_value_name(arg.value_name) + "E";
		if (abi_type_is_dependent_parameter(arg.type))
			return "Li" + to_string(arg.value) + "E";
		return "L" + abi_type_probe_with_substitutions(arg.type, ctx) +
		       to_string(arg.value) + "E";
	}
	if (arg.kind == pa11::TemplateInstanceArgumentKind::Pack)
	{
		string out = "J";
		for (size_t i = 0; i < arg.pack.size(); ++i)
			out += abi_template_instance_argument_probe_with_substitutions(
				arg.pack[i], ctx);
		out += "E";
		return out;
	}
	return abi_template_name(arg.template_name);
}

string abi_record_type_probe_with_substitutions(TypePtr type,
                                                AbiSubstitutionContext& ctx,
                                                bool include_namespace)
{
	TypePtr bare = type.get() != NULL ? pa11::strip_cv(type) : TypePtr();
	if (bare.get() == NULL)
		return "v";
	string special = abi_std_abbreviation(bare);
	string name = bare->is_template_specialization &&
	              !bare->template_primary_name.empty()
		? bare->template_primary_name : bare->name;
	size_t args = name.find('<');
	if (args != string::npos)
		name = name.substr(0, args);
	string leaf = special.empty() ? abi_source_name(name) : special;
	vector<Scope*> scopes;
	string scope_prefix;
	if (special.empty() && include_namespace && bare->scope != NULL)
	{
		scopes = abi_scope_path_outer_first(bare->scope->parent);
		if (!scopes.empty() &&
		    !(scopes.size() == 1 && abi_scope_is_std_namespace(scopes[0])))
			scope_prefix =
				abi_scope_prefix_probe_with_substitutions(scopes, ctx);
	}
	if (bare->is_template_specialization)
	{
		leaf += "I";
		for (size_t i = 0; i < bare->template_arguments.size(); ++i)
			leaf += abi_template_instance_argument_probe_with_substitutions(
				bare->template_arguments[i], ctx);
		leaf += "E";
	}
	if (!special.empty())
		return leaf;
	if (!scopes.empty())
	{
		if (scopes.size() == 1 && abi_scope_is_std_namespace(scopes[0]))
			return "St" + leaf;
		return "N" + scope_prefix + leaf + "E";
	}
	return leaf;
}

string abi_type_probe_with_substitutions(TypePtr type,
                                         AbiSubstitutionContext& ctx)
{
	if (type.get() == NULL)
		return "v";
	if (type->is_dependent_typename)
		return abi_dependent_typename_type(type,
		                                   ctx.template_parameters,
		                                   ctx.expression_tokens,
		                                   true);
	if (type->kind == pa11::TypeKind::Cv)
	{
		string quals;
		if ((type->cv & pa11::CV_CONST) != 0)
			quals += "K";
		if ((type->cv & pa11::CV_VOLATILE) != 0)
			quals += "V";
		return quals + abi_type_probe_with_substitutions(type->base, ctx);
	}
	if (type->kind == pa11::TypeKind::Pointer)
		return "P" + abi_type_probe_with_substitutions(type->base, ctx);
	if (type->kind == pa11::TypeKind::LValueReference)
		return "R" + abi_type_probe_with_substitutions(type->base, ctx);
	if (type->kind == pa11::TypeKind::RValueReference)
		return "O" + abi_type_probe_with_substitutions(type->base, ctx);
	if (type->kind == pa11::TypeKind::Array)
		return "A" + (type->unknown_bound ? string("") :
		       to_string(type->bound)) + "_" +
		       abi_type_probe_with_substitutions(type->base, ctx);
	if (type->kind == pa11::TypeKind::Function)
	{
		string out;
		if ((type->cv & pa11::CV_CONST) != 0)
			out += "K";
		if ((type->cv & pa11::CV_VOLATILE) != 0)
			out += "V";
		out += "F" + abi_type_probe_with_substitutions(type->base, ctx);
		for (size_t i = 0; i < type->parameters.size(); ++i)
			out += abi_type_probe_with_substitutions(type->parameters[i],
			                                        ctx);
		if (type->parameters.empty())
			out += "v";
		return out + "E";
	}
	if (type->kind == pa11::TypeKind::Record ||
	    type->kind == pa11::TypeKind::Enum)
		return abi_record_type_probe_with_substitutions(type, ctx, true);
	if (type->kind == pa11::TypeKind::TemplateParameter ||
	    type->kind == pa11::TypeKind::TemplateTemplateParameter)
	{
		map<string, size_t>::const_iterator found =
			ctx.template_parameters.find(type->name);
		size_t index = found == ctx.template_parameters.end() ? 0 : found->second;
		return index == 0 ? string("T_") :
		       string("T") + to_string(index - 1) + "_";
	}
	if (type->kind == pa11::TypeKind::MemberPointer)
		return "M" + abi_type_probe_with_substitutions(type->member_class,
		                                               ctx) +
		       abi_type_probe_with_substitutions(type->base, ctx);
	return abi_fundamental_type(type->fundamental);
}


}  // namespace internal
}  // namespace pa12
