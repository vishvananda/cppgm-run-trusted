#include "pa12_internal.h"
#include "pa12_expr_semantics_support.h"
#include "pa12_templates_function_support.h"
#include <algorithm>
#include <exception>
#include <sstream>
#include <stdexcept>
using namespace std;
namespace pa12 {
namespace internal {
bool has_token(const vector<Token>& tokens, size_t begin, size_t end, ETokenType type);
void merge_template_defaults(vector<TemplateParameterInfo>& target, const vector<TemplateParameterInfo>& source);
Binding* find_matching_function_template_placeholder(const map<Binding*, TemplateDeclaration*>& placeholders, Scope* scope, const string& name, TypePtr type, const vector<TemplateParameterInfo>& parameters);
void collect_template_parameter_placeholders(const vector<TemplateParameterInfo>& parameters, map<string, TypePtr>& parameter_types, map<string, TemplateArgument>& parameter_values);
set<string> collect_template_type_parameter_packs(const vector<TemplateParameterInfo>& parameters);
vector<string> function_parameter_names_from_tokens(const vector<Token>& tokens, size_t lparen, size_t end, bool include_this);
bool function_header_has_noexcept(const vector<Token>& tokens, size_t lparen, size_t end);
Scope* primary_class_template_scope(TemplateDeclaration* declaration);
size_t explicit_function_parameter_name_count(const vector<string>& names);
vector<pa11::TemplateInstanceArgument> template_instance_arguments(
	const vector<TemplateArgument>& arguments);
bool hosted_library_namespace_scope(Scope* scope);
bool owner_pattern_is_primary_parameter_list(
	const vector<TemplateArgument>& pattern,
	const vector<TemplateParameterInfo>& parameters);
bool skip_template_id_argument_tokens(const vector<Token>& tokens, size_t& pos);
bool template_parameter_lists_match(const vector<TemplateParameterInfo>& left,
                                    const vector<TemplateParameterInfo>& right);
namespace {
pa11::TemplateInstanceArgument dependent_value_instance_argument(
	const TemplateArgument& argument)
{
	if (argument.pack_expansion && argument.kind != TemplateArgumentKind::Pack)
	{
		TemplateArgument element = argument;
		element.pack_expansion = false;
		vector<pa11::TemplateInstanceArgument> pack;
		pack.push_back(dependent_value_instance_argument(element));
		return pa11::TemplateInstanceArgument::pack_arg(pack);
	}
	if (argument.kind == TemplateArgumentKind::Type)
		return pa11::TemplateInstanceArgument::type_arg(argument.type);
	if (argument.kind == TemplateArgumentKind::Value)
	{
		pa11::TemplateInstanceArgument out = argument.dependent
			? pa11::TemplateInstanceArgument::dependent_value_arg(
				argument.type)
			: pa11::TemplateInstanceArgument::value_arg(argument.type,
			                                            argument.value);
		out.value_name = argument.value_name;
		out.value_negated = argument.value_negated;
		out.value_owner_template_name =
			argument.value_owner_template_name;
		out.value_member_name = argument.value_member_name;
		out.value_owner_template_arguments =
			argument.value_owner_template_arguments;
		out.value_expr_begin = argument.value_expr_begin;
		out.value_expr_end = argument.value_expr_end;
		return out;
	}
	if (argument.kind == TemplateArgumentKind::Template)
	{
		pa11::TemplateInstanceArgument out =
			pa11::TemplateInstanceArgument::template_arg(
				argument.template_declaration != NULL
				? qualified_template_declaration_name(
					argument.template_declaration)
				: !argument.value_name.empty()
				  ? argument.value_name
				  : string("template_parameter"));
		out.dependent = argument.template_declaration == NULL;
		return out;
	}
	vector<pa11::TemplateInstanceArgument> pack;
	for (size_t i = 0; i < argument.pack.size(); ++i)
		pack.push_back(
			dependent_value_instance_argument(argument.pack[i]));
	pa11::TemplateInstanceArgument out =
		pa11::TemplateInstanceArgument::pack_arg(pack);
	out.value_name = argument.value_name;
	out.template_name = argument.value_name;
	return out;
}
vector<pa11::TemplateInstanceArgument> dependent_value_instance_arguments(
	const vector<TemplateArgument>& arguments)
{
	vector<pa11::TemplateInstanceArgument> out;
	for (size_t i = 0; i < arguments.size(); ++i)
		out.push_back(dependent_value_instance_argument(arguments[i]));
	return out;
}  // namespace
}  // namespace
bool Parser::find_template_type_substitution(const string& name,
                                             TypePtr& out) const
{
	for (size_t i = template_type_substitutions_.size(); i > 0; --i)
	{
		map<string, TypePtr>::const_iterator found =
			template_type_substitutions_[i - 1].find(name);
		if (found != template_type_substitutions_[i - 1].end())
		{
			out = found->second;
			return true;
		}
	}
	return false;
}
bool Parser::find_template_value_substitution(const string& name,
                                              TemplateArgument& out) const
{
	for (size_t i = template_value_substitutions_.size(); i > 0; --i)
	{
		map<string, TemplateArgument>::const_iterator found =
			template_value_substitutions_[i - 1].find(name);
		if (found != template_value_substitutions_[i - 1].end())
		{
			out = found->second;
			return true;
		}
		if (i - 1 < template_type_substitutions_.size() &&
		    template_type_substitutions_[i - 1].find(name) !=
			    template_type_substitutions_[i - 1].end())
			return false;
	}
	return false;
}
bool Parser::find_function_parameter_pack_substitution(
	const string& name,
	vector<Binding*>& out) const
{
	if (function_parameter_pack_substitutions_.empty())
		return false;
	{
		map<string, vector<Binding*> >::const_iterator found =
			function_parameter_pack_substitutions_.back().find(name);
		if (found != function_parameter_pack_substitutions_.back().end())
		{
			out = found->second;
			return true;
		}
	}
	return false;
}
bool Parser::try_parse_template_template_argument(TemplateArgument& out)
{
	size_t save = pos_;
		Scope* qualifier = NULL;
		string qualifier_spelling;
		bool qualifier_template_keyword = false;
	bool template_id_qualifier = false;
	if (at_identifier() && lookahead(OP_LT, 1))
	{
		size_t p = pos_ + 1;
		int depth = 0;
		while (p < tokens_.size())
		{
			if (tokens_[p].kind == posttoken::TokenKind::Simple &&
			    tokens_[p].type == OP_LT)
				++depth;
			else if (tokens_[p].kind == posttoken::TokenKind::Simple &&
			         tokens_[p].type == OP_GT)
			{
				--depth;
				if (depth == 0)
				{
					template_id_qualifier =
						p + 1 < tokens_.size() &&
						tokens_[p + 1].kind ==
							posttoken::TokenKind::Simple &&
						tokens_[p + 1].type == OP_COLON2;
					break;
				}
			}
			++p;
		}
	}
	if (at(OP_COLON2) ||
	    (at_identifier() &&
	     (lookahead(OP_COLON2, 1) || template_id_qualifier)))
	{
			try
				{
					qualifier = parse_nested_name_specifier(&qualifier_spelling);
				}
				catch (const exception&)
				{
					pos_ = save;
					return false;
				}
			qualifier_template_keyword = consume(KW_TEMPLATE);
		}
	if (!at_identifier())
	{
		pos_ = save;
		return false;
	}
	string name = consume_identifier();
	if (at(OP_LT) || (!at(OP_COMMA) && !at(OP_GT) && !at(OP_DOTS)))
	{
		pos_ = save;
		return false;
	}
	if (qualifier == NULL)
	{
		TemplateArgument subst;
		if (find_template_value_substitution(name, subst) &&
		    subst.kind == TemplateArgumentKind::Template)
		{
			out = subst;
			return true;
		}
	}
		TemplateDeclaration* declaration = NULL;
		if (qualifier != NULL)
		{
			declaration = find_class_template(qualifier, name);
			if (declaration == NULL)
				declaration = find_alias_template(qualifier, name);
		}
		else
		{
			for (Scope* cur = current_scope(); cur != NULL; cur = cur->parent)
			{
				declaration = find_class_template(cur, name);
				if (declaration == NULL)
					declaration = find_alias_template(cur, name);
				if (declaration != NULL)
					break;
			}
			if (declaration == NULL && global_scope() != current_scope())
			{
				declaration = find_class_template(global_scope(), name);
				if (declaration == NULL)
					declaration = find_alias_template(global_scope(), name);
			}
		}
		if (declaration == NULL)
		{
		TypePtr qualifier_record =
			qualifier != NULL ? pa11::record_type_for_scope(qualifier)
			                  : TypePtr();
			if (qualifier_record.get() != NULL &&
			    type_is_template_dependent(qualifier_record) &&
			    qualifier_template_keyword)
			{
				out = TemplateArgument::template_arg(NULL);
				out.value_name = qualifier_spelling + name;
			return true;
		}
		pos_ = save;
		return false;
	}
	out = TemplateArgument::template_arg(declaration);
	return true;
}
bool Parser::try_parse_dependent_qualified_non_type_template_argument(
	TemplateArgument& out)
{ size_t save = pos_; if (!at_identifier()) return false; string spelling = consume_identifier(); string root_name = spelling; TypePtr root_type; bool have_root_type_substitution =
find_template_type_substitution(spelling, root_type); TypePtr substituted_root = root_type.get() != NULL ? pa11::strip_cv(root_type) : TypePtr(); bool dependent_root = have_root_type_substitution &&
(type_is_template_dependent(root_type) ||
 (substituted_root.get() != NULL &&
  substituted_root->kind == pa11::TypeKind::TemplateParameter)); string owner_template_name; vector<pa11::TemplateInstanceArgument> owner_template_arguments; if (have_root_type_substitution && substituted_root.get() != NULL &&
substituted_root->kind == pa11::TypeKind::Record && substituted_root->is_template_specialization) { owner_template_name = substituted_root->template_primary_name.empty()
? root_name : substituted_root->template_primary_name; owner_template_arguments = substituted_root->template_arguments; } TemplateArgument root_template; if (find_template_value_substitution(root_name, root_template) &&
root_template.kind == TemplateArgumentKind::Template && root_template.template_declaration == NULL) dependent_root = true; if (have_root_type_substitution && !dependent_root) { pos_ = save; return false; } vector<TemplateArgument> root_arguments; if (at(OP_LT)) { try {
parse_template_argument_list(root_arguments); } catch (const exception&) { pos_ = save; return false; } for (size_t i = 0; i < root_arguments.size(); ++i) if (template_argument_has_template_parameter( root_arguments[i],
record_template_arguments_)) dependent_root = true; owner_template_arguments = dependent_value_instance_arguments(root_arguments); spelling += "<>"; } if ((!dependent_root && !have_root_type_substitution) || !at(OP_COLON2)) { pos_ = save; return false; }
string final_member_name; do { expect(OP_COLON2); spelling += "::"; consume(KW_TEMPLATE); if (!at_identifier()) { pos_ = save; return false; } string member_name = consume_identifier(); spelling += member_name;
final_member_name = member_name; if (at(OP_LT)) { if (!skip_template_id_argument_tokens(tokens_, pos_)) { pos_ = save; return false; } spelling += "<>"; } } while (at(OP_COLON2)); TypePtr dependent_value_type;
if (!validating_template_definition_ && !root_name.empty() && !final_member_name.empty()) { size_t type_save = pos_; try { TemplateDeclaration* alias = find_alias_template(NULL, root_name);
TemplateDeclaration* klass = alias == NULL ? find_class_template(NULL, root_name) : NULL; TypePtr owner = alias != NULL ? instantiate_alias_template(alias, root_arguments) : (klass != NULL
? instantiate_class_template(klass, root_arguments) : TypePtr()); TypePtr bare_owner = owner.get() != NULL ? pa11::strip_cv(owner) : TypePtr(); if (bare_owner.get() != NULL &&
bare_owner->kind == pa11::TypeKind::Record && bare_owner->scope != NULL) { complete_template_record(bare_owner); vector<Binding*> found = lookup_qualified_set(bare_owner->scope, final_member_name, pa11::LOOKUP_VALUE);
if (!found.empty() && found[0]->type.get() != NULL) dependent_value_type = expression_object_type(found[0]->type); } } catch (const exception&) { pos_ = type_save; } pos_ = type_save; } if (at(OP_LPAREN)) { try {
skip_balanced(OP_LPAREN, OP_RPAREN); } catch (const exception&) { pos_ = save; return false; } spelling += "()"; } ETokenType follow_op = OP_PLUS; int follow_prec = 0;
bool binary_follow = binary_operator(follow_op, follow_prec); if (!at(OP_COMMA) && !at(OP_GT) && !at(OP_DOTS) && !at(OP_RPAREN) && !at(OP_LSQUARE) && !binary_follow) { pos_ = save; return false; }
out = TemplateArgument::dependent_value_arg(dependent_value_type); out.value_name = spelling; if (!final_member_name.empty()) { out.value_owner_template_name = owner_template_name.empty()
? root_name : owner_template_name; out.value_member_name = final_member_name; out.value_owner_template_arguments = owner_template_arguments; } return true; }
bool Parser::try_parse_dependent_unqualified_template_call_non_type_template_argument(
	TemplateArgument& out)
{
	size_t save = pos_;
	if ((active_class_instantiations_.empty() &&
	     template_type_substitutions_.empty() &&
	     template_value_substitutions_.empty()) ||
	    !at_identifier() ||
	    !lookahead(OP_LT, 1))
		return false;
	string name = consume_identifier();
	vector<TemplateArgument> arguments;
	try
	{
		parse_template_argument_list(arguments);
		if (!at(OP_LPAREN))
		{
			pos_ = save;
			return false;
		}
		skip_balanced(OP_LPAREN, OP_RPAREN);
	}
	catch (const exception&)
	{
		pos_ = save;
		return false;
	}
	ETokenType follow_op = OP_PLUS;
	int follow_prec = 0;
	bool binary_follow = binary_operator(follow_op, follow_prec);
	if (!at(OP_COMMA) && !at(OP_GT) && !at(OP_DOTS) &&
	    !at(OP_RPAREN) && !at(OP_LSQUARE) && !binary_follow)
	{
		pos_ = save;
		return false;
	}
	out = TemplateArgument::dependent_value_arg(
		pa11::make_fundamental(FT_BOOL));
	out.value_name = name + "<>()";
	TypePtr current_record = pa11::record_type_for_scope(current_scope());
	TypePtr current_bare = current_record.get() != NULL
		? pa11::strip_cv(current_record) : TypePtr();
	if (current_bare.get() != NULL &&
	    current_bare->kind == pa11::TypeKind::Record)
	{
		out.value_owner_template_name =
			current_bare->template_primary_name.empty()
			? current_bare->name
			: current_bare->template_primary_name;
		out.value_member_name = name;
		out.value_owner_template_arguments =
			current_bare->template_arguments;
		if (out.value_owner_template_arguments.empty())
		{
			map<const void*, vector<TemplateArgument> >::const_iterator
				args = record_template_arguments_.find(current_bare.get());
			if (args != record_template_arguments_.end())
				out.value_owner_template_arguments =
					template_instance_arguments(args->second);
		}
	}
	out.value_expr_begin = save;
	out.value_expr_end = pos_;
	(void)arguments;
	return true;
}
TemplateArgument Parser::parse_non_type_template_argument_expression()
{ size_t save = pos_; ++template_argument_expression_depth_; Expr expr; try { expr = parse_assignment_expression(); } catch (...) { exception_ptr original_exception = current_exception(); --template_argument_expression_depth_; pos_ = save; TemplateArgument dependent;
if ((!active_class_instantiations_.empty() || !template_type_substitutions_.empty() || !template_value_substitutions_.empty()) && try_parse_dependent_qualified_non_type_template_argument( dependent)) {
dependent.value_expr_begin = save; dependent.value_expr_end = pos_; return dependent; } if ((!active_class_instantiations_.empty() || !template_type_substitutions_.empty() || !template_value_substitutions_.empty()) && try_parse_dependent_unqualified_template_call_non_type_template_argument( dependent)) return dependent; rethrow_exception(original_exception); } size_t expr_end = pos_; --template_argument_expression_depth_; if (expr.valid && !expr.has_constant_value) {
ConstexprValue value; if (try_evaluate_constexpr_expr(expr.node, value) && !value.is_object) { expr.has_constant_value = true; expr.constant_value = value.int_value; expr.node.has_constant_value = true;
expr.node.constant_value = value.int_value; } } if (expr.valid && !expr.has_constant_value) { try { Conversion conv = convert_to(expr, pa11::make_fundamental(FT_BOOL)); if (conv.viable && !conv.expr.has_constant_value) {
ConstexprValue value; if (try_evaluate_constexpr_expr(conv.expr.node, value)) apply_constexpr_value(conv.expr, value); } if (conv.viable && conv.expr.has_constant_value) expr = conv.expr; } catch (const runtime_error&) {
} } TypePtr expr_bare = expr.type.get() != NULL ? pa11::strip_cv(expression_object_type(expr.type)) : TypePtr(); if (expr_bare.get() != NULL && expr_bare->kind == pa11::TypeKind::MemberPointer && expr.node.has_op &&
expr.node.op == OP_AMP && !expr.node.children.empty() && expr.node.children[0].binding != NULL && expr.dependent_value_owner_template_name.empty() && expr.overloads.size() <= 1) { Binding* member = expr.node.children[0].binding; if (member->aliased_binding != NULL && member->target_scope != NULL)
member = member->aliased_binding; TemplateArgument arg = TemplateArgument::value_arg(expression_object_type(expr.type), reinterpret_cast<uint64_t>( member)); arg.value_binding = member; return arg; }
	Binding* function_binding = NULL; if (expr.binding != NULL && expr.binding->kind == BindingKind::Function) function_binding = expr.binding; else if (expr.overloads.size() == 1 &&
expr.overloads[0]->kind == BindingKind::Function) function_binding = expr.overloads[0]; if (function_binding != NULL) { TypePtr value_type = expr.type; if (value_type.get() != NULL &&
value_type->kind == pa11::TypeKind::Function) value_type = pa11::make_pointer(value_type); TemplateArgument arg = TemplateArgument::value_arg(value_type, reinterpret_cast<uint64_t>( function_binding));
arg.value_binding = function_binding; return arg; } if (expr.binding != NULL && expr.binding->kind == BindingKind::Variable && expr.category == ValueCategory::LValue && !expr.has_constant_value) {
if (expr.binding->is_static_member && (!active_class_instantiations_.empty() || !template_type_substitutions_.empty() || !template_value_substitutions_.empty())) { TemplateArgument arg =
TemplateArgument::dependent_value_arg( expression_object_type(expr.type)); arg.value_name = expr.dependent_value_name.empty() ? expr.binding->name : expr.dependent_value_name; arg.value_owner_template_name =
expr.dependent_value_owner_template_name; arg.value_member_name = expr.dependent_value_member_name; arg.value_negated = expr.dependent_value_negated; arg.value_owner_template_arguments =
expr.dependent_value_owner_template_arguments; arg.value_expr_begin = save; arg.value_expr_end = expr_end; return arg; } TemplateArgument arg = TemplateArgument::value_arg(expression_object_type(expr.type),
	reinterpret_cast<uint64_t>( expr.binding)); arg.value_binding = expr.binding; return arg; } if (!expr.has_constant_value) { if (!expr.dependent_value_name.empty() || !active_class_instantiations_.empty() || !template_type_substitutions_.empty() ||
	!template_value_substitutions_.empty()) { TemplateArgument qualified_dependent; size_t replay_save = pos_; pos_ = save; bool saw_amp = consume(OP_AMP); bool parsed_qualified = saw_amp && try_parse_dependent_qualified_non_type_template_argument(qualified_dependent); if (parsed_qualified) { qualified_dependent.type = expression_object_type(expr.type); qualified_dependent.value_expr_begin = save; qualified_dependent.value_expr_end = expr_end; pos_ = replay_save; return qualified_dependent; } pos_ = replay_save; TemplateArgument arg = TemplateArgument::dependent_value_arg( expression_object_type(expr.type)); arg.value_name = expr.dependent_value_name; arg.value_owner_template_name =
expr.dependent_value_owner_template_name; arg.value_member_name = expr.dependent_value_member_name; arg.value_negated = expr.dependent_value_negated; arg.value_owner_template_arguments =
expr.dependent_value_owner_template_arguments; arg.value_expr_begin = save; arg.value_expr_end = expr_end; return arg; } throw runtime_error("invalid non-type template argument"); }
return TemplateArgument::value_arg(expression_object_type(expr.type), expr.constant_value); }
}  // namespace internal
}  // namespace pa12
