#include "pa12_internal.h"
#include "pa12_expr_semantics_support.h"
#include "pa12_templates_function_support.h"
#include <algorithm>
#include <sstream>
#include <stdexcept>
using namespace std;
namespace pa12 {
namespace internal {
namespace {
bool template_argument_has_top_level_brace(const vector<Token>& tokens,
                                           size_t pos)
{
	int angle_depth = 0;
	int paren_depth = 0;
	int square_depth = 0;
	int brace_depth = 0;
	for (size_t i = pos; i < tokens.size(); ++i)
	{
		const Token& token = tokens[i];
		if (token.kind != posttoken::TokenKind::Simple)
			continue;
		if (token.type == OP_LT)
		{
			++angle_depth;
			continue;
		}
		if (token.type == OP_GT)
		{
			if (angle_depth == 0 && paren_depth == 0 &&
			    square_depth == 0 && brace_depth == 0)
				return false;
			if (angle_depth > 0)
				--angle_depth;
			continue;
		}
		if (token.type == OP_COMMA && angle_depth == 0 &&
		    paren_depth == 0 && square_depth == 0 && brace_depth == 0)
			return false;
		if (token.type == OP_LPAREN)
			++paren_depth;
		else if (token.type == OP_RPAREN && paren_depth > 0)
			--paren_depth;
		else if (token.type == OP_LSQUARE)
			++square_depth;
		else if (token.type == OP_RSQUARE && square_depth > 0)
			--square_depth;
		else if (token.type == OP_LBRACE)
		{
			if (angle_depth == 0 && paren_depth == 0 &&
			    square_depth == 0 && brace_depth == 0)
				return true;
			++brace_depth;
		}
		else if (token.type == OP_RBRACE && brace_depth > 0)
			--brace_depth;
	}
	return false;
}

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
			? pa11::TemplateInstanceArgument::dependent_value_arg(argument.type)
			: pa11::TemplateInstanceArgument::value_arg(argument.type,
			                                            argument.value);
		out.value_name = argument.value_name;
		out.value_negated = argument.value_negated;
		out.value_owner_template_name = argument.value_owner_template_name;
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
		pack.push_back(dependent_value_instance_argument(argument.pack[i]));
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
}
}  // namespace

bool Parser::parse_template_argument_list(vector<TemplateArgument>& arguments)
{ if (!consume(OP_LT)) return false; if (consume(OP_GT)) return true; for (;;) { size_t save = pos_; if (at_identifier()) { string value_name = current().source; TemplateArgument subst;
bool have_value_substitution = false; bool hidden_by_type_substitution = false; size_t depth = max(template_type_substitutions_.size(), template_value_substitutions_.size());
for (size_t offset = 0; offset < depth; ++offset) { bool have_value = false; TemplateArgument candidate; if (offset < template_value_substitutions_.size()) { size_t index =
template_value_substitutions_.size() - 1 - offset; map<string, TemplateArgument>::const_iterator found = template_value_substitutions_[index].find(value_name); if (found != template_value_substitutions_[index].end()) {
have_value = true; candidate = found->second; } } if (have_value && candidate.kind != TemplateArgumentKind::Type) { subst = candidate; have_value_substitution = true; break; }
if (offset < template_type_substitutions_.size()) { size_t index = template_type_substitutions_.size() - 1 - offset; if (template_type_substitutions_[index].find(value_name) != template_type_substitutions_[index].end())
{ hidden_by_type_substitution = true; break; } } } if (have_value_substitution && !hidden_by_type_substitution && (lookahead(OP_COMMA, 1) || lookahead(OP_GT, 1) || lookahead(OP_DOTS, 1))) { ++pos_; TemplateArgument arg;
if (subst.kind == TemplateArgumentKind::Pack && !at(OP_DOTS)) { TypePtr type_subst; if (find_template_type_substitution(value_name, type_subst) && active_type_parameter_pack(value_name))
arg = TemplateArgument::type_arg(type_subst); else if (!subst.pack.empty() && subst.pack[0].dependent && subst.pack[0].value_name == value_name) arg = subst.pack[0]; else { TypePtr value_type =
!subst.pack.empty() ? subst.pack[0].type : TypePtr(); arg = TemplateArgument::dependent_value_arg( value_type.get() != NULL ? value_type : pa11::make_fundamental(FT_INT)); arg.value_name = value_name; } } else
arg = subst; arg.pack_expansion = consume(OP_DOTS); arguments.push_back(arg); if (!consume(OP_COMMA)) break; continue; } } try { size_t braced_value_save = pos_; if (template_argument_has_top_level_brace(tokens_, pos_)) { TypePtr braced_type; bool parsed_braced_type = false;
++defer_class_template_completion_depth_; try { parsed_braced_type = try_parse_type_name(braced_type); } catch (...) { --defer_class_template_completion_depth_; throw; } --defer_class_template_completion_depth_;
if (parsed_braced_type && at(OP_LBRACE)) { Expr init = parse_braced_init_list(); if (init.node.children.empty()) { TemplateArgument braced_arg; TypePtr bare = pa11::strip_cv(braced_type);
if (type_is_template_dependent(braced_type)) { braced_arg = TemplateArgument::dependent_value_arg(braced_type); braced_arg.value_name = pa11::describe_type(braced_type) + "{}"; arguments.push_back(braced_arg);
if (!consume(OP_COMMA)) break; continue; } if (bare->kind == pa11::TypeKind::Record && bare->scope != NULL) { complete_template_record(bare); vector<Binding*> values = lookup_qualified_set(bare->scope, "value",
pa11::LOOKUP_VARIABLE); bool have_braced_value = false; for (size_t vi = 0; vi < values.size(); ++vi) if (values[vi]->has_constant) { braced_arg = TemplateArgument::value_arg( expression_object_type(values[vi]->type),
values[vi]->constant_value); have_braced_value = true; break; } if (have_braced_value) { arguments.push_back(braced_arg); if (!consume(OP_COMMA)) break; continue; } } } } } pos_ = braced_value_save; TypePtr type;
++defer_class_template_completion_depth_; try { type = parse_type_id(); } catch (...) { --defer_class_template_completion_depth_; throw; } --defer_class_template_completion_depth_; if (save < tokens_.size() &&
tokens_[save].type == KW_TYPENAME && at(OP_COLON2)) { TypePtr bare = type.get() != NULL ? pa11::strip_cv(type) : TypePtr(); if (bare.get() != NULL && !bare->template_primary_name.empty()) { string dependent_name =
bare->template_primary_name + "<>"; vector<vector<pa11::TemplateInstanceArgument> > argument_lists; if (!bare->template_arguments.empty()) argument_lists.push_back( bare->template_arguments); while (consume(OP_COLON2)) {
dependent_name += "::"; consume(KW_TEMPLATE); if (!at_identifier()) throw runtime_error( "invalid dependent typename argument"); dependent_name += consume_identifier(); if (at(OP_LT)) { dependent_name += "<>";
vector<TemplateArgument> member_args; parse_template_argument_list(member_args); argument_lists.push_back( dependent_value_instance_arguments( member_args)); } } TypePtr dependent = pa11::make_dependent_typename_type(
dependent_name, true, true, false); dependent->template_primary_name = bare->template_primary_name; dependent->template_arguments = bare->template_arguments; dependent->dependent_typename_template_argument_lists =
argument_lists; type = dependent; } } bool pack_expansion = consume(OP_DOTS); if (at(OP_COMMA) || at(OP_GT)) { TemplateArgument arg = TemplateArgument::type_arg(type); arg.pack_expansion = pack_expansion;
arguments.push_back(arg); } else throw runtime_error("template argument is not a type"); } catch (const exception&) { pos_ = save; if (consume(KW_TYPENAME)) { size_t typename_save = pos_; try { if (!at_identifier())
throw runtime_error( "invalid dependent typename argument"); string root_name = consume_identifier(); string dependent_name = root_name; vector<TemplateArgument> root_args; vector<vector<pa11::TemplateInstanceArgument> >
instance_argument_lists; if (at(OP_LT)) { dependent_name += "<>"; parse_template_argument_list(root_args); instance_argument_lists.push_back( dependent_value_instance_arguments( root_args)); } bool qualified = false;
while (consume(OP_COLON2)) { qualified = true; dependent_name += "::"; consume(KW_TEMPLATE); if (!at_identifier()) throw runtime_error( "invalid dependent typename argument"); dependent_name += consume_identifier();
if (at(OP_LT)) { dependent_name += "<>"; vector<TemplateArgument> member_args; parse_template_argument_list(member_args); instance_argument_lists.push_back( dependent_value_instance_arguments( member_args)); } }
if (!qualified || (!at(OP_COMMA) && !at(OP_GT) && !at(OP_DOTS))) throw runtime_error( "invalid dependent typename argument"); TypePtr dependent = pa11::make_dependent_typename_type( dependent_name, true, true, false);
dependent->template_primary_name = root_name; dependent->template_arguments = dependent_value_instance_arguments(root_args); dependent->dependent_typename_template_argument_lists = instance_argument_lists;
TemplateArgument arg = TemplateArgument::type_arg(dependent); arg.pack_expansion = consume(OP_DOTS); arguments.push_back(arg); if (!consume(OP_COMMA)) break; continue; } catch (const exception&) {
pos_ = typename_save - 1; } } pos_ = save; if (at_identifier() && (lookahead(OP_COMMA, 1) || lookahead(OP_GT, 1) || lookahead(OP_DOTS, 1))) { string current_name = current().source; TypePtr current_record =
pa11::record_type_for_scope(current_scope()); TypePtr current_bare = current_record.get() != NULL ? pa11::strip_cv(current_record) : TypePtr(); bool current_instantiation_name = current_bare.get() != NULL &&
current_bare->kind == pa11::TypeKind::Record && current_bare->is_template_specialization && (current_name == current_scope()->name || current_name == current_bare->name || current_name ==
current_bare->template_primary_name); if (current_instantiation_name) { ++pos_; TemplateArgument arg = TemplateArgument::type_arg(current_record); arg.pack_expansion = consume(OP_DOTS); arguments.push_back(arg);
if (!consume(OP_COMMA)) break; continue; } } TemplateArgument template_argument; if (try_parse_template_template_argument(template_argument)) { template_argument.pack_expansion = consume(OP_DOTS);
arguments.push_back(template_argument); if (!consume(OP_COMMA)) break; continue; } if (at_identifier() && lookahead(OP_DOTS, 1)) { string pack_name = consume_identifier(); expect(OP_DOTS); TypePtr type_subst;
if (find_template_type_substitution(pack_name, type_subst)) { TemplateArgument arg = TemplateArgument::type_arg(type_subst); arg.pack_expansion = true; arguments.push_back(arg); if (!at(OP_COMMA) && !at(OP_GT))
throw runtime_error( "template argument is not a type"); if (!consume(OP_COMMA)) break; continue; } TemplateArgument subst; if (!find_template_value_substitution(pack_name, subst) ||
subst.kind != TemplateArgumentKind::Pack) throw runtime_error("invalid template argument pack"); TemplateArgument arg = subst; arg.pack_expansion = true; arguments.push_back(arg); if (!at(OP_COMMA) && !at(OP_GT))
	throw runtime_error( "template argument is not a value"); if (!consume(OP_COMMA)) break; continue; }
	if (at_identifier() &&
	    current().source == "__integer_pack" &&
	    lookahead(OP_LPAREN, 1))
	{
		++pos_;
		expect(OP_LPAREN);
		size_t count_begin = pos_;
		Expr count = parse_assignment_expression();
		size_t count_end = pos_;
		expect(OP_RPAREN);
		bool pack_expansion = consume(OP_DOTS);
		if (!count.has_constant_value)
		{
			ConstexprValue value;
			if (try_evaluate_constexpr_expr(count.node, value) &&
			    !value.is_object)
			{
				count.has_constant_value = true;
				count.constant_value = value.int_value;
			}
		}
		TypePtr value_type = expression_object_type(count.type);
		if (!count.has_constant_value)
		{
			TemplateArgument dependent =
				TemplateArgument::dependent_value_arg(value_type);
			dependent.value_name = "__integer_pack";
			dependent.value_expr_begin = count_begin;
			dependent.value_expr_end = count_end;
			dependent.pack_expansion = pack_expansion;
			arguments.push_back(dependent);
			if (!consume(OP_COMMA))
				break;
			continue;
		}
		vector<TemplateArgument> elems;
		for (uint64_t i = 0; i < count.constant_value; ++i)
			elems.push_back(TemplateArgument::value_arg(value_type, i));
		TemplateArgument pack = TemplateArgument::pack_arg(elems);
		pack.pack_expansion = pack_expansion;
		arguments.push_back(pack);
		if (!consume(OP_COMMA))
			break;
		continue;
	}
	TemplateArgument arg = parse_non_type_template_argument_expression(); arg.pack_expansion = consume(OP_DOTS);
arguments.push_back(arg); } if (!consume(OP_COMMA)) break; } expect(OP_GT); return true; }
}  // namespace internal
}  // namespace pa12
