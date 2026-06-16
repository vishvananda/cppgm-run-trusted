#include "pa12_internal.h"
#include "pa12_expr_semantics_support.h"
#include "pa12_templates_function_support.h"
#include <algorithm>
#include <functional>
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
namespace {
bool hosted_library_namespace_scope(Scope* scope)
{
	for (Scope* cur = scope; cur != NULL; cur = cur->parent)
		if (cur->kind == ScopeKind::Namespace &&
		    (cur->name == "std" || cur->name == "__gnu_cxx"))
			return true;
	return false;
}

	bool owner_pattern_is_primary_parameter_list(
	const vector<TemplateArgument>& pattern,
	const vector<TemplateParameterInfo>& parameters)
{
	if (pattern.size() != parameters.size())
		return false;
	for (size_t i = 0; i < pattern.size(); ++i)
	{
		const TemplateParameterInfo& parameter = parameters[i];
		const TemplateArgument& argument = pattern[i];
		if (parameter.name.empty())
			return false;
		if (parameter.kind == TemplateParameterKind::Type)
		{
			if (argument.kind != TemplateArgumentKind::Type ||
			    argument.pack_expansion != parameter.is_pack)
				return false;
			TypePtr bare = argument.type.get() != NULL
				? pa11::strip_cv(argument.type) : TypePtr();
			if (bare.get() == NULL ||
			    bare->kind != pa11::TypeKind::TemplateParameter ||
			    bare->name.empty())
				return false;
		}
		else if (parameter.kind == TemplateParameterKind::NonType)
		{
			if (argument.kind != TemplateArgumentKind::Value ||
			    !argument.dependent ||
			    argument.value_name.empty())
				return false;
		}
		else
			return false;
	}
	return true;
}
bool skip_template_id_argument_tokens(const vector<Token>& tokens, size_t& pos)
{
	if (pos >= tokens.size() ||
	    tokens[pos].kind != posttoken::TokenKind::Simple ||
	    tokens[pos].type != OP_LT)
		return false;
	int depth = 0;
	int paren = 0;
	int square = 0;
	int brace = 0;
	while (pos < tokens.size())
	{
		const Token& tok = tokens[pos];
		if (tok.kind != posttoken::TokenKind::Simple)
		{
			++pos;
			continue;
		}
		if (tok.type == OP_LPAREN)
			++paren;
		else if (tok.type == OP_RPAREN && paren > 0)
			--paren;
		else if (tok.type == OP_LSQUARE)
			++square;
		else if (tok.type == OP_RSQUARE && square > 0)
			--square;
		else if (tok.type == OP_LBRACE)
			++brace;
		else if (tok.type == OP_RBRACE && brace > 0)
			--brace;
		else if (paren == 0 && square == 0 && brace == 0 &&
		         tok.type == OP_LT)
			++depth;
		else if (paren == 0 && square == 0 && brace == 0 &&
		         tok.type == OP_GT)
		{
			--depth;
			++pos;
			if (depth == 0)
				return true;
			continue;
		}
		++pos;
	}
	return false;
}
struct DependentMemberTemplateHeader
{
	size_t call_lparen;
	size_t member_name_pos;
	size_t member_colon;
	string member_name;
};
typedef function<string(ETokenType, const string&)> OperatorNameCallback;
void init_dependent_member_template_header(DependentMemberTemplateHeader& header,
                                           size_t end)
{
	header.call_lparen = end;
	header.member_name_pos = end;
	header.member_colon = end;
	header.member_name.clear();
}
bool find_dependent_member_template_header(
	const vector<Token>& tokens,
	TemplateDeclaration* declaration,
	const OperatorNameCallback& operator_name,
	DependentMemberTemplateHeader& out)
{
	int paren_depth = 0;
	int angle_depth = 0;
	int square_depth = 0;
	for (size_t p = declaration->decl_begin; p < declaration->decl_end; ++p)
	{
		const Token& tok = tokens[p];
		if (tok.kind != posttoken::TokenKind::Simple)
			continue;
		if (tok.type == OP_LBRACE &&
		    paren_depth == 0 &&
		    square_depth == 0)
			break;
		if (tok.type == OP_ARROW &&
		    paren_depth == 0 &&
		    angle_depth == 0 &&
		    square_depth == 0)
			break;
		if (tok.type == OP_LT)
		{
			++angle_depth;
			continue;
		}
		if (tok.type == OP_GT && angle_depth > 0)
		{
			--angle_depth;
			continue;
		}
		if (tok.type == OP_LSQUARE)
		{
			++square_depth;
			continue;
		}
		if (tok.type == OP_RSQUARE && square_depth > 0)
		{
			--square_depth;
			continue;
		}
		if (tok.type == OP_RPAREN && paren_depth > 0)
		{
			--paren_depth;
			continue;
		}
		if (tok.type != OP_LPAREN)
			continue;
		bool operator_less_name =
			p >= declaration->decl_begin + 2 &&
			tokens[p - 2].kind == posttoken::TokenKind::Simple &&
			tokens[p - 2].type == KW_OPERATOR &&
			tokens[p - 1].kind == posttoken::TokenKind::Simple &&
			tokens[p - 1].type == OP_LT;
		bool top_level_lparen =
			paren_depth == 0 &&
			square_depth == 0 &&
			(angle_depth == 0 ||
			 (angle_depth == 1 && operator_less_name));
		++paren_depth;
		if (!top_level_lparen || p == declaration->decl_begin)
			continue;
		size_t name_pos = p - 1;
		if (tokens[name_pos].kind == posttoken::TokenKind::Simple &&
		    tokens[name_pos].type == OP_GT)
		{
			int depth = 1;
			while (name_pos > declaration->decl_begin && depth > 0)
			{
				--name_pos;
				if (tokens[name_pos].kind != posttoken::TokenKind::Simple)
					continue;
				if (tokens[name_pos].type == OP_GT)
					++depth;
				else if (tokens[name_pos].type == OP_LT)
					--depth;
			}
			if (name_pos == declaration->decl_begin || depth != 0)
				continue;
			--name_pos;
		}
		string parsed_member_name;
		size_t before_name = name_pos;
		if (tokens[name_pos].kind == posttoken::TokenKind::Identifier)
		{
			parsed_member_name = tokens[name_pos].source;
			if (name_pos > declaration->decl_begin &&
			    tokens[name_pos - 1].kind == posttoken::TokenKind::Simple &&
			    tokens[name_pos - 1].type == OP_COMPL)
			{
				parsed_member_name = "~" + parsed_member_name;
				before_name = name_pos - 1;
			}
		}
		else if (p >= declaration->decl_begin + 3 &&
		         tokens[p - 3].kind == posttoken::TokenKind::Simple &&
		         tokens[p - 3].type == KW_OPERATOR &&
		         tokens[p - 2].kind == posttoken::TokenKind::Simple &&
		         tokens[p - 2].type == OP_LSQUARE &&
		         tokens[p - 1].kind == posttoken::TokenKind::Simple &&
		         tokens[p - 1].type == OP_RSQUARE)
		{
			before_name = p - 3;
			parsed_member_name = "operator[]";
		}
		else if (p >= declaration->decl_begin + 3 &&
		         tokens[p - 3].kind == posttoken::TokenKind::Simple &&
		         tokens[p - 3].type == KW_OPERATOR &&
		         tokens[p - 2].kind == posttoken::TokenKind::Simple &&
		         tokens[p - 2].type == OP_LPAREN &&
		         tokens[p - 1].kind == posttoken::TokenKind::Simple &&
		         tokens[p - 1].type == OP_RPAREN)
		{
			before_name = p - 3;
			parsed_member_name = "operator()";
		}
		else if (p >= declaration->decl_begin + 2 &&
		         tokens[p - 2].kind == posttoken::TokenKind::Simple &&
		         tokens[p - 2].type == KW_OPERATOR &&
		         tokens[p - 1].kind == posttoken::TokenKind::Simple)
		{
			before_name = p - 2;
			parsed_member_name = operator_name(tokens[p - 1].type,
			                                   tokens[p - 1].source);
		}
		else
			continue;
		if (before_name > declaration->decl_begin &&
		    tokens[before_name - 1].kind == posttoken::TokenKind::Simple &&
		    tokens[before_name - 1].type == KW_TEMPLATE)
			--before_name;
		if (before_name <= declaration->decl_begin ||
		    tokens[before_name - 1].kind != posttoken::TokenKind::Simple ||
		    tokens[before_name - 1].type != OP_COLON2)
			continue;
		out.call_lparen = p;
		out.member_name_pos = name_pos;
		out.member_name = parsed_member_name;
		out.member_colon = before_name - 1;
	}
	return out.call_lparen != declaration->decl_end &&
	       out.member_name_pos != declaration->decl_end &&
	       out.member_colon != declaration->decl_end &&
	       !out.member_name.empty();
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
}
string template_parameter_type_pattern_key(TypePtr type);
string template_instance_argument_pattern_key(
	const pa11::TemplateInstanceArgument& argument)
{
	if (argument.kind == pa11::TemplateInstanceArgumentKind::Type)
		return "T(" + template_parameter_type_pattern_key(argument.type) + ")";
	if (argument.kind == pa11::TemplateInstanceArgumentKind::Value)
	{
		ostringstream out;
		out << "V(" << template_parameter_type_pattern_key(argument.type)
		    << ",";
		if (argument.dependent)
			out << "?" << (argument.value_negated ? "!" : "")
			    << argument.value_name << ":"
			    << argument.value_owner_template_name << ":"
			    << argument.value_member_name;
		if (argument.dependent &&
		    argument.value_expr_end > argument.value_expr_begin &&
		    argument.value_owner_template_name.empty() &&
		    argument.value_member_name.empty() &&
		    argument.value_name.find("::") == string::npos)
			out << "@" << argument.value_expr_begin << ":"
			    << argument.value_expr_end;
		else if (!argument.dependent)
			out << argument.value;
		out << ")";
		return out.str();
	}
	if (argument.kind == pa11::TemplateInstanceArgumentKind::Template)
		return "M(" + argument.template_name + ")";
	string out = "P(";
	for (size_t i = 0; i < argument.pack.size(); ++i)
	{
		if (i != 0)
			out += ",";
		out += template_instance_argument_pattern_key(argument.pack[i]);
	}
	return out + ")";
}
string template_parameter_type_pattern_key(TypePtr type)
{
	if (type.get() == NULL)
		return "";
	TypePtr bare = pa11::strip_cv(type);
	string key = pa11::describe_type(type);
	if (bare->is_dependent_typename ||
	    (bare->kind == pa11::TypeKind::Record &&
	     bare->is_template_specialization))
	{
		key += "<" + bare->template_primary_name + ":";
		for (size_t i = 0; i < bare->template_arguments.size(); ++i)
		{
			if (i != 0)
				key += ",";
			key += template_instance_argument_pattern_key(
				bare->template_arguments[i]);
		}
		key += ">";
	}
	return key;
}
bool template_parameter_lists_match(const vector<TemplateParameterInfo>& left,
                                    const vector<TemplateParameterInfo>& right)
{
	if (left.size() != right.size())
		return false;
	for (size_t i = 0; i < left.size(); ++i)
	{
		if (left[i].kind != right[i].kind ||
		    left[i].is_pack != right[i].is_pack ||
		    left[i].template_parameters.size() !=
			    right[i].template_parameters.size())
			return false;
		if (left[i].kind == TemplateParameterKind::NonType &&
		    template_parameter_type_pattern_key(left[i].type) !=
			    template_parameter_type_pattern_key(right[i].type))
			return false;
		for (size_t j = 0; j < left[i].template_parameters.size(); ++j)
			if (left[i].template_parameters[j].kind !=
				    right[i].template_parameters[j].kind ||
			    left[i].template_parameters[j].is_pack !=
				    right[i].template_parameters[j].is_pack)
				return false;
	}
	return true;
}
bool same_placeholder_template_instance_type(TypePtr left, TypePtr right);
bool same_placeholder_template_instance_arguments(
	const vector<pa11::TemplateInstanceArgument>& left,
	const vector<pa11::TemplateInstanceArgument>& right);
bool same_placeholder_template_instance_argument(
	const pa11::TemplateInstanceArgument& left,
	const pa11::TemplateInstanceArgument& right)
{
	if (left.kind != right.kind)
		return false;
	if (left.kind == pa11::TemplateInstanceArgumentKind::Type)
		return same_placeholder_template_instance_type(left.type,
		                                               right.type);
	if (left.kind == pa11::TemplateInstanceArgumentKind::Value)
		return left.dependent == right.dependent &&
		       left.value_negated == right.value_negated &&
		       left.value == right.value &&
		       left.value_name == right.value_name &&
		       left.value_owner_template_name ==
			       right.value_owner_template_name &&
		       left.value_member_name == right.value_member_name &&
		       same_placeholder_template_instance_type(left.type,
		                                               right.type) &&
		       same_placeholder_template_instance_arguments(
			       left.value_owner_template_arguments,
			       right.value_owner_template_arguments);
	if (left.kind == pa11::TemplateInstanceArgumentKind::Template)
		return left.template_name == right.template_name &&
		       left.dependent == right.dependent;
	if (left.pack.size() != right.pack.size())
		return false;
	for (size_t i = 0; i < left.pack.size(); ++i)
		if (!same_placeholder_template_instance_argument(left.pack[i],
		                                                 right.pack[i]))
			return false;
	return true;
}
bool same_placeholder_template_instance_arguments(
	const vector<pa11::TemplateInstanceArgument>& left,
	const vector<pa11::TemplateInstanceArgument>& right)
{
	if (left.size() != right.size())
		return false;
	for (size_t i = 0; i < left.size(); ++i)
		if (!same_placeholder_template_instance_argument(left[i], right[i]))
			return false;
	return true;
}
bool same_placeholder_template_argument_lists(
	const vector<vector<pa11::TemplateInstanceArgument> >& left,
	const vector<vector<pa11::TemplateInstanceArgument> >& right)
{
	if (left.size() != right.size())
		return false;
	for (size_t i = 0; i < left.size(); ++i)
		if (!same_placeholder_template_instance_arguments(left[i], right[i]))
			return false;
	return true;
}
bool same_placeholder_template_instance_type(TypePtr left, TypePtr right)
{
	if (left.get() == NULL || right.get() == NULL)
		return left.get() == right.get();
	if (!pa11::same_type(left, right))
		return false;
	if (left->is_dependent_typename || right->is_dependent_typename)
	{
		if (left->is_dependent_typename != right->is_dependent_typename ||
		    left->dependent_typename_qualified !=
			    right->dependent_typename_qualified ||
		    left->dependent_typename_template_id !=
			    right->dependent_typename_template_id ||
		    left->dependent_typename_decltype !=
			    right->dependent_typename_decltype ||
		    left->template_primary_name != right->template_primary_name)
			return false;
	}
	if (!same_placeholder_template_instance_arguments(left->template_arguments,
	                                                 right->template_arguments))
		return false;
	if (!same_placeholder_template_argument_lists(
		    left->dependent_typename_template_argument_lists,
		    right->dependent_typename_template_argument_lists))
		return false;
	if (left->kind == pa11::TypeKind::Function)
	{
		if (!same_placeholder_template_instance_type(left->base, right->base) ||
		    left->parameters.size() != right->parameters.size())
			return false;
		for (size_t i = 0; i < left->parameters.size(); ++i)
			if (!same_placeholder_template_instance_type(left->parameters[i],
			                                            right->parameters[i]))
				return false;
	}
	else if (left->kind == pa11::TypeKind::Cv ||
	         left->kind == pa11::TypeKind::Pointer ||
	         left->kind == pa11::TypeKind::LValueReference ||
	         left->kind == pa11::TypeKind::RValueReference ||
	         left->kind == pa11::TypeKind::Array)
		return same_placeholder_template_instance_type(left->base,
		                                               right->base);
	else if (left->kind == pa11::TypeKind::MemberPointer)
		return same_placeholder_template_instance_type(left->member_class,
		                                               right->member_class) &&
		       same_placeholder_template_instance_type(left->base,
		                                               right->base);
	return true;
}
bool hard_template_registration_error(const string& message)
{
	return message == "template argument kind mismatch" ||
	       message == "template pack argument kind mismatch" ||
	       message == "missing template argument" ||
	       message == "type template argument pack required" ||
	       message == "value template argument pack required";
}
Binding* find_matching_function(Scope* scope,
                                const string& name,
                                TypePtr type)
{
	if (scope == NULL)
		return NULL;
	map<string, vector<Binding*> >::iterator it = scope->members.find(name);
	if (it == scope->members.end())
		return NULL;
	for (size_t i = 0; i < it->second.size(); ++i)
	{
		Binding* binding = it->second[i];
		if (binding->kind == BindingKind::Function &&
		    pa11::same_type(binding->type, type))
			return binding;
	}
	return NULL;
}
}  // namespace
void Parser::parse_explicit_template_instantiation(bool extern_declaration)
{ if (extern_declaration) expect(KW_EXTERN); expect(KW_TEMPLATE); if (starts_class_key()) { ++pos_; TypePtr type; if (!try_parse_type_name(type)) throw runtime_error("invalid explicit class instantiation");
complete_template_record(type); TypePtr bare = pa11::strip_cv(type); if (extern_declaration && bare->kind == pa11::TypeKind::Record) bare->is_extern_template_instantiation = true; if (bare->kind == pa11::TypeKind::Record && bare->scope != NULL) { if (!extern_declaration) { parse_pending_member_bodies(bare->scope);
parse_deferred_nested_member_bodies(bare->scope); instantiate_member_function_templates(type, true); } } expect(OP_SEMICOLON); return; } size_t constructor_save = pos_; try {
QualifiedName ctor_name = parse_id_expression_name(); if (ctor_name.qualifier == NULL || ctor_name.qualifier->kind != ScopeKind::Class || !constructor_name_matches_scope(ctor_name.qualifier, ctor_name.name))
throw runtime_error("not an explicit constructor instantiation"); expect(OP_LPAREN); vector<ParameterInfo> parameters; bool variadic = false; parse_parameter_clause(parameters, variadic); expect(OP_RPAREN);
Suffix suffix(SuffixKind::Function); parse_function_suffix_tail(suffix); TypePtr class_type = pa11::record_type_for_scope(ctor_name.qualifier); if (class_type.get() == NULL)
throw runtime_error("constructor without class type"); vector<TypePtr> fn_params; fn_params.push_back(pa11::make_pointer(class_type)); for (size_t i = 0; i < parameters.size(); ++i)
fn_params.push_back(parameters[i].type); TypePtr fn_type = pa11::make_function(pa11::make_fundamental(FT_VOID), fn_params, variadic); vector<Binding*> found = lookup_qualified_set(ctor_name.qualifier, ctor_name.name,
pa11::LOOKUP_FUNCTION); Binding* selected_ctor = NULL; for (size_t i = 0; i < found.size(); ++i) { Binding* candidate = found[i]; if (candidate->kind == BindingKind::Function &&
pa11::same_type(candidate->type, fn_type) && candidate->ref_qualifier == suffix.ref_qualifier) { selected_ctor = candidate; break; } } if (selected_ctor == NULL)
throw runtime_error("explicit constructor instantiation not found"); if (!extern_declaration) { parse_pending_function_body(selected_ctor); parse_pending_member_body(selected_ctor); selected_ctor->is_object_root = true;
if (selected_ctor->aliased_binding != NULL) { parse_pending_function_body(selected_ctor->aliased_binding); parse_pending_member_body(selected_ctor->aliased_binding); selected_ctor->aliased_binding->is_object_root = true;
} } expect(OP_SEMICOLON); return; } catch (const exception&) { pos_ = constructor_save; } DeclSpecs specs = parse_decl_specifier_seq(false); TypePtr base = type_from_decl_specs(specs);
Declarator declarator = parse_declarator(false); TypePtr declared_type = apply_declarator(declarator, base); const QualifiedName& qname = declarator_name(declarator);
if (qname.qualifier != NULL && qname.qualifier->kind == ScopeKind::Class) { if (declared_type->kind == pa11::TypeKind::Function) { const Suffix* suffix = declarator_function_suffix(declarator);
int ref_qualifier = suffix != NULL ? suffix->ref_qualifier : 0; vector<Binding*> found = lookup_qualified_set(qname.qualifier, qname.name, pa11::LOOKUP_FUNCTION); TypePtr target_type = declared_type;
bool constructor_instantiation = constructor_name_matches_scope(qname.qualifier, qname.name); if (constructor_instantiation) { TypePtr class_type = pa11::record_type_for_scope(qname.qualifier);
if (class_type.get() == NULL) throw runtime_error("constructor without class type"); vector<TypePtr> params; params.push_back(pa11::make_pointer(class_type)); for (size_t i = 0; i < declared_type->parameters.size(); ++i)
params.push_back(declared_type->parameters[i]); target_type = pa11::make_function(pa11::make_fundamental(FT_VOID), params, declared_type->variadic); } Binding* selected_member = NULL;
for (size_t i = 0; i < found.size(); ++i) { Binding* candidate = found[i]; if (candidate->kind == BindingKind::Function && pa11::same_type(candidate->type, target_type) && candidate->ref_qualifier == ref_qualifier) {
selected_member = candidate; break; } } if (selected_member == NULL && !constructor_instantiation) { TypePtr member_type = make_member_function_type(qname.qualifier, declared_type);
for (size_t i = 0; i < found.size(); ++i) { Binding* candidate = found[i]; if (candidate->kind == BindingKind::Function && pa11::same_type(candidate->type, member_type) && candidate->ref_qualifier == ref_qualifier) {
selected_member = candidate; break; } } } if (selected_member != NULL) { if (!extern_declaration) { parse_pending_function_body(selected_member); parse_pending_member_body(selected_member);
selected_member->is_object_root = true; if (selected_member->aliased_binding != NULL) { parse_pending_function_body( selected_member->aliased_binding); parse_pending_member_body( selected_member->aliased_binding);
selected_member->aliased_binding->is_object_root = true; } } expect(OP_SEMICOLON); return; } } else { vector<Binding*> found = lookup_qualified_set(qname.qualifier, qname.name, pa11::LOOKUP_VALUE);
for (size_t i = 0; i < found.size(); ++i) { Binding* candidate = found[i]; if (candidate->kind == BindingKind::Variable && pa11::same_type(candidate->type, declared_type)) { expect(OP_SEMICOLON); return; } }
throw runtime_error("explicit member instantiation not found"); } } if (declared_type->kind != pa11::TypeKind::Function) throw runtime_error("invalid explicit function instantiation");
if (qname.name.compare(0, 8, "operator") == 0) { bool overloaded_parameter = false; for (size_t i = 0; i < declared_type->parameters.size(); ++i) { TypePtr param =
pa11::strip_cv(expression_object_type(declared_type->parameters[i])); if (param->kind == pa11::TypeKind::Record || param->kind == pa11::TypeKind::Enum) overloaded_parameter = true; } if (!overloaded_parameter)
throw runtime_error("invalid overloaded operator instantiation"); } if (qname.qualifier != NULL && qname.qualifier->kind == ScopeKind::Class) { TypePtr qualifier_record = pa11::record_type_for_scope(qname.qualifier); if (qualifier_record.get() != NULL) { TypePtr bare_qualifier_record = pa11::strip_cv(qualifier_record); if (bare_qualifier_record->kind == pa11::TypeKind::Record) { complete_template_record(bare_qualifier_record); instantiate_member_function_templates(bare_qualifier_record); } } } vector<TemplateDeclaration*> declarations = find_function_templates(qname); TemplateDeclaration* selected = NULL;
vector<TemplateArgument> selected_args; TypePtr explicit_template_target_type = declared_type; TypePtr explicit_member_template_target_type; if (qname.qualifier != NULL && qname.qualifier->kind == ScopeKind::Class) explicit_member_template_target_type = make_member_function_type(qname.qualifier, declared_type);
auto target_type_for_declaration = [&](TemplateDeclaration* declaration) -> TypePtr { if (explicit_member_template_target_type.get() != NULL && declaration != NULL && declaration->generic_function_type.get() != NULL && declaration->generic_function_type->kind == pa11::TypeKind::Function && declaration->generic_function_type->parameters.size() == explicit_member_template_target_type->parameters.size()) return explicit_member_template_target_type; return explicit_template_target_type; };
auto substituted_function_type = [&](TemplateDeclaration* declaration, const vector<TemplateArgument>& full_args, TypePtr& out) -> bool { if (declaration == NULL ||
declaration->generic_function_type.get() == NULL || declaration->generic_function_type->kind != pa11::TypeKind::Function) return false; vector<map<string, TypePtr> > save_subst = template_type_substitutions_;
vector<map<string, TemplateArgument> > save_value_subst = template_value_substitutions_; vector<set<string> > save_pack_subst = template_type_parameter_packs_; map<string, TypePtr> subst;
map<string, TemplateArgument> value_subst; set<string> pack_subst; for (size_t ai = 0; ai < full_args.size() && ai < declaration->parameters.size(); ++ai) { const TemplateParameterInfo& parameter =
declaration->parameters[ai]; if (parameter.name.empty()) continue; if (parameter.kind == TemplateParameterKind::Type) { if (parameter.is_pack) { subst[parameter.name] = pa11::make_template_parameter_type(
parameter.name); value_subst[parameter.name] = full_args[ai]; pack_subst.insert(parameter.name); } else if (full_args[ai].kind == TemplateArgumentKind::Type) subst[parameter.name] = full_args[ai].type; } else
value_subst[parameter.name] = full_args[ai]; } template_type_substitutions_.insert( template_type_substitutions_.end(), declaration->outer_type_substitutions.begin(), declaration->outer_type_substitutions.end());
template_value_substitutions_.insert( template_value_substitutions_.end(), declaration->outer_value_substitutions.begin(), declaration->outer_value_substitutions.end()); template_type_substitutions_.push_back(subst);
template_value_substitutions_.push_back(value_subst); template_type_parameter_packs_.push_back(pack_subst); try { out = substitute_function_template_type( declaration, declaration->generic_function_type); }
catch (const runtime_error&) { template_type_substitutions_ = save_subst; template_value_substitutions_ = save_value_subst; template_type_parameter_packs_ = save_pack_subst; return false; }
template_type_substitutions_ = save_subst; template_value_substitutions_ = save_value_subst; template_type_parameter_packs_ = save_pack_subst; return out.get() != NULL && out->kind == pa11::TypeKind::Function; };
	TypePtr selected_target_type; for (size_t i = 0; i < declarations.size(); ++i) { TypePtr target_type = target_type_for_declaration(declarations[i]); vector<TemplateArgument> full_args; if (!deduce_function_template_target_type(declarations[i], target_type, qname.template_arguments, full_args)) continue;
		TypePtr candidate_type; if (!substituted_function_type(declarations[i], full_args, candidate_type) || (!pa11::same_type(candidate_type, target_type) && !same_template_signature_type(candidate_type, target_type))) continue; if (selected != NULL)
			{
				if (same_function_template_declaration_family(selected,
				                                              declarations[i]))
				{
					if (!selected->has_definition &&
					    declarations[i]->has_definition)
					{
						selected = declarations[i];
						selected_args = full_args;
						selected_target_type = target_type;
					}
					continue;
				}
				bool candidate_more_specialized =
					function_template_declaration_more_specialized(
						declarations[i],
						selected);
				bool selected_more_specialized =
					function_template_declaration_more_specialized(
						selected,
						declarations[i]);
				if (candidate_more_specialized && !selected_more_specialized)
				{
					selected = declarations[i];
					selected_args = full_args;
					selected_target_type = target_type;
					continue;
				}
				if (selected_more_specialized && !candidate_more_specialized)
					continue;
				throw runtime_error("ambiguous explicit function instantiation");
			}
			selected = declarations[i];
			selected_args = full_args;
			selected_target_type = target_type;
		}
		if (selected == NULL)
		{
			if (hosted_compatibility_ &&
			    hosted_library_namespace_scope(current_scope()))
			{
				expect(OP_SEMICOLON);
				return;
			}
			throw runtime_error("function template not found");
		}
string key = template_argument_key(selected_args); map<string, Binding*>::iterator existing_specialization = selected->function_specializations.find(key);
if (existing_specialization == selected->function_specializations.end()) for (size_t i = 0; i < declarations.size(); ++i) {
if (declarations[i] == selected || !same_function_template_declaration_family(selected, declarations[i])) continue;
map<string, Binding*>::iterator found_existing = declarations[i]->function_specializations.find(key);
if (found_existing == declarations[i]->function_specializations.end()) continue;
selected->function_specializations[key] = found_existing->second;
existing_specialization = selected->function_specializations.find(key);
break; }
	if (existing_specialization != selected->function_specializations.end()) { Binding* existing = existing_specialization->second; bool existing_has_body = function_bodies_.find(existing) != function_bodies_.end() || pending_function_bodies_.find(existing) != pending_function_bodies_.end(); if (function_template_placeholders_.find(existing) == function_template_placeholders_.end() || existing_has_body) { if (extern_declaration)
	existing->is_extern_template_instantiation = true; else
	existing->is_object_root = true; expect(OP_SEMICOLON); return; } } if (extern_declaration) { Binding* binding = add_function_binding(selected->owner, selected->name, selected_target_type.get() != NULL ? selected_target_type : declared_type, false);
	binding->language_linkage = current_language_linkage(); binding->is_object_root = true; binding->is_extern_template_instantiation = true; binding->function_specialization_symbol = abi_function_template_specialization_symbol(selected, selected_args, binding, &declaration_tokens_);
selected->function_specializations[key] = binding; function_template_placeholders_[binding] = selected;
function_template_specialization_arguments_[binding] = selected_args; } else { selected->function_specializations.erase(key); Binding* binding = instantiate_function_template(selected, selected_args);
parse_pending_function_body(binding); parse_pending_member_body(binding); binding->is_object_root = true; } expect(OP_SEMICOLON); }
TemplateDeclaration* Parser::register_template_declaration(
	const vector<TemplateParameterInfo>& parameters,
	size_t decl_begin,
	size_t decl_end)
{
	unique_ptr<TemplateDeclaration> holder(new TemplateDeclaration());
	holder->owner = current_scope();
	holder->lexical_scope = current_scope();
	holder->parameters = parameters;
	holder->decl_begin = decl_begin;
	holder->decl_end = decl_end;
	holder->outer_type_substitutions = template_type_substitutions_;
	holder->outer_value_substitutions = template_value_substitutions_;
	TemplateDeclaration* declaration = holder.get();
	template_declarations_.push_back(std::move(holder));
	size_t save = pos_;
	pos_ = decl_begin;
	if (current_scope()->kind == ScopeKind::Class && at(KW_FRIEND))
	{
		Scope* class_scope = current_scope();
		size_t friend_save = pos_;
		++pos_;
		if (starts_class_key())
		{
			ETokenType key = current().type;
			++pos_;
			QualifiedName name = parse_id_expression_name();
			if (at(OP_LT) && !name.has_template_arguments)
			{
				name.has_template_arguments = true;
				parse_template_argument_list(name.template_arguments);
			}
			Scope* target = name.qualifier != NULL
				? name.qualifier : nearest_namespace_scope(class_scope);
			TypePtr friend_type;
			if (name.has_template_arguments)
			{
				TemplateDeclaration* class_template =
					find_class_template(target, name.name);
				if (class_template != NULL)
					friend_type = instantiate_class_template(
						class_template,
						name.template_arguments);
			}
			if (friend_type.get() == NULL)
			{
				vector<Binding*> found =
					lookup_qualified_set(target,
					                     name.name,
					                     pa11::LOOKUP_TYPE);
				if (!found.empty() &&
				    found[0]->type.get() != NULL &&
				    pa11::strip_cv(found[0]->type)->kind ==
				    pa11::TypeKind::Record)
					friend_type = found[0]->type;
			}
			if (friend_type.get() == NULL)
				friend_type = add_record(target,
				                         name.name,
				                         class_tag(key),
				                         false,
				                         NULL);
			add_friend_class(class_scope, friend_type);
			declaration->kind = TemplateDeclarationKind::Class;
			declaration->owner = target;
			declaration->name = name.name;
			expect(OP_SEMICOLON);
			pos_ = save;
			return declaration;
		}
		pos_ = friend_save;
	}
	if (starts_class_key())
		register_class_template(declaration);
	else if (at(KW_USING))
		register_alias_template(declaration);
	else
		register_function_template(declaration);
	pos_ = save;
	return declaration;
}
void Parser::register_alias_template(TemplateDeclaration* declaration)
{
	declaration->kind = TemplateDeclarationKind::Alias;
	expect(KW_USING);
	if (!at_identifier())
		throw runtime_error("expected alias template name");
	declaration->name = consume_identifier();
	declaration->has_definition = true;
	skip_attributes();
	expect(OP_ASS);
	declaration->owner = current_scope();
	TemplateDeclaration*& slot =
		alias_templates_[declaration->owner][declaration->name];
	if (slot == NULL)
		slot = declaration;
	else
	{
		merge_template_defaults(slot->parameters, declaration->parameters);
		slot->lexical_scope = declaration->lexical_scope;
		slot->decl_begin = declaration->decl_begin;
		slot->decl_end = declaration->decl_end;
		slot->has_definition = true;
	}
}
void Parser::register_class_template(TemplateDeclaration* declaration)
{ declaration->kind = TemplateDeclarationKind::Class; map<string, TypePtr> parameter_types; map<string, TemplateArgument> parameter_values; collect_template_parameter_placeholders(declaration->parameters,
parameter_types, parameter_values); vector<map<string, TypePtr> > save_subst = template_type_substitutions_; vector<map<string, TemplateArgument> > save_value_subst = template_value_substitutions_;
vector<set<string> > save_pack_subst = template_type_parameter_packs_; template_type_substitutions_.push_back(parameter_types); template_value_substitutions_.push_back(parameter_values);
template_type_parameter_packs_.push_back( collect_template_type_parameter_packs(declaration->parameters)); ETokenType key = current().type; declaration->tag = class_tag(key); ++pos_; while (consume(KW_ALIGNAS))
skip_balanced(OP_LPAREN, OP_RPAREN); Scope* owner = current_scope(); bool template_id_qualifier = false; if (at_identifier() && lookahead(OP_LT, 1)) { size_t p = pos_ + 1; int depth = 0; while (p < tokens_.size()) {
if (tokens_[p].kind == posttoken::TokenKind::Simple && tokens_[p].type == OP_LT) ++depth; else if (tokens_[p].kind == posttoken::TokenKind::Simple && tokens_[p].type == OP_GT) { --depth; if (depth == 0) {
template_id_qualifier = p + 1 < tokens_.size() && tokens_[p + 1].kind == posttoken::TokenKind::Simple && tokens_[p + 1].type == OP_COLON2; break; } } ++p; } } if (at(OP_COLON2) || (at_identifier() &&
(lookahead(OP_COLON2, 1) || template_id_qualifier))) owner = parse_nested_name_specifier(NULL); if (!at_identifier()) throw runtime_error("expected class template name"); declaration->owner = owner;
			declaration->name = consume_identifier(); bool hosted_library_template = hosted_compatibility_ && hosted_library_namespace_scope(owner); if (owner != NULL && owner->kind == ScopeKind::Class) declaration->lexical_scope = owner; if (at(OP_LT)) { vector<TemplateArgument> pattern;
parse_template_argument_list(pattern); declaration->class_specialization = true; declaration->class_specialization_pattern = pattern; declaration->has_definition = has_token(tokens_, pos_,
declaration->decl_end, OP_LBRACE); TemplateDeclaration* primary = find_class_template(owner, declaration->name); if (primary == NULL) { if (owner == NULL) owner = current_scope(); unique_ptr<TemplateDeclaration> holder( new TemplateDeclaration()); primary = holder.get(); primary->kind = TemplateDeclarationKind::Class; primary->owner = owner;
primary->lexical_scope = owner; primary->name = declaration->name; primary->tag = declaration->tag; primary->parameters = declaration->parameters; class_templates_[owner][declaration->name] = primary;
template_declarations_.push_back(std::move(holder)); } string pattern_key = template_argument_key(pattern); if (declaration->parameters.empty()) { vector<TemplateArgument> full_args =
complete_template_arguments(primary, pattern); string owner_key; TypePtr owner_record = pa11::record_type_for_scope(primary->owner); owner_record = owner_record.get() != NULL ? pa11::strip_cv(owner_record) : TypePtr();
map<const void*, vector<TemplateArgument> >::const_iterator owner_args = owner_record.get() != NULL ? record_template_arguments_.find(owner_record.get()) : record_template_arguments_.end();
if (owner_args != record_template_arguments_.end()) owner_key = template_argument_key(owner_args->second); string instantiation_key = template_argument_key(full_args); if (!owner_key.empty())
instantiation_key = owner_key + "::" + primary->name + "<" + instantiation_key + ">"; map<string, TypePtr>::iterator instantiated = primary->class_specializations.find(instantiation_key);
if (instantiated != primary->class_specializations.end()) { TypePtr existing_record = pa11::strip_cv(instantiated->second); map<const void*, TemplateDeclaration*>::iterator existing_declaration =
record_template_declarations_.find( existing_record.get()); bool existing_explicit_specialization = existing_declaration != record_template_declarations_.end() && existing_declaration->second != NULL &&
existing_declaration->second->class_specialization; bool demanded_instantiation = demanded_class_template_specializations_.count( existing_record.get()) != 0; if (!existing_explicit_specialization &&
candidate_only_class_template_specializations_.count( existing_record.get()) == 0 && demanded_instantiation) throw runtime_error( "explicit specialization after instantiation"); } } for (size_t i = 0;
i < primary->class_specialization_declarations.size(); ++i) { TemplateDeclaration* existing = primary->class_specialization_declarations[i]; if (template_argument_key( existing->class_specialization_pattern) !=
pattern_key) continue; if (declaration->has_definition) primary->class_specialization_declarations[i] = declaration; template_type_substitutions_ = save_subst; template_value_substitutions_ = save_value_subst;
	template_type_parameter_packs_ = save_pack_subst; if (declaration->has_definition && active_class_instantiations_.empty() && !validating_template_definition_ && !hosted_library_template) { try { validate_class_template_definition(declaration); }
catch (const runtime_error& err) { string message = err.what(); if (message != "dependent typename not resolved" && message != "too many template arguments") throw; } } return; } primary->class_specialization_declarations.push_back(declaration);
template_type_substitutions_ = save_subst; template_value_substitutions_ = save_value_subst; template_type_parameter_packs_ = save_pack_subst; if (declaration->has_definition && active_class_instantiations_.empty() &&
	!validating_template_definition_ && !hosted_library_template) { try { validate_class_template_definition(declaration); } catch (const runtime_error& err) { string message = err.what(); if (message != "dependent typename not resolved" && message != "too many template arguments") throw; } } return; }
declaration->has_definition = has_token(tokens_, pos_, declaration->decl_end, OP_LBRACE); TemplateDeclaration*& slot = class_templates_[owner][declaration->name];
TypePtr owner_record = pa11::record_type_for_scope(owner); if (owner_record.get() != NULL) { map<const void*, TemplateDeclaration*>::iterator outer = record_template_declarations_.find(
pa11::strip_cv(owner_record).get()); if (outer != record_template_declarations_.end()) { pair<TemplateDeclaration*, string> key = make_pair(outer->second, declaration->name); map<pair<TemplateDeclaration*, string>,
TemplateDeclaration*>::iterator existing = member_class_templates_.find(key); if (existing != member_class_templates_.end() && existing->second != declaration) declaration->class_specialization_declarations.insert(
declaration->class_specialization_declarations.end(), existing->second->class_specialization_declarations.begin(), existing->second->class_specialization_declarations.end());
for (map<Scope*, map<string, TemplateDeclaration*> >::iterator sit = class_templates_.begin(); sit != class_templates_.end(); ++sit) { map<string, TemplateDeclaration*>::iterator it = sit->second.find(declaration->name);
if (it == sit->second.end() || it->second == NULL || it->second == declaration || it->second->owner == NULL || it->second->class_specialization_declarations.empty()) continue; TypePtr candidate_owner =
pa11::record_type_for_scope(it->second->owner); candidate_owner = candidate_owner.get() != NULL ? pa11::strip_cv(candidate_owner) : TypePtr(); string owner_template_name = !owner_record->template_primary_name.empty()
? owner_record->template_primary_name : owner_record->name; if (candidate_owner.get() != NULL && candidate_owner->kind == pa11::TypeKind::Record && !owner_template_name.empty() &&
candidate_owner->name != owner_template_name) continue; declaration->class_specialization_declarations.insert( declaration->class_specialization_declarations.end(), it->second->class_specialization_declarations.begin(),
it->second->class_specialization_declarations.end()); } if (existing == member_class_templates_.end() || declaration->has_definition || existing->second == NULL || !existing->second->has_definition)
member_class_templates_[key] = declaration; } } if (slot == NULL) { slot = declaration; } else { if (declaration->has_definition) { vector<TemplateParameterInfo> merged_parameters = declaration->parameters;
if (merged_parameters.size() < slot->parameters.size()) merged_parameters.resize(slot->parameters.size()); for (size_t i = 0; i < slot->parameters.size(); ++i) if (slot->parameters[i].has_default &&
!merged_parameters[i].has_default) { merged_parameters[i].has_default = true; merged_parameters[i].default_begin = slot->parameters[i].default_begin; merged_parameters[i].default_end = slot->parameters[i].default_end; }
slot->parameters = merged_parameters; slot->lexical_scope = declaration->lexical_scope; slot->decl_begin = declaration->decl_begin; slot->decl_end = declaration->decl_end; slot->tag = declaration->tag;
slot->has_definition = true; slot->class_definition_validated = false; } else merge_template_defaults(slot->parameters, declaration->parameters); } template_type_substitutions_ = save_subst; template_value_substitutions_ = save_value_subst;
	template_type_parameter_packs_ = save_pack_subst; if (declaration->has_definition) { if (active_class_instantiations_.empty() && !validating_template_definition_ && !hosted_library_template) { try { validate_class_template_definition(declaration);
} catch (const runtime_error& err) { string message = err.what(); if (message != "dependent typename not resolved" && message != "too many template arguments") throw; } } if (slot != declaration && class_templates_with_dependent_base_.count(declaration) != 0)
class_templates_with_dependent_base_.insert(slot); } }
void Parser::register_explicit_function_template_specialization(
	TemplateDeclaration* declaration,
	const QualifiedName& qname,
	TypePtr declared_type,
	size_t save_pos,
	const vector<map<string, TypePtr> >& save_subst,
	const vector<map<string, TemplateArgument> >& save_value_subst)
{
	vector<TemplateDeclaration*> primaries = find_function_templates(qname);
	if (primaries.empty())
		throw runtime_error("function template specialization without primary");
	TemplateDeclaration* primary = primaries[0];
	vector<TemplateArgument> full_args;
	if (!deduce_function_template_target_type(primary,
	                                          declared_type,
	                                          qname.template_arguments,
	                                          full_args))
		throw runtime_error("function template specialization mismatch");
	string key = template_argument_key(full_args);
	template_type_substitutions_ = save_subst;
	template_value_substitutions_ = save_value_subst;
	pos_ = declaration->decl_begin;
	bool save_force = force_new_function_binding_;
	bool save_override = override_function_parameter_names_;
	vector<string> save_override_names = function_parameter_name_override_;
	map<Binding*, vector<string> >::iterator primary_names =
		function_parameter_names_.find(primary->placeholder);
	force_new_function_binding_ = true;
	if (primary_names != function_parameter_names_.end())
	{
		override_function_parameter_names_ = true;
		function_parameter_name_override_ = primary_names->second;
	}
	Node node;
	try
	{
		parse_simple_or_function_declaration(node, true);
	}
	catch (...)
	{
		force_new_function_binding_ = save_force;
		override_function_parameter_names_ = save_override;
		function_parameter_name_override_ = save_override_names;
		pos_ = save_pos;
		throw;
	}
	force_new_function_binding_ = save_force;
	override_function_parameter_names_ = save_override;
	function_parameter_name_override_ = save_override_names;
	if (node.line.compare(0, 19, "function-definition") == 0 &&
	    node.binding != NULL)
	{
		primary->function_specializations[key] = node.binding;
		function_template_specialization_arguments_[node.binding] =
			full_args;
		add_child(root_, node);
	}
	else if (!node.children.empty() && node.children.back().binding != NULL)
	{
		primary->function_specializations[key] =
			node.children.back().binding;
		function_template_specialization_arguments_[
			node.children.back().binding] = full_args;
		add_child(root_, node.children.back());
	}
	else
		throw runtime_error("function template specialization failed");
	pos_ = save_pos;
}
void Parser::register_function_template(TemplateDeclaration* declaration)
{ bool could_conversion_template = at(KW_OPERATOR) || at(KW_EXPLICIT) || at(KW_CONSTEXPR) || starts_attribute(); bool could_constructor_template = at_identifier() || at(OP_COLON2) || at(KW_EXPLICIT) || at(KW_CONSTEXPR) || starts_attribute(); if (could_conversion_template && register_conversion_function_template(declaration)) return; if (could_constructor_template && register_constructor_template(declaration)) return; declaration->kind = TemplateDeclarationKind::Function; map<string, TypePtr> parameter_types;
map<string, TemplateArgument> parameter_values; collect_template_parameter_placeholders(declaration->parameters, parameter_types, parameter_values); size_t save_pos = pos_;
vector<map<string, TypePtr> > save_subst = template_type_substitutions_; vector<map<string, TemplateArgument> > save_value_subst = template_value_substitutions_;
vector<set<string> > save_pack_subst = template_type_parameter_packs_; template_type_substitutions_.push_back(parameter_types); template_value_substitutions_.push_back(parameter_values);
template_type_parameter_packs_.push_back( collect_template_type_parameter_packs(declaration->parameters)); pos_ = declaration->decl_begin; if (at(KW_TEMPLATE)) { expect(KW_TEMPLATE);
vector<TemplateParameterInfo> nested_parameters = parse_template_parameter_clause(); unique_ptr<TemplateDeclaration> nested_holder( new TemplateDeclaration()); nested_holder->owner = current_scope();
nested_holder->lexical_scope = current_scope(); nested_holder->parameters = nested_parameters; nested_holder->decl_begin = pos_; nested_holder->decl_end = declaration->decl_end; nested_holder->outer_type_substitutions =
template_type_substitutions_; nested_holder->outer_value_substitutions = template_value_substitutions_; TemplateDeclaration* nested = nested_holder.get(); template_declarations_.push_back(std::move(nested_holder));
if (starts_class_key()) register_class_template(nested); else if (at(KW_USING)) register_alias_template(nested); else register_function_template(nested); template_type_substitutions_ = save_subst;
template_value_substitutions_ = save_value_subst; template_type_parameter_packs_ = save_pack_subst; pos_ = save_pos; return; } if (!declaration->parameters.empty() && register_dependent_qualified_member_function_template(declaration)) { template_type_substitutions_ = save_subst; template_value_substitutions_ = save_value_subst; template_type_parameter_packs_ = save_pack_subst; pos_ = save_pos; return; } try { DeclSpecs specs = parse_decl_specifier_seq(false);
TypePtr base = type_from_decl_specs(specs); Declarator declarator = parse_declarator(false); TypePtr type = apply_declarator(declarator, base); if (type->kind != pa11::TypeKind::Function) {
const QualifiedName& qname = declarator_name(declarator); if (qname.qualifier != NULL && at(OP_LPAREN) && has_token(tokens_, pos_, declaration->decl_end, OP_LBRACE)) { TypePtr owner_record =
pa11::record_type_for_scope(qname.qualifier); owner_record = owner_record.get() != NULL ? pa11::strip_cv(owner_record) : TypePtr(); map<const void*, TemplateDeclaration*>::iterator outer = owner_record.get() != NULL
? record_template_declarations_.find( owner_record.get()) : record_template_declarations_.end(); TemplateDeclaration* owner_template = outer != record_template_declarations_.end() ? outer->second
: find_class_template(qname.qualifier->parent, qname.qualifier->name); if (owner_template != NULL) { declaration->kind = TemplateDeclarationKind::Function; declaration->owner = qname.qualifier;
declaration->name = qname.name; declaration->class_template_member = template_parameter_lists_match( declaration->parameters, owner_template->parameters) || !declaration->outer_type_substitutions.empty(); declaration->generic_function_type = pa11::make_function(
pa11::make_fundamental(FT_VOID), vector<TypePtr>(), false); declaration->has_definition = true; vector<TemplateDeclaration*>& members = member_function_templates_[make_pair( owner_template, qname.name)];
add_member_function_template(members, declaration); template_type_substitutions_ = save_subst; template_value_substitutions_ = save_value_subst;
template_type_parameter_packs_ = save_pack_subst; pos_ = save_pos; return; } } Scope* target = qname.qualifier != NULL ? qname.qualifier : declaration->owner; declaration->owner = target; declaration->name = qname.name;
if (qname.has_template_arguments) { declaration->class_specialization = true; declaration->class_specialization_pattern = qname.template_arguments; } template_type_substitutions_ = save_subst;
template_value_substitutions_ = save_value_subst; template_type_parameter_packs_ = save_pack_subst; pos_ = save_pos; if (declaration->parameters.empty() && target->kind == ScopeKind::Class && qname.qualifier != NULL) {
vector<Binding*> found = lookup_qualified_set(target, qname.name, pa11::LOOKUP_VALUE); Binding* member = NULL; for (size_t i = 0; i < found.size(); ++i) { Binding* candidate = found[i];
if (candidate->kind == BindingKind::Variable && pa11::same_type(candidate->type, type)) { member = candidate; break; } } if (member != NULL) { pos_ = declaration->decl_begin; Node node;
parse_simple_or_function_declaration(node, true); member->is_template_static_member_definition = false; if (node.line.empty()) { for (size_t i = 0; i < node.children.size(); ++i) add_child(root_, node.children[i]); }
else add_child(root_, node); TypePtr owner_record = pa11::record_type_for_scope(target); owner_record = owner_record.get() != NULL ? pa11::strip_cv(owner_record) : TypePtr();
map<const void*, TemplateDeclaration*>::iterator outer = owner_record.get() != NULL ? record_template_declarations_.find( owner_record.get()) : record_template_declarations_.end();
map<const void*, vector<TemplateArgument> >::iterator owner_args = owner_record.get() != NULL ? record_template_arguments_.find(owner_record.get()) : record_template_arguments_.end();
if (outer != record_template_declarations_.end() && owner_args != record_template_arguments_.end()) { string key = template_argument_key(owner_args->second) + "::" + qname.name; map<pair<TemplateDeclaration*, string>,
vector<TemplateDeclaration*> >::iterator templates = member_variable_templates_.find( make_pair(outer->second, qname.name)); if (templates != member_variable_templates_.end()) for (size_t i = 0;
i < templates->second.size(); ++i) templates->second[i]-> emitted_variable_specializations.insert( key); } pos_ = save_pos; return; } } if (register_static_member_variable_template(declaration)) return;
declaration->kind = TemplateDeclarationKind::Variable; vector<TemplateDeclaration*>& variable_family = variable_templates_[target][qname.name]; if (declaration->class_specialization)
for (size_t i = 0; i < variable_family.size(); ++i) if (!variable_family[i]->class_specialization) variable_template_specializations_.erase( variable_family[i]); variable_family.push_back(declaration); return; }
const QualifiedName& qname = declarator_name(declarator); Scope* friend_class_scope = specs.friend_decl && declaration->owner != NULL && declaration->owner->kind == ScopeKind::Class ? declaration->owner : NULL;
Scope* target = qname.qualifier != NULL ? qname.qualifier : (friend_class_scope != NULL ? nearest_namespace_scope(friend_class_scope) : declaration->owner); if (declaration->parameters.empty()) {
if (target->kind == ScopeKind::Class && qname.qualifier != NULL) { Binding* member = find_matching_function(target, qname.name, type); if (member == NULL) { TypePtr member_type = make_member_function_type(target, type);
member = find_matching_function(target, qname.name, member_type); } if (member != NULL && function_template_placeholders_.find(member) == function_template_placeholders_.end()) {
template_type_substitutions_ = save_subst; template_value_substitutions_ = save_value_subst; template_type_parameter_packs_ = save_pack_subst; pos_ = declaration->decl_begin;
bool save_force = force_new_function_binding_; force_new_function_binding_ = false; Node node; try { parse_simple_or_function_declaration(node, true); } catch (...) { force_new_function_binding_ = save_force;
pos_ = save_pos; throw; } force_new_function_binding_ = save_force; if (node.line.compare(0, 19, "function-definition") == 0) add_child(root_, node); else if (!node.children.empty())
add_child(root_, node.children.back()); pos_ = save_pos; return; } } template_type_parameter_packs_ = save_pack_subst;
register_explicit_function_template_specialization(declaration, qname, type, save_pos, save_subst, save_value_subst); return; } declaration->owner = target; declaration->friend_class_scope = friend_class_scope;
declaration->hidden_friend = friend_class_scope != NULL && qname.qualifier == NULL; declaration->name = qname.name; Binding* placeholder = NULL; bool static_member_definition = false;
if (target->kind == ScopeKind::Class && qname.qualifier != NULL) { placeholder = find_matching_function_template_placeholder( function_template_placeholders_, target, qname.name, type, declaration->parameters);
static_member_definition = placeholder != NULL && placeholder->is_static_member; } if (target->kind == ScopeKind::Class && !specs.static_decl && !static_member_definition) type = make_member_function_type(target, type);
declaration->generic_function_type = type; declaration->has_definition = has_token(tokens_, pos_, declaration->decl_end, OP_LBRACE); if (placeholder == NULL) placeholder = find_matching_function_template_placeholder(
function_template_placeholders_, target, qname.name, type, declaration->parameters); TemplateDeclaration* previous_declaration = NULL; if (placeholder != NULL) { map<Binding*, TemplateDeclaration*>::iterator previous =
function_template_placeholders_.find(placeholder); if (previous != function_template_placeholders_.end()) previous_declaration = previous->second; } if (placeholder != NULL && previous_declaration != NULL &&
previous_declaration->has_definition && declaration->has_definition && !same_placeholder_template_instance_type( previous_declaration->generic_function_type, type)) { placeholder = NULL; previous_declaration = NULL; }
if (placeholder == NULL) { placeholder = add_value(target, BindingKind::Function, qname.name, type); placeholder->is_hidden_friend = declaration->hidden_friend; } else if (!declaration->hidden_friend)
placeholder->is_hidden_friend = false; placeholder->is_static_member = target->kind == ScopeKind::Class && (specs.static_decl || static_member_definition); declaration->placeholder = placeholder;
const Suffix* primary_suffix = declarator_function_suffix(declarator); placeholder->is_constexpr = placeholder->is_constexpr || specs.constexpr_decl; placeholder->is_declared_inline = placeholder->is_declared_inline || specs.inline_decl || specs.constexpr_decl; placeholder->is_private = target->kind == ScopeKind::Class && !class_private_access_.empty() && class_private_access_.back(); placeholder->is_protected_member = target->kind == ScopeKind::Class && !class_protected_access_.empty() && class_protected_access_.back(); if (primary_suffix != NULL) { placeholder->unwind_no = primary_suffix->noexcept_decl; placeholder->dynamic_exception_spec = primary_suffix->dynamic_exception_spec; placeholder->dynamic_exception_types = primary_suffix->dynamic_exception_types; placeholder->ref_qualifier = primary_suffix->ref_qualifier; } if (primary_suffix != NULL) { vector<string> names; vector<Expr> defaults; if (target->kind == ScopeKind::Class && !placeholder->is_static_member)
defaults.push_back(Expr()); for (size_t i = 0; i < primary_suffix->parameters.size(); ++i) { if (primary_suffix->parameters[i].type.get() != NULL || !primary_suffix->parameters[i].name.empty())
	names.push_back(primary_suffix->parameters[i].name); defaults.push_back( primary_suffix->parameters[i].default_value); } map<Binding*, vector<string> >::const_iterator old_names =
	function_parameter_names_.find(placeholder); if (old_names != function_parameter_names_.end()) { vector<string> merged = old_names->second; size_t offset = placeholder->owner != NULL &&
placeholder->owner->kind == ScopeKind::Class && !placeholder->is_static_member && merged.size() == names.size() + 1 ? 1 : 0; if (merged.size() < names.size() + offset) merged.resize(names.size() + offset);
for (size_t i = 0; i < names.size(); ++i) if (!names[i].empty() || merged[i + offset].empty()) merged[i + offset] = names[i]; names = merged; } else if (target->kind == ScopeKind::Class && qname.qualifier != NULL) {
vector<Binding*> existing_functions = lookup_qualified_set(target, qname.name, pa11::LOOKUP_FUNCTION); for (size_t fi = 0; fi < existing_functions.size(); ++fi) { map<Binding*, vector<string> >::const_iterator
existing_names = function_parameter_names_.find( existing_functions[fi]); if (existing_names == function_parameter_names_.end() || existing_names->second.size() != names.size()) continue;
for (size_t ni = 0; ni < names.size(); ++ni) if (names[ni].empty()) names[ni] = existing_names->second[ni]; break; } } function_parameter_names_[placeholder] = names; placeholder->function_parameter_names = names; declaration->function_parameter_names = names;
map<Binding*, vector<Expr> >::const_iterator old_defaults = default_arguments_.find(placeholder); if (old_defaults != default_arguments_.end()) { vector<Expr> merged = defaults;
if (merged.size() < old_defaults->second.size()) merged.resize(old_defaults->second.size()); for (size_t i = 0; i < old_defaults->second.size(); ++i) if (!merged[i].valid && old_defaults->second[i].valid)
merged[i] = old_defaults->second[i]; defaults = merged; } default_arguments_[placeholder] = defaults; } if (previous_declaration != NULL) merge_template_defaults(declaration->parameters,
previous_declaration->parameters); function_template_placeholders_[placeholder] = declaration; if (friend_class_scope != NULL) add_friend_function(friend_class_scope, placeholder);
vector<TemplateDeclaration*>& overloads = function_templates_[target][qname.name]; if (find(overloads.begin(), overloads.end(), declaration) == overloads.end()) overloads.push_back(declaration);
TypePtr owner_record = pa11::record_type_for_scope(target); if (owner_record.get() != NULL) { map<const void*, TemplateDeclaration*>::iterator outer =
record_template_declarations_.find(pa11::strip_cv(owner_record).get()); TemplateDeclaration* owner_template = outer != record_template_declarations_.end() ? outer->second
: find_class_template(target->parent, target->name); if (qname.qualifier != NULL && owner_template != NULL && (template_parameter_lists_match(declaration->parameters, owner_template->parameters) || !declaration->outer_type_substitutions.empty()))
declaration->class_template_member = true; if (owner_template != NULL) { vector<TemplateDeclaration*>& members = member_function_templates_[make_pair(owner_template, qname.name)];
add_member_function_template(members, declaration); } } } catch (const exception& err) { string message = err.what(); bool hard_registration_error =
hard_template_registration_error(message); template_type_substitutions_ = save_subst; template_value_substitutions_ = save_value_subst; template_type_parameter_packs_ = save_pack_subst; pos_ = save_pos;
if (could_constructor_template && register_constructor_template(declaration)) return; if (register_dependent_nested_constructor_template(declaration)) return; if (register_dependent_qualified_conversion_function_template( declaration)) return;
if (register_dependent_qualified_member_function_template( declaration)) return; if (register_static_member_variable_template(declaration)) return; if (hard_registration_error) throw;
declaration->kind = TemplateDeclarationKind::Variable; } template_type_substitutions_ = save_subst; template_value_substitutions_ = save_value_subst; template_type_parameter_packs_ = save_pack_subst; pos_ = save_pos; }
bool Parser::register_dependent_qualified_member_function_template(
	TemplateDeclaration* declaration)
{
	if (!has_token(tokens_,
	               declaration->decl_begin,
	               declaration->decl_end,
	               OP_LBRACE))
		return false;
	DependentMemberTemplateHeader header;
	init_dependent_member_template_header(header, declaration->decl_end);
	OperatorNameCallback operator_name =
		[this](ETokenType type, const string& source) {
			return operator_function_name(type, source);
		};
	if (!find_dependent_member_template_header(tokens_,
	                                           declaration,
	                                           operator_name,
	                                           header))
		return false;
	size_t call_lparen = header.call_lparen;
	string member_name = header.member_name;
	size_t member_colon = header.member_colon;
	TemplateDeclaration* owner_template = NULL;
size_t owner_template_args_pos = declaration->decl_end; for (size_t p = declaration->decl_begin; p < member_colon; ++p) { if (tokens_[p].kind != posttoken::TokenKind::Identifier) continue; if (p + 1 >= member_colon ||
tokens_[p + 1].kind != posttoken::TokenKind::Simple || tokens_[p + 1].type != OP_LT) continue; size_t after_args = p + 1; if (!skip_template_id_argument_tokens(tokens_, after_args)) continue;
if (after_args > member_colon || tokens_[after_args].kind != posttoken::TokenKind::Simple || tokens_[after_args].type != OP_COLON2) continue; TemplateDeclaration* templ = find_class_template(NULL, tokens_[p].source);
if (templ != NULL) { owner_template = templ; owner_template_args_pos = p + 1; } } if (owner_template == NULL) return false; if (owner_template_args_pos != declaration->decl_end) { size_t save_pos = pos_;
vector<map<string, TypePtr> > save_subst = template_type_substitutions_; vector<map<string, TemplateArgument> > save_value_subst = template_value_substitutions_; vector<set<string> > save_pack_subst =
template_type_parameter_packs_; map<string, TypePtr> parameter_types; map<string, TemplateArgument> parameter_values; collect_template_parameter_placeholders(declaration->parameters, parameter_types, parameter_values);
template_type_substitutions_.insert( template_type_substitutions_.end(), declaration->outer_type_substitutions.begin(), declaration->outer_type_substitutions.end()); template_value_substitutions_.insert(
template_value_substitutions_.end(), declaration->outer_value_substitutions.begin(), declaration->outer_value_substitutions.end()); template_type_substitutions_.push_back(parameter_types);
template_value_substitutions_.push_back(parameter_values); template_type_parameter_packs_.push_back( collect_template_type_parameter_packs(declaration->parameters)); pos_ = owner_template_args_pos;
vector<TemplateArgument> owner_pattern_args; try { parse_template_argument_list(owner_pattern_args); } catch (const exception&) { pos_ = save_pos; template_type_substitutions_ = save_subst;
template_value_substitutions_ = save_value_subst; template_type_parameter_packs_ = save_pack_subst; return false; } pos_ = save_pos; template_type_substitutions_ = save_subst;
	template_value_substitutions_ = save_value_subst; template_type_parameter_packs_ = save_pack_subst; if (!owner_pattern_is_primary_parameter_list(owner_pattern_args, owner_template->parameters)) {
	declaration->class_specialization = true; declaration->class_specialization_pattern = owner_pattern_args; } map<string, TypePtr> owner_name_subst; for (size_t i = 0; i < owner_pattern_args.size() &&
i < owner_template->parameters.size(); ++i) { const TemplateParameterInfo& parameter = owner_template->parameters[i]; if (parameter.kind != TemplateParameterKind::Type || parameter.name.empty() ||
owner_pattern_args[i].kind != TemplateArgumentKind::Type) continue; TypePtr arg_type = pa11::strip_cv(owner_pattern_args[i].type); if (arg_type.get() != NULL && arg_type->kind == pa11::TypeKind::TemplateParameter &&
arg_type->name != parameter.name) owner_name_subst[arg_type->name] = pa11::make_template_parameter_type(parameter.name); } if (!owner_name_subst.empty()) declaration->outer_type_substitutions.push_back(
owner_name_subst); } declaration->kind = TemplateDeclarationKind::Function; declaration->owner = owner_template->owner; declaration->name = member_name; declaration->class_template_member =
template_parameter_lists_match(declaration->parameters, owner_template->parameters) || owner_template_args_pos != declaration->decl_end || !declaration->outer_type_substitutions.empty(); declaration->generic_function_type = pa11::make_function(pa11::make_fundamental(FT_VOID), vector<TypePtr>(), false);
declaration->constructor_template = member_name == owner_template->name; declaration->has_definition = true; vector<TemplateDeclaration*>& members = member_function_templates_[make_pair(owner_template, declaration->name)];
	declaration->function_parameter_names =
		function_parameter_names_from_tokens(tokens_, call_lparen,
		                                     declaration->decl_end,
		                                     true);
	Scope* primary_scope = primary_class_template_scope(owner_template);
	if (primary_scope != NULL &&
	    !hosted_library_namespace_scope(primary_scope))
	{
		bool definition_noexcept =
			function_header_has_noexcept(tokens_,
			                             call_lparen,
			                             declaration->decl_end);
		size_t explicit_count =
			explicit_function_parameter_name_count(
				declaration->function_parameter_names);
		vector<Binding*> existing_members =
			lookup_qualified_set(primary_scope,
			                     declaration->name,
			                     pa11::LOOKUP_FUNCTION);
		for (size_t i = 0; i < existing_members.size(); ++i)
		{
			Binding* existing = existing_members[i];
			if (existing == NULL ||
			    existing->type.get() == NULL ||
			    existing->type->kind != pa11::TypeKind::Function)
				continue;
			size_t existing_count = existing->type->parameters.size();
			if (!existing->is_static_member && existing_count != 0)
				--existing_count;
			if (existing_count == explicit_count &&
			    existing->unwind_no != definition_noexcept)
				throw runtime_error(
					"function exception specification mismatch");
		}
	}
	add_member_function_template(members, declaration); return true; }
bool Parser::register_dependent_qualified_conversion_function_template(
	TemplateDeclaration* declaration)
{
	if (!has_token(tokens_,
	               declaration->decl_begin,
	               declaration->decl_end,
	               OP_LBRACE))
		return false;
	size_t member_colon = declaration->decl_end;
	for (size_t p = declaration->decl_begin;
	     p + 1 < declaration->decl_end;
	     ++p)
	{
		if (tokens_[p].kind != posttoken::TokenKind::Simple ||
		    tokens_[p].type != OP_COLON2 ||
		    tokens_[p + 1].kind != posttoken::TokenKind::Simple ||
		    tokens_[p + 1].type != KW_OPERATOR)
			continue;
		member_colon = p;
		break;
	}
	if (member_colon == declaration->decl_end)
		return false;
	TemplateDeclaration* owner_template = NULL;
	for (size_t p = declaration->decl_begin; p < member_colon; ++p)
	{
		if (tokens_[p].kind != posttoken::TokenKind::Identifier)
			continue;
		if (p + 1 >= member_colon ||
		    tokens_[p + 1].kind != posttoken::TokenKind::Simple ||
		    tokens_[p + 1].type != OP_LT)
			continue;
		size_t after_args = p + 1;
		if (!skip_template_id_argument_tokens(tokens_, after_args))
			continue;
		if (after_args > member_colon ||
		    tokens_[after_args].kind != posttoken::TokenKind::Simple ||
		    tokens_[after_args].type != OP_COLON2)
			continue;
		TemplateDeclaration* templ =
			find_class_template(NULL, tokens_[p].source);
		if (templ != NULL)
			owner_template = templ;
	}
	if (owner_template == NULL)
		return false;
	declaration->kind = TemplateDeclarationKind::Function;
	declaration->owner = owner_template->owner;
	declaration->name = "operator ";
	declaration->class_template_member =
		template_parameter_lists_match(declaration->parameters,
		                               owner_template->parameters) ||
		!declaration->outer_type_substitutions.empty();
	declaration->generic_function_type =
		pa11::make_function(pa11::make_fundamental(FT_VOID),
		                    vector<TypePtr>(),
		                    false);
	declaration->has_definition = true;
	vector<TemplateDeclaration*>& members =
		member_function_templates_[make_pair(owner_template,
		                                     declaration->name)];
	add_member_function_template(members, declaration);
	return true;
}
bool Parser::register_dependent_nested_constructor_template(
	TemplateDeclaration* declaration)
{ map<string, TypePtr> parameter_types; map<string, TemplateArgument> parameter_values; collect_template_parameter_placeholders(declaration->parameters, parameter_types, parameter_values); size_t save_pos = pos_;
vector<map<string, TypePtr> > save_subst = template_type_substitutions_; vector<map<string, TemplateArgument> > save_value_subst = template_value_substitutions_;
vector<set<string> > save_pack_subst = template_type_parameter_packs_; template_type_substitutions_.push_back(parameter_types); template_value_substitutions_.push_back(parameter_values);
template_type_parameter_packs_.push_back( collect_template_type_parameter_packs(declaration->parameters)); pos_ = declaration->decl_begin; try { for (;;) { if (consume(KW_INLINE) || consume(KW_CONSTEXPR) ||
consume_explicit_specifier()) continue; break; } Scope* lookup_scope = NULL; bool qualified_lookup = false; if (consume(OP_COLON2)) { lookup_scope = global_scope(); qualified_lookup = true; }
TemplateDeclaration* outer_template = NULL; for (;;) { if (!at_identifier()) throw runtime_error("dependent constructor owner missing"); string component = consume_identifier(); if (at(OP_LT)) {
outer_template = find_class_template( qualified_lookup ? lookup_scope : NULL, component); if (outer_template == NULL) throw runtime_error( "dependent constructor owner template missing");
vector<TemplateArgument> ignored_args; parse_template_argument_list(ignored_args); expect(OP_COLON2); break; } expect(OP_COLON2); Binding* binding = qualified_lookup ? pa11::lookup_qualified(lookup_scope, component,
pa11::LOOKUP_QUALIFIER) : pa11::lookup_unqualified(current_scope(), component, pa11::LOOKUP_QUALIFIER); if (binding == NULL) throw runtime_error("dependent constructor qualifier missing");
if (binding->type.get() != NULL) complete_template_record(binding->type); lookup_scope = resolve_qualifier(binding); if (lookup_scope == NULL) throw runtime_error("dependent constructor qualifier invalid");
qualified_lookup = true; } vector<string> nested_components; string final_name; for (;;) { consume(KW_TEMPLATE); if (!at_identifier()) throw runtime_error("dependent constructor component missing");
string component = consume_identifier(); if (at(OP_LT) && !skip_template_id_argument_tokens(tokens_, pos_)) throw runtime_error( "dependent constructor template-id malformed"); if (consume(OP_COLON2)) {
nested_components.push_back(component); continue; } final_name = component; break; } if (nested_components.empty() || final_name != nested_components.back() || !at(OP_LPAREN))
throw runtime_error("not a dependent nested constructor"); declaration->kind = TemplateDeclarationKind::Function; declaration->constructor_template = true; declaration->class_template_member = true;
declaration->owner = outer_template->owner; declaration->name = final_name; declaration->generic_function_type = pa11::make_function(pa11::make_fundamental(FT_VOID), vector<TypePtr>(), false);
declaration->has_definition = has_token(tokens_, pos_, declaration->decl_end, OP_LBRACE); vector<TemplateDeclaration*>& constructors = member_function_templates_[make_pair(outer_template, final_name)];
add_member_function_template(constructors, declaration); template_type_substitutions_ = save_subst; template_value_substitutions_ = save_value_subst;
template_type_parameter_packs_ = save_pack_subst; pos_ = save_pos; return true; } catch (const exception&) { template_type_substitutions_ = save_subst; template_value_substitutions_ = save_value_subst;
template_type_parameter_packs_ = save_pack_subst; pos_ = save_pos; return false; } }
bool Parser::register_constructor_template(TemplateDeclaration* declaration)
{ map<string, TypePtr> parameter_types; map<string, TemplateArgument> parameter_values; collect_template_parameter_placeholders(declaration->parameters, parameter_types, parameter_values); size_t save_pos = pos_;
vector<Scope*> save_scopes = scopes_; vector<map<string, TypePtr> > save_subst = template_type_substitutions_; vector<map<string, TemplateArgument> > save_value_subst = template_value_substitutions_;
vector<set<string> > save_pack_subst = template_type_parameter_packs_; template_type_substitutions_.push_back(parameter_types); template_value_substitutions_.push_back(parameter_values);
template_type_parameter_packs_.push_back( collect_template_type_parameter_packs(declaration->parameters)); pos_ = declaration->decl_begin; bool matched_constructor = false; bool defer_hosted_constructor_registration = false; try {
skip_attributes(); bool explicit_ctor = consume_explicit_specifier(); bool constexpr_ctor = consume(KW_CONSTEXPR); if (!explicit_ctor) explicit_ctor = consume_explicit_specifier(); QualifiedName qname = parse_id_expression_name();
Scope* class_scope = qname.qualifier; if (class_scope == NULL && current_scope() != NULL && current_scope()->kind == ScopeKind::Class && qname.name == current_scope()->name) class_scope = current_scope();
	if (class_scope == NULL || class_scope->kind != ScopeKind::Class || !at(OP_LPAREN)) throw runtime_error("not a constructor template definition"); TypePtr class_type = pa11::record_type_for_scope(class_scope);
if (class_type.get() == NULL) throw runtime_error("constructor without class type"); if (!constructor_name_matches_scope(class_scope, qname.name)) throw runtime_error("not a constructor template definition");
if (qname.qualifier == NULL)
	declaration->lexical_scope = class_scope;
matched_constructor = true; TypePtr bare_class_type = pa11::strip_cv(class_type); bool skip_hosted_completion = hosted_compatibility_ && hosted_library_namespace_scope(class_scope) && bare_class_type->kind == pa11::TypeKind::Record; defer_hosted_constructor_registration = class_scope != current_scope() && skip_hosted_completion; if (class_scope != current_scope() && !skip_hosted_completion) { size_t parameter_pos = pos_; complete_template_record(class_type); pos_ = parameter_pos; } if (declaration->parameters.empty() && bare_class_type->is_template_specialization) {
map<const void*, TemplateDeclaration*>::iterator owner_decl = record_template_declarations_.find(bare_class_type.get()); if (owner_decl != record_template_declarations_.end() && owner_decl->second->class_specialization)
throw runtime_error("member of explicit class specialization must not use template<>"); } expect(OP_LPAREN); vector<ParameterInfo> parameters; bool variadic = false; scopes_.push_back(class_scope);
parse_parameter_clause(parameters, variadic); scopes_.pop_back(); expect(OP_RPAREN); Suffix suffix(SuffixKind::Function); parse_function_suffix_tail(suffix); vector<TypePtr> fn_params;
fn_params.push_back(pa11::make_pointer(class_type)); for (size_t i = 0; i < parameters.size(); ++i) fn_params.push_back(parameters[i].type);
	TypePtr fn_type = pa11::make_function(pa11::make_fundamental(FT_VOID), fn_params, variadic); Binding* existing = find_matching_function_template_placeholder( function_template_placeholders_, class_scope, qname.name,
	fn_type, declaration->parameters);
	Binding* declared_ctor = find_matching_function(class_scope,
	                                                qname.name,
	                                                fn_type);
	Binding* exception_spec_source = existing != NULL ? existing : declared_ctor;
	bool hosted_mismatch_allowed =
		hosted_compatibility_ &&
		hosted_library_namespace_scope(class_scope);
	if (exception_spec_source != NULL &&
	    exception_spec_source->unwind_no != suffix.noexcept_decl &&
	    !hosted_mismatch_allowed)
		throw runtime_error("function exception specification mismatch");
	bool merged_noexcept =
		(exception_spec_source != NULL && exception_spec_source->unwind_no) ||
		suffix.noexcept_decl;
	vector<TypePtr> merged_dynamic_exception_types = suffix.dynamic_exception_types;
	if (merged_dynamic_exception_types.empty() &&
	    exception_spec_source != NULL)
		merged_dynamic_exception_types =
			exception_spec_source->dynamic_exception_types;
	Binding* placeholder = existing != NULL ? existing : add_value(class_scope, BindingKind::Function, qname.name, fn_type);
	discard_implicit_default_constructor(class_type, placeholder);
	TemplateDeclaration* previous_declaration = NULL; if (existing != NULL) { map<Binding*, TemplateDeclaration*>::iterator previous = function_template_placeholders_.find(existing);
if (previous != function_template_placeholders_.end()) previous_declaration = previous->second; } placeholder->unwind_no = merged_noexcept; placeholder->dynamic_exception_spec = suffix.dynamic_exception_spec; placeholder->dynamic_exception_types = merged_dynamic_exception_types; placeholder->is_explicit = explicit_ctor;
placeholder->is_constexpr = placeholder->is_constexpr || constexpr_ctor; vector<string> names(1, "this"); vector<Expr> defaults(1); for (size_t i = 0; i < parameters.size(); ++i) { names.push_back(parameters[i].name);
defaults.push_back(parameters[i].default_value); } function_parameter_names_[placeholder] = names; placeholder->function_parameter_names = names; declaration->function_parameter_names = names; default_arguments_[placeholder] = defaults; declaration->kind = TemplateDeclarationKind::Function;
declaration->constructor_template = true; declaration->owner = class_scope; declaration->name = qname.name; declaration->generic_function_type = fn_type; declaration->placeholder = placeholder;
if (previous_declaration != NULL) merge_template_defaults(declaration->parameters, previous_declaration->parameters); function_template_placeholders_[placeholder] = declaration;
declaration->has_definition = has_token(tokens_, pos_, declaration->decl_end, OP_LBRACE); TemplateDeclaration* outer_template = NULL; for (Scope* owner_scope = class_scope; owner_scope != NULL && outer_template == NULL;
owner_scope = owner_scope->parent) { TypePtr owner_record = pa11::record_type_for_scope(owner_scope); if (owner_record.get() == NULL) continue; map<const void*, TemplateDeclaration*>::iterator outer =
record_template_declarations_.find( pa11::strip_cv(owner_record).get()); if (outer != record_template_declarations_.end()) outer_template = outer->second; } if (outer_template == NULL) {
string outer_name = qname.spelling; size_t nested = outer_name.find("::"); if (nested != string::npos) outer_name = outer_name.substr(0, nested); size_t args = outer_name.find("<"); if (args != string::npos)
outer_name = outer_name.substr(0, args); map<Scope*, map<string, TemplateDeclaration*> >::iterator sit = class_templates_.find(declaration->owner); if (sit != class_templates_.end()) {
map<string, TemplateDeclaration*>::iterator found = sit->second.find(outer_name); if (found != sit->second.end()) outer_template = found->second; } } if (outer_template == NULL && qname.qualified) {
map<Scope*, map<string, TemplateDeclaration*> >::iterator sit = class_templates_.find(declaration->owner); if (sit != class_templates_.end() && sit->second.size() == 1) outer_template = sit->second.begin()->second; }
if (outer_template != NULL) { declaration->class_template_member = declaration->outer_type_substitutions.empty() && template_parameter_lists_match(declaration->parameters, outer_template->parameters); vector<TemplateDeclaration*>& members = member_function_templates_[make_pair(outer_template, qname.name)]; add_member_function_template(members, declaration); } template_type_substitutions_ = save_subst; template_value_substitutions_ = save_value_subst;
template_type_parameter_packs_ = save_pack_subst; scopes_ = save_scopes; pos_ = save_pos; return true; } catch (const exception& err) { template_type_substitutions_ = save_subst;
template_value_substitutions_ = save_value_subst; template_type_parameter_packs_ = save_pack_subst; scopes_ = save_scopes; pos_ = save_pos; if (matched_constructor && !(defer_hosted_constructor_registration && string(err.what()) == "expected declaration specifiers")) throw; return false; } }
bool Parser::register_static_member_variable_template(
	TemplateDeclaration* declaration)
{ map<string, TypePtr> parameter_types; map<string, TemplateArgument> parameter_values; collect_template_parameter_placeholders(declaration->parameters, parameter_types, parameter_values); size_t save_pos = pos_;
vector<Scope*> save_scopes = scopes_; vector<map<string, TypePtr> > save_subst = template_type_substitutions_; vector<map<string, TemplateArgument> > save_value_subst = template_value_substitutions_;
vector<set<string> > save_pack_subst = template_type_parameter_packs_; template_type_substitutions_.push_back(parameter_types); template_value_substitutions_.push_back(parameter_values);
template_type_parameter_packs_.push_back( collect_template_type_parameter_packs(declaration->parameters)); pos_ = declaration->decl_begin; bool matched = false; try { DeclSpecs specs = parse_decl_specifier_seq(false);
TypePtr base = type_from_decl_specs(specs); Declarator declarator = parse_declarator(false); TypePtr type = apply_declarator(declarator, base); (void)type; const QualifiedName& qname = declarator_name(declarator);
if (qname.qualifier == NULL || qname.qualifier->kind != ScopeKind::Class) throw runtime_error("not a static member template definition"); matched = true; declaration->kind = TemplateDeclarationKind::Variable;
declaration->owner = qname.qualifier; declaration->name = qname.name; TypePtr owner_record = pa11::record_type_for_scope(qname.qualifier); TemplateDeclaration* outer_template = NULL;
for (Scope* owner_scope = qname.qualifier; owner_scope != NULL && outer_template == NULL; owner_scope = owner_scope->parent) { owner_record = pa11::record_type_for_scope(owner_scope); if (owner_record.get() == NULL)
continue; map<const void*, TemplateDeclaration*>::iterator outer = record_template_declarations_.find( pa11::strip_cv(owner_record).get()); if (outer != record_template_declarations_.end())
outer_template = outer->second; } string member_name = qname.name; if (outer_template == NULL) { size_t recover_pos = pos_; try { pos_ = declaration->decl_begin; parse_decl_specifier_seq(false);
vector<PtrOp> ignored_ptrs; parse_ptr_prefix(ignored_ptrs); if (at_identifier() && lookahead(OP_LT, 1)) { string root = consume_identifier(); TemplateDeclaration* recovered =
find_class_template(declaration->lexical_scope, root); if (recovered == NULL) recovered = find_class_template(declaration->owner, root); if (recovered == NULL) recovered = find_class_template(NULL, root);
vector<TemplateArgument> ignored_args; parse_template_argument_list(ignored_args); if (consume(OP_COLON2)) { string last_name; for (;;) { if (!at_identifier()) break; last_name = consume_identifier(); if (at(OP_LT)) {
vector<TemplateArgument> nested_args; parse_template_argument_list(nested_args); } if (!consume(OP_COLON2)) break; } if (recovered != NULL && !last_name.empty()) { outer_template = recovered; member_name = last_name; } }
} } catch (const exception&) { } pos_ = recover_pos; } if (outer_template != NULL) { member_variable_templates_[make_pair(outer_template, member_name)] .push_back(declaration); }
template_type_substitutions_ = save_subst; template_value_substitutions_ = save_value_subst; template_type_parameter_packs_ = save_pack_subst; scopes_ = save_scopes; pos_ = save_pos; return true; }
catch (const exception&) { template_type_substitutions_ = save_subst; template_value_substitutions_ = save_value_subst; template_type_parameter_packs_ = save_pack_subst; scopes_ = save_scopes; pos_ = save_pos;
if (matched) throw; size_t fallback_pos = pos_; vector<map<string, TypePtr> > fallback_subst = template_type_substitutions_; vector<map<string, TemplateArgument> > fallback_value_subst = template_value_substitutions_;
vector<set<string> > fallback_pack_subst = template_type_parameter_packs_; try { template_type_substitutions_.push_back(parameter_types); template_value_substitutions_.push_back(parameter_values);
template_type_parameter_packs_.push_back( collect_template_type_parameter_packs( declaration->parameters)); pos_ = declaration->decl_begin; DeclSpecs specs = parse_decl_specifier_seq(false);
(void)type_from_decl_specs(specs); vector<PtrOp> ignored_ptrs; parse_ptr_prefix(ignored_ptrs); if (!at_identifier() || !lookahead(OP_LT, 1)) throw runtime_error("not a dependent static member template definition");
string root = consume_identifier(); TemplateDeclaration* outer_template = find_class_template(declaration->lexical_scope, root); if (outer_template == NULL) outer_template = find_class_template(declaration->owner, root);
if (outer_template == NULL) outer_template = find_class_template(NULL, root); if (outer_template == NULL) throw runtime_error("static member template owner not found"); vector<TemplateArgument> ignored_args;
parse_template_argument_list(ignored_args); expect(OP_COLON2); string member_name; for (;;) { if (!at_identifier()) throw runtime_error("static member template name missing"); member_name = consume_identifier();
if (at(OP_LT)) { vector<TemplateArgument> nested_args; parse_template_argument_list(nested_args); } if (!consume(OP_COLON2)) break; } declaration->kind = TemplateDeclarationKind::Variable;
declaration->owner = outer_template->owner; declaration->name = member_name; member_variable_templates_[make_pair(outer_template, member_name)] .push_back(declaration); template_type_substitutions_ = fallback_subst;
template_value_substitutions_ = fallback_value_subst; template_type_parameter_packs_ = fallback_pack_subst; pos_ = fallback_pos; return outer_template != NULL; } catch (const exception&) {
template_type_substitutions_ = fallback_subst; template_value_substitutions_ = fallback_value_subst; template_type_parameter_packs_ = fallback_pack_subst; pos_ = fallback_pos; } return false; } }
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
	TemplateDeclaration* declaration = find_class_template(qualifier, name);
	if (declaration == NULL)
		declaration = find_alias_template(qualifier, name);
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
type_is_template_dependent(root_type); string owner_template_name; vector<pa11::TemplateInstanceArgument> owner_template_arguments; if (have_root_type_substitution && substituted_root.get() != NULL &&
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
TemplateArgument Parser::parse_non_type_template_argument_expression()
{ size_t save = pos_; ++template_argument_expression_depth_; Expr expr; try { expr = parse_assignment_expression(); } catch (...) { --template_argument_expression_depth_; pos_ = save; TemplateArgument dependent;
if ((!active_class_instantiations_.empty() || !template_type_substitutions_.empty() || !template_value_substitutions_.empty()) && try_parse_dependent_qualified_non_type_template_argument( dependent)) {
dependent.value_expr_begin = save; dependent.value_expr_end = pos_; return dependent; } throw; } size_t expr_end = pos_; --template_argument_expression_depth_; if (expr.valid && !expr.has_constant_value) {
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
