#include "pa12_internal.h"
#include "pa12_expr_semantics_support.h"
#include "pa12_templates_function_support.h"
#include <algorithm>
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
struct DependentMemberTemplateHeader
{
	size_t call_lparen;
	size_t member_name_pos;
	size_t member_colon;
	string member_name;
};
string operator_function_name_token(ETokenType type, const string& source)
{
	if (type == OP_LPAREN)
		return "operator()";
	if (type == OP_LSQUARE)
		return "operator[]";
	return "operator" + source;
}
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
			parsed_member_name = operator_function_name_token(
				tokens[p - 1].type, tokens[p - 1].source);
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
	if (!find_dependent_member_template_header(tokens_,
	                                           declaration,
	                                           header))
		return false;
	size_t call_lparen = header.call_lparen;
	string member_name = header.member_name;
	size_t member_colon = header.member_colon;
	TemplateDeclaration* owner_template = NULL;
size_t owner_template_args_pos = declaration->decl_end; for (size_t p = declaration->decl_begin; p < member_colon; ++p) { if (tokens_[p].kind != posttoken::TokenKind::Identifier) continue; if (p + 1 >= member_colon ||
tokens_[p + 1].kind != posttoken::TokenKind::Simple || tokens_[p + 1].type != OP_LT) continue; size_t after_args = p + 1; if (!skip_template_id_argument_tokens(tokens_, after_args)) continue;
if (after_args > member_colon || tokens_[after_args].kind != posttoken::TokenKind::Simple || tokens_[after_args].type != OP_COLON2) continue; TemplateDeclaration* templ = find_class_template(declaration->owner, tokens_[p].source);
if (templ == NULL && declaration->lexical_scope != declaration->owner) templ = find_class_template(declaration->lexical_scope, tokens_[p].source);
if (templ == NULL) templ = find_class_template(NULL, tokens_[p].source);
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
arg_type->name != parameter.name) owner_name_subst[arg_type->name] = template_parameter_placeholder_type(parameter); } if (!owner_name_subst.empty()) declaration->outer_type_substitutions.push_back(
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
placeholder->is_constexpr = placeholder->is_constexpr || constexpr_ctor; vector<string> names(1, "this"); vector<Expr> defaults(1); vector<bool> pack_expansions(1, false); for (size_t i = 0; i < parameters.size(); ++i) { names.push_back(parameters[i].name);
defaults.push_back(parameters[i].default_value); pack_expansions.push_back(parameters[i].is_pack_expansion); } function_parameter_names_[placeholder] = names; placeholder->function_parameter_names = names; declaration->function_parameter_names = names; declaration->function_parameter_pack_expansions = pack_expansions; default_arguments_[placeholder] = default_arguments_for_binding(placeholder, defaults); declaration->kind = TemplateDeclarationKind::Function;
declaration->constructor_template = true; declaration->owner = class_scope; declaration->name = qname.name; declaration->generic_function_type = fn_type; declaration->placeholder = placeholder;
if (previous_declaration != NULL) merge_template_defaults(declaration->parameters, previous_declaration->parameters); function_template_placeholders_[placeholder] = declaration;
declaration->has_definition = has_token(tokens_, pos_, declaration->decl_end, OP_LBRACE); TemplateDeclaration* outer_template = NULL; for (Scope* owner_scope = class_scope; owner_scope != NULL && outer_template == NULL;
owner_scope = owner_scope->parent) { TypePtr owner_record = pa11::record_type_for_scope(owner_scope); if (owner_record.get() == NULL) continue; map<const void*, TemplateDeclaration*>::iterator outer =
record_template_declarations_.find( pa11::strip_cv(owner_record).get()); if (outer != record_template_declarations_.end()) outer_template = outer->second; } if (outer_template == NULL) {
string outer_name = qname.spelling; size_t nested = outer_name.find("::"); if (nested != string::npos) outer_name = outer_name.substr(0, nested); size_t args = outer_name.find("<"); if (args != string::npos)
outer_name = outer_name.substr(0, args); map<Scope*, map<string, TemplateDeclaration*> >::iterator sit = class_templates_.find(declaration->owner); if (sit != class_templates_.end()) {
map<string, TemplateDeclaration*>::iterator found = sit->second.find(outer_name); if (found != sit->second.end()) outer_template = found->second; } } if (outer_template == NULL && qname.qualified) {
map<Scope*, map<string, TemplateDeclaration*> >::iterator sit = class_templates_.find(declaration->owner); if (sit != class_templates_.end() && sit->second.size() == 1) outer_template = sit->second.begin()->second; }
if (outer_template != NULL) { declaration->class_template_member = qname.qualifier != NULL && declaration->outer_type_substitutions.empty() && template_parameter_lists_match(declaration->parameters, outer_template->parameters); vector<TemplateDeclaration*>& members = member_function_templates_[make_pair(outer_template, qname.name)]; add_member_function_template(members, declaration); } template_type_substitutions_ = save_subst; template_value_substitutions_ = save_value_subst;
template_type_parameter_packs_ = save_pack_subst; scopes_ = save_scopes; pos_ = save_pos; return true; } catch (const exception& err) { template_type_substitutions_ = save_subst;
	template_value_substitutions_ = save_value_subst; template_type_parameter_packs_ = save_pack_subst; scopes_ = save_scopes; pos_ = save_pos; if (matched_constructor && defer_hosted_constructor_registration && string(err.what()).compare(0, 31, "expected declaration specifiers") == 0) return true; if (matched_constructor) throw; return false; } }
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
}  // namespace internal
}  // namespace pa12
