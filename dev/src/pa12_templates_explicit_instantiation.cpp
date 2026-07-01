#include "pa12_internal.h"
#include "pa12_expr_semantics_support.h"
#include "pa12_templates_function_support.h"
#include <algorithm>
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
TypePtr explicit_function_template_target_type(
	TemplateDeclaration* declaration,
	TypePtr explicit_template_target_type,
	TypePtr explicit_member_template_target_type)
{
	if (explicit_member_template_target_type.get() != NULL &&
	    declaration != NULL &&
	    declaration->generic_function_type.get() != NULL &&
	    declaration->generic_function_type->kind == pa11::TypeKind::Function &&
	    declaration->generic_function_type->parameters.size() ==
		    explicit_member_template_target_type->parameters.size())
		return explicit_member_template_target_type;
	return explicit_template_target_type;
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
	TypePtr selected_target_type; for (size_t i = 0; i < declarations.size(); ++i) { TypePtr target_type = explicit_function_template_target_type(declarations[i], explicit_template_target_type, explicit_member_template_target_type); vector<TemplateArgument> full_args; if (!deduce_function_template_target_type(declarations[i], target_type, qname.template_arguments, full_args)) continue;
		TypePtr candidate_type; if (!substitute_explicit_function_template_type(declarations[i], full_args, candidate_type) || (!pa11::same_type(candidate_type, target_type) && !same_template_signature_type(candidate_type, target_type))) continue; if (selected != NULL)
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
}  // namespace internal
}  // namespace pa12
