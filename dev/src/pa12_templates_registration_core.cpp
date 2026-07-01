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
	vector<Scope*> save_scopes = scopes_;
	try
	{
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
				scopes_ = save_scopes;
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
	}
	catch (...)
	{
		pos_ = save;
		scopes_ = save_scopes;
		throw;
	}
	pos_ = save;
	scopes_ = save_scopes;
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
	bool save_class_specialization_pattern = parsing_class_specialization_pattern_; parsing_class_specialization_pattern_ = true; try { parse_template_argument_list(pattern); } catch (...) { parsing_class_specialization_pattern_ = save_class_specialization_pattern; throw; } parsing_class_specialization_pattern_ = save_class_specialization_pattern; declaration->class_specialization = true; declaration->class_specialization_pattern = pattern; declaration->has_definition = has_token(tokens_, pos_,
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
}  // namespace internal
}  // namespace pa12
