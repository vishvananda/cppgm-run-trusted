#include "pa12_internal.h"

#include <stdexcept>

using namespace std;

namespace pa12 {
namespace internal {
namespace {

TypePtr adjust_parameter_type(TypePtr type)
{
	if (type->kind == pa11::TypeKind::Array)
		return pa11::make_pointer(type->base);
	if (type->kind == pa11::TypeKind::Function)
		return pa11::make_pointer(type);
	return type;
}

bool type_contains_template_parameter_name(TypePtr type, string& name)
{
	return template_type_has_template_parameter_name(type, name);
}

}  // namespace

void Parser::parse_function_suffix_tail(Suffix& suffix)
{ for (;;) { if (at_simple_cv()) { suffix.function_cv |= consume_cv_flag(); continue; } if (consume(OP_AMP)) { suffix.ref_qualifier = 1; continue; } if (consume(OP_LAND)) { suffix.ref_qualifier = 2; continue; }
if (consume(KW_NOEXCEPT)) { suffix.noexcept_decl = true; if (at(OP_LPAREN)) skip_balanced(OP_LPAREN, OP_RPAREN); continue; } if (consume(KW_THROW)) { suffix.noexcept_decl = true; if (at(OP_LPAREN))
skip_balanced(OP_LPAREN, OP_RPAREN); continue; } if (at_identifier() && current().source == "override") { ++pos_; suffix.override_decl = true; continue; } if (at_identifier() && current().source == "final") { ++pos_;
suffix.final_decl = true; continue; } if (consume(OP_ARROW)) { vector<Scope*> saved_scopes = scopes_; Scope* parameter_scope = pa11::create_child_scope(current_scope(), ScopeKind::Function, "");
scopes_.push_back(parameter_scope); map<string, vector<Binding*> > parameter_packs; for (size_t i = 0; i < suffix.parameters.size(); ++i) { const ParameterInfo& parameter = suffix.parameters[i];
if (!parameter.pack_expression_name.empty() && !parameter.pack_name.empty()) { TemplateArgument subst; if (find_template_value_substitution( parameter.pack_name, subst) && subst.kind == TemplateArgumentKind::Pack &&
subst.pack.empty()) { parameter_packs[parameter.pack_expression_name]; continue; } } if (parameter.name.empty() || parameter.type.get() == NULL) continue; TypePtr parameter_type =
substitute_template_type(parameter.type); Binding* binding = pa11::add_binding(parameter_scope, BindingKind::Parameter, parameter.name, parameter_type); if (!parameter.pack_expression_name.empty())
parameter_packs[parameter.pack_expression_name] .push_back(binding); } function_parameter_pack_substitutions_.push_back(parameter_packs); size_t trailing_return_begin = pos_; try {
suffix.trailing_return = parse_type_id(); TypePtr trailing_bare = suffix.trailing_return.get() != NULL ? pa11::strip_cv(suffix.trailing_return) : TypePtr(); bool concrete_substitution_context =
!validating_template_definition_ && (!template_type_substitutions_.empty() || !template_value_substitutions_.empty()); if (concrete_substitution_context) { if (!template_type_substitutions_.empty())
for (map<string, TypePtr>::const_iterator it = template_type_substitutions_.back().begin(); it != template_type_substitutions_.back().end(); ++it) if (type_is_template_dependent(it->second))
concrete_substitution_context = false; if (!template_value_substitutions_.empty()) for (map<string, TemplateArgument>::const_iterator it = template_value_substitutions_.back().begin();
it != template_value_substitutions_.back().end(); ++it) if (template_argument_has_template_parameter( it->second, record_template_arguments_)) concrete_substitution_context = false; } if (trailing_bare.get() != NULL &&
trailing_bare->is_dependent_typename && trailing_bare->dependent_typename_decltype && concrete_substitution_context) suffix.trailing_return = substitute_template_type(suffix.trailing_return); } catch (const exception&) {
bool concrete_substitution_context = !validating_template_definition_ && (!template_type_substitutions_.empty() || !template_value_substitutions_.empty()); if (concrete_substitution_context) {
if (!template_type_substitutions_.empty()) for (map<string, TypePtr>::const_iterator it = template_type_substitutions_.back().begin(); it != template_type_substitutions_.back().end(); ++it)
if (type_is_template_dependent(it->second)) concrete_substitution_context = false; if (!template_value_substitutions_.empty()) for (map<string, TemplateArgument>::const_iterator it =
template_value_substitutions_.back().begin(); it != template_value_substitutions_.back().end(); ++it) if (template_argument_has_template_parameter( it->second, record_template_arguments_))
concrete_substitution_context = false; } if (concrete_substitution_context && !active_class_instantiation_dependent()) { function_parameter_pack_substitutions_.pop_back(); scopes_ = saved_scopes; throw; }
if (!template_type_substitutions_.empty() || !template_value_substitutions_.empty() || !active_class_instantiations_.empty() || validating_template_definition_) { pos_ = trailing_return_begin; int angle = 0;
int paren = 0; int square = 0; while (!at_eof()) { if (angle == 0 && paren == 0 && square == 0 && (at(OP_LBRACE) || at(OP_SEMICOLON) || at(OP_COLON))) break; if (at(OP_LT)) ++angle; else if (at(OP_GT) && angle > 0)
--angle; else if (at(OP_LPAREN)) ++paren; else if (at(OP_RPAREN) && paren > 0) --paren; else if (at(OP_LSQUARE)) ++square; else if (at(OP_RSQUARE) && square > 0) --square; ++pos_; } suffix.trailing_return =
pa11::make_dependent_typename_type( "__dependent_trailing_return", false, false, false); function_parameter_pack_substitutions_.pop_back(); scopes_ = saved_scopes; continue; }
function_parameter_pack_substitutions_.pop_back(); scopes_ = saved_scopes; throw; } function_parameter_pack_substitutions_.pop_back(); scopes_ = saved_scopes; continue; } break; } }

void Parser::parse_parameter_clause(vector<ParameterInfo>& parameters,
                                    bool& variadic)
{
	variadic = false;
	Scope* parameter_scope =
		pa11::create_child_scope(current_scope(), ScopeKind::Function, "");
	scopes_.push_back(parameter_scope);
	try
	{
		if (consume(OP_DOTS))
		{
			variadic = true;
		}
		else if (!at(OP_RPAREN))
		{
			for (;;)
			{
				ParameterInfo parsed = parse_parameter_declaration();
				vector<ParameterInfo> expanded = expand_parameter_pack(parsed);
				for (size_t i = 0; i < expanded.size(); ++i)
				{
					parameters.push_back(expanded[i]);
					ParameterInfo& parameter = parameters.back();
					if (!parameter.name.empty())
						pa11::add_binding(parameter_scope,
						                  BindingKind::Parameter,
						                  parameter.name,
						                  parameter.type);
				}
				if (!consume(OP_COMMA))
					break;
				if (consume(OP_DOTS))
				{
					variadic = true;
					break;
				}
			}
			if (!variadic && !parameters.empty() &&
			    !parameters.back().is_pack_expansion &&
			    consume(OP_DOTS))
				variadic = true;
		}
	}
	catch (...)
	{
		scopes_.pop_back();
		throw;
	}
	scopes_.pop_back();
}

vector<ParameterInfo> Parser::expand_parameter_pack(
	const ParameterInfo& parameter) const
{
	vector<ParameterInfo> out;
	if (!parameter.is_pack_expansion)
	{
		out.push_back(parameter);
		return out;
	}
	TemplateArgument subst;
	if (!find_template_value_substitution(parameter.pack_name, subst) ||
	    subst.kind != TemplateArgumentKind::Pack)
	{
		out.push_back(parameter);
		return out;
	}
	if (subst.pack.empty() && !parameter.pack_expression_name.empty())
	{
		if (validating_template_definition_)
		{
			out.push_back(parameter);
			return out;
		}
		ParameterInfo marker = parameter;
		marker.name.clear();
		marker.type.reset();
		marker.is_pack_expansion = false;
		out.push_back(marker);
		return out;
	}
	for (size_t i = 0; i < subst.pack.size(); ++i)
	{
		if (subst.pack[i].kind != TemplateArgumentKind::Type)
			throw runtime_error("type parameter pack required");
		ParameterInfo expanded = parameter;
		expanded.is_pack_expansion = false;
		expanded.type =
			substitute_template_type_parameter(parameter.type,
			                                   parameter.pack_name,
			                                   subst.pack[i].type);
		if (!parameter.name.empty() && i > 0)
			expanded.name = parameter.name + "__pack" + to_string(i + 1);
		out.push_back(expanded);
	}
	return out;
}

ParameterInfo Parser::parse_parameter_declaration()
{
	size_t parameter_begin = pos_;
	DeclSpecs specs = parse_decl_specifier_seq(false);
	TypePtr base = type_from_decl_specs(specs);
	ParameterInfo info;
	size_t save = pos_;
	if (starts_declarator())
	{
		try
		{
			Declarator declarator = parse_declarator(true);
			info.type = adjust_parameter_type(apply_declarator(declarator, base));
				if (declarator_has_name(declarator))
					info.name = declarator_name(declarator).name;
				string pack_name;
				bool pack_expansion =
					at(OP_DOTS) &&
					type_contains_template_parameter_name(info.type,
					                                      pack_name) &&
					parameter_pack_expansion_name(pack_name);
				if (!pack_expansion && at(OP_DOTS) && pos_ > 0 &&
				    parameter_pack_expansion_name(tokens_[pos_ - 1].source))
				{
					pack_name = tokens_[pos_ - 1].source;
					pack_expansion = true;
				}
				if (!pack_expansion && at(OP_DOTS))
				{
					for (size_t i = parameter_begin; i < pos_; ++i)
						if (parameter_pack_expansion_name(tokens_[i].source))
						{
							pack_name = tokens_[i].source;
							pack_expansion = true;
							break;
						}
				}
				if (pack_expansion)
				{
					expect(OP_DOTS);
					info.is_pack_expansion = true;
					info.pack_name = pack_name;
					if (info.name.empty() && at_identifier())
						info.name = consume_identifier();
					info.pack_expression_name = info.name;
				}
				if (consume(OP_ASS))
				{
					info.has_default = true;
					size_t default_begin = pos_;
					info.default_value = parse_assignment_expression();
					info.default_value.source_begin = default_begin;
					info.default_value.source_end = pos_;
				}
			return info;
		}
		catch (const exception&)
		{
			pos_ = save;
		}
	}
	if (starts_abstract_declarator())
		info.type = adjust_parameter_type(
			apply_declarator(parse_abstract_declarator(), base));
		else
			info.type = adjust_parameter_type(base);
		string pack_name;
		bool pack_expansion =
			at(OP_DOTS) &&
			type_contains_template_parameter_name(info.type, pack_name) &&
			parameter_pack_expansion_name(pack_name);
			if (!pack_expansion && at(OP_DOTS) && pos_ > 0 &&
			    parameter_pack_expansion_name(tokens_[pos_ - 1].source))
			{
				pack_name = tokens_[pos_ - 1].source;
				pack_expansion = true;
			}
			if (!pack_expansion && at(OP_DOTS))
			{
				for (size_t i = parameter_begin; i < pos_; ++i)
					if (parameter_pack_expansion_name(tokens_[i].source))
					{
						pack_name = tokens_[i].source;
						pack_expansion = true;
						break;
					}
			}
				if (pack_expansion)
				{
					expect(OP_DOTS);
					info.is_pack_expansion = true;
					info.pack_name = pack_name;
			if (info.name.empty() && at_identifier())
				info.name = consume_identifier();
			info.pack_expression_name = info.name;
		}
		if (consume(OP_ASS))
		{
			info.has_default = true;
			size_t default_begin = pos_;
			info.default_value = parse_assignment_expression();
			info.default_value.source_begin = default_begin;
			info.default_value.source_end = pos_;
		}
	return info;
}

bool Parser::starts_declaration()
{
	if (at(KW_TYPEDEF) || at(KW_CONSTEXPR) || at(KW_EXTERN) ||
	    at(KW_STATIC) || at(KW_DECLTYPE) || at(KW_TYPENAME) ||
	    starts_class_key() || at(KW_ENUM) || at(KW_STATIC_ASSERT))
		return true;
	if (at_simple_cv() || at_simple_builtin())
		return true;
	if (at_identifier() &&
	    pos_ + 1 < tokens_.size() &&
	    tokens_[pos_ + 1].kind == posttoken::TokenKind::Identifier)
		return true;
	if (!at_identifier() && !at(OP_COLON2) && !at(KW_TYPENAME))
		return false;
	TypePtr type;
	size_t save = pos_;
	bool ok = try_parse_type_name(type);
	pos_ = save;
	return ok;
}

bool Parser::starts_class_key() const
{
	return at(KW_STRUCT) || at(KW_CLASS) || at(KW_UNION);
}

bool Parser::starts_ptr_operator() const
{
	return at(OP_STAR) || at(OP_AMP) || at(OP_LAND) ||
	       (at_identifier() && lookahead(OP_COLON2, 1));
}

bool Parser::starts_declarator() const
{
	return starts_ptr_operator() || at(OP_LPAREN) || at(OP_COLON2) ||
	       at_identifier();
}

bool Parser::starts_abstract_declarator() const
{
	return starts_ptr_operator() || at(OP_LPAREN) || at(OP_LSQUARE);
}

bool Parser::starts_parenthesized_abstract_declarator() const
{
	if (!at(OP_LPAREN))
		return false;
	return lookahead(OP_STAR, 1) || lookahead(OP_AMP, 1) ||
	       lookahead(OP_LAND, 1) || lookahead(OP_LPAREN, 1);
}

bool Parser::at_simple_ignored_specifier() const
{
	return pos_ < tokens_.size() &&
	       tokens_[pos_].kind == posttoken::TokenKind::Simple &&
	       pa11::is_storage_or_function_specifier(tokens_[pos_].type);
}

bool Parser::at_simple_cv() const
{
	return pos_ < tokens_.size() &&
	       tokens_[pos_].kind == posttoken::TokenKind::Simple &&
	       pa11::is_cv_token(tokens_[pos_].type);
}

bool Parser::at_simple_builtin() const
{
	return pos_ < tokens_.size() &&
	       tokens_[pos_].kind == posttoken::TokenKind::Simple &&
	       pa11::is_builtin_type_token(tokens_[pos_].type);
}

unsigned Parser::consume_cv_flag()
{
	if (consume(KW_CONST))
		return pa11::CV_CONST;
	expect(KW_VOLATILE);
	return pa11::CV_VOLATILE;
}

}  // namespace internal
}  // namespace pa12
