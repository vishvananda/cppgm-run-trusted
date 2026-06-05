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
	if (type.get() == NULL)
		return false;
	type = pa11::strip_cv(type);
	if (type->kind == pa11::TypeKind::TemplateParameter)
	{
		if (!pa11::is_deducible_template_parameter_type(type))
			return false;
		name = type->name;
		return true;
	}
	if (type->kind == pa11::TypeKind::Pointer ||
	    type->kind == pa11::TypeKind::LValueReference ||
	    type->kind == pa11::TypeKind::RValueReference ||
	    type->kind == pa11::TypeKind::Array)
		return type_contains_template_parameter_name(type->base, name);
	if (type->kind == pa11::TypeKind::Function)
	{
		if (type_contains_template_parameter_name(type->base, name))
			return true;
		for (size_t i = 0; i < type->parameters.size(); ++i)
			if (type_contains_template_parameter_name(type->parameters[i],
			                                          name))
				return true;
	}
	if (type->kind == pa11::TypeKind::MemberPointer)
		return type_contains_template_parameter_name(type->member_class,
		                                             name) ||
		       type_contains_template_parameter_name(type->base, name);
	return false;
}

}  // namespace

void Parser::parse_function_suffix_tail(Suffix& suffix)
{
	for (;;)
	{
		if (at_simple_cv())
		{
			suffix.function_cv |= consume_cv_flag();
			continue;
		}
		if (consume(OP_AMP))
		{
			suffix.ref_qualifier = 1;
			continue;
		}
		if (consume(OP_LAND))
		{
			suffix.ref_qualifier = 2;
			continue;
		}
		if (consume(KW_NOEXCEPT))
		{
			suffix.noexcept_decl = true;
			if (at(OP_LPAREN))
				skip_balanced(OP_LPAREN, OP_RPAREN);
			continue;
		}
		if (consume(KW_THROW))
		{
			suffix.noexcept_decl = true;
			if (at(OP_LPAREN))
				skip_balanced(OP_LPAREN, OP_RPAREN);
			continue;
		}
		if (at_identifier() && current().source == "override")
		{
			++pos_;
			suffix.override_decl = true;
			continue;
		}
		if (at_identifier() && current().source == "final")
		{
			++pos_;
			suffix.final_decl = true;
			continue;
		}
		if (consume(OP_ARROW))
		{
			vector<Scope*> saved_scopes = scopes_;
			Scope* parameter_scope =
				pa11::create_child_scope(current_scope(),
				                         ScopeKind::Function,
				                         "");
			scopes_.push_back(parameter_scope);
			for (size_t i = 0; i < suffix.parameters.size(); ++i)
			{
				const ParameterInfo& parameter = suffix.parameters[i];
				if (parameter.name.empty())
					continue;
				pa11::add_binding(parameter_scope,
				                  BindingKind::Parameter,
				                  parameter.name,
				                  parameter.type);
			}
			try
			{
				suffix.trailing_return = parse_type_id();
			}
			catch (const exception&)
			{
				scopes_ = saved_scopes;
				throw;
			}
			scopes_ = saved_scopes;
			continue;
		}
		break;
	}
}

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
			if (at(OP_DOTS) &&
			    type_contains_template_parameter_name(info.type, pack_name))
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
				info.default_value = parse_assignment_expression();
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
	if (at(OP_DOTS) &&
	    type_contains_template_parameter_name(info.type, pack_name))
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
		info.default_value = parse_assignment_expression();
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
