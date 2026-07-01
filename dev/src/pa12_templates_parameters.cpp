#include "pa12_internal.h"

#include <stdexcept>

using namespace std;

namespace pa12 {
namespace internal {
namespace {

bool simple_token_is_one_of(const Token& token,
                            const initializer_list<ETokenType>& types)
{
	if (token.kind != posttoken::TokenKind::Simple)
		return false;
	for (initializer_list<ETokenType>::const_iterator it = types.begin();
	     it != types.end();
	     ++it)
		if (token.type == *it)
			return true;
	return false;
}

bool token_can_follow_template_id_in_default(const vector<Token>& tokens,
                                             size_t close)
{
	if (close + 1 >= tokens.size())
		return true;
	const Token& next = tokens[close + 1];
	return simple_token_is_one_of(next,
	                              { OP_COLON2,
	                                OP_LPAREN,
	                                OP_LBRACE,
	                                OP_LSQUARE,
	                                OP_COMMA,
	                                OP_GT,
	                                OP_RPAREN,
	                                OP_RSQUARE,
	                                OP_RBRACE,
	                                OP_DOTS,
	                                OP_SEMICOLON });
}

bool token_can_precede_template_id_angle(const vector<Token>& tokens,
                                         size_t lt)
{
	if (lt == 0)
		return false;
	const Token& prev = tokens[lt - 1];
	if (prev.kind == posttoken::TokenKind::Identifier)
		return true;
	return simple_token_is_one_of(prev,
	                              { OP_GT,
	                                KW_OPERATOR,
	                                KW_DECLTYPE,
	                                KW_TEMPLATE });
}

bool top_level_lt_opens_template_id_in_default(const vector<Token>& tokens,
                                               size_t lt)
{
	if (lt >= tokens.size() ||
	    tokens[lt].kind != posttoken::TokenKind::Simple ||
	    tokens[lt].type != OP_LT ||
	    !token_can_precede_template_id_angle(tokens, lt))
		return false;
	int depth = 0;
	int paren = 0;
	int square = 0;
	int brace = 0;
	for (size_t p = lt; p < tokens.size(); ++p)
	{
		const Token& tok = tokens[p];
		if (tok.kind != posttoken::TokenKind::Simple)
			continue;
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
			if (depth == 0)
				return token_can_follow_template_id_in_default(tokens, p);
		}
	}
	return false;
}

}  // namespace

bool typename_starts_qualified_type(const vector<Token>& tokens, size_t pos)
{
	if (pos >= tokens.size() ||
	    tokens[pos].kind != posttoken::TokenKind::Simple ||
	    tokens[pos].type != KW_TYPENAME)
		return false;
	++pos;
	if (pos >= tokens.size() ||
	    tokens[pos].kind != posttoken::TokenKind::Identifier)
		return false;
	++pos;
	if (pos < tokens.size() &&
	    tokens[pos].kind == posttoken::TokenKind::Simple &&
	    tokens[pos].type == OP_LT)
	{
		int depth = 0;
		while (pos < tokens.size())
		{
			if (tokens[pos].kind == posttoken::TokenKind::Simple &&
			    tokens[pos].type == OP_LT)
				++depth;
			else if (tokens[pos].kind == posttoken::TokenKind::Simple &&
			         tokens[pos].type == OP_GT)
			{
				--depth;
				++pos;
				if (depth == 0)
					break;
				continue;
			}
			++pos;
		}
	}
	return pos < tokens.size() &&
	       tokens[pos].kind == posttoken::TokenKind::Simple &&
	       tokens[pos].type == OP_COLON2;
}


vector<TemplateParameterInfo> Parser::parse_template_parameter_clause()
{
	vector<TemplateParameterInfo> parameters;
	expect(OP_LT);
	vector<map<string, TypePtr> > save_subst = template_type_substitutions_;
	vector<map<string, TemplateArgument> > save_value_subst =
		template_value_substitutions_;
	vector<set<string> > save_pack_subst = template_type_parameter_packs_;
	template_type_substitutions_.push_back(map<string, TypePtr>());
	template_value_substitutions_.push_back(map<string, TemplateArgument>());
	template_type_parameter_packs_.push_back(set<string>());
	if (consume(OP_GT))
	{
		template_type_substitutions_ = save_subst;
		template_value_substitutions_ = save_value_subst;
		template_type_parameter_packs_ = save_pack_subst;
		return parameters;
	}
	for (;;)
	{
		TemplateParameterInfo parameter = parse_template_parameter_info();
		parameters.push_back(parameter);
		TemplateParameterInfo& stored_parameter = parameters.back();
		if (!stored_parameter.name.empty() &&
		    stored_parameter.kind == TemplateParameterKind::Type)
		{
			template_type_substitutions_.back()[stored_parameter.name] =
				template_parameter_placeholder_type(stored_parameter);
			if (stored_parameter.is_pack)
				template_type_parameter_packs_.back().insert(
					stored_parameter.name);
		}
		else if (!stored_parameter.name.empty() &&
		         stored_parameter.kind == TemplateParameterKind::NonType)
		{
			TemplateArgument arg =
				TemplateArgument::dependent_value_arg(
					stored_parameter.type.get() != NULL
					? stored_parameter.type
					: pa11::make_fundamental(FT_INT));
			arg.value_name = stored_parameter.name;
			if (stored_parameter.is_pack)
			{
				vector<TemplateArgument> pack;
				pack.push_back(arg);
				template_value_substitutions_.back()[stored_parameter.name] =
					TemplateArgument::pack_arg(pack);
			}
			else
				template_value_substitutions_.back()[stored_parameter.name] = arg;
		}
		else if (!stored_parameter.name.empty() &&
		         stored_parameter.kind == TemplateParameterKind::TemplateTemplate)
		{
			TemplateArgument arg = TemplateArgument::template_arg(NULL);
			arg.value_name = stored_parameter.name;
			template_value_substitutions_.back()[stored_parameter.name] = arg;
		}
		if (!consume(OP_COMMA))
			break;
	}
	expect(OP_GT);
	template_type_substitutions_ = save_subst;
	template_value_substitutions_ = save_value_subst;
	template_type_parameter_packs_ = save_pack_subst;
	return parameters;
}

bool Parser::active_type_parameter_pack(const string& name) const
{
	for (size_t i = template_type_parameter_packs_.size(); i > 0; --i)
	{
		if (template_type_parameter_packs_[i - 1].count(name) != 0)
			return true;
		if (i - 1 < template_type_substitutions_.size() &&
		    template_type_substitutions_[i - 1].find(name) !=
			    template_type_substitutions_[i - 1].end())
			return false;
	}
	return false;
}

bool Parser::type_substitution_hides_value_substitution(
	const string& name) const
{
	size_t depth = max(template_type_substitutions_.size(),
	                   template_value_substitutions_.size());
	for (size_t offset = 0; offset < depth; ++offset)
	{
		bool have_type = false;
		if (offset < template_type_substitutions_.size())
		{
			size_t index = template_type_substitutions_.size() - 1 - offset;
			have_type =
				template_type_substitutions_[index].find(name) !=
				template_type_substitutions_[index].end();
		}
		bool have_value = false;
		if (offset < template_value_substitutions_.size())
		{
			size_t index = template_value_substitutions_.size() - 1 - offset;
			have_value =
				template_value_substitutions_[index].find(name) !=
				template_value_substitutions_[index].end();
		}
		if (have_type)
			return true;
		if (have_value)
			return false;
	}
	return false;
}

bool Parser::parameter_pack_expansion_name(const string& name) const
{
	if (active_type_parameter_pack(name))
		return true;
	TemplateArgument subst;
	return find_template_value_substitution(name, subst) &&
	       subst.kind == TemplateArgumentKind::Pack;
}

TemplateParameterInfo Parser::parse_template_parameter_info()
{
	TemplateParameterInfo parameter;
	if (consume(KW_TEMPLATE))
	{
		parameter.kind = TemplateParameterKind::TemplateTemplate;
		parameter.template_parameters = parse_template_parameter_clause();
		if (!consume(KW_CLASS) && !consume(KW_TYPENAME))
			throw runtime_error("unsupported template template parameter");
		parameter.is_pack = consume(OP_DOTS);
		if (at_identifier())
			parameter.name = consume_identifier();
		if (consume(OP_ASS))
			skip_template_parameter_default(parameter);
		return parameter;
	}
	bool typename_qualified_type =
		typename_starts_qualified_type(tokens_, pos_);
	if (!typename_qualified_type &&
	    (consume(KW_CLASS) || consume(KW_TYPENAME)))
	{
		parameter.kind = TemplateParameterKind::Type;
		parameter.is_pack = consume(OP_DOTS);
		if (at_identifier())
			parameter.name = consume_identifier();
		if (parameter.name.empty())
			parameter.name = "__template_param" +
			                 to_string(template_declarations_.size()) + "_" +
			                 to_string(pos_);
		if (consume(OP_ASS))
			skip_template_parameter_default(parameter);
		return parameter;
	}

	parameter.kind = TemplateParameterKind::NonType;
	DeclSpecs specs = parse_decl_specifier_seq(false);
	TypePtr base = type_from_decl_specs(specs);
	parameter.is_pack = consume(OP_DOTS);
	if (!at(OP_COMMA) && !at(OP_GT) && !at(OP_ASS))
	{
		size_t declarator_save = pos_;
		Declarator declarator;
		try
		{
			declarator = parse_declarator(false);
		}
		catch (const exception&)
		{
			pos_ = declarator_save;
			declarator = parse_abstract_declarator();
		}
		parameter.type = apply_declarator(declarator, base);
		parameter.is_pack = parameter.is_pack || consume(OP_DOTS);
		if (declarator_has_name(declarator))
			parameter.name = declarator_name(declarator).name;
	}
	else
	{
		parameter.type = base;
	}
	if (consume(OP_ASS))
	{
		skip_template_parameter_default(parameter);
		return parameter;
	}
	return parameter;
}

void Parser::skip_template_parameter_default(TemplateParameterInfo& parameter)
{
	parameter.has_default = true;
	parameter.default_begin = pos_;
	int angle = 0;
	int paren = 0;
	int square = 0;
	int brace = 0;
	while (!at_eof())
	{
		if (angle == 0 && paren == 0 && square == 0 && brace == 0 &&
		    (at(OP_COMMA) || at(OP_GT)))
			break;
		if (at(OP_LPAREN))
			++paren;
		else if (at(OP_RPAREN) && paren > 0)
			--paren;
		else if (at(OP_LSQUARE))
			++square;
		else if (at(OP_RSQUARE) && square > 0)
			--square;
		else if (at(OP_LBRACE))
			++brace;
		else if (at(OP_RBRACE) && brace > 0)
			--brace;
		else if (paren == 0 && square == 0 && brace == 0 && at(OP_LT) &&
		         (angle > 0 ||
		          top_level_lt_opens_template_id_in_default(tokens_, pos_)))
			++angle;
		else if (paren == 0 && square == 0 && brace == 0 && at(OP_GT))
		{
			if (angle == 0 && paren == 0 && square == 0 && brace == 0)
				break;
			if (angle > 0)
				--angle;
		}
		++pos_;
	}
	parameter.default_end = pos_;
}

size_t Parser::skip_template_declaration_body(size_t begin) const
{
	int paren = 0;
	int square = 0;
	for (size_t p = begin; p < tokens_.size(); ++p)
	{
		const Token& tok = tokens_[p];
		if (tok.kind != posttoken::TokenKind::Simple)
			continue;
		if (tok.type == OP_LPAREN)
			++paren;
		else if (tok.type == OP_RPAREN)
			--paren;
		else if (tok.type == OP_LSQUARE)
			++square;
		else if (tok.type == OP_RSQUARE)
			--square;
		else if (tok.type == OP_LBRACE && paren == 0 && square == 0)
		{
			size_t q = p + 1;
			int brace = 1;
			while (q < tokens_.size() && brace > 0)
			{
				if (tokens_[q].kind == posttoken::TokenKind::Simple &&
				    tokens_[q].type == OP_LBRACE)
					++brace;
				else if (tokens_[q].kind == posttoken::TokenKind::Simple &&
				         tokens_[q].type == OP_RBRACE)
					--brace;
				++q;
			}
			for (;;)
			{
				if (q < tokens_.size() &&
				    tokens_[q].kind == posttoken::TokenKind::Identifier &&
				    (tokens_[q].source == "__attribute__" ||
				     tokens_[q].source == "__declspec") &&
				    q + 1 < tokens_.size() &&
				    tokens_[q + 1].kind == posttoken::TokenKind::Simple &&
				    tokens_[q + 1].type == OP_LPAREN)
				{
					q += 2;
					int attr_paren = 1;
					while (q < tokens_.size() && attr_paren > 0)
					{
						if (tokens_[q].kind == posttoken::TokenKind::Simple &&
						    tokens_[q].type == OP_LPAREN)
							++attr_paren;
						else if (tokens_[q].kind == posttoken::TokenKind::Simple &&
						         tokens_[q].type == OP_RPAREN)
							--attr_paren;
						++q;
					}
					continue;
				}
				if (q + 1 < tokens_.size() &&
				    tokens_[q].kind == posttoken::TokenKind::Simple &&
				    tokens_[q].type == OP_LSQUARE &&
				    tokens_[q + 1].kind == posttoken::TokenKind::Simple &&
				    tokens_[q + 1].type == OP_LSQUARE)
				{
					q += 2;
					int attr_square = 1;
					while (q < tokens_.size() && attr_square > 0)
					{
						if (tokens_[q].kind == posttoken::TokenKind::Simple &&
						    tokens_[q].type == OP_LSQUARE)
							++attr_square;
						else if (tokens_[q].kind == posttoken::TokenKind::Simple &&
						         tokens_[q].type == OP_RSQUARE)
							--attr_square;
						++q;
					}
					if (q < tokens_.size() &&
					    tokens_[q].kind == posttoken::TokenKind::Simple &&
					    tokens_[q].type == OP_RSQUARE)
						++q;
					continue;
				}
				break;
			}
			if (q < tokens_.size() &&
			    tokens_[q].kind == posttoken::TokenKind::Simple &&
			    tokens_[q].type == OP_SEMICOLON)
				++q;
				else if (q < tokens_.size() &&
				         tokens_[q].kind == posttoken::TokenKind::Simple &&
				         (tokens_[q].type == OP_COMMA ||
				          tokens_[q].type == OP_GT ||
				          tokens_[q].type == OP_LBRACE))
				{
					p = q - 1;
					continue;
			}
			return q;
		}
		else if (tok.type == OP_SEMICOLON && paren == 0 && square == 0)
			return p + 1;
	}
	return tokens_.size();
}

void Parser::parse_template_declaration()
{
	expect(KW_TEMPLATE);
	if (!at(OP_LT))
	{
		--pos_;
		parse_explicit_template_instantiation(false);
		return;
	}
	vector<TemplateParameterInfo> parameters = parse_template_parameter_clause();
	size_t decl_begin = pos_;
	size_t decl_end = skip_template_declaration_body(decl_begin);
	register_template_declaration(parameters, decl_begin, decl_end);
	pos_ = decl_end;
}

}  // namespace internal
}  // namespace pa12
