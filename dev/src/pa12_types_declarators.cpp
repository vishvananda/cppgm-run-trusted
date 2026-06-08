#include "pa12_types_support.h"

#include <algorithm>
#include <stdexcept>

using namespace std;

namespace pa12 {
namespace internal {

Declarator Parser::parse_declarator(bool abstract_allowed)
{
	Declarator declarator;
	parse_ptr_prefix(declarator.prefix);
	parse_noptr_declarator_root(declarator, abstract_allowed);
	if (declarator.has_name &&
	    declarator.name.qualifier != NULL &&
	    declarator.name.qualifier->kind == ScopeKind::Class)
	{
		vector<Scope*> saved_scopes = scopes_;
		scopes_.push_back(declarator.name.qualifier);
		try
		{
			parse_suffixes(declarator.suffixes);
		}
		catch (...)
		{
			scopes_ = saved_scopes;
			throw;
		}
		scopes_ = saved_scopes;
	}
	else
		parse_suffixes(declarator.suffixes);
	return declarator;
}

Declarator Parser::parse_abstract_declarator()
{
	Declarator declarator;
	parse_ptr_prefix(declarator.prefix);
	if (starts_parenthesized_abstract_declarator())
	{
		expect(OP_LPAREN);
		declarator.inner.reset(new Declarator(parse_abstract_declarator()));
		expect(OP_RPAREN);
	}
	parse_suffixes(declarator.suffixes);
	if (declarator.prefix.empty() && declarator.suffixes.empty() &&
	    declarator.inner.get() == NULL)
		throw runtime_error("expected abstract declarator");
	return declarator;
}

void Parser::parse_noptr_declarator_root(Declarator& declarator,
                                         bool abstract_allowed)
{
	if (consume(OP_LPAREN))
	{
		declarator.inner.reset(new Declarator(parse_declarator(true)));
		expect(OP_RPAREN);
		return;
	}
	if (!abstract_allowed || at_identifier() || at(OP_COLON2))
	{
		declarator.name = parse_id_expression_name();
		declarator.has_name = true;
		return;
	}
}

void Parser::parse_ptr_prefix(vector<PtrOp>& ops)
{
	for (;;)
	{
		if (at_identifier() && lookahead(OP_COLON2, 1))
		{
			size_t save = pos_;
			string class_name = consume_identifier();
			expect(OP_COLON2);
			TypePtr class_type;
			if (!find_template_type_substitution(class_name, class_type))
			{
				Binding* binding =
					pa11::lookup_unqualified(current_scope(),
					                         class_name,
					                         pa11::LOOKUP_TYPE);
				class_type = binding != NULL ? binding->type : TypePtr();
			}
			if (class_type.get() != NULL && consume(OP_STAR))
			{
				unsigned cv = pa11::CV_NONE;
				while (at_simple_cv())
					cv |= consume_cv_flag();
				ops.push_back(PtrOp(class_type, cv));
				continue;
			}
			pos_ = save;
		}
		if (at(OP_COLON2) ||
		    (at_identifier() && lookahead(OP_COLON2, 1)))
		{
			size_t save = pos_;
			try
			{
				string spelling;
				Scope* scope = parse_nested_name_specifier(&spelling);
				TypePtr class_type = scope != NULL &&
				                     scope->kind == ScopeKind::Class
					? pa11::record_type_for_scope(scope) : TypePtr();
				if (scope != NULL &&
				    scope->kind == ScopeKind::Class &&
				    class_type.get() != NULL &&
				    consume(OP_STAR))
				{
					unsigned cv = pa11::CV_NONE;
					while (at_simple_cv())
						cv |= consume_cv_flag();
					ops.push_back(PtrOp(class_type, cv));
					continue;
				}
			}
			catch (const exception&)
			{
			}
			pos_ = save;
		}
		{
			size_t save = pos_;
			TypePtr class_type;
			if (try_parse_type_name(class_type) &&
			    consume(OP_COLON2) &&
			    consume(OP_STAR))
			{
				unsigned cv = pa11::CV_NONE;
				while (at_simple_cv())
					cv |= consume_cv_flag();
				ops.push_back(PtrOp(class_type, cv));
				continue;
			}
			pos_ = save;
		}
		if (at_identifier() && lookahead(OP_COLON2, 1))
		{
			size_t save = pos_;
			string class_name = consume_identifier();
			expect(OP_COLON2);
			vector<Binding*> found =
				lookup_unqualified_set(current_scope(), class_name, pa11::LOOKUP_TYPE);
			if (found.empty() || !consume(OP_STAR))
			{
				pos_ = save;
				return;
			}
			TypePtr class_type = found[0]->type;
			unsigned cv = pa11::CV_NONE;
			while (at_simple_cv())
				cv |= consume_cv_flag();
			ops.push_back(PtrOp(class_type, cv));
		}
		else if (consume(OP_STAR))
		{
			unsigned cv = pa11::CV_NONE;
			while (at_simple_cv())
				cv |= consume_cv_flag();
			ops.push_back(PtrOp(PtrKind::Pointer, cv));
		}
		else if (consume(OP_AMP))
			ops.push_back(PtrOp(PtrKind::LValueReference, pa11::CV_NONE));
		else if (consume(OP_LAND))
			ops.push_back(PtrOp(PtrKind::RValueReference, pa11::CV_NONE));
		else
			return;
	}
}

void Parser::parse_suffixes(vector<Suffix>& suffixes)
{
	for (;;)
	{
		if (at(OP_LSQUARE))
			suffixes.push_back(parse_array_suffix());
		else if (at(OP_LPAREN))
		{
			if (pos_ + 1 < tokens_.size() &&
			    tokens_[pos_ + 1].kind == posttoken::TokenKind::Identifier &&
			    pa11::lookup_unqualified(current_scope(),
			                             tokens_[pos_ + 1].source,
			                             pa11::LOOKUP_VARIABLE |
			                             pa11::LOOKUP_PARAMETER) != NULL)
				return;
			size_t save = pos_;
				try
				{
					suffixes.push_back(parse_function_suffix());
				}
				catch (const exception&)
				{
					bool trailing_return = false;
					int depth = 0;
					for (size_t p = save; p < tokens_.size(); ++p)
					{
						if (tokens_[p].kind != posttoken::TokenKind::Simple)
							continue;
						if (tokens_[p].type == OP_LPAREN)
							++depth;
						else if (tokens_[p].type == OP_RPAREN)
						{
							--depth;
							if (depth == 0)
							{
								trailing_return =
									p + 1 < tokens_.size() &&
									tokens_[p + 1].kind ==
										posttoken::TokenKind::Simple &&
									tokens_[p + 1].type == OP_ARROW;
								break;
							}
						}
					}
					if (trailing_return)
						throw;
					if (save + 1 < tokens_.size() &&
					    tokens_[save + 1].kind == posttoken::TokenKind::Simple &&
				    tokens_[save + 1].type == OP_RPAREN)
					throw;
				pos_ = save;
				return;
			}
		}
		else
			return;
	}
}

Suffix Parser::parse_array_suffix()
{
	Suffix suffix(SuffixKind::Array);
	expect(OP_LSQUARE);
	if (consume(OP_RSQUARE))
	{
		suffix.unknown_bound = true;
		return suffix;
	}
	string dependent_bound_name;
	if (at_identifier() && lookahead(OP_RSQUARE, 1))
		dependent_bound_name = current().source;
	Expr bound = parse_expression();
	ConstexprValue value;
	if (try_evaluate_constexpr_expr(bound.node, value) &&
	    value.valid &&
	    !value.is_float &&
	    !value.is_object &&
	    !value.is_pointer)
	{
		bound.has_constant_value = true;
		bound.constant_value = value.int_value;
	}
	if (!bound.has_constant_value || bound.constant_value == 0)
	{
		TemplateArgument subst;
		if (!dependent_bound_name.empty() &&
		    find_template_value_substitution(dependent_bound_name, subst) &&
		    subst.kind == TemplateArgumentKind::Value)
		{
			suffix.unknown_bound = true;
			suffix.array_bound_name = dependent_bound_name;
			expect(OP_RSQUARE);
			return suffix;
		}
		if (active_class_instantiation_dependent())
		{
			suffix.unknown_bound = true;
			expect(OP_RSQUARE);
			return suffix;
		}
	}
	if (!bound.has_constant_value || bound.constant_value == 0)
		throw runtime_error("invalid array bound");
	suffix.bound = bound.constant_value;
	expect(OP_RSQUARE);
	return suffix;
}

Suffix Parser::parse_function_suffix()
{
	Suffix suffix(SuffixKind::Function);
	expect(OP_LPAREN);
	vector<Scope*> saved_scopes = scopes_;
	Scope* parameter_scope =
		pa11::create_child_scope(current_scope(),
		                         ScopeKind::Function,
		                         "");
	scopes_.push_back(parameter_scope);
	try
	{
		parse_parameter_clause(suffix.parameters, suffix.variadic);
		expect(OP_RPAREN);
		parse_function_suffix_tail(suffix);
	}
	catch (const exception&)
	{
		scopes_ = saved_scopes;
		throw;
	}
	scopes_ = saved_scopes;
	return suffix;
}


}  // namespace internal
}  // namespace pa12
