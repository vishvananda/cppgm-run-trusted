#include "pa12_types_support.h"

#include <algorithm>
#include <stdexcept>

using namespace std;

namespace pa12 {
namespace internal {
namespace {

bool ignored_pointer_qualifier_name(const string& name)
{
	return name == "_Nonnull" ||
	       name == "_Nullable" ||
	       name == "_Null_unspecified" ||
	       name == "_Nullable_result" ||
	       name == "restrict" ||
	       name == "__restrict" ||
	       name == "__restrict__";
}

}  // namespace

Declarator Parser::parse_declarator(bool abstract_allowed)
{
	size_t declarator_begin = pos_;
	Declarator declarator;
	parse_ptr_prefix(declarator.prefix);
	parse_noptr_declarator_root(declarator, abstract_allowed);
	bool textual_qualified_declarator = false;
	for (size_t ti = declarator_begin; ti < pos_ && ti < tokens_.size(); ++ti)
		if (tokens_[ti].kind == posttoken::TokenKind::Simple &&
		    tokens_[ti].type == OP_COLON2)
		{
			textual_qualified_declarator = true;
			break;
		}
	bool qualified_declarator =
		declarator.has_name &&
		(declarator.name.qualified || textual_qualified_declarator);
	if (declarator.has_name &&
	    declarator.name.qualifier != NULL &&
	    declarator.name.qualifier->kind == ScopeKind::Class)
	{
		Scope* suffix_scope = declarator.name.qualifier;
		TypePtr qualifier_record =
			pa11::record_type_for_scope(declarator.name.qualifier);
		if (qualifier_record.get() != NULL)
		{
			complete_template_record(qualifier_record);
			TypePtr bare_qualifier = pa11::strip_cv(qualifier_record);
			map<const void*, TemplateDeclaration*>::const_iterator decl =
				record_template_declarations_.find(bare_qualifier.get());
			TemplateDeclaration* qualifier_template =
				decl != record_template_declarations_.end()
				? decl->second : NULL;
			if (qualifier_template == NULL)
				qualifier_template =
					find_class_template(declarator.name.qualifier->parent,
					                    declarator.name.qualifier->name);
			if (qualifier_template == NULL)
				qualifier_template =
					find_class_template(current_scope(),
					                    declarator.name.qualifier->name);
			if (qualifier_template != NULL && suffix_scope->members.empty())
			{
				Binding* primary =
					pa11::lookup_qualified(qualifier_template->owner,
					                       qualifier_template->name,
					                       pa11::LOOKUP_TYPE);
				TypePtr primary_record =
					primary != NULL && primary->type.get() != NULL
					? pa11::strip_cv(primary->type) : TypePtr();
				if (primary_record.get() != NULL &&
				    primary_record->kind == pa11::TypeKind::Record &&
				    primary_record->scope != NULL)
					suffix_scope = primary_record->scope;
			}
		}
		vector<Scope*> saved_scopes = scopes_;
		scopes_.push_back(suffix_scope);
		try
		{
			parse_suffixes(declarator.suffixes, qualified_declarator);
		}
		catch (...)
		{
			scopes_ = saved_scopes;
			throw;
		}
		scopes_ = saved_scopes;
	}
	else
		parse_suffixes(declarator.suffixes, qualified_declarator);
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
	auto consume_ptr_qualifiers = [&]() -> unsigned {
		unsigned cv = pa11::CV_NONE;
		for (;;)
		{
			if (at_simple_cv())
			{
				cv |= consume_cv_flag();
				continue;
			}
			if (starts_attribute())
			{
				skip_attributes();
				continue;
			}
			if (at_identifier() &&
			    ignored_pointer_qualifier_name(current().source))
			{
				++pos_;
				continue;
			}
			break;
		}
		return cv;
	};
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
				unsigned cv = consume_ptr_qualifiers();
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
					unsigned cv = consume_ptr_qualifiers();
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
				unsigned cv = consume_ptr_qualifiers();
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
			unsigned cv = consume_ptr_qualifiers();
			ops.push_back(PtrOp(class_type, cv));
		}
		else if (consume(OP_STAR) || consume(OP_XOR))
		{
			unsigned cv = consume_ptr_qualifiers();
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

void Parser::parse_suffixes(vector<Suffix>& suffixes,
                            bool qualified_declarator)
{
	for (;;)
	{
		if (starts_attribute())
		{
			Suffix attribute(SuffixKind::Attribute);
			if (parse_gnu_attribute_suffix(attribute))
			{
				if (attribute.vector_size != 0)
					suffixes.push_back(attribute);
			}
			else
				skip_attributes();
		}
		else if (at(OP_LSQUARE))
			suffixes.push_back(parse_array_suffix());
		else if (at(OP_LPAREN))
		{
			if (!qualified_declarator &&
			    pos_ + 1 < tokens_.size() &&
			    tokens_[pos_ + 1].kind == posttoken::TokenKind::Identifier)
			{
				const string& name = tokens_[pos_ + 1].source;
				Binding* type =
					pa11::lookup_unqualified(current_scope(),
					                         name,
					                         pa11::LOOKUP_TYPE);
				Binding* value =
					pa11::lookup_unqualified(current_scope(),
					                         name,
					                         pa11::LOOKUP_VARIABLE |
					                         pa11::LOOKUP_PARAMETER);
				bool local_value_hides_type =
					value != NULL &&
					value->owner != NULL &&
					(value->owner->kind == ScopeKind::Function ||
					 value->owner->kind == ScopeKind::Block);
				if ((type == NULL && value != NULL) || local_value_hides_type)
					return;
			}
			size_t save = pos_;
				try
				{
					suffixes.push_back(parse_function_suffix());
				}
					catch (const exception& err)
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
					if (qualified_declarator)
					{
						int body_depth = 0;
						size_t close = save;
						for (; close < tokens_.size(); ++close)
						{
							if (tokens_[close].kind != posttoken::TokenKind::Simple)
								continue;
							if (tokens_[close].type == OP_LPAREN)
								++body_depth;
							else if (tokens_[close].type == OP_RPAREN)
							{
								--body_depth;
								if (body_depth == 0)
								{
									++close;
									while (close < tokens_.size() &&
									       tokens_[close].kind ==
									       posttoken::TokenKind::Simple &&
									       (tokens_[close].type == KW_CONST ||
									        tokens_[close].type == KW_VOLATILE ||
									        tokens_[close].type == OP_AMP ||
									        tokens_[close].type == OP_LAND))
										++close;
									if (close < tokens_.size() &&
									    ((tokens_[close].kind ==
									      posttoken::TokenKind::Simple &&
									      (tokens_[close].type == OP_LBRACE ||
									       tokens_[close].type == KW_TRY)) ||
									     (tokens_[close].kind ==
									      posttoken::TokenKind::Identifier &&
									      tokens_[close].source == "__try")))
										throw;
									break;
								}
							}
						}
					}
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
	Expr bound;
	int saved_constexpr_value_depth = constexpr_value_expression_depth_;
	++constexpr_value_expression_depth_;
	try
	{
		bound = parse_expression();
	}
	catch (...)
	{
		constexpr_value_expression_depth_ = saved_constexpr_value_depth;
		throw;
	}
	constexpr_value_expression_depth_ = saved_constexpr_value_depth;
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
	if (!bound.has_constant_value ||
	    (bound.constant_value == 0 &&
	     current_scope()->kind != ScopeKind::Class))
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
