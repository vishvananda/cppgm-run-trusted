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

}  // namespace

DeclSpecs Parser::parse_decl_specifier_seq(bool type_id_context)
{
	DeclSpecs specs;
	bool saw_any = false;
	bool saw_non_cv_type = false;
	for (;;)
	{
		if (!type_id_context && consume(KW_TYPEDEF))
		{
			specs.typedef_decl = true;
			saw_any = true;
		}
		else if (!type_id_context && consume(KW_CONSTEXPR))
		{
			specs.constexpr_decl = true;
			saw_any = true;
		}
		else if (!type_id_context && at_simple_ignored_specifier())
		{
			++pos_;
			saw_any = true;
		}
		else if (at_simple_cv())
		{
			specs.cv |= consume_cv_flag();
			saw_any = true;
		}
		else if (at_simple_builtin())
		{
			specs.builtin.push_back(tokens_[pos_++].type);
			saw_any = true;
			saw_non_cv_type = true;
		}
		else if (!saw_non_cv_type && at(KW_DECLTYPE))
		{
			specs.named_type = parse_decltype_specifier();
			saw_any = true;
			saw_non_cv_type = true;
		}
		else if (!saw_non_cv_type && starts_class_key())
		{
			specs.named_type = parse_class_specifier();
			saw_any = true;
			saw_non_cv_type = true;
		}
		else if (!saw_non_cv_type && at(KW_ENUM))
		{
			specs.named_type = parse_enum_specifier();
			saw_any = true;
			saw_non_cv_type = true;
		}
		else if (!saw_non_cv_type && try_parse_type_name(specs.named_type))
		{
			saw_any = true;
			saw_non_cv_type = true;
		}
		else
			break;
	}
	if (!saw_any || !saw_non_cv_type)
		throw runtime_error("expected declaration specifiers");
	return specs;
}

TypePtr Parser::type_from_decl_specs(const DeclSpecs& specs)
{
	TypePtr type = specs.named_type.get() != NULL ? specs.named_type :
		pa11::make_fundamental(pa11::fundamental_from_specs(specs.builtin));
	return pa11::make_cv(type, specs.cv);
}

TypePtr Parser::parse_type_id()
{
	DeclSpecs specs = parse_decl_specifier_seq(true);
	TypePtr base = type_from_decl_specs(specs);
	if (!starts_abstract_declarator())
		return base;
	size_t save = pos_;
	try
	{
		return apply_declarator(parse_abstract_declarator(), base);
	}
	catch (const exception&)
	{
		pos_ = save;
		return base;
	}
}

TypePtr Parser::parse_decltype_specifier()
{
	expect(KW_DECLTYPE);
	expect(OP_LPAREN);
	if (at(KW_SIZEOF))
	{
		Expr expr = parse_type_trait_expression(KW_SIZEOF);
		expect(OP_RPAREN);
		return expr.type;
	}
	bool parenthesized = consume(OP_LPAREN);
	QualifiedName name = parse_id_expression_name();
	Binding* binding = resolve_single_name(name, pa11::LOOKUP_VALUE);
	if (binding == NULL)
		throw runtime_error("decltype target not found");
	if (parenthesized)
		expect(OP_RPAREN);
	expect(OP_RPAREN);
	if (parenthesized && binding->kind != BindingKind::Function)
		return pa11::make_lvalue_reference(binding->type);
	return binding->type;
}

TypePtr Parser::parse_class_specifier()
{
	const size_t start_index = pos_;
	ETokenType key = current().type;
	++pos_;
	string name;
	if (at_identifier())
		name = consume_identifier();
	if (!at(OP_LBRACE))
	{
		if (name.empty())
			throw runtime_error("anonymous class declaration is not a type");
		vector<Binding*> found =
			lookup_unqualified_set(current_scope(), name, pa11::LOOKUP_TYPE);
		if (!found.empty() &&
		    found[0]->type->kind == pa11::TypeKind::Record)
			return found[0]->type;
		return add_record(current_scope(), name, class_tag(key), false, NULL);
	}

	bool anonymous = name.empty();
	if (anonymous)
	{
		size_t p = pos_;
		int depth = 0;
		do
		{
			if (tokens_[p].kind == posttoken::TokenKind::Simple &&
			    tokens_[p].type == OP_LBRACE)
				++depth;
			else if (tokens_[p].kind == posttoken::TokenKind::Simple &&
			         tokens_[p].type == OP_RBRACE)
				--depth;
			++p;
		}
		while (p < tokens_.size() && depth > 0);
		const bool injected_union =
			key == KW_UNION && p < tokens_.size() &&
			tokens_[p].kind == posttoken::TokenKind::Simple &&
			tokens_[p].type == OP_SEMICOLON;
		name = injected_union
			? "__anonymous_union_type__" + to_string(start_index) +
			  "_" + to_string(p + 1)
			: make_local_type_name("__local_type");
	}
	Scope* class_scope =
		pa11::create_child_scope(current_scope(), ScopeKind::Class, name);
	TypePtr type =
		add_record(current_scope(), name, class_tag(key), true, class_scope);
	type->scope = class_scope;
	expect(OP_LBRACE);
	scopes_.push_back(class_scope);
	parse_class_body(class_scope);
	scopes_.pop_back();
	expect(OP_RBRACE);
	return type;
}

void Parser::parse_class_body(Scope* class_scope)
{
	while (!at(OP_RBRACE))
	{
		if (consume(KW_PUBLIC) || consume(KW_PRIVATE) || consume(KW_PROTECTED))
		{
			expect(OP_COLON);
			continue;
		}
		Node ignored;
		size_t save = pos_;
		try
		{
			parse_simple_or_function_declaration(ignored, false);
		}
		catch (const exception&)
		{
			pos_ = save;
			if (!parse_constructor_like_member())
				throw;
		}
		(void)class_scope;
	}
}

TypePtr Parser::parse_enum_specifier()
{
	expect(KW_ENUM);
	bool scoped = consume(KW_CLASS) || consume(KW_STRUCT);
	string name;
	if (at_identifier())
		name = consume_identifier();
	EFundamentalType underlying = FT_INT;
	if (consume(OP_COLON))
		underlying = parse_enum_underlying_type();
	if (!at(OP_LBRACE))
	{
		if (name.empty())
			throw runtime_error("opaque enum requires name");
		return add_enum(current_scope(), name, scoped, underlying, true, scoped);
	}

	if (name.empty())
		name = make_local_type_name("__anonymous_enum");
	TypePtr type = add_enum(current_scope(), name, scoped, underlying, true, scoped);
	Scope* enum_scope = scoped && type->scope != NULL ? type->scope : current_scope();
	expect(OP_LBRACE);
	if (scoped)
		scopes_.push_back(enum_scope);
	uint64_t next_value = 0;
	while (!at(OP_RBRACE))
	{
		string enumerator = consume_identifier();
		uint64_t value = next_value;
		if (consume(OP_ASS))
		{
			Expr explicit_value = parse_assignment_expression();
			if (!explicit_value.has_constant_value)
				throw runtime_error("invalid enumerator initializer");
			value = explicit_value.constant_value;
		}
		Binding* binding =
			pa11::add_binding(enum_scope, BindingKind::Enumerator, enumerator, type);
		binding->has_constant = true;
		binding->constant_value = value;
		next_value = value + 1;
		if (!consume(OP_COMMA))
			break;
	}
	if (scoped)
		scopes_.pop_back();
	expect(OP_RBRACE);
	return type;
}

EFundamentalType Parser::parse_enum_underlying_type()
{
	DeclSpecs specs = parse_decl_specifier_seq(true);
	if (specs.named_type.get() != NULL)
		return FT_INT;
	return pa11::fundamental_from_specs(specs.builtin);
}

bool Parser::try_parse_type_name(TypePtr& out)
{
	size_t save = pos_;
	string spelling;
	Scope* qualifier = NULL;
	if (at(OP_COLON2) || (at_identifier() && lookahead(OP_COLON2, 1)))
		qualifier = parse_nested_name_specifier(&spelling);
	if (!at_identifier())
	{
		pos_ = save;
		return false;
	}
	string name = consume_identifier();
	vector<Binding*> found = qualifier != NULL
		? lookup_qualified_set(qualifier, name, pa11::LOOKUP_TYPE)
		: lookup_unqualified_set(current_scope(), name, pa11::LOOKUP_TYPE);
	if (found.empty())
	{
		pos_ = save;
		return false;
	}
	out = found[0]->type;
	return true;
}

Declarator Parser::parse_declarator(bool abstract_allowed)
{
	Declarator declarator;
	parse_ptr_prefix(declarator.prefix);
	parse_noptr_declarator_root(declarator, abstract_allowed);
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
			size_t save = pos_;
			try
			{
				suffixes.push_back(parse_function_suffix());
			}
			catch (const exception&)
			{
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
	Expr bound = parse_expression();
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
	parse_parameter_clause(suffix.parameters, suffix.variadic);
	expect(OP_RPAREN);
	parse_function_suffix_tail(suffix);
	return suffix;
}

void Parser::parse_function_suffix_tail(Suffix& suffix)
{
	for (;;)
	{
		if (at_simple_cv())
		{
			suffix.function_cv |= consume_cv_flag();
			continue;
		}
		if (consume(OP_AMP) || consume(OP_LAND))
			continue;
		if (consume(KW_NOEXCEPT) || consume(KW_THROW))
		{
			if (at(OP_LPAREN))
				skip_balanced(OP_LPAREN, OP_RPAREN);
			continue;
		}
		break;
	}
}

void Parser::parse_parameter_clause(vector<ParameterInfo>& parameters,
                                    bool& variadic)
{
	variadic = false;
	if (at(OP_RPAREN))
		return;
	if (consume(OP_DOTS))
	{
		variadic = true;
		return;
	}
	for (;;)
	{
		parameters.push_back(parse_parameter_declaration());
		if (!consume(OP_COMMA))
			break;
		if (consume(OP_DOTS))
		{
			variadic = true;
			return;
		}
	}
	if (consume(OP_DOTS))
		variadic = true;
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
	    at(KW_STATIC) || at(KW_DECLTYPE) || starts_class_key() || at(KW_ENUM))
		return true;
	if (at_simple_cv() || at_simple_builtin())
		return true;
	if (!at_identifier() && !at(OP_COLON2))
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
	       lookahead(OP_LAND, 1) || lookahead(OP_LPAREN, 1) ||
	       lookahead(OP_RPAREN, 1);
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
