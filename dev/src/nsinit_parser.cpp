#include "nsinit_internal.h"

#include <algorithm>
#include <stdexcept>
#include <utility>

#include "preproc_support.h"

using namespace std;

namespace nsinit {
namespace {

enum class TokenKind
{
	Simple,
	Identifier,
	Literal,
	EndOfFile
};

struct Token
{
	TokenKind kind;
	ETokenType type;
	string source;

	Token(TokenKind k, ETokenType t, const string& s)
		: kind(k), type(t), source(s)
	{
	}
};

struct DeclSpecs
{
	bool typedef_decl;
	bool constexpr_decl;
	bool inline_decl;
	StorageClass storage;
	unsigned cv;
	vector<ETokenType> builtin;
	TypePtr named_type;

	DeclSpecs()
		: typedef_decl(false),
		  constexpr_decl(false),
		  inline_decl(false),
		  storage(StorageClass::None),
		  cv(CV_NONE)
	{
	}
};

enum class PtrKind
{
	Pointer,
	LValueReference,
	RValueReference
};

struct PtrOp
{
	PtrKind kind;
	unsigned cv;

	PtrOp(PtrKind k, unsigned flags) : kind(k), cv(flags) {}
};

enum class SuffixKind
{
	Array,
	Function
};

struct Suffix
{
	SuffixKind kind;
	bool unknown_bound;
	uint64_t bound;
	vector<TypePtr> parameters;
	bool variadic;

	explicit Suffix(SuffixKind k)
		: kind(k), unknown_bound(false), bound(0), variadic(false)
	{
	}
};

struct Declarator
{
	vector<PtrOp> prefix;
	vector<Suffix> suffixes;
	unique_ptr<Declarator> inner;
	bool has_name;
	QualifiedName name;

	Declarator() : has_name(false) {}
};

bool is_cv_token(ETokenType type)
{
	return type == KW_CONST || type == KW_VOLATILE;
}

bool is_storage_token(ETokenType type)
{
	return type == KW_STATIC ||
	       type == KW_THREAD_LOCAL ||
	       type == KW_EXTERN;
}

bool is_builtin_type_token(ETokenType type)
{
	switch (type)
	{
	case KW_CHAR:
	case KW_CHAR16_T:
	case KW_CHAR32_T:
	case KW_WCHAR_T:
	case KW_BOOL:
	case KW_SHORT:
	case KW_INT:
	case KW_LONG:
	case KW_SIGNED:
	case KW_UNSIGNED:
	case KW_FLOAT:
	case KW_DOUBLE:
	case KW_VOID:
		return true;
	default:
		return false;
	}
}

bool contains_token(const vector<ETokenType>& tokens, ETokenType token)
{
	return find(tokens.begin(), tokens.end(), token) != tokens.end();
}

size_t count_token(const vector<ETokenType>& tokens, ETokenType token)
{
	return static_cast<size_t>(count(tokens.begin(), tokens.end(), token));
}

EFundamentalType fundamental_from_specs(const vector<ETokenType>& specs)
{
	const bool sign = contains_token(specs, KW_SIGNED);
	const bool unsign = contains_token(specs, KW_UNSIGNED);
	const size_t longs = count_token(specs, KW_LONG);
	if (contains_token(specs, KW_CHAR))
		return unsign ? FT_UNSIGNED_CHAR : (sign ? FT_SIGNED_CHAR : FT_CHAR);
	if (contains_token(specs, KW_CHAR16_T))
		return FT_CHAR16_T;
	if (contains_token(specs, KW_CHAR32_T))
		return FT_CHAR32_T;
	if (contains_token(specs, KW_WCHAR_T))
		return FT_WCHAR_T;
	if (contains_token(specs, KW_BOOL))
		return FT_BOOL;
	if (contains_token(specs, KW_FLOAT))
		return FT_FLOAT;
	if (contains_token(specs, KW_DOUBLE))
		return longs > 0 ? FT_LONG_DOUBLE : FT_DOUBLE;
	if (contains_token(specs, KW_VOID))
		return FT_VOID;
	if (unsign && contains_token(specs, KW_SHORT))
		return FT_UNSIGNED_SHORT_INT;
	if (unsign && longs >= 2)
		return FT_UNSIGNED_LONG_LONG_INT;
	if (unsign && longs == 1)
		return FT_UNSIGNED_LONG_INT;
	if (unsign)
		return FT_UNSIGNED_INT;
	if (contains_token(specs, KW_SHORT))
		return FT_SHORT_INT;
	if (longs >= 2)
		return FT_LONG_LONG_INT;
	if (longs == 1)
		return FT_LONG_INT;
	return FT_INT;
}

TypePtr apply_ptr_ops(TypePtr type, const vector<PtrOp>& ops)
{
	for (size_t i = 0; i < ops.size(); ++i)
	{
		if (ops[i].kind == PtrKind::Pointer)
			type = make_cv(make_pointer(type), ops[i].cv);
		else if (ops[i].kind == PtrKind::LValueReference)
			type = make_lvalue_reference(type);
		else
			type = make_rvalue_reference(type);
	}
	return type;
}

TypePtr apply_suffix(TypePtr type, const Suffix& suffix)
{
	if (suffix.kind == SuffixKind::Array)
		return make_array(type, suffix.unknown_bound, suffix.bound);
	return make_function(type, suffix.parameters, suffix.variadic);
}

TypePtr apply_suffixes(TypePtr type, const vector<Suffix>& suffixes)
{
	for (size_t i = suffixes.size(); i > 0; --i)
		type = apply_suffix(type, suffixes[i - 1]);
	return type;
}

TypePtr apply_declarator(const Declarator& declarator, TypePtr base)
{
	TypePtr type = apply_ptr_ops(base, declarator.prefix);
	type = apply_suffixes(type, declarator.suffixes);
	if (declarator.inner.get() != NULL)
		return apply_declarator(*declarator.inner, type);
	return type;
}

const QualifiedName& declarator_name(const Declarator& declarator)
{
	if (declarator.has_name)
		return declarator.name;
	if (declarator.inner.get() != NULL)
		return declarator_name(*declarator.inner);
	throw runtime_error("declarator has no name");
}

Namespace* declarator_suffix_scope(const Declarator& declarator,
                                   Namespace* fallback)
{
	if (declarator.has_name && declarator.name.qualifier != NULL)
		return declarator.name.qualifier;
	if (declarator.inner.get() != NULL)
		return declarator_suffix_scope(*declarator.inner, fallback);
	return fallback;
}

bool is_string_literal_expr(const shared_ptr<Expr>& expr)
{
	if (!expr.get())
		return false;
	if (expr->kind == ExprKind::Paren)
		return is_string_literal_expr(expr->inner);
	return expr->kind == ExprKind::Literal && expr->string_literal != NULL;
}

StringLiteral* string_literal_from_expr(const shared_ptr<Expr>& expr)
{
	if (expr->kind == ExprKind::Paren)
		return string_literal_from_expr(expr->inner);
	return expr->string_literal;
}

bool char_array_compatible(EFundamentalType dest, EFundamentalType source)
{
	if (source == FT_CHAR)
		return dest == FT_CHAR || dest == FT_SIGNED_CHAR ||
		       dest == FT_UNSIGNED_CHAR;
	return dest == source;
}

TypePtr complete_unknown_string_array(TypePtr type, const shared_ptr<Expr>& init)
{
	if (type->kind != TypeKind::Array || !type->unknown_bound ||
	    !is_string_literal_expr(init))
		return type;
	StringLiteral* literal = string_literal_from_expr(init);
	TypePtr element = strip_cv(type->base);
	if (element->kind != TypeKind::Fundamental ||
	    !char_array_compatible(element->fundamental, literal->element_type))
		return type;
	return make_array(type->base, false, literal->elements);
}

vector<Token> convert_tokens(const vector<posttoken::Token>& tokens)
{
	vector<Token> out;
	for (size_t i = 0; i < tokens.size(); ++i)
	{
		const posttoken::Token& token = tokens[i];
		if (token.kind == posttoken::TokenKind::Simple)
			out.push_back(Token(TokenKind::Simple,
			                    token.token_type,
			                    token.source));
		else if (token.kind == posttoken::TokenKind::Identifier)
			out.push_back(Token(TokenKind::Identifier, OP_LBRACE, token.source));
		else if (token.kind == posttoken::TokenKind::Literal)
			out.push_back(Token(TokenKind::Literal, OP_LBRACE, token.source));
		else if (token.kind == posttoken::TokenKind::EndOfFile)
			out.push_back(Token(TokenKind::EndOfFile, OP_LBRACE, token.source));
		else
			throw runtime_error("invalid posttoken");
	}
	return out;
}

class Parser
{
public:
	Parser(TranslationUnit& tu, Program& program, const vector<Token>& tokens)
		: tu_(tu), program_(program), tokens_(tokens), pos_(0)
	{
		scopes_.push_back(tu_.global_namespace.get());
	}

	void parse_translation_unit()
	{
		while (!at_eof())
			parse_declaration();
		expect_eof();
	}

private:
	TranslationUnit& tu_;
	Program& program_;
	const vector<Token>& tokens_;
	size_t pos_;
	vector<Namespace*> scopes_;

	Namespace* current_namespace() const
	{
		return scopes_.back();
	}

	Namespace* global_namespace() const
	{
		return tu_.global_namespace.get();
	}

	size_t next_order()
	{
		return program_.next_order++;
	}

	bool at_eof() const
	{
		return pos_ < tokens_.size() &&
		       tokens_[pos_].kind == TokenKind::EndOfFile;
	}

	bool at_identifier() const
	{
		return pos_ < tokens_.size() &&
		       tokens_[pos_].kind == TokenKind::Identifier;
	}

	bool at_literal() const
	{
		return pos_ < tokens_.size() &&
		       tokens_[pos_].kind == TokenKind::Literal;
	}

	bool at(ETokenType type) const
	{
		return pos_ < tokens_.size() &&
		       tokens_[pos_].kind == TokenKind::Simple &&
		       tokens_[pos_].type == type;
	}

	bool lookahead(ETokenType type, size_t offset) const
	{
		size_t index = pos_ + offset;
		return index < tokens_.size() &&
		       tokens_[index].kind == TokenKind::Simple &&
		       tokens_[index].type == type;
	}

	bool consume(ETokenType type)
	{
		if (!at(type))
			return false;
		++pos_;
		return true;
	}

	void expect(ETokenType type)
	{
		if (!consume(type))
			throw runtime_error("unexpected token");
	}

	void expect_eof()
	{
		if (!at_eof())
			throw runtime_error("expected end of file");
	}

	string consume_identifier()
	{
		if (!at_identifier())
			throw runtime_error("expected identifier");
		return tokens_[pos_++].source;
	}

	void parse_declaration()
	{
		if (consume(OP_SEMICOLON))
			return;
		if (at(KW_STATIC_ASSERT))
		{
			parse_static_assert();
			return;
		}
		if ((at(KW_INLINE) && lookahead(KW_NAMESPACE, 1)) ||
		    at(KW_NAMESPACE))
		{
			parse_namespace_or_alias();
			return;
		}
		if (at(KW_USING))
		{
			parse_using_declaration_family();
			return;
		}
		parse_simple_or_function_declaration();
	}

	void parse_namespace_or_alias()
	{
		bool inline_ns = consume(KW_INLINE);
		expect(KW_NAMESPACE);
		if (!inline_ns && at_identifier() && lookahead(OP_ASS, 1))
		{
			string alias = consume_identifier();
			expect(OP_ASS);
			Namespace* target = parse_qualified_namespace_specifier();
			expect(OP_SEMICOLON);
			add_namespace_alias(tu_, current_namespace(), alias, target, next_order());
			return;
		}
		string name;
		bool named = false;
		if (at_identifier())
		{
			named = true;
			name = consume_identifier();
		}
		expect(OP_LBRACE);
		Namespace* child = named
			? get_or_create_named_namespace(tu_, current_namespace(), name, inline_ns)
			: create_unnamed_namespace(tu_, current_namespace(), inline_ns);
		scopes_.push_back(child);
		while (!at(OP_RBRACE))
			parse_declaration();
		scopes_.pop_back();
		expect(OP_RBRACE);
	}

	void parse_using_declaration_family()
	{
		expect(KW_USING);
		if (consume(KW_NAMESPACE))
		{
			Namespace* target = parse_qualified_namespace_specifier();
			expect(OP_SEMICOLON);
			add_using_directive(current_namespace(), target);
			return;
		}
		if (at_identifier() && lookahead(OP_ASS, 1))
		{
			string name = consume_identifier();
			expect(OP_ASS);
			TypePtr type = parse_type_id();
			expect(OP_SEMICOLON);
			add_type_alias(tu_, current_namespace(), name, type, next_order());
			return;
		}
		Namespace* ns = parse_nested_name_specifier();
		string name = consume_identifier();
		expect(OP_SEMICOLON);
		Entity* entity = lookup_qualified(ns, name, LOOKUP_ANY);
		if (entity == NULL)
			throw runtime_error("using declaration target not found");
		add_using_declaration(current_namespace(), name, entity);
	}

	void parse_static_assert()
	{
		expect(KW_STATIC_ASSERT);
		expect(OP_LPAREN);
		shared_ptr<Expr> expr = parse_expression(current_namespace());
		expect(OP_COMMA);
		if (!at_literal())
			throw runtime_error("expected static_assert message");
		++pos_;
		expect(OP_RPAREN);
		expect(OP_SEMICOLON);
		if (!eval_static_assert_condition(expr))
			throw runtime_error("static_assert failed");
	}

	void parse_simple_or_function_declaration()
	{
		DeclSpecs specs = parse_decl_specifier_seq();
		TypePtr base = type_from_decl_specs(specs);
		Declarator declarator = parse_declarator();
		if (at(OP_LBRACE))
		{
			declare_one(specs, base, declarator, shared_ptr<Expr>(), true);
			parse_function_body();
			return;
		}
		Namespace* init_scope =
			declarator_suffix_scope(declarator, current_namespace());
		shared_ptr<Expr> init = parse_optional_initializer(init_scope);
		declare_one(specs, base, declarator, init, false);
		while (consume(OP_COMMA))
		{
			Declarator next = parse_declarator();
			Namespace* next_scope =
				declarator_suffix_scope(next, current_namespace());
			shared_ptr<Expr> next_init = parse_optional_initializer(next_scope);
			declare_one(specs, base, next, next_init, false);
		}
		expect(OP_SEMICOLON);
	}

	void parse_function_body()
	{
		expect(OP_LBRACE);
		expect(OP_RBRACE);
	}

	shared_ptr<Expr> parse_optional_initializer(Namespace* lookup_scope)
	{
		if (!consume(OP_ASS))
			return shared_ptr<Expr>();
		return parse_expression(lookup_scope);
	}

	void declare_one(const DeclSpecs& specs,
	                 TypePtr base,
	                 const Declarator& declarator,
	                 shared_ptr<Expr> init,
	                 bool function_definition)
	{
		const QualifiedName& qname = declarator_name(declarator);
		Namespace* target = qname.qualifier != NULL
			? qname.qualifier
			: current_namespace();
		if (qname.qualifier != NULL &&
		    !namespace_encloses(current_namespace(), target))
			throw runtime_error("qualified declaration names a non-enclosing namespace");
		TypePtr type = apply_declarator(declarator, base);
		type = complete_unknown_string_array(type, init);
		if (specs.typedef_decl)
			add_type_alias(tu_, target, qname.name, type, next_order());
		else if (type->kind == TypeKind::Function || function_definition)
			add_function(tu_, target, qname.name, type, specs.storage,
			             specs.inline_decl, function_definition, next_order());
		else
			declare_variable(specs, target, qname.name, type, init);
	}

	void declare_variable(const DeclSpecs& specs,
	                      Namespace* target,
	                      const string& name,
	                      TypePtr type,
	                      shared_ptr<Expr> init)
	{
		if (is_void_type(type))
			throw runtime_error("object of void type");
		const bool definition =
			!(specs.storage == StorageClass::Extern && !init.get());
		if (definition)
		{
			if (!is_complete_object_type(type))
				throw runtime_error("incomplete object type");
			if (!init.get() && !can_default_initialize(type))
				throw runtime_error("type cannot be default initialized");
		}
		Initializer initializer;
		const Initializer* initializer_ptr = NULL;
		if (init.get())
		{
			initializer.expr = init;
			initializer_ptr = &initializer;
		}
		add_variable(tu_, target, name, type, specs.storage,
		             specs.constexpr_decl, definition, initializer_ptr,
		             next_order());
	}

	DeclSpecs parse_decl_specifier_seq()
	{
		DeclSpecs specs;
		bool saw_any = false;
		bool saw_non_cv_type = false;
		for (;;)
		{
			if (consume(KW_TYPEDEF))
			{
				specs.typedef_decl = true;
				saw_any = true;
			}
			else if (consume(KW_CONSTEXPR))
			{
				specs.constexpr_decl = true;
				saw_any = true;
			}
			else if (consume(KW_INLINE))
			{
				specs.inline_decl = true;
				saw_any = true;
			}
			else if (at_simple_storage())
			{
				specs.storage = consume_storage();
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

	bool at_simple_storage() const
	{
		return pos_ < tokens_.size() &&
		       tokens_[pos_].kind == TokenKind::Simple &&
		       is_storage_token(tokens_[pos_].type);
	}

	StorageClass consume_storage()
	{
		if (consume(KW_STATIC))
			return StorageClass::Static;
		if (consume(KW_THREAD_LOCAL))
			return StorageClass::ThreadLocal;
		expect(KW_EXTERN);
		return StorageClass::Extern;
	}

	bool at_simple_cv() const
	{
		return pos_ < tokens_.size() &&
		       tokens_[pos_].kind == TokenKind::Simple &&
		       is_cv_token(tokens_[pos_].type);
	}

	bool at_simple_builtin() const
	{
		return pos_ < tokens_.size() &&
		       tokens_[pos_].kind == TokenKind::Simple &&
		       is_builtin_type_token(tokens_[pos_].type);
	}

	unsigned consume_cv_flag()
	{
		if (consume(KW_CONST))
			return CV_CONST;
		expect(KW_VOLATILE);
		return CV_VOLATILE;
	}

	TypePtr type_from_decl_specs(const DeclSpecs& specs)
	{
		TypePtr type = specs.named_type.get() != NULL
			? specs.named_type
			: make_fundamental(fundamental_from_specs(specs.builtin));
		return make_cv(type, specs.cv);
	}

	bool try_parse_type_name(TypePtr& out)
	{
		size_t save = pos_;
		Namespace* qualifier = NULL;
		if (starts_nested_name_specifier())
			qualifier = parse_nested_name_specifier();
		if (!at_identifier())
		{
			pos_ = save;
			return false;
		}
		string name = consume_identifier();
		Entity* entity = qualifier != NULL
			? lookup_qualified(qualifier, name, LOOKUP_TYPE)
			: lookup_unqualified(current_namespace(), name, LOOKUP_TYPE);
		if (entity == NULL)
		{
			pos_ = save;
			return false;
		}
		out = entity->type;
		return true;
	}

	TypePtr parse_type_id()
	{
		DeclSpecs specs = parse_type_specifier_seq();
		TypePtr base = type_from_decl_specs(specs);
		if (!starts_abstract_declarator())
			return base;
		size_t save = pos_;
		try
		{
			Declarator declarator = parse_abstract_declarator();
			return apply_declarator(declarator, base);
		}
		catch (const exception&)
		{
			pos_ = save;
			return base;
		}
	}

	DeclSpecs parse_type_specifier_seq()
	{
		DeclSpecs specs;
		bool saw_any = false;
		bool saw_non_cv_type = false;
		for (;;)
		{
			if (at_simple_cv())
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
			else if (!saw_non_cv_type && try_parse_type_name(specs.named_type))
			{
				saw_any = true;
				saw_non_cv_type = true;
			}
			else
				break;
		}
		if (!saw_any || !saw_non_cv_type)
			throw runtime_error("expected type specifiers");
		return specs;
	}

	Declarator parse_declarator()
	{
		Declarator declarator;
		parse_ptr_prefix(declarator.prefix);
		parse_noptr_declarator_root(declarator);
		parse_suffixes(declarator.suffixes,
		               declarator_suffix_scope(declarator, current_namespace()));
		return declarator;
	}

	void parse_noptr_declarator_root(Declarator& declarator)
	{
		if (consume(OP_LPAREN))
		{
			declarator.inner.reset(new Declarator(parse_declarator()));
			expect(OP_RPAREN);
			return;
		}
		declarator.name = parse_id_expression_name();
		declarator.has_name = true;
	}

	QualifiedName parse_id_expression_name()
	{
		QualifiedName name;
		if (starts_nested_name_specifier())
			name.qualifier = parse_nested_name_specifier();
		name.name = consume_identifier();
		return name;
	}

	Declarator parse_abstract_declarator()
	{
		Declarator declarator;
		parse_ptr_prefix(declarator.prefix);
		if (starts_parenthesized_abstract_declarator())
		{
			expect(OP_LPAREN);
			declarator.inner.reset(new Declarator(parse_abstract_declarator()));
			expect(OP_RPAREN);
		}
		parse_suffixes(declarator.suffixes, current_namespace());
		if (declarator.prefix.empty() &&
		    declarator.suffixes.empty() &&
		    declarator.inner.get() == NULL)
			throw runtime_error("expected abstract declarator");
		return declarator;
	}

	void parse_ptr_prefix(vector<PtrOp>& ops)
	{
		for (;;)
		{
			if (consume(OP_STAR))
			{
				unsigned cv = CV_NONE;
				while (at_simple_cv())
					cv |= consume_cv_flag();
				ops.push_back(PtrOp(PtrKind::Pointer, cv));
			}
			else if (consume(OP_AMP))
				ops.push_back(PtrOp(PtrKind::LValueReference, CV_NONE));
			else if (consume(OP_LAND))
				ops.push_back(PtrOp(PtrKind::RValueReference, CV_NONE));
			else
				return;
		}
	}

	void parse_suffixes(vector<Suffix>& suffixes, Namespace* expr_scope)
	{
		for (;;)
		{
			if (at(OP_LSQUARE))
				suffixes.push_back(parse_array_suffix(expr_scope));
			else if (at(OP_LPAREN))
				suffixes.push_back(parse_function_suffix());
			else
				return;
		}
	}

	Suffix parse_array_suffix(Namespace* expr_scope)
	{
		Suffix suffix(SuffixKind::Array);
		expect(OP_LSQUARE);
		if (consume(OP_RSQUARE))
		{
			suffix.unknown_bound = true;
			return suffix;
		}
		shared_ptr<Expr> bound_expr = parse_expression(expr_scope);
		if (!eval_array_bound(bound_expr, suffix.bound))
			throw runtime_error("invalid array bound");
		expect(OP_RSQUARE);
		return suffix;
	}

	Suffix parse_function_suffix()
	{
		Suffix suffix(SuffixKind::Function);
		expect(OP_LPAREN);
		parse_parameter_clause(suffix.parameters, suffix.variadic);
		expect(OP_RPAREN);
		return suffix;
	}

	void parse_parameter_clause(vector<TypePtr>& parameters, bool& variadic)
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
			if (consume(OP_COMMA))
			{
				if (consume(OP_DOTS))
				{
					variadic = true;
					return;
				}
				continue;
			}
			if (consume(OP_DOTS))
				variadic = true;
			return;
		}
	}

	TypePtr parse_parameter_declaration()
	{
		DeclSpecs specs = parse_decl_specifier_seq();
		TypePtr base = type_from_decl_specs(specs);
		size_t save = pos_;
		if (starts_declarator())
		{
			try
			{
				Declarator declarator = parse_declarator();
				return apply_declarator(declarator, base);
			}
			catch (const exception&)
			{
				pos_ = save;
			}
		}
		if (starts_abstract_declarator())
			return apply_declarator(parse_abstract_declarator(), base);
		return base;
	}

	shared_ptr<Expr> parse_expression(Namespace* lookup_scope)
	{
		if (consume(KW_TRUE))
		{
			shared_ptr<Expr> expr(new Expr(ExprKind::BoolLiteral));
			expr->bool_value = true;
			return expr;
		}
		if (consume(KW_FALSE))
			return shared_ptr<Expr>(new Expr(ExprKind::BoolLiteral));
		if (consume(KW_NULLPTR))
			return shared_ptr<Expr>(new Expr(ExprKind::NullptrLiteral));
		if (at_literal())
			return parse_literal_expression();
		if (consume(OP_LPAREN))
		{
			shared_ptr<Expr> expr(new Expr(ExprKind::Paren));
			expr->inner = parse_expression(lookup_scope);
			expect(OP_RPAREN);
			return expr;
		}
		shared_ptr<Expr> expr(new Expr(ExprKind::Id));
		expr->lookup_scope = lookup_scope;
		expr->name = parse_id_expression_name();
		return expr;
	}

	shared_ptr<Expr> parse_literal_expression()
	{
		string source = tokens_[pos_++].source;
		shared_ptr<Expr> expr(new Expr(ExprKind::Literal));
		expr->literal_source = source;
		StringLiteralInfo string_info;
		if (AnalyzeStringLiteral(source, string_info) && string_info.ud_suffix.empty())
			expr->string_literal = add_string_literal(tu_, source, next_order());
		return expr;
	}

	bool starts_declarator() const
	{
		return starts_ptr_operator() ||
		       at(OP_LPAREN) ||
		       at(OP_COLON2) ||
		       at_identifier();
	}

	bool starts_abstract_declarator() const
	{
		return starts_ptr_operator() || at(OP_LPAREN) || at(OP_LSQUARE);
	}

	bool starts_ptr_operator() const
	{
		return at(OP_STAR) || at(OP_AMP) || at(OP_LAND);
	}

	bool starts_parenthesized_abstract_declarator() const
	{
		if (!at(OP_LPAREN))
			return false;
		return lookahead(OP_STAR, 1) ||
		       lookahead(OP_AMP, 1) ||
		       lookahead(OP_LAND, 1) ||
		       lookahead(OP_LPAREN, 1);
	}

	bool starts_nested_name_specifier() const
	{
		if (at(OP_COLON2))
			return true;
		return at_identifier() && lookahead(OP_COLON2, 1);
	}

	Namespace* parse_nested_name_specifier()
	{
		Namespace* ns = NULL;
		if (consume(OP_COLON2))
			ns = global_namespace();
		else
		{
			string root = consume_identifier();
			expect(OP_COLON2);
			ns = resolve_namespace(
				lookup_unqualified(current_namespace(), root, LOOKUP_NAMESPACE));
		}
		if (ns == NULL)
			throw runtime_error("namespace not found");
		while (at_identifier() && lookahead(OP_COLON2, 1))
		{
			string component = consume_identifier();
			expect(OP_COLON2);
			ns = resolve_namespace(lookup_qualified(ns,
			                                        component,
			                                        LOOKUP_NAMESPACE));
			if (ns == NULL)
				throw runtime_error("namespace component not found");
		}
		return ns;
	}

	Namespace* parse_qualified_namespace_specifier()
	{
		Namespace* qualifier = NULL;
		if (starts_nested_name_specifier())
			qualifier = parse_nested_name_specifier();
		string name = consume_identifier();
		Entity* entity = qualifier != NULL
			? lookup_qualified(qualifier, name, LOOKUP_NAMESPACE)
			: lookup_unqualified(current_namespace(), name, LOOKUP_NAMESPACE);
		Namespace* ns = resolve_namespace(entity);
		if (ns == NULL)
			throw runtime_error("namespace specifier not found");
		return ns;
	}
};

}  // namespace

unique_ptr<TranslationUnit> parse_source_file(const string& srcfile,
                                              const Options& options,
                                              Program& program)
{
	vector<PPToken> pp_tokens =
		preproc::preprocess_source_file(srcfile, options.preprocess);
	vector<posttoken::Token> post_tokens;
	if (!posttoken::collect_posttokens_checked(pp_tokens, post_tokens))
		throw runtime_error("invalid posttoken stream");

	unique_ptr<TranslationUnit> tu(new TranslationUnit());
	tu->srcfile = srcfile;
	tu->global_namespace.reset(new Namespace("", false, false, NULL));
	vector<Token> tokens = convert_tokens(post_tokens);
	Parser parser(*tu, program, tokens);
	parser.parse_translation_unit();
	return tu;
}

}  // namespace nsinit
