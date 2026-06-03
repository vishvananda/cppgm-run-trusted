#include "pa11_internal.h"

#include <algorithm>
#include <stdexcept>
#include <utility>
#include "pa10_parser_internal.h"
#include "preproc_support.h"

using namespace std;

namespace pa11 {
namespace {
using pa10::internal::Token;

struct EvalResult {
	bool valid;
	uint64_t value;
	TypePtr type;
	Binding* binding;
	bool lvalue;
	EvalResult() : valid(false), value(0), binding(NULL), lvalue(false) {}
};
struct DeclSpecs {
	bool typedef_decl;
	bool constexpr_decl;
	unsigned cv;
	vector<ETokenType> builtin;
	TypePtr named_type;
	DeclSpecs() : typedef_decl(false), constexpr_decl(false), cv(CV_NONE) {}
};
enum class PtrKind { Pointer, LValueReference, RValueReference };

struct PtrOp {
	PtrKind kind;
	unsigned cv;
	PtrOp(PtrKind k, unsigned flags) : kind(k), cv(flags) {}
};
struct ParameterInfo { string name; TypePtr type; };

enum class SuffixKind { Array, Function };

struct Suffix
{
	SuffixKind kind;
	bool unknown_bound;
	uint64_t bound;
	vector<ParameterInfo> parameters;
	bool variadic;

	explicit Suffix(SuffixKind k)
		: kind(k), unknown_bound(false), bound(0), variadic(false)
	{
	}
};

struct QualifiedName {
	Scope* qualifier;
	string name;
	QualifiedName() : qualifier(NULL) {}
};

struct Declarator {
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

bool is_storage_or_function_specifier(ETokenType type)
{
	return type == KW_EXTERN || type == KW_STATIC ||
	       type == KW_THREAD_LOCAL || type == KW_INLINE ||
	       type == KW_VIRTUAL || type == KW_FRIEND ||
	       type == KW_MUTABLE || type == KW_REGISTER ||
	       type == KW_EXPLICIT;
}

bool is_builtin_type_token(ETokenType type)
{
	switch (type)
	{
	case KW_CHAR: case KW_CHAR16_T: case KW_CHAR32_T: case KW_WCHAR_T:
	case KW_BOOL: case KW_SHORT: case KW_INT: case KW_LONG:
	case KW_SIGNED: case KW_UNSIGNED: case KW_FLOAT: case KW_DOUBLE:
	case KW_VOID:
		return true;
	default:
		return false;
	}
}

bool contains_token(const vector<ETokenType>& tokens, ETokenType token)
{ return find(tokens.begin(), tokens.end(), token) != tokens.end(); }

size_t count_token(const vector<ETokenType>& tokens, ETokenType token)
{ return static_cast<size_t>(count(tokens.begin(), tokens.end(), token)); }

EFundamentalType fundamental_from_specs(const vector<ETokenType>& specs)
{
	const bool sign = contains_token(specs, KW_SIGNED);
	const bool unsign = contains_token(specs, KW_UNSIGNED);
	const size_t longs = count_token(specs, KW_LONG);
	if (contains_token(specs, KW_CHAR))
		return unsign ? FT_UNSIGNED_CHAR : (sign ? FT_SIGNED_CHAR : FT_CHAR);
	if (contains_token(specs, KW_CHAR16_T)) return FT_CHAR16_T;
	if (contains_token(specs, KW_CHAR32_T)) return FT_CHAR32_T;
	if (contains_token(specs, KW_WCHAR_T)) return FT_WCHAR_T;
	if (contains_token(specs, KW_BOOL)) return FT_BOOL;
	if (contains_token(specs, KW_FLOAT)) return FT_FLOAT;
	if (contains_token(specs, KW_DOUBLE))
		return longs > 0 ? FT_LONG_DOUBLE : FT_DOUBLE;
	if (contains_token(specs, KW_VOID)) return FT_VOID;
	if (unsign && contains_token(specs, KW_SHORT))
		return FT_UNSIGNED_SHORT_INT;
	if (unsign && longs >= 2) return FT_UNSIGNED_LONG_LONG_INT;
	if (unsign && longs == 1) return FT_UNSIGNED_LONG_INT;
	if (unsign) return FT_UNSIGNED_INT;
	if (contains_token(specs, KW_SHORT)) return FT_SHORT_INT;
	if (longs >= 2) return FT_LONG_LONG_INT;
	if (longs == 1) return FT_LONG_INT;
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

vector<TypePtr> parameter_types(const vector<ParameterInfo>& parameters)
{
	vector<TypePtr> out;
	for (size_t i = 0; i < parameters.size(); ++i)
		out.push_back(parameters[i].type);
	return out;
}

TypePtr apply_suffix(TypePtr type, const Suffix& suffix)
{
	if (suffix.kind == SuffixKind::Array)
		return make_array(type, suffix.unknown_bound, suffix.bound);
	return make_function(type, parameter_types(suffix.parameters), suffix.variadic);
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

const Suffix* declarator_function_suffix(const Declarator& declarator)
{
	for (size_t i = 0; i < declarator.suffixes.size(); ++i)
	{
		if (declarator.suffixes[i].kind == SuffixKind::Function)
			return &declarator.suffixes[i];
	}
	return NULL;
}

bool is_identifier_token(const Token& token)
{ return token.kind == posttoken::TokenKind::Identifier; }

bool is_literal_token(const Token& token)
{ return token.kind == posttoken::TokenKind::Literal; }

class Parser
{
public:
	Parser(TranslationUnit& tu, const vector<Token>& tokens)
		: tu_(tu), tokens_(tokens), pos_(0)
	{
		scopes_.push_back(tu_.global_scope.get());
	}

	void parse_translation_unit()
	{
		while (!at_eof())
			parse_declaration();
		expect_eof();
	}

private:
	TranslationUnit& tu_;
	const vector<Token>& tokens_;
	size_t pos_;
	vector<Scope*> scopes_;

	Scope* current_scope() const { return scopes_.back(); }
	Scope* global_scope() const { return tu_.global_scope.get(); }

	bool at_eof() const
	{
		return pos_ < tokens_.size() &&
		       tokens_[pos_].kind == posttoken::TokenKind::EndOfFile;
	}

	bool at_identifier() const
	{ return pos_ < tokens_.size() && is_identifier_token(tokens_[pos_]); }

	bool at_literal() const
	{ return pos_ < tokens_.size() && is_literal_token(tokens_[pos_]); }

	bool at(ETokenType type) const
	{
		return pos_ < tokens_.size() &&
		       tokens_[pos_].kind == posttoken::TokenKind::Simple &&
		       tokens_[pos_].type == type;
	}

	bool lookahead(ETokenType type, size_t offset) const
	{
		size_t index = pos_ + offset;
		return index < tokens_.size() &&
		       tokens_[index].kind == posttoken::TokenKind::Simple &&
		       tokens_[index].type == type;
	}

	bool consume(ETokenType type)
	{
		if (!at(type)) return false;
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
		if (!at_eof()) throw runtime_error("expected end of file");
	}

	string consume_identifier()
	{
		if (!at_identifier())
			throw runtime_error("expected identifier");
		return tokens_[pos_++].source;
	}

	void parse_declaration()
	{
		if (consume(OP_SEMICOLON) || parse_access_specifier()) return;
		if (at(KW_STATIC_ASSERT))
		{
			parse_static_assert();
			return;
		}
		if ((at(KW_INLINE) && lookahead(KW_NAMESPACE, 1)) || at(KW_NAMESPACE))
		{
			parse_namespace_or_alias();
			return;
		}
		if (at(KW_USING))
		{
			parse_using_family();
			return;
		}
		if (at(KW_TEMPLATE))
		{
			parse_template_declaration();
			return;
		}
		parse_simple_or_function_declaration();
	}

	bool parse_access_specifier()
	{
		if (!((at(KW_PUBLIC) || at(KW_PRIVATE) || at(KW_PROTECTED)) &&
		      lookahead(OP_COLON, 1))) return false;
		pos_ += 2;
		return true;
	}

	void parse_namespace_or_alias()
	{
		bool inline_ns = consume(KW_INLINE);
		expect(KW_NAMESPACE);
		if (!inline_ns && at_identifier() && lookahead(OP_ASS, 1))
		{
			string alias = consume_identifier();
			expect(OP_ASS);
			Scope* target = parse_qualified_namespace_specifier();
			expect(OP_SEMICOLON);
			add_namespace_alias(current_scope(), alias, target);
			return;
		}
		string name;
		bool named = false;
		if (at_identifier()) { named = true; name = consume_identifier(); }
		expect(OP_LBRACE);
		Scope* child = named
			? get_or_create_namespace(current_scope(), name, inline_ns)
			: create_child_scope(current_scope(), ScopeKind::Namespace, "<unnamed>");
		scopes_.push_back(child);
		while (!at(OP_RBRACE))
			parse_declaration();
		scopes_.pop_back();
		expect(OP_RBRACE);
	}

	void parse_using_family()
	{
		expect(KW_USING);
		if (consume(KW_NAMESPACE))
		{
			Scope* target = parse_qualified_namespace_specifier();
			expect(OP_SEMICOLON);
			add_using_directive(current_scope(), target);
			return;
		}
		if (at_identifier() && lookahead(OP_ASS, 1))
		{
			string name = consume_identifier();
			expect(OP_ASS);
			TypePtr type = parse_type_id();
			expect(OP_SEMICOLON);
			add_or_update_alias(current_scope(), name, type);
			return;
		}
		Scope* qualifier = parse_nested_name_specifier();
		string name = consume_identifier();
		if (at(OP_LT))
			throw runtime_error("using declaration cannot name template-id");
		expect(OP_SEMICOLON);
		Binding* target = lookup_qualified(qualifier, name, LOOKUP_ANY);
		if (target == NULL)
			throw runtime_error("using declaration target not found");
		add_using_declaration(current_scope(), name, target);
	}

	void parse_template_declaration()
	{
		expect(KW_TEMPLATE);
		Scope* scope =
			create_child_scope(current_scope(), ScopeKind::TemplateParameters, "");
		scopes_.push_back(scope);
		parse_template_parameter_clause();
		parse_declaration();
		scopes_.pop_back();
	}

	void parse_template_parameter_clause()
	{
		expect(OP_LT);
		if (!at(OP_GT))
		{
			for (;;)
			{
				parse_template_parameter();
				if (!consume(OP_COMMA))
					break;
			}
		}
		expect(OP_GT);
	}

	void parse_template_parameter()
	{
		if (consume(KW_TEMPLATE))
		{
			parse_template_parameter_clause();
			if (!(consume(KW_CLASS) || consume(KW_TYPENAME)))
				throw runtime_error("expected template template parameter kind");
			string name = at_identifier() ? consume_identifier() : "";
			if (!name.empty())
				add_binding(current_scope(),
				            BindingKind::Type,
				            name,
				            make_template_template_parameter_type(name));
			parse_optional_template_default();
			return;
		}
		if (consume(KW_TYPENAME) || consume(KW_CLASS))
		{
			string name = at_identifier() ? consume_identifier() : "";
			if (!name.empty())
				add_binding(current_scope(),
				            BindingKind::Type,
				            name,
				            make_template_parameter_type(name));
			parse_optional_template_default();
			return;
		}
		parse_type_id();
		if (at_identifier())
			++pos_;
		parse_optional_template_default();
	}

	void parse_optional_template_default()
	{
		if (!consume(OP_ASS)) return;
		skip_until_template_parameter_separator();
	}

	void skip_until_template_parameter_separator()
	{
		int angle = 0;
		int paren = 0;
		int square = 0;
		while (!at_eof())
		{
			if (angle == 0 && paren == 0 && square == 0 &&
			    (at(OP_COMMA) || at(OP_GT)))
				return;
			if (consume(OP_LT))
				++angle;
			else if (consume(OP_GT))
				--angle;
			else if (consume(OP_LPAREN))
				++paren;
			else if (consume(OP_RPAREN))
				--paren;
			else if (consume(OP_LSQUARE))
				++square;
			else if (consume(OP_RSQUARE))
				--square;
			else
				++pos_;
		}
	}

	void parse_static_assert()
	{
		expect(KW_STATIC_ASSERT);
		expect(OP_LPAREN);
		EvalResult result = parse_expression();
		expect(OP_COMMA);
		if (!at_literal())
			throw runtime_error("expected static_assert message");
		++pos_;
		expect(OP_RPAREN);
		expect(OP_SEMICOLON);
		if (!result.valid || result.value == 0)
			throw runtime_error("static_assert failed");
	}

	void parse_simple_or_function_declaration()
	{
		DeclSpecs specs = parse_decl_specifier_seq(false);
		TypePtr base = type_from_decl_specs(specs);
		if (consume(OP_SEMICOLON))
			return;
		Declarator declarator = parse_declarator(false);
		if (at(OP_LBRACE))
		{
			Binding* function = declare_one(specs, base, declarator, EvalResult(), true);
			parse_function_body(function, declarator);
			return;
		}
		EvalResult init = parse_optional_initializer();
		declare_one(specs, base, declarator, init, false);
		while (consume(OP_COMMA))
		{
			Declarator next = parse_declarator(false);
			EvalResult next_init = parse_optional_initializer();
			declare_one(specs, base, next, next_init, false);
		}
		expect(OP_SEMICOLON);
	}

	EvalResult parse_optional_initializer()
	{
		if (!consume(OP_ASS)) return EvalResult();
		return parse_expression();
	}

	Binding* declare_one(const DeclSpecs& specs,
	                     TypePtr base,
	                     const Declarator& declarator,
	                     const EvalResult& init,
	                     bool function_definition)
	{
		const QualifiedName& qname = declarator_name(declarator);
		Scope* target = qname.qualifier != NULL ? qname.qualifier : current_scope();
		TypePtr type = apply_declarator(declarator, base);
		if (specs.typedef_decl)
			return add_or_update_alias(target, qname.name, type);
		if (specs.constexpr_decl && !is_reference_type(type))
			type = make_cv(type, CV_CONST);
		if (type->kind == TypeKind::Function || function_definition)
			return add_or_update_value(target, BindingKind::Function, qname.name, type);
		Binding* variable =
			add_or_update_value(target, BindingKind::Variable, qname.name, type);
		if ((specs.constexpr_decl || type_has_const(type)) && init.valid)
		{
			variable->has_constant = true;
			variable->constant_value = init.value;
		}
		return variable;
	}

	void parse_function_body(Binding* function, const Declarator& declarator)
	{
		Scope* function_scope =
			create_child_scope(current_scope(), ScopeKind::Function, function->name);
		const Suffix* suffix = declarator_function_suffix(declarator);
		if (suffix != NULL)
		{
			for (size_t i = 0; i < suffix->parameters.size(); ++i)
			{
				if (!suffix->parameters[i].name.empty())
					add_binding(function_scope,
					            BindingKind::Parameter,
					            suffix->parameters[i].name,
					            suffix->parameters[i].type);
			}
		}
		scopes_.push_back(function_scope);
		parse_compound_statement();
		scopes_.pop_back();
	}

	void parse_compound_statement()
	{
		expect(OP_LBRACE);
		Scope* block = create_child_scope(current_scope(), ScopeKind::Block, "");
		scopes_.push_back(block);
		while (!at(OP_RBRACE)) parse_block_item();
		scopes_.pop_back();
		expect(OP_RBRACE);
	}

	void parse_block_item()
	{
		if (at(OP_LBRACE))
		{
			parse_compound_statement();
			return;
		}
		if (at(KW_STATIC_ASSERT))
		{
			parse_static_assert();
			return;
		}
		if (starts_declaration())
		{
			size_t save = pos_;
			try
			{
				parse_simple_or_function_declaration();
				return;
			}
			catch (const exception&)
			{
				pos_ = save;
			}
		}
		skip_statement();
	}

	bool starts_declaration()
	{
		if (at(KW_TYPEDEF) || at(KW_CONSTEXPR) ||
		    (pos_ < tokens_.size() &&
		     tokens_[pos_].kind == posttoken::TokenKind::Simple &&
		     (is_storage_or_function_specifier(tokens_[pos_].type) ||
		      is_cv_token(tokens_[pos_].type) ||
		      is_builtin_type_token(tokens_[pos_].type))))
			return true;
		if (at(KW_DECLTYPE) || at(KW_STRUCT) || at(KW_CLASS) ||
		    at(KW_UNION) || at(KW_ENUM))
			return true;
		if (!at_identifier()) return false;
		TypePtr type;
		size_t save = pos_;
		const bool ok = try_parse_type_name(type);
		pos_ = save;
		return ok;
	}

	void skip_statement()
	{
		if (at(OP_LBRACE))
		{
			parse_compound_statement();
			return;
		}
		int paren = 0;
		int square = 0;
		while (!at_eof())
		{
			if (paren == 0 && square == 0 && consume(OP_SEMICOLON))
				return;
			if (paren == 0 && square == 0 && at(OP_RBRACE))
				return;
			if (consume(OP_LPAREN))
				++paren;
			else if (consume(OP_RPAREN))
				--paren;
			else if (consume(OP_LSQUARE))
				++square;
			else if (consume(OP_RSQUARE))
				--square;
			else if (at(OP_LBRACE))
			{
				parse_compound_statement();
				return;
			}
			else
				++pos_;
		}
	}

	DeclSpecs parse_decl_specifier_seq(bool type_id_context)
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

	bool at_simple_ignored_specifier() const
	{ return pos_ < tokens_.size() && tokens_[pos_].kind == posttoken::TokenKind::Simple && is_storage_or_function_specifier(tokens_[pos_].type); }

	bool at_simple_cv() const
	{ return pos_ < tokens_.size() && tokens_[pos_].kind == posttoken::TokenKind::Simple && is_cv_token(tokens_[pos_].type); }

	bool at_simple_builtin() const
	{ return pos_ < tokens_.size() && tokens_[pos_].kind == posttoken::TokenKind::Simple && is_builtin_type_token(tokens_[pos_].type); }

	unsigned consume_cv_flag()
	{
		if (consume(KW_CONST)) return CV_CONST;
		expect(KW_VOLATILE);
		return CV_VOLATILE;
	}

	bool starts_class_key() const
	{ return at(KW_STRUCT) || at(KW_CLASS) || at(KW_UNION); }

	TypePtr type_from_decl_specs(const DeclSpecs& specs)
	{
		TypePtr type = specs.named_type.get() != NULL ? specs.named_type :
			make_fundamental(fundamental_from_specs(specs.builtin));
		return make_cv(type, specs.cv);
	}

	TypePtr parse_type_id()
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

	TypePtr parse_decltype_specifier()
	{
		expect(KW_DECLTYPE);
		expect(OP_LPAREN);
		bool parenthesized = false;
		if (consume(OP_LPAREN))
			parenthesized = true;
		QualifiedName name = parse_id_expression_name();
		Binding* binding = resolve_name(name, LOOKUP_VALUE);
		if (binding == NULL)
			throw runtime_error("decltype target not found");
		if (parenthesized)
			expect(OP_RPAREN);
		expect(OP_RPAREN);
		if (parenthesized && binding->kind != BindingKind::Function)
			return make_lvalue_reference(binding->type);
		return binding->type;
	}

	TypePtr parse_class_specifier()
	{
		const ETokenType key = tokens_[pos_].type;
		++pos_;
		string name;
		if (at_identifier())
			name = consume_identifier();
		if (!at(OP_LBRACE))
		{
			if (name.empty())
				throw runtime_error("anonymous class declaration is not a type");
			return add_or_update_record(current_scope(),
			                            name,
			                            class_tag(key),
			                            false,
			                            NULL);
		}
		expect(OP_LBRACE);
		const bool anonymous = name.empty();
		Scope* class_scope = NULL;
		TypePtr type;
		if (!anonymous)
		{
			type = add_or_update_record(current_scope(),
			                            name,
			                            class_tag(key),
			                            true,
			                            NULL);
			class_scope = type->scope;
			if (class_scope == NULL)
			{
				class_scope =
					create_child_scope(current_scope(), ScopeKind::Class, name);
				type->scope = class_scope;
			}
		}
		else
		{
			name = "__anonymous_union_type__" +
			       to_string(tu_.anonymous_counter++) + "_" +
			       to_string(pos_after_anonymous_class_hint());
			class_scope = create_child_scope(current_scope(), ScopeKind::Class, name);
			type = make_record_type(name, class_tag(key), true, class_scope);
		}
		scopes_.push_back(class_scope);
		while (!at(OP_RBRACE))
			parse_declaration();
		scopes_.pop_back();
		expect(OP_RBRACE);
		if (anonymous && key == KW_UNION)
			inject_anonymous_union_members(class_scope);
		type->complete = true;
		return type;
	}

	size_t pos_after_anonymous_class_hint() const
	{
		size_t p = pos_;
		int depth = 1;
		while (p < tokens_.size() && depth > 0)
		{
			if (tokens_[p].kind == posttoken::TokenKind::Simple &&
			    tokens_[p].type == OP_LBRACE)
				++depth;
			else if (tokens_[p].kind == posttoken::TokenKind::Simple &&
			         tokens_[p].type == OP_RBRACE)
				--depth;
			++p;
		}
		return p + 1;
	}

	string class_tag(ETokenType key) const
	{ return key == KW_CLASS ? "class" : (key == KW_UNION ? "union" : "struct"); }

	void inject_anonymous_union_members(Scope* class_scope)
	{
		Scope* target = class_scope->parent;
		for (size_t i = 0; i < class_scope->binding_order.size(); ++i)
		{
			Binding* member = class_scope->binding_order[i];
			if (member->kind == BindingKind::Variable)
				add_or_update_value(target,
				                    BindingKind::Variable,
				                    member->name,
				                    member->type);
		}
	}

	TypePtr parse_enum_specifier()
	{
		expect(KW_ENUM);
		bool scoped = false;
		if (consume(KW_CLASS) || consume(KW_STRUCT))
			scoped = true;
		string name;
		if (at_identifier())
			name = consume_identifier();
		EFundamentalType underlying = FT_INT;
		bool explicit_underlying = false;
		if (consume(OP_COLON))
		{
			underlying = parse_enum_underlying_type();
			explicit_underlying = true;
		}
		if (!at(OP_LBRACE))
		{
			if (name.empty())
				throw runtime_error("opaque enum requires a name");
			if (!scoped && !explicit_underlying)
				throw runtime_error("opaque unscoped enum not supported");
			return add_or_update_enum(current_scope(),
			                          name,
			                          scoped,
			                          underlying,
			                          true,
			                          scoped);
		}
		TypePtr type = add_or_update_enum(current_scope(),
		                                  name,
		                                  scoped,
		                                  underlying,
		                                  true,
		                                  scoped);
		Scope* enum_scope = scoped ? type->scope : current_scope();
		expect(OP_LBRACE);
		uint64_t next_value = 0;
		while (!at(OP_RBRACE))
		{
			string enumerator = consume_identifier();
			uint64_t value = next_value;
			if (consume(OP_ASS))
				value = parse_expression().value;
			Binding* binding = add_binding(enum_scope,
			                               BindingKind::Enumerator,
			                               enumerator,
			                               type);
			binding->has_constant = true;
			binding->constant_value = value;
			next_value = value + 1;
			if (!consume(OP_COMMA))
				break;
		}
		expect(OP_RBRACE);
		return type;
	}

	EFundamentalType parse_enum_underlying_type()
	{
		DeclSpecs specs = parse_decl_specifier_seq(true);
		if (specs.named_type.get() != NULL)
			return FT_INT;
		return fundamental_from_specs(specs.builtin);
	}

	bool try_parse_type_name(TypePtr& out)
	{
		size_t save = pos_;
		Scope* qualifier = NULL;
		if (starts_nested_name_specifier())
			qualifier = parse_nested_name_specifier();
		if (!at_identifier())
		{
			pos_ = save;
			return false;
		}
		string name = consume_identifier();
		Binding* binding = qualifier != NULL
			? lookup_qualified(qualifier, name, LOOKUP_TYPE)
			: lookup_unqualified(current_scope(), name, LOOKUP_TYPE);
		if (binding == NULL)
		{
			pos_ = save;
			return false;
		}
		out = binding->type;
		return true;
	}

	Declarator parse_declarator(bool abstract_allowed)
	{
		Declarator declarator;
		parse_ptr_prefix(declarator.prefix);
		parse_noptr_declarator_root(declarator, abstract_allowed);
		parse_suffixes(declarator.suffixes);
		return declarator;
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
		parse_suffixes(declarator.suffixes);
		if (declarator.prefix.empty() &&
		    declarator.suffixes.empty() &&
		    declarator.inner.get() == NULL)
			throw runtime_error("expected abstract declarator");
		return declarator;
	}

	void parse_noptr_declarator_root(Declarator& declarator,
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

	void parse_suffixes(vector<Suffix>& suffixes)
	{
		for (;;)
		{
			if (at(OP_LSQUARE))
				suffixes.push_back(parse_array_suffix());
			else if (at(OP_LPAREN))
				suffixes.push_back(parse_function_suffix());
			else
				return;
		}
	}

	Suffix parse_array_suffix()
	{
		Suffix suffix(SuffixKind::Array);
		expect(OP_LSQUARE);
		if (consume(OP_RSQUARE))
		{
			suffix.unknown_bound = true;
			return suffix;
		}
		EvalResult bound = parse_expression();
		if (!bound.valid || bound.value == 0)
			throw runtime_error("invalid array bound");
		suffix.bound = bound.value;
		expect(OP_RSQUARE);
		return suffix;
	}

	Suffix parse_function_suffix()
	{
		Suffix suffix(SuffixKind::Function);
		expect(OP_LPAREN);
		parse_parameter_clause(suffix.parameters, suffix.variadic);
		expect(OP_RPAREN);
		parse_function_suffix_tail();
		return suffix;
	}

	void parse_function_suffix_tail()
	{
		for (;;)
		{
			if (at_simple_cv() || at(OP_AMP) || at(OP_LAND))
			{
				++pos_;
				continue;
			}
			if (consume(KW_NOEXCEPT) || consume(KW_THROW))
			{
				if (at(OP_LPAREN))
					skip_balanced(OP_LPAREN, OP_RPAREN);
				continue;
			}
			break;
		}
	}

	void parse_parameter_clause(vector<ParameterInfo>& parameters, bool& variadic)
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

	ParameterInfo parse_parameter_declaration()
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
				info.type = apply_declarator(declarator, base);
				if (declarator_has_name(declarator))
					info.name = declarator_name(declarator).name;
				return info;
			}
			catch (const exception&)
			{
				pos_ = save;
			}
		}
		if (starts_abstract_declarator())
			info.type = apply_declarator(parse_abstract_declarator(), base);
		else
			info.type = base;
		return info;
	}

	bool declarator_has_name(const Declarator& declarator) const
	{
		return declarator.has_name ||
		       (declarator.inner.get() != NULL &&
		        declarator_has_name(*declarator.inner));
	}

	bool starts_declarator() const
	{ return starts_ptr_operator() || at(OP_LPAREN) || at(OP_COLON2) || at_identifier(); }

	bool starts_abstract_declarator() const
	{ return starts_ptr_operator() || at(OP_LPAREN) || at(OP_LSQUARE); }

	bool starts_ptr_operator() const
	{ return at(OP_STAR) || at(OP_AMP) || at(OP_LAND); }

	bool starts_parenthesized_abstract_declarator() const
	{
		if (!at(OP_LPAREN))
			return false;
		return lookahead(OP_STAR, 1) ||
		       lookahead(OP_AMP, 1) ||
		       lookahead(OP_LAND, 1) ||
		       lookahead(OP_LPAREN, 1) ||
		       lookahead(OP_RPAREN, 1);
	}

	EvalResult parse_expression() { return parse_equality_expression(); }

	EvalResult parse_equality_expression()
	{
		EvalResult left = parse_additive_expression();
		for (;;)
		{
			if (consume(OP_EQ))
			{
				EvalResult right = parse_additive_expression();
				left = make_integer_result(left.valid && right.valid &&
				                           left.value == right.value);
			}
			else if (consume(OP_NE))
			{
				EvalResult right = parse_additive_expression();
				left = make_integer_result(left.valid && right.valid &&
				                           left.value != right.value);
			}
			else
				return left;
		}
	}

	EvalResult parse_additive_expression()
	{
		EvalResult left = parse_multiplicative_expression();
		for (;;)
		{
			if (consume(OP_PLUS))
			{
				EvalResult right = parse_multiplicative_expression();
				left = make_integer_result(left.value + right.value,
				                           left.valid && right.valid);
			}
			else if (consume(OP_MINUS))
			{
				EvalResult right = parse_multiplicative_expression();
				left = make_integer_result(left.value - right.value,
				                           left.valid && right.valid);
			}
			else
				return left;
		}
	}

	EvalResult parse_multiplicative_expression()
	{
		EvalResult left = parse_unary_expression();
		for (;;)
		{
			if (consume(OP_STAR))
			{
				EvalResult right = parse_unary_expression();
				left = make_integer_result(left.value * right.value,
				                           left.valid && right.valid);
			}
			else if (consume(OP_DIV))
			{
				EvalResult right = parse_unary_expression();
				if (!right.valid || right.value == 0)
					throw runtime_error("invalid division in constant expression");
				left = make_integer_result(left.value / right.value, left.valid);
			}
			else if (consume(OP_MOD))
			{
				EvalResult right = parse_unary_expression();
				if (!right.valid || right.value == 0)
					throw runtime_error("invalid modulo in constant expression");
				left = make_integer_result(left.value % right.value, left.valid);
			}
			else
				return left;
		}
	}

	EvalResult parse_unary_expression()
	{
		if (consume(OP_PLUS))
			return parse_unary_expression();
		if (consume(OP_MINUS))
		{
			EvalResult inner = parse_unary_expression();
			return make_integer_result(0 - inner.value, inner.valid);
		}
		if (at(KW_SIZEOF) || at(KW_ALIGNOF))
			return parse_type_trait_expression();
		if (at(KW_STATIC_CAST))
			return parse_static_cast_expression();
		return parse_primary_expression();
	}

	EvalResult parse_type_trait_expression()
	{
		const bool is_sizeof = consume(KW_SIZEOF);
		if (!is_sizeof)
			expect(KW_ALIGNOF);
		expect(OP_LPAREN);
		TypePtr type = parse_type_id();
		expect(OP_RPAREN);
		return make_integer_result(is_sizeof ? type_size(type) : type_align(type),
		                           true);
	}

	EvalResult parse_static_cast_expression()
	{
		expect(KW_STATIC_CAST);
		expect(OP_LT);
		parse_type_id();
		expect(OP_GT);
		expect(OP_LPAREN);
		EvalResult result = parse_expression();
		expect(OP_RPAREN);
		return result;
	}

	EvalResult parse_primary_expression()
	{
		if (consume(KW_TRUE))
			return make_integer_result(1, true);
		if (consume(KW_FALSE))
			return make_integer_result(0, true);
		if (at_literal())
			return parse_literal_expression();
		if (consume(OP_LPAREN))
		{
			EvalResult inner = parse_expression();
			expect(OP_RPAREN);
			return inner;
		}
		QualifiedName name = parse_id_expression_name();
		Binding* binding = resolve_name(name, LOOKUP_VALUE);
		if (binding == NULL)
			return EvalResult();
		EvalResult result;
		result.type = binding->type;
		result.binding = binding;
		result.lvalue = binding->kind != BindingKind::Enumerator;
		if (binding->has_constant)
		{
			result.valid = true;
			result.value = binding->constant_value;
		}
		return result;
	}

	EvalResult parse_literal_expression()
	{
		string source = tokens_[pos_++].source;
		IntegerLiteralInfo info;
		if (!AnalyzeIntegerLiteral(source, info) || info.user_defined)
			return EvalResult();
		return make_integer_result(info.value, true);
	}

	EvalResult make_integer_result(uint64_t value, bool valid)
	{
		EvalResult result;
		result.valid = valid;
		result.value = value;
		result.type = make_fundamental(FT_INT);
		return result;
	}

	EvalResult make_integer_result(bool value)
	{ return make_integer_result(value ? 1 : 0, true); }

	QualifiedName parse_id_expression_name()
	{
		QualifiedName name;
		if (starts_nested_name_specifier())
			name.qualifier = parse_nested_name_specifier();
		name.name = consume_identifier();
		return name;
	}

	bool starts_nested_name_specifier() const
	{ return at(OP_COLON2) || (at_identifier() && lookahead(OP_COLON2, 1)); }

	Scope* parse_nested_name_specifier()
	{
		Scope* scope = NULL;
		if (consume(OP_COLON2))
			scope = global_scope();
		else
		{
			string root = consume_identifier();
			expect(OP_COLON2);
			scope = resolve_qualifier(
				lookup_unqualified(current_scope(), root, LOOKUP_QUALIFIER));
		}
		if (scope == NULL)
			throw runtime_error("qualified lookup root not found");
		while (at_identifier() && lookahead(OP_COLON2, 1))
		{
			string component = consume_identifier();
			expect(OP_COLON2);
			scope = resolve_qualifier(
				lookup_qualified(scope, component, LOOKUP_QUALIFIER));
			if (scope == NULL)
				throw runtime_error("qualified lookup component not found");
		}
		return scope;
	}

	Scope* parse_qualified_namespace_specifier()
	{
		Scope* qualifier = NULL;
		if (starts_nested_name_specifier())
			qualifier = parse_nested_name_specifier();
		string name = consume_identifier();
		Binding* binding = qualifier != NULL
			? lookup_qualified(qualifier, name, LOOKUP_NAMESPACE)
			: lookup_unqualified(current_scope(), name, LOOKUP_NAMESPACE);
		Scope* scope = resolve_qualifier(binding);
		if (scope == NULL || scope->kind != ScopeKind::Namespace)
			throw runtime_error("namespace specifier not found");
		return scope;
	}

	Scope* resolve_qualifier(Binding* binding)
	{ return binding_qualifier_scope(binding); }

	Binding* resolve_name(const QualifiedName& name, int mask)
	{
		if (name.qualifier != NULL)
			return lookup_qualified(name.qualifier, name.name, mask);
		return lookup_unqualified(current_scope(), name.name, mask);
	}

	Binding* add_or_update_alias(Scope* scope,
	                             const string& name,
	                             TypePtr type)
	{
		Binding* existing = find_owned_binding(scope, name, BindingKind::TypeAlias);
		if (existing != NULL)
		{
			existing->type = type;
			existing->target_scope = type.get() != NULL ? type->scope : NULL;
			return existing;
		}
		Binding* binding = add_binding(scope, BindingKind::TypeAlias, name, type);
		binding->target_scope = type.get() != NULL ? type->scope : NULL;
		return binding;
	}

	Binding* add_or_update_value(Scope* scope,
	                             BindingKind kind,
	                             const string& name,
	                             TypePtr type)
	{
		Binding* existing = find_owned_binding(scope, name, kind);
		if (existing != NULL)
		{
			existing->type = type;
			return existing;
		}
		return add_binding(scope, kind, name, type);
	}

	TypePtr add_or_update_record(Scope* scope,
	                             const string& name,
	                             const string& tag,
	                             bool complete,
	                             Scope* class_scope)
	{
		Binding* existing = find_owned_binding(scope, name, BindingKind::Type);
		if (existing != NULL && existing->type->kind == TypeKind::Record)
		{
			existing->type->complete = existing->type->complete || complete;
			if (class_scope != NULL)
				existing->type->scope = class_scope;
			return existing->type;
		}
		TypePtr type = make_record_type(name, tag, complete, class_scope);
		Binding* binding = add_binding(scope, BindingKind::Type, name, type);
		binding->target_scope = class_scope;
		return type;
	}

	TypePtr add_or_update_enum(Scope* scope,
	                           const string& name,
	                           bool scoped,
	                           EFundamentalType underlying,
	                           bool complete,
	                           bool create_scope)
	{
		Binding* existing = find_owned_binding(scope, name, BindingKind::Type);
		if (existing != NULL && existing->type->kind == TypeKind::Enum)
		{
			if (existing->type->enum_underlying != underlying)
				throw runtime_error("conflicting enum underlying type");
			existing->type->complete = existing->type->complete || complete;
			if (create_scope && existing->type->scope == NULL)
				existing->type->scope =
					create_child_scope(scope, ScopeKind::Enum, name);
			return existing->type;
		}
		Scope* enum_scope = create_scope
			? create_child_scope(scope, ScopeKind::Enum, name)
			: NULL;
		TypePtr type = make_enum_type(name, scoped, underlying, complete, enum_scope);
		Binding* binding = add_binding(scope, BindingKind::Type, name, type);
		binding->target_scope = enum_scope;
		return type;
	}

	void skip_balanced(ETokenType open, ETokenType close)
	{
		expect(open);
		int depth = 1;
		while (depth > 0 && !at_eof())
		{
			if (consume(open))
				++depth;
			else if (consume(close))
				--depth;
			else
				++pos_;
		}
	}
};

}  // namespace

TranslationUnit analyze_source_file(const string& srcfile,
                                    const Options& options)
{
	pa10::Options pa10_options;
	pa10_options.preprocess = options.preprocess;
	vector<Token> tokens =
		pa10::internal::collect_source_tokens(srcfile, pa10_options);

	pa10::internal::Parser syntax_parser(tokens);
	syntax_parser.parse_translation_unit();

	TranslationUnit tu;
	tu.srcfile = srcfile;
	tu.global_scope.reset(new Scope(ScopeKind::Namespace, "", NULL));
	Parser parser(tu, tokens);
	parser.parse_translation_unit();
	return tu;
}

}  // namespace pa11
