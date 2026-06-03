#include "pa10_parser_internal.h"

#include <stdexcept>

using namespace std;

namespace pa10 {
namespace internal {

namespace {

bool mock_type_name(const string& name)
{
	return name.find('C') != string::npos ||
	       name.find('T') != string::npos ||
	       name.find('Y') != string::npos ||
	       name.find('E') != string::npos;
}

string unqualified_type_key(const string& name)
{
	string stem = name;
	size_t colon = stem.rfind("::");
	if (colon != string::npos)
		stem = stem.substr(colon + 2);
	size_t end = stem.find('<');
	if (end != string::npos)
		stem = stem.substr(0, end);
	if (!stem.empty() && stem[0] == '~')
		stem = stem.substr(1);
	return stem;
}

string qualifier_type_key(const string& name)
{
	size_t colon = name.rfind("::");
	if (colon == string::npos)
		return "";
	return unqualified_type_key(name.substr(0, colon));
}

bool has_matching_angle(const vector<Token>& tokens, size_t p)
{
	if (p >= tokens.size() ||
	    tokens[p].kind != posttoken::TokenKind::Simple ||
	    tokens[p].type != OP_LT)
		return false;
	int depth = 0;
	int paren = 0;
	int square = 0;
	int brace = 0;
	while (p < tokens.size())
	{
		if (tokens[p].kind == posttoken::TokenKind::EndOfFile ||
		    (tokens[p].kind == posttoken::TokenKind::Simple &&
		     tokens[p].type == OP_SEMICOLON) ||
		    (depth == 0 && paren == 0 && square == 0 && brace == 0 &&
		     tokens[p].kind == posttoken::TokenKind::Simple &&
		     (tokens[p].type == OP_RPAREN || tokens[p].type == OP_RBRACE)))
			return false;
		if (tokens[p].kind == posttoken::TokenKind::Simple)
		{
			if (tokens[p].type == OP_LPAREN)
				++paren;
			else if (tokens[p].type == OP_RPAREN)
				--paren;
			else if (tokens[p].type == OP_LSQUARE)
				++square;
			else if (tokens[p].type == OP_RSQUARE)
				--square;
			else if (tokens[p].type == OP_LBRACE)
				++brace;
			else if (tokens[p].type == OP_RBRACE)
				--brace;
			else if (paren == 0 && square == 0 && brace == 0 &&
			         tokens[p].type == OP_LT)
				++depth;
			else if (paren == 0 && square == 0 && brace == 0 &&
			         tokens[p].type == OP_GT)
			{
				--depth;
				if (depth == 0)
					return true;
			}
		}
		++p;
	}
	return false;
}

bool matching_angle_end(const vector<Token>& tokens, size_t p, size_t& end)
{
	if (!has_matching_angle(tokens, p))
		return false;
	int depth = 0;
	while (p < tokens.size())
	{
		if (tokens[p].kind == posttoken::TokenKind::Simple &&
		    tokens[p].type == OP_LT)
			++depth;
		else if (tokens[p].kind == posttoken::TokenKind::Simple &&
		         tokens[p].type == OP_GT)
		{
			--depth;
			if (depth == 0)
			{
				end = p + 1;
				return true;
			}
		}
		++p;
	}
	return false;
}

bool angle_text_allows_template_id(const vector<Token>& tokens, size_t begin, size_t end)
{
	int depth = 0;
	for (size_t i = begin; i < end && i < tokens.size(); ++i)
	{
		if (tokens[i].kind != posttoken::TokenKind::Simple)
			continue;
		if (tokens[i].type == OP_LT)
			++depth;
		else if (tokens[i].type == OP_GT)
			--depth;
		else if (depth == 1 && (tokens[i].type == OP_LOR ||
		                        tokens[i].type == OP_LAND ||
		                        tokens[i].type == OP_QMARK ||
		                        tokens[i].type == OP_COLON))
			return false;
	}
	return true;
}

void skip_template_text_scan(const vector<Token>& tokens, size_t& p)
{
	if (p >= tokens.size() ||
	    tokens[p].kind != posttoken::TokenKind::Simple ||
	    tokens[p].type != OP_LT)
		return;
	int depth = 0;
	while (p < tokens.size())
	{
		if (tokens[p].kind == posttoken::TokenKind::Simple &&
		    tokens[p].type == OP_LT)
			++depth;
		else if (tokens[p].kind == posttoken::TokenKind::Simple &&
		         tokens[p].type == OP_GT)
		{
			--depth;
			if (depth == 0)
			{
				++p;
				return;
			}
		}
		++p;
	}
}

string scan_unqualified_name(const vector<Token>& tokens, size_t& p)
{
	if (p >= tokens.size())
		return "";
	if (tokens[p].kind == posttoken::TokenKind::Simple &&
	    tokens[p].type == OP_COMPL)
	{
		++p;
		if (p < tokens.size() && tokens[p].kind == posttoken::TokenKind::Identifier)
			return "~" + tokens[p++].source;
		return "~";
	}
	if (tokens[p].kind == posttoken::TokenKind::Simple &&
	    tokens[p].type == KW_OPERATOR)
	{
		++p;
		return "operator";
	}
	if (tokens[p].kind != posttoken::TokenKind::Identifier)
		return "";
	string name = tokens[p++].source;
	if (p < tokens.size() &&
	    tokens[p].kind == posttoken::TokenKind::Simple &&
	    tokens[p].type == OP_LT)
		skip_template_text_scan(tokens, p);
	return name;
}

void skip_balanced_at(const vector<Token>& tokens,
                      size_t& p,
                      ETokenType open,
                      ETokenType close)
{
	if (p >= tokens.size() ||
	    tokens[p].kind != posttoken::TokenKind::Simple ||
	    tokens[p].type != open)
		return;
	int depth = 1;
	++p;
	while (depth > 0 && p < tokens.size())
	{
		if (tokens[p].kind == posttoken::TokenKind::Simple &&
		    tokens[p].type == open)
			++depth;
		else if (tokens[p].kind == posttoken::TokenKind::Simple &&
		         tokens[p].type == close)
			--depth;
		++p;
	}
}

void skip_attributes_at(const vector<Token>& tokens, size_t& p)
{
	while (p < tokens.size())
	{
		if (tokens[p].kind == posttoken::TokenKind::Simple &&
		    tokens[p].type == KW_ALIGNAS)
		{
			++p;
			skip_balanced_at(tokens, p, OP_LPAREN, OP_RPAREN);
			continue;
		}
		if (p + 1 < tokens.size() &&
		    tokens[p].kind == posttoken::TokenKind::Simple &&
		    tokens[p].type == OP_LSQUARE &&
		    tokens[p + 1].kind == posttoken::TokenKind::Simple &&
		    tokens[p + 1].type == OP_LSQUARE)
		{
			p += 2;
			skip_balanced_at(tokens, p, OP_LSQUARE, OP_RSQUARE);
			continue;
		}
		if (tokens[p].kind == posttoken::TokenKind::Identifier &&
		    tokens[p].source == "__attribute__")
		{
			++p;
			skip_balanced_at(tokens, p, OP_LPAREN, OP_RPAREN);
			continue;
		}
		break;
	}
}

}  // namespace

Parser::Parser(const vector<Token>& tokens)
	: tokens_(tokens),
	  pos_(0),
	  class_depth_(0),
	  expression_angle_stop_(0)
{
	push_scope();
}

const Token& Parser::current() const
{
	return at(pos_);
}

const Token& Parser::at(size_t pos) const
{
	if (pos >= tokens_.size())
		return tokens_.back();
	return tokens_[pos];
}

bool Parser::eof() const
{
	return current().kind == posttoken::TokenKind::EndOfFile;
}

bool Parser::simple(ETokenType type) const
{
	return simple_at(pos_, type);
}

bool Parser::simple_at(size_t pos, ETokenType type) const
{
	return at(pos).kind == posttoken::TokenKind::Simple && at(pos).type == type;
}

bool Parser::identifier() const
{
	return current().kind == posttoken::TokenKind::Identifier;
}

bool Parser::literal() const
{
	return current().kind == posttoken::TokenKind::Literal;
}

bool Parser::consume(ETokenType type)
{
	if (!simple(type))
		return false;
	++pos_;
	return true;
}

bool Parser::consume_identifier(string& out)
{
	if (!identifier())
		return false;
	out = current().source;
	++pos_;
	return true;
}

bool Parser::consume_literal(string& out)
{
	if (!literal())
		return false;
	out = current().source;
	++pos_;
	return true;
}

const Token& Parser::expect(ETokenType type)
{
	if (!simple(type))
		throw runtime_error("unexpected token '" + current().source + "'");
	const Token& token = current();
	++pos_;
	return token;
}

string Parser::expect_identifier()
{
	string out;
	if (!consume_identifier(out))
		throw runtime_error("expected identifier before '" + current().source + "'");
	return out;
}

string Parser::expect_literal()
{
	string out;
	if (!consume_literal(out))
		throw runtime_error("expected literal");
	return out;
}

void Parser::skip_balanced(ETokenType open, ETokenType close)
{
	expect(open);
	int depth = 1;
	while (depth > 0)
	{
		if (eof())
			throw runtime_error("unclosed balanced sequence");
		if (simple(open))
			++depth;
		else if (simple(close))
			--depth;
		++pos_;
	}
}

bool Parser::starts_attribute() const
{
	if (simple(KW_ALIGNAS))
		return true;
	if (simple_at(pos_, OP_LSQUARE) && simple_at(pos_ + 1, OP_LSQUARE))
		return true;
	if (identifier() && current().source == "__attribute__")
		return true;
	return false;
}

void Parser::skip_attributes()
{
	while (starts_attribute())
	{
		if (simple(KW_ALIGNAS))
		{
			++pos_;
			if (simple(OP_LPAREN))
				skip_balanced(OP_LPAREN, OP_RPAREN);
			continue;
		}
		if (simple(OP_LSQUARE))
		{
			++pos_;
			skip_balanced(OP_LSQUARE, OP_RSQUARE);
			expect(OP_RSQUARE);
			continue;
		}
		++pos_;
		if (simple(OP_LPAREN))
			skip_balanced(OP_LPAREN, OP_RPAREN);
	}
}

void Parser::push_scope()
{
	scopes_.push_back(Scope());
}

void Parser::push_template_scope()
{
	push_scope();
	scopes_.back().template_parameter_scope = true;
}

void Parser::push_namespace_scope(const string& name)
{
	push_scope();
	scopes_.back().namespace_name = name;
	if (!name.empty())
		import_namespace_types(name);
}

void Parser::push_class_scope(const string& name)
{
	push_scope();
	scopes_.back().class_name = unqualified_type_key(name);
	import_class_member_types(name);
}

void Parser::pop_scope()
{
	if (scopes_.size() <= 1)
		return;
	scopes_.pop_back();
}

string Parser::current_namespace_name() const
{
	return namespace_stack_.empty() ? string() : namespace_stack_.back();
}

string Parser::qualify_namespace_name(const string& name) const
{
	if (name.empty())
		return "";
	if (name.size() >= 2 && name.substr(0, 2) == "::")
		return name.substr(2);
	if (name.find("::") != string::npos)
		return name;
	const string current_ns = current_namespace_name();
	return current_ns.empty() ? name : current_ns + "::" + name;
}

string Parser::resolve_namespace_name(const string& name) const
{
	string key = name;
	if (key.size() >= 2 && key.substr(0, 2) == "::")
		key = key.substr(2);
	map<string, string>::const_iterator alias = namespace_aliases_.find(key);
	if (alias != namespace_aliases_.end())
		return alias->second;
	if (namespace_types_.count(key) != 0)
		return key;

	const string qualified = qualify_namespace_name(key);
	alias = namespace_aliases_.find(qualified);
	if (alias != namespace_aliases_.end())
		return alias->second;
	if (namespace_types_.count(qualified) != 0)
		return qualified;
	return qualified;
}

void Parser::import_namespace_types(const string& name)
{
	const string resolved = resolve_namespace_name(name);
	map<string, set<string> >::const_iterator it = namespace_types_.find(resolved);
	if (it == namespace_types_.end())
		return;
	for (set<string>::const_iterator type = it->second.begin();
	     type != it->second.end();
	     ++type)
	{
		scopes_.back().types.insert(*type);
		if (!scopes_.back().class_name.empty())
			class_member_types_[scopes_.back().class_name].insert(*type);
	}
}

void Parser::record_namespace_alias(const string& name, const string& target)
{
	if (name.empty())
		return;
	const string resolved = resolve_namespace_name(target);
	namespace_aliases_[name] = resolved;
	const string qualified = qualify_namespace_name(name);
	namespace_aliases_[qualified] = resolved;
}

void Parser::import_class_member_types(const string& name)
{
	const string key = unqualified_type_key(name);
	map<string, set<string> >::const_iterator it = class_member_types_.find(key);
	if (it == class_member_types_.end())
		return;
	for (set<string>::const_iterator type = it->second.begin();
	     type != it->second.end();
	     ++type)
		scopes_.back().types.insert(*type);
}

void Parser::queue_compound_type_imports_for_qualified_name(const string& name)
{
	const string key = qualifier_type_key(name);
	if (!key.empty())
		pending_compound_type_imports_.push_back(key);
}

void Parser::queue_compound_type_name_from_qualified_name(const string& name)
{
	if (name.find("::") == string::npos)
		return;
	const string key = unqualified_type_key(name);
	if (!key.empty())
		pending_compound_type_names_.push_back(key);
}

void Parser::add_type_name(const string& name)
{
	if (name.empty())
		return;
	size_t target = scopes_.empty() ? 0 : scopes_.size() - 1;
	while (target > 0 && scopes_[target].template_parameter_scope)
		--target;
	scopes_[target].types.insert(name);
	if (!scopes_[target].namespace_name.empty())
		namespace_types_[scopes_[target].namespace_name].insert(name);
	if (!scopes_[target].class_name.empty())
		class_member_types_[scopes_[target].class_name].insert(name);
}

void Parser::add_template_type_name(const string& name)
{
	if (!name.empty())
		scopes_.back().types.insert(name);
}

void Parser::add_value_name(const string& name)
{
	if (!name.empty())
		scopes_.back().values.insert(name);
}

void Parser::add_namespace_name(const string& name)
{
	if (!name.empty())
		scopes_.back().namespaces.insert(name);
}

bool Parser::value_shadows_type(const string& name) const
{
	for (vector<Scope>::const_reverse_iterator it = scopes_.rbegin();
	     it != scopes_.rend();
	     ++it)
	{
		if (it->values.count(name) != 0)
			return true;
		if (it->types.count(name) != 0)
			return false;
	}
	return false;
}

bool Parser::is_type_name(const string& name) const
{
	if (name.empty())
		return false;
	for (vector<Scope>::const_reverse_iterator it = scopes_.rbegin();
	     it != scopes_.rend();
	     ++it)
	{
		if (it->values.count(name) != 0)
			return false;
		if (it->types.count(name) != 0)
			return true;
	}
	if (name.find("::") != string::npos)
		return true;
	if (name.find('<') != string::npos)
		return true;
	if (mock_type_name(name))
		return true;
	return false;
}

Ast Parser::parse_translation_unit()
{
	Ast root = make_ast("translation-unit");
	while (!eof())
	{
		skip_attributes();
		if (eof())
			break;
		add_child(root, parse_declaration());
	}
	return root;
}

string Parser::parse_balanced_text(ETokenType open, ETokenType close)
{
	string out;
	expect(open);
	out += TokenTypeToStringMap.at(open) == "OP_LPAREN" ? "(" :
	       TokenTypeToStringMap.at(open) == "OP_LSQUARE" ? "[" : "{";
	int depth = 1;
	while (depth > 0)
	{
		if (eof())
			throw runtime_error("unclosed text sequence");
		if (simple(open))
			++depth;
		else if (simple(close))
			--depth;
		if (depth == 0)
		{
			out += close == OP_RPAREN ? ")" : close == OP_RSQUARE ? "]" : "}";
			++pos_;
			break;
		}
		out += current().source;
		++pos_;
	}
	return out;
}

bool Parser::consume_close_angle()
{
	if (!simple(OP_GT))
		return false;
	++pos_;
	return true;
}

bool Parser::starts_template_argument_list() const
{
	return simple(OP_LT);
}

string Parser::parse_template_id_text(const string& base)
{
	string out = base;
	string previous;
	expect(OP_LT);
	out += "<";
	previous = "<";
	int angle = 1;
	int paren = 0;
	int square = 0;
	int brace = 0;
	while (angle > 0)
	{
		if (eof())
			throw runtime_error("unclosed template-id");
		if (simple(OP_LPAREN))
			++paren;
		else if (simple(OP_RPAREN))
			--paren;
		else if (simple(OP_LSQUARE))
			++square;
		else if (simple(OP_RSQUARE))
			--square;
		else if (simple(OP_LBRACE))
			++brace;
		else if (simple(OP_RBRACE))
			--brace;
		if (paren == 0 && square == 0 && brace == 0 && simple(OP_LT) &&
		    current_less_starts_template_id())
		{
			++angle;
			out += "<";
			previous = "<";
			++pos_;
			continue;
		}
		if (paren == 0 && square == 0 && brace == 0 && simple(OP_GT))
		{
			--angle;
			out += ">";
			previous = ">";
			++pos_;
			continue;
		}
		if (previous == "const" ||
		    previous == "volatile" ||
		    previous == "typename" ||
		    previous == "template" ||
		    previous == "struct" ||
		    previous == "class" ||
		    previous == "enum")
			out += " ";
		out += current().source;
		previous = current().source;
		++pos_;
	}
	return out;
}

string Parser::parse_unqualified_id_text(bool allow_template_id)
{
	if (consume(KW_OPERATOR))
	{
		if (simple(KW_NEW))
		{
			++pos_;
			if (consume(OP_LSQUARE))
			{
				expect(OP_RSQUARE);
				return "operatornew[]";
			}
			return "operatornew";
		}
		if (simple(KW_DELETE))
		{
			++pos_;
			if (consume(OP_LSQUARE))
			{
				expect(OP_RSQUARE);
				return "operatordelete[]";
			}
			return "operatordelete";
		}
		if (starts_type_id())
		{
			string text = "operator" + parse_type_name_text();
			return text;
		}
		string op = current().source;
		++pos_;
		if (op == "(")
		{
			expect(OP_RPAREN);
			return "operator()";
		}
		if (op == "[")
		{
			expect(OP_RSQUARE);
			return "operator[]";
		}
		return "operator" + op;
	}
	if (consume(OP_COMPL))
	{
		string name = parse_unqualified_id_text();
		return "~" + name;
	}
	string name = expect_identifier();
	if (allow_template_id && starts_template_argument_list())
	{
		if (is_type_name(name))
			name = parse_template_id_text(name);
		else
		{
			size_t angle_end = 0;
			if (matching_angle_end(tokens_, pos_, angle_end) &&
			    angle_text_allows_template_id(tokens_, pos_, angle_end) &&
			    at(angle_end).kind != posttoken::TokenKind::Identifier)
				name = parse_template_id_text(name);
		}
	}
	return name;
}

string Parser::parse_qualified_suffix_text(string base)
{
	while (consume(OP_COLON2))
	{
		if (consume(KW_TEMPLATE))
		{
		}
		if (simple(KW_OPERATOR) &&
		    (at(pos_ + 1).kind == posttoken::TokenKind::Identifier ||
		     simple_at(pos_ + 1, OP_COLON2) ||
		     simple_at(pos_ + 1, KW_TYPENAME) ||
		     (at(pos_ + 1).kind == posttoken::TokenKind::Simple &&
		      is_builtin_type(at(pos_ + 1).type))))
		{
			consume(KW_OPERATOR);
			base += "::operator " + parse_type_name_text();
			continue;
		}
		base += "::" + parse_unqualified_id_text();
	}
	return base;
}

string Parser::parse_id_expression_text()
{
	string base;
	if (consume(OP_COLON2))
		base = "::" + parse_unqualified_id_text();
	else
		base = parse_unqualified_id_text();
	return parse_qualified_suffix_text(base);
}

string Parser::parse_type_name_text()
{
	if (consume(KW_TYPENAME))
	{
		string name = parse_id_expression_text();
		return name;
	}
	if (simple(KW_DECLTYPE))
	{
		++pos_;
		return "decltype" + parse_balanced_text(OP_LPAREN, OP_RPAREN);
	}
	if (simple(KW_STRUCT) || simple(KW_CLASS) || simple(KW_UNION) || simple(KW_ENUM))
	{
		++pos_;
		return parse_id_expression_text();
	}
	if (current().kind == posttoken::TokenKind::Simple && is_builtin_type(current().type))
	{
		string text = current().source;
		++pos_;
		return text;
	}
	return parse_id_expression_text();
}

Ast Parser::make_id_expression(const string& text) const
{
	return make_ast("id-expression " + text);
}

Ast Parser::make_binary(ETokenType op,
                        const string& text,
                        Ast lhs,
                        Ast rhs) const
{
	Ast node = make_ast("binary-expression " + op_leaf(op, text));
	add_child(node, lhs);
	add_child(node, rhs);
	return node;
}

bool Parser::starts_expression() const
{
	return identifier() ||
	       literal() ||
	       simple(OP_LPAREN) ||
	       simple(OP_LBRACE) ||
	       simple(OP_LSQUARE) ||
	       simple(OP_INC) ||
	       simple(OP_DEC) ||
	       simple(OP_STAR) ||
	       simple(OP_AMP) ||
	       simple(OP_PLUS) ||
	       simple(OP_MINUS) ||
	       simple(OP_LNOT) ||
	       simple(OP_COMPL) ||
	       simple(KW_TRUE) ||
	       simple(KW_FALSE) ||
	       simple(KW_NULLPTR) ||
	       simple(KW_THIS) ||
	       simple(KW_SIZEOF) ||
	       simple(KW_ALIGNOF) ||
	       simple(KW_NOEXCEPT) ||
	       simple(KW_TYPEID) ||
	       simple(KW_NEW) ||
	       simple(KW_DELETE) ||
	       simple(OP_COLON2) ||
	       simple(KW_STATIC_CAST) ||
	       simple(KW_DYNAMIC_CAST) ||
	       simple(KW_CONST_CAST) ||
	       simple(KW_REINTERPET_CAST);
}

bool Parser::starts_type_id() const
{
	if (simple(KW_TYPENAME) || simple(KW_DECLTYPE))
		return true;
	if (simple(KW_STRUCT) || simple(KW_CLASS) || simple(KW_UNION) || simple(KW_ENUM))
		return true;
	if (current().kind == posttoken::TokenKind::Simple &&
	    (is_builtin_type(current().type) || is_cv_qualifier(current().type)))
		return true;
	if (identifier())
		return is_type_name(current().source) || simple_at(pos_ + 1, OP_COLON2);
	if (simple(OP_COLON2))
		return true;
	return false;
}

bool Parser::id_expression_call_follows(size_t pos) const
{
	size_t p = pos;
	if (simple_at(p, OP_COLON2))
		++p;
	string first = scan_unqualified_name(tokens_, p);
	if (first.empty())
		return false;
	while (simple_at(p, OP_COLON2))
	{
		++p;
		if (simple_at(p, KW_TEMPLATE))
			++p;
		string next = scan_unqualified_name(tokens_, p);
		if (next.empty())
			return false;
	}
	return simple_at(p, OP_LPAREN);
}

bool Parser::current_less_starts_template_id() const
{
	if (!simple(OP_LT) || pos_ == 0)
		return false;
	size_t name_pos = pos_ - 1;
	if (at(name_pos).kind == posttoken::TokenKind::Simple &&
	    at(name_pos).type == OP_GT)
		return true;
	if (at(name_pos).kind != posttoken::TokenKind::Identifier)
		return false;
	if (name_pos > 0 &&
	    at(name_pos - 1).kind == posttoken::TokenKind::Simple &&
	    at(name_pos - 1).type == KW_TEMPLATE)
		return true;
	if (is_type_name(at(name_pos).source))
		return true;
	if (value_shadows_type(at(name_pos).source))
		return false;
	if (name_pos > 0 &&
	    at(name_pos - 1).kind == posttoken::TokenKind::Simple &&
	    at(name_pos - 1).type == OP_COLON2)
		return qualified_template_name_is_type(name_pos);
	return true;
}

bool Parser::qualified_template_name_is_type(size_t name_pos) const
{
	if (at(name_pos).kind != posttoken::TokenKind::Identifier)
		return false;
	string qualifier;
	size_t p = name_pos;
	while (p >= 2 &&
	       at(p - 1).kind == posttoken::TokenKind::Simple &&
	       at(p - 1).type == OP_COLON2 &&
	       at(p - 2).kind == posttoken::TokenKind::Identifier)
	{
		qualifier = at(p - 2).source +
			(qualifier.empty() ? string() : "::" + qualifier);
		p -= 2;
	}
	if (qualifier.empty())
		return false;
	const string resolved = resolve_namespace_name(qualifier);
	map<string, set<string> >::const_iterator it = namespace_types_.find(resolved);
	return it != namespace_types_.end() &&
	       it->second.count(at(name_pos).source) != 0;
}

bool Parser::starts_declaration() const
{
	if (simple(OP_SEMICOLON) ||
	    (simple(KW_INLINE) && simple_at(pos_ + 1, KW_NAMESPACE)) ||
	    simple(KW_NAMESPACE) ||
	    simple(KW_USING) ||
	    simple(KW_TEMPLATE) ||
	    simple(KW_STATIC_ASSERT) ||
	    simple(KW_EXTERN) ||
	    simple(KW_STRUCT) ||
	    simple(KW_CLASS) ||
	    simple(KW_UNION) ||
	    simple(KW_ENUM))
		return true;
	if (current().kind == posttoken::TokenKind::Simple &&
	    is_decl_specifier_keyword(current().type))
		return true;
	if (identifier())
	{
		if (simple_at(pos_ + 1, OP_COLON2))
		{
			size_t p = pos_;
			string first = scan_unqualified_name(tokens_, p);
			while (simple_at(p, OP_COLON2))
			{
				++p;
				scan_unqualified_name(tokens_, p);
			}
			if (simple_at(p, OP_LPAREN) && !is_type_name(first))
				return false;
			return true;
		}
		return !value_shadows_type(current().source) &&
		       is_type_name(current().source);
	}
	if (simple(OP_COLON2))
	{
		size_t p = pos_ + 1;
		scan_unqualified_name(tokens_, p);
		while (simple_at(p, OP_COLON2))
		{
			++p;
			scan_unqualified_name(tokens_, p);
		}
		return !simple_at(p, OP_LPAREN);
	}
	return false;
}

bool Parser::starts_special_member() const
{
	size_t p = pos_;
	while (at(p).kind == posttoken::TokenKind::Simple &&
	       is_member_function_specifier(at(p).type))
	{
		++p;
		skip_attributes_at(tokens_, p);
	}
	if (simple_at(p, OP_COMPL) || simple_at(p, KW_OPERATOR))
		return true;
	string first = scan_unqualified_name(tokens_, p);
	if (first.empty())
		return false;
	if (simple_at(p, OP_LPAREN))
		return !class_stack_.empty() && first == class_stack_.back();
	string qualifier = first;
	while (simple_at(p, OP_COLON2))
	{
		p += 1;
		if (simple_at(p, KW_OPERATOR))
			return true;
		string next = scan_unqualified_name(tokens_, p);
		if (next.empty())
			return false;
		if (simple_at(p, OP_LPAREN))
		{
			string q = qualifier;
			size_t angle = q.find('<');
			if (angle != string::npos)
				q = q.substr(0, angle);
			size_t colon = q.rfind("::");
			if (colon != string::npos)
				q = q.substr(colon + 2);
			return next == q || (!next.empty() && next[0] == '~') ||
			       next == "operator";
		}
		qualifier += "::" + next;
	}
	return false;
}

}  // namespace internal
}  // namespace pa10
