#include "recog_support.h"

#include <algorithm>
#include <map>
#include <memory>
#include <set>
#include <sstream>
#include <stdexcept>
#include <utility>
#include <vector>

#include "posttoken_pipeline.h"
#include "posttoken_support.h"
#include "recog_grammar.h"

using namespace std;

namespace recog {
namespace {

struct RecogToken
{
	string symbol;
	string source;
	bool identifier;
	bool literal;

	RecogToken() : identifier(false), literal(false) {}
	RecogToken(const string& sym, const string& src, bool id, bool lit)
		: symbol(sym), source(src), identifier(id), literal(lit) {}
};

enum class NodeKind
{
	Symbol,
	Sequence,
	Optional,
	Star,
	Plus
};

struct Node;
typedef shared_ptr<Node> NodePtr;

struct Node
{
	NodeKind kind;
	string symbol;
	vector<NodePtr> children;
	NodePtr child;
	bool opens_angle;

	explicit Node(NodeKind k) : kind(k), opens_angle(false) {}
};

struct Rule
{
	vector<NodePtr> alternatives;
};

struct Grammar
{
	map<string, Rule> rules;
};

struct State
{
	size_t pos;
	int bracket_depth;
	vector<int> angle_stack;

	State() : pos(0), bracket_depth(0) {}
};

struct MemoKey
{
	string rule;
	State state;
};

struct SpecResult
{
	State state;
	bool saw_non_cv_type;
};

bool operator<(const State& a, const State& b)
{
	if (a.pos != b.pos)
		return a.pos < b.pos;
	if (a.bracket_depth != b.bracket_depth)
		return a.bracket_depth < b.bracket_depth;
	return a.angle_stack < b.angle_stack;
}

bool operator<(const MemoKey& a, const MemoKey& b)
{
	if (a.rule != b.rule)
		return a.rule < b.rule;
	return a.state < b.state;
}

bool operator<(const SpecResult& a, const SpecResult& b)
{
	if (a.state < b.state)
		return true;
	if (b.state < a.state)
		return false;
	return a.saw_non_cv_type < b.saw_non_cv_type;
}

NodePtr MakeNode(NodeKind kind)
{
	return NodePtr(new Node(kind));
}

NodePtr MakeSymbol(const string& symbol)
{
	NodePtr node = MakeNode(NodeKind::Symbol);
	node->symbol = symbol;
	return node;
}

string Trim(const string& s)
{
	size_t begin = 0;
	while (begin < s.size() && isspace(static_cast<unsigned char>(s[begin])))
		++begin;
	size_t end = s.size();
	while (end > begin && isspace(static_cast<unsigned char>(s[end - 1])))
		--end;
	return s.substr(begin, end - begin);
}

bool EndsWith(const string& s, char c)
{
	return !s.empty() && s[s.size() - 1] == c;
}

bool IsRuleHeader(const string& line)
{
	if (line.empty() || isspace(static_cast<unsigned char>(line[0])))
		return false;
	const string trimmed = Trim(line);
	return EndsWith(trimmed, ':');
}

vector<string> TokenizeBody(const string& body)
{
	vector<string> out;
	for (size_t i = 0; i < body.size();)
	{
		if (isspace(static_cast<unsigned char>(body[i])))
		{
			++i;
			continue;
		}
		if (body[i] == '(' || body[i] == ')' ||
		    body[i] == '?' || body[i] == '*' || body[i] == '+')
		{
			out.push_back(body.substr(i, 1));
			++i;
			continue;
		}
		size_t j = i;
		while (j < body.size() &&
		       !isspace(static_cast<unsigned char>(body[j])) &&
		       body[j] != '(' && body[j] != ')' &&
		       body[j] != '?' && body[j] != '*' && body[j] != '+')
			++j;
		out.push_back(body.substr(i, j - i));
		i = j;
	}
	return out;
}

class BodyParser
{
public:
	explicit BodyParser(const vector<string>& tokens)
		: tokens_(tokens), pos_(0)
	{
	}

	NodePtr parse()
	{
		NodePtr node = parse_sequence();
		if (pos_ != tokens_.size())
			throw runtime_error("trailing grammar tokens");
		return node;
	}

private:
	const vector<string>& tokens_;
	size_t pos_;

	NodePtr parse_sequence()
	{
		NodePtr seq = MakeNode(NodeKind::Sequence);
		while (pos_ < tokens_.size() && tokens_[pos_] != ")")
			seq->children.push_back(parse_postfix());
		return seq;
	}

	NodePtr parse_postfix()
	{
		NodePtr node = parse_atom();
		if (pos_ >= tokens_.size())
			return node;
		NodeKind kind = NodeKind::Symbol;
		if (tokens_[pos_] == "?")
			kind = NodeKind::Optional;
		else if (tokens_[pos_] == "*")
			kind = NodeKind::Star;
		else if (tokens_[pos_] == "+")
			kind = NodeKind::Plus;
		else
			return node;
		++pos_;
		NodePtr wrapper = MakeNode(kind);
		wrapper->child = node;
		return wrapper;
	}

	NodePtr parse_atom()
	{
		if (pos_ >= tokens_.size())
			throw runtime_error("unexpected end of grammar body");
		if (tokens_[pos_] == "(")
		{
			++pos_;
			NodePtr group = parse_sequence();
			if (pos_ >= tokens_.size() || tokens_[pos_] != ")")
				throw runtime_error("unmatched grammar group");
			++pos_;
			return group;
		}
		if (tokens_[pos_] == ")")
			throw runtime_error("unexpected grammar group close");
		return MakeSymbol(tokens_[pos_++]);
	}
};

bool IsCloseAngleNode(const NodePtr& node)
{
	return node->kind == NodeKind::Symbol &&
	       node->symbol == "close-angle-bracket";
}

void AnnotateAngleOpens(const NodePtr& node)
{
	if (!node)
		return;
	if (node->kind == NodeKind::Sequence)
	{
		for (size_t i = 0; i < node->children.size(); ++i)
		{
			NodePtr child = node->children[i];
			if (child->kind != NodeKind::Symbol || child->symbol != "OP_LT")
				continue;
			for (size_t j = i + 1; j < node->children.size(); ++j)
			{
				if (IsCloseAngleNode(node->children[j]))
				{
					child->opens_angle = true;
					break;
				}
			}
		}
		for (size_t i = 0; i < node->children.size(); ++i)
			AnnotateAngleOpens(node->children[i]);
		return;
	}
	AnnotateAngleOpens(node->child);
}

NodePtr ParseBody(const string& body)
{
	vector<string> tokens = TokenizeBody(body);
	BodyParser parser(tokens);
	NodePtr node = parser.parse();
	AnnotateAngleOpens(node);
	return node;
}

void AddAlternative(Grammar& grammar,
                    const string& rule_name,
                    const string& body)
{
	if (rule_name.empty())
		throw runtime_error("grammar body before rule");
	grammar.rules[rule_name].alternatives.push_back(ParseBody(body));
}

Grammar LoadGrammar(const vector<string>& lines)
{
	Grammar grammar;
	string current_rule;
	string pending_body;
	for (size_t i = 0; i < lines.size(); ++i)
	{
		string line = lines[i];
		if (!line.empty() && line[line.size() - 1] == '\r')
			line.erase(line.size() - 1);
		if (Trim(line).empty())
			continue;
		if (IsRuleHeader(line))
		{
			current_rule = Trim(line);
			current_rule.erase(current_rule.size() - 1);
			pending_body.clear();
			continue;
		}
		string body = Trim(line);
		bool continued = EndsWith(body, '\\');
		if (continued)
			body = Trim(body.substr(0, body.size() - 1));
		pending_body = pending_body.empty() ? body : pending_body + " " + body;
		if (!continued)
		{
			AddAlternative(grammar, current_rule, pending_body);
			pending_body.clear();
		}
	}
	if (!pending_body.empty())
		AddAlternative(grammar, current_rule, pending_body);
	return grammar;
}

bool ContainsChar(const string& text, char c)
{
	return text.find(c) != string::npos;
}

bool IsTerminalSymbol(const string& symbol)
{
	return symbol.compare(0, 3, "KW_") == 0 ||
	       symbol.compare(0, 3, "OP_") == 0 ||
	       symbol.compare(0, 3, "TT_") == 0 ||
	       symbol.compare(0, 3, "ST_") == 0;
}

bool IsNonParenToken(const RecogToken& token)
{
	return token.symbol != "OP_LPAREN" &&
	       token.symbol != "OP_RPAREN" &&
	       token.symbol != "OP_LSQUARE" &&
	       token.symbol != "OP_RSQUARE" &&
	       token.symbol != "OP_LBRACE" &&
	       token.symbol != "OP_RBRACE" &&
	       token.symbol != "ST_EOF";
}

bool IsBuiltinSimpleType(const string& symbol)
{
	static const char* const names[] = {
		"KW_CHAR", "KW_CHAR16_T", "KW_CHAR32_T", "KW_WCHAR_T",
		"KW_BOOL", "KW_SHORT", "KW_INT", "KW_LONG", "KW_SIGNED",
		"KW_UNSIGNED", "KW_FLOAT", "KW_DOUBLE", "KW_VOID", "KW_AUTO"
	};
	for (size_t i = 0; i < sizeof(names) / sizeof(names[0]); ++i)
	{
		if (symbol == names[i])
			return true;
	}
	return false;
}

bool IsNoTypeDeclSpecifier(const string& symbol)
{
	static const char* const names[] = {
		"storage-class-specifier", "function-specifier",
		"KW_FRIEND", "KW_TYPEDEF", "KW_CONSTEXPR"
	};
	for (size_t i = 0; i < sizeof(names) / sizeof(names[0]); ++i)
	{
		if (symbol == names[i])
			return true;
	}
	return false;
}

string SimpleTokenSymbol(ETokenType token_type)
{
	map<ETokenType, string>::const_iterator it =
		TokenTypeToStringMap.find(token_type);
	if (it == TokenTypeToStringMap.end())
		throw runtime_error("unknown simple token");
	return it->second;
}

void AppendPostToken(const posttoken::Token& token,
                     vector<RecogToken>& out)
{
	if (token.kind == posttoken::TokenKind::Invalid)
		throw runtime_error("invalid token");
	if (token.kind == posttoken::TokenKind::Identifier)
	{
		out.push_back(RecogToken("TT_IDENTIFIER", token.source, true, false));
		return;
	}
	if (token.kind == posttoken::TokenKind::Literal)
	{
		out.push_back(RecogToken("TT_LITERAL", token.source, false, true));
		return;
	}
	if (token.kind == posttoken::TokenKind::EndOfFile)
	{
		out.push_back(RecogToken("ST_EOF", token.source, false, false));
		return;
	}
	if (token.token_type == OP_RSHIFT)
	{
		out.push_back(RecogToken("ST_RSHIFT_1", token.source, false, false));
		out.push_back(RecogToken("ST_RSHIFT_2", token.source, false, false));
		return;
	}
	out.push_back(RecogToken(SimpleTokenSymbol(token.token_type),
	                         token.source,
	                         false,
	                         false));
}

vector<RecogToken> ConvertTokens(const vector<posttoken::Token>& tokens)
{
	vector<RecogToken> out;
	for (size_t i = 0; i < tokens.size(); ++i)
		AppendPostToken(tokens[i], out);
	return out;
}

class Parser
{
public:
	Parser(const Grammar& grammar, const vector<RecogToken>& tokens)
		: grammar_(grammar), tokens_(tokens)
	{
	}

	bool parse_translation_unit()
	{
		State start;
		vector<State> ends = parse_nonterminal("translation-unit", start);
		for (size_t i = 0; i < ends.size(); ++i)
		{
			if (ends[i].pos == tokens_.size() &&
			    ends[i].bracket_depth == 0 &&
			    ends[i].angle_stack.empty())
				return true;
		}
		return false;
	}

private:
	const Grammar& grammar_;
	const vector<RecogToken>& tokens_;
	map<MemoKey, vector<State> > memo_;
	set<MemoKey> active_;

	vector<State> parse_nonterminal(const string& name, const State& state)
	{
		if (name == "class-name")
			return parse_class_name(state);
		if (name == "enum-name")
			return parse_identifier_category(state, 'E');
		if (name == "namespace-name")
			return parse_identifier_category(state, 'N');
		if (name == "template-name")
			return parse_identifier_category(state, 'T');
		if (name == "typedef-name")
			return parse_identifier_category(state, 'Y');
		if (name == "type-name")
			return parse_type_name(state);
		if (name == "unqualified-id")
			return parse_unqualified_id(state);
		if (name == "decl-specifier-seq")
			return parse_decl_specifier_seq(state);
		if (name == "close-angle-bracket")
			return parse_close_angle(state);
		return parse_generic_nonterminal(name, state);
	}

	vector<State> parse_generic_nonterminal(const string& name,
	                                        const State& state)
	{
		MemoKey key;
		key.rule = name;
		key.state = state;
		map<MemoKey, vector<State> >::const_iterator memo = memo_.find(key);
		if (memo != memo_.end())
			return memo->second;
		if (active_.count(key) != 0)
			return vector<State>();
		map<string, Rule>::const_iterator it = grammar_.rules.find(name);
		if (it == grammar_.rules.end())
			throw runtime_error("unknown grammar rule: " + name);
		active_.insert(key);
		vector<State> out;
		for (size_t i = 0; i < it->second.alternatives.size(); ++i)
			append_unique(out, eval_node(it->second.alternatives[i], state));
		active_.erase(key);
		memo_[key] = out;
		return out;
	}

	vector<State> eval_node(const NodePtr& node, const State& state)
	{
		if (node->kind == NodeKind::Symbol)
			return eval_symbol(node, state);
		if (node->kind == NodeKind::Sequence)
			return eval_sequence(node->children, state);
		if (node->kind == NodeKind::Optional)
			return eval_optional(node->child, state);
		if (node->kind == NodeKind::Star)
			return eval_star(node->child, state);
		return eval_plus(node->child, state);
	}

	vector<State> eval_symbol(const NodePtr& node, const State& state)
	{
		if (IsTerminalSymbol(node->symbol))
			return match_terminal(node->symbol, node->opens_angle, state);
		return parse_nonterminal(node->symbol, state);
	}

	vector<State> eval_sequence(const vector<NodePtr>& nodes,
	                            const State& state)
	{
		vector<State> states(1, state);
		for (size_t i = 0; i < nodes.size(); ++i)
		{
			vector<State> next;
			for (size_t j = 0; j < states.size(); ++j)
				append_unique(next, eval_node(nodes[i], states[j]));
			states.swap(next);
			if (states.empty())
				break;
		}
		return states;
	}

	vector<State> eval_optional(const NodePtr& node, const State& state)
	{
		vector<State> out(1, state);
		append_unique(out, eval_node(node, state));
		return out;
	}

	vector<State> eval_plus(const NodePtr& node, const State& state)
	{
		vector<State> out;
		vector<State> first = eval_node(node, state);
		for (size_t i = 0; i < first.size(); ++i)
			append_unique(out, eval_star(node, first[i]));
		return out;
	}

	vector<State> eval_star(const NodePtr& node, const State& state)
	{
		set<State> seen;
		vector<State> out;
		vector<State> work(1, state);
		seen.insert(state);
		out.push_back(state);
		for (size_t index = 0; index < work.size(); ++index)
		{
			vector<State> next = eval_node(node, work[index]);
			for (size_t i = 0; i < next.size(); ++i)
			{
				if (seen.insert(next[i]).second)
				{
					work.push_back(next[i]);
					out.push_back(next[i]);
				}
			}
		}
		return out;
	}

	vector<State> match_terminal(const string& symbol,
	                             bool opens_angle,
	                             const State& state) const
	{
		vector<State> out;
		if (state.pos >= tokens_.size())
			return out;
		if (angle_blocks(symbol, state))
			return out;
		if (!token_matches(tokens_[state.pos], symbol))
			return out;
		State next = state;
		++next.pos;
		if (!update_bracket_depth(symbol, next))
			return out;
		if (opens_angle)
			next.angle_stack.push_back(next.bracket_depth);
		out.push_back(next);
		return out;
	}

	vector<State> parse_close_angle(const State& state) const
	{
		vector<State> out;
		if (state.angle_stack.empty() || state.pos >= tokens_.size())
			return out;
		const string& symbol = tokens_[state.pos].symbol;
		if (symbol != "OP_GT" &&
		    symbol != "ST_RSHIFT_1" &&
		    symbol != "ST_RSHIFT_2")
			return out;
		State next = state;
		++next.pos;
		next.angle_stack.pop_back();
		out.push_back(next);
		return out;
	}

	bool token_matches(const RecogToken& token, const string& symbol) const
	{
		if (symbol == "TT_IDENTIFIER")
			return token.identifier;
		if (symbol == "TT_LITERAL")
			return token.literal;
		if (symbol == "ST_EMPTYSTR")
			return token.literal && token.source == "\"\"";
		if (symbol == "ST_ZERO")
			return token.literal && token.source == "0";
		if (symbol == "ST_OVERRIDE")
			return token.identifier && token.source == "override";
		if (symbol == "ST_FINAL")
			return token.identifier && token.source == "final";
		if (symbol == "ST_NONPAREN")
			return IsNonParenToken(token);
		return token.symbol == symbol;
	}

	bool angle_blocks(const string& symbol, const State& state) const
	{
		if (state.angle_stack.empty())
			return false;
		if (state.angle_stack.back() != state.bracket_depth)
			return false;
		return symbol == "OP_GT" ||
		       symbol == "ST_RSHIFT_1" ||
		       symbol == "ST_RSHIFT_2";
	}

	bool update_bracket_depth(const string& symbol, State& state) const
	{
		if (symbol == "OP_LPAREN" ||
		    symbol == "OP_LSQUARE" ||
		    symbol == "OP_LBRACE")
			++state.bracket_depth;
		else if (symbol == "OP_RPAREN" ||
		         symbol == "OP_RSQUARE" ||
		         symbol == "OP_RBRACE")
			--state.bracket_depth;
		return state.bracket_depth >= 0;
	}

	vector<State> parse_identifier_category(const State& state,
	                                        char category) const
	{
		vector<State> out;
		if (state.pos < tokens_.size() &&
		    tokens_[state.pos].identifier &&
		    ContainsChar(tokens_[state.pos].source, category))
		{
			State next = state;
			++next.pos;
			out.push_back(next);
		}
		return out;
	}

	vector<State> parse_class_name(const State& state)
	{
		vector<State> out;
		if (state.pos >= tokens_.size() || !tokens_[state.pos].identifier)
			return out;
		const string& name = tokens_[state.pos].source;
		if (!ContainsChar(name, 'C'))
			return out;
		if (ContainsChar(name, 'T') && next_token_is("OP_LT", state.pos))
			return parse_nonterminal("simple-template-id", state);
		State next = state;
		++next.pos;
		out.push_back(next);
		return out;
	}

	vector<State> parse_type_name(const State& state)
	{
		if (state.pos < tokens_.size() &&
		    tokens_[state.pos].identifier &&
		    ContainsChar(tokens_[state.pos].source, 'T') &&
		    next_token_is("OP_LT", state.pos))
			return parse_nonterminal("simple-template-id", state);
		return parse_generic_nonterminal("type-name", state);
	}

	vector<State> parse_unqualified_id(const State& state)
	{
		if (state.pos < tokens_.size() &&
		    tokens_[state.pos].identifier &&
		    ContainsChar(tokens_[state.pos].source, 'T') &&
		    next_token_is("OP_LT", state.pos))
			return parse_nonterminal("template-id", state);
		return parse_generic_nonterminal("unqualified-id", state);
	}

	vector<State> parse_decl_specifier_seq(const State& state)
	{
		set<SpecResult> seen;
		vector<SpecResult> work;
		vector<State> out;
		append_spec_results(work, seen, parse_decl_specifier_once(state, false));
		for (size_t i = 0; i < work.size(); ++i)
		{
			append_unique(out, parse_attribute_tail(work[i].state));
			append_spec_results(work,
			                    seen,
			                    parse_decl_specifier_once(work[i].state,
			                                              work[i].saw_non_cv_type));
		}
		return out;
	}

	vector<State> parse_attribute_tail(const State& state)
	{
		return eval_star(MakeSymbol("attribute-specifier"), state);
	}

	vector<SpecResult> parse_decl_specifier_once(const State& state,
	                                             bool saw_non_cv_type)
	{
		vector<SpecResult> out;
		append_no_type_specs(out, state, saw_non_cv_type);
		append_cv_specs(out, state, saw_non_cv_type);
		append_builtin_type_specs(out, state);
		append_named_type_specs(out, state, saw_non_cv_type);
		append_general_type_specs(out, state);
		return out;
	}

	void append_no_type_specs(vector<SpecResult>& out,
	                          const State& state,
	                          bool saw_non_cv_type)
	{
		for (map<string, Rule>::const_iterator it = grammar_.rules.begin();
		     it != grammar_.rules.end();
		     ++it)
		{
			if (!IsNoTypeDeclSpecifier(it->first))
				continue;
			vector<State> states = parse_nonterminal(it->first, state);
			append_spec_states(out, states, saw_non_cv_type);
		}
		static const char* const terminals[] = {
			"KW_FRIEND", "KW_TYPEDEF", "KW_CONSTEXPR"
		};
		for (size_t i = 0; i < sizeof(terminals) / sizeof(terminals[0]); ++i)
			append_spec_states(out,
			                   match_terminal(terminals[i], false, state),
			                   saw_non_cv_type);
	}

	void append_cv_specs(vector<SpecResult>& out,
	                     const State& state,
	                     bool saw_non_cv_type)
	{
		append_spec_states(out,
		                   parse_nonterminal("cv-qualifier", state),
		                   saw_non_cv_type);
	}

	void append_builtin_type_specs(vector<SpecResult>& out,
	                               const State& state)
	{
		if (state.pos >= tokens_.size())
			return;
		if (!IsBuiltinSimpleType(tokens_[state.pos].symbol))
			return;
		append_spec_states(out,
		                   match_terminal(tokens_[state.pos].symbol, false, state),
		                   true);
	}

	void append_named_type_specs(vector<SpecResult>& out,
	                             const State& state,
	                             bool saw_non_cv_type)
	{
		if (saw_non_cv_type)
			return;
		append_spec_states(out,
		                   parse_nonterminal("type-name", state),
		                   true);
		append_spec_states(out,
		                   parse_sequence_symbols({"nested-name-specifier",
		                                           "type-name"}, state),
		                   true);
		append_spec_states(out,
		                   parse_sequence_symbols({"nested-name-specifier",
		                                           "KW_TEMPLATE",
		                                           "simple-template-id"}, state),
		                   true);
	}

	void append_general_type_specs(vector<SpecResult>& out,
	                               const State& state)
	{
		static const char* const names[] = {
			"class-specifier", "enum-specifier",
			"elaborated-type-specifier", "typename-specifier",
			"decltype-specifier"
		};
		for (size_t i = 0; i < sizeof(names) / sizeof(names[0]); ++i)
			append_spec_states(out, parse_nonterminal(names[i], state), true);
	}

	vector<State> parse_sequence_symbols(initializer_list<string> symbols,
	                                     const State& state)
	{
		vector<State> states(1, state);
		for (initializer_list<string>::const_iterator it = symbols.begin();
		     it != symbols.end();
		     ++it)
		{
			vector<State> next;
			for (size_t i = 0; i < states.size(); ++i)
			{
				if (IsTerminalSymbol(*it))
					append_unique(next, match_terminal(*it, false, states[i]));
				else
					append_unique(next, parse_nonterminal(*it, states[i]));
			}
			states.swap(next);
		}
		return states;
	}

	bool next_token_is(const string& symbol, size_t pos) const
	{
		return pos + 1 < tokens_.size() &&
		       tokens_[pos + 1].symbol == symbol;
	}

	void append_unique(vector<State>& out, const vector<State>& states) const
	{
		set<State> existing(out.begin(), out.end());
		for (size_t i = 0; i < states.size(); ++i)
		{
			if (existing.insert(states[i]).second)
				out.push_back(states[i]);
		}
	}

	void append_spec_states(vector<SpecResult>& out,
	                        const vector<State>& states,
	                        bool saw_non_cv_type) const
	{
		for (size_t i = 0; i < states.size(); ++i)
		{
			SpecResult result;
			result.state = states[i];
			result.saw_non_cv_type = saw_non_cv_type;
			out.push_back(result);
		}
	}

	void append_spec_results(vector<SpecResult>& out,
	                         set<SpecResult>& seen,
	                         const vector<SpecResult>& states) const
	{
		for (size_t i = 0; i < states.size(); ++i)
		{
			if (seen.insert(states[i]).second)
				out.push_back(states[i]);
		}
	}
};

}  // namespace

bool recognize_source_file(const string& srcfile, const Options& options)
{
	vector<PPToken> pp_tokens =
		preproc::preprocess_source_file(srcfile, options.preprocess);
	vector<posttoken::Token> post_tokens;
	if (!posttoken::collect_posttokens_checked(pp_tokens, post_tokens))
		return false;
	Grammar grammar = LoadGrammar(pa6_grammar_lines());
	vector<RecogToken> tokens = ConvertTokens(post_tokens);
	Parser parser(grammar, tokens);
	return parser.parse_translation_unit();
}

}  // namespace recog
