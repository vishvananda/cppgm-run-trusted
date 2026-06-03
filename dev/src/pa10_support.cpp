#include "pa10_internal.h"

#include <fstream>
#include <stdexcept>

#include "preproc_support.h"
#include "posttoken_support.h"

using namespace std;

namespace pa10 {
namespace internal {

Ast make_ast(const string& line)
{
	return Ast(new AstNode(line));
}

void add_child(const Ast& parent, const Ast& child)
{
	if (child)
		parent->children.push_back(child);
}

void dump_ast(ostream& out, const Ast& node, int indent)
{
	for (int i = 0; i < indent; ++i)
		out << "  ";
	out << node->line << '\n';
	for (size_t i = 0; i < node->children.size(); ++i)
		dump_ast(out, node->children[i], indent + 1);
}

Token::Token()
	: kind(posttoken::TokenKind::Invalid),
	  type(OP_LBRACE),
	  split_rshift(false),
	  split_group(0)
{
}

Token::Token(posttoken::TokenKind k, const string& text, ETokenType tt)
	: kind(k),
	  source(text),
	  type(tt),
	  split_rshift(false),
	  split_group(0)
{
}

DeclParse::DeclParse()
	: has_typedef(false),
	  has_friend(false)
{
}

DeclaratorParse::DeclaratorParse()
	: has_parameter_clause(false),
	  is_pack(false)
{
}

vector<Token> collect_source_tokens(const string& srcfile,
                                    const Options& options)
{
	vector<PPToken> pp_tokens =
		preproc::preprocess_source_file(srcfile, options.preprocess);
	vector<posttoken::Token> post_tokens;
	if (!posttoken::collect_posttokens_checked(pp_tokens, post_tokens))
		throw runtime_error("posttoken conversion failed");

	vector<Token> out;
	int rshift_group = 1;
	for (size_t i = 0; i < post_tokens.size(); ++i)
	{
		const posttoken::Token& in = post_tokens[i];
		if (in.kind == posttoken::TokenKind::Simple && in.token_type == OP_RSHIFT)
		{
			Token first(posttoken::TokenKind::Simple, ">", OP_GT);
			Token second(posttoken::TokenKind::Simple, ">", OP_GT);
			first.split_rshift = true;
			second.split_rshift = true;
			first.split_group = rshift_group;
			second.split_group = rshift_group;
			++rshift_group;
			out.push_back(first);
			out.push_back(second);
			continue;
		}

		Token token(in.kind, in.source, in.token_type);
		out.push_back(token);
	}
	return out;
}

string token_leaf(const Token& token)
{
	if (token.kind == posttoken::TokenKind::Identifier)
		return "TT_IDENTIFIER:" + token.source;
	if (token.kind == posttoken::TokenKind::Literal)
		return token.source;
	if (token.kind == posttoken::TokenKind::Simple)
		return TokenTypeToStringMap.at(token.type) + ":" + token.source;
	return token.source;
}

string op_leaf(ETokenType type, const string& source)
{
	return TokenTypeToStringMap.at(type) + ":" + source;
}

string keyword_leaf(ETokenType type, const string& source)
{
	return TokenTypeToStringMap.at(type) + ":" + source;
}

string format_token_range(const vector<Token>& tokens, size_t begin, size_t end)
{
	string out;
	for (size_t i = begin; i < end && i < tokens.size(); ++i)
	{
		if (!out.empty() &&
		    (tokens[i - 1].source == "const" ||
		     tokens[i - 1].source == "volatile" ||
		     tokens[i - 1].source == "typename" ||
		     tokens[i - 1].source == "template" ||
		     tokens[i - 1].source == "struct" ||
		     tokens[i - 1].source == "class" ||
		     tokens[i - 1].source == "enum"))
			out += " ";
		out += tokens[i].source;
	}
	return out;
}

bool is_builtin_type(ETokenType type)
{
	return type == KW_BOOL ||
	       type == KW_CHAR ||
	       type == KW_CHAR16_T ||
	       type == KW_CHAR32_T ||
	       type == KW_DOUBLE ||
	       type == KW_FLOAT ||
	       type == KW_INT ||
	       type == KW_LONG ||
	       type == KW_SHORT ||
	       type == KW_SIGNED ||
	       type == KW_UNSIGNED ||
	       type == KW_VOID ||
	       type == KW_WCHAR_T ||
	       type == KW_AUTO;
}

bool is_cv_qualifier(ETokenType type)
{
	return type == KW_CONST || type == KW_VOLATILE;
}

bool is_decl_specifier_keyword(ETokenType type)
{
	return is_builtin_type(type) ||
	       is_cv_qualifier(type) ||
	       type == KW_TYPEDEF ||
	       type == KW_EXTERN ||
	       type == KW_STATIC ||
	       type == KW_INLINE ||
	       type == KW_VIRTUAL ||
	       type == KW_CONSTEXPR ||
	       type == KW_THREAD_LOCAL ||
	       type == KW_FRIEND ||
	       type == KW_MUTABLE ||
	       type == KW_REGISTER ||
	       type == KW_EXPLICIT;
}

bool is_access_specifier(ETokenType type)
{
	return type == KW_PUBLIC || type == KW_PRIVATE || type == KW_PROTECTED;
}

bool is_member_function_specifier(ETokenType type)
{
	return type == KW_INLINE ||
	       type == KW_VIRTUAL ||
	       type == KW_EXPLICIT ||
	       type == KW_CONSTEXPR ||
	       type == KW_FRIEND ||
	       type == KW_STATIC;
}

}  // namespace internal

void emit_ast(const vector<string>& srcfiles,
              const string& outfile,
              const Options& options)
{
	ofstream out(outfile.c_str());
	if (!out)
		throw runtime_error("cannot open output file");

	vector<internal::Ast> units;
	for (size_t i = 0; i < srcfiles.size(); ++i)
	{
		vector<internal::Token> tokens =
			internal::collect_source_tokens(srcfiles[i], options);
		internal::Parser parser(tokens);
		units.push_back(parser.parse_translation_unit());
	}

	out << units.size() << " translation units\n";
	for (size_t i = 0; i < units.size(); ++i)
	{
		out << "start translation unit " << (i + 1) << '\n';
		internal::dump_ast(out, units[i], 0);
		out << "end translation unit\n";
	}
}

}  // namespace pa10
