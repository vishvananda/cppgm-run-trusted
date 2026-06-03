#pragma once

#include <memory>
#include <set>
#include <sstream>
#include <string>
#include <vector>

#include "pa10_ast.h"
#include "posttoken_pipeline.h"

using namespace std;

namespace pa10 {
namespace internal {

struct AstNode;
typedef shared_ptr<AstNode> Ast;

struct AstNode
{
	string line;
	vector<Ast> children;
	bool builtin_type_expression;
	bool type_id_has_qualified_name;
	string type_id_primary_name;

	explicit AstNode(const string& text);
};

Ast make_ast(const string& line);
void add_child(const Ast& parent, const Ast& child);
void dump_ast(ostream& out, const Ast& node, int indent);

struct Token
{
	posttoken::TokenKind kind;
	string source;
	ETokenType type;
	bool split_rshift;
	int split_group;

	Token();
	Token(posttoken::TokenKind k, const string& text, ETokenType tt);
};

struct DeclParse
{
	Ast specs;
	bool has_typedef;
	bool has_friend;
	bool last_specifier_is_non_cv_type;
	bool all_specifiers_are_keywords;
	bool has_qualified_type_name;
	string primary_type_name;
	vector<string> introduced_types;

	DeclParse();
};

struct DeclaratorParse
{
	Ast node;
	string name;
	bool has_parameter_clause;
	bool is_pack;

	DeclaratorParse();
};

struct Scope
{
	set<string> types;
	set<string> values;
	set<string> namespaces;

	bool template_parameter_scope;
	string namespace_name;
	string class_name;

	Scope();
};

vector<Token> collect_source_tokens(const string& srcfile,
                                    const Options& options);
string token_leaf(const Token& token);
string op_leaf(ETokenType type, const string& source);
string keyword_leaf(ETokenType type, const string& source);
string format_token_range(const vector<Token>& tokens, size_t begin, size_t end);
bool is_builtin_type(ETokenType type);
bool is_decl_specifier_keyword(ETokenType type);
bool is_cv_qualifier(ETokenType type);
bool is_access_specifier(ETokenType type);
bool is_member_function_specifier(ETokenType type);

}  // namespace internal
}  // namespace pa10
