#include "cy86_model.h"

#include <stdexcept>

#include "posttoken_pipeline.h"

using namespace std;

namespace cy86 {
namespace {

typedef posttoken::Token Token;

bool is_keyword_token(const Token& token)
{
	return token.kind == posttoken::TokenKind::Simple &&
	       token.token_type < OP_LBRACE;
}

class Parser
{
public:
	explicit Parser(const vector<Token>& tokens) : tokens_(tokens), pos_(0) {}

	Program parse()
	{
		Program program;
		while (!at_end())
		{
			Statement stmt = parse_statement();
			expect_simple(OP_SEMICOLON);
			program.statements.push_back(stmt);
		}
		return program;
	}

private:
	const vector<Token>& tokens_;
	size_t pos_;

	bool at_end() const
	{
		return peek().kind == posttoken::TokenKind::EndOfFile;
	}

	const Token& peek(size_t lookahead = 0) const
	{
		if (pos_ + lookahead >= tokens_.size())
			throw runtime_error("unexpected end of input");
		return tokens_[pos_ + lookahead];
	}

	bool check_simple(ETokenType type) const
	{
		return peek().kind == posttoken::TokenKind::Simple &&
		       peek().token_type == type;
	}

	bool match_simple(ETokenType type)
	{
		if (!check_simple(type))
			return false;
		++pos_;
		return true;
	}

	void expect_simple(ETokenType type)
	{
		if (!match_simple(type))
			throw runtime_error("unexpected token");
	}

	string expect_identifier()
	{
		if (peek().kind != posttoken::TokenKind::Identifier)
			throw runtime_error("expected identifier");
		return tokens_[pos_++].source;
	}

	LiteralValue expect_literal()
	{
		if (peek().kind != posttoken::TokenKind::Literal)
			throw runtime_error("expected literal");
		return parse_literal_value(tokens_[pos_++].source);
	}

	bool starts_label() const
	{
		return peek().kind == posttoken::TokenKind::Identifier &&
		       peek(1).kind == posttoken::TokenKind::Simple &&
		       peek(1).token_type == OP_COLON;
	}

	Statement parse_statement()
	{
		Statement stmt;
		while (starts_label())
		{
			stmt.labels.push_back(peek().source);
			pos_ += 2;
		}
		if (match_simple(OP_MINUS))
		{
			stmt.kind = StatementKind::LiteralData;
			stmt.literal = negate_literal_value(expect_literal());
			return stmt;
		}
		if (peek().kind == posttoken::TokenKind::Literal)
		{
			stmt.kind = StatementKind::LiteralData;
			stmt.literal = expect_literal();
			return stmt;
		}
		if (is_keyword_token(peek()))
			throw runtime_error("C++ keyword is invalid in CY86");
		stmt.kind = StatementKind::Instruction;
		stmt.opcode = expect_identifier();
		while (!check_simple(OP_SEMICOLON))
			stmt.operands.push_back(parse_operand());
		return stmt;
	}

	Operand parse_operand()
	{
		if (peek().kind == posttoken::TokenKind::Identifier)
			return parse_identifier_operand();
		if (peek().kind == posttoken::TokenKind::Literal)
			return make_immediate_operand(expect_literal());
		if (match_simple(OP_LPAREN))
			return parse_parenthesized_immediate();
		if (match_simple(OP_LSQUARE))
			return parse_memory_operand();
		if (is_keyword_token(peek()))
			throw runtime_error("C++ keyword is invalid in CY86");
		throw runtime_error("expected operand");
	}

	Operand parse_identifier_operand()
	{
		const string name = expect_identifier();
		RegisterRef reg;
		if (parse_register(name, reg))
		{
			Operand out;
			out.kind = OperandKind::Register;
			out.reg = reg;
			return out;
		}
		Operand out;
		out.kind = OperandKind::Immediate;
		out.imm.label = true;
		out.imm.label_name = name;
		return out;
	}

	Operand make_immediate_operand(const LiteralValue& literal)
	{
		Operand out;
		out.kind = OperandKind::Immediate;
		out.imm.literal = literal;
		return out;
	}

	Operand parse_parenthesized_immediate()
	{
		Operand out;
		out.kind = OperandKind::Immediate;
		if (match_simple(OP_MINUS))
			out.imm.literal = negate_literal_value(expect_literal());
		else if (peek().kind == posttoken::TokenKind::Literal)
			out.imm.literal = expect_literal();
		else
			parse_label_immediate(out.imm);
		expect_simple(OP_RPAREN);
		return out;
	}

	void parse_label_immediate(ImmediateValue& imm)
	{
		imm.label = true;
		imm.label_name = expect_identifier();
		if (match_simple(OP_PLUS) || match_simple(OP_MINUS))
		{
			imm.has_addend = true;
			imm.addend_sign = tokens_[pos_ - 1].token_type == OP_MINUS ? -1 : 1;
			imm.addend = expect_literal();
		}
	}

	Operand parse_memory_operand()
	{
		Operand out;
		out.kind = OperandKind::Memory;
		if (peek().kind == posttoken::TokenKind::Literal)
		{
			out.mem.kind = AddressKind::Literal;
			out.mem.literal = expect_literal();
		}
		else if (peek().kind == posttoken::TokenKind::Identifier)
			parse_memory_identifier(out.mem);
		else
			throw runtime_error("expected memory address");
		expect_simple(OP_RSQUARE);
		return out;
	}

	void parse_memory_identifier(MemoryAddress& mem)
	{
		const string name = expect_identifier();
		RegisterRef reg;
		if (parse_register(name, reg))
		{
			mem.kind = AddressKind::Register;
			mem.reg = reg;
		}
		else
		{
			mem.kind = AddressKind::Label;
			mem.label_name = name;
		}
		if (match_simple(OP_PLUS) || match_simple(OP_MINUS))
		{
			mem.has_addend = true;
			mem.addend_sign = tokens_[pos_ - 1].token_type == OP_MINUS ? -1 : 1;
			mem.addend = expect_literal();
		}
	}
};

vector<Token> posttokens_for_file(const string& srcfile, const Options& options)
{
	vector<PPToken> pp = preproc::preprocess_source_file(srcfile,
	                                                     options.preprocess);
	vector<Token> tokens;
	if (!posttoken::collect_posttokens_checked(pp, tokens))
		throw runtime_error("invalid token");
	return tokens;
}

}  // namespace

Program parse_program_files(const vector<string>& srcfiles,
                            const Options& options)
{
	vector<Token> all;
	for (size_t i = 0; i < srcfiles.size(); ++i)
	{
		vector<Token> tokens = posttokens_for_file(srcfiles[i], options);
		for (size_t j = 0; j < tokens.size(); ++j)
		{
			if (tokens[j].kind != posttoken::TokenKind::EndOfFile)
				all.push_back(tokens[j]);
		}
	}
	all.push_back(Token(posttoken::TokenKind::EndOfFile, ""));
	Parser parser(all);
	return parser.parse();
}

}  // namespace cy86
