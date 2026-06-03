#include "preproc_support.h"

#include <cstdlib>
#include <fstream>
#include <set>
#include <sstream>
#include <stdexcept>
#include <utility>

#include "ctrlexpr_support.h"
#include "macro_support.h"
#include "posttoken_pipeline.h"
#include "posttoken_support.h"
#include "pptoken_lib.h"

using namespace std;

namespace preproc {
namespace {

typedef pair<unsigned long int, unsigned long int> PA5FileId;

extern "C" long int syscall(long int n, ...) throw ();

bool PA5GetFileId(const string& path, PA5FileId& out_fileid)
{
	struct
	{
		unsigned long int dev;
		unsigned long int ino;
		long int unused[16];
	} data = {};

	int res = syscall(4, path.c_str(), &data);
	out_fileid = make_pair(data.dev, data.ino);
	return res == 0;
}

struct IfFrame
{
	bool parent_active;
	bool current_active;
	bool branch_taken;
	bool saw_else;
};

bool IsHorizontalWhitespace(const PPToken& token)
{
	return token.kind == PPTokenKind::Whitespace;
}

size_t SkipHorizontalWhitespace(const vector<PPToken>& tokens,
                                size_t pos,
                                size_t end)
{
	while (pos < end && IsHorizontalWhitespace(tokens[pos]))
		++pos;
	return pos;
}

size_t NextRealToken(const vector<PPToken>& tokens, size_t pos)
{
	while (pos < tokens.size() && !IsRealToken(tokens[pos]))
		++pos;
	return pos;
}

bool HasRealTokens(const vector<PPToken>& tokens, size_t pos)
{
	return NextRealToken(tokens, pos) < tokens.size();
}

vector<PPToken> SliceTokens(const vector<PPToken>& tokens,
                            size_t begin,
                            size_t end)
{
	vector<PPToken> out;
	out.reserve(end - begin);
	for (size_t i = begin; i < end; ++i)
		out.push_back(tokens[i]);
	return out;
}

string DecodeStringLiteralUtf8(const PPToken& token)
{
	if (token.kind != PPTokenKind::StringLiteral)
		throw runtime_error("expected string literal");
	LiteralEncoding encoding = LiteralEncoding::Ordinary;
	const size_t prefix_len = PrefixLengthForQuotedLiteral(token.text, '"', encoding);
	if (prefix_len == string::npos)
		throw runtime_error("invalid string literal");
	size_t close_pos = 0;
	if (!FindOrdinaryClosingQuote(token.text, prefix_len, '"', close_pos))
		throw runtime_error("invalid string literal");
	vector<uint32_t> code_points;
	if (!DecodeOrdinaryBody(token.text, prefix_len + 1, close_pos, code_points))
		throw runtime_error("invalid string literal");
	vector<unsigned char> bytes;
	for (size_t i = 0; i < code_points.size(); ++i)
		AppendUtf8CodePoint(bytes, code_points[i]);
	return string(bytes.begin(), bytes.end());
}

bool IntegerValueFromPPNumber(const PPToken& token, int& out)
{
	if (token.kind != PPTokenKind::PPNumber)
		return false;
	IntegerLiteralInfo info;
	if (!AnalyzeIntegerLiteral(token.text, info) || info.user_defined)
		return false;
	if (info.value == 0 || info.value > 2147483647ULL)
		return false;
	out = static_cast<int>(info.value);
	return true;
}

bool IsKnownDirective(const string& name)
{
	static const char* const names[] = {
		"if", "ifdef", "ifndef", "elif", "else", "endif",
		"include", "define", "undef", "line", "error", "pragma"
	};
	for (size_t i = 0; i < sizeof(names) / sizeof(names[0]); ++i)
	{
		if (name == names[i])
			return true;
	}
	return false;
}

class Preprocessor
{
public:
	explicit Preprocessor(const Options& options)
		: line_delta_(0)
	{
		macros_.initialize_predefined_macros(options.author,
		                                     options.build_date,
		                                     options.build_time);
	}

	void process_source_file(const string& srcfile, vector<PPToken>& output)
	{
		process_file(srcfile, output);
		if (!if_stack_.empty())
			throw runtime_error("File completed with unmatched #if");
	}

private:
	macro::MacroProcessor macros_;
	set<PA5FileId> once_files_;
	vector<IfFrame> if_stack_;
	string current_file_;
	int line_delta_;

	bool is_active() const
	{
		return if_stack_.empty() || if_stack_.back().current_active;
	}

	PPToken presumed_token(const PPToken& raw) const
	{
		PPToken token = raw;
		token.source_file = current_file_;
		if (raw.source_line > 0)
			token.source_line = raw.source_line + line_delta_;
		return token;
	}

	vector<PPToken> presumed_tokens(const vector<PPToken>& raw) const
	{
		vector<PPToken> out;
		out.reserve(raw.size());
		for (size_t i = 0; i < raw.size(); ++i)
			out.push_back(presumed_token(raw[i]));
		return out;
	}

	void process_file(const string& path, vector<PPToken>& output)
	{
		ifstream in(path.c_str());
		if (!in)
			throw runtime_error("include file not found");

		PPTokenCollector collector;
		collector.source_file = path;
		pptoken::run_pptoken(in, collector);

		const string saved_file = current_file_;
		const int saved_delta = line_delta_;
		const size_t base_depth = if_stack_.size();
		current_file_ = path;
		line_delta_ = 0;

		vector<PPToken> text;
		vector<PPToken> line;
		for (size_t i = 0; i < collector.tokens.size(); ++i)
		{
			const PPToken& token = collector.tokens[i];
			if (token.kind == PPTokenKind::EndOfFile)
				break;
			if (IsNewLine(token))
			{
				process_line(line, token, text, output);
				line.clear();
			}
			else
				line.push_back(token);
		}
		flush_text(text, output);
		if (if_stack_.size() != base_depth)
			throw runtime_error("File completed with unmatched #if");

		current_file_ = saved_file;
		line_delta_ = saved_delta;
	}

	void process_line(const vector<PPToken>& raw_line,
	                  const PPToken& raw_newline,
	                  vector<PPToken>& text,
	                  vector<PPToken>& output)
	{
		vector<PPToken> line = presumed_tokens(raw_line);
		const PPToken newline = presumed_token(raw_newline);
		const size_t hash = first_directive_hash(line);
		if (hash == line.size())
		{
			if (is_active())
			{
				text.insert(text.end(), line.begin(), line.end());
				text.push_back(newline);
			}
			return;
		}
		flush_text(text, output);
		handle_directive(line, hash, raw_newline.source_line, output);
	}

	size_t first_directive_hash(const vector<PPToken>& line) const
	{
		size_t pos = SkipHorizontalWhitespace(line, 0, line.size());
		if (pos < line.size() && IsHash(line[pos]))
			return pos;
		return line.size();
	}

	void flush_text(vector<PPToken>& text, vector<PPToken>& output)
	{
		if (text.empty())
			return;
		vector<PPToken> expanded = macros_.expand_tokens(text);
		vector<PPToken> pragmaless = execute_pragma_operators(expanded);
		output.insert(output.end(), pragmaless.begin(), pragmaless.end());
		text.clear();
	}

	void handle_directive(const vector<PPToken>& line,
	                      size_t hash,
	                      int newline_physical_line,
	                      vector<PPToken>& output)
	{
		const size_t end = line.size();
		size_t name_pos = SkipHorizontalWhitespace(line, hash + 1, end);
		if (name_pos >= end)
			return;
		if (!IsIdentifier(line[name_pos]))
		{
			if (is_active())
				throw runtime_error("Invalid preprocessing directive");
			return;
		}
		const string name = line[name_pos].text;
		const size_t body = name_pos + 1;
		if (!IsKnownDirective(name))
		{
			if (is_active())
				throw runtime_error("Unknown preprocessing directive");
			return;
		}

		if (name == "if")
			handle_if(line, body, end);
		else if (name == "ifdef")
			handle_ifdef(line, body, end, false);
		else if (name == "ifndef")
			handle_ifdef(line, body, end, true);
		else if (name == "elif")
			handle_elif(line, body, end);
		else if (name == "else")
			handle_else();
		else if (name == "endif")
			handle_endif();
		else if (!is_active())
			return;
		else if (name == "include")
			handle_include(line, body, end, output);
		else if (name == "define")
			macros_.parse_define(line, body, end);
		else if (name == "undef")
			macros_.parse_undef(line, body, end);
		else if (name == "line")
			handle_line(line, body, end, newline_physical_line);
		else if (name == "error")
			throw runtime_error("#error");
		else if (name == "pragma")
			execute_pragma_directive(SliceTokens(line, body, end));
	}

	bool evaluate_condition(const vector<PPToken>& line, size_t begin, size_t end)
	{
		vector<PPToken> expr = SliceTokens(line, begin, end);
		expr = macros_.expand_control_expression(expr);
		bool result = false;
		ctrlexpr::DefinedPredicate pred =
			[this](const string& name) { return macros_.is_defined(name); };
		if (!ctrlexpr::evaluate_tokens(expr, pred, result))
			throw runtime_error("invalid controlling expression");
		return result;
	}

	void handle_if(const vector<PPToken>& line, size_t begin, size_t end)
	{
		const bool parent_active = is_active();
		bool condition = false;
		if (parent_active)
			condition = evaluate_condition(line, begin, end);
		IfFrame frame;
		frame.parent_active = parent_active;
		frame.current_active = parent_active && condition;
		frame.branch_taken = frame.current_active;
		frame.saw_else = false;
		if_stack_.push_back(frame);
	}

	void handle_ifdef(const vector<PPToken>& line,
	                  size_t begin,
	                  size_t end,
	                  bool negate)
	{
		const bool parent_active = is_active();
		bool condition = false;
		if (parent_active)
		{
			size_t pos = SkipHorizontalWhitespace(line, begin, end);
			if (pos >= end || !IsIdentifier(line[pos]))
				throw runtime_error("invalid #ifdef");
			condition = macros_.is_defined(line[pos].text);
			pos = SkipHorizontalWhitespace(line, pos + 1, end);
			if (pos != end)
				throw runtime_error("invalid #ifdef");
			if (negate)
				condition = !condition;
		}
		IfFrame frame;
		frame.parent_active = parent_active;
		frame.current_active = parent_active && condition;
		frame.branch_taken = frame.current_active;
		frame.saw_else = false;
		if_stack_.push_back(frame);
	}

	void handle_elif(const vector<PPToken>& line, size_t begin, size_t end)
	{
		if (if_stack_.empty())
			throw runtime_error("#elif without #if");
		IfFrame& frame = if_stack_.back();
		if (frame.saw_else)
			throw runtime_error("#elif after #else");
		if (!frame.parent_active || frame.branch_taken)
		{
			frame.current_active = false;
			return;
		}
		const bool condition = evaluate_condition(line, begin, end);
		frame.current_active = condition;
		if (condition)
			frame.branch_taken = true;
	}

	void handle_else()
	{
		if (if_stack_.empty())
			throw runtime_error("#else without #if");
		IfFrame& frame = if_stack_.back();
		if (frame.saw_else)
			throw runtime_error("duplicate #else");
		frame.saw_else = true;
		frame.current_active = frame.parent_active && !frame.branch_taken;
		if (frame.current_active)
			frame.branch_taken = true;
	}

	void handle_endif()
	{
		if (if_stack_.empty())
			throw runtime_error("#endif without #if");
		if_stack_.pop_back();
	}

	void handle_include(const vector<PPToken>& line,
	                    size_t begin,
	                    size_t end,
	                    vector<PPToken>& output)
	{
		vector<PPToken> operand = SliceTokens(line, begin, end);
		operand = macros_.expand_tokens(operand);
		const string include_name = include_name_from_tokens(operand);
		const string include_path = resolve_include(include_name);
		PA5FileId file_id;
		if (PA5GetFileId(include_path, file_id) &&
		    once_files_.find(file_id) != once_files_.end())
			return;
		process_file(include_path, output);
	}

	string include_name_from_tokens(const vector<PPToken>& tokens)
	{
		size_t pos = NextRealToken(tokens, 0);
		if (pos >= tokens.size())
			throw runtime_error("invalid include");
		const PPToken& token = tokens[pos];
		if (HasRealTokens(tokens, pos + 1))
			throw runtime_error("invalid include");
		if (token.kind == PPTokenKind::HeaderName)
		{
			if (token.text.size() >= 2 &&
			    ((token.text[0] == '"' && token.text[token.text.size() - 1] == '"') ||
			     (token.text[0] == '<' && token.text[token.text.size() - 1] == '>')))
				return token.text.substr(1, token.text.size() - 2);
			throw runtime_error("invalid include");
		}
		return DecodeStringLiteralUtf8(token);
	}

	string resolve_include(const string& name)
	{
		const size_t slash = current_file_.rfind('/');
		if (slash != string::npos)
		{
			const string pathrel = current_file_.substr(0, slash + 1) + name;
			PA5FileId id;
			if (PA5GetFileId(pathrel, id))
				return pathrel;
		}
		PA5FileId id;
		if (PA5GetFileId(name, id))
			return name;
		throw runtime_error("include file not found");
	}

	void handle_line(const vector<PPToken>& line,
	                 size_t begin,
	                 size_t end,
	                 int newline_physical_line)
	{
		vector<PPToken> replacement = macros_.expand_tokens(SliceTokens(line, begin, end));
		size_t pos = NextRealToken(replacement, 0);
		if (pos >= replacement.size())
			throw runtime_error("invalid #line");
		int next_line = 0;
		if (!IntegerValueFromPPNumber(replacement[pos], next_line))
			throw runtime_error("invalid #line");
		pos = NextRealToken(replacement, pos + 1);
		if (pos < replacement.size())
		{
			current_file_ = DecodeStringLiteralUtf8(replacement[pos]);
			pos = NextRealToken(replacement, pos + 1);
			if (pos < replacement.size())
				throw runtime_error("invalid #line");
		}
		line_delta_ = next_line - (newline_physical_line + 1);
	}

	vector<PPToken> execute_pragma_operators(const vector<PPToken>& tokens)
	{
		vector<PPToken> out;
		out.reserve(tokens.size());
		for (size_t pos = 0; pos < tokens.size();)
		{
			if (!IsIdentifier(tokens[pos], "_Pragma"))
			{
				out.push_back(tokens[pos++]);
				continue;
			}
			size_t open = NextRealToken(tokens, pos + 1);
			size_t arg = open < tokens.size() ? NextRealToken(tokens, open + 1) : open;
			size_t close = arg < tokens.size() ? NextRealToken(tokens, arg + 1) : arg;
			if (open >= tokens.size() || !IsOp(tokens[open], "(") ||
			    arg >= tokens.size() ||
			    tokens[arg].kind != PPTokenKind::StringLiteral ||
			    close >= tokens.size() || !IsOp(tokens[close], ")"))
				throw runtime_error("invalid _Pragma");
			execute_pragma_text(DecodeStringLiteralUtf8(tokens[arg]));
			pos = close + 1;
		}
		return out;
	}

	void execute_pragma_directive(const vector<PPToken>& tokens)
	{
		size_t pos = NextRealToken(tokens, 0);
		if (pos >= tokens.size())
			return;
		if (IsIdentifier(tokens[pos], "once"))
			mark_current_file_once();
	}

	void execute_pragma_text(const string& text)
	{
		PPTokenCollector collector;
		istringstream in(text);
		pptoken::run_pptoken(in, collector);
		execute_pragma_directive(collector.tokens);
	}

	void mark_current_file_once()
	{
		PA5FileId file_id;
		if (PA5GetFileId(current_file_, file_id))
			once_files_.insert(file_id);
	}

};

}  // namespace

void run_preproc(const vector<string>& srcfiles,
                 ostream& out,
                 const Options& options)
{
	out << "preproc " << srcfiles.size() << '\n';
	for (size_t i = 0; i < srcfiles.size(); ++i)
	{
		out << "sof " << srcfiles[i] << '\n';
		vector<PPToken> tokens = preprocess_source_file(srcfiles[i], options);
		if (!posttoken::emit_posttokens_checked(tokens, out))
			throw runtime_error("invalid token");
	}
}

vector<PPToken> preprocess_source_file(const string& srcfile,
                                       const Options& options)
{
	vector<PPToken> tokens;
	Preprocessor processor(options);
	processor.process_source_file(srcfile, tokens);
	return tokens;
}

}  // namespace preproc
