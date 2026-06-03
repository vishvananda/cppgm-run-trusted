#include "macro_support.h"

#include <algorithm>
#include <map>
#include <set>
#include <sstream>
#include <stdexcept>
#include <utility>
#include <vector>

#include "posttoken_pipeline.h"
#include "pp_token.h"
#include "pptoken_lib.h"

using namespace std;

namespace macro {
namespace {

const char* const kVaArgs = "__VA_ARGS__";

PPToken MakeCommaToken()
{
	return PPToken(PPTokenKind::PreprocessingOpOrPunc, ",");
}

bool IsEnd(const PPToken& token)
{
	return token.kind == PPTokenKind::EndOfFile;
}

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

bool HasRealTokens(const vector<PPToken>& tokens)
{
	for (size_t i = 0; i < tokens.size(); ++i)
	{
		if (IsRealToken(tokens[i]))
			return true;
	}
	return false;
}

vector<PPToken> NormalizeWhitespace(const vector<PPToken>& tokens, bool trim)
{
	vector<PPToken> out;
	bool pending_space = false;
	for (size_t i = 0; i < tokens.size(); ++i)
	{
		if (IsEnd(tokens[i]))
			continue;
		if (IsWhitespace(tokens[i]))
		{
			pending_space = true;
			continue;
		}
		if (pending_space && (!trim || !out.empty()))
			out.push_back(MakeWhitespaceToken());
		pending_space = false;
		out.push_back(tokens[i]);
	}
	return out;
}

vector<PPToken> TokenSlice(const vector<PPToken>& tokens,
                           size_t begin,
                           size_t end)
{
	vector<PPToken> out;
	for (size_t i = begin; i < end; ++i)
		out.push_back(tokens[i]);
	return out;
}

bool TokenMatchesForRedefinition(const PPToken& a, const PPToken& b)
{
	if (IsWhitespace(a) && IsWhitespace(b))
		return true;
	return a.kind == b.kind && a.text == b.text;
}

void AddPaint(PPToken& token, const set<string>& names)
{
	token.unavailable.insert(names.begin(), names.end());
}

set<string> BaseInvocationPaint(const PPToken& head, const MacroDefinition& macro)
{
	set<string> paint;
	if (!macro.function_like)
		paint = head.unavailable;
	paint.insert(macro.name);
	return paint;
}

bool UnavailableNameBlocksHere(const map<string, MacroDefinition>& macros,
                               const string& name,
                               bool starts_call)
{
	map<string, MacroDefinition>::const_iterator it = macros.find(name);
	if (it == macros.end() || !it->second.function_like)
		return true;
	return starts_call;
}

bool NextRealTokenIsOpenParen(const vector<PPToken>& tokens, size_t pos)
{
	for (size_t i = pos; i < tokens.size(); ++i)
	{
		if (IsWhitespace(tokens[i]))
			continue;
		return IsOp(tokens[i], "(");
	}
	return false;
}

void PaintOwnReplacementToken(PPToken& token,
                              const PPToken& head,
                              const MacroDefinition& macro,
                              const map<string, MacroDefinition>& macros,
                              size_t replacement_pos)
{
	AddPaint(token, BaseInvocationPaint(head, macro));
	if (!macro.function_like || !IsIdentifier(token))
		return;
	if (head.unavailable.count(token.text) != 0 &&
	    UnavailableNameBlocksHere(macros,
	                              token.text,
	                              NextRealTokenIsOpenParen(macro.replacement,
	                                                       replacement_pos + 1)))
		token.unavailable.insert(token.text);
}

void PaintParameterTokens(vector<PPToken>& tokens,
                          const PPToken& head,
                          const MacroDefinition& macro,
                          bool forwarded_through_call)
{
	set<string> base = BaseInvocationPaint(head, macro);
	if (macro.function_like && forwarded_through_call)
		base.clear();
	for (size_t i = 0; i < tokens.size(); ++i)
	{
		AddPaint(tokens[i], base);
		if (macro.function_like && IsIdentifier(tokens[i]) &&
		    head.unavailable.count(tokens[i].text) != 0)
			tokens[i].unavailable.insert(tokens[i].text);
	}
}

bool IsParameterName(const MacroDefinition& macro, const string& name)
{
	if (macro.parameter_index.find(name) != macro.parameter_index.end())
		return true;
	return macro.variadic && name == kVaArgs;
}

size_t ArgumentIndexForName(const MacroDefinition& macro, const string& name)
{
	if (name == kVaArgs)
		return macro.parameters.size();
	return macro.parameter_index.at(name);
}

bool IsEmptyArgumentListForZeroParam(const vector<vector<PPToken> >& segments)
{
	return segments.size() == 1 && !HasRealTokens(segments[0]);
}

void ThrowError(const string& message)
{
	throw runtime_error(message);
}

bool EscapesInsideStringizedToken(const PPToken& token)
{
	return token.kind == PPTokenKind::CharacterLiteral ||
	       token.kind == PPTokenKind::UserDefinedCharacterLiteral ||
	       token.kind == PPTokenKind::StringLiteral ||
	       token.kind == PPTokenKind::UserDefinedStringLiteral;
}

bool HasPasteBefore(const vector<PPToken>& tokens, size_t pos)
{
	while (pos > 0)
	{
		--pos;
		if (IsWhitespace(tokens[pos]))
			continue;
		return IsHashHash(tokens[pos]);
	}
	return false;
}

bool HasPasteAfter(const vector<PPToken>& tokens, size_t pos)
{
	for (size_t i = pos + 1; i < tokens.size(); ++i)
	{
		if (IsWhitespace(tokens[i]))
			continue;
		return IsHashHash(tokens[i]);
	}
	return false;
}

bool PreviousRealTokenIsCallHead(const MacroDefinition& macro,
                                 const vector<PPToken>& tokens,
                                 size_t open_pos)
{
	size_t pos = open_pos;
	while (pos > 0)
	{
		--pos;
		if (IsWhitespace(tokens[pos]))
			continue;
		return IsIdentifier(tokens[pos]) &&
		       !IsParameterName(macro, tokens[pos].text);
	}
	return false;
}

bool ParameterIsForwardedThroughCall(const MacroDefinition& macro, size_t pos)
{
	vector<bool> call_stack;
	for (size_t i = 0; i < pos && i < macro.replacement.size(); ++i)
	{
		if (IsOp(macro.replacement[i], "("))
		{
			call_stack.push_back(
				PreviousRealTokenIsCallHead(macro, macro.replacement, i));
		}
		else if (IsOp(macro.replacement[i], ")") && !call_stack.empty())
		{
			call_stack.pop_back();
		}
	}
	for (size_t i = 0; i < call_stack.size(); ++i)
	{
		if (call_stack[i])
			return true;
	}
	return false;
}

string DecimalString(int value)
{
	ostringstream out;
	out << value;
	return out.str();
}

string QuoteStringLiteral(const string& value)
{
	string out = "\"";
	for (size_t i = 0; i < value.size(); ++i)
	{
		const unsigned char c = static_cast<unsigned char>(value[i]);
		if (c == '\\' || c == '"')
			out += '\\';
		if (c == '\n')
			out += "\\n";
		else if (c == '\t')
			out += "\\t";
		else
			out += static_cast<char>(c);
	}
	out += '"';
	return out;
}

bool IsIdentifierLikeOperatorName(const string& data)
{
	static const char* const names[] = {
		"new", "delete", "and", "and_eq", "bitand", "bitor", "compl",
		"not", "not_eq", "or", "or_eq", "xor", "xor_eq"
	};
	for (size_t i = 0; i < sizeof(names) / sizeof(names[0]); ++i)
	{
		if (data == names[i])
			return true;
	}
	return false;
}

bool IsDefinedOperandToken(const PPToken& token)
{
	return IsIdentifier(token) ||
	       (token.kind == PPTokenKind::PreprocessingOpOrPunc &&
	        IsIdentifierLikeOperatorName(token.text));
}

size_t NextRealToken(const vector<PPToken>& tokens, size_t pos)
{
	while (pos < tokens.size() && !IsRealToken(tokens[pos]))
		++pos;
	return pos;
}

void MaskDefinedOperands(vector<PPToken>& tokens)
{
	for (size_t pos = 0; pos < tokens.size(); ++pos)
	{
		if (!IsIdentifier(tokens[pos], "defined"))
			continue;
		tokens[pos].unavailable.insert("defined");
		size_t next = NextRealToken(tokens, pos + 1);
		if (next >= tokens.size())
			continue;
		if (IsOp(tokens[next], "("))
		{
			size_t name = NextRealToken(tokens, next + 1);
			if (name < tokens.size() && IsDefinedOperandToken(tokens[name]))
				tokens[name].unavailable.insert(tokens[name].text);
			continue;
		}
		if (IsDefinedOperandToken(tokens[next]))
			tokens[next].unavailable.insert(tokens[next].text);
	}
}

}  // namespace

MacroProcessor::MacroProcessor() : predefined_enabled_(false)
{
}

void MacroProcessor::define_object_macro(const string& name,
                                         const vector<PPToken>& replacement)
{
	MacroDefinition macro;
	macro.name = name;
	macro.replacement = NormalizeWhitespace(replacement, true);
	finish_define(name, macro);
}

void MacroProcessor::initialize_predefined_macros(const string& author,
                                                  const string& build_date,
                                                  const string& build_time)
{
	predefined_enabled_ = true;
	build_date_ = build_date;
	build_time_ = build_time;
	define_object_macro("__CPPGM__", TokenizePPString("201303L"));
	define_object_macro("__cplusplus", TokenizePPString("201103L"));
	define_object_macro("__STDC_HOSTED__", TokenizePPString("1"));
	define_object_macro("__CPPGM_AUTHOR__",
	                    TokenizePPString(QuoteStringLiteral(author)));
	define_object_macro("__DATE__", TokenizePPString(QuoteStringLiteral(build_date_)));
	define_object_macro("__TIME__", TokenizePPString(QuoteStringLiteral(build_time_)));
}

bool MacroProcessor::is_defined(const string& name) const
{
	return macros_.find(name) != macros_.end() || is_dynamic_predefined(name);
}

bool MacroProcessor::is_dynamic_predefined(const string& name) const
{
	return predefined_enabled_ && (name == "__FILE__" || name == "__LINE__");
}

vector<PPToken> MacroProcessor::dynamic_predefined_replacement(
	const PPToken& head) const
{
	vector<PPToken> out;
	if (head.text == "__FILE__")
		out.push_back(MakeStringLiteralToken(QuoteStringLiteral(head.source_file)));
	else if (head.text == "__LINE__")
		out.push_back(PPToken(PPTokenKind::PPNumber,
		                      DecimalString(head.source_line)));
	for (size_t i = 0; i < out.size(); ++i)
	{
		CopyTokenLocation(out[i], head);
		out[i].unavailable.insert(head.text);
	}
	return out;
}

vector<PPToken> MacroProcessor::process(const vector<PPToken>& tokens)
{
	vector<PPToken> output;
	vector<PPToken> text;
	bool line_start = true;
	size_t pos = 0;
	while (pos < tokens.size() && !IsEnd(tokens[pos]))
	{
		if (line_start)
		{
			size_t after_ws = pos;
			while (after_ws < tokens.size() && IsHorizontalWhitespace(tokens[after_ws]))
				++after_ws;
			if (after_ws < tokens.size() && IsHash(tokens[after_ws]))
			{
				flush_text(text, output);
				pos = parse_directive(tokens, after_ws);
				line_start = true;
				continue;
			}
		}

		PPToken token = tokens[pos++];
		text.push_back(token);
		if (IsNewLine(token))
			line_start = true;
		else if (!IsHorizontalWhitespace(token))
			line_start = false;
	}
	flush_text(text, output);
	return output;
}

vector<PPToken> MacroProcessor::expand_control_expression(
	const vector<PPToken>& tokens)
{
	vector<PPToken> copy = tokens;
	MaskDefinedOperands(copy);
	return expand_tokens(copy);
}

void MacroProcessor::flush_text(vector<PPToken>& text, vector<PPToken>& output)
{
	if (text.empty())
		return;
	vector<PPToken> normalized = NormalizeWhitespace(text, false);
	vector<PPToken> expanded = expand_tokens(normalized);
	output.insert(output.end(), expanded.begin(), expanded.end());
	text.clear();
}

size_t MacroProcessor::parse_directive(const vector<PPToken>& tokens,
                                       size_t hash_pos)
{
	const size_t end = find_directive_end(tokens, hash_pos);
	size_t pos = SkipHorizontalWhitespace(tokens, hash_pos + 1, end);
	if (pos >= end || !IsIdentifier(tokens[pos]))
		ThrowError("invalid preprocessing directive");
	const string directive = tokens[pos].text;
	++pos;
	if (directive == "define")
		parse_define(tokens, pos, end);
	else if (directive == "undef")
		parse_undef(tokens, pos, end);
	else
		ThrowError("unsupported preprocessing directive");
	return end + 1;
}

size_t MacroProcessor::find_directive_end(const vector<PPToken>& tokens,
                                          size_t hash_pos)
{
	for (size_t i = hash_pos + 1; i < tokens.size(); ++i)
	{
		if (IsNewLine(tokens[i]))
			return i;
		if (IsEnd(tokens[i]))
			break;
	}
	ThrowError("preprocessing directive is not terminated by a new-line");
	return tokens.size();
}

void MacroProcessor::parse_define(const vector<PPToken>& tokens,
                                  size_t pos,
                                  size_t end)
{
	pos = SkipHorizontalWhitespace(tokens, pos, end);
	if (pos >= end || !IsIdentifier(tokens[pos]))
		ThrowError("macro name is missing");
	const string name = tokens[pos].text;
	if (name == kVaArgs)
		ThrowError("__VA_ARGS__ cannot be a macro name");

	MacroDefinition macro;
	macro.name = name;
	const size_t after_name = pos + 1;
	if (after_name < end && IsOp(tokens[after_name], "("))
	{
		macro.function_like = true;
		pos = parse_function_parameters(tokens, after_name + 1, end, macro);
		macro.replacement = NormalizeWhitespace(TokenSlice(tokens, pos, end), true);
	}
	else
	{
		if (after_name < end && !IsHorizontalWhitespace(tokens[after_name]))
			ThrowError("object-like macro replacement requires whitespace");
		pos = SkipHorizontalWhitespace(tokens, after_name, end);
		macro.replacement = NormalizeWhitespace(TokenSlice(tokens, pos, end), true);
	}
	finish_define(name, macro);
}

void MacroProcessor::parse_undef(const vector<PPToken>& tokens,
                                 size_t pos,
                                 size_t end)
{
	pos = SkipHorizontalWhitespace(tokens, pos, end);
	if (pos >= end || !IsIdentifier(tokens[pos]))
		ThrowError("macro name is missing");
	if (tokens[pos].text == kVaArgs)
		ThrowError("__VA_ARGS__ cannot be undefined");
	const string name = tokens[pos].text;
	pos = SkipHorizontalWhitespace(tokens, pos + 1, end);
	if (pos != end)
		ThrowError("extra tokens after #undef");
	macros_.erase(name);
}

size_t MacroProcessor::parse_function_parameters(const vector<PPToken>& tokens,
                                                 size_t pos,
                                                 size_t end,
                                                 MacroDefinition& macro)
{
	pos = SkipHorizontalWhitespace(tokens, pos, end);
	if (pos < end && IsOp(tokens[pos], ")"))
		return pos + 1;
	while (pos < end)
	{
		if (IsOp(tokens[pos], "..."))
		{
			macro.variadic = true;
			pos = SkipHorizontalWhitespace(tokens, pos + 1, end);
			if (pos >= end || !IsOp(tokens[pos], ")"))
				ThrowError("expected ')' after variadic parameter");
			return pos + 1;
		}
		if (!IsIdentifier(tokens[pos]) || tokens[pos].text == kVaArgs)
			ThrowError("invalid macro parameter");
		if (macro.parameter_index.count(tokens[pos].text) != 0)
			ThrowError("duplicate macro parameter");
		macro.parameter_index[tokens[pos].text] = macro.parameters.size();
		macro.parameters.push_back(tokens[pos].text);
		pos = SkipHorizontalWhitespace(tokens, pos + 1, end);
		if (pos < end && IsOp(tokens[pos], ")"))
			return pos + 1;
		if (pos >= end || !IsOp(tokens[pos], ","))
			ThrowError("expected ',' or ')' in macro parameter list");
		pos = SkipHorizontalWhitespace(tokens, pos + 1, end);
	}
	ThrowError("unterminated macro parameter list");
	return end;
}

void MacroProcessor::finish_define(const string& name, MacroDefinition& macro)
{
	validate_replacement(macro);
	map<string, MacroDefinition>::iterator existing = macros_.find(name);
	if (existing != macros_.end() && !macro_matches(existing->second, macro))
		ThrowError("macro redefinition differs from existing definition");
	macros_[name] = macro;
}

void MacroProcessor::validate_replacement(const MacroDefinition& macro)
{
	vector<size_t> real;
	for (size_t i = 0; i < macro.replacement.size(); ++i)
	{
		const PPToken& token = macro.replacement[i];
		if (IsRealToken(token))
			real.push_back(i);
		if (IsIdentifier(token, kVaArgs) && !macro.variadic)
			ThrowError("__VA_ARGS__ used outside a variadic macro");
	}
	for (size_t i = 0; i < real.size(); ++i)
	{
		const PPToken& token = macro.replacement[real[i]];
		if (IsHashHash(token) && (i == 0 || i + 1 == real.size()))
			ThrowError("'##' cannot appear at either end of a replacement list");
		if (!macro.function_like || !IsHash(token))
			continue;
		if (i + 1 == real.size())
			ThrowError("'#' must be followed by a macro parameter");
		const PPToken& next = macro.replacement[real[i + 1]];
		if (!IsIdentifier(next) || !IsParameterName(macro, next.text))
			ThrowError("'#' must be followed by a macro parameter");
	}
}

bool MacroProcessor::macro_matches(const MacroDefinition& a,
                                   const MacroDefinition& b)
{
	if (a.function_like != b.function_like ||
	    a.variadic != b.variadic ||
	    a.parameters != b.parameters ||
	    a.replacement.size() != b.replacement.size())
		return false;
	for (size_t i = 0; i < a.replacement.size(); ++i)
	{
		if (!TokenMatchesForRedefinition(a.replacement[i], b.replacement[i]))
			return false;
	}
	return true;
}

vector<PPToken> MacroProcessor::expand_tokens(const vector<PPToken>& tokens)
{
	vector<PPToken> stream = NormalizeWhitespace(tokens, false);
	vector<PPToken> output;
	size_t pos = 0;
	while (pos < stream.size())
	{
		PPToken token = stream[pos];
		if (IsIdentifier(token, kVaArgs))
			ThrowError("__VA_ARGS__ is reserved");
		if (IsIdentifier(token) && is_dynamic_predefined(token.text) &&
		    token.unavailable.count(token.text) == 0)
		{
			vector<PPToken> repl = dynamic_predefined_replacement(token);
			stream.erase(stream.begin() + pos, stream.begin() + pos + 1);
			stream.insert(stream.begin() + pos, repl.begin(), repl.end());
			continue;
		}
		map<string, MacroDefinition>::iterator it = macros_.find(token.text);
		if (IsIdentifier(token) && it != macros_.end() &&
		    token.unavailable.count(token.text) == 0)
		{
			Invocation invocation;
			if (try_build_invocation(stream, pos, it->second, invocation))
			{
				vector<PPToken> repl =
					instantiate(it->second, token, invocation.arguments);
				stream.erase(stream.begin() + pos, stream.begin() + invocation.end_pos);
				stream.insert(stream.begin() + pos, repl.begin(), repl.end());
				continue;
			}
		}
		output.push_back(token);
		++pos;
	}
	return NormalizeWhitespace(output, false);
}

bool MacroProcessor::try_build_invocation(const vector<PPToken>& stream,
                                          size_t pos,
                                          const MacroDefinition& macro,
                                          Invocation& invocation)
{
	if (!macro.function_like)
	{
		invocation.end_pos = pos + 1;
		return true;
	}
	size_t open = pos + 1;
	while (open < stream.size() && IsWhitespace(stream[open]))
		++open;
	if (open >= stream.size() || !IsOp(stream[open], "("))
		return false;
	vector<vector<PPToken> > segments;
	parse_argument_segments(stream, open, segments, invocation.end_pos);
	build_arguments(macro, segments, invocation.arguments);
	return true;
}

void MacroProcessor::parse_argument_segments(const vector<PPToken>& stream,
                                             size_t open_pos,
                                             vector<vector<PPToken> >& segments,
                                             size_t& end_pos)
{
	vector<PPToken> current;
	int depth = 0;
	for (size_t pos = open_pos + 1; pos < stream.size(); ++pos)
	{
		if (IsEnd(stream[pos]))
			break;
		if (IsOp(stream[pos], "("))
		{
			++depth;
			current.push_back(stream[pos]);
		}
		else if (IsOp(stream[pos], ")"))
		{
			if (depth == 0)
			{
				segments.push_back(NormalizeWhitespace(current, false));
				end_pos = pos + 1;
				return;
			}
			--depth;
			current.push_back(stream[pos]);
		}
		else if (IsOp(stream[pos], ",") && depth == 0)
		{
			segments.push_back(NormalizeWhitespace(current, false));
			current.clear();
		}
		else
		{
			current.push_back(stream[pos]);
		}
	}
	ThrowError("unterminated macro invocation");
}

void MacroProcessor::build_arguments(const MacroDefinition& macro,
                                     const vector<vector<PPToken> >& segments,
                                     vector<MacroArgument>& arguments)
{
	const size_t fixed = macro.parameters.size();
	arguments.clear();
	if (!macro.variadic)
	{
		if (fixed == 0 && IsEmptyArgumentListForZeroParam(segments))
			return;
		if (segments.size() != fixed)
			ThrowError("wrong number of macro arguments");
		for (size_t i = 0; i < fixed; ++i)
		{
			MacroArgument arg;
			arg.raw = segments[i];
			arguments.push_back(arg);
		}
		return;
	}
	if (segments.size() < fixed)
		ThrowError("wrong number of macro arguments");
	for (size_t i = 0; i < fixed; ++i)
	{
		MacroArgument arg;
		arg.raw = segments[i];
		arguments.push_back(arg);
	}
	MacroArgument variadic;
	for (size_t i = fixed; i < segments.size(); ++i)
	{
		if (i != fixed)
			variadic.raw.push_back(MakeCommaToken());
		variadic.raw.insert(variadic.raw.end(), segments[i].begin(), segments[i].end());
	}
	if (fixed == 0 && IsEmptyArgumentListForZeroParam(segments))
		variadic.raw.clear();
	arguments.push_back(variadic);
}

vector<PPToken> MacroProcessor::instantiate(const MacroDefinition& macro,
                                            const PPToken& head,
                                            vector<MacroArgument>& arguments)
{
	vector<PPToken> substituted;
	const set<string> paint = BaseInvocationPaint(head, macro);
	for (size_t i = 0; i < macro.replacement.size(); ++i)
	{
		const PPToken& token = macro.replacement[i];
		if (macro.function_like && IsHash(token))
		{
			size_t next = i + 1;
			while (next < macro.replacement.size() && IsWhitespace(macro.replacement[next]))
				++next;
			if (next < macro.replacement.size() && IsIdentifier(macro.replacement[next]) &&
			    IsParameterName(macro, macro.replacement[next].text))
			{
				const size_t arg_index =
					ArgumentIndexForName(macro, macro.replacement[next].text);
				PPToken stringized =
					MakeStringLiteralToken(stringify_argument(arguments[arg_index].raw));
				CopyTokenLocation(stringized, head);
				AddPaint(stringized, paint);
				substituted.push_back(stringized);
				i = next;
				continue;
			}
		}
		if (IsIdentifier(token) && IsParameterName(macro, token.text))
		{
			const bool raw =
				HasPasteBefore(macro.replacement, i) ||
				HasPasteAfter(macro.replacement, i);
			const bool forwarded = ParameterIsForwardedThroughCall(macro, i);
			append_parameter(substituted, macro, head, token.text, raw, forwarded, arguments);
			continue;
		}
		PPToken copy = token;
		CopyTokenLocation(copy, head);
		if (IsHashHash(copy))
			copy.active_paste = true;
		PaintOwnReplacementToken(copy, head, macro, macros_, i);
		substituted.push_back(copy);
	}
	return process_pastes(substituted, head);
}

void MacroProcessor::append_parameter(vector<PPToken>& out,
                                      const MacroDefinition& macro,
                                      const PPToken& head,
                                      const string& name,
                                      bool raw,
                                      bool forwarded_through_call,
                                      vector<MacroArgument>& arguments)
{
	const size_t index = ArgumentIndexForName(macro, name);
	MacroArgument& argument = arguments[index];
	vector<PPToken> tokens =
		raw ? argument.raw : expanded_argument(argument);
	if (!HasRealTokens(tokens))
	{
		if (raw)
			out.push_back(MakePlacemarkerToken());
		return;
	}
	PaintParameterTokens(tokens, head, macro, forwarded_through_call);
	out.insert(out.end(), tokens.begin(), tokens.end());
}

vector<PPToken>& MacroProcessor::expanded_argument(MacroArgument& argument)
{
	if (!argument.expanded_ready)
	{
		argument.expanded = expand_tokens(argument.raw);
		argument.expanded_ready = true;
	}
	return argument.expanded;
}

vector<PPToken> MacroProcessor::process_pastes(vector<PPToken> tokens,
                                               const PPToken& head)
{
	for (size_t pos = 0; pos < tokens.size(); ++pos)
	{
		if (!IsActivePaste(tokens[pos]))
			continue;
		size_t left = pos;
		while (left > 0 && IsWhitespace(tokens[left - 1]))
			--left;
		if (left == 0)
			ThrowError("'##' is missing a left operand");
		--left;
		size_t right = pos + 1;
		while (right < tokens.size() && IsWhitespace(tokens[right]))
			++right;
		if (right >= tokens.size())
			ThrowError("'##' is missing a right operand");

		vector<PPToken> replacement;
		const bool left_empty = tokens[left].kind == PPTokenKind::Placemarker;
		const bool right_empty = tokens[right].kind == PPTokenKind::Placemarker;
		if (!left_empty && !right_empty)
		{
			set<string> paste_paint = tokens[left].unavailable;
			paste_paint.insert(tokens[right].unavailable.begin(),
			                   tokens[right].unavailable.end());
			replacement = TokenizePPString(tokens[left].text + tokens[right].text);
			for (size_t i = 0; i < replacement.size(); ++i)
			{
				CopyTokenLocation(replacement[i], head);
				AddPaint(replacement[i], paste_paint);
				if (IsIdentifier(replacement[i]) &&
				    head.unavailable.count(replacement[i].text) != 0 &&
				    UnavailableNameBlocksHere(
					    macros_,
					    replacement[i].text,
					    NextRealTokenIsOpenParen(replacement, i + 1) ||
						    NextRealTokenIsOpenParen(tokens, right + 1)))
					replacement[i].unavailable.insert(replacement[i].text);
			}
		}
		else if (!left_empty)
		{
			replacement.push_back(tokens[left]);
		}
		else if (!right_empty)
		{
			replacement.push_back(tokens[right]);
		}
		else
		{
			replacement.push_back(MakePlacemarkerToken());
		}
		tokens.erase(tokens.begin() + left, tokens.begin() + right + 1);
		tokens.insert(tokens.begin() + left, replacement.begin(), replacement.end());
		pos = left == 0 ? 0 : left - 1;
	}
	vector<PPToken> out;
	for (size_t i = 0; i < tokens.size(); ++i)
	{
		if (tokens[i].kind != PPTokenKind::Placemarker)
			out.push_back(tokens[i]);
	}
	return NormalizeWhitespace(out, false);
}

string MacroProcessor::stringify_argument(const vector<PPToken>& raw)
{
	string out = "\"";
	bool have_token = false;
	bool pending_space = false;
	for (size_t i = 0; i < raw.size(); ++i)
	{
		if (IsWhitespace(raw[i]))
		{
			pending_space = have_token;
			continue;
		}
		if (pending_space)
			out += ' ';
		pending_space = false;
		have_token = true;
		const bool escape_spelling = EscapesInsideStringizedToken(raw[i]);
		for (size_t j = 0; j < raw[i].text.size(); ++j)
		{
			const char c = raw[i].text[j];
			if ((escape_spelling && (c == '\\' || c == '"')) ||
			    (!escape_spelling && c == '"'))
				out += '\\';
			out += c;
		}
	}
	out += '"';
	return out;
}

void run_macro(istream& in)
{
	PPTokenCollector collector;
	pptoken::run_pptoken(in, collector);
	MacroProcessor processor;
	posttoken::emit_posttokens(processor.process(collector.tokens));
}

}  // namespace macro
