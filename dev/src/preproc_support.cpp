#include "preproc_support.h"

#include <algorithm>
#include <fstream>
#include <map>
#include <set>
#include <sstream>
#include <stdexcept>
#include <utility>

#include "ctrlexpr_support.h"
#include "macro_support.h"
#include "posttoken_pipeline.h"
#include "posttoken_support.h"
#include "pptoken_lib.h"

#if defined(__has_include)
#if __has_include("cppgm_builtin_host_config.h")
#include "cppgm_builtin_host_config.h"
#define CPPGM_HAVE_BUILTIN_HOST_CONFIG 1
#endif
#endif

#ifndef CPPGM_HAVE_BUILTIN_HOST_CONFIG
namespace cppgm_builtin_host_config
{
static const char kHostPredefinedMacros[] = "";
static const char * const kStandardIncludePaths[] = { 0 };
}
#endif

using namespace std;

namespace preproc {

MacroCommand::MacroCommand()
	: kind(Define)
{
}

MacroCommand::MacroCommand(Kind kind, const string& value)
	: kind(kind), value(value)
{
}

Options::Options()
	: import_host_predefined_macros(false),
	  import_host_include_paths(false)
{
}

namespace {

typedef pair<unsigned long int, unsigned long int> PA5FileId;

const size_t kNoIncludePathIndex = static_cast<size_t>(-1);

struct IncludeSpec
{
	string name;
	bool angled;

	IncludeSpec() : angled(false) {}
	IncludeSpec(const string& name, bool angled)
		: name(name), angled(angled) {}
};

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
		"include", "include_next", "define", "undef", "line",
		"error", "warning", "pragma"
	};
	for (size_t i = 0; i < sizeof(names) / sizeof(names[0]); ++i)
	{
		if (name == names[i])
			return true;
	}
	return false;
}

bool NameInList(const string& name, const char* const* names, size_t count)
{
	for (size_t i = 0; i < count; ++i)
	{
		if (name == names[i])
			return true;
	}
	return false;
}

bool IsHostedProbeName(const string& name)
{
	static const char* const names[] = {
		"__has_builtin",
		"__has_feature",
		"__has_extension",
		"__has_attribute",
		"__has_cpp_attribute",
		"__building_module",
		"__has_include",
		"__has_include_next",
		"__is_identifier"
	};
	return NameInList(name, names, sizeof(names) / sizeof(names[0]));
}

const char* const kBuiltinProbeNames[] = {
	"__add_lvalue_reference",
	"__add_pointer",
	"__add_rvalue_reference",
	"__array_rank",
	"__builtin_alloca",
	"__builtin_add_overflow",
	"__builtin_addressof",
	"__builtin_assume_aligned",
	"__builtin_bswap16",
	"__builtin_bswap32",
	"__builtin_bswap64",
	"__builtin_clz",
	"__builtin_clzg",
	"__builtin_clzl",
	"__builtin_clzll",
	"__builtin_COLUMN",
	"__builtin_complex",
	"__builtin_ctz",
	"__builtin_ctzl",
	"__builtin_ctzll",
	"__builtin_expect",
	"__builtin_FILE",
	"__builtin_flt_rounds",
	"__builtin_fpclassify",
	"__builtin_FUNCTION",
	"__builtin_huge_val",
	"__builtin_huge_valf",
	"__builtin_huge_vall",
	"__builtin_ia32_emms",
	"__builtin_ia32_femms",
	"__builtin_ia32_pause",
	"__builtin_ia32_sfence",
	"__builtin_inf",
	"__builtin_inff",
	"__builtin_infl",
	"__builtin_invoke",
	"__builtin_isnan",
	"__builtin_is_constant_evaluated",
	"__builtin_LINE",
	"__builtin_memchr",
	"__builtin_memcmp",
	"__builtin_memcpy",
	"__builtin_memmove",
	"__builtin_memset",
	"__builtin_mul_overflow",
	"__builtin_nan",
	"__builtin_nanf",
	"__builtin_nanl",
	"__builtin_nans",
	"__builtin_nansf",
	"__builtin_nansl",
	"__builtin_offsetof",
	"__builtin_operator_delete",
	"__builtin_operator_new",
	"__builtin_popcount",
	"__builtin_popcountg",
	"__builtin_popcountl",
	"__builtin_popcountll",
	"__builtin_prefetch",
	"__builtin_vsnprintf",
	"__builtin_strchr",
	"__builtin_strcmp",
	"__builtin_strlen",
	"__builtin_sub_overflow",
	"__builtin_unreachable",
	"__builtin_va_end",
	"__builtin_va_start",
	"__builtin_bzero",
	"__atomic_add_fetch",
	"__atomic_always_lock_free",
	"__atomic_and_fetch",
	"__atomic_clear",
	"__atomic_compare_exchange",
	"__atomic_compare_exchange_n",
	"__atomic_exchange_n",
	"__atomic_fetch_add",
	"__atomic_fetch_and",
	"__atomic_fetch_or",
	"__atomic_fetch_sub",
	"__atomic_fetch_xor",
	"__atomic_is_lock_free",
	"__atomic_load",
	"__atomic_load_n",
	"__atomic_or_fetch",
	"__atomic_signal_fence",
	"__atomic_store",
	"__atomic_store_n",
	"__atomic_sub_fetch",
	"__atomic_test_and_set",
	"__atomic_thread_fence",
	"__atomic_xor_fetch",
	"__c11_atomic_compare_exchange_strong",
	"__c11_atomic_compare_exchange_weak",
	"__c11_atomic_exchange",
	"__c11_atomic_fetch_add",
	"__c11_atomic_fetch_and",
	"__c11_atomic_fetch_or",
	"__c11_atomic_fetch_sub",
	"__c11_atomic_fetch_xor",
	"__c11_atomic_init",
	"__c11_atomic_is_lock_free",
	"__c11_atomic_load",
	"__c11_atomic_signal_fence",
	"__c11_atomic_store",
	"__c11_atomic_thread_fence",
	"__decay",
	"__has_trivial_constructor",
	"__has_trivial_destructor",
	"__has_virtual_destructor",
	"__integer_pack",
	"__is_abstract",
	"__is_assignable",
	"__is_base_of",
	"__is_class",
	"__is_complete_or_unbounded",
	"__is_constructible",
	"__is_convertible",
	"__is_destructible",
	"__is_empty",
	"__is_enum",
	"__is_final",
	"__is_floating_point",
	"__is_function",
	"__is_integral",
	"__is_invocable",
	"__is_invocable_r",
	"__is_literal_type",
	"__is_member_function_pointer",
	"__is_member_object_pointer",
	"__is_member_pointer",
	"__is_nothrow_assignable",
	"__is_nothrow_constructible",
	"__is_nothrow_invocable",
	"__is_pod",
	"__is_polymorphic",
	"__is_scalar",
	"__is_same",
	"__is_signed",
	"__is_standard_layout",
	"__is_trivial",
	"__is_trivially_assignable",
	"__is_trivially_constructible",
	"__is_trivially_copyable",
	"__is_trivially_destructible",
	"__is_union",
	"__reference_binds_to_temporary",
	"__reference_constructs_from_temporary",
	"__remove_all_extents",
	"__remove_const",
	"__remove_cv",
	"__remove_cvref",
	"__remove_pointer",
	"__remove_reference_t",
	"__remove_volatile",
	"__sync_lock_release",
	"__sync_lock_test_and_set",
	"__underlying_type"
};

bool HasBuiltinProbe(const string& name)
{
	if (name.compare(0, 15, "__builtin_ia32_") == 0)
		return true;
	return NameInList(name,
	                  kBuiltinProbeNames,
	                  sizeof(kBuiltinProbeNames) /
	                  sizeof(kBuiltinProbeNames[0]));
}

bool HasFeatureProbe(const string& name)
{
	static const char* const names[] = {
		"__cxx_binary_literals__",
		"__cxx_variable_templates__",
		"c_atomic",
		"cxx_alias_templates",
		"cxx_alignas",
		"cxx_alignof",
		"cxx_atomic",
		"cxx_auto_type",
		"cxx_decltype",
		"cxx_decltype_incomplete_return_types",
		"cxx_default_function_template_args",
		"cxx_defaulted_functions",
		"cxx_deleted_functions",
		"cxx_exceptions",
		"cxx_explicit_conversions",
		"cxx_generalized_initializers",
		"cxx_inline_namespaces",
		"cxx_lambdas",
		"cxx_local_type_template_args",
		"cxx_noexcept",
		"cxx_nullptr",
		"cxx_override_control",
		"cxx_range_for",
		"cxx_raw_string_literals",
		"cxx_reference_qualified_functions",
		"cxx_rtti",
		"cxx_rvalue_references",
		"cxx_static_assert",
		"cxx_strong_enums",
		"cxx_trailing_return",
		"cxx_unicode_literals",
		"cxx_unrestricted_unions",
		"cxx_variadic_templates",
		"is_constructible",
		"is_pod",
		"is_trivially_constructible"
	};
	return NameInList(name, names, sizeof(names) / sizeof(names[0]));
}

bool HasAttributeProbe(const string& name)
{
	return name == "__using_if_exists__";
}

bool IsLanguageKeywordName(const string& name)
{
	unordered_map<string, ETokenType>::const_iterator found =
		StringToTokenTypeMap.find(name);
	return found != StringToTokenTypeMap.end() &&
	       found->second >= KW_ALIGNAS &&
	       found->second <= KW_WHILE;
}

bool IsIdentifierProbeResult(const string& name)
{
	if (IsLanguageKeywordName(name))
		return false;
	if (IsHostedProbeName(name) || HasBuiltinProbe(name))
		return false;
	return true;
}

void AppendHostStandardIncludePaths(vector<string>& out)
{
	for (size_t i = 0;
	     cppgm_builtin_host_config::kStandardIncludePaths[i] != 0;
	     ++i)
		out.push_back(cppgm_builtin_host_config::kStandardIncludePaths[i]);
}

bool HostPredefinedMacroOwnedByCompiler(const string& name)
{
	return name == "__SIZE_TYPE__";
}

bool NextLogicalLine(const vector<PPToken>& tokens,
                     size_t& pos,
                     vector<PPToken>& line)
{
	line.clear();
	while (pos < tokens.size())
	{
		const PPToken& token = tokens[pos++];
		if (token.kind == PPTokenKind::EndOfFile)
			return !line.empty();
		if (IsNewLine(token))
			return true;
		if (IsRealToken(token))
			line.push_back(token);
	}
	return !line.empty();
}

bool IsIfDirectiveName(const string& name)
{
	return name == "if" || name == "ifdef" || name == "ifndef";
}

bool DetectWholeFileIncludeGuard(const vector<PPToken>& tokens,
                                 string& guard_name)
{
	size_t pos = 0;
	vector<PPToken> line;
	bool found_ifndef = false;
	while (NextLogicalLine(tokens, pos, line))
	{
		if (line.empty())
			continue;
		if (line.size() != 3 ||
		    !IsHash(line[0]) ||
		    !IsIdentifier(line[1], "ifndef") ||
		    !IsIdentifier(line[2]))
			return false;
		guard_name = line[2].text;
		found_ifndef = true;
		break;
	}
	if (!found_ifndef)
		return false;
	bool found_define = false;
	while (NextLogicalLine(tokens, pos, line))
	{
		if (line.empty())
			continue;
		if (line.size() < 3 ||
		    !IsHash(line[0]) ||
		    !IsIdentifier(line[1], "define") ||
		    !IsIdentifier(line[2], guard_name))
			return false;
		found_define = true;
		break;
	}
	if (!found_define)
		return false;
	int depth = 1;
	while (NextLogicalLine(tokens, pos, line))
	{
		if (line.empty())
			continue;
		if (!IsHash(line[0]) || line.size() < 2 || !IsIdentifier(line[1]))
			continue;
		const string directive = line[1].text;
		if (IsIfDirectiveName(directive))
			++depth;
		else if (directive == "endif")
		{
			--depth;
			if (depth == 0)
			{
				while (NextLogicalLine(tokens, pos, line))
					if (!line.empty())
						return false;
				return true;
			}
		}
	}
	return false;
}

class Preprocessor
{
public:
	explicit Preprocessor(const Options& options)
		: include_paths_(options.include_paths),
		  current_include_path_index_(kNoIncludePathIndex),
		  line_delta_(0),
		  import_host_predefined_macros_(options.import_host_predefined_macros)
	{
		if (options.import_host_include_paths)
			AppendHostStandardIncludePaths(include_paths_);
		macros_.initialize_predefined_macros(options.author,
		                                     options.build_date,
		                                     options.build_time);
		if (options.import_host_predefined_macros)
			import_host_predefined_macros();
		apply_command_line_macros(options.macro_commands);
		forced_includes_ = options.forced_includes;
	}

		void process_source_file(const string& srcfile, vector<PPToken>& output)
		{
			for (size_t i = 0; i < forced_includes_.size(); ++i)
				process_forced_include(srcfile, forced_includes_[i], output);
			process_file(srcfile, kNoIncludePathIndex, output);
			if (!if_stack_.empty())
				throw runtime_error("File completed with unmatched #if");
		}

private:
	macro::MacroProcessor macros_;
	set<PA5FileId> once_files_;
	map<PA5FileId, string> include_guard_macros_;
	vector<string> include_paths_;
	vector<string> forced_includes_;
		vector<IfFrame> if_stack_;
		string current_file_;
		size_t current_include_path_index_;
		int line_delta_;
		bool import_host_predefined_macros_;

	bool is_active() const
	{
		return if_stack_.empty() || if_stack_.back().current_active;
	}

	bool is_defined_name(const string& name) const
	{
		if (macros_.is_defined(name))
			return true;
		return import_host_predefined_macros_ && IsHostedProbeName(name);
	}

	void import_host_predefined_macros()
	{
		istringstream input(cppgm_builtin_host_config::kHostPredefinedMacros);
		string line;
		while (getline(input, line))
		{
			if (line.empty())
				continue;
			vector<PPToken> tokens = TokenizePPString(line);
			try
			{
					size_t hash = SkipHorizontalWhitespace(tokens, 0, tokens.size());
					if (hash >= tokens.size() || !IsHash(tokens[hash]))
						continue;
					size_t name = SkipHorizontalWhitespace(tokens, hash + 1,
					                                       tokens.size());
					if (name >= tokens.size() || !IsIdentifier(tokens[name]))
						continue;
					const string directive = tokens[name].text;
					size_t body = name + 1;
					if (directive == "define")
					{
						const size_t macro_name =
							SkipHorizontalWhitespace(tokens, body, tokens.size());
						if (macro_name < tokens.size() &&
						    IsIdentifier(tokens[macro_name]) &&
						    HostPredefinedMacroOwnedByCompiler(tokens[macro_name].text))
							continue;
						macros_.parse_define(tokens, body, tokens.size());
					}
					else if (directive == "undef")
						macros_.parse_undef(tokens, body, tokens.size());
				}
			catch (const exception&)
			{
			}
		}
	}

	void apply_command_line_macros(const vector<MacroCommand>& commands)
	{
		for (size_t i = 0; i < commands.size(); ++i)
		{
			if (commands[i].kind == MacroCommand::Define)
				apply_command_line_define(commands[i].value);
			else
				apply_command_line_undefine(commands[i].value);
		}
	}

	void apply_command_line_define(const string& definition)
	{
		if (definition.empty())
			throw runtime_error("empty command-line macro definition");
		const size_t equals = definition.find('=');
		const string lhs = equals == string::npos
			? definition
			: definition.substr(0, equals);
		const string rhs = equals == string::npos
			? string("1")
			: definition.substr(equals + 1);
		if (lhs.empty())
			throw runtime_error("empty command-line macro name");
		string source = "#define " + lhs;
		if (equals == string::npos || !rhs.empty())
			source += " " + rhs;
		vector<PPToken> tokens = TokenizePPString(source);
		size_t hash = SkipHorizontalWhitespace(tokens, 0, tokens.size());
		size_t name = hash < tokens.size()
			? SkipHorizontalWhitespace(tokens, hash + 1, tokens.size())
			: tokens.size();
		if (hash >= tokens.size() || !IsHash(tokens[hash]) ||
		    name >= tokens.size() || !IsIdentifier(tokens[name], "define"))
			throw runtime_error("invalid command-line macro definition");
		macros_.parse_define(tokens, name + 1, tokens.size());
	}

	void apply_command_line_undefine(const string& name)
	{
		string source = "#undef " + name;
		vector<PPToken> tokens = TokenizePPString(source);
		size_t hash = SkipHorizontalWhitespace(tokens, 0, tokens.size());
		size_t directive = hash < tokens.size()
			? SkipHorizontalWhitespace(tokens, hash + 1, tokens.size())
			: tokens.size();
		if (hash >= tokens.size() || !IsHash(tokens[hash]) ||
		    directive >= tokens.size() ||
		    !IsIdentifier(tokens[directive], "undef"))
			throw runtime_error("invalid command-line macro undefinition");
		macros_.parse_undef(tokens, directive + 1, tokens.size());
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

	void process_forced_include(const string& srcfile,
	                            const string& include,
	                            vector<PPToken>& output)
	{
		const string saved_file = current_file_;
		const size_t saved_index = current_include_path_index_;
		current_file_ = srcfile;
		current_include_path_index_ = kNoIncludePathIndex;
		IncludeSpec spec(include, false);
		size_t include_path_index = kNoIncludePathIndex;
		const string path = resolve_include(spec, false, include_path_index);
		current_file_ = saved_file;
		current_include_path_index_ = saved_index;

		PA5FileId file_id;
		if (PA5GetFileId(path, file_id) && should_skip_file(file_id))
			return;
		process_file(path, include_path_index, output);
	}

		void process_file(const string& path,
		                  size_t include_path_index,
		                  vector<PPToken>& output)
		{
			PA5FileId file_id;
			const bool have_file_id = PA5GetFileId(path, file_id);
			if (have_file_id && should_skip_file(file_id))
				return;
			ifstream in(path.c_str());
			if (!in)
				throw runtime_error("include file not found");

		PPTokenCollector collector;
		collector.source_file = path;
		pptoken::run_pptoken(in, collector);

		const string saved_file = current_file_;
		const size_t saved_include_path_index = current_include_path_index_;
		const int saved_delta = line_delta_;
		const size_t base_depth = if_stack_.size();
		current_file_ = path;
		current_include_path_index_ = include_path_index;
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
		string guard_name;
			if (have_file_id &&
			    DetectWholeFileIncludeGuard(collector.tokens, guard_name) &&
			    is_defined_name(guard_name))
				include_guard_macros_[file_id] = guard_name;

		current_file_ = saved_file;
		current_include_path_index_ = saved_include_path_index;
		line_delta_ = saved_delta;
	}

	bool should_skip_file(const PA5FileId& file_id) const
	{
		if (once_files_.find(file_id) != once_files_.end())
			return true;
		map<PA5FileId, string>::const_iterator guard =
			include_guard_macros_.find(file_id);
		return guard != include_guard_macros_.end() &&
		       is_defined_name(guard->second);
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
			handle_include(line, body, end, false, output);
		else if (name == "include_next")
			handle_include(line, body, end, true, output);
		else if (name == "define")
			macros_.parse_define(line, body, end);
		else if (name == "undef")
			macros_.parse_undef(line, body, end);
		else if (name == "line")
			handle_line(line, body, end, newline_physical_line);
		else if (name == "error")
			throw runtime_error("#error");
		else if (name == "warning")
			return;
		else if (name == "pragma")
			execute_pragma_directive(SliceTokens(line, body, end));
	}

	bool evaluate_condition(const vector<PPToken>& line, size_t begin, size_t end)
	{
		vector<PPToken> expr = SliceTokens(line, begin, end);
		expr = macros_.expand_control_expression(expr);
		expr = replace_control_probes(expr);
		bool result = false;
		ctrlexpr::DefinedPredicate pred =
			[this](const string& name) { return is_defined_name(name); };
		if (!ctrlexpr::evaluate_tokens(expr, pred, result))
			throw runtime_error("invalid controlling expression");
		return result;
	}

	vector<PPToken> significant_tokens(const vector<PPToken>& tokens)
	{
		vector<PPToken> out;
		for (size_t i = 0; i < tokens.size(); ++i)
		{
			if (IsRealToken(tokens[i]))
				out.push_back(tokens[i]);
		}
		return out;
	}

	vector<PPToken> replace_control_probes(const vector<PPToken>& tokens)
	{
		vector<PPToken> out;
		for (size_t pos = 0; pos < tokens.size(); ++pos)
		{
			const bool is_has_builtin = IsIdentifier(tokens[pos], "__has_builtin");
			const bool is_has_feature = IsIdentifier(tokens[pos], "__has_feature");
			const bool is_has_extension = IsIdentifier(tokens[pos], "__has_extension");
			const bool is_has_attribute = IsIdentifier(tokens[pos], "__has_attribute");
			const bool is_has_cpp_attribute =
				IsIdentifier(tokens[pos], "__has_cpp_attribute");
			const bool is_building_module =
				IsIdentifier(tokens[pos], "__building_module");
			const bool is_has_include = IsIdentifier(tokens[pos], "__has_include");
			const bool is_has_include_next =
				IsIdentifier(tokens[pos], "__has_include_next");
			const bool is_is_identifier =
				IsIdentifier(tokens[pos], "__is_identifier");

			if (!is_has_builtin && !is_has_feature && !is_has_extension &&
			    !is_has_attribute && !is_has_cpp_attribute &&
			    !is_building_module && !is_has_include &&
			    !is_has_include_next && !is_is_identifier)
			{
				out.push_back(tokens[pos]);
				continue;
			}

			size_t open = NextRealToken(tokens, pos + 1);
			if (open >= tokens.size() || !IsOp(tokens[open], "("))
			{
				out.push_back(tokens[pos]);
				continue;
			}

			size_t close = tokens.size();
			int depth = 0;
			for (size_t scan = open; scan < tokens.size(); ++scan)
			{
				if (IsOp(tokens[scan], "("))
					++depth;
				else if (IsOp(tokens[scan], ")"))
				{
					--depth;
					if (depth == 0)
					{
						close = scan;
						break;
					}
				}
			}
			if (close == tokens.size())
			{
				out.push_back(tokens[pos]);
				continue;
			}

			bool supported = false;
			vector<PPToken> arg = SliceTokens(tokens, open + 1, close);
			if (is_has_include || is_has_include_next)
				supported = control_include_probe(arg, is_has_include_next);
			else if (is_building_module)
				supported = false;
			else if (is_is_identifier)
				supported = control_is_identifier_probe(arg);
			else
				supported = control_name_probe(arg,
				                               is_has_builtin,
				                               is_has_feature,
				                               is_has_extension,
				                               is_has_attribute,
				                               is_has_cpp_attribute);

			PPToken value(PPTokenKind::PPNumber, supported ? "1" : "0");
			CopyTokenLocation(value, tokens[pos]);
			out.push_back(value);
			pos = close;
		}
		return out;
	}

	bool control_is_identifier_probe(const vector<PPToken>& arg)
	{
		vector<PPToken> significant = significant_tokens(arg);
		if (significant.size() != 1 || !IsIdentifier(significant[0]))
			return false;
		return IsIdentifierProbeResult(significant[0].text);
	}

	bool control_name_probe(const vector<PPToken>& arg,
	                        bool is_has_builtin,
	                        bool is_has_feature,
	                        bool is_has_extension,
	                        bool is_has_attribute,
	                        bool is_has_cpp_attribute)
	{
		vector<PPToken> significant = significant_tokens(arg);
		if (significant.size() != 1 || !IsIdentifier(significant[0]))
			return false;
		const string name = significant[0].text;
		if (is_has_builtin)
			return HasBuiltinProbe(name);
		if (is_has_feature || is_has_extension)
			return HasFeatureProbe(name);
		if (is_has_attribute)
			return HasAttributeProbe(name);
		if (is_has_cpp_attribute)
			return false;
		return false;
	}

	bool control_include_probe(const vector<PPToken>& arg, bool include_next)
	{
		try
		{
			vector<PPToken> expanded = macros_.expand_tokens(arg);
			IncludeSpec spec = include_spec_from_tokens(expanded);
			size_t include_path_index = kNoIncludePathIndex;
			string path;
			return find_include(spec, include_next, path, include_path_index);
		}
		catch (const exception&)
		{
			return false;
		}
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
			condition = is_defined_name(line[pos].text);
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
	                    bool include_next,
	                    vector<PPToken>& output)
	{
		vector<PPToken> operand = SliceTokens(line, begin, end);
		operand = macros_.expand_tokens(operand);
		const IncludeSpec spec = include_spec_from_tokens(operand);
		size_t include_path_index = kNoIncludePathIndex;
		const string include_path =
			resolve_include(spec, include_next, include_path_index);
			PA5FileId file_id;
			if (PA5GetFileId(include_path, file_id) && should_skip_file(file_id))
				return;
			process_file(include_path, include_path_index, output);
		}

	IncludeSpec include_spec_from_tokens(const vector<PPToken>& tokens)
	{
		vector<PPToken> significant = significant_tokens(tokens);
		if (significant.size() == 1)
		{
			const PPToken& token = significant[0];
			if (token.kind == PPTokenKind::HeaderName)
			{
				if (token.text.size() >= 2 &&
				    ((token.text[0] == '"' &&
				      token.text[token.text.size() - 1] == '"') ||
				     (token.text[0] == '<' &&
				      token.text[token.text.size() - 1] == '>')))
					return IncludeSpec(token.text.substr(1,
					                                     token.text.size() - 2),
					                   token.text[0] == '<');
				throw runtime_error("invalid include");
			}
			if (token.kind == PPTokenKind::StringLiteral)
				return IncludeSpec(DecodeStringLiteralUtf8(token), false);
		}
		if (significant.size() >= 2 &&
		    IsOp(significant.front(), "<") &&
		    IsOp(significant.back(), ">"))
		{
			string name;
			for (size_t i = 1; i + 1 < significant.size(); ++i)
				name += significant[i].text;
			if (!name.empty())
				return IncludeSpec(name, true);
		}
		throw runtime_error("invalid include");
	}

	bool find_include(const IncludeSpec& spec,
	                  bool include_next,
	                  string& path,
	                  size_t& include_path_index)
	{
		if (!include_next && !spec.angled)
		{
			const size_t slash = current_file_.rfind('/');
			if (slash != string::npos)
			{
				const string pathrel =
					current_file_.substr(0, slash + 1) + spec.name;
				PA5FileId id;
				if (PA5GetFileId(pathrel, id))
				{
					path = pathrel;
					include_path_index = kNoIncludePathIndex;
					return true;
				}
			}
		}
		size_t begin = 0;
		if (include_next &&
		    current_include_path_index_ != kNoIncludePathIndex)
			begin = current_include_path_index_ + 1;
		for (size_t i = begin; i < include_paths_.size(); ++i)
		{
			string candidate = include_paths_[i];
			if (!candidate.empty() && candidate[candidate.size() - 1] != '/')
				candidate += "/";
			candidate += spec.name;
			PA5FileId id;
			if (PA5GetFileId(candidate, id))
			{
				path = candidate;
				include_path_index = i;
				return true;
			}
		}
		if (!include_next)
		{
			PA5FileId id;
			if (PA5GetFileId(spec.name, id))
			{
				path = spec.name;
				include_path_index = kNoIncludePathIndex;
				return true;
			}
		}
		return false;
	}

	string resolve_include(const IncludeSpec& spec,
	                       bool include_next,
	                       size_t& include_path_index)
	{
		string path;
		if (find_include(spec, include_next, path, include_path_index))
			return path;
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
