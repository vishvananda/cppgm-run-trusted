#pragma once

#include <cstddef>
#include <istream>
#include <map>
#include <string>
#include <vector>

using namespace std;

#include "pp_token.h"

namespace macro {

struct MacroArgument
{
	vector<PPToken> raw;
	vector<PPToken> expanded;
	bool expanded_ready;

	MacroArgument() : expanded_ready(false) {}
};

struct MacroDefinition
{
	string name;
	bool function_like;
	bool variadic;
	vector<string> parameters;
	vector<PPToken> replacement;
	map<string, size_t> parameter_index;

	MacroDefinition() : function_like(false), variadic(false) {}
};

struct Invocation
{
	size_t end_pos;
	vector<MacroArgument> arguments;

	Invocation() : end_pos(0) {}
};

class MacroProcessor
{
public:
	MacroProcessor();

	vector<PPToken> process(const vector<PPToken>& tokens);
	vector<PPToken> expand_tokens(const vector<PPToken>& tokens);
	vector<PPToken> expand_control_expression(const vector<PPToken>& tokens);

	void parse_define(const vector<PPToken>& tokens, size_t pos, size_t end);
	void parse_undef(const vector<PPToken>& tokens, size_t pos, size_t end);
	bool is_defined(const string& name) const;

	void define_object_macro(const string& name,
	                         const vector<PPToken>& replacement);
	void initialize_predefined_macros(const string& author,
	                                  const string& build_date,
	                                  const string& build_time);

private:
	map<string, MacroDefinition> macros_;
	string build_date_;
	string build_time_;
	bool predefined_enabled_;

	void flush_text(vector<PPToken>& text, vector<PPToken>& output);
	size_t parse_directive(const vector<PPToken>& tokens, size_t hash_pos);
	size_t find_directive_end(const vector<PPToken>& tokens, size_t hash_pos);
	size_t parse_function_parameters(const vector<PPToken>& tokens,
	                                 size_t pos,
	                                 size_t end,
	                                 MacroDefinition& macro);
	void finish_define(const string& name, MacroDefinition& macro);
	void validate_replacement(const MacroDefinition& macro);
	bool macro_matches(const MacroDefinition& a, const MacroDefinition& b);

	bool try_build_invocation(const vector<PPToken>& stream,
	                          size_t pos,
	                          const MacroDefinition& macro,
	                          Invocation& invocation);
	void parse_argument_segments(const vector<PPToken>& stream,
	                             size_t open_pos,
	                             vector<vector<PPToken> >& segments,
	                             size_t& end_pos);
	void build_arguments(const MacroDefinition& macro,
	                     const vector<vector<PPToken> >& segments,
	                     vector<MacroArgument>& arguments);
	vector<PPToken> instantiate(const MacroDefinition& macro,
	                            const PPToken& head,
	                            vector<MacroArgument>& arguments);
	void append_parameter(vector<PPToken>& out,
	                      const MacroDefinition& macro,
	                      const PPToken& head,
	                      const string& name,
	                      bool raw,
	                      bool forwarded_through_call,
	                      vector<MacroArgument>& arguments);
	vector<PPToken>& expanded_argument(MacroArgument& argument);
	vector<PPToken> process_pastes(vector<PPToken> tokens, const PPToken& head);
	string stringify_argument(const vector<PPToken>& raw);

	bool is_dynamic_predefined(const string& name) const;
	vector<PPToken> dynamic_predefined_replacement(const PPToken& head) const;
};

void run_macro(istream& in);

}  // namespace macro
