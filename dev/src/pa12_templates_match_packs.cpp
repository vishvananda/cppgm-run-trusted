#include "pa12_templates_instance_support.h"

#include <algorithm>
#include <cstdint>
#include <sstream>
#include <stdexcept>
#include <utility>

#include "posttoken_pipeline.h"
#include "pp_token.h"

using namespace std;

namespace pa12 {
namespace internal {


bool match_pack_expansion_pattern(
	const TemplateArgument& pattern,
	const vector<TemplateArgument>& actual,
	size_t begin,
	size_t end,
	map<string, TemplateArgument>& deduced,
	const map<const void*, vector<TemplateArgument> >& record_arguments)
{
	string pack_name;
	if (!pack_expansion_parameter_name(pattern, pack_name))
		return false;
	TemplateArgument element_pattern =
		pattern.kind == TemplateArgumentKind::Pack &&
		pattern.pack.size() == 1
		? pattern.pack[0]
		: pattern;
	element_pattern.pack_expansion = false;
	map<string, TemplateArgument> local = deduced;
	map<string, TemplateArgument>::iterator existing_pack =
		local.find(pack_name);
	bool have_existing_pack = existing_pack != local.end();
	TemplateArgument existing_pack_value =
		have_existing_pack ? existing_pack->second : TemplateArgument();
	local.erase(pack_name);
	vector<TemplateArgument> pack;
	for (size_t i = begin; i < end; ++i)
	{
		if (simple_pack_expansion_pattern(element_pattern, pack_name))
		{
			if (element_pattern.kind != actual[i].kind)
				return false;
			pack.push_back(actual[i]);
			continue;
		}
		map<string, TemplateArgument> per_element = local;
		if (!match_template_argument_pattern(element_pattern,
		                                     actual[i],
		                                     per_element,
		                                     record_arguments))
			return false;
		map<string, TemplateArgument>::iterator found =
			per_element.find(pack_name);
		if (found == per_element.end())
			return false;
		pack.push_back(found->second);
		per_element.erase(found);
		for (map<string, TemplateArgument>::const_iterator it =
			     per_element.begin();
		     it != per_element.end();
		     ++it)
			if (!merge_deduced_template_argument(local,
			                                     it->first,
			                                     it->second,
			                                     record_arguments))
				return false;
	}
	TemplateArgument matched_pack = TemplateArgument::pack_arg(pack);
	matched_pack.value_name = pack_name;
	if (have_existing_pack)
	{
		if (!same_template_argument_value(existing_pack_value,
		                                  matched_pack,
		                                  record_arguments))
			return false;
		local[pack_name] = existing_pack_value;
	}
	else if (!merge_deduced_template_argument(local,
	                                          pack_name,
	                                          matched_pack,
	                                          record_arguments))
		return false;
	deduced = local;
	return true;
}

bool match_dependent_alias_projection_argument(
	const TemplateArgument& argument,
	TypePtr alias_pattern,
	TypePtr actual,
	map<string, TemplateArgument>& deduced,
	const map<const void*, vector<TemplateArgument> >& record_arguments)
{
	if (argument.kind == TemplateArgumentKind::Type &&
	    argument.type.get() != NULL)
	{
		if (!template_argument_has_template_parameter(argument,
		                                             record_arguments))
			return false;
		map<string, TemplateArgument> local = deduced;
		bool projected = false;
		try
		{
			projected = match_template_type_pattern(argument.type,
			                                       actual,
			                                       local,
			                                       record_arguments);
		}
		catch (const exception&)
		{
		}
		if (projected)
		{
			deduced = local;
			return true;
		}
		return false;
	}
	if (argument.kind == TemplateArgumentKind::Pack)
	{
		for (size_t i = 0; i < argument.pack.size(); ++i)
		{
			map<string, TemplateArgument> local = deduced;
			if (match_dependent_alias_projection_argument(
				    argument.pack[i],
				    alias_pattern,
				    actual,
				    local,
				    record_arguments))
			{
				deduced = local;
				return true;
			}
		}
	}
	return false;
}

bool match_dependent_alias_projection(
	TypePtr alias_pattern,
	TypePtr actual,
	map<string, TemplateArgument>& deduced,
	const map<const void*, vector<TemplateArgument> >& record_arguments)
{
	if (alias_pattern.get() == NULL ||
	    !alias_pattern->is_dependent_typename ||
	    alias_pattern->dependent_typename_qualified ||
	    !alias_pattern->dependent_typename_template_id ||
	    alias_pattern->template_arguments.empty())
		return false;
	if (active_template_match_parser != NULL)
	{
		map<string, TemplateArgument> local = deduced;
		try
		{
			TypePtr expanded =
				active_template_match_parser
					->expand_alias_template_for_match(alias_pattern,
					                                  local);
			if (expanded.get() != NULL &&
			    expanded.get() != alias_pattern.get() &&
			    match_template_type_pattern(expanded,
			                                actual,
			                                local,
			                                record_arguments))
			{
				deduced = local;
				return true;
			}
		}
		catch (const runtime_error&)
		{
		}
	}
	for (size_t i = 0; i < alias_pattern->template_arguments.size(); ++i)
	{
		TemplateArgument argument =
			raw_template_argument_from_instance_argument(
				alias_pattern->template_arguments[i]);
		map<string, TemplateArgument> local = deduced;
		if (match_dependent_alias_projection_argument(argument,
		                                              alias_pattern,
		                                              actual,
		                                              local,
		                                              record_arguments))
		{
			deduced = local;
			return true;
		}
	}
	return false;
}

namespace {

string sequence_match_deduced_key(
	const map<string, TemplateArgument>& deduced)
{
	ostringstream out;
	for (map<string, TemplateArgument>::const_iterator it = deduced.begin();
	     it != deduced.end();
	     ++it)
		out << it->first << "=" << template_argument_key_part(it->second)
		    << ";";
	return out.str();
}

struct SequenceMatchMemoKey
{
	const vector<TemplateArgument>* pattern;
	const vector<TemplateArgument>* actual;
	const map<const void*, vector<TemplateArgument> >* record_arguments;
	Parser* parser;
	const vector<TemplateParameterInfo>* parameters;
	size_t pattern_index;
	size_t actual_index;
	string deduced;

	bool operator<(const SequenceMatchMemoKey& other) const
	{
		if (pattern != other.pattern)
			return pattern < other.pattern;
		if (actual != other.actual)
			return actual < other.actual;
		if (record_arguments != other.record_arguments)
			return record_arguments < other.record_arguments;
		if (parser != other.parser)
			return parser < other.parser;
		if (parameters != other.parameters)
			return parameters < other.parameters;
		if (pattern_index != other.pattern_index)
			return pattern_index < other.pattern_index;
		if (actual_index != other.actual_index)
			return actual_index < other.actual_index;
		return deduced < other.deduced;
	}
};

struct SequenceMatchMemoValue
{
	bool matched;
	map<string, TemplateArgument> deduced;
};

typedef map<SequenceMatchMemoKey, SequenceMatchMemoValue> SequenceMatchMemo;

bool match_template_argument_sequence_pattern_from_memo(
	const vector<TemplateArgument>& pattern,
	size_t pattern_index,
	const vector<TemplateArgument>& actual,
	size_t actual_index,
	map<string, TemplateArgument>& deduced,
	const map<const void*, vector<TemplateArgument> >& record_arguments,
	SequenceMatchMemo& memo)
{
	SequenceMatchMemoKey memo_key;
	memo_key.pattern = &pattern;
	memo_key.actual = &actual;
	memo_key.record_arguments = &record_arguments;
	memo_key.parser = active_template_match_parser;
	memo_key.parameters = active_template_match_parameters;
	memo_key.pattern_index = pattern_index;
	memo_key.actual_index = actual_index;
	memo_key.deduced = sequence_match_deduced_key(deduced);
	SequenceMatchMemo::const_iterator memoized = memo.find(memo_key);
	if (memoized != memo.end())
	{
		if (memoized->second.matched)
			deduced = memoized->second.deduced;
		return memoized->second.matched;
	}
	SequenceMatchMemoValue memo_value;
	memo_value.matched = false;
	if (pattern_index == pattern.size())
	{
		memo_value.matched = actual_index == actual.size();
		if (memo_value.matched)
			memo_value.deduced = deduced;
		memo[memo_key] = memo_value;
		return memo_value.matched;
	}
	const TemplateArgument& current = pattern[pattern_index];
	string pack_pattern_name;
	if (current.pack_expansion ||
	    pack_argument_parameter_name(current, pack_pattern_name))
	{
		for (size_t end = actual_index; end <= actual.size(); ++end)
		{
			map<string, TemplateArgument> local = deduced;
			if (!match_pack_expansion_pattern(current,
			                                  actual,
			                                  actual_index,
			                                  end,
			                                  local,
			                                  record_arguments))
				continue;
			if (match_template_argument_sequence_pattern_from_memo(
				    pattern,
				    pattern_index + 1,
				    actual,
				    end,
				    local,
				    record_arguments,
				    memo))
			{
				deduced = local;
				memo_value.matched = true;
				memo_value.deduced = deduced;
				memo[memo_key] = memo_value;
				return true;
			}
		}
		memo[memo_key] = memo_value;
		return false;
	}
		if (actual_index == actual.size())
		{
			memo[memo_key] = memo_value;
			return false;
		}
		bool current_active_template_template_pattern =
			current.kind == TemplateArgumentKind::Type &&
			current.type.get() != NULL &&
			current.type->is_dependent_typename &&
			current.type->dependent_typename_template_id &&
			!current.type->template_primary_name.empty() &&
			active_match_parameter_is_template_template(
				current.type->template_primary_name);
		if (current.kind == TemplateArgumentKind::Type &&
		    current.type.get() != NULL &&
		    current.type->is_dependent_typename &&
		    actual[actual_index].kind == TemplateArgumentKind::Type &&
		    active_template_match_parser != NULL &&
		    !current_active_template_template_pattern)
		{
		TypePtr actual_bare = pa11::strip_cv(actual[actual_index].type);
		bool actual_plain_template_parameter =
			actual_bare.get() != NULL &&
			actual_bare->kind == pa11::TypeKind::TemplateParameter &&
			!actual_bare->is_dependent_typename;
		if (!actual_plain_template_parameter)
		{
			map<string, TemplateArgument> local = deduced;
			if (match_template_argument_sequence_pattern_from_memo(
				    pattern,
				    pattern_index + 1,
				    actual,
				    actual_index + 1,
				    local,
				    record_arguments,
				    memo))
			{
				try
				{
					TypePtr substituted =
						active_template_match_parser
							->substitute_type_for_template_match(
								current.type,
								local);
					if (match_template_type_pattern(
						    substituted,
						    actual[actual_index].type,
						    local,
						    record_arguments))
					{
						deduced = local;
						memo_value.matched = true;
						memo_value.deduced = deduced;
						memo[memo_key] = memo_value;
						return true;
					}
				}
				catch (const runtime_error&)
				{
				}
				if (match_dependent_alias_projection(current.type,
				                                     actual[actual_index].type,
				                                     local,
				                                     record_arguments))
				{
					deduced = local;
					memo_value.matched = true;
					memo_value.deduced = deduced;
					memo[memo_key] = memo_value;
					return true;
				}
			}
		}
	}
	map<string, TemplateArgument> local = deduced;
	if (!match_template_argument_pattern(current,
	                                     actual[actual_index],
	                                     local,
	                                     record_arguments))
	{
		memo[memo_key] = memo_value;
		return false;
	}
	if (!match_template_argument_sequence_pattern_from_memo(pattern,
	                                                        pattern_index + 1,
	                                                        actual,
	                                                        actual_index + 1,
	                                                        local,
	                                                        record_arguments,
	                                                        memo))
	{
		memo[memo_key] = memo_value;
		return false;
	}
	deduced = local;
	memo_value.matched = true;
	memo_value.deduced = deduced;
	memo[memo_key] = memo_value;
	return true;
}

}  // namespace

bool match_template_argument_sequence_pattern_from(
	const vector<TemplateArgument>& pattern,
	size_t pattern_index,
	const vector<TemplateArgument>& actual,
	size_t actual_index,
	map<string, TemplateArgument>& deduced,
	const map<const void*, vector<TemplateArgument> >& record_arguments)
{
	SequenceMatchMemo memo;
	return match_template_argument_sequence_pattern_from_memo(pattern,
	                                                          pattern_index,
	                                                          actual,
	                                                          actual_index,
	                                                          deduced,
	                                                          record_arguments,
	                                                          memo);
}

bool match_template_argument_sequence_pattern(
	const vector<TemplateArgument>& pattern,
	const vector<TemplateArgument>& actual,
	map<string, TemplateArgument>& deduced,
	const map<const void*, vector<TemplateArgument> >& record_arguments)
{
	return match_template_argument_sequence_pattern_from(pattern,
	                                                    0,
	                                                    actual,
	                                                    0,
	                                                    deduced,
	                                                    record_arguments);
}

bool template_value_patterns_match_after_deduction(
	Parser* parser,
	TemplateDeclaration* specialization,
	const TemplateArgument& pattern,
	const TemplateArgument& actual,
	const map<string, TemplateArgument>& deduced)
{
	if (pattern.kind == TemplateArgumentKind::Value &&
	    pattern.dependent &&
	    pattern.value_expr_end > pattern.value_expr_begin)
	{
		if (actual.kind == TemplateArgumentKind::Pack && parser != NULL)
		{
			TemplateArgument evaluated;
			if (parser->try_evaluate_template_value_argument_for_template_match(
				    specialization,
				    pattern,
				    deduced,
				    evaluated))
			{
				map<const void*, vector<TemplateArgument> >
					empty_record_arguments;
				return same_template_argument_value(evaluated,
				                                    actual,
				                                    empty_record_arguments);
			}
		}
		if (actual.kind != TemplateArgumentKind::Value ||
		    actual.dependent)
			return true;
		return parser->template_value_argument_matches_for_template_match(
			specialization,
			pattern,
			actual,
			deduced);
	}
	if (pattern.kind == TemplateArgumentKind::Pack)
	{
		if (actual.kind != TemplateArgumentKind::Pack ||
		    pattern.pack.size() != actual.pack.size())
			return false;
		for (size_t i = 0; i < pattern.pack.size(); ++i)
			if (!template_value_patterns_match_after_deduction(
				    parser,
				    specialization,
				    pattern.pack[i],
				    actual.pack[i],
				    deduced))
				return false;
	}
	return true;
}

bool template_value_patterns_match_after_deduction(
	Parser* parser,
	TemplateDeclaration* specialization,
	const vector<TemplateArgument>& pattern,
	const vector<TemplateArgument>& actual,
	const map<string, TemplateArgument>& deduced)
{
	if (parser == NULL || pattern.size() != actual.size())
		return parser != NULL;
	for (size_t i = 0; i < pattern.size(); ++i)
		if (!template_value_patterns_match_after_deduction(
			    parser,
			    specialization,
			    pattern[i],
			    actual[i],
			    deduced))
			return false;
	return true;
}

bool template_argument_sequence_has_pack_expansion(
	const vector<TemplateArgument>& pattern)
{
	for (size_t i = 0; i < pattern.size(); ++i)
		if (pattern[i].pack_expansion)
			return true;
	return false;
}

}  // namespace internal
}  // namespace pa12
