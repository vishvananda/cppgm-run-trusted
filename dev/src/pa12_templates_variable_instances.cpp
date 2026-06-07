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

void Parser::select_variable_template_specialization(
	TemplateDeclaration* declaration,
	const vector<TemplateArgument>& full_args,
	size_t explicit_arg_count,
	TemplateDeclaration*& selected_declaration,
	vector<TemplateArgument>& selected_args)
{
	TemplateMatchParserScope match_scope(this);
	map<Scope*, map<string, vector<TemplateDeclaration*> > >::iterator sit =
		variable_templates_.find(declaration->owner);
	if (sit == variable_templates_.end())
		return;
	map<string, vector<TemplateDeclaration*> >::iterator it =
		sit->second.find(declaration->name);
	if (it == sit->second.end())
		return;
	TemplateDeclaration* best_partial = NULL;
	vector<TemplateArgument> match_args =
		flatten_template_argument_packs(full_args);
	for (size_t i = 0; i < it->second.size(); ++i)
	{
		TemplateDeclaration* candidate = it->second[i];
		if (!candidate->class_specialization)
			continue;
		TemplateMatchParameterScope parameter_scope(&candidate->parameters);
		vector<TemplateArgument> pattern =
			candidate->class_specialization_pattern;
		vector<TemplateArgument> actual = match_args;
		bool matched = false;
		map<string, TemplateArgument> deduced;
		try
		{
			matched = match_template_argument_sequence_pattern(
				pattern,
				actual,
				deduced,
				record_template_arguments_);
			if (!matched && pattern.size() != match_args.size())
			{
				vector<TemplateArgument> completed =
					complete_template_arguments(declaration, pattern);
				if (completed.size() == match_args.size())
				{
					map<string, TemplateArgument> local;
					if (match_template_argument_sequence_pattern(
						    completed,
						    match_args,
						    local,
						    record_template_arguments_))
					{
						pattern = completed;
						actual = match_args;
						deduced = local;
						matched = true;
					}
				}
			}
			if (!matched &&
			    !template_argument_sequence_has_pack_expansion(
				    candidate->class_specialization_pattern) &&
			    candidate->class_specialization_pattern.size() <=
				    match_args.size() &&
			    explicit_arg_count <=
				    candidate->class_specialization_pattern.size())
			{
				bool default_tail = true;
				for (size_t j =
					     candidate->class_specialization_pattern.size();
				     j < match_args.size();
				     ++j)
					if (j >= declaration->parameters.size() ||
					    !declaration->parameters[j].has_default)
						default_tail = false;
				if (default_tail)
				{
					vector<TemplateArgument> prefix(
						match_args.begin(),
						match_args.begin() +
							candidate->class_specialization_pattern.size());
					map<string, TemplateArgument> local;
					if (match_template_argument_sequence_pattern(
						    candidate->class_specialization_pattern,
						    prefix,
						    local,
						    record_template_arguments_))
					{
						pattern =
							candidate->class_specialization_pattern;
						actual = prefix;
						deduced = local;
						matched = true;
					}
				}
			}
			if (matched &&
			    !template_value_patterns_match_after_deduction(
				    this,
				    candidate,
				    pattern,
				    actual,
				    deduced))
				matched = false;
		}
		catch (const runtime_error&)
		{
			matched = false;
		}
		if (!matched)
			continue;
		vector<TemplateArgument> candidate_args;
		for (size_t j = 0; j < candidate->parameters.size(); ++j)
		{
			const string& name = candidate->parameters[j].name;
			map<string, TemplateArgument>::iterator found = deduced.find(name);
			if (found == deduced.end())
			{
				matched = false;
				break;
			}
			candidate_args.push_back(found->second);
		}
		if (!matched)
			continue;
		if (best_partial == NULL ||
		    class_specialization_more_specialized(candidate,
		                                          best_partial,
		                                          record_template_arguments_))
		{
			best_partial = candidate;
			selected_declaration = candidate;
			selected_args = candidate_args;
		}
		else if (!class_specialization_more_specialized(
			         best_partial,
			         candidate,
			         record_template_arguments_))
			throw runtime_error(
				"ambiguous variable template partial specialization");
	}
}

}  // namespace internal
}  // namespace pa12
