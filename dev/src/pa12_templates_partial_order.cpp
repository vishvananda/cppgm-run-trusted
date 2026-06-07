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

void collect_template_parameter_occurrences_from_instance(
	const pa11::TemplateInstanceArgument& argument,
	map<string, int>& occurrences);

void collect_template_parameter_occurrences(
	const TemplateArgument& argument,
	map<string, int>& occurrences,
	const map<const void*, vector<TemplateArgument> >& record_arguments);

void collect_template_parameter_occurrences_from_type(
	TypePtr type,
	map<string, int>& occurrences,
	const map<const void*, vector<TemplateArgument> >& record_arguments)
{
	if (type.get() == NULL)
		return;
	type = pa11::strip_cv(type);
	if (type->kind == pa11::TypeKind::TemplateParameter)
	{
		if (!type->is_dependent_typename &&
		    pa11::is_deducible_template_parameter_type(type))
			++occurrences[type->name];
		if (type->is_dependent_typename)
			for (size_t i = 0; i < type->template_arguments.size(); ++i)
				collect_template_parameter_occurrences_from_instance(
					type->template_arguments[i],
					occurrences);
		return;
	}
	if (type->kind == pa11::TypeKind::Pointer ||
	    type->kind == pa11::TypeKind::LValueReference ||
	    type->kind == pa11::TypeKind::RValueReference ||
	    type->kind == pa11::TypeKind::Array)
	{
		collect_template_parameter_occurrences_from_type(type->base,
		                                                 occurrences,
		                                                 record_arguments);
		return;
	}
	if (type->kind == pa11::TypeKind::Function)
	{
		collect_template_parameter_occurrences_from_type(type->base,
		                                                 occurrences,
		                                                 record_arguments);
		for (size_t i = 0; i < type->parameters.size(); ++i)
			collect_template_parameter_occurrences_from_type(
				type->parameters[i],
				occurrences,
				record_arguments);
		return;
	}
	if (type->kind == pa11::TypeKind::MemberPointer)
	{
		collect_template_parameter_occurrences_from_type(type->member_class,
		                                                 occurrences,
		                                                 record_arguments);
		collect_template_parameter_occurrences_from_type(type->base,
		                                                 occurrences,
		                                                 record_arguments);
		return;
	}
	if (type->kind == pa11::TypeKind::Record &&
	    type->is_template_specialization)
	{
		if (type->scope == NULL && !type->template_primary_name.empty())
			++occurrences[type->template_primary_name];
		map<const void*, vector<TemplateArgument> >::const_iterator args =
			record_arguments.find(type.get());
		if (args != record_arguments.end())
		{
			for (size_t i = 0; i < args->second.size(); ++i)
				collect_template_parameter_occurrences(
					args->second[i],
					occurrences,
					record_arguments);
			return;
		}
		for (size_t i = 0; i < type->template_arguments.size(); ++i)
			collect_template_parameter_occurrences_from_instance(
				type->template_arguments[i],
				occurrences);
	}
}

void collect_template_parameter_occurrences_from_instance(
	const pa11::TemplateInstanceArgument& argument,
	map<string, int>& occurrences)
{
	if (argument.kind == pa11::TemplateInstanceArgumentKind::Type)
		collect_template_parameter_occurrences_from_type(
			argument.type,
			occurrences,
			map<const void*, vector<TemplateArgument> >());
	else if (argument.kind == pa11::TemplateInstanceArgumentKind::Value)
	{
		if (argument.dependent && !argument.value_name.empty())
			++occurrences[argument.value_name];
		collect_template_parameter_occurrences_from_type(
			argument.type,
			occurrences,
			map<const void*, vector<TemplateArgument> >());
	}
	else if (argument.kind == pa11::TemplateInstanceArgumentKind::Template)
		++occurrences[argument.template_name];
	else
		for (size_t i = 0; i < argument.pack.size(); ++i)
			collect_template_parameter_occurrences_from_instance(
				argument.pack[i],
				occurrences);
}

void collect_template_parameter_occurrences(
	const TemplateArgument& argument,
	map<string, int>& occurrences,
	const map<const void*, vector<TemplateArgument> >& record_arguments)
{
	if (argument.kind == TemplateArgumentKind::Type)
		collect_template_parameter_occurrences_from_type(argument.type,
		                                                 occurrences,
		                                                 record_arguments);
	else if (argument.kind == TemplateArgumentKind::Value)
	{
		if (argument.dependent && !argument.value_name.empty())
			++occurrences[argument.value_name];
		collect_template_parameter_occurrences_from_type(argument.type,
		                                                 occurrences,
		                                                 record_arguments);
	}
	else if (argument.kind == TemplateArgumentKind::Template)
	{
		if (argument.template_declaration == NULL &&
		    !argument.value_name.empty())
			++occurrences[argument.value_name];
	}
	else
		for (size_t i = 0; i < argument.pack.size(); ++i)
			collect_template_parameter_occurrences(argument.pack[i],
			                                       occurrences,
			                                       record_arguments);
}

int repeated_template_parameter_score(
	const vector<TemplateArgument>& pattern,
	const map<const void*, vector<TemplateArgument> >& record_arguments)
{
	map<string, int> occurrences;
	for (size_t i = 0; i < pattern.size(); ++i)
		collect_template_parameter_occurrences(pattern[i],
		                                       occurrences,
		                                       record_arguments);
	int score = 0;
	for (map<string, int>::const_iterator it = occurrences.begin();
	     it != occurrences.end();
	     ++it)
		if (it->second > 1)
			score += it->second - 1;
	return score;
}

int cv_qualified_direct_parameter_score(
	const vector<TemplateArgument>& pattern)
{
	int score = 0;
	for (size_t i = 0; i < pattern.size(); ++i)
	{
		if (pattern[i].kind != TemplateArgumentKind::Type ||
		    pattern[i].type.get() == NULL)
			continue;
		TypePtr type = pattern[i].type;
		if (type->kind == pa11::TypeKind::Cv &&
		    type->cv != 0 &&
		    deducible_template_parameter_type(type->base))
			++score;
	}
	return score;
}

int fixed_template_argument_score(const vector<TemplateArgument>& pattern)
{
	int score = 0;
	for (size_t i = 0; i < pattern.size(); ++i)
	{
		string pack_name;
		if (pattern[i].pack_expansion ||
		    pack_argument_parameter_name(pattern[i], pack_name))
			continue;
		if (pattern[i].kind == TemplateArgumentKind::Type &&
		    pattern[i].type.get() != NULL &&
		    deducible_template_parameter_type(pattern[i].type))
			continue;
		if (pattern[i].kind == TemplateArgumentKind::Value &&
		    pattern[i].dependent &&
		    !pattern[i].value_name.empty() &&
		    pattern[i].value_expr_begin == pattern[i].value_expr_end &&
		    pattern[i].value_owner_template_name.empty() &&
		    pattern[i].value_member_name.empty())
			continue;
		if (pattern[i].kind == TemplateArgumentKind::Template &&
		    pattern[i].template_declaration == NULL &&
		    !pattern[i].value_name.empty())
			continue;
		++score;
	}
	return score;
}

bool declaration_parameter_is_pack(const TemplateDeclaration* declaration,
                                   const string& name);

int pack_pattern_penalty_type(
	TypePtr type,
	const TemplateDeclaration* declaration,
	const map<const void*, vector<TemplateArgument> >& record_arguments);

int pack_pattern_penalty_argument(
	const TemplateArgument& argument,
	const TemplateDeclaration* declaration,
	const map<const void*, vector<TemplateArgument> >& record_arguments)
{
	string pack_name;
	if (argument.pack_expansion)
		return 1;
	if (pack_argument_parameter_name(argument, pack_name) &&
	    declaration_parameter_is_pack(declaration, pack_name))
		return 1;
	int penalty = 0;
	if (argument.kind == TemplateArgumentKind::Type)
		penalty += pack_pattern_penalty_type(argument.type,
		                                     declaration,
		                                     record_arguments);
	else if (argument.kind == TemplateArgumentKind::Value)
		penalty += pack_pattern_penalty_type(argument.type,
		                                     declaration,
		                                     record_arguments);
	else if (argument.kind == TemplateArgumentKind::Pack)
		for (size_t i = 0; i < argument.pack.size(); ++i)
			penalty += pack_pattern_penalty_argument(
				argument.pack[i],
				declaration,
				record_arguments);
	return penalty;
}

int pack_pattern_penalty_instance(
	const pa11::TemplateInstanceArgument& argument,
	const TemplateDeclaration* declaration,
	const map<const void*, vector<TemplateArgument> >& record_arguments)
{
	if (argument.kind == pa11::TemplateInstanceArgumentKind::Pack)
	{
		if (argument.pack.size() == 1 &&
		    argument.pack[0].kind ==
			    pa11::TemplateInstanceArgumentKind::Type &&
		    argument.pack[0].type.get() != NULL)
		{
			TypePtr element = pa11::strip_cv(argument.pack[0].type);
			if (element->kind == pa11::TypeKind::TemplateParameter &&
			    declaration_parameter_is_pack(declaration, element->name))
				return 1;
		}
		int nested = 0;
		for (size_t i = 0; i < argument.pack.size(); ++i)
			nested += pack_pattern_penalty_instance(argument.pack[i],
			                                        declaration,
			                                        record_arguments);
		return nested;
	}
	int penalty = 0;
	if (argument.kind == pa11::TemplateInstanceArgumentKind::Type ||
	    argument.kind == pa11::TemplateInstanceArgumentKind::Value)
		penalty += pack_pattern_penalty_type(argument.type,
		                                     declaration,
		                                     record_arguments);
	for (size_t i = 0;
	     i < argument.value_owner_template_arguments.size();
	     ++i)
		penalty += pack_pattern_penalty_instance(
			argument.value_owner_template_arguments[i],
			declaration,
			record_arguments);
	return penalty;
}

int pack_pattern_penalty_type(
	TypePtr type,
	const TemplateDeclaration* declaration,
	const map<const void*, vector<TemplateArgument> >& record_arguments)
{
	if (type.get() == NULL)
		return 0;
	TypePtr bare = pa11::strip_cv(type);
	if (bare->kind == pa11::TypeKind::Pointer ||
	    bare->kind == pa11::TypeKind::LValueReference ||
	    bare->kind == pa11::TypeKind::RValueReference ||
	    bare->kind == pa11::TypeKind::Array)
		return pack_pattern_penalty_type(bare->base,
		                                 declaration,
		                                 record_arguments);
	if (bare->kind == pa11::TypeKind::Function)
	{
		int penalty = pack_pattern_penalty_type(bare->base,
		                                        declaration,
		                                        record_arguments);
		for (size_t i = 0; i < bare->parameters.size(); ++i)
			penalty += pack_pattern_penalty_type(bare->parameters[i],
			                                     declaration,
			                                     record_arguments);
		return penalty;
	}
	if (bare->kind == pa11::TypeKind::MemberPointer)
		return pack_pattern_penalty_type(bare->member_class,
		                                 declaration,
		                                 record_arguments) +
		       pack_pattern_penalty_type(bare->base,
		                                 declaration,
		                                 record_arguments);
	int penalty = 0;
	map<const void*, vector<TemplateArgument> >::const_iterator stored =
		record_arguments.find(bare.get());
	if (stored != record_arguments.end())
		for (size_t i = 0; i < stored->second.size(); ++i)
			penalty += pack_pattern_penalty_argument(stored->second[i],
			                                         declaration,
			                                         record_arguments);
	for (size_t i = 0; i < bare->template_arguments.size(); ++i)
		penalty += pack_pattern_penalty_instance(
			bare->template_arguments[i],
			declaration,
			record_arguments);
	return penalty;
}

int pack_pattern_penalty(
	const vector<TemplateArgument>& pattern,
	const TemplateDeclaration* declaration,
	const map<const void*, vector<TemplateArgument> >& record_arguments)
{
	int penalty = 0;
	for (size_t i = 0; i < pattern.size(); ++i)
		penalty += pack_pattern_penalty_argument(pattern[i],
		                                         declaration,
		                                         record_arguments);
	return penalty;
}

bool declaration_parameter_is_pack(const TemplateDeclaration* declaration,
                                   const string& name)
{
	if (declaration == NULL)
	{
		return false;
	}
	for (size_t i = 0; i < declaration->parameters.size(); ++i)
		if (declaration->parameters[i].name == name)
			return declaration->parameters[i].is_pack;
	return false;
}

int nonpack_type_score(TypePtr type, const TemplateDeclaration* declaration);

int nonpack_instance_argument_score(
	const pa11::TemplateInstanceArgument& argument,
	const TemplateDeclaration* declaration)
{
	if (argument.kind == pa11::TemplateInstanceArgumentKind::Type)
		return nonpack_type_score(argument.type, declaration);
	if (argument.kind == pa11::TemplateInstanceArgumentKind::Value)
		return nonpack_type_score(argument.type, declaration);
	if (argument.kind == pa11::TemplateInstanceArgumentKind::Pack)
	{
		int score = 0;
		for (size_t i = 0; i < argument.pack.size(); ++i)
			score += nonpack_instance_argument_score(argument.pack[i],
			                                        declaration);
		return score;
	}
	return 1;
}

int nonpack_type_score(TypePtr type, const TemplateDeclaration* declaration)
{
	if (type.get() == NULL)
		return 0;
	type = pa11::strip_cv(type);
	if (type->kind == pa11::TypeKind::TemplateParameter)
	{
		if (type->is_dependent_typename)
		{
			int score = 0;
			for (size_t i = 0; i < type->template_arguments.size(); ++i)
				score += nonpack_instance_argument_score(
					type->template_arguments[i],
					declaration);
			for (size_t i = 0;
			     i < type->dependent_typename_template_argument_lists.size();
			     ++i)
				for (size_t j = 0;
				     j < type->dependent_typename_template_argument_lists[i].size();
				     ++j)
					score += nonpack_instance_argument_score(
						type->dependent_typename_template_argument_lists[i][j],
						declaration);
			return score;
		}
		if (!pa11::is_deducible_template_parameter_type(type))
			return 0;
		return declaration_parameter_is_pack(declaration, type->name) ? 0 : 1;
	}
	if (type->kind == pa11::TypeKind::Pointer ||
	    type->kind == pa11::TypeKind::LValueReference ||
	    type->kind == pa11::TypeKind::RValueReference ||
	    type->kind == pa11::TypeKind::Array)
		return nonpack_type_score(type->base, declaration);
	if (type->kind == pa11::TypeKind::Function)
	{
		int score = nonpack_type_score(type->base, declaration);
		for (size_t i = 0; i < type->parameters.size(); ++i)
			score += nonpack_type_score(type->parameters[i],
			                            declaration);
		return score;
	}
	if (type->kind == pa11::TypeKind::MemberPointer)
		return nonpack_type_score(type->member_class, declaration) +
		       nonpack_type_score(type->base, declaration);
	if (type->is_template_specialization ||
	    type->dependent_typename_template_id ||
	    !type->template_arguments.empty())
	{
		int score = 0;
		for (size_t i = 0; i < type->template_arguments.size(); ++i)
			score += nonpack_instance_argument_score(
				type->template_arguments[i],
				declaration);
		return score;
	}
	return 1;
}

int nonpack_template_argument_score(const vector<TemplateArgument>& pattern,
                                    const TemplateDeclaration* declaration)
{
	int score = 0;
	for (size_t i = 0; i < pattern.size(); ++i)
	{
		string pack_name;
		if (pattern[i].pack_expansion ||
		    pack_argument_parameter_name(pattern[i], pack_name))
			continue;
		if (pattern[i].kind == TemplateArgumentKind::Type)
			score += nonpack_type_score(pattern[i].type, declaration);
		else if (pattern[i].kind == TemplateArgumentKind::Value)
			score += nonpack_type_score(pattern[i].type, declaration);
		else if (pattern[i].kind == TemplateArgumentKind::Pack)
			for (size_t j = 0; j < pattern[i].pack.size(); ++j)
			{
				vector<TemplateArgument> single;
				single.push_back(pattern[i].pack[j]);
				score += nonpack_template_argument_score(single,
				                                         declaration);
			}
		else
			++score;
	}
	return score;
}

bool match_class_specialization(TemplateDeclaration* primary,
                                TemplateDeclaration* specialization,
                                const vector<TemplateArgument>& full_args,
                                size_t explicit_arg_count,
                                vector<TemplateArgument>& selected_args,
                                const map<const void*, vector<TemplateArgument> >&
                                        record_arguments)
{
	TemplateMatchParameterScope parameter_scope(&specialization->parameters);
	map<string, TemplateArgument> deduced;
	bool matched = false;
	try
	{
		matched = match_template_argument_sequence_pattern(
			specialization->class_specialization_pattern,
			full_args,
			deduced,
			record_arguments);
	}
	catch (const runtime_error&)
	{
		return false;
	}
	if (!matched)
		{
			const vector<TemplateArgument>& pattern =
				specialization->class_specialization_pattern;
		if (template_argument_sequence_has_pack_expansion(pattern) ||
		    pattern.size() > full_args.size() ||
		    explicit_arg_count > pattern.size())
			return false;
		for (size_t i = pattern.size(); i < full_args.size(); ++i)
			if (i >= primary->parameters.size() ||
			    !primary->parameters[i].has_default)
				return false;
		vector<TemplateArgument> prefix(full_args.begin(),
		                                full_args.begin() + pattern.size());
		deduced.clear();
		try
		{
			matched = match_template_argument_sequence_pattern(
				pattern,
				prefix,
				deduced,
				record_arguments);
		}
		catch (const runtime_error&)
		{
			return false;
		}
		if (!matched)
			return false;
		if (!template_value_patterns_match_after_deduction(
			    active_template_match_parser,
			    specialization,
			    pattern,
			    prefix,
			    deduced))
			return false;
	}
	else if (!template_value_patterns_match_after_deduction(
		         active_template_match_parser,
		         specialization,
		         specialization->class_specialization_pattern,
		         full_args,
		         deduced))
		return false;
	for (size_t i = 0; i < specialization->parameters.size(); ++i)
	{
		const string& name = specialization->parameters[i].name;
		map<string, TemplateArgument>::iterator found = deduced.find(name);
		if (found == deduced.end())
		{
			if (specialization->parameters[i].is_pack)
			{
				TemplateArgument remapped;
				bool have_remap = false;
				bool ambiguous_remap = false;
				for (map<string, TemplateArgument>::const_iterator it =
					     deduced.begin();
				     it != deduced.end();
				     ++it)
				{
					bool is_specialization_parameter = false;
					for (size_t j = 0;
					     j < specialization->parameters.size();
					     ++j)
						if (specialization->parameters[j].name == it->first)
							is_specialization_parameter = true;
					if (is_specialization_parameter ||
					    it->second.kind != TemplateArgumentKind::Pack)
						continue;
					if (have_remap)
					{
						ambiguous_remap = true;
						break;
					}
					remapped = it->second;
					have_remap = true;
				}
				if (have_remap && !ambiguous_remap)
					found = deduced.insert(make_pair(name, remapped)).first;
			}
			if (found == deduced.end())
				return false;
		}
		selected_args.push_back(found->second);
	}
	return true;
}

bool class_specialization_at_least_as_specialized(
	TemplateDeclaration* left,
	TemplateDeclaration* right,
	const map<const void*, vector<TemplateArgument> >& record_arguments)
{
	TemplateMatchParameterScope parameter_scope(&right->parameters);
	map<string, TemplateArgument> deduced;
	bool result = match_template_argument_sequence_pattern(
		right->class_specialization_pattern,
		left->class_specialization_pattern,
		deduced,
		record_arguments);
	return result;
}

bool class_specialization_more_specialized(
	TemplateDeclaration* left,
	TemplateDeclaration* right,
	const map<const void*, vector<TemplateArgument> >& record_arguments)
{
	bool left_at_least =
		class_specialization_at_least_as_specialized(left,
		                                             right,
		                                             record_arguments);
	bool right_at_least =
		class_specialization_at_least_as_specialized(right,
		                                             left,
		                                             record_arguments);
	if (!left_at_least || !right_at_least)
	{
		if (left_at_least != right_at_least)
			return left_at_least;
		int left_repeated = repeated_template_parameter_score(
			left->class_specialization_pattern,
			record_arguments);
		int right_repeated = repeated_template_parameter_score(
			right->class_specialization_pattern,
			record_arguments);
		if (left_repeated != right_repeated)
			return left_repeated > right_repeated;
		int left_nonpack = nonpack_template_argument_score(
			left->class_specialization_pattern,
			left);
		int right_nonpack = nonpack_template_argument_score(
			right->class_specialization_pattern,
			right);
		if (left_nonpack != right_nonpack)
			return left_nonpack > right_nonpack;
		int left_pack_penalty = pack_pattern_penalty(
			left->class_specialization_pattern,
			left,
			record_arguments);
		int right_pack_penalty = pack_pattern_penalty(
			right->class_specialization_pattern,
			right,
			record_arguments);
		if (left_pack_penalty != right_pack_penalty)
			return left_pack_penalty < right_pack_penalty;
		int left_fixed = fixed_template_argument_score(
			left->class_specialization_pattern);
		int right_fixed = fixed_template_argument_score(
			right->class_specialization_pattern);
		if (left_fixed != right_fixed)
			return left_fixed > right_fixed;
		int left_cv = cv_qualified_direct_parameter_score(
			left->class_specialization_pattern);
		int right_cv = cv_qualified_direct_parameter_score(
			right->class_specialization_pattern);
		return left_cv > right_cv;
	}
	int left_repeated = repeated_template_parameter_score(
		left->class_specialization_pattern,
		record_arguments);
	int right_repeated = repeated_template_parameter_score(
		right->class_specialization_pattern,
		record_arguments);
	if (left_repeated != right_repeated)
		return left_repeated > right_repeated;
	int left_nonpack = nonpack_template_argument_score(
		left->class_specialization_pattern,
		left);
	int right_nonpack = nonpack_template_argument_score(
		right->class_specialization_pattern,
		right);
	if (left_nonpack != right_nonpack)
		return left_nonpack > right_nonpack;
	int left_pack_penalty = pack_pattern_penalty(
		left->class_specialization_pattern,
		left,
		record_arguments);
	int right_pack_penalty = pack_pattern_penalty(
		right->class_specialization_pattern,
		right,
		record_arguments);
	if (left_pack_penalty != right_pack_penalty)
		return left_pack_penalty < right_pack_penalty;
	int left_fixed = fixed_template_argument_score(
		left->class_specialization_pattern);
	int right_fixed = fixed_template_argument_score(
		right->class_specialization_pattern);
	if (left_fixed != right_fixed)
		return left_fixed > right_fixed;
	int left_cv = cv_qualified_direct_parameter_score(
		left->class_specialization_pattern);
	int right_cv = cv_qualified_direct_parameter_score(
		right->class_specialization_pattern);
	return left_cv > right_cv;
}

vector<TemplateArgument> flatten_template_argument_packs(
	const vector<TemplateArgument>& arguments)
{
	vector<TemplateArgument> out;
	for (size_t i = 0; i < arguments.size(); ++i)
	{
		if (arguments[i].kind == TemplateArgumentKind::Pack)
		{
			out.insert(out.end(),
			           arguments[i].pack.begin(),
			           arguments[i].pack.end());
			continue;
		}
		out.push_back(arguments[i]);
	}
	return out;
}

void clear_actual_template_pack_expansion(TemplateArgument& argument)
{
	argument.pack_expansion = false;
	if (argument.kind != TemplateArgumentKind::Pack)
		return;
	for (size_t i = 0; i < argument.pack.size(); ++i)
		clear_actual_template_pack_expansion(argument.pack[i]);
}

vector<TemplateArgument> flatten_actual_template_argument_packs(
	const vector<TemplateArgument>& arguments)
{
	vector<TemplateArgument> out = flatten_template_argument_packs(arguments);
	for (size_t i = 0; i < out.size(); ++i)
		clear_actual_template_pack_expansion(out[i]);
	return out;
}

bool template_instance_argument_has_pack(
	const pa11::TemplateInstanceArgument& argument)
{
	if (argument.kind == pa11::TemplateInstanceArgumentKind::Pack)
		return true;
	for (size_t i = 0; i < argument.value_owner_template_arguments.size();
	     ++i)
		if (template_instance_argument_has_pack(
			    argument.value_owner_template_arguments[i]))
			return true;
	return false;
}

bool template_instance_arguments_have_pack(
	const vector<pa11::TemplateInstanceArgument>& arguments)
{
	for (size_t i = 0; i < arguments.size(); ++i)
		if (template_instance_argument_has_pack(arguments[i]))
			return true;
	return false;
}


}  // namespace internal
}  // namespace pa12
