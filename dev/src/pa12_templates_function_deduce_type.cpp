#include "pa12_templates_function_support.h"

#include <algorithm>
#include <functional>
#include <stdexcept>

using namespace std;

namespace pa12 {
namespace internal {

bool Parser::deduce_template_type(TypePtr pattern,
                                  TypePtr argument,
                                  map<string, TypePtr>& deduced,
                                  const map<string, TypePtr>* fixed,
                                  map<string, TemplateArgument>* deduced_arguments) const
{
	if (pattern->kind == pa11::TypeKind::Cv &&
	    type_is_template_dependent(pattern->base))
	{
		TypePtr remaining_argument =
			remove_pattern_cv_from_argument(argument, pattern->cv);
		return deduce_template_type(pattern->base,
		                            remaining_argument,
		                            deduced,
		                            fixed,
		                            deduced_arguments);
	}
	if (pattern->kind == pa11::TypeKind::LValueReference ||
	    pattern->kind == pa11::TypeKind::RValueReference)
	{
		if (argument->kind == pa11::TypeKind::LValueReference ||
		    argument->kind == pa11::TypeKind::RValueReference)
			argument = argument->base;
		return deduce_template_type(pattern->base,
		                            argument,
		                            deduced,
		                            fixed,
		                            deduced_arguments);
	}
	if (pattern->kind == pa11::TypeKind::TemplateParameter)
	{
		if (!pa11::is_deducible_template_parameter_type(pattern))
			return true;
		if (fixed != NULL && fixed->find(pattern->name) != fixed->end())
			return pa11::same_type(fixed->find(pattern->name)->second,
			                       argument);
		map<string, TypePtr>::iterator found = deduced.find(pattern->name);
		if (found == deduced.end())
		{
			deduced[pattern->name] = argument;
			return true;
		}
		return pa11::same_type(found->second, argument);
	}
	pattern = pa11::strip_cv(pattern);
	argument = pa11::strip_cv(argument);
	bool pattern_dependent =
		type_is_template_dependent(pattern);
	if (!pattern_dependent && pattern->kind == pa11::TypeKind::Record)
	{
			if (pattern->is_template_specialization &&
			    !pattern->template_primary_name.empty() &&
			    const_cast<Parser*>(this)->
				    class_template_declaration_for_match(pattern) == NULL)
				pattern_dependent = true;
			map<const void*, vector<TemplateArgument> >::const_iterator pit =
				record_template_arguments_.find(pattern.get());
			if (pit != record_template_arguments_.end())
				for (size_t i = 0; i < pit->second.size(); ++i)
				{
					vector<TemplateArgument> pending;
					pending.push_back(pit->second[i]);
					while (!pending.empty())
					{
						TemplateArgument arg = pending.back();
						pending.pop_back();
						if (arg.kind == TemplateArgumentKind::Type)
						{
							if (type_is_template_dependent(arg.type))
								pattern_dependent = true;
						}
							else if (arg.kind == TemplateArgumentKind::Value)
							{
								if (arg.dependent ||
								    type_is_template_dependent(arg.type))
									pattern_dependent = true;
							}
							else if (arg.kind == TemplateArgumentKind::Template)
							{
								if (arg.template_declaration == NULL)
									pattern_dependent = true;
							}
							else
							{
								for (size_t p = 0; p < arg.pack.size(); ++p)
								pending.push_back(arg.pack[p]);
						}
					}
				}
			if (!pattern_dependent && pattern->is_template_specialization)
				for (size_t i = 0; i < pattern->template_arguments.size(); ++i)
				{
					vector<pa11::TemplateInstanceArgument> pending;
					pending.push_back(pattern->template_arguments[i]);
					while (!pending.empty())
					{
						pa11::TemplateInstanceArgument arg = pending.back();
						pending.pop_back();
						if (arg.kind == pa11::TemplateInstanceArgumentKind::Type)
						{
							if (type_is_template_dependent(arg.type))
								pattern_dependent = true;
						}
						else if (arg.kind == pa11::TemplateInstanceArgumentKind::Value)
						{
							if (arg.dependent ||
							    type_is_template_dependent(arg.type))
								pattern_dependent = true;
						}
						else if (arg.kind == pa11::TemplateInstanceArgumentKind::Template)
						{
							if (arg.dependent)
								pattern_dependent = true;
						}
						else
						{
							for (size_t p = 0; p < arg.pack.size(); ++p)
								pending.push_back(arg.pack[p]);
						}
					}
				}
		}
	if (!pattern_dependent)
		return true;
	if (pattern->kind != argument->kind)
		return false;
	if (pattern->kind == pa11::TypeKind::Pointer ||
	    pattern->kind == pa11::TypeKind::Array)
		return deduce_template_type(pattern->base,
		                            argument->base,
		                            deduced,
		                            fixed,
		                            deduced_arguments);
	if (pattern->kind == pa11::TypeKind::Function)
	{
		if (pattern->parameters.size() != argument->parameters.size())
			return false;
		if (!deduce_template_type(pattern->base,
		                          argument->base,
		                          deduced,
		                          fixed,
		                          deduced_arguments))
			return false;
		for (size_t i = 0; i < pattern->parameters.size(); ++i)
			if (!deduce_template_type(pattern->parameters[i],
			                          argument->parameters[i],
			                          deduced,
			                          fixed,
			                          deduced_arguments))
				return false;
		return true;
	}
	if (pattern->kind == pa11::TypeKind::Record)
	{
		auto merge_type_deductions =
			[fixed](map<string, TypePtr>& target,
			        const map<string, TypePtr>& source) -> bool
		{
			for (map<string, TypePtr>::const_iterator it = source.begin();
			     it != source.end();
			     ++it)
			{
				if (fixed != NULL)
				{
					map<string, TypePtr>::const_iterator fit =
						fixed->find(it->first);
					if (fit != fixed->end() &&
					    !pa11::same_type(fit->second, it->second))
						return false;
				}
				map<string, TypePtr>::iterator found =
					target.find(it->first);
				if (found == target.end())
					target[it->first] = it->second;
				else if (!pa11::same_type(found->second, it->second))
					return false;
			}
			return true;
		};
		auto merge_argument_deductions =
			[](map<string, TemplateArgument>& target,
			   const map<string, TemplateArgument>& source) -> bool
		{
			for (map<string, TemplateArgument>::const_iterator it =
				     source.begin();
			     it != source.end();
			     ++it)
			{
				map<string, TemplateArgument>::iterator found =
					target.find(it->first);
				if (found == target.end())
					target[it->first] = it->second;
				else if (!same_deduced_template_argument(found->second,
				                                         it->second))
					return false;
			}
			return true;
		};
		auto pack_expansion_argument_name =
			[](const TemplateArgument& argument, string& name) -> bool
		{
			if (argument.kind == TemplateArgumentKind::Pack)
				return template_argument_pack_parameter_name(argument,
				                                             name);
			if (!argument.pack_expansion)
				return false;
			if (argument.kind == TemplateArgumentKind::Type)
				return template_type_has_template_parameter_name(
					argument.type,
					name);
			if (argument.kind == TemplateArgumentKind::Value)
			{
				if (!argument.value_name.empty())
				{
					name = argument.value_name;
					return true;
				}
				return template_type_has_template_parameter_name(
					argument.type,
					name);
			}
			if (argument.kind == TemplateArgumentKind::Template &&
			    argument.template_declaration == NULL &&
			    !argument.value_name.empty())
			{
				name = argument.value_name;
				return true;
			}
			return false;
		};
		auto simple_pack_pattern =
			[](const TemplateArgument& argument,
			   const string& name) -> bool
		{
			if (argument.kind == TemplateArgumentKind::Type &&
			    argument.type.get() != NULL)
			{
				TypePtr type = pa11::strip_cv(argument.type);
				return type->kind == pa11::TypeKind::TemplateParameter &&
				       pa11::is_deducible_template_parameter_type(type) &&
				       type->name == name;
			}
			if (argument.kind == TemplateArgumentKind::Value)
				return argument.value_name == name;
			if (argument.kind == TemplateArgumentKind::Template)
				return argument.template_declaration == NULL &&
				       argument.value_name == name;
			return false;
			};
			auto argument_sequence_has_pack_pattern =
				[&](const vector<TemplateArgument>& arguments) -> bool
			{
				for (size_t i = 0; i < arguments.size(); ++i)
				{
					string pack_name;
					if (pack_expansion_argument_name(arguments[i],
					                                 pack_name))
						return true;
				}
				return false;
			};
			auto flatten_argument_packs =
				[](const vector<TemplateArgument>& arguments)
					-> vector<TemplateArgument>
			{
				vector<TemplateArgument> out;
				for (size_t i = 0; i < arguments.size(); ++i)
				{
					if (arguments[i].kind == TemplateArgumentKind::Pack)
						out.insert(out.end(),
						           arguments[i].pack.begin(),
						           arguments[i].pack.end());
					else
						out.push_back(arguments[i]);
				}
				return out;
			};
			auto same_nondependent_argument_type =
				[](TypePtr left, TypePtr right) -> bool
		{
			if (left.get() == NULL || right.get() == NULL)
				return left.get() == right.get();
			if (pa11::same_type(left, right))
				return true;
			TypePtr l = pa11::strip_cv(left);
			TypePtr r = pa11::strip_cv(right);
			if (l->kind == pa11::TypeKind::Record &&
			    r->kind == pa11::TypeKind::Record &&
			    !l->name.empty() &&
			    l->name == r->name)
				return true;
			return false;
		};
		function<bool(const TemplateArgument&,
		              const TemplateArgument&,
		              map<string, TypePtr>&,
		              map<string, TemplateArgument>&)> match_one;
		function<bool(const vector<TemplateArgument>&,
		              size_t,
		              const vector<TemplateArgument>&,
		              size_t,
		              map<string, TypePtr>&,
		              map<string, TemplateArgument>&)> match_sequence;
		function<bool(const TemplateArgument&,
		              const vector<TemplateArgument>&,
		              size_t,
		              size_t,
		              map<string, TypePtr>&,
		              map<string, TemplateArgument>&)> match_pack;
		match_one =
			[&](const TemplateArgument& p_arg,
			    const TemplateArgument& a_arg,
			    map<string, TypePtr>& local_deduced,
			    map<string, TemplateArgument>& local_arguments) -> bool
		{
			if (p_arg.kind == TemplateArgumentKind::Type &&
			    a_arg.kind == TemplateArgumentKind::Type)
			{
				if (!template_type_has_template_parameter(
					    p_arg.type,
					    record_template_arguments_) &&
				    !same_nondependent_argument_type(p_arg.type,
				                                     a_arg.type))
					return false;
				return deduce_template_type(p_arg.type,
				                            a_arg.type,
				                            local_deduced,
				                            fixed,
				                            &local_arguments);
			}
			if (p_arg.kind == TemplateArgumentKind::Value &&
			    a_arg.kind == TemplateArgumentKind::Value)
				return match_or_deduce_value_argument(p_arg,
				                                      a_arg,
				                                      &local_arguments);
			if (p_arg.kind == TemplateArgumentKind::Template &&
			    a_arg.kind == TemplateArgumentKind::Template)
			{
				if (p_arg.template_declaration == NULL)
				{
					if (!a_arg.value_name.empty() &&
					    a_arg.template_declaration == NULL)
					{
						map<string, TemplateArgument>::iterator found =
							local_arguments.find(p_arg.value_name);
						if (found == local_arguments.end())
						{
							local_arguments[p_arg.value_name] = a_arg;
							return true;
						}
						return same_deduced_template_argument(found->second,
						                                      a_arg);
					}
					return bind_deduced_template_argument(
						&local_arguments,
						p_arg.value_name,
						a_arg.template_declaration);
				}
				return p_arg.template_declaration ==
				       a_arg.template_declaration;
			}
			if (p_arg.kind == TemplateArgumentKind::Pack)
			{
				string pack_name;
				if (template_argument_pack_parameter_name(p_arg,
				                                          pack_name))
				{
					vector<TemplateArgument> pack;
					if (a_arg.kind == TemplateArgumentKind::Pack)
						pack = a_arg.pack;
					else
						pack.push_back(a_arg);
					return bind_deduced_pack_argument(&local_arguments,
					                                  pack_name,
					                                  pack);
				}
				if (a_arg.kind != TemplateArgumentKind::Pack)
					return false;
				return match_sequence(p_arg.pack,
				                      0,
				                      a_arg.pack,
				                      0,
				                      local_deduced,
				                      local_arguments);
			}
			return false;
		};
		match_pack =
			[&](const TemplateArgument& current,
			    const vector<TemplateArgument>& actual,
			    size_t begin,
			    size_t end,
			    map<string, TypePtr>& local_deduced,
			    map<string, TemplateArgument>& local_arguments) -> bool
		{
			string pack_name;
			if (!pack_expansion_argument_name(current, pack_name))
				return false;
			TemplateArgument element =
				current.kind == TemplateArgumentKind::Pack &&
				current.pack.size() == 1
				? current.pack[0]
				: current;
			element.pack_expansion = false;
			vector<TemplateArgument> pack;
			map<string, TypePtr> merged_deduced = local_deduced;
			map<string, TemplateArgument> merged_arguments =
				local_arguments;
			for (size_t i = begin; i < end; ++i)
			{
				if (simple_pack_pattern(element, pack_name))
				{
					if (element.kind != actual[i].kind)
						return false;
					pack.push_back(actual[i]);
					continue;
				}
				map<string, TypePtr> per_deduced = merged_deduced;
				map<string, TemplateArgument> per_arguments =
					merged_arguments;
				if (!match_one(element,
				               actual[i],
				               per_deduced,
				               per_arguments))
					return false;
				map<string, TemplateArgument>::iterator arg_found =
					per_arguments.find(pack_name);
				map<string, TypePtr>::iterator type_found =
					per_deduced.find(pack_name);
				if (arg_found != per_arguments.end())
				{
					pack.push_back(arg_found->second);
					per_arguments.erase(arg_found);
				}
				else if (type_found != per_deduced.end())
				{
					pack.push_back(
						TemplateArgument::type_arg(type_found->second));
					per_deduced.erase(type_found);
				}
				else
					return false;
				if (!merge_type_deductions(merged_deduced,
				                           per_deduced) ||
				    !merge_argument_deductions(merged_arguments,
				                               per_arguments))
					return false;
			}
			if (!bind_deduced_pack_argument(&merged_arguments,
			                                pack_name,
			                                pack))
				return false;
			local_deduced = merged_deduced;
			local_arguments = merged_arguments;
			return true;
		};
		match_sequence =
			[&](const vector<TemplateArgument>& p_args,
			    size_t p_index,
			    const vector<TemplateArgument>& a_args,
			    size_t a_index,
			    map<string, TypePtr>& local_deduced,
			    map<string, TemplateArgument>& local_arguments) -> bool
		{
			if (p_index == p_args.size())
				return a_index == a_args.size();
			const TemplateArgument& current = p_args[p_index];
			string pack_name;
			if (pack_expansion_argument_name(current, pack_name))
			{
				for (size_t end = a_index; end <= a_args.size(); ++end)
				{
					map<string, TypePtr> trial_deduced = local_deduced;
					map<string, TemplateArgument> trial_arguments =
						local_arguments;
					if (!match_pack(current,
					                a_args,
					                a_index,
					                end,
					                trial_deduced,
					                trial_arguments))
						continue;
					size_t consumed = end - a_index;
					size_t next_pattern = p_index + 1;
					size_t desired_next =
						next_pattern +
						(consumed > 0 ? consumed - 1 : 0);
					while (next_pattern < desired_next &&
					       next_pattern < p_args.size() &&
					       !template_argument_has_template_parameter(
						       p_args[next_pattern],
						       record_template_arguments_))
						++next_pattern;
					if (match_sequence(p_args,
					                   next_pattern,
					                   a_args,
					                   end,
					                   trial_deduced,
					                   trial_arguments))
					{
						local_deduced = trial_deduced;
						local_arguments = trial_arguments;
						return true;
					}
				}
				return false;
			}
			if (a_index == a_args.size())
				return false;
			map<string, TypePtr> trial_deduced = local_deduced;
			map<string, TemplateArgument> trial_arguments =
				local_arguments;
			if (!match_one(current,
			               a_args[a_index],
			               trial_deduced,
			               trial_arguments))
				return false;
			if (!match_sequence(p_args,
			                    p_index + 1,
			                    a_args,
			                    a_index + 1,
			                    trial_deduced,
			                    trial_arguments))
				return false;
			local_deduced = trial_deduced;
			local_arguments = trial_arguments;
			return true;
		};
			TemplateDeclaration* pattern_template =
				const_cast<Parser*>(this)->
					class_template_declaration_for_match(pattern);
			bool pattern_template_parameter =
				pattern->is_template_specialization &&
				!pattern->template_primary_name.empty() &&
				pattern_template == NULL;
					if (pattern_template_parameter &&
					    argument->is_template_specialization)
				{
					TemplateDeclaration* actual_template =
						const_cast<Parser*>(this)->
							class_template_declaration_for_match(argument);
					if (actual_template == NULL)
					{
						return false;
					}
					if (actual_template->class_specialization)
					{
					TemplateDeclaration* primary =
						const_cast<Parser*>(this)->find_class_template(
							actual_template->owner,
						actual_template->name);
					if (primary != NULL)
						actual_template = primary;
				}
				map<const void*, vector<TemplateArgument> >::const_iterator pit =
					record_template_arguments_.find(pattern.get());
				map<const void*, vector<TemplateArgument> >::const_iterator ait =
					record_template_arguments_.find(argument.get());
				vector<TemplateArgument> p_args;
				vector<TemplateArgument> a_args;
				try
				{
					if (!pattern->template_arguments.empty())
						for (size_t i = 0;
						     i < pattern->template_arguments.size();
						     ++i)
							p_args.push_back(
								template_argument_from_instance_argument(
									pattern->template_arguments[i]));
					else if (pit != record_template_arguments_.end())
						p_args = pit->second;
					if (!argument->template_arguments.empty())
						for (size_t i = 0;
						     i < argument->template_arguments.size();
						     ++i)
							a_args.push_back(
								template_argument_from_instance_argument(
									argument->template_arguments[i]));
					else if (ait != record_template_arguments_.end())
						a_args = ait->second;
				}
				catch (const runtime_error&)
				{
				}
					map<string, TypePtr> local_deduced = deduced;
					map<string, TemplateArgument> local_arguments =
						deduced_arguments != NULL
						? *deduced_arguments
						: map<string, TemplateArgument>();
						if (!bind_deduced_template_argument(
							    &local_arguments,
							    pattern->template_primary_name,
							    actual_template))
							return false;
						vector<TemplateArgument> match_a_args =
							argument_sequence_has_pack_pattern(p_args)
							? flatten_argument_packs(a_args)
							: a_args;
						bool matched_template_parameter_sequence =
							match_sequence(p_args,
							               0,
							               match_a_args,
							               0,
							               local_deduced,
							               local_arguments);
					if (matched_template_parameter_sequence)
				{
					deduced = local_deduced;
					if (deduced_arguments != NULL)
					*deduced_arguments = local_arguments;
				return true;
			}
		}
		map<const void*, TemplateDeclaration*>::const_iterator pt =
			record_template_declarations_.find(pattern.get());
		map<const void*, TemplateDeclaration*>::const_iterator at =
			record_template_declarations_.find(argument.get());
		if (pt != record_template_declarations_.end() &&
		    at != record_template_declarations_.end() &&
		    pt->second == at->second)
		{
					const vector<TemplateArgument>& p_args =
						record_template_arguments_.find(pattern.get())->second;
					const vector<TemplateArgument>& a_args =
						record_template_arguments_.find(argument.get())->second;
					map<string, TypePtr> local_deduced = deduced;
						map<string, TemplateArgument> local_arguments =
							deduced_arguments != NULL
							? *deduced_arguments
							: map<string, TemplateArgument>();
						vector<TemplateArgument> match_a_args =
							argument_sequence_has_pack_pattern(p_args)
							? flatten_argument_packs(a_args)
							: a_args;
						bool matched_template_parameter_sequence =
							match_sequence(p_args,
							               0,
							               match_a_args,
							               0,
							               local_deduced,
							               local_arguments);
						if (matched_template_parameter_sequence)
					{
						deduced = local_deduced;
						if (deduced_arguments != NULL)
						*deduced_arguments = local_arguments;
					return true;
				}
			}
		Scope* pattern_owner =
			pattern->scope != NULL ? pattern->scope->parent : NULL;
		Scope* argument_owner =
			argument->scope != NULL ? argument->scope->parent : NULL;
		if (pt != record_template_declarations_.end() &&
		    at != record_template_declarations_.end() &&
		    pattern->is_template_specialization &&
		    argument->is_template_specialization &&
		    pattern->template_primary_name == argument->template_primary_name &&
		    (pattern_owner == NULL || argument_owner == NULL ||
		     pattern_owner == argument_owner))
		{
				const vector<TemplateArgument>& p_args =
					record_template_arguments_.find(pattern.get())->second;
				const vector<TemplateArgument>& a_args =
					record_template_arguments_.find(argument.get())->second;
				map<string, TypePtr> local_deduced = deduced;
					map<string, TemplateArgument> local_arguments =
						deduced_arguments != NULL
						? *deduced_arguments
						: map<string, TemplateArgument>();
					vector<TemplateArgument> match_a_args =
						argument_sequence_has_pack_pattern(p_args)
						? flatten_argument_packs(a_args)
						: a_args;
					if (match_sequence(p_args,
					                   0,
					                   match_a_args,
					                   0,
					                   local_deduced,
					                   local_arguments))
				{
					deduced = local_deduced;
					if (deduced_arguments != NULL)
						*deduced_arguments = local_arguments;
					return true;
				}
			}
			if (pattern->is_template_specialization &&
			    argument->is_template_specialization &&
			    pattern->template_primary_name == argument->template_primary_name &&
			    (pattern_owner == NULL || argument_owner == NULL ||
			     pattern_owner == argument_owner))
			{
				vector<TemplateArgument> p_args;
				vector<TemplateArgument> a_args;
				try
				{
					for (size_t i = 0; i < pattern->template_arguments.size(); ++i)
						p_args.push_back(
							template_argument_from_instance_argument(
								pattern->template_arguments[i]));
					for (size_t i = 0; i < argument->template_arguments.size(); ++i)
						a_args.push_back(
							template_argument_from_instance_argument(
								argument->template_arguments[i]));
				}
				catch (const runtime_error&)
				{
					p_args.clear();
					a_args.clear();
				}
				map<string, TypePtr> local_deduced = deduced;
					map<string, TemplateArgument> local_arguments =
						deduced_arguments != NULL
						? *deduced_arguments
						: map<string, TemplateArgument>();
					vector<TemplateArgument> match_a_args =
						argument_sequence_has_pack_pattern(p_args)
						? flatten_argument_packs(a_args)
						: a_args;
						bool matched_instance_sequence =
							!p_args.empty() &&
							match_sequence(p_args,
							               0,
							               match_a_args,
							               0,
							               local_deduced,
							               local_arguments);
					if (matched_instance_sequence)
				{
					deduced = local_deduced;
					if (deduced_arguments != NULL)
						*deduced_arguments = local_arguments;
					return true;
				}
			}
			if (argument->kind == pa11::TypeKind::Record)
			{
				if (pattern_template_parameter)
					return false;
				const_cast<Parser*>(this)->complete_template_record(argument);
				TypePtr base = argument->base.get() != NULL
					? pa11::strip_cv(argument->base) : TypePtr();
			if (base.get() != NULL &&
			    deduce_template_type(pattern,
			                         base,
			                         deduced,
			                         fixed,
			                         deduced_arguments))
				return true;
		}
	}
	return pa11::same_type(pattern, argument);
}

}  // namespace internal
}  // namespace pa12
