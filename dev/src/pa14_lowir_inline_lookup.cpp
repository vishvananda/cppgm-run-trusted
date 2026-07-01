#include "pa14_lowir_internal.h"
#include "pa12_templates_function_support.h"
#include "pa12_types_support.h"

#include <algorithm>

namespace pa14 {
namespace internal {
namespace {
	struct InlineDefinitionEntry
	{
		const Binding* binding;
		const Node* body;
		bool has_rank;
		size_t rank;
		string key;
		InlineDefinitionEntry(const Binding* b, const Node* n,
		                      bool hr, size_t r, const string& k)
			: binding(b), body(n), has_rank(hr), rank(r), key(k)
		{
		}
	};

	const Node* recorded_inline_body(const ProgramLowerer& program,
	                                 const Binding* binding)
	{
		map<const Binding*, const Node*>::const_iterator found =
			program.inline_definitions.find(binding);
		if (found != program.inline_definitions.end())
			return found->second;
		map<const Binding*, Node>::const_iterator synthetic =
			program.synthetic_inline_definitions.find(binding);
		return synthetic != program.synthetic_inline_definitions.end()
			? &synthetic->second
			: NULL;
	}

	bool recorded_inline_body_is_synthetic(const ProgramLowerer& program,
	                                       const Binding* binding,
	                                       const Node* body);

	void append_inline_body_shape_key(const Node& node,
	                                  size_t depth,
	                                  string& out);

	bool recorded_inline_body_is_synthetic(const ProgramLowerer& program,
	                                       const Binding* binding,
	                                       const Node* body)
	{
		map<const Binding*, Node>::const_iterator synthetic =
			program.synthetic_inline_definitions.find(binding);
		return synthetic != program.synthetic_inline_definitions.end() &&
		       body == &synthetic->second;
	}

	string inline_definition_base_key(const ProgramLowerer& program,
	                                  const Binding* binding,
	                                  const Node* body)
	{
		string key = binding != NULL ? global_object_symbol(binding) : string();
		key += '\n';
		key += binding != NULL ? source_symbol_base(binding) : string();
		key += '\n';
		key += binding != NULL ? binding->name : string();
		key += '\n';
		if (binding != NULL && binding->type.get() != NULL)
			key += pa11::describe_type(binding->type);
		key += '\n';
		key += recorded_inline_body_is_synthetic(program, binding, body)
			? "synthetic\n" : "source\n";
		return key;
	}

	string inline_definition_stable_key(const ProgramLowerer& program,
	                                    const Binding* binding,
	                                    const Node* body)
	{
		string key = inline_definition_base_key(program, binding, body);
		if (body != NULL)
			append_inline_body_shape_key(*body, 8, key);
		return key;
	}

	void finalize_inline_definition_entry_keys(
		vector<InlineDefinitionEntry>& entries)
	{
		map<string, size_t> key_counts;
		for (size_t i = 0; i < entries.size(); ++i)
			++key_counts[entries[i].key];
		for (size_t i = 0; i < entries.size(); ++i)
			if (key_counts[entries[i].key] > 1 && entries[i].body != NULL)
			{
				append_inline_body_shape_key(*entries[i].body,
				                             8,
				                             entries[i].key);
			}
	}

	bool inline_definition_entry_less(const InlineDefinitionEntry& left,
	                                  const InlineDefinitionEntry& right)
	{
		if (left.key != right.key)
			return left.key < right.key;
		if (left.has_rank != right.has_rank)
			return left.has_rank;
		if (left.has_rank && left.rank != right.rank)
			return left.rank < right.rank;
		return false;
	}

	InlineDefinitionEntry make_inline_definition_entry(
		const ProgramLowerer& program,
		const Binding* binding,
		const Node* body)
	{
		map<const Binding*, size_t>::const_iterator rank =
			program.inline_definition_ranks.find(binding);
		bool has_rank = rank != program.inline_definition_ranks.end();
		return InlineDefinitionEntry(
			binding,
			body,
			has_rank,
			has_rank ? rank->second : 0,
			inline_definition_base_key(program, binding, body));
	}

	vector<InlineDefinitionEntry> sorted_inline_definition_entries(
		const ProgramLowerer& program,
		bool include_synthetic)
	{
		vector<InlineDefinitionEntry> entries;
		for (map<const Binding*, const Node*>::const_iterator it =
			     program.inline_definitions.begin();
		     it != program.inline_definitions.end();
		     ++it)
			entries.push_back(make_inline_definition_entry(program,
			                                               it->first,
			                                               it->second));
		if (include_synthetic)
			for (map<const Binding*, Node>::const_iterator it =
				     program.synthetic_inline_definitions.begin();
			     it != program.synthetic_inline_definitions.end();
			     ++it)
				entries.push_back(make_inline_definition_entry(program,
				                                               it->first,
				                                               &it->second));
		finalize_inline_definition_entry_keys(entries);
		sort(entries.begin(), entries.end(), inline_definition_entry_less);
		return entries;
	}

	bool collect_inline_definition_entries_from_rank(
		const ProgramLowerer& program,
		size_t first_rank,
		vector<InlineDefinitionEntry>& entries)
	{
		entries.clear();
		for (map<const Binding*, const Node*>::const_iterator it =
			     program.inline_definitions.begin();
		     it != program.inline_definitions.end();
		     ++it)
		{
			map<const Binding*, size_t>::const_iterator rank =
				program.inline_definition_ranks.find(it->first);
			if (rank == program.inline_definition_ranks.end())
				return false;
			if (rank->second >= first_rank)
				entries.push_back(InlineDefinitionEntry(
					it->first,
					it->second,
					true,
					rank->second,
					inline_definition_base_key(program,
					                           it->first,
					                           it->second)));
		}
		finalize_inline_definition_entry_keys(entries);
		sort(entries.begin(), entries.end(), inline_definition_entry_less);
		return true;
	}

	void append_inline_body_shape_key(const Node& node,
	                                  size_t depth,
	                                  string& out)
	{
		out += node.line;
		out += '\n';
		if (!node.token_text.empty())
		{
			out += "token:";
			out += node.token_text;
			out += '\n';
		}
		if (node.binding != NULL)
		{
			out += "binding:";
			out += node.binding->name;
			out += ':';
			out += global_object_symbol(node.binding);
			out += '\n';
		}
		if (node.direct_call != NULL)
		{
			out += "call:";
			out += node.direct_call->name;
			out += ':';
			out += global_object_symbol(node.direct_call);
			out += '\n';
		}
		if (node.type.get() != NULL)
		{
			out += "type:";
			out += pa11::describe_type(node.type);
			out += '\n';
		}
		if (depth == 0)
		{
			out += "children:";
			out += to_string(node.children.size());
			out += '\n';
			return;
		}
		for (size_t i = 0; i < node.children.size(); ++i)
			append_inline_body_shape_key(node.children[i], depth - 1, out);
	}

	string inline_lookup_stable_key(const ProgramLowerer& program,
	                                const Binding* binding)
	{
		const Node* body = recorded_inline_body(program, binding);
		return inline_definition_stable_key(program, binding, body);
	}

	bool prefer_inline_lookup_binding(const ProgramLowerer& program,
	                                  const Binding* current,
	                                  const Binding* candidate)
	{
		if (candidate == NULL)
			return false;
		if (current == NULL)
			return true;
		return inline_lookup_stable_key(program, candidate) <
		       inline_lookup_stable_key(program, current);
	}

	void refresh_inline_definition_member_lookup(const ProgramLowerer& program)
	{
		const size_t target_rank = program.inline_definition_ranks.size();
		if (program.inline_definition_member_lookup_cache_size == target_rank)
			return;
		const size_t first_rank =
			program.inline_definition_member_lookup_cache_size;
		vector<InlineDefinitionEntry> entries;
		bool incremental =
			first_rank <= target_rank &&
			collect_inline_definition_entries_from_rank(program,
			                                            first_rank,
			                                            entries);
		if (!incremental)
		{
			program.inline_definition_members_by_name.clear();
			entries = sorted_inline_definition_entries(program, true);
		}
		program.inline_definition_member_lookup_cache_size = target_rank;
		set<const Binding*> added;
		for (size_t i = 0; i < entries.size(); ++i)
		{
			const Binding* binding = entries[i].binding;
			if (binding == NULL ||
			    binding->kind != BindingKind::Function ||
			    !added.insert(binding).second)
				continue;
			program.inline_definition_members_by_name[binding->name]
				.push_back(binding);
		}
	}

	void refresh_inline_definition_lookup_cache(ProgramLowerer& program)
	{
		const size_t target_rank = program.inline_definition_ranks.size();
		if (program.inline_definition_lookup_cache_size == target_rank)
			return;
		const size_t first_rank =
			program.inline_definition_lookup_cache_size;
		vector<InlineDefinitionEntry> entries;
		bool incremental =
			first_rank <= target_rank &&
			collect_inline_definition_entries_from_rank(program,
			                                            first_rank,
			                                            entries);
		if (!incremental)
		{
			program.inline_definition_lookup_by_name.clear();
			program.inline_definition_lookup_by_object.clear();
			entries = sorted_inline_definition_entries(program, false);
		}
		program.inline_definition_lookup_cache_size = target_rank;
		for (size_t i = 0; i < entries.size(); ++i)
		{
			const Binding* binding = entries[i].binding;
			if (binding == NULL || binding->kind != BindingKind::Function)
				continue;
			string name = program.symbol_for(binding);
			if (!name.empty())
			{
				map<string, const Binding*>::iterator existing =
					program.inline_definition_lookup_by_name.find(name);
				if (existing == program.inline_definition_lookup_by_name.end())
					program.inline_definition_lookup_by_name[name] = binding;
				else if (prefer_inline_lookup_binding(program,
				                                      existing->second,
				                                      binding))
					existing->second = binding;
			}
			string object = global_object_symbol(binding);
			if (!object.empty())
			{
				map<string, const Binding*>::iterator existing =
					program.inline_definition_lookup_by_object.find(object);
				if (existing == program.inline_definition_lookup_by_object.end())
					program.inline_definition_lookup_by_object[object] = binding;
				else if (prefer_inline_lookup_binding(program,
				                                      existing->second,
				                                      binding))
					existing->second = binding;
			}
		}
	}
}  // namespace

const vector<const Binding*>* inline_alias_member_candidates(
	const ProgramLowerer& program,
	const string& name)
{
	refresh_inline_definition_member_lookup(program);
	map<string, vector<const Binding*> >::const_iterator found =
		program.inline_definition_members_by_name.find(name);
	return found == program.inline_definition_members_by_name.end()
		? NULL : &found->second;
}

	const Binding* inline_alias_lookup_binding(ProgramLowerer& program,
	                                           const string& name,
	                                           const string& object)
	{
		refresh_inline_definition_lookup_cache(program);
		const Binding* result = NULL;
		if (!object.empty())
		{
			map<string, const Binding*>::const_iterator found_object =
				program.inline_definition_lookup_by_object.find(object);
			if (found_object != program.inline_definition_lookup_by_object.end())
				result = found_object->second;
		}
		if (result == NULL)
		{
			map<string, const Binding*>::const_iterator found_name =
				program.inline_definition_lookup_by_name.find(name);
			if (found_name != program.inline_definition_lookup_by_name.end())
				result = found_name->second;
		}
		return result;
	}

}  // namespace internal
}  // namespace pa14
