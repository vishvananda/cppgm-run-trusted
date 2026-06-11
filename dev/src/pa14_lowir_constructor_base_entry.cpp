#include "pa14_lowir_internal.h"

#include <algorithm>
#include <cctype>
#include <map>
#include <set>
#include <sstream>

namespace pa14 {
namespace internal {
namespace {

void remove_hidden_pvb_parameters(string& header)
{
	for (;;)
	{
		size_t pos = header.find(", %__pvbptr");
		if (pos == string::npos)
			break;
		size_t end = header.find(" : ptr", pos);
		if (end == string::npos)
			break;
		header.erase(pos, end + 6 - pos);
	}
}

size_t max_temp_index(const FunctionOut& fn)
{
	size_t out = 0;
	for (size_t b = 0; b < fn.blocks.size(); ++b)
		for (size_t i = 0; i < fn.blocks[b].instrs.size(); ++i)
		{
			const string& text = fn.blocks[b].instrs[i];
			for (size_t pos = text.find("%t");
			     pos != string::npos;
			     pos = text.find("%t", pos + 2))
			{
				size_t n = 0;
				size_t p = pos + 2;
				if (p >= text.size() || !isdigit(text[p]))
					continue;
				while (p < text.size() && isdigit(text[p]))
				{
					n = n * 10 + size_t(text[p] - '0');
					++p;
				}
				out = max(out, n);
			}
		}
	return out;
}

vector<string> temps_in_text(const string& text)
{
	vector<string> out;
	for (size_t pos = text.find("%t");
	     pos != string::npos;
	     pos = text.find("%t", pos + 2))
	{
		size_t p = pos + 2;
		if (p >= text.size() || !isdigit(text[p]))
			continue;
		while (p < text.size() && isdigit(text[p]))
			++p;
		string temp = text.substr(pos, p - pos);
		if (find(out.begin(), out.end(), temp) == out.end())
			out.push_back(temp);
	}
	return out;
}

string defined_temp(const string& text)
{
	size_t pos = text.find("    %t");
	if (pos != 0)
		return "";
	size_t end = text.find(" = ", 4);
	if (end == string::npos)
		return "";
	return text.substr(4, end - 4);
}

bool temp_loads_this(const string& temp,
                     const map<string, string>& defs)
{
	map<string, string>::const_iterator found = defs.find(temp);
	return found != defs.end() &&
	       found->second.find(" = load ptr $this") != string::npos;
}

bool temp_is_this_virtual_base_projection(
	const string& temp,
	const map<string, string>& defs,
	const vector<uint64_t>& virtual_offsets)
{
	map<string, string>::const_iterator found = defs.find(temp);
	if (found == defs.end())
		return false;
	const string& text = found->second;
	if (text.find(" = index i8 [projection=base_subobject] ") ==
	    string::npos)
		return false;
	for (size_t i = 0; i < virtual_offsets.size(); ++i)
	{
		string suffix = ", " + to_string(virtual_offsets[i]);
		if (text.size() < suffix.size() ||
		    text.compare(text.size() - suffix.size(), suffix.size(),
		                 suffix) != 0)
			continue;
		vector<string> temps = temps_in_text(text);
		for (size_t t = 0; t < temps.size(); ++t)
			if (temps[t] != temp && temp_loads_this(temps[t], defs))
				return true;
	}
	return false;
}

bool constructor_call_targets_virtual_base(const string& text,
                                           const vector<TypePtr>& vbases)
{
	if (text.find("call void @") == string::npos ||
	    text.find("(") == string::npos)
		return false;
	for (size_t i = 0; i < vbases.size(); ++i)
	{
		string record = record_lowir_name(vbases[i]);
		string needle = "@" + record + "__";
		if (text.find(needle) != string::npos)
			return true;
	}
	return false;
}

bool copyobj_targets_virtual_base(const string& text,
                                  const map<string, string>& defs,
                                  const vector<uint64_t>& virtual_offsets)
{
	if (text.find("copyobj ") == string::npos)
		return false;
	vector<string> temps = temps_in_text(text);
	for (size_t i = 0; i < temps.size(); ++i)
		if (temp_is_this_virtual_base_projection(temps[i],
		                                         defs,
		                                         virtual_offsets))
			return true;
	return false;
}

void mark_temp_definitions_for_removal(
	const string& text,
	const map<string, size_t>& def_indices,
	const map<string, string>& defs,
	set<size_t>& remove)
{
	vector<string> temps = temps_in_text(text);
	for (size_t i = 0; i < temps.size(); ++i)
	{
		map<string, size_t>::const_iterator index =
			def_indices.find(temps[i]);
		if (index == def_indices.end())
			continue;
		if (!remove.insert(index->second).second)
			continue;
		map<string, string>::const_iterator def = defs.find(temps[i]);
		if (def != defs.end())
			mark_temp_definitions_for_removal(def->second,
			                                  def_indices,
			                                  defs,
			                                  remove);
	}
}

bool lowir_token_char(char ch)
{
	return std::isalnum(static_cast<unsigned char>(ch)) ||
	       ch == '_' || ch == '%';
}

bool replace_lowir_token(string& text,
                         const string& from,
                         const string& to)
{
	bool changed = false;
	size_t pos = 0;
	while ((pos = text.find(from, pos)) != string::npos)
	{
		size_t end = pos + from.size();
		bool before_ok = pos == 0 || !lowir_token_char(text[pos - 1]);
		bool after_ok = end == text.size() || !lowir_token_char(text[end]);
		if (!before_ok || !after_ok)
		{
			pos = end;
			continue;
		}
		text.replace(pos, from.size(), to);
		pos += to.size();
		changed = true;
	}
	return changed;
}

void apply_constructor_base_entry_arg_rewrites(FunctionOut& base_entry)
{
	if (base_entry.constructor_base_entry_arg_rewrites.empty())
		return;
	for (size_t b = 0; b < base_entry.blocks.size(); ++b)
	{
		Block& block = base_entry.blocks[b];
		map<string, size_t> def_indices;
		map<string, string> defs;
		for (size_t i = 0; i < block.instrs.size(); ++i)
		{
			string temp = defined_temp(block.instrs[i]);
			if (!temp.empty())
			{
				def_indices[temp] = i;
				defs[temp] = block.instrs[i];
			}
		}
		set<size_t> remove;
		for (size_t i = 0; i < block.instrs.size(); ++i)
		{
			if (block.instrs[i].find("call ") == string::npos)
				continue;
			string text = block.instrs[i];
			for (size_t r = 0;
			     r < base_entry.constructor_base_entry_arg_rewrites.size();
			     ++r)
			{
				const pair<string, string>& rewrite =
					base_entry.constructor_base_entry_arg_rewrites[r];
				if (rewrite.first.empty() ||
				    rewrite.first[0] != '%' ||
				    !replace_lowir_token(text,
				                         rewrite.first,
				                         rewrite.second))
					continue;
				mark_temp_definitions_for_removal(rewrite.first,
				                                  def_indices,
				                                  defs,
				                                  remove);
			}
			block.instrs[i] = text;
		}
		if (remove.empty())
			continue;
		vector<string> kept;
		for (size_t i = 0; i < block.instrs.size(); ++i)
			if (remove.find(i) == remove.end())
				kept.push_back(block.instrs[i]);
		block.instrs.swap(kept);
	}
}

void renumber_function_temps(FunctionOut& fn)
{
	map<string, string> replacements;
	size_t next = 0;
	for (size_t b = 0; b < fn.blocks.size(); ++b)
		for (size_t i = 0; i < fn.blocks[b].instrs.size(); ++i)
		{
			vector<string> temps = temps_in_text(fn.blocks[b].instrs[i]);
			for (size_t t = 0; t < temps.size(); ++t)
				if (replacements.find(temps[t]) == replacements.end())
					replacements[temps[t]] =
						"%t" + to_string(++next);
		}
	for (size_t b = 0; b < fn.blocks.size(); ++b)
		for (size_t i = 0; i < fn.blocks[b].instrs.size(); ++i)
			for (map<string, string>::const_iterator it =
				     replacements.begin();
			     it != replacements.end();
			     ++it)
				replace_lowir_token(fn.blocks[b].instrs[i],
				                    it->first,
				                    "__renumber_tmp_" +
				                    it->second.substr(2) + "__");
	for (size_t b = 0; b < fn.blocks.size(); ++b)
		for (size_t i = 0; i < fn.blocks[b].instrs.size(); ++i)
			for (map<string, string>::const_iterator it =
				     replacements.begin();
			     it != replacements.end();
			     ++it)
				replace_lowir_token(fn.blocks[b].instrs[i],
				                    "__renumber_tmp_" +
				                    it->second.substr(2) + "__",
				                    it->second);
}

void strip_constructor_base_entry_virtual_base_initializers(
	FunctionOut& base_entry)
{
	TypePtr record = class_record_for_member(base_entry.binding);
	record = record.get() != NULL ? pa11::strip_cv(record) : TypePtr();
	if (record.get() == NULL || record->kind != TypeKind::Record)
		return;
	vector<TypePtr> vbases = hidden_virtual_bases_for_record(record);
	if (vbases.empty())
		return;
	vector<uint64_t> virtual_offsets;
	for (size_t i = 0; i < vbases.size(); ++i)
		virtual_offsets.push_back(
			pa11::record_virtual_base_offset(record, vbases[i]));
	for (size_t b = 0; b < base_entry.blocks.size(); ++b)
	{
		Block& block = base_entry.blocks[b];
		map<string, size_t> def_indices;
		map<string, string> defs;
		for (size_t i = 0; i < block.instrs.size(); ++i)
		{
			string temp = defined_temp(block.instrs[i]);
			if (!temp.empty())
			{
				def_indices[temp] = i;
				defs[temp] = block.instrs[i];
			}
		}
		set<size_t> remove;
		for (size_t i = 0; i < block.instrs.size(); ++i)
		{
			const string& text = block.instrs[i];
			if (constructor_call_targets_virtual_base(text, vbases) ||
			    copyobj_targets_virtual_base(text, defs, virtual_offsets))
			{
				remove.insert(i);
				mark_temp_definitions_for_removal(text,
				                                  def_indices,
				                                  defs,
				                                  remove);
			}
		}
		if (remove.empty())
			continue;
		vector<string> kept;
		for (size_t i = 0; i < block.instrs.size(); ++i)
			if (remove.find(i) == remove.end())
				kept.push_back(block.instrs[i]);
		block.instrs.swap(kept);
	}
}

void rewrite_constructor_base_entry_pvb_stores(FunctionOut& base_entry,
                                               const vector<string>& param_names)
{
	const Binding* binding = base_entry.binding;
	if (binding == NULL ||
	    binding->type.get() == NULL ||
	    binding->type->kind != TypeKind::Function)
		return;
	size_t next_temp = max_temp_index(base_entry);
	size_t hidden_index = 0;
	for (size_t p = 1;
	     p < binding->type->parameters.size() && p < param_names.size();
	     ++p)
	{
		TypePtr context =
			hidden_virtual_base_context_record(binding->type->parameters[p]);
		vector<TypePtr> vbases =
			hidden_virtual_bases_for_parameter(binding->type->parameters[p]);
		for (size_t v = 0; v < vbases.size(); ++v)
		{
			string needle = "    store ptr %__pvbptr" +
				to_string(hidden_index) + ", $" + param_names[p] +
				"__pvb" + to_string(v);
			for (size_t b = 0; b < base_entry.blocks.size(); ++b)
				for (size_t i = 0;
				     i < base_entry.blocks[b].instrs.size();
				     ++i)
				{
					if (base_entry.blocks[b].instrs[i] != needle)
						continue;
					string tmp = "%t" + to_string(++next_temp);
					uint64_t offset = base_subobject_offset(context,
					                                        vbases[v]);
					base_entry.blocks[b].instrs[i] =
						"    " + tmp + " = index i8 %" +
						param_names[p] + ", " + to_string(offset);
					base_entry.blocks[b].instrs.insert(
						base_entry.blocks[b].instrs.begin() + i + 1,
						"    store ptr " + tmp + ", $" +
						param_names[p] + "__pvb" + to_string(v));
					++i;
				}
			++hidden_index;
		}
	}
}

void insert_constructor_base_entry_vtt_parameter(FunctionOut& base_entry)
{
	if (base_entry.header.find("%__vtt : ptr") != string::npos)
		return;
	size_t this_pos = base_entry.header.find("%this : ptr");
	if (this_pos == string::npos)
		return;
	base_entry.header.insert(this_pos + string("%this : ptr").size(),
	                         ", %__vtt : ptr");
}

string addr_global_symbol(const string& text)
{
	size_t pos = text.find(" = addr @");
	if (pos == string::npos)
		return "";
	pos += string(" = addr @").size();
	size_t end = text.find_first_of(" \t)", pos);
	return text.substr(pos, end == string::npos ? string::npos : end - pos);
}

string index_i8_base_temp(const string& text)
{
	size_t pos = text.find(" = index i8 ");
	if (pos == string::npos)
		return "";
	pos += string(" = index i8 ").size();
	if (pos >= text.size() || text[pos] != '%')
		return "";
	size_t end = text.find(',', pos);
	if (end == string::npos)
		return "";
	return text.substr(pos, end - pos);
}

bool index_i8_has_offset(const string& text, uint64_t offset)
{
	string suffix = ", " + to_string(offset);
	return text.size() >= suffix.size() &&
	       text.compare(text.size() - suffix.size(),
	                    suffix.size(),
	                    suffix) == 0;
}

size_t constructor_vtt_slot_for_vtable_symbol(TypePtr record,
                                              const string& symbol)
{
	TypePtr bare = record.get() != NULL ? pa11::strip_cv(record) : TypePtr();
	if (bare.get() == NULL || bare->kind != TypeKind::Record)
		return static_cast<size_t>(-1);
	if (symbol == vtable_symbol_for_record(bare))
		return 0;
	vector<pair<TypePtr, uint64_t> > views =
		vtt_ordered_vtable_views(bare);
	for (size_t i = 0; i < views.size(); ++i)
		if (symbol == vtable_view_symbol_for_record(bare,
		                                            views[i].first,
		                                            views[i].second))
			return construction_vtt_slot_for_view(bare,
			                                      views[i].first,
			                                      views[i].second);
	return static_cast<size_t>(-1);
}

size_t constructor_vtt_slot_for_addr_point_temp(
	const string& temp,
	const map<string, string>& defs,
	TypePtr record,
	string& addr_temp)
{
	map<string, string>::const_iterator value_def = defs.find(temp);
	if (value_def == defs.end() ||
	    !index_i8_has_offset(value_def->second,
	                         vtable_address_point_offset(record)))
		return static_cast<size_t>(-1);
	addr_temp = index_i8_base_temp(value_def->second);
	if (addr_temp.empty())
		return static_cast<size_t>(-1);
	map<string, string>::const_iterator addr_def = defs.find(addr_temp);
	if (addr_def == defs.end())
		return static_cast<size_t>(-1);
	return constructor_vtt_slot_for_vtable_symbol(
		record,
		addr_global_symbol(addr_def->second));
}

void rewrite_constructor_base_entry_vptr_stores(FunctionOut& base_entry,
                                                TypePtr record)
{
	TypePtr bare = record.get() != NULL ? pa11::strip_cv(record) : TypePtr();
	if (bare.get() == NULL || bare->kind != TypeKind::Record ||
	    !bare->is_polymorphic || !record_uses_virtual_base_vtt(bare))
		return;
	size_t next_temp = max_temp_index(base_entry);
	for (size_t b = 0; b < base_entry.blocks.size(); ++b)
	{
		Block& block = base_entry.blocks[b];
		map<string, size_t> def_indices;
		map<string, string> defs;
		for (size_t i = 0; i < block.instrs.size(); ++i)
		{
			string temp = defined_temp(block.instrs[i]);
			if (!temp.empty())
			{
				def_indices[temp] = i;
				defs[temp] = block.instrs[i];
			}
		}
		set<size_t> remove;
		map<size_t, vector<string> > insert_after;
		for (size_t i = 0; i < block.instrs.size(); ++i)
		{
			string value = defined_temp(block.instrs[i]);
			if (value.empty())
				continue;
			string addr_temp;
			size_t slot = constructor_vtt_slot_for_addr_point_temp(
				value,
				defs,
				bare,
				addr_temp);
			if (slot == static_cast<size_t>(-1))
				continue;
			map<string, size_t>::const_iterator addr_index =
				def_indices.find(addr_temp);
			if (addr_index != def_indices.end())
				remove.insert(addr_index->second);
			if (slot == 0)
			{
				block.instrs[i] =
					"    " + value + " = load ptr %__vtt";
				continue;
			}
			string slot_temp = "%t" + to_string(++next_temp);
			block.instrs[i] =
				"    " + slot_temp + " = index i8 %__vtt, " +
				to_string(slot * 8);
			insert_after[i].push_back("    " + value +
			                          " = load ptr " + slot_temp);
		}
		if (remove.empty() && insert_after.empty())
			continue;
		vector<string> rewritten;
		for (size_t i = 0; i < block.instrs.size(); ++i)
		{
			if (remove.find(i) == remove.end())
			{
				rewritten.push_back(block.instrs[i]);
				map<size_t, vector<string> >::const_iterator extra =
					insert_after.find(i);
				if (extra != insert_after.end())
					rewritten.insert(rewritten.end(),
					                 extra->second.begin(),
					                 extra->second.end());
			}
		}
		block.instrs.swap(rewritten);
	}
}

void rewrite_constructor_base_entry_vtt_references(FunctionOut& base_entry,
                                                   TypePtr record)
{
	TypePtr bare = record.get() != NULL ? pa11::strip_cv(record) : TypePtr();
	if (bare.get() == NULL || bare->kind != TypeKind::Record)
		return;
	string symbol = vtt_symbol_for_record(bare);
	for (size_t b = 0; b < base_entry.blocks.size(); ++b)
	{
		Block& block = base_entry.blocks[b];
		set<size_t> remove;
		for (size_t i = 0; i < block.instrs.size(); ++i)
		{
			if (addr_global_symbol(block.instrs[i]) != symbol)
				continue;
			string temp = defined_temp(block.instrs[i]);
			if (temp.empty())
				continue;
			remove.insert(i);
			for (size_t j = 0; j < block.instrs.size(); ++j)
				if (j != i)
					replace_lowir_token(block.instrs[j],
					                    temp,
					                    "%__vtt");
		}
		if (remove.empty())
			continue;
		vector<string> kept;
		for (size_t i = 0; i < block.instrs.size(); ++i)
			if (remove.find(i) == remove.end())
				kept.push_back(block.instrs[i]);
		block.instrs.swap(kept);
	}
}

}  // namespace

FunctionOut make_constructor_base_entry(const FunctionOut& lowered,
                                        const string& name)
{
	FunctionOut base_entry = lowered;
	base_entry.name = name + "__base_entry";
	vector<string> param_names = lowered.parameter_names;
	string from = "function @" + name + "(";
	string to = "function @" + name + "__base_entry(";
	size_t pos = base_entry.header.find(from);
	if (pos != string::npos)
		base_entry.header.replace(pos, from.size(), to);
	remove_hidden_pvb_parameters(base_entry.header);
	strip_constructor_base_entry_virtual_base_initializers(base_entry);
	rewrite_constructor_base_entry_pvb_stores(base_entry, param_names);
	apply_constructor_base_entry_arg_rewrites(base_entry);
	TypePtr record = class_record_for_member(lowered.binding);
	TypePtr bare_record = record.get() != NULL
		? pa11::strip_cv(record) : TypePtr();
	if (bare_record.get() != NULL &&
	    bare_record->kind == TypeKind::Record &&
	    bare_record->is_polymorphic &&
	    record_uses_virtual_base_vtt(bare_record))
	{
		insert_constructor_base_entry_vtt_parameter(base_entry);
		rewrite_constructor_base_entry_vptr_stores(base_entry,
		                                           bare_record);
		rewrite_constructor_base_entry_vtt_references(base_entry,
		                                              bare_record);
	}
	renumber_function_temps(base_entry);
	vector<TypePtr> vbases = hidden_virtual_bases_for_record(record);
	if (!vbases.empty())
	{
		size_t close = base_entry.header.find(") ->");
		if (close != string::npos)
		{
			ostringstream hidden;
			for (size_t i = 0; i < vbases.size(); ++i)
				hidden << ", %__vbptr" << i << " : ptr";
			base_entry.header.insert(close, hidden.str());
		}
	}
	size_t object_pos = base_entry.header.find("object=");
	if (object_pos != string::npos)
	{
		size_t ctor_pos = base_entry.header.find("C1", object_pos);
		if (ctor_pos != string::npos)
			base_entry.header.replace(ctor_pos, 2, "C2");
	}
	return base_entry;
}

FunctionOut make_destructor_base_entry(const FunctionOut& lowered,
                                       const string& name,
                                       bool native_lowering)
{
	FunctionOut base_entry = lowered;
	base_entry.name = name + "__base_entry";
	string from = "function @" + name + "(";
	string to = "function @" + name + "__base_entry(";
	size_t pos = base_entry.header.find(from);
	if (pos != string::npos)
		base_entry.header.replace(pos, from.size(), to);
	TypePtr record = class_record_for_member(lowered.binding);
	TypePtr bare_record = record.get() != NULL
		? pa11::strip_cv(record) : TypePtr();
	if (!native_lowering &&
	    bare_record.get() != NULL &&
	    bare_record->kind == TypeKind::Record &&
	    bare_record->is_polymorphic &&
	    record_uses_virtual_base_vtt(bare_record))
	{
		insert_constructor_base_entry_vtt_parameter(base_entry);
		rewrite_constructor_base_entry_vptr_stores(base_entry,
		                                           bare_record);
		rewrite_constructor_base_entry_vtt_references(base_entry,
		                                              bare_record);
		vector<TypePtr> vbases = hidden_virtual_bases_for_record(bare_record);
		if (!vbases.empty())
		{
			size_t close = base_entry.header.find(") ->");
			if (close != string::npos)
			{
				ostringstream hidden;
				for (size_t i = 0; i < vbases.size(); ++i)
					hidden << ", %__vbptr" << i << " : ptr";
				base_entry.header.insert(close, hidden.str());
			}
		}
		renumber_function_temps(base_entry);
	}
	size_t object_pos = base_entry.header.find("object=");
	if (object_pos != string::npos)
	{
		size_t dtor_pos = base_entry.header.find("D1", object_pos);
		if (dtor_pos != string::npos)
			base_entry.header.replace(dtor_pos, 2, "D2");
	}
	return base_entry;
}

}  // namespace internal
}  // namespace pa14
