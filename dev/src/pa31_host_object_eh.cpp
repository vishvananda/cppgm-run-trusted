#include "pa31_host_object_internal.h"

using namespace std;

namespace pa31 {
namespace host {

void append_uleb_to(vector<unsigned char>& out, uint64_t value)
{
	Blob b; uleb(b, value); out.insert(out.end(), b.data.begin(), b.data.end());
}
	void append_sleb_to(vector<unsigned char>& out, int64_t value)
	{
		Blob b; sleb(b, value); out.insert(out.end(), b.data.begin(), b.data.end());
	}
	int ensure_type_symbol_index(map<string, int>& type_index,
	                             vector<string>& types,
	                             const string& type,
	                             int preferred_selector)
	{
		map<string, int>::const_iterator found = type_index.find(type);
		if (found != type_index.end())
			return found->second;
		int selector = preferred_selector > 0
			? preferred_selector
			: static_cast<int>(types.size() + 1);
		if (selector <= 0)
			selector = static_cast<int>(types.size() + 1);
		if (types.size() < static_cast<size_t>(selector))
			types.resize(static_cast<size_t>(selector));
		if (!types[static_cast<size_t>(selector - 1)].empty() &&
		    types[static_cast<size_t>(selector - 1)] != type)
		{
			selector = static_cast<int>(types.size() + 1);
			types.push_back(type);
		}
		else
			types[static_cast<size_t>(selector - 1)] = type;
		type_index[type] = selector;
		return selector;
	}
	int ensure_catch_type_index(map<string, int>& type_index,
	                            vector<string>& types,
	                            const CatchInfo& c)
	{
		const string type = c.catch_all ? string() : c.type_symbol;
		return ensure_type_symbol_index(type_index, types, type, c.selector);
	}
	int ensure_exception_spec_filter(map<string, int>& type_index,
	                                 vector<string>& types,
	                                 map<string, int>& spec_filters,
	                                 vector<unsigned char>& spec_table,
	                                 const CatchInfo& c)
	{
		string key;
		for (size_t i = 0; i < c.exception_spec_types.size(); ++i)
		{
			if (i != 0)
				key += '\n';
			key += c.exception_spec_types[i];
		}
		map<string, int>::const_iterator found = spec_filters.find(key);
		if (found != spec_filters.end())
			return found->second;
		const size_t start = spec_table.size();
		for (size_t i = 0; i < c.exception_spec_types.size(); ++i)
		{
			int index = ensure_type_symbol_index(
				type_index, types, c.exception_spec_types[i], 0);
			append_uleb_to(spec_table, static_cast<uint64_t>(index));
		}
		append_uleb_to(spec_table, 0);
		const int filter = -static_cast<int>(start + 1);
		spec_filters[key] = filter;
		return filter;
	}
	int append_action_chain(vector<unsigned char>& action_table,
	                        map<string, int>& type_index,
	                        vector<string>& types,
	                        map<string, int>& spec_filters,
	                        vector<unsigned char>& spec_table,
	                        const vector<CatchInfo>& catch_list,
	                        bool cleanup)
	{
		vector<int> filters;
		if (cleanup && !catch_list.empty())
			filters.push_back(0);
		for (size_t i = 0; i < catch_list.size(); ++i)
		{
			if (catch_list[i].exception_spec)
				filters.push_back(ensure_exception_spec_filter(
					type_index, types, spec_filters, spec_table,
					catch_list[i]));
			else
				filters.push_back(
					ensure_catch_type_index(type_index, types,
					                        catch_list[i]));
		}
		if (filters.empty())
			return 0;
		int next_start = -1;
		for (size_t n = 0; n < filters.size(); ++n)
		{
			const size_t i = filters.size() - 1 - n;
			const int record_start = static_cast<int>(action_table.size());
			append_sleb_to(action_table, filters[i]);
			const int64_t next = next_start < 0
				? 0
				: static_cast<int64_t>(next_start) -
				  static_cast<int64_t>(action_table.size());
			append_sleb_to(action_table, next);
			next_start = record_start;
		}
		return next_start + 1;
	}
	void FuncGen::finish_lsda(FunctionInfo& info, size_t base)
	{
	if (ranges.empty())
		return;
	sort(ranges.begin(), ranges.end(),
	     [](const EhRange& a, const EhRange& b) { return a.start < b.start; });
	map<string, int> type_index;
	map<string, int> spec_filters;
	vector<string> types;
	vector<unsigned char> call_table;
	vector<unsigned char> action_table;
	vector<unsigned char> spec_table;
	size_t cursor = 0;
	for (size_t i = 0; i < ranges.size(); ++i)
	{
		const size_t range_start = ranges[i].start - base;
		const size_t range_end = ranges[i].end - base + 1;
		if (range_start > cursor)
		{
			append_uleb_to(call_table, cursor);
			append_uleb_to(call_table, range_start - cursor);
			append_uleb_to(call_table, 0);
			append_uleb_to(call_table, 0);
		}
		const size_t lp = ranges[i].target.empty()
			? 0 : block_offsets[ranges[i].target];
			int action = 0;
			map<string, vector<CatchInfo> >::const_iterator c =
				ranges[i].target.empty() ? catches.end()
				                         : catches.find(ranges[i].target);
			const bool cleanup =
				!ranges[i].target.empty() &&
				cleanup_action_blocks.count(ranges[i].target) != 0;
			if (c != catches.end())
				action = append_action_chain(action_table, type_index, types,
				                             spec_filters, spec_table,
				                             c->second, cleanup);
		append_uleb_to(call_table, range_start);
		append_uleb_to(call_table, range_end - range_start);
		append_uleb_to(call_table, lp);
		append_uleb_to(call_table, action);
		cursor = max(cursor, range_end);
	}
	if (cursor < info.size)
	{
		append_uleb_to(call_table, cursor);
		append_uleb_to(call_table, info.size - cursor);
		append_uleb_to(call_table, 0);
		append_uleb_to(call_table, 0);
	}
	vector<string> type_refs(types.size());
	for (size_t i = 0; i < types.size(); ++i)
		if (!types[i].empty())
			type_refs[i] = unit.obj.ensure_dw_ref(types[i]);
	Section& lsda = unit.obj.gcc_except_table();
	lsda.bytes.align(4);
	const size_t start = lsda.bytes.pos();
	info.has_lsda = true;
	info.lsda_offset = start;
	lsda.bytes.u8(0xff);
	if (types.empty())
		lsda.bytes.u8(0xff);
	else
	{
		lsda.bytes.u8(0x9b);
		const size_t offset_pos = lsda.bytes.pos();
		uleb(lsda.bytes, 1);
		lsda.bytes.u8(0x01);
		uleb(lsda.bytes, call_table.size());
		for (size_t i = 0; i < call_table.size(); ++i) lsda.bytes.u8(call_table[i]);
		for (size_t i = 0; i < action_table.size(); ++i) lsda.bytes.u8(action_table[i]);
		for (size_t n = 0; n < types.size(); ++n)
		{
				const string& type = types[types.size() - 1 - n];
				const size_t off = lsda.bytes.pos();
				lsda.bytes.u32(0);
				if (!type.empty())
					unit.obj.reloc(lsda, off,
					               type_refs[types.size() - 1 - n],
					               R_X86_64_PC32, 0);
		}
		const size_t base_pos = lsda.bytes.pos();
		for (size_t i = 0; i < spec_table.size(); ++i)
			lsda.bytes.u8(spec_table[i]);
		const uint64_t ttype_offset = base_pos - (offset_pos + 1);
		lsda.bytes.data[offset_pos] = static_cast<unsigned char>(ttype_offset);
		return;
	}
		lsda.bytes.u8(0x01);
		uleb(lsda.bytes, call_table.size());
		for (size_t i = 0; i < call_table.size(); ++i) lsda.bytes.u8(call_table[i]);
		for (size_t i = 0; i < action_table.size(); ++i) lsda.bytes.u8(action_table[i]);
	}

	void cie_instructions(Blob& b)
{
	b.u8(0x0c); uleb(b, 7); uleb(b, 8);
	b.u8(0x90); uleb(b, 1);
}
size_t write_cie(ObjectFile& obj, bool personality)
{
	Section& eh = obj.eh_frame();
	eh.bytes.align(4);
	const size_t start = eh.bytes.pos();
	eh.bytes.u32(0);
	eh.bytes.u32(0);
	eh.bytes.u8(1);
	const char* aug = personality ? "zPLR" : "zR";
	for (const char* p = aug; *p; ++p) eh.bytes.u8(static_cast<uint8_t>(*p));
	eh.bytes.u8(0);
	uleb(eh.bytes, 1);
	sleb(eh.bytes, -8);
	uleb(eh.bytes, 16);
	if (personality)
	{
		uleb(eh.bytes, 7);
		eh.bytes.u8(0x9b);
		const size_t off = eh.bytes.pos();
		eh.bytes.u32(0);
		obj.reloc(eh, off, obj.ensure_dw_ref("__gxx_personality_v0"),
		          R_X86_64_PC32, 0);
		eh.bytes.u8(0x1b);
		eh.bytes.u8(0x1b);
	}
	else
	{
		uleb(eh.bytes, 1);
		eh.bytes.u8(0x1b);
	}
	cie_instructions(eh.bytes);
	eh.bytes.align(4);
	eh.bytes.patch32(start, static_cast<uint32_t>(eh.bytes.pos() - start - 4));
	return start;
}
void write_fde(ObjectFile& obj, const FunctionInfo& fn, size_t cie)
{
	Section& eh = obj.eh_frame();
	eh.bytes.align(4);
	const size_t start = eh.bytes.pos();
	eh.bytes.u32(0);
	eh.bytes.u32(static_cast<uint32_t>((start + 4) - cie));
	const size_t loc = eh.bytes.pos();
	eh.bytes.u32(0);
	obj.reloc(eh, loc, fn.section, R_X86_64_PC32, fn.start);
	eh.bytes.u32(static_cast<uint32_t>(fn.size));
	if (fn.has_lsda)
	{
		uleb(eh.bytes, 4);
		const size_t off = eh.bytes.pos();
		eh.bytes.u32(0);
		obj.reloc(eh, off, ".gcc_except_table", R_X86_64_PC32,
		          fn.lsda_offset);
	}
	else
		uleb(eh.bytes, 0);
	eh.bytes.u8(0x41);
	eh.bytes.u8(0x0e); uleb(eh.bytes, 16);
	eh.bytes.u8(0x86); uleb(eh.bytes, 2);
	eh.bytes.u8(0x43);
	eh.bytes.u8(0x0d); uleb(eh.bytes, 6);
	eh.bytes.align(4);
	eh.bytes.patch32(start, static_cast<uint32_t>(eh.bytes.pos() - start - 4));
}
void Unit::emit_eh_frame()
{
	if (infos.empty())
		return;
	const size_t cie_plain = write_cie(obj, false);
	size_t cie_eh = 0;
	bool made_eh = false;
	for (size_t i = 0; i < infos.size(); ++i)
	{
		if (infos[i].has_lsda && !made_eh)
		{
			cie_eh = write_cie(obj, true);
			made_eh = true;
		}
		write_fde(obj, infos[i], infos[i].has_lsda ? cie_eh : cie_plain);
	}
}

}  // namespace host
}  // namespace pa31
