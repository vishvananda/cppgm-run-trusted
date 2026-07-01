#include "pa31_host_object_internal.h"

using namespace std;

namespace pa31 {
namespace host {

namespace {

const string& catch_all_type_marker()
{
	static const string marker = "\001catch_all";
	return marker;
}

string catch_all_type_key(int selector)
{
	return catch_all_type_marker() + ":" + to_string(selector);
}

bool is_catch_all_type_key(const string& type)
{
	const string& marker = catch_all_type_marker();
	return type.compare(0, marker.size(), marker) == 0;
}

}  // namespace

void append_uleb_to(vector<unsigned char>& out, uint64_t value)
{
	Blob b; uleb(b, value); out.insert(out.end(), b.data.begin(), b.data.end());
}
	void append_bytes(Blob& out, const vector<unsigned char>& bytes)
	{
		out.data.insert(out.data.end(), bytes.begin(), bytes.end());
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
		const string type = c.catch_all
			? catch_all_type_key(c.selector)
			: c.type_symbol;
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
	                        const vector<CatchInfo>& catch_list,
	                        bool cleanup)
		{
			vector<int> filters;
			for (size_t i = 0; i < catch_list.size(); ++i)
				filters.push_back(catch_list[i].raw_selector);
			if (cleanup && !catch_list.empty())
				filters.push_back(0);
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
	vector<unsigned char> call_table;
	vector<unsigned char> action_table;
	size_t cursor = 0;
	for (size_t i = 0; i < ranges.size(); ++i)
	{
		const size_t range_start = ranges[i].start - base;
		const size_t range_end = ranges[i].end - base;
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
				action = append_action_chain(action_table, c->second,
				                             cleanup);
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
	vector<string> type_refs(lsda_types.size());
	for (size_t i = 0; i < lsda_types.size(); ++i)
		if (!lsda_types[i].empty() &&
		    !is_catch_all_type_key(lsda_types[i]))
			type_refs[i] = unit.obj.ensure_dw_ref(lsda_types[i]);
	Section& lsda = unit.obj.gcc_except_table();
	lsda.bytes.align(4);
	const size_t start = lsda.bytes.pos();
	info.has_lsda = true;
	info.lsda_offset = start;
	lsda.bytes.u8(0xff);
	if (lsda_types.empty())
	{
		lsda.bytes.u8(0xff);
		lsda.bytes.u8(0x01);
		uleb(lsda.bytes, call_table.size());
		for (size_t i = 0; i < call_table.size(); ++i) lsda.bytes.u8(call_table[i]);
		for (size_t i = 0; i < action_table.size(); ++i) lsda.bytes.u8(action_table[i]);
	}
	else
	{
		Blob body;
		body.u8(0x01);
		uleb(body, call_table.size());
		append_bytes(body, call_table);
		append_bytes(body, action_table);
		vector<size_t> type_offsets;
		for (size_t n = 0; n < lsda_types.size(); ++n)
		{
			type_offsets.push_back(body.pos());
			body.u32(0);
		}
		const size_t type_table_base = body.pos();
		append_bytes(body, lsda_spec_table);
		lsda.bytes.u8(0x9b);
		uleb(lsda.bytes, type_table_base);
		const size_t body_start = lsda.bytes.pos();
		append_bytes(lsda.bytes, body.data);
		for (size_t n = 0; n < type_offsets.size(); ++n)
		{
			const size_t i = lsda_types.size() - 1 - n;
			if (!lsda_types[i].empty() &&
			    !is_catch_all_type_key(lsda_types[i]))
				unit.obj.reloc(lsda, body_start + type_offsets[n],
				               type_refs[i], R_X86_64_PC32, 0);
		}
	}
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
	bool any_fde = false;
	for (size_t i = 0; i < infos.size(); ++i)
		any_fde = any_fde || infos[i].emit_fde;
	if (!any_fde)
		return;
	const size_t cie_plain = write_cie(obj, false);
	size_t cie_eh = 0;
	bool made_eh = false;
	for (size_t i = 0; i < infos.size(); ++i)
	{
		if (!infos[i].emit_fde)
			continue;
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
