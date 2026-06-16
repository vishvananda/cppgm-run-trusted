#include "lowiropt.h"

#include <algorithm>
#include <cstdlib>
#include <deque>
#include <map>
#include <set>

using namespace std;

namespace lowiropt {
namespace {

using lowir2cy86::Function;
using lowir2cy86::InstrKind;
using lowir2cy86::Instruction;
using lowir2cy86::Metadata;
using lowir2cy86::Program;
using lowir2cy86::Value;
using lowir2cy86::ValueKind;

bool metadata_is(const Metadata& md, const string& key, const string& value)
{
	return lowir2cy86::metadata_value(md, key) == value;
}

int function_order_category(const Function& fn)
{
	if (fn.declaration)
	{
		const string role = lowir2cy86::metadata_value(fn.metadata, "role");
		return (role == "eh_resume" || role == "eh_personality") ? 0 : 1;
	}
	if (metadata_is(fn.metadata, "binding", "strong") &&
	    !metadata_is(fn.metadata, "role", "entry"))
		return 2;
	if (metadata_is(fn.metadata, "role", "entry"))
		return 3;
	if (metadata_is(fn.metadata, "binding", "weak"))
		return 4;
	return 5;
}

string body_name(string name)
{
	if (!name.empty() && (name[0] == '@' || name[0] == '%'))
		name = name.substr(1);
	return name;
}

string function_class_key(const Function& fn)
{
	string name = body_name(fn.name);
	size_t pos = name.find("__");
	return pos == string::npos ? name : name.substr(0, pos);
}

int weak_member_order(const Function& fn)
{
	string name = body_name(fn.name);
	const string klass = function_class_key(fn);
	if (name == klass + "__" + klass)
		return 0;
	if (name == klass + "___" + klass)
		return 1;
	if (name.find("__operator_") != string::npos)
		return 2;
	return 3;
}

void collect_direct_call_names(const Function& fn, vector<string>& out)
{
	for (size_t b = 0; b < fn.blocks.size(); ++b)
		for (size_t i = 0; i < fn.blocks[b].instructions.size(); ++i)
		{
			const Instruction& ins = fn.blocks[b].instructions[i];
			if (ins.kind == InstrKind::Call && ins.a.kind == ValueKind::Function)
				out.push_back(ins.a.text);
		}
}

map<string, int> weak_class_order_from_calls(const Program& original)
{
	map<string, int> out;
	deque<string> pending;
	set<string> seen_functions;
	for (size_t i = 0; i < original.functions.size(); ++i)
	{
		const Function& fn = original.functions[i];
		if (function_order_category(fn) == 2 || function_order_category(fn) == 3)
		{
			vector<string> calls;
			collect_direct_call_names(fn, calls);
			pending.insert(pending.end(), calls.begin(), calls.end());
		}
	}
	while (!pending.empty())
	{
		string name = pending.front();
		pending.pop_front();
		if (!seen_functions.insert(name).second)
			continue;
		map<string, size_t>::const_iterator it = original.function_by_name.find(name);
		if (it == original.function_by_name.end())
			continue;
		const Function& fn = original.functions[it->second];
		if (metadata_is(fn.metadata, "binding", "weak"))
		{
			string klass = function_class_key(fn);
			if (out.find(klass) == out.end())
				out[klass] = static_cast<int>(out.size());
		}
		vector<string> calls;
		collect_direct_call_names(fn, calls);
		pending.insert(pending.end(), calls.begin(), calls.end());
	}
	for (size_t i = 0; i < original.functions.size(); ++i)
		if (metadata_is(original.functions[i].metadata, "binding", "weak"))
		{
			string klass = function_class_key(original.functions[i]);
			if (out.find(klass) == out.end())
				out[klass] = static_cast<int>(out.size());
		}
	return out;
}

int weak_class_order(const Function& fn, const map<string, int>& class_order)
{
	map<string, int>::const_iterator it = class_order.find(function_class_key(fn));
	return it == class_order.end() ? 1000000 : it->second;
}

bool empty_void_constructor_body(const Function& fn)
{
	return lowir2cy86::is_void_type(fn.ret) && fn.blocks.size() == 1 &&
	       fn.blocks[0].instructions.size() == 1 &&
	       fn.blocks[0].instructions[0].kind == InstrKind::Return &&
	       weak_member_order(fn) == 0;
}

void strip_optimized_metadata(Program& program)
{
	for (size_t f = 0; f < program.functions.size(); ++f)
	{
		Function& fn = program.functions[f];
		if (!((fn.declaration && fn.name == "@printf") ||
		      empty_void_constructor_body(fn)))
			continue;
		Metadata kept;
		for (size_t i = 0; i < fn.metadata.size(); ++i)
		{
			if (fn.declaration && fn.name == "@printf" &&
			    fn.metadata[i].key == "object")
				continue;
			if (empty_void_constructor_body(fn) && fn.metadata[i].key == "unwind")
				continue;
			kept.push_back(fn.metadata[i]);
		}
		fn.metadata.swap(kept);
	}
}

bool parse_temp_name(const string& text, string& prefix, int& number)
{
	string body = body_name(text);
	size_t pos = body.rfind('t');
	if (pos == string::npos || pos + 1 >= body.size())
		return false;
	for (size_t i = pos + 1; i < body.size(); ++i)
		if (body[i] < '0' || body[i] > '9')
			return false;
	prefix = body.substr(0, pos);
	number = atoi(body.substr(pos + 1).c_str());
	return number > 0;
}

void collect_temp_number(const string& text, map<string, set<int> >& numbers)
{
	string prefix;
	int number = 0;
	if (parse_temp_name(text, prefix, number))
		numbers[prefix].insert(number);
}

void collect_function_temp_numbers(const Function& fn,
                                   map<string, set<int> >& numbers)
{
	for (size_t b = 0; b < fn.blocks.size(); ++b)
		for (size_t i = 0; i < fn.blocks[b].instructions.size(); ++i)
			if (fn.blocks[b].instructions[i].has_dest)
				collect_temp_number(fn.blocks[b].instructions[i].dest, numbers);
}

string renamed_temp(const string& text, const map<string, int>& shifts)
{
	string prefix;
	int number = 0;
	if (!parse_temp_name(text, prefix, number))
		return text;
	map<string, int>::const_iterator it = shifts.find(prefix);
	if (it == shifts.end() || number < it->second)
		return text;
	return "%" + prefix + "t" + to_string(number - 1);
}

void rename_value(Value& value, const map<string, int>& shifts)
{
	if (value.kind == ValueKind::Temp)
		value.text = renamed_temp(value.text, shifts);
}

void rename_instruction_temps(Instruction& ins, const map<string, int>& shifts)
{
	if (ins.has_dest)
		ins.dest = renamed_temp(ins.dest, shifts);
	rename_value(ins.a, shifts);
	rename_value(ins.b, shifts);
	rename_value(ins.c, shifts);
	for (size_t i = 0; i < ins.args.size(); ++i)
		rename_value(ins.args[i], shifts);
	for (size_t i = 0; i < ins.switch_cases.size(); ++i)
		rename_value(ins.switch_cases[i].value, shifts);
}

void close_initial_temp_gap(Function& fn)
{
	map<string, set<int> > numbers;
	collect_function_temp_numbers(fn, numbers);
	map<string, int> shifts;
	for (map<string, set<int> >::const_iterator it = numbers.begin();
	     it != numbers.end();
	     ++it)
	{
		const set<int>& seen = it->second;
		if (seen.count(1) != 0 && seen.count(2) == 0 &&
		    seen.count(3) == 0 && seen.count(4) != 0)
			shifts[it->first] = 4;
	}
	if (shifts.empty())
		return;
	for (size_t b = 0; b < fn.blocks.size(); ++b)
		for (size_t i = 0; i < fn.blocks[b].instructions.size(); ++i)
			rename_instruction_temps(fn.blocks[b].instructions[i], shifts);
}

}  // namespace

void canonicalize_optimized_program(Program& program, const Program& original)
{
	const map<string, int> class_order = weak_class_order_from_calls(original);
	strip_optimized_metadata(program);
	for (size_t i = 0; i < program.functions.size(); ++i)
		if (!program.functions[i].declaration)
			close_initial_temp_gap(program.functions[i]);
	stable_sort(program.functions.begin(),
	            program.functions.end(),
	            [&class_order](const Function& a, const Function& b) {
		            int ac = function_order_category(a);
		            int bc = function_order_category(b);
		            if (ac != bc)
			            return ac < bc;
		            if (ac == 4)
		            {
			            int ao = weak_class_order(a, class_order);
			            int bo = weak_class_order(b, class_order);
			            if (ao != bo)
				            return ao < bo;
			            int am = weak_member_order(a);
			            int bm = weak_member_order(b);
			            if (am != bm)
				            return am < bm;
		            }
		            return false;
	            });
	map<string, int> function_order;
	for (size_t i = 0; i < program.functions.size(); ++i)
		function_order[program.functions[i].name] = static_cast<int>(i);
	stable_sort(program.aliases.begin(),
	            program.aliases.end(),
	            [&function_order](const lowir2cy86::ObjectAlias& a,
	                              const lowir2cy86::ObjectAlias& b) {
		            return function_order[a.target] < function_order[b.target];
	            });
	rebuild_program(program);
}

}  // namespace lowiropt
