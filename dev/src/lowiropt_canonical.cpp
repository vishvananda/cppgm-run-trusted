#include "lowiropt.h"

#include <algorithm>
#include <cstdlib>
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

string function_object_order_key(const Function& fn)
{
	const string object = lowir2cy86::metadata_value(fn.metadata, "object");
	return object.empty() ? body_name(fn.name) : object;
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

void collect_weak_order_value(const Program& program,
                              const Value& value,
                              map<string, size_t>& order,
                              set<string>& visiting);

void collect_weak_order_function(const Program& program,
                                 const string& name,
                                 map<string, size_t>& order,
                                 set<string>& visiting)
{
	map<string, size_t>::const_iterator found =
		program.function_by_name.find(name);
	if (found == program.function_by_name.end())
		return;
	const Function& fn = program.functions[found->second];
	if (fn.declaration)
		return;
	if (function_order_category(fn) == 4 &&
	    order.find(fn.name) == order.end())
		order[fn.name] = order.size();
	if (!visiting.insert(fn.name).second)
		return;
	for (size_t b = 0; b < fn.blocks.size(); ++b)
		for (size_t i = 0; i < fn.blocks[b].instructions.size(); ++i)
		{
			const Instruction& ins = fn.blocks[b].instructions[i];
			collect_weak_order_value(program, ins.a, order, visiting);
			collect_weak_order_value(program, ins.b, order, visiting);
			collect_weak_order_value(program, ins.c, order, visiting);
			for (size_t a = 0; a < ins.args.size(); ++a)
				collect_weak_order_value(program, ins.args[a], order, visiting);
			for (size_t s = 0; s < ins.switch_cases.size(); ++s)
				collect_weak_order_value(program,
				                         ins.switch_cases[s].value,
				                         order,
				                         visiting);
		}
	visiting.erase(fn.name);
}

void collect_weak_order_value(const Program& program,
                              const Value& value,
                              map<string, size_t>& order,
                              set<string>& visiting)
{
	if (value.kind == ValueKind::Function ||
	    (value.kind == ValueKind::Global &&
	     program.function_by_name.find(value.text) !=
		     program.function_by_name.end()))
		collect_weak_order_function(program, value.text, order, visiting);
}

map<string, size_t> original_reachable_weak_order(const Program& original)
{
	map<string, size_t> order;
	set<string> visiting;
	for (size_t i = 0; i < original.functions.size(); ++i)
	{
		const Function& fn = original.functions[i];
		if (fn.declaration || function_order_category(fn) == 4)
			continue;
		collect_weak_order_function(original, fn.name, order, visiting);
	}
	return order;
}

}  // namespace

void canonicalize_optimized_program(Program& program,
                                    const Program& original,
                                    bool preserve_weak_order)
{
	strip_optimized_metadata(program);
	for (size_t i = 0; i < program.functions.size(); ++i)
		if (!program.functions[i].declaration)
			close_initial_temp_gap(program.functions[i]);
	map<string, size_t> weak_order = preserve_weak_order
		? original_reachable_weak_order(original)
		: map<string, size_t>();
	map<string, size_t> weak_class_order;
	if (preserve_weak_order)
		for (size_t i = 0; i < program.functions.size(); ++i)
		{
			const Function& fn = program.functions[i];
			map<string, size_t>::const_iterator found =
				weak_order.find(fn.name);
			if (found == weak_order.end())
				continue;
			string klass = function_class_key(fn);
			map<string, size_t>::iterator existing =
				weak_class_order.find(klass);
			if (existing == weak_class_order.end() ||
			    found->second < existing->second)
				weak_class_order[klass] = found->second;
		}
	stable_sort(program.functions.begin(),
	            program.functions.end(),
	            [preserve_weak_order,
	             &weak_order,
	             &weak_class_order](const Function& a, const Function& b) {
		            int ac = function_order_category(a);
		            int bc = function_order_category(b);
		            if (ac != bc)
			            return ac < bc;
		            if (ac == 1)
		            {
			            string ak = lowir2cy86::metadata_value(a.metadata, "object");
			            string bk = lowir2cy86::metadata_value(b.metadata, "object");
			            if (ak.empty() && bk.empty())
				            return false;
			            if (ak.empty() != bk.empty())
				            return !ak.empty();
			            if (ak != bk)
				            return ak < bk;
			            return a.name < b.name;
		            }
		            if (ac == 4)
		            {
			            if (preserve_weak_order)
			            {
				            string ak = function_class_key(a);
				            string bk = function_class_key(b);
				            if (ak != bk)
				            {
					            map<string, size_t>::const_iterator aco =
						            weak_class_order.find(ak);
					            map<string, size_t>::const_iterator bco =
						            weak_class_order.find(bk);
					            bool ach = aco != weak_class_order.end();
					            bool bch = bco != weak_class_order.end();
					            if (ach != bch)
						            return ach;
					            if (ach && aco->second != bco->second)
						            return aco->second < bco->second;
				            }
			            }
			            string ak = function_class_key(a);
			            string bk = function_class_key(b);
			            if (ak != bk)
				            return ak < bk;
			            int am = weak_member_order(a);
			            int bm = weak_member_order(b);
			            if (am != bm)
				            return am < bm;
			            ak = function_object_order_key(a);
			            bk = function_object_order_key(b);
			            if (ak != bk)
				            return ak < bk;
			            return a.name < b.name;
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
