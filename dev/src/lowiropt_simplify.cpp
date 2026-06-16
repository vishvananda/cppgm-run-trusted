#include "lowiropt.h"

#include <algorithm>
#include <cstdlib>
#include <iterator>
#include <map>
#include <set>
#include <stdexcept>

using namespace std;

namespace lowiropt {
namespace {

using lowir2cy86::Block;
using lowir2cy86::Function;
using lowir2cy86::InstrKind;
using lowir2cy86::Instruction;
using lowir2cy86::Metadata;
using lowir2cy86::MetadataItem;
using lowir2cy86::Program;
using lowir2cy86::Slot;
using lowir2cy86::SwitchCase;
using lowir2cy86::Type;
using lowir2cy86::Value;
using lowir2cy86::ValueKind;

struct Fact
{
	Value value;
	size_t block;
};

struct ExprFact
{
	string temp;
	size_t block;
};

Value literal_value(const string& text)
{
	Value value;
	value.kind = ValueKind::Literal;
	value.text = text;
	return value;
}

Value temp_value(const string& text)
{
	Value value;
	value.kind = ValueKind::Temp;
	value.text = text;
	return value;
}

bool is_literal(const Value& value, const string& text)
{
	return value.kind == ValueKind::Literal && value.text == text;
}

bool parse_int_literal(const string& text, long long& out)
{
	char* end = 0;
	out = strtoll(text.c_str(), &end, 0);
	return end != text.c_str() && *end == '\0';
}

string int_text(long long value)
{
	return to_string(value);
}

bool literal_truth(const Value& value, bool& out)
{
	if (value.kind != ValueKind::Literal)
		return false;
	long long n = 0;
	if (!parse_int_literal(value.text, n))
		return false;
	out = n != 0;
	return true;
}

string value_key(const Value& value)
{
	return value.text;
}

void count_storage_temp(const Value& value, set<string>& out)
{
	if (value.kind == ValueKind::Temp)
		out.insert(value.text);
}

set<string> storage_temp_uses(const Function& fn)
{
	set<string> out;
	for (size_t b = 0; b < fn.blocks.size(); ++b)
		for (size_t i = 0; i < fn.blocks[b].instructions.size(); ++i)
		{
			const Instruction& ins = fn.blocks[b].instructions[i];
			if (ins.kind == InstrKind::Load ||
			    ins.kind == InstrKind::AtomicLoad ||
			    ins.kind == InstrKind::VaArg)
				count_storage_temp(ins.a, out);
			else if (ins.kind == InstrKind::Store ||
			         ins.kind == InstrKind::AtomicStore ||
			         ins.kind == InstrKind::AtomicExchange ||
			         ins.kind == InstrKind::AtomicCompareExchange ||
			         ins.kind == InstrKind::AtomicAddFetch)
				count_storage_temp(ins.b, out);
			else if (ins.kind == InstrKind::CopyObj)
				count_storage_temp(ins.b, out);
			else if (ins.kind == InstrKind::ZeroInit)
				count_storage_temp(ins.a, out);
		}
	return out;
}

bool dominates(const vector<set<size_t> >& doms, size_t def_block, size_t use_block)
{
	return use_block < doms.size() && doms[use_block].count(def_block) != 0;
}

void replace_value(Value& value,
                   const map<string, Fact>& facts,
                   const vector<set<size_t> >& doms,
                   size_t block)
{
	set<string> seen;
	while (value.kind == ValueKind::Temp)
	{
		map<string, Fact>::const_iterator it = facts.find(value.text);
		if (it == facts.end() || !dominates(doms, it->second.block, block))
			return;
		if (!seen.insert(value.text).second)
			return;
		value = it->second.value;
	}
}

void replace_instruction_values(Instruction& ins,
                                const map<string, Fact>& facts,
                                const vector<set<size_t> >& doms,
                                size_t block)
{
	replace_value(ins.a, facts, doms, block);
	replace_value(ins.b, facts, doms, block);
	replace_value(ins.c, facts, doms, block);
	for (size_t i = 0; i < ins.args.size(); ++i)
		replace_value(ins.args[i], facts, doms, block);
	for (size_t i = 0; i < ins.switch_cases.size(); ++i)
		replace_value(ins.switch_cases[i].value, facts, doms, block);
}

bool commutative_binary(const string& op)
{
	return op == "add" || op == "mul" || op == "and" ||
	       op == "or" || op == "xor";
}

string reverse_cmp(const string& op)
{
	if (op == "lt") return "gt";
	if (op == "gt") return "lt";
	if (op == "le") return "ge";
	if (op == "ge") return "le";
	if (op == "ult") return "ugt";
	if (op == "ugt") return "ult";
	if (op == "ule") return "uge";
	if (op == "uge") return "ule";
	return op;
}

bool normalize_cmp_key(string& op, string& a, string& b)
{
	const string rev = reverse_cmp(op);
	if (rev != op && a > b)
	{
		op = rev;
		swap(a, b);
		return true;
	}
	return false;
}

string expr_key(const Instruction& ins)
{
	if (ins.kind == InstrKind::Addr)
		return "addr|" + value_key(ins.a);
	if (ins.kind == InstrKind::Index)
		return "index|" + ins.type.text + "|" + ins.op + "|" +
		       value_key(ins.a) + "|" + value_key(ins.b);
	if (ins.kind == InstrKind::Unary)
		return "unary|" + ins.op + "|" + ins.type.text + "|" +
		       value_key(ins.a);
	if (ins.kind == InstrKind::Binary)
	{
		string a = value_key(ins.a);
		string b = value_key(ins.b);
		if (commutative_binary(ins.op) && b < a)
			swap(a, b);
		return "binary|" + ins.op + "|" + ins.type.text + "|" + a + "|" + b;
	}
	if (ins.kind == InstrKind::Cmp)
	{
		string op = ins.op;
		string a = value_key(ins.a);
		string b = value_key(ins.b);
		normalize_cmp_key(op, a, b);
		return "cmp|" + op + "|" + ins.type.text + "|" + a + "|" + b;
	}
	if (ins.kind == InstrKind::Convert)
		return "convert|" + ins.op + "|" + ins.type.text + "|" +
		       ins.src_type.text + "|" + value_key(ins.a);
	return "";
}

bool pure_expr_kind(InstrKind kind)
{
	return kind == InstrKind::Addr || kind == InstrKind::Index ||
	       kind == InstrKind::Unary || kind == InstrKind::Binary ||
	       kind == InstrKind::Cmp || kind == InstrKind::Convert;
}

bool type_is_bool_temp(const Function& fn, const string& name)
{
	map<string, Type>::const_iterator it = fn.temp_types.find(name);
	if (it == fn.temp_types.end())
		return false;
	return it->second.text == "i64" || it->second.text == "i1" ||
	       it->second.text == "i32";
}

bool temp_defined_by_cmp(const map<string, const Instruction*>& defs,
                         const Value& value)
{
	if (value.kind != ValueKind::Temp)
		return false;
	map<string, const Instruction*>::const_iterator it = defs.find(value.text);
	return it != defs.end() && it->second->kind == InstrKind::Cmp;
}

bool fold_unary(Instruction& ins, Value& replacement)
{
	if (ins.op == "decay")
	{
		replacement = ins.a;
		return true;
	}
	if (ins.a.kind != ValueKind::Literal)
		return false;
	long long a = 0;
	if (!parse_int_literal(ins.a.text, a))
		return false;
	if (ins.op == "neg")
		replacement = literal_value(int_text(-a));
	else if (ins.op == "lnot")
		replacement = literal_value(a == 0 ? "1" : "0");
	else if (ins.op == "not")
		replacement = literal_value(int_text(~a));
	else
		return false;
	return true;
}

bool eval_binary_int(const string& op, long long a, long long b, long long& out)
{
	if (op == "add") out = a + b;
	else if (op == "sub") out = a - b;
	else if (op == "mul") out = a * b;
	else if (op == "and") out = a & b;
	else if (op == "or") out = a | b;
	else if (op == "xor") out = a ^ b;
	else if (op == "shl") out = a << b;
	else if (op == "shr") out = a >> b;
	else if ((op == "sdiv" || op == "udiv") && b != 0) out = a / b;
	else if ((op == "smod" || op == "umod") && b != 0) out = a % b;
	else return false;
	return true;
}

bool fold_binary(Instruction& ins, Value& replacement)
{
	long long a = 0;
	long long b = 0;
	const bool ai = ins.a.kind == ValueKind::Literal &&
	                parse_int_literal(ins.a.text, a);
	const bool bi = ins.b.kind == ValueKind::Literal &&
	                parse_int_literal(ins.b.text, b);
	if (ai && bi)
	{
		long long out = 0;
		if (eval_binary_int(ins.op, a, b, out))
		{
			replacement = literal_value(int_text(out));
			return true;
		}
	}
	if (ins.op == "add")
	{
		if (is_literal(ins.b, "0")) replacement = ins.a;
		else if (is_literal(ins.a, "0")) replacement = ins.b;
		else return false;
		return true;
	}
	if (ins.op == "sub" && is_literal(ins.b, "0"))
	{
		replacement = ins.a;
		return true;
	}
	if (ins.op == "mul")
	{
		if (is_literal(ins.b, "1")) replacement = ins.a;
		else if (is_literal(ins.a, "1")) replacement = ins.b;
		else if (is_literal(ins.b, "0") || is_literal(ins.a, "0"))
			replacement = literal_value("0");
		else return false;
		return true;
	}
	if ((ins.op == "and" && is_literal(ins.b, "-1")) ||
	    ((ins.op == "or" || ins.op == "xor" || ins.op == "shl" ||
	      ins.op == "shr") && is_literal(ins.b, "0")))
	{
		replacement = ins.a;
		return true;
	}
	if (ins.op == "and" && is_literal(ins.a, "-1"))
	{
		replacement = ins.b;
		return true;
	}
	return false;
}

bool eval_cmp_int(const string& op, long long a, long long b)
{
	if (op == "eq") return a == b;
	if (op == "ne") return a != b;
	if (op == "lt" || op == "ult") return a < b;
	if (op == "le" || op == "ule") return a <= b;
	if (op == "gt" || op == "ugt") return a > b;
	if (op == "ge" || op == "uge") return a >= b;
	return false;
}

bool parse_float_literal(const string& text, double& out)
{
	char* end = 0;
	out = strtod(text.c_str(), &end);
	return end != text.c_str() && *end == '\0';
}

bool eval_cmp_float(const string& op, double a, double b, bool& out)
{
	if (op == "eq") out = a == b;
	else if (op == "ne") out = a != b;
	else if (op == "lt") out = a < b;
	else if (op == "le") out = a <= b;
	else if (op == "gt") out = a > b;
	else if (op == "ge") out = a >= b;
	else return false;
	return true;
}

bool fold_cmp(const map<string, const Instruction*>& defs,
              Instruction& ins,
              Value& replacement)
{
	if (ins.a.text == ins.b.text)
	{
		const bool yes = ins.op == "eq" || ins.op == "le" ||
		                 ins.op == "ge" || ins.op == "ule" ||
		                 ins.op == "uge";
		replacement = literal_value(yes ? "1" : "0");
		return true;
	}
	if (temp_defined_by_cmp(defs, ins.a) && ins.b.kind == ValueKind::Literal)
	{
		if ((ins.op == "eq" && ins.b.text == "1") ||
		    (ins.op == "ne" && ins.b.text == "0"))
		{
			replacement = ins.a;
			return true;
		}
	}
	if (temp_defined_by_cmp(defs, ins.b) && ins.a.kind == ValueKind::Literal)
	{
		if ((ins.op == "eq" && ins.a.text == "1") ||
		    (ins.op == "ne" && ins.a.text == "0"))
		{
			replacement = ins.b;
			return true;
		}
	}
	long long a = 0;
	long long b = 0;
	if (ins.a.kind == ValueKind::Literal && ins.b.kind == ValueKind::Literal &&
	    parse_int_literal(ins.a.text, a) && parse_int_literal(ins.b.text, b))
	{
		replacement = literal_value(eval_cmp_int(ins.op, a, b) ? "1" : "0");
		return true;
	}
	double fa = 0;
	double fb = 0;
	bool fout = false;
	if (ins.a.kind == ValueKind::Literal && ins.b.kind == ValueKind::Literal &&
	    parse_float_literal(ins.a.text, fa) &&
	    parse_float_literal(ins.b.text, fb) &&
	    eval_cmp_float(ins.op, fa, fb, fout))
	{
		replacement = literal_value(fout ? "1" : "0");
		return true;
	}
	return false;
}

bool fold_convert(Instruction& ins, Value& replacement)
{
	if (same_type(ins.type, ins.src_type))
	{
		replacement = ins.a;
		return true;
	}
	if (ins.a.kind != ValueKind::Literal ||
	    (!lowir2cy86::is_integer_type(ins.type) &&
	     !lowir2cy86::is_float_type(ins.type)) ||
	    !lowir2cy86::is_integer_type(ins.src_type))
		return false;
	long long a = 0;
	if (!parse_int_literal(ins.a.text, a))
		return false;
	if (lowir2cy86::is_float_type(ins.type))
	{
		replacement = literal_value(ins.a.text);
		return true;
	}
	if (ins.op == "trunc" && ins.type.bits > 0 && ins.type.bits < 63)
	{
		const long long mask = (1LL << ins.type.bits) - 1;
		a &= mask;
	}
	replacement = literal_value(int_text(a));
	return true;
}

bool reassociate(Instruction& ins,
                 const map<string, const Instruction*>& defs)
{
	if (ins.kind != InstrKind::Binary || ins.a.kind != ValueKind::Temp ||
	    ins.b.kind != ValueKind::Literal)
		return false;
	map<string, const Instruction*>::const_iterator it = defs.find(ins.a.text);
	if (it == defs.end())
		return false;
	const Instruction& prev = *it->second;
	if (prev.kind != InstrKind::Binary || prev.op != ins.op ||
	    !same_type(prev.type, ins.type) || prev.b.kind != ValueKind::Literal)
		return false;
	long long a = 0;
	long long b = 0;
	if (!parse_int_literal(prev.b.text, a) ||
	    !parse_int_literal(ins.b.text, b))
		return false;
	long long combined = 0;
	if (ins.op == "add")
		combined = a + b;
	else if (ins.op == "mul")
		combined = a * b;
	else if (ins.op == "and")
		combined = a & b;
	else if (ins.op == "or")
		combined = a | b;
	else if (ins.op == "xor")
		combined = a ^ b;
	else
		return false;
	ins.a = prev.a;
	ins.b = literal_value(int_text(combined));
	return true;
}

bool simplify_instruction(Function& fn,
                          const Program& program,
                          Instruction& ins,
                          size_t block,
                          const vector<set<size_t> >& doms,
                          const set<string>& storage_temps,
                          map<string, Fact>& facts,
                          map<string, vector<ExprFact> >& exprs,
                          map<string, const Instruction*>& defs)
{
	(void)program;
	bool changed = false;
	replace_instruction_values(ins, facts, doms, block);
	Value replacement;
	bool has_replacement = false;
	if (ins.kind == InstrKind::Const || ins.kind == InstrKind::Copy)
	{
		if (!(ins.kind == InstrKind::Const && ins.has_dest &&
		      ins.type.text == "ptr" &&
		      storage_temps.count(ins.dest) != 0))
		{
			replacement = ins.a;
			has_replacement = true;
		}
	}
	else if (ins.kind == InstrKind::Unary)
		has_replacement = fold_unary(ins, replacement);
	else if (ins.kind == InstrKind::Binary)
	{
		changed = reassociate(ins, defs) || changed;
		has_replacement = fold_binary(ins, replacement);
	}
	else if (ins.kind == InstrKind::Cmp)
		has_replacement = fold_cmp(defs, ins, replacement);
	else if (ins.kind == InstrKind::Convert)
		has_replacement = fold_convert(ins, replacement);

	if (ins.has_dest && has_replacement)
	{
		Fact fact;
		fact.value = replacement;
		fact.block = block;
		facts[ins.dest] = fact;
		changed = true;
	}
	else if (ins.has_dest && pure_expr_kind(ins.kind))
	{
		const string key = expr_key(ins);
		map<string, vector<ExprFact> >::const_iterator found = exprs.find(key);
		bool reused = false;
		if (found != exprs.end())
		{
			for (size_t i = found->second.size(); i > 0; --i)
			{
				const ExprFact& expr = found->second[i - 1];
				if (!dominates(doms, expr.block, block))
					continue;
				Fact fact;
				fact.value = temp_value(expr.temp);
				fact.block = block;
				facts[ins.dest] = fact;
				changed = true;
				reused = true;
				break;
			}
		}
		if (!reused)
		{
			ExprFact expr;
			expr.temp = ins.dest;
			expr.block = block;
			exprs[key].push_back(expr);
		}
	}

	if (ins.has_dest)
		defs[ins.dest] = &ins;
	if (ins.kind == InstrKind::Branch)
	{
		bool truth = false;
		if (literal_truth(ins.a, truth))
		{
			ins.kind = InstrKind::Jump;
			ins.target = truth ? ins.target : ins.target_false;
			ins.target_false.clear();
			changed = true;
		}
		else if (ins.target == ins.target_false)
		{
			ins.kind = InstrKind::Jump;
			ins.target_false.clear();
			changed = true;
		}
	}
	else if (ins.kind == InstrKind::Switch)
	{
		long long selector = 0;
		if (ins.a.kind == ValueKind::Literal &&
		    parse_int_literal(ins.a.text, selector))
		{
			string target = ins.target;
			for (size_t i = 0; i < ins.switch_cases.size(); ++i)
			{
				long long c = 0;
				if (parse_int_literal(ins.switch_cases[i].value.text, c) &&
				    c == selector)
					target = ins.switch_cases[i].target;
			}
			ins.kind = InstrKind::Jump;
			ins.target = target;
			ins.switch_cases.clear();
			changed = true;
		}
	}
	(void)fn;
	return changed;
}

void collect_successors(const Function& fn,
                        size_t block,
                        vector<string>& out,
                        set<string>* eh_targets)
{
	const Block& b = fn.blocks[block];
	for (size_t i = 0; i < b.instructions.size(); ++i)
	{
		const Instruction& ins = b.instructions[i];
		if ((ins.kind == InstrKind::EhTry || ins.kind == InstrKind::EhCleanup) &&
		    !ins.target.empty())
		{
			out.push_back(ins.target);
			if (eh_targets != 0)
				eh_targets->insert(ins.target);
		}
	}
	const Instruction& term = b.instructions.back();
	if (term.kind == InstrKind::Jump)
		out.push_back(term.target);
	else if (term.kind == InstrKind::Branch)
	{
		out.push_back(term.target);
		out.push_back(term.target_false);
	}
	else if (term.kind == InstrKind::Switch)
	{
		out.push_back(term.target);
		for (size_t i = 0; i < term.switch_cases.size(); ++i)
			out.push_back(term.switch_cases[i].target);
	}
}

map<string, size_t> block_indices(const Function& fn)
{
	map<string, size_t> out;
	for (size_t i = 0; i < fn.blocks.size(); ++i)
		out[fn.blocks[i].name] = i;
	return out;
}

vector<set<size_t> > compute_dominators(const Function& fn)
{
	const size_t n = fn.blocks.size();
	vector<set<size_t> > doms(n);
	if (n == 0)
		return doms;
	set<size_t> all;
	for (size_t i = 0; i < n; ++i)
		all.insert(i);
	for (size_t i = 0; i < n; ++i)
		doms[i] = i == 0 ? set<size_t>() : all;
	doms[0].insert(0);

	map<string, size_t> index = block_indices(fn);
	vector<vector<size_t> > preds(n);
	for (size_t b = 0; b < n; ++b)
	{
		vector<string> succs;
		collect_successors(fn, b, succs, 0);
		for (size_t s = 0; s < succs.size(); ++s)
		{
			map<string, size_t>::const_iterator it = index.find(succs[s]);
			if (it != index.end())
				preds[it->second].push_back(b);
		}
	}

	bool changed = true;
	while (changed)
	{
		changed = false;
		for (size_t b = 1; b < n; ++b)
		{
			set<size_t> next = all;
			if (preds[b].empty())
				next.clear();
			for (size_t p = 0; p < preds[b].size(); ++p)
			{
				set<size_t> intersection;
				set_intersection(next.begin(), next.end(),
				                 doms[preds[b][p]].begin(), doms[preds[b][p]].end(),
				                 inserter(intersection, intersection.begin()));
				next.swap(intersection);
			}
			next.insert(b);
			if (next != doms[b])
			{
				doms[b].swap(next);
				changed = true;
			}
		}
	}
	return doms;
}

bool remove_unreachable_blocks(Function& fn)
{
	if (fn.blocks.empty())
		return false;
	map<string, size_t> index = block_indices(fn);
	set<string> reachable;
	vector<string> work;
	work.push_back(fn.blocks[0].name);
	while (!work.empty())
	{
		string name = work.back();
		work.pop_back();
		if (!reachable.insert(name).second)
			continue;
		map<string, size_t>::const_iterator it = index.find(name);
		if (it == index.end())
			continue;
		vector<string> succs;
		collect_successors(fn, it->second, succs, 0);
		for (size_t i = 0; i < succs.size(); ++i)
			work.push_back(succs[i]);
	}
	vector<Block> kept;
	for (size_t i = 0; i < fn.blocks.size(); ++i)
		if (reachable.count(fn.blocks[i].name) != 0)
			kept.push_back(fn.blocks[i]);
	const bool changed = kept.size() != fn.blocks.size();
	fn.blocks.swap(kept);
	return changed;
}

bool jump_only(const Block& block)
{
	return block.instructions.size() == 1 &&
	       block.instructions[0].kind == InstrKind::Jump;
}

bool inline_continuation_block(const string& name)
{
	return name.find("__o1inl") != string::npos &&
	       name.size() >= 6 &&
	       name.compare(name.size() - 6, 6, "__cont") == 0;
}

void rewrite_target(string& target, const map<string, string>& rewrites)
{
	set<string> seen;
	while (rewrites.find(target) != rewrites.end() && seen.insert(target).second)
		target = rewrites.find(target)->second;
}

bool rewrite_block_targets(Function& fn, const map<string, string>& rewrites)
{
	bool changed = false;
	for (size_t b = 0; b < fn.blocks.size(); ++b)
	{
		for (size_t i = 0; i < fn.blocks[b].instructions.size(); ++i)
		{
			Instruction& ins = fn.blocks[b].instructions[i];
			const string old_target = ins.target;
			const string old_false = ins.target_false;
			rewrite_target(ins.target, rewrites);
			rewrite_target(ins.target_false, rewrites);
			for (size_t c = 0; c < ins.switch_cases.size(); ++c)
				rewrite_target(ins.switch_cases[c].target, rewrites);
			changed = changed || old_target != ins.target ||
			          old_false != ins.target_false;
		}
	}
	return changed;
}

bool collapse_jump_only_blocks(Function& fn)
{
	set<string> eh_targets;
	for (size_t i = 0; i < fn.blocks.size(); ++i)
	{
		vector<string> ignored;
		collect_successors(fn, i, ignored, &eh_targets);
	}
	map<string, string> rewrites;
	for (size_t i = 1; i < fn.blocks.size(); ++i)
	{
		if (eh_targets.count(fn.blocks[i].name) == 0 && jump_only(fn.blocks[i]))
			rewrites[fn.blocks[i].name] = fn.blocks[i].instructions[0].target;
	}
	if (rewrites.empty())
		return false;
	bool changed = rewrite_block_targets(fn, rewrites);
	vector<Block> kept;
	for (size_t i = 0; i < fn.blocks.size(); ++i)
		if (rewrites.find(fn.blocks[i].name) == rewrites.end())
			kept.push_back(fn.blocks[i]);
	changed = changed || kept.size() != fn.blocks.size();
	fn.blocks.swap(kept);
	return changed;
}

map<string, int> predecessor_counts(const Function& fn)
{
	map<string, int> counts;
	for (size_t i = 0; i < fn.blocks.size(); ++i)
	{
		vector<string> succs;
		collect_successors(fn, i, succs, 0);
		for (size_t j = 0; j < succs.size(); ++j)
			++counts[succs[j]];
	}
	return counts;
}

bool merge_straight_line_blocks(Function& fn)
{
	map<string, size_t> index = block_indices(fn);
	map<string, int> preds = predecessor_counts(fn);
	bool changed = false;
	for (size_t i = 0; i < fn.blocks.size(); ++i)
	{
		Block& block = fn.blocks[i];
		if (block.instructions.empty() ||
		    block.instructions.back().kind != InstrKind::Jump)
			continue;
		bool source_has_eh = false;
		for (size_t k = 0; k < block.instructions.size(); ++k)
			source_has_eh = source_has_eh ||
			                block.instructions[k].kind == InstrKind::EhTry ||
			                block.instructions[k].kind == InstrKind::EhCleanup ||
			                block.instructions[k].kind == InstrKind::EhCatch ||
			                block.instructions[k].kind == InstrKind::EhCatchAll ||
			                block.instructions[k].kind == InstrKind::EhFilter ||
			                block.instructions[k].kind == InstrKind::EhEnd;
		if (source_has_eh)
			continue;
		const string target = block.instructions.back().target;
		map<string, size_t>::const_iterator it = index.find(target);
		if (it == index.end() || it->second == i || preds[target] != 1)
			continue;
		if (inline_continuation_block(target))
			continue;
		Block& next = fn.blocks[it->second];
		block.instructions.pop_back();
		block.instructions.insert(block.instructions.end(),
		                          next.instructions.begin(),
		                          next.instructions.end());
		fn.blocks.erase(fn.blocks.begin() + it->second);
		changed = true;
		break;
	}
	return changed;
}

bool cleanup_cfg(Function& fn)
{
	bool changed = false;
	for (;;)
	{
		bool pass = false;
		pass = remove_unreachable_blocks(fn) || pass;
		pass = collapse_jump_only_blocks(fn) || pass;
		pass = merge_straight_line_blocks(fn) || pass;
		changed = changed || pass;
		if (!pass)
			break;
	}
	return changed;
}

void count_value_use(const Value& value, map<string, int>& uses)
{
	if (value.kind == ValueKind::Temp)
		++uses[value.text];
}

map<string, int> count_temp_uses(const Function& fn)
{
	map<string, int> uses;
	for (size_t b = 0; b < fn.blocks.size(); ++b)
		for (size_t i = 0; i < fn.blocks[b].instructions.size(); ++i)
		{
			const Instruction& ins = fn.blocks[b].instructions[i];
			count_value_use(ins.a, uses);
			count_value_use(ins.b, uses);
			count_value_use(ins.c, uses);
			for (size_t a = 0; a < ins.args.size(); ++a)
				count_value_use(ins.args[a], uses);
			for (size_t c = 0; c < ins.switch_cases.size(); ++c)
				count_value_use(ins.switch_cases[c].value, uses);
		}
	return uses;
}

bool metadata_is(const Metadata& md, const string& key, const string& value)
{
	return lowir2cy86::metadata_value(md, key) == value;
}

bool direct_call_may_unwind(const Program& program, const Instruction& ins)
{
	if (ins.kind != InstrKind::Call)
		return false;
	if (metadata_is(ins.signature.metadata, "unwind", "no"))
		return false;
	if (ins.a.kind != ValueKind::Function)
		return true;
	map<string, size_t>::const_iterator it =
	    program.function_by_name.find(ins.a.text);
	if (it == program.function_by_name.end())
		return true;
	return !metadata_is(program.functions[it->second].metadata, "unwind", "no");
}

bool eh_marker(InstrKind kind)
{
	return kind == InstrKind::EhTry || kind == InstrKind::EhCleanup ||
	       kind == InstrKind::EhCatch || kind == InstrKind::EhCatchAll ||
	       kind == InstrKind::EhFilter || kind == InstrKind::EhEnd;
}

bool strip_no_unwind_eh(Function& fn, const Program& program)
{
	if (!metadata_is(fn.metadata, "unwind", "no"))
		return false;
	set<string> handlers;
	bool has_eh = false;
	for (size_t b = 0; b < fn.blocks.size(); ++b)
	{
		for (size_t i = 0; i < fn.blocks[b].instructions.size(); ++i)
		{
			const Instruction& ins = fn.blocks[b].instructions[i];
			if ((ins.kind == InstrKind::EhTry || ins.kind == InstrKind::EhCleanup) &&
			    !ins.target.empty())
				handlers.insert(ins.target);
			has_eh = has_eh || eh_marker(ins.kind);
		}
	}
	if (!has_eh)
		return false;
	for (size_t b = 0; b < fn.blocks.size(); ++b)
	{
		if (handlers.count(fn.blocks[b].name) != 0)
			continue;
		for (size_t i = 0; i < fn.blocks[b].instructions.size(); ++i)
		{
			const Instruction& ins = fn.blocks[b].instructions[i];
			if (ins.kind == InstrKind::Throw || ins.kind == InstrKind::Resume ||
			    direct_call_may_unwind(program, ins))
				return false;
		}
	}
	for (size_t b = 0; b < fn.blocks.size(); ++b)
	{
		vector<Instruction> kept;
		for (size_t i = 0; i < fn.blocks[b].instructions.size(); ++i)
			if (!eh_marker(fn.blocks[b].instructions[i].kind))
				kept.push_back(fn.blocks[b].instructions[i]);
		fn.blocks[b].instructions.swap(kept);
	}
	return true;
}

bool direct_function_readnone_nothrow(const Program& program, const string& name)
{
	map<string, size_t>::const_iterator it = program.function_by_name.find(name);
	if (it == program.function_by_name.end())
		return false;
	const Function& fn = program.functions[it->second];
	if (metadata_is(fn.metadata, "effects", "readnone") &&
	    metadata_is(fn.metadata, "unwind", "no") &&
	    !metadata_is(fn.metadata, "return", "noreturn"))
		return true;
	if (fn.declaration)
		return false;
	for (size_t b = 0; b < fn.blocks.size(); ++b)
		for (size_t i = 0; i < fn.blocks[b].instructions.size(); ++i)
		{
			const Instruction& ins = fn.blocks[b].instructions[i];
			if (ins.kind == InstrKind::Call || ins.kind == InstrKind::Store ||
			    ins.kind == InstrKind::AtomicStore ||
			    ins.kind == InstrKind::AtomicExchange ||
			    ins.kind == InstrKind::AtomicCompareExchange ||
			    ins.kind == InstrKind::AtomicAddFetch ||
			    ins.kind == InstrKind::Throw || ins.kind == InstrKind::Resume ||
			    ins.kind == InstrKind::EhTry || ins.kind == InstrKind::EhCleanup)
				return false;
		}
	return true;
}

bool removable_unused_call(const Program& program, const Instruction& ins)
{
	if (ins.kind != InstrKind::Call || !ins.has_dest)
		return false;
	if (ins.a.kind == ValueKind::Function)
		return direct_function_readnone_nothrow(program, ins.a.text);
	return metadata_is(ins.signature.metadata, "effects", "readnone") &&
	       metadata_is(ins.signature.metadata, "unwind", "no") &&
	       !metadata_is(ins.signature.metadata, "return", "noreturn");
}

bool pure_unused_instruction(const Program& program, const Instruction& ins)
{
	if (!ins.has_dest)
		return false;
	if (removable_unused_call(program, ins))
		return true;
	if (ins.kind == InstrKind::Const || ins.kind == InstrKind::Copy ||
	    ins.kind == InstrKind::Addr || ins.kind == InstrKind::Index ||
	    ins.kind == InstrKind::Unary || ins.kind == InstrKind::Binary ||
	    ins.kind == InstrKind::Cmp || ins.kind == InstrKind::Convert)
		return true;
	if (ins.kind == InstrKind::Load && ins.a.kind == ValueKind::Slot)
		return true;
	return false;
}

bool remove_unused_temps(Function& fn, const Program& program)
{
	bool changed = false;
	for (;;)
	{
		map<string, int> uses = count_temp_uses(fn);
		bool pass = false;
		for (size_t b = 0; b < fn.blocks.size(); ++b)
		{
			vector<Instruction> kept;
			for (size_t i = 0; i < fn.blocks[b].instructions.size(); ++i)
			{
				const Instruction& ins = fn.blocks[b].instructions[i];
				if (ins.has_dest && uses[ins.dest] == 0 &&
				    pure_unused_instruction(program, ins))
				{
					pass = true;
					continue;
				}
				kept.push_back(ins);
			}
			fn.blocks[b].instructions.swap(kept);
		}
		changed = changed || pass;
		if (!pass)
			break;
	}
	return changed;
}

void collect_slot_uses(const Function& fn,
                       map<string, int>& loads,
                       map<string, int>& stores,
                       set<string>& escapes)
{
	for (size_t b = 0; b < fn.blocks.size(); ++b)
		for (size_t i = 0; i < fn.blocks[b].instructions.size(); ++i)
		{
			const Instruction& ins = fn.blocks[b].instructions[i];
			if (ins.kind == InstrKind::Load && ins.a.kind == ValueKind::Slot)
				++loads[ins.a.text];
			else if (ins.kind == InstrKind::Store && ins.b.kind == ValueKind::Slot)
				++stores[ins.b.text];
			else
			{
				if (ins.a.kind == ValueKind::Slot) escapes.insert(ins.a.text);
				if (ins.b.kind == ValueKind::Slot) escapes.insert(ins.b.text);
				if (ins.c.kind == ValueKind::Slot) escapes.insert(ins.c.text);
				for (size_t a = 0; a < ins.args.size(); ++a)
					if (ins.args[a].kind == ValueKind::Slot)
						escapes.insert(ins.args[a].text);
			}
		}
}

bool remove_dead_slot_traffic(Function& fn)
{
	map<string, int> loads;
	map<string, int> stores;
	set<string> escapes;
	collect_slot_uses(fn, loads, stores, escapes);
	set<string> dead;
	for (size_t i = 0; i < fn.slots.size(); ++i)
	{
		const string& slot = fn.slots[i].name;
		if (escapes.count(slot) == 0 && loads[slot] == 0 && stores[slot] != 0)
			dead.insert(slot);
	}
	if (dead.empty())
		return false;
	for (size_t b = 0; b < fn.blocks.size(); ++b)
	{
		vector<Instruction> kept;
		for (size_t i = 0; i < fn.blocks[b].instructions.size(); ++i)
		{
			const Instruction& ins = fn.blocks[b].instructions[i];
			if (ins.kind == InstrKind::Store && ins.b.kind == ValueKind::Slot &&
			    dead.count(ins.b.text) != 0)
				continue;
			kept.push_back(ins);
		}
		fn.blocks[b].instructions.swap(kept);
	}
	vector<Slot> kept_slots;
	for (size_t i = 0; i < fn.slots.size(); ++i)
		if (dead.count(fn.slots[i].name) == 0)
			kept_slots.push_back(fn.slots[i]);
	fn.slots.swap(kept_slots);
	return true;
}

struct SlotStore
{
	Value value;
	Type type;
	size_t block;
	size_t index;
	int count;

	SlotStore() : block(0), index(0), count(0) {}
};

struct SlotLoad
{
	string dest;
	size_t block;
	size_t index;
};

void replace_value_from_map(Value& value, const map<string, Value>& replacements)
{
	set<string> seen;
	while (value.kind == ValueKind::Temp)
	{
		map<string, Value>::const_iterator it = replacements.find(value.text);
		if (it == replacements.end() || !seen.insert(value.text).second)
			return;
		value = it->second;
	}
}

void replace_instruction_temps(Instruction& ins,
                               const map<string, Value>& replacements)
{
	replace_value_from_map(ins.a, replacements);
	replace_value_from_map(ins.b, replacements);
	replace_value_from_map(ins.c, replacements);
	for (size_t i = 0; i < ins.args.size(); ++i)
		replace_value_from_map(ins.args[i], replacements);
	for (size_t i = 0; i < ins.switch_cases.size(); ++i)
		replace_value_from_map(ins.switch_cases[i].value, replacements);
}

bool promote_single_store_slots(Function& fn,
                                const vector<set<size_t> >& doms,
                                bool inline_artifacts_only)
{
	map<string, SlotStore> stores;
	map<string, vector<SlotLoad> > loads;
	set<string> escapes;
	for (size_t b = 0; b < fn.blocks.size(); ++b)
	{
		for (size_t i = 0; i < fn.blocks[b].instructions.size(); ++i)
		{
			const Instruction& ins = fn.blocks[b].instructions[i];
			if (ins.kind == InstrKind::Load && ins.has_dest &&
			    ins.a.kind == ValueKind::Slot)
			{
				SlotLoad load;
				load.dest = ins.dest;
				load.block = b;
				load.index = i;
				loads[ins.a.text].push_back(load);
			}
			else if (ins.kind == InstrKind::Store && ins.b.kind == ValueKind::Slot)
			{
				SlotStore& store = stores[ins.b.text];
				store.value = ins.a;
				store.type = ins.type;
				store.block = b;
				store.index = i;
				++store.count;
			}
			else
			{
				if (ins.a.kind == ValueKind::Slot) escapes.insert(ins.a.text);
				if (ins.b.kind == ValueKind::Slot) escapes.insert(ins.b.text);
				if (ins.c.kind == ValueKind::Slot) escapes.insert(ins.c.text);
				for (size_t a = 0; a < ins.args.size(); ++a)
					if (ins.args[a].kind == ValueKind::Slot)
						escapes.insert(ins.args[a].text);
			}
		}
	}

	set<string> promoted_slots;
	map<string, Value> replacements;
	for (size_t s = 0; s < fn.slots.size(); ++s)
	{
		const Slot& slot = fn.slots[s];
		if (inline_artifacts_only &&
		    slot.name.find("__o1inl") == string::npos)
			continue;
		if (escapes.count(slot.name) != 0)
			continue;
		map<string, SlotStore>::const_iterator st = stores.find(slot.name);
		map<string, vector<SlotLoad> >::const_iterator ld = loads.find(slot.name);
		if (st == stores.end() || st->second.count != 1 ||
		    ld == loads.end() || ld->second.empty())
			continue;
		if (lowir2cy86::is_obj_type(slot.type))
			continue;
		if (slot.type.text == "ptr" && st->second.value.kind == ValueKind::Literal)
			continue;
		bool all_dominated = true;
		for (size_t i = 0; i < ld->second.size(); ++i)
		{
			const SlotLoad& load = ld->second[i];
			if (st->second.block == load.block)
			{
				if (st->second.index >= load.index)
				{
					all_dominated = false;
					break;
				}
				continue;
			}
			if (!dominates(doms, st->second.block, load.block))
			{
				all_dominated = false;
				break;
			}
		}
		if (!all_dominated)
			continue;
		promoted_slots.insert(slot.name);
		for (size_t i = 0; i < ld->second.size(); ++i)
			replacements[ld->second[i].dest] = st->second.value;
	}

	if (promoted_slots.empty())
		return false;

	for (size_t b = 0; b < fn.blocks.size(); ++b)
	{
		vector<Instruction> kept;
		for (size_t i = 0; i < fn.blocks[b].instructions.size(); ++i)
		{
			Instruction ins = fn.blocks[b].instructions[i];
			if (ins.kind == InstrKind::Load && ins.a.kind == ValueKind::Slot &&
			    promoted_slots.count(ins.a.text) != 0)
				continue;
			if (ins.kind == InstrKind::Store && ins.b.kind == ValueKind::Slot &&
			    promoted_slots.count(ins.b.text) != 0)
				continue;
			replace_instruction_temps(ins, replacements);
			kept.push_back(ins);
		}
		fn.blocks[b].instructions.swap(kept);
	}
	vector<Slot> kept_slots;
	for (size_t i = 0; i < fn.slots.size(); ++i)
		if (promoted_slots.count(fn.slots[i].name) == 0)
			kept_slots.push_back(fn.slots[i]);
	fn.slots.swap(kept_slots);
	return true;
}

bool function_has_inline_artifact(const Function& fn)
{
	for (size_t i = 0; i < fn.slots.size(); ++i)
		if (fn.slots[i].name.find("__o1inl") != string::npos)
			return true;
	for (size_t b = 0; b < fn.blocks.size(); ++b)
	{
		if (fn.blocks[b].name.find("__o1inl") != string::npos)
			return true;
		for (size_t i = 0; i < fn.blocks[b].instructions.size(); ++i)
			if (fn.blocks[b].instructions[i].has_dest &&
			    fn.blocks[b].instructions[i].dest.find("__o1inl") != string::npos)
				return true;
	}
	return false;
}

bool simplify_function(Function& fn, Program& program)
{
	bool changed = false;
	map<string, Fact> facts;
	map<string, vector<ExprFact> > exprs;
	map<string, const Instruction*> defs;
	bool has_eh = false;
	for (size_t b = 0; b < fn.blocks.size(); ++b)
		for (size_t i = 0; i < fn.blocks[b].instructions.size(); ++i)
			has_eh = has_eh ||
			         fn.blocks[b].instructions[i].kind == InstrKind::EhTry ||
			         fn.blocks[b].instructions[i].kind == InstrKind::EhCleanup ||
			         fn.blocks[b].instructions[i].kind == InstrKind::EhCatch ||
			         fn.blocks[b].instructions[i].kind == InstrKind::EhCatchAll ||
			         fn.blocks[b].instructions[i].kind == InstrKind::EhFilter ||
			         fn.blocks[b].instructions[i].kind == InstrKind::EhEnd;
	vector<set<size_t> > doms = compute_dominators(fn);
	set<string> storage_temps = storage_temp_uses(fn);
	for (size_t b = 0; b < fn.blocks.size(); ++b)
	{
		if (has_eh && b != 0)
		{
			facts.clear();
			exprs.clear();
		}
		for (size_t i = 0; i < fn.blocks[b].instructions.size(); ++i)
			changed = simplify_instruction(fn, program, fn.blocks[b].instructions[i],
			                               b, doms, storage_temps, facts, exprs, defs) ||
			          changed;
	}
	rebuild_program(program);
	const bool broad_slot_cleanup =
	    function_has_inline_artifact(fn) || metadata_is(fn.metadata, "role", "entry");
	changed = promote_single_store_slots(fn, doms, !broad_slot_cleanup) || changed;
	rebuild_program(program);
	changed = remove_unused_temps(fn, program) || changed;
	rebuild_program(program);
	changed = remove_dead_slot_traffic(fn) || changed;
	rebuild_program(program);
	changed = strip_no_unwind_eh(fn, program) || changed;
	rebuild_program(program);
	changed = cleanup_cfg(fn) || changed;
	return changed;
}

bool add_prefer_local_binding(Function& fn)
{
	if (lowir2cy86::metadata_value(fn.metadata, "prefer_local") != "yes" ||
	    !lowir2cy86::metadata_value(fn.metadata, "binding").empty())
		return false;
	Metadata out;
	bool inserted = false;
	for (size_t i = 0; i < fn.metadata.size(); ++i)
	{
		if (!inserted && fn.metadata[i].key == "prefer_local")
		{
			MetadataItem item;
			item.key = "binding";
			item.value = "strong";
			out.push_back(item);
			inserted = true;
		}
		out.push_back(fn.metadata[i]);
	}
	fn.metadata.swap(out);
	return true;
}

bool simplify_o1_once(Program& program)
{
	rebuild_program(program);
	bool changed = false;
	for (size_t i = 0; i < program.functions.size(); ++i)
	{
		changed = add_prefer_local_binding(program.functions[i]) || changed;
		if (!program.functions[i].declaration)
			changed = simplify_function(program.functions[i], program) || changed;
	}
	rebuild_program(program);
	changed = inline_o1_once(program) || changed;
	rebuild_program(program);
	return changed;
}

bool run_o1_fixedpoint(Program& program)
{
	bool changed = false;
	for (int pass = 0; pass < 20; ++pass)
	{
		if (!simplify_o1_once(program))
			break;
		changed = true;
	}
	return changed;
}

}  // namespace

Program optimize_program(Program program, int level)
{
	if (level < 0 || level > 2)
		throw runtime_error("unsupported optimization level");
	rebuild_program(program);
	const Program original = program;
	if (level == 0)
		return program;
	run_o1_fixedpoint(program);
	if (level == 1)
		return program;
	for (int pass = 0; pass < 20; ++pass)
	{
		bool changed = promote_o2_slots_once(program);
		changed = run_o1_fixedpoint(program) || changed;
		if (!changed)
			break;
	}
	canonicalize_optimized_program(program, original);
	return program;
}

}  // namespace lowiropt
