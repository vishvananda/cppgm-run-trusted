#include "lowir2native.h"

#include "lowir2cy86.h"

#include <algorithm>
#include <map>
#include <set>
#include <sstream>
#include <stdexcept>
#include <string>
#include <vector>

using namespace std;

namespace lowir2native {

string effective_target(const Options& options);
void write_text_file(const string& path, const string& text);
void write_native_file(const lowir2cy86::Program& program,
                       const Options& options);
string storage_suffix(const lowir2cy86::Type& type);
string reg_for_index(size_t index);
string abi_gpr(size_t index);
bool metadata_is(const lowir2cy86::Metadata& md,
                 const string& key,
                 const string& value);
string value_text(const lowir2cy86::Value& value);
string mem_for_offset(size_t offset);

namespace {

class MirDumper
{
public:
	MirDumper(const lowir2cy86::Program& program, const string& target)
		: program_(program), target_(target)
	{
	}

	string dump()
	{
		out_ << "machine_ir x86_64 " << target_ << "\n\n";
		dump_startup();
		dump_globals();
		dump_functions();
		return out_.str();
	}

private:
	const lowir2cy86::Program& program_;
	string target_;
	ostringstream out_;
	vector<string> temp_names_;
	vector<string> temp_regs_;
	map<string, string> fixed_temp_regs_;
	vector<string> xmm_names_;
	vector<string> xmm_regs_;
	map<string, int> use_counts_;
	map<string, const lowir2cy86::Instruction*> definitions_;
	set<string> direct_branch_cmp_;
	set<string> inline_atomic_expected_addrs_;
	set<string> used_preserves_;
	string preferred_load_ptr_;
	string preferred_load_reg_;
	string preferred_literal_reg_;
	bool preferred_load_sets_literal_;
	bool prefer_r8_stack_load_;
	bool fixed_load_dest_;
	bool fixed_const_dest_;
	bool prefer_r8_literal_;

	void dump_startup()
	{
		if (program_.entry_function.empty())
			return;
		out_ << "startup\n";
		if (!program_.init_function.empty())
			out_ << "    call " << program_.init_function << "\n";
		out_ << "    call " << program_.entry_function << "\n";
		if (!program_.fini_function.empty())
		{
			out_ << "    mov r12, rax\n";
			out_ << "    call " << program_.fini_function << "\n";
			out_ << "    mov rdi, r12\n";
		}
		else
			out_ << "    mov rdi, rax\n";
		out_ << "    exit\n\n";
	}

	void dump_globals()
	{
		for (size_t i = 0; i < program_.globals.size(); ++i)
		{
			const lowir2cy86::Global& g = program_.globals[i];
			if (g.declaration)
				continue;
			out_ << "global " << g.name;
			if (metadata_is(g.metadata, "storage", "readonly"))
				out_ << " readonly";
			if (metadata_is(g.metadata, "storage", "thread_local"))
				out_ << " thread_local";
			out_ << "\n";
			if (g.has_type)
			{
				out_ << "  storage scalar " << g.type.text << "\n";
				if (g.init.kind == "zero")
					out_ << "  init " << g.type.text << " 0\n";
				else if (g.init.kind == "addr")
					out_ << "  init ptr addr " << g.init.target
					     << addend_text(g.init.has_addend, g.init.addend) << "\n";
				else
					out_ << "  init " << g.type.text << " " << g.init.literal << "\n";
			}
			else
			{
				out_ << "  storage data\n";
				for (size_t j = 0; j < g.data.size(); ++j)
					dump_global_item(g.data[j]);
			}
			out_ << "\n";
		}
	}

	string addend_text(bool has, int addend) const
	{
		if (!has)
			return "";
		return addend >= 0 ? " + " + to_string(addend)
		                   : " - " + to_string(-addend);
	}

	void dump_global_item(const lowir2cy86::GlobalDataItem& item)
	{
		if (item.kind == "zero")
			out_ << "  item zero " << item.zero_bytes << "\n";
		else if (item.kind == "addr")
			out_ << "  item ptr addr " << item.target
			     << addend_text(item.has_addend, item.addend) << "\n";
		else
			out_ << "  item " << item.type.text << " " << item.literal << "\n";
	}

	void dump_functions()
	{
		for (size_t i = 0; i < program_.functions.size(); ++i)
		{
			const lowir2cy86::Function& fn = program_.functions[i];
			if (fn.declaration)
				continue;
			dump_function(fn);
			if (i + 1 != program_.functions.size())
				out_ << "\n";
		}
	}

	void dump_function(const lowir2cy86::Function& fn)
	{
		analyze_function(fn);
		const vector<string> preserves = frame_preserves(fn);
		reset_function_state();
		out_ << "function " << fn.name << "\n";
		dump_abi(fn);
		dump_frame(fn, preserves);
		out_ << "\n";
		for (size_t i = 0; i < fn.blocks.size(); ++i)
		{
			out_ << "  block " << fn.blocks[i].name << "\n";
			for (size_t j = 0; j < fn.blocks[i].instructions.size(); ++j)
				dump_instruction(fn, fn.blocks[i].instructions[j]);
			if (i + 1 != fn.blocks.size())
				out_ << "\n";
		}
	}

	void reset_function_state()
	{
		temp_names_.clear();
		temp_regs_.clear();
		fixed_temp_regs_.clear();
		xmm_names_.clear();
		xmm_regs_.clear();
		used_preserves_.clear();
		preferred_load_ptr_.clear();
		preferred_load_reg_.clear();
		preferred_literal_reg_.clear();
		preferred_load_sets_literal_ = false;
		prefer_r8_stack_load_ = false;
		fixed_load_dest_ = false;
		fixed_const_dest_ = false;
		prefer_r8_literal_ = false;
	}

	void analyze_function(const lowir2cy86::Function& fn)
	{
		use_counts_.clear();
		definitions_.clear();
		direct_branch_cmp_.clear();
		inline_atomic_expected_addrs_.clear();
		for (size_t i = 0; i < fn.blocks.size(); ++i)
		{
			for (size_t j = 0; j < fn.blocks[i].instructions.size(); ++j)
			{
				const lowir2cy86::Instruction& ins = fn.blocks[i].instructions[j];
				if (ins.has_dest)
					definitions_[ins.dest] = &ins;
				count_uses(ins);
			}
		}
		for (size_t i = 0; i < fn.blocks.size(); ++i)
		{
			for (size_t j = 0; j < fn.blocks[i].instructions.size(); ++j)
			{
				const lowir2cy86::Instruction& ins = fn.blocks[i].instructions[j];
				if (ins.kind == lowir2cy86::InstrKind::AtomicCompareExchange &&
				    ins.b.kind == lowir2cy86::ValueKind::Temp &&
				    use_counts_[ins.b.text] == 1)
				{
					map<string, const lowir2cy86::Instruction*>::const_iterator ait =
					    definitions_.find(ins.b.text);
					if (ait != definitions_.end() &&
					    ait->second->kind == lowir2cy86::InstrKind::Addr)
						inline_atomic_expected_addrs_.insert(ins.b.text);
				}
				if (ins.kind != lowir2cy86::InstrKind::Branch ||
				    ins.a.kind != lowir2cy86::ValueKind::Temp)
					continue;
				map<string, const lowir2cy86::Instruction*>::const_iterator it =
				    definitions_.find(ins.a.text);
				if (it != definitions_.end() &&
				    it->second->kind == lowir2cy86::InstrKind::Cmp &&
				    use_counts_[ins.a.text] == 1)
					direct_branch_cmp_.insert(ins.a.text);
			}
		}
	}

	void count_uses(const lowir2cy86::Instruction& ins)
	{
		count_use(ins.a);
		count_use(ins.b);
		count_use(ins.c);
		for (size_t i = 0; i < ins.args.size(); ++i)
			count_use(ins.args[i]);
		for (size_t i = 0; i < ins.switch_cases.size(); ++i)
			count_use(ins.switch_cases[i].value);
	}

	void count_use(const lowir2cy86::Value& value)
	{
		if (value.kind == lowir2cy86::ValueKind::Temp)
			++use_counts_[value.text];
	}

	void dump_abi(const lowir2cy86::Function& fn)
	{
		out_ << "  abi\n";
		for (size_t i = 0; i < fn.params.size(); ++i)
			out_ << "    param " << fn.params[i].name << " -> " << abi_gpr(i)
			     << " : " << fn.params[i].type.text << "\n";
		out_ << "    return " << storage_suffix(fn.ret) << " -> "
		     << (lowir2cy86::is_void_type(fn.ret) ? "void" : "rax") << "\n";
	}

	void dump_frame(const lowir2cy86::Function& fn,
	                const vector<string>& preserves)
	{
		const bool float_frame = function_uses_float(fn);
		const size_t saved_reg_bytes = preserves.size() * 8;
		out_ << "  frame\n";
		out_ << "    stack_size "
		     << max(align_to(raw_stack_size(fn) + saved_reg_bytes, 16),
		            float_frame ? static_cast<size_t>(48) : static_cast<size_t>(0))
		     << "\n";
		out_ << "    scratch_bytes "
		     << (float_frame || fn.needs_convert_scratch ? 48 : 0) << "\n";
		if (!preserves.empty())
		{
			out_ << "    preserve";
			for (size_t i = 0; i < preserves.size(); ++i)
				out_ << " " << preserves[i];
			out_ << "\n";
		}
		for (size_t i = 0; i < fn.slots.size(); ++i)
			out_ << "    slot " << fn.slots[i].name << " -> "
			     << mem_for_offset(fn.slots[i].offset) << " : "
			     << fn.slots[i].type.text << "\n";
	}

	bool function_uses_float(const lowir2cy86::Function& fn) const
	{
		for (size_t i = 0; i < fn.blocks.size(); ++i)
		{
			for (size_t j = 0; j < fn.blocks[i].instructions.size(); ++j)
			{
				const lowir2cy86::Instruction& ins = fn.blocks[i].instructions[j];
				if (lowir2cy86::is_float_type(ins.type) ||
				    lowir2cy86::is_float_type(ins.src_type))
					return true;
			}
		}
		return false;
	}

	vector<string> frame_preserves(const lowir2cy86::Function& fn)
	{
		reset_function_state();
		for (size_t i = 0; i < fn.blocks.size(); ++i)
		{
			for (size_t j = 0; j < fn.blocks[i].instructions.size(); ++j)
				simulate_instruction(fn, fn.blocks[i].instructions[j]);
		}
		return ordered_preserves();
	}

	vector<string> ordered_preserves() const
	{
		static const char* const order[] = {"rbx", "r12", "r13", "r14", "r15"};
		vector<string> regs;
		for (size_t i = 0; i < sizeof(order) / sizeof(order[0]); ++i)
		{
			if (used_preserves_.find(order[i]) != used_preserves_.end())
				regs.push_back(order[i]);
		}
		return regs;
	}

	size_t raw_stack_size(const lowir2cy86::Function& fn) const
	{
		size_t bytes = 0;
		for (size_t i = 0; i < fn.slots.size(); ++i)
		{
			const size_t end = fn.slots[i].offset;
			if (end > bytes)
				bytes = end;
		}
		return bytes;
	}

	size_t align_to(size_t value, size_t alignment) const
	{
		if (alignment == 0)
			return value;
		const size_t rem = value % alignment;
		return rem == 0 ? value : value + alignment - rem;
	}

	string temp_reg(const string& name)
	{
		for (size_t i = 0; i < temp_names_.size(); ++i)
		{
			if (temp_names_[i] == name)
			{
				note_temp_reg(temp_regs_[i]);
				return temp_regs_[i];
			}
		}
		temp_names_.push_back(name);
		temp_regs_.push_back(reg_for_index(temp_regs_.size()));
		note_temp_reg(temp_regs_.back());
		return temp_regs_.back();
	}

	void note_temp_reg(const string& reg)
	{
		if (reg == "rbx" || reg == "r12" || reg == "r13" ||
		    reg == "r14" || reg == "r15")
			used_preserves_.insert(reg);
	}

	string xmm_reg(const string& name)
	{
		for (size_t i = 0; i < xmm_names_.size(); ++i)
		{
			if (xmm_names_[i] == name)
				return xmm_regs_[i];
		}
		static const char* const regs[] = {"xmm0", "xmm1", "xmm2", "xmm3"};
		xmm_names_.push_back(name);
		xmm_regs_.push_back(regs[xmm_regs_.size() %
		                         (sizeof(regs) / sizeof(regs[0]))]);
		return xmm_regs_.back();
	}

	void remember_xmm_reg(const string& name, const string& reg)
	{
		for (size_t i = 0; i < xmm_names_.size(); ++i)
		{
			if (xmm_names_[i] == name)
			{
				xmm_regs_[i] = reg;
				return;
			}
		}
		xmm_names_.push_back(name);
		xmm_regs_.push_back(reg);
	}

	lowir2cy86::Type lookup_type(const lowir2cy86::Function& fn,
	                             const lowir2cy86::Value& value) const
	{
		if (value.kind == lowir2cy86::ValueKind::Temp)
		{
			map<string, lowir2cy86::Type>::const_iterator pit =
			    fn.param_types.find(value.text);
			if (pit != fn.param_types.end())
				return pit->second;
			map<string, lowir2cy86::Type>::const_iterator it =
			    fn.temp_types.find(value.text);
			if (it != fn.temp_types.end())
				return it->second;
		}
		if (value.kind == lowir2cy86::ValueKind::Slot)
		{
			map<string, lowir2cy86::Type>::const_iterator it =
			    fn.slot_types.find(value.text);
			if (it != fn.slot_types.end())
				return it->second;
		}
		return lowir2cy86::Type();
	}

	string float_value(const lowir2cy86::Function& fn,
	                   const lowir2cy86::Value& value)
	{
		if (value.kind == lowir2cy86::ValueKind::Temp)
			return xmm_reg(value.text);
		return value_reg(fn, value);
	}

	string f80_home(const lowir2cy86::Function& fn, const string& name) const
	{
		map<string, size_t>::const_iterator it = fn.temp_offsets.find(name);
		if (it != fn.temp_offsets.end())
			return mem_for_offset(it->second);
		return name;
	}

	string f80_value(const lowir2cy86::Function& fn,
	                 const lowir2cy86::Value& value) const
	{
		if (value.kind == lowir2cy86::ValueKind::Temp)
			return f80_home(fn, value.text);
		if (value.kind == lowir2cy86::ValueKind::Slot)
		{
			map<string, size_t>::const_iterator it = fn.slot_offsets.find(value.text);
			if (it != fn.slot_offsets.end())
				return mem_for_offset(it->second);
		}
		return value.text;
	}

	string value_reg(const lowir2cy86::Function& fn, const lowir2cy86::Value& value)
	{
		if (value.kind == lowir2cy86::ValueKind::Temp)
		{
			for (size_t i = 0; i < fn.params.size(); ++i)
			{
				if (fn.params[i].name == value.text)
					return abi_gpr(i);
			}
			map<string, string>::const_iterator fit = fixed_temp_regs_.find(value.text);
			if (fit != fixed_temp_regs_.end())
				return fit->second;
			return temp_reg(value.text);
		}
		if (value.kind == lowir2cy86::ValueKind::Literal)
			return value.text;
		if (value.kind == lowir2cy86::ValueKind::Global ||
		    value.kind == lowir2cy86::ValueKind::Function)
			return value.text;
		if (value.kind == lowir2cy86::ValueKind::Slot)
		{
			map<string, size_t>::const_iterator it = fn.slot_offsets.find(value.text);
			if (it != fn.slot_offsets.end())
				return mem_for_offset(it->second);
		}
		return value_text(value);
	}

	void dump_instruction(const lowir2cy86::Function& fn,
	                      const lowir2cy86::Instruction& ins)
	{
		switch (ins.kind)
		{
		case lowir2cy86::InstrKind::Const:
			dump_const(ins);
			break;
		case lowir2cy86::InstrKind::Copy:
			dump_copy(fn, ins);
			break;
		case lowir2cy86::InstrKind::Addr:
			if (inline_atomic_expected_addrs_.find(ins.dest) !=
			    inline_atomic_expected_addrs_.end())
				break;
			dump_addr(fn, ins);
			break;
		case lowir2cy86::InstrKind::Load:
		case lowir2cy86::InstrKind::AtomicLoad:
			dump_load(fn, ins);
			break;
		case lowir2cy86::InstrKind::Store:
			dump_store(fn, ins);
			break;
		case lowir2cy86::InstrKind::AtomicStore:
			dump_atomic_store(fn, ins);
			break;
		case lowir2cy86::InstrKind::Index:
			dump_index(fn, ins);
			break;
		case lowir2cy86::InstrKind::CopyObj:
			out_ << "    copy_bytes " << ins.span.bytes << "x" << ins.span.align
			     << ", " << value_reg(fn, ins.b) << ", "
			     << value_reg(fn, ins.a) << "\n";
			break;
		case lowir2cy86::InstrKind::ZeroInit:
			out_ << "    zero_bytes " << ins.span.bytes << "x" << ins.span.align
			     << ", " << value_reg(fn, ins.a) << "\n";
			break;
		case lowir2cy86::InstrKind::Unary:
		case lowir2cy86::InstrKind::Binary:
		case lowir2cy86::InstrKind::Cmp:
		case lowir2cy86::InstrKind::Convert:
			if (ins.kind != lowir2cy86::InstrKind::Cmp ||
			    direct_branch_cmp_.find(ins.dest) == direct_branch_cmp_.end())
				dump_scalar(fn, ins);
			break;
		case lowir2cy86::InstrKind::Call:
			dump_call(fn, ins);
			break;
		case lowir2cy86::InstrKind::AtomicExchange:
		case lowir2cy86::InstrKind::AtomicCompareExchange:
		case lowir2cy86::InstrKind::AtomicAddFetch:
			dump_atomic(fn, ins);
			break;
		case lowir2cy86::InstrKind::AtomicThreadFence:
		case lowir2cy86::InstrKind::AtomicSignalFence:
			out_ << "    mfence\n";
			break;
		case lowir2cy86::InstrKind::Jump:
			out_ << "    jmp " << ins.target << "\n";
			break;
		case lowir2cy86::InstrKind::Branch:
			dump_branch(fn, ins);
			break;
		case lowir2cy86::InstrKind::Switch:
			dump_switch(fn, ins);
			break;
		case lowir2cy86::InstrKind::Return:
			dump_return(fn, ins);
			break;
		default:
			out_ << "    ; unsupported\n";
			break;
		}
	}

	void simulate_instruction(const lowir2cy86::Function& fn,
	                          const lowir2cy86::Instruction& ins)
	{
		switch (ins.kind)
		{
		case lowir2cy86::InstrKind::Const:
			if (lowir2cy86::is_float_type(ins.type) &&
			    !lowir2cy86::is_f80_type(ins.type))
				xmm_reg(ins.dest);
			else
				remember_const_dest(ins.dest, const_dest_reg(ins));
			break;
		case lowir2cy86::InstrKind::Copy:
			if (lowir2cy86::is_float_type(ins.type) &&
			    !lowir2cy86::is_f80_type(ins.type))
			{
				float_value(fn, ins.a);
				xmm_reg(ins.dest);
			}
			else
			{
				temp_reg(ins.dest);
				value_reg(fn, ins.a);
			}
			break;
		case lowir2cy86::InstrKind::Addr:
			if (inline_atomic_expected_addrs_.find(ins.dest) !=
			    inline_atomic_expected_addrs_.end())
				break;
			temp_reg(ins.dest);
			value_reg(fn, ins.a);
			break;
		case lowir2cy86::InstrKind::Load:
		case lowir2cy86::InstrKind::AtomicLoad:
		{
			const string dst = load_dest_reg(fn, ins);
			load_source(fn, ins.a);
			remember_load_dest(ins.dest, dst);
			break;
		}
		case lowir2cy86::InstrKind::Store:
			value_reg(fn, ins.a);
			store_dest(fn, ins.b);
			remember_store_literal(fn, ins.a);
			break;
		case lowir2cy86::InstrKind::AtomicStore:
			remember_store_reload(fn, ins.b, ins.a);
			break;
		case lowir2cy86::InstrKind::Index:
			temp_reg(ins.dest);
			value_reg(fn, ins.a);
			if (ins.b.kind != lowir2cy86::ValueKind::Literal)
				value_reg(fn, ins.b);
			break;
		case lowir2cy86::InstrKind::CopyObj:
			value_reg(fn, ins.b);
			value_reg(fn, ins.a);
			break;
		case lowir2cy86::InstrKind::ZeroInit:
			value_reg(fn, ins.a);
			break;
		case lowir2cy86::InstrKind::Unary:
			temp_reg(ins.dest);
			value_reg(fn, ins.a);
			break;
		case lowir2cy86::InstrKind::Binary:
			simulate_binary(fn, ins);
			break;
		case lowir2cy86::InstrKind::Cmp:
			if (direct_branch_cmp_.find(ins.dest) == direct_branch_cmp_.end())
				simulate_cmp(fn, ins);
			break;
		case lowir2cy86::InstrKind::Convert:
		{
			const string dst = convert_dest(fn, ins);
			convert_source(fn, ins);
			remember_convert_dest(ins, dst);
			break;
		}
		case lowir2cy86::InstrKind::Call:
			for (size_t i = 0; i < ins.args.size() && i < 6; ++i)
				value_reg(fn, ins.args[i]);
			if (ins.a.kind != lowir2cy86::ValueKind::Function)
				value_reg(fn, ins.a);
			if (ins.has_dest && !lowir2cy86::is_void_type(ins.type))
				temp_reg(ins.dest);
			break;
		case lowir2cy86::InstrKind::AtomicExchange:
		case lowir2cy86::InstrKind::AtomicCompareExchange:
		case lowir2cy86::InstrKind::AtomicAddFetch:
			simulate_atomic(fn, ins);
			break;
		case lowir2cy86::InstrKind::Branch:
			if (ins.a.kind == lowir2cy86::ValueKind::Temp &&
			    direct_branch_cmp_.find(ins.a.text) != direct_branch_cmp_.end())
			{
				const lowir2cy86::Instruction& cmp = *definitions_[ins.a.text];
				value_reg(fn, cmp.a);
				if (cmp.b.kind != lowir2cy86::ValueKind::Literal)
					value_reg(fn, cmp.b);
			}
			else
				value_reg(fn, ins.a);
			break;
		case lowir2cy86::InstrKind::Switch:
			value_reg(fn, ins.a);
			for (size_t i = 0; i < ins.switch_cases.size(); ++i)
				value_reg(fn, ins.switch_cases[i].value);
			break;
		case lowir2cy86::InstrKind::Return:
			value_reg(fn, ins.a);
			break;
		default:
			break;
		}
	}

	void simulate_atomic(const lowir2cy86::Function& fn,
	                     const lowir2cy86::Instruction& ins)
	{
		if (ins.has_dest)
			temp_reg(ins.dest);
		if (ins.kind == lowir2cy86::InstrKind::AtomicExchange)
		{
			const string ptr = value_reg(fn, ins.a);
			const string src = value_reg(fn, ins.b);
			if (can_reuse_written_value(ins.b))
				remember_reload(ptr, src, true);
		}
		else if (ins.kind == lowir2cy86::InstrKind::AtomicCompareExchange)
		{
			const string ptr = value_reg(fn, ins.a);
			simulate_expected_pointer(fn, ins.b);
			const string desired = value_reg(fn, ins.c);
			if (can_reuse_written_value(ins.c))
				remember_reload(ptr, desired, false);
			prefer_r8_stack_load_ = true;
		}
		else
		{
			value_reg(fn, ins.a);
			value_reg(fn, ins.b);
			value_reg(fn, ins.c);
		}
		if (ins.has_dest &&
		    ins.kind != lowir2cy86::InstrKind::AtomicCompareExchange)
			prefer_r8_literal_ = true;
	}

	void simulate_expected_pointer(const lowir2cy86::Function& fn,
	                               const lowir2cy86::Value& value)
	{
		const lowir2cy86::Instruction* addr = inline_addr_definition(value);
		if (addr != nullptr)
		{
			if (addr->a.kind == lowir2cy86::ValueKind::Temp)
				value_reg(fn, addr->a);
			return;
		}
		value_reg(fn, value);
	}

	void simulate_binary(const lowir2cy86::Function& fn,
	                     const lowir2cy86::Instruction& ins)
	{
		if (lowir2cy86::is_float_type(ins.type) &&
		    !lowir2cy86::is_f80_type(ins.type))
		{
			float_binary_dest(ins);
			float_value(fn, ins.a);
			float_value(fn, ins.b);
			return;
		}
		const string dst = binary_dest_reg(ins);
		value_reg(fn, ins.a);
		if (ins.b.kind != lowir2cy86::ValueKind::Literal)
			value_reg(fn, ins.b);
		remember_temp_reg(ins.dest, dst);
	}

	void simulate_cmp(const lowir2cy86::Function& fn,
	                  const lowir2cy86::Instruction& ins)
	{
		if (lowir2cy86::is_float_type(ins.type))
		{
			float_value(fn, ins.a);
			float_value(fn, ins.b);
			remember_temp_reg(ins.dest, "rax");
			return;
		}
		const string dst = cmp_value_dest_reg(fn, ins);
		value_reg(fn, ins.a);
		if (ins.b.kind != lowir2cy86::ValueKind::Literal)
			value_reg(fn, ins.b);
		remember_temp_reg(ins.dest, dst);
	}

	void dump_const(const lowir2cy86::Instruction& ins)
	{
		if (lowir2cy86::is_float_type(ins.type) && !lowir2cy86::is_f80_type(ins.type))
		{
			out_ << "    fmov." << ins.type.text << " " << xmm_reg(ins.dest)
			     << ", " << ins.a.text << "\n";
			return;
		}
		const string dst = const_dest_reg(ins);
		out_ << "    mov " << dst << ", " << ins.a.text << "\n";
		dump_narrow_extend(ins.type, dst);
		remember_const_dest(ins.dest, dst);
	}

	string const_dest_reg(const lowir2cy86::Instruction& ins)
	{
		if (!preferred_literal_reg_.empty() && lowir2cy86::is_integer_type(ins.type))
		{
			const string reg = preferred_literal_reg_;
			preferred_literal_reg_.clear();
			fixed_const_dest_ = true;
			return reg;
		}
		if (prefer_r8_literal_ && lowir2cy86::is_integer_type(ins.type))
		{
			prefer_r8_literal_ = false;
			return "r8";
		}
		return temp_reg(ins.dest);
	}

	void remember_const_dest(const string& name, const string& reg)
	{
		if (fixed_const_dest_)
		{
			fixed_temp_regs_[name] = reg;
			note_temp_reg(reg);
			fixed_const_dest_ = false;
			return;
		}
		remember_temp_reg(name, reg);
	}

	void dump_addr(const lowir2cy86::Function& fn,
	               const lowir2cy86::Instruction& ins)
	{
		const string op =
		    ins.a.kind == lowir2cy86::ValueKind::Global ? "mov" : "lea";
		out_ << "    " << op << " " << temp_reg(ins.dest) << ", "
		     << value_reg(fn, ins.a) << "\n";
	}

	void dump_copy(const lowir2cy86::Function& fn,
	               const lowir2cy86::Instruction& ins)
	{
		if (lowir2cy86::is_float_type(ins.type) && !lowir2cy86::is_f80_type(ins.type))
		{
			out_ << "    fmov." << ins.type.text << " " << xmm_reg(ins.dest)
			     << ", " << float_value(fn, ins.a) << "\n";
			return;
		}
		out_ << "    mov " << temp_reg(ins.dest) << ", "
		     << value_reg(fn, ins.a) << "\n";
	}

	void dump_index(const lowir2cy86::Function& fn,
	                const lowir2cy86::Instruction& ins)
	{
		const size_t scale = lowir2cy86::storage_size(ins.type);
		const string dst = temp_reg(ins.dest);
		out_ << "    mov " << dst << ", " << value_reg(fn, ins.a) << "\n";
		if (ins.b.kind == lowir2cy86::ValueKind::Literal)
		{
			const long offset = stol(ins.b.text) * static_cast<long>(scale);
			out_ << "    lea " << dst << ", [" << dst << "+"
			     << offset << "]\n";
		}
		else
			out_ << "    lea " << dst << ", [" << dst << "+"
			     << value_reg(fn, ins.b)
			     << (scale == 1 ? "" : "*" + to_string(scale)) << "]\n";
	}

	string load_source(const lowir2cy86::Function& fn,
	                   const lowir2cy86::Value& value)
	{
		if (value.kind == lowir2cy86::ValueKind::Temp)
			return "[" + value_reg(fn, value) + "]";
		return value_reg(fn, value);
	}

	void dump_load(const lowir2cy86::Function& fn,
	               const lowir2cy86::Instruction& ins)
	{
		const string dst = load_dest_reg(fn, ins);
		out_ << "    load." << ins.type.text << " " << dst << ", "
		     << load_source(fn, ins.a) << "\n";
		dump_narrow_extend(ins.type, dst);
		remember_load_dest(ins.dest, dst);
	}

	string load_dest_reg(const lowir2cy86::Function& fn,
	                     const lowir2cy86::Instruction& ins)
	{
		if (ins.kind == lowir2cy86::InstrKind::AtomicLoad)
		{
			const string ptr = value_reg(fn, ins.a);
			if (!preferred_load_reg_.empty() && ptr == preferred_load_ptr_)
			{
				const string reg = preferred_load_reg_;
				preferred_load_ptr_.clear();
				preferred_load_reg_.clear();
				fixed_load_dest_ = true;
				if (preferred_load_sets_literal_)
					prefer_r8_literal_ = true;
				preferred_load_sets_literal_ = false;
				return reg;
			}
			return temp_reg(ins.dest);
		}
		if (prefer_r8_stack_load_ && ins.a.kind == lowir2cy86::ValueKind::Slot)
		{
			prefer_r8_stack_load_ = false;
			fixed_load_dest_ = true;
			return "r8";
		}
		if (ins.a.kind == lowir2cy86::ValueKind::Temp)
			return "r8";
		return temp_reg(ins.dest);
	}

	void remember_load_dest(const string& name, const string& reg)
	{
		if (fixed_load_dest_)
		{
			fixed_temp_regs_[name] = reg;
			note_temp_reg(reg);
			fixed_load_dest_ = false;
			return;
		}
		remember_temp_reg(name, reg);
	}

	void dump_atomic_store(const lowir2cy86::Function& fn,
	                       const lowir2cy86::Instruction& ins)
	{
		const string ptr = value_reg(fn, ins.b);
		const string src = value_reg(fn, ins.a);
		if (ins.order_a >= 5)
		{
			out_ << "    mov rax, " << src << "\n";
			out_ << "    xchg." << ins.type.text << " [" << ptr << "], rax\n";
			remember_reload(ptr, src, true);
			return;
		}
		out_ << "    store." << ins.type.text << " [" << ptr << "], " << src << "\n";
		remember_reload(ptr, src, true);
	}

	void remember_store_reload(const lowir2cy86::Function& fn,
	                           const lowir2cy86::Value& ptr_value,
	                           const lowir2cy86::Value& src_value)
	{
		remember_reload(value_reg(fn, ptr_value), value_reg(fn, src_value), true);
	}

	void remember_reload(const string& ptr, const string& reg, bool prefer_literal)
	{
		preferred_load_ptr_ = ptr;
		preferred_load_reg_ = reg;
		preferred_load_sets_literal_ = prefer_literal;
		note_temp_reg(reg);
	}

	void dump_narrow_extend(const lowir2cy86::Type& type, const string& reg)
	{
		if (lowir2cy86::is_signed_integer_type(type) && type.bits < 64)
			out_ << "    sext.i" << type.bits << " " << reg << "\n";
		else if (type.kind == lowir2cy86::TypeKind::UnsignedInt && type.bits < 64)
			out_ << "    zext.i" << type.bits << " " << reg << "\n";
	}

	string store_dest(const lowir2cy86::Function& fn,
	                  const lowir2cy86::Value& value)
	{
		if (value.kind == lowir2cy86::ValueKind::Temp)
			return "[" + value_reg(fn, value) + "]";
		return value_reg(fn, value);
	}

	void dump_store(const lowir2cy86::Function& fn,
	                const lowir2cy86::Instruction& ins)
	{
		out_ << "    store." << ins.type.text << " " << store_dest(fn, ins.b)
		     << ", " << value_reg(fn, ins.a) << "\n";
		remember_store_literal(fn, ins.a);
	}

	void remember_store_literal(const lowir2cy86::Function& fn,
	                            const lowir2cy86::Value& value)
	{
		if (can_reuse_written_value(value))
			preferred_literal_reg_ = value_reg(fn, value);
	}

	void dump_scalar(const lowir2cy86::Function& fn,
	                 const lowir2cy86::Instruction& ins)
	{
		if (ins.kind == lowir2cy86::InstrKind::Unary)
			dump_unary(fn, ins);
		else if (ins.kind == lowir2cy86::InstrKind::Binary)
			dump_binary(fn, ins);
		else if (ins.kind == lowir2cy86::InstrKind::Cmp)
			dump_cmp_value(fn, ins);
		else
			dump_convert(fn, ins);
	}

	void dump_unary(const lowir2cy86::Function& fn,
	                const lowir2cy86::Instruction& ins)
	{
		const string dst = temp_reg(ins.dest);
		out_ << "    mov " << dst << ", " << value_reg(fn, ins.a) << "\n";
		if (ins.op == "neg")
			out_ << "    neg " << dst << "\n";
		else if (ins.op == "bitnot")
			out_ << "    not " << dst << "\n";
		else if (ins.op == "bswap")
		{
			out_ << "    bswap " << dst << "\n";
			if (ins.type.kind == lowir2cy86::TypeKind::UnsignedInt &&
			    ins.type.bits < 64)
				out_ << "    zext.i" << ins.type.bits << " " << dst << "\n";
		}
		else if (ins.op == "not")
		{
			out_ << "    cmp." << ins.type.text << " " << dst << ", 0\n";
			out_ << "    sete " << dst << "\n";
			out_ << "    movzx " << dst << ", " << dst << "\n";
		}
	}

	void dump_convert(const lowir2cy86::Function& fn,
	                  const lowir2cy86::Instruction& ins)
	{
		const string dst = convert_dest(fn, ins);
		out_ << "    " << ins.op << "." << conversion_type_text(ins.src_type)
		     << "." << conversion_type_text(ins.type) << " " << dst << ", "
		     << convert_source(fn, ins) << "\n";
		remember_convert_dest(ins, dst);
	}

	string conversion_type_text(const lowir2cy86::Type& type) const
	{
		if (lowir2cy86::is_integer_type(type))
			return "i" + to_string(type.bits);
		return type.text;
	}

	string convert_dest(const lowir2cy86::Function& fn,
	                    const lowir2cy86::Instruction& ins)
	{
		if (lowir2cy86::is_float_type(ins.type) && !lowir2cy86::is_f80_type(ins.type))
			return "xmm0";
		if (lowir2cy86::is_integer_type(ins.type))
		{
			const string origin = integer_roundtrip_origin(fn, ins);
			if (!origin.empty())
				return origin;
		}
		return lowir2cy86::is_float_type(ins.type) ? f80_home(fn, ins.dest)
		                                           : temp_reg(ins.dest);
	}

	string convert_source(const lowir2cy86::Function& fn,
	                      const lowir2cy86::Instruction& ins)
	{
		if (lowir2cy86::is_float_type(ins.src_type) &&
		    !lowir2cy86::is_f80_type(ins.src_type))
			return float_value(fn, ins.a);
		if (lowir2cy86::is_f80_type(ins.src_type))
			return f80_value(fn, ins.a);
		return value_reg(fn, ins.a);
	}

	void remember_convert_dest(const lowir2cy86::Instruction& ins,
	                           const string& dst)
	{
		if (lowir2cy86::is_float_type(ins.type) && !lowir2cy86::is_f80_type(ins.type))
			remember_xmm_reg(ins.dest, dst);
		else
			remember_temp_reg(ins.dest, dst);
	}

	string integer_roundtrip_origin(const lowir2cy86::Function& fn,
	                                const lowir2cy86::Instruction& ins)
	{
		if (ins.a.kind != lowir2cy86::ValueKind::Temp)
			return "";
		map<string, const lowir2cy86::Instruction*>::const_iterator it =
		    definitions_.find(ins.a.text);
		if (it == definitions_.end() || it->second->kind != lowir2cy86::InstrKind::Convert)
			return "";
		const lowir2cy86::Instruction& src = *it->second;
		if (src.a.kind != lowir2cy86::ValueKind::Temp)
			return "";
		return value_reg(fn, src.a);
	}

	void dump_binary(const lowir2cy86::Function& fn,
	                 const lowir2cy86::Instruction& ins)
	{
		if (lowir2cy86::is_float_type(ins.type) && !lowir2cy86::is_f80_type(ins.type))
		{
			dump_float_binary(fn, ins);
			return;
		}
		const string dst = binary_dest_reg(ins);
		const string left = value_reg(fn, ins.a);
		if (dst != left)
			out_ << "    mov " << dst << ", " << left << "\n";
		if (ins.op == "udiv" || ins.op == "umod")
			dump_divmod(fn, ins, dst, false);
		else if (ins.op == "div" || ins.op == "mod")
			dump_divmod(fn, ins, dst, true);
		else if (ins.op == "ushr")
			out_ << "    shr " << dst << ", " << shift_rhs(fn, ins.b) << "\n";
		else if (ins.op == "shr")
			out_ << "    sar " << dst << ", " << shift_rhs(fn, ins.b) << "\n";
		else if (ins.op == "shl")
			out_ << "    shl " << dst << ", " << shift_rhs(fn, ins.b) << "\n";
		else
		{
			string rhs = value_reg(fn, ins.b);
			if (ins.a.kind == lowir2cy86::ValueKind::Temp &&
			    ins.b.kind == lowir2cy86::ValueKind::Temp &&
			    ins.a.text == ins.b.text && dst != left)
				rhs = dst;
			out_ << "    " << binary_opcode(ins.op) << " " << dst << ", "
			     << rhs << "\n";
		}
		dump_narrow_extend(ins.type, dst);
		remember_temp_reg(ins.dest, dst);
	}

	void dump_float_binary(const lowir2cy86::Function& fn,
	                       const lowir2cy86::Instruction& ins)
	{
		const string dst = float_binary_dest(ins);
		out_ << "    f" << float_binary_opcode(ins.op) << "." << ins.type.text << " "
		     << dst << ", " << float_value(fn, ins.a) << ", "
		     << float_value(fn, ins.b) << "\n";
		remember_xmm_reg(ins.dest, dst);
	}

	string float_binary_opcode(const string& op) const
	{
		if (op == "add") return "add";
		if (op == "sub") return "sub";
		if (op == "mul") return "mul";
		if (op == "div") return "div";
		return op;
	}

	string float_binary_dest(const lowir2cy86::Instruction& ins)
	{
		if (ins.b.kind == lowir2cy86::ValueKind::Literal)
			return "xmm0";
		return xmm_reg(ins.dest);
	}

	string binary_dest_reg(const lowir2cy86::Instruction& ins)
	{
		if (ins.a.kind == lowir2cy86::ValueKind::Temp &&
		    ins.b.kind == lowir2cy86::ValueKind::Temp &&
		    ins.a.text == ins.b.text)
		{
			if (temp_reg(ins.a.text) == "rax")
				return "r8";
			return temp_reg(ins.a.text);
		}
		if (ins.a.kind == lowir2cy86::ValueKind::Temp &&
		    use_counts_[ins.a.text] == 1)
			return temp_reg(ins.a.text);
		return temp_reg(ins.dest);
	}

	void remember_temp_reg(const string& name, const string& reg)
	{
		note_temp_reg(reg);
		for (size_t i = 0; i < temp_names_.size(); ++i)
		{
			if (temp_names_[i] == name)
			{
				temp_regs_[i] = reg;
				return;
			}
		}
		temp_names_.push_back(name);
		temp_regs_.push_back(reg);
	}

	string binary_opcode(const string& op) const
	{
		if (op == "add") return "add";
		if (op == "sub") return "sub";
		if (op == "mul") return "imul";
		if (op == "and") return "and";
		if (op == "or") return "or";
		if (op == "xor") return "xor";
		return op;
	}

	string shift_rhs(const lowir2cy86::Function& fn,
	                 const lowir2cy86::Value& value)
	{
		return value.kind == lowir2cy86::ValueKind::Literal ? value.text : value_reg(fn, value);
	}

	void dump_divmod(const lowir2cy86::Function& fn,
	                 const lowir2cy86::Instruction& ins,
	                 const string& dst,
	                 bool signed_div)
	{
		out_ << "    mov rcx, " << value_reg(fn, ins.b) << "\n";
		out_ << "    mov rax, " << dst << "\n";
		out_ << "    mov rdx, 0\n";
		out_ << "    " << (signed_div ? "idiv" : "div") << " rcx\n";
		if (ins.op == "mod" || ins.op == "umod")
			out_ << "    mov " << dst << ", rdx\n";
		else
			out_ << "    mov " << dst << ", rax\n";
	}

	void dump_cmp_value(const lowir2cy86::Function& fn,
	                    const lowir2cy86::Instruction& ins)
	{
		if (lowir2cy86::is_float_type(ins.type))
		{
			out_ << "    f" << condition_word(ins.op) << "." << ins.type.text
			     << " rax, " << float_value(fn, ins.a) << ", "
			     << float_value(fn, ins.b) << "\n";
			remember_temp_reg(ins.dest, "rax");
			return;
		}
		const string dst = cmp_value_dest_reg(fn, ins);
		const string lhs = value_reg(fn, ins.a);
		if (dst != lhs)
			out_ << "    mov " << dst << ", " << lhs << "\n";
		const string rhs = compare_rhs(fn, ins.b);
		out_ << "    cmp." << ins.type.text << " " << dst << ", " << rhs << "\n";
		out_ << "    set" << condition_suffix(ins.op) << " " << dst << "\n";
		out_ << "    movzx " << dst << ", " << dst << "\n";
		remember_temp_reg(ins.dest, dst);
	}

	string condition_word(const string& op) const
	{
		if (op == "eq") return "eq";
		if (op == "ne") return "ne";
		if (op == "lt" || op == "ult") return "lt";
		if (op == "le" || op == "ule") return "le";
		if (op == "gt" || op == "ugt") return "gt";
		if (op == "ge" || op == "uge") return "ge";
		return op;
	}

	string cmp_value_dest_reg(const lowir2cy86::Function& fn,
	                          const lowir2cy86::Instruction& ins)
	{
		if (ins.a.kind == lowir2cy86::ValueKind::Temp &&
		    use_counts_[ins.a.text] == 1)
			return value_reg(fn, ins.a);
		return temp_reg(ins.dest);
	}

	string compare_rhs(const lowir2cy86::Function& fn,
	                   const lowir2cy86::Value& value)
	{
		if (value.kind == lowir2cy86::ValueKind::Literal)
		{
			out_ << "    mov rdx, " << value.text << "\n";
			return "rdx";
		}
		return value_reg(fn, value);
	}

	string condition_suffix(const string& op) const
	{
		if (op == "eq") return "e";
		if (op == "ne") return "ne";
		if (op == "lt") return "l";
		if (op == "le") return "le";
		if (op == "gt") return "g";
		if (op == "ge") return "ge";
		if (op == "ult") return "b";
		if (op == "ule") return "be";
		if (op == "ugt") return "a";
		if (op == "uge") return "ae";
		return op;
	}

	string branch_suffix(const string& op) const
	{
		if (op == "eq") return "e";
		if (op == "ne") return "ne";
		if (op == "lt") return "l";
		if (op == "le") return "le";
		if (op == "gt") return "g";
		if (op == "ge") return "ge";
		if (op == "ult") return "b";
		if (op == "ule") return "be";
		if (op == "ugt") return "a";
		if (op == "uge") return "ae";
		return "ne";
	}

	void dump_branch(const lowir2cy86::Function& fn,
	                 const lowir2cy86::Instruction& ins)
	{
		if (ins.a.kind == lowir2cy86::ValueKind::Temp &&
		    direct_branch_cmp_.find(ins.a.text) != direct_branch_cmp_.end())
		{
			const lowir2cy86::Instruction& cmp = *definitions_[ins.a.text];
			if (lowir2cy86::is_float_type(cmp.type))
			{
				dump_float_branch(fn, cmp, ins.target, ins.target_false);
				return;
			}
			const string lhs = direct_cmp_lhs(fn, cmp);
			const string rhs = direct_cmp_rhs(fn, cmp);
			out_ << "    cmp." << cmp.type.text << " " << lhs << ", "
			     << rhs << "\n";
			out_ << "    j" << branch_suffix(cmp.op) << " " << ins.target << "\n";
			out_ << "    jmp " << ins.target_false << "\n";
			return;
		}
		out_ << "    cmp.i64 " << value_reg(fn, ins.a) << ", 0\n";
		out_ << "    jne " << ins.target << "\n";
		out_ << "    jmp " << ins.target_false << "\n";
	}

	void dump_float_branch(const lowir2cy86::Function& fn,
	                       const lowir2cy86::Instruction& cmp,
	                       const string& target,
	                       const string& target_false)
	{
		out_ << "    fcmp." << cmp.type.text << " " << float_value(fn, cmp.a)
		     << ", " << float_value(fn, cmp.b) << "\n";
		if (cmp.op == "ne")
			out_ << "    jp " << target << "\n";
		else
			out_ << "    jp " << target_false << "\n";
		out_ << "    j" << float_branch_suffix(cmp.op) << " " << target << "\n";
		out_ << "    jmp " << target_false << "\n";
	}

	string float_branch_suffix(const string& op) const
	{
		if (op == "eq") return "e";
		if (op == "ne") return "ne";
		if (op == "lt") return "a";
		if (op == "le") return "ae";
		if (op == "gt") return "b";
		if (op == "ge") return "be";
		return branch_suffix(op);
	}

	string direct_cmp_lhs(const lowir2cy86::Function& fn,
	                      const lowir2cy86::Instruction& cmp)
	{
		if (cmp.a.kind == lowir2cy86::ValueKind::Literal)
		{
			out_ << "    mov rax, " << cmp.a.text << "\n";
			return "rax";
		}
		return value_reg(fn, cmp.a);
	}

	string direct_cmp_rhs(const lowir2cy86::Function& fn,
	                      const lowir2cy86::Instruction& cmp)
	{
		if (cmp.b.kind == lowir2cy86::ValueKind::Literal &&
		    lowir2cy86::is_integer_type(cmp.type) && cmp.type.bits < 32)
		{
			out_ << "    mov rdx, " << cmp.b.text << "\n";
			return "rdx";
		}
		return cmp.b.kind == lowir2cy86::ValueKind::Literal
		           ? cmp.b.text
		           : value_reg(fn, cmp.b);
	}

	void dump_call(const lowir2cy86::Function& fn,
	               const lowir2cy86::Instruction& ins)
	{
		for (size_t i = 0; i < ins.args.size() && i < 6; ++i)
			out_ << "    mov " << abi_gpr(i) << ", "
			     << value_reg(fn, ins.args[i]) << "\n";
		if (ins.a.kind == lowir2cy86::ValueKind::Function)
			out_ << "    call " << ins.a.text << "\n";
		else
			out_ << "    call *" << value_reg(fn, ins.a) << "\n";
		if (ins.has_dest && !lowir2cy86::is_void_type(ins.type))
			out_ << "    mov " << temp_reg(ins.dest) << ", rax\n";
	}

	void dump_atomic(const lowir2cy86::Function& fn,
	                 const lowir2cy86::Instruction& ins)
	{
		const string dst = ins.has_dest ? temp_reg(ins.dest) : "rax";
		if (ins.kind == lowir2cy86::InstrKind::AtomicExchange)
		{
			const string ptr = value_reg(fn, ins.a);
			const string src = value_reg(fn, ins.b);
			out_ << "    mov rax, " << src << "\n";
			out_ << "    xchg." << ins.type.text << " [" << ptr << "], rax\n";
			if (can_reuse_written_value(ins.b))
				remember_reload(ptr, src, true);
		}
		else if (ins.kind == lowir2cy86::InstrKind::AtomicAddFetch)
		{
			out_ << "    mov rcx, " << value_reg(fn, ins.a) << "\n";
			out_ << "    mov rdx, " << value_reg(fn, ins.b) << "\n";
			out_ << "    mov rax, " << value_reg(fn, ins.b) << "\n";
			out_ << "    lock_xadd." << ins.type.text << " [rcx], rax\n";
			out_ << "    add rax, rdx\n";
		}
		else
			dump_atomic_compare_exchange(fn, ins);
		if (ins.has_dest)
		{
			out_ << "    mov " << dst << ", rax\n";
			if (ins.kind != lowir2cy86::InstrKind::AtomicCompareExchange)
				dump_narrow_extend(ins.type, dst);
			if (ins.kind != lowir2cy86::InstrKind::AtomicCompareExchange)
				prefer_r8_literal_ = true;
			if (ins.kind == lowir2cy86::InstrKind::AtomicCompareExchange)
				prefer_r8_stack_load_ = true;
		}
	}

	void dump_atomic_compare_exchange(const lowir2cy86::Function& fn,
	                                  const lowir2cy86::Instruction& ins)
	{
		const string ptr = value_reg(fn, ins.a);
		out_ << "    mov rcx, " << ptr << "\n";
		dump_expected_pointer(fn, ins.b);
		out_ << "    load." << ins.type.text << " rax, [rdx]\n";
		const string desired = value_reg(fn, ins.c);
		out_ << "    mov rsi, " << desired << "\n";
		out_ << "    lock_cmpxchg." << ins.type.text << " [rcx], rsi\n";
		out_ << "    store." << ins.type.text << " [rdx], rax\n";
		out_ << "    sete rax\n";
		out_ << "    movzx rax, rax\n";
		if (can_reuse_written_value(ins.c))
			remember_reload(ptr, desired, false);
	}

	void dump_expected_pointer(const lowir2cy86::Function& fn,
	                           const lowir2cy86::Value& value)
	{
		const lowir2cy86::Instruction* addr = inline_addr_definition(value);
		if (addr != nullptr)
		{
			const string op =
			    addr->a.kind == lowir2cy86::ValueKind::Global ? "mov" : "lea";
			out_ << "    " << op << " rdx, " << value_reg(fn, addr->a) << "\n";
			return;
		}
		out_ << "    mov rdx, " << value_reg(fn, value) << "\n";
	}

	const lowir2cy86::Instruction* inline_addr_definition(
	    const lowir2cy86::Value& value) const
	{
		if (value.kind != lowir2cy86::ValueKind::Temp ||
		    inline_atomic_expected_addrs_.find(value.text) ==
		        inline_atomic_expected_addrs_.end())
			return nullptr;
		map<string, const lowir2cy86::Instruction*>::const_iterator it =
		    definitions_.find(value.text);
		if (it == definitions_.end())
			return nullptr;
		return it->second;
	}

	bool can_reuse_written_value(const lowir2cy86::Value& value) const
	{
		if (value.kind != lowir2cy86::ValueKind::Temp)
			return false;
		map<string, int>::const_iterator it = use_counts_.find(value.text);
		return it == use_counts_.end() || it->second <= 1;
	}

	void dump_switch(const lowir2cy86::Function& fn,
	                 const lowir2cy86::Instruction& ins)
	{
		out_ << "    mov rax, " << value_reg(fn, ins.a) << "\n";
		for (size_t i = 0; i < ins.switch_cases.size(); ++i)
		{
			out_ << "    mov rcx, " << value_reg(fn, ins.switch_cases[i].value)
			     << "\n";
			out_ << "    cmp.i64 rax, rcx\n";
			out_ << "    je " << ins.switch_cases[i].target << "\n";
		}
		out_ << "    jmp " << ins.target << "\n";
	}

	void dump_return(const lowir2cy86::Function& fn,
	                 const lowir2cy86::Instruction& ins)
	{
		if (lowir2cy86::is_void_type(ins.type))
		{
			out_ << "    ret\n";
			return;
		}
		const string src = value_reg(fn, ins.a);
		if (src != "rax")
			out_ << "    mov rax, " << src << "\n";
		out_ << "    ret rax\n";
	}
};

void write_machine_ir_file(const lowir2cy86::Program& program,
                           const Options& options)
{
	MirDumper dumper(program, effective_target(options));
	write_text_file(options.machine_ir_file, dumper.dump());
}

}  // namespace

void compile(const vector<string>& srcfiles, const Options& options)
{
	if (!options.target.empty() && options.target != "linux")
		throw runtime_error("unsupported target");
	lowir2cy86::Program program = lowir2cy86::parse_files(srcfiles);
	lowir2cy86::validate_and_layout(program);
	if (!options.machine_ir_file.empty())
		write_machine_ir_file(program, options);
	if (!options.outfile.empty())
		write_native_file(program, options);
}

}  // namespace lowir2native
