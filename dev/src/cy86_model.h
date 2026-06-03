#pragma once

#include <cstddef>
#include <cstdint>
#include <map>
#include <string>
#include <vector>

#include "posttoken_support.h"
#include "preproc_support.h"

using namespace std;

namespace cy86 {

struct Options
{
	preproc::Options preprocess;
	string target;
};

enum class RegisterBase
{
	SP,
	BP,
	X,
	Y,
	Z,
	T
};

struct RegisterRef
{
	RegisterBase base;
	int width_bits;
	string name;

	RegisterRef();
};

enum class OperandKind
{
	Register,
	Immediate,
	Memory
};

enum class AddressKind
{
	Literal,
	Label,
	Register
};

struct LiteralValue
{
	string source;
	EFundamentalType type;
	vector<unsigned char> bytes;
	size_t alignment;
	bool signed_integral;
	bool unsigned_integral;
	bool floating;
	bool arithmetic;

	LiteralValue();
};

struct ImmediateValue
{
	bool label;
	string label_name;
	LiteralValue literal;
	bool has_addend;
	LiteralValue addend;
	int addend_sign;

	ImmediateValue();
};

struct MemoryAddress
{
	AddressKind kind;
	LiteralValue literal;
	string label_name;
	RegisterRef reg;
	bool has_addend;
	LiteralValue addend;
	int addend_sign;

	MemoryAddress();
};

struct Operand
{
	OperandKind kind;
	RegisterRef reg;
	ImmediateValue imm;
	MemoryAddress mem;

	Operand();
};

enum class StatementKind
{
	Instruction,
	LiteralData
};

struct Statement
{
	StatementKind kind;
	vector<string> labels;
	string opcode;
	vector<Operand> operands;
	LiteralValue literal;
	size_t offset;
	size_t size;

	Statement();
};

struct OperandDesc
{
	bool write;
	bool read;
	bool address;
	bool boolean_value;
	bool integer;
	bool signed_integer;
	bool unsigned_integer;
	bool floating;
	bool immediate_only;
	int width_bits;

	OperandDesc();
};

struct OpcodeDesc
{
	string name;
	vector<OperandDesc> operands;
	bool data_opcode;
	int data_width_bits;

	OpcodeDesc();
};

struct Program
{
	vector<Statement> statements;
	map<string, uint64_t> labels;
};

bool is_register_name(const string& name);
bool parse_register(const string& name, RegisterRef& out);
int register_family_x86_code(RegisterBase base);
bool is_opcode_name(const string& name);
const OpcodeDesc* find_opcode(const string& name);

LiteralValue parse_literal_value(const string& source);
LiteralValue negate_literal_value(const LiteralValue& value);
vector<unsigned char> convert_literal_width(const LiteralValue& value,
                                            int width_bits);
uint64_t literal_to_u64(const LiteralValue& value);
uint64_t immediate_to_u64(const ImmediateValue& imm,
                          const map<string, uint64_t>& labels);

Program parse_program_files(const vector<string>& srcfiles,
                            const Options& options);
void compile_to_file(const vector<string>& srcfiles,
                     const Options& options,
                     const string& outfile);

}  // namespace cy86
