#pragma once

#include <cstddef>
#include <map>
#include <string>
#include <utility>
#include <vector>

using namespace std;

namespace lowir2cy86 {

enum class TypeKind
{
	Void,
	SignedInt,
	UnsignedInt,
	Float,
	Ptr,
	Obj
};

struct Type
{
	TypeKind kind;
	string text;
	int bits;
	size_t size;
	size_t align;
	size_t obj_size;
	size_t obj_align;

	Type();
};

struct MetadataItem
{
	string key;
	string value;
	bool global_value;

	MetadataItem();
};

typedef vector<MetadataItem> Metadata;

struct Span
{
	size_t bytes;
	size_t align;

	Span();
};

enum class ValueKind
{
	None,
	Temp,
	Slot,
	Global,
	Function,
	Literal
};

struct Value
{
	ValueKind kind;
	string text;

	Value();
};

struct Parameter
{
	string name;
	Type type;
	Metadata metadata;
	size_t offset;

	Parameter();
};

struct Slot
{
	string name;
	Type type;
	size_t offset;

	Slot();
};

struct CallSignature
{
	bool present;
	vector<Parameter> params;
	Type ret;
	Metadata metadata;

	CallSignature();
};

enum class InstrKind
{
	Const,
	Copy,
	Addr,
	Load,
	Store,
	AtomicLoad,
	AtomicStore,
	AtomicExchange,
	AtomicCompareExchange,
	AtomicAddFetch,
	AtomicThreadFence,
	AtomicSignalFence,
	Index,
	CopyObj,
	ZeroInit,
	Unary,
	Binary,
	Cmp,
	Convert,
	Call,
	EhTry,
	EhCleanup,
	EhEnd,
	Throw,
	Exception,
	Resume,
	Jump,
	Branch,
	Switch,
	Return
};

struct SwitchCase
{
	Value value;
	string target;
};

struct Instruction
{
	InstrKind kind;
	string dest;
	Type type;
	Type src_type;
	Type result_type;
	string op;
	Value a;
	Value b;
	Value c;
	vector<Value> args;
	CallSignature signature;
	Span span;
	string target;
	string target_false;
	vector<SwitchCase> switch_cases;
	int order_a;
	int order_b;
	bool has_dest;

	Instruction();
};

struct Block
{
	string name;
	vector<Instruction> instructions;

	Block();
};

struct GlobalInit
{
	string kind;
	string literal;
	string target;
	int addend;
	bool has_addend;

	GlobalInit();
};

struct GlobalDataItem
{
	string kind;
	Type type;
	string literal;
	string target;
	int addend;
	bool has_addend;
	size_t zero_bytes;
};

struct Global
{
	bool declaration;
	string name;
	bool has_type;
	Type type;
	Metadata metadata;
	GlobalInit init;
	vector<GlobalDataItem> data;

	Global();
};

struct Function
{
	bool declaration;
	string name;
	vector<Parameter> params;
	Type ret;
	Metadata metadata;
	vector<Slot> slots;
	vector<Block> blocks;
	vector<string> temp_order;
	map<string, Type> temp_types;
	map<string, size_t> temp_offsets;
	map<string, size_t> slot_offsets;
	map<string, Type> slot_types;
	map<string, Type> param_types;
	map<string, size_t> param_offsets;
	size_t hidden_result_offset;
	size_t stack_size;
	size_t convert_scratch_offset;
	bool needs_convert_scratch;

	Function();
};

struct ObjectAlias
{
	string object;
	string target;
};

struct Program
{
	vector<Global> globals;
	vector<Function> functions;
	vector<ObjectAlias> aliases;
	map<string, size_t> global_by_name;
	map<string, size_t> function_by_name;
	bool needs_eh_runtime;
	string entry_function;
	string init_function;
	string fini_function;

	Program();
};

Type parse_type_text(const string& text);
Type object_type(size_t bytes, size_t align);
Span parse_span_text(const string& text);

bool is_void_type(const Type& type);
bool is_ptr_type(const Type& type);
bool is_obj_type(const Type& type);
bool is_float_type(const Type& type);
bool is_f80_type(const Type& type);
bool is_integer_type(const Type& type);
bool is_signed_integer_type(const Type& type);
bool is_scalar_runtime_type(const Type& type);
size_t storage_size(const Type& type);
size_t stack_storage_size(const Type& type);
int cy86_width_bits(const Type& type);

string metadata_value(const Metadata& metadata, const string& key);
bool metadata_has(const Metadata& metadata, const string& key);
string lowir_symbol_body(const string& name);
string function_label(const string& name);
string global_label(const string& name);

Program parse_files(const vector<string>& srcfiles);
void validate_and_layout(Program& program);
string emit_cy86(const Program& program);
void compile_to_file(const vector<string>& srcfiles, const string& outfile);

}  // namespace lowir2cy86
