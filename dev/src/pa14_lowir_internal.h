#pragma once

#include "pa14_lowir.h"

#include "pa12_internal.h"

#include <map>
#include <memory>
#include <set>
#include <sstream>
#include <stdexcept>
#include <string>
#include <vector>

using namespace std;

namespace pa14 {
namespace internal {

using pa11::Binding;
using pa11::BindingKind;
using pa11::Scope;
using pa11::ScopeKind;
using pa11::TypeKind;
using pa11::TypePtr;
using pa12::internal::Node;
using pa12::internal::ValueCategory;

struct Value
{
	string type;
	string text;

	Value() {}
	Value(const string& t, const string& v) : type(t), text(v) {}
};

struct Block
{
	string name;
	vector<string> instrs;
	bool terminated;

	explicit Block(const string& n) : name(n), terminated(false) {}
};

struct FunctionOut
{
	string header;
	vector<string> slots;
	vector<Block> blocks;
};

bool starts_with(const string& text, const string& prefix);
TypePtr object_type(TypePtr type);
TypePtr strip_for_value(TypePtr type);
bool is_reference(TypePtr type);
bool is_float_type(TypePtr type);
bool is_unsigned_type(TypePtr type);
string scalar_lowir_type(TypePtr type);
int lowir_arithmetic_rank(TypePtr type);
TypePtr lowir_integral_promotion(TypePtr type);
TypePtr lowir_common_type(TypePtr left, TypePtr right);
string slot_lowir_type(TypePtr type);
string lowir_literal(TypePtr type, const Node& node);
string lowir_parameter(TypePtr type);
string metadata_suffix(const vector<string>& items);
vector<string> qualified_parts(const Binding* binding);
string source_symbol_base(const Binding* binding);

struct ProgramLowerer
{
	vector<string> declares;
	vector<string> globals;
	vector<FunctionOut> functions;
	map<const Binding*, string> symbols;
	map<string, int> used_symbols;
	map<string, string> function_symbols;
	set<string> defined_functions;
	set<string> declared_functions;
	map<string, string> string_literals;
	vector<pair<string, vector<unsigned char> > > string_defs;

	string symbol_for(const Binding* binding);
	string string_symbol(const string& token_text);
	void collect_translation_unit(const Node& root);
	void collect_node(const Node& node);
	void emit_global(const Node& node);
	string global_scalar_initializer(TypePtr type, const Node& init);
	string global_data_item(TypePtr elem, const Node& init);
	void write(const string& outfile) const;
};

class FunctionLowerer
{
public:
	FunctionLowerer(ProgramLowerer& program, const Node& fn);

	FunctionOut lower();

private:
	ProgramLowerer& program_;
	const Node& fn_;
	FunctionOut out_;
	vector<unique_ptr<Block> > blocks_;
	Block* current_;
	map<const Binding*, string> slots_;
	map<string, int> slot_names_;
	vector<string> break_targets_;
	vector<string> continue_targets_;
	map<string, string> labels_;
	map<const Node*, string> switch_labels_;
	int temp_counter_;
	int block_counter_;
	int aux_slot_counter_;

	void add_slot(const string& name, const string& type);
	string slot_for(const Binding* binding);
	string fresh_temp();
	string fresh_block(const string& prefix);
	string fresh_aux_slot(const string& prefix, const string& type);
	void start_block(const string& name);
	void instr(const string& text);
	void terminate(const string& text);

	void lower_params();
	void lower_param_stores();
	void lower_stmt(const Node& node);
	void lower_compound(const Node& node);
	void lower_decl_stmt(const Node& node);
	void lower_variable_decl(const Node& var);
	void lower_if(const Node& node);
	void lower_while(const Node& node);
	void lower_do(const Node& node);
	void lower_for(const Node& node);
	void lower_return(const Node& node);
	void lower_expr_stmt(const Node& node);
	void lower_switch(const Node& node);
	void lower_switch_items(const Node& node,
	                        vector<pair<string, const Node*> >& cases,
	                        const Node*& default_node);

	Value emit_rvalue(const Node& expr);
	Value emit_lvalue_addr(const Node& expr);
	Value emit_literal(const Node& expr);
	Value emit_id_rvalue(const Node& expr);
	Value emit_binary(const Node& expr);
	Value emit_assignment(const Node& expr);
	Value emit_unary(const Node& expr);
	Value emit_postfix(const Node& expr);
	Value emit_call(const Node& expr);
	Value emit_subscript_addr(const Node& expr);
	Value emit_cast(const Node& expr);
	Value emit_conditional(const Node& expr);
	Value emit_conditional_value(const Node& expr);
	Value convert_value(Value value, TypePtr from, TypePtr to);
	Value convert_binary_value(Value value, TypePtr from, TypePtr to);
	Value bool_value(Value value, TypePtr type);
	Value ensure_pointer(Value storage);
	void branch_logical_operand(const Node& expr, const string& yes, const string& no);
	void branch_on(const Node& expr, const string& yes, const string& no);
};


}  // namespace internal
}  // namespace pa14
