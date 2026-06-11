#include "lowir2native_mir_helpers.h"

#include <string>

using namespace std;

namespace lowir2native {

string binary_opcode(const string& op)
{
	if (op == "add") return "add";
	if (op == "sub") return "sub";
	if (op == "mul") return "imul";
	if (op == "and") return "and";
	if (op == "or") return "or";
	if (op == "xor") return "xor";
	return op;
}

string float_binary_opcode(const string& op)
{
	if (op == "add") return "add";
	if (op == "sub") return "sub";
	if (op == "mul") return "mul";
	if (op == "div") return "div";
	return op;
}

string condition_word(const string& op)
{
	if (op == "eq") return "eq";
	if (op == "ne") return "ne";
	if (op == "lt" || op == "ult") return "lt";
	if (op == "le" || op == "ule") return "le";
	if (op == "gt" || op == "ugt") return "gt";
	if (op == "ge" || op == "uge") return "ge";
	return op;
}

string condition_suffix(const string& op)
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

string branch_suffix(const string& op)
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

string float_branch_suffix(const string& op)
{
	if (op == "eq") return "e";
	if (op == "ne") return "ne";
	if (op == "lt") return "a";
	if (op == "le") return "ae";
	if (op == "gt") return "b";
	if (op == "ge") return "be";
	return branch_suffix(op);
}

}  // namespace lowir2native
