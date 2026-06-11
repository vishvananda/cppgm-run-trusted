#include "abi_mangle.h"
#include <algorithm>
#include <cctype>
#include <fstream>
#include <functional>
#include <map>
#include <sstream>
#include <stdexcept>
using namespace std;
namespace abi_mangle { namespace {
bool starts_with(const string& text, const string& prefix) { return text.compare(0, prefix.size(), prefix) == 0; }
string trim(const string& text)
{
	size_t first = 0;
	while (first < text.size() && isspace(static_cast<unsigned char>(text[first])))
		++first;
	size_t last = text.size();
	while (last > first && isspace(static_cast<unsigned char>(text[last - 1])))
		--last;
	return text.substr(first, last - first);
}
vector<string> split_words(const string& text)
{
	istringstream in(text);
	vector<string> out;
	string word;
	while (in >> word) out.push_back(word);
	return out;
}
long long parse_ll(const string& text)
{
	char* end = NULL;
	long long value = strtoll(text.c_str(), &end, 10);
	if (end == text.c_str() || *end != '\0') throw logic_error("invalid integer '" + text + "'");
	return value;
}
unsigned long long parse_ull(const string& text)
{
	char* end = NULL;
	unsigned long long value = strtoull(text.c_str(), &end, 10);
	if (end == text.c_str() || *end != '\0') throw logic_error("invalid unsigned integer '" + text + "'");
	return value;
}
bool parse_bool_word(const string& text)
{
	if (text == "yes" || text == "true") return true;
	if (text == "no" || text == "false") return false;
	throw logic_error("invalid boolean '" + text + "'");
}
bool is_builtin_name(const string& name)
{
	static const char* const names[] = {
		"void", "bool", "char", "schar", "uchar", "short", "ushort",
		"int", "uint", "long", "ulong", "longlong", "ulonglong",
		"float", "double"
	};
	for (size_t i = 0; i < sizeof(names) / sizeof(names[0]); ++i) if (name == names[i]) return true;
	return false;
}
AbiType make_ref_type(const string& name)
{
	AbiType type;
	type.kind = is_builtin_name(name) ? ABI_TYPE_BUILTIN : ABI_TYPE_NAME_OR_REFERENCE;
	type.name = name;
	return type;
}
AbiType parse_type_spec(const vector<string>& words, size_t first);
AbiType parse_type_token(const string& token);
AbiType unary_type(AbiTypeKind kind, const AbiType& base)
{
	AbiType type; type.kind = kind; type.types.push_back(base); return type;
}
AbiType parse_type_token(const string& token)
{
	if (starts_with(token, "ptr:"))
		return unary_type(ABI_TYPE_POINTER, parse_type_token(token.substr(4)));
	if (starts_with(token, "ref:"))
		return unary_type(ABI_TYPE_LVALUE_REFERENCE, parse_type_token(token.substr(4)));
	if (starts_with(token, "rref:"))
		return unary_type(ABI_TYPE_RVALUE_REFERENCE, parse_type_token(token.substr(5)));
	if (starts_with(token, "const:")) {
		AbiType type = unary_type(ABI_TYPE_CV, parse_type_token(token.substr(6)));
		type.is_const = true;
		return type;
	}
	if (starts_with(token, "volatile:")) {
		AbiType type = unary_type(ABI_TYPE_CV, parse_type_token(token.substr(9)));
		type.is_volatile = true;
		return type;
	}
	if (starts_with(token, "named:")) {
		AbiType type;
		type.kind = ABI_TYPE_NAMED;
		type.name = token.substr(6);
		return type;
	}
	if (starts_with(token, "array:")) {
		size_t colon = token.find(':', 6);
		if (colon == string::npos)
			throw logic_error("invalid array type '" + token + "'");
		AbiType type;
		type.kind = ABI_TYPE_ARRAY;
		type.array_bound.kind = ABI_ARRAY_BOUND_VALUE;
		type.array_bound.value = token.substr(6, colon - 6);
		type.types.push_back(parse_type_token(token.substr(colon + 1)));
		return type;
	}
	if (starts_with(token, "memberptr:")) {
		string rest = token.substr(10);
		size_t colon = rest.rfind(':');
		if (colon == string::npos)
			throw logic_error("invalid member pointer type '" + token + "'");
		AbiType type;
		type.kind = ABI_TYPE_MEMBER_POINTER;
		type.types.push_back(parse_type_token("named:" + rest.substr(0, colon)));
		type.types.push_back(parse_type_token(rest.substr(colon + 1)));
		return type;
	}
	return make_ref_type(token);
}
void append_arg_refs(AbiType& type, const vector<string>& words, size_t first)
{
	for (size_t i = first; i < words.size(); ++i) type.argument_refs.push_back(words[i]);
}
AbiType parse_word_type(const vector<string>& words, size_t first)
{
	if (first >= words.size())
		throw logic_error("missing type");
	const string kind = words[first];
	AbiType type;
	if (kind == "name") {
		type.kind = ABI_TYPE_NAMED;
		type.name = words.at(first + 1);
	} else if (kind == "template-param" || kind == "template-param-subst") {
		type.kind = ABI_TYPE_TEMPLATE_PARAMETER;
		type.index = static_cast<size_t>(parse_ull(words.at(first + 1)));
		type.substitutable = kind == "template-param-subst";
	} else if (kind == "const" || kind == "volatile") {
		type = unary_type(ABI_TYPE_CV, parse_type_spec(words, first + 1));
		type.is_const = kind == "const";
		type.is_volatile = kind == "volatile";
	} else if (kind == "ptr" || kind == "ref" || kind == "rref") {
		AbiTypeKind tk = kind == "ptr" ? ABI_TYPE_POINTER :
			(kind == "ref" ? ABI_TYPE_LVALUE_REFERENCE : ABI_TYPE_RVALUE_REFERENCE);
		type = unary_type(tk, parse_type_spec(words, first + 1));
	} else if (kind == "vendor") {
		type.kind = ABI_TYPE_VENDOR_QUALIFIED;
		type.name = words.at(first + 1);
		type.types.push_back(parse_type_spec(words, first + 2));
	} else if (kind == "template" || kind == "std-template") {
		type.kind = kind == "template" ? ABI_TYPE_TEMPLATE_SPECIALIZATION :
			ABI_TYPE_STD_TEMPLATE_SPECIALIZATION;
		size_t name_pos = first + 1;
		if (kind == "std-template") {
			type.standard_substitution = words.at(first + 1);
			type.standard_substitution_includes_arguments = parse_bool_word(words.at(first + 2));
			name_pos = first + 3;
		}
		type.name = words.at(name_pos);
		append_arg_refs(type, words, name_pos + 1);
	} else if (kind == "member" || kind == "member-template") {
		type.kind = kind == "member" ? ABI_TYPE_MEMBER :
			ABI_TYPE_MEMBER_TEMPLATE_SPECIALIZATION;
		type.types.push_back(parse_type_spec(vector<string>(1, words.at(first + 1)), 0));
		type.name = words.at(first + 2);
		append_arg_refs(type, words, first + 3);
	} else if (kind == "builtin-transform") {
		type.kind = ABI_TYPE_BUILTIN_TRANSFORM;
		type.name = words.at(first + 1);
		type.types.push_back(parse_type_spec(words, first + 2));
	} else if (kind == "decltype") {
		type.kind = ABI_TYPE_DECLTYPE_EXPRESSION;
		type.expression_ref = words.at(first + 1);
	} else if (kind == "lambda-closure") {
		type.kind = ABI_TYPE_LAMBDA_CLOSURE;
		type.context_ref = words.at(first + 1);
		type.discriminator = words.at(first + 2);
		for (size_t i = first + 3; i < words.size(); ++i)
			type.types.push_back(parse_type_token(words[i]));
	} else if (kind == "local-type") {
		type.kind = ABI_TYPE_LOCAL_TYPE;
		type.context_ref = words.at(first + 1);
		type.name = words.at(first + 2);
		type.discriminator = words.at(first + 3);
	} else if (kind == "function-type-variadic") {
		type.kind = ABI_TYPE_FUNCTION;
		type.variadic = true;
		for (size_t i = first + 1; i < words.size(); ++i)
			type.types.push_back(parse_type_token(words[i]));
	} else {
		throw logic_error("unknown type kind '" + kind + "'");
	}
	return type;
}
AbiType parse_type_spec(const vector<string>& words, size_t first)
{
	return first + 1 == words.size() ? parse_type_token(words[first]) : parse_word_type(words, first);
}
AbiTemplateArgument parse_template_argument(const vector<string>& words, size_t first)
{
	AbiTemplateArgument arg;
	const string kind = words.at(first);
	if (kind == "type") {
		arg.kind = ABI_TEMPLATE_ARGUMENT_TYPE;
		arg.type = parse_type_spec(words, first + 1);
	} else if (kind == "dependent-value") {
		arg.kind = ABI_TEMPLATE_ARGUMENT_DEPENDENT_VALUE;
		arg.type = parse_type_spec(vector<string>(1, words.at(first + 1)), 0);
		arg.value_type = parse_type_spec(vector<string>(1, words.at(first + 2)), 0);
		arg.value = parse_ll(words.at(first + 3));
	} else if (kind == "expression") {
		arg.kind = ABI_TEMPLATE_ARGUMENT_EXPRESSION;
		arg.entity_ref = words.at(first + 1);
	} else if (kind == "template-param-template") {
		arg.kind = ABI_TEMPLATE_ARGUMENT_TEMPLATE_PARAMETER_TEMPLATE;
		arg.index = static_cast<size_t>(parse_ull(words.at(first + 1)));
	} else if (kind == "entity-address") {
		arg.kind = ABI_TEMPLATE_ARGUMENT_ENTITY;
		arg.address_of = true;
		arg.entity_ref = words.at(first + 1);
	} else if (kind == "member-template-entity") {
		arg.kind = ABI_TEMPLATE_ARGUMENT_MEMBER_TEMPLATE_ENTITY;
		arg.owner_type = parse_type_token(words.at(first + 1));
		arg.name = words.at(first + 2);
		arg.substitution = words.at(first + 3);
	} else if (kind == "template-entity") {
		arg.kind = ABI_TEMPLATE_ARGUMENT_TEMPLATE_ENTITY;
		arg.name = words.at(first + 1);
	} else if (kind == "member-external-address") {
		arg.kind = ABI_TEMPLATE_ARGUMENT_MEMBER_EXTERNAL_ENTITY;
		arg.address_of = true;
		arg.symbol = words.at(first + 1);
		arg.owner_type = parse_type_token(words.at(first + 2));
		arg.name = words.at(first + 3);
		arg.member_is_function = parse_bool_word(words.at(first + 4));
		arg.member_function_const = parse_bool_word(words.at(first + 5)); arg.member_function_volatile = parse_bool_word(words.at(first + 6));
		arg.member_function_lvalue_ref = parse_bool_word(words.at(first + 7)); arg.member_function_rvalue_ref = parse_bool_word(words.at(first + 8));
		arg.member_function_variadic = parse_bool_word(words.at(first + 9));
		for (size_t i = first + 10; i < words.size(); ++i)
			arg.parameter_types.push_back(parse_type_token(words[i]));
	} else {
		throw logic_error("unknown template argument kind '" + kind + "'");
	}
	return arg;
}
AbiDependentExpression parse_expression(const vector<string>& words, size_t first)
{
	AbiDependentExpression expr;
	const string kind = words.at(first);
	if (kind == "template-param") {
		expr.kind = ABI_EXPRESSION_TEMPLATE_PARAMETER;
		expr.index = static_cast<size_t>(parse_ull(words.at(first + 1)));
	} else if (kind == "function-param") {
		expr.kind = ABI_EXPRESSION_FUNCTION_PARAMETER;
		expr.index = static_cast<size_t>(parse_ull(words.at(first + 1)));
	} else if (kind == "literal") {
		expr.kind = ABI_EXPRESSION_LITERAL;
		expr.value = parse_ll(words.at(first + 1));
	} else if (kind == "unary" || kind == "binary") {
		expr.kind = kind == "unary" ? ABI_EXPRESSION_UNARY : ABI_EXPRESSION_BINARY;
		expr.op = words.at(first + 1);
		expr.expression_refs.push_back(words.at(first + 2));
		if (kind == "binary")
			expr.expression_refs.push_back(words.at(first + 3));
	} else if (kind == "conditional") {
		expr.kind = ABI_EXPRESSION_CONDITIONAL;
		for (size_t i = first + 1; i < first + 4; ++i)
			expr.expression_refs.push_back(words.at(i));
	} else if (kind == "pack") {
		expr.kind = ABI_EXPRESSION_PACK_EXPANSION;
		expr.expression_refs.push_back(words.at(first + 1));
	} else if (kind == "call") {
		expr.kind = ABI_EXPRESSION_CALL;
		for (size_t i = first + 1; i < words.size(); ++i)
			expr.expression_refs.push_back(words[i]);
	} else if (kind == "cast") {
		expr.kind = ABI_EXPRESSION_CAST;
		expr.op = words.at(first + 1);
		expr.type = parse_type_token(words.at(first + 2));
		expr.expression_refs.push_back(words.at(first + 3));
	} else if (kind == "template-id") {
		expr.kind = ABI_EXPRESSION_TEMPLATE_ID;
		expr.text = words.at(first + 1);
		for (size_t i = first + 2; i < words.size(); ++i)
			expr.argument_refs.push_back(words[i]);
	} else if (kind == "type-trait") {
		expr.kind = ABI_EXPRESSION_TYPE_TRAIT;
		expr.text = words.at(first + 1);
		for (size_t i = first + 2; i < words.size(); ++i)
			expr.type_arguments.push_back(parse_type_token(words[i]));
	} else if (kind == "sizeof-type") {
		expr.kind = ABI_EXPRESSION_SIZEOF_TYPE;
		expr.type = parse_type_spec(words, first + 1);
	} else if (kind == "member") {
		expr.kind = ABI_EXPRESSION_MEMBER;
		expr.type = parse_type_token(words.at(first + 1));
		expr.close_member_owner = parse_bool_word(words.at(first + 2));
		expr.text = words.at(first + 3);
	} else if (kind == "object-member") {
		expr.kind = ABI_EXPRESSION_OBJECT_MEMBER;
		expr.op = words.at(first + 1);
		expr.expression_refs.push_back(words.at(first + 2));
		expr.text = words.at(first + 3);
		for (size_t i = first + 4; i < words.size(); ++i)
			expr.argument_refs.push_back(words[i]);
	} else {
		throw logic_error("unknown expression kind '" + kind + "'");
	}
	return expr;
}
AbiFunctionTarget parse_function_target(const vector<string>& words, size_t first)
{
	AbiFunctionTarget target;
	string kind = words.at(first);
	if (kind == "path") {
		target.kind = ABI_FUNCTION_TARGET_PATH;
		target.qualified_name = words.at(first + 1);
		for (size_t i = first + 2; i < words.size(); ++i) {
			AbiFunctionPathOperand op;
			op.kind = ABI_FUNCTION_PATH_TEMPLATE_ARGUMENT;
			op.argument_ref = words[i];
			target.path_operands.push_back(op);
		}
	} else if (kind == "encoding") {
		target.kind = ABI_FUNCTION_TARGET_ENCODING;
	} else if (kind == "local") {
		target.kind = ABI_FUNCTION_TARGET_LOCAL;
		target.context_ref = words.at(first + 1);
		target.source_name = words.at(first + 2);
		target.terminal = words.at(first + 3);
		target.discriminator = words.at(first + 4);
	} else if (kind == "lambda") {
		target.kind = ABI_FUNCTION_TARGET_LAMBDA;
		target.context_ref = words.at(first + 1);
		target.discriminator = words.at(first + 2);
		target.terminal = words.at(first + 3);
		for (size_t i = first + 4; i < words.size(); ++i)
			target.signature_parameter_types.push_back(parse_type_token(words[i]));
	} else {
		target.kind = ABI_FUNCTION_TARGET_PATH;
		target.qualified_name = words.at(first);
		for (size_t i = first + 1; i < words.size(); ++i)
			target.signature_parameter_types.push_back(parse_type_token(words[i]));
	}
	return target;
}
AbiFactRecord parse_name_source_record(const string& line)
{
	AbiFactRecord record;
	record.kind = ABI_FACT_RECORD_FUNCTION;
	record.function.kind = ABI_FUNCTION_RECORD_NAME_SOURCE;
	string rest = line.substr(string("name-source").size());
	if (!rest.empty() && rest[0] == ' ')
		rest.erase(rest.begin());
	if (!rest.empty() && rest[0] == ' ') {
		record.function.source_name = "";
		record.function.substitution = trim(rest);
		return record;
	}
	vector<string> words = split_words(rest);
	record.function.source_name = words.empty() ? "" : words[0];
	record.function.substitution = words.size() > 1 ? words[1] : "-";
	return record;
}
AbiFactRecord parse_function_record(const vector<string>& words, const string& line)
{
	if (words[0] == "name-source")
		return parse_name_source_record(line);
	AbiFactRecord record;
	record.kind = ABI_FACT_RECORD_FUNCTION;
	if (words[0] == "name-std") {
		record.function.kind = ABI_FUNCTION_RECORD_NAME_STD;
	} else if (words[0] == "name-template") {
		record.function.kind = ABI_FUNCTION_RECORD_NAME_TEMPLATE;
		record.function.source_name = words.at(1);
		record.function.substitution = words.at(2);
		record.function.complete_substitution = words.at(3);
		record.function.standard_substitution = words.at(4);
		record.function.standard_substitution_includes_arguments = parse_bool_word(words.at(5));
		for (size_t i = 6; i < words.size(); ++i)
			record.function.argument_refs.push_back(words[i]);
	} else if (words[0] == "function-template-arg") {
		record.function.kind = ABI_FUNCTION_RECORD_FUNCTION_TEMPLATE_ARGUMENT;
		record.function.name = words.at(1);
	} else if (words[0] == "function-template-prefix") {
		record.function.kind = ABI_FUNCTION_RECORD_FUNCTION_TEMPLATE_PREFIX;
		record.function.name = words.at(1);
	} else if (words[0] == "local-context" || words[0] == "lambda-context") {
		record.function.kind = words[0] == "local-context" ?
			ABI_FUNCTION_RECORD_LOCAL_CONTEXT : ABI_FUNCTION_RECORD_LAMBDA_CONTEXT;
		record.function.context_ref = words.at(1);
		if (words[0] == "local-context") {
			record.function.source_name = words.at(2);
			record.function.discriminator = words.at(3);
			for (size_t i = 4; i < words.size(); ++i)
				record.function.types.push_back(parse_type_token(words[i]));
		} else {
			record.function.discriminator = words.at(2);
			for (size_t i = 3; i < words.size(); ++i)
				record.function.types.push_back(parse_type_token(words[i]));
		}
	} else if (words[0] == "terminal-source" || words[0] == "terminal") {
		record.function.kind = words[0] == "terminal-source" ?
			ABI_FUNCTION_RECORD_TERMINAL_SOURCE : ABI_FUNCTION_RECORD_TERMINAL;
		record.function.terminal = words.at(1);
	} else if (words[0] == "operator-terminal") {
		record.function.kind = ABI_FUNCTION_RECORD_OPERATOR_TERMINAL;
		record.function.terminal = words.at(1);
		if (words.size() > 2)
			record.function.literal_suffix = words.at(2);
	} else if (words[0] == "conversion-terminal") {
		record.function.kind = ABI_FUNCTION_RECORD_CONVERSION_TERMINAL;
		record.function.type = parse_type_spec(words, 1);
	} else if (words[0] == "param" || words[0] == "result") {
		record.function.kind = words[0] == "param" ?
			ABI_FUNCTION_RECORD_PARAMETER : ABI_FUNCTION_RECORD_RESULT;
		record.function.type = parse_type_spec(words, 1);
	} else if (words[0] == "variadic") {
		record.function.kind = ABI_FUNCTION_RECORD_VARIADIC;
	} else if (words[0] == "abi-tag") {
		record.function.kind = ABI_FUNCTION_RECORD_ABI_TAG;
		record.function.name = words.at(1);
	} else if (words[0] == "function-qualifier") {
		record.function.kind = ABI_FUNCTION_RECORD_QUALIFIER;
		if (words.at(1) == "const")
			record.function.qualifiers.push_back(ABI_FUNCTION_QUALIFIER_CONST);
		else if (words.at(1) == "volatile")
			record.function.qualifiers.push_back(ABI_FUNCTION_QUALIFIER_VOLATILE);
		else if (words.at(1) == "lvalue-ref" || words.at(1) == "ref") record.function.qualifiers.push_back(ABI_FUNCTION_QUALIFIER_LVALUE_REFERENCE);
		else if (words.at(1) == "rvalue-ref" || words.at(1) == "rref") record.function.qualifiers.push_back(ABI_FUNCTION_QUALIFIER_RVALUE_REFERENCE);
		else
			throw logic_error("unknown function qualifier '" + words.at(1) + "'");
	}
	return record;
}
AbiFactRecord parse_fact_record_line(const string& line);
AbiFactRecord parse_definition_record(const vector<string>& words)
{
	AbiFactRecord record;
	record.kind = ABI_FACT_RECORD_DEFINITION;
	record.definition.id = words.at(1);
	if (words[0] == "let-type") {
		record.definition.kind = ABI_DEFINITION_TYPE;
		record.definition.type = parse_type_spec(words, 2);
	} else if (words[0] == "let-arg") {
		record.definition.kind = ABI_DEFINITION_TEMPLATE_ARGUMENT;
		record.definition.template_argument = parse_template_argument(words, 2);
	} else if (words[0] == "let-expr") {
		record.definition.kind = ABI_DEFINITION_EXPRESSION;
		record.definition.expression = parse_expression(words, 2);
	} else if (words[0] == "let-context") {
		record.definition.kind = ABI_DEFINITION_CONTEXT;
		if (words.at(2) == "raw") {
			record.definition.context.kind = ABI_CONTEXT_RAW;
			record.definition.context.fragment = words.at(3);
		} else if (words.at(2) == "function") {
			record.definition.context.kind = ABI_CONTEXT_FUNCTION;
			record.definition.context.function = parse_function_target(words, 3);
		} else
			throw logic_error("unknown context kind '" + words.at(2) + "'");
	} else if (words[0] == "let-entity") {
		record.definition.kind = ABI_DEFINITION_ENTITY;
		if (words.at(2) == "symbol") {
			record.definition.entity.kind = ABI_ENTITY_FACT_SYMBOL;
			record.definition.entity.qualified_name = words.at(3);
		} else if (words.at(2) == "function") {
			record.definition.entity.kind = ABI_ENTITY_FACT_FUNCTION;
			record.definition.entity.function = parse_function_target(words, 3);
		} else if (words.at(2) == "variable") {
			record.definition.entity.kind = ABI_ENTITY_FACT_VARIABLE;
			record.definition.entity.qualified_name = words.at(3);
		} else
			throw logic_error("unknown entity kind '" + words.at(2) + "'");
	} else
		throw logic_error("unknown definition kind '" + words[0] + "'");
	return record;
}
AbiFactRecord parse_target_record(const vector<string>& words)
{
	AbiFactRecord record;
	record.kind = ABI_FACT_RECORD_TARGET;
	if (words[0] == "c-function" || words[0] == "function") {
		record.target.kind = ABI_TARGET_FACT_FUNCTION;
		record.target.c_linkage = words[0] == "c-function";
		record.target.function = parse_function_target(words, 1);
	} else if (words[0] == "type") {
		record.target.kind = ABI_TARGET_FACT_TYPE;
		record.target.type = parse_type_spec(words, 1);
	} else if (words[0] == "variable") {
		record.target.kind = ABI_TARGET_FACT_VARIABLE;
		record.target.qualified_name = words.at(1);
	} else if (words[0] == "typeinfo" || words[0] == "vtable" || words[0] == "vtt") {
		record.target.kind = words[0] == "typeinfo" ? ABI_TARGET_FACT_TYPEINFO :
			(words[0] == "vtable" ? ABI_TARGET_FACT_VTABLE : ABI_TARGET_FACT_VTT);
		record.target.type = parse_type_spec(words, 1);
	} else if (words[0] == "construction-vtable") {
		record.target.kind = ABI_TARGET_FACT_CONSTRUCTION_VTABLE;
		record.target.type = parse_type_token(words.at(1));
		record.target.base_offset = parse_ull(words.at(2));
		record.target.base_type = parse_type_token(words.at(3));
	} else if (words[0] == "tls-wrapper") {
		if (words.at(1) != "variable") throw logic_error("tls-wrapper target must name a variable");
		record.target.kind = ABI_TARGET_FACT_THREAD_LOCAL_WRAPPER;
		record.target.qualified_name = words.at(2);
	} else if (words[0] == "thunk" || words[0] == "virtual-base-thunk") {
		record.target.kind = words[0] == "thunk" ? ABI_TARGET_FACT_THUNK :
			ABI_TARGET_FACT_VIRTUAL_BASE_THUNK;
		record.target.this_adjust = parse_ll(words.at(1));
		size_t fn_pos = 2;
		if (words[0] == "thunk" && words.at(2) != "function") {
			record.target.has_result_adjust = true;
			record.target.result_adjust = parse_ll(words.at(2));
			fn_pos = 3;
		}
		if (words.at(fn_pos) != "function") throw logic_error("thunk target must name a function");
		vector<string> rest(words.begin() + fn_pos + 1, words.end());
		record.target.function = parse_function_target(rest, 0);
	} else
		throw logic_error("unknown target kind '" + words[0] + "'");
	return record;
}
bool is_function_record_keyword(const string& word)
{
	static const char* const names[] = {
		"name-source", "name-std", "name-template", "function-template-arg",
		"function-template-prefix", "local-context", "lambda-context",
		"terminal-source", "terminal", "operator-terminal",
		"conversion-terminal", "param", "result", "variadic",
		"abi-tag", "function-qualifier"
	};
	for (size_t i = 0; i < sizeof(names) / sizeof(names[0]); ++i)
		if (word == names[i])
			return true;
	return false;
}
AbiFactRecord parse_fact_record_line(const string& line)
{
	vector<string> words = split_words(line);
	if (words.empty())
		throw logic_error("empty fact line");
	if (starts_with(words[0], "let-"))
		return parse_definition_record(words);
	if (is_function_record_keyword(words[0]))
		return parse_function_record(words, line);
	return parse_target_record(words);
}
vector<string> split_qualified(string name)
{
	while (starts_with(name, "::"))
		name = name.substr(2);
	vector<string> out;
	size_t pos = 0;
	while (pos <= name.size()) {
		size_t next = name.find("::", pos);
		out.push_back(name.substr(pos, next == string::npos ? string::npos : next - pos));
		if (next == string::npos)
			break;
		pos = next + 2;
	}
	return out;
}
string source_name(const string& name)
{
	return to_string(name.size()) + name;
}
string base36(size_t value)
{
	const char* digits = "0123456789ABCDEFGHIJKLMNOPQRSTUVWXYZ";
	string out;
	do { out.push_back(digits[value % 36]); value /= 36; } while (value != 0);
	reverse(out.begin(), out.end());
	return out;
}
struct Env
{
	map<string, AbiType> types;
	map<string, AbiTemplateArgument> args;
	map<string, AbiDependentExpression> exprs;
	map<string, AbiLocalContext> contexts;
	map<string, AbiEntityFact> entities;
};
struct Component
{
	string name;
	vector<string> argument_refs;
	vector<string> abi_tags;
	bool is_std = false;
	bool is_operator = false;
	bool is_conversion = false;
	bool is_ctor_dtor = false;
	bool unary_operator = false;
	AbiType conversion_type;
	string terminal;
	string literal_suffix;
};
size_t explicit_parameter_count(const vector<AbiFunctionRecord>& records)
{
	size_t count = 0; for (size_t i = 0; i < records.size(); ++i) if (records[i].kind == ABI_FUNCTION_RECORD_PARAMETER) ++count; return count;
}
class Mangler
{
public:
	explicit Mangler(const AbiFactCase& c) : records(c.records) { build_env(); }
	string mangle_case();
private:
	const vector<AbiFactRecord>& records;
	Env env;
	vector<string> substitutions;
	map<string, size_t> substitution_index;
	void build_env();
	string encode_target(const AbiTargetRecord& target, const vector<AbiFunctionRecord>& fn_records);
	string encode_function(const AbiFunctionTarget& target, const vector<AbiFunctionRecord>& fn_records,
		bool prefix, bool allow_name_prefix);
	string encode_function_name(const AbiFunctionTarget& target,
		const vector<AbiFunctionRecord>& fn_records, bool allow_name_prefix);
	string encode_path_name(const string& qname, const vector<AbiFunctionPathOperand>& operands,
		const vector<AbiFunctionRecord>& fn_records, bool allow_name_prefix);
	string encode_encoding_name(const vector<AbiFunctionRecord>& fn_records, bool allow_name_prefix);
	string encode_local_name(const string& context_ref, const string& entity, const string& discriminator);
	string encode_lambda_entity(const string& context_ref, const string& discriminator, const vector<AbiType>& params);
	string encode_context_fragment(const string& context_ref);
	string encode_signature(const AbiFunctionTarget& target, const vector<AbiFunctionRecord>& fn_records);
	string encode_type(const AbiType& type);
	string encode_type_ref(const string& name);
	string encode_template_arg_ref(const string& name);
	string encode_template_arg(const AbiTemplateArgument& arg);
	string encode_expression_ref(const string& name);
	string encode_expression(const AbiDependentExpression& expr);
	string encode_entity_symbol(const string& ref);
	string encode_unscoped_or_nested(const vector<Component>& comps, const string& qualifier_prefix,
		bool allow_initial_prefix = true);
	string encode_component(const Component& comp);
	string encode_template_args(const vector<string>& refs);
	string encode_nested_member(const AbiType& owner, const Component& member);
	string encode_qualified_name(const string& qname);
	string type_key(const AbiType& type) const;
	string arg_key(const AbiTemplateArgument& arg) const;
	string operator_code(const string& name, bool unary) const;
	string terminal_code(const string& name) const;
	string builtin_code(const string& name) const;
	string substitution_code(size_t index) const;
	string substitute(const string& key, const function<string()>& emit);
	void add_substitution(const string& key, const string& encoded);
};
void Mangler::build_env()
{
	for (size_t i = 0; i < records.size(); ++i) {
		if (records[i].kind != ABI_FACT_RECORD_DEFINITION)
			continue;
		const AbiDefinitionRecord& def = records[i].definition;
		if (def.kind == ABI_DEFINITION_TYPE)
			env.types[def.id] = def.type;
		else if (def.kind == ABI_DEFINITION_TEMPLATE_ARGUMENT)
			env.args[def.id] = def.template_argument;
		else if (def.kind == ABI_DEFINITION_EXPRESSION)
			env.exprs[def.id] = def.expression;
		else if (def.kind == ABI_DEFINITION_CONTEXT)
			env.contexts[def.id] = def.context;
		else
			env.entities[def.id] = def.entity;
	}
}
string Mangler::mangle_case()
{
	const AbiTargetRecord* target = NULL;
	vector<AbiFunctionRecord> fn_records;
	for (size_t i = 0; i < records.size(); ++i) {
		if (records[i].kind == ABI_FACT_RECORD_TARGET) {
			if (target != NULL)
				throw logic_error("case has multiple targets");
			target = &records[i].target;
		} else if (records[i].kind == ABI_FACT_RECORD_FUNCTION)
			fn_records.push_back(records[i].function);
	}
	if (target == NULL)
		throw logic_error("case has no target");
	return encode_target(*target, fn_records);
}
string Mangler::substitution_code(size_t index) const
{
	if (index == 0)
		return "S_";
	return "S" + base36(index - 1) + "_";
}
void Mangler::add_substitution(const string& key, const string&)
{
	if (key.empty() || substitution_index.count(key) != 0)
		return;
	substitution_index[key] = substitutions.size();
	substitutions.push_back(key);
}
string Mangler::substitute(const string& key, const function<string()>& emit)
{
	map<string, size_t>::const_iterator found = substitution_index.find(key);
	if (found != substitution_index.end())
		return substitution_code(found->second);
	string encoded = emit();
	add_substitution(key, encoded);
	return encoded;
}
string Mangler::builtin_code(const string& name) const
{
	struct Code { const char* name; const char* code; };
	static const Code codes[] = {
		{"void", "v"}, {"bool", "b"}, {"char", "c"}, {"schar", "a"}, {"uchar", "h"},
		{"short", "s"}, {"ushort", "t"}, {"int", "i"}, {"uint", "j"}, {"long", "l"},
		{"ulong", "m"}, {"longlong", "x"}, {"ulonglong", "y"}, {"float", "f"}, {"double", "d"}
	};
	for (size_t i = 0; i < sizeof(codes) / sizeof(codes[0]); ++i)
		if (name == codes[i].name)
			return codes[i].code;
	throw logic_error("unknown builtin type '" + name + "'");
}
string Mangler::operator_code(const string& name, bool unary) const
{
	if (name == "plus") return unary ? "ps" : "pl";
	if (name == "minus") return unary ? "ng" : "mi";
	struct Code { const char* name; const char* code; };
	static const Code codes[] = {
		{"new", "nw"}, {"new-array", "na"}, {"delete", "dl"}, {"delete-array", "da"},
		{"call", "cl"}, {"operator-call", "cl"}, {"binary-plus", "pl"}, {"unary-plus", "ps"},
		{"binary-minus", "mi"}, {"unary-minus", "ng"}, {"address-of", "ad"}, {"bit-and", "an"},
		{"deref", "de"}, {"multiply", "ml"}, {"divide", "dv"}, {"remainder", "rm"},
		{"bit-or", "or"}, {"bit-xor", "eo"}, {"assign", "aS"}, {"plus-assign", "pL"}, {"minus-assign", "mI"}, {"multiply-assign", "mL"},
		{"divide-assign", "dV"}, {"remainder-assign", "rM"}, {"bit-and-assign", "aN"}, {"bit-or-assign", "oR"}, {"bit-xor-assign", "eO"},
		{"left-shift", "ls"}, {"right-shift", "rs"}, {"left-shift-assign", "lS"}, {"right-shift-assign", "rS"}, {"equal", "eq"},
		{"not-equal", "ne"}, {"less", "lt"}, {"greater", "gt"}, {"less-equal", "le"}, {"greater-equal", "ge"}, {"three-way", "ss"},
		{"logical-and", "aa"}, {"logical-or", "oo"}, {"logical-not", "nt"},
		{"increment", "pp"}, {"decrement", "mm"}, {"comma", "cm"},
		{"member-pointer", "pm"}, {"arrow", "pt"}, {"index", "ix"}
	};
	for (size_t i = 0; i < sizeof(codes) / sizeof(codes[0]); ++i)
		if (name == codes[i].name)
			return codes[i].code;
	throw logic_error("unknown operator terminal '" + name + "'");
}
string Mangler::terminal_code(const string& name) const
{
	struct Code { const char* name; const char* code; };
	static const Code codes[] = {
		{"constructor-complete", "C1"}, {"constructor-base", "C2"},
		{"constructor-allocating", "C3"}, {"destructor-deleting", "D0"},
		{"destructor-complete", "D1"}, {"destructor-base", "D2"}
	};
	for (size_t i = 0; i < sizeof(codes) / sizeof(codes[0]); ++i)
		if (name == codes[i].name)
			return codes[i].code;
	throw logic_error("unknown special terminal '" + name + "'");
}
string Mangler::type_key(const AbiType& type) const
{
	if (type.kind == ABI_TYPE_NAME_OR_REFERENCE) {
		map<string, AbiType>::const_iterator found = env.types.find(type.name);
		if (found != env.types.end())
			return "ref:" + type_key(found->second);
	}
	ostringstream out;
	out << type.kind << ':' << type.name << ':' << type.index << ':' << type.substitution
	    << ':' << type.standard_substitution << ':' << type.is_const << ':' << type.is_volatile
	    << ':' << type.variadic << ':' << type.expression_ref << ':' << type.context_ref
	    << ':' << type.discriminator << ':' << type.array_bound.value;
	for (size_t i = 0; i < type.types.size(); ++i)
		out << '[' << type_key(type.types[i]) << ']';
	for (size_t i = 0; i < type.argument_refs.size(); ++i)
	{
		map<string, AbiTemplateArgument>::const_iterator found = env.args.find(type.argument_refs[i]);
		out << '<' << (found == env.args.end() ? type.argument_refs[i] : arg_key(found->second)) << '>';
	}
	return out.str();
}
string Mangler::arg_key(const AbiTemplateArgument& arg) const
{
	ostringstream out;
	out << arg.kind << ':' << arg.name << ':' << arg.entity_ref << ':' << arg.symbol
	    << ':' << arg.value << ':' << arg.index << ':' << type_key(arg.type)
	    << ':' << type_key(arg.value_type) << ':' << type_key(arg.owner_type);
	for (size_t i = 0; i < arg.argument_refs.size(); ++i)
		out << '<' << arg.argument_refs[i] << '>';
	return out.str();
}
string Mangler::encode_type_ref(const string& name)
{
	map<string, AbiType>::const_iterator found = env.types.find(name);
	if (found != env.types.end())
		return encode_type(found->second);
	return encode_type(parse_type_token(name));
}
string Mangler::encode_template_arg_ref(const string& name)
{
	map<string, AbiTemplateArgument>::const_iterator found = env.args.find(name);
	if (found == env.args.end())
		throw logic_error("unknown template argument '" + name + "'");
	return encode_template_arg(found->second);
}
string Mangler::encode_expression_ref(const string& name)
{
	map<string, AbiDependentExpression>::const_iterator found = env.exprs.find(name);
	if (found == env.exprs.end())
		throw logic_error("unknown expression '" + name + "'");
	return encode_expression(found->second);
}
string Mangler::encode_template_args(const vector<string>& refs)
{
	string out = "I";
	for (size_t i = 0; i < refs.size(); ++i)
		out += encode_template_arg_ref(refs[i]);
	out += "E";
	return out;
}
string Mangler::encode_qualified_name(const string& qname)
{
	vector<Component> comps;
	vector<string> parts = split_qualified(qname);
	for (size_t i = 0; i < parts.size(); ++i) {
		Component comp;
		comp.name = parts[i];
		comp.is_std = i == 0 && parts[i] == "std";
		comps.push_back(comp);
	}
	return encode_unscoped_or_nested(comps, "");
}
string Mangler::encode_component(const Component& comp)
{
	if (comp.is_std)
		return "St";
	string base;
	if (comp.is_operator && comp.terminal == "literal")
		base = "li" + source_name(comp.literal_suffix);
	else if (comp.is_operator)
		base = operator_code(comp.terminal, comp.unary_operator);
	else if (comp.is_conversion)
		base = "cv" + encode_type(comp.conversion_type);
	else if (comp.is_ctor_dtor)
		base = terminal_code(comp.terminal);
	else
		base = source_name(comp.name);
	for (size_t i = 0; i < comp.abi_tags.size(); ++i)
		base += "B" + source_name(comp.abi_tags[i]);
	if (!comp.argument_refs.empty())
		base += encode_template_args(comp.argument_refs);
	return base;
}
string Mangler::encode_unscoped_or_nested(const vector<Component>& comps, const string& qualifier_prefix,
	bool allow_initial_prefix)
{
	if (comps.empty())
		return "";
	if (comps.size() == 1 && qualifier_prefix.empty()) {
		if (allow_initial_prefix && !comps[0].argument_refs.empty())
			add_substitution("name:" + comps[0].name, "");
		string encoded = encode_component(comps[0]);
		return encoded;
	}
	if (comps.size() == 2 && qualifier_prefix.empty() && comps[0].is_std) {
		return "St" + encode_component(comps[1]);
	}
	string out = "N" + qualifier_prefix;
	string prefix_key;
	size_t start = 0;
	if (allow_initial_prefix) {
		for (size_t len = comps.size() - 1; len > 0; --len) {
			string key;
			for (size_t i = 0; i < len; ++i) {
				if (i != 0)
					key += "::";
				key += comps[i].is_std ? "std" : comps[i].name;
			}
			map<string, size_t>::const_iterator found = substitution_index.find("name:" + key);
			if (found != substitution_index.end()) {
				out += substitution_code(found->second);
				prefix_key = key;
				start = len;
				break;
			}
		}
	}
	for (size_t i = start; i < comps.size(); ++i) {
		string next_prefix = comps[i].is_std ? "std" :
			(prefix_key.empty() ? comps[i].name : prefix_key + "::" + comps[i].name);
		if (!comps[i].argument_refs.empty() && !comps[i].name.empty())
			add_substitution("name:" + next_prefix, "");
		string encoded = encode_component(comps[i]);
		out += encoded;
		if (comps[i].is_std)
			prefix_key = "std";
		else
			prefix_key = next_prefix;
		if (!comps[i].is_ctor_dtor && !(comps[i].is_std && prefix_key == "std"))
			add_substitution("name:" + prefix_key, out.substr(1 + qualifier_prefix.size()));
	}
	out += "E";
	return out;
}
string Mangler::encode_type(const AbiType& type)
{
	if (type.kind == ABI_TYPE_NAME_OR_REFERENCE)
		return encode_type_ref(type.name);
	if (type.kind == ABI_TYPE_BUILTIN)
		return builtin_code(type.name);
	if (type.kind == ABI_TYPE_NAMED) {
		map<string, size_t>::const_iterator named = substitution_index.find("name:" + type.name);
		if (named != substitution_index.end())
			return substitution_code(named->second);
		string encoded = encode_qualified_name(type.name);
		if (split_qualified(type.name).size() == 1)
			add_substitution("name:" + type.name, encoded);
		return encoded;
	}
	if (type.kind == ABI_TYPE_TEMPLATE_PARAMETER) {
		string text = type.index == 0 ? "T_" : "T" + base36(type.index - 1) + "_";
		if (type.substitutable)
			return substitute("type:tparam:" + to_string(type.index), [&]() { return text; });
		return text;
	}
	if (type.kind == ABI_TYPE_CV) {
		string prefix = type.is_const ? "K" : "";
		if (type.is_volatile)
			prefix += "V";
		return substitute("type:cv:" + type_key(type), [&]() { return prefix + encode_type(type.types[0]); });
	}
	if (type.kind == ABI_TYPE_POINTER || type.kind == ABI_TYPE_LVALUE_REFERENCE ||
	    type.kind == ABI_TYPE_RVALUE_REFERENCE) {
		string code = type.kind == ABI_TYPE_POINTER ? "P" :
			(type.kind == ABI_TYPE_LVALUE_REFERENCE ? "R" : "O");
		return substitute("type:unary:" + type_key(type), [&]() { return code + encode_type(type.types[0]); });
	}
	if (type.kind == ABI_TYPE_ARRAY) {
		return substitute("type:array:" + type_key(type), [&]() {
			return "A" + type.array_bound.value + "_" + encode_type(type.types[0]);
		});
	}
	if (type.kind == ABI_TYPE_MEMBER_POINTER) {
		return substitute("type:memberptr:" + type_key(type), [&]() {
			return "M" + encode_type(type.types[0]) + encode_type(type.types[1]);
		});
	}
	if (type.kind == ABI_TYPE_FUNCTION) {
		return substitute("type:function:" + type_key(type), [&]() {
			string out = "F" + encode_type(type.types[0]);
			for (size_t i = 1; i < type.types.size(); ++i)
				out += encode_type(type.types[i]);
			if (type.variadic)
				out += "z";
			out += "E";
			return out;
		});
	}
	if (type.kind == ABI_TYPE_VENDOR_QUALIFIED) {
		return substitute("type:vendor:" + type_key(type), [&]() {
			return "U" + source_name(type.name) + encode_type(type.types[0]);
		});
	}
	if (type.kind == ABI_TYPE_BUILTIN_TRANSFORM) {
		return substitute("type:transform:" + type_key(type), [&]() {
			return "u" + source_name(type.name) + "I" + encode_type(type.types[0]) + "E";
		});
	}
	if (type.kind == ABI_TYPE_TEMPLATE_SPECIALIZATION ||
	    type.kind == ABI_TYPE_STD_TEMPLATE_SPECIALIZATION) {
		return substitute("type:template:" + type_key(type), [&]() {
			if (type.kind == ABI_TYPE_STD_TEMPLATE_SPECIALIZATION &&
			    !type.standard_substitution.empty() &&
			    type.standard_substitution != "-")
				return type.standard_substitution +
					(type.standard_substitution_includes_arguments ? "" : encode_template_args(type.argument_refs));
			map<string, size_t>::const_iterator primary =
				substitution_index.find("name:" + type.name);
			if (primary != substitution_index.end() && !type.argument_refs.empty()) {
				string text = substitution_code(primary->second) +
					encode_template_args(type.argument_refs);
				return split_qualified(type.name).size() == 1 ? text : "N" + text + "E";
			}
			vector<Component> comps;
			vector<string> parts = split_qualified(type.name);
			for (size_t i = 0; i < parts.size(); ++i) {
				Component comp;
				comp.name = parts[i];
				comp.is_std = i == 0 && parts[i] == "std";
				if (i + 1 == parts.size())
					comp.argument_refs = type.argument_refs;
				comps.push_back(comp);
			}
			return encode_unscoped_or_nested(comps, "");
		});
	}
	if (type.kind == ABI_TYPE_MEMBER || type.kind == ABI_TYPE_MEMBER_TEMPLATE_SPECIALIZATION) {
		Component member;
		member.name = type.name;
		member.argument_refs = type.argument_refs;
		return substitute("type:member:" + type_key(type), [&]() {
			return encode_nested_member(type.types[0], member);
		});
	}
	if (type.kind == ABI_TYPE_DECLTYPE_EXPRESSION) {
		string expr = encode_expression_ref(type.expression_ref);
		return substitute("type:decltype:" + expr,
			[&]() { return "DT" + expr + "E"; });
	}
	if (type.kind == ABI_TYPE_LAMBDA_CLOSURE)
		return substitute("type:lambda:" + type_key(type),
			[&]() { return encode_lambda_entity(type.context_ref, type.discriminator, type.types); });
	if (type.kind == ABI_TYPE_LOCAL_TYPE)
		return substitute("type:local:" + type_key(type),
			[&]() { return encode_local_name(type.context_ref, source_name(type.name), type.discriminator); });
	throw logic_error("unsupported type kind");
}
string Mangler::encode_nested_member(const AbiType& owner, const Component& member)
{
	AbiType resolved_owner = owner;
	if (owner.kind == ABI_TYPE_NAME_OR_REFERENCE) {
		map<string, AbiType>::const_iterator found = env.types.find(owner.name);
		if (found != env.types.end())
			resolved_owner = found->second;
	}
	string owner_text;
	if (resolved_owner.kind == ABI_TYPE_TEMPLATE_SPECIALIZATION ||
	    resolved_owner.kind == ABI_TYPE_STD_TEMPLATE_SPECIALIZATION) {
		map<string, size_t>::const_iterator primary =
			substitution_index.find("name:" + resolved_owner.name);
		if (primary != substitution_index.end() && !resolved_owner.argument_refs.empty()) {
			owner_text = substitution_code(primary->second) +
				encode_template_args(resolved_owner.argument_refs);
		} else {
			vector<Component> comps;
			vector<string> parts = split_qualified(resolved_owner.name);
			for (size_t i = 0; i < parts.size(); ++i) {
				Component comp;
				comp.name = parts[i];
				comp.is_std = i == 0 && parts[i] == "std";
				if (i + 1 == parts.size())
					comp.argument_refs = resolved_owner.argument_refs;
				comps.push_back(comp);
			}
			owner_text = encode_unscoped_or_nested(comps, "");
		}
	} else {
		owner_text = encode_type(owner);
	}
	string body = owner_text;
	if (starts_with(owner_text, "N") && owner_text.size() > 2 && owner_text[owner_text.size() - 1] == 'E')
		body = owner_text.substr(1, owner_text.size() - 2);
	string member_text;
	map<string, size_t>::const_iterator member_sub =
		substitution_index.find("name:" + member.name);
	if (member_sub != substitution_index.end())
		member_text = substitution_code(member_sub->second);
	else {
		member_text = encode_component(member);
		if (!member.name.empty())
			add_substitution("name:" + member.name, member_text);
	}
	return "N" + body + member_text + "E";
}
string Mangler::encode_template_arg(const AbiTemplateArgument& arg)
{
	if (arg.kind == ABI_TEMPLATE_ARGUMENT_TYPE)
		return encode_type(arg.type);
	if (arg.kind == ABI_TEMPLATE_ARGUMENT_DEPENDENT_VALUE)
		return "Tn" + encode_type(arg.type) + "L" + encode_type(arg.value_type) +
			to_string(arg.value) + "E";
	if (arg.kind == ABI_TEMPLATE_ARGUMENT_EXPRESSION)
		return "X" + encode_expression_ref(arg.entity_ref) + "E";
	if (arg.kind == ABI_TEMPLATE_ARGUMENT_TEMPLATE_PARAMETER_TEMPLATE)
		return arg.index == 0 ? "T_" : "T" + base36(arg.index - 1) + "_";
	if (arg.kind == ABI_TEMPLATE_ARGUMENT_ENTITY ||
	    arg.kind == ABI_TEMPLATE_ARGUMENT_MEMBER_EXTERNAL_ENTITY) {
		string symbol = !arg.symbol.empty() ? arg.symbol : encode_entity_symbol(arg.entity_ref);
		return "XadL" + symbol + "EE";
	}
	if (arg.kind == ABI_TEMPLATE_ARGUMENT_MEMBER_TEMPLATE_ENTITY) {
		Component member;
		member.name = arg.name;
		return encode_nested_member(arg.owner_type, member);
	}
	if (arg.kind == ABI_TEMPLATE_ARGUMENT_TEMPLATE_ENTITY)
		return encode_qualified_name(arg.name);
	throw logic_error("unsupported template argument");
}
string Mangler::encode_entity_symbol(const string& ref)
{
	if (ref.empty())
		return "";
	map<string, AbiEntityFact>::const_iterator found = env.entities.find(ref);
	if (found == env.entities.end())
		throw logic_error("unknown entity '" + ref + "'");
	if (found->second.kind == ABI_ENTITY_FACT_SYMBOL)
		return found->second.qualified_name;
	if (found->second.kind == ABI_ENTITY_FACT_VARIABLE)
		return "_Z" + encode_qualified_name(found->second.qualified_name);
	return encode_function(found->second.function, vector<AbiFunctionRecord>(), true, false);
}
string Mangler::encode_expression(const AbiDependentExpression& expr)
{
	if (expr.kind == ABI_EXPRESSION_TEMPLATE_PARAMETER)
		return expr.index == 0 ? "T_" : "T" + base36(expr.index - 1) + "_";
	if (expr.kind == ABI_EXPRESSION_FUNCTION_PARAMETER)
		return expr.index == 0 ? "fp_" : "fp" + base36(expr.index - 1) + "_";
	if (expr.kind == ABI_EXPRESSION_LITERAL)
		return "Li" + to_string(expr.value) + "E";
	if (expr.kind == ABI_EXPRESSION_UNARY)
		return expr.op + encode_expression_ref(expr.expression_refs[0]);
	if (expr.kind == ABI_EXPRESSION_BINARY)
		return expr.op + encode_expression_ref(expr.expression_refs[0]) +
			encode_expression_ref(expr.expression_refs[1]);
	if (expr.kind == ABI_EXPRESSION_CONDITIONAL)
		return "qu" + encode_expression_ref(expr.expression_refs[0]) +
			encode_expression_ref(expr.expression_refs[1]) +
			encode_expression_ref(expr.expression_refs[2]);
	if (expr.kind == ABI_EXPRESSION_PACK_EXPANSION)
		return "sp" + encode_expression_ref(expr.expression_refs[0]);
	if (expr.kind == ABI_EXPRESSION_CALL) {
		string out = "cl";
		for (size_t i = 0; i < expr.expression_refs.size(); ++i)
			out += encode_expression_ref(expr.expression_refs[i]);
		return out + "E";
	}
	if (expr.kind == ABI_EXPRESSION_CAST)
		return expr.op + encode_type(expr.type) + encode_expression_ref(expr.expression_refs[0]);
	if (expr.kind == ABI_EXPRESSION_TEMPLATE_ID) {
		string out = source_name(expr.text);
		vector<string> refs = expr.argument_refs;
		out += encode_template_args(refs);
		return out;
	}
	if (expr.kind == ABI_EXPRESSION_TYPE_TRAIT) {
		string out = "u" + source_name(expr.text);
		for (size_t i = 0; i < expr.type_arguments.size(); ++i)
			out += encode_type(expr.type_arguments[i]);
		return out + "E";
	}
	if (expr.kind == ABI_EXPRESSION_SIZEOF_TYPE)
		return "st" + encode_type(expr.type);
	if (expr.kind == ABI_EXPRESSION_MEMBER) {
		string owner = encode_type(expr.type);
		return "sr" + owner + (expr.close_member_owner ? "E" : "") + source_name(expr.text);
	}
	if (expr.kind == ABI_EXPRESSION_OBJECT_MEMBER) {
		string out = expr.op + encode_expression_ref(expr.expression_refs[0]) + source_name(expr.text);
		if (!expr.argument_refs.empty())
			out += encode_template_args(expr.argument_refs);
		return out;
	}
	throw logic_error("unsupported expression kind");
}
string Mangler::encode_context_fragment(const string& context_ref)
{
	map<string, AbiLocalContext>::const_iterator found = env.contexts.find(context_ref);
	if (found == env.contexts.end())
		throw logic_error("unknown context '" + context_ref + "'");
	if (found->second.kind == ABI_CONTEXT_RAW)
		return found->second.fragment;
	string full = encode_function(found->second.function, vector<AbiFunctionRecord>(), false, true);
	return "Z" + full + "E";
}
string Mangler::encode_local_name(const string& context_ref, const string& entity, const string&)
{
	return encode_context_fragment(context_ref) + entity;
}
string Mangler::encode_lambda_entity(const string& context_ref, const string& discriminator, const vector<AbiType>& params)
{
	string out = encode_context_fragment(context_ref) + "Ul";
	for (size_t i = 0; i < params.size(); ++i)
		out += encode_type(params[i]);
	if (params.empty())
		out += "v";
	out += "E" + discriminator + "_";
	return out;
}
string Mangler::encode_path_name(const string& qname, const vector<AbiFunctionPathOperand>& operands,
	const vector<AbiFunctionRecord>& fn_records, bool allow_name_prefix)
{
	vector<string> parts = split_qualified(qname);
	vector<Component> comps;
	vector<string> abi_tags;
	Component terminal;
	bool has_terminal = false;
	for (size_t i = 0; i < fn_records.size(); ++i) {
		const AbiFunctionRecord& rec = fn_records[i];
		if (rec.kind == ABI_FUNCTION_RECORD_ABI_TAG)
			abi_tags.push_back(rec.name);
		else if (rec.kind == ABI_FUNCTION_RECORD_OPERATOR_TERMINAL) {
			terminal.is_operator = true;
			terminal.terminal = rec.terminal;
			terminal.literal_suffix = rec.literal_suffix;
			terminal.unary_operator = explicit_parameter_count(fn_records) + (parts.size() > 1 ? 1 : 0) == 1;
			has_terminal = true;
		} else if (rec.kind == ABI_FUNCTION_RECORD_CONVERSION_TERMINAL) {
			terminal.is_conversion = true;
			terminal.conversion_type = rec.type;
			has_terminal = true;
		}
	}
	for (size_t i = 0; i < parts.size(); ++i) {
		if (i + 1 == parts.size() && parts[i] == "operator" && has_terminal) {
			terminal.abi_tags = abi_tags;
			comps.push_back(terminal);
			continue;
		}
		Component comp;
		comp.name = parts[i];
		comp.is_std = i == 0 && parts[i] == "std";
		if (i + 1 == parts.size()) {
			comp.abi_tags = abi_tags;
			for (size_t j = 0; j < operands.size(); ++j)
				comp.argument_refs.push_back(operands[j].argument_ref);
		}
		comps.push_back(comp);
	}
	return encode_unscoped_or_nested(comps, "", allow_name_prefix);
}
string Mangler::encode_encoding_name(const vector<AbiFunctionRecord>& fn_records, bool allow_name_prefix)
{
	vector<Component> comps;
	vector<string> abi_tags;
	vector<string> function_template_args;
	string qualifier_prefix;
	bool has_local_context = false;
	bool has_lambda_context = false;
	AbiFunctionRecord local_record;
	for (size_t i = 0; i < fn_records.size(); ++i) {
		const AbiFunctionRecord& rec = fn_records[i];
		if (rec.kind == ABI_FUNCTION_RECORD_ABI_TAG)
			abi_tags.push_back(rec.name);
		else if (rec.kind == ABI_FUNCTION_RECORD_FUNCTION_TEMPLATE_ARGUMENT)
			function_template_args.push_back(rec.name);
		else if (rec.kind == ABI_FUNCTION_RECORD_LOCAL_CONTEXT) {
			has_local_context = true;
			local_record = rec;
		} else if (rec.kind == ABI_FUNCTION_RECORD_LAMBDA_CONTEXT) {
			has_lambda_context = true;
			local_record = rec;
		}
		else if (rec.kind == ABI_FUNCTION_RECORD_QUALIFIER) {
			for (size_t q = 0; q < rec.qualifiers.size(); ++q)
				if (rec.qualifiers[q] == ABI_FUNCTION_QUALIFIER_CONST)
					qualifier_prefix += "K";
				else if (rec.qualifiers[q] == ABI_FUNCTION_QUALIFIER_VOLATILE) qualifier_prefix += "V";
				else if (rec.qualifiers[q] == ABI_FUNCTION_QUALIFIER_LVALUE_REFERENCE) qualifier_prefix += "R";
				else if (rec.qualifiers[q] == ABI_FUNCTION_QUALIFIER_RVALUE_REFERENCE) qualifier_prefix += "O";
		}
	}
	if (has_local_context || has_lambda_context) {
		vector<Component> inner;
		if (has_local_context) {
			Component local_type;
			local_type.name = local_record.source_name;
			inner.push_back(local_type);
		} else {
			Component lambda;
			lambda.name = "Ul";
			for (size_t t = 0; t < local_record.types.size(); ++t)
				lambda.name += encode_type(local_record.types[t]);
			if (local_record.types.empty())
				lambda.name += "v";
			lambda.name += "E" + local_record.discriminator + "_";
			inner.push_back(lambda);
		}
		for (size_t i = 0; i < fn_records.size(); ++i) {
			const AbiFunctionRecord& rec = fn_records[i];
				Component comp;
				if (rec.kind == ABI_FUNCTION_RECORD_TERMINAL_SOURCE) {
					comp.name = rec.terminal;
				} else if (rec.kind == ABI_FUNCTION_RECORD_OPERATOR_TERMINAL) {
					comp.is_operator = true;
					comp.terminal = rec.terminal;
					comp.literal_suffix = rec.literal_suffix;
					comp.unary_operator = explicit_parameter_count(fn_records) + (inner.empty() ? 0 : 1) == 1;
				} else {
					continue;
				}
			inner.push_back(comp);
		}
		string entity = "N";
		for (size_t i = 0; i < inner.size(); ++i) {
			if (has_lambda_context && i == 0)
				entity += inner[i].name;
			else
				entity += encode_component(inner[i]);
		}
		entity += "E";
		return encode_local_name(local_record.context_ref, entity, local_record.discriminator);
	}
	for (size_t i = 0; i < fn_records.size(); ++i) {
		const AbiFunctionRecord& rec = fn_records[i];
		Component comp;
		if (rec.kind == ABI_FUNCTION_RECORD_NAME_STD) {
			comp.name = "std";
			comp.is_std = true;
		} else if (rec.kind == ABI_FUNCTION_RECORD_NAME_SOURCE) {
			comp.name = rec.source_name;
			if (comp.name.empty())
				continue;
		} else if (rec.kind == ABI_FUNCTION_RECORD_NAME_TEMPLATE) {
			comp.name = rec.source_name;
			comp.argument_refs = rec.argument_refs;
		} else if (rec.kind == ABI_FUNCTION_RECORD_TERMINAL) {
			comp.is_ctor_dtor = true;
			comp.terminal = rec.terminal;
			} else if (rec.kind == ABI_FUNCTION_RECORD_TERMINAL_SOURCE) {
				comp.name = rec.terminal;
			} else if (rec.kind == ABI_FUNCTION_RECORD_OPERATOR_TERMINAL) {
				comp.is_operator = true;
				comp.terminal = rec.terminal;
				comp.literal_suffix = rec.literal_suffix;
				comp.unary_operator = explicit_parameter_count(fn_records) + (comps.empty() ? 0 : 1) == 1;
			} else if (rec.kind == ABI_FUNCTION_RECORD_CONVERSION_TERMINAL) {
				comp.is_conversion = true;
				comp.conversion_type = rec.type;
		} else {
			continue;
		}
		comps.push_back(comp);
	}
	if (!comps.empty())
		comps.back().abi_tags = abi_tags;
	if (!comps.empty())
		comps.back().argument_refs.insert(comps.back().argument_refs.end(),
			function_template_args.begin(), function_template_args.end());
	return encode_unscoped_or_nested(comps, qualifier_prefix, allow_name_prefix);
}
string Mangler::encode_function_name(const AbiFunctionTarget& target,
	const vector<AbiFunctionRecord>& fn_records, bool allow_name_prefix)
{
	if (target.kind == ABI_FUNCTION_TARGET_ENCODING)
		return encode_encoding_name(fn_records, allow_name_prefix);
	if (target.kind == ABI_FUNCTION_TARGET_LOCAL) {
		string entity = "N" + source_name(target.source_name) + operator_code(target.terminal, false) + "E";
		return encode_local_name(target.context_ref, entity, target.discriminator);
	}
	if (target.kind == ABI_FUNCTION_TARGET_LAMBDA) {
		string lambda = "Ul";
		for (size_t i = 0; i < target.signature_parameter_types.size(); ++i)
			lambda += encode_type(target.signature_parameter_types[i]);
		if (target.signature_parameter_types.empty())
			lambda += "v";
		lambda += "E" + target.discriminator + "_";
		return encode_local_name(target.context_ref, "N" + lambda + operator_code(target.terminal, false) + "E",
			target.discriminator);
	}
	return encode_path_name(target.qualified_name, target.path_operands, fn_records,
		allow_name_prefix);
}
string Mangler::encode_signature(const AbiFunctionTarget& target,
	const vector<AbiFunctionRecord>& fn_records)
{
	vector<AbiType> params;
	if (target.kind != ABI_FUNCTION_TARGET_LAMBDA)
		params = target.signature_parameter_types;
	bool variadic = false;
	bool has_result = false;
	AbiType result;
	for (size_t i = 0; i < fn_records.size(); ++i) {
		if (fn_records[i].kind == ABI_FUNCTION_RECORD_PARAMETER)
			params.push_back(fn_records[i].type);
		else if (fn_records[i].kind == ABI_FUNCTION_RECORD_VARIADIC)
			variadic = true;
		else if (fn_records[i].kind == ABI_FUNCTION_RECORD_RESULT) {
			has_result = true;
			result = fn_records[i].type;
		}
	}
	string out;
	if (has_result)
		out += encode_type(result);
	if (params.empty() && !variadic)
		out += "v";
	for (size_t i = 0; i < params.size(); ++i)
		out += encode_type(params[i]);
	if (variadic)
		out += "z";
	return out;
}
string Mangler::encode_function(const AbiFunctionTarget& target,
	const vector<AbiFunctionRecord>& fn_records, bool prefix, bool allow_name_prefix)
{
	string name = encode_function_name(target, fn_records, allow_name_prefix);
	bool has_template_args = !target.path_operands.empty();
	string template_prefix_key;
	for (size_t i = 0; i < fn_records.size(); ++i)
		if (fn_records[i].kind == ABI_FUNCTION_RECORD_FUNCTION_TEMPLATE_ARGUMENT ||
		    (fn_records[i].kind == ABI_FUNCTION_RECORD_NAME_TEMPLATE &&
		     !fn_records[i].argument_refs.empty()))
			has_template_args = true;
	for (size_t i = 0; i < fn_records.size(); ++i) {
		if (fn_records[i].kind == ABI_FUNCTION_RECORD_FUNCTION_TEMPLATE_PREFIX &&
		    !starts_with(fn_records[i].name, "operator-name:"))
			template_prefix_key = fn_records[i].name;
		else if (template_prefix_key.empty() &&
		         fn_records[i].kind == ABI_FUNCTION_RECORD_NAME_TEMPLATE)
			template_prefix_key = fn_records[i].source_name;
	}
	bool prefix_already_registered = false;
	if (!template_prefix_key.empty()) {
		while (starts_with(template_prefix_key, "::"))
			template_prefix_key = template_prefix_key.substr(2);
		prefix_already_registered =
			substitution_index.count("name:" + template_prefix_key) != 0;
	}
	if (has_template_args && !prefix_already_registered)
		add_substitution("fn-template:" + name, name);
	string signature = encode_signature(target, fn_records);
	string out = name + signature;
	return prefix ? "_Z" + out : out;
}
string Mangler::encode_target(const AbiTargetRecord& target, const vector<AbiFunctionRecord>& fn_records)
{
	if (target.kind == ABI_TARGET_FACT_TYPE)
		return encode_type(target.type);
	if (target.kind == ABI_TARGET_FACT_FUNCTION) {
		if (target.c_linkage)
			return target.function.qualified_name;
		return encode_function(target.function, fn_records, true, false);
	}
	if (target.kind == ABI_TARGET_FACT_VARIABLE)
		return "_Z" + encode_qualified_name(target.qualified_name);
	if (target.kind == ABI_TARGET_FACT_TYPEINFO)
		return "_ZTI" + encode_type(target.type);
	if (target.kind == ABI_TARGET_FACT_VTABLE)
		return "_ZTV" + encode_type(target.type);
	if (target.kind == ABI_TARGET_FACT_VTT)
		return "_ZTT" + encode_type(target.type);
	if (target.kind == ABI_TARGET_FACT_CONSTRUCTION_VTABLE)
		return "_ZTC" + encode_type(target.type) + to_string(target.base_offset) + "_" +
			encode_type(target.base_type);
	if (target.kind == ABI_TARGET_FACT_THREAD_LOCAL_WRAPPER)
		return "_ZTW" + encode_qualified_name(target.qualified_name);
	if (target.kind == ABI_TARGET_FACT_THUNK) {
		string call = target.this_adjust < 0 ? "hn" + to_string(-target.this_adjust) + "_" :
			"h" + to_string(target.this_adjust) + "_";
		if (target.has_result_adjust) {
			string result = target.result_adjust < 0 ? "hn" + to_string(-target.result_adjust) + "_" :
				"h" + to_string(target.result_adjust) + "_";
			return "_ZTc" + call + result +
				encode_function(target.function, vector<AbiFunctionRecord>(), false, false);
		}
		return "_ZT" + call +
			encode_function(target.function, vector<AbiFunctionRecord>(), false, false);
	}
	if (target.kind == ABI_TARGET_FACT_VIRTUAL_BASE_THUNK)
		return "_ZTv0_n" + to_string(-target.this_adjust) + "_" +
			encode_function(target.function, vector<AbiFunctionRecord>(), false, false);
	throw logic_error("unsupported target");
}
}  // namespace
AbiFactRecord parse_fact_record_words(const vector<string>& words)
{
	ostringstream line;
	for (size_t i = 0; i < words.size(); ++i) line << (i == 0 ? "" : " ") << words[i];
	return parse_fact_record_line(line.str());
}
AbiFactFile parse_fact_text(const string& text)
{
	AbiFactFile file;
	AbiFactCase current;
	current.label = "";
	istringstream in(text);
	string line;
	while (getline(in, line)) {
		line = trim(line);
		if (line.empty())
			continue;
		vector<string> words = split_words(line);
		if (!words.empty() && words[0] == "case") {
			if (!current.records.empty())
				file.cases.push_back(current);
			current = AbiFactCase();
			current.label = words.size() > 1 ? words[1] : "";
			continue;
		}
		current.records.push_back(parse_fact_record_line(line));
	}
	if (!current.records.empty())
		file.cases.push_back(current);
	return file;
}
string serialize_fact_file(const AbiFactFile& file) { return "cases " + to_string(file.cases.size()) + "\n"; }
string mangle_fact_file(const AbiFactFile& file)
{
	ostringstream out;
	for (size_t i = 0; i < file.cases.size(); ++i) {
		Mangler mangler(file.cases[i]);
		out << mangler.mangle_case() << "\n";
	}
	return out.str();
}
string mangle_fact_files(const vector<string>& input_paths)
{
	ostringstream out;
	for (size_t i = 0; i < input_paths.size(); ++i) {
		ifstream in(input_paths[i].c_str());
		if (!in)
			throw logic_error("unable to open input file '" + input_paths[i] + "'");
		ostringstream text;
		text << in.rdbuf();
		out << mangle_fact_file(parse_fact_text(text.str()));
	}
	return out.str();
}
}
