#include "lowir2cy86.h"

#include <cctype>
#include <fstream>
#include <sstream>
#include <stdexcept>

using namespace std;

namespace lowir2cy86 {
namespace {

struct Token
{
	string text;
	int line;

	Token(const string& t, int l) : text(t), line(l) {}
};

bool is_name_prefix(char c)
{
	return c == '@' || c == '%' || c == '$' || c == '^';
}

bool is_punctuation(char c)
{
	return c == '(' || c == ')' || c == '{' || c == '}' || c == '[' ||
	       c == ']' || c == ',' || c == ':' || c == '=' || c == '+' ||
	       c == '<' || c == '>';
}

bool is_word_delim(char c)
{
	return isspace(static_cast<unsigned char>(c)) || is_punctuation(c) ||
	       c == '-' || c == '#';
}

void read_debug_token(const string& text,
                      size_t& i,
                      int& line,
                      vector<Token>& out);
void read_name_token(const string& text,
                     size_t& i,
                     int line,
                     vector<Token>& out);
void read_word_token(const string& text,
                     size_t& i,
                     int line,
                     vector<Token>& out);

vector<Token> lex_text(const string& text)
{
	vector<Token> out;
	int line = 1;
	for (size_t i = 0; i < text.size();)
	{
		const char c = text[i];
		if (c == '\n')
		{
			++line;
			++i;
		}
		else if (isspace(static_cast<unsigned char>(c)))
			++i;
		else if (c == '#')
		{
			while (i < text.size() && text[i] != '\n')
				++i;
		}
		else if (c == '!' && text.compare(i, 5, "!dbg(") == 0)
			read_debug_token(text, i, line, out);
		else if (c == '-' && i + 1 < text.size() && text[i + 1] == '>')
		{
			out.push_back(Token("->", line));
			i += 2;
		}
		else if (c == '-' || is_punctuation(c))
			out.push_back(Token(string(1, text[i++]), line));
		else if (is_name_prefix(c))
			read_name_token(text, i, line, out);
		else
			read_word_token(text, i, line, out);
	}
	out.push_back(Token("<eof>", line));
	return out;
}

void read_debug_token(const string& text,
                      size_t& i,
                      int& line,
                      vector<Token>& out)
{
	const size_t start = i;
	int depth = 0;
	while (i < text.size())
	{
		if (text[i] == '\n')
			++line;
		if (text[i] == '(')
			++depth;
		else if (text[i] == ')')
		{
			++i;
			if (--depth == 0)
				break;
			continue;
		}
		++i;
	}
	out.push_back(Token(text.substr(start, i - start), line));
}

void read_name_token(const string& text,
                     size_t& i,
                     int line,
                     vector<Token>& out)
{
	const size_t start = i++;
	while (i < text.size() && !is_word_delim(text[i]))
		++i;
	out.push_back(Token(text.substr(start, i - start), line));
}

void read_word_token(const string& text,
                     size_t& i,
                     int line,
                     vector<Token>& out)
{
	const size_t start = i++;
	while (i < text.size())
	{
		if ((text[i] == '+' || text[i] == '-') && i > start)
		{
			const char prev = text[i - 1];
			if (prev == 'e' || prev == 'E' || prev == 'p' || prev == 'P')
			{
				++i;
				continue;
			}
		}
		if (is_word_delim(text[i]))
			break;
		++i;
	}
	out.push_back(Token(text.substr(start, i - start), line));
}

string read_file_text(const string& path)
{
	ifstream in(path.c_str());
	if (!in)
		throw runtime_error("cannot open LowIR input");
	ostringstream ss;
	ss << in.rdbuf();
	return ss.str();
}

class Parser
{
public:
	explicit Parser(const vector<Token>& tokens) : tokens_(tokens), pos_(0) {}

	Program parse_program()
	{
		Program program;
		while (!check("<eof>"))
			parse_top_level(program);
		return program;
	}

private:
	const vector<Token>& tokens_;
	size_t pos_;

	bool check(const string& text) const { return peek().text == text; }
	bool match(const string& text)
	{
		if (!check(text))
			return false;
		++pos_;
		return true;
	}

	const Token& peek(size_t n = 0) const
	{
		if (pos_ + n >= tokens_.size())
			throw runtime_error("unexpected end of LowIR");
		return tokens_[pos_ + n];
	}

	string take()
	{
		if (check("<eof>"))
			throw runtime_error("unexpected end of LowIR");
		return tokens_[pos_++].text;
	}

	string take_metadata_value()
	{
		if (check("<eof>") || check(",") || check("]"))
			throw runtime_error("expected metadata value");
		string value;
		while (!check("<eof>") && !check(",") && !check("]"))
			value += take();
		return value;
	}

		void expect(const string& text)
		{
			if (!match(text))
				throw runtime_error("expected '" + text + "'");
		}

	void parse_top_level(Program& program)
	{
		if (match("declare"))
		{
			if (match("global"))
				program.globals.push_back(parse_global_declaration());
			else if (match("function"))
				program.functions.push_back(parse_function_declaration());
			else
				throw runtime_error("expected declaration kind");
		}
		else if (match("global"))
			program.globals.push_back(parse_global_definition());
		else if (match("function"))
			program.functions.push_back(parse_function_definition());
		else if (match("alias"))
			program.aliases.push_back(parse_object_alias());
		else
			throw runtime_error("expected top-level item");
	}

	Global parse_global_declaration()
	{
		Global global;
		global.declaration = true;
		global.name = parse_global_name();
		if (match(":"))
		{
			global.has_type = true;
			global.type = parse_type();
		}
		parse_storage_keyword(global.metadata);
		append_metadata(global.metadata);
		return global;
	}

	Global parse_global_definition()
	{
		Global global;
		global.name = parse_global_name();
		parse_storage_keyword(global.metadata);
		if (match(":"))
		{
			global.has_type = true;
			global.type = parse_type();
			parse_storage_keyword(global.metadata);
			append_metadata(global.metadata);
			expect("=");
			global.init = parse_global_initializer();
		}
		else
		{
			parse_storage_keyword(global.metadata);
			append_metadata(global.metadata);
			expect("=");
			expect("{");
			while (!match("}"))
				global.data.push_back(parse_global_data_item());
		}
		return global;
	}

	Function parse_function_declaration()
	{
		Function function;
		function.declaration = true;
		function.name = parse_function_name();
		expect("(");
		function.params = parse_parameter_list();
		expect(")");
		expect("->");
		function.ret = parse_type();
		append_metadata(function.metadata);
		return function;
	}

	Function parse_function_definition()
	{
		Function function = parse_function_header(false);
		expect("{");
		Block* current = nullptr;
		while (!match("}"))
			parse_function_item(function, current);
		return function;
	}

	Function parse_function_header(bool declaration)
	{
		Function function;
		function.declaration = declaration;
		function.name = parse_function_name();
		expect("(");
		function.params = parse_parameter_list();
		expect(")");
		expect("->");
		function.ret = parse_type();
		append_metadata(function.metadata);
		skip_debug();
		return function;
	}

	void parse_function_item(Function& function, Block*& current)
	{
		if (match("slot"))
		{
			function.slots.push_back(parse_slot());
			return;
		}
		if (match("block"))
		{
			function.blocks.push_back(parse_block_header());
			current = &function.blocks.back();
			return;
		}
		if (!current)
			throw runtime_error("instruction outside block");
		current->instructions.push_back(parse_instruction());
	}

	Slot parse_slot()
	{
		Slot slot;
		slot.name = parse_slot_name();
		expect(":");
		slot.type = parse_type();
		return slot;
	}

	Block parse_block_header()
	{
		Block block;
		block.name = parse_block_name();
		expect(":");
		return block;
	}

	ObjectAlias parse_object_alias()
	{
		expect("object");
		ObjectAlias alias;
		alias.object = take();
		expect("=");
		alias.target = parse_symbol_name();
		return alias;
	}

	vector<Parameter> parse_parameter_list()
	{
		vector<Parameter> params;
		if (check(")"))
			return params;
		params.push_back(parse_parameter());
		while (match(","))
			params.push_back(parse_parameter());
		return params;
	}

	Parameter parse_parameter()
	{
		Parameter param;
		param.name = parse_temp_name();
		expect(":");
		param.type = parse_type();
		append_metadata(param.metadata);
		return param;
	}

	Type parse_type()
	{
		if (match("obj"))
		{
			expect("<");
			const Span span = parse_span_text(take());
			expect(">");
			return object_type(span.bytes, span.align);
		}
		return parse_type_text(take());
	}

	void append_metadata(Metadata& metadata)
	{
		while (match("["))
		{
			do
			{
				MetadataItem item;
				item.key = take();
				expect("=");
				item.value = take_metadata_value();
				item.global_value = !item.value.empty() && item.value[0] == '@';
				metadata.push_back(item);
			} while (match(","));
			expect("]");
		}
	}

	void parse_storage_keyword(Metadata& metadata)
	{
		if (match("readonly") || match("thread_local"))
		{
			MetadataItem item;
			item.key = "storage";
			item.value = tokens_[pos_ - 1].text;
			metadata.push_back(item);
		}
	}

	GlobalInit parse_global_initializer()
	{
		GlobalInit init;
		if (match("zero"))
			init.kind = "zero";
		else if (match("addr"))
		{
			init.kind = "addr";
			init.target = parse_symbol_name();
			parse_address_addend(init.has_addend, init.addend);
		}
		else
		{
			init.kind = "literal";
			init.literal = parse_literal_text();
		}
		return init;
	}

	GlobalDataItem parse_global_data_item()
	{
		GlobalDataItem item;
		item.addend = 0;
		item.has_addend = false;
		item.zero_bytes = 0;
		if (match("zero"))
		{
			item.kind = "zero";
			item.zero_bytes = parse_size_literal(take());
			return item;
		}
		if (match("ptr"))
		{
			item.kind = "addr";
			expect("addr");
			item.target = parse_symbol_name();
			parse_address_addend(item.has_addend, item.addend);
			return item;
		}
		item.kind = "literal";
		item.type = parse_type_text(take());
		item.literal = parse_literal_text();
		return item;
	}

	Instruction parse_instruction()
	{
		Instruction ins;
		if (is_temp_token(peek().text) && peek(1).text == "=")
		{
			ins.has_dest = true;
			ins.dest = take();
			expect("=");
			parse_rvalue(ins);
		}
		else
			parse_void_or_terminator(ins);
		skip_debug();
		return ins;
	}

	void parse_rvalue(Instruction& ins)
	{
		const string kw = take();
		if (kw == "const")
			parse_const(ins);
		else if (kw == "copy")
			parse_copy(ins);
		else if (kw == "addr")
			parse_addr(ins);
		else if (kw == "load")
			parse_load(ins);
		else if (kw == "atomic_load")
			parse_atomic_load(ins);
		else if (kw == "index")
			parse_index(ins);
		else if (kw == "unary")
			parse_unary(ins);
		else if (kw == "binary")
			parse_binary(ins);
		else if (kw == "cmp")
			parse_cmp(ins);
		else if (kw == "convert")
			parse_convert(ins);
		else if (kw == "atomic_add_fetch" || kw == "atomic_exchange")
			parse_atomic_rmw(ins, kw);
		else if (kw == "atomic_compare_exchange")
			parse_atomic_compare_exchange(ins);
		else if (kw == "call")
			parse_call(ins, false);
		else if (kw == "stackalloc")
			parse_stackalloc(ins);
		else if (kw == "va_arg")
			parse_va_arg(ins);
		else if (kw == "exception" || kw == "exception_selector")
			parse_exception_value(ins);
		else
			throw runtime_error("unknown rvalue instruction");
	}

	void parse_void_or_terminator(Instruction& ins)
	{
		const string kw = take();
		if (kw == "store")
			parse_store(ins);
		else if (kw == "atomic_store")
			parse_atomic_store(ins);
		else if (kw == "atomic_thread_fence")
			parse_fence(ins, InstrKind::AtomicThreadFence);
		else if (kw == "atomic_signal_fence")
			parse_fence(ins, InstrKind::AtomicSignalFence);
		else if (kw == "call")
			parse_call(ins, true);
		else if (kw == "va_start")
			parse_va_start(ins);
		else if (kw == "va_end")
			parse_va_end(ins);
		else if (kw == "copyobj")
			parse_copyobj(ins);
		else if (kw == "zeroinit")
			parse_zeroinit(ins);
		else if (kw == "eh_try" || kw == "eh_cleanup")
			parse_eh_push(ins, kw);
		else if (kw == "eh_catch")
			parse_eh_catch(ins);
		else if (kw == "eh_catch_all")
			parse_eh_catch_all(ins);
		else if (kw == "eh_filter")
			parse_eh_filter(ins);
		else if (kw == "eh_end")
			ins.kind = InstrKind::EhEnd;
		else if (kw == "throw")
			parse_throw(ins);
		else if (kw == "resume")
			ins.kind = InstrKind::Resume;
		else if (kw == "jump")
			parse_jump(ins);
		else if (kw == "branch")
			parse_branch(ins);
		else if (kw == "switch")
			parse_switch(ins);
		else if (kw == "return")
			parse_return(ins);
		else
			throw runtime_error("unknown instruction");
	}

	void parse_const(Instruction& ins)
	{
		ins.kind = InstrKind::Const;
		ins.type = parse_type();
		ins.a = literal_value(parse_literal_text());
	}

	void parse_copy(Instruction& ins)
	{
		ins.kind = InstrKind::Copy;
		ins.type = parse_type();
		ins.a = parse_value();
	}

	void parse_addr(Instruction& ins)
	{
		ins.kind = InstrKind::Addr;
		ins.a = parse_addressable();
	}

	void parse_load(Instruction& ins)
	{
		ins.kind = InstrKind::Load;
		ins.type = parse_type();
		ins.a = parse_storage();
	}

	void parse_atomic_load(Instruction& ins)
	{
		ins.kind = InstrKind::AtomicLoad;
		ins.type = parse_type();
		ins.a = parse_value();
		expect(",");
		ins.order_a = parse_int_literal();
	}

	void parse_index(Instruction& ins)
	{
		ins.kind = InstrKind::Index;
		ins.type = parse_type();
		if (check("["))
			append_metadata_as_op(ins.op);
		ins.a = parse_value();
		expect(",");
		ins.b = parse_value();
	}

	void append_metadata_as_op(string& out)
	{
		Metadata md;
		append_metadata(md);
		for (size_t i = 0; i < md.size(); ++i)
		{
			if (md[i].key == "projection")
				out = md[i].value;
		}
	}

	void parse_unary(Instruction& ins)
	{
		ins.kind = InstrKind::Unary;
		ins.op = take();
		ins.type = parse_type();
		ins.a = parse_value();
	}

	void parse_binary(Instruction& ins)
	{
		ins.kind = InstrKind::Binary;
		ins.op = take();
		ins.type = parse_type();
		ins.a = parse_value();
		expect(",");
		ins.b = parse_value();
	}

	void parse_cmp(Instruction& ins)
	{
		ins.kind = InstrKind::Cmp;
		ins.op = take();
		ins.type = parse_type();
		ins.a = parse_value();
		expect(",");
		ins.b = parse_value();
	}

	void parse_convert(Instruction& ins)
	{
		ins.kind = InstrKind::Convert;
		ins.op = take();
		ins.type = parse_type();
		ins.src_type = parse_type();
		ins.a = parse_value();
	}

	void parse_atomic_rmw(Instruction& ins, const string& kw)
	{
		ins.kind = kw == "atomic_add_fetch"
		               ? InstrKind::AtomicAddFetch
		               : InstrKind::AtomicExchange;
		ins.type = parse_type();
		ins.a = parse_value();
		expect(",");
		ins.b = parse_value();
		expect(",");
		ins.order_a = parse_int_literal();
	}

	void parse_atomic_compare_exchange(Instruction& ins)
	{
		ins.kind = InstrKind::AtomicCompareExchange;
		ins.type = parse_type();
		ins.a = parse_value();
		expect(",");
		ins.b = parse_value();
		expect(",");
		ins.c = parse_value();
		expect(",");
		ins.order_a = parse_int_literal();
		expect(",");
		ins.order_b = parse_int_literal();
	}

	void parse_call(Instruction& ins, bool leading_call_seen)
	{
		ins.kind = InstrKind::Call;
		ins.type = leading_call_seen && match("void") ? Type() : parse_type();
		ins.a = parse_callee();
		expect("(");
		ins.args = parse_argument_list();
		expect(")");
		if (match("as"))
			ins.signature = parse_call_signature();
	}

	void parse_stackalloc(Instruction& ins)
	{
		ins.kind = InstrKind::StackAlloc;
		ins.type = parse_type_text("ptr");
		ins.src_type = parse_type();
		ins.a = parse_value();
	}

	void parse_va_start(Instruction& ins)
	{
		ins.kind = InstrKind::VaStart;
		ins.a = parse_value();
	}

	void parse_va_arg(Instruction& ins)
	{
		ins.kind = InstrKind::VaArg;
		ins.type = parse_type();
		ins.a = parse_value();
	}

	void parse_va_end(Instruction& ins)
	{
		ins.kind = InstrKind::VaEnd;
		ins.a = parse_value();
	}

	CallSignature parse_call_signature()
	{
		CallSignature sig;
		sig.present = true;
		expect("(");
		sig.params = parse_parameter_list();
		expect(")");
		expect("->");
		sig.ret = parse_type();
		append_metadata(sig.metadata);
		return sig;
	}

	vector<Value> parse_argument_list()
	{
		vector<Value> args;
		if (check(")"))
			return args;
		args.push_back(parse_value());
		while (match(","))
			args.push_back(parse_value());
		return args;
	}

	void parse_exception_value(Instruction& ins)
	{
		if (tokens_[pos_ - 1].text == "exception_selector")
			ins.kind = InstrKind::ExceptionSelector;
		else
			ins.kind = InstrKind::Exception;
		ins.type = parse_type();
	}

	void parse_store(Instruction& ins)
	{
		ins.kind = InstrKind::Store;
		ins.type = parse_type();
		ins.a = parse_value();
		expect(",");
		ins.b = parse_storage();
	}

	void parse_atomic_store(Instruction& ins)
	{
		ins.kind = InstrKind::AtomicStore;
		ins.type = parse_type();
		ins.a = parse_value();
		expect(",");
		ins.b = parse_value();
		expect(",");
		ins.order_a = parse_int_literal();
	}

	void parse_fence(Instruction& ins, InstrKind kind)
	{
		ins.kind = kind;
		ins.order_a = parse_int_literal();
	}

	void parse_copyobj(Instruction& ins)
	{
		ins.kind = InstrKind::CopyObj;
		ins.span = parse_span_text(take());
		ins.a = parse_value();
		expect(",");
		ins.b = parse_value();
	}

	void parse_zeroinit(Instruction& ins)
	{
		ins.kind = InstrKind::ZeroInit;
		ins.span = parse_span_text(take());
		ins.a = parse_value();
	}

	void parse_eh_push(Instruction& ins, const string& kw)
	{
		ins.kind = kw == "eh_try" ? InstrKind::EhTry : InstrKind::EhCleanup;
		if (!check(",") && !check("<eof>") &&
		    !(peek().text.compare(0, 5, "!dbg(") == 0) &&
		    !peek().text.empty() && peek().text[0] == '^')
			ins.target = parse_block_name();
	}

	void parse_eh_catch(Instruction& ins)
	{
		ins.kind = InstrKind::EhCatch;
		ins.a = named_value(ValueKind::Global, parse_symbol_name());
		ins.order_a = 1;
		if (match(","))
			ins.order_a = parse_int_literal();
	}

	void parse_eh_catch_all(Instruction& ins)
	{
		ins.kind = InstrKind::EhCatchAll;
		ins.order_a = 1;
		if (match(","))
			ins.order_a = parse_int_literal();
	}

	void parse_eh_filter(Instruction& ins)
	{
		ins.kind = InstrKind::EhFilter;
		ins.a = named_value(ValueKind::Global, parse_symbol_name());
		ins.args.push_back(ins.a);
		ins.order_a = 1;
		while (match(","))
		{
			if (!peek().text.empty() && peek().text[0] == '@')
				ins.args.push_back(
					named_value(ValueKind::Global, parse_symbol_name()));
			else
			{
				ins.order_a = parse_int_literal();
				break;
			}
		}
	}

	void parse_throw(Instruction& ins)
	{
		ins.kind = InstrKind::Throw;
		ins.type = parse_type();
		ins.a = parse_value();
	}

	void parse_jump(Instruction& ins)
	{
		ins.kind = InstrKind::Jump;
		ins.target = parse_block_name();
	}

	void parse_branch(Instruction& ins)
	{
		ins.kind = InstrKind::Branch;
		ins.a = parse_value();
		expect(",");
		ins.target = parse_block_name();
		expect(",");
		ins.target_false = parse_block_name();
	}

	void parse_switch(Instruction& ins)
	{
		ins.kind = InstrKind::Switch;
		ins.a = parse_value();
		expect(",");
		ins.target = parse_block_name();
		while (match(","))
		{
			SwitchCase item;
			item.value = parse_value();
			expect(":");
			item.target = parse_block_name();
			ins.switch_cases.push_back(item);
		}
	}

	void parse_return(Instruction& ins)
	{
		ins.kind = InstrKind::Return;
		ins.type = parse_type();
		if (!is_void_type(ins.type))
			ins.a = parse_value();
	}

	Value parse_value()
	{
		if (match("-"))
			return literal_value("-" + take());
		const string text = take();
		if (is_temp_token(text))
			return named_value(ValueKind::Temp, text);
		if (is_slot_token(text))
			return named_value(ValueKind::Slot, text);
		if (is_global_token(text))
			return named_value(ValueKind::Global, text);
		return literal_value(text);
	}

	Value parse_storage()
	{
		const string text = take();
		if (is_temp_token(text))
			return named_value(ValueKind::Temp, text);
		if (is_slot_token(text))
			return named_value(ValueKind::Slot, text);
		if (is_global_token(text))
			return named_value(ValueKind::Global, text);
		throw runtime_error("expected storage");
	}

	Value parse_addressable()
	{
		const string text = take();
		if (is_slot_token(text))
			return named_value(ValueKind::Slot, text);
		if (is_global_token(text))
			return named_value(ValueKind::Global, text);
		throw runtime_error("expected addressable");
	}

	Value parse_callee()
	{
		const string text = take();
		if (is_function_token(text))
			return named_value(ValueKind::Function, text);
		if (is_temp_token(text))
			return named_value(ValueKind::Temp, text);
		if (is_global_token(text))
			return named_value(ValueKind::Global, text);
		throw runtime_error("expected callee");
	}

	string parse_literal_text()
	{
		if (match("-"))
			return "-" + take();
		return take();
	}

	void parse_address_addend(bool& has, int& addend)
	{
		if (match("+") || match("-"))
		{
			const bool negative = tokens_[pos_ - 1].text == "-";
			has = true;
			addend = parse_int_literal();
			if (negative)
				addend = -addend;
		}
	}

	int parse_int_literal()
	{
		const string text = parse_literal_text();
		return stoi(text, nullptr, 0);
	}

	size_t parse_size_literal(const string& text)
	{
		return static_cast<size_t>(stoul(text, nullptr, 0));
	}

	string parse_symbol_name()
	{
		const string text = take();
		if (!is_global_token(text))
			throw runtime_error("expected top-level symbol");
		return text;
	}

	string parse_global_name() { return require_prefix('@'); }
	string parse_function_name() { return require_prefix('@'); }
	string parse_temp_name() { return require_prefix('%'); }
	string parse_slot_name() { return require_prefix('$'); }
	string parse_block_name() { return require_prefix('^'); }

	string require_prefix(char prefix)
	{
		const string text = take();
		if (text.empty() || text[0] != prefix)
			throw runtime_error("unexpected LowIR name");
		return text;
	}

	void skip_debug()
	{
		if (!check("<eof>") && peek().text.compare(0, 5, "!dbg(") == 0)
			++pos_;
	}

	static bool is_temp_token(const string& text)
	{
		return !text.empty() && text[0] == '%';
	}

	static bool is_slot_token(const string& text)
	{
		return !text.empty() && text[0] == '$';
	}

	static bool is_global_token(const string& text)
	{
		return !text.empty() && text[0] == '@';
	}

	static bool is_function_token(const string& text)
	{
		return is_global_token(text);
	}

	static Value named_value(ValueKind kind, const string& text)
	{
		Value value;
		value.kind = kind;
		value.text = text;
		return value;
	}

	static Value literal_value(const string& text)
	{
		Value value;
		value.kind = ValueKind::Literal;
		value.text = text == "nullptr" ? "0" : text;
		return value;
	}
};

}  // namespace

Program parse_files(const vector<string>& srcfiles)
{
	vector<Token> tokens;
	for (size_t i = 0; i < srcfiles.size(); ++i)
	{
		vector<Token> unit = lex_text(read_file_text(srcfiles[i]));
		for (size_t j = 0; j + 1 < unit.size(); ++j)
			tokens.push_back(unit[j]);
	}
	tokens.push_back(Token("<eof>", 0));
	Parser parser(tokens);
	return parser.parse_program();
}

}  // namespace lowir2cy86
