#include "pa14_lowir_internal.h"

namespace pa14 {
namespace internal {
namespace {

bool node_contains_call_expression(const Node& node)
{
	if (starts_with(node.line, "call-expression"))
		return true;
	for (size_t i = 0; i < node.children.size(); ++i)
		if (node_contains_call_expression(node.children[i]))
			return true;
	return false;
}

}  // namespace

FunctionLowerer::FunctionLowerer(ProgramLowerer& program, const Node& fn)
	: program_(program),
	  fn_(fn),
	  current_(NULL),
	  temp_counter_(0),
	  block_counter_(0),
	  aux_slot_counter_(0),
	  eh_try_depth_(0)
{
}

void FunctionLowerer::add_slot(const string& name, const string& type)
{
	out_.slots.push_back("  slot $" + name + " : " + type);
}

string FunctionLowerer::slot_for(const Binding* binding)
{
	map<const Binding*, string>::const_iterator found = slots_.find(binding);
	if (found != slots_.end())
		return found->second;
	string base = binding != NULL && !binding->name.empty()
		? binding->name : "__param" + to_string(slots_.size());
	int& count = slot_names_[base];
	++count;
	string name = base;
	if (count > 1)
		name += "__shadow" + to_string(count);
	slots_[binding] = name;
	add_slot(name, slot_lowir_type(binding->type));
	return name;
}

string FunctionLowerer::fresh_temp()
{
	++temp_counter_;
	return "%t" + to_string(temp_counter_);
}

string FunctionLowerer::fresh_block(const string& prefix)
{
	++block_counter_;
	return prefix + "_" + to_string(block_counter_);
}

string FunctionLowerer::fresh_aux_slot(const string& prefix, const string& type)
{
	++aux_slot_counter_;
	string name = prefix + "__" + to_string(aux_slot_counter_);
	add_slot(name, type);
	return name;
}

void FunctionLowerer::start_block(const string& name)
{
	blocks_.push_back(unique_ptr<Block>(new Block(name)));
	current_ = blocks_.back().get();
}

void FunctionLowerer::instr(const string& text)
{
	if (current_ == NULL || current_->terminated)
		return;
	current_->instrs.push_back("    " + text);
}

void FunctionLowerer::terminate(const string& text)
{
	if (current_ == NULL || current_->terminated)
		return;
	current_->instrs.push_back("    " + text);
	current_->terminated = true;
}

FunctionOut FunctionLowerer::lower()
{
	Binding* binding = fn_.binding;
	if (binding == NULL)
		throw runtime_error("missing function binding");
	string name = program_.symbol_for(binding);
	TypePtr fn_type = binding->type;
	ostringstream header;
	header << "function @" << name << "(";
	for (size_t i = 0; i < fn_type->parameters.size(); ++i)
	{
		if (i != 0)
			header << ", ";
		string pname = i < fn_.children.size() &&
			starts_with(fn_.children[i].line, "parameter ")
			? fn_.children[i].line.substr(10) : "";
		size_t space = pname.find(' ');
		pname = space == string::npos ? pname : pname.substr(0, space);
		if (pname.empty())
			pname = "__param" + to_string(i);
		TypePtr ptype = fn_type->parameters[i];
		header << "%" << pname << " : " << lowir_parameter(ptype);
	}
	header << ") -> " << scalar_lowir_type(fn_type->base);
	vector<string> metadata;
	if (fn_type->variadic)
		metadata.push_back("arity=variadic");
	if (binding->language_linkage == "c")
		metadata.push_back("linkage=c");
	if (binding->unwind_no)
		metadata.push_back("unwind=no");
	if (binding->name == "__cppgm_init")
		metadata.push_back("role=init");
	else if (binding->name == "__cppgm_fini")
		metadata.push_back("role=fini");
	else if (binding->name == "main")
	{
		metadata.push_back("role=entry");
		metadata.push_back("binding=strong");
		metadata.push_back("keep_alias=yes");
	}
	else if (binding->is_inline_definition)
		metadata.push_back("binding=weak");
	else
		metadata.push_back("binding=strong");
	header << metadata_suffix(metadata);
	out_.header = header.str();
	lower_params();
	start_block("entry");
	lower_param_stores();
	for (size_t i = 0; i < fn_.children.size(); ++i)
	{
		if (starts_with(fn_.children[i].line, "compound-statement"))
			lower_compound(fn_.children[i]);
	}
	if (current_ != NULL && !current_->terminated)
	{
		if (pa11::is_void_type(fn_type->base))
			terminate("return void");
		else
			terminate("return " + scalar_lowir_type(fn_type->base) + " 0");
	}
	for (size_t i = 0; i < blocks_.size(); ++i)
		out_.blocks.push_back(*blocks_[i]);
	return out_;
}

void FunctionLowerer::lower_params()
{
	TypePtr fn_type = fn_.binding->type;
	size_t param_index = 0;
	for (size_t i = 0; i < fn_.children.size(); ++i)
	{
		if (!starts_with(fn_.children[i].line, "parameter "))
			continue;
		string pname = fn_.children[i].line.substr(10);
		size_t space = pname.find(' ');
		pname = space == string::npos ? pname : pname.substr(0, space);
		if (pname.empty())
			pname = "__param" + to_string(param_index);
		if (pname.size() > 1 && pname[0] == 't')
		{
			int n = 0;
			bool digits = true;
			for (size_t j = 1; j < pname.size(); ++j)
				if (pname[j] >= '0' && pname[j] <= '9')
					n = n * 10 + (pname[j] - '0');
				else
					digits = false;
			if (digits && n > temp_counter_)
				temp_counter_ = n;
		}
		Binding* binding = fn_.children[i].binding;
		if (binding == NULL)
		{
			add_slot(pname, slot_lowir_type(fn_type->parameters[param_index]));
			++param_index;
		}
		else
		{
			slots_[binding] = pname;
			add_slot(pname, slot_lowir_type(binding->type));
			++param_index;
		}
	}
}

void FunctionLowerer::lower_param_stores()
{
	TypePtr fn_type = fn_.binding->type;
	size_t param_index = 0;
	for (size_t i = 0; i < fn_.children.size(); ++i)
	{
		if (!starts_with(fn_.children[i].line, "parameter "))
			continue;
		string pname = fn_.children[i].line.substr(10);
		size_t space = pname.find(' ');
		pname = space == string::npos ? pname : pname.substr(0, space);
		if (pname.empty())
			pname = "__param" + to_string(param_index);
		TypePtr ptype = fn_type->parameters[param_index];
		if (pa11::strip_cv(ptype)->kind == TypeKind::Record)
		{
			++param_index;
			continue;
		}
		instr("store " + scalar_lowir_type(ptype) + " %" + pname +
		      ", $" + pname);
		++param_index;
	}
}

void FunctionLowerer::lower_compound(const Node& node)
{
	cleanups_.push_back(vector<Cleanup>());
	for (size_t i = 0; i < node.children.size(); ++i)
		lower_stmt(node.children[i]);
	if (current_ != NULL && !current_->terminated)
		emit_scope_cleanups(cleanups_.back());
	cleanups_.pop_back();
}

void FunctionLowerer::lower_stmt(const Node& node)
{
	if (starts_with(node.line, "compound-statement"))
		lower_compound(node);
	else if (starts_with(node.line, "base-init-action"))
		lower_base_init(node);
	else if (starts_with(node.line, "member-init-action"))
		lower_member_init(node);
	else if (starts_with(node.line, "base-fini-action"))
		lower_base_fini(node);
	else if (starts_with(node.line, "member-fini-action"))
		lower_member_fini(node);
	else if (starts_with(node.line, "simple-declaration"))
		lower_decl_stmt(node);
	else if (starts_with(node.line, "global-init-variable"))
	{
		if (!node.children.empty())
			lower_global_variable_init(node.children[0]);
	}
	else if (starts_with(node.line, "global-fini-variable"))
	{
		if (!node.children.empty())
			lower_global_variable_fini(node.children[0]);
	}
	else if (starts_with(node.line, "return-statement"))
		lower_return(node);
	else if (starts_with(node.line, "expression-statement"))
		lower_expr_stmt(node);
	else if (starts_with(node.line, "if-statement"))
		lower_if(node);
	else if (starts_with(node.line, "while-statement"))
		lower_while(node);
	else if (starts_with(node.line, "do-statement"))
		lower_do(node);
	else if (starts_with(node.line, "for-statement"))
		lower_for(node);
	else if (starts_with(node.line, "break-statement"))
	{
		if (break_targets_.empty())
			throw runtime_error("break outside loop or switch");
		terminate("jump ^" + break_targets_.back());
	}
	else if (starts_with(node.line, "continue-statement"))
	{
		if (continue_targets_.empty())
			throw runtime_error("continue outside loop");
		terminate("jump ^" + continue_targets_.back());
	}
	else if (starts_with(node.line, "goto-statement "))
	{
		string label = node.line.substr(15);
		string block = labels_[label];
		if (block.empty())
			block = labels_[label] = fresh_block("goto");
		terminate("jump ^" + block);
	}
	else if (starts_with(node.line, "switch-statement"))
		lower_switch(node);
	else if (starts_with(node.line, "case-statement"))
	{
		map<const Node*, string>::const_iterator found = switch_labels_.find(&node);
		if (found == switch_labels_.end())
			throw runtime_error("case outside switch");
		if (!current_->terminated)
			terminate("jump ^" + found->second);
		start_block(found->second);
		if (node.children.size() > 1)
			lower_stmt(node.children[1]);
	}
	else if (starts_with(node.line, "default-statement"))
	{
		map<const Node*, string>::const_iterator found = switch_labels_.find(&node);
		if (found == switch_labels_.end())
			throw runtime_error("default outside switch");
		if (!current_->terminated)
			terminate("jump ^" + found->second);
		start_block(found->second);
		if (!node.children.empty())
			lower_stmt(node.children[0]);
	}
	else if (starts_with(node.line, "labeled-statement "))
	{
		string label = node.line.substr(18);
		string block = labels_[label];
		if (block.empty())
			block = labels_[label] = fresh_block("goto");
		terminate("jump ^" + block);
		start_block(block);
		if (!node.children.empty())
			lower_stmt(node.children[0]);
	}
	else if (!node.children.empty())
		lower_stmt(node.children[0]);
}

void FunctionLowerer::lower_decl_stmt(const Node& node)
{
	for (size_t i = 0; i < node.children.size(); ++i)
		lower_variable_decl(node.children[i]);
}

void FunctionLowerer::lower_return(const Node& node)
{
	TypePtr ret = fn_.binding->type->base;
	if (node.children.empty() || pa11::is_void_type(ret))
	{
		if (!node.children.empty())
			emit_rvalue(node.children[0]);
		emit_all_cleanups();
		terminate("return void");
		return;
	}
	if (is_reference(ret))
	{
		Value addr = ensure_pointer(emit_lvalue_addr(node.children[0]));
		addr = convert_value(addr,
		                     pa11::make_pointer(object_type(node.children[0].type)),
		                     pa11::make_pointer(ret->base));
		emit_all_cleanups();
		terminate("return ptr " + addr.text);
		return;
	}
	Value raw = emit_rvalue(node.children[0]);
	TypePtr raw_type = node.children[0].type;
	if (fn_.binding->is_inline_definition &&
	    !raw.text.empty() && raw.text[0] != '%' &&
	    raw.text[0] != '$' && raw.text[0] != '@' &&
	    pa11::is_integral_or_bool_type(node.children[0].type) &&
	    pa11::is_integral_or_bool_type(ret) &&
	    pa11::type_size(ret) != pa11::type_size(node.children[0].type))
	{
		string src = scalar_lowir_type(strip_for_value(node.children[0].type));
		string dst = scalar_lowir_type(ret);
		string tmp = fresh_temp();
		string op = pa11::type_size(ret) < pa11::type_size(node.children[0].type)
			? "trunc" : is_unsigned_type(node.children[0].type) ? "zext" : "sext";
		instr(tmp + " = convert " + op + " " + dst + " " + src + " " +
		      raw.text);
		raw = Value(dst, tmp);
		raw_type = ret;
	}
	Value value = convert_value(raw, raw_type, ret);
	emit_all_cleanups();
	terminate("return " + scalar_lowir_type(ret) + " " + value.text);
}

void FunctionLowerer::lower_expr_stmt(const Node& node)
{
	if (!node.children.empty())
		lower_discarded_expr(node.children[0]);
}

void FunctionLowerer::lower_discarded_expr(const Node& expr)
{
	if (starts_with(expr.line, "call-expression") && is_reference(expr.type))
	{
		emit_call(expr);
		return;
	}
	if (starts_with(expr.line, "binary-expression") &&
	    expr.has_op && expr.op == OP_COMMA)
	{
		emit_rvalue(expr.children[0]);
		lower_discarded_expr(expr.children[1]);
		return;
	}
	emit_rvalue(expr);
}

void FunctionLowerer::lower_if(const Node& node)
{
	string then_block = fresh_block("if_then");
	string else_block = fresh_block("if_else");
	string end_block = fresh_block("if_end");
	const Node& cond = node.children[0].children[0];
	branch_on(cond, then_block, else_block);
	start_block(then_block);
	lower_stmt(node.children[1].children[0]);
	bool then_done = current_->terminated;
	if (!current_->terminated)
		terminate("jump ^" + end_block);
	start_block(else_block);
	if (node.children.size() > 2)
		lower_stmt(node.children[2].children[0]);
	bool else_done = current_->terminated;
	if (!current_->terminated)
		terminate("jump ^" + end_block);
	if (!then_done || !else_done)
		start_block(end_block);
}

void FunctionLowerer::lower_while(const Node& node)
{
	string cond_block = fresh_block("while_cond");
	string body_block = fresh_block("while_body");
	string end_block = fresh_block("while_end");
	terminate("jump ^" + cond_block);
	start_block(cond_block);
	continue_targets_.push_back(cond_block);
	break_targets_.push_back(end_block);
	branch_on(node.children[0].children[0], body_block, end_block);
	start_block(body_block);
	lower_stmt(node.children[1]);
	if (!current_->terminated)
		terminate("jump ^" + cond_block);
	break_targets_.pop_back();
	continue_targets_.pop_back();
	start_block(end_block);
}

void FunctionLowerer::lower_do(const Node& node)
{
	string body_block = fresh_block("do_body");
	string cond_block = fresh_block("do_cond");
	string end_block = fresh_block("do_end");
	terminate("jump ^" + body_block);
	start_block(body_block);
	continue_targets_.push_back(cond_block);
	break_targets_.push_back(end_block);
	lower_stmt(node.children[0]);
	if (!current_->terminated)
		terminate("jump ^" + cond_block);
	start_block(cond_block);
	branch_on(node.children[1].children[0], body_block, end_block);
	break_targets_.pop_back();
	continue_targets_.pop_back();
	start_block(end_block);
}

void FunctionLowerer::lower_for(const Node& node)
{
	if (!node.children[0].children.empty())
	{
		const Node& init = node.children[0].children[0];
		if (starts_with(init.line, "simple-declaration"))
			lower_stmt(init);
		else
			lower_discarded_expr(init);
	}
	string cond_block = fresh_block("for_cond");
	string body_block = fresh_block("for_body");
	string iter_block = fresh_block("for_iter");
	string end_block = fresh_block("for_end");
	terminate("jump ^" + cond_block);
	start_block(cond_block);
	continue_targets_.push_back(iter_block);
	break_targets_.push_back(end_block);
	if (node.children.size() > 1 && starts_with(node.children[1].line, "condition"))
		branch_on(node.children[1].children[0], body_block, end_block);
	else
		terminate("jump ^" + body_block);
	start_block(body_block);
	lower_stmt(node.children.back());
	if (!current_->terminated)
		terminate("jump ^" + iter_block);
	start_block(iter_block);
	for (size_t i = 0; i < node.children.size(); ++i)
		if (starts_with(node.children[i].line, "iteration") &&
		    !node.children[i].children.empty())
			lower_discarded_expr(node.children[i].children[0]);
	terminate("jump ^" + cond_block);
	break_targets_.pop_back();
	continue_targets_.pop_back();
	start_block(end_block);
}

void FunctionLowerer::lower_switch_items(const Node& node,
                                         vector<pair<string, const Node*> >& cases,
                                         const Node*& default_node)
{
	if (starts_with(node.line, "switch-statement"))
		return;
	if (starts_with(node.line, "case-statement"))
		cases.push_back(make_pair(lowir_literal(node.children[0].type, node.children[0]),
		                          &node));
	else if (starts_with(node.line, "default-statement"))
		default_node = &node;
	for (size_t i = 0; i < node.children.size(); ++i)
		lower_switch_items(node.children[i], cases, default_node);
}

void FunctionLowerer::lower_switch(const Node& node)
{
	const Node& condition = node.children[0].children[0];
	Value selector;
	if (starts_with(condition.line, "condition-declaration"))
	{
		if (condition.children.empty())
			throw runtime_error("empty switch condition declaration");
		lower_variable_decl(condition.children[0]);
		selector = emit_rvalue(condition.children[0]);
	}
	else
		selector = emit_rvalue(condition);
	vector<pair<string, const Node*> > cases;
	const Node* default_node = NULL;
	lower_switch_items(node.children[1], cases, default_node);
	string dispatch = fresh_block("switch_dispatch");
	string end = fresh_block("switch_end");
	vector<string> case_blocks;
	for (size_t i = 0; i < cases.size(); ++i)
		case_blocks.push_back(fresh_block("switch_case"));
	string def = default_node == NULL ? end : fresh_block("switch_default");
	vector<const Node*> installed;
	for (size_t i = 0; i < cases.size(); ++i)
	{
		switch_labels_[cases[i].second] = case_blocks[i];
		installed.push_back(cases[i].second);
	}
	if (default_node != NULL)
	{
		switch_labels_[default_node] = def;
		installed.push_back(default_node);
	}
	terminate("jump ^" + dispatch);
	start_block(dispatch);
	ostringstream sw;
	sw << "switch " << selector.text << ", ^" << def;
	for (size_t i = 0; i < cases.size(); ++i)
		sw << ", " << cases[i].first << ":^" << case_blocks[i];
	terminate(sw.str());
	break_targets_.push_back(end);
	lower_stmt(node.children[1]);
	if (!current_->terminated)
		terminate("jump ^" + end);
	break_targets_.pop_back();
	for (size_t i = 0; i < installed.size(); ++i)
		switch_labels_.erase(installed[i]);
	start_block(end);
}

Value FunctionLowerer::emit_literal(const Node& expr)
{
	if (expr.token_text.size() > 0 &&
	    expr.token_text[expr.token_text.size() - 1] == '"')
	{
		string sym = program_.string_symbol(expr.token_text);
		string tmp = fresh_temp();
		instr(tmp + " = addr @" + sym);
		return Value("ptr", tmp);
	}
	return Value(scalar_lowir_type(expr.type), lowir_literal(expr.type, expr));
}

Value FunctionLowerer::emit_id_rvalue(const Node& expr)
{
	if (expr.binding == NULL)
		return emit_literal(expr);
	if (expr.binding->kind == BindingKind::Function)
	{
		string addr = fresh_temp();
		instr(addr + " = addr @" + program_.symbol_for(expr.binding));
		string decay = fresh_temp();
		instr(decay + " = unary decay ptr " + addr);
		return Value("ptr", decay);
	}
	TypePtr object = object_type(expr.type);
	if (object->kind == TypeKind::Array &&
	    expr.binding->owner != NULL &&
	    (expr.binding->owner->kind == ScopeKind::Namespace ||
	     expr.binding->is_static_member))
	{
		program_.demand_global_declaration(expr.binding);
		string addr = fresh_temp();
		instr(addr + " = addr @" + program_.symbol_for(expr.binding));
		string decay = fresh_temp();
		instr(decay + " = unary decay ptr " + addr);
		return Value("ptr", decay);
	}
	Value addr = emit_lvalue_addr(expr);
	TypePtr value_type = strip_for_value(expr.type);
	if (pa11::strip_cv(object_type(expr.type))->kind == TypeKind::Array)
	{
		addr = ensure_pointer(addr);
		string tmp = fresh_temp();
		instr(tmp + " = unary decay ptr " + addr.text);
		return Value("ptr", tmp);
	}
	if (pa11::strip_cv(object_type(expr.type))->kind == TypeKind::Function)
	{
		string tmp = fresh_temp();
		instr(tmp + " = unary decay ptr " + addr.text);
		return Value("ptr", tmp);
	}
	string value_low_type = scalar_lowir_type(value_type);
	if (expr.binding != NULL && expr.binding->is_bit_field)
		value_low_type = "i" + to_string(pa11::type_size(value_type) * 8);
	string tmp = fresh_temp();
	instr(tmp + " = load " + value_low_type + " " + addr.text);
	if (expr.binding != NULL && expr.binding->is_bit_field)
	{
		string value = tmp;
		if (expr.binding->bit_offset != 0)
		{
			string shifted = fresh_temp();
			instr(shifted + " = binary ushr " + value_low_type +
			      " " + value + ", " + to_string(expr.binding->bit_offset));
			value = shifted;
		}
		uint64_t mask = expr.binding->bit_width >= 64
			? ~uint64_t(0) : ((uint64_t(1) << expr.binding->bit_width) - 1);
		string masked = fresh_temp();
		instr(masked + " = binary and " + value_low_type +
		      " " + value + ", " + to_string(mask));
		tmp = masked;
	}
	return Value(scalar_lowir_type(value_type), tmp);
}

Value FunctionLowerer::emit_lvalue_addr(const Node& expr)
{
	if (starts_with(expr.line, "id-expression") && expr.binding != NULL)
	{
		if (expr.binding->kind == BindingKind::Function)
		{
			string tmp = fresh_temp();
			instr(tmp + " = addr @" + program_.symbol_for(expr.binding));
			return Value("ptr", tmp);
		}
		if (is_reference(expr.binding->type))
		{
			string tmp = fresh_temp();
			if (expr.binding->is_static_member ||
			    (expr.binding->owner != NULL &&
			     expr.binding->owner->kind == ScopeKind::Namespace))
			{
				program_.demand_global_declaration(expr.binding);
				instr(tmp + " = load ptr @" + program_.symbol_for(expr.binding));
			}
			else
				instr(tmp + " = load ptr $" + slot_for(expr.binding));
			return Value("ptr", tmp);
		}
		if (expr.binding->is_static_member ||
		    (expr.binding->owner != NULL &&
		     expr.binding->owner->kind == ScopeKind::Namespace))
		{
			program_.demand_global_declaration(expr.binding);
			return Value("ptr", "@" + program_.symbol_for(expr.binding));
		}
		string slot = slot_for(expr.binding);
		return Value("ptr", "$" + slot);
	}
	if (starts_with(expr.line, "variable ") && expr.binding != NULL)
		return Value("ptr", "$" + slot_for(expr.binding));
	if (starts_with(expr.line, "member-expression") && expr.binding != NULL)
		return emit_member_lvalue_addr(expr);
	if (starts_with(expr.line, "unary-expression") && expr.has_op &&
	    expr.op == OP_STAR)
		return emit_rvalue(expr.children[0]);
	if (starts_with(expr.line, "unary-expression") && expr.has_op &&
	    expr.op == OP_AMP)
		return emit_lvalue_addr(expr.children[0]);
	if (starts_with(expr.line, "unary-expression") && expr.has_op &&
	    (expr.op == OP_INC || expr.op == OP_DEC))
	{
		emit_unary(expr);
		return emit_lvalue_addr(expr.children[0]);
	}
	if (starts_with(expr.line, "postfix-expression") && expr.has_op)
	{
		emit_postfix(expr);
		return emit_lvalue_addr(expr.children[0]);
	}
	if (starts_with(expr.line, "binary-expression") && expr.has_op &&
	    expr.op == OP_COMMA)
	{
		emit_rvalue(expr.children[0]);
		return emit_lvalue_addr(expr.children[1]);
	}
	if (starts_with(expr.line, "subscript-expression"))
		return emit_subscript_addr(expr);
	if (starts_with(expr.line, "conditional-expression"))
		return emit_conditional(expr);
	if (starts_with(expr.line, "call-expression") && is_reference(expr.type))
		return emit_call(expr);
	if (starts_with(expr.line, "assignment-expression") &&
	    expr.has_op && (expr.op == OP_INC || expr.op == OP_DEC))
		return emit_lvalue_addr(expr.children[0]);
	if (starts_with(expr.line, "literal lvalue"))
		return emit_literal(expr);
	if (starts_with(expr.line, "cast-expression") ||
	    starts_with(expr.line, "id-expression xvalue"))
		return emit_lvalue_addr(expr.children.empty() ? expr : expr.children[0]);
	throw runtime_error("unsupported lvalue expression");
}

Value FunctionLowerer::emit_member_lvalue_addr(const Node& expr)
{
	if (expr.binding->is_static_member)
	{
		program_.demand_global_declaration(expr.binding);
		return Value("ptr", "@" + program_.symbol_for(expr.binding));
	}
	if (expr.children.empty())
		throw runtime_error("member expression missing object");
	Value base = expr.has_op && expr.op == OP_ARROW
		? emit_rvalue(expr.children[0])
		: emit_lvalue_addr(expr.children[0]);
	base = ensure_pointer(base);
	TypePtr object_record = expr.has_op && expr.op == OP_ARROW
		? pa11::strip_cv(strip_for_value(expr.children[0].type))
		: pa11::strip_cv(object_type(expr.children[0].type));
	if (object_record.get() != NULL &&
	    object_record->kind == TypeKind::Pointer)
		object_record = pa11::strip_cv(object_record->base);
	TypePtr owner_record = pa11::record_type_for_scope(expr.binding->owner);
	if (object_record.get() != NULL &&
	    object_record->kind == TypeKind::Record &&
	    owner_record.get() != NULL &&
	    !pa11::same_type(object_record, owner_record))
	{
		TypePtr direct_base = object_record->base.get() != NULL
			? pa11::strip_cv(object_record->base) : TypePtr();
		if (direct_base.get() != NULL &&
		    pa11::same_type(direct_base, owner_record))
		{
			string base_tmp = fresh_temp();
			instr(base_tmp + " = index i8 [projection=base_subobject] " +
			      base.text + ", 0");
			base = Value("ptr", base_tmp);
		}
	}
	string tmp = fresh_temp();
	instr(tmp + " = index i8 [projection=field] " + base.text +
	      ", " + to_string(expr.binding->member_offset));
	if (is_reference(expr.binding->type))
	{
		string ref = fresh_temp();
		instr(ref + " = load ptr " + tmp);
		return Value("ptr", ref);
	}
	return Value("ptr", tmp);
}

Value FunctionLowerer::emit_subscript_addr(const Node& expr)
{
	Value base;
	if (starts_with(expr.children[0].line, "conditional-expression") &&
	    expr.children[0].category == ValueCategory::LValue &&
	    pa11::strip_cv(object_type(expr.children[0].type))->kind == TypeKind::Array)
		base = emit_lvalue_addr(expr.children[0]);
	else
		base = emit_rvalue(expr.children[0]);
	base = ensure_pointer(base);
	Value index = emit_rvalue(expr.children[1]);
	TypePtr object = pa11::strip_cv(object_type(expr.type));
	if (object->kind == TypeKind::Record)
	{
		string scaled = fresh_temp();
		instr(scaled + " = binary mul i64 " + index.text + ", " +
		      to_string(pa11::type_size(object)));
		string tmp = fresh_temp();
		instr(tmp + " = index i8 [projection=array_element] " + base.text +
		      ", " + scaled);
		return Value("ptr", tmp);
	}
	string tmp = fresh_temp();
	string elem = scalar_lowir_type(expr.type);
	instr(tmp + " = index " + elem +
	      " [projection=array_element] " + base.text + ", " + index.text);
	return Value("ptr", tmp);
}

Value FunctionLowerer::emit_rvalue(const Node& expr)
{
	if (starts_with(expr.line, "literal "))
		return emit_literal(expr);
	if (starts_with(expr.line, "id-expression") ||
	    starts_with(expr.line, "member-expression") ||
	    starts_with(expr.line, "variable "))
		return emit_id_rvalue(expr);
	if (starts_with(expr.line, "binary-expression"))
		return emit_binary(expr);
	if (starts_with(expr.line, "assignment-expression"))
		return emit_assignment(expr);
	if (starts_with(expr.line, "unary-expression"))
		return emit_unary(expr);
	if (starts_with(expr.line, "postfix-expression"))
		return emit_postfix(expr);
	if (starts_with(expr.line, "call-expression"))
	{
		Value value = emit_call(expr);
		if (is_reference(expr.type))
		{
			TypePtr value_type = strip_for_value(expr.type);
			string tmp = fresh_temp();
			instr(tmp + " = load " + scalar_lowir_type(value_type) +
			      " " + value.text);
			return Value(scalar_lowir_type(value_type), tmp);
		}
		return value;
	}
	if (starts_with(expr.line, "new-expression"))
	{
		Value size_value;
		if (expr.binding != NULL)
		{
			TypePtr object = pa11::strip_cv(pa11::strip_cv(expr.type)->base);
			string size_tmp = fresh_temp();
			instr(size_tmp + " = convert sext i64 i32 " +
			      to_string(pa11::type_size(object)));
			size_value = Value("i64", size_tmp);
		}
		Value storage = ensure_pointer(emit_rvalue(expr.children[0]));
		if (expr.binding != NULL)
		{
			program_.demand_function_declaration(expr.binding);
			string call_tmp = fresh_temp();
			instr(call_tmp + " = call ptr @" + program_.symbol_for(expr.binding) +
			      "(" + size_value.text + ", " + storage.text + ")");
			storage = Value("ptr", call_tmp);
		}
		Binding* ctor = expr.direct_call;
		if (ctor != NULL)
		{
			program_.demand_function_declaration(ctor);
			program_.demand_inline_function(ctor);
			vector<string> lowered;
			lowered.push_back(storage.text);
			for (size_t i = 1; i < expr.children.size(); ++i)
			{
				TypePtr param = ctor->type->parameters[i];
				lowered.push_back(convert_value(emit_rvalue(expr.children[i]),
				                                expr.children[i].type,
				                                param).text);
			}
			ostringstream call;
			call << "call void @" << program_.symbol_for(ctor) << "(";
			for (size_t i = 0; i < lowered.size(); ++i)
			{
				if (i != 0)
					call << ", ";
				call << lowered[i];
			}
			call << ")";
			instr(call.str());
		}
		return convert_value(storage,
		                     expr.children[0].type,
		                     expr.type);
	}
	if (starts_with(expr.line, "subscript-expression"))
	{
		Value addr = emit_subscript_addr(expr);
		string tmp = fresh_temp();
		instr(tmp + " = load " + scalar_lowir_type(expr.type) + " " + addr.text);
		return Value(scalar_lowir_type(expr.type), tmp);
	}
	if (starts_with(expr.line, "cast-expression") ||
	    starts_with(expr.line, "id-expression xvalue"))
		return emit_cast(expr);
	if (starts_with(expr.line, "conditional-expression"))
	{
		if (expr.category == ValueCategory::LValue)
			return emit_conditional_value(expr);
		return emit_conditional(expr);
	}
	if (starts_with(expr.line, "sizeof-expression"))
	{
		string tmp = fresh_temp();
		instr(tmp + " = const i64 " + expr.token_text);
		return Value("i64", tmp);
	}
	if (starts_with(expr.line, "pseudo-destructor-expression"))
	{
		if (expr.direct_call != NULL && !expr.children.empty())
		{
			program_.demand_function_declaration(expr.direct_call);
			program_.demand_inline_function(expr.direct_call);
			Value addr = expr.has_op && expr.op == OP_ARROW
				? emit_rvalue(expr.children[0])
				: emit_lvalue_addr(expr.children[0]);
			addr = ensure_pointer(addr);
			instr("call void @" + program_.symbol_for(expr.direct_call) +
			      "(" + addr.text + ")");
		}
		else if (!expr.children.empty())
			emit_rvalue(expr.children[0]);
		return Value("void", "");
	}
	throw runtime_error("unsupported rvalue expression: " + expr.line);
}

Value FunctionLowerer::convert_value(Value value, TypePtr from, TypePtr to)
{
	string dst = scalar_lowir_type(to);
	string src = scalar_lowir_type(strip_for_value(from));
	TypePtr from_bare = pa11::strip_cv(strip_for_value(from));
	TypePtr to_bare = pa11::strip_cv(strip_for_value(to));
	if (from_bare->kind == TypeKind::Fundamental &&
	    from_bare->fundamental == FT_NULLPTR_T &&
	    to_bare->kind == TypeKind::Pointer)
	{
		string tmp = fresh_temp();
		instr(tmp + " = copy ptr " + value.text);
		return Value(dst, tmp);
	}
	if (dst == src)
	{
		if (from_bare->kind == TypeKind::Pointer &&
		    to_bare->kind == TypeKind::Pointer)
		{
			TypePtr from_pointee = pa11::strip_cv(from_bare->base);
			TypePtr to_pointee = pa11::strip_cv(to_bare->base);
			if (from_pointee->kind == TypeKind::Record &&
			    to_pointee->kind == TypeKind::Record &&
			    from_pointee->base.get() != NULL &&
			    pa11::same_type(pa11::strip_cv(from_pointee->base),
			                    to_pointee))
			{
				string tmp = fresh_temp();
				instr(tmp + " = index i8 [projection=base_subobject] " +
				      value.text + ", 0");
				return Value("ptr", tmp);
			}
		}
		return Value(dst, value.text);
	}
	if (value.text != "" && value.text[0] != '%' &&
	    value.text[0] != '$' && value.text[0] != '@' &&
	    !is_float_type(from) && !is_float_type(to))
		return Value(dst, value.text);
	string op = "copy";
	if (dst == "ptr" || src == "ptr")
		op = "copy";
	else if (starts_with(dst, "f") && starts_with(src, "f"))
		op = pa11::type_size(to) > pa11::type_size(from) ? "fpext" : "fptrunc";
	else if (starts_with(dst, "f"))
		op = is_unsigned_type(from) ? "uitofp" : "sitofp";
	else if (starts_with(src, "f"))
		op = is_unsigned_type(to) ? "fptoui" : "fptosi";
	else if (pa11::type_size(to) == pa11::type_size(from))
		op = "copy";
	else if (pa11::type_size(to) < pa11::type_size(from))
		op = "trunc";
	else
		op = is_unsigned_type(from) ? "zext" : "sext";
	string tmp = fresh_temp();
	if (op == "copy")
		instr(tmp + " = copy " + dst + " " + value.text);
	else
		instr(tmp + " = convert " + op + " " + dst + " " + src + " " +
		      value.text);
	return Value(dst, tmp);
}

Value FunctionLowerer::convert_binary_value(Value value, TypePtr from, TypePtr to)
{
	string dst = scalar_lowir_type(to);
	string src = scalar_lowir_type(strip_for_value(from));
	if (dst == "i64" && src != dst && is_unsigned_type(to) &&
	    value.text != "" &&
	    value.text[0] != '%' && value.text[0] != '$' &&
	    value.text[0] != '@' && !is_float_type(from) && !is_float_type(to))
	{
		string tmp = fresh_temp();
		instr(tmp + " = convert " + string(is_unsigned_type(from) ? "zext" : "sext") +
		      " i64 " + src + " " + value.text);
		return Value("i64", tmp);
	}
	return convert_value(value, from, to);
}

Value FunctionLowerer::bool_value(Value value, TypePtr type)
{
	string src = scalar_lowir_type(strip_for_value(type));
	string cmp_type = (!is_float_type(type) && src != "ptr") ? "i64" : src;
	string tmp = fresh_temp();
	string zero = is_float_type(type) ? "0.0" : (src == "ptr" ? "nullptr" : "0");
	instr(tmp + " = cmp ne " + cmp_type + " " + value.text + ", " + zero);
	return Value("u8", tmp);
}

Value FunctionLowerer::ensure_pointer(Value storage)
{
	if (storage.text.empty())
		return storage;
	if (storage.text[0] != '$' && storage.text[0] != '@')
		return storage;
	string tmp = fresh_temp();
	instr(tmp + " = addr " + storage.text);
	return Value("ptr", tmp);
}

void FunctionLowerer::branch_logical_operand(const Node& expr,
                                             const string& yes,
                                             const string& no)
{
	if (starts_with(expr.line, "binary-expression") && expr.has_op &&
	    (expr.op == OP_LAND || expr.op == OP_LOR))
	{
		Value value = emit_rvalue(expr);
		terminate("branch " + value.text + ", ^" + yes + ", ^" + no);
		return;
	}
	branch_on(expr, yes, no);
}

void FunctionLowerer::branch_with_unwind_cleanups(const Node& expr,
                                                  const string& yes,
                                                  const string& no)
{
	string dispatch = fresh_block("call_unwind_dispatch");
	string end = fresh_block("call_unwind_end");
	instr("eh_try ^" + dispatch);
	++eh_try_depth_;
	Value cond = emit_rvalue(expr);
	if (is_float_type(expr.type))
		cond = bool_value(cond, expr.type);
	--eh_try_depth_;
	instr("eh_end");
	terminate("jump ^" + end);
	start_block(dispatch);
	emit_unwind_cleanups();
	terminate("resume");
	start_block(end);
	terminate("branch " + cond.text + ", ^" + yes + ", ^" + no);
}

Value FunctionLowerer::emit_binary(const Node& expr)
{
	if (expr.has_op && expr.op == OP_COMMA)
	{
		emit_rvalue(expr.children[0]);
		return emit_rvalue(expr.children[1]);
	}
	if (expr.has_op && (expr.op == OP_LAND || expr.op == OP_LOR))
		return emit_logical_binary(expr);
	Value lhs = emit_rvalue(expr.children[0]);
	Value rhs = emit_rvalue(expr.children[1]);
	TypePtr lhs_type = strip_for_value(expr.children[0].type);
	TypePtr rhs_type = strip_for_value(expr.children[1].type);
	if ((expr.op == OP_PLUS || expr.op == OP_MINUS) &&
	    scalar_lowir_type(expr.type) == "ptr")
		return emit_pointer_index_binary(expr, lhs, rhs, lhs_type, rhs_type);
	if (expr.op == OP_MINUS &&
	    pa11::strip_cv(lhs_type)->kind == TypeKind::Pointer &&
	    pa11::strip_cv(rhs_type)->kind == TypeKind::Pointer)
		return emit_pointer_difference(expr, lhs, rhs, lhs_type);
	string op;
	bool cmp = false;
	switch (expr.op)
	{
	case OP_PLUS: op = "add"; break;
	case OP_MINUS: op = "sub"; break;
	case OP_STAR: op = "mul"; break;
	case OP_DIV: op = is_unsigned_type(expr.children[0].type) ? "udiv" : "div"; break;
	case OP_MOD: op = is_unsigned_type(expr.children[0].type) ? "umod" : "mod"; break;
	case OP_AMP: op = "and"; break;
	case OP_BOR: op = "or"; break;
	case OP_XOR: op = "xor"; break;
	case OP_LSHIFT: op = "shl"; break;
	case OP_RSHIFT: op = is_unsigned_type(expr.children[0].type) ? "ushr" : "shr"; break;
	case OP_EQ: op = "eq"; cmp = true; break;
	case OP_NE: op = "ne"; cmp = true; break;
	case OP_LT: op = is_unsigned_type(expr.children[0].type) ? "ult" : "lt"; cmp = true; break;
	case OP_LE: op = is_unsigned_type(expr.children[0].type) ? "ule" : "le"; cmp = true; break;
	case OP_GT: op = is_unsigned_type(expr.children[0].type) ? "ugt" : "gt"; cmp = true; break;
	case OP_GE: op = is_unsigned_type(expr.children[0].type) ? "uge" : "ge"; cmp = true; break;
	default: throw runtime_error("unsupported binary operator");
	}
	TypePtr op_type = cmp ? lowir_common_type(expr.children[0].type,
	                                          expr.children[1].type)
	                     : expr.type;
	if (expr.op == OP_DIV)
		op = is_unsigned_type(op_type) ? "udiv" : "div";
	else if (expr.op == OP_MOD)
		op = is_unsigned_type(op_type) ? "umod" : "mod";
	else if (expr.op == OP_RSHIFT)
		op = is_unsigned_type(op_type) ? "ushr" : "shr";
	else if (expr.op == OP_LT)
		op = is_unsigned_type(op_type) ? "ult" : "lt";
	else if (expr.op == OP_LE)
		op = is_unsigned_type(op_type) ? "ule" : "le";
	else if (expr.op == OP_GT)
		op = is_unsigned_type(op_type) ? "ugt" : "gt";
	else if (expr.op == OP_GE)
		op = is_unsigned_type(op_type) ? "uge" : "ge";
	if (cmp && scalar_lowir_type(op_type) == "ptr")
	{
		if (scalar_lowir_type(strip_for_value(expr.children[0].type)) != "ptr")
			lhs = convert_binary_value(lhs, expr.children[0].type, op_type);
		if (scalar_lowir_type(strip_for_value(expr.children[1].type)) != "ptr")
			rhs = convert_binary_value(rhs, expr.children[1].type, op_type);
	}
	else
	{
		lhs = convert_binary_value(lhs, expr.children[0].type, op_type);
		rhs = convert_binary_value(rhs, expr.children[1].type, op_type);
	}
	string type = scalar_lowir_type(op_type);
	string tmp = fresh_temp();
	instr(tmp + " = " + string(cmp ? "cmp " : "binary ") + op + " " +
	      type + " " + lhs.text + ", " + rhs.text);
	return Value(cmp ? "u8" : scalar_lowir_type(expr.type), tmp);
}

Value FunctionLowerer::emit_assignment(const Node& expr)
{
	if (expr.op == OP_ASS &&
	    starts_with(expr.children[0].line, "member-expression"))
	{
		TypePtr lhs_type = object_type(expr.children[0].type);
		Value rhs = emit_rvalue(expr.children[1]);
		rhs = convert_binary_value(rhs, expr.children[1].type, lhs_type);
		Value addr = emit_lvalue_addr(expr.children[0]);
		if (expr.children[0].binding != NULL &&
		    expr.children[0].binding->is_bit_field)
		{
			Binding* field = expr.children[0].binding;
			string low_type = scalar_lowir_type(lhs_type);
			uint64_t mask = field->bit_width >= 64
				? ~uint64_t(0) : ((uint64_t(1) << field->bit_width) - 1);
			string masked = fresh_temp();
			instr(masked + " = binary and " + low_type + " " +
			      rhs.text + ", " + to_string(mask));
			string shifted = masked;
			uint64_t storage_mask = mask << field->bit_offset;
			if (field->bit_offset != 0)
			{
				shifted = fresh_temp();
				instr(shifted + " = binary shl " + low_type + " " +
				      masked + ", " + to_string(field->bit_offset));
			}
			string oldv = fresh_temp();
			instr(oldv + " = load " + low_type + " " + addr.text);
			string cleared = fresh_temp();
			instr(cleared + " = binary and " + low_type + " " + oldv +
			      ", " + to_string(~storage_mask));
			string merged = fresh_temp();
			instr(merged + " = binary or " + low_type + " " + cleared +
			      ", " + shifted);
			instr("store " + low_type + " " + merged + ", " + addr.text);
			return rhs;
		}
		instr("store " + scalar_lowir_type(lhs_type) + " " + rhs.text +
		      ", " + addr.text);
		return rhs;
	}
	Value addr = emit_lvalue_addr(expr.children[0]);
	TypePtr lhs_type = object_type(expr.children[0].type);
	if (expr.op != OP_ASS)
	{
		Value oldv = emit_rvalue(expr.children[0]);
		Value rhs = emit_rvalue(expr.children[1]);
		if (scalar_lowir_type(lhs_type) == "ptr" &&
		    (expr.op == OP_PLUSASS || expr.op == OP_MINUSASS))
		{
			TypePtr ptr = pa11::strip_cv(strip_for_value(lhs_type));
			uint64_t scale = pa11::type_size(ptr->base);
			string offset = rhs.text;
			if (scale != 1)
			{
				string mul = fresh_temp();
				instr(mul + " = binary mul i64 " + offset + ", " +
				      to_string(scale));
				offset = mul;
			}
			if (expr.op == OP_MINUSASS)
			{
				string neg = fresh_temp();
				instr(neg + " = binary sub i64 0, " + offset);
				offset = neg;
			}
			string tmp = fresh_temp();
			instr(tmp + " = index i8 " + oldv.text + ", " + offset);
			instr("store ptr " + tmp + ", " + addr.text);
			return Value("ptr", tmp);
		}
		rhs = convert_value(rhs, expr.children[1].type, lhs_type);
		ETokenType op = expr.op == OP_PLUSASS ? OP_PLUS :
		                expr.op == OP_MINUSASS ? OP_MINUS :
		                expr.op == OP_STARASS ? OP_STAR :
		                expr.op == OP_DIVASS ? OP_DIV : OP_PLUS;
		string tmp = fresh_temp();
		instr(tmp + " = binary " + string(op == OP_MINUS ? "sub" :
		      op == OP_STAR ? "mul" : op == OP_DIV ? "div" : "add") + " " +
		      scalar_lowir_type(lhs_type) + " " + oldv.text + ", " + rhs.text);
		rhs = Value(scalar_lowir_type(lhs_type), tmp);
		instr("store " + scalar_lowir_type(lhs_type) + " " +
		      rhs.text + ", " + addr.text);
		return rhs;
	}
	Value rhs = emit_rvalue(expr.children[1]);
	rhs = convert_binary_value(rhs, expr.children[1].type, lhs_type);
	instr("store " + scalar_lowir_type(lhs_type) + " " + rhs.text + ", " + addr.text);
	return rhs;
}

Value FunctionLowerer::emit_unary(const Node& expr)
{
	if (expr.op == OP_AMP)
		return ensure_pointer(emit_lvalue_addr(expr.children[0]));
	if (expr.op == OP_STAR)
	{
		Value addr = emit_lvalue_addr(expr);
		string tmp = fresh_temp();
		instr(tmp + " = load " + scalar_lowir_type(expr.type) + " " + addr.text);
		return Value(scalar_lowir_type(expr.type), tmp);
	}
	if (expr.op == OP_INC || expr.op == OP_DEC)
	{
		Value addr = emit_lvalue_addr(expr.children[0]);
		TypePtr value_type = strip_for_value(expr.children[0].type);
		string oldtmp = fresh_temp();
		instr(oldtmp + " = load " + scalar_lowir_type(value_type) + " " +
		      addr.text);
		Value oldv(scalar_lowir_type(value_type), oldtmp);
		string one = "1";
		string tmp;
		if (oldv.type == "ptr")
		{
			TypePtr ptr = pa11::strip_cv(strip_for_value(expr.type));
			uint64_t scale = pa11::type_size(ptr->base);
			if (expr.op == OP_DEC && scale == 1)
				one = "-1";
			else if (expr.op == OP_DEC)
			{
				string mul = fresh_temp();
				instr(mul + " = binary mul i64 1, " + to_string(scale));
				string neg = fresh_temp();
				instr(neg + " = binary sub i64 0, " + mul);
				one = neg;
			}
			else if (scale != 1)
			{
				string mul = fresh_temp();
				instr(mul + " = binary mul i64 1, " + to_string(scale));
				one = mul;
			}
			tmp = fresh_temp();
			instr(tmp + " = index i8 " + oldv.text + ", " + one);
		}
		else
		{
			tmp = fresh_temp();
			instr(tmp + " = binary " + string(expr.op == OP_INC ? "add" : "sub") +
			      " " + scalar_lowir_type(expr.type) + " " + oldv.text + ", " + one);
		}
		instr("store " + scalar_lowir_type(expr.type) + " " + tmp + ", " + addr.text);
		return Value(scalar_lowir_type(expr.type), tmp);
	}
	Value inner = emit_rvalue(expr.children[0]);
	if (expr.op == OP_PLUS)
		return inner;
	string op = expr.op == OP_MINUS ? "neg" :
	            expr.op == OP_COMPL ? "bitnot" : "not";
	if (expr.op == OP_LNOT)
	{
		string tmp = fresh_temp();
		string cmp_type = (!is_float_type(expr.children[0].type) &&
		                   inner.type != "ptr") ? "i64" : inner.type;
		string zero = is_float_type(expr.children[0].type) ? "0.0" :
		              (inner.type == "ptr" ? "nullptr" : "0");
		instr(tmp + " = cmp eq " + cmp_type + " " + inner.text + ", " + zero);
		return Value("u8", tmp);
	}
	string tmp = fresh_temp();
	instr(tmp + " = unary " + op + " " + inner.type + " " + inner.text);
	return Value(inner.type, tmp);
}

Value FunctionLowerer::emit_postfix(const Node& expr)
{
	Value addr = emit_lvalue_addr(expr.children[0]);
	TypePtr value_type = strip_for_value(expr.children[0].type);
	string oldtmp = fresh_temp();
	instr(oldtmp + " = load " + scalar_lowir_type(value_type) + " " + addr.text);
	Value oldv(scalar_lowir_type(value_type), oldtmp);
	string one = "1";
	string tmp;
	if (oldv.type == "ptr")
	{
		TypePtr ptr = pa11::strip_cv(strip_for_value(expr.type));
		uint64_t scale = pa11::type_size(ptr->base);
		if (expr.op == OP_DEC && scale == 1)
			one = "-1";
		else if (expr.op == OP_DEC)
		{
			string mul = fresh_temp();
			instr(mul + " = binary mul i64 1, " + to_string(scale));
			string neg = fresh_temp();
			instr(neg + " = binary sub i64 0, " + mul);
			one = neg;
		}
		else if (scale != 1)
		{
			string mul = fresh_temp();
			instr(mul + " = binary mul i64 1, " + to_string(scale));
			one = mul;
		}
		tmp = fresh_temp();
		instr(tmp + " = index i8 " + oldv.text + ", " + one);
	}
	else
	{
		tmp = fresh_temp();
		instr(tmp + " = binary " + string(expr.op == OP_INC ? "add" : "sub") +
		      " " + oldv.type + " " + oldv.text + ", 1");
	}
	instr("store " + oldv.type + " " + tmp + ", " + addr.text);
	return oldv;
}

Value FunctionLowerer::emit_cast(const Node& expr)
{
	if (pa11::is_void_type(expr.type))
	{
		if (expr.children[0].category == ValueCategory::LValue &&
		    pa11::strip_cv(object_type(expr.children[0].type))->kind ==
		    TypeKind::Record)
			ensure_pointer(emit_lvalue_addr(expr.children[0]));
		else
			emit_rvalue(expr.children[0]);
		return Value("void", "");
	}
	if (is_reference(expr.type))
		return emit_rvalue(expr.children[0]);
	if (pa11::strip_cv(strip_for_value(expr.children[0].type))->kind == TypeKind::Enum &&
	    pa11::strip_cv(strip_for_value(expr.type))->kind == TypeKind::Fundamental &&
	    scalar_lowir_type(expr.children[0].type) == scalar_lowir_type(expr.type))
	{
		Value inner = emit_rvalue(expr.children[0]);
		string tmp = fresh_temp();
		instr(tmp + " = copy " + scalar_lowir_type(expr.type) + " " + inner.text);
		return Value(scalar_lowir_type(expr.type), tmp);
	}
	return convert_value(emit_rvalue(expr.children[0]),
	                     expr.children[0].type,
	                     expr.type);
}

Value FunctionLowerer::emit_conditional(const Node& expr)
{
	string type = expr.category == ValueCategory::LValue ? "ptr" :
	              scalar_lowir_type(expr.type);
	string slot = fresh_aux_slot(expr.category == ValueCategory::LValue ?
	                             "condaddr" : "cond", type);
	string yes = fresh_block(expr.category == ValueCategory::LValue ?
	                         "condaddr_then" : "cond_then");
	string no = fresh_block(expr.category == ValueCategory::LValue ?
	                        "condaddr_else" : "cond_else");
	string end = fresh_block(expr.category == ValueCategory::LValue ?
	                         "condaddr_end" : "cond_end");
	Value cond = emit_rvalue(expr.children[0]);
	if (is_float_type(expr.children[0].type))
		cond = bool_value(cond, expr.children[0].type);
	terminate("branch " + cond.text + ", ^" + yes + ", ^" + no);
	start_block(yes);
	Value yv = expr.category == ValueCategory::LValue
		? ensure_pointer(emit_lvalue_addr(expr.children[1]))
		: convert_value(emit_rvalue(expr.children[1]),
		                expr.children[1].type,
		                expr.type);
	if (expr.category == ValueCategory::LValue)
		yv = convert_value(yv,
		                   pa11::make_pointer(object_type(expr.children[1].type)),
		                   pa11::make_pointer(expr.type));
	instr("store " + type + " " + yv.text + ", $" + slot);
	terminate("jump ^" + end);
	start_block(no);
	Value nv = expr.category == ValueCategory::LValue
		? ensure_pointer(emit_lvalue_addr(expr.children[2]))
		: convert_value(emit_rvalue(expr.children[2]),
		                expr.children[2].type,
		                expr.type);
	if (expr.category == ValueCategory::LValue)
		nv = convert_value(nv,
		                   pa11::make_pointer(object_type(expr.children[2].type)),
		                   pa11::make_pointer(expr.type));
	instr("store " + type + " " + nv.text + ", $" + slot);
	terminate("jump ^" + end);
	start_block(end);
	string tmp = fresh_temp();
	instr(tmp + " = load " + type + " $" + slot);
	return Value(type, tmp);
}

Value FunctionLowerer::emit_conditional_value(const Node& expr)
{
	string type = scalar_lowir_type(expr.type);
	string slot = fresh_aux_slot("cond", type);
	string yes = fresh_block("cond_then");
	string no = fresh_block("cond_else");
	string end = fresh_block("cond_end");
	Value cond = emit_rvalue(expr.children[0]);
	if (is_float_type(expr.children[0].type))
		cond = bool_value(cond, expr.children[0].type);
	terminate("branch " + cond.text + ", ^" + yes + ", ^" + no);
	start_block(yes);
	Value yv = convert_value(emit_rvalue(expr.children[1]),
	                         expr.children[1].type,
	                         expr.type);
	instr("store " + type + " " + yv.text + ", $" + slot);
	terminate("jump ^" + end);
	start_block(no);
	Value nv = convert_value(emit_rvalue(expr.children[2]),
	                         expr.children[2].type,
	                         expr.type);
	instr("store " + type + " " + nv.text + ", $" + slot);
	terminate("jump ^" + end);
	start_block(end);
	string tmp = fresh_temp();
	instr(tmp + " = load " + type + " $" + slot);
	return Value(type, tmp);
}

void FunctionLowerer::branch_on(const Node& expr, const string& yes, const string& no)
{
	if (starts_with(expr.line, "condition-declaration"))
	{
		if (expr.children.empty())
			throw runtime_error("empty condition declaration");
		lower_variable_decl(expr.children[0]);
		Value cond = emit_rvalue(expr.children[0]);
		if (is_float_type(expr.children[0].type))
			cond = bool_value(cond, expr.children[0].type);
		terminate("branch " + cond.text + ", ^" + yes + ", ^" + no);
		return;
	}
	if (starts_with(expr.line, "binary-expression") && expr.has_op &&
	    expr.op == OP_LOR)
	{
		string rhs = fresh_block("lor_rhs");
		branch_on(expr.children[0], yes, rhs);
		start_block(rhs);
		branch_on(expr.children[1], yes, no);
		return;
	}
	if (starts_with(expr.line, "binary-expression") && expr.has_op &&
	    expr.op == OP_LAND)
	{
		string rhs = fresh_block("land_rhs");
		branch_on(expr.children[0], rhs, no);
		start_block(rhs);
		branch_on(expr.children[1], yes, no);
		return;
	}
	if (eh_try_depth_ == 0 && has_active_cleanups() &&
	    node_contains_call_expression(expr))
	{
		branch_with_unwind_cleanups(expr, yes, no);
		return;
	}
	Value cond = emit_rvalue(expr);
	if (is_float_type(expr.type))
		cond = bool_value(cond, expr.type);
	terminate("branch " + cond.text + ", ^" + yes + ", ^" + no);
}


}  // namespace internal
}  // namespace pa14
