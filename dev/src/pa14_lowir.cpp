#include "pa14_lowir_internal.h"

namespace pa14 {
namespace internal {

bool node_contains_call_expression(const Node& node)
{
	if (starts_with(node.line, "call-expression"))
		return true;
	for (size_t i = 0; i < node.children.size(); ++i)
		if (node_contains_call_expression(node.children[i]))
			return true;
	return false;
}

bool node_contains_return_statement(const Node& node)
{
	if (starts_with(node.line, "return-statement"))
		return true;
	for (size_t i = 0; i < node.children.size(); ++i)
		if (node_contains_return_statement(node.children[i]))
			return true;
	return false;
}

bool record_has_default_constructor_for_array(TypePtr type)
{
	TypePtr bare = pa11::strip_cv(type);
	if (bare->kind != TypeKind::Record || bare->scope == NULL)
		return false;
	map<string, vector<Binding*> >::const_iterator found =
		bare->scope->members.find(bare->scope->name);
	if (found == bare->scope->members.end())
		return false;
	for (size_t i = 0; i < found->second.size(); ++i)
		if (found->second[i]->kind == BindingKind::Function &&
		    found->second[i]->type->kind == TypeKind::Function &&
		    found->second[i]->type->parameters.size() == 1)
			return true;
	return false;
}

Binding* find_record_destructor(TypePtr type)
{
	TypePtr bare = pa11::strip_cv(type);
	if (bare->kind != TypeKind::Record || bare->scope == NULL)
		return NULL;
	string name = "~" + bare->scope->name;
	map<string, vector<Binding*> >::const_iterator found =
		bare->scope->members.find(name);
	if (found == bare->scope->members.end())
		return NULL;
	for (size_t i = 0; i < found->second.size(); ++i)
		if (found->second[i]->kind == BindingKind::Function)
			return found->second[i];
	return NULL;
}

bool parameter_type_needs_destructor(TypePtr type)
{
	TypePtr bare = pa11::strip_cv(type);
	if (bare->kind == TypeKind::Array)
		return parameter_type_needs_destructor(bare->base);
	if (bare->kind != TypeKind::Record)
		return false;
	Binding* dtor = find_record_destructor(bare);
	if (dtor != NULL &&
	    (!dtor->is_noop_destructor || !dtor->is_generated_default_destructor))
		return true;
	pa11::layout_record_type(bare);
	if (bare->base.get() != NULL &&
	    parameter_type_needs_destructor(bare->base))
		return true;
	for (size_t i = 0; i < bare->fields.size(); ++i)
		if (parameter_type_needs_destructor(bare->fields[i]->type))
			return true;
	return false;
}

bool record_has_base_subobject(TypePtr source, TypePtr target)
{
	TypePtr bare = pa11::strip_cv(source);
	TypePtr wanted = pa11::strip_cv(target);
	if (bare->kind != TypeKind::Record || wanted->kind != TypeKind::Record)
		return false;
	for (TypePtr base = bare->base; base.get() != NULL;
	     base = pa11::strip_cv(base)->base)
	{
		TypePtr stripped = pa11::strip_cv(base);
		if (pa11::same_type(stripped, wanted))
			return true;
		if (record_has_base_subobject(stripped, wanted))
			return true;
	}
	return false;
}

uint64_t base_subobject_offset(TypePtr source, TypePtr target)
{
	if (source.get() == NULL || target.get() == NULL)
		return 0;
	TypePtr cur = pa11::strip_cv(source);
	TypePtr wanted = pa11::strip_cv(target);
	uint64_t offset = 0;
	if (cur->kind != TypeKind::Record || wanted->kind != TypeKind::Record)
		return 0;
	for (;;)
	{
		if (cur->base.get() == NULL)
			return 0;
		pa11::layout_record_type(cur);
		TypePtr direct = pa11::strip_cv(cur->base);
		offset += cur->direct_base_offset;
		if (pa11::same_type(direct, wanted))
			return offset;
		cur = direct;
		if (cur->kind != TypeKind::Record)
			return 0;
	}
}

Binding* find_record_copy_move_constructor(TypePtr type, bool move)
{
	TypePtr bare = pa11::strip_cv(type);
	if (bare->kind != TypeKind::Record || bare->scope == NULL)
		return NULL;
	map<string, vector<Binding*> >::const_iterator found =
		bare->scope->members.find(bare->scope->name);
	if (found == bare->scope->members.end())
		return NULL;
	for (size_t i = 0; i < found->second.size(); ++i)
	{
		Binding* binding = found->second[i];
		if (binding->kind != BindingKind::Function ||
		    binding->type->kind != TypeKind::Function ||
		    binding->type->parameters.size() != 2 ||
		    !is_reference(binding->type->parameters[1]))
			continue;
		TypePtr param = binding->type->parameters[1];
		if (move && param->kind != TypeKind::RValueReference)
			continue;
		if (!move && param->kind != TypeKind::LValueReference)
			continue;
		if (pa11::same_type(pa11::strip_cv(param->base), bare))
			return binding;
	}
	return NULL;
}

Binding* find_record_copy_move_assignment(TypePtr type, bool move)
{
	TypePtr bare = pa11::strip_cv(type);
	if (bare->kind != TypeKind::Record || bare->scope == NULL)
		return NULL;
	map<string, vector<Binding*> >::const_iterator found =
		bare->scope->members.find("operator=");
	if (found == bare->scope->members.end())
		return NULL;
	for (size_t i = 0; i < found->second.size(); ++i)
	{
		Binding* binding = found->second[i];
		if (binding->kind != BindingKind::Function ||
		    binding->type->kind != TypeKind::Function ||
		    binding->type->parameters.size() != 2 ||
		    !is_reference(binding->type->parameters[1]))
			continue;
		TypePtr param = binding->type->parameters[1];
		if (move && param->kind != TypeKind::RValueReference)
			continue;
		if (!move && param->kind != TypeKind::LValueReference)
			continue;
		if (pa11::same_type(pa11::strip_cv(param->base), bare))
			return binding;
	}
	return NULL;
}

FunctionLowerer::FunctionLowerer(ProgramLowerer& program, const Node& fn)
	: program_(program),
	  fn_(fn),
	  current_(NULL),
	  temp_counter_(0),
	  block_counter_(0),
	  aux_slot_counter_(0),
	  eh_try_depth_(0),
	  call_temp_cleanup_defer_depth_(0),
	  logical_call_result_consumed_(false),
	  call_result_store_consumed_(false)
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

Value FunctionLowerer::emit_base_subobject_addr(Value object,
                                                TypePtr source,
                                                TypePtr target)
{
	string addr = fresh_temp();
	instr(addr + " = index i8 [projection=base_subobject] " +
	      object.text + ", " + to_string(base_subobject_offset(source, target)));
	return Value("ptr", addr);
}

void FunctionLowerer::terminate(const string& text)
{
	if (current_ == NULL || current_->terminated)
		return;
	current_->instrs.push_back("    " + text);
	current_->terminated = true;
}

void FunctionLowerer::lower_vptr_store(TypePtr record)
{
	TypePtr bare = pa11::strip_cv(record);
	if (bare->kind != TypeKind::Record || !bare->is_polymorphic)
		return;
	program_.demand_vtable(bare);
	string self = fresh_temp();
	instr(self + " = load ptr $this");
	string vt = fresh_temp();
	instr(vt + " = addr @" + vtable_symbol_for_record(bare));
	string addr_point = fresh_temp();
	instr(addr_point + " = index i8 " + vt + ", 16");
	instr("store ptr " + addr_point + ", " + self);
}

void FunctionLowerer::maybe_lower_constructor_vptr(size_t index, size_t total)
{
	Binding* binding = fn_.binding;
	if (!is_class_constructor_binding(binding))
		return;
	TypePtr record = class_record_for_member(binding);
	if (record.get() == NULL ||
	    !pa11::strip_cv(record)->is_polymorphic)
		return;
	const Node* current = index < total ? &fn_.children[index] : NULL;
	if (current != NULL && starts_with(current->line, "base-init-action"))
		return;
	lower_vptr_store(record);
}

void FunctionLowerer::maybe_lower_destructor_epilogue(bool& emitted)
{
	Binding* binding = fn_.binding;
	if (!is_class_destructor_binding(binding) || !binding->is_virtual)
		return;
	TypePtr record = class_record_for_member(binding);
	TypePtr bare = record.get() != NULL ? pa11::strip_cv(record) : TypePtr();
	if (bare.get() == NULL || bare->kind != TypeKind::Record)
		return;
	pa11::layout_record_type(bare);
	for (size_t n = 0; n < bare->fields.size(); ++n)
	{
		size_t i = bare->fields.size() - 1 - n;
		Binding* field = bare->fields[i];
		function<Value()> field_addr = [this, field]() {
			string this_ptr = fresh_temp();
			instr(this_ptr + " = load ptr $this");
			string addr = fresh_temp();
			instr(addr + " = index i8 [projection=field] " + this_ptr +
			      ", " + to_string(field->member_offset));
			return Value("ptr", addr);
		};
		lower_destructor_for_object(field_addr, field->type);
		emitted = true;
	}
	if (bare->base.get() != NULL)
	{
		Node action("base-fini-action " + pa11::strip_cv(bare->base)->name);
		action.type = bare->base;
		lower_base_fini(action);
		emitted = true;
	}
}

FunctionOut FunctionLowerer::lower()
{
	Binding* binding = fn_.binding;
	if (binding == NULL)
		throw runtime_error("missing function binding");
	string name = program_.symbol_for(binding);
	TypePtr fn_type = binding->type;
	bool indirect_result =
		pa11::strip_cv(fn_type->base)->kind == TypeKind::Record &&
		record_return_by_address(fn_type->base);
	ostringstream header;
	header << "function @" << name << "(";
	if (indirect_result)
		header << "%ret : ptr [pass=indirect_result]";
	for (size_t i = 0; i < fn_type->parameters.size(); ++i)
	{
		if (i != 0 || indirect_result)
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
	header << ") -> " << (indirect_result ? "void" :
	                      scalar_lowir_type(fn_type->base));
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
	if (!binding->function_specialization_symbol.empty())
		metadata.push_back("object=" + binding->function_specialization_symbol);
	if (binding->is_object_root)
		metadata.push_back("object_root=yes");
	header << metadata_suffix(metadata);
	out_.header = header.str();
	if (binding->is_generated_copy_move_assignment &&
	    fn_type->parameters.size() == 2 &&
	    fn_type->parameters[1]->kind == TypeKind::RValueReference &&
	    binding->owner != NULL &&
	    binding->owner->kind == ScopeKind::Class)
	{
		TypePtr record = pa11::record_type_for_scope(binding->owner);
		if (record.get() != NULL)
		{
			pa11::layout_record_type(record);
			for (size_t i = 0; i < record->fields.size(); ++i)
			{
				Binding* ctor =
					find_record_copy_move_constructor(record->fields[i]->type,
					                                  true);
				if (ctor != NULL && ctor->is_inline_definition)
					program_.demand_inline_function(ctor);
			}
		}
	}
	cleanups_.push_back(vector<Cleanup>());
	lower_params();
	start_block("entry");
	lower_param_stores();
	if (!lower_defaulted_storage_special_member())
		for (size_t i = 0; i < fn_.children.size(); ++i)
		{
			if (starts_with(fn_.children[i].line, "compound-statement"))
				lower_compound(fn_.children[i]);
		}
	if (current_ != NULL && !current_->terminated)
	{
		emit_scope_cleanups(cleanups_.back());
		if (pa11::is_void_type(fn_type->base) || indirect_result)
			terminate("return void");
		else
			terminate("return " + scalar_lowir_type(fn_type->base) + " 0");
	}
	cleanups_.pop_back();
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
		TypePtr ptype = fn_type->parameters[param_index];
		if (binding == NULL)
		{
			if (slot_names_[pname] == 0)
				slot_names_[pname] = 1;
			add_slot(pname, slot_lowir_type(ptype));
			++param_index;
		}
		else
		{
			slots_[binding] = pname;
			if (slot_names_[pname] == 0)
				slot_names_[pname] = 1;
			add_slot(pname, slot_lowir_type(binding->type));
			if (pa11::strip_cv(ptype)->kind == TypeKind::Record &&
			    record_pass_by_address(ptype))
				by_address_parameters_.insert(binding);
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
			Binding* binding = fn_.children[i].binding;
			if (!record_pass_by_address(ptype) &&
			    record_has_storage_copy(ptype))
			{
				string addr = fresh_temp();
				instr(addr + " = addr $" + pname);
				instr("copyobj " + to_string(pa11::type_size(ptype)) +
				      "x" + to_string(pa11::type_align(ptype)) +
				      " %" + pname + ", " + addr);
			}
			if (!cleanups_.empty() && parameter_type_needs_destructor(ptype))
			{
				if (record_pass_by_address(ptype))
					cleanups_.back().push_back(
						Cleanup("%" + pname, ptype, true));
				else if (binding != NULL)
					cleanups_.back().push_back(
						Cleanup(binding, binding->type, true));
			}
			++param_index;
			continue;
		}
		instr("store " + scalar_lowir_type(ptype) + " %" + pname +
		      ", $" + pname);
		++param_index;
	}
}

bool FunctionLowerer::lower_defaulted_storage_special_member()
{
	Binding* binding = fn_.binding;
	if (binding == NULL ||
	    !binding->is_defaulted ||
	    binding->owner == NULL ||
	    binding->owner->kind != ScopeKind::Class ||
	    binding->type->kind != TypeKind::Function ||
	    binding->type->parameters.size() != 2 ||
	    !is_reference(binding->type->parameters[1]))
		return false;
	bool special =
		binding->name == binding->owner->name || binding->name == "operator=";
	if (!special)
		return false;
	for (size_t i = 0; i < fn_.children.size(); ++i)
		if (starts_with(fn_.children[i].line, "compound-statement") &&
		    !fn_.children[i].children.empty())
			return false;
	TypePtr record = pa11::record_type_for_scope(binding->owner);
	if (record.get() == NULL)
		return false;
	string other_name = "__param1";
	if (fn_.children.size() > 1 &&
	    starts_with(fn_.children[1].line, "parameter "))
	{
		other_name = fn_.children[1].line.substr(10);
		size_t space = other_name.find(' ');
		other_name = space == string::npos
			? other_name : other_name.substr(0, space);
		if (other_name.empty())
			other_name = "__param1";
	}
	if (binding->name == "operator=")
	{
		bool move = binding->type->parameters[1]->kind == TypeKind::RValueReference;
		TypePtr bare = pa11::strip_cv(record);
		TypePtr direct_base = bare->base.get() != NULL
			? pa11::strip_cv(bare->base) : TypePtr();
		Binding* base_assign = direct_base.get() != NULL
			? find_record_copy_move_assignment(direct_base, move) : NULL;
		if (base_assign != NULL)
		{
			program_.demand_function_declaration(base_assign);
			program_.demand_inline_function(base_assign);
			string self = fresh_temp();
			instr(self + " = load ptr $this");
			string self_base =
				emit_base_subobject_addr(Value("ptr", self),
				                         record,
				                         direct_base).text;
			string other = fresh_temp();
			instr(other + " = load ptr $" + other_name);
			string other_base =
				emit_base_subobject_addr(Value("ptr", other),
				                         record,
				                         direct_base).text;
			string ignored = fresh_temp();
			instr(ignored + " = call ptr @" + program_.symbol_for(base_assign) +
			      "(" + self_base + ", " + other_base + ")");
			string ret = fresh_temp();
			instr(ret + " = load ptr $this");
			terminate("return ptr " + ret);
			return true;
		}
	}
	if (record_has_storage_copy(record))
	{
		string self = fresh_temp();
		string other = fresh_temp();
		instr(self + " = load ptr $this");
		instr(other + " = load ptr $" + other_name);
		instr("copyobj " + to_string(pa11::type_size(record)) + "x" +
		      to_string(pa11::type_align(record)) + " " + other + ", " + self);
	}
	if (binding->name == "operator=")
	{
		string ret = fresh_temp();
		instr(ret + " = load ptr $this");
		terminate("return ptr " + ret);
	}
	else
		terminate("return void");
	return true;
}

void FunctionLowerer::lower_compound(const Node& node)
{
	cleanups_.push_back(vector<Cleanup>());
	bool top_function_body = cleanups_.size() == 2;
	bool constructor_vptr_written = false;
	bool destructor_has_fini_actions = false;
	if (top_function_body && is_class_destructor_binding(fn_.binding) &&
	    fn_.binding->is_virtual)
	{
		TypePtr record = class_record_for_member(fn_.binding);
		if (record.get() != NULL)
			lower_vptr_store(record);
	}
	if (top_function_body && is_class_constructor_binding(fn_.binding))
	{
		TypePtr record = class_record_for_member(fn_.binding);
		TypePtr bare = record.get() != NULL ? pa11::strip_cv(record) : TypePtr();
		TypePtr direct_base =
			bare.get() != NULL && bare->kind == TypeKind::Record
			? bare->base : TypePtr();
		if (direct_base.get() != NULL &&
		    !record_has_storage_copy(direct_base) &&
		    fn_.binding->type->parameters.size() == 2)
		{
			TypePtr param_record = pa11::strip_cv(
				object_type(fn_.binding->type->parameters[1]));
			if (param_record->kind == TypeKind::Record &&
			    pa11::same_type(param_record, pa11::strip_cv(direct_base)))
			{
				string this_ptr = fresh_temp();
				instr(this_ptr + " = load ptr $this");
				emit_base_subobject_addr(Value("ptr", this_ptr),
				                         bare,
				                         direct_base);
			}
		}
	}
	Binding* final_return_binding = NULL;
	bool earlier_return = false;
	if (!node.children.empty())
	{
		size_t last = node.children.size() - 1;
		if (starts_with(node.children[last].line, "return-statement") &&
		    !node.children[last].children.empty())
			final_return_binding = node.children[last].children[0].binding;
		for (size_t i = 0; i < last; ++i)
			if (node_contains_return_statement(node.children[i]))
				earlier_return = true;
	}
	for (size_t i = 0; i < node.children.size(); ++i)
	{
		if (top_function_body && is_class_constructor_binding(fn_.binding) &&
		    !constructor_vptr_written &&
		    !starts_with(node.children[i].line, "base-init-action"))
		{
			TypePtr record = class_record_for_member(fn_.binding);
			if (record.get() != NULL)
				lower_vptr_store(record);
			constructor_vptr_written = true;
		}
		if (starts_with(node.children[i].line, "base-fini-action") ||
		    starts_with(node.children[i].line, "member-fini-action"))
			destructor_has_fini_actions = true;
		bool returns_declared_variable = false;
		if (starts_with(node.children[i].line, "simple-declaration") &&
		    i + 1 < node.children.size() &&
		    starts_with(node.children[i + 1].line, "return-statement") &&
		    node.children[i].children.size() == 1 &&
		    starts_with(node.children[i].children[0].line, "variable ") &&
		    node.children[i].children[0].binding != NULL &&
		    !node.children[i + 1].children.empty())
		{
			const Node& ret_expr = node.children[i + 1].children[0];
			Binding* binding = node.children[i].children[0].binding;
			string suffix = " " + binding->name;
			returns_declared_variable =
				ret_expr.binding == binding ||
				(starts_with(ret_expr.line, "id-expression") &&
				 ret_expr.line.size() >= suffix.size() &&
				 ret_expr.line.compare(ret_expr.line.size() - suffix.size(),
				                       suffix.size(),
				                       suffix) == 0);
		}
		if (pa11::strip_cv(fn_.binding->type->base)->kind == TypeKind::Record &&
		    record_return_by_address(fn_.binding->type->base) &&
		    (returns_declared_variable ||
		     (starts_with(node.children[i].line, "simple-declaration") &&
		      node.children[i].children.size() == 1 &&
		      starts_with(node.children[i].children[0].line, "variable ") &&
		      node.children[i].children[0].binding != NULL &&
		      !earlier_return &&
		      node.children[i].children[0].binding == final_return_binding)))
			return_slot_variables_.insert(node.children[i].children[0].binding);
		lower_stmt(node.children[i]);
	}
	if (top_function_body && is_class_constructor_binding(fn_.binding) &&
	    !constructor_vptr_written)
	{
		TypePtr record = class_record_for_member(fn_.binding);
		if (record.get() != NULL)
			lower_vptr_store(record);
	}
	if (top_function_body && !destructor_has_fini_actions)
		maybe_lower_destructor_epilogue(destructor_has_fini_actions);
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
	else if (starts_with(node.line, "delegating-init-action"))
		lower_delegating_init(node);
	else if (starts_with(node.line, "storage-copy-action"))
		lower_storage_copy_action(node);
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
	else if (starts_with(node.line, "thread-local-init-variable"))
		lower_thread_local_variable_init(node);
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
		emit_pending_temp_cleanups();
		emit_all_cleanups();
		terminate("return void");
		return;
	}
	if (is_reference(ret))
	{
		Value addr;
		if (node.children[0].category == ValueCategory::LValue ||
		    node.children[0].category == ValueCategory::XValue)
		{
			addr = ensure_pointer(emit_lvalue_addr(node.children[0]));
		}
		else
		{
			string slot =
				fresh_aux_slot("retref", scalar_lowir_type(ret->base));
			Value value = convert_value(emit_rvalue(node.children[0]),
			                            node.children[0].type,
			                            ret->base);
			instr("store " + scalar_lowir_type(ret->base) + " " +
			      value.text + ", $" + slot);
			string addr_name = fresh_temp();
			instr(addr_name + " = addr $" + slot);
			addr = Value("ptr", addr_name);
		}
		addr = convert_value(addr,
		                     pa11::make_pointer(object_type(node.children[0].type)),
		                     pa11::make_pointer(ret->base));
		emit_pending_temp_cleanups();
		emit_all_cleanups();
		terminate("return ptr " + addr.text);
		return;
	}
	if (pa11::strip_cv(ret)->kind == TypeKind::Record)
	{
		if (record_return_by_address(ret))
		{
			if (node.children[0].binding != NULL &&
			    return_slot_variables_.find(node.children[0].binding) !=
			    return_slot_variables_.end())
			{
				emit_pending_temp_cleanups();
				emit_all_cleanups();
				terminate("return void");
				return;
			}
			Value ret_addr("ptr", "%ret");
			function<Value()> addr_for = [ret_addr]() {
				return ret_addr;
			};
			lower_object_init(addr_for, ret, node.children[0]);
			emit_pending_temp_cleanups();
			emit_all_cleanups();
			terminate("return void");
			return;
		}
		string slot = fresh_aux_slot("retobj", slot_lowir_type(ret));
		string addr_name = fresh_temp();
		instr(addr_name + " = addr $" + slot);
		Value ret_addr("ptr", addr_name);
		function<Value()> addr_for = [ret_addr]() {
			return ret_addr;
		};
		lower_object_init(addr_for, ret, node.children[0]);
		emit_pending_temp_cleanups();
		emit_all_cleanups();
		terminate("return " + scalar_lowir_type(ret) + " $" + slot);
		return;
	}
	Value raw = emit_rvalue(node.children[0]);
	TypePtr raw_type = node.children[0].type;
	Value value = convert_binary_value(raw, raw_type, ret);
	emit_pending_temp_cleanups();
	emit_all_cleanups();
	terminate("return " + scalar_lowir_type(ret) + " " + value.text);
}

void FunctionLowerer::lower_expr_stmt(const Node& node)
{
	if (!node.children.empty())
		lower_discarded_expr(node.children[0]);
	emit_pending_temp_cleanups();
}

void FunctionLowerer::lower_discarded_expr(const Node& expr)
{
	if (starts_with(expr.line, "cast-expression") &&
	    pa11::is_void_type(expr.type) &&
	    expr.children.size() == 1)
	{
		TypePtr child_object = pa11::strip_cv(object_type(expr.children[0].type));
		if (expr.children[0].category == ValueCategory::LValue &&
		    child_object->kind == TypeKind::Record)
			ensure_pointer(emit_lvalue_addr(expr.children[0]));
		else
			lower_discarded_expr(expr.children[0]);
		return;
	}
	if (starts_with(expr.line, "call-expression") &&
	    expr.direct_call != NULL && expr.direct_call->name == "operator=" &&
	    eh_try_depth_ == 0 && has_active_cleanups())
	{
		string dispatch = active_unwind_dispatch_.empty()
			? fresh_block("call_unwind_dispatch") : active_unwind_dispatch_;
		bool define_dispatch = active_unwind_dispatch_.empty();
		instr("eh_try ^" + dispatch);
		++eh_try_depth_;
		emit_call(expr);
		--eh_try_depth_;
		instr("eh_end");
		if (define_dispatch)
		{
			string end = fresh_block("call_unwind_end");
			terminate("jump ^" + end);
			active_unwind_dispatch_ = dispatch;
			start_block(dispatch);
			emit_unwind_cleanups();
			terminate("resume");
			start_block(end);
		}
		return;
	}
	if ((starts_with(expr.line, "binary-expression") ||
	     starts_with(expr.line, "assignment-expression")) &&
	    expr.has_op && expr.op == OP_ASS &&
	    !expr.children.empty() &&
	    starts_with(expr.children[0].line, "member-expression") &&
	    eh_try_depth_ == 0 && has_active_cleanups())
	{
		string dispatch = active_unwind_dispatch_.empty()
			? fresh_block("call_unwind_dispatch") : active_unwind_dispatch_;
		bool define_dispatch = active_unwind_dispatch_.empty();
		instr("eh_try ^" + dispatch);
		++eh_try_depth_;
		emit_rvalue(expr);
		--eh_try_depth_;
		instr("eh_end");
		if (define_dispatch)
		{
			string end = fresh_block("call_unwind_end");
			terminate("jump ^" + end);
			active_unwind_dispatch_ = dispatch;
			start_block(dispatch);
			emit_unwind_cleanups();
			terminate("resume");
			start_block(end);
		}
		return;
	}
	if (starts_with(expr.line, "call-expression") && is_reference(expr.type))
	{
		emit_call(expr);
		return;
	}
	if (starts_with(expr.line, "binary-expression") &&
	    expr.has_op && expr.op == OP_COMMA)
	{
		lower_discarded_expr(expr.children[0]);
		lower_discarded_expr(expr.children[1]);
		return;
	}
	TypePtr object = pa11::strip_cv(object_type(expr.type));
	if (expr.category == ValueCategory::PRValue &&
	    !is_reference(expr.type) &&
	    (object->kind == TypeKind::Record ||
	     object->kind == TypeKind::Array))
	{
		string slot = fresh_aux_slot(object->kind == TypeKind::Array
		                             ? "discardarr" : "discard",
		                             slot_lowir_type(object));
		string addr_name = fresh_temp();
		instr(addr_name + " = addr $" + slot);
		Value addr("ptr", addr_name);
		function<Value()> addr_for = [addr]() {
			return addr;
		};
		if (object->kind == TypeKind::Array &&
		    starts_with(expr.line, "braced-init-list"))
			lower_direct_array_init(addr, object, expr);
		else
			lower_object_init(addr_for, object, expr);
		return;
	}
	if (expr.category == ValueCategory::LValue &&
	    object->kind == TypeKind::Array)
	{
		ensure_pointer(emit_lvalue_addr(expr));
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
	bool init_cleanup_scope = false;
	if (!node.children[0].children.empty())
	{
		const Node& init = node.children[0].children[0];
		if (starts_with(init.line, "simple-declaration"))
		{
			cleanups_.push_back(vector<Cleanup>());
			init_cleanup_scope = true;
			lower_stmt(init);
		}
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
	if (init_cleanup_scope)
	{
		emit_scope_cleanups(cleanups_.back());
		cleanups_.pop_back();
	}
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
		const Node& selector_node =
			condition.children.size() > 1 ? condition.children[1] :
			condition.children[0];
		selector = emit_rvalue(selector_node);
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


}  // namespace internal
}  // namespace pa14
