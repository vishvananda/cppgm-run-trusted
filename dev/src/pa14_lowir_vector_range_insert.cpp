#include "pa14_lowir_internal.h"
#include "pa14_lowir_function_internal.h"

namespace pa14 {
namespace internal {

void declare_vector_range_insert_body_module(ProgramLowerer& program);

namespace {

TypePtr vector_member_record_for_lowering(const Binding* binding)
{
	TypePtr record = class_record_for_member(binding);
	record = record.get() != NULL ? pa11::strip_cv(record) : TypePtr();
	if (record.get() != NULL)
		return record;
	for (Scope* scope = binding != NULL ? binding->owner : NULL;
	     scope != NULL;
	     scope = scope->parent)
	{
		if (scope->kind != ScopeKind::Class)
			continue;
		record = pa11::record_type_for_scope(scope);
		record = record.get() != NULL ? pa11::strip_cv(record) : TypePtr();
		if (record.get() != NULL)
			return record;
	}
	return TypePtr();
}

TypePtr vector_member_element_for_lowering(const Binding* binding)
{
	TypePtr record = vector_member_record_for_lowering(binding);
	if (record.get() == NULL ||
	    record->template_arguments.empty() ||
	    record->template_arguments[0].kind !=
		    pa11::TemplateInstanceArgumentKind::Type)
		return TypePtr();
	return pa11::strip_cv(record->template_arguments[0].type);
}

void declare_memmove_if_needed(ProgramLowerer& program)
{
	if (program.declared_functions.insert("__builtin_memmove").second)
		program.declares.push_back(
			"declare function @__builtin_memmove(%arg0 : ptr "
			"[capture=nocapture, access=readwrite], "
			"%arg1 : ptr [capture=nocapture, access=read], "
			"%arg2 : i64) -> ptr [effects=readwrite, unwind=no, "
			"linkage=c, binding=strong, object=memmove]");
}

void declare_operator_new_delete_if_needed(ProgramLowerer& program)
{
	if (program.declared_functions.insert("operator_new").second)
		program.declares.push_back(
			"declare function @operator_new(%arg0 : i64) -> ptr "
			"[binding=strong, object=" +
			string(program.native_lowering
			       ? "_Znwm" : "cppgm_builtin_operator_new") + "]");
	if (program.declared_functions.insert("operator_delete").second)
		program.declares.push_back(
			"declare function @operator_delete(%arg0 : ptr) -> void "
			"[unwind=no, binding=strong, object=" +
			string(program.native_lowering
			       ? "_ZdlPv" : "cppgm_builtin_operator_delete") + "]");
}

bool vector_bool_element(TypePtr element)
{
	return element.get() != NULL &&
	       element->kind == TypeKind::Fundamental &&
	       element->fundamental == FT_BOOL;
}

string vector_unqualified_template_primary(TypePtr type)
{
	TypePtr bare = type.get() != NULL ? pa11::strip_cv(type) : TypePtr();
	if (bare.get() == NULL)
		return "";
	string primary = bare->template_primary_name.empty()
		? bare->name : bare->template_primary_name;
	size_t args = primary.find('<');
	if (args != string::npos)
		primary = primary.substr(0, args);
	size_t scope = primary.rfind("::");
	if (scope != string::npos)
		primary = primary.substr(scope + 2);
	return primary;
}

bool vector_record_is_in_std_namespace(TypePtr record)
{
	record = record.get() != NULL ? pa11::strip_cv(record) : TypePtr();
	Scope* scope = record.get() != NULL ? record->scope : NULL;
	for (Scope* cur = scope; cur != NULL; cur = cur->parent)
		if (cur->kind == ScopeKind::Namespace && cur->name == "std")
			return true;
	return false;
}

bool hosted_vector_move_iterator_type(TypePtr type)
{
	TypePtr bare = type.get() != NULL ? pa11::strip_cv(type) : TypePtr();
	if (is_reference(bare))
		bare = pa11::strip_cv(bare->base);
	return bare.get() != NULL &&
	       bare->kind == TypeKind::Record &&
	       vector_unqualified_template_primary(bare) == "move_iterator" &&
	       vector_record_is_in_std_namespace(bare);
}

}  // namespace

void FunctionLowerer::store_hosted_vector_bool_empty(const string& object)
{
	instr("store ptr 0, " + object);
	string start_offset = fresh_temp();
	instr(start_offset + " = index i8 [projection=field] " +
	      object + ", 8");
	instr("store u32 0, " + start_offset);
	string finish_ptr = fresh_temp();
	instr(finish_ptr + " = index i8 [projection=field] " +
	      object + ", 16");
	instr("store ptr 0, " + finish_ptr);
	string finish_offset = fresh_temp();
	instr(finish_offset + " = index i8 [projection=field] " +
	      object + ", 24");
	instr("store u32 0, " + finish_offset);
	string end_storage = fresh_temp();
	instr(end_storage + " = index i8 [projection=field] " +
	      object + ", 32");
	instr("store ptr 0, " + end_storage);
}

void FunctionLowerer::emit_hosted_vector_bool_copy_from(
	const string& object,
	const string& source_object,
	const string& next_block)
{
	string source_start = fresh_temp();
	instr(source_start + " = load ptr " + source_object);
	string source_start_offset_addr = fresh_temp();
	instr(source_start_offset_addr +
	      " = index i8 [projection=field] " +
	      source_object + ", 8");
	string source_start_offset32 = fresh_temp();
	instr(source_start_offset32 + " = load u32 " +
	      source_start_offset_addr);
	string source_finish_addr = fresh_temp();
	instr(source_finish_addr +
	      " = index i8 [projection=field] " +
	      source_object + ", 16");
	string source_finish = fresh_temp();
	instr(source_finish + " = load ptr " + source_finish_addr);
	string source_finish_offset_addr = fresh_temp();
	instr(source_finish_offset_addr +
	      " = index i8 [projection=field] " +
	      source_object + ", 24");
	string source_finish_offset32 = fresh_temp();
	instr(source_finish_offset32 + " = load u32 " +
	      source_finish_offset_addr);
	string source_bytes = fresh_temp();
	instr(source_bytes + " = binary sub ptr " + source_finish +
	      ", " + source_start);
	string source_words = fresh_temp();
	instr(source_words + " = binary div i64 " + source_bytes +
	      ", 8");
	string source_word_bits = fresh_temp();
	instr(source_word_bits + " = binary mul i64 " +
	      source_words + ", 64");
	string start_offset = fresh_temp();
	instr(start_offset + " = convert zext i64 u32 " +
	      source_start_offset32);
	string finish_offset = fresh_temp();
	instr(finish_offset + " = convert zext i64 u32 " +
	      source_finish_offset32);
	string offset_delta = fresh_temp();
	instr(offset_delta + " = binary sub i64 " +
	      finish_offset + ", " + start_offset);
	string bit_size = fresh_temp();
	instr(bit_size + " = binary add i64 " + source_word_bits +
	      ", " + offset_delta);
	string empty = fresh_temp();
	instr(empty + " = cmp eq i64 " + bit_size + ", 0");
	string empty_block = fresh_block("vector_bool_copy_empty");
	string copy_block = fresh_block("vector_bool_copy_alloc");
	terminate("branch " + empty + ", ^" + empty_block +
	          ", ^" + copy_block);

	start_block(empty_block);
	store_hosted_vector_bool_empty(object);
	terminate("jump ^" + next_block);

	start_block(copy_block);
	string bits_with_slop = fresh_temp();
	instr(bits_with_slop + " = binary add i64 " + bit_size +
	      ", 63");
	string word_count = fresh_temp();
	instr(word_count + " = binary div i64 " + bits_with_slop +
	      ", 64");
	string byte_count = fresh_temp();
	instr(byte_count + " = binary mul i64 " + word_count +
	      ", 8");
	string storage = fresh_temp();
	instr(storage + " = call ptr @operator_new(" + byte_count +
	      ")");
	string ignored = fresh_temp();
	instr(ignored + " = call ptr @__builtin_memmove(" +
	      storage + ", " + source_start + ", " + byte_count +
	      ")");
	string finish_word_index = fresh_temp();
	instr(finish_word_index + " = binary div i64 " +
	      bit_size + ", 64");
	string finish_bit_offset = fresh_temp();
	instr(finish_bit_offset + " = binary mod i64 " +
	      bit_size + ", 64");
	string finish_word_bytes = fresh_temp();
	instr(finish_word_bytes + " = binary mul i64 " +
	      finish_word_index + ", 8");
	string finish_word = fresh_temp();
	instr(finish_word + " = index i8 " + storage + ", " +
	      finish_word_bytes);
	string end_storage = fresh_temp();
	instr(end_storage + " = index i8 " + storage + ", " +
	      byte_count);
	string finish_bit_offset32 = fresh_temp();
	instr(finish_bit_offset32 + " = convert trunc u32 i64 " +
	      finish_bit_offset);
	instr("store ptr " + storage + ", " + object);
	string start_offset_addr = fresh_temp();
	instr(start_offset_addr +
	      " = index i8 [projection=field] " + object + ", 8");
	instr("store u32 0, " + start_offset_addr);
	string finish_ptr_addr = fresh_temp();
	instr(finish_ptr_addr +
	      " = index i8 [projection=field] " + object + ", 16");
	instr("store ptr " + finish_word + ", " + finish_ptr_addr);
	string finish_offset_addr = fresh_temp();
	instr(finish_offset_addr +
	      " = index i8 [projection=field] " + object + ", 24");
	instr("store u32 " + finish_bit_offset32 + ", " +
	      finish_offset_addr);
	string end_storage_addr = fresh_temp();
	instr(end_storage_addr +
	      " = index i8 [projection=field] " + object + ", 32");
	instr("store ptr " + end_storage + ", " + end_storage_addr);
	terminate("jump ^" + next_block);
}

void FunctionLowerer::emit_hosted_vector_copy_construct_loop(
	const string& src_begin,
	const string& src_end,
	const string& dst_begin,
	TypePtr element,
	Binding* copy_ctor,
	const string& label)
{
	const uint64_t element_size = pa11::type_size(element);
	const uint64_t element_align = pa11::type_align(element);
	string src_slot = fresh_aux_slot(label + "_src", "ptr");
	string src_end_slot = fresh_aux_slot(label + "_src_end", "ptr");
	string dst_slot = fresh_aux_slot(label + "_dst", "ptr");
	string check = fresh_block(label + "_check");
	string body = fresh_block(label + "_body");
	string done = fresh_block(label + "_done");
	instr("store ptr " + src_begin + ", $" + src_slot);
	instr("store ptr " + src_end + ", $" + src_end_slot);
	instr("store ptr " + dst_begin + ", $" + dst_slot);
	terminate("jump ^" + check);
	start_block(check);
	string src_cur = fresh_temp();
	instr(src_cur + " = load ptr $" + src_slot);
	string src_end_cur = fresh_temp();
	instr(src_end_cur + " = load ptr $" + src_end_slot);
	string more = fresh_temp();
	instr(more + " = cmp ult ptr " + src_cur + ", " + src_end_cur);
	terminate("branch " + more + ", ^" + body + ", ^" + done);
	start_block(body);
	string dst_cur = fresh_temp();
	instr(dst_cur + " = load ptr $" + dst_slot);
	if (copy_ctor != NULL)
		instr("call void @" + program_.symbol_for(copy_ctor) +
		      "(" + dst_cur + ", " + src_cur + ")");
	else
		instr("copyobj " + to_string(element_size) + "x" +
		      to_string(element_align) + " " + src_cur + ", " + dst_cur);
	string next_src = fresh_temp();
	instr(next_src + " = index i8 " + src_cur + ", " +
	      to_string(element_size));
	string next_dst = fresh_temp();
	instr(next_dst + " = index i8 " + dst_cur + ", " +
	      to_string(element_size));
	instr("store ptr " + next_src + ", $" + src_slot);
	instr("store ptr " + next_dst + ", $" + dst_slot);
	terminate("jump ^" + check);
	start_block(done);
}

void FunctionLowerer::emit_hosted_vector_copy_assign_loop(
	const string& src_begin,
	const string& src_end,
	const string& dst_begin,
	TypePtr element,
	Binding* copy_assign,
	const string& label)
{
	const uint64_t element_size = pa11::type_size(element);
	const uint64_t element_align = pa11::type_align(element);
	string src_slot = fresh_aux_slot(label + "_src", "ptr");
	string src_end_slot = fresh_aux_slot(label + "_src_end", "ptr");
	string dst_slot = fresh_aux_slot(label + "_dst", "ptr");
	string check = fresh_block(label + "_check");
	string body = fresh_block(label + "_body");
	string done = fresh_block(label + "_done");
	instr("store ptr " + src_begin + ", $" + src_slot);
	instr("store ptr " + src_end + ", $" + src_end_slot);
	instr("store ptr " + dst_begin + ", $" + dst_slot);
	terminate("jump ^" + check);
	start_block(check);
	string src_cur = fresh_temp();
	instr(src_cur + " = load ptr $" + src_slot);
	string src_end_cur = fresh_temp();
	instr(src_end_cur + " = load ptr $" + src_end_slot);
	string more = fresh_temp();
	instr(more + " = cmp ult ptr " + src_cur + ", " + src_end_cur);
	terminate("branch " + more + ", ^" + body + ", ^" + done);
	start_block(body);
	string dst_cur = fresh_temp();
	instr(dst_cur + " = load ptr $" + dst_slot);
	if (copy_assign != NULL)
	{
		string ignored = fresh_temp();
		instr(ignored + " = call ptr @" + program_.symbol_for(copy_assign) +
		      "(" + dst_cur + ", " + src_cur + ")");
	}
	else
		instr("copyobj " + to_string(element_size) + "x" +
		      to_string(element_align) + " " + src_cur + ", " + dst_cur);
	string next_src = fresh_temp();
	instr(next_src + " = index i8 " + src_cur + ", " +
	      to_string(element_size));
	string next_dst = fresh_temp();
	instr(next_dst + " = index i8 " + dst_cur + ", " +
	      to_string(element_size));
	instr("store ptr " + next_src + ", $" + src_slot);
	instr("store ptr " + next_dst + ", $" + dst_slot);
	terminate("jump ^" + check);
	start_block(done);
}

void FunctionLowerer::emit_hosted_vector_destroy_loop(
	const string& begin,
	const string& end,
	TypePtr element,
	const string& label)
{
	if (!type_needs_destructor(element))
		return;
	const uint64_t element_size = pa11::type_size(element);
	string slot = fresh_aux_slot(label + "_cur", "ptr");
	string end_slot = fresh_aux_slot(label + "_end", "ptr");
	string check = fresh_block(label + "_check");
	string body = fresh_block(label + "_body");
	string done = fresh_block(label + "_done");
	instr("store ptr " + begin + ", $" + slot);
	instr("store ptr " + end + ", $" + end_slot);
	terminate("jump ^" + check);
	start_block(check);
	string cur = fresh_temp();
	instr(cur + " = load ptr $" + slot);
	string end_cur = fresh_temp();
	instr(end_cur + " = load ptr $" + end_slot);
	string more = fresh_temp();
	instr(more + " = cmp ult ptr " + cur + ", " + end_cur);
	terminate("branch " + more + ", ^" + body + ", ^" + done);
	start_block(body);
	lower_destructor_for_object([cur]() { return Value("ptr", cur); },
	                            element);
	string next = fresh_temp();
	instr(next + " = index i8 " + cur + ", " + to_string(element_size));
	instr("store ptr " + next + ", $" + slot);
	terminate("jump ^" + check);
	start_block(done);
}

void FunctionLowerer::emit_hosted_vector_assignment_grow(
	const string& object,
	const string& start,
	const string& finish,
	const string& source_start,
	const string& source_finish,
	const string& source_bytes,
	const string& finish_addr,
	const string& end_storage_addr,
	TypePtr element,
	Binding* copy_ctor,
	const string& done_block)
{
	string storage = fresh_temp();
	instr(storage + " = call ptr @operator_new(" + source_bytes + ")");
	if (element->kind == TypeKind::Record)
		emit_hosted_vector_copy_construct_loop(source_start,
		                                       source_finish,
		                                       storage,
		                                       element,
		                                       copy_ctor,
		                                       "vector_assign_copy_new");
	else
	{
		string ignored = fresh_temp();
		instr(ignored + " = call ptr @__builtin_memmove(" + storage +
		      ", " + source_start + ", " + source_bytes + ")");
	}
	string grown_finish = fresh_temp();
	instr(grown_finish + " = index i8 " + storage + ", " + source_bytes);
	emit_hosted_vector_destroy_loop(start, finish, element,
	                                "vector_assign_destroy_old");
	instr("store ptr " + storage + ", " + object);
	instr("store ptr " + grown_finish + ", " + finish_addr);
	instr("store ptr " + grown_finish + ", " + end_storage_addr);
	string has_old_storage = fresh_temp();
	instr(has_old_storage + " = cmp ne ptr " + start + ", 0");
	string delete_block = fresh_block("vector_assign_delete_old");
	string skip_delete_block = fresh_block("vector_assign_skip_delete");
	terminate("branch " + has_old_storage + ", ^" + delete_block + ", ^" +
	          skip_delete_block);
	start_block(delete_block);
	instr("call void @operator_delete(" + start + ")");
	terminate("jump ^" + skip_delete_block);
	start_block(skip_delete_block);
	terminate("jump ^" + done_block);
}

void FunctionLowerer::emit_hosted_vector_assignment_fit(
	const string& start,
	const string& finish,
	const string& source_start,
	const string& source_finish,
	const string& source_bytes,
	const string& old_size_bytes,
	const string& finish_addr,
	TypePtr element,
	Binding* copy_ctor,
	Binding* copy_assign,
	const string& done_block)
{
	string assigned_finish = fresh_temp();
	instr(assigned_finish + " = index i8 " + start + ", " + source_bytes);
	if (element->kind != TypeKind::Record)
	{
		string ignored = fresh_temp();
		instr(ignored + " = call ptr @__builtin_memmove(" + start +
		      ", " + source_start + ", " + source_bytes + ")");
		instr("store ptr " + assigned_finish + ", " + finish_addr);
		terminate("jump ^" + done_block);
		return;
	}
	string source_longer = fresh_temp();
	instr(source_longer + " = cmp ult i64 " + old_size_bytes + ", " +
	      source_bytes);
	string record_grow_tail = fresh_block("vector_assign_tail");
	string record_shrink_tail = fresh_block("vector_assign_shrink");
	terminate("branch " + source_longer + ", ^" + record_grow_tail +
	          ", ^" + record_shrink_tail);
	start_block(record_grow_tail);
	string source_old_end = fresh_temp();
	instr(source_old_end + " = index i8 " + source_start + ", " +
	      old_size_bytes);
	emit_hosted_vector_copy_assign_loop(source_start, source_old_end, start,
	                                    element, copy_assign,
	                                    "vector_assign_existing");
	emit_hosted_vector_copy_construct_loop(source_old_end, source_finish,
	                                       finish, element, copy_ctor,
	                                       "vector_assign_tail_construct");
	instr("store ptr " + assigned_finish + ", " + finish_addr);
	terminate("jump ^" + done_block);
	start_block(record_shrink_tail);
	emit_hosted_vector_copy_assign_loop(source_start, source_finish, start,
	                                    element, copy_assign,
	                                    "vector_assign_prefix");
	emit_hosted_vector_destroy_loop(assigned_finish, finish, element,
	                                "vector_assign_destroy_tail");
	instr("store ptr " + assigned_finish + ", " + finish_addr);
	terminate("jump ^" + done_block);
}

bool FunctionLowerer::lower_hosted_vector_copy_constructor_body()
{
	Binding* binding = fn_.binding;
	if (!lowir_synthesizable_hosted_vector_copy_constructor(binding) ||
	    binding->type.get() == NULL ||
	    binding->type->kind != TypeKind::Function ||
	    binding->type->parameters.size() != 2 ||
	    !pa11::is_void_type(binding->type->base))
		return false;
	TypePtr vector_record = vector_member_record_for_lowering(binding);
	vector_record = vector_record.get() != NULL
		? pa11::strip_cv(vector_record) : TypePtr();
	TypePtr element = vector_member_element_for_lowering(binding);
	if (vector_record.get() == NULL ||
	    element.get() == NULL)
		return false;
	if (vector_bool_element(element))
	{
		declare_operator_new_delete_if_needed(program_);
		declare_memmove_if_needed(program_);
		string this_name = out_.parameter_names.size() > 0
			? out_.parameter_names[0] : "this";
		string other_name = out_.parameter_names.size() > 1
			? out_.parameter_names[1] : "__x";
		string object = fresh_temp();
		instr(object + " = load ptr $" + this_name);
		string source_object = fresh_temp();
		instr(source_object + " = load ptr $" + other_name);
		string done_block = fresh_block("vector_bool_copy_done");
		emit_hosted_vector_bool_copy_from(object, source_object,
		                                  done_block);
		start_block(done_block);
		terminate("return void");
		return true;
	}
	bool record_element = element->kind == TypeKind::Record;
	Binding* copy_ctor = NULL;
	if (record_element)
	{
		copy_ctor = find_copy_move_constructor(element, false);
		if (copy_ctor == NULL)
			copy_ctor = program_.demand_implicit_copy_constructor(
				element,
				false);
		if (copy_ctor != NULL)
		{
			program_.demand_function_declaration(copy_ctor);
			program_.demand_inline_function(copy_ctor);
		}
		else if (type_needs_destructor(element))
			return false;
	}
	declare_operator_new_delete_if_needed(program_);
	if (!record_element)
		declare_memmove_if_needed(program_);

	string this_name = out_.parameter_names.size() > 0
		? out_.parameter_names[0] : "this";
	string other_name = out_.parameter_names.size() > 1
		? out_.parameter_names[1] : "__x";
	string object = fresh_temp();
	instr(object + " = load ptr $" + this_name);
	string source_object = fresh_temp();
	instr(source_object + " = load ptr $" + other_name);
	string finish_addr = fresh_temp();
	instr(finish_addr + " = index i8 [projection=field] " +
	      object + ", 8");
	string end_storage_addr = fresh_temp();
	instr(end_storage_addr + " = index i8 [projection=field] " +
	      object + ", 16");
	instr("store ptr 0, " + object);
	instr("store ptr 0, " + finish_addr);
	instr("store ptr 0, " + end_storage_addr);

	string source_finish_addr = fresh_temp();
	instr(source_finish_addr + " = index i8 [projection=field] " +
	      source_object + ", 8");
	string source_start = fresh_temp();
	instr(source_start + " = load ptr " + source_object);
	string source_finish = fresh_temp();
	instr(source_finish + " = load ptr " + source_finish_addr);
	string source_bytes = fresh_temp();
	instr(source_bytes + " = binary sub ptr " + source_finish + ", " +
	      source_start);
	string empty = fresh_temp();
	instr(empty + " = cmp eq i64 " + source_bytes + ", 0");
	string empty_block = fresh_block("vector_copy_empty");
	string copy_block = fresh_block("vector_copy_alloc");
	string done_block = fresh_block("vector_copy_done");
	terminate("branch " + empty + ", ^" + empty_block + ", ^" +
	          copy_block);

	start_block(empty_block);
	terminate("jump ^" + done_block);

	start_block(copy_block);
	string storage = fresh_temp();
	instr(storage + " = call ptr @operator_new(" + source_bytes + ")");
	if (!record_element)
	{
		string ignored = fresh_temp();
		instr(ignored + " = call ptr @__builtin_memmove(" + storage +
		      ", " + source_start + ", " + source_bytes + ")");
	}
	else
	{
		emit_hosted_vector_copy_construct_loop(source_start,
		                                       source_finish,
		                                       storage,
		                                       element,
		                                       copy_ctor,
		                                       "vector_copy_loop");
	}
	string finish = fresh_temp();
	instr(finish + " = index i8 " + storage + ", " + source_bytes);
	instr("store ptr " + storage + ", " + object);
	instr("store ptr " + finish + ", " + finish_addr);
	instr("store ptr " + finish + ", " + end_storage_addr);
	terminate("jump ^" + done_block);

	start_block(done_block);
	terminate("return void");
	return true;
}

bool FunctionLowerer::lower_hosted_vector_bool_copy_assignment_body()
{
	declare_operator_new_delete_if_needed(program_);
	declare_memmove_if_needed(program_);
	string this_name = out_.parameter_names.size() > 0
		? out_.parameter_names[0] : "this";
	string other_name = out_.parameter_names.size() > 1
		? out_.parameter_names[1] : "__x";
	string object = fresh_temp();
	instr(object + " = load ptr $" + this_name);
	string source_object = fresh_temp();
	instr(source_object + " = load ptr $" + other_name);
	string same_object = fresh_temp();
	instr(same_object + " = cmp eq ptr " + object + ", " + source_object);
	string self_block = fresh_block("vector_bool_assign_self");
	string work_block = fresh_block("vector_bool_assign_work");
	terminate("branch " + same_object + ", ^" + self_block +
	          ", ^" + work_block);
	start_block(self_block);
	terminate("return ptr " + object);
	start_block(work_block);
	string old_start = fresh_temp();
	instr(old_start + " = load ptr " + object);
	string after_store = fresh_block("vector_bool_assign_after_store");
	emit_hosted_vector_bool_copy_from(object, source_object, after_store);
	start_block(after_store);
	string has_old_storage = fresh_temp();
	instr(has_old_storage + " = cmp ne ptr " + old_start + ", 0");
	string delete_block = fresh_block("vector_bool_assign_delete_old");
	string done_block = fresh_block("vector_bool_assign_done");
	terminate("branch " + has_old_storage + ", ^" + delete_block +
	          ", ^" + done_block);
	start_block(delete_block);
	instr("call void @operator_delete(" + old_start + ")");
	terminate("jump ^" + done_block);
	start_block(done_block);
	terminate("return ptr " + object);
	return true;
}

bool FunctionLowerer::lower_hosted_vector_copy_assignment_body()
{
	Binding* binding = fn_.binding;
	if (!lowir_synthesizable_hosted_vector_copy_assignment(binding) ||
	    binding->type.get() == NULL ||
	    binding->type->kind != TypeKind::Function ||
	    binding->type->parameters.size() != 2 ||
	    scalar_lowir_type(binding->type->base) != "ptr")
		return false;
	TypePtr vector_record = vector_member_record_for_lowering(binding);
	vector_record = vector_record.get() != NULL
		? pa11::strip_cv(vector_record) : TypePtr();
	if (vector_record.get() == NULL ||
	    vector_record->template_arguments.empty() ||
	    vector_record->template_arguments[0].kind !=
		    pa11::TemplateInstanceArgumentKind::Type)
		return false;
	TypePtr element = pa11::strip_cv(vector_record->template_arguments[0].type);
	if (element.get() == NULL)
		return false;
	if (vector_bool_element(element))
		return lower_hosted_vector_bool_copy_assignment_body();
	bool record_element = element->kind == TypeKind::Record;
	Binding* copy_ctor = NULL;
	Binding* copy_assign = NULL;
	bool needs_destructor = record_element && type_needs_destructor(element);
	if (record_element)
	{
		copy_ctor = find_copy_move_constructor(element, false);
		if (copy_ctor == NULL)
			copy_ctor = program_.demand_implicit_copy_constructor(
				element,
				false);
		copy_assign = program_.demand_implicit_copy_assignment(element, false);
		if ((copy_ctor == NULL || copy_assign == NULL) && needs_destructor)
			return false;
		if (copy_ctor != NULL)
		{
			program_.demand_function_declaration(copy_ctor);
			program_.demand_inline_function(copy_ctor);
		}
		if (copy_assign != NULL)
		{
			program_.demand_function_declaration(copy_assign);
			if (copy_assign->is_inline_definition ||
			    copy_assign->is_generated_copy_move_assignment)
				program_.demand_inline_function(copy_assign);
		}
	}
	declare_operator_new_delete_if_needed(program_);
	if (!record_element)
		declare_memmove_if_needed(program_);
	string this_name = out_.parameter_names.size() > 0
		? out_.parameter_names[0] : "this";
	string other_name = out_.parameter_names.size() > 1
		? out_.parameter_names[1] : "__x";
	string object = fresh_temp();
	instr(object + " = load ptr $" + this_name);
	string source_object = fresh_temp();
	instr(source_object + " = load ptr $" + other_name);
	string same_object = fresh_temp();
	instr(same_object + " = cmp eq ptr " + object + ", " + source_object);
	string self_block = fresh_block("vector_assign_self");
	string work_block = fresh_block("vector_assign_work");
	terminate("branch " + same_object + ", ^" + self_block + ", ^" +
	          work_block);
	start_block(self_block);
	terminate("return ptr " + object);
	start_block(work_block);
	string finish_addr = fresh_temp();
	instr(finish_addr + " = index i8 [projection=field] " +
	      object + ", 8");
	string end_storage_addr = fresh_temp();
	instr(end_storage_addr + " = index i8 [projection=field] " +
	      object + ", 16");
	string source_finish_addr = fresh_temp();
	instr(source_finish_addr + " = index i8 [projection=field] " +
	      source_object + ", 8");
	string start = fresh_temp();
	instr(start + " = load ptr " + object);
	string finish = fresh_temp();
	instr(finish + " = load ptr " + finish_addr);
	string end_storage = fresh_temp();
	instr(end_storage + " = load ptr " + end_storage_addr);
	string source_start = fresh_temp();
	instr(source_start + " = load ptr " + source_object);
	string source_finish = fresh_temp();
	instr(source_finish + " = load ptr " + source_finish_addr);
	string old_size_bytes = fresh_temp();
	instr(old_size_bytes + " = binary sub ptr " + finish + ", " + start);
	string source_bytes = fresh_temp();
	instr(source_bytes + " = binary sub ptr " + source_finish + ", " +
	      source_start);
	string capacity_bytes = fresh_temp();
	instr(capacity_bytes + " = binary sub ptr " + end_storage + ", " +
	      start);
	string needs_grow = fresh_temp();
	instr(needs_grow + " = cmp ult i64 " + capacity_bytes + ", " +
	      source_bytes);
	string grow_block = fresh_block("vector_assign_grow");
	string fit_block = fresh_block("vector_assign_fit");
	string done_block = fresh_block("vector_assign_done");
	terminate("branch " + needs_grow + ", ^" + grow_block + ", ^" +
	          fit_block);

	start_block(grow_block);
	emit_hosted_vector_assignment_grow(object, start, finish,
	                                   source_start, source_finish,
	                                   source_bytes, finish_addr,
	                                   end_storage_addr, element,
	                                   copy_ctor, done_block);

	start_block(fit_block);
	emit_hosted_vector_assignment_fit(start, finish, source_start,
	                                  source_finish, source_bytes,
	                                  old_size_bytes, finish_addr,
	                                  element, copy_ctor, copy_assign,
	                                  done_block);

	start_block(done_block);
	terminate("return ptr " + object);
	return true;
}

bool FunctionLowerer::lower_hosted_vector_range_insert_body()
{
	Binding* binding = fn_.binding;
	if (!lowir_synthesizable_hosted_vector_range_insert(binding) ||
	    binding->type.get() == NULL ||
	    binding->type->kind != TypeKind::Function ||
	    binding->type->parameters.size() != 4 ||
	    pa11::strip_cv(binding->type->base)->kind != TypeKind::Record)
		return false;
	TypePtr vector_record = class_record_for_member(binding);
	vector_record = vector_record.get() != NULL
		? pa11::strip_cv(vector_record) : TypePtr();
	TypePtr element;
	if (vector_record.get() != NULL &&
	    !vector_record->template_arguments.empty() &&
	    vector_record->template_arguments[0].kind ==
		    pa11::TemplateInstanceArgumentKind::Type)
		element = pa11::strip_cv(vector_record->template_arguments[0].type);
	bool record_element =
		element.get() != NULL && element->kind == TypeKind::Record;
	bool indirect_result = record_return_by_address(binding->type->base);
	if (program_.declared_functions.insert("__builtin_memmove").second)
		program_.declares.push_back(
			"declare function @__builtin_memmove(%arg0 : ptr "
			"[capture=nocapture, access=readwrite], "
			"%arg1 : ptr [capture=nocapture, access=read], "
			"%arg2 : i64) -> ptr [effects=readwrite, unwind=no, "
			"linkage=c, binding=strong, object=memmove]");
	if (program_.declared_functions.insert("operator_new").second)
		program_.declares.push_back(
			"declare function @operator_new(%arg0 : i64) -> ptr "
			"[binding=strong, object=" +
			string(program_.native_lowering
			       ? "_Znwm" : "cppgm_builtin_operator_new") + "]");
	if (program_.declared_functions.insert("operator_delete").second)
		program_.declares.push_back(
			"declare function @operator_delete(%arg0 : ptr) -> void "
			"[unwind=no, binding=strong, object=" +
			string(program_.native_lowering
			       ? "_ZdlPv" : "cppgm_builtin_operator_delete") + "]");
	string this_name = out_.parameter_names.size() > 0
		? out_.parameter_names[0] : "this";
	string position_name = out_.parameter_names.size() > 1
		? out_.parameter_names[1] : "__position";
	string first_name = out_.parameter_names.size() > 2
		? out_.parameter_names[2] : "__first";
	string last_name = out_.parameter_names.size() > 3
		? out_.parameter_names[3] : "__last";
	string object = fresh_temp();
	instr(object + " = load ptr $" + this_name);
	string position_source =
		record_pass_by_address(binding->type->parameters[1])
		? "%" + position_name : "$" + position_name;
	string first_source =
		record_pass_by_address(binding->type->parameters[2])
		? "%" + first_name : "$" + first_name;
	string last_source =
		record_pass_by_address(binding->type->parameters[3])
		? "%" + last_name : "$" + last_name;
	string position = fresh_temp();
	instr(position + " = load ptr " + position_source);
	string first = fresh_temp();
	instr(first + " = load ptr " + first_source);
	string last = fresh_temp();
	instr(last + " = load ptr " + last_source);
	string finish_addr = fresh_temp();
	instr(finish_addr + " = index i8 [projection=field] " +
	      object + ", 8");
	string end_storage_addr = fresh_temp();
	instr(end_storage_addr + " = index i8 [projection=field] " +
	      object + ", 16");
	string start = fresh_temp();
	instr(start + " = load ptr " + object);
	string finish = fresh_temp();
	instr(finish + " = load ptr " + finish_addr);
	string end_storage = fresh_temp();
	instr(end_storage + " = load ptr " + end_storage_addr);
	string insert_bytes = fresh_temp();
	instr(insert_bytes + " = binary sub ptr " + last + ", " + first);
	if (record_element)
	{
		bool range_is_move =
			hosted_vector_move_iterator_type(binding->type->parameters[2]);
		Binding* move_ctor = find_copy_move_constructor(element, true);
		Binding* copy_ctor = find_copy_move_constructor(element, false);
		Binding* range_ctor = range_is_move && move_ctor != NULL
			? move_ctor : copy_ctor;
		Binding* relocate_ctor = move_ctor != NULL ? move_ctor : copy_ctor;
		if ((range_ctor == NULL || relocate_ctor == NULL) &&
		    type_needs_destructor(element))
			return false;
		auto demand_ctor =
			[&](Binding* ctor)
		{
			if (ctor == NULL)
				return;
			program_.demand_function_declaration(ctor);
			program_.demand_inline_function(ctor);
		};
		demand_ctor(range_ctor);
		if (relocate_ctor != range_ctor)
			demand_ctor(relocate_ctor);
		const uint64_t element_size = pa11::type_size(element);
		const uint64_t element_align = pa11::type_align(element);
		string result_slot = fresh_aux_slot("insert_result", "ptr");
		string empty_block = fresh_block("vector_insert_empty");
		string work_block = fresh_block("vector_insert_work_record");
		string fit_probe_block = fresh_block("vector_insert_fit_probe_record");
		string fit_append_block = fresh_block("vector_insert_fit_append_record");
		string grow_size_block = fresh_block("vector_insert_grow_size_record");
		string exact_block = fresh_block("vector_insert_exact_record");
		string doubled_block = fresh_block("vector_insert_doubled_record");
		string alloc_block = fresh_block("vector_insert_alloc_record");
		string finish_block = fresh_block("vector_insert_finish_record");
		string empty = fresh_temp();
		instr(empty + " = cmp eq i64 " + insert_bytes + ", 0");
		terminate("branch " + empty + ", ^" + empty_block + ", ^" +
		          work_block);
		start_block(empty_block);
		instr("store ptr " + position + ", $" + result_slot);
		terminate("jump ^" + finish_block);
		start_block(work_block);
		string old_size_bytes = fresh_temp();
		instr(old_size_bytes + " = binary sub ptr " + finish + ", " + start);
		string prefix_bytes = fresh_temp();
		instr(prefix_bytes + " = binary sub ptr " + position + ", " + start);
		string new_size_bytes = fresh_temp();
		instr(new_size_bytes + " = binary add i64 " + old_size_bytes + ", " +
		      insert_bytes);
		string available_bytes = fresh_temp();
		instr(available_bytes + " = binary sub ptr " + end_storage + ", " +
		      finish);
		string src_slot = fresh_aux_slot("insert_src", "ptr");
		string src_end_slot = fresh_aux_slot("insert_src_end", "ptr");
		string dst_slot = fresh_aux_slot("insert_dst", "ptr");
		auto emit_construct_loop =
			[&](const string& src_begin,
			    const string& src_end,
			    const string& dst_begin,
			    Binding* ctor,
			    const string& label)
		{
			string check = fresh_block(label + "_check");
			string body = fresh_block(label + "_body");
			string done = fresh_block(label + "_done");
			instr("store ptr " + src_begin + ", $" + src_slot);
			instr("store ptr " + src_end + ", $" + src_end_slot);
			instr("store ptr " + dst_begin + ", $" + dst_slot);
			terminate("jump ^" + check);
			start_block(check);
			string src_cur = fresh_temp();
			instr(src_cur + " = load ptr $" + src_slot);
			string src_end_cur = fresh_temp();
			instr(src_end_cur + " = load ptr $" + src_end_slot);
			string more = fresh_temp();
			instr(more + " = cmp ult ptr " + src_cur + ", " + src_end_cur);
			terminate("branch " + more + ", ^" + body + ", ^" + done);
			start_block(body);
			string dst_cur = fresh_temp();
			instr(dst_cur + " = load ptr $" + dst_slot);
			if (ctor != NULL)
				instr("call void @" + program_.symbol_for(ctor) +
				      "(" + dst_cur + ", " + src_cur + ")");
			else
				instr("copyobj " + to_string(element_size) + "x" +
				      to_string(element_align) + " " + src_cur +
				      ", " + dst_cur);
			string next_src = fresh_temp();
			instr(next_src + " = index i8 " + src_cur + ", " +
			      to_string(element_size));
			string next_dst = fresh_temp();
			instr(next_dst + " = index i8 " + dst_cur + ", " +
			      to_string(element_size));
			instr("store ptr " + next_src + ", $" + src_slot);
			instr("store ptr " + next_dst + ", $" + dst_slot);
			terminate("jump ^" + check);
			start_block(done);
		};
		string needs_grow = fresh_temp();
		instr(needs_grow + " = cmp ult i64 " + available_bytes + ", " +
		      insert_bytes);
		terminate("branch " + needs_grow + ", ^" + grow_size_block +
		          ", ^" + fit_probe_block);
		start_block(fit_probe_block);
		string append_at_end = fresh_temp();
		instr(append_at_end + " = cmp eq ptr " + position + ", " + finish);
		terminate("branch " + append_at_end + ", ^" + fit_append_block +
		          ", ^" + grow_size_block);
		start_block(fit_append_block);
		emit_construct_loop(first, last, finish, range_ctor,
		                    "vector_insert_fit_append");
		string appended_finish = fresh_temp();
		instr(appended_finish + " = load ptr $" + dst_slot);
		instr("store ptr " + appended_finish + ", " + finish_addr);
		instr("store ptr " + position + ", $" + result_slot);
		terminate("jump ^" + finish_block);

		start_block(grow_size_block);
		string doubled_old = fresh_temp();
		instr(doubled_old + " = binary mul i64 " + old_size_bytes + ", 2");
		string grow_to_exact = fresh_temp();
		instr(grow_to_exact + " = cmp ult i64 " + doubled_old + ", " +
		      new_size_bytes);
		string alloc_slot = fresh_aux_slot("insert_alloc_bytes", "i64");
		terminate("branch " + grow_to_exact + ", ^" + exact_block +
		          ", ^" + doubled_block);
		start_block(exact_block);
		instr("store i64 " + new_size_bytes + ", $" + alloc_slot);
		terminate("jump ^" + alloc_block);
		start_block(doubled_block);
		instr("store i64 " + doubled_old + ", $" + alloc_slot);
		terminate("jump ^" + alloc_block);
		start_block(alloc_block);
		string alloc_bytes = fresh_temp();
		instr(alloc_bytes + " = load i64 $" + alloc_slot);
		string storage = fresh_temp();
		instr(storage + " = call ptr @operator_new(" + alloc_bytes + ")");
		string insert_dest = fresh_temp();
		instr(insert_dest + " = index i8 " + storage + ", " + prefix_bytes);
		auto emit_destroy_loop =
			[&](const string& begin, const string& end)
		{
			if (!type_needs_destructor(element))
				return;
			string check = fresh_block("vector_insert_destroy_check");
			string body = fresh_block("vector_insert_destroy_body");
			string done = fresh_block("vector_insert_destroy_done");
			instr("store ptr " + begin + ", $" + src_slot);
			instr("store ptr " + end + ", $" + src_end_slot);
			terminate("jump ^" + check);
			start_block(check);
			string cur = fresh_temp();
			instr(cur + " = load ptr $" + src_slot);
			string end_cur = fresh_temp();
			instr(end_cur + " = load ptr $" + src_end_slot);
			string more = fresh_temp();
			instr(more + " = cmp ult ptr " + cur + ", " + end_cur);
			terminate("branch " + more + ", ^" + body + ", ^" + done);
			start_block(body);
			lower_destructor_for_object(
				[cur]() { return Value("ptr", cur); }, element);
			string next = fresh_temp();
			instr(next + " = index i8 " + cur + ", " +
			      to_string(element_size));
			instr("store ptr " + next + ", $" + src_slot);
			terminate("jump ^" + check);
			start_block(done);
		};
		emit_construct_loop(start, position, storage, relocate_ctor,
		                    "vector_insert_prefix");
		string after_prefix = fresh_temp();
		instr(after_prefix + " = load ptr $" + dst_slot);
		emit_construct_loop(first, last, after_prefix, range_ctor,
		                    "vector_insert_range");
		string after_insert = fresh_temp();
		instr(after_insert + " = load ptr $" + dst_slot);
		emit_construct_loop(position, finish, after_insert, relocate_ctor,
		                    "vector_insert_suffix");
		string new_finish = fresh_temp();
		instr(new_finish + " = load ptr $" + dst_slot);
		emit_destroy_loop(start, finish);
		instr("store ptr " + storage + ", " + object);
		instr("store ptr " + new_finish + ", " + finish_addr);
		string grown_end_storage = fresh_temp();
		instr(grown_end_storage + " = index i8 " + storage + ", " +
		      alloc_bytes);
		instr("store ptr " + grown_end_storage + ", " + end_storage_addr);
		string has_old_storage = fresh_temp();
		instr(has_old_storage + " = cmp ne ptr " + start + ", 0");
		string delete_block = fresh_block("vector_insert_delete_old_record");
		string skip_delete_block = fresh_block("vector_insert_skip_delete_record");
		terminate("branch " + has_old_storage + ", ^" + delete_block + ", ^" +
		          skip_delete_block);
		start_block(delete_block);
		instr("call void @operator_delete(" + start + ")");
		terminate("jump ^" + skip_delete_block);
		start_block(skip_delete_block);
		instr("store ptr " + insert_dest + ", $" + result_slot);
		terminate("jump ^" + finish_block);
		start_block(finish_block);
		string result_ptr = fresh_temp();
		instr(result_ptr + " = load ptr $" + result_slot);
		if (indirect_result)
		{
			instr("store ptr " + result_ptr + ", %ret");
			terminate("return void");
			return true;
		}
		string ret = scalar_lowir_type(binding->type->base);
		string ret_slot = fresh_aux_slot("insert_ret", ret);
		instr("store ptr " + result_ptr + ", $" + ret_slot);
		terminate("return " + ret + " $" + ret_slot);
		return true;
	}
	string tail_bytes = fresh_temp();
	instr(tail_bytes + " = binary sub ptr " + finish + ", " + position);
	string new_finish = fresh_temp();
	instr(new_finish + " = index i8 " + finish + ", " + insert_bytes);
	string available_bytes = fresh_temp();
	instr(available_bytes + " = binary sub ptr " + end_storage + ", " +
	      finish);
	string needs_grow = fresh_temp();
	instr(needs_grow + " = cmp ult i64 " + available_bytes + ", " +
	      insert_bytes);
	string result_slot = fresh_aux_slot("insert_result", "ptr");
	string grow_block = fresh_block("vector_insert_grow");
	string fit_block = fresh_block("vector_insert_fit");
	string done_block = fresh_block("vector_insert_done");
	terminate("branch " + needs_grow + ", ^" + grow_block + ", ^" +
	          fit_block);
	start_block(fit_block);
	string tail_dest = fresh_temp();
	instr(tail_dest + " = index i8 " + position + ", " + insert_bytes);
	string ignored_tail = fresh_temp();
	instr(ignored_tail + " = call ptr @__builtin_memmove(" + tail_dest +
	      ", " + position + ", " + tail_bytes + ")");
	string ignored_insert = fresh_temp();
	instr(ignored_insert + " = call ptr @__builtin_memmove(" + position +
	      ", " + first + ", " + insert_bytes + ")");
	instr("store ptr " + new_finish + ", " + finish_addr);
	instr("store ptr " + position + ", $" + result_slot);
	terminate("jump ^" + done_block);
	start_block(grow_block);
	string old_size_bytes = fresh_temp();
	instr(old_size_bytes + " = binary sub ptr " + finish + ", " + start);
	string prefix_bytes = fresh_temp();
	instr(prefix_bytes + " = binary sub ptr " + position + ", " + start);
	string new_size_bytes = fresh_temp();
	instr(new_size_bytes + " = binary add i64 " + old_size_bytes + ", " +
	      insert_bytes);
	string doubled_old = fresh_temp();
	instr(doubled_old + " = binary mul i64 " + old_size_bytes + ", 2");
	string grow_to_exact = fresh_temp();
	instr(grow_to_exact + " = cmp ult i64 " + doubled_old + ", " +
	      new_size_bytes);
	string exact_block = fresh_block("vector_insert_exact");
	string doubled_block = fresh_block("vector_insert_doubled");
	string alloc_block = fresh_block("vector_insert_alloc");
	string alloc_slot = fresh_aux_slot("insert_alloc_bytes", "i64");
	terminate("branch " + grow_to_exact + ", ^" + exact_block + ", ^" +
	          doubled_block);
	start_block(exact_block);
	instr("store i64 " + new_size_bytes + ", $" + alloc_slot);
	terminate("jump ^" + alloc_block);
	start_block(doubled_block);
	instr("store i64 " + doubled_old + ", $" + alloc_slot);
	terminate("jump ^" + alloc_block);
	start_block(alloc_block);
	string alloc_bytes = fresh_temp();
	instr(alloc_bytes + " = load i64 $" + alloc_slot);
	string storage = fresh_temp();
	instr(storage + " = call ptr @operator_new(" + alloc_bytes + ")");
	string ignored_prefix = fresh_temp();
	instr(ignored_prefix + " = call ptr @__builtin_memmove(" + storage +
	      ", " + start + ", " + prefix_bytes + ")");
	string insert_dest = fresh_temp();
	instr(insert_dest + " = index i8 " + storage + ", " + prefix_bytes);
	string ignored_new = fresh_temp();
	instr(ignored_new + " = call ptr @__builtin_memmove(" + insert_dest +
	      ", " + first + ", " + insert_bytes + ")");
	string new_tail_dest = fresh_temp();
	instr(new_tail_dest + " = index i8 " + insert_dest + ", " +
	      insert_bytes);
	string ignored_new_tail = fresh_temp();
	instr(ignored_new_tail + " = call ptr @__builtin_memmove(" +
	      new_tail_dest + ", " + position + ", " + tail_bytes + ")");
	string grown_finish = fresh_temp();
	instr(grown_finish + " = index i8 " + storage + ", " +
	      new_size_bytes);
	string grown_end_storage = fresh_temp();
	instr(grown_end_storage + " = index i8 " + storage + ", " +
	      alloc_bytes);
	instr("store ptr " + storage + ", " + object);
	instr("store ptr " + grown_finish + ", " + finish_addr);
	instr("store ptr " + grown_end_storage + ", " + end_storage_addr);
	string has_old_storage = fresh_temp();
	instr(has_old_storage + " = cmp ne ptr " + start + ", 0");
	string delete_block = fresh_block("vector_insert_delete_old");
	string skip_delete_block = fresh_block("vector_insert_skip_delete");
	terminate("branch " + has_old_storage + ", ^" + delete_block + ", ^" +
	          skip_delete_block);
	start_block(delete_block);
	instr("call void @operator_delete(" + start + ")");
	terminate("jump ^" + skip_delete_block);
	start_block(skip_delete_block);
	instr("store ptr " + insert_dest + ", $" + result_slot);
	terminate("jump ^" + done_block);
	start_block(done_block);
	string result_ptr = fresh_temp();
	instr(result_ptr + " = load ptr $" + result_slot);
	if (indirect_result)
	{
		instr("store ptr " + result_ptr + ", %ret");
		terminate("return void");
		return true;
	}
	string ret = scalar_lowir_type(binding->type->base);
	string ret_slot = fresh_aux_slot("insert_ret", ret);
	instr("store ptr " + result_ptr + ", $" + ret_slot);
	terminate("return " + ret + " $" + ret_slot);
	return true;
}

bool FunctionLowerer::lower_hosted_vector_relocate_body()
{
	Binding* binding = fn_.binding;
	if (!lowir_synthesizable_hosted_vector_relocate(binding) ||
	    binding->type.get() == NULL ||
	    binding->type->kind != TypeKind::Function ||
	    binding->type->parameters.size() != 4 ||
	    scalar_lowir_type(binding->type->base) != "ptr")
		return false;
	TypePtr element = vector_member_element_for_lowering(binding);
	element = element.get() != NULL ? pa11::strip_cv(element) : TypePtr();
	if (element.get() == NULL)
		return false;
	const uint64_t element_size = pa11::type_size(element);
	const uint64_t element_align = pa11::type_align(element);
	string first_name = out_.parameter_names.size() > 0
		? out_.parameter_names[0] : "__first";
	string last_name = out_.parameter_names.size() > 1
		? out_.parameter_names[1] : "__last";
	string result_name = out_.parameter_names.size() > 2
		? out_.parameter_names[2] : "__result";
	string first = fresh_temp();
	instr(first + " = load ptr $" + first_name);
	string last = fresh_temp();
	instr(last + " = load ptr $" + last_name);
	string result = fresh_temp();
	instr(result + " = load ptr $" + result_name);
	if (element->kind != TypeKind::Record)
	{
		declare_memmove_if_needed(program_);
		string bytes = fresh_temp();
		instr(bytes + " = binary sub ptr " + last + ", " + first);
		string ignored = fresh_temp();
		instr(ignored + " = call ptr @__builtin_memmove(" + result +
		      ", " + first + ", " + bytes + ")");
		string ret = fresh_temp();
		instr(ret + " = index i8 " + result + ", " + bytes);
		terminate("return ptr " + ret);
		return true;
	}
	Binding* move_ctor = find_copy_move_constructor(element, true);
	Binding* copy_ctor = find_copy_move_constructor(element, false);
	Binding* relocate_ctor = move_ctor != NULL ? move_ctor : copy_ctor;
	if (relocate_ctor == NULL && type_needs_destructor(element))
		return false;
	if (relocate_ctor != NULL)
	{
		program_.demand_function_declaration(relocate_ctor);
		program_.demand_inline_function(relocate_ctor);
	}
	string src_slot = fresh_aux_slot("relocate_src", "ptr");
	string src_end_slot = fresh_aux_slot("relocate_src_end", "ptr");
	string dst_slot = fresh_aux_slot("relocate_dst", "ptr");
	string check = fresh_block("vector_relocate_check");
	string body = fresh_block("vector_relocate_body");
	string done = fresh_block("vector_relocate_done");
	instr("store ptr " + first + ", $" + src_slot);
	instr("store ptr " + last + ", $" + src_end_slot);
	instr("store ptr " + result + ", $" + dst_slot);
	terminate("jump ^" + check);
	start_block(check);
	string src_cur = fresh_temp();
	instr(src_cur + " = load ptr $" + src_slot);
	string src_end_cur = fresh_temp();
	instr(src_end_cur + " = load ptr $" + src_end_slot);
	string more = fresh_temp();
	instr(more + " = cmp ult ptr " + src_cur + ", " + src_end_cur);
	terminate("branch " + more + ", ^" + body + ", ^" + done);
	start_block(body);
	string dst_cur = fresh_temp();
	instr(dst_cur + " = load ptr $" + dst_slot);
	if (relocate_ctor != NULL)
		instr("call void @" + program_.symbol_for(relocate_ctor) +
		      "(" + dst_cur + ", " + src_cur + ")");
	else
		instr("copyobj " + to_string(element_size) + "x" +
		      to_string(element_align) + " " + src_cur + ", " +
		      dst_cur);
	if (type_needs_destructor(element))
		lower_destructor_for_object(
			[src_cur]() { return Value("ptr", src_cur); }, element);
	string next_src = fresh_temp();
	instr(next_src + " = index i8 " + src_cur + ", " +
	      to_string(element_size));
	string next_dst = fresh_temp();
	instr(next_dst + " = index i8 " + dst_cur + ", " +
	      to_string(element_size));
	instr("store ptr " + next_src + ", $" + src_slot);
	instr("store ptr " + next_dst + ", $" + dst_slot);
	terminate("jump ^" + check);
	start_block(done);
	string ret = fresh_temp();
	instr(ret + " = load ptr $" + dst_slot);
	terminate("return ptr " + ret);
	return true;
}

bool FunctionLowerer::lower_hosted_vector_realloc_insert_body()
{
	Binding* binding = fn_.binding;
	if (!lowir_synthesizable_hosted_vector_realloc_insert(binding) ||
	    binding->type.get() == NULL ||
	    binding->type->kind != TypeKind::Function ||
	    binding->type->parameters.size() != 3)
		return false;
	TypePtr vector_record = class_record_for_member(binding);
	vector_record = vector_record.get() != NULL
		? pa11::strip_cv(vector_record) : TypePtr();
	TypePtr element = vector_record->template_arguments[0].type;
	element = element.get() != NULL ? pa11::strip_cv(element) : TypePtr();
	if (element.get() == NULL || element->kind != TypeKind::Record)
		return false;
	Binding* move_ctor = find_copy_move_constructor(element, true);
	Binding* copy_ctor = find_copy_move_constructor(element, false);
	Binding* relocate_ctor = move_ctor != NULL ? move_ctor : copy_ctor;
	TypePtr arg_param = pa11::strip_cv(binding->type->parameters[2]);
	bool inserted_move = arg_param->kind == TypeKind::RValueReference;
	Binding* insert_ctor = inserted_move && move_ctor != NULL
		? move_ctor : copy_ctor;
	if ((relocate_ctor == NULL || insert_ctor == NULL) &&
	    type_needs_destructor(element))
		return false;
	if (relocate_ctor != NULL)
	{
		program_.demand_function_declaration(relocate_ctor);
		program_.demand_inline_function(relocate_ctor);
	}
	if (insert_ctor != NULL && insert_ctor != relocate_ctor)
	{
		program_.demand_function_declaration(insert_ctor);
		program_.demand_inline_function(insert_ctor);
	}
	if (program_.declared_functions.insert("operator_new").second)
		program_.declares.push_back(
			"declare function @operator_new(%arg0 : i64) -> ptr "
			"[binding=strong, object=" +
			string(program_.native_lowering
			       ? "_Znwm" : "cppgm_builtin_operator_new") + "]");
	if (program_.declared_functions.insert("operator_delete").second)
		program_.declares.push_back(
			"declare function @operator_delete(%arg0 : ptr) -> void "
			"[unwind=no, binding=strong, object=" +
			string(program_.native_lowering
			       ? "_ZdlPv" : "cppgm_builtin_operator_delete") + "]");
	string this_name = out_.parameter_names.size() > 0
		? out_.parameter_names[0] : "this";
	string position_name = out_.parameter_names.size() > 1
		? out_.parameter_names[1] : "__position";
	string arg_name = out_.parameter_names.size() > 2
		? out_.parameter_names[2] : "__args";
	string object = fresh_temp();
	instr(object + " = load ptr $" + this_name);
	string position_source =
		record_pass_by_address(binding->type->parameters[1])
		? "%" + position_name : "$" + position_name;
	string position = fresh_temp();
	instr(position + " = load ptr " + position_source);
	string arg_ptr = fresh_temp();
	instr(arg_ptr + " = load ptr $" + arg_name);
	string finish_addr = fresh_temp();
	instr(finish_addr + " = index i8 [projection=field] " +
	      object + ", 8");
	string end_storage_addr = fresh_temp();
	instr(end_storage_addr + " = index i8 [projection=field] " +
	      object + ", 16");
	string start = fresh_temp();
	instr(start + " = load ptr " + object);
	string finish = fresh_temp();
	instr(finish + " = load ptr " + finish_addr);
	string old_size_bytes = fresh_temp();
	instr(old_size_bytes + " = binary sub ptr " + finish + ", " + start);
	string prefix_bytes = fresh_temp();
	instr(prefix_bytes + " = binary sub ptr " + position + ", " + start);
	const uint64_t element_size = pa11::type_size(element);
	const uint64_t element_align = pa11::type_align(element);
	string new_size_bytes = fresh_temp();
	instr(new_size_bytes + " = binary add i64 " + old_size_bytes + ", " +
	      to_string(element_size));
	string doubled_old = fresh_temp();
	instr(doubled_old + " = binary mul i64 " + old_size_bytes + ", 2");
	string grow_to_exact = fresh_temp();
	instr(grow_to_exact + " = cmp ult i64 " + doubled_old + ", " +
	      new_size_bytes);
	string exact_block = fresh_block("vector_realloc_insert_exact");
	string doubled_block = fresh_block("vector_realloc_insert_doubled");
	string alloc_block = fresh_block("vector_realloc_insert_alloc");
	string alloc_slot = fresh_aux_slot("realloc_insert_bytes", "i64");
	terminate("branch " + grow_to_exact + ", ^" + exact_block + ", ^" +
	          doubled_block);
	start_block(exact_block);
	instr("store i64 " + new_size_bytes + ", $" + alloc_slot);
	terminate("jump ^" + alloc_block);
	start_block(doubled_block);
	instr("store i64 " + doubled_old + ", $" + alloc_slot);
	terminate("jump ^" + alloc_block);
	start_block(alloc_block);
	string alloc_bytes = fresh_temp();
	instr(alloc_bytes + " = load i64 $" + alloc_slot);
	string storage = fresh_temp();
	instr(storage + " = call ptr @operator_new(" + alloc_bytes + ")");
	string insert_dest = fresh_temp();
	instr(insert_dest + " = index i8 " + storage + ", " + prefix_bytes);
	string src_slot = fresh_aux_slot("realloc_src", "ptr");
	string src_end_slot = fresh_aux_slot("realloc_src_end", "ptr");
	string dst_slot = fresh_aux_slot("realloc_dst", "ptr");
	auto emit_relocate_loop =
		[&](const string& src_begin,
		    const string& src_end,
		    const string& dst_begin,
		    const string& label)
	{
		string check = fresh_block(label + "_check");
		string body = fresh_block(label + "_body");
		string done = fresh_block(label + "_done");
		instr("store ptr " + src_begin + ", $" + src_slot);
		instr("store ptr " + src_end + ", $" + src_end_slot);
		instr("store ptr " + dst_begin + ", $" + dst_slot);
		terminate("jump ^" + check);
		start_block(check);
		string src_cur = fresh_temp();
		instr(src_cur + " = load ptr $" + src_slot);
		string src_end_cur = fresh_temp();
		instr(src_end_cur + " = load ptr $" + src_end_slot);
		string more = fresh_temp();
		instr(more + " = cmp ult ptr " + src_cur + ", " + src_end_cur);
		terminate("branch " + more + ", ^" + body + ", ^" + done);
		start_block(body);
		string dst_cur = fresh_temp();
		instr(dst_cur + " = load ptr $" + dst_slot);
		if (relocate_ctor != NULL)
			instr("call void @" + program_.symbol_for(relocate_ctor) +
			      "(" + dst_cur + ", " + src_cur + ")");
		else
			instr("copyobj " + to_string(element_size) + "x" +
			      to_string(element_align) + " " + src_cur +
			      ", " + dst_cur);
		string next_src = fresh_temp();
		instr(next_src + " = index i8 " + src_cur + ", " +
		      to_string(element_size));
		string next_dst = fresh_temp();
		instr(next_dst + " = index i8 " + dst_cur + ", " +
		      to_string(element_size));
		instr("store ptr " + next_src + ", $" + src_slot);
		instr("store ptr " + next_dst + ", $" + dst_slot);
		terminate("jump ^" + check);
		start_block(done);
	};
	auto emit_destroy_loop =
		[&](const string& begin, const string& end)
	{
		if (!type_needs_destructor(element))
			return;
		string check = fresh_block("vector_realloc_destroy_check");
		string body = fresh_block("vector_realloc_destroy_body");
		string done = fresh_block("vector_realloc_destroy_done");
		instr("store ptr " + begin + ", $" + src_slot);
		instr("store ptr " + end + ", $" + src_end_slot);
		terminate("jump ^" + check);
		start_block(check);
		string cur = fresh_temp();
		instr(cur + " = load ptr $" + src_slot);
		string end_cur = fresh_temp();
		instr(end_cur + " = load ptr $" + src_end_slot);
		string more = fresh_temp();
		instr(more + " = cmp ult ptr " + cur + ", " + end_cur);
		terminate("branch " + more + ", ^" + body + ", ^" + done);
		start_block(body);
		lower_destructor_for_object(
			[cur]() { return Value("ptr", cur); }, element);
		string next = fresh_temp();
		instr(next + " = index i8 " + cur + ", " +
		      to_string(element_size));
		instr("store ptr " + next + ", $" + src_slot);
		terminate("jump ^" + check);
		start_block(done);
	};
	emit_relocate_loop(start, position, storage, "vector_realloc_prefix");
	if (insert_ctor != NULL)
		instr("call void @" + program_.symbol_for(insert_ctor) +
		      "(" + insert_dest + ", " + arg_ptr + ")");
	else
		instr("copyobj " + to_string(element_size) + "x" +
		      to_string(element_align) + " " + arg_ptr + ", " +
		      insert_dest);
	string after_insert = fresh_temp();
	instr(after_insert + " = index i8 " + insert_dest + ", " +
	      to_string(element_size));
	emit_relocate_loop(position, finish, after_insert, "vector_realloc_suffix");
	string new_finish = fresh_temp();
	instr(new_finish + " = load ptr $" + dst_slot);
	emit_destroy_loop(start, finish);
	instr("store ptr " + storage + ", " + object);
	instr("store ptr " + new_finish + ", " + finish_addr);
	string grown_end_storage = fresh_temp();
	instr(grown_end_storage + " = index i8 " + storage + ", " +
	      alloc_bytes);
	instr("store ptr " + grown_end_storage + ", " + end_storage_addr);
	string has_old_storage = fresh_temp();
	instr(has_old_storage + " = cmp ne ptr " + start + ", 0");
	string delete_block = fresh_block("vector_realloc_delete_old");
	string skip_delete_block = fresh_block("vector_realloc_skip_delete");
	terminate("branch " + has_old_storage + ", ^" + delete_block + ", ^" +
	          skip_delete_block);
	start_block(delete_block);
	instr("call void @operator_delete(" + start + ")");
	terminate("jump ^" + skip_delete_block);
	start_block(skip_delete_block);
	terminate("return void");
	return true;
}

}  // namespace internal
}  // namespace pa14
