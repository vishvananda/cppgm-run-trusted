#include "pa14_lowir_internal.h"
#include "pa14_lowir_function_internal.h"

namespace pa14 {
namespace internal {

void ensure_builtin_memset_declaration(ProgramLowerer& program);

bool FunctionLowerer::lower_hosted_hashtable_count_constructor_body()
{
	Binding* binding = fn_.binding;
	if (!lowir_synthesizable_hosted_hashtable_count_constructor(binding))
		return false;
	string hint_name = "__bkt_count_hint";
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
		if (param_index < out_.parameter_names.size())
			pname = out_.parameter_names[param_index];
		if (param_index == 1)
		{
			hint_name = pname;
			break;
		}
		++param_index;
	}
	if (program_.declared_functions.insert("operator_new").second)
		program_.declares.push_back(
			"declare function @operator_new(%arg0 : i64) -> ptr "
			"[binding=strong, object=" +
			string(program_.native_lowering
			       ? "_Znwm" : "cppgm_builtin_operator_new") + "]");
	ensure_builtin_memset_declaration(program_);
	string self = fresh_temp();
	instr(self + " = load ptr $this");
	string bucket_count_addr = fresh_temp();
	instr(bucket_count_addr + " = index i8 [projection=field] " +
	      self + ", 8");
	string before_begin_addr = fresh_temp();
	instr(before_begin_addr + " = index i8 [projection=field] " +
	      self + ", 16");
	string element_count_addr = fresh_temp();
	instr(element_count_addr + " = index i8 [projection=field] " +
	      self + ", 24");
	string max_load_addr = fresh_temp();
	instr(max_load_addr + " = index i8 [projection=field] " +
	      self + ", 32");
	string next_resize_addr = fresh_temp();
	instr(next_resize_addr + " = index i8 [projection=field] " +
	      self + ", 40");
	string single_bucket_addr = fresh_temp();
	instr(single_bucket_addr + " = index i8 [projection=field] " +
	      self + ", 48");
	instr("store ptr " + single_bucket_addr + ", " + self);
	instr("store i64 1, " + bucket_count_addr);
	instr("store ptr 0, " + before_begin_addr);
	instr("store i64 0, " + element_count_addr);
	instr("store f32 1.0, " + max_load_addr);
	instr("store i64 0, " + next_resize_addr);
	instr("store ptr 0, " + single_bucket_addr);
	string hint = fresh_temp();
	instr(hint + " = load i64 $" + hint_name);
	string needs_alloc = fresh_temp();
	instr(needs_alloc + " = cmp ult i64 1, " + hint);
	string alloc_block = fresh_block("hashtable_buckets_alloc");
	string done_block = fresh_block("hashtable_ctor_done");
	terminate("branch " + needs_alloc + ", ^" + alloc_block + ", ^" +
	          done_block);
	start_block(alloc_block);
	string bytes = fresh_temp();
	instr(bytes + " = binary mul i64 " + hint + ", 8");
	string buckets = fresh_temp();
	instr(buckets + " = call ptr @operator_new(" + bytes + ")");
	string ignored = fresh_temp();
	instr(ignored + " = call ptr @__builtin_memset(" + buckets +
	      ", 0, " + bytes + ")");
	instr("store ptr " + buckets + ", " + self);
	instr("store i64 " + hint + ", " + bucket_count_addr);
	instr("store i64 " + hint + ", " + next_resize_addr);
	terminate("jump ^" + done_block);
	start_block(done_block);
	return true;
}

namespace {

uint64_t align_up_uint64(uint64_t value, uint64_t align)
{
	if (align == 0)
		return value;
	uint64_t rem = value % align;
	return rem == 0 ? value : value + (align - rem);
}

TypePtr hashtable_template_type_arg(TypePtr record, size_t index)
{
	TypePtr bare = record.get() != NULL ? pa11::strip_cv(record) : TypePtr();
	if (bare.get() == NULL ||
	    bare->kind != TypeKind::Record ||
	    index >= bare->template_arguments.size() ||
	    bare->template_arguments[index].kind !=
		    pa11::TemplateInstanceArgumentKind::Type)
		return TypePtr();
	return pa11::strip_cv(bare->template_arguments[index].type);
}

uint64_t record_field_offset(TypePtr record,
                             const string& name,
                             uint64_t fallback)
{
	TypePtr bare = record.get() != NULL ? pa11::strip_cv(record) : TypePtr();
	if (bare.get() == NULL || bare->kind != TypeKind::Record)
		return fallback;
	pa11::layout_record_type(bare);
	for (size_t i = 0; i < bare->fields.size(); ++i)
		if (bare->fields[i] != NULL && bare->fields[i]->name == name)
			return bare->fields[i]->member_offset;
	return fallback;
}

Binding* find_member_function_recursive_impl(TypePtr record,
                                             const string& name,
                                             size_t parameter_count,
                                             set<const void*>& seen)
{
	TypePtr bare = record.get() != NULL ? pa11::strip_cv(record) : TypePtr();
	if (bare.get() == NULL ||
	    bare->kind != TypeKind::Record ||
	    bare->scope == NULL ||
	    !seen.insert(bare.get()).second)
		return NULL;
	map<string, vector<Binding*> >::const_iterator found =
		bare->scope->members.find(name);
	if (found != bare->scope->members.end())
		for (size_t i = 0; i < found->second.size(); ++i)
		{
			Binding* binding = found->second[i];
			if (binding != NULL &&
			    binding->kind == BindingKind::Function &&
			    binding->type.get() != NULL &&
			    binding->type->kind == TypeKind::Function &&
			    binding->type->parameters.size() == parameter_count)
				return binding;
		}
	vector<TypePtr> bases = pa11::record_direct_bases(bare);
	for (size_t i = 0; i < bases.size(); ++i)
	{
		Binding* binding = find_member_function_recursive_impl(
			bases[i], name, parameter_count, seen);
		if (binding != NULL)
			return binding;
	}
	return NULL;
}

Binding* find_member_function_recursive(TypePtr record,
                                        const string& name,
                                        size_t parameter_count)
{
	set<const void*> seen;
	return find_member_function_recursive_impl(
		record, name, parameter_count, seen);
}

}  // namespace

bool FunctionLowerer::lower_hosted_hashtable_range_constructor_body()
{
	Binding* binding = fn_.binding;
	if (!lowir_synthesizable_hosted_hashtable_range_constructor(binding))
		return false;
	TypePtr table_record = class_record_for_member(binding);
	table_record = table_record.get() != NULL
		? pa11::strip_cv(table_record) : TypePtr();
	TypePtr key_type = hashtable_template_type_arg(table_record, 0);
	TypePtr value_type = hashtable_template_type_arg(table_record, 1);
	if (key_type.get() == NULL ||
	    value_type.get() == NULL ||
	    value_type->kind != TypeKind::Record)
		return false;
	uint64_t value_size = pa11::type_size(value_type);
	uint64_t value_align = pa11::type_align(value_type);
	uint64_t key_offset = record_field_offset(value_type, "first", 0);
	uint64_t hash_offset = align_up_uint64(8 + value_size, 8);
	uint64_t node_size = hash_offset + 8;
	Binding* copy_ctor = find_copy_move_constructor(value_type, false);
	if (copy_ctor != NULL)
	{
		program_.demand_function_declaration(copy_ctor);
		program_.demand_inline_function(copy_ctor);
	}
	else if (type_needs_destructor(value_type))
		return false;
	Binding* hash_code = find_member_function_recursive(
		table_record, pa11::abi_private_name("M_hash_code"), 2);
	if (hash_code == NULL)
		return false;
	program_.demand_function_declaration(hash_code);
	program_.demand_inline_function(hash_code);
	TypePtr hash_owner = class_record_for_member(hash_code);
	hash_owner = hash_owner.get() != NULL ? pa11::strip_cv(hash_owner)
	                                      : TypePtr();
	uint64_t hash_owner_offset =
		hash_owner.get() != NULL ? base_subobject_offset(table_record,
		                                                 hash_owner) : 0;
	if (program_.declared_functions.insert("operator_new").second)
		program_.declares.push_back(
			"declare function @operator_new(%arg0 : i64) -> ptr "
			"[binding=strong, object=" +
			string(program_.native_lowering
			       ? "_Znwm" : "cppgm_builtin_operator_new") + "]");
	ensure_builtin_memset_declaration(program_);
	string self = fresh_temp();
	instr(self + " = load ptr $this");
	string bucket_count_addr = fresh_temp();
	instr(bucket_count_addr + " = index i8 [projection=field] " +
	      self + ", 8");
	string before_begin_addr = fresh_temp();
	instr(before_begin_addr + " = index i8 [projection=field] " +
	      self + ", 16");
	string element_count_addr = fresh_temp();
	instr(element_count_addr + " = index i8 [projection=field] " +
	      self + ", 24");
	string max_load_addr = fresh_temp();
	instr(max_load_addr + " = index i8 [projection=field] " +
	      self + ", 32");
	string next_resize_addr = fresh_temp();
	instr(next_resize_addr + " = index i8 [projection=field] " +
	      self + ", 40");
	string single_bucket_addr = fresh_temp();
	instr(single_bucket_addr + " = index i8 [projection=field] " +
	      self + ", 48");
	instr("store ptr " + single_bucket_addr + ", " + self);
	instr("store i64 1, " + bucket_count_addr);
	instr("store ptr 0, " + before_begin_addr);
	instr("store i64 0, " + element_count_addr);
	instr("store f32 1.0, " + max_load_addr);
	instr("store i64 0, " + next_resize_addr);
	instr("store ptr 0, " + single_bucket_addr);
	string first = fresh_temp();
	instr(first + " = load ptr $__f");
	string last = fresh_temp();
	instr(last + " = load ptr $__l");
	string range_bytes = fresh_temp();
	instr(range_bytes + " = binary sub ptr " + last + ", " + first);
	string range_count = fresh_temp();
	instr(range_count + " = binary div i64 " + range_bytes + ", " +
	      to_string(value_size));
	string bucket_base_slot = fresh_aux_slot("hashtable_bucket_base", "ptr");
	string bucket_count_slot = fresh_aux_slot("hashtable_bucket_count", "i64");
	instr("store ptr " + single_bucket_addr + ", $" + bucket_base_slot);
	instr("store i64 1, $" + bucket_count_slot);
	string needs_bucket_array = fresh_temp();
	instr(needs_bucket_array + " = cmp ult i64 1, " + range_count);
	string alloc_buckets = fresh_block("hashtable_range_alloc_buckets");
	string init_done = fresh_block("hashtable_range_init_done");
	terminate("branch " + needs_bucket_array + ", ^" + alloc_buckets +
	          ", ^" + init_done);
	start_block(alloc_buckets);
	string bucket_bytes = fresh_temp();
	instr(bucket_bytes + " = binary mul i64 " + range_count + ", 8");
	string buckets = fresh_temp();
	instr(buckets + " = call ptr @operator_new(" + bucket_bytes + ")");
	string ignored = fresh_temp();
	instr(ignored + " = call ptr @__builtin_memset(" + buckets +
	      ", 0, " + bucket_bytes + ")");
	instr("store ptr " + buckets + ", " + self);
	instr("store i64 " + range_count + ", " + bucket_count_addr);
	instr("store i64 " + range_count + ", " + next_resize_addr);
	instr("store ptr " + buckets + ", $" + bucket_base_slot);
	instr("store i64 " + range_count + ", $" + bucket_count_slot);
	terminate("jump ^" + init_done);
	start_block(init_done);
	string cur_slot = fresh_aux_slot("hashtable_src", "ptr");
	string last_slot = fresh_aux_slot("hashtable_src_end", "ptr");
	string count_slot = fresh_aux_slot("hashtable_count", "i64");
	instr("store ptr " + first + ", $" + cur_slot);
	instr("store ptr " + last + ", $" + last_slot);
	instr("store i64 0, $" + count_slot);
	string check = fresh_block("hashtable_range_check");
	string body = fresh_block("hashtable_range_body");
	string done = fresh_block("hashtable_range_done");
	terminate("jump ^" + check);
	start_block(check);
	string cur = fresh_temp();
	instr(cur + " = load ptr $" + cur_slot);
	string end = fresh_temp();
	instr(end + " = load ptr $" + last_slot);
	string more = fresh_temp();
	instr(more + " = cmp ne ptr " + cur + ", " + end);
	terminate("branch " + more + ", ^" + body + ", ^" + done);
	start_block(body);
	string node = fresh_temp();
	instr(node + " = call ptr @operator_new(" + to_string(node_size) + ")");
	instr("store ptr 0, " + node);
	string value_addr = fresh_temp();
	instr(value_addr + " = index i8 " + node + ", 8");
	if (copy_ctor != NULL)
		instr("call void @" + program_.symbol_for(copy_ctor) +
		      "(" + value_addr + ", " + cur + ")");
	else
		instr("copyobj " + to_string(value_size) + "x" +
		      to_string(value_align) + " " + cur + ", " + value_addr);
	string key_addr = value_addr;
	if (key_offset != 0)
	{
		key_addr = fresh_temp();
		instr(key_addr + " = index i8 " + value_addr + ", " +
		      to_string(key_offset));
	}
	string hash_self = self;
	if (hash_owner_offset != 0)
	{
		hash_self = fresh_temp();
		instr(hash_self + " = index i8 " + self + ", " +
		      to_string(hash_owner_offset));
	}
	string hash = fresh_temp();
	instr(hash + " = call i64 @" + program_.symbol_for(hash_code) +
	      "(" + hash_self + ", " + key_addr + ")");
	string hash_addr = fresh_temp();
	instr(hash_addr + " = index i8 " + node + ", " +
	      to_string(hash_offset));
	instr("store i64 " + hash + ", " + hash_addr);
	string bucket_count_for_hash = fresh_temp();
	instr(bucket_count_for_hash + " = load i64 $" + bucket_count_slot);
	string bucket_index = fresh_temp();
	instr(bucket_index + " = binary umod i64 " + hash + ", " +
	      bucket_count_for_hash);
	string bucket_base = fresh_temp();
	instr(bucket_base + " = load ptr $" + bucket_base_slot);
	string bucket_offset = fresh_temp();
	instr(bucket_offset + " = binary mul i64 " + bucket_index + ", 8");
	string bucket_addr = fresh_temp();
	instr(bucket_addr + " = index i8 " + bucket_base + ", " +
	      bucket_offset);
	string bucket_before = fresh_temp();
	instr(bucket_before + " = load ptr " + bucket_addr);
	string bucket_nonempty = fresh_temp();
	instr(bucket_nonempty + " = cmp ne ptr " + bucket_before + ", 0");
	string insert_nonempty = fresh_block("hashtable_range_insert_nonempty");
	string insert_empty = fresh_block("hashtable_range_insert_empty");
	string insert_done = fresh_block("hashtable_range_insert_done");
	terminate("branch " + bucket_nonempty + ", ^" + insert_nonempty +
	          ", ^" + insert_empty);
	start_block(insert_nonempty);
	string bucket_next = fresh_temp();
	instr(bucket_next + " = load ptr " + bucket_before);
	instr("store ptr " + bucket_next + ", " + node);
	instr("store ptr " + node + ", " + bucket_before);
	terminate("jump ^" + insert_done);
	start_block(insert_empty);
	string old_begin = fresh_temp();
	instr(old_begin + " = load ptr " + before_begin_addr);
	instr("store ptr " + old_begin + ", " + node);
	instr("store ptr " + node + ", " + before_begin_addr);
	string has_old_begin = fresh_temp();
	instr(has_old_begin + " = cmp ne ptr " + old_begin + ", 0");
	string update_old_bucket = fresh_block("hashtable_range_update_old_bucket");
	string set_new_bucket = fresh_block("hashtable_range_set_new_bucket");
	terminate("branch " + has_old_begin + ", ^" + update_old_bucket +
	          ", ^" + set_new_bucket);
	start_block(update_old_bucket);
	string old_hash_addr = fresh_temp();
	instr(old_hash_addr + " = index i8 " + old_begin + ", " +
	      to_string(hash_offset));
	string old_hash = fresh_temp();
	instr(old_hash + " = load i64 " + old_hash_addr);
	string old_bucket_index = fresh_temp();
	instr(old_bucket_index + " = binary umod i64 " + old_hash + ", " +
	      bucket_count_for_hash);
	string old_bucket_offset = fresh_temp();
	instr(old_bucket_offset + " = binary mul i64 " + old_bucket_index +
	      ", 8");
	string old_bucket_addr = fresh_temp();
	instr(old_bucket_addr + " = index i8 " + bucket_base + ", " +
	      old_bucket_offset);
	instr("store ptr " + node + ", " + old_bucket_addr);
	terminate("jump ^" + set_new_bucket);
	start_block(set_new_bucket);
	instr("store ptr " + before_begin_addr + ", " + bucket_addr);
	terminate("jump ^" + insert_done);
	start_block(insert_done);
	string count = fresh_temp();
	instr(count + " = load i64 $" + count_slot);
	string next_count = fresh_temp();
	instr(next_count + " = binary add i64 " + count + ", 1");
	instr("store i64 " + next_count + ", $" + count_slot);
	string next_cur = fresh_temp();
	instr(next_cur + " = index i8 " + cur + ", " +
	      to_string(value_size));
	instr("store ptr " + next_cur + ", $" + cur_slot);
	terminate("jump ^" + check);
	start_block(done);
	string final_count = fresh_temp();
	instr(final_count + " = load i64 $" + count_slot);
	instr("store i64 " + final_count + ", " + element_count_addr);
	string nonempty = fresh_temp();
	instr(nonempty + " = cmp ne i64 " + final_count + ", 0");
	string link_bucket = fresh_block("hashtable_range_link_bucket");
	string finish = fresh_block("hashtable_range_finish");
	terminate("branch " + nonempty + ", ^" + link_bucket + ", ^" +
	          finish);
	start_block(link_bucket);
	instr("store ptr " + before_begin_addr + ", " + single_bucket_addr);
	terminate("jump ^" + finish);
	start_block(finish);
	terminate("return void");
	return true;
}

bool FunctionLowerer::lower_hosted_hash_code_base_hash_code_body()
{
	Binding* binding = fn_.binding;
	if (!lowir_synthesizable_hosted_hash_code_base_hash_code(binding))
		return false;
	string key = fresh_temp();
	instr(key + " = load ptr $__k");
	string data = fresh_temp();
	instr(data + " = load ptr " + key);
	string len_addr = fresh_temp();
	instr(len_addr + " = index i8 [projection=field] " + key + ", 8");
	string len = fresh_temp();
	instr(len + " = load i64 " + len_addr);
	string index_slot = fresh_aux_slot("hash_index", "i64");
	string hash_slot = fresh_aux_slot("hash_value", "i64");
	instr("store i64 0, $" + index_slot);
	instr("store i64 5381, $" + hash_slot);
	string check = fresh_block("hash_code_check");
	string body = fresh_block("hash_code_body");
	string done = fresh_block("hash_code_done");
	terminate("jump ^" + check);
	start_block(check);
	string index = fresh_temp();
	instr(index + " = load i64 $" + index_slot);
	string more = fresh_temp();
	instr(more + " = cmp ult i64 " + index + ", " + len);
	terminate("branch " + more + ", ^" + body + ", ^" + done);
	start_block(body);
	string ch_addr = fresh_temp();
	instr(ch_addr + " = index i8 " + data + ", " + index);
	string ch = fresh_temp();
	instr(ch + " = load u8 " + ch_addr);
	string wide = fresh_temp();
	instr(wide + " = convert zext i64 u8 " + ch);
	string old_hash = fresh_temp();
	instr(old_hash + " = load i64 $" + hash_slot);
	string scaled = fresh_temp();
	instr(scaled + " = binary mul i64 " + old_hash + ", 33");
	string next_hash = fresh_temp();
	instr(next_hash + " = binary add i64 " + scaled + ", " + wide);
	instr("store i64 " + next_hash + ", $" + hash_slot);
	string next_index = fresh_temp();
	instr(next_index + " = binary add i64 " + index + ", 1");
	instr("store i64 " + next_index + ", $" + index_slot);
	terminate("jump ^" + check);
	start_block(done);
	string result = fresh_temp();
	instr(result + " = load i64 $" + hash_slot);
	terminate("return i64 " + result);
	return true;
}


}  // namespace internal
}  // namespace pa14
