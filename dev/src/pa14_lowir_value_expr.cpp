#include "pa14_lowir_internal.h"
namespace pa14 {
namespace internal {

void FunctionLowerer::emit_builtin_va_start(const Node& expr)
{
	if (expr.children.size() < 3)
		throw runtime_error("invalid __builtin_va_start");
	Value list_addr = ensure_pointer(emit_lvalue_addr(expr.children[1]));
	string tag_slot = fresh_aux_slot("va_list", "obj<24x8>");
	string tag_addr = fresh_temp();
	instr(tag_addr + " = addr $" + tag_slot);
	instr("store ptr " + tag_addr + ", " + list_addr.text);
	instr("va_start " + tag_addr);
}

Value FunctionLowerer::emit_builtin_va_arg(const Node& expr)
{
	if (expr.children.size() != 1)
		throw runtime_error("invalid __builtin_va_arg");
	Value list = convert_value(emit_rvalue(expr.children[0]),
	                           expr.children[0].type,
	                           pa11::make_pointer(
		                           pa11::make_fundamental(FT_VOID)));
	string out = fresh_temp();
	instr(out + " = va_arg " + scalar_lowir_type(expr.type) + " " +
	      list.text);
	return Value(scalar_lowir_type(expr.type), out);
}

Value FunctionLowerer::emit_rvalue(const Node& expr) {
	if (starts_with(expr.line, "literal "))
		return emit_literal(expr);
	if (starts_with(expr.line, "statement-expression")) {
		if (expr.children.empty())
			return Value("void", "");
		const Node& body = expr.children[0];
		cleanups_.push_back(vector<Cleanup>());
		Value result("void", "");
		size_t result_index = body.children.size();
		if (!body.children.empty() && starts_with(body.children.back().line, "expression-statement") && !body.children.back().children.empty())
			result_index = body.children.size() - 1;
		for (size_t i = 0; i < result_index; ++i)
			lower_stmt(body.children[i]);
		if (result_index < body.children.size())
			result = emit_rvalue(body.children[result_index].children[0]);
		if (current_ != NULL && !current_->terminated)
			emit_scope_cleanups(cleanups_.back());
		cleanups_.pop_back();
		return result; }
	if (starts_with(expr.line, "member-pointer-function-expression")) {
		if (expr.children.size() < 2)
			throw runtime_error("member pointer function missing operand");
		if (!program_.native_lowering) {
			const Node& member_expr = expr.children[1];
			if (starts_with(member_expr.line, "unary-expression") && member_expr.has_op && member_expr.op == OP_AMP && !member_expr.children.empty() && member_expr.children[0].binding != NULL && member_expr.children[0].binding->kind == BindingKind::Function) {
				Binding* fn = member_expr.children[0].binding;
				if (fn->is_inline_definition)
					program_.demand_inline_function(fn);
				string addr = fresh_temp();
				instr(addr + " = addr @" + program_.symbol_for(fn));
				return Value("ptr", addr); }
			Value member = emit_rvalue(expr.children[1]);
			string bits = fresh_temp();
			instr(bits + " = convert trunc i64 i128 " + member.text);
			string fn = fresh_temp();
			instr(fn + " = copy ptr " + bits);
			return Value("ptr", fn); }
		Value base;
		if (expr.has_op && expr.op == OP_ARROWSTAR)
			base = emit_rvalue(expr.children[0]);
		else if (expr.children[0].category == ValueCategory::LValue || expr.children[0].category == ValueCategory::XValue)
			base = emit_lvalue_addr(expr.children[0]);
		else {
			TypePtr object_record = pa11::strip_cv(object_type(expr.children[0].type));
			if (object_record->kind != TypeKind::Record)
				throw runtime_error("unsupported member pointer object");
			string slot = fresh_aux_slot("tmpobj", scalar_lowir_type(object_record));
			string addr = fresh_temp();
			instr(addr + " = addr $" + slot);
			base = Value("ptr", addr);
			function<Value()> object_addr = [base]() { return base; };
			lower_object_init(object_addr, object_record, expr.children[0]); }
		base = ensure_pointer(base);
		TypePtr object_record = expr.has_op && expr.op == OP_ARROWSTAR
			? pa11::strip_cv(strip_for_value(expr.children[0].type))
			: pa11::strip_cv(object_type(expr.children[0].type));
		if (object_record.get() != NULL && object_record->kind == TypeKind::Pointer)
			object_record = pa11::strip_cv(object_record->base);
		TypePtr member_pointer = pa11::strip_cv(object_type(expr.children[1].type));
		if (member_pointer->kind != TypeKind::MemberPointer)
			throw runtime_error("member pointer function operand type missing");
		TypePtr owner_record = pa11::strip_cv(member_pointer->member_class);
		if (object_record.get() != NULL && object_record->kind == TypeKind::Record && owner_record.get() != NULL && !pa11::same_type(object_record, owner_record) && record_has_base_subobject(object_record, owner_record))
			base = emit_base_subobject_addr(base, object_record, owner_record);
		Value member = emit_rvalue(expr.children[1]);
		string bits_slot = fresh_aux_slot("memptr_bits", "i128");
		instr("store i128 " + member.text + ", $" + bits_slot);
		string bits_addr = fresh_temp();
		instr(bits_addr + " = addr $" + bits_slot);
		string bits = fresh_temp();
		instr(bits + " = load i64 " + bits_addr);
		string flag_addr = fresh_temp();
		instr(flag_addr + " = index i8 " + bits_addr + ", 8");
		string is_virtual = fresh_temp();
		instr(is_virtual + " = load i64 " + flag_addr);
		string indirect = fresh_block("memptr_virtual");
		string direct = fresh_block("memptr_direct");
		string end = fresh_block("memptr_end");
		string slot = fresh_aux_slot("memptr_fn", "ptr");
		terminate("branch " + is_virtual + ", ^" + indirect + ", ^" + direct);
		start_block(indirect);
		string offset_slot = fresh_aux_slot("memptr_offset", "i64");
		instr("store i64 " + bits + ", $" + offset_slot);
		string vptr = fresh_temp();
		instr(vptr + " = load ptr " + base.text);
		string slot_addr = fresh_temp();
		instr(slot_addr + " = index i8 " + vptr + ", $" + offset_slot);
		string vfn = fresh_temp();
		instr(vfn + " = load ptr " + slot_addr);
		instr("store ptr " + vfn + ", $" + slot);
		terminate("jump ^" + end);
		start_block(direct);
		string fn = fresh_temp();
		instr(fn + " = copy ptr " + bits);
		instr("store ptr " + fn + ", $" + slot);
		terminate("jump ^" + end);
		start_block(end);
		string loaded = fresh_temp();
		instr(loaded + " = load ptr $" + slot);
		return Value("ptr", loaded); }
	if (starts_with(expr.line, "id-expression") || starts_with(expr.line, "member-expression") || starts_with(expr.line, "variable "))
		return emit_id_rvalue(expr);
	if (starts_with(expr.line, "binary-expression"))
		return emit_binary(expr);
	if (starts_with(expr.line, "assignment-expression"))
		return emit_assignment(expr);
	if (starts_with(expr.line, "throw-expression"))
		return emit_throw(expr);
	if (starts_with(expr.line, "builtin-va-arg-expression"))
		return emit_builtin_va_arg(expr);
	if (starts_with(expr.line, "unary-expression"))
		return emit_unary(expr);
	if (starts_with(expr.line, "postfix-expression"))
		return emit_postfix(expr);
	if (starts_with(expr.line, "call-expression")) {
		if (expr.direct_call != NULL &&
		    (expr.direct_call->name == "__builtin_va_start" ||
		     expr.direct_call->name == "__builtin_va_end"))
		{
			if (expr.direct_call->name == "__builtin_va_start")
				emit_builtin_va_start(expr);
			return Value("void", "");
		}
		Value value = emit_call(expr);
		if (is_reference(expr.type)) {
			TypePtr value_type = object_type(expr.type);
			while (is_reference(value_type))
				value_type = object_type(value_type);
			string tmp = fresh_temp();
			instr(tmp + " = load " + scalar_lowir_type(value_type) + " " + value.text);
			return Value(scalar_lowir_type(value_type), tmp); }
		return value; }
	if (starts_with(expr.line, "new-expression")) {
		TypePtr object = pa11::strip_cv(pa11::strip_cv(expr.type)->base);
		bool array_new = expr.line.find(" array") != string::npos;
		if (array_new) {
			if (expr.children.empty())
				throw runtime_error("array new missing bound");
			if (program_.declared_functions.insert("operator_new__").second)
				program_.declares.push_back(
					"declare function @operator_new__(%arg0 : i64) -> ptr "
					"[binding=strong, object=" +
					string(program_.native_lowering
					       ? "_Znam"
					       : "cppgm_builtin_operator_new_array") + "]");
			bool record_array = object->kind == TypeKind::Record;
			bool constant_record_bound = record_array && expr.children[0].has_constant_value;
			uint64_t constant_count = expr.children[0].constant_value;
			Value raw_count;
			Value count;
			bool u32_record_size = record_array && scalar_lowir_type(expr.children[0].type) == "u32";
			string alloc_size;
			string size_slot;
			if (constant_record_bound) {
				uint64_t total = constant_count * pa11::type_size(object) + 8;
				alloc_size = fresh_temp();
				instr(alloc_size + " = convert sext i64 i32 " + to_string(total)); }
			else {
				raw_count = emit_rvalue(expr.children[0]);
				count = raw_count;
				if (!u32_record_size)
					count = convert_value(
						raw_count, expr.children[0].type, pa11::make_fundamental(FT_UNSIGNED_LONG_INT));
				string bytes = u32_record_size ? raw_count.text : count.text;
				if (pa11::type_size(object) != 1) {
					if (u32_record_size) {
						bytes = fresh_temp();
						instr(bytes + " = binary mul u32 " + raw_count.text + ", " + to_string(pa11::type_size(object))); }
					else {
						string size_tmp = fresh_temp();
						instr(size_tmp + " = convert sext i64 i32 " + to_string(pa11::type_size(object)));
						bytes = fresh_temp();
						instr(bytes + " = binary mul i64 " + count.text + ", " + size_tmp); } }
				alloc_size = bytes;
				if (record_array && u32_record_size) {
					string total32 = fresh_temp();
					instr(total32 + " = binary add u32 " + bytes + ", 8");
					alloc_size = fresh_temp();
					instr(alloc_size + " = convert zext i64 u32 " + total32); }
				else if (record_array) {
					string total = fresh_temp();
					instr(total + " = binary add i64 " + bytes + ", 8");
					alloc_size = total; }
				size_slot = fresh_aux_slot("array_new_size", "i64");
				instr("store i64 " + alloc_size + ", $" + size_slot); }
			string call_tmp = fresh_temp();
			instr(call_tmp + " = call ptr @operator_new__(" + alloc_size + ")");
			string result_ptr = call_tmp;
			if (record_array) {
				if (constant_record_bound) {
					result_ptr = fresh_temp();
					instr(result_ptr + " = index i8 " + call_tmp + ", 8");
					string cookie_count = fresh_temp();
					instr(cookie_count + " = const i64 " + to_string(constant_count));
					instr("store i64 " + cookie_count + ", " + call_tmp); }
				else {
					string stored_size = fresh_temp();
					instr(stored_size + " = load i64 $" + size_slot);
					result_ptr = fresh_temp();
					instr(result_ptr + " = index i8 " + call_tmp + ", 8");
					string payload_size = fresh_temp();
					instr(payload_size + " = binary sub i64 " + stored_size + ", 8");
					string cookie_count = fresh_temp();
					instr(cookie_count + " = binary udiv i64 " + payload_size + ", " + to_string(pa11::type_size(object)));
					instr("store i64 " + cookie_count + ", " + call_tmp); } }
			if (record_array && record_has_default_constructor_for_array(object)) {
				string index_slot = fresh_aux_slot("array_new_index", "i64");
				string cond_block = fresh_block("array_new_ctor_cond");
				string body_block = fresh_block("array_new_ctor_body");
				string end_block = fresh_block("array_new_ctor_end");
				string constant_bound;
				if (constant_record_bound) {
					constant_bound = fresh_temp();
					instr(constant_bound + " = const i64 " + to_string(constant_count)); }
				instr("store i64 0, $" + index_slot);
				terminate("jump ^" + cond_block);
				start_block(cond_block);
				string idx = fresh_temp();
				instr(idx + " = load i64 $" + index_slot);
				string more = fresh_temp();
				string bound = constant_bound.empty() ? count.text : constant_bound;
				if (!constant_record_bound && u32_record_size) {
					bound = fresh_temp();
					instr(bound + " = convert zext i64 u32 " + raw_count.text); }
				instr(more + " = cmp ult i64 " + idx + ", " + bound);
				terminate("branch " + more + ", ^" + body_block + ", ^" + end_block);
				start_block(body_block);
				string offset = fresh_temp();
				instr(offset + " = binary mul i64 " + idx + ", " + to_string(pa11::type_size(object)));
				string elem = fresh_temp();
				instr(elem + " = index i8 " + result_ptr + ", " + offset);
				Value elem_addr("ptr", elem);
				function<Value()> addr_for = [elem_addr]() {
					return elem_addr;
				};
				lower_default_init(addr_for, object);
				string next = fresh_temp();
				instr(next + " = binary add i64 " + idx + ", 1");
				instr("store i64 " + next + ", $" + index_slot);
				terminate("jump ^" + cond_block);
				start_block(end_block); }
			else if (!record_array && expr.token_text == "paren-init") {
				string index_slot = fresh_aux_slot("zeroinit_offset", "i64");
				string cond_block = fresh_block("zeroinit_cond");
				string body_block = fresh_block("zeroinit_body");
				string end_block = fresh_block("zeroinit_end");
				string bound = fresh_temp();
				instr(bound + " = load i64 $" + size_slot);
				instr("store i64 0, $" + index_slot);
				terminate("jump ^" + cond_block);
				start_block(cond_block);
				string idx = fresh_temp();
				instr(idx + " = load i64 $" + index_slot);
				string more = fresh_temp();
				instr(more + " = cmp ult i64 " + idx + ", " + bound);
				terminate("branch " + more + ", ^" + body_block + ", ^" + end_block);
				start_block(body_block);
				string elem = fresh_temp();
				instr(elem + " = index i8 " + result_ptr + ", " + idx);
				instr("store i8 0, " + elem);
				string next = fresh_temp();
				instr(next + " = binary add i64 " + idx + ", 1");
				instr("store i64 " + next + ", $" + index_slot);
				terminate("jump ^" + cond_block);
				start_block(end_block); }
			return convert_value(Value("ptr", result_ptr), pa11::make_pointer(object), expr.type); }
		bool placement = !expr.children.empty() && expr.binding != NULL;
		Value storage;
		size_t arg_start = 0;
		TypePtr placement_param;
		if (placement) {
			string size_tmp = fresh_temp();
			instr(size_tmp + " = convert sext i64 i32 " + to_string(pa11::type_size(object)));
			Value size_value("i64", size_tmp);
			program_.demand_function_declaration(expr.binding);
			vector<string> new_args;
			new_args.push_back(size_value.text);
			placement_param = expr.binding->type->parameters.size() > 1
				? expr.binding->type->parameters[1] : expr.children[0].type;
			lower_call_argument(expr.children[0], placement_param, new_args);
			string call_tmp = fresh_temp();
			ostringstream call;
			call << call_tmp << " = call ptr @" << program_.symbol_for(expr.binding)
			     << "(";
			for (size_t i = 0; i < new_args.size(); ++i) {
				if (i != 0)
					call << ", ";
				call << new_args[i]; }
			call << ")";
			instr(call.str());
			storage = Value("ptr", call_tmp);
			arg_start = 1; }
		else {
			if (program_.declared_functions.insert("operator_new").second)
				program_.declares.push_back(
					"declare function @operator_new(%arg0 : i64) -> ptr "
					"[binding=strong, object=" +
					string(program_.native_lowering
					       ? "_Znwm"
					       : "cppgm_builtin_operator_new") + "]");
			string size_tmp = fresh_temp();
			instr(size_tmp + " = convert sext i64 i32 " + to_string(pa11::type_size(object)));
			string call_tmp = fresh_temp();
			instr(call_tmp + " = call ptr @operator_new(" + size_tmp + ")");
			storage = Value("ptr", call_tmp); }
		Binding* ctor = expr.direct_call;
		if (ctor != NULL) {
			bool guard_null = placement && placement_param.get() != NULL && pa11::strip_cv(strip_for_value(placement_param))->kind != TypeKind::Pointer;
			string end_block;
			if (guard_null) {
				string init_block = fresh_block("new_init");
				end_block = fresh_block("new_end");
				string nonnull = fresh_temp();
				instr(nonnull + " = cmp ne ptr " + storage.text + ", 0");
				terminate("branch " + nonnull + ", ^" + init_block + ", ^" + end_block);
				start_block(init_block); }
			program_.demand_function_declaration(ctor);
			program_.demand_inline_function(ctor);
			vector<string> lowered;
			lowered.push_back(storage.text);
				for (size_t i = arg_start; i < expr.children.size(); ++i) {
					TypePtr param = ctor->type->parameters[i - arg_start + 1];
					lower_call_argument(expr.children[i], param, lowered); }
			ostringstream call;
			call << "call void @" << program_.symbol_for(ctor) << "(";
			for (size_t i = 0; i < lowered.size(); ++i) {
				if (i != 0)
					call << ", ";
				call << lowered[i]; }
			call << ")";
			instr(call.str());
			if (guard_null) {
				terminate("jump ^" + end_block);
				start_block(end_block); } }
		else if (arg_start < expr.children.size()) {
			Value value = convert_value(emit_rvalue(expr.children[arg_start]), expr.children[arg_start].type, object);
			instr("store " + scalar_lowir_type(object) + " " + value.text + ", " + storage.text); }
		return convert_value(storage, pa11::make_pointer(object), expr.type); }
	if (starts_with(expr.line, "delete-expression")) {
		if (expr.children.empty() || expr.binding == NULL)
			return Value("void", "");
		Value pointer = ensure_pointer(emit_rvalue(expr.children[0]));
		TypePtr ptr_type = pa11::strip_cv(strip_for_value(expr.children[0].type));
		TypePtr object = ptr_type->kind == TypeKind::Pointer
			? pa11::strip_cv(ptr_type->base) : TypePtr();
		program_.demand_function_declaration(expr.binding);
		bool array_delete = expr.line.find(" array") != string::npos;
		if (array_delete && object.get() != NULL && object->kind == TypeKind::Record) {
			string nonnull = fresh_block("array_delete_nonnull");
			string end = fresh_block("array_delete_end");
			string cond = fresh_temp();
			instr(cond + " = cmp ne ptr " + pointer.text + ", 0");
			terminate("branch " + cond + ", ^" + nonnull + ", ^" + end);
			start_block(nonnull);
			string base = fresh_temp();
			instr(base + " = index i8 " + pointer.text + ", -8");
			string count = fresh_temp();
			instr(count + " = load i64 " + base);
			if (type_needs_cleanup(object)) {
				string index_slot = fresh_aux_slot("array_delete_index", "i64");
				string dtor_cond = fresh_block("array_delete_dtor_cond");
				string dtor_body = fresh_block("array_delete_dtor_body");
				string dtor_end = fresh_block("array_delete_dtor_end");
				instr("store i64 " + count + ", $" + index_slot);
				terminate("jump ^" + dtor_cond);
				start_block(dtor_cond);
				string idx = fresh_temp();
				instr(idx + " = load i64 $" + index_slot);
				string more = fresh_temp();
				instr(more + " = cmp ne i64 " + idx + ", 0");
				terminate("branch " + more + ", ^" + dtor_body + ", ^" + dtor_end);
				start_block(dtor_body);
				string prev = fresh_temp();
				instr(prev + " = binary sub i64 " + idx + ", 1");
				instr("store i64 " + prev + ", $" + index_slot);
				string offset = fresh_temp();
				instr(offset + " = binary mul i64 " + prev + ", " + to_string(pa11::type_size(object)));
				string elem = fresh_temp();
				instr(elem + " = index i8 " + pointer.text + ", " + offset);
				Value elem_addr("ptr", elem);
				function<Value()> addr_for = [elem_addr]() {
					return elem_addr;
				};
				lower_destructor_for_object(addr_for, object);
				terminate("jump ^" + dtor_cond);
				start_block(dtor_end); }
			instr("call void @" + program_.symbol_for(expr.binding) + "(" + base + ")");
			terminate("jump ^" + end);
			start_block(end);
			return Value("void", ""); }
		if (array_delete || object.get() == NULL || object->kind != TypeKind::Record) {
			instr("call void @" + program_.symbol_for(expr.binding) + "(" + pointer.text + ")");
			return Value("void", ""); }
		string nonnull = fresh_block("delete_nonnull");
		string end = fresh_block("delete_end");
		string cond = fresh_temp();
		instr(cond + " = cmp ne ptr " + pointer.text + ", 0");
		terminate("branch " + cond + ", ^" + nonnull + ", ^" + end);
		start_block(nonnull);
		Binding* vdtor = find_destructor(object);
		if (vdtor != NULL && vdtor->is_virtual && vdtor->virtual_slot_index >= 0) {
			program_.demand_vtable(object);
			string vptr = fresh_temp();
			instr(vptr + " = load ptr " + pointer.text);
			int deleting_slot = vdtor->virtual_slot_index + 1;
			string slot_addr = vptr;
			if (deleting_slot > 0) {
				slot_addr = fresh_temp();
				instr(slot_addr + " = index i8 " + vptr + ", " + to_string(deleting_slot * 8)); }
			string fnptr = fresh_temp();
			instr(fnptr + " = load ptr " + slot_addr);
			instr("call void " + fnptr + "(" + pointer.text + ") as (%arg0 : ptr) -> void");
			terminate("jump ^" + end);
			start_block(end);
			return Value("void", ""); }
		function<Value()> addr_for = [pointer]() {
			return pointer;
		};
		lower_destructor_for_object(addr_for, object);
		instr("call void @" + program_.symbol_for(expr.binding) + "(" + pointer.text + ")");
		terminate("jump ^" + end);
		start_block(end);
		return Value("void", ""); }
	if (starts_with(expr.line, "subscript-expression")) {
		Value addr = emit_subscript_addr(expr);
		string tmp = fresh_temp();
		instr(tmp + " = load " + scalar_lowir_type(expr.type) + " " + addr.text);
		return Value(scalar_lowir_type(expr.type), tmp); }
	if (starts_with(expr.line, "member-pointer-expression")) {
		Value addr = emit_lvalue_addr(expr);
		string tmp = fresh_temp();
		instr(tmp + " = load " + scalar_lowir_type(expr.type) + " " + addr.text);
		return Value(scalar_lowir_type(expr.type), tmp); }
	if (starts_with(expr.line, "cast-expression") || starts_with(expr.line, "id-expression xvalue"))
		return emit_cast(expr);
	if (starts_with(expr.line, "conditional-expression")) {
		if (expr.category == ValueCategory::LValue)
			return emit_conditional_value(expr);
		return emit_conditional(expr); }
	if (starts_with(expr.line, "sizeof-expression")) {
		string tmp = fresh_temp();
		instr(tmp + " = const i64 " + expr.token_text);
		return Value("i64", tmp); }
	if (starts_with(expr.line, "pseudo-destructor-expression")) {
		if (expr.direct_call != NULL && !expr.children.empty()) {
			program_.demand_function_declaration(expr.direct_call);
			program_.demand_inline_function(expr.direct_call);
			Value addr = expr.has_op && expr.op == OP_ARROW
				? emit_rvalue(expr.children[0])
				: emit_lvalue_addr(expr.children[0]);
			addr = ensure_pointer(addr);
			instr("call void @" + program_.symbol_for(expr.direct_call) + "(" + addr.text + ")"); }
		else if (!expr.children.empty())
			emit_rvalue(expr.children[0]);
		return Value("void", ""); }
	throw runtime_error("unsupported rvalue expression: " + expr.line); }
Value FunctionLowerer::convert_value(Value value, TypePtr from, TypePtr to, bool fold_literals) {
	string dst = scalar_lowir_type(to);
	string src = scalar_lowir_type(strip_for_value(from));
	TypePtr from_bare = pa11::strip_cv(strip_for_value(from));
	TypePtr to_bare = pa11::strip_cv(strip_for_value(to));
	if (from_bare->kind == TypeKind::Fundamental && from_bare->fundamental == FT_NULLPTR_T && to_bare->kind == TypeKind::Pointer) {
		string tmp = fresh_temp();
		instr(tmp + " = copy ptr " + value.text);
		return Value(dst, tmp); }
	if (from_bare->kind == TypeKind::Fundamental && from_bare->fundamental == FT_NULLPTR_T && to_bare->kind == TypeKind::MemberPointer) {
		if (fold_literals && value.text != "" && value.text[0] != '%' && value.text[0] != '$' && value.text[0] != '@')
			return Value(dst, value.text);
		string tmp = fresh_temp();
		if (dst == src)
			instr(tmp + " = copy " + dst + " " + value.text);
		else
			instr(tmp + " = convert zext " + dst + " " + src + " " + value.text);
		return Value(dst, tmp); }
	if (from_bare->kind == TypeKind::Pointer && to_bare->kind == TypeKind::Fundamental && to_bare->fundamental == FT_BOOL) {
		string cmp = fresh_temp();
		instr(cmp + " = cmp ne ptr " + value.text + ", 0");
		string tmp = fresh_temp();
		instr(tmp + " = copy u8 " + cmp);
		return Value("u8", tmp); }
	if (from_bare->kind == TypeKind::MemberPointer && to_bare->kind == TypeKind::Fundamental && to_bare->fundamental == FT_BOOL) {
		string type = scalar_lowir_type(from);
		if (from_bare->base.get() != NULL && from_bare->base->kind == TypeKind::Function && type == "i128")
			type = "i64";
		string cmp = fresh_temp();
		instr(cmp + " = cmp ne " + type + " " + value.text + ", 0");
		string tmp = fresh_temp();
		instr(tmp + " = copy u8 " + cmp);
		return Value("u8", tmp); }
	if (program_.native_lowering && to_bare->kind == TypeKind::Fundamental && to_bare->fundamental == FT_BOOL && (from_bare->kind == TypeKind::Fundamental || from_bare->kind == TypeKind::Enum))
		return bool_value(value, from);
	if (from_bare->kind == TypeKind::MemberPointer && to_bare->kind == TypeKind::MemberPointer) {
		TypePtr member_type = pa11::strip_cv(from_bare->base);
		if (member_type->kind != TypeKind::Function && !pa11::same_type(pa11::strip_cv(from_bare->member_class), pa11::strip_cv(to_bare->member_class)) && record_has_base_subobject(to_bare->member_class, from_bare->member_class)) {
			uint64_t offset = base_subobject_offset(to_bare->member_class, from_bare->member_class);
			if (offset != 0) {
				string slot = fresh_aux_slot("memptrconv", "i64");
				string is_null = fresh_temp();
				instr(is_null + " = cmp eq i64 " + value.text + ", 0");
				string null_block = fresh_block("memptr_null");
				string value_block = fresh_block("memptr_value");
				string end_block = fresh_block("memptr_end");
				terminate("branch " + is_null + ", ^" + null_block + ", ^" + value_block);
				start_block(null_block);
				instr("store i64 0, $" + slot);
				terminate("jump ^" + end_block);
				start_block(value_block);
				string adjusted = fresh_temp();
				instr(adjusted + " = binary add i64 " + value.text + ", " + to_string(offset));
				instr("store i64 " + adjusted + ", $" + slot);
				terminate("jump ^" + end_block);
				start_block(end_block);
				string loaded = fresh_temp();
				instr(loaded + " = load i64 $" + slot);
				return Value("i64", loaded); } }
		if (dst == src)
			return Value(dst, value.text);
		string tmp = fresh_temp();
		instr(tmp + " = copy " + dst + " " + value.text);
		return Value(dst, tmp); }
	if (dst == src) {
		if (from_bare->kind == TypeKind::Pointer && to_bare->kind == TypeKind::Pointer) {
			TypePtr from_pointee = pa11::strip_cv(from_bare->base);
			TypePtr to_pointee = pa11::strip_cv(to_bare->base);
				if (from_pointee->kind == TypeKind::Record && to_pointee->kind == TypeKind::Record && record_has_base_subobject(from_pointee, to_pointee)) {
					return emit_base_subobject_addr(value, from_pointee, to_pointee); }
			if (from_pointee->kind == TypeKind::Record && to_pointee->kind == TypeKind::Record && record_has_base_subobject(to_pointee, from_pointee)) {
				program_.mark_static_downcast_source_record(from_pointee);
				uint64_t offset = base_subobject_offset(to_pointee, from_pointee);
				if (offset == 0)
					return value;
				string slot = fresh_aux_slot("basecast", "ptr");
				string is_null = fresh_temp();
				instr(is_null + " = cmp eq ptr " + value.text + ", 0");
				string null_block = fresh_block("basecast_null");
				string adjust_block = fresh_block("basecast_adjust");
				string end_block = fresh_block("basecast_end");
				terminate("branch " + is_null + ", ^" + null_block + ", ^" + adjust_block);
				start_block(null_block);
				instr("store ptr 0, $" + slot);
				terminate("jump ^" + end_block);
				start_block(adjust_block);
				string adjusted = fresh_temp();
				instr(adjusted + " = index i8 [projection=base_subobject] " + value.text + ", -" + to_string(offset));
				instr("store ptr " + adjusted + ", $" + slot);
				terminate("jump ^" + end_block);
				start_block(end_block);
				string loaded = fresh_temp();
				instr(loaded + " = load ptr $" + slot);
				return Value("ptr", loaded); } }
		return Value(dst, value.text); }
	if (fold_literals && value.text != "" && value.text[0] != '%' && value.text[0] != '$' && value.text[0] != '@' && !is_float_type(from) && !is_float_type(to) && (value.text == "0" || (dst != "ptr" && src != "ptr")))
		return Value(dst, value.text);
	string op = "copy";
	if (dst == "ptr" || src == "ptr")
		op = "copy";
	else if (starts_with(dst, "f") && starts_with(src, "f"))
		op = pa11::type_size(to) > pa11::type_size(from) ? "fpext" : "fptrunc";
	else if (starts_with(dst, "f")) {
		bool literal_zero = value.text == "0" && value.text[0] != '%' && value.text[0] != '$' && value.text[0] != '@';
		if (pa11::is_integral_or_bool_type(from) && pa11::type_size(from_bare) < 8 && !literal_zero) {
			int shift = (8 - pa11::type_size(from_bare)) * 8;
			string shifted = fresh_temp();
			instr(shifted + " = binary shl i64 " + value.text + ", " + to_string(shift));
			string normalized = fresh_temp();
			instr(normalized + " = binary " + string(is_unsigned_type(from) ? "ushr" : "shr") + " i64 " + shifted + ", " + to_string(shift));
			value = Value(value.type, normalized); }
		op = is_unsigned_type(from) ? "uitofp" : "sitofp"; }
	else if (starts_with(src, "f"))
		op = is_unsigned_type(to) ? "fptoui" : "fptosi";
	else if ((is_reference(from) ? pa11::type_size(strip_for_value(from))
	                             : pa11::type_size(from)) == (is_reference(to) ? pa11::type_size(strip_for_value(to))
	                           : pa11::type_size(to)))
		op = "copy";
	else if ((is_reference(to) ? pa11::type_size(strip_for_value(to))
	                           : pa11::type_size(to)) <
	         (is_reference(from) ? pa11::type_size(strip_for_value(from))
	                             : pa11::type_size(from)))
		op = "trunc";
	else
		op = is_unsigned_type(from) ? "zext" : "sext";
	string tmp = fresh_temp();
	if (op == "copy")
		instr(tmp + " = copy " + dst + " " + value.text);
	else
		instr(tmp + " = convert " + op + " " + dst + " " + src + " " + value.text);
	return Value(dst, tmp); }
Value FunctionLowerer::convert_binary_value(Value value, TypePtr from, TypePtr to) {
	string dst = scalar_lowir_type(to);
	string src = scalar_lowir_type(strip_for_value(from));
	if (dst == "i64" && src != dst && is_unsigned_type(to) && value.text != "" && value.text[0] != '%' && value.text[0] != '$' && value.text[0] != '@' && !is_float_type(from) && !is_float_type(to)) {
		string tmp = fresh_temp();
		instr(tmp + " = convert " + string(is_unsigned_type(from) ? "zext" : "sext") + " i64 " + src + " " + value.text);
		return Value("i64", tmp); }
	return convert_value(value, from, to); }
Value FunctionLowerer::bool_value(Value value, TypePtr type) {
	TypePtr bare = strip_cv(strip_for_value(type));
	if (bare->kind == TypeKind::MemberPointer && bare->base.get() != NULL && bare->base->kind == TypeKind::Function && value.type == "i128")
		value = Value("i64", value.text);
	string src = scalar_lowir_type(strip_for_value(type));
	if (value.type == "i64" && src == "i128")
		src = "i64";
	string cmp_type = (!is_float_type(type) && src != "ptr" && src != "i128")
		? "i64" : src;
	string tmp = fresh_temp();
	string zero = is_float_type(type) ? "0.0" : "0";
	instr(tmp + " = cmp ne " + cmp_type + " " + value.text + ", " + zero);
	return Value("u8", tmp); }
Value FunctionLowerer::ensure_pointer(Value storage) {
	if (storage.text.empty())
		return storage;
	if (storage.text[0] != '$' && storage.text[0] != '@')
		return storage;
	string tmp = fresh_temp();
	instr(tmp + " = addr " + storage.text);
	return Value("ptr", tmp); }
void FunctionLowerer::branch_logical_operand(const Node& expr, const string& yes, const string& no) {
	if (starts_with(expr.line, "binary-expression") && expr.has_op && (expr.op == OP_LAND || expr.op == OP_LOR)) {
		Value value = emit_rvalue(expr);
		terminate_with_pending_temp_cleanups(value.text, yes, no);
		return; }
	branch_on(expr, yes, no); }
void FunctionLowerer::branch_with_unwind_cleanups(const Node& expr, const string& yes, const string& no) {
	string dispatch = active_unwind_dispatch_.empty()
		? fresh_block("call_unwind_dispatch") : active_unwind_dispatch_;
	bool define_dispatch = active_unwind_dispatch_.empty();
	instr("eh_try ^" + dispatch);
	++eh_try_depth_;
	Value cond = emit_rvalue(expr);
	if (is_float_type(expr.type))
		cond = bool_value(cond, expr.type);
	--eh_try_depth_;
	instr("eh_end");
	if (define_dispatch) {
		string end = fresh_block("call_unwind_end");
		terminate("jump ^" + end);
		active_unwind_dispatch_ = dispatch;
		start_block(dispatch);
		emit_unwind_cleanups();
		terminate("resume");
		start_block(end); }
	terminate_with_pending_temp_cleanups(cond.text, yes, no); }
Value FunctionLowerer::emit_binary(const Node& expr) {
	if (expr.has_op && expr.op == OP_COMMA) {
		emit_rvalue(expr.children[0]);
		return emit_rvalue(expr.children[1]); }
	if (expr.has_op && (expr.op == OP_EQ || expr.op == OP_NE) && expr.children.size() == 2 && expr.children[0].is_typeid_expression && expr.children[1].is_typeid_expression) {
		Value lhs = emit_lvalue_addr(expr.children[0]);
		Value rhs = emit_lvalue_addr(expr.children[1]);
		string tmp = fresh_temp();
		instr(tmp + " = cmp " + string(expr.op == OP_EQ ? "eq" : "ne") + " ptr " + lhs.text + ", " + rhs.text);
		return Value("u8", tmp); }
	if (expr.has_op && (expr.op == OP_LAND || expr.op == OP_LOR))
		return emit_logical_binary(expr);
	bool wrap_lhs_materialized_member = eh_try_depth_ == 0 && has_active_cleanups() && starts_with(expr.children[0].line, "member-expression") && node_contains_call_expression(expr.children[0]) && expr.children[0].category == ValueCategory::LValue && scalar_lowir_type(expr.children[0].type).compare(0, 4, "obj<") != 0;
	string dispatch;
	bool define_dispatch = false;
	Value lhs;
	if (wrap_lhs_materialized_member) {
		Value lhs_addr;
		if (!expr.children[0].children.empty() && starts_with(expr.children[0].children[0].line, "call-expression") && expr.children[0].binding != NULL) {
			const Node& member_expr = expr.children[0];
			TypePtr object_record = pa11::strip_cv(object_type(member_expr.children[0].type));
			string slot = fresh_aux_slot("tmpobj", scalar_lowir_type(object_record));
			string object_addr_name = fresh_temp();
			instr(object_addr_name + " = addr $" + slot);
			Value object_addr("ptr", object_addr_name);
			function<Value()> object_addr_for = [object_addr]() {
				return object_addr;
			};
			lower_object_init(object_addr_for, object_record, member_expr.children[0]);
			dispatch = active_unwind_dispatch_.empty()
				? fresh_block("call_unwind_dispatch") : active_unwind_dispatch_;
			define_dispatch = active_unwind_dispatch_.empty();
			instr("eh_try ^" + dispatch);
			++eh_try_depth_;
			Binding* member = member_expr.binding;
			TypePtr owner_record = pa11::record_type_for_scope(member->owner);
			Value projected_base = object_addr;
			if (owner_record.get() != NULL && object_record.get() != NULL && object_record->kind == TypeKind::Record && owner_record->kind == TypeKind::Record && !pa11::same_type(object_record, owner_record))
				projected_base = emit_base_subobject_addr(object_addr, object_record, owner_record);
			string field_addr = fresh_temp();
			instr(field_addr + " = index i8 [projection=field] " + projected_base.text + ", " + to_string(member->member_offset));
			lhs_addr = Value("ptr", field_addr); }
		else {
			lhs_addr = ensure_pointer(emit_lvalue_addr(expr.children[0]));
			dispatch = active_unwind_dispatch_.empty()
				? fresh_block("call_unwind_dispatch") : active_unwind_dispatch_;
			define_dispatch = active_unwind_dispatch_.empty();
			instr("eh_try ^" + dispatch);
			++eh_try_depth_; }
		string loaded = fresh_temp();
		instr(loaded + " = load " + scalar_lowir_type(expr.children[0].type) + " " + lhs_addr.text);
		lhs = Value(scalar_lowir_type(expr.children[0].type), loaded); }
	else
		lhs = emit_rvalue(expr.children[0]);
	Value rhs = emit_rvalue(expr.children[1]);
	TypePtr lhs_type = strip_for_value(expr.children[0].type);
	TypePtr rhs_type = strip_for_value(expr.children[1].type);
	if ((expr.op == OP_PLUS || expr.op == OP_MINUS) && scalar_lowir_type(expr.type) == "ptr")
		return emit_pointer_index_binary(expr, lhs, rhs, lhs_type, rhs_type);
	if (expr.op == OP_MINUS && pa11::strip_cv(lhs_type)->kind == TypeKind::Pointer && pa11::strip_cv(rhs_type)->kind == TypeKind::Pointer)
		return emit_pointer_difference(expr, lhs, rhs, lhs_type);
	string op;
	bool cmp = false;
	switch (expr.op) {
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
	default: throw runtime_error("unsupported binary operator"); }
	TypePtr op_type = cmp ? lowir_common_type(expr.children[0].type, expr.children[1].type)
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
	if (cmp && scalar_lowir_type(op_type) == "ptr") {
		if (scalar_lowir_type(strip_for_value(expr.children[0].type)) != "ptr")
			lhs = convert_binary_value(lhs, expr.children[0].type, op_type);
		if (scalar_lowir_type(strip_for_value(expr.children[1].type)) != "ptr")
			rhs = convert_binary_value(rhs, expr.children[1].type, op_type); }
	else {
		lhs = convert_binary_value(lhs, expr.children[0].type, op_type);
		rhs = convert_binary_value(rhs, expr.children[1].type, op_type); }
	string type = scalar_lowir_type(op_type);
	string tmp = fresh_temp();
	instr(tmp + " = " + string(cmp ? "cmp " : "binary ") + op + " " + type + " " + lhs.text + ", " + rhs.text);
	if (wrap_lhs_materialized_member) {
		--eh_try_depth_;
		instr("eh_end");
		if (define_dispatch) {
			string end = fresh_block("call_unwind_end");
			terminate("jump ^" + end);
			active_unwind_dispatch_ = dispatch;
			start_block(dispatch);
			emit_unwind_cleanups();
			terminate("resume");
			start_block(end); } }
	return Value(cmp ? "u8" : scalar_lowir_type(expr.type), tmp); }
Value FunctionLowerer::emit_assignment(const Node& expr) {
	if (expr.op == OP_ASS && expr.children.size() == 2 && pa11::strip_cv(object_type(expr.children[0].type))->kind == TypeKind::Record) {
		TypePtr lhs_type = object_type(expr.children[0].type);
		bool move_assign = expr.children[1].category != ValueCategory::LValue;
		bool wrap = eh_try_depth_ == 0 && has_active_cleanups();
		string dispatch;
		bool define_dispatch = false;
		if (wrap) {
			dispatch = active_unwind_dispatch_.empty()
				? fresh_block("call_unwind_dispatch")
				: active_unwind_dispatch_;
			define_dispatch = active_unwind_dispatch_.empty();
			instr("eh_try ^" + dispatch);
			++eh_try_depth_; }
		Value target = ensure_pointer(emit_lvalue_addr(expr.children[0]));
		TypePtr rhs_type = object_type(expr.children[1].type);
		Value source;
		if (expr.children[1].category == ValueCategory::LValue || expr.children[1].category == ValueCategory::XValue)
			source = ensure_pointer(emit_lvalue_addr(expr.children[1]));
		else {
			TypePtr object = pa11::strip_cv(rhs_type);
			string slot = fresh_aux_slot("assignarg", scalar_lowir_type(object));
			string addr = fresh_temp();
			instr(addr + " = addr $" + slot);
			source = Value("ptr", addr);
			function<Value()> source_addr = [source]() {
				return source;
			};
			lower_object_init(source_addr, object, expr.children[1]); }
		Binding* assign = program_.demand_implicit_copy_assignment(lhs_type, move_assign);
		string tmp = fresh_temp();
		instr(tmp + " = call ptr @" + program_.symbol_for(assign) + "(" + target.text + ", " + source.text + ")");
		if (wrap) {
			--eh_try_depth_;
			instr("eh_end");
			if (define_dispatch) {
				string end = fresh_block("call_unwind_end");
				terminate("jump ^" + end);
				active_unwind_dispatch_ = dispatch;
				start_block(dispatch);
				emit_unwind_cleanups();
				terminate("resume");
				start_block(end); } }
		return Value("ptr", tmp); }
	if (expr.op == OP_ASS && starts_with(expr.children[0].line, "member-expression")) {
		TypePtr lhs_type = object_type(expr.children[0].type);
		bool wrap_lhs_call_store = eh_try_depth_ == 0 && has_active_cleanups() && node_contains_call_expression(expr.children[0]);
		string dispatch;
		bool define_dispatch = false;
		if (wrap_lhs_call_store) {
			dispatch = active_unwind_dispatch_.empty()
				? fresh_block("call_unwind_dispatch")
				: active_unwind_dispatch_;
			define_dispatch = active_unwind_dispatch_.empty();
			instr("eh_try ^" + dispatch);
			++eh_try_depth_; }
		function<void()> finish_lhs_call_store = [this, wrap_lhs_call_store, define_dispatch, dispatch]() {
			if (!wrap_lhs_call_store)
				return;
			--eh_try_depth_;
			instr("eh_end");
			if (define_dispatch) {
				string end = fresh_block("call_unwind_end");
				terminate("jump ^" + end);
				active_unwind_dispatch_ = dispatch;
				start_block(dispatch);
				emit_unwind_cleanups();
				terminate("resume");
				start_block(end); }
		};
		Value rhs = emit_rvalue(expr.children[1]);
		rhs = convert_binary_value(rhs, expr.children[1].type, lhs_type);
		Value addr = emit_lvalue_addr(expr.children[0]);
		if (expr.children[0].binding != NULL && expr.children[0].binding->is_bit_field) {
			Binding* field = expr.children[0].binding;
			string low_type = scalar_lowir_type(lhs_type);
			uint64_t mask = field->bit_width >= 64
				? ~uint64_t(0) : ((uint64_t(1) << field->bit_width) - 1);
			string masked = fresh_temp();
			instr(masked + " = binary and " + low_type + " " + rhs.text + ", " + to_string(mask));
			string shifted = masked;
			uint64_t storage_mask = mask << field->bit_offset;
			if (field->bit_offset != 0) {
				shifted = fresh_temp();
				instr(shifted + " = binary shl " + low_type + " " + masked + ", " + to_string(field->bit_offset)); }
			string oldv = fresh_temp();
			instr(oldv + " = load " + low_type + " " + addr.text);
			string cleared = fresh_temp();
			instr(cleared + " = binary and " + low_type + " " + oldv + ", " + to_string(~storage_mask));
			string merged = fresh_temp();
			instr(merged + " = binary or " + low_type + " " + cleared + ", " + shifted);
			instr("store " + low_type + " " + merged + ", " + addr.text);
			finish_lhs_call_store();
			return rhs; }
		instr("store " + scalar_lowir_type(lhs_type) + " " + rhs.text + ", " + addr.text);
		finish_lhs_call_store();
		return rhs; }
	TypePtr lhs_type = object_type(expr.children[0].type);
	if (expr.op != OP_ASS) {
		Value oldv = emit_rvalue(expr.children[0]);
		Value rhs = emit_rvalue(expr.children[1]);
		if (scalar_lowir_type(lhs_type) == "ptr" && (expr.op == OP_PLUSASS || expr.op == OP_MINUSASS)) {
			TypePtr ptr = pa11::strip_cv(strip_for_value(lhs_type));
			uint64_t scale = pa11::type_size(ptr->base);
			string offset = rhs.text;
			if (scale != 1) {
				string mul = fresh_temp();
				instr(mul + " = binary mul i64 " + offset + ", " + to_string(scale));
				offset = mul; }
			if (expr.op == OP_MINUSASS) {
				string neg = fresh_temp();
				instr(neg + " = binary sub i64 0, " + offset);
				offset = neg; }
			string tmp = fresh_temp();
			instr(tmp + " = index i8 " + oldv.text + ", " + offset);
			Value addr = emit_lvalue_addr(expr.children[0]);
			instr("store ptr " + tmp + ", " + addr.text);
			return Value("ptr", tmp); }
		TypePtr arithmetic_type = lowir_common_type(expr.children[0].type, expr.children[1].type);
		oldv = convert_binary_value(oldv, expr.children[0].type, arithmetic_type);
		rhs = convert_value(rhs, expr.children[1].type, arithmetic_type);
		ETokenType op = expr.op == OP_PLUSASS ? OP_PLUS : expr.op == OP_MINUSASS ? OP_MINUS : expr.op == OP_STARASS ? OP_STAR : expr.op == OP_DIVASS ? OP_DIV : expr.op == OP_MODASS ? OP_MOD : OP_PLUS;
		string op_name = op == OP_MINUS ? "sub" : op == OP_STAR ? "mul" : op == OP_DIV ? (is_unsigned_type(arithmetic_type) ? "udiv" : "div") : op == OP_MOD ? (is_unsigned_type(arithmetic_type) ? "umod" : "mod") : "add";
		string tmp = fresh_temp();
		instr(tmp + " = binary " + op_name + " " + scalar_lowir_type(arithmetic_type) + " " + oldv.text + ", " + rhs.text);
		rhs = convert_value(Value(scalar_lowir_type(arithmetic_type), tmp), arithmetic_type, lhs_type);
		Value addr = emit_lvalue_addr(expr.children[0]);
		instr("store " + scalar_lowir_type(lhs_type) + " " + rhs.text + ", " + addr.text);
		return rhs; }
		Binding* lhs_binding = expr.children[0].binding;
		map<const Binding*, string>::const_iterator slot_it = lhs_binding != NULL ? slots_.find(lhs_binding) : slots_.end();
		if (starts_with(expr.children[1].line, "call-expression") && slot_it != slots_.end()) {
			call_result_store_slot_ = slot_it->second;
			call_result_store_type_ = lhs_type;
			call_result_store_consumed_ = false; }
		Value rhs = emit_rvalue(expr.children[1]);
		if (!call_result_store_consumed_) {
			rhs = convert_binary_value(rhs, expr.children[1].type, lhs_type);
			Value addr = emit_lvalue_addr(expr.children[0]);
			instr("store " + scalar_lowir_type(lhs_type) + " " + rhs.text + ", " + addr.text); }
		call_result_store_slot_.clear();
		call_result_store_type_.reset();
		call_result_store_consumed_ = false;
		return rhs; }
Value FunctionLowerer::emit_unary(const Node& expr) {
	if (expr.op == OP_AMP) {
		TypePtr result_bare = pa11::strip_cv(expr.type);
		if (result_bare->kind == TypeKind::MemberPointer) {
			if (expr.children.empty() || expr.children[0].binding == NULL)
				throw runtime_error("member pointer address missing member");
			Binding* member = expr.children[0].binding->aliased_binding != NULL && expr.children[0].binding->target_scope != NULL
				? expr.children[0].binding->aliased_binding
				: expr.children[0].binding;
			if (member->kind == BindingKind::Function) {
				if (member->is_inline_definition)
					program_.demand_inline_function(member);
				if (!program_.native_lowering) {
					string addr = fresh_temp();
					instr(addr + " = addr @" + program_.symbol_for(member));
					string bits = fresh_temp();
					instr(bits + " = copy i64 " + addr);
					string wide = fresh_temp();
					instr(wide + " = convert zext i128 i64 " + bits);
					return Value("i128", wide); }
				string bits = fresh_temp();
				if (member->virtual_slot_index >= 0) {
					TypePtr owner = pa11::record_type_for_scope(member->owner);
					if (owner.get() != NULL)
						program_.demand_vtable(owner);
					string slot = fresh_aux_slot("memptr_lit", "i128");
					string addr = fresh_temp();
					instr(addr + " = addr $" + slot);
					instr("store i64 " + to_string(member->virtual_slot_index * 8) + ", " + addr);
					string flag_addr = fresh_temp();
					instr(flag_addr + " = index i8 " + addr + ", 8");
					instr("store i64 1, " + flag_addr);
					instr(bits + " = load i128 $" + slot);
					return Value("i128", bits); }
				else {
					string addr = fresh_temp();
					instr(addr + " = addr @" + program_.symbol_for(member));
					instr(bits + " = copy i64 " + addr); }
				string wide = fresh_temp();
				instr(wide + " = convert zext i128 i64 " + bits);
				return Value("i128", wide); }
			TypePtr owner = pa11::record_type_for_scope(member->owner);
			if (owner.get() != NULL)
				pa11::layout_record_type(pa11::strip_cv(owner));
			string tmp = fresh_temp();
			instr(tmp + " = const i64 " + to_string(member->member_offset + 1));
			return Value("i64", tmp); }
		if (!expr.children.empty() && expr.children[0].binding != NULL && expr.children[0].binding->kind == BindingKind::Function) {
			if (expr.children[0].binding->is_inline_definition)
				program_.demand_inline_function(expr.children[0].binding);
			string addr = fresh_temp();
			instr(addr + " = addr @" + program_.symbol_for(expr.children[0].binding));
			return Value("ptr", addr); }
		return ensure_pointer(emit_lvalue_addr(expr.children[0])); }
	if (expr.op == OP_STAR) {
		Value addr = emit_lvalue_addr(expr);
		string tmp = fresh_temp();
		instr(tmp + " = load " + scalar_lowir_type(expr.type) + " " + addr.text);
		return Value(scalar_lowir_type(expr.type), tmp); }
	if (expr.op == OP_INC || expr.op == OP_DEC) {
		Value addr = emit_lvalue_addr(expr.children[0]);
		TypePtr value_type = strip_for_value(expr.children[0].type);
		string oldtmp = fresh_temp();
		instr(oldtmp + " = load " + scalar_lowir_type(value_type) + " " + addr.text);
		Value oldv(scalar_lowir_type(value_type), oldtmp);
		string one = "1";
		string tmp;
		if (oldv.type == "ptr") {
			TypePtr ptr = pa11::strip_cv(strip_for_value(expr.type));
			uint64_t scale = pa11::type_size(ptr->base);
			if (expr.op == OP_DEC && scale == 1)
				one = "-1";
			else if (expr.op == OP_DEC) {
				string mul = fresh_temp();
				instr(mul + " = binary mul i64 1, " + to_string(scale));
				string neg = fresh_temp();
				instr(neg + " = binary sub i64 0, " + mul);
				one = neg; }
			else if (scale != 1) {
				string mul = fresh_temp();
				instr(mul + " = binary mul i64 1, " + to_string(scale));
				one = mul; }
			tmp = fresh_temp();
			instr(tmp + " = index i8 " + oldv.text + ", " + one); }
		else {
			tmp = fresh_temp();
			instr(tmp + " = binary " + string(expr.op == OP_INC ? "add" : "sub") + " " + scalar_lowir_type(expr.type) + " " + oldv.text + ", " + one); }
		instr("store " + scalar_lowir_type(expr.type) + " " + tmp + ", " + addr.text);
		return Value(scalar_lowir_type(expr.type), tmp); }
	Value inner = emit_rvalue(expr.children[0]);
	if (expr.op == OP_PLUS)
		return inner;
	string op = expr.op == OP_MINUS ? "neg" : expr.op == OP_COMPL ? "bitnot" : "not";
	if (expr.op == OP_LNOT) {
		string tmp = fresh_temp();
		TypePtr bare = strip_cv(strip_for_value(expr.children[0].type));
		if (bare->kind == TypeKind::MemberPointer && bare->base.get() != NULL && bare->base->kind == TypeKind::Function && inner.type == "i128")
			inner = Value("i64", inner.text);
		string cmp_type = (!is_float_type(expr.children[0].type) && inner.type != "ptr" && inner.type != "i128") ? "i64" : inner.type;
			string zero = is_float_type(expr.children[0].type) ? "0.0" : "0";
		instr(tmp + " = cmp eq " + cmp_type + " " + inner.text + ", " + zero);
		return Value("u8", tmp); }
	string tmp = fresh_temp();
	instr(tmp + " = unary " + op + " " + inner.type + " " + inner.text);
	return Value(inner.type, tmp); }
Value FunctionLowerer::emit_postfix(const Node& expr) {
	Value addr = emit_lvalue_addr(expr.children[0]);
	bool refetch_store_addr = starts_with(expr.children[0].line, "call-expression") && is_reference(expr.children[0].type);
	TypePtr value_type = strip_for_value(expr.children[0].type);
	string oldtmp = fresh_temp();
	instr(oldtmp + " = load " + scalar_lowir_type(value_type) + " " + addr.text);
	Value oldv(scalar_lowir_type(value_type), oldtmp);
	string one = "1";
	string tmp;
	if (oldv.type == "ptr") {
		TypePtr ptr = pa11::strip_cv(strip_for_value(expr.type));
		uint64_t scale = pa11::type_size(ptr->base);
		if (expr.op == OP_DEC && scale == 1)
			one = "-1";
		else if (expr.op == OP_DEC) {
			string mul = fresh_temp();
			instr(mul + " = binary mul i64 1, " + to_string(scale));
			string neg = fresh_temp();
			instr(neg + " = binary sub i64 0, " + mul);
			one = neg; }
		else if (scale != 1) {
			string mul = fresh_temp();
			instr(mul + " = binary mul i64 1, " + to_string(scale));
			one = mul; }
		tmp = fresh_temp();
		instr(tmp + " = index i8 " + oldv.text + ", " + one); }
	else {
		tmp = fresh_temp();
		instr(tmp + " = binary " + string(expr.op == OP_INC ? "add" : "sub") + " " + oldv.type + " " + oldv.text + ", 1"); }
	Value store_addr = refetch_store_addr ? emit_lvalue_addr(expr.children[0]) : addr;
	instr("store " + oldv.type + " " + tmp + ", " + store_addr.text);
	return oldv; }
Value FunctionLowerer::emit_cast(const Node& expr) {
	if (expr.is_dynamic_cast_expression)
		return emit_dynamic_cast(expr, is_reference(expr.type));
	if (pa11::is_void_type(expr.type)) {
		if (expr.children[0].category == ValueCategory::LValue && pa11::strip_cv(object_type(expr.children[0].type))->kind == TypeKind::Record)
			ensure_pointer(emit_lvalue_addr(expr.children[0]));
		else
			lower_discarded_expr(expr.children[0]);
		return Value("void", ""); }
	if (is_reference(expr.type))
		return emit_rvalue(expr.children[0]);
	TypePtr cast_source = pa11::strip_cv(strip_for_value(expr.children[0].type));
	TypePtr cast_target = pa11::strip_cv(strip_for_value(expr.type));
	if (cast_source->kind == TypeKind::Enum && cast_source->enum_underlying != FT_INT && cast_target->kind == TypeKind::Fundamental && scalar_lowir_type(expr.children[0].type) == scalar_lowir_type(expr.type)) {
		Value raw = emit_rvalue(expr.children[0]);
		string tmp = fresh_temp();
		instr(tmp + " = copy " + scalar_lowir_type(expr.type) + " " + raw.text);
		return Value(scalar_lowir_type(expr.type), tmp); }
	if (cast_source->kind == TypeKind::Fundamental && cast_target->kind == TypeKind::Enum && cast_target->enum_underlying != FT_INT && scalar_lowir_type(expr.children[0].type) == scalar_lowir_type(expr.type)) {
		Value raw = emit_rvalue(expr.children[0]);
		string tmp = fresh_temp();
		instr(tmp + " = copy " + scalar_lowir_type(expr.type) + " " + raw.text);
		return Value(scalar_lowir_type(expr.type), tmp); }
	if (cast_source->kind == TypeKind::Fundamental && cast_target->kind == TypeKind::Fundamental && cast_source->fundamental == FT_LONG_INT && cast_target->fundamental == FT_UNSIGNED_LONG_INT && scalar_lowir_type(expr.children[0].type) == scalar_lowir_type(expr.type)) {
		Value raw = emit_rvalue(expr.children[0]);
		string tmp = fresh_temp();
		instr(tmp + " = copy " + scalar_lowir_type(expr.type) + " " + raw.text);
		return Value(scalar_lowir_type(expr.type), tmp); }
	if (cast_source->kind == TypeKind::Pointer && cast_target->kind == TypeKind::Pointer && expr.children[0].binding != NULL && expr.children[0].binding->kind == BindingKind::Parameter && expr.children[0].binding->name == "this") {
		TypePtr source_record = pa11::strip_cv(cast_source->base);
		TypePtr target_record = pa11::strip_cv(cast_target->base);
		if (source_record->kind == TypeKind::Record && target_record->kind == TypeKind::Record && record_has_base_subobject(target_record, source_record)) {
			program_.mark_static_downcast_source_record(source_record);
			Value raw = emit_rvalue(expr.children[0]);
			uint64_t offset = base_subobject_offset(target_record, source_record);
			if (offset == 0)
				return raw;
			string tmp = fresh_temp();
			instr(tmp + " = index i8 [projection=base_subobject] " + raw.text + ", -" + to_string(offset));
			return Value("ptr", tmp); } }
	return convert_value(emit_rvalue(expr.children[0]), expr.children[0].type, expr.type); }
void FunctionLowerer::branch_on(const Node& expr, const string& yes, const string& no) {
	if (starts_with(expr.line, "condition-declaration")) {
		if (expr.children.empty())
			throw runtime_error("empty condition declaration");
		lower_variable_decl(expr.children[0]);
		const Node& cond_node = expr.children.size() > 1 ? expr.children[1] : expr.children[0];
		Value cond = emit_rvalue(cond_node);
		if (is_float_type(cond_node.type))
			cond = bool_value(cond, cond_node.type);
		terminate_with_pending_temp_cleanups(cond.text, yes, no);
		return; }
	if (starts_with(expr.line, "binary-expression") && expr.has_op && expr.op == OP_LOR) {
		string rhs = fresh_block("lor_rhs");
		branch_on(expr.children[0], yes, rhs);
		start_block(rhs);
		branch_on(expr.children[1], yes, no);
		return; }
	if (starts_with(expr.line, "binary-expression") && expr.has_op && expr.op == OP_LAND) {
		string rhs = fresh_block("land_rhs");
		branch_on(expr.children[0], rhs, no);
		start_block(rhs);
		branch_on(expr.children[1], yes, no);
		return; }
	if (eh_try_depth_ == 0 && has_active_cleanups() && node_contains_call_expression(expr)) {
		branch_with_unwind_cleanups(expr, yes, no);
		return; }
	Value cond = emit_rvalue(expr);
	if (is_float_type(expr.type))
		cond = bool_value(cond, expr.type);
	terminate_with_pending_temp_cleanups(cond.text, yes, no); }
}  // namespace internal
}  // namespace pa14
