#include "pa14_lowir_internal.h"
#include "pa12_templates_function_support.h"
#include <cctype>
namespace pa14 { namespace internal { bool starts_with(const string& text, const string& prefix) {
return text.size() >= prefix.size() && text.compare(0, prefix.size(), prefix) == 0; } TypePtr object_type(TypePtr type)
{ if (type->kind == TypeKind::LValueReference || type->kind == TypeKind::RValueReference) return type->base;
return type; } TypePtr strip_for_value(TypePtr type) {
TypePtr object = object_type(type); if (object->kind == TypeKind::Array) return pa11::make_pointer(object->base); if (object->kind == TypeKind::Function)
return pa11::make_pointer(object); return pa11::strip_top_level_cv(object); } bool is_reference(TypePtr type)
{ return type->kind == TypeKind::LValueReference || type->kind == TypeKind::RValueReference; }
bool is_float_type(TypePtr type) { TypePtr bare = pa11::strip_cv(strip_for_value(type)); return bare->kind == TypeKind::Fundamental &&
(bare->fundamental == FT_FLOAT || bare->fundamental == FT_DOUBLE || bare->fundamental == FT_LONG_DOUBLE); }
bool is_unsigned_type(TypePtr type) { TypePtr bare = pa11::strip_cv(strip_for_value(type)); if (bare->kind == TypeKind::Enum)
{ switch (bare->enum_underlying) { case FT_UNSIGNED_CHAR:
case FT_UNSIGNED_SHORT_INT: case FT_UNSIGNED_INT: case FT_UNSIGNED_LONG_INT: case FT_UNSIGNED_LONG_LONG_INT: case FT_UNSIGNED_INT128:
return true; default: return false; }
} if (bare->kind != TypeKind::Fundamental) return false; switch (bare->fundamental)
{ case FT_UNSIGNED_CHAR: case FT_UNSIGNED_SHORT_INT: case FT_UNSIGNED_INT:
case FT_UNSIGNED_LONG_INT: case FT_UNSIGNED_LONG_LONG_INT: case FT_UNSIGNED_INT128: case FT_CHAR16_T: case FT_CHAR32_T:
case FT_BOOL: return true; default: return false;
} } bool is_initializer_list_type(TypePtr type, TypePtr* element) {
if (type.get() == NULL) return false; TypePtr bare = pa11::strip_cv(type);
if (bare->kind != TypeKind::Record || !bare->is_template_specialization ||
bare->template_primary_name != "initializer_list") return false;
Scope* owner = bare->scope != NULL ? bare->scope->parent : NULL;
if (owner == NULL || owner->kind != ScopeKind::Namespace || owner->name != "std") return false;
if (bare->template_arguments.size() != 1 ||
bare->template_arguments[0].kind != pa11::TemplateInstanceArgumentKind::Type) return false;
if (element != NULL) *element = bare->template_arguments[0].type;
return true;
} string scalar_lowir_type(TypePtr type) {
TypePtr bare = pa11::strip_cv(object_type(type)); if (is_reference(type)) return "ptr"; if (bare->kind == TypeKind::Pointer ||
bare->kind == TypeKind::Function || bare->kind == TypeKind::Array) return "ptr"; if (bare->kind == TypeKind::MemberPointer)
return pa11::strip_cv(bare->base)->kind == TypeKind::Function ? "i128" : "i64"; if (bare->kind == TypeKind::Record)
{ ostringstream out; out << "obj<" << pa11::type_size(bare) << "x" << pa11::type_align(bare) << ">";
return out.str(); } if (bare->kind == TypeKind::Enum) {
switch (pa11::type_size(bare)) { case 1: return "i8"; case 2: return "i16";
case 4: return "i32"; default: return "i64"; } }
if (bare->kind != TypeKind::Fundamental) throw runtime_error("unsupported PA14 type"); switch (bare->fundamental) {
case FT_BOOL: return "u8"; case FT_CHAR: case FT_SIGNED_CHAR: return "i8"; case FT_UNSIGNED_CHAR: return "u8"; case FT_SHORT_INT: return "i16";
case FT_UNSIGNED_SHORT_INT: return "u16"; case FT_INT: return "i32"; case FT_UNSIGNED_INT: return "u32"; case FT_LONG_INT:
case FT_LONG_LONG_INT: case FT_UNSIGNED_LONG_INT: case FT_UNSIGNED_LONG_LONG_INT: return "i64"; case FT_INT128: case FT_UNSIGNED_INT128: return "i128";
case FT_FLOAT: return "f32"; case FT_DOUBLE: return "f64"; case FT_LONG_DOUBLE: return "f80"; case FT_VOID: return "void";
case FT_NULLPTR_T: return "i64"; case FT_WCHAR_T: return "i32"; case FT_CHAR16_T: return "u16"; case FT_CHAR32_T: return "u32";
} throw runtime_error("unknown fundamental type"); } int lowir_arithmetic_rank(TypePtr type)
{ TypePtr bare = pa11::strip_cv(strip_for_value(type)); if (bare->kind == TypeKind::Enum) return 3;
if (bare->kind != TypeKind::Fundamental) return 0; switch (bare->fundamental) {
case FT_BOOL: case FT_CHAR: case FT_SIGNED_CHAR: case FT_UNSIGNED_CHAR: return 1; case FT_SHORT_INT: case FT_UNSIGNED_SHORT_INT: return 2; case FT_CHAR16_T: return 2;
case FT_WCHAR_T: case FT_CHAR32_T: case FT_INT: case FT_UNSIGNED_INT: return 3; case FT_LONG_INT: case FT_UNSIGNED_LONG_INT:
case FT_LONG_LONG_INT: case FT_UNSIGNED_LONG_LONG_INT: return 4; case FT_INT128: case FT_UNSIGNED_INT128: return 5; case FT_FLOAT: return 6; case FT_DOUBLE: return 7; case FT_LONG_DOUBLE: return 8;
default: return 0; } } TypePtr lowir_integral_promotion(TypePtr type)
{ TypePtr bare = pa11::strip_cv(strip_for_value(type)); if (bare->kind == TypeKind::Enum || (pa11::is_integral_or_bool_type(type) &&
lowir_arithmetic_rank(type) < 3)) return pa11::make_fundamental(FT_INT); return strip_for_value(type); }
TypePtr lowir_common_type(TypePtr left, TypePtr right) { TypePtr l = lowir_integral_promotion(left); TypePtr r = lowir_integral_promotion(right);
if (pa11::strip_cv(l)->kind == TypeKind::Pointer) return l; if (pa11::strip_cv(r)->kind == TypeKind::Pointer) return r;
if (pa11::same_type(l, r)) return l; if (is_float_type(l)) return is_float_type(r) && lowir_arithmetic_rank(r) >
lowir_arithmetic_rank(l) ? r : l; if (is_float_type(r)) return r; return lowir_arithmetic_rank(r) > lowir_arithmetic_rank(l) ? r : l;
} string slot_lowir_type(TypePtr type) { TypePtr bare = pa11::strip_cv(type);
if (is_reference(type)) return "ptr"; if (bare->kind == TypeKind::Array) {
ostringstream out; out << "obj<" << pa11::type_size(bare) << "x" << pa11::type_align(bare) << ">"; return out.str();
} if (bare->kind == TypeKind::Record) { ostringstream out;
out << "obj<" << pa11::type_size(bare) << "x" << pa11::type_align(bare) << ">"; return out.str(); }
return scalar_lowir_type(type); } namespace { bool is_copy_or_move_constructor(const Binding* binding, TypePtr record)
{ if (binding == NULL || binding->kind != BindingKind::Function || binding->type->kind != TypeKind::Function ||
binding->type->parameters.size() < 2) return false; TypePtr param = binding->type->parameters[1]; if (!is_reference(param))
return false; TypePtr param_record = pa11::strip_cv(param->base); TypePtr target_record = pa11::strip_cv(record); return pa11::same_type(param_record, target_record);
} bool is_move_constructor(const Binding* binding, TypePtr record) { if (!is_copy_or_move_constructor(binding, record))
return false; return binding->type->parameters[1]->kind == TypeKind::RValueReference; } bool type_has_user_copy_move_or_destructor(TypePtr type);
bool type_has_abi_indirect_special_member(TypePtr type); bool defaulted_member_affects_call_abi(const Binding* binding) { if (binding->owner == NULL || binding->owner->kind != ScopeKind::Class)
return binding->is_inline_definition; TypePtr record = pa11::record_type_for_scope(binding->owner); if (record.get() == NULL) return binding->is_inline_definition;
	TypePtr bare = pa11::strip_cv(record); if (bare->tag == "union") return true; pa11::layout_record_type(bare);
	vector<TypePtr> bases = pa11::record_direct_bases(bare); for (size_t i = 0; i < bases.size(); ++i)
	if (type_has_abi_indirect_special_member(bases[i])) return true; for (size_t i = 0; i < bare->fields.size(); ++i)
	if (type_has_abi_indirect_special_member(bare->fields[i]->type)) return true; return false; }
bool record_declares_or_inherits_virtual_base(TypePtr type)
{
	TypePtr bare = type.get() != NULL ? pa11::strip_cv(type) : TypePtr();
	if (bare.get() == NULL || bare->kind != TypeKind::Record)
		return false;
	for (size_t i = 0; i < bare->direct_base_virtuals.size(); ++i)
		if (bare->direct_base_virtuals[i])
			return true;
	vector<TypePtr> bases = bare->direct_bases;
	for (size_t i = 0; i < bases.size(); ++i)
		if (record_declares_or_inherits_virtual_base(bases[i]))
			return true;
	return false;
}
bool special_member_affects_call_abi(const Binding* binding) { if (binding->is_generated_copy_move_constructor || binding->is_generated_default_destructor)
return false; if (!binding->is_defaulted) return true; return defaulted_member_affects_call_abi(binding);
} bool record_has_user_copy_move_or_destructor(TypePtr type) { TypePtr bare = pa11::strip_cv(type);
if (bare->kind != TypeKind::Record || bare->scope == NULL) return false; if (bare->tag == "union") return true;
map<string, vector<Binding*> >::const_iterator ctors = bare->scope->members.find(bare->scope->name); if (ctors != bare->scope->members.end()) {
for (size_t i = 0; i < ctors->second.size(); ++i) { Binding* ctor = ctors->second[i]; if (bare->is_template_specialization &&
	ctor->is_defaulted && !ctor->is_generated_copy_move_constructor && is_move_constructor(ctor, bare) && (!pa11::record_direct_bases(bare).empty() || !bare->fields.empty()))
	return true; if (is_copy_or_move_constructor(ctor, bare) && special_member_affects_call_abi(ctor)) return true;
	} } string dtor_name = "~" + bare->scope->name; map<string, vector<Binding*> >::const_iterator dtors =
	bare->scope->members.find(dtor_name); if (dtors != bare->scope->members.end()) { for (size_t i = 0; i < dtors->second.size(); ++i)
	if (dtors->second[i]->kind == BindingKind::Function && special_member_affects_call_abi(dtors->second[i])) return true; }
	vector<TypePtr> bases = pa11::record_direct_bases(bare); for (size_t i = 0; i < bases.size(); ++i)
	if (type_has_user_copy_move_or_destructor(bases[i])) return true; pa11::layout_record_type(bare);
	for (size_t i = 0; i < bare->fields.size(); ++i) if (type_has_user_copy_move_or_destructor(bare->fields[i]->type)) return true; return false;
} bool type_has_user_copy_move_or_destructor(TypePtr type) { TypePtr bare = pa11::strip_cv(type);
if (bare->kind == TypeKind::Array) return type_has_user_copy_move_or_destructor(bare->base); if (bare->kind == TypeKind::Record) return record_has_user_copy_move_or_destructor(bare);
return false; } bool record_has_abi_indirect_special_member(TypePtr type) {
TypePtr bare = pa11::strip_cv(type); if (bare->kind != TypeKind::Record || bare->scope == NULL) return false; if (bare->tag == "union")
return true; map<string, vector<Binding*> >::const_iterator ctors = bare->scope->members.find(bare->scope->name); if (ctors != bare->scope->members.end())
{ for (size_t i = 0; i < ctors->second.size(); ++i) { Binding* ctor = ctors->second[i];
if ((is_move_constructor(ctor, bare) || (bare->is_template_specialization && is_copy_or_move_constructor(ctor, bare))) && special_member_affects_call_abi(ctor))
return true; } } string dtor_name = "~" + bare->scope->name;
map<string, vector<Binding*> >::const_iterator dtors = bare->scope->members.find(dtor_name); if (dtors != bare->scope->members.end()) {
for (size_t i = 0; i < dtors->second.size(); ++i) if (dtors->second[i]->kind == BindingKind::Function && special_member_affects_call_abi(dtors->second[i])) return true;
	} vector<TypePtr> bases = pa11::record_direct_bases(bare); for (size_t i = 0; i < bases.size(); ++i)
	if (type_has_abi_indirect_special_member(bases[i])) return true;
	pa11::layout_record_type(bare); for (size_t i = 0; i < bare->fields.size(); ++i) if (type_has_abi_indirect_special_member(bare->fields[i]->type)) return true;
return false; } bool type_has_abi_indirect_special_member(TypePtr type) {
TypePtr bare = pa11::strip_cv(type); if (bare->kind == TypeKind::Array) return type_has_abi_indirect_special_member(bare->base); if (bare->kind == TypeKind::Record)
return record_has_abi_indirect_special_member(bare); return false; }
}  // namespace
bool record_pass_by_address(TypePtr type) { if (is_initializer_list_type(type, NULL)) return false; TypePtr bare = pa11::strip_cv(type); if (bare->kind != TypeKind::Record)
return false; if (pa11::type_size(bare) > 16) return true; return record_has_abi_indirect_special_member(bare);
} bool record_return_by_address(TypePtr type) { TypePtr bare = pa11::strip_cv(type);
if (bare->kind != TypeKind::Record) return false; if (is_initializer_list_type(type, NULL)) return false; if (record_declares_or_inherits_virtual_base(bare)) return true; if (pa11::type_size(bare) > 16) return true;
return record_has_user_copy_move_or_destructor(bare); } bool record_has_nontrivial_value_transfer(TypePtr type) {
return record_has_user_copy_move_or_destructor(type); } bool record_has_storage_copy(TypePtr type) {
TypePtr bare = pa11::strip_cv(type); if (bare->kind == TypeKind::Array) return record_has_storage_copy(bare->base); if (bare->kind != TypeKind::Record)
	return true; pa11::layout_record_type(bare); if (!pa11::record_virtual_bases(bare).empty()) return false; vector<TypePtr> bases = pa11::record_direct_bases(bare); for (size_t i = 0; i < bases.size(); ++i)
	if (record_has_storage_copy(bases[i])) return true; return !bare->fields.empty(); } string lowir_literal(TypePtr type, const Node& node)
{ if (node.token_text == "nullptr") return "nullptr"; if (node.has_constant_value && !is_float_type(type))
return to_string(node.constant_value); if (!node.token_text.empty()) return node.token_text; return to_string(node.constant_value);
} string lowir_parameter(TypePtr type) { string out = scalar_lowir_type(type);
if (is_reference(type)) out += " [pass=reference]"; else if (pa11::strip_cv(type)->kind == TypeKind::Record && record_pass_by_address(type))
out = "ptr [pass=by_address]"; return out; } string metadata_suffix(const vector<string>& items)
{ if (items.empty()) return ""; ostringstream out;
out << " ["; for (size_t i = 0; i < items.size(); ++i) { if (i != 0)
out << ", "; out << items[i]; } out << "]";
return out.str(); } string sanitized_symbol_part(const string& part) {
ostringstream out; for (size_t i = 0; i < part.size(); ++i) { const unsigned char ch = static_cast<unsigned char>(part[i]);
if (isalnum(ch) || ch == '_') out << part[i]; else if (ch == '+') out << "_plus";
else if (ch == '-') out << "_minus"; else if (ch == '*') out << "_star";
else if (ch == '/') out << "_slash"; else if (ch == '%') out << "_percent";
else if (ch == '&') out << "_amp"; else if (ch == '|') out << "_bar";
else if (ch == '^') out << "_caret"; else if (ch == '~') out << "_tilde";
else if (ch == '!') out << "_bang"; else if (ch == '=') out << "_eq";
else if (ch == '<') out << "_lt"; else if (ch == '>') out << "_gt";
else if (ch == '[') out << "_lb"; else if (ch == ']') out << "_rb";
else if (ch == '(') out << "_lp"; else if (ch == ')') out << "_rp";
else if (ch == ',') out << "_comma"; else out << "_x" << static_cast<unsigned>(ch) << "_";
} string text = out.str(); if (text.empty()) return "_";
if (isdigit(static_cast<unsigned char>(text[0]))) text = "_" + text; return text; }
string hex_symbol_text(const string& text) { static const char* digits = "0123456789abcdef"; string out;
for (size_t i = 0; i < text.size(); ++i) { unsigned char ch = static_cast<unsigned char>(text[i]); out.push_back(digits[ch >> 4]);
out.push_back(digits[ch & 0xf]); } return out; }
string abi_source_name(const string& name) { return to_string(name.size()) + name; }
string template_record_symbol_part(TypePtr record); string template_abi_component_for_type(TypePtr type); vector<string> qualified_parts(const Binding* binding) {
vector<string> parts; for (Scope* s = binding->owner; s != NULL; s = s->parent) { if ((s->kind == ScopeKind::Namespace || s->kind == ScopeKind::Class) &&
!s->name.empty()) { string part = s->name == "<unnamed>" ? "_GLOBAL__N_1" : s->name; if (s->kind == ScopeKind::Class)
{ TypePtr record = pa11::record_type_for_scope(s); if (record_is_template_specialization(record)) part = template_record_symbol_part(record);
} parts.push_back(part); } }
vector<string> out; for (size_t i = parts.size(); i > 0; --i) out.push_back(parts[i - 1]); if (binding->owner != NULL &&
binding->owner->kind == ScopeKind::Class && !binding->name.empty() && binding->name[0] == '~') out.push_back("_" + binding->name.substr(1));
else if (binding->name == "operator[]" || binding->name == "operator()" || binding->name == "operator ()") out.push_back("operator__"); else if (binding->name == "operator=" || binding->name == "operator," || binding->name == "operator ,") out.push_back("operator_");
else if (binding->name == "operator&=") out.push_back("operator__"); else if (binding->name.compare(0, 18, "operator typename ") == 0) out.push_back("operator" + binding->name.substr(18));
else out.push_back(binding->name); return out; }
string source_symbol_base(const Binding* binding) { if (binding != NULL && binding->is_local_static) {
if (binding->local_static_function_owner != NULL && !binding->local_static_function_owner ->function_specialization_symbol.empty()) {
ostringstream out; out << "__local_static__function_symbol_" << hex_symbol_text(binding->local_static_function_owner ->function_specialization_symbol)
<< "__" << sanitized_symbol_part(binding->name); if (!binding->local_static_discriminator.empty()) out << "__" << sanitized_symbol_part( binding->local_static_discriminator);
return out.str(); } vector<string> parts; for (Scope* s = binding->owner; s != NULL; s = s->parent)
{ if ((s->kind == ScopeKind::Namespace || s->kind == ScopeKind::Class || s->kind == ScopeKind::Function) &&
!s->name.empty()) parts.push_back(s->name); } ostringstream out;
out << "__local_static"; for (size_t i = parts.size(); i > 0; --i) out << "__" << sanitized_symbol_part(parts[i - 1]); out << "__" << sanitized_symbol_part(binding->name);
if (!binding->local_static_discriminator.empty()) out << "__" << sanitized_symbol_part( binding->local_static_discriminator); return out.str();
} if (binding->owner != NULL && binding->owner->parent == NULL && binding->kind == BindingKind::Function)
{ if (binding->name == "operatornew") return binding->type.get() != NULL && binding->type->parameters.size() == 1
? "operator_new" : "operatornew"; if (binding->name == "operatordelete") return binding->type.get() != NULL && binding->type->parameters.size() == 1
? "operator_delete" : "operatordelete"; if (binding->name == "operatornew[]") return binding->type.get() != NULL && binding->type->parameters.size() == 1
? "operator_new__" : "operatornew__"; if (binding->name == "operatordelete[]") return binding->type.get() != NULL && binding->type->parameters.size() == 1
? "operator_delete__" : "operatordelete__"; } vector<string> parts = qualified_parts(binding); ostringstream out;
for (size_t i = 0; i < parts.size(); ++i) { if (i != 0) out << "__";
out << sanitized_symbol_part(parts[i]); } return out.str(); }
string global_object_symbol(const Binding* binding) { if (binding == NULL) return string();
if (binding->language_linkage == "c") return binding->name; if (binding->is_local_static) {
const Binding* owner = binding->local_static_function_owner; if (owner != NULL) {
string fn = owner->function_specialization_symbol.empty() ?
pa12::internal::abi_binding_symbol(owner, map<string, size_t>()) :
owner->function_specialization_symbol; string leaf = abi_source_name(binding->name);
if (!binding->local_static_discriminator.empty()) leaf += abi_source_name(binding->local_static_discriminator);
return "_ZZ" + fn.substr(2) + "E" + leaf; } }
return pa12::internal::abi_binding_symbol(binding, map<string, size_t>());
} bool binding_has_internal_linkage(const Binding* binding) { if (binding == NULL) return false;
if (binding->is_local_static || binding->is_namespace_static) return true;
for (Scope* scope = binding->owner; scope != NULL; scope = scope->parent)
if (scope->kind == ScopeKind::Namespace && scope->name == "<unnamed>") return true;
return false; } bool is_class_constructor_binding(const Binding* binding) { return binding != NULL &&
binding->owner != NULL && binding->owner->kind == ScopeKind::Class && binding->name == binding->owner->name; }
bool is_class_destructor_binding(const Binding* binding) { return binding != NULL && binding->owner != NULL &&
binding->owner->kind == ScopeKind::Class && !binding->name.empty() && binding->name[0] == '~'; }
TypePtr class_record_for_member(const Binding* binding) { if (binding == NULL || binding->owner == NULL || binding->owner->kind != ScopeKind::Class)
return TypePtr(); return pa11::record_type_for_scope(binding->owner); } Binding* anonymous_storage_member_target(Binding* binding) {
if (binding == NULL || binding->aliased_binding == NULL || binding->target_scope == NULL) return NULL;
map<string, vector<Binding*> >::iterator found = binding->target_scope->members.find(binding->name);
if (found == binding->target_scope->members.end()) return NULL;
for (size_t i = 0; i < found->second.size(); ++i)
if (found->second[i]->kind == BindingKind::Variable && !found->second[i]->is_static_member) return found->second[i];
return NULL; } bool record_is_template_specialization(TypePtr record)
{ record = record.get() != NULL ? pa11::strip_cv(record) : TypePtr(); return record.get() != NULL && record->kind == TypeKind::Record &&
record->is_template_specialization; } bool binding_has_template_specialization_context(const Binding* binding) {
if (binding == NULL) return false; for (Scope* scope = binding->owner; scope != NULL; scope = scope->parent) if (scope->kind == ScopeKind::Class &&
record_is_template_specialization(pa11::record_type_for_scope(scope))) return true; return false; }
string template_static_member_primary_name(const Binding* binding) { TypePtr record = class_record_for_member(binding); record = record.get() != NULL ? pa11::strip_cv(record) : TypePtr();
if (record.get() == NULL || record->kind != TypeKind::Record) return string(); if (!record->template_primary_name.empty()) return record->template_primary_name;
if (record->scope != NULL) return record->scope->name; return record->name; }
void append_template_static_match_type(TypePtr type, vector<string>& out); void append_template_static_match_argument( const pa11::TemplateInstanceArgument& arg, vector<string>& out)
{ if (arg.kind == pa11::TemplateInstanceArgumentKind::Value) { out.push_back("V:" + pa11::describe_type(arg.type) + ":" +
to_string(arg.value) + ":" + arg.value_name); return; } if (arg.kind == pa11::TemplateInstanceArgumentKind::Type)
{ append_template_static_match_type(arg.type, out); return; }
if (arg.kind == pa11::TemplateInstanceArgumentKind::Template) { out.push_back("M:" + arg.template_name); return;
} for (size_t i = 0; i < arg.pack.size(); ++i) append_template_static_match_argument(arg.pack[i], out); }
void append_template_static_match_type(TypePtr type, vector<string>& out) { TypePtr bare = type.get() != NULL ? pa11::strip_cv(type) : TypePtr(); if (bare.get() == NULL)
{ out.push_back("T:"); return; }
if (bare->kind == TypeKind::Record && record_is_template_specialization(bare) && !bare->template_arguments.empty()) {
size_t before = out.size(); for (size_t i = 0; i < bare->template_arguments.size(); ++i) append_template_static_match_argument( bare->template_arguments[i],
out); if (out.size() != before) return; }
out.push_back("T:" + pa11::describe_type(type)); } vector<string> template_static_member_argument_key(const Binding* binding) {
vector<string> out; TypePtr record = class_record_for_member(binding); record = record.get() != NULL ? pa11::strip_cv(record) : TypePtr(); if (record.get() == NULL ||
record->kind != TypeKind::Record || !record_is_template_specialization(record)) return out; for (size_t i = 0; i < record->template_arguments.size(); ++i)
append_template_static_match_argument(record->template_arguments[i], out); return out; }
bool template_static_member_definition_matches(const Binding* use, const Binding* definition) { if (use == NULL ||
definition == NULL || use == definition || use->kind != BindingKind::Variable || definition->kind != BindingKind::Variable ||
!use->is_static_member || !definition->is_static_member || use->name != definition->name || !pa11::same_type(use->type, definition->type) ||
template_static_member_primary_name(use) != template_static_member_primary_name(definition)) return false; if (!definition->is_template_static_member_definition &&
!binding_has_template_specialization_context(definition)) return false; vector<string> use_key = template_static_member_argument_key(use); vector<string> def_key = template_static_member_argument_key(definition);
return !use_key.empty() && use_key == def_key; } string template_display_symbol_text(string text) {
for (size_t i = 0; i < text.size(); ++i) if (text[i] == '<' || text[i] == '>' || text[i] == ',' || text[i] == ' ' || text[i] == '&' || text[i] == '*' || text[i] == ':')
text[i] = '_'; return sanitized_symbol_part(text); } string template_value_symbol_text(uint64_t value)
{ return to_string(value); } string template_value_symbol_text(const pa11::TemplateInstanceArgument& arg)
{ if (!arg.value_name.empty()) return "_" + template_display_symbol_text(arg.value_name); return template_value_symbol_text(arg.value);
} string template_type_symbol_text(TypePtr type); string function_type_parameter_symbol_suffix(TypePtr function_type) {
ostringstream out; out << "_"; for (size_t i = 0; i < function_type->parameters.size(); ++i) {
if (i != 0) out << "_"; out << template_type_symbol_text(function_type->parameters[i]); }
if (function_type->variadic) { if (!function_type->parameters.empty()) out << "_";
out << "ellipsis"; } out << "_"; return out.str();
} string template_type_symbol_text(TypePtr type) { if (type.get() != NULL && type->kind == TypeKind::Cv)
{ string prefix; if ((type->cv & pa11::CV_CONST) != 0) prefix += "const_";
if ((type->cv & pa11::CV_VOLATILE) != 0) prefix += "volatile_"; return prefix + template_type_symbol_text(type->base); }
TypePtr bare = type.get() != NULL ? pa11::strip_cv(type) : TypePtr(); if (bare.get() != NULL && bare->kind == TypeKind::Record && record_is_template_specialization(bare))
return record_lowir_name(bare); if (bare.get() != NULL && (bare->kind == TypeKind::Record || bare->kind == TypeKind::Enum)) return template_display_symbol_text(bare->name);
if (bare.get() != NULL && bare->kind == TypeKind::Function) return template_type_symbol_text(bare->base) + function_type_parameter_symbol_suffix(bare); if (bare.get() != NULL &&
bare->kind == TypeKind::MemberPointer && pa11::strip_cv(bare->base)->kind == TypeKind::Function) { TypePtr function_type = pa11::strip_cv(bare->base);
string out = template_type_symbol_text(function_type->base) + "__" + template_type_symbol_text(bare->member_class) + "_____" + function_type_parameter_symbol_suffix(function_type);
if ((function_type->cv & pa11::CV_CONST) != 0) out += "const";
if ((function_type->cv & pa11::CV_VOLATILE) != 0) out += "volatile";
if ((function_type->cv & (pa11::CV_CONST | pa11::CV_VOLATILE)) == 0) out += "_";
return out; } if (bare.get() != NULL &&
bare->kind == TypeKind::Pointer && pa11::strip_cv(bare->base)->kind == TypeKind::Function) { TypePtr function_type = pa11::strip_cv(bare->base);
return template_type_symbol_text(function_type->base) + "_____" + function_type_parameter_symbol_suffix(function_type); } return template_display_symbol_text(pa11::describe_type(type));
} void append_template_argument_separator(string& out, const string& next); string template_argument_symbol_part( const pa11::TemplateInstanceArgument& arg)
{ if (arg.kind == pa11::TemplateInstanceArgumentKind::Type) return template_type_symbol_text(arg.type); if (arg.kind == pa11::TemplateInstanceArgumentKind::Value)
{ TypePtr bare = arg.type.get() != NULL ? pa11::strip_cv(arg.type) : TypePtr(); if (arg.dependent)
return "dependent_value"; if (bare.get() != NULL && bare->kind == TypeKind::Fundamental && bare->fundamental == FT_BOOL)
return arg.value != 0 ? "true" : "false"; if (bare.get() != NULL && bare->kind == TypeKind::Enum) return "__" + template_type_symbol_text(bare) + "_" + template_value_symbol_text(arg);
return template_value_symbol_text(arg); } if (arg.kind == pa11::TemplateInstanceArgumentKind::Template) return "tmpl_" + template_display_symbol_text(arg.template_name);
string out; for (size_t i = 0; i < arg.pack.size(); ++i) { string part = template_argument_symbol_part(arg.pack[i]);
if (i != 0) append_template_argument_separator(out, part); out += part; }
return out; } void append_template_argument_separator(string& out, const string& next) {
if (next.size() >= 2 && next[0] == '_' && next[1] == '_') { if (out.empty() || out[out.size() - 1] != '_') out += "_";
return; } size_t existing = 0; for (size_t i = out.size(); i > 0 && out[i - 1] == '_'; --i)
++existing; size_t leading = 0; for (size_t i = 0; i < next.size() && next[i] == '_'; ++i) ++leading; existing += leading; size_t wanted = (existing > leading || leading == 1) ? 3 : 2; while (existing < wanted)
{ out += "_"; ++existing; }
} string template_record_symbol_part(TypePtr record) { TypePtr bare = pa11::strip_cv(record);
string primary = !bare->template_primary_name.empty() ? bare->template_primary_name : (bare->scope != NULL ? bare->scope->name : bare->name); string out = template_display_symbol_text(primary);
if (!record_is_template_specialization(bare)) return out; out += "_"; for (size_t i = 0; i < bare->template_arguments.size(); ++i)
{ string arg = template_argument_symbol_part(bare->template_arguments[i]); if (i != 0) append_template_argument_separator(out, arg);
out += arg; } out += "_"; return out;
} string template_abi_builtin_code(EFundamentalType type) { switch (type)
{ case FT_VOID: return "v"; case FT_BOOL: return "b"; case FT_CHAR: return "c";
case FT_SIGNED_CHAR: return "a"; case FT_UNSIGNED_CHAR: return "h"; case FT_SHORT_INT: return "s"; case FT_UNSIGNED_SHORT_INT: return "t";
case FT_INT: return "i"; case FT_UNSIGNED_INT: return "j"; case FT_LONG_INT: return "l"; case FT_UNSIGNED_LONG_INT: return "m";
case FT_LONG_LONG_INT: return "x"; case FT_UNSIGNED_LONG_LONG_INT: return "y"; case FT_INT128: return "n"; case FT_UNSIGNED_INT128: return "o"; case FT_FLOAT: return "f"; case FT_DOUBLE: return "d";
default: return "i"; } } string template_abi_component_for_argument(
const pa11::TemplateInstanceArgument& arg) { if (arg.kind == pa11::TemplateInstanceArgumentKind::Type) return template_abi_component_for_type(arg.type);
if (arg.kind == pa11::TemplateInstanceArgumentKind::Value) { if (!arg.value_name.empty()) return "L" + template_abi_component_for_type(arg.type) +
template_display_symbol_text(arg.value_name) + "E"; return "L" + template_abi_component_for_type(arg.type) + to_string(arg.value) + "E"; }
if (arg.kind == pa11::TemplateInstanceArgumentKind::Template) return to_string(arg.template_name.size()) + arg.template_name; string out; out += "J";
for (size_t i = 0; i < arg.pack.size(); ++i) out += template_abi_component_for_argument(arg.pack[i]); out += "E"; return out;
} string template_abi_component_for_type(TypePtr type) { if (type.get() == NULL)
return ""; if (type->kind == TypeKind::Cv) { string prefix;
if ((type->cv & pa11::CV_CONST) != 0) prefix += "K"; if ((type->cv & pa11::CV_VOLATILE) != 0) prefix += "V";
return prefix + template_abi_component_for_type(type->base); } if (type->kind == TypeKind::LValueReference) return "R" + template_abi_component_for_type(type->base);
if (type->kind == TypeKind::RValueReference) return "O" + template_abi_component_for_type(type->base); if (type->kind == TypeKind::Pointer) return "P" + template_abi_component_for_type(type->base);
if (type->kind == TypeKind::Function) { string out; if ((type->cv & pa11::CV_CONST) != 0) out += "K"; if ((type->cv & pa11::CV_VOLATILE) != 0) out += "V"; out += "F" + template_abi_component_for_type(type->base);
for (size_t i = 0; i < type->parameters.size(); ++i) out += template_abi_component_for_type(type->parameters[i]);
if (type->parameters.empty()) out += "v"; out += "E"; return out; }
if (type->kind == TypeKind::MemberPointer) return "M" + template_abi_component_for_type(type->member_class) + template_abi_component_for_type(type->base);
if (type->kind == TypeKind::Array) return "A" + (type->unknown_bound ? string("") : to_string(type->bound)) + "_" + template_abi_component_for_type(type->base); TypePtr bare = pa11::strip_cv(type);
if (bare->kind == TypeKind::Fundamental) return template_abi_builtin_code(bare->fundamental); if (bare->kind == TypeKind::Record && record_is_template_specialization(bare))
{ string primary = !bare->template_primary_name.empty() ? bare->template_primary_name : (bare->scope != NULL ? bare->scope->name : bare->name);
string out = to_string(primary.size()) + primary + "I"; for (size_t i = 0; i < bare->template_arguments.size(); ++i) out += template_abi_component_for_argument( bare->template_arguments[i]);
out += "E"; return out; } if (bare->kind == TypeKind::Record || bare->kind == TypeKind::Enum)
return to_string(bare->name.size()) + bare->name; return template_display_symbol_text(pa11::describe_type(type)); } bool template_argument_uses_abi_global_symbol(
const pa11::TemplateInstanceArgument& arg); bool type_uses_abi_global_symbol(TypePtr type) { if (type.get() == NULL)
return false; if (type->kind == TypeKind::Cv || type->kind == TypeKind::Pointer) return type_uses_abi_global_symbol(type->base);
if (type->kind == TypeKind::LValueReference || type->kind == TypeKind::RValueReference || type->kind == TypeKind::Array) return true;
TypePtr bare = pa11::strip_cv(type); if (bare->kind == TypeKind::Record && record_is_template_specialization(bare)) return template_record_uses_abi_global_symbol(bare);
return false; } bool template_argument_uses_abi_global_symbol( const pa11::TemplateInstanceArgument& arg)
{ if (arg.kind == pa11::TemplateInstanceArgumentKind::Type) return type_uses_abi_global_symbol(arg.type); if (arg.kind == pa11::TemplateInstanceArgumentKind::Pack)
{ for (size_t i = 0; i < arg.pack.size(); ++i) if (template_argument_uses_abi_global_symbol(arg.pack[i])) return true;
} return false; } bool template_record_uses_abi_global_symbol(TypePtr record)
{ TypePtr bare = pa11::strip_cv(record); if (!record_is_template_specialization(bare)) return false;
for (size_t i = 0; i < bare->template_arguments.size(); ++i) if (template_argument_uses_abi_global_symbol( bare->template_arguments[i])) return true;
return false; } string template_record_global_symbol_part(TypePtr record) {
TypePtr bare = pa11::strip_cv(record); if (template_record_uses_abi_global_symbol(bare)) return "type_" + template_abi_component_for_type(bare); return record_lowir_name(bare);
} string record_lowir_name(TypePtr record) { TypePtr bare = pa11::strip_cv(record);
vector<string> parts; for (Scope* s = bare->scope; s != NULL; s = s->parent) { if ((s->kind == ScopeKind::Namespace || s->kind == ScopeKind::Class) &&
!s->name.empty()) { string part = s->name == "<unnamed>" ? "_GLOBAL__N_1" : s->name;
if (part.compare(0, 8, "__lambda") == 0) { size_t pos = 0; while ((pos = part.find("::", pos)) != string::npos)
{ part.replace(pos, 2, "__"); pos += 2; }
} if (s->kind == ScopeKind::Class) { TypePtr scope_record = pa11::record_type_for_scope(s);
if (record_is_template_specialization(scope_record)) part = template_record_symbol_part(scope_record); } parts.push_back(part);
} } if (parts.empty()) parts.push_back(bare->name);
ostringstream out; for (size_t i = parts.size(); i > 0; --i) { if (i != parts.size())
out << "__"; out << sanitized_symbol_part(parts[i - 1]); } return out.str();
} string rtti_record_symbol_part(TypePtr record) { TypePtr bare = pa11::strip_cv(record);
vector<string> parts; for (Scope* s = bare->scope; s != NULL; s = s->parent) { if ((s->kind == ScopeKind::Namespace || s->kind == ScopeKind::Class) &&
!s->name.empty()) { if (s->kind == ScopeKind::Namespace && s->name == "<unnamed>") continue; string part = s->name;
if (part.compare(0, 8, "__lambda") == 0) { size_t pos = 0; while ((pos = part.find("::", pos)) != string::npos)
{ part.replace(pos, 2, "__"); pos += 2; }
} if (s->kind == ScopeKind::Class) { TypePtr scope_record = pa11::record_type_for_scope(s);
if (record_is_template_specialization(scope_record)) part = template_record_symbol_part(scope_record); } parts.push_back(part);
} } if (parts.empty()) parts.push_back(bare->name);
ostringstream out; for (size_t i = parts.size(); i > 0; --i) { if (i != parts.size())
out << "__"; out << sanitized_symbol_part(parts[i - 1]); } return out.str();
} string vtable_symbol_for_record(TypePtr record) { TypePtr bare = pa11::strip_cv(record);
if (template_record_uses_abi_global_symbol(bare)) return "__vtable_" + template_record_global_symbol_part(bare); return record_lowir_name(record) + "__vtable"; }
string vtable_view_symbol_for_record(TypePtr record, TypePtr view_base, uint64_t offset)
{ return record_lowir_name(record) + "____view__" + record_lowir_name(view_base) + "__" + to_string(offset) + "__vtable"; }
uint64_t vtable_address_point_offset(TypePtr record)
{ TypePtr bare = record.get() != NULL ? pa11::strip_cv(record) : TypePtr(); if (bare.get() == NULL || bare->kind != TypeKind::Record) return 16; vector<TypePtr> vbases = pa11::record_virtual_bases(bare); return vbases.empty() ? 16 : 16 + vbases.size() * 8; }
string vtt_symbol_for_record(TypePtr record)
{ return record_lowir_name(record) + "____vtt"; }
string construction_vtable_symbol_for_record(TypePtr record, TypePtr constructed, uint64_t offset, size_t slice)
{ return record_lowir_name(record) + "____construction__" + record_lowir_name(constructed) + "__" + to_string(offset) + "__s" + to_string(slice) + "__vtable"; }
namespace { bool view_vector_contains(const vector<pair<TypePtr, uint64_t> >& views, TypePtr record, uint64_t offset)
{ TypePtr bare = pa11::strip_cv(record); for (size_t i = 0; i < views.size(); ++i) if (views[i].second == offset && pa11::same_type(pa11::strip_cv(views[i].first), bare)) return true; return false; }
void collect_polymorphic_vtable_views(TypePtr root, TypePtr record, uint64_t base_offset, vector<pair<TypePtr, uint64_t> >& out)
{ TypePtr bare = record.get() != NULL ? pa11::strip_cv(record) : TypePtr(); TypePtr root_bare = root.get() != NULL ? pa11::strip_cv(root) : TypePtr(); if (bare.get() == NULL || bare->kind != TypeKind::Record || root_bare.get() == NULL || root_bare->kind != TypeKind::Record) return; pa11::layout_record_type(bare); vector<TypePtr> bases = pa11::record_direct_bases(bare); for (size_t i = 0; i < bases.size(); ++i) { TypePtr direct = bases[i].get() != NULL ? pa11::strip_cv(bases[i]) : TypePtr(); if (direct.get() == NULL || direct->kind != TypeKind::Record) continue; uint64_t offset = pa11::record_direct_base_is_virtual(bare, i) ? pa11::record_virtual_base_offset(root_bare, direct) : base_offset + pa11::record_direct_base_offset(bare, direct); if (direct->is_polymorphic && offset != 0 && !view_vector_contains(out, direct, offset)) out.push_back(make_pair(direct, offset)); collect_polymorphic_vtable_views(root_bare, direct, offset, out); } }
}  // namespace
vector<pair<TypePtr, uint64_t> > polymorphic_vtable_views(TypePtr record)
{ vector<pair<TypePtr, uint64_t> > out; collect_polymorphic_vtable_views(record, record, 0, out); return out; }
namespace {
bool record_is_virtual_base_of_for_vtt(TypePtr record, TypePtr base)
{
	TypePtr bare = record.get() != NULL ? pa11::strip_cv(record) : TypePtr();
	TypePtr wanted = base.get() != NULL ? pa11::strip_cv(base) : TypePtr();
	if (bare.get() == NULL || bare->kind != TypeKind::Record ||
	    wanted.get() == NULL || wanted->kind != TypeKind::Record)
		return false;
	vector<TypePtr> vbases = pa11::record_virtual_bases(bare);
	for (size_t i = 0; i < vbases.size(); ++i)
		if (pa11::same_type(pa11::strip_cv(vbases[i]), wanted))
			return true;
	return false;
}
}
bool record_uses_virtual_base_vtt(TypePtr record)
{ TypePtr bare = record.get() != NULL ? pa11::strip_cv(record) : TypePtr(); return bare.get() != NULL && bare->kind == TypeKind::Record && !pa11::record_virtual_bases(bare).empty(); }
vector<pair<TypePtr, uint64_t> > vtt_ordered_vtable_views(TypePtr record)
{ vector<pair<TypePtr, uint64_t> > views = polymorphic_vtable_views(record); vector<pair<TypePtr, uint64_t> > ordered; for (size_t i = 0; i < views.size(); ++i) if (!record_is_virtual_base_of_for_vtt(record, views[i].first)) ordered.push_back(views[i]); for (size_t i = 0; i < views.size(); ++i) if (record_is_virtual_base_of_for_vtt(record, views[i].first)) ordered.push_back(views[i]); return ordered; }
size_t construction_vtt_group_size(TypePtr record)
{ TypePtr bare = record.get() != NULL ? pa11::strip_cv(record) : TypePtr(); if (bare.get() == NULL || bare->kind != TypeKind::Record || !bare->is_polymorphic || !record_uses_virtual_base_vtt(bare)) return 0; size_t size = 1; vector<TypePtr> bases = pa11::record_direct_bases(bare); for (size_t i = 0; i < bases.size(); ++i) { if (pa11::record_direct_base_is_virtual(bare, i)) continue; TypePtr direct = bases[i].get() != NULL ? pa11::strip_cv(bases[i]) : TypePtr(); if (direct.get() != NULL && direct->kind == TypeKind::Record && direct->is_polymorphic && record_uses_virtual_base_vtt(direct)) size += construction_vtt_group_size(direct); } size += vtt_ordered_vtable_views(bare).size(); return size; }
size_t construction_vtt_slot_for_direct_base(TypePtr record, TypePtr direct_base)
{ TypePtr bare = record.get() != NULL ? pa11::strip_cv(record) : TypePtr(); TypePtr wanted = direct_base.get() != NULL ? pa11::strip_cv(direct_base) : TypePtr(); if (bare.get() == NULL || bare->kind != TypeKind::Record || wanted.get() == NULL || wanted->kind != TypeKind::Record) return static_cast<size_t>(-1); size_t slot = 1; vector<TypePtr> bases = pa11::record_direct_bases(bare); for (size_t i = 0; i < bases.size(); ++i) { if (pa11::record_direct_base_is_virtual(bare, i)) continue; TypePtr direct = bases[i].get() != NULL ? pa11::strip_cv(bases[i]) : TypePtr(); if (direct.get() == NULL || direct->kind != TypeKind::Record || !direct->is_polymorphic || !record_uses_virtual_base_vtt(direct)) continue; if (pa11::same_type(direct, wanted)) return slot; slot += construction_vtt_group_size(direct); } return static_cast<size_t>(-1); }
size_t construction_vtt_slot_for_view(TypePtr record, TypePtr view_base, uint64_t offset)
{ TypePtr bare = record.get() != NULL ? pa11::strip_cv(record) : TypePtr(); TypePtr wanted = view_base.get() != NULL ? pa11::strip_cv(view_base) : TypePtr(); if (bare.get() == NULL || bare->kind != TypeKind::Record || wanted.get() == NULL || wanted->kind != TypeKind::Record) return static_cast<size_t>(-1); size_t slot = 1; vector<TypePtr> bases = pa11::record_direct_bases(bare); for (size_t i = 0; i < bases.size(); ++i) { if (pa11::record_direct_base_is_virtual(bare, i)) continue; TypePtr direct = bases[i].get() != NULL ? pa11::strip_cv(bases[i]) : TypePtr(); if (direct.get() != NULL && direct->kind == TypeKind::Record && direct->is_polymorphic && record_uses_virtual_base_vtt(direct)) slot += construction_vtt_group_size(direct); } vector<pair<TypePtr, uint64_t> > views = vtt_ordered_vtable_views(bare); for (size_t i = 0; i < views.size(); ++i) if (views[i].second == offset && pa11::same_type(pa11::strip_cv(views[i].first), wanted)) return slot + i; return static_cast<size_t>(-1); }
TypePtr hidden_virtual_base_context_record(TypePtr type)
{ TypePtr bare = type.get() != NULL ? pa11::strip_cv(type) : TypePtr(); if (bare.get() == NULL) return TypePtr(); if (bare->kind == TypeKind::LValueReference || bare->kind == TypeKind::RValueReference) bare = pa11::strip_cv(bare->base); if (bare.get() != NULL && bare->kind == TypeKind::Pointer) bare = pa11::strip_cv(bare->base); if (bare.get() != NULL && bare->kind == TypeKind::Record) return bare; return TypePtr(); }
vector<TypePtr> hidden_virtual_bases_for_record(TypePtr record)
{ TypePtr bare = record.get() != NULL ? pa11::strip_cv(record) : TypePtr(); if (bare.get() == NULL || bare->kind != TypeKind::Record || !bare->complete) return vector<TypePtr>(); return pa11::record_virtual_bases(bare); }
vector<TypePtr> hidden_virtual_bases_for_parameter(TypePtr type)
{
	TypePtr bare = type.get() != NULL ? pa11::strip_cv(type) : TypePtr();
	if (bare.get() == NULL)
		return vector<TypePtr>();
	bool pointer_parameter = false;
	if (bare->kind == TypeKind::LValueReference ||
	    bare->kind == TypeKind::RValueReference)
	{
		TypePtr ref_base = pa11::strip_cv(bare->base);
		pointer_parameter = ref_base.get() != NULL &&
		                    ref_base->kind == TypeKind::Pointer;
	}
	else
		pointer_parameter = bare->kind == TypeKind::Pointer;
	TypePtr record = hidden_virtual_base_context_record(type);
	if (record.get() == NULL)
		return vector<TypePtr>();
	if (!record->complete)
		return vector<TypePtr>();
	if (!pointer_parameter)
		return hidden_virtual_bases_for_record(record);
	TypePtr top = bare;
	if (top->kind == TypeKind::LValueReference ||
	    top->kind == TypeKind::RValueReference)
		top = pa11::strip_cv(top->base);
	if (top.get() == NULL || top->kind != TypeKind::Pointer)
		return hidden_virtual_bases_for_record(record);
	vector<TypePtr> out;
	vector<TypePtr> bases = pa11::record_direct_bases(record);
	for (size_t i = 0; i < bases.size(); ++i)
		if (pa11::record_direct_base_is_virtual(record, i))
		{
			TypePtr base = bases[i].get() != NULL
				? pa11::strip_cv(bases[i]) : TypePtr();
			if (base.get() != NULL && base->kind == TypeKind::Record)
				out.push_back(base);
		}
	return out.empty() ? hidden_virtual_bases_for_record(record) : out;
}
string rtti_symbol_for_record(TypePtr record) { TypePtr bare = pa11::strip_cv(record); if (template_record_uses_abi_global_symbol(bare))
return "__rtti_" + template_record_global_symbol_part(bare); return "__rtti_" + bare->tag + "_" + rtti_record_symbol_part(bare); } string function_symbol_key(const Binding* binding, const string& base)
{ string specialization = binding->function_specialization_symbol.empty() ? string()
: binding->function_specialization_symbol + " "; return base + " " + specialization + string(binding->is_static_member ? "static " : "nonstatic ") + "refqual=" + to_string(binding->ref_qualifier) + " " +
pa11::describe_type(binding->type); } bool function_template_specialization_binding_for_symbol( const Binding* binding)
{ return binding != NULL && (!binding->function_specialization_symbol.empty() || (binding->aliased_binding != NULL &&
!binding->aliased_binding->function_specialization_symbol.empty())); } bool member_pointer_adapter_overload_for_symbol(const Binding* current, const Binding* candidate) {
if (current == NULL || candidate == NULL || current == candidate ||
current->type.get() == NULL || candidate->type.get() == NULL ||
current->type->kind != TypeKind::Function || candidate->type->kind != TypeKind::Function ||
current->type->parameters.size() != candidate->type->parameters.size()) return false;
size_t first = current->owner != NULL && current->owner->kind == ScopeKind::Class && !current->is_static_member ? 1 : 0;
for (size_t i = first; i < current->type->parameters.size(); ++i) {
TypePtr cur = pa11::strip_cv(object_type(current->type->parameters[i]));
TypePtr cand = pa11::strip_cv(object_type(candidate->type->parameters[i]));
if (cur.get() != NULL && cand.get() != NULL && cur->kind == TypeKind::MemberPointer &&
cand->kind == TypeKind::Record && !is_reference(candidate->type->parameters[i])) return true; }
return false; } string template_family_name_for_symbol(TypePtr record) {
record = record.get() != NULL ? pa11::strip_cv(record) : TypePtr(); if (record.get() == NULL || record->kind != TypeKind::Record) return ""; return record->template_primary_name.empty()
? record->name : record->template_primary_name; } bool template_argument_pattern_matches( const pa11::TemplateInstanceArgument& pattern,
const pa11::TemplateInstanceArgument& actual); bool template_parameter_pattern_matches(TypePtr pattern, TypePtr actual) { pattern = pattern.get() != NULL ? pa11::strip_cv(pattern) : TypePtr();
actual = actual.get() != NULL ? pa11::strip_cv(actual) : TypePtr(); if (pattern.get() == NULL || actual.get() == NULL) return false; if (pattern->kind == TypeKind::TemplateParameter ||
pattern->kind == TypeKind::TemplateTemplateParameter || pattern->is_dependent_typename) return true; if (pa11::same_type(pattern, actual))
return true; if (pattern->kind != actual->kind) return false; if (pattern->kind == TypeKind::Pointer ||
pattern->kind == TypeKind::LValueReference || pattern->kind == TypeKind::RValueReference || pattern->kind == TypeKind::Array) return template_parameter_pattern_matches(pattern->base,
actual->base); if (pattern->kind == TypeKind::MemberPointer) return template_parameter_pattern_matches(pattern->member_class, actual->member_class) &&
template_parameter_pattern_matches(pattern->base, actual->base); if (pattern->kind == TypeKind::Record && pattern->is_template_specialization &&
actual->is_template_specialization && template_family_name_for_symbol(pattern) == template_family_name_for_symbol(actual) && pattern->template_arguments.size() ==
actual->template_arguments.size()) { for (size_t i = 0; i < pattern->template_arguments.size(); ++i) if (!template_argument_pattern_matches(
pattern->template_arguments[i], actual->template_arguments[i])) return false; return true;
} return false; } bool template_argument_pattern_matches(
const pa11::TemplateInstanceArgument& pattern, const pa11::TemplateInstanceArgument& actual) { if (pattern.dependent)
return true; if (pattern.kind != actual.kind) return false; if (pattern.kind == pa11::TemplateInstanceArgumentKind::Type)
return template_parameter_pattern_matches(pattern.type, actual.type); if (pattern.kind == pa11::TemplateInstanceArgumentKind::Template) return pattern.template_name.empty() || pattern.template_name == actual.template_name;
if (pattern.kind == pa11::TemplateInstanceArgumentKind::Pack) { if (pattern.pack.size() != actual.pack.size()) return false;
for (size_t i = 0; i < pattern.pack.size(); ++i) if (!template_argument_pattern_matches(pattern.pack[i], actual.pack[i])) return false;
return true; } return pattern.value_name.empty() || pattern.value_name == actual.value_name; }
int template_parameter_specificity(TypePtr pattern) { pattern = pattern.get() != NULL ? pa11::strip_cv(pattern) : TypePtr(); if (pattern.get() == NULL ||
pattern->kind == TypeKind::TemplateParameter || pattern->kind == TypeKind::TemplateTemplateParameter || pattern->is_dependent_typename) return 0;
if (pattern->kind == TypeKind::Pointer || pattern->kind == TypeKind::LValueReference || pattern->kind == TypeKind::RValueReference || pattern->kind == TypeKind::Array)
return 1 + template_parameter_specificity(pattern->base); if (pattern->kind == TypeKind::MemberPointer) return 2 + template_parameter_specificity(pattern->member_class) + template_parameter_specificity(pattern->base);
if (pattern->kind == TypeKind::Record && pattern->is_template_specialization) return 20 + static_cast<int>(pattern->template_arguments.size()); if (pattern->kind == TypeKind::Record)
return 10; return 5; } int constructor_template_placeholder_match_score(const Binding* placeholder,
const Binding* binding) { if (placeholder == NULL || binding == NULL ||
placeholder->kind != BindingKind::Function || binding->kind != BindingKind::Function || placeholder->owner != binding->owner || placeholder->name != binding->name ||
placeholder->type.get() == NULL || binding->type.get() == NULL || placeholder->type->kind != TypeKind::Function || binding->type->kind != TypeKind::Function ||
placeholder->type->parameters.size() != binding->type->parameters.size()) return -1; int score = 0; for (size_t i = 1; i < placeholder->type->parameters.size(); ++i)
{ TypePtr pattern = object_type(placeholder->type->parameters[i]); TypePtr actual = object_type(binding->type->parameters[i]); if (!template_parameter_pattern_matches(pattern, actual))
return -1; score += template_parameter_specificity(pattern); } return score;
} bool type_contains_template_symbol_pattern(TypePtr type) {
type = type.get() != NULL ? pa11::strip_cv(type) : TypePtr(); if (type.get() == NULL) return false;
if (type->kind == TypeKind::TemplateParameter || type->kind == TypeKind::TemplateTemplateParameter || type->is_dependent_typename) return true;
if (type->kind == TypeKind::Pointer || type->kind == TypeKind::LValueReference || type->kind == TypeKind::RValueReference || type->kind == TypeKind::Array)
return type_contains_template_symbol_pattern(type->base); if (type->kind == TypeKind::MemberPointer)
return type_contains_template_symbol_pattern(type->member_class) || type_contains_template_symbol_pattern(type->base);
if (type->kind == TypeKind::Function) { if (type_contains_template_symbol_pattern(type->base)) return true;
for (size_t i = 0; i < type->parameters.size(); ++i) if (type_contains_template_symbol_pattern(type->parameters[i])) return true; return false; }
if (type->kind == TypeKind::Record && type->is_template_specialization) for (size_t i = 0; i < type->template_arguments.size(); ++i) {
const pa11::TemplateInstanceArgument& arg = type->template_arguments[i]; if (arg.kind == pa11::TemplateInstanceArgumentKind::Type &&
type_contains_template_symbol_pattern(arg.type)) return true; if (arg.kind == pa11::TemplateInstanceArgumentKind::Pack) for (size_t j = 0; j < arg.pack.size(); ++j)
if (arg.pack[j].kind == pa11::TemplateInstanceArgumentKind::Type && type_contains_template_symbol_pattern(arg.pack[j].type)) return true; }
return false;
} bool constructor_template_symbol_placeholder_candidate(const Binding* binding, const string& base) {
if (binding == NULL || binding->kind != BindingKind::Function || !is_class_constructor_binding(binding) || source_symbol_base(binding) != base ||
function_template_specialization_binding_for_symbol(binding) || binding->is_generated_default_constructor || binding->is_generated_copy_move_constructor ||
binding->type.get() == NULL || binding->type->kind != TypeKind::Function)
return false; for (size_t i = 1; i < binding->type->parameters.size(); ++i) if (type_contains_template_symbol_pattern(object_type(binding->type->parameters[i]))) return true;
return false;
} size_t constructor_template_symbol_placeholder_count(const vector<Binding*>& overloads, const string& base) {
size_t count = 0; for (size_t i = 0; i < overloads.size(); ++i) if (constructor_template_symbol_placeholder_candidate(overloads[i], base)) ++count;
return count;
} string ProgramLowerer::symbol_for(const Binding* binding) { if (binding != NULL &&
binding->kind == BindingKind::Function && binding->aliased_binding != NULL && binding->aliased_binding->is_inline_definition) binding = binding->aliased_binding;
map<const Binding*, string>::const_iterator found = symbols.find(binding); if (found != symbols.end()) return found->second; string base = source_symbol_base(binding);
if (binding->kind == BindingKind::Function) { string key = function_symbol_key(binding, base); map<string, string>::const_iterator fit = function_symbols.find(key);
if (fit != function_symbols.end()) { symbols[binding] = fit->second; return fit->second;
} if (function_template_specialization_binding_for_symbol(binding) && used_symbols[base] == 0 && binding->owner != NULL) {
map<string, vector<Binding*> >::const_iterator overloads = binding->owner->members.find(binding->name);
if (overloads != binding->owner->members.end()) for (size_t i = 0; i < overloads->second.size(); ++i) { Binding* candidate = overloads->second[i];
if (candidate == binding || candidate->kind != BindingKind::Function || source_symbol_base(candidate) != base ||
!function_template_specialization_binding_for_symbol(candidate) || !member_pointer_adapter_overload_for_symbol(binding, candidate)) continue;
string candidate_key = function_symbol_key(candidate, base);
if (function_symbols.find(candidate_key) == function_symbols.end()) {
function_symbols[candidate_key] = base; symbols[candidate] = base; used_symbols[base] = 1; }
break; }
} if (binding->owner != NULL && binding->owner->kind == ScopeKind::Class && binding->name == binding->owner->name &&
function_template_specialization_binding_for_symbol(binding)) { TypePtr symbol_owner_record = pa11::record_type_for_scope(binding->owner);
symbol_owner_record = symbol_owner_record.get() != NULL ? pa11::strip_cv(symbol_owner_record) : TypePtr(); if (symbol_owner_record.get() != NULL &&
symbol_owner_record->kind == TypeKind::Record) {
map<string, vector<Binding*> >::const_iterator overloads = binding->owner->members.find(binding->name); Binding* matched_placeholder = NULL; int matched_score = -1;
bool specialized_owner = symbol_owner_record->is_template_specialization; bool allow_placeholder_match = !specialized_owner || (overloads != binding->owner->members.end() &&
constructor_template_symbol_placeholder_count(overloads->second, base) > 1);
if (allow_placeholder_match && overloads != binding->owner->members.end()) for (size_t i = 0; i < overloads->second.size(); ++i) { Binding* prior = overloads->second[i];
if (prior == binding || prior->aliased_binding == binding || binding->aliased_binding == prior) break;
if (specialized_owner && !constructor_template_symbol_placeholder_candidate(prior, base)) continue;
if (source_symbol_base(prior) != base) continue; int score = constructor_template_placeholder_match_score(
prior, binding); if (score > matched_score) { matched_score = score;
matched_placeholder = prior; } } if (matched_placeholder != NULL)
{ for (size_t i = 0; i < overloads->second.size(); ++i) { Binding* prior = overloads->second[i];
if (prior->kind != BindingKind::Function || source_symbol_base(prior) != base) continue; string prior_key = function_symbol_key(prior, base);
map<string, string>::const_iterator pit = function_symbols.find(prior_key); if (pit == function_symbols.end()) {
int& prior_count = used_symbols[base]; ++prior_count; string prior_name = base; if (prior_count > 1)
prior_name += "__ov" + to_string(prior_count); function_symbols[prior_key] = prior_name; pit = function_symbols.find(prior_key);
} if (prior == matched_placeholder) { symbols[binding] = pit->second;
function_symbols[key] = pit->second; return pit->second; } }
} } } if (binding->owner != NULL && binding->owner->kind == ScopeKind::Namespace && !base.empty() && base[0] != '<' && function_template_specialization_binding_for_symbol(binding)) { map<string, vector<Binding*> >::const_iterator overloads = binding->owner->members.find(binding->name);
if (overloads != binding->owner->members.end()) for (size_t i = 0; i < overloads->second.size(); ++i) { Binding* prior = overloads->second[i];
if (prior->kind != BindingKind::Function || source_symbol_base(prior) != base || function_template_specialization_binding_for_symbol(prior) || type_contains_template_symbol_pattern(prior->type)) continue; string prior_key = function_symbol_key(prior, base);
if (function_symbols.find(prior_key) == function_symbols.end()) { int& prior_count = used_symbols[base]; ++prior_count; string prior_name = base; if (prior_count > 1)
prior_name += "__ov" + to_string(prior_count); function_symbols[prior_key] = prior_name; symbols[prior] = prior_name; } } }
if (binding->owner != NULL && binding->owner->kind == ScopeKind::Namespace && !base.empty() && base[0] != '<' && !function_template_specialization_binding_for_symbol(binding)) { map<string, vector<Binding*> >::const_iterator overloads = binding->owner->members.find(binding->name);
if (overloads != binding->owner->members.end()) { for (size_t i = 0; i < overloads->second.size(); ++i) { Binding* prior = overloads->second[i];
if (prior->kind != BindingKind::Function || source_symbol_base(prior) != base || function_template_specialization_binding_for_symbol(prior) || type_contains_template_symbol_pattern(prior->type)) continue; string prior_key = function_symbol_key(prior, base);
if (function_symbols.find(prior_key) == function_symbols.end()) { int& prior_count = used_symbols[base]; ++prior_count; string prior_name = base; if (prior_count > 1)
prior_name += "__ov" + to_string(prior_count); function_symbols[prior_key] = prior_name; symbols[prior] = prior_name; } if (prior == binding || prior->aliased_binding == binding || binding->aliased_binding == prior) break; }
map<string, string>::const_iterator reserved = function_symbols.find(key); if (reserved != function_symbols.end()) { symbols[binding] = reserved->second; return reserved->second; } } } if (binding->is_generated_copy_move_constructor && used_symbols[base] == 0 && binding->owner != NULL &&
binding->owner->kind == ScopeKind::Class && binding->name == binding->owner->name) { TypePtr owner_record =
pa11::record_type_for_scope(binding->owner); owner_record = owner_record.get() != NULL ? pa11::strip_cv(owner_record) : TypePtr(); if (owner_record.get() != NULL &&
owner_record->kind == TypeKind::Record && record_declares_or_inherits_virtual_base(owner_record)) { map<string, vector<Binding*> >::const_iterator overloads = binding->owner->members.find(binding->name);
if (overloads != binding->owner->members.end()) for (size_t i = 0; i < overloads->second.size(); ++i) { Binding* prior = overloads->second[i];
if (prior->kind != BindingKind::Function || prior == binding || source_symbol_base(prior) != base || !prior->is_generated_default_constructor || prior->type.get() == NULL || prior->type->kind != TypeKind::Function || prior->type->parameters.size() != 1) continue; string prior_key = function_symbol_key(prior, base);
if (function_symbols.find(prior_key) == function_symbols.end()) { int& prior_count = used_symbols[base]; ++prior_count; string prior_name = base; if (prior_count > 1)
prior_name += "__ov" + to_string(prior_count); function_symbols[prior_key] = prior_name; symbols[prior] = prior_name; } break; } } } if (binding->owner != NULL &&
binding->owner->kind == ScopeKind::Class && binding->name == binding->owner->name) { TypePtr owner_record =
pa11::record_type_for_scope(binding->owner); owner_record = owner_record.get() != NULL ? pa11::strip_cv(owner_record) : TypePtr(); if (owner_record.get() != NULL &&
owner_record->kind == TypeKind::Record) { map<string, vector<Binding*> >::const_iterator overloads = binding->owner->members.find(binding->name);
if (overloads != binding->owner->members.end()) for (size_t i = 0; i < overloads->second.size(); ++i) { Binding* prior = overloads->second[i];
if (prior == binding || prior->aliased_binding == binding || binding->aliased_binding == prior) break;
if (prior->kind != BindingKind::Function || source_symbol_base(prior) != base) continue; string prior_key =
function_symbol_key(prior, base); if (function_symbols.find(prior_key) != function_symbols.end()) continue;
int& prior_count = used_symbols[base]; ++prior_count; string prior_name = base; if (prior_count > 1)
prior_name += "__ov" + to_string(prior_count); function_symbols[prior_key] = prior_name; }
} } if (binding->is_generated_copy_move_assignment && binding->type.get() != NULL &&
binding->type->kind == TypeKind::Function && binding->type->parameters.size() == 2 && binding->type->parameters[1]->kind == TypeKind::RValueReference) {
TypePtr record = pa11::strip_cv(binding->type->parameters[1]->base); vector<TypePtr> copy_params; copy_params.push_back(binding->type->parameters[0]); copy_params.push_back(
pa11::make_lvalue_reference( pa11::make_cv(record, pa11::CV_CONST))); TypePtr copy_type = pa11::make_function(binding->type->base, copy_params,
false); string copy_key = base + " " + string(binding->is_static_member ? "static " : "nonstatic ") +
"refqual=" + to_string(binding->ref_qualifier) + " " + pa11::describe_type(copy_type); if (function_symbols.find(copy_key) == function_symbols.end())
{ function_symbols[copy_key] = base; if (used_symbols[base] < 1) used_symbols[base] = 1;
} } } if (binding->kind == BindingKind::Function &&
binding->reserve_primary_function_symbol && !binding->function_specialization_symbol.empty() && used_symbols[base] == 0) used_symbols[base] = 1;
int& count = used_symbols[base]; ++count; string name = base; if (count > 1)
name += "__ov" + to_string(count); symbols[binding] = name; if (binding->kind == BindingKind::Function) {
string key = function_symbol_key(binding, base); function_symbols[key] = name; } return name;
} string ProgramLowerer::constructor_symbol_for(const Binding* binding, bool base_entry) {
string name = symbol_for(binding); if (base_entry && binding != NULL && binding->owner != NULL &&
binding->owner->kind == ScopeKind::Class && binding->name == binding->owner->name) { demanded_constructor_base_entries.insert(binding);
name += "__base_entry"; } return name; }
string ProgramLowerer::destructor_symbol_for(const Binding* binding, bool base_entry) { string name = symbol_for(binding);
if (base_entry && is_class_destructor_binding(binding)) { demanded_destructor_base_entries.insert(binding);
name += "__base_entry"; } return name; }
vector<uint32_t> decode_string_literal(const string& text) { StringLiteralInfo info; if (!AnalyzeStringLiteral(text, info) || !info.ud_suffix.empty())
throw runtime_error("invalid string literal"); size_t width = 1; if (info.type == FT_CHAR16_T) width = 2;
else if (info.type == FT_WCHAR_T || info.type == FT_CHAR32_T) width = 4; if (width == 0 || info.bytes.size() % width != 0) throw runtime_error("invalid string literal");
vector<uint32_t> code_points; for (size_t i = 0; i < info.bytes.size(); i += width) { uint32_t value = 0;
for (size_t j = 0; j < width; ++j) value |= static_cast<uint32_t>(info.bytes[i + j]) << (8 * j); code_points.push_back(value); }
return code_points; } string string_literal_lowir_type(const string& text) {
StringLiteralInfo info; if (!AnalyzeStringLiteral(text, info) || !info.ud_suffix.empty()) throw runtime_error("invalid string literal"); switch (info.type)
{ case FT_CHAR16_T: return "i16"; case FT_WCHAR_T:
case FT_CHAR32_T: return "i32"; default: return "i8";
} } string ProgramLowerer::string_symbol(const string& token_text) {
map<string, string>::const_iterator found = string_literals.find(token_text); if (found != string_literals.end()) return found->second; string name = "__strlit__" + to_string(string_literals.size() + 1);
string_literals[token_text] = name; string_literal_types[name] = string_literal_lowir_type(token_text); string_defs.push_back(make_pair(name, decode_string_literal(token_text))); return name;
}
}  // namespace internal
}  // namespace pa14
