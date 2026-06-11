#include "pa12_expr_semantics_support.h"
#include <algorithm>
#include <functional>
#include <stdexcept>
using namespace std; namespace pa12 { namespace internal { bool is_pointer(TypePtr type)
{ return pa11::strip_cv(type)->kind == pa11::TypeKind::Pointer; } namespace {
bool same_template_specialization_type(TypePtr left, TypePtr right); void append_normalized_specialization_arguments( vector<pa11::TemplateInstanceArgument>& out, const vector<pa11::TemplateInstanceArgument>& arguments)
{ for (size_t i = 0; i < arguments.size(); ++i) { if (arguments[i].kind == pa11::TemplateInstanceArgumentKind::Pack)
{ append_normalized_specialization_arguments(out, arguments[i].pack); continue; }
out.push_back(arguments[i]); } } bool same_template_specialization_arguments(
const vector<pa11::TemplateInstanceArgument>& left, const vector<pa11::TemplateInstanceArgument>& right); bool same_template_specialization_argument( const pa11::TemplateInstanceArgument& left,
const pa11::TemplateInstanceArgument& right) { if (left.kind != right.kind) return false;
if (left.kind == pa11::TemplateInstanceArgumentKind::Type) return same_template_specialization_type(left.type, right.type); if (left.kind == pa11::TemplateInstanceArgumentKind::Value) return left.dependent == right.dependent &&
left.value_negated == right.value_negated && left.value == right.value && left.value_name == right.value_name && left.value_owner_template_name ==
right.value_owner_template_name && left.value_member_name == right.value_member_name && same_template_specialization_type(left.type, right.type) && same_template_specialization_arguments(
left.value_owner_template_arguments, right.value_owner_template_arguments); if (left.kind == pa11::TemplateInstanceArgumentKind::Template) return left.template_name == right.template_name &&
left.dependent == right.dependent; if (left.pack.size() != right.pack.size()) return false; for (size_t i = 0; i < left.pack.size(); ++i)
if (!same_template_specialization_argument(left.pack[i], right.pack[i])) return false; return true; }
bool same_template_specialization_arguments( const vector<pa11::TemplateInstanceArgument>& left, const vector<pa11::TemplateInstanceArgument>& right) {
vector<pa11::TemplateInstanceArgument> flat_left; vector<pa11::TemplateInstanceArgument> flat_right; append_normalized_specialization_arguments(flat_left, left); append_normalized_specialization_arguments(flat_right, right);
if (flat_left.size() != flat_right.size()) return false; for (size_t i = 0; i < flat_left.size(); ++i) if (!same_template_specialization_argument(flat_left[i], flat_right[i]))
return false; return true; } bool same_template_specialization_type(TypePtr left, TypePtr right)
{ if (left.get() == NULL || right.get() == NULL) return left.get() == right.get(); if (pa11::same_type(left, right))
return true; TypePtr l = pa11::strip_cv(left); TypePtr r = pa11::strip_cv(right); return l->kind == pa11::TypeKind::Record &&
r->kind == pa11::TypeKind::Record && l->is_template_specialization && r->is_template_specialization && !l->template_primary_name.empty() &&
l->template_primary_name == r->template_primary_name && same_template_specialization_arguments(l->template_arguments, r->template_arguments); }
}  // namespace
bool Parser::is_std_initializer_list_type(TypePtr type,
                                          TypePtr* element) const
{
	if (type.get() == NULL)
		return false;
	TypePtr bare = pa11::strip_cv(type);
	if (bare->kind != pa11::TypeKind::Record ||
	    !bare->is_template_specialization ||
	    bare->template_primary_name != "initializer_list")
		return false;
	Scope* owner = bare->scope != NULL ? bare->scope->parent : NULL;
	if (owner == NULL || owner->kind != ScopeKind::Namespace ||
	    owner->name != "std")
		return false;
	if (bare->template_arguments.size() != 1 ||
	    bare->template_arguments[0].kind !=
		    pa11::TemplateInstanceArgumentKind::Type)
		return false;
	if (element != NULL)
		*element = bare->template_arguments[0].type;
	return true;
}

void Parser::normalize_std_initializer_list_type(TypePtr type)
{
	TypePtr element;
	if (!is_std_initializer_list_type(type, &element))
		return;
	TypePtr bare = pa11::strip_cv(type);
	if (bare->scope == NULL)
		return;
	bool has_begin = false;
	bool has_size = false;
	for (size_t i = 0; i < bare->scope->binding_order.size(); ++i)
	{
		Binding* binding = bare->scope->binding_order[i];
		if (binding->kind != BindingKind::Variable ||
		    binding->is_static_member)
			continue;
		if (binding->name == "__begin_" || binding->name == "first")
			has_begin = true;
		if (binding->name == "__size_" || binding->name == "count")
			has_size = true;
	}
	if (!has_begin)
		add_value(bare->scope,
		          BindingKind::Variable,
		          "__begin_",
		          pa11::make_pointer(pa11::make_cv(element,
		                                           pa11::CV_CONST)));
	if (!has_size)
		add_value(bare->scope,
		          BindingKind::Variable,
		          "__size_",
		          pa11::make_fundamental(FT_UNSIGNED_LONG_INT));
	bare->complete = true;
	bare->layout_valid = false;
}

TypePtr Parser::make_std_initializer_list_type(TypePtr element)
{
	Binding* std_binding =
		pa11::lookup_qualified(global_scope(), "std", pa11::LOOKUP_NAMESPACE);
	Scope* std_scope =
		std_binding != NULL ? std_binding->target_scope : NULL;
	TemplateDeclaration* templ =
		std_scope != NULL ? find_class_template(std_scope, "initializer_list")
		                  : NULL;
	if (templ == NULL)
		throw runtime_error("std::initializer_list is not declared");
	TemplateArgument arg;
	arg.kind = TemplateArgumentKind::Type;
	arg.type = element;
	vector<TemplateArgument> args;
	args.push_back(arg);
	TypePtr list_type = instantiate_class_template(templ, args);
	normalize_std_initializer_list_type(list_type);
	return list_type;
}

Expr Parser::make_initializer_list_expr(const Expr& init, TypePtr target)
{
	if (!init.braced_init_list)
		throw runtime_error("initializer_list requires braced-init-list");
	TypePtr element;
	if (target.get() != NULL)
	{
		if (!is_std_initializer_list_type(target, &element))
			throw runtime_error("target is not std::initializer_list");
		normalize_std_initializer_list_type(target);
	}
	else
	{
		if (init.node.children.empty())
			throw runtime_error("empty auto initializer_list");
		const Node& first = init.node.children[0];
		element = lvalue_to_rvalue_type(first.type);
		target = make_std_initializer_list_type(element);
	}
	Expr out;
	out.valid = true;
	out.type = target;
	out.category = ValueCategory::PRValue;
	out.braced_init_list = true;
	out.node = Node("braced-init-list");
	out.node.type = target;
	out.node.category = out.category;
	out.node.token_text = "initializer-list";
	for (size_t i = 0; i < init.node.children.size(); ++i)
	{
		Expr child;
		child.valid = true;
		child.node = init.node.children[i];
		child.type = child.node.type;
		child.category = child.node.category;
		child.binding = child.node.binding;
		child.has_constant_value = child.node.has_constant_value;
		child.constant_value = child.node.constant_value;
		child.braced_init_list =
			child.node.line.compare(0, 16, "braced-init-list") == 0;
		Conversion conv = convert_to(child, element);
		if (!conv.viable)
			throw runtime_error("invalid initializer_list element");
		add_child(out.node, conv.expr.node);
	}
	annotate_expr_node(out);
	return out;
}
bool template_declaration_has_body(const vector<Token>& tokens, const TemplateDeclaration* declaration) { if (declaration == NULL || !declaration->has_definition)
return false; for (size_t i = declaration->decl_begin; i < declaration->decl_end && i < tokens.size(); ++i)
if (tokens[i].kind == posttoken::TokenKind::Simple && tokens[i].type == OP_LBRACE) return true; return false;
} bool same_template_specialization_record(TypePtr left, TypePtr right) { if (left.get() == NULL || right.get() == NULL)
return left.get() == right.get(); TypePtr l = pa11::strip_cv(left); TypePtr r = pa11::strip_cv(right); if (l->kind != pa11::TypeKind::Record ||
r->kind != pa11::TypeKind::Record || !l->is_template_specialization || !r->is_template_specialization) return false;
return same_template_specialization_type(l, r) || l->name == r->name; } bool record_has_base_type(TypePtr source, TypePtr target) {
if (source.get() == NULL || target.get() == NULL) return false; TypePtr wanted = pa11::strip_cv(target); TypePtr root = pa11::strip_cv(source); vector<TypePtr> pending = pa11::record_direct_bases(root); vector<TypePtr> seen;
while (!pending.empty()) { TypePtr cur = pending.back().get() != NULL ? pa11::strip_cv(pending.back()) : TypePtr(); pending.pop_back(); if (cur.get() == NULL || cur->kind != pa11::TypeKind::Record) continue; bool already = false; for (size_t i = 0; i < seen.size(); ++i) if (pa11::same_type(seen[i], cur)) already = true; if (already) continue; seen.push_back(cur); if (pa11::same_type(cur, wanted)) return true; vector<TypePtr> bases = pa11::record_direct_bases(cur); pending.insert(pending.end(), bases.begin(), bases.end()); }
return false; } bool same_template_specialization_family(TypePtr left, TypePtr right) {
TypePtr l = pa11::strip_cv(left); TypePtr r = pa11::strip_cv(right); return l->kind == pa11::TypeKind::Record && r->kind == pa11::TypeKind::Record &&
l->is_template_specialization && r->is_template_specialization && (l->name == r->name || (!l->template_primary_name.empty() &&
l->template_primary_name == r->template_primary_name)); } bool record_conversion_active(const vector<TypePtr>& active, TypePtr record) {
for (size_t i = 0; i < active.size(); ++i) if (pa11::same_type(pa11::strip_cv(active[i]), pa11::strip_cv(record)) || same_template_specialization_record(active[i], record))
return true; return false; } unsigned reference_cv_flags(TypePtr type)
{ return type.get() != NULL && type->kind == pa11::TypeKind::Cv ? type->cv : pa11::CV_NONE; }
int cv_added_rank(unsigned target, unsigned source) { unsigned added = target & ~source; int rank = 0;
if ((added & pa11::CV_CONST) != 0) ++rank; if ((added & pa11::CV_VOLATILE) != 0) ++rank;
return rank; } int qualification_conversion_rank(TypePtr target, TypePtr source) {
if (target.get() == NULL || source.get() == NULL) return 0; int rank = cv_added_rank(reference_cv_flags(target), reference_cv_flags(source));
TypePtr t = pa11::strip_cv(target); TypePtr s = pa11::strip_cv(source); if ((t->kind == pa11::TypeKind::Pointer && s->kind == pa11::TypeKind::Pointer) ||
(t->kind == pa11::TypeKind::Array && s->kind == pa11::TypeKind::Array) || (t->kind == pa11::TypeKind::LValueReference && s->kind == pa11::TypeKind::LValueReference) ||
(t->kind == pa11::TypeKind::RValueReference && s->kind == pa11::TypeKind::RValueReference)) rank += qualification_conversion_rank(t->base, s->base); return rank;
} unsigned scalar_constant_bits(TypePtr type) { uint64_t bytes = pa11::type_size(pa11::strip_cv(type));
return bytes >= 8 ? 64 : static_cast<unsigned>(bytes * 8); } uint64_t scalar_constant_mask(unsigned bits) {
return bits >= 64 ? ~uint64_t(0) : ((uint64_t(1) << bits) - 1); } bool scalar_constant_unsigned(TypePtr type) {
TypePtr bare = pa11::strip_cv(type); if (bare->kind == pa11::TypeKind::Enum) { switch (bare->enum_underlying)
{ case FT_UNSIGNED_CHAR: case FT_UNSIGNED_SHORT_INT: case FT_UNSIGNED_INT:
case FT_UNSIGNED_LONG_INT: case FT_UNSIGNED_LONG_LONG_INT: case FT_UNSIGNED_INT128: return true; default:
return false; } } if (bare->kind != pa11::TypeKind::Fundamental)
return false; switch (bare->fundamental) { case FT_BOOL:
case FT_UNSIGNED_CHAR: case FT_UNSIGNED_SHORT_INT: case FT_UNSIGNED_INT: case FT_UNSIGNED_LONG_INT:
case FT_UNSIGNED_LONG_LONG_INT: case FT_UNSIGNED_INT128: case FT_CHAR16_T: case FT_CHAR32_T: return true;
default: return false; } }
int64_t scalar_constant_signed(TypePtr type, uint64_t value) { unsigned bits = scalar_constant_bits(type); uint64_t normalized = value & scalar_constant_mask(bits);
if (bits >= 64) return static_cast<int64_t>(normalized); uint64_t sign = uint64_t(1) << (bits - 1); if ((normalized & sign) == 0)
return static_cast<int64_t>(normalized); return static_cast<int64_t>(normalized | ~scalar_constant_mask(bits)); } uint64_t convert_scalar_constant_value(TypePtr source,
TypePtr target, uint64_t value) { TypePtr src = pa11::strip_cv(source);
TypePtr dst = pa11::strip_cv(target); if ((pa11::is_integral_or_bool_type(src) || src->kind == pa11::TypeKind::Enum) && (pa11::is_integral_or_bool_type(dst) ||
dst->kind == pa11::TypeKind::Enum) && !scalar_constant_unsigned(src) && scalar_constant_bits(dst) > scalar_constant_bits(src)) return static_cast<uint64_t>(
scalar_constant_signed(src, value)) & scalar_constant_mask(scalar_constant_bits(dst)); return value & scalar_constant_mask(scalar_constant_bits(dst)); }
struct ActiveRecordConversion { vector<TypePtr>& active; ActiveRecordConversion(vector<TypePtr>& a, TypePtr record)
: active(a) { active.push_back(record); }
~ActiveRecordConversion() { active.pop_back(); }
}; bool same_template_signature_argument( const pa11::TemplateInstanceArgument& left, const pa11::TemplateInstanceArgument& right,
map<string, string>& type_parameter_names); bool same_template_signature_type(TypePtr left, TypePtr right, map<string, string>& type_parameter_names)
{ if (left.get() == NULL || right.get() == NULL) return left.get() == right.get(); if (left->kind == pa11::TypeKind::TemplateParameter &&
right->kind == pa11::TypeKind::TemplateParameter) { map<string, string>::iterator found = type_parameter_names.find(left->name);
if (found == type_parameter_names.end()) { type_parameter_names[left->name] = right->name; return true;
} return found->second == right->name; } if (pa11::same_type(left, right) ||
same_template_specialization_record(left, right)) return true; if (left->kind != right->kind) return false;
if (left->kind == pa11::TypeKind::Record && left->is_template_specialization && right->is_template_specialization && left->template_primary_name == right->template_primary_name &&
left->template_arguments.size() == right->template_arguments.size()) { for (size_t i = 0; i < left->template_arguments.size(); ++i) if (!same_template_signature_argument(
left->template_arguments[i], right->template_arguments[i], type_parameter_names)) return false;
return true; } switch (left->kind) {
case pa11::TypeKind::Cv: return left->cv == right->cv && same_template_signature_type(left->base, right->base,
type_parameter_names); case pa11::TypeKind::Pointer: case pa11::TypeKind::LValueReference: case pa11::TypeKind::RValueReference:
return same_template_signature_type(left->base, right->base, type_parameter_names); case pa11::TypeKind::Array:
return left->unknown_bound == right->unknown_bound && left->bound == right->bound && same_template_signature_type(left->base, right->base,
type_parameter_names); case pa11::TypeKind::Function: if (left->cv != right->cv || left->variadic != right->variadic ||
left->parameters.size() != right->parameters.size() || !same_template_signature_type(left->base, right->base, type_parameter_names))
return false; for (size_t i = 0; i < left->parameters.size(); ++i) if (!same_template_signature_type(left->parameters[i], right->parameters[i],
type_parameter_names)) return false; return true; case pa11::TypeKind::MemberPointer:
return same_template_signature_type(left->member_class, right->member_class, type_parameter_names) && same_template_signature_type(left->base,
right->base, type_parameter_names); default: return false;
} } bool same_template_signature_argument( const pa11::TemplateInstanceArgument& left,
const pa11::TemplateInstanceArgument& right, map<string, string>& type_parameter_names) { if (left.kind != right.kind)
return false; if (left.kind == pa11::TemplateInstanceArgumentKind::Type) return same_template_signature_type(left.type, right.type,
type_parameter_names); if (left.kind == pa11::TemplateInstanceArgumentKind::Value) return left.dependent == right.dependent && (left.dependent ||
(left.value == right.value && (left.type.get() == NULL || right.type.get() == NULL || same_template_signature_type(left.type, right.type,
type_parameter_names)))); if (left.kind == pa11::TemplateInstanceArgumentKind::Template) return left.template_name == right.template_name; if (left.pack.size() != right.pack.size())
return false; for (size_t i = 0; i < left.pack.size(); ++i) if (!same_template_signature_argument(left.pack[i], right.pack[i],
type_parameter_names)) return false; return true; }
bool same_template_signature_type(TypePtr left, TypePtr right) { map<string, string> type_parameter_names; return same_template_signature_type(left, right, type_parameter_names);
} Binding* duplicate_function_candidate(const vector<Binding*>& considered, Binding* candidate) {
for (size_t i = 0; i < considered.size(); ++i) if (pa11::same_type(considered[i]->type, candidate->type) && considered[i]->is_static_member == candidate->is_static_member) return considered[i];
return NULL; } TemplateDeclaration* function_template_origin( const map<Binding*, TemplateDeclaration*>& origins,
Binding* binding) { map<Binding*, TemplateDeclaration*>::const_iterator found = origins.find(binding);
return found != origins.end() ? found->second : NULL; } bool expr_template_parameter_lists_match(const vector<TemplateParameterInfo>& left, const vector<TemplateParameterInfo>& right)
{ if (left.size() != right.size()) return false; for (size_t i = 0; i < left.size(); ++i)
{ if (left[i].kind != right[i].kind || left[i].is_pack != right[i].is_pack || left[i].template_parameters.size() !=
right[i].template_parameters.size()) return false; for (size_t j = 0; j < left[i].template_parameters.size(); ++j) if (left[i].template_parameters[j].kind !=
right[i].template_parameters[j].kind || left[i].template_parameters[j].is_pack != right[i].template_parameters[j].is_pack) return false;
} return true; } int template_argument_specificity(
const pa11::TemplateInstanceArgument& argument); int type_pattern_specificity(TypePtr type) { if (type.get() == NULL)
return 0; if (type->kind == pa11::TypeKind::TemplateParameter || type->kind == pa11::TypeKind::TemplateTemplateParameter) return 0;
if (type->kind == pa11::TypeKind::Cv || type->kind == pa11::TypeKind::Pointer || type->kind == pa11::TypeKind::LValueReference || type->kind == pa11::TypeKind::RValueReference ||
type->kind == pa11::TypeKind::Array) return 1 + type_pattern_specificity(type->base); if (type->kind == pa11::TypeKind::Function) {
int score = 1 + type_pattern_specificity(type->base); for (size_t i = 0; i < type->parameters.size(); ++i) score += type_pattern_specificity(type->parameters[i]); return score;
} if (type->kind == pa11::TypeKind::MemberPointer) return 1 + type_pattern_specificity(type->member_class) + type_pattern_specificity(type->base);
if (type->kind == pa11::TypeKind::Record && type->is_template_specialization) { int score = 2;
for (size_t i = 0; i < type->template_arguments.size(); ++i) score += template_argument_specificity( type->template_arguments[i]); return score;
} return 1; } int template_argument_specificity(
const pa11::TemplateInstanceArgument& argument) { if (argument.kind == pa11::TemplateInstanceArgumentKind::Type) return type_pattern_specificity(argument.type);
if (argument.kind == pa11::TemplateInstanceArgumentKind::Value) return argument.dependent ? 0 : 1; if (argument.kind == pa11::TemplateInstanceArgumentKind::Template) return 1;
int score = 0; for (size_t i = 0; i < argument.pack.size(); ++i) score += template_argument_specificity(argument.pack[i]); return score;
} int function_template_parameter_specificity(TemplateDeclaration* declaration) { if (declaration == NULL ||
declaration->generic_function_type.get() == NULL || declaration->generic_function_type->kind != pa11::TypeKind::Function) return 0; int score = 0;
for (size_t i = 0; i < declaration->generic_function_type->parameters.size(); ++i) score += type_pattern_specificity(
declaration->generic_function_type->parameters[i]); return score; } int function_template_parameter_specificity_for_call(
TemplateDeclaration* declaration, size_t parameter_count) { if (declaration == NULL ||
declaration->generic_function_type.get() == NULL || declaration->generic_function_type->kind != pa11::TypeKind::Function) return 0; int score = 0;
size_t count = min(parameter_count, declaration->generic_function_type->parameters.size()); for (size_t i = 0; i < count; ++i) score += type_pattern_specificity(
declaration->generic_function_type->parameters[i]); return score; } bool template_declaration_parameter_is_pack(TemplateDeclaration* declaration,
const string& name) { if (declaration == NULL) return false;
for (size_t i = 0; i < declaration->parameters.size(); ++i) if (declaration->parameters[i].name == name) return declaration->parameters[i].is_pack; return false;
} bool function_template_parameter_pattern_is_pack( TemplateDeclaration* declaration, TypePtr pattern)
{ string name; return template_type_has_template_parameter_name(pattern, name) && template_declaration_parameter_is_pack(declaration, name);
} int function_template_nonpack_parameter_specificity_for_call( TemplateDeclaration* declaration, size_t parameter_count)
{ if (declaration == NULL || declaration->generic_function_type.get() == NULL || declaration->generic_function_type->kind != pa11::TypeKind::Function)
return 0; int score = 0; size_t count = min(parameter_count, declaration->generic_function_type->parameters.size());
for (size_t i = 0; i < count; ++i) if (!function_template_parameter_pattern_is_pack( declaration, declaration->generic_function_type->parameters[i]))
++score; return score; } bool function_template_more_specialized(
const map<Binding*, TemplateDeclaration*>& origins, Binding* lhs, Binding* rhs) {
TemplateDeclaration* left = function_template_origin(origins, lhs); TemplateDeclaration* right = function_template_origin(origins, rhs); if (left == NULL || right == NULL || left == right) return false;
int left_score = function_template_parameter_specificity(left); int right_score = function_template_parameter_specificity(right); if (left_score != right_score) return left_score > right_score;
return left->parameters.size() < right->parameters.size(); } bool same_function_template_declaration_family(TemplateDeclaration* left, TemplateDeclaration* right)
{ if (left == NULL || right == NULL || left == right) return left == right; if (left->owner == right->owner &&
left->name == right->name && expr_template_parameter_lists_match(left->parameters, right->parameters) && same_template_signature_type(left->generic_function_type,
right->generic_function_type)) return true; return left->name == right->name && left->decl_begin == right->decl_begin &&
left->decl_end == right->decl_end && expr_template_parameter_lists_match(left->parameters, right->parameters); }
bool function_template_more_specialized_for_call( const map<Binding*, TemplateDeclaration*>& origins, Binding* lhs, Binding* rhs,
size_t parameter_count) { TemplateDeclaration* left = function_template_origin(origins, lhs); TemplateDeclaration* right = function_template_origin(origins, rhs);
if (left == NULL || right == NULL || left == right) return false; int left_score = function_template_parameter_specificity_for_call(left, parameter_count);
int right_score = function_template_parameter_specificity_for_call(right, parameter_count); if (left_score != right_score) return left_score > right_score;
left_score = function_template_nonpack_parameter_specificity_for_call( left, parameter_count);
right_score = function_template_nonpack_parameter_specificity_for_call( right, parameter_count);
if (left_score != right_score) return left_score > right_score; return left->parameters.size() < right->parameters.size(); }
bool forwarding_reference_lvalue_parameter(TypePtr pattern) { TypePtr bare = pattern.get() != NULL ? pa11::strip_cv(pattern) : TypePtr();
if (bare.get() == NULL || bare->kind != pa11::TypeKind::RValueReference) return false; TypePtr base = pa11::strip_cv(bare->base);
return base.get() != NULL && base->kind == pa11::TypeKind::TemplateParameter && pa11::is_deducible_template_parameter_type(base); }
int forwarding_reference_lvalue_penalty(TemplateDeclaration* declaration, const vector<Expr>& args) { if (declaration == NULL ||
declaration->generic_function_type.get() == NULL || declaration->generic_function_type->kind != pa11::TypeKind::Function) return 0; int penalty = 0;
size_t count = min(args.size(), declaration->generic_function_type->parameters.size()); for (size_t i = 0; i < count; ++i) if (args[i].category == ValueCategory::LValue &&
forwarding_reference_lvalue_parameter( declaration->generic_function_type->parameters[i])) ++penalty; return penalty;
} bool function_template_fewer_forwarding_lvalue_parameters_for_call( const map<Binding*, TemplateDeclaration*>& origins, Binding* lhs,
Binding* rhs, const vector<Expr>& args) { TemplateDeclaration* left = function_template_origin(origins, lhs);
TemplateDeclaration* right = function_template_origin(origins, rhs); if (left == NULL || right == NULL || left == right) return false; int left_penalty = forwarding_reference_lvalue_penalty(left, args);
int right_penalty = forwarding_reference_lvalue_penalty(right, args); return left_penalty < right_penalty; } Binding* canonical_function_binding(Binding* binding)
{ while (binding != NULL && binding->kind == BindingKind::Function && binding->aliased_binding != NULL)
{ if (binding->is_inline_definition && !binding->aliased_binding->is_inline_definition) break;
binding = binding->aliased_binding; } return binding; }
void collect_conversion_functions(TypePtr record, set<Scope*>& seen, vector<Binding*>& out) {
TypePtr bare = pa11::strip_cv(record); if (bare->kind != pa11::TypeKind::Record || bare->scope == NULL || !seen.insert(bare->scope).second)
return; for (map<string, vector<Binding*> >::const_iterator it = bare->scope->members.begin(); it != bare->scope->members.end();
++it) { if (it->first.compare(0, 9, "operator ") != 0) continue;
out.insert(out.end(), it->second.begin(), it->second.end()); } vector<TypePtr> direct_bases = pa11::record_direct_bases(bare);
for (size_t b = 0; b < direct_bases.size(); ++b) collect_conversion_functions(direct_bases[b], seen, out);
} Expr make_builtin_constant_call(const vector<Expr>& args) { if (args.size() != 1)
throw runtime_error("wrong argument count"); Expr out; out.type = pa11::make_fundamental(FT_INT); out.category = ValueCategory::PRValue;
out.valid = true; const bool constant = args[0].constant_expression; out.node = Node(string("literal prvalue int ") + (constant ? "1" : "0")); out.constant_expression = true;
out.has_constant_value = true; out.constant_value = constant ? 1 : 0; out.null_pointer_constant = constant ? false : true; out.node.token_text = constant ? "1" : "0";
annotate_expr_node(out); return out; } void filter_static_class_member_overloads(Expr& callee)
{ vector<Binding*> static_overloads; bool has_class_member = false; for (size_t i = 0; i < callee.overloads.size(); ++i)
{ Binding* candidate = callee.overloads[i]; if (candidate->owner != NULL && candidate->owner->kind == ScopeKind::Class)
{ has_class_member = true; if (candidate->is_static_member) static_overloads.push_back(candidate);
} } if (has_class_member && !static_overloads.empty()) callee.overloads = static_overloads;
} Conversion Parser::convert_to(const Expr& expr, TypePtr target) { if (target->kind == pa11::TypeKind::LValueReference ||
target->kind == pa11::TypeKind::RValueReference) return convert_reference(expr, target); return convert_value(expr, target); }
Conversion Parser::convert_reference(const Expr& expr, TypePtr target) { if (expr.braced_init_list && expr.type.get() == NULL && is_std_initializer_list_type(target->base, NULL))
{ Expr list = make_initializer_list_expr(expr, target->base); return Conversion(true, 1, list); }
if (expr.braced_init_list && expr.type.get() == NULL) {
TypePtr target_object = pa11::strip_cv(target->base); if (target_object->kind == pa11::TypeKind::Record) { complete_template_record(target_object);
if (target->kind == pa11::TypeKind::LValueReference && !pa11::type_has_const(target->base)) return Conversion(); vector<Expr> args;
for (size_t i = 0; i < expr.node.children.size(); ++i) { Expr child; child.valid = true;
child.node = expr.node.children[i]; child.type = child.node.type; child.category = child.node.category; child.binding = child.node.binding;
child.overloads = child.node.overloads; child.explicit_template_arguments = child.node.explicit_template_arguments;
child.has_constant_value = child.node.has_constant_value; child.constant_value = child.node.constant_value; child.braced_init_list = child.node.line.compare(0, 16,
"braced-init-list") == 0; args.push_back(child); } Expr temporary =
make_constructor_init_expr(target->base, args, false); return Conversion(true, 1, temporary); } if (target_object->kind == pa11::TypeKind::Array)
{ function<Expr(const Node&)> expr_from_node = [&](const Node& node) { Expr out;
out.valid = true; out.node = node; out.type = node.type; out.category = node.category;
out.binding = node.binding; out.has_constant_value = node.has_constant_value; out.constant_value = node.constant_value; out.dependent_value_name = node.dependent_value_name;
out.overloads = node.overloads; out.explicit_template_arguments = node.explicit_template_arguments;
out.dependent_value_owner_template_name = node.dependent_value_owner_template_name; out.dependent_value_member_name = node.dependent_value_member_name;
out.dependent_value_negated = node.dependent_value_negated; out.dependent_value_owner_template_arguments = node.dependent_value_owner_template_arguments; out.braced_init_list =
node.line.compare(0, 16, "braced-init-list") == 0; return out; }; function<Conversion(const Expr&, TypePtr)> convert_array_list =
[&](const Expr& list, TypePtr array_type) -> Conversion { TypePtr bare_array = pa11::strip_cv(array_type); if (bare_array->kind != pa11::TypeKind::Array) return Conversion();
if (!bare_array->unknown_bound && list.node.children.size() > bare_array->bound) return Conversion(); TypePtr elem = bare_array->base;
Expr out; out.valid = true; out.type = array_type; out.category = ValueCategory::PRValue;
out.braced_init_list = true; out.node = Node("braced-init-list"); out.node.type = array_type; out.node.category = out.category;
for (size_t i = 0; i < list.node.children.size(); ++i) { Expr child = expr_from_node(list.node.children[i]); Conversion elem_conv;
if (child.braced_init_list && pa11::strip_cv(elem)->kind == pa11::TypeKind::Array) elem_conv = convert_array_list(child, elem);
else elem_conv = convert_to(child, elem); if (!elem_conv.viable) return Conversion();
add_child(out.node, elem_conv.expr.node); } annotate_expr_node(out); return Conversion(true, 0, out);
}; if (target->kind == pa11::TypeKind::LValueReference && !pa11::type_has_const(target->base)) return Conversion();
Conversion converted = convert_array_list(expr, target->base); if (!converted.viable) return converted; if (target->kind == pa11::TypeKind::LValueReference)
converted.rank += 1; return converted; } }
Expr selected = select_overload_expr(expr, target); if (!type_can_bind_reference(target, selected)) { TypePtr selected_object =
pa11::strip_cv(expression_object_type(selected.type)); Conversion via_conversion = try_reference_conversion_functions(selected, target); if (via_conversion.viable)
return via_conversion; bool lvalue_can_convert_to_prvalue = selected_object->kind == pa11::TypeKind::Array || selected_object->kind == pa11::TypeKind::Function;
if (target->kind == pa11::TypeKind::RValueReference && (selected.category != ValueCategory::LValue || lvalue_can_convert_to_prvalue)) {
TypePtr source_object = expression_object_type(selected.type); if ((source_object->cv & ~target->base->cv) != 0) return Conversion(); Conversion conv = convert_value(selected, target->base);
if (!conv.viable) return Conversion(); Expr converted = conv.expr; converted.type = target->base;
converted.category = ValueCategory::PRValue; if (!pa11::same_type(expression_object_type(selected.type), target->base)) {
converted.node = Node("cast-expression prvalue " + pa11::describe_type(target->base)); add_child(converted.node, selected.node); annotate_expr_node(converted);
} return Conversion(true, conv.rank + 1, converted); } TypePtr record = pa11::strip_cv(target->base);
if (target->kind == pa11::TypeKind::LValueReference && pa11::type_has_const(target->base) && record->kind == pa11::TypeKind::Record && record->scope != NULL)
{ Conversion conv = convert_value(selected, target->base); if (conv.viable && type_can_bind_reference(target, conv.expr)) return Conversion(true, conv.rank + 1, conv.expr);
map<string, vector<Binding*> >::const_iterator found = record->scope->members.find(record->scope->name); if (found != record->scope->members.end()) {
for (size_t i = 0; i < found->second.size(); ++i) { Binding* ctor = found->second[i]; if (function_template_placeholders_.find(ctor) !=
function_template_placeholders_.end()) { Expr this_arg; this_arg.valid = true;
this_arg.type = pa11::make_pointer(record); this_arg.category = ValueCategory::PRValue; this_arg.node = Node("id-expression prvalue " + pa11::describe_type(this_arg.type) +
" this"); annotate_expr_node(this_arg); vector<Expr> deduction_args; deduction_args.push_back(this_arg);
deduction_args.push_back(selected); map<Binding*, vector<TemplateArgument> > explicit_args; ctor = instantiate_template_call_candidate( ctor,
explicit_args, deduction_args); if (ctor == NULL) continue;
} if (ctor->kind != BindingKind::Function || ctor->is_explicit || ctor->type->parameters.size() != 2)
continue; TypePtr ctor_param = ctor->type->parameters[1]; if (pa11::is_reference_type(ctor_param) && pa11::same_type(pa11::strip_cv(ctor_param->base),
record)) continue; Conversion arg = convert_to(selected, ctor_param);
if (!arg.viable) continue; Binding* selected_ctor = ctor; ctor = canonical_function_binding(ctor);
if (unevaluated_expression_depth_ == 0) { map<Binding*, TemplateDeclaration*>::iterator template_it = function_template_placeholders_.find(ctor);
map<Binding*, vector<TemplateArgument> >::iterator args_it = function_template_specialization_arguments_.find(ctor); if (template_it == function_template_placeholders_.end() && selected_ctor != ctor)
{ template_it = function_template_placeholders_.find(selected_ctor); args_it =
function_template_specialization_arguments_.find( selected_ctor); } if (template_it != function_template_placeholders_.end() &&
args_it != function_template_specialization_arguments_.end() && template_it->second->has_definition && (!ctor->is_inline_definition ||
function_bodies_.find(ctor) == function_bodies_.end())) { Binding* instantiated =
instantiate_function_template(template_it->second, args_it->second); if (instantiated != NULL) {
if (ctor != instantiated) ctor->aliased_binding = instantiated; ctor = instantiated; }
} parse_pending_function_body(ctor); parse_pending_member_body(ctor); ensure_function_body_extra_node(ctor);
} if (deleted_functions_.find(ctor) != deleted_functions_.end()) throw runtime_error("call to deleted function"); Expr temporary;
temporary.valid = true; temporary.type = target->base; temporary.category = ValueCategory::PRValue; temporary.braced_init_list = true;
temporary.copy_initialization = true; temporary.node = Node("braced-init-list"); temporary.node.type = target->base; temporary.node.category = temporary.category;
temporary.node.direct_call = ctor; add_child(temporary.node, arg.expr.node); annotate_expr_node(temporary); return Conversion(true, arg.rank + 3, temporary);
} } } if (target->kind != pa11::TypeKind::LValueReference ||
!pa11::type_has_const(target->base)) return Conversion(); Conversion conv = convert_value(selected, target->base); if (!conv.viable)
return Conversion(); Expr converted = conv.expr; converted.type = target->base; converted.category = ValueCategory::PRValue;
converted.node = Node("cast-expression prvalue " + pa11::describe_type(target->base)); add_child(converted.node, selected.node); annotate_expr_node(converted);
return Conversion(true, conv.rank + 1, converted); } TypePtr source_object = expression_object_type(selected.type); int rank = record_base_distance(source_object, target->base);
if (rank < 1000000) rank += qualification_conversion_rank(target->base, source_object); if (rank >= 1000000)
{ if (pa11::same_type(source_object, target->base)) rank = 0; else if (types_reference_compatible(target->base, source_object))
rank = qualification_conversion_rank(target->base, source_object); else rank = 1;
} if (target->kind == pa11::TypeKind::RValueReference && selected.category != ValueCategory::LValue && pa11::same_type(source_object, target->base))
rank = 0; else if (target->kind == pa11::TypeKind::LValueReference && selected.category != ValueCategory::LValue) rank += 1;
if (selected.category == ValueCategory::PRValue) { TypePtr source_object = pa11::strip_cv(expression_object_type(selected.type));
if (source_object->kind == pa11::TypeKind::Record) ensure_default_destructor( source_object, source_object->base.get() != NULL);
} return Conversion(true, rank, selected); } Binding* Parser::instantiate_conversion_function_template_candidate(Binding* op,
TypePtr target) { map<Binding*, TemplateDeclaration*>::iterator found = function_template_placeholders_.find(op);
if (found == function_template_placeholders_.end()) return op; TemplateDeclaration* declaration = found->second; if (declaration->class_template_member &&
op->type.get() != NULL && op->type->kind == pa11::TypeKind::Function && !type_is_template_dependent(op->type)) return op;
if (declaration->generic_function_type.get() == NULL || declaration->generic_function_type->kind != pa11::TypeKind::Function) { return NULL;
} TypePtr desired = target; if (desired->kind == pa11::TypeKind::LValueReference || desired->kind == pa11::TypeKind::RValueReference)
desired = desired->base; TypePtr pattern = declaration->generic_function_type; TypePtr target_function = pa11::make_function(desired,
pattern->parameters, pattern->variadic); target_function->cv = pattern->cv; vector<TemplateArgument> deduced;
if (!deduce_function_template_target_type(declaration, target_function, vector<TemplateArgument>(), deduced))
return NULL; try { return instantiate_function_template(declaration, deduced);
} catch (const runtime_error&) { return NULL;
} } bool Parser::conversion_function_template_candidate(Binding* op) const {
map<Binding*, TemplateDeclaration*>::const_iterator found = function_template_placeholders_.find(op); return found != function_template_placeholders_.end() && !found->second->class_template_member;
} Conversion Parser::try_reference_conversion_functions(const Expr& selected, TypePtr target) {
TypePtr selected_object = pa11::strip_cv(expression_object_type(selected.type)); if (selected_object->kind != pa11::TypeKind::Record || selected_object->scope == NULL)
return Conversion(); if (!type_is_template_dependent(selected_object)) instantiate_member_function_templates(selected_object); Conversion best;
bool best_template = false; vector<Binding*> conversions; set<Scope*> seen; collect_conversion_functions(selected_object, seen, conversions);
for (size_t i = 0; i < conversions.size(); ++i) if (conversions[i]->owner != NULL && conversions[i]->owner->kind == ScopeKind::Class) mark_template_specialization_demanded(
pa11::record_type_for_scope(conversions[i]->owner)); TypePtr desired_conversion = target; if (desired_conversion->kind == pa11::TypeKind::LValueReference || desired_conversion->kind == pa11::TypeKind::RValueReference)
desired_conversion = desired_conversion->base; TypePtr desired_record = pa11::strip_cv(desired_conversion); bool exact_nontemplate_conversion = false; for (size_t i = 0; i < conversions.size(); ++i)
{ Binding* candidate = conversions[i]; if (conversion_function_template_candidate(candidate) || candidate->kind != BindingKind::Function ||
candidate->type.get() == NULL || candidate->type->kind != pa11::TypeKind::Function) continue; if (pa11::same_type(pa11::strip_cv(candidate->type->base),
desired_record)) exact_nontemplate_conversion = true; } for (size_t i = 0; i < conversions.size(); ++i)
{ bool op_template = conversion_function_template_candidate(conversions[i]); if (exact_nontemplate_conversion && op_template)
continue; if (conversions[i]->is_explicit && explicit_conversion_context_ == 0) continue; Binding* op =
instantiate_conversion_function_template_candidate( conversions[i], target); if (op == NULL)
continue; op_template = op_template || conversion_function_template_candidate(op); if (op->kind != BindingKind::Function ||
op->type->kind != pa11::TypeKind::Function || op->type->parameters.size() != 1) continue; if (pa11::same_type(pa11::strip_cv(op->type->base),
selected_object)) continue; try {
Expr member = make_member_expr(selected, op->name, "."); member.overloads.clear(); member.overloads.push_back(op); member.binding = op;
member.type = op->type; Expr call = make_call_expr(member, vector<Expr>()); Conversion tail = convert_reference(call, target); if (!tail.viable)
continue; tail.rank += 2; if (!best.viable || tail.rank < best.rank ||
(tail.rank == best.rank && best_template && !op_template)) { best = tail; best_template = op_template;
} else if (best.viable && tail.rank == best.rank && best_template == op_template)
throw runtime_error("ambiguous conversion function"); } catch (const runtime_error&) {
} } return best; }
Conversion Parser::convert_value(const Expr& expr, TypePtr target) { if (expr.braced_init_list && expr.type.get() == NULL && is_std_initializer_list_type(target, NULL))
{ Expr list = make_initializer_list_expr(expr, target); return Conversion(true, 0, list); }
Expr selected = select_overload_expr(expr, target); TypePtr src = lvalue_to_rvalue_type(selected.type);
TypePtr dst = pa11::strip_top_level_cv(target); TypePtr dst_bare = pa11::strip_cv(dst); if (selected.binding != NULL && selected.binding->kind == BindingKind::Function &&
dst_bare->kind == pa11::TypeKind::Pointer && dst_bare->base.get() != NULL && dst_bare->base->kind == pa11::TypeKind::Function && unevaluated_expression_depth_ == 0)
{ parse_pending_function_body(selected.binding); parse_pending_member_body(selected.binding); }
if (pa11::same_type(src, dst) || same_template_specialization_record(src, dst)) { TypePtr src_same_record = pa11::strip_cv(src);
TypePtr dst_same_record = pa11::strip_cv(dst); if (src_same_record->kind == pa11::TypeKind::Record && dst_same_record->kind == pa11::TypeKind::Record && (selected.category == ValueCategory::LValue ||
selected.category == ValueCategory::XValue)) { Binding* ctor = ensure_copy_move_constructor(dst_same_record,
selected.category == ValueCategory::XValue); if (unevaluated_expression_depth_ == 0) parse_pending_member_body(ctor);
} return Conversion(true, 0, selected); } TypePtr src_record = pa11::strip_cv(src);
TypePtr dst_record = pa11::strip_cv(dst); if (src_record->kind == pa11::TypeKind::Record && dst_record->kind == pa11::TypeKind::Record) {
int distance = record_base_distance(src_record, dst_record); if (distance < 1000000) { Expr converted = selected;
converted.type = dst; converted.category = ValueCategory::PRValue; converted.node = Node("cast-expression prvalue " + pa11::describe_type(dst));
add_child(converted.node, selected.node); annotate_expr_node(converted); return Conversion(true, distance + 1, converted); }
} if (selected.null_pointer_constant && is_pointer(dst)) { selected.type = dst;
selected.node = Node("literal prvalue " + pa11::describe_type(dst) + " 0"); selected.constant_expression = true; selected.has_constant_value = false; selected.node.token_text = "0";
annotate_expr_node(selected); return Conversion(true, 2, selected); } if (selected.null_pointer_constant &&
dst_bare->kind == pa11::TypeKind::MemberPointer) { selected.type = dst;
selected.node = Node("literal prvalue " + pa11::describe_type(dst) + " 0"); selected.constant_expression = true; selected.has_constant_value = false; selected.node.token_text = "0";
annotate_expr_node(selected); return Conversion(true, 2, selected); } if (selected.null_pointer_constant &&
pa11::strip_cv(dst)->kind == pa11::TypeKind::Fundamental && pa11::strip_cv(dst)->fundamental == FT_NULLPTR_T) { selected.type = dst;
selected.node = Node("literal prvalue nullptr_t 0"); selected.constant_expression = true; selected.has_constant_value = true; selected.constant_value = 0;
selected.node.token_text = "0"; annotate_expr_node(selected); return Conversion(true, 2, selected); }
if (pa11::strip_cv(src)->kind == pa11::TypeKind::Fundamental && pa11::strip_cv(src)->fundamental == FT_NULLPTR_T && is_pointer(dst)) return Conversion(true, 2, selected); if (pa11::strip_cv(src)->kind == pa11::TypeKind::Fundamental && pa11::strip_cv(src)->fundamental == FT_NULLPTR_T && dst_bare->kind == pa11::TypeKind::MemberPointer) { selected.type = dst; selected.node = Node("literal prvalue " + pa11::describe_type(dst) + " nullptr"); selected.node.token_text = "nullptr"; annotate_expr_node(selected); return Conversion(true, 2, selected); } int rank = scalar_conversion_rank(selected.type, dst);
if (rank < 1000000) { if (selected.has_constant_value) {
selected.constant_value = convert_scalar_constant_value(src, dst, selected.constant_value);
selected.node.has_constant_value = true; selected.node.constant_value = selected.constant_value; selected.node.token_text = to_string(selected.constant_value); }
return Conversion(true, rank, selected); } if (dst_record->kind == pa11::TypeKind::Record && dst_record->scope != NULL)
{ mark_template_specialization_demanded(dst_record); if (!type_is_template_dependent(dst_record)) {
complete_template_record(dst_record); instantiate_member_function_templates(dst_record); } if (record_conversion_active(active_record_conversion_targets_,
dst_record)) return Conversion(); ActiveRecordConversion active_conversion( active_record_conversion_targets_,
dst_record); Conversion best; Binding* best_ctor = NULL; Expr best_arg;
bool ambiguous = false; vector<Binding*> considered; map<string, vector<Binding*> >::const_iterator found = dst_record->scope->members.find(dst_record->scope->name);
if (found != dst_record->scope->members.end()) { for (size_t i = 0; i < found->second.size(); ++i) {
Binding* ctor = found->second[i]; if (function_template_placeholders_.find(ctor) != function_template_placeholders_.end()) {
Expr this_arg; this_arg.valid = true; this_arg.type = pa11::make_pointer(dst_record); this_arg.category = ValueCategory::PRValue;
this_arg.node = Node("id-expression prvalue " + pa11::describe_type(this_arg.type) + " this"); annotate_expr_node(this_arg);
vector<Expr> deduction_args; deduction_args.push_back(this_arg); deduction_args.push_back(selected); map<Binding*, vector<TemplateArgument> > explicit_args;
ctor = instantiate_template_call_candidate(ctor, explicit_args, deduction_args); if (ctor == NULL)
continue; } if (ctor->kind != BindingKind::Function || ctor->is_explicit ||
ctor->type->kind != pa11::TypeKind::Function || ctor->type->parameters.size() != 2) continue; bool duplicate = false;
for (size_t j = 0; j < considered.size(); ++j) if (pa11::same_type(considered[j]->type, ctor->type)) { if (!(ctor->is_inline_definition &&
!considered[j]->is_inline_definition)) duplicate = true; } if (duplicate)
continue; considered.push_back(ctor); TypePtr param = ctor->type->parameters[1]; if (pa11::is_reference_type(param) &&
(pa11::same_type(pa11::strip_cv(param->base), dst_record) || same_template_specialization_record(param->base, dst_record)))
continue; Conversion arg = convert_to(selected, param); if (!arg.viable) continue;
if (!best.viable || arg.rank < best.rank) { best = arg; best_ctor = ctor;
best_arg = arg.expr; ambiguous = false; } else if (best.viable && arg.rank == best.rank)
ambiguous = true; } } if (best.viable && !ambiguous)
{ Binding* selected_ctor = best_ctor; best_ctor = canonical_function_binding(best_ctor); if (unevaluated_expression_depth_ == 0)
{ map<Binding*, TemplateDeclaration*>::iterator template_it = function_template_placeholders_.find(best_ctor); map<Binding*, vector<TemplateArgument> >::iterator args_it =
function_template_specialization_arguments_.find(best_ctor); if (template_it == function_template_placeholders_.end() && selected_ctor != best_ctor) {
template_it = function_template_placeholders_.find(selected_ctor); args_it = function_template_specialization_arguments_.find(
selected_ctor); } if (template_it != function_template_placeholders_.end() && args_it !=
function_template_specialization_arguments_.end() && template_it->second->has_definition && (!best_ctor->is_inline_definition || function_bodies_.find(best_ctor) ==
function_bodies_.end())) { vector<TemplateArgument> selected_args = args_it->second; Binding* instantiated =
instantiate_function_template(template_it->second, selected_args); if (instantiated != NULL) {
if (best_ctor != instantiated) best_ctor->aliased_binding = instantiated; best_ctor = instantiated; }
} parse_pending_function_body(best_ctor); parse_pending_member_body(best_ctor); ensure_function_body_extra_node(best_ctor);
} if (deleted_functions_.find(best_ctor) != deleted_functions_.end()) throw runtime_error("call to deleted function"); Expr constructed;
constructed.valid = true; constructed.type = dst; constructed.category = ValueCategory::PRValue; constructed.braced_init_list = true;
constructed.copy_initialization = true; constructed.node = Node("braced-init-list"); constructed.node.type = dst; constructed.node.category = constructed.category;
constructed.node.direct_call = best_ctor; add_child(constructed.node, best_arg.node); annotate_expr_node(constructed); return Conversion(true, best.rank + 3, constructed);
} } if (src_record->kind == pa11::TypeKind::Record && src_record->scope != NULL) {
if (!type_is_template_dependent(src_record)) instantiate_member_function_templates(src_record); Conversion best; bool best_template = false;
vector<Binding*> conversions; set<Scope*> seen; collect_conversion_functions(src_record, seen, conversions); for (size_t i = 0; i < conversions.size(); ++i)
if (conversions[i]->owner != NULL && conversions[i]->owner->kind == ScopeKind::Class) mark_template_specialization_demanded( pa11::record_type_for_scope(conversions[i]->owner));
bool exact_nontemplate_conversion = false; for (size_t i = 0; i < conversions.size(); ++i) { Binding* candidate = conversions[i];
if (conversion_function_template_candidate(candidate) || candidate->kind != BindingKind::Function || candidate->type.get() == NULL || candidate->type->kind != pa11::TypeKind::Function)
continue; if (pa11::same_type(pa11::strip_cv(candidate->type->base), dst_record)) exact_nontemplate_conversion = true;
} for (size_t i = 0; i < conversions.size(); ++i) { bool op_template =
conversion_function_template_candidate(conversions[i]); if (exact_nontemplate_conversion && op_template) continue; if (conversions[i]->is_explicit && explicit_conversion_context_ == 0)
continue; Binding* op = instantiate_conversion_function_template_candidate( conversions[i],
dst); if (op == NULL) continue; op_template =
op_template || conversion_function_template_candidate(op); if (op->kind != BindingKind::Function || op->type->kind != pa11::TypeKind::Function || op->type->parameters.size() != 1)
continue; if (pa11::same_type(pa11::strip_cv(op->type->base), src_record)) continue;
try { Expr member = make_member_expr(selected, op->name, "."); member.overloads.clear();
member.overloads.push_back(op); member.binding = op; member.type = op->type; Expr call = make_call_expr(member, vector<Expr>());
Conversion tail = convert_value(call, dst); if (!tail.viable) continue; tail.rank += 2;
if (!best.viable || tail.rank < best.rank || (tail.rank == best.rank && best_template && !op_template)) {
best = tail; best_template = op_template; } else if (best.viable &&
tail.rank == best.rank && best_template == op_template) throw runtime_error("ambiguous conversion function"); }
catch (const runtime_error&) { } }
if (best.viable) return best; } return Conversion();
}
}  // namespace internal
}  // namespace pa12
