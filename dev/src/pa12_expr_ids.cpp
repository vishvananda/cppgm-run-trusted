#include "pa12_internal.h"
#include <algorithm>
#include <stdexcept>
using namespace std; namespace pa12 { namespace internal { namespace {
Expr make_this_id_expr(Binding* binding) { Expr out; out.binding = binding;
out.type = binding->type; out.category = ValueCategory::LValue; out.valid = true; out.node = Node("id-expression lvalue " + pa11::describe_type(out.type) +
" this"); annotate_expr_node(out); return out; }
Expr make_constant_binding_expr(Binding* binding, TypePtr type) { Expr out; out.binding = binding;
out.type = type; out.category = ValueCategory::PRValue; out.valid = true; out.constant_expression = true;
out.has_constant_value = true; out.constant_value = binding->constant_value; out.null_pointer_constant = binding->constant_value == 0; out.node = Node("literal prvalue " + pa11::describe_type(out.type) +
" " + to_string(binding->constant_value)); out.node.binding = binding; out.node.token_text = to_string(binding->constant_value); annotate_expr_node(out);
return out; } bool equivalent_nonfunction_binding(Binding* a, Binding* b) {
if (a == b) return true; if (a == NULL || b == NULL) return false;
if (a->kind == BindingKind::Function || b->kind == BindingKind::Function) return false; return a->kind == b->kind && a->owner == b->owner &&
a->name == b->name && a->target_scope == b->target_scope && a->aliased_binding == b->aliased_binding && pa11::same_type(a->type, b->type);
} pa11::TemplateInstanceArgument id_template_instance_argument( const TemplateArgument& argument) {
if (argument.pack_expansion && argument.kind != TemplateArgumentKind::Pack) { TemplateArgument element = argument; element.pack_expansion = false;
vector<pa11::TemplateInstanceArgument> pack; pack.push_back(id_template_instance_argument(element)); return pa11::TemplateInstanceArgument::pack_arg(pack); }
if (argument.kind == TemplateArgumentKind::Type) return pa11::TemplateInstanceArgument::type_arg(argument.type); if (argument.kind == TemplateArgumentKind::Value) {
pa11::TemplateInstanceArgument out = argument.dependent ? pa11::TemplateInstanceArgument::dependent_value_arg(argument.type) : pa11::TemplateInstanceArgument::value_arg(argument.type, argument.value);
out.value_name = argument.value_name; out.value_negated = argument.value_negated; out.value_owner_template_name = argument.value_owner_template_name; out.value_member_name = argument.value_member_name;
out.value_owner_template_arguments = argument.value_owner_template_arguments; out.value_expr_begin = argument.value_expr_begin; out.value_expr_end = argument.value_expr_end;
return out; } if (argument.kind == TemplateArgumentKind::Template) {
pa11::TemplateInstanceArgument out = pa11::TemplateInstanceArgument::template_arg( argument.template_declaration != NULL ? qualified_template_declaration_name(
argument.template_declaration) : argument.value_name); out.dependent = argument.template_declaration == NULL; return out;
} vector<pa11::TemplateInstanceArgument> pack; for (size_t i = 0; i < argument.pack.size(); ++i) { TemplateArgument element = argument.pack[i]; if (element.kind == TemplateArgumentKind::Value && !element.dependent) element.pack_expansion = false; pack.push_back(id_template_instance_argument(element)); }
return pa11::TemplateInstanceArgument::pack_arg(pack); } vector<pa11::TemplateInstanceArgument> id_template_instance_arguments( const vector<TemplateArgument>& arguments)
{ vector<pa11::TemplateInstanceArgument> out; for (size_t i = 0; i < arguments.size(); ++i) out.push_back(id_template_instance_argument(arguments[i]));
return out; } bool find_variable_templates_in_scope_tree( Scope* scope,
const string& name, map<Scope*, map<string, vector<TemplateDeclaration*> > >& variable_templates, vector<TemplateDeclaration*>& out, set<Scope*>& seen)
{ if (scope == NULL || !seen.insert(scope).second) return false; map<Scope*, map<string, vector<TemplateDeclaration*> > >::iterator sit =
variable_templates.find(scope); if (sit != variable_templates.end()) { map<string, vector<TemplateDeclaration*> >::iterator it =
sit->second.find(name); if (it != sit->second.end()) { out = it->second;
return true; } } TypePtr record = pa11::record_type_for_scope(scope);
vector<TypePtr> bases = record.get() != NULL ? pa11::record_direct_bases(record) : vector<TypePtr>(); for (size_t i = 0; i < bases.size(); ++i) { TypePtr base = bases[i].get() != NULL ? pa11::strip_cv(bases[i]) : TypePtr(); if (base.get() != NULL && base->kind == pa11::TypeKind::Record &&
base->scope != NULL && find_variable_templates_in_scope_tree(base->scope, name, variable_templates,
out, seen)) return true; } return false; }
bool scope_is_lambda_closure(Scope* scope) { return scope != NULL && scope->kind == ScopeKind::Class &&
scope->name.compare(0, 8, "__lambda") == 0; } TypePtr this_binding_record_type(Binding* binding) {
if (binding == NULL || binding->type.get() == NULL) return TypePtr(); TypePtr object = pa11::strip_cv(binding->type); if (object.get() != NULL &&
(object->kind == pa11::TypeKind::LValueReference || object->kind == pa11::TypeKind::RValueReference)) object = pa11::strip_cv(object->base); if (object.get() != NULL && object->kind == pa11::TypeKind::Pointer)
object = pa11::strip_cv(object->base); if (object.get() == NULL || object->kind != pa11::TypeKind::Record) return TypePtr(); return object;
} Binding* find_enclosing_nonlambda_this(Scope* start) { for (Scope* scope = start; scope != NULL; scope = scope->parent) {
map<string, vector<Binding*> >::iterator it = scope->members.find("this"); if (it == scope->members.end()) continue;
for (size_t i = 0; i < it->second.size(); ++i) { TypePtr record = this_binding_record_type(it->second[i]); if (record.get() != NULL &&
record->scope != NULL && !scope_is_lambda_closure(record->scope)) return it->second[i]; }
} return NULL;
}
}  // namespace
Expr Parser::make_implicit_member_id_expr(const QualifiedName& name, const vector<Binding*>& found, Binding* binding, Binding* this_binding,
const map<Binding*, vector<TemplateArgument> >* explicit_template_arguments) { if ((!name.qualified ||
(name.qualifier != NULL && name.qualifier->kind == ScopeKind::Class)) && this_binding != NULL && binding->owner != NULL && binding->owner->kind == ScopeKind::Class &&
!binding->is_static_member) { Expr this_expr = make_this_id_expr(this_binding); if (name.qualified)
{ TypePtr this_type = pa11::strip_cv(expression_object_type(this_binding->type)); TypePtr object_type = this_type->kind == pa11::TypeKind::Pointer
? this_type->base : TypePtr(); TypePtr object_record = object_type.get() != NULL ? pa11::strip_cv(object_type) : TypePtr(); if (!member_access_allowed(binding, object_record))
{ if (binding->is_private) throw runtime_error("private member access"); throw runtime_error("protected member access");
} Expr object_expr = make_deref_expr("*", this_expr); TypePtr qualifier_record = pa11::record_type_for_scope(name.qualifier);
qualifier_record = qualifier_record.get() != NULL ? pa11::strip_cv(qualifier_record) : TypePtr(); if (qualifier_record.get() != NULL && object_record.get() != NULL &&
!pa11::same_type(object_record, qualifier_record) && record_base_distance(object_record, qualifier_record) < 1000000) { Expr base_expr;
base_expr.valid = true; base_expr.type = qualifier_record; base_expr.category = ValueCategory::LValue; base_expr.node = Node("base-subobject-expression lvalue " +
pa11::describe_type(qualifier_record)); base_expr.node.type = qualifier_record; base_expr.node.category = ValueCategory::LValue; add_child(base_expr.node, object_expr.node);
annotate_expr_node(base_expr); object_expr = base_expr; } Expr member;
member.valid = true; member.binding = binding; member.type = binding->type; member.category = ValueCategory::LValue;
if (binding->kind == BindingKind::Function) { for (size_t i = 0; i < found.size(); ++i) if (found[i]->kind == BindingKind::Function)
{ member.overloads.push_back(found[i]); if (explicit_template_arguments != NULL) {
map<Binding*, vector<TemplateArgument> >::const_iterator eit = explicit_template_arguments->find(found[i]); if (eit != explicit_template_arguments->end()) member.explicit_template_arguments[found[i]] =
eit->second; } } }
else if (object_type.get() != NULL && pa11::type_has_const(object_type) && !binding->is_mutable_member) member.type = pa11::make_cv(member.type, pa11::CV_CONST);
member.node = Node("member-expression lvalue " + pa11::describe_type(member.type) + " OP_DOT:" + binding->name); add_child(member.node, object_expr.node);
member.node.binding = binding; member.node.has_op = true; member.node.op = OP_DOT; member.node.token_text = binding->name;
member.node.suppress_virtual_dispatch = true; annotate_expr_node(member); return member; }
Expr member = make_member_expr(this_expr, binding->name, "->"); if (binding->kind == BindingKind::Function && explicit_template_arguments != NULL) {
for (size_t i = 0; i < member.overloads.size(); ++i) { map<Binding*, vector<TemplateArgument> >::const_iterator eit = explicit_template_arguments->find(member.overloads[i]);
if (eit != explicit_template_arguments->end()) member.explicit_template_arguments[member.overloads[i]] = eit->second; }
} return member; } return Expr();
} void Parser::synthesize_default_assignment_lookup(const QualifiedName& name, vector<Binding*>& found) {
if (!found.empty() || !name.qualified || name.qualifier == NULL || name.qualifier->kind != ScopeKind::Class ||
name.name != "operator=") return; TypePtr record = pa11::record_type_for_scope(name.qualifier); if (record.get() == NULL)
return; vector<TypePtr> params; params.push_back(pa11::make_pointer(record)); params.push_back(
pa11::make_lvalue_reference(pa11::make_cv(record, pa11::CV_CONST))); TypePtr fn_type = pa11::make_function(pa11::make_lvalue_reference(record), params,
false); Binding* op = add_value(name.qualifier, BindingKind::Function, "operator=",
fn_type); op->is_generated_copy_move_assignment = true; op->is_inline_definition = true; found.push_back(op);
} Expr Parser::make_missing_id_expr(const QualifiedName& name) { Binding* this_binding =
pa11::lookup_unqualified(current_scope(), "this", pa11::LOOKUP_PARAMETER); Binding* active = active_functions_.empty() ? NULL : active_functions_.back(); Scope* active_class = active != NULL && active->owner != NULL &&
active->owner->kind == ScopeKind::Class ? active->owner : NULL; if (!name.qualified && this_binding != NULL && active_class != NULL) { vector<Binding*> members =
lookup_qualified_set(active_class, name.name, pa11::LOOKUP_VALUE); if (!members.empty()) { Expr member =
make_implicit_member_id_expr(name, members, members[0], this_binding);
if (member.valid) return member; } }
if (!name.qualified && active_class != NULL) { vector<Binding*> members = lookup_qualified_set(active_class, name.name, pa11::LOOKUP_VALUE);
if (!members.empty()) { TypePtr class_type = pa11::record_type_for_scope(active_class); if (class_type.get() != NULL)
{ Expr this_expr; this_expr.valid = true; this_expr.type = pa11::make_pointer(class_type);
this_expr.category = ValueCategory::LValue; this_expr.node = Node("id-expression lvalue " + pa11::describe_type(this_expr.type) + " this");
annotate_expr_node(this_expr); return make_member_expr(this_expr, name.name, "->"); } }
} if (!name.qualified) { for (Scope* scope = current_scope(); scope != NULL; scope = scope->parent)
{ map<string, vector<Binding*> >::iterator it = scope->members.find("this"); if (it == scope->members.end())
continue; for (size_t i = 0; i < it->second.size(); ++i) { Binding* enclosing_this = it->second[i];
TypePtr record = this_binding_record_type(enclosing_this); if (record.get() == NULL || record->scope == NULL || scope_is_lambda_closure(record->scope))
continue; vector<Binding*> members = lookup_qualified_set(record->scope, name.name,
pa11::LOOKUP_VALUE); if (members.empty()) continue; Expr member =
make_implicit_member_id_expr(name, members, members[0], enclosing_this);
if (member.valid) return member; } }
} if (name.qualified && name.qualifier != NULL) { TypePtr owner = pa11::record_type_for_scope(name.qualifier);
owner = owner.get() != NULL ? pa11::strip_cv(owner) : TypePtr(); if (owner.get() != NULL && owner->kind == pa11::TypeKind::Record && owner->is_template_specialization &&
type_is_template_dependent(owner)) { Expr out; out.valid = true;
out.type = pa11::make_fundamental(FT_INT); out.category = ValueCategory::PRValue; out.dependent_value_name = name.spelling; out.dependent_value_owner_template_name =
owner->template_primary_name; out.dependent_value_member_name = name.name; out.dependent_value_owner_template_arguments = owner->template_arguments;
out.node = Node("id-expression prvalue " + pa11::describe_type(out.type) + " " + name.spelling); annotate_expr_node(out);
return out; } if (owner.get() == NULL && !name.qualifier->name.empty()) {
Expr out; out.valid = true; out.type = pa11::make_fundamental(FT_INT); out.category = ValueCategory::PRValue;
out.dependent_value_name = name.spelling; out.dependent_value_owner_template_name = name.qualifier->name; out.dependent_value_member_name = name.name; out.node = Node("id-expression prvalue " +
pa11::describe_type(out.type) + " " + name.spelling); annotate_expr_node(out); return out;
} } if (name.qualified && (!template_type_substitutions_.empty() ||
!template_value_substitutions_.empty() || function_template_candidate_instantiation_depth_ != 0)) { size_t member_pos = name.spelling.rfind("::");
if (member_pos != string::npos) { string owner_name = name.spelling.substr(0, member_pos); size_t template_pos = owner_name.find('<');
if (template_pos != string::npos) owner_name = owner_name.substr(0, template_pos); size_t nested_pos = owner_name.rfind("::"); if (nested_pos != string::npos)
owner_name = owner_name.substr(nested_pos + 2); Expr out; out.valid = true; out.type = pa11::make_fundamental(FT_INT);
out.category = ValueCategory::PRValue; out.dependent_value_name = name.spelling; out.dependent_value_owner_template_name = owner_name; out.dependent_value_member_name = name.name;
out.node = Node("id-expression prvalue " + pa11::describe_type(out.type) + " " + name.spelling); annotate_expr_node(out);
return out; } } string near_token = pos_ < tokens_.size() ? tokens_[pos_].source :
string("<eof>"); throw runtime_error("name not found: " + name.spelling + " near '" + near_token + "'"); }
Expr Parser::make_aliased_member_variable_id_expr(Binding* binding) { Binding* storage = binding->aliased_binding; Expr out;
out.valid = true; out.binding = binding; out.type = binding->type; out.category = ValueCategory::LValue;
out.node = Node("member-expression lvalue " + pa11::describe_type(out.type) + " " + binding->name); TypePtr storage_type = expression_object_type(storage->type); add_child(out.node,
Node("id-expression lvalue " + pa11::describe_type(storage_type) + " " + storage->name)); out.node.binding = binding;
annotate_expr_node(out); return out; } Expr Parser::make_enumerator_id_expr(Binding* binding)
{ Expr out; out.valid = true; out.binding = binding;
out.type = binding->type; out.category = ValueCategory::PRValue; out.node = Node("literal prvalue " + pa11::describe_type(out.type) + " " + to_string(binding->constant_value));
out.constant_expression = true; out.has_constant_value = true; out.constant_value = binding->constant_value; out.null_pointer_constant = binding->constant_value == 0;
out.node.binding = binding; out.node.token_text = to_string(binding->constant_value); annotate_expr_node(out); return out;
} void Parser::prefer_static_qualified_overloads(const QualifiedName& name, Expr& out, Binding*& binding)
{ if (!name.qualified || name.qualifier == NULL || name.qualifier->kind != ScopeKind::Class ||
out.overloads.empty() || pa11::lookup_unqualified(current_scope(), "this", pa11::LOOKUP_PARAMETER) != NULL) return; vector<Binding*> static_overloads;
for (size_t i = 0; i < out.overloads.size(); ++i) if (out.overloads[i]->is_static_member) static_overloads.push_back(out.overloads[i]); if (static_overloads.empty())
return; out.overloads = static_overloads; binding = out.overloads[0]; }
Expr Parser::make_template_substitution_id_expr(const QualifiedName& name)
{
	if (name.qualified || name.has_template_arguments)
		return Expr();

	bool current_function_pack =
		!function_parameter_pack_substitutions_.empty() &&
		function_parameter_pack_substitutions_.back().find(name.name) !=
			function_parameter_pack_substitutions_.back().end();
	if (!current_function_pack)
	{
		for (Scope* scope = current_scope(); scope != NULL; scope = scope->parent)
		{
			map<string, vector<Binding*> >::iterator found =
				scope->members.find(name.name);
			if (found != scope->members.end())
				for (size_t i = 0; i < found->second.size(); ++i)
				{
					Binding* binding = found->second[i];
					if (binding != NULL &&
					    (binding->kind == BindingKind::Parameter ||
					     binding->kind == BindingKind::Variable) &&
					    binding->owner != NULL &&
					    (binding->owner->kind == ScopeKind::Function ||
					     binding->owner->kind == ScopeKind::Block))
						return Expr();
				}
			if (scope->kind == ScopeKind::Function)
				break;
		}
	}

	vector<Binding*> parameter_pack;
	if (find_function_parameter_pack_substitution(name.name, parameter_pack))
	{
		Expr out;
		out.valid = true;
		out.pack_expansion = true;
		out.type = parameter_pack.empty()
			? pa11::make_fundamental(FT_INT) : parameter_pack[0]->type;
		out.category = ValueCategory::LValue;
		out.node = Node("pack-expression " + name.name);
		for (size_t i = 0; i < parameter_pack.size(); ++i)
		{
			Expr elem;
			elem.valid = true;
			elem.binding = parameter_pack[i];
			elem.type = parameter_pack[i]->type;
			elem.category = ValueCategory::LValue;
			elem.node = Node("id-expression lvalue " +
			                 pa11::describe_type(elem.type) + " " +
			                 parameter_pack[i]->name);
			elem.node.binding = parameter_pack[i];
			annotate_expr_node(elem);
			out.pack.push_back(elem);
			add_child(out.node, elem.node);
		}
		annotate_expr_node(out);
		return out;
	}

	TemplateArgument value_arg;
	if (find_template_value_substitution(name.name, value_arg) &&
	    value_arg.kind == TemplateArgumentKind::Pack)
	{
		Expr out;
		out.valid = true;
		out.pack_expansion = true;
		out.type = value_arg.pack.empty() ||
		           value_arg.pack[0].type.get() == NULL
			? pa11::make_fundamental(FT_INT) : value_arg.pack[0].type;
		out.category = ValueCategory::PRValue;
		out.dependent_value_name = name.name;
		out.node = Node("pack-expression " + name.name);
		for (size_t i = 0; i < value_arg.pack.size(); ++i)
		{
			if (value_arg.pack[i].kind != TemplateArgumentKind::Value)
				throw runtime_error("value pack required");
			Expr elem;
			elem.valid = true;
			elem.type = value_arg.pack[i].type.get() != NULL
				? value_arg.pack[i].type : pa11::make_fundamental(FT_INT);
			elem.category = ValueCategory::PRValue;
			elem.constant_expression = !value_arg.pack[i].dependent;
			elem.has_constant_value = !value_arg.pack[i].dependent;
			elem.constant_value = value_arg.pack[i].value;
			elem.dependent_value_name = value_arg.pack[i].value_name.empty()
				? name.name : value_arg.pack[i].value_name;
			elem.dependent_value_owner_template_name =
				value_arg.pack[i].value_owner_template_name;
			elem.dependent_value_member_name =
				value_arg.pack[i].value_member_name;
			elem.dependent_value_negated = value_arg.pack[i].value_negated;
			elem.dependent_value_owner_template_arguments =
				value_arg.pack[i].value_owner_template_arguments;
			if (value_arg.pack[i].dependent)
				elem.node = Node("id-expression prvalue " +
				                 pa11::describe_type(elem.type) +
				                 " " + name.name);
			else
			{
				elem.node = Node("literal prvalue " +
				                 pa11::describe_type(elem.type) +
				                 " " + to_string(elem.constant_value));
				elem.node.token_text = to_string(elem.constant_value);
			}
			annotate_expr_node(elem);
			out.pack.push_back(elem);
			add_child(out.node, elem.node);
		}
		annotate_expr_node(out);
		return out;
	}

	if (find_template_value_substitution(name.name, value_arg) &&
	    value_arg.kind == TemplateArgumentKind::Value)
	{
		Expr out;
		out.valid = true;
		out.type = value_arg.type.get() != NULL
			? value_arg.type : pa11::make_fundamental(FT_INT);
		out.category = ValueCategory::PRValue;
		out.constant_expression = true;
		out.has_constant_value =
			!value_arg.dependent && value_arg.value_binding == NULL;
		out.constant_value = value_arg.value;
		out.null_pointer_constant = out.constant_value == 0;
		if (value_arg.value_binding != NULL)
		{
			TypePtr value_bare = value_arg.type.get() != NULL
				? pa11::strip_cv(expression_object_type(value_arg.type))
				: TypePtr();
			if (value_bare.get() != NULL &&
			    value_bare->kind == pa11::TypeKind::MemberPointer)
			{
				out.type = value_arg.type;
				out.category = ValueCategory::PRValue;
				out.has_constant_value = false;
				out.constant_value = 0;
				out.null_pointer_constant = false;
				TypePtr member_base = value_bare->base.get() != NULL
					? pa11::strip_cv(value_bare->base) : TypePtr();
				if (member_base.get() != NULL &&
				    member_base->kind != pa11::TypeKind::Function &&
				    value_arg.value_binding->kind == BindingKind::Variable)
				{
					Binding* member = value_arg.value_binding;
					if (member->aliased_binding != NULL &&
					    member->target_scope != NULL)
						member = member->aliased_binding;
					TypePtr owner = member->owner != NULL
						? pa11::record_type_for_scope(member->owner)
						: TypePtr();
					if (owner.get() != NULL)
						pa11::layout_record_type(pa11::strip_cv(owner));
					out.has_constant_value = true;
					out.constant_value = member->member_offset + 1;
					out.node = Node("literal prvalue " +
					                pa11::describe_type(out.type) +
					                " " + to_string(out.constant_value));
					out.node.token_text = to_string(out.constant_value);
					annotate_expr_node(out);
					return out;
				}
				Node member("id-expression lvalue " +
				            pa11::describe_type(value_arg.value_binding->type) +
				            " " + qualified_decl_name(value_arg.value_binding));
				member.binding = value_arg.value_binding;
				member.type = value_arg.value_binding->type;
				member.category = ValueCategory::LValue;
				out.node = Node("unary-expression prvalue " +
				                pa11::describe_type(out.type) +
				                " OP_AMP:&");
				add_child(out.node, member);
				out.node.has_op = true;
				out.node.op = OP_AMP;
				out.node.token_text = "&";
				annotate_expr_node(out);
				out.node.binding = value_arg.value_binding;
				return out;
			}
			if (unevaluated_expression_depth_ == 0 &&
			    value_arg.value_binding->kind == BindingKind::Function)
			{
				parse_pending_function_body(value_arg.value_binding);
				parse_pending_member_body(value_arg.value_binding);
			}
			out.type = value_arg.value_binding->type;
			out.category = ValueCategory::LValue;
			out.constant_value = 0;
			out.null_pointer_constant = false;
			out.node = Node("id-expression lvalue " +
			                pa11::describe_type(out.type) + " " +
			                qualified_decl_name(value_arg.value_binding));
		}
		else
		{
			if (value_arg.dependent)
			{
				string value_name = value_arg.value_name.empty()
					? name.name : value_arg.value_name;
				out.dependent_value_name = value_name;
				out.dependent_value_owner_template_name =
					value_arg.value_owner_template_name;
				out.dependent_value_member_name =
					value_arg.value_member_name;
				out.dependent_value_negated = value_arg.value_negated;
				out.dependent_value_owner_template_arguments =
					value_arg.value_owner_template_arguments;
				out.node = Node("id-expression prvalue " +
				                pa11::describe_type(out.type) + " " +
				                value_name);
			}
			else
			{
				out.node = Node("literal prvalue " +
				                pa11::describe_type(out.type) + " " +
				                to_string(out.constant_value));
				out.node.token_text = to_string(out.constant_value);
			}
		}
		annotate_expr_node(out);
		if (value_arg.value_binding != NULL)
			out.node.binding = value_arg.value_binding;
		return out;
	}
	return Expr();
}
vector<Binding*> Parser::resolve_id_expr_bindings( const QualifiedName& name, map<Binding*, vector<TemplateArgument> >& explicit_template_arguments) { QualifiedName lookup_name = name; if (lookup_name.qualifier != NULL) { TypePtr qualifier_record = pa11::record_type_for_scope(lookup_name.qualifier); qualifier_record = qualifier_record.get() != NULL
? pa11::strip_cv(qualifier_record) : TypePtr(); if (qualifier_record.get() != NULL && qualifier_record->kind == pa11::TypeKind::Record && qualifier_record->is_template_specialization) { try { TypePtr canonical = pa11::strip_cv(substitute_template_type(qualifier_record)); if (canonical.get() != NULL && canonical->kind == pa11::TypeKind::Record && canonical->scope != NULL) { qualifier_record = canonical; lookup_name.qualifier = canonical->scope; } } catch (const runtime_error&) { } } if (qualifier_record.get() != NULL && qualifier_record->kind == pa11::TypeKind::Record && !type_is_template_dependent(qualifier_record)) { try { complete_template_record(qualifier_record); instantiate_member_function_templates(qualifier_record); instantiate_member_variable_templates(qualifier_record); } catch (const runtime_error& err) {
if (string(err.what()) != "incomplete class type" && string(err.what()) != "incomplete object type") throw; } } } vector<Binding*> found = resolve_name_set(lookup_name, pa11::LOOKUP_VALUE); if (!lookup_name.has_template_arguments) { vector<TemplateDeclaration*> templates = find_function_templates(lookup_name); for (size_t i = 0; i < templates.size(); ++i) if (templates[i]->placeholder != NULL && find(found.begin(), found.end(), templates[i]->placeholder) == found.end()) found.push_back(templates[i]->placeholder); return found; } vector<TemplateDeclaration*> templates = find_function_templates(lookup_name); found.clear(); if (templates.size() == 1 && templates[0]->placeholder != NULL) { bool defer_deduced_pack = false;
for (size_t i = lookup_name.template_arguments.size(); i < templates[0]->parameters.size(); ++i) if (templates[0]->parameters[i].is_pack) defer_deduced_pack = true; try { if (templates.size() == 1 && !defer_deduced_pack) { vector<TemplateArgument> full_args = complete_template_arguments(templates[0], lookup_name.template_arguments); Binding* instantiated = instantiate_function_template(templates[0], full_args); if (unevaluated_expression_depth_ == 0) { parse_pending_function_body(instantiated); parse_pending_member_body(instantiated); } found.push_back(instantiated); explicit_template_arguments[instantiated] = full_args; return found; } } catch (const runtime_error&) { } } for (size_t i = 0; i < templates.size(); ++i) { if (templates[i]->placeholder == NULL) continue; found.push_back(templates[i]->placeholder);
explicit_template_arguments[templates[i]->placeholder] = lookup_name.template_arguments; } if (!found.empty()) return found; vector<TemplateDeclaration*> variables; if (lookup_name.qualifier != NULL) { set<Scope*> seen; find_variable_templates_in_scope_tree(lookup_name.qualifier, lookup_name.name, variable_templates_, variables, seen); } else { for (Scope* cur = current_scope(); cur != NULL; cur = cur->parent) { set<Scope*> seen; if (find_variable_templates_in_scope_tree(cur, lookup_name.name, variable_templates_, variables, seen)) { break; } } } if (variables.empty()) throw runtime_error("function template not found"); Binding* variable = instantiate_variable_template(variables[0], lookup_name.template_arguments); found.push_back(variable); return found; }
Expr Parser::make_id_expr(const QualifiedName& name) { Expr builtin = make_builtin_id_expr(name); if (builtin.valid) return builtin; Expr substitution = make_template_substitution_id_expr(name); if (substitution.valid) return substitution; map<Binding*, vector<TemplateArgument> > explicit_template_arguments; vector<Binding*> found = resolve_id_expr_bindings(name, explicit_template_arguments); synthesize_default_assignment_lookup(name, found); if (found.empty()) return make_missing_id_expr(name); Binding* nonfunction = NULL; for (size_t i = 0; i < found.size(); ++i) { if (found[i]->kind == BindingKind::Function) continue; if (nonfunction != NULL) {
if (equivalent_nonfunction_binding(nonfunction, found[i])) continue; bool found_local = found[i]->owner != NULL && (found[i]->owner->kind == ScopeKind::Function || found[i]->owner->kind == ScopeKind::Block); bool previous_local = nonfunction->owner != NULL && (nonfunction->owner->kind == ScopeKind::Function || nonfunction->owner->kind == ScopeKind::Block); if (found_local && !previous_local) { nonfunction = found[i]; continue; } if (!found_local && previous_local) continue; if (found[i]->kind == BindingKind::Parameter && nonfunction->kind != BindingKind::Parameter) { nonfunction = found[i]; continue; } if (nonfunction->kind == BindingKind::Parameter && found[i]->kind != BindingKind::Parameter) continue; throw runtime_error("ambiguous name: " + name.spelling); } nonfunction = found[i]; } Expr out; out.valid = true;
out.explicit_template_arguments = explicit_template_arguments; for (size_t i = 0; i < found.size(); ++i) { if (found[i]->kind == BindingKind::Function) out.overloads.push_back(found[i]); } if (name.qualified && name.qualifier != NULL) { TypePtr owner = pa11::record_type_for_scope(name.qualifier); owner = owner.get() != NULL ? pa11::strip_cv(owner) : TypePtr(); if (owner.get() != NULL && owner->kind == pa11::TypeKind::Record && owner->is_template_specialization && type_is_template_dependent(owner)) { out.dependent_value_name = name.spelling; out.dependent_value_owner_template_name = owner->template_primary_name; out.dependent_value_member_name = name.name; out.dependent_value_owner_template_arguments = owner->template_arguments; } } Binding* binding = found[0]; if (binding->aliased_binding != NULL && binding->target_scope != NULL && binding->kind == BindingKind::Variable) return make_aliased_member_variable_id_expr(binding); if (binding->kind == BindingKind::Enumerator) return make_enumerator_id_expr(binding); if (!out.overloads.empty()) binding = out.overloads[0]; Binding* this_binding = pa11::lookup_unqualified(current_scope(), "this", pa11::LOOKUP_PARAMETER); TypePtr this_record = this_binding_record_type(this_binding); if (this_record.get() != NULL && scope_is_lambda_closure(this_record->scope) && binding->owner != NULL && binding->owner->kind == ScopeKind::Class && !scope_is_lambda_closure(binding->owner)) { Binding* enclosing_this = find_enclosing_nonlambda_this(current_scope()); if (enclosing_this != NULL) this_binding = enclosing_this; } if (binding->owner != NULL && binding->owner->kind == ScopeKind::Class && this_record.get() != NULL && this_record->scope != binding->owner) { for (Scope* scope = current_scope(); scope != NULL; scope = scope->parent) { map<string, vector<Binding*> >::iterator it = scope->members.find("this"); if (it == scope->members.end()) continue; for (size_t i = 0; i < it->second.size(); ++i) { TypePtr candidate_record = this_binding_record_type(it->second[i]); if (candidate_record.get() != NULL && candidate_record->scope == binding->owner) { this_binding = it->second[i]; this_record = candidate_record; break; } } if (this_record.get() != NULL && this_record->scope == binding->owner) break; } } prefer_static_qualified_overloads(name, out, binding); Expr member = make_implicit_member_id_expr(name, found, binding, this_binding, &explicit_template_arguments); if (member.valid) return member;
if (binding->kind == BindingKind::Variable && binding->aliased_binding != NULL) binding = binding->aliased_binding; if (binding->kind == BindingKind::Variable && binding->is_static_member && binding->owner != NULL && binding->owner->kind == ScopeKind::Class && !validating_template_definition_ && function_template_candidate_instantiation_depth_ == 0 && short_circuit_static_member_demand_depth_ == 0) { TypePtr owner_type = pa11::record_type_for_scope(binding->owner); if (owner_type.get() != NULL) { size_t saved_pos = pos_; vector<Scope*> saved_scopes = scopes_; mark_template_specialization_demanded(owner_type); scopes_ = saved_scopes; pos_ = saved_pos; } } if (binding->kind == BindingKind::Variable && binding->has_constant && name.has_template_arguments) { return make_constant_binding_expr(binding, expression_object_type(binding->type)); } if (binding->kind == BindingKind::Variable && name.has_template_arguments &&
template_arguments_dependent(name.template_arguments)) { Expr dependent; dependent.valid = true; dependent.type = expression_object_type(binding->type); dependent.category = ValueCategory::PRValue; dependent.constant_expression = true; dependent.dependent_value_name = name.spelling; dependent.dependent_value_owner_template_name = name.name; dependent.dependent_value_owner_template_arguments = id_template_instance_arguments(name.template_arguments); dependent.node = Node("id-expression prvalue " + pa11::describe_type(dependent.type) + " " + name.spelling); dependent.node.token_text = name.spelling; annotate_expr_node(dependent); return dependent; } out.binding = binding; out.type = expression_object_type(binding->type); if (binding->kind == BindingKind::Function) out.type = binding->type;
out.category = binding->kind == BindingKind::Enumerator ? ValueCategory::PRValue : ValueCategory::LValue; string spelling = name.qualified ? name.spelling : binding->name; out.node = Node("id-expression " + value_category_name(out.category) + " " + pa11::describe_type(out.type) + " " + spelling); out.node.token_text = spelling; if (binding->has_constant) { out.constant_expression = true; out.has_constant_value = true; out.constant_value = binding->constant_value; out.null_pointer_constant = binding->constant_value == 0; } else if (!name.qualified && binding->kind == BindingKind::Variable && binding->is_static_member) { ConstexprValue value; if (try_evaluate_constexpr_binding(binding, value) && !value.is_object && !value.is_pointer) { out.constant_expression = true; out.has_constant_value = true; out.constant_value = value.int_value;
out.null_pointer_constant = value.int_value == 0; } } annotate_expr_node(out); return out; }
}  // namespace internal
}  // namespace pa12
