#include "pa12_internal.h"
#include "pa12_templates_instance_support.h"
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
if (a->kind == BindingKind::Function || b->kind == BindingKind::Function) return false; if (a->kind != b->kind || a->name != b->name)
return false; bool same_declared_type = a->type.get() != NULL && b->type.get() != NULL && pa11::same_type(a->type, b->type);
if (!same_declared_type && a->type.get() != NULL && b->type.get() != NULL) { TypePtr at = pa11::strip_cv(a->type); TypePtr bt = pa11::strip_cv(b->type);
if (at->kind == pa11::TypeKind::Array && bt->kind == pa11::TypeKind::Array && (at->unknown_bound || bt->unknown_bound || at->bound == bt->bound))
same_declared_type = pa11::same_type(pa11::strip_cv(at->base), pa11::strip_cv(bt->base)); }
bool template_owner_match = false; bool same_owner = a->owner == b->owner; if (!same_owner && a->owner != NULL &&
b->owner != NULL && a->owner->kind == ScopeKind::Class && b->owner->kind == ScopeKind::Class) { TypePtr a_record =
pa11::record_type_for_scope(a->owner); TypePtr b_record = pa11::record_type_for_scope(b->owner); template_owner_match =
a_record.get() != NULL && b_record.get() != NULL && same_template_record_type(a_record, b_record); same_owner = template_owner_match; }
if (!same_owner) return false; if (!same_declared_type && !(template_owner_match && a->is_static_member && b->is_static_member)) return false;
bool same_alias = a->aliased_binding == b->aliased_binding || a->aliased_binding == b || b->aliased_binding == a;
return a->target_scope == b->target_scope || same_alias || template_owner_match;
}
bool type_has_dependent_template_value(TypePtr type);
bool instance_argument_has_dependent_template_value(
	const pa11::TemplateInstanceArgument& argument)
{
	if (argument.kind == pa11::TemplateInstanceArgumentKind::Type)
		return type_has_dependent_template_value(argument.type);
	if (argument.kind == pa11::TemplateInstanceArgumentKind::Value)
	{
		if (argument.dependent)
			return true;
		for (size_t i = 0;
		     i < argument.value_owner_template_arguments.size();
		     ++i)
			if (instance_argument_has_dependent_template_value(
				    argument.value_owner_template_arguments[i]))
				return true;
		return type_has_dependent_template_value(argument.type);
	}
	if (argument.kind == pa11::TemplateInstanceArgumentKind::Template)
		return argument.dependent;
	if (argument.kind == pa11::TemplateInstanceArgumentKind::Pack)
		for (size_t i = 0; i < argument.pack.size(); ++i)
			if (instance_argument_has_dependent_template_value(
				    argument.pack[i]))
				return true;
	return false;
}
bool type_has_dependent_template_value(TypePtr type)
{
	if (type.get() == NULL)
		return false;
	type = pa11::strip_cv(type);
	for (size_t i = 0; i < type->template_arguments.size(); ++i)
		if (instance_argument_has_dependent_template_value(
			    type->template_arguments[i]))
			return true;
	for (size_t i = 0;
	     i < type->dependent_typename_template_argument_lists.size();
	     ++i)
		for (size_t j = 0;
		     j < type->dependent_typename_template_argument_lists[i].size();
		     ++j)
			if (instance_argument_has_dependent_template_value(
				    type->dependent_typename_template_argument_lists[i][j]))
				return true;
	if (type->kind == pa11::TypeKind::Cv ||
	    type->kind == pa11::TypeKind::Pointer ||
	    type->kind == pa11::TypeKind::LValueReference ||
	    type->kind == pa11::TypeKind::RValueReference ||
	    type->kind == pa11::TypeKind::Array)
		return type_has_dependent_template_value(type->base);
	if (type->kind == pa11::TypeKind::Function)
	{
		if (type_has_dependent_template_value(type->base))
			return true;
		for (size_t i = 0; i < type->parameters.size(); ++i)
			if (type_has_dependent_template_value(type->parameters[i]))
				return true;
	}
	if (type->kind == pa11::TypeKind::MemberPointer)
		return type_has_dependent_template_value(type->member_class) ||
		       type_has_dependent_template_value(type->base);
	return false;
}
bool template_argument_has_dependent_template_value(
	const TemplateArgument& argument)
{
	if (argument.kind == TemplateArgumentKind::Type)
		return type_has_dependent_template_value(argument.type);
	if (argument.kind == TemplateArgumentKind::Value)
	{
		if (argument.dependent)
			return true;
		for (size_t i = 0;
		     i < argument.value_owner_template_arguments.size();
		     ++i)
			if (instance_argument_has_dependent_template_value(
				    argument.value_owner_template_arguments[i]))
				return true;
		return type_has_dependent_template_value(argument.type);
	}
	if (argument.kind == TemplateArgumentKind::Template)
		return argument.template_declaration == NULL;
	if (argument.kind == TemplateArgumentKind::Pack)
		for (size_t i = 0; i < argument.pack.size(); ++i)
			if (template_argument_has_dependent_template_value(
				    argument.pack[i]))
				return true;
	return false;
}
bool template_arguments_have_dependent_template_value(
	const vector<TemplateArgument>& arguments)
{
	for (size_t i = 0; i < arguments.size(); ++i)
		if (template_argument_has_dependent_template_value(arguments[i]))
			return true;
	return false;
}
bool binding_set_all_functions(const vector<Binding*>& bindings)
{
	if (bindings.empty())
		return false;
	for (size_t i = 0; i < bindings.size(); ++i)
		if (bindings[i] == NULL ||
		    bindings[i]->kind != BindingKind::Function)
			return false;
	return true;
}
pa11::TemplateInstanceArgument id_template_instance_argument( const TemplateArgument& argument) {
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
	pa11::TemplateInstanceArgument out = pa11::TemplateInstanceArgument::pack_arg(pack); out.value_name = argument.value_name; out.template_name = argument.value_name; return out; } vector<pa11::TemplateInstanceArgument> id_template_instance_arguments( const vector<TemplateArgument>& arguments)
{ vector<pa11::TemplateInstanceArgument> out; for (size_t i = 0; i < arguments.size(); ++i) out.push_back(id_template_instance_argument(arguments[i]));
return out; }
bool hosted_trait_record_is_empty(TypePtr record)
{
	TypePtr bare = record.get() != NULL ? pa11::strip_cv(record) : TypePtr();
	if (bare.get() == NULL || bare->kind != pa11::TypeKind::Record)
		return false;
	pa11::layout_record_type(bare);
	for (size_t i = 0; i < bare->fields.size(); ++i)
	{
		Binding* field = bare->fields[i];
		if (field != NULL &&
		    field->is_no_unique_address &&
		    hosted_trait_record_is_empty(field->type))
			continue;
		return false;
	}
	vector<TypePtr> bases = pa11::record_direct_bases(bare);
	for (size_t i = 0; i < bases.size(); ++i)
		if (!hosted_trait_record_is_empty(bases[i]))
		return false;
	return true;
}
string unqualified_template_primary(TypePtr record)
{
	record = record.get() != NULL ? pa11::strip_cv(record) : TypePtr();
	if (record.get() == NULL)
		return string();
	string primary = record->template_primary_name;
	if (primary.empty() && record->scope != NULL)
		primary = record->scope->name;
	size_t qpos = primary.rfind("::");
	return qpos == string::npos ? primary : primary.substr(qpos + 2);
}
bool hosted_enable_shared_from_this_record(TypePtr record)
{
	return unqualified_template_primary(record) == "enable_shared_from_this";
}
bool hosted_record_has_esft_base(TypePtr record, set<const void*>& seen)
{
	record = record.get() != NULL ? pa11::strip_cv(record) : TypePtr();
	if (record.get() == NULL ||
	    record->kind != pa11::TypeKind::Record ||
	    !seen.insert(record.get()).second)
		return false;
	vector<TypePtr> bases = pa11::record_direct_bases(record);
	for (size_t i = 0; i < bases.size(); ++i)
	{
		TypePtr base = bases[i].get() != NULL
			? pa11::strip_cv(bases[i]) : TypePtr();
		if (hosted_enable_shared_from_this_record(base) ||
		    hosted_record_has_esft_base(base, seen))
			return true;
	}
	return false;
}
		Expr make_literal_value_expr(TypePtr type, uint64_t value)
		{
		Expr out;
		out.type = type.get() != NULL ? type : pa11::make_fundamental(FT_INT);
	out.category = ValueCategory::PRValue;
	out.valid = true;
	out.constant_expression = true;
	out.has_constant_value = true;
	out.constant_value = value;
	out.null_pointer_constant = value == 0;
	out.node = Node("literal prvalue " + pa11::describe_type(out.type) +
	                " " + to_string(value));
	out.node.token_text = to_string(value);
		annotate_expr_node(out);
		return out;
	}
	void append_hosted_trait_arg(vector<TemplateArgument>& out,
	                             const TemplateArgument& arg)
	{
		if (arg.kind == TemplateArgumentKind::Pack)
		{
			for (size_t i = 0; i < arg.pack.size(); ++i)
				append_hosted_trait_arg(out, arg.pack[i]);
			return;
		}
		out.push_back(arg);
	}
	bool instance_argument_to_template_argument(
		const pa11::TemplateInstanceArgument& in,
		TemplateArgument& out)
	{
		if (in.kind == pa11::TemplateInstanceArgumentKind::Type)
		{
			out = TemplateArgument::type_arg(in.type);
			return true;
		}
		if (in.kind == pa11::TemplateInstanceArgumentKind::Value)
		{
			out = in.dependent
				? TemplateArgument::dependent_value_arg(in.type)
				: TemplateArgument::value_arg(in.type, in.value);
			out.dependent = in.dependent;
			out.value_name = in.value_name;
			out.value_negated = in.value_negated;
			out.value_owner_template_name = in.value_owner_template_name;
			out.value_member_name = in.value_member_name;
			out.value_owner_template_arguments =
				in.value_owner_template_arguments;
			return true;
		}
		if (in.kind == pa11::TemplateInstanceArgumentKind::Pack)
		{
			vector<TemplateArgument> pack;
			for (size_t i = 0; i < in.pack.size(); ++i)
			{
				TemplateArgument elem;
				if (!instance_argument_to_template_argument(in.pack[i], elem))
					return false;
				pack.push_back(elem);
			}
			out = TemplateArgument::pack_arg(pack);
			return true;
		}
		return false;
	}
	bool hosted_trait_arguments(
		TypePtr owner,
		const map<const void*, vector<TemplateArgument> >& record_template_arguments,
		vector<TemplateArgument>& out)
	{
		owner = owner.get() != NULL ? pa11::strip_cv(owner) : TypePtr();
		if (owner.get() == NULL)
			return false;
		map<const void*, vector<TemplateArgument> >::const_iterator stored =
			record_template_arguments.find(owner.get());
		if (stored != record_template_arguments.end())
		{
			for (size_t i = 0; i < stored->second.size(); ++i)
				append_hosted_trait_arg(out, stored->second[i]);
			return true;
		}
		for (size_t i = 0; i < owner->template_arguments.size(); ++i)
		{
			TemplateArgument arg;
			if (!instance_argument_to_template_argument(
				    owner->template_arguments[i],
				    arg))
				return false;
			append_hosted_trait_arg(out, arg);
		}
		return !out.empty();
	}
	bool evaluate_hosted_trait_record(
		TypePtr owner,
		const map<const void*, vector<TemplateArgument> >& record_template_arguments,
		bool& value)
	{
		owner = owner.get() != NULL ? pa11::strip_cv(owner) : TypePtr();
		if (owner.get() == NULL || owner->kind != pa11::TypeKind::Record)
			return false;
		string primary = unqualified_template_primary(owner);
		vector<TemplateArgument> args;
		hosted_trait_arguments(owner, record_template_arguments, args);
		if ((primary == "integral_constant" ||
		     primary == "__bool_constant") &&
		    args.size() >= 2 &&
		    args[1].kind == TemplateArgumentKind::Value &&
		    !args[1].dependent)
		{
			value = args[1].value != 0;
			return true;
		}
		if ((primary == "is_same" || primary == "__are_same") &&
		    args.size() >= 2 &&
		    args[0].kind == TemplateArgumentKind::Type &&
		    args[1].kind == TemplateArgumentKind::Type)
		{
			value = pa11::same_type(args[0].type, args[1].type);
			return true;
		}
			if (primary == "is_class" &&
			    !args.empty() &&
			    args[0].kind == TemplateArgumentKind::Type)
		{
			TypePtr bare = args[0].type.get() != NULL
				? pa11::strip_cv(args[0].type) : TypePtr();
			value = bare.get() != NULL &&
			        bare->kind == pa11::TypeKind::Record;
				return true;
			}
			if (primary == "__has_esft_base" &&
			    !args.empty() &&
			    args[0].kind == TemplateArgumentKind::Type)
			{
				TypePtr bare = args[0].type.get() != NULL
					? pa11::strip_cv(args[0].type) : TypePtr();
				set<const void*> seen;
				value = bare.get() != NULL &&
				        bare->kind == pa11::TypeKind::Record &&
				        hosted_record_has_esft_base(bare, seen);
				return true;
			}
			if (primary == "__not_" &&
			    args.size() == 1 &&
		    args[0].kind == TemplateArgumentKind::Type)
		{
			bool inner = false;
			if (!evaluate_hosted_trait_record(args[0].type,
			                                  record_template_arguments,
			                                  inner))
				return false;
			value = !inner;
			return true;
		}
		if (primary == "__and_" || primary == "__or_")
		{
			value = primary == "__and_";
			for (size_t i = 0; i < args.size(); ++i)
			{
				if (args[i].kind != TemplateArgumentKind::Type)
					return false;
				bool elem = false;
				if (!evaluate_hosted_trait_record(args[i].type,
				                                  record_template_arguments,
				                                  elem))
					return false;
				if (primary == "__and_" && !elem)
				{
					value = false;
					return true;
				}
				if (primary == "__or_" && elem)
				{
					value = true;
					return true;
				}
			}
			return true;
		}
		return false;
	}
	Expr make_hosted_trait_value_expr(
		TypePtr owner,
		const map<const void*, vector<TemplateArgument> >& record_template_arguments)
	{
	owner = owner.get() != NULL ? pa11::strip_cv(owner) : TypePtr();
	if (owner.get() == NULL || owner->kind != pa11::TypeKind::Record)
		return Expr();
		map<const void*, vector<TemplateArgument> >::const_iterator stored_args =
			record_template_arguments.find(owner.get());
		string primary = unqualified_template_primary(owner);
		if (stored_args != record_template_arguments.end())
		{
		const vector<TemplateArgument>& args = stored_args->second;
		if ((primary == "is_same" || primary == "__are_same") &&
		    args.size() >= 2 &&
		    args[0].kind == TemplateArgumentKind::Type &&
		    args[1].kind == TemplateArgumentKind::Type &&
		    !template_argument_has_template_parameter(args[0],
		                                             record_template_arguments) &&
		    !template_argument_has_template_parameter(args[1],
		                                             record_template_arguments))
		{
			return make_literal_value_expr(
				pa11::make_fundamental(FT_BOOL),
				pa11::same_type(args[0].type, args[1].type) ? 1 : 0);
		}
		if ((primary == "integral_constant" || primary == "__bool_constant") &&
		    args.size() >= 2 &&
		    args[0].kind == TemplateArgumentKind::Type &&
		    args[1].kind == TemplateArgumentKind::Value &&
		    !template_argument_has_template_parameter(args[0],
		                                             record_template_arguments) &&
		    !args[1].dependent)
		{
			return make_literal_value_expr(args[0].type, args[1].value);
		}
	}
	const vector<pa11::TemplateInstanceArgument>& instance_args =
		owner->template_arguments;
	if ((primary == "is_same" || primary == "__are_same") &&
	    instance_args.size() >= 2 &&
	    instance_args[0].kind == pa11::TemplateInstanceArgumentKind::Type &&
	    instance_args[1].kind == pa11::TemplateInstanceArgumentKind::Type &&
	    !template_instance_argument_has_template_parameter(instance_args[0],
	                                                      record_template_arguments) &&
	    !template_instance_argument_has_template_parameter(instance_args[1],
	                                                      record_template_arguments))
	{
		return make_literal_value_expr(
			pa11::make_fundamental(FT_BOOL),
			pa11::same_type(instance_args[0].type,
			                instance_args[1].type) ? 1 : 0);
	}
	if ((primary == "integral_constant" || primary == "__bool_constant") &&
	    instance_args.size() >= 2 &&
	    instance_args[0].kind == pa11::TemplateInstanceArgumentKind::Type &&
	    instance_args[1].kind == pa11::TemplateInstanceArgumentKind::Value &&
	    !template_instance_argument_has_template_parameter(instance_args[0],
	                                                      record_template_arguments) &&
	    !instance_args[1].dependent)
	{
		return make_literal_value_expr(instance_args[0].type,
		                               instance_args[1].value);
	}
	bool hosted_value = false;
	if (evaluate_hosted_trait_record(owner,
	                                 record_template_arguments,
	                                 hosted_value))
		return make_literal_value_expr(pa11::make_fundamental(FT_BOOL),
		                               hosted_value ? 1 : 0);
	return Expr();
}
bool find_variable_templates_in_scope_tree( Scope* scope,
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
bool is_std_namespace_scope(Scope* scope)
{
	return scope != NULL &&
	       scope->kind == ScopeKind::Namespace &&
	       scope->name == "std";
}
bool hosted_deprecated_exception_name(const string& name)
{
	return name == "set_unexpected" ||
	       name == "get_unexpected" ||
	       name == "unexpected";
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
	member.valid = true; member.binding = binding; member.type = binding->type; if (binding->kind != BindingKind::Function && (!template_type_substitutions_.empty() || !template_value_substitutions_.empty())) { try { member.type = substitute_template_type(member.type); } catch (const runtime_error&) { } } member.category = ValueCategory::LValue;
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
}
void Parser::synthesize_default_assignment_lookup(const QualifiedName& name, vector<Binding*>& found) {
if (!found.empty() || !name.qualified || name.qualifier == NULL || name.qualifier->kind != ScopeKind::Class ||
name.name != "operator=") return; TypePtr record = pa11::record_type_for_scope(name.qualifier); if (record.get() == NULL)
return; vector<TypePtr> params; params.push_back(pa11::make_pointer(record)); params.push_back(
pa11::make_lvalue_reference(pa11::make_cv(record, pa11::CV_CONST))); TypePtr fn_type = pa11::make_function(pa11::make_lvalue_reference(record), params,
false); Binding* op = add_value(name.qualifier, BindingKind::Function, "operator=",
fn_type); op->is_generated_copy_move_assignment = true; op->is_inline_definition = true; found.push_back(op);
}
Expr Parser::make_missing_id_expr(const QualifiedName& name) { Binding* this_binding =
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
	} Scope* dependent_member_owner = NULL; if (!name.qualified) {
		if (current_scope()->kind == ScopeKind::Class)
			dependent_member_owner = current_scope();
		else if (active_class != NULL) {
			TypePtr active_owner = pa11::record_type_for_scope(active_class);
			active_owner = active_owner.get() != NULL ? pa11::strip_cv(active_owner) : TypePtr();
			for (size_t i = 0; i < active_class_instantiations_.size(); ++i) {
				TypePtr active_type = active_class_instantiations_[i].type.get() != NULL ?
					pa11::strip_cv(active_class_instantiations_[i].type) : TypePtr();
				if (active_type.get() != NULL && active_type.get() == active_owner.get() &&
				    !active_type->complete) {
					dependent_member_owner = active_class;
					break;
				}
			}
		}
	} if (dependent_member_owner != NULL &&
		(validating_template_definition_ ||
		 active_class_instantiation_dependent() ||
		 !active_class_instantiations_.empty() ||
		 !template_type_substitutions_.empty() ||
		 !template_value_substitutions_.empty())) {
		TypePtr owner = pa11::record_type_for_scope(dependent_member_owner);
		owner = owner.get() != NULL ? pa11::strip_cv(owner) : TypePtr();
		Expr out;
		out.valid = true;
		out.type = pa11::make_dependent_typename_type(
			dependent_member_owner->name + "::" + name.name,
			true,
			false,
			false);
	out.category = ValueCategory::LValue;
		out.dependent_value_name = name.name;
		out.dependent_value_owner_template_name =
			owner.get() != NULL && !owner->template_primary_name.empty()
			? owner->template_primary_name : dependent_member_owner->name;
	out.dependent_value_member_name = name.name;
	if (owner.get() != NULL && !owner->template_arguments.empty())
		out.dependent_value_owner_template_arguments =
			owner->template_arguments;
	else if (owner.get() != NULL)
	{
		map<const void*, vector<TemplateArgument> >::const_iterator args =
			record_template_arguments_.find(owner.get());
		if (args != record_template_arguments_.end())
			out.dependent_value_owner_template_arguments =
				id_template_instance_arguments(args->second);
	}
	out.node = Node("id-expression lvalue " +
	                pa11::describe_type(out.type) + " " + name.name);
	out.node.token_text = name.name;
	annotate_expr_node(out);
	return out;
} if (name.qualified && name.qualifier != NULL) { TypePtr owner = pa11::record_type_for_scope(name.qualifier);
owner = owner.get() != NULL ? pa11::strip_cv(owner) : TypePtr(); bool owner_dependent = owner.get() != NULL && type_is_template_dependent(owner); bool defer_template_specialization_member =
owner.get() != NULL && owner->kind == pa11::TypeKind::Record && owner->is_template_specialization &&
(owner_dependent || validating_template_definition_); if (defer_template_specialization_member) { Expr out; out.valid = true;
out.type = pa11::make_fundamental(FT_INT); out.category = ValueCategory::PRValue; out.dependent_value_name = name.spelling; out.dependent_value_owner_template_name =
owner->template_primary_name; out.dependent_value_member_name = name.name; out.dependent_value_owner_template_arguments = owner->template_arguments;
if (out.dependent_value_owner_template_arguments.empty()) { map<const void*, vector<TemplateArgument> >::const_iterator args = record_template_arguments_.find(owner.get()); if (args != record_template_arguments_.end())
for (size_t i = 0; i < args->second.size(); ++i) out.dependent_value_owner_template_arguments.push_back(id_template_instance_argument(args->second[i])); }
out.node = Node("id-expression prvalue " + pa11::describe_type(out.type) + " " + name.spelling); annotate_expr_node(out);
return out; } if (owner.get() != NULL && owner->kind == pa11::TypeKind::Record && owner->is_template_specialization && !owner_dependent && owner->scope != NULL && !validating_template_definition_) complete_template_record(owner); if (owner.get() == NULL && !name.qualifier->name.empty()) {
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
			return out; } } throw runtime_error("name not found: " + name.spelling); }
Expr Parser::make_aliased_member_variable_id_expr(Binding* binding) { Binding* storage = binding->aliased_binding; Expr out;
out.valid = true; out.binding = binding; out.type = binding->type; out.category = ValueCategory::LValue;
out.node = Node("member-expression lvalue " + pa11::describe_type(out.type) + " " + binding->name); TypePtr storage_type = expression_object_type(storage->type); Node storage_node(
"id-expression lvalue " + pa11::describe_type(storage_type) + " " + storage->name);
storage_node.binding = storage; storage_node.type = storage_type;
storage_node.category = ValueCategory::LValue; add_child(out.node,
storage_node); out.node.binding = binding;
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
			if (value_arg.value_binding->kind == BindingKind::Function)
				out.dependent_value_name = value_arg.value_name.empty()
					? name.name : value_arg.value_name;
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
vector<Binding*> Parser::resolve_id_expr_bindings(
	const QualifiedName& name,
	map<Binding*, vector<TemplateArgument> >& explicit_template_arguments)
{
	QualifiedName lookup_name = name;
	if (lookup_name.qualifier != NULL)
	{
		TypePtr qualifier_record =
			pa11::record_type_for_scope(lookup_name.qualifier);
		qualifier_record = qualifier_record.get() != NULL
			? pa11::strip_cv(qualifier_record) : TypePtr();
		if (qualifier_record.get() != NULL &&
		    qualifier_record->kind == pa11::TypeKind::Record &&
		    qualifier_record->is_template_specialization)
		{
			try {
				TypePtr canonical =
					pa11::strip_cv(substitute_template_type(qualifier_record));
				if (canonical.get() != NULL &&
				    canonical->kind == pa11::TypeKind::Record &&
				    canonical->scope != NULL)
				{
					qualifier_record = canonical;
					lookup_name.qualifier = canonical->scope;
				}
			} catch (const runtime_error&) { }
		}
		if (qualifier_record.get() != NULL &&
		    qualifier_record->kind == pa11::TypeKind::Record &&
		    !type_is_template_dependent(qualifier_record))
		{
			try {
				complete_template_record(qualifier_record);
				instantiate_member_function_templates(qualifier_record);
				instantiate_member_variable_templates(qualifier_record);
			} catch (const runtime_error& err) {
				if (string(err.what()) != "incomplete class type" &&
				    string(err.what()) != "incomplete object type")
					throw;
			}
		}
	}
	vector<Binding*> found = resolve_name_set(lookup_name, pa11::LOOKUP_VALUE);
	if (!lookup_name.has_template_arguments)
	{
		if (found.empty() || binding_set_all_functions(found))
		{
			vector<TemplateDeclaration*> templates =
				find_function_templates(lookup_name);
			for (size_t i = 0; i < templates.size(); ++i)
				if (templates[i]->placeholder != NULL &&
				    find(found.begin(), found.end(),
				         templates[i]->placeholder) == found.end())
					found.push_back(templates[i]->placeholder);
		}
		return found;
	}
	vector<TemplateDeclaration*> templates = find_function_templates(lookup_name);
	found.clear();
	if (templates.size() == 1 && templates[0]->placeholder != NULL)
	{
		bool defer_deduced_pack = false;
		for (size_t i = lookup_name.template_arguments.size();
		     i < templates[0]->parameters.size(); ++i)
			if (templates[0]->parameters[i].is_pack)
				defer_deduced_pack = true;
		bool immediate_call = at(OP_LPAREN);
		try {
			if (!defer_deduced_pack && !immediate_call)
			{
				vector<TemplateArgument> full_args =
					complete_template_arguments(templates[0],
					                            lookup_name.template_arguments);
				Binding* instantiated =
					instantiate_function_template(templates[0], full_args);
				if (unevaluated_expression_depth_ == 0)
				{
					parse_pending_function_body(instantiated);
					parse_pending_member_body(instantiated);
				}
				found.push_back(instantiated);
				explicit_template_arguments[instantiated] = full_args;
				return found;
			}
		} catch (const runtime_error&) { }
	}
	for (size_t i = 0; i < templates.size(); ++i)
	{
		if (templates[i]->placeholder == NULL)
			continue;
		found.push_back(templates[i]->placeholder);
		explicit_template_arguments[templates[i]->placeholder] =
			lookup_name.template_arguments;
	}
	if (!found.empty())
		return found;
	vector<TemplateDeclaration*> variables;
	if (lookup_name.qualifier != NULL)
	{
		set<Scope*> seen;
		find_variable_templates_in_scope_tree(lookup_name.qualifier,
		                                      lookup_name.name,
		                                      variable_templates_,
		                                      variables,
		                                      seen);
	}
	else
	{
		for (Scope* cur = current_scope(); cur != NULL; cur = cur->parent)
		{
			set<Scope*> seen;
			if (find_variable_templates_in_scope_tree(cur, lookup_name.name,
			                                          variable_templates_,
			                                          variables, seen))
				break;
		}
	}
	if (variables.empty())
	{
		throw runtime_error("function template not found");
	}
	Binding* variable =
		instantiate_variable_template(variables[0],
		                              lookup_name.template_arguments);
	found.push_back(variable);
	return found;
}
Expr Parser::make_id_expr(const QualifiedName& name)
{
	Expr builtin = make_builtin_id_expr(name);
	if (builtin.valid)
		return builtin;
	Expr substitution = make_template_substitution_id_expr(name);
	if (substitution.valid)
		return substitution;
	if (hosted_compatibility_ && name.qualified &&
	    (name.name == "value" || name.name == "__value") &&
	    name.qualifier != NULL)
	{
		TypePtr owner = pa11::record_type_for_scope(name.qualifier);
		Expr trait_value =
			make_hosted_trait_value_expr(owner, record_template_arguments_);
		if (trait_value.valid)
			return trait_value;
		owner = owner.get() != NULL ? pa11::strip_cv(owner) : TypePtr();
		if (owner.get() != NULL && owner->kind == pa11::TypeKind::Record)
		{
			string primary = owner->template_primary_name;
			size_t qpos = primary.rfind("::");
			string unqualified =
				qpos == string::npos ? primary : primary.substr(qpos + 2);
			map<const void*, vector<TemplateArgument> >::const_iterator stored_args =
				record_template_arguments_.find(owner.get());
			if (unqualified == "__empty_not_final" &&
			    stored_args != record_template_arguments_.end() &&
			    !stored_args->second.empty() &&
			    stored_args->second[0].kind == TemplateArgumentKind::Type)
			{
				TypePtr type = stored_args->second[0].type;
				if (type_is_template_dependent(type))
				{
					Expr out;
					out.valid = true;
					out.type = pa11::make_fundamental(FT_BOOL);
					out.category = ValueCategory::PRValue;
					out.constant_expression = true;
					out.dependent_value_name = name.spelling;
					out.dependent_value_owner_template_name =
						owner->template_primary_name;
					out.dependent_value_member_name = name.name;
					out.dependent_value_owner_template_arguments =
						owner->template_arguments;
					if (out.dependent_value_owner_template_arguments.empty())
						out.dependent_value_owner_template_arguments =
							id_template_instance_arguments(stored_args->second);
					out.node = Node("id-expression prvalue " +
					                pa11::describe_type(out.type) + " " +
					                name.spelling);
					out.node.token_text = name.spelling;
					annotate_expr_node(out);
					return out;
				}
				TypePtr bare = pa11::strip_cv(type);
				bool value = bare->kind == pa11::TypeKind::Record &&
				             !bare->is_final_record &&
				             hosted_trait_record_is_empty(type);
				return make_integer_literal_expr(FT_BOOL, value ? 1 : 0);
			}
			if (unqualified == "__are_same" && name.name == "__value" &&
			    stored_args != record_template_arguments_.end() &&
			    stored_args->second.size() >= 2 &&
			    stored_args->second[0].kind == TemplateArgumentKind::Type &&
			    stored_args->second[1].kind == TemplateArgumentKind::Type &&
			    !type_is_template_dependent(stored_args->second[0].type) &&
			    !type_is_template_dependent(stored_args->second[1].type))
				return make_integer_literal_expr(
					FT_INT,
					pa11::same_type(stored_args->second[0].type,
					                stored_args->second[1].type) ? 1 : 0);
		}
	}
	if (hosted_compatibility_ &&
	    name.qualified &&
	    is_std_namespace_scope(name.qualifier) &&
	    hosted_deprecated_exception_name(name.name) &&
	    pa11::lookup_qualified(name.qualifier,
	                          name.name,
	                          pa11::LOOKUP_FUNCTION) == NULL)
	{
		TypePtr void_type = pa11::make_fundamental(FT_VOID);
		TypePtr handler_type = pa11::make_pointer(
			pa11::make_function(void_type, vector<TypePtr>(), false));
		if (pa11::lookup_qualified(name.qualifier,
		                          "unexpected_handler",
		                          pa11::LOOKUP_TYPE) == NULL)
			add_alias(name.qualifier, "unexpected_handler", handler_type);
		if (pa11::lookup_qualified(name.qualifier,
		                          "set_unexpected",
		                          pa11::LOOKUP_FUNCTION) == NULL)
		{
			vector<TypePtr> params(1, handler_type);
			Binding* binding = add_value(
				name.qualifier,
				BindingKind::Function,
				"set_unexpected",
				pa11::make_function(handler_type, params, false));
			binding->unwind_no = true;
		}
		if (pa11::lookup_qualified(name.qualifier,
		                          "get_unexpected",
		                          pa11::LOOKUP_FUNCTION) == NULL)
		{
			Binding* binding = add_value(
				name.qualifier,
				BindingKind::Function,
				"get_unexpected",
				pa11::make_function(handler_type,
				                    vector<TypePtr>(),
				                    false));
			binding->unwind_no = true;
		}
		if (pa11::lookup_qualified(name.qualifier,
		                          "unexpected",
		                          pa11::LOOKUP_FUNCTION) == NULL)
		{
			Binding* binding = add_value(
				name.qualifier,
				BindingKind::Function,
				"unexpected",
				pa11::make_function(void_type,
				                    vector<TypePtr>(),
				                    false));
			binding->unwind_no = true;
		}
	}
	map<Binding*, vector<TemplateArgument> > explicit_template_arguments;
	vector<Binding*> found =
		resolve_id_expr_bindings(name, explicit_template_arguments);
	synthesize_default_assignment_lookup(name, found);
	if (found.empty())
		return make_missing_id_expr(name);
	Binding* nonfunction = NULL;
	for (size_t i = 0; i < found.size(); ++i)
	{
		if (found[i]->kind == BindingKind::Function)
			continue;
		if (nonfunction != NULL)
		{
			if (equivalent_nonfunction_binding(nonfunction, found[i]))
				continue;
			bool found_local = found[i]->owner != NULL &&
				(found[i]->owner->kind == ScopeKind::Function ||
				 found[i]->owner->kind == ScopeKind::Block);
			bool previous_local = nonfunction->owner != NULL &&
				(nonfunction->owner->kind == ScopeKind::Function ||
				 nonfunction->owner->kind == ScopeKind::Block);
			if (found_local && !previous_local)
			{
				nonfunction = found[i];
				continue;
			}
			if (!found_local && previous_local)
				continue;
			if (found[i]->kind == BindingKind::Parameter &&
			    nonfunction->kind != BindingKind::Parameter)
			{
				nonfunction = found[i];
				continue;
			}
			if (nonfunction->kind == BindingKind::Parameter &&
			    found[i]->kind != BindingKind::Parameter)
				continue;
			throw runtime_error("ambiguous name: " + name.spelling);
		}
		nonfunction = found[i];
	}
	Expr out;
	out.valid = true;
out.explicit_template_arguments = explicit_template_arguments;
for (size_t i = 0; i < found.size(); ++i)
	if (found[i]->kind == BindingKind::Function)
		out.overloads.push_back(found[i]);
if (name.qualified && name.qualifier != NULL)
{
	TypePtr owner = pa11::record_type_for_scope(name.qualifier);
	owner = owner.get() != NULL ? pa11::strip_cv(owner) : TypePtr();
	if (owner.get() != NULL &&
	    owner->kind == pa11::TypeKind::Record &&
	    owner->is_template_specialization)
	{
		map<const void*, vector<TemplateArgument> >::const_iterator args =
			record_template_arguments_.find(owner.get());
		bool dependent_owner =
			type_is_template_dependent(owner) ||
			type_has_dependent_template_value(owner) ||
			(args != record_template_arguments_.end() &&
			 template_arguments_have_dependent_template_value(
				 args->second));
		if (dependent_owner)
		{
			out.dependent_value_name = name.spelling;
			out.dependent_value_owner_template_name =
				owner->template_primary_name;
			out.dependent_value_member_name = name.name;
			out.dependent_value_owner_template_arguments =
				owner->template_arguments;
			if (out.dependent_value_owner_template_arguments.empty() &&
			    args != record_template_arguments_.end())
				for (size_t i = 0; i < args->second.size(); ++i)
					out.dependent_value_owner_template_arguments.push_back(
						id_template_instance_argument(args->second[i]));
		}
	}
}
	Binding* binding = found[0];
	if (binding->aliased_binding != NULL &&
	    binding->target_scope != NULL &&
	    binding->kind == BindingKind::Variable)
		return make_aliased_member_variable_id_expr(binding);
	if (binding->kind == BindingKind::Enumerator)
		return make_enumerator_id_expr(binding);
	if (!out.overloads.empty())
		binding = out.overloads[0];
	Binding* this_binding =
		pa11::lookup_unqualified(current_scope(), "this", pa11::LOOKUP_PARAMETER);
	TypePtr this_record = this_binding_record_type(this_binding);
	if (this_record.get() != NULL &&
	    scope_is_lambda_closure(this_record->scope) &&
	    binding->owner != NULL &&
	    binding->owner->kind == ScopeKind::Class &&
	    !scope_is_lambda_closure(binding->owner))
	{
		Binding* enclosing_this = find_enclosing_nonlambda_this(current_scope());
		if (enclosing_this != NULL)
			this_binding = enclosing_this;
	}
	if (binding->owner != NULL &&
	    binding->owner->kind == ScopeKind::Class &&
	    this_record.get() != NULL &&
	    this_record->scope != binding->owner)
	{
		for (Scope* scope = current_scope(); scope != NULL; scope = scope->parent)
		{
			map<string, vector<Binding*> >::iterator it =
				scope->members.find("this");
			if (it == scope->members.end())
				continue;
			for (size_t i = 0; i < it->second.size(); ++i)
			{
				TypePtr candidate_record =
					this_binding_record_type(it->second[i]);
				if (candidate_record.get() != NULL &&
				    candidate_record->scope == binding->owner)
				{
					this_binding = it->second[i];
					this_record = candidate_record;
					break;
				}
			}
			if (this_record.get() != NULL &&
			    this_record->scope == binding->owner)
				break;
		}
	}
	prefer_static_qualified_overloads(name, out, binding);
	Expr member = make_implicit_member_id_expr(name, found, binding,
	                                           this_binding,
	                                           &explicit_template_arguments);
	if (member.valid)
		return member;
	if (hosted_compatibility_ && name.qualified &&
	    name.name == "value" && name.qualifier != NULL)
	{
		TypePtr owner = pa11::record_type_for_scope(name.qualifier);
		owner = owner.get() != NULL ? pa11::strip_cv(owner) : TypePtr();
		if (owner.get() != NULL && owner->kind == pa11::TypeKind::Record)
		{
			string primary = owner->template_primary_name;
			size_t qpos = primary.rfind("::");
			string unqualified =
				qpos == string::npos ? primary : primary.substr(qpos + 2);
			if (unqualified == "__is_nothrow_invocable")
			{
				map<const void*, vector<TemplateArgument> >::const_iterator stored_args =
					record_template_arguments_.find(owner.get());
				vector<TypePtr> types;
				bool type_args = stored_args != record_template_arguments_.end();
				if (type_args)
					for (size_t i = 0; i < stored_args->second.size(); ++i)
					{
						const TemplateArgument& trait_arg =
							stored_args->second[i];
						if (trait_arg.kind == TemplateArgumentKind::Type)
							types.push_back(trait_arg.type);
						else if (trait_arg.kind == TemplateArgumentKind::Pack)
							for (size_t j = 0; j < trait_arg.pack.size(); ++j)
							{
								if (trait_arg.pack[j].kind !=
								    TemplateArgumentKind::Type)
								{
									type_args = false;
									break;
								}
								types.push_back(trait_arg.pack[j].type);
							}
						else
							type_args = false;
						if (!type_args)
							break;
					}
				if (type_args)
					return make_integer_literal_expr(
						FT_BOOL,
						is_invocable_type_trait(types, true) ? 1 : 0);
			}
		}
	}
	if (binding->kind == BindingKind::Variable &&
	    binding->aliased_binding != NULL)
		binding = binding->aliased_binding;
	if (binding->kind == BindingKind::Variable &&
	    binding->is_static_member &&
	    binding->owner != NULL &&
	    binding->owner->kind == ScopeKind::Class &&
	    !validating_template_definition_ &&
	    function_template_candidate_instantiation_depth_ == 0 &&
	    short_circuit_static_member_demand_depth_ == 0)
	{
		TypePtr owner_type = pa11::record_type_for_scope(binding->owner);
		if (owner_type.get() != NULL)
		{
			size_t saved_pos = pos_;
			vector<Scope*> saved_scopes = scopes_;
			mark_template_specialization_demanded(owner_type);
			scopes_ = saved_scopes;
			pos_ = saved_pos;
		}
	}
	if (binding->kind == BindingKind::Variable &&
	    binding->has_constant &&
	    name.has_template_arguments)
		return make_constant_binding_expr(binding,
		                                  expression_object_type(binding->type));
	if (binding->kind == BindingKind::Variable &&
	    name.has_template_arguments &&
	    template_arguments_dependent(name.template_arguments))
	{
		Expr dependent;
		dependent.valid = true;
		dependent.type = expression_object_type(binding->type);
		dependent.category = ValueCategory::PRValue;
		dependent.constant_expression = true;
		dependent.dependent_value_name = name.spelling;
		dependent.dependent_value_owner_template_name = name.name;
		dependent.dependent_value_owner_template_arguments =
			id_template_instance_arguments(name.template_arguments);
		dependent.node = Node("id-expression prvalue " +
		                      pa11::describe_type(dependent.type) + " " +
		                      name.spelling);
		dependent.node.token_text = name.spelling;
		annotate_expr_node(dependent);
		return dependent;
		}
		out.binding = binding;
		TypePtr resolved_binding_type = binding->type;
	if (binding->kind != BindingKind::Function &&
	    (!template_type_substitutions_.empty() ||
	     !template_value_substitutions_.empty()))
	{
		try {
			resolved_binding_type =
				substitute_template_type(resolved_binding_type);
		} catch (const runtime_error&) { }
	}
	out.type = expression_object_type(resolved_binding_type);
	if (binding->kind == BindingKind::Function)
		out.type = binding->type;
	out.category = binding->kind == BindingKind::Enumerator
		? ValueCategory::PRValue : ValueCategory::LValue;
	string spelling = name.qualified ? name.spelling : binding->name;
	out.node = Node("id-expression " + value_category_name(out.category) +
	                " " + pa11::describe_type(out.type) + " " + spelling);
	out.node.token_text = spelling;
	if (binding->has_constant)
	{
		out.constant_expression = true;
		out.has_constant_value = true;
		out.constant_value = binding->constant_value;
		out.null_pointer_constant = binding->constant_value == 0;
	}
	else if (!name.qualified &&
	         binding->kind == BindingKind::Variable &&
	         binding->is_static_member)
	{
		ConstexprValue value;
		if (try_evaluate_constexpr_binding(binding, value) &&
		    !value.is_object && !value.is_pointer)
		{
			out.constant_expression = true;
			out.has_constant_value = true;
			out.constant_value = value.int_value;
			out.null_pointer_constant = value.int_value == 0;
		}
	}
	annotate_expr_node(out);
	return out;
}
}  // namespace internal
}  // namespace pa12
