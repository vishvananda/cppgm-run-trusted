#include "pa12_internal.h"

using namespace std;

namespace pa12 {
namespace internal {
namespace {

bool array_redeclaration_compatible(TypePtr existing, TypePtr redeclared)
{
	TypePtr lhs = pa11::strip_cv(existing);
	TypePtr rhs = pa11::strip_cv(redeclared);
	if (lhs->kind == pa11::TypeKind::Array && rhs->kind == pa11::TypeKind::Array)
	{
		if (!lhs->unknown_bound && !rhs->unknown_bound &&
		    lhs->bound != rhs->bound)
			return false;
		return array_redeclaration_compatible(lhs->base, rhs->base);
	}
	return pa11::same_type(lhs, rhs);
}

bool type_contains_auto_placeholder(TypePtr type)
{
	if (type.get() == NULL)
		return false;
	TypePtr bare = pa11::strip_cv(type);
	if (bare->kind == pa11::TypeKind::Fundamental &&
	    bare->fundamental == FT_VOID)
		return true;
	if (type->kind == pa11::TypeKind::Cv)
		return type_contains_auto_placeholder(type->base);
	if (type->kind == pa11::TypeKind::Pointer ||
	    type->kind == pa11::TypeKind::LValueReference ||
	    type->kind == pa11::TypeKind::RValueReference ||
	    type->kind == pa11::TypeKind::Array)
		return type_contains_auto_placeholder(type->base);
	if (type->kind == pa11::TypeKind::Function)
	{
		if (type_contains_auto_placeholder(type->base))
			return true;
		for (size_t i = 0; i < type->parameters.size(); ++i)
			if (type_contains_auto_placeholder(type->parameters[i]))
				return true;
	}
	return false;
}

TypePtr expression_object_type_for_auto(TypePtr type)
{
	if (type->kind == pa11::TypeKind::LValueReference ||
	    type->kind == pa11::TypeKind::RValueReference)
		return type->base;
	return type;
}

TypePtr lvalue_to_rvalue_type_for_auto(TypePtr type)
{
	TypePtr object = expression_object_type_for_auto(type);
	if (object->kind == pa11::TypeKind::Array)
		return pa11::make_pointer(object->base);
	if (object->kind == pa11::TypeKind::Function)
		return pa11::make_pointer(object);
	return pa11::strip_top_level_cv(object);
}

TypePtr infer_auto_placeholder(TypePtr pattern, TypePtr source)
{
	if (pattern.get() == NULL || source.get() == NULL)
		throw runtime_error("invalid auto deduction");
	if (pattern->kind == pa11::TypeKind::Cv)
	{
		if (type_contains_auto_placeholder(pattern->base) &&
		    pa11::strip_cv(pattern->base)->kind == pa11::TypeKind::Fundamental &&
		    pa11::strip_cv(pattern->base)->fundamental == FT_VOID)
			return source;
		return infer_auto_placeholder(pattern->base, source);
	}
	if (pattern->kind == pa11::TypeKind::Fundamental &&
	    pattern->fundamental == FT_VOID)
		return source;
	if (pattern->kind == pa11::TypeKind::Pointer)
	{
		TypePtr src = pa11::strip_cv(source);
		if (src->kind != pa11::TypeKind::Pointer)
			throw runtime_error("invalid auto deduction");
		return infer_auto_placeholder(pattern->base, src->base);
	}
	if (pattern->kind == pa11::TypeKind::LValueReference ||
	    pattern->kind == pa11::TypeKind::RValueReference)
		return infer_auto_placeholder(pattern->base, source);
	if (pattern->kind == pa11::TypeKind::Array)
	{
		TypePtr src = pa11::strip_cv(source);
		if (src->kind != pa11::TypeKind::Array)
			throw runtime_error("invalid auto deduction");
		return infer_auto_placeholder(pattern->base, src->base);
	}
	if (!pa11::same_type(pa11::strip_cv(pattern), pa11::strip_cv(source)))
		throw runtime_error("invalid auto deduction");
	return source;
}

TypePtr replace_auto_placeholder(TypePtr pattern, TypePtr deduced)
{
	if (pattern->kind == pa11::TypeKind::Cv)
	{
		TypePtr bare = pa11::strip_cv(pattern->base);
		if (bare->kind == pa11::TypeKind::Fundamental &&
		    bare->fundamental == FT_VOID)
			return pa11::make_cv(deduced, pattern->cv);
		return pa11::make_cv(replace_auto_placeholder(pattern->base, deduced),
		                     pattern->cv);
	}
	if (pattern->kind == pa11::TypeKind::Fundamental &&
	    pattern->fundamental == FT_VOID)
		return deduced;
	if (pattern->kind == pa11::TypeKind::Pointer)
		return pa11::make_pointer(replace_auto_placeholder(pattern->base,
		                                                   deduced));
	if (pattern->kind == pa11::TypeKind::LValueReference)
		return pa11::make_lvalue_reference(
			replace_auto_placeholder(pattern->base, deduced));
	if (pattern->kind == pa11::TypeKind::RValueReference)
		return pa11::make_rvalue_reference(
			replace_auto_placeholder(pattern->base, deduced));
	if (pattern->kind == pa11::TypeKind::Array)
		return pa11::make_array(replace_auto_placeholder(pattern->base,
		                                                 deduced),
		                        pattern->unknown_bound,
		                        pattern->bound);
	return pattern;
}

TypePtr deduce_auto_variable_type(TypePtr declared,
                                  const Expr* init)
{
	if (init == NULL)
		throw runtime_error("auto declaration requires initializer");
	if (!type_contains_auto_placeholder(declared))
		return declared;
	bool lvalue_ref =
		declared->kind == pa11::TypeKind::LValueReference;
	bool rvalue_ref =
		declared->kind == pa11::TypeKind::RValueReference;
	TypePtr source = (lvalue_ref || rvalue_ref)
		? expression_object_type_for_auto(init->type)
		: lvalue_to_rvalue_type_for_auto(init->type);
	TypePtr pattern = declared;
	if (rvalue_ref && init->category == ValueCategory::LValue)
		pattern = declared->base;
	TypePtr deduced = infer_auto_placeholder(pattern, source);
	if (rvalue_ref && init->category == ValueCategory::LValue)
		return pa11::make_lvalue_reference(
			replace_auto_placeholder(declared->base, deduced));
	return replace_auto_placeholder(declared, deduced);
}

bool declarator_declares_function_type(const Declarator& declarator)
{
	for (size_t i = 0; i < declarator.suffixes.size(); ++i)
		if (declarator.suffixes[i].kind == SuffixKind::Function)
			return true;
	return declarator.inner.get() != NULL &&
	       declarator_declares_function_type(*declarator.inner);
}

TypePtr source_for_auto_declarator_base(const Declarator& declarator,
                                        const Expr* init)
{
	if (declarator.inner.get() != NULL)
		throw runtime_error("unsupported auto declarator");
	bool reference_decl = false;
	for (size_t i = 0; i < declarator.prefix.size(); ++i)
		if (declarator.prefix[i].kind == PtrKind::LValueReference ||
		    declarator.prefix[i].kind == PtrKind::RValueReference)
			reference_decl = true;
	TypePtr source = reference_decl
		? expression_object_type_for_auto(init->type)
		: lvalue_to_rvalue_type_for_auto(init->type);
	for (size_t i = declarator.prefix.size(); i > 0; --i)
	{
		const PtrOp& op = declarator.prefix[i - 1];
		if (op.kind == PtrKind::Pointer)
		{
			TypePtr ptr = pa11::strip_cv(source);
			if (ptr->kind != pa11::TypeKind::Pointer)
				throw runtime_error("invalid auto deduction");
			source = ptr->base;
		}
		else if (op.kind == PtrKind::MemberPointer)
		{
			TypePtr ptr = pa11::strip_cv(source);
			if (ptr->kind != pa11::TypeKind::MemberPointer)
				throw runtime_error("invalid auto deduction");
			source = ptr->base;
		}
	}
	return source;
}

bool declarator_has_forwarding_auto_ref(const Declarator& declarator)
{
	if (declarator.inner.get() != NULL)
		return false;
	for (size_t i = 0; i < declarator.prefix.size(); ++i)
		if (declarator.prefix[i].kind == PtrKind::RValueReference)
			return true;
	return false;
}

TypePtr apply_simple_auto_declarator(const Declarator& declarator, TypePtr type)
{
	if (declarator.inner.get() != NULL)
		throw runtime_error("unsupported auto declarator");
	for (size_t i = 0; i < declarator.prefix.size(); ++i)
	{
		const PtrOp& op = declarator.prefix[i];
		if (op.kind == PtrKind::Pointer)
			type = pa11::make_cv(pa11::make_pointer(type), op.cv);
		else if (op.kind == PtrKind::LValueReference)
			type = pa11::make_lvalue_reference(type);
		else if (op.kind == PtrKind::RValueReference)
			type = pa11::make_rvalue_reference(type);
		else
			type = pa11::make_cv(pa11::make_member_pointer(op.member_class,
			                                               type),
			                     op.cv);
	}
	for (size_t i = declarator.suffixes.size(); i > 0; --i)
	{
		const Suffix& suffix = declarator.suffixes[i - 1];
		if (suffix.kind == SuffixKind::Array)
			type = pa11::make_array(type, suffix.unknown_bound, suffix.bound);
		else
			throw runtime_error("unsupported auto declarator");
	}
	return type;
}

TypePtr deduce_auto_declared_type(TypePtr base,
                                  const Declarator& declarator,
                                  const Expr* init)
{
	if (init == NULL)
		throw runtime_error("auto declaration requires initializer");
	TypePtr deduced_base =
		replace_auto_placeholder(base,
		                         source_for_auto_declarator_base(declarator,
		                                                         init));
	TypePtr type = apply_simple_auto_declarator(declarator, deduced_base);
	if (declarator_has_forwarding_auto_ref(declarator) &&
	    init->category == ValueCategory::LValue &&
	    type->kind == pa11::TypeKind::RValueReference)
		return pa11::make_lvalue_reference(type->base);
	return type;
}

}  // namespace

Binding* Parser::declare_one(const DeclSpecs& specs,
                             TypePtr base,
                             const Declarator& declarator,
                             const Expr* init,
                             bool function_definition,
                             Node& out)
{ Expr lambda_closure_init; if (specs.auto_decl && init != NULL &&
is_lambda_helper_expr(*init) && ((specs.cv != pa11::CV_NONE) ||
specs.constexpr_decl || lambda_requires_closure_object_.count(init->binding) != 0)) { lambda_closure_init = lambda_closure_expr(*init); init = &lambda_closure_init; }
const QualifiedName& qname = declarator_name(declarator); Scope* target = qname.qualifier != NULL ? qname.qualifier : current_scope(); Scope* friend_class_scope =
specs.friend_decl && current_scope()->kind == ScopeKind::Class ? current_scope() : NULL; bool hidden_friend = friend_class_scope != NULL && qname.qualifier == NULL;
if (friend_class_scope != NULL && qname.qualifier == NULL) target = nearest_namespace_scope(friend_class_scope); bool auto_function_declarator = specs.auto_decl && declarator_declares_function_type(declarator);
TypePtr type = specs.auto_decl && init != NULL && !auto_function_declarator ? deduce_auto_declared_type(base, declarator, init) : apply_declarator(declarator, auto_function_declarator ?
pa11::make_cv(pa11::make_fundamental(FT_INT), specs.cv) : base); if (specs.auto_decl && type->kind != pa11::TypeKind::Function && !function_definition) type =
deduce_auto_variable_type(type, init); if (specs.typedef_decl) {
if (type.get() != NULL && type->is_dependent_typename) { TypePtr resolved = resolve_dependent_typename_type(type); if (resolved.get() != NULL && resolved != type) type = substitute_template_type(resolved); }
Binding* alias = add_alias(target, qname.name, type); add_child(out, Node("type-alias " + qname.name + " " + pa11::describe_type(alias->type))); return alias; } if (specs.constexpr_decl &&
!pa11::is_reference_type(type) && type->kind != pa11::TypeKind::Function) type = pa11::make_cv(type, pa11::CV_CONST); if (init != NULL && type->kind == pa11::TypeKind::Array && type->unknown_bound) { uint64_t elements = 0;
if (string_literal_initializes_array(type, *init, &elements)) type = pa11::make_array(type->base, false, elements); else if (init->braced_init_list && init->node.children.size() == 1) { Expr child;
child.valid = true; child.node = init->node.children[0]; child.type = child.node.type; child.category = child.node.category; if (string_literal_initializes_array(type, child, &elements)) type =
pa11::make_array(type->base, false, elements); else type = pa11::make_array(type->base, false, init->node.children.size()); } else if (init->braced_init_list) type = pa11::make_array(type->base, false,
init->node.children.size()); } bool existing_static_member_function = false; if (target->kind == ScopeKind::Class &&
type->kind == pa11::TypeKind::Function && !specs.static_decl) { TypePtr substituted_type; if (qname.qualifier != NULL) { try { substituted_type = substitute_template_type(type); } catch (const exception&) {
substituted_type.reset(); } } map<string, vector<Binding*> >::iterator found = target->members.find(qname.name); if (found != target->members.end()) for (size_t i = 0; i < found->second.size(); ++i) {
Binding* candidate = found->second[i]; if (candidate->kind == BindingKind::Function && candidate->is_static_member && (pa11::same_type(candidate->type, type) || (substituted_type.get() != NULL &&
pa11::same_type(candidate->type, substituted_type)) || (qname.qualifier != NULL && function_template_placeholders_.find(candidate) != function_template_placeholders_.end()))) { existing_static_member_function = true;
break; } } } bool nonstatic_member_function = target->kind == ScopeKind::Class && type->kind == pa11::TypeKind::Function && !specs.static_decl && !existing_static_member_function; if (nonstatic_member_function)
type = make_member_function_type(target, type); if (type->kind == pa11::TypeKind::Function || function_definition) { Binding* function = declare_function_entity(specs, target, qname.name, type, declarator,
function_definition, nonstatic_member_function, hidden_friend, out); if (specs.friend_decl && friend_class_scope != NULL) add_friend_function(friend_class_scope, function); return function; } Binding* variable = NULL;
if ((target->kind == ScopeKind::Namespace || target->kind == ScopeKind::Class) && (qname.qualifier != NULL || target->kind == ScopeKind::Namespace)) { Binding* existing =
pa11::find_owned_binding(target, qname.name, BindingKind::Variable); if (existing != NULL && (pa11::same_type(existing->type, type) || array_redeclaration_compatible(existing->type, type))) { variable = existing;
type = existing->type; } } if (variable == NULL) variable = add_value(target, BindingKind::Variable, qname.name, type); if (target->kind == ScopeKind::Class && pa11::is_reference_type(pa11::strip_cv(type)))
variable->is_reference_member = true; return finish_variable_declaration(specs, target, variable, qname, type, init, out); }

}  // namespace internal
}  // namespace pa12
