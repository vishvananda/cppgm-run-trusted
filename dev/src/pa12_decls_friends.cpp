#include "pa12_internal.h"
#include <stdexcept>

using namespace std;

namespace pa12 {
namespace internal {

bool Parser::parse_friend_declaration()
{
	if (current_scope()->kind != ScopeKind::Class || !at(KW_FRIEND))
		return false;
	Scope* class_scope = current_scope();
	expect(KW_FRIEND);
	if (starts_class_key())
	{
		ETokenType key = current().type;
		++pos_;
		QualifiedName name = parse_id_expression_name();
		if (at(OP_LT) && !name.has_template_arguments)
		{
			name.has_template_arguments = true;
			parse_template_argument_list(name.template_arguments);
		}
		Scope* target = name.qualifier != NULL
			? name.qualifier : nearest_namespace_scope(class_scope);
		TypePtr friend_type;
		if (name.has_template_arguments)
		{
			TemplateDeclaration* class_template = NULL;
			if (name.qualifier == NULL)
				class_template = find_class_template(class_scope,
				                                     name.name);
			if (class_template == NULL)
				class_template = find_class_template(target, name.name);
			if (class_template != NULL)
				friend_type = instantiate_class_template(
					class_template,
					name.template_arguments);
		}
		if (friend_type.get() == NULL)
		{
			vector<Binding*> found = name.qualifier != NULL
				? lookup_qualified_set(target,
				                       name.name,
				                       pa11::LOOKUP_TYPE)
				: lookup_unqualified_set(class_scope,
				                         name.name,
				                         pa11::LOOKUP_TYPE);
			if (!found.empty() &&
			    found[0]->type.get() != NULL &&
			    pa11::strip_cv(found[0]->type)->kind ==
			    pa11::TypeKind::Record)
				friend_type = found[0]->type;
		}
		if (friend_type.get() == NULL)
			friend_type = add_record(target,
			                         name.name,
			                         class_tag(key),
			                         false,
			                         NULL);
		add_friend_class(class_scope, friend_type);
		expect(OP_SEMICOLON);
		return true;
	}
	if (at(KW_TYPENAME))
	{
		TypePtr friend_type;
		if (!try_parse_type_name(friend_type))
			throw runtime_error("invalid friend type declaration");
		add_friend_class(class_scope, friend_type);
		expect(OP_SEMICOLON);
		return true;
	}

	DeclSpecs specs = parse_decl_specifier_seq(false);
	specs.friend_decl = true;
	TypePtr base = type_from_decl_specs(specs);
	Declarator declarator = parse_declarator(false);
	TypePtr type = apply_declarator(declarator, base);
	if (type->kind != pa11::TypeKind::Function)
		throw runtime_error("unsupported friend declaration");
	const QualifiedName& qname = declarator_name(declarator);
	Scope* target = qname.qualifier != NULL
		? qname.qualifier : nearest_namespace_scope(class_scope);
	Binding* function =
		add_function_binding(target, qname.name, type, !qname.qualified);
	function->language_linkage = current_language_linkage();
	function->is_constexpr = function->is_constexpr || specs.constexpr_decl;
	const Suffix* suffix = declarator_function_suffix(declarator);
	function->unwind_no = suffix != NULL && suffix->noexcept_decl;
	function->dynamic_exception_spec =
		suffix != NULL && suffix->dynamic_exception_spec;
	if (suffix != NULL)
		function->dynamic_exception_types =
			suffix->dynamic_exception_types;
	function->ref_qualifier = suffix != NULL ? suffix->ref_qualifier : 0;
	if (pa11::strip_cv(type->base)->kind == pa11::TypeKind::Record &&
	    pa11::strip_cv(type->base)->scope != NULL)
		ensure_default_destructor(type->base);
	for (size_t i = 0; i < type->parameters.size(); ++i)
	{
		TypePtr param = pa11::strip_cv(type->parameters[i]);
		if (param->kind == pa11::TypeKind::Record && param->scope != NULL)
			ensure_default_destructor(type->parameters[i]);
	}
	if (qname.has_template_arguments)
	{
		Scope* lookup_target = target;
		if (lookup_target != NULL &&
		    lookup_target->kind == ScopeKind::Namespace)
		{
			for (Scope* cur = lookup_target;
			     cur != NULL && cur->kind == ScopeKind::Namespace;
			     cur = cur->parent)
			{
				if (cur != lookup_target && cur->name != lookup_target->name)
					break;
				map<Scope*, map<string, vector<TemplateDeclaration*> > >::iterator
					sit = function_templates_.find(cur);
				if (sit != function_templates_.end() &&
				    sit->second.find(qname.name) != sit->second.end())
				{
					lookup_target = cur;
					break;
				}
			}
		}
		QualifiedName template_name = qname;
		if (template_name.qualifier == NULL)
			template_name.qualifier = lookup_target;
		vector<TemplateDeclaration*> templates =
			find_function_templates(template_name);
		TemplateDeclaration* selected = NULL;
		vector<TemplateArgument> selected_args;
		for (size_t i = 0; i < templates.size(); ++i)
		{
			vector<TemplateArgument> full_args;
			if (!deduce_function_template_target_type(
				    templates[i],
				    type,
				    qname.template_arguments,
				    full_args))
				continue;
			bool selected_declaration =
				selected != NULL && !selected->has_definition;
			bool candidate_declaration = !templates[i]->has_definition;
			if (selected == NULL ||
			    (!selected_declaration && candidate_declaration))
			{
				selected = templates[i];
				selected_args = full_args;
				continue;
			}
			if (selected_declaration != candidate_declaration)
				continue;
			throw runtime_error("ambiguous friend function template");
			}
				if (selected == NULL || selected->placeholder == NULL)
					throw runtime_error("function template not found");
			add_friend_function(class_scope, selected->placeholder);
		if (!selected->has_definition)
		{
			Binding* specialization =
				instantiate_function_template(selected, selected_args);
			add_friend_function(class_scope, specialization);
		}
		expect(OP_SEMICOLON);
		return true;
	}
	if (suffix != NULL)
	{
		vector<Expr> defaults;
		vector<string> names;
		for (size_t i = 0; i < suffix->parameters.size(); ++i)
		{
			defaults.push_back(suffix->parameters[i].default_value);
			names.push_back(suffix->parameters[i].name);
		}
		default_arguments_[function] = defaults;
		function_parameter_names_[function] = names;
	}
	add_friend_function(class_scope, function);

	if (at(OP_LBRACE))
	{
		function->is_inline_definition = true;
		Node node;
		Node fn("function-definition " + qualified_decl_name(function) + " " +
		        pa11::describe_type(type));
		fn.binding = function;
		fn.type = type;
		add_child(node, fn);
		PendingFunctionBody pending;
		pending.function = function;
		pending.node = node.children.back();
		if (suffix != NULL)
			pending.parameters = suffix->parameters;
		pending.body_pos = pos_;
		skip_balanced(OP_LBRACE, OP_RBRACE);
		enqueue_pending_member_body(class_scope, pending);
		return true;
	}
	expect(OP_SEMICOLON);
	return true;
}


}  // namespace internal
}  // namespace pa12
