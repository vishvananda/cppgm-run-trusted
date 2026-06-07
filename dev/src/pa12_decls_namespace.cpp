#include "pa12_internal.h"

#include <algorithm>
#include <stdexcept>

using namespace std;

namespace pa12 {
namespace internal {

void Parser::parse_namespace_or_alias(Node& out)
{
	bool inline_ns = consume(KW_INLINE);
	expect(KW_NAMESPACE);
	if (!inline_ns && at_identifier() && lookahead(OP_ASS, 1))
	{
		string alias = consume_identifier();
		expect(OP_ASS);
		Scope* target = parse_qualified_namespace_specifier();
		expect(OP_SEMICOLON);
		pa11::add_namespace_alias(current_scope(), alias, target);
		return;
	}

	string name;
	bool named = false;
	if (at_identifier())
	{
		named = true;
		name = consume_identifier();
	}
	expect(OP_LBRACE);
	Scope* child = NULL;
	if (named)
		child = pa11::get_or_create_namespace(current_scope(), name, inline_ns);
	else
	{
		if (current_scope()->unnamed_namespace == NULL)
		{
			current_scope()->unnamed_namespace =
				pa11::create_child_scope(current_scope(),
				                         ScopeKind::Namespace,
				                         "<unnamed>");
			pa11::add_using_directive(current_scope(),
			                          current_scope()->unnamed_namespace);
		}
		child = current_scope()->unnamed_namespace;
		name = "<unnamed>";
	}

	Node node("namespace-definition " + name);
	scopes_.push_back(child);
	while (!at(OP_RBRACE))
		parse_declaration_into(node);
	scopes_.pop_back();
	expect(OP_RBRACE);
	add_child(out, node);
}

void Parser::parse_using_family(Node& out)
{
	expect(KW_USING);
	if (consume(KW_NAMESPACE))
	{
		Scope* target = parse_qualified_namespace_specifier();
		expect(OP_SEMICOLON);
		pa11::add_using_directive(current_scope(), target);
		return;
	}
	if (at_identifier() && lookahead(OP_ASS, 1))
	{
		string name = consume_identifier();
		TypePtr shadowed_template_parameter;
		if (find_template_type_substitution(name, shadowed_template_parameter))
			throw runtime_error("alias shadows template parameter");
		expect(OP_ASS);
		TypePtr type = parse_type_id();
		if (type.get() != NULL && type->is_dependent_typename)
		{
			TypePtr resolved = resolve_dependent_typename_type(type);
			if (resolved.get() != NULL && resolved != type)
				type = substitute_template_type(resolved);
		}
		expect(OP_SEMICOLON);
		add_alias(current_scope(), name, type);
		Node node("type-alias " + name + " " + pa11::describe_type(type));
		add_child(out, node);
		return;
	}
	bool using_typename = consume(KW_TYPENAME);
	string spelling;
	Scope* qualifier = parse_nested_name_specifier(&spelling);
	string name = at(KW_OPERATOR)
		? consume_operator_function_name()
		: consume_identifier();
	expect(OP_SEMICOLON);
	vector<Binding*> targets =
		lookup_qualified_set(qualifier,
		                     name,
		                     using_typename ? pa11::LOOKUP_TYPE :
		                     pa11::LOOKUP_ANY);
	if (targets.empty() &&
	    current_scope()->kind == ScopeKind::Class &&
	    qualifier->kind == ScopeKind::Class)
	{
		vector<Binding*> ctors =
			lookup_qualified_set(qualifier,
			                     qualifier->name,
			                     pa11::LOOKUP_FUNCTION);
		if (!ctors.empty())
		{
			targets = ctors;
			name = qualifier->name;
		}
	}
	if (targets.empty())
	{
		TemplateDeclaration* class_template = find_class_template(qualifier, name);
		if (class_template != NULL)
		{
			class_templates_[current_scope()][name] = class_template;
			return;
		}
		QualifiedName qname;
		qname.qualifier = qualifier;
		qname.name = name;
		qname.qualified = true;
		vector<TemplateDeclaration*> function_template =
			find_function_templates(qname);
		if (!function_template.empty())
		{
			function_templates_[current_scope()][name] = function_template;
			return;
		}
		TypePtr qualifier_record =
			qualifier != NULL ? pa11::record_type_for_scope(qualifier) :
			TypePtr();
		if (validating_template_definition_ &&
		    qualifier_record.get() != NULL &&
		    type_is_template_dependent(qualifier_record))
			return;
		throw runtime_error("using declaration target not found");
	}
	if (current_scope()->kind == ScopeKind::Class &&
	    qualifier->kind == ScopeKind::Class &&
	    name == qualifier->name)
	{
			TypePtr derived = pa11::record_type_for_scope(current_scope());
			TypePtr base = pa11::record_type_for_scope(qualifier);
			if (derived.get() == NULL || base.get() == NULL)
				throw runtime_error("invalid inheriting constructor");
			for (size_t i = 0; i < targets.size(); ++i)
			{
				Binding* inherited = targets[i];
				if (inherited->kind != BindingKind::Function ||
				    inherited->type->parameters.empty())
					continue;
				map<Binding*, TemplateDeclaration*>::iterator inherited_template =
					function_template_placeholders_.find(inherited);
				if (inherited_template != function_template_placeholders_.end())
				{
					vector<TypePtr> params;
					params.push_back(pa11::make_pointer(derived));
					for (size_t j = 1; j < inherited->type->parameters.size(); ++j)
						params.push_back(inherited->type->parameters[j]);
					TypePtr fn_type =
						pa11::make_function(pa11::make_fundamental(FT_VOID),
						                    params,
						                    inherited->type->variadic);
					Binding* ctor = add_value(current_scope(),
					                          BindingKind::Function,
					                          current_scope()->name,
					                          fn_type);
					ctor->is_explicit = inherited->is_explicit;
					ctor->unwind_no = inherited->unwind_no;
					map<Binding*, vector<string> >::const_iterator nit =
						function_parameter_names_.find(inherited);
					vector<string> inherited_names =
						nit != function_parameter_names_.end()
						? nit->second : vector<string>();
					vector<string> ctor_names(1, "this");
					for (size_t j = 1; j < params.size(); ++j)
					{
						string pname = j < inherited_names.size() &&
						               !inherited_names[j].empty()
							? inherited_names[j]
							: "__param" + to_string(j);
						ctor_names.push_back(pname);
					}
					function_parameter_names_[ctor] = ctor_names;
					unique_ptr<TemplateDeclaration> holder(
						new TemplateDeclaration());
					TemplateDeclaration* declaration = holder.get();
					declaration->kind = TemplateDeclarationKind::Function;
					declaration->owner = current_scope();
					declaration->lexical_scope = current_scope();
					declaration->name = current_scope()->name;
					declaration->parameters =
						inherited_template->second->parameters;
					declaration->has_definition = true;
					declaration->constructor_template = true;
					declaration->generic_function_type = fn_type;
					declaration->placeholder = ctor;
					declaration->inherited_constructor_base = inherited;
					declaration->inherited_constructor_base_type = base;
					template_declarations_.push_back(std::move(holder));
					function_template_placeholders_[ctor] = declaration;
					vector<TemplateDeclaration*>& overloads =
						function_templates_[current_scope()][current_scope()->name];
					if (find(overloads.begin(), overloads.end(), declaration) ==
					    overloads.end())
						overloads.push_back(declaration);
					TypePtr owner_record =
						pa11::record_type_for_scope(current_scope());
					owner_record = owner_record.get() != NULL
						? pa11::strip_cv(owner_record) : TypePtr();
					map<const void*, TemplateDeclaration*>::iterator owner_template =
						owner_record.get() != NULL
						? record_template_declarations_.find(
							owner_record.get())
						: record_template_declarations_.end();
					if (owner_template != record_template_declarations_.end())
					{
						vector<TemplateDeclaration*>& member_overloads =
							member_function_templates_[make_pair(
								owner_template->second,
								current_scope()->name)];
						if (find(member_overloads.begin(),
						         member_overloads.end(),
						         declaration) == member_overloads.end())
							member_overloads.push_back(declaration);
					}
					continue;
				}
				parse_pending_function_body(inherited);
				parse_pending_member_body(inherited);
				vector<TypePtr> params;
				params.push_back(pa11::make_pointer(derived));
				for (size_t j = 1; j < inherited->type->parameters.size(); ++j)
					params.push_back(inherited->type->parameters[j]);
				TypePtr fn_type = pa11::make_function(pa11::make_fundamental(FT_VOID),
				                                      params,
				                                      inherited->type->variadic);
				Binding* ctor = add_value(current_scope(),
				                          BindingKind::Function,
				                          current_scope()->name,
				                          fn_type);
				map<Binding*, vector<string> >::const_iterator nit =
					function_parameter_names_.find(inherited);
				vector<string> inherited_names =
					nit != function_parameter_names_.end()
					? nit->second : vector<string>();
				vector<string> ctor_names(1, "this");
				ctor->is_inline_definition = true;
				Node fn("function-definition " + qualified_decl_name(ctor) + " " +
				        pa11::describe_type(fn_type));
				fn.binding = ctor;
				fn.type = fn_type;
				Scope* function_scope =
					pa11::create_child_scope(current_scope(),
					                         ScopeKind::Function,
					                         ctor->name);
				Binding* this_binding =
					pa11::add_binding(function_scope,
					                  BindingKind::Parameter,
					                  "this",
					                  params[0]);
				Node this_node("parameter this " + pa11::describe_type(params[0]));
				this_node.binding = this_binding;
				this_node.type = params[0];
				add_child(fn, this_node);
				Node init("braced-init-list");
				for (size_t j = 1; j < params.size(); ++j)
				{
					string pname = j < inherited_names.size() &&
					               !inherited_names[j].empty()
						? inherited_names[j] : "__param" + to_string(j);
					ctor_names.push_back(pname);
					Binding* param =
						pa11::add_binding(function_scope,
						                  BindingKind::Parameter,
						                  pname,
						                  params[j]);
					Node param_node("parameter " + pname + " " +
					                pa11::describe_type(params[j]));
					param_node.binding = param;
					param_node.type = params[j];
					add_child(fn, param_node);
					Node arg("id-expression lvalue " +
					         pa11::describe_type(params[j]) + " " + pname);
					arg.binding = param;
					arg.type = params[j];
					arg.category = ValueCategory::LValue;
					add_child(init, arg);
				}
				Node body("compound-statement");
				Node base_action = make_base_init_action(base, &init);
				base_action.direct_call = inherited;
				base_action.token_text = "inherited-constructor";
				add_child(body, base_action);
				add_child(fn, body);
				function_parameter_names_[ctor] = ctor_names;
				extra_lowir_nodes_.push_back(fn);
			}
			return;
		}
	for (size_t i = 0; i < targets.size(); ++i)
	{
		Binding* imported =
			pa11::add_using_declaration(current_scope(), name, targets[i]);
		map<Binding*, TemplateDeclaration*>::iterator templ =
			function_template_placeholders_.find(targets[i]);
		if (templ != function_template_placeholders_.end())
		{
			function_template_placeholders_[imported] = templ->second;
			vector<TemplateDeclaration*>& overloads =
				function_templates_[current_scope()][name];
			if (find(overloads.begin(), overloads.end(), templ->second) ==
			    overloads.end())
				overloads.push_back(templ->second);
		}
	}
}

void Parser::parse_linkage_specification(Node& out)
{
	expect(KW_EXTERN);
	string language = current_language_linkage();
	if (at_literal())
	{
		if (current().source == "\"C\"")
			language = "c";
		else if (current().source == "\"C++\"")
			language = "cpp";
		++pos_;
	}
	if (consume(OP_LBRACE))
	{
		language_linkages_.push_back(language);
		while (!at(OP_RBRACE))
			parse_declaration_into(out);
		language_linkages_.pop_back();
		expect(OP_RBRACE);
		return;
	}
	language_linkages_.push_back(language);
	parse_simple_or_function_declaration(out, true);
	language_linkages_.pop_back();
}

}  // namespace internal
}  // namespace pa12
