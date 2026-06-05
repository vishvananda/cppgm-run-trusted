#include "pa12_internal.h"

#include <stdexcept>

using namespace std;

namespace pa12 {
namespace internal {
namespace {

Expr make_this_id_expr(Binding* binding)
{
	Expr out;
	out.binding = binding;
	out.type = binding->type;
	out.category = ValueCategory::LValue;
	out.valid = true;
	out.node = Node("id-expression lvalue " + pa11::describe_type(out.type) +
	                " this");
	annotate_expr_node(out);
	return out;
}

Expr make_constant_binding_expr(Binding* binding, TypePtr type)
{
	Expr out;
	out.binding = binding;
	out.type = type;
	out.category = ValueCategory::PRValue;
	out.valid = true;
	out.constant_expression = true;
	out.has_constant_value = true;
	out.constant_value = binding->constant_value;
	out.null_pointer_constant = binding->constant_value == 0;
	out.node = Node("literal prvalue " + pa11::describe_type(out.type) +
	                " " + to_string(binding->constant_value));
	out.node.binding = binding;
	out.node.token_text = to_string(binding->constant_value);
	annotate_expr_node(out);
	return out;
}

bool equivalent_nonfunction_binding(Binding* a, Binding* b)
{
	if (a == b)
		return true;
	if (a == NULL || b == NULL)
		return false;
	if (a->kind == BindingKind::Function || b->kind == BindingKind::Function)
		return false;
	return a->kind == b->kind &&
	       a->owner == b->owner &&
	       a->name == b->name &&
	       a->target_scope == b->target_scope &&
	       a->aliased_binding == b->aliased_binding &&
	       pa11::same_type(a->type, b->type);
}

}  // namespace

Expr Parser::make_implicit_member_id_expr(const QualifiedName& name,
                                          const vector<Binding*>& found,
                                          Binding* binding,
                                          Binding* this_binding,
                                          const map<Binding*, vector<TemplateArgument> >*
                                              explicit_template_arguments)
{
	if ((!name.qualified ||
	     (name.qualifier != NULL && name.qualifier->kind == ScopeKind::Class)) &&
	    this_binding != NULL &&
	    binding->owner != NULL &&
	    binding->owner->kind == ScopeKind::Class &&
	    !binding->is_static_member)
	{
		Expr this_expr = make_this_id_expr(this_binding);
		if (name.qualified)
		{
			TypePtr this_type =
				pa11::strip_cv(expression_object_type(this_binding->type));
			TypePtr object_type = this_type->kind == pa11::TypeKind::Pointer
				? this_type->base : TypePtr();
			TypePtr object_record = object_type.get() != NULL
				? pa11::strip_cv(object_type) : TypePtr();
			if (!member_access_allowed(binding, object_record))
			{
				if (binding->is_private)
					throw runtime_error("private member access");
				throw runtime_error("protected member access");
			}
			Expr object_expr = make_deref_expr("*", this_expr);
			TypePtr qualifier_record =
				pa11::record_type_for_scope(name.qualifier);
			qualifier_record = qualifier_record.get() != NULL
				? pa11::strip_cv(qualifier_record) : TypePtr();
			if (qualifier_record.get() != NULL &&
			    object_record.get() != NULL &&
			    !pa11::same_type(object_record, qualifier_record) &&
			    record_base_distance(object_record, qualifier_record) < 1000000)
			{
				Expr base_expr;
				base_expr.valid = true;
				base_expr.type = qualifier_record;
				base_expr.category = ValueCategory::LValue;
				base_expr.node = Node("base-subobject-expression lvalue " +
				                      pa11::describe_type(qualifier_record));
				base_expr.node.type = qualifier_record;
				base_expr.node.category = ValueCategory::LValue;
				add_child(base_expr.node, object_expr.node);
				annotate_expr_node(base_expr);
				object_expr = base_expr;
			}
			Expr member;
			member.valid = true;
			member.binding = binding;
			member.type = binding->type;
			member.category = ValueCategory::LValue;
				if (binding->kind == BindingKind::Function)
				{
					for (size_t i = 0; i < found.size(); ++i)
						if (found[i]->kind == BindingKind::Function)
						{
							member.overloads.push_back(found[i]);
							if (explicit_template_arguments != NULL)
							{
								map<Binding*, vector<TemplateArgument> >::const_iterator
									eit = explicit_template_arguments->find(found[i]);
								if (eit != explicit_template_arguments->end())
									member.explicit_template_arguments[found[i]] =
										eit->second;
							}
						}
				}
			else if (object_type.get() != NULL &&
			         pa11::type_has_const(object_type) &&
			         !binding->is_mutable_member)
				member.type = pa11::make_cv(member.type, pa11::CV_CONST);
			member.node = Node("member-expression lvalue " +
			                   pa11::describe_type(member.type) +
			                   " OP_DOT:" + binding->name);
			add_child(member.node, object_expr.node);
			member.node.binding = binding;
			member.node.has_op = true;
			member.node.op = OP_DOT;
			member.node.token_text = binding->name;
			member.node.suppress_virtual_dispatch = true;
			annotate_expr_node(member);
			return member;
		}
		return make_member_expr(this_expr, binding->name, "->");
	}
	return Expr();
}

void Parser::synthesize_default_assignment_lookup(const QualifiedName& name,
                                                  vector<Binding*>& found)
{
	if (!found.empty() ||
	    !name.qualified ||
	    name.qualifier == NULL ||
	    name.qualifier->kind != ScopeKind::Class ||
	    name.name != "operator=")
		return;
	TypePtr record = pa11::record_type_for_scope(name.qualifier);
	if (record.get() == NULL)
		return;
	vector<TypePtr> params;
	params.push_back(pa11::make_pointer(record));
	params.push_back(
		pa11::make_lvalue_reference(pa11::make_cv(record, pa11::CV_CONST)));
	TypePtr fn_type =
		pa11::make_function(pa11::make_lvalue_reference(record),
		                    params,
		                    false);
	found.push_back(add_value(name.qualifier,
	                          BindingKind::Function,
	                          "operator=",
	                          fn_type));
}

Expr Parser::make_missing_id_expr(const QualifiedName& name)
{
	Binding* this_binding =
		pa11::lookup_unqualified(current_scope(), "this", pa11::LOOKUP_PARAMETER);
	Binding* active = active_functions_.empty() ? NULL : active_functions_.back();
	Scope* active_class =
		active != NULL && active->owner != NULL &&
		active->owner->kind == ScopeKind::Class ? active->owner : NULL;
	if (!name.qualified && this_binding != NULL && active_class != NULL)
	{
		vector<Binding*> members =
			lookup_qualified_set(active_class, name.name, pa11::LOOKUP_VALUE);
		if (!members.empty())
		{
			Expr member =
				make_implicit_member_id_expr(name,
				                             members,
				                             members[0],
				                             this_binding);
			if (member.valid)
				return member;
		}
	}
	if (!name.qualified && active_class != NULL)
	{
		vector<Binding*> members =
			lookup_qualified_set(active_class, name.name, pa11::LOOKUP_VALUE);
		if (!members.empty())
		{
			TypePtr class_type = pa11::record_type_for_scope(active_class);
			if (class_type.get() != NULL)
			{
				Expr this_expr;
				this_expr.valid = true;
				this_expr.type = pa11::make_pointer(class_type);
				this_expr.category = ValueCategory::LValue;
				this_expr.node = Node("id-expression lvalue " +
				                      pa11::describe_type(this_expr.type) +
				                      " this");
				annotate_expr_node(this_expr);
				return make_member_expr(this_expr, name.name, "->");
			}
		}
	}
	string near_token = pos_ < tokens_.size() ? tokens_[pos_].source :
	                    string("<eof>");
	throw runtime_error("name not found: " + name.spelling +
	                    " near '" + near_token + "'");
}

Expr Parser::make_aliased_member_variable_id_expr(Binding* binding)
{
	Binding* storage = binding->aliased_binding;
	Expr out;
	out.valid = true;
	out.binding = binding;
	out.type = binding->type;
	out.category = ValueCategory::LValue;
	out.node = Node("member-expression lvalue " +
	                pa11::describe_type(out.type) + " " + binding->name);
	TypePtr storage_type = expression_object_type(storage->type);
	add_child(out.node,
	          Node("id-expression lvalue " +
	               pa11::describe_type(storage_type) + " " +
	               storage->name));
	out.node.binding = binding;
	annotate_expr_node(out);
	return out;
}

Expr Parser::make_enumerator_id_expr(Binding* binding)
{
	Expr out;
	out.valid = true;
	out.binding = binding;
	out.type = binding->type;
	out.category = ValueCategory::PRValue;
	out.node = Node("literal prvalue " + pa11::describe_type(out.type) +
	                " " + to_string(binding->constant_value));
	out.constant_expression = true;
	out.has_constant_value = true;
	out.constant_value = binding->constant_value;
	out.null_pointer_constant = binding->constant_value == 0;
	out.node.binding = binding;
	out.node.token_text = to_string(binding->constant_value);
	annotate_expr_node(out);
	return out;
}

void Parser::prefer_static_qualified_overloads(const QualifiedName& name,
                                               Expr& out,
                                               Binding*& binding)
{
	if (!name.qualified ||
	    name.qualifier == NULL ||
	    name.qualifier->kind != ScopeKind::Class ||
	    out.overloads.empty() ||
	    pa11::lookup_unqualified(current_scope(), "this", pa11::LOOKUP_PARAMETER) != NULL)
		return;
	vector<Binding*> static_overloads;
	for (size_t i = 0; i < out.overloads.size(); ++i)
		if (out.overloads[i]->is_static_member)
			static_overloads.push_back(out.overloads[i]);
	if (static_overloads.empty())
		return;
	out.overloads = static_overloads;
	binding = out.overloads[0];
}

Expr Parser::make_template_substitution_id_expr(const QualifiedName& name)
{
	if (name.qualified || name.has_template_arguments)
		return Expr();
	vector<Binding*> parameter_pack;
	if (find_function_parameter_pack_substitution(name.name,
	                                              parameter_pack))
	{
		Expr out;
		out.valid = true;
		out.pack_expansion = true;
		out.type = parameter_pack.empty()
			? pa11::make_fundamental(FT_INT)
			: parameter_pack[0]->type;
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
			? pa11::make_fundamental(FT_INT)
			: value_arg.pack[0].type;
		out.category = ValueCategory::PRValue;
		out.node = Node("pack-expression " + name.name);
		for (size_t i = 0; i < value_arg.pack.size(); ++i)
		{
			if (value_arg.pack[i].kind != TemplateArgumentKind::Value)
				throw runtime_error("value pack required");
			Expr elem;
			elem.valid = true;
			elem.type = value_arg.pack[i].type.get() != NULL
				? value_arg.pack[i].type
				: pa11::make_fundamental(FT_INT);
			elem.category = ValueCategory::PRValue;
			elem.constant_expression = true;
			elem.has_constant_value = true;
			elem.constant_value = value_arg.pack[i].dependent
				? 1 : value_arg.pack[i].value;
			elem.node = Node("literal prvalue " +
			                 pa11::describe_type(elem.type) + " " +
			                 to_string(elem.constant_value));
			elem.node.token_text = to_string(elem.constant_value);
			annotate_expr_node(elem);
			out.pack.push_back(elem);
			add_child(out.node, elem.node);
		}
		annotate_expr_node(out);
		return out;
	}
	if (value_arg.kind == TemplateArgumentKind::Value)
	{
		Expr out;
		out.valid = true;
		out.type = value_arg.type.get() != NULL
			? value_arg.type : pa11::make_fundamental(FT_INT);
		out.category = ValueCategory::PRValue;
		out.constant_expression = true;
		out.has_constant_value = true;
		out.constant_value = value_arg.dependent ? 1 : value_arg.value;
		out.null_pointer_constant = out.constant_value == 0;
		out.node = Node("literal prvalue " +
		                pa11::describe_type(out.type) + " " +
		                to_string(out.constant_value));
		out.node.token_text = to_string(out.constant_value);
		annotate_expr_node(out);
		return out;
	}
	return Expr();
}

vector<Binding*> Parser::resolve_id_expr_bindings(
	const QualifiedName& name,
	map<Binding*, vector<TemplateArgument> >& explicit_template_arguments)
{
	vector<Binding*> found = resolve_name_set(name, pa11::LOOKUP_VALUE);
	if (!name.has_template_arguments)
		return found;
	vector<TemplateDeclaration*> templates = find_function_templates(name);
	found.clear();
	if (!name.qualified && templates.size() == 1 &&
	    templates[0]->placeholder != NULL)
	{
		bool defer_deduced_pack = false;
		for (size_t i = name.template_arguments.size();
		     i < templates[0]->parameters.size();
		     ++i)
			if (templates[0]->parameters[i].is_pack)
				defer_deduced_pack = true;
		try
		{
			if (!defer_deduced_pack)
			{
				vector<TemplateArgument> full_args =
					complete_template_arguments(templates[0],
					                            name.template_arguments);
				Binding* instantiated =
					instantiate_function_template(templates[0], full_args);
				found.push_back(instantiated);
				if (instantiated == templates[0]->placeholder)
					explicit_template_arguments[instantiated] =
						name.template_arguments;
				return found;
			}
		}
			catch (const runtime_error&)
			{
			}
	}
	for (size_t i = 0; i < templates.size(); ++i)
	{
		if (templates[i]->placeholder == NULL)
			continue;
		found.push_back(templates[i]->placeholder);
		explicit_template_arguments[templates[i]->placeholder] =
			name.template_arguments;
	}
	if (!found.empty())
		return found;
	vector<TemplateDeclaration*> variables;
	if (name.qualifier != NULL)
	{
		map<Scope*, map<string, vector<TemplateDeclaration*> > >::iterator sit =
			variable_templates_.find(name.qualifier);
		if (sit != variable_templates_.end())
		{
			map<string, vector<TemplateDeclaration*> >::iterator it =
				sit->second.find(name.name);
			if (it != sit->second.end())
				variables = it->second;
		}
	}
	else
	{
		for (Scope* cur = current_scope(); cur != NULL; cur = cur->parent)
		{
			map<Scope*, map<string, vector<TemplateDeclaration*> > >::iterator sit =
				variable_templates_.find(cur);
			if (sit == variable_templates_.end())
				continue;
			map<string, vector<TemplateDeclaration*> >::iterator it =
				sit->second.find(name.name);
			if (it != sit->second.end())
			{
				variables = it->second;
				break;
			}
		}
	}
	if (variables.empty())
		throw runtime_error("function template not found");
	Binding* variable =
		instantiate_variable_template(variables[0], name.template_arguments);
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
				bool found_local =
					found[i]->owner != NULL &&
					(found[i]->owner->kind == ScopeKind::Function ||
				 found[i]->owner->kind == ScopeKind::Block);
			bool previous_local =
				nonfunction->owner != NULL &&
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
	{
		if (found[i]->kind == BindingKind::Function)
			out.overloads.push_back(found[i]);
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
	prefer_static_qualified_overloads(name, out, binding);
	Expr member = make_implicit_member_id_expr(name,
	                                           found,
	                                           binding,
	                                           this_binding,
	                                           &explicit_template_arguments);
	if (member.valid)
		return member;
	if (binding->kind == BindingKind::Variable &&
	    binding->aliased_binding != NULL)
		binding = binding->aliased_binding;
	if (binding->kind == BindingKind::Variable &&
	    binding->has_constant &&
	    name.has_template_arguments)
	{
		return make_constant_binding_expr(binding,
		                                  expression_object_type(binding->type));
	}
	out.binding = binding;
	out.type = expression_object_type(binding->type);
	if (binding->kind == BindingKind::Function)
		out.type = binding->type;
	out.category = binding->kind == BindingKind::Enumerator
		? ValueCategory::PRValue : ValueCategory::LValue;
	string spelling = name.qualified ? name.spelling : binding->name;
	out.node = Node("id-expression " + value_category_name(out.category) + " " +
	                pa11::describe_type(out.type) + " " + spelling);
	if (binding->has_constant)
	{
		out.constant_expression = true;
		out.has_constant_value = true;
		out.constant_value = binding->constant_value;
		out.null_pointer_constant = binding->constant_value == 0;
	}
	annotate_expr_node(out);
	return out;
}

}  // namespace internal
}  // namespace pa12
