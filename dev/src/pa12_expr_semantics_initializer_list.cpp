#include "pa12_expr_semantics_support.h"
#include "pa12_templates_instance_support.h"
#include "pa12_types_support.h"

#include <algorithm>
#include <map>
#include <stdexcept>

using namespace std;

namespace pa12 {
namespace internal {

namespace {
Binding* find_initializer_list_accessor(Scope* scope,
                                        const string& name,
                                        TypePtr fn_type)
{
	map<string, vector<Binding*> >::iterator found = scope->members.find(name);
	if (found != scope->members.end())
		for (size_t i = 0; i < found->second.size(); ++i)
			if (found->second[i]->kind == BindingKind::Function &&
			    pa11::same_type(found->second[i]->type, fn_type))
				return found->second[i];
	return NULL;
}
}  // namespace

bool Parser::is_std_initializer_list_type(TypePtr type,
                                          TypePtr* element) const
{
	if (type.get() == NULL)
		return false;
	TypePtr bare = pa11::strip_cv(type);
	if (bare->kind != pa11::TypeKind::Record)
		return false;
	string primary = bare->template_primary_name.empty()
		? bare->name : bare->template_primary_name;
	size_t scope_pos = primary.rfind("::");
	string unqualified_primary = scope_pos == string::npos
		? primary : primary.substr(scope_pos + 2);
	size_t args_pos = unqualified_primary.find('<');
	if (args_pos != string::npos)
		unqualified_primary = unqualified_primary.substr(0, args_pos);
	if (unqualified_primary != "initializer_list")
		return false;
	Scope* owner = bare->scope != NULL ? bare->scope->parent : NULL;
	if (owner != NULL &&
	    (owner->kind != ScopeKind::Namespace || owner->name != "std"))
		return false;
	TypePtr element_type;
	if (bare->template_arguments.size() == 1 &&
	    bare->template_arguments[0].kind ==
		    pa11::TemplateInstanceArgumentKind::Type)
	{
		element_type = bare->template_arguments[0].type;
	}
	else
	{
		map<const void*, vector<TemplateArgument> >::const_iterator stored =
			record_template_arguments_.find(bare.get());
		if (stored == record_template_arguments_.end() ||
		    stored->second.size() != 1 ||
		    stored->second[0].kind != TemplateArgumentKind::Type)
			return false;
		element_type = stored->second[0].type;
	}
	if (element != NULL)
		*element = element_type;
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
	TypePtr begin_field_type =
		pa11::make_pointer(pa11::make_cv(element, pa11::CV_CONST));
	TypePtr size_field_type = pa11::make_fundamental(FT_UNSIGNED_LONG_INT);
	TypePtr const_element = pa11::make_cv(element, pa11::CV_CONST);
	TypePtr const_reference = pa11::make_lvalue_reference(const_element);
	TypePtr const_iterator = pa11::make_pointer(const_element);
	auto ensure_alias = [&](const string& name, TypePtr alias) {
		map<string, vector<Binding*> >::const_iterator existing =
			bare->scope->members.find(name);
		if (existing == bare->scope->members.end())
		{
			Binding* binding = add_alias(bare->scope, name, alias);
			binding->is_private = false;
			binding->is_protected_member = false;
		}
	};
	ensure_alias("value_type", element);
	ensure_alias("reference", const_reference);
	ensure_alias("const_reference", const_reference);
	ensure_alias("size_type", size_field_type);
	ensure_alias("iterator", const_iterator);
	ensure_alias("const_iterator", const_iterator);
	for (size_t i = 0; i < bare->scope->binding_order.size(); ++i)
	{
		Binding* binding = bare->scope->binding_order[i];
		if (binding->kind != BindingKind::Variable ||
		    binding->is_static_member)
			continue;
		if (binding->name == "__begin_" ||
		    binding->name == "first" ||
		    pa11::same_type(binding->type, begin_field_type))
			has_begin = true;
		if (binding->name == "__size_" ||
		    binding->name == "count" ||
		    pa11::same_type(binding->type, size_field_type))
			has_size = true;
	}
	if (!has_begin)
		add_value(bare->scope,
		          BindingKind::Variable,
		          "__begin_",
		          begin_field_type);
	if (!has_size)
		add_value(bare->scope,
		          BindingKind::Variable,
		          "__size_",
		          size_field_type);
	TypePtr this_type =
		pa11::make_pointer(pa11::make_cv(bare, pa11::CV_CONST));
	TypePtr const_element_ptr =
		pa11::make_pointer(pa11::make_cv(element, pa11::CV_CONST));
	vector<TypePtr> params(1, this_type);
	TypePtr begin_type = pa11::make_function(const_element_ptr, params, false);
	TypePtr size_type =
		pa11::make_function(pa11::make_fundamental(FT_UNSIGNED_LONG_INT),
		                    params,
		                    false);
	if (find_initializer_list_accessor(bare->scope, "begin", begin_type) == NULL)
	{
		Binding* begin =
			add_value(bare->scope, BindingKind::Function, "begin", begin_type);
		begin->is_inline_definition = true;
		begin->unwind_no = true;
		function_parameter_names_[begin] = vector<string>(1, "this");
		begin->function_parameter_names = function_parameter_names_[begin];
	}
	if (find_initializer_list_accessor(bare->scope, "end", begin_type) == NULL)
	{
		Binding* end =
			add_value(bare->scope, BindingKind::Function, "end", begin_type);
		end->is_inline_definition = true;
		end->unwind_no = true;
		function_parameter_names_[end] = vector<string>(1, "this");
		end->function_parameter_names = function_parameter_names_[end];
	}
	if (find_initializer_list_accessor(bare->scope, "size", size_type) == NULL)
	{
		Binding* size =
			add_value(bare->scope, BindingKind::Function, "size", size_type);
		size->is_inline_definition = true;
		size->unwind_no = true;
		function_parameter_names_[size] = vector<string>(1, "this");
		size->function_parameter_names = function_parameter_names_[size];
	}
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
	out.node = Node("initializer-list-object prvalue " +
	                pa11::describe_type(target) + " ");
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

}  // namespace internal
}  // namespace pa12
