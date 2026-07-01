#include "pa12_expr_semantics_support.h"
#include "pa12_templates_instance_support.h"
#include "pa12_types_support.h"

#include <algorithm>
#include <stdexcept>

using namespace std;

namespace pa12 {
namespace internal {

void Parser::substitute_lambda_helper_node_types(
	Node& node,
	const map<string, TypePtr>& substitutions,
	const map<Binding*, Binding*>& replacements) const
{
	map<Binding*, Binding*>::const_iterator binding =
		replacements.find(node.binding);
	if (binding != replacements.end())
		node.binding = binding->second;
	map<Binding*, Binding*>::const_iterator direct =
		replacements.find(node.direct_call);
	if (direct != replacements.end())
		node.direct_call = direct->second;
	for (map<string, TypePtr>::const_iterator it = substitutions.begin();
	     it != substitutions.end();
	     ++it)
		node.type = substitute_template_type_parameter(node.type,
		                                               it->first,
		                                               it->second);
	for (size_t i = 0; i < node.children.size(); ++i)
		substitute_lambda_helper_node_types(node.children[i],
		                                    substitutions,
		                                    replacements);
}

bool Parser::deduce_lambda_helper_substitutions(
	Binding* helper,
	const vector<Expr>& args,
	vector<TemplateArgument>& full_args,
	map<string, TypePtr>& substitutions,
	string& key)
{
	map<Binding*, vector<TemplateParameterInfo> >::const_iterator params_it =
		lambda_template_parameters_.find(helper);
	if (helper == NULL ||
	    helper->type.get() == NULL ||
	    helper->type->kind != pa11::TypeKind::Function ||
	    params_it == lambda_template_parameters_.end())
		return false;
	map<string, TypePtr> deduced;
	map<string, TypePtr> fixed;
	map<string, TemplateArgument> fixed_arguments;
	size_t deduce_count = min(args.size(), helper->type->parameters.size());
	for (size_t i = 0; i < deduce_count; ++i)
		if (!deduce_regular_template_call_argument(helper->type->parameters[i],
		                                           args[i],
		                                           deduced,
		                                           fixed,
		                                           fixed_arguments))
			return false;
	for (size_t i = 0; i < params_it->second.size(); ++i)
	{
		const TemplateParameterInfo& parameter = params_it->second[i];
		if (parameter.kind != TemplateParameterKind::Type ||
		    parameter.is_pack ||
		    parameter.name.empty())
			return false;
		map<string, TypePtr>::const_iterator found =
			deduced.find(parameter.name);
		if (found == deduced.end() || found->second.get() == NULL)
			return false;
		substitutions[parameter.name] = found->second;
		full_args.push_back(TemplateArgument::type_arg(found->second));
		key += "|";
		key += pa11::describe_type(found->second);
	}
	return true;
}

void Parser::materialize_lambda_helper_parameters(
	Binding* helper,
	Binding* binding,
	TypePtr concrete_type,
	Node& fn,
	Scope* function_scope,
	map<Binding*, Binding*>& replacements)
{
	vector<string> names;
	map<Binding*, vector<string> >::const_iterator old_names =
		function_parameter_names_.find(helper);
	for (size_t i = 0; i < concrete_type->parameters.size(); ++i)
	{
		string pname;
		if (old_names != function_parameter_names_.end() &&
		    i < old_names->second.size())
			pname = old_names->second[i];
		if (pname.empty())
			pname = "__param" + to_string(i);
		names.push_back(pname);
		Binding* param = pa11::add_binding(function_scope,
		                                   BindingKind::Parameter,
		                                   pname,
		                                   concrete_type->parameters[i]);
		if (i < fn.children.size())
		{
			if (fn.children[i].binding != NULL)
				replacements[fn.children[i].binding] = param;
			fn.children[i].line =
				"parameter " + pname + " " +
				pa11::describe_type(concrete_type->parameters[i]);
			fn.children[i].binding = param;
			fn.children[i].type = concrete_type->parameters[i];
		}
	}
	function_parameter_names_[binding] = names;
}

void Parser::substitute_lambda_helper_defaults(
	Binding* helper,
	Binding* binding,
	const map<string, TypePtr>& substitutions)
{
	map<Binding*, vector<Expr> >::const_iterator old_defaults =
		default_arguments_.find(helper);
	if (old_defaults == default_arguments_.end())
		return;
	vector<Expr> defaults = old_defaults->second;
	map<Binding*, Binding*> no_replacements;
	for (size_t i = 0; i < defaults.size(); ++i)
	{
		if (!defaults[i].valid)
			continue;
		for (map<string, TypePtr>::const_iterator it = substitutions.begin();
		     it != substitutions.end();
		     ++it)
			defaults[i].type =
				substitute_template_type_parameter(defaults[i].type,
				                                   it->first,
				                                   it->second);
		substitute_lambda_helper_node_types(defaults[i].node,
		                                    substitutions,
		                                    no_replacements);
		annotate_expr_node(defaults[i]);
	}
	default_arguments_[binding] =
		default_arguments_for_binding(binding, defaults);
}

Binding* Parser::instantiate_lambda_helper_call(Binding* helper,
                                                const vector<Expr>& args,
                                                vector<Expr>& converted)
{
	vector<TemplateArgument> full_args;
	map<string, TypePtr> substitutions;
	string key;
	if (!deduce_lambda_helper_substitutions(helper,
	                                       args,
	                                       full_args,
	                                       substitutions,
	                                       key))
		return NULL;

	pair<Binding*, string> cache_key(helper, key);
	map<pair<Binding*, string>, Binding*>::iterator cached =
		lambda_helper_specializations_.find(cache_key);
	if (cached != lambda_helper_specializations_.end())
	{
		vector<Binding*> overloads(1, cached->second);
		map<Binding*, vector<TemplateArgument> > no_explicit_args;
		return resolve_call_candidate(overloads,
		                              args,
		                              no_explicit_args,
		                              converted);
	}

	TypePtr concrete_type = helper->type;
	for (map<string, TypePtr>::const_iterator it = substitutions.begin();
	     it != substitutions.end();
	     ++it)
		concrete_type = substitute_template_type_parameter(concrete_type,
		                                                   it->first,
		                                                   it->second);

	string spec_name =
		helper->name + "__lambda_spec" +
		to_string(lambda_helper_specializations_.size());
	Binding* binding =
		add_value(helper->owner,
		          BindingKind::Function,
		          spec_name,
		          concrete_type);
	binding->language_linkage = helper->language_linkage;
	binding->is_inline_definition = true;
		binding->is_namespace_static = helper->is_namespace_static;
		binding->is_constexpr = helper->is_constexpr;
		binding->unwind_no = helper->unwind_no;
		binding->dynamic_exception_spec = helper->dynamic_exception_spec;
		binding->dynamic_exception_types = helper->dynamic_exception_types;
		binding->ref_qualifier = helper->ref_qualifier;
	function_template_specialization_arguments_[binding] = full_args;

	map<Binding*, Node>::const_iterator body_it = function_bodies_.find(helper);
	if (body_it == function_bodies_.end())
		throw runtime_error("missing lambda helper body");
	Node fn = body_it->second;
	fn.line = "function-definition " + qualified_decl_name(binding) + " " +
	          pa11::describe_type(concrete_type);
	fn.binding = binding;
	fn.type = concrete_type;

	Scope* function_scope =
		pa11::create_child_scope(helper->owner,
		                         ScopeKind::Function,
		                         spec_name);
	map<Binding*, Binding*> replacements;
	materialize_lambda_helper_parameters(helper,
	                                     binding,
	                                     concrete_type,
	                                     fn,
	                                     function_scope,
	                                     replacements);
	substitute_lambda_helper_node_types(fn, substitutions, replacements);
	substitute_lambda_helper_defaults(helper, binding, substitutions);

	remember_function_body(binding, fn);
	extra_lowir_nodes_.push_back(fn);
	lambda_helper_specializations_[cache_key] = binding;

	vector<Binding*> overloads(1, binding);
	map<Binding*, vector<TemplateArgument> > no_explicit_args;
	return resolve_call_candidate(overloads,
	                              args,
	                              no_explicit_args,
	                              converted);
}

}  // namespace internal
}  // namespace pa12
