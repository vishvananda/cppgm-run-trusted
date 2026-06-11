#include "pa12_templates_function_support.h"
#include "pa12_templates_instance_support.h"

using namespace std;

namespace pa12 {
namespace internal {

size_t function_body_start(const vector<Token>& tokens,
                           size_t begin,
                           size_t end)
{
	for (size_t i = begin; i < end && i < tokens.size(); ++i)
		if (tokens[i].kind == posttoken::TokenKind::Simple &&
		    tokens[i].type == OP_LBRACE)
			return i;
	return end;
}

vector<ParameterInfo> concrete_member_body_parameters(
	Binding* function,
	const map<Binding*, vector<string> >& function_parameter_names)
{
	vector<ParameterInfo> parameters;
	if (function == NULL || function->type.get() == NULL ||
	    function->type->kind != pa11::TypeKind::Function)
		return parameters;
	size_t first = function->owner != NULL &&
	               function->owner->kind == ScopeKind::Class &&
	               !function->is_static_member ? 1 : 0;
	map<Binding*, vector<string> >::const_iterator names =
		function_parameter_names.find(function);
	for (size_t i = first; i < function->type->parameters.size(); ++i)
	{
		ParameterInfo parameter;
		parameter.type = function->type->parameters[i];
		if (names != function_parameter_names.end() &&
		    i < names->second.size())
			parameter.name = names->second[i];
		parameters.push_back(parameter);
	}
	return parameters;
}

bool function_body_signature_matches(Binding* function, const Node& body)
{
	if (function == NULL ||
	    function->type.get() == NULL ||
	    function->type->kind != pa11::TypeKind::Function)
		return true;
	size_t parameter_index = 0;
	for (size_t i = 0; i < body.children.size(); ++i)
	{
		const Node& child = body.children[i];
		if (child.line.compare(0, 10, "parameter ") != 0)
			continue;
		if (parameter_index >= function->type->parameters.size())
			return false;
		if (child.type.get() != NULL &&
		    !pa11::same_type(child.type,
		                     function->type->parameters[parameter_index]))
			return false;
		++parameter_index;
	}
	return parameter_index == function->type->parameters.size();
}

bool matching_member_template_class_specialization(
	Parser* parser,
	TemplateDeclaration* primary,
	TemplateDeclaration* specialization,
	const vector<TemplateArgument>& primary_args,
	const map<const void*, vector<TemplateArgument> >& record_arguments)
{
	if (specialization == NULL || !specialization->class_specialization)
		return false;
	vector<TemplateArgument> pattern_args;
	TemplateMatchParserScope match_scope(parser);
	return match_class_specialization(primary,
	                                  specialization,
	                                  primary_args,
	                                  primary_args.size(),
	                                  pattern_args,
	                                  record_arguments);
}

bool member_template_set_has_class_specialization(
	Parser* parser,
	TemplateDeclaration* primary,
	const vector<TemplateDeclaration*>& declarations,
	const vector<TemplateArgument>& primary_args,
	const map<const void*, vector<TemplateArgument> >& record_arguments)
{
	for (size_t i = 0; i < declarations.size(); ++i)
		if (matching_member_template_class_specialization(
			    parser,
			    primary,
			    declarations[i],
			    primary_args,
			    record_arguments))
			return true;
	return false;
}

bool member_template_definition_matches_owner(
	Parser* parser,
	TemplateDeclaration* declared_owner,
	TemplateDeclaration* owner,
	TemplateDeclaration* primary,
	TemplateDeclaration* declaration,
	const vector<TemplateArgument>& primary_args,
	const map<const void*, vector<TemplateArgument> >& record_arguments)
{
	bool owner_is_class_specialization =
		owner != NULL && owner->class_specialization;
	bool matches = declared_owner == owner;
	if (!matches && declared_owner == primary)
	{
		matches = !owner_is_class_specialization;
		if (owner_is_class_specialization)
			matches = matching_member_template_class_specialization(
				parser, primary, declaration, primary_args, record_arguments);
	}
	if (matches && declaration != NULL && declaration->class_specialization)
		matches = matching_member_template_class_specialization(
			parser, primary, declaration, primary_args, record_arguments);
	return matches;
}

}  // namespace internal
}  // namespace pa12
