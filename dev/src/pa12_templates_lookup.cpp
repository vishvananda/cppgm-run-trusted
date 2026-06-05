#include "pa12_internal.h"

using namespace std;

namespace pa12 {
namespace internal {

vector<TemplateDeclaration*> Parser::find_function_templates(
	const QualifiedName& name)
{
	vector<TemplateDeclaration*> out;
	if (name.qualifier != NULL)
	{
		map<Scope*, map<string, vector<TemplateDeclaration*> > >::iterator sit =
			function_templates_.find(name.qualifier);
		if (sit != function_templates_.end())
		{
			map<string, vector<TemplateDeclaration*> >::iterator it =
				sit->second.find(name.name);
			if (it != sit->second.end())
				out = it->second;
			if (!out.empty())
				return out;
		}
		for (size_t i = 0; i < name.qualifier->using_directives.size(); ++i)
		{
			QualifiedName nested = name;
			nested.qualifier = name.qualifier->using_directives[i];
			out = find_function_templates(nested);
			if (!out.empty())
				return out;
		}
		return out;
	}
	for (Scope* cur = current_scope(); cur != NULL; cur = cur->parent)
	{
		map<Scope*, map<string, vector<TemplateDeclaration*> > >::iterator sit =
			function_templates_.find(cur);
		if (sit != function_templates_.end())
		{
			map<string, vector<TemplateDeclaration*> >::iterator it =
				sit->second.find(name.name);
			if (it != sit->second.end())
				return it->second;
		}
		for (size_t i = 0; i < cur->using_directives.size(); ++i)
		{
			QualifiedName nested = name;
			nested.qualifier = cur->using_directives[i];
			out = find_function_templates(nested);
			if (!out.empty())
				return out;
		}
	}
	return out;
}

bool Parser::visible_function_template_name(const QualifiedName& name)
{
	return !find_function_templates(name).empty();
}

vector<Binding*> Parser::instantiate_explicit_function_templates(
	const QualifiedName& name)
{
	vector<Binding*> out;
	vector<TemplateDeclaration*> declarations = find_function_templates(name);
	for (size_t i = 0; i < declarations.size(); ++i)
		out.push_back(instantiate_function_template(declarations[i],
		                                            name.template_arguments));
	return out;
}

}  // namespace internal
}  // namespace pa12
