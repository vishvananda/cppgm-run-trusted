#include "pa12_internal.h"

using namespace std;

namespace pa12 {
namespace internal {

namespace {

bool variable_template_visible_in_scope_tree(
	Scope* scope,
	const string& name,
	map<Scope*, map<string, vector<TemplateDeclaration*> > >& variable_templates,
	set<Scope*>& seen)
{
	if (scope == NULL || !seen.insert(scope).second)
		return false;
	map<Scope*, map<string, vector<TemplateDeclaration*> > >::iterator sit =
		variable_templates.find(scope);
	if (sit != variable_templates.end())
	{
		map<string, vector<TemplateDeclaration*> >::iterator it =
			sit->second.find(name);
		if (it != sit->second.end() && !it->second.empty())
			return true;
	}
	TypePtr record = pa11::record_type_for_scope(scope);
	vector<TypePtr> bases = record.get() != NULL
		? pa11::record_direct_bases(record) : vector<TypePtr>();
	for (size_t i = 0; i < bases.size(); ++i)
	{
		TypePtr base = bases[i].get() != NULL
			? pa11::strip_cv(bases[i]) : TypePtr();
		if (base.get() != NULL &&
		    base->kind == pa11::TypeKind::Record &&
		    base->scope != NULL &&
		    variable_template_visible_in_scope_tree(base->scope,
		                                            name,
		                                            variable_templates,
		                                            seen))
			return true;
	}
	return false;
}

bool scope_has_visible_direct_binding(Scope* scope, const string& name)
{
	if (scope == NULL)
		return false;
	map<string, vector<Binding*> >::const_iterator found =
		scope->members.find(name);
	if (found == scope->members.end())
		return false;
	for (size_t i = 0; i < found->second.size(); ++i)
		if (found->second[i] != NULL && !found->second[i]->is_hidden_friend)
			return true;
	return false;
}

}  // namespace

vector<TemplateDeclaration*> Parser::find_function_templates(
	const QualifiedName& name)
{
	vector<size_t> cache_key;
	cache_key.push_back(reinterpret_cast<uintptr_t>(
		name.qualifier != NULL ? name.qualifier : current_scope()));
	cache_key.push_back(name.qualifier != NULL);
	cache_key.push_back(hash<string>()(name.name));
	cache_key.push_back(replaying_dependent_decltype_);
	cache_key.push_back(template_declarations_.size());
	cache_key.push_back(member_function_template_generation_);
	cache_key.push_back(function_templates_.size());
	cache_key.push_back(record_dependent_base_lookup_skips_.size());
	map<vector<size_t>, vector<TemplateDeclaration*> >::const_iterator cached =
		function_template_lookup_cache_.find(cache_key);
	if (cached != function_template_lookup_cache_.end())
		return cached->second;
	vector<TemplateDeclaration*> out =
		find_function_templates_uncached(name);
	function_template_lookup_cache_[cache_key] = out;
	return out;
}

vector<TemplateDeclaration*> Parser::find_function_templates_uncached(
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
		TypePtr record = pa11::record_type_for_scope(name.qualifier);
		vector<TypePtr> bases = record.get() != NULL
			? pa11::record_direct_bases(record) : vector<TypePtr>();
		for (size_t b = 0; b < bases.size(); ++b)
		{
			TypePtr base = bases[b].get() != NULL
				? pa11::strip_cv(bases[b]) : TypePtr();
			if (base.get() != NULL &&
			    base->kind == pa11::TypeKind::Record &&
			    base->scope != NULL &&
			    !record_skips_dependent_base_unqualified_lookup(record))
			{
				QualifiedName nested = name;
				nested.qualifier = base->scope;
				out = find_function_templates(nested);
				if (!out.empty())
					return out;
			}
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
		if (scope_has_visible_direct_binding(cur, name.name))
			return out;
		for (size_t i = 0; i < cur->using_directives.size(); ++i)
		{
			QualifiedName nested = name;
			nested.qualifier = cur->using_directives[i];
			out = find_function_templates(nested);
			if (!out.empty())
				return out;
		}
		TypePtr record = pa11::record_type_for_scope(cur);
		vector<TypePtr> bases = record.get() != NULL
			? pa11::record_direct_bases(record) : vector<TypePtr>();
		for (size_t b = 0; b < bases.size(); ++b)
		{
			TypePtr base = bases[b].get() != NULL
				? pa11::strip_cv(bases[b]) : TypePtr();
			if (base.get() != NULL &&
			    base->kind == pa11::TypeKind::Record &&
			    base->scope != NULL &&
			    record_dependent_base_lookup_skips_.count(
				    pa11::strip_cv(record).get()) == 0)
			{
				QualifiedName nested = name;
				nested.qualifier = base->scope;
				out = find_function_templates(nested);
				if (!out.empty())
					return out;
			}
		}
	}
	if (replaying_dependent_decltype_)
	{
		map<Scope*, map<string, vector<TemplateDeclaration*> > >::iterator sit =
			function_templates_.find(global_scope());
		if (sit != function_templates_.end())
		{
			map<string, vector<TemplateDeclaration*> >::iterator it =
				sit->second.find(name.name);
			if (it != sit->second.end())
				return it->second;
		}
	}
	return out;
}

bool Parser::visible_function_template_name(const QualifiedName& name)
{
	return !find_function_templates(name).empty();
}

bool Parser::visible_variable_template_name(const QualifiedName& name)
{
	if (name.qualifier != NULL)
	{
		set<Scope*> seen;
		return variable_template_visible_in_scope_tree(name.qualifier,
		                                               name.name,
		                                               variable_templates_,
		                                               seen);
	}
	for (Scope* cur = current_scope(); cur != NULL; cur = cur->parent)
	{
		if (scope_has_visible_direct_binding(cur, name.name))
			return false;
		set<Scope*> seen;
		if (variable_template_visible_in_scope_tree(cur,
		                                            name.name,
		                                            variable_templates_,
		                                            seen))
			return true;
	}
	return false;
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
