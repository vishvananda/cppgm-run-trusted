#include "pa12_internal.h"

#include <algorithm>

using namespace std;

namespace pa12 {
namespace internal {
namespace {

bool seen_insert(set<Scope*>& seen, Scope* scope)
{
	return scope != NULL && seen.insert(scope).second;
}

void append_unique(vector<Binding*>& out, Binding* binding)
{
	if (binding == NULL)
		return;
	if (find(out.begin(), out.end(), binding) == out.end())
		out.push_back(binding);
}

bool scope_contains(Scope* ancestor, Scope* scope)
{
	for (Scope* cur = scope; cur != NULL; cur = cur->parent)
		if (cur == ancestor)
			return true;
	return false;
}

void append_unique_scope(vector<Scope*>& out, Scope* scope)
{
	if (scope == NULL)
		return;
	if (find(out.begin(), out.end(), scope) == out.end())
		out.push_back(scope);
}

void collect_direct_in_scope(Scope* scope,
                             const string& name,
                             int mask,
                             vector<Binding*>& out)
{
	if (scope == NULL)
		return;
	map<string, vector<Binding*> >::iterator it = scope->members.find(name);
	if (it == scope->members.end())
		return;
	for (size_t i = 0; i < it->second.size(); ++i)
	{
		if (!pa11::binding_matches(it->second[i], mask) ||
		    it->second[i]->is_hidden_friend)
			continue;
		append_unique(out, it->second[i]);
	}
}

}  // namespace

Scope* Parser::resolve_qualifier(Binding* binding)
{
	return pa11::binding_qualifier_scope(binding);
}

vector<Binding*> Parser::lookup_direct_set(Scope* scope,
                                           const string& name,
                                           int mask)
{
	pair<pair<Scope*, string>, int> key =
		make_pair(make_pair(scope, name), mask);
	size_t bucket_generation = 0;
	if (scope != NULL)
	{
		map<string, vector<Binding*> >::iterator it =
			scope->members.find(name);
		if (it != scope->members.end())
		{
			bucket_generation = it->second.size();
			if (!it->second.empty())
				bucket_generation =
					bucket_generation * 1315423911u ^
					reinterpret_cast<uintptr_t>(it->second.back());
		}
	}
	map<pair<pair<Scope*, string>, int>,
	    pair<size_t, vector<Binding*> > >::const_iterator cached =
		direct_lookup_cache_.find(key);
	if (cached != direct_lookup_cache_.end() &&
	    cached->second.first == bucket_generation)
		return cached->second.second;
	vector<Binding*> out;
	collect_direct_in_scope(scope, name, mask, out);
	direct_lookup_cache_[key] = make_pair(bucket_generation, out);
	return out;
}

void Parser::collect_lookup_in_scope(Scope* scope,
                                     const string& name,
                                     int mask,
                                     set<Scope*>& seen,
                                     vector<Binding*>& out)
{
	if (!seen_insert(seen, scope))
		return;
	vector<Binding*> direct = lookup_direct_set(scope, name, mask);
	for (size_t i = 0; i < direct.size(); ++i)
		append_unique(out, direct[i]);
	for (size_t i = 0; i < scope->using_directives.size(); ++i)
		collect_lookup_in_scope(scope->using_directives[i],
		                        name,
		                        mask,
		                        seen,
		                        out);
	if (!out.empty())
		return;
	TypePtr record = pa11::record_type_for_scope(scope);
	vector<TypePtr> bases = record.get() != NULL
		? pa11::record_direct_bases(record) : vector<TypePtr>();
	for (size_t i = 0; i < bases.size(); ++i)
	{
		TypePtr base = bases[i].get() != NULL
			? pa11::strip_cv(bases[i]) : TypePtr();
		if (base.get() != NULL &&
		    base->kind == pa11::TypeKind::Record &&
		    base->scope != NULL)
			collect_lookup_in_scope(base->scope, name, mask, seen, out);
	}
}

vector<Binding*> Parser::lookup_qualified_set(Scope* scope,
                                              const string& name,
                                              int mask)
{
	pair<pair<Scope*, string>, int> cache_key =
		make_pair(make_pair(scope, name), mask);
	TypePtr lookup_record = pa11::record_type_for_scope(scope);
	if (lookup_record.get() != NULL)
	{
		TypePtr bare_lookup = pa11::strip_cv(lookup_record);
		if (bare_lookup->kind == pa11::TypeKind::Record &&
		    !type_is_template_dependent(bare_lookup))
			complete_template_record(bare_lookup);
	}
	for (TypePtr cur = lookup_record.get() != NULL
	     ? pa11::strip_cv(lookup_record) : TypePtr();
	     cur.get() != NULL &&
	     cur->kind == pa11::TypeKind::Record &&
	     cur->base.get() != NULL;)
	{
		bool skip_dependent_lookup =
			record_dependent_base_lookup_skips_.count(cur.get()) != 0;
		TypePtr raw_base = cur->base.get() != NULL
			? pa11::strip_cv(cur->base) : TypePtr();
		for (int resolve_depth = 0;
		     raw_base.get() != NULL &&
		     raw_base->is_dependent_typename &&
		     resolve_depth < 8;
		     ++resolve_depth)
		{
			try
			{
				TypePtr resolved = resolve_dependent_typename_type(raw_base);
				if (resolved.get() == NULL)
					resolved = substitute_template_type(raw_base);
				if (resolved.get() == NULL ||
				    resolved.get() == raw_base.get())
					break;
				cur->base = resolved;
				raw_base = cur->base.get() != NULL
					? pa11::strip_cv(cur->base) : TypePtr();
			}
			catch (const runtime_error&)
			{
				break;
			}
		}
		TypePtr base = pa11::strip_cv(cur->base);
		if (base.get() == NULL || base->kind != pa11::TypeKind::Record)
			break;
		if (skip_dependent_lookup && type_is_template_dependent(base))
			break;
		if (!type_is_template_dependent(base))
			record_dependent_base_lookup_skips_.erase(cur.get());
		complete_template_record(base);
		cur = base;
	}
	size_t cache_generation = pa11::binding_generation();
	map<pair<pair<Scope*, string>, int>,
	    pair<size_t, vector<Binding*> > >::const_iterator cached =
		qualified_lookup_cache_.find(cache_key);
	if (cached != qualified_lookup_cache_.end() &&
	    cached->second.first == cache_generation)
		return cached->second.second;
	vector<Binding*> out;
	set<Scope*> seen;
	collect_lookup_in_scope(scope, name, mask, seen, out);
	qualified_lookup_cache_[cache_key] =
		make_pair(pa11::binding_generation(), out);
	return out;
}

vector<Binding*> Parser::lookup_unqualified_set(Scope* start,
                                                const string& name,
                                                int mask)
{
	pair<pair<Scope*, string>, int> cache_key =
		make_pair(make_pair(start, name), mask);
	size_t cache_generation = pa11::binding_generation();
	map<pair<pair<Scope*, string>, int>,
	    pair<size_t, vector<Binding*> > >::const_iterator cached =
		unqualified_lookup_cache_.find(cache_key);
	if (cached != unqualified_lookup_cache_.end() &&
	    cached->second.first == cache_generation)
		return cached->second.second;
	vector<Scope*> deferred_using_directives;
	for (Scope* scope = start; scope != NULL; scope = scope->parent)
	{
		for (size_t i = 0; i < scope->using_directives.size(); ++i)
			append_unique_scope(deferred_using_directives,
			                    scope->using_directives[i]);
		vector<Binding*> direct = lookup_direct_set(scope, name, mask);
		for (size_t i = 0; i < deferred_using_directives.size(); ++i)
		{
			if (!scope_contains(scope, deferred_using_directives[i]))
				continue;
			set<Scope*> seen;
			collect_lookup_in_scope(deferred_using_directives[i],
			                        name,
			                        mask,
			                        seen,
			                        direct);
		}
		if (!direct.empty())
		{
			unqualified_lookup_cache_[cache_key] =
				make_pair(pa11::binding_generation(), direct);
			return direct;
		}
		TypePtr record = pa11::record_type_for_scope(scope);
		vector<TypePtr> bases = record.get() != NULL
			? pa11::record_direct_bases(record) : vector<TypePtr>();
		vector<Binding*> base_found;
		for (size_t b = 0; b < bases.size(); ++b)
		{
			TypePtr base = bases[b].get() != NULL
				? pa11::strip_cv(bases[b]) : TypePtr();
			bool skip_dependent_base_lookup =
				record_skips_dependent_base_unqualified_lookup(record) &&
				(mask & pa11::LOOKUP_VALUE) != 0;
			if (base.get() != NULL &&
			    base->kind == pa11::TypeKind::Record &&
			    base->scope != NULL &&
			    !skip_dependent_base_lookup)
			{
				complete_template_record(base);
				set<Scope*> seen;
				collect_lookup_in_scope(base->scope,
				                        name,
				                        mask,
				                        seen,
				                        base_found);
			}
		}
		if (!base_found.empty())
		{
			unqualified_lookup_cache_[cache_key] =
				make_pair(pa11::binding_generation(), base_found);
			return base_found;
		}
	}
	vector<Binding*> empty;
	unqualified_lookup_cache_[cache_key] =
		make_pair(pa11::binding_generation(), empty);
	return empty;
}

}  // namespace internal
}  // namespace pa12
