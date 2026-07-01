#include "pa12_expr_semantics_call_template_instantiator.h"
#include "pa12_expr_semantics_support.h"
#include "pa12_templates_function_support.h"
#include "pa12_types_support.h"

#include <algorithm>
#include <cstdint>
#include <stdexcept>

using namespace std;

namespace pa12 {
namespace internal {

const size_t kTemplateCallDeductionCacheLimit = 65536;

size_t dependent_cache_template_argument_identity(
	const TemplateArgument& argument,
	int depth);
size_t dependent_cache_type_identity(TypePtr type);

void Parser::trim_template_call_deduction_cache()
{
	if (template_call_deduction_cache_.size() >
	    kTemplateCallDeductionCacheLimit)
		template_call_deduction_cache_.clear();
}

bool TemplateCallCandidateInstantiator::try_explicit_specialization_for_call(
	Binding*& out)
{
	out = NULL;
	if (!have_call_explicit_args || explicit_args.empty() ||
	    declaration == NULL)
		return false;
	vector<TemplateDeclaration*> candidates;
	if (original_declaration != NULL)
		candidates.push_back(original_declaration);
	if (declaration != NULL && declaration != original_declaration)
		candidates.push_back(declaration);
	Scope* owner = original_declaration != NULL
		? original_declaration->owner : declaration->owner;
	const string& name = original_declaration != NULL
		? original_declaration->name : declaration->name;
	map<Scope*, map<string, vector<TemplateDeclaration*> > >::iterator sit =
		p.function_templates_.find(owner);
	if (sit != p.function_templates_.end())
	{
		map<string, vector<TemplateDeclaration*> >::iterator nit =
			sit->second.find(name);
		if (nit != sit->second.end())
			for (size_t i = 0; i < nit->second.size(); ++i)
			{
				TemplateDeclaration* candidate = nit->second[i];
				if (candidate == NULL)
					continue;
				bool known = false;
				for (size_t ci = 0; ci < candidates.size(); ++ci)
					if (candidates[ci] == candidate)
						known = true;
				if (known)
					continue;
				if (original_declaration != NULL &&
				    !same_function_template_declaration_family(
					    original_declaration, candidate))
					continue;
				candidates.push_back(candidate);
			}
	}
	for (size_t i = 0; i < candidates.size(); ++i)
	{
		TemplateDeclaration* candidate = candidates[i];
		vector<TemplateArgument> full_args;
		bool entered = false;
		try
		{
			++p.function_template_candidate_instantiation_depth_;
			entered = true;
			full_args = p.complete_template_arguments(candidate,
			                                          explicit_args);
			--p.function_template_candidate_instantiation_depth_;
			entered = false;
		}
		catch (const runtime_error&)
		{
			if (entered)
				--p.function_template_candidate_instantiation_depth_;
			continue;
		}
		map<string, Binding*>::iterator found =
			candidate->function_specializations.find(
				p.template_argument_key(full_args));
		if (found == candidate->function_specializations.end() ||
		    found->second == NULL ||
		    !found->second->is_explicit_specialization_member)
			continue;
		out = canonical_function_binding(found->second);
		return true;
	}
	return false;
}

void TemplateCallCandidateInstantiator::append_expr_key(
	vector<size_t>& key,
	const Expr& expr,
	size_t depth) const
{
	key.push_back(dependent_cache_type_identity(expr.type));
	key.push_back(static_cast<size_t>(expr.category));
	key.push_back(expr.pack_expansion ? 1 : 0);
	key.push_back(expr.braced_init_list ? 1 : 0);
	key.push_back(expr.copy_initialization ? 1 : 0);
	key.push_back(reinterpret_cast<uintptr_t>(expr.binding));
	key.push_back(expr.overloads.size());
	for (size_t i = 0; i < expr.overloads.size(); ++i)
	{
		Binding* overload = expr.overloads[i];
		key.push_back(reinterpret_cast<uintptr_t>(overload));
		key.push_back(reinterpret_cast<uintptr_t>(
			overload != NULL ? overload->type.get() : NULL));
	}
	if (depth != 0)
		return;
	key.push_back(expr.pack.size());
	for (size_t i = 0; i < expr.pack.size(); ++i)
		append_expr_key(key, expr.pack[i], depth + 1);
}

vector<size_t> TemplateCallCandidateInstantiator::deduction_cache_key() const
{
	vector<size_t> key;
	key.reserve(12 + explicit_args.size() * 2 + args.size() * 8);
	key.push_back(reinterpret_cast<uintptr_t>(fn));
	key.push_back(reinterpret_cast<uintptr_t>(placeholder));
	key.push_back(reinterpret_cast<uintptr_t>(original_declaration));
	key.push_back(reinterpret_cast<uintptr_t>(declaration));
	key.push_back(p.hosted_compatibility_ ? 1 : 0);
	key.push_back(have_call_explicit_args ? 1 : 0);
	key.push_back(explicit_args.size());
	for (size_t i = 0; i < explicit_args.size(); ++i)
		key.push_back(dependent_cache_template_argument_identity(
			explicit_args[i],
			0));
	key.push_back(args.size());
	for (size_t i = 0; i < args.size(); ++i)
		append_expr_key(key, args[i], 0);
	return key;
}

bool TemplateCallCandidateInstantiator::deduce_arguments()
{
	vector<size_t> cache_key = deduction_cache_key();
	map<vector<size_t>, pair<bool, vector<TemplateArgument> > >::iterator cached =
		p.template_call_deduction_cache_.find(cache_key);
	if (cached != p.template_call_deduction_cache_.end())
	{
		if (!cached->second.first)
			return false;
		deduced = cached->second.second;
		return true;
	}
	bool entered = false;
	bool ok = false;
	try
	{
		++p.function_template_candidate_instantiation_depth_;
		entered = true;
		ok = p.deduce_function_template_arguments(
			declaration, args, explicit_args, deduced);
		if (!ok && (!p.hosted_compatibility_ ||
		    !recover_hosted_call_template_arguments(declaration, args, deduced)))
		{
			--p.function_template_candidate_instantiation_depth_;
			p.template_call_deduction_cache_[cache_key] =
				make_pair(false, vector<TemplateArgument>());
			p.trim_template_call_deduction_cache();
			return false;
		}
		--p.function_template_candidate_instantiation_depth_;
		p.template_call_deduction_cache_[cache_key] =
			make_pair(true, deduced);
		p.trim_template_call_deduction_cache();
		return true;
	}
	catch (const runtime_error&)
	{
		if (entered)
			--p.function_template_candidate_instantiation_depth_;
		ok = p.hosted_compatibility_ &&
		     recover_hosted_call_template_arguments(declaration, args, deduced);
		p.template_call_deduction_cache_[cache_key] =
			make_pair(ok, ok ? deduced : vector<TemplateArgument>());
		p.trim_template_call_deduction_cache();
		return ok;
	}
}

}  // namespace internal
}  // namespace pa12
