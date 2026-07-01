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

size_t dependent_cache_template_argument_identity(
	const TemplateArgument& argument,
	int depth);
size_t dependent_cache_type_identity(TypePtr type);

namespace {
void append_flattened_template_arguments(
	const vector<TemplateArgument>& arguments,
	vector<TemplateArgument>& out)
{
	for (size_t i = 0; i < arguments.size(); ++i)
	{
		if (arguments[i].kind == TemplateArgumentKind::Pack)
			out.insert(out.end(),
			           arguments[i].pack.begin(),
			           arguments[i].pack.end());
		else
			out.push_back(arguments[i]);
	}
}

}  // namespace

void TemplateCallCandidateInstantiator::select_explicit_arguments()
{
	map<Binding*, vector<TemplateArgument> >::const_iterator eit =
		explicit_template_arguments.find(fn);
	if (eit == explicit_template_arguments.end() && placeholder != fn)
		eit = explicit_template_arguments.find(placeholder);
	if (eit == explicit_template_arguments.end() &&
	    original_declaration->placeholder != NULL)
		eit = explicit_template_arguments.find(original_declaration->placeholder);
	have_call_explicit_args = eit != explicit_template_arguments.end();
	if (eit != explicit_template_arguments.end())
		explicit_args = eit->second;
	else
	{
		map<Binding*, vector<TemplateArgument> >::const_iterator stored =
			p.function_template_specialization_arguments_.find(fn);
		if (!placeholder_candidate &&
		    stored != p.function_template_specialization_arguments_.end() &&
		    !p.template_arguments_dependent(stored->second))
			explicit_args = stored->second;
	}
}

size_t TemplateCallCandidateInstantiator::
stored_concrete_specialization_cache_key() const
{
	size_t key = 0x57c011;
	auto mix = [&key](size_t value) {
		key ^= value + 0x9e3779b97f4a7c15ULL + (key << 6) + (key >> 2);
	};
	mix(reinterpret_cast<uintptr_t>(&p));
	mix(reinterpret_cast<uintptr_t>(fn));
	mix(reinterpret_cast<uintptr_t>(fn != NULL ? fn->aliased_binding : NULL));
	mix(reinterpret_cast<uintptr_t>(declaration));
	mix(declaration != NULL ? declaration->function_specializations.size() : 0);
	mix(p.function_template_specialization_arguments_.size());
	mix(explicit_template_arguments.size());
	for (map<Binding*, vector<TemplateArgument> >::const_iterator it =
		     explicit_template_arguments.begin();
	     it != explicit_template_arguments.end();
	     ++it)
	{
		mix(reinterpret_cast<uintptr_t>(it->first));
		mix(it->second.size());
		for (size_t i = 0; i < it->second.size(); ++i)
			mix(dependent_cache_template_argument_identity(it->second[i],
			                                               0));
	}
	return key;
}

bool TemplateCallCandidateInstantiator::try_stored_concrete_specialization(
	Binding*& out)
{
	out = NULL;
	Binding* stored_binding = fn;
	map<Binding*, vector<TemplateArgument> >::const_iterator stored =
		p.function_template_specialization_arguments_.find(stored_binding);
	if (stored == p.function_template_specialization_arguments_.end() &&
	    fn->aliased_binding != NULL)
	{
		stored_binding = fn->aliased_binding;
		stored = p.function_template_specialization_arguments_.find(
			stored_binding);
	}
	if (stored == p.function_template_specialization_arguments_.end())
		return false;
	map<Binding*, TemplateDeclaration*>::const_iterator template_it =
		p.function_template_placeholders_.find(stored_binding);
	if (template_it == p.function_template_placeholders_.end() &&
	    stored_binding != fn)
		template_it = p.function_template_placeholders_.find(fn);
	if (template_it != p.function_template_placeholders_.end() &&
	    stored->second.size() < template_it->second->parameters.size())
		return false;
	if (explicit_template_arguments.empty())
	{
		if (stored_binding != fn)
			return false;
		if (cached_binding_type_dependent(stored_binding))
			return false;
		out = canonical_call_binding(fn);
		return member_call_owner_matches(out);
	}
	if (cached_binding_type_dependent(stored_binding))
		return false;
	map<Binding*, vector<TemplateArgument> >::const_iterator explicit_it =
		explicit_template_arguments.find(fn);
	if (explicit_it == explicit_template_arguments.end() &&
	    stored_binding != fn)
		explicit_it = explicit_template_arguments.find(stored_binding);
	bool followed_alias = stored_binding != fn;
	bool placeholder_alias = false;
	if (followed_alias)
	{
		map<Binding*, TemplateDeclaration*>::const_iterator direct_template =
			p.function_template_placeholders_.find(fn);
		placeholder_alias =
			direct_template != p.function_template_placeholders_.end() &&
			direct_template->second->placeholder == fn;
	}
	if (explicit_it == explicit_template_arguments.end() &&
	    template_it != p.function_template_placeholders_.end() &&
	    template_it->second->placeholder != NULL)
		explicit_it =
			explicit_template_arguments.find(template_it->second->placeholder);
	if (placeholder_alias)
		return false;
	if (explicit_it == explicit_template_arguments.end())
	{
		out = canonical_call_binding(fn);
		return member_call_owner_matches(out);
	}
	static map<size_t, Binding*> success_cache;
	static set<size_t> miss_cache;
	size_t cache_key = stored_concrete_specialization_cache_key();
	map<size_t, Binding*>::const_iterator cached = success_cache.find(cache_key);
	if (cached != success_cache.end())
	{
		out = canonical_call_binding(cached->second);
		return member_call_owner_matches(out);
	}
	if (miss_cache.find(cache_key) != miss_cache.end())
		return false;
	auto remember_miss = [&]() -> bool
	{
		miss_cache.insert(cache_key);
		return false;
	};
	if (explicit_it != explicit_template_arguments.end() &&
	    !stored_binding->is_explicit_specialization_member &&
	    template_it != p.function_template_placeholders_.end())
	{
		bool entered = false;
		try
		{
			++p.function_template_candidate_instantiation_depth_;
			entered = true;
			vector<TemplateArgument> full_args =
				p.complete_template_arguments(template_it->second,
				                              explicit_it->second);
			--p.function_template_candidate_instantiation_depth_;
			entered = false;
			map<string, Binding*>::iterator found =
				template_it->second->function_specializations.find(
					p.template_argument_key(full_args));
			if (found !=
				    template_it->second->function_specializations.end() &&
			    found->second != NULL &&
			    found->second->is_explicit_specialization_member)
				return remember_miss();
		}
		catch (const runtime_error& err)
		{
			if (entered)
				--p.function_template_candidate_instantiation_depth_;
			string message = err.what();
			if (message == "dependent typename not resolved" ||
			    message == "missing template argument" ||
			    message == "too many template arguments" ||
			    message == "template argument arity mismatch" ||
			    message == "template argument kind mismatch" ||
			    message == "template pack argument kind mismatch")
				return remember_miss();
		}
	}
	const vector<TemplateArgument>& explicit_args = explicit_it->second;
	const vector<TemplateArgument>& stored_args = stored->second;
	vector<TemplateArgument> explicit_compare;
	vector<TemplateArgument> stored_compare;
	append_flattened_template_arguments(explicit_args, explicit_compare);
	append_flattened_template_arguments(stored_args, stored_compare);
	if (explicit_compare.size() > stored_compare.size())
		return remember_miss();
	for (size_t i = 0; i < explicit_compare.size(); ++i)
	{
		if (dependent_cache_template_argument_identity(explicit_compare[i],
		                                                0) !=
		    dependent_cache_template_argument_identity(stored_compare[i],
		                                                0))
			return remember_miss();
	}
	out = canonical_call_binding(fn);
	if (!member_call_owner_matches(out))
		return remember_miss();
	success_cache[cache_key] = out;
	return true;
}

bool TemplateCallCandidateInstantiator::try_modeled_hosted_candidate(Binding*& out)
{
	out = NULL;
	if (!p.hosted_compatibility_ || !explicit_args.empty())
		return false;
	vector<TemplateArgument> modeled_args;
	TypePtr modeled = modeled_hosted_function_assignment_type(fn, args, modeled_args);
	if (modeled.get() == NULL)
		modeled = modeled_hosted_vector_insert_type(fn, args, modeled_args);
	if (modeled.get() == NULL)
		modeled = modeled_hosted_dependent_pointer_member_type(
			fn, declaration, args, modeled_args);
	if (modeled.get() == NULL)
		modeled = p.modeled_hosted_make_pair_type(
			fn, declaration, args, modeled_args);
	if (modeled.get() == NULL)
		return false;
	Scope* owner = fn->owner != NULL ? fn->owner : declaration->owner;
	if (owner == NULL)
		return true;
	map<string, vector<Binding*> >::iterator found = owner->members.find(fn->name);
	vector<TemplateArgument> full_args =
		p.complete_template_arguments(declaration, modeled_args);
	string key = p.template_argument_key(full_args);
	if (found != owner->members.end())
		for (size_t mi = 0; mi < found->second.size(); ++mi)
			if (found->second[mi] != NULL &&
			    found->second[mi]->kind == BindingKind::Function &&
			    found->second[mi] != fn &&
			    found->second[mi]->type.get() != NULL &&
			    found->second[mi]->type->kind == pa11::TypeKind::Function &&
			    pa11::same_type(found->second[mi]->type, modeled))
			{
				out = found->second[mi];
				declaration->function_specializations[key] = out;
				p.function_template_placeholders_[out] = declaration;
				p.function_template_specialization_arguments_[out] = full_args;
				if (out->function_specialization_symbol.empty())
					out->function_specialization_symbol =
						declaration->class_template_member
						? (constructor_template_function_template_symbol(declaration) ||
						   class_template_member_function_template_symbol(declaration)
							   ? abi_function_template_specialization_symbol(
								 declaration, full_args, out, &p.declaration_tokens_)
							   : abi_binding_symbol(out, map<string, size_t>()))
						: abi_function_template_specialization_symbol(
							  declaration, full_args, out, &p.declaration_tokens_);
				return true;
			}
	Binding* binding = p.add_value(owner, BindingKind::Function, fn->name, modeled);
	binding->is_static_member = fn->is_static_member;
	binding->is_constexpr = fn->is_constexpr;
	binding->is_private = fn->is_private;
	binding->is_protected_member = fn->is_protected_member;
	binding->ref_qualifier = fn->ref_qualifier;
	binding->unwind_no = fn->unwind_no;
	binding->dynamic_exception_spec = fn->dynamic_exception_spec;
	binding->dynamic_exception_types = fn->dynamic_exception_types;
	map<string, Binding*>::iterator previous =
		declaration->function_specializations.find(key);
	if (previous != declaration->function_specializations.end() &&
	    previous->second != binding)
		previous->second->aliased_binding = binding;
	declaration->function_specializations[key] = binding;
	p.function_template_placeholders_[binding] = declaration;
	p.function_template_specialization_arguments_[binding] = full_args;
	binding->function_specialization_symbol =
		declaration->class_template_member
		? (constructor_template_function_template_symbol(declaration) ||
		   class_template_member_function_template_symbol(declaration)
			   ? abi_function_template_specialization_symbol(
				 declaration, full_args, binding, &p.declaration_tokens_)
			   : abi_binding_symbol(binding, map<string, size_t>()))
		: abi_function_template_specialization_symbol(
			  declaration, full_args, binding, &p.declaration_tokens_);
	out = binding;
	return true;
}

}  // namespace internal
}  // namespace pa12
