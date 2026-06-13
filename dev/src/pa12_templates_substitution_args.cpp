#include "pa12_templates_instance_support.h"
#include "pa12_types_support.h"

#include <algorithm>
#include <cstdint>
#include <functional>
#include <sstream>
#include <stdexcept>
#include <utility>

#include "posttoken_pipeline.h"
#include "pp_token.h"

using namespace std;

namespace pa12 {
namespace internal {
namespace {

size_t dependent_cache_hash_combine(size_t seed, size_t value)
{
	return seed ^ (value + 0x9e3779b97f4a7c15ULL + (seed << 6) +
	               (seed >> 2));
}

size_t dependent_cache_string_hash(const string& value)
{
	return dependent_cache_hash_combine(value.size(),
	                                    hash<string>()(value));
}

size_t dependent_cache_type_identity(TypePtr type)
{
	type = type.get() != NULL ? pa11::strip_cv(type) : TypePtr();
	if (type.get() == NULL)
		return 0;
	size_t out = reinterpret_cast<uintptr_t>(type.get());
	out = dependent_cache_hash_combine(
		out,
		static_cast<size_t>(type->kind));
	out = dependent_cache_hash_combine(out,
	                                   type->is_template_specialization);
	out = dependent_cache_hash_combine(out, type->is_dependent_typename);
	out = dependent_cache_hash_combine(
		out,
		dependent_cache_string_hash(type->template_primary_name));
	return out;
}

size_t dependent_cache_instance_argument_identity(
	const pa11::TemplateInstanceArgument& argument,
	int depth);

size_t dependent_cache_template_argument_identity(
	const TemplateArgument& argument,
	int depth)
{
	size_t out = static_cast<size_t>(argument.kind);
	if (depth > 8)
		return dependent_cache_hash_combine(out, 0xfeed);
	if (argument.kind == TemplateArgumentKind::Type)
		return dependent_cache_hash_combine(
			out,
			dependent_cache_type_identity(argument.type));
	if (argument.kind == TemplateArgumentKind::Value)
	{
		out = dependent_cache_hash_combine(
			out,
			dependent_cache_type_identity(argument.type));
		out = dependent_cache_hash_combine(
			out,
			reinterpret_cast<uintptr_t>(argument.value_binding));
		out = dependent_cache_hash_combine(
			out,
			dependent_cache_string_hash(argument.value_name));
		out = dependent_cache_hash_combine(
			out,
			dependent_cache_string_hash(
				argument.value_owner_template_name));
		out = dependent_cache_hash_combine(
			out,
			dependent_cache_string_hash(argument.value_member_name));
		out = dependent_cache_hash_combine(out, argument.value);
		out = dependent_cache_hash_combine(out, argument.dependent);
		out = dependent_cache_hash_combine(out, argument.value_negated);
		for (size_t i = 0;
		     i < argument.value_owner_template_arguments.size();
		     ++i)
			out = dependent_cache_hash_combine(
				out,
				dependent_cache_instance_argument_identity(
					argument.value_owner_template_arguments[i],
					depth + 1));
		return out;
	}
	if (argument.kind == TemplateArgumentKind::Template)
	{
		out = dependent_cache_hash_combine(
			out,
			reinterpret_cast<uintptr_t>(argument.template_declaration));
		return dependent_cache_hash_combine(
			out,
			dependent_cache_string_hash(argument.value_name));
	}
	out = dependent_cache_hash_combine(
		out,
		dependent_cache_string_hash(argument.value_name));
	for (size_t i = 0; i < argument.pack.size(); ++i)
		out = dependent_cache_hash_combine(
			out,
			dependent_cache_template_argument_identity(argument.pack[i],
			                                           depth + 1));
	return out;
}

size_t dependent_cache_instance_argument_identity(
	const pa11::TemplateInstanceArgument& argument,
	int depth)
{
	size_t out = static_cast<size_t>(argument.kind);
	if (depth > 8)
		return dependent_cache_hash_combine(out, 0xbeef);
	if (argument.kind == pa11::TemplateInstanceArgumentKind::Type)
		return dependent_cache_hash_combine(
			out,
			dependent_cache_type_identity(argument.type));
	if (argument.kind == pa11::TemplateInstanceArgumentKind::Value)
	{
		out = dependent_cache_hash_combine(
			out,
			dependent_cache_type_identity(argument.type));
		out = dependent_cache_hash_combine(
			out,
			dependent_cache_string_hash(argument.value_name));
		out = dependent_cache_hash_combine(
			out,
			dependent_cache_string_hash(
				argument.value_owner_template_name));
		out = dependent_cache_hash_combine(
			out,
			dependent_cache_string_hash(argument.value_member_name));
		out = dependent_cache_hash_combine(out, argument.value);
		out = dependent_cache_hash_combine(out, argument.dependent);
		out = dependent_cache_hash_combine(out, argument.value_negated);
		for (size_t i = 0;
		     i < argument.value_owner_template_arguments.size();
		     ++i)
			out = dependent_cache_hash_combine(
				out,
				dependent_cache_instance_argument_identity(
					argument.value_owner_template_arguments[i],
					depth + 1));
		return out;
	}
	if (argument.kind == pa11::TemplateInstanceArgumentKind::Template)
	{
		out = dependent_cache_hash_combine(
			out,
			dependent_cache_string_hash(argument.template_name));
		return dependent_cache_hash_combine(out, argument.dependent);
	}
	out = dependent_cache_hash_combine(
		out,
		dependent_cache_string_hash(argument.value_name));
	out = dependent_cache_hash_combine(
		out,
		dependent_cache_string_hash(argument.template_name));
	for (size_t i = 0; i < argument.pack.size(); ++i)
		out = dependent_cache_hash_combine(
			out,
			dependent_cache_instance_argument_identity(argument.pack[i],
			                                           depth + 1));
	return out;
}

size_t dependent_value_member_cache_prefix(const TemplateArgument& arg)
{
	size_t out = dependent_cache_string_hash(arg.value_owner_template_name);
	out = dependent_cache_hash_combine(
		out,
		dependent_cache_string_hash(arg.value_member_name));
	out = dependent_cache_hash_combine(
		out,
		dependent_cache_string_hash(arg.value_name));
	for (size_t i = 0; i < arg.value_owner_template_arguments.size(); ++i)
		out = dependent_cache_hash_combine(
			out,
			dependent_cache_instance_argument_identity(
				arg.value_owner_template_arguments[i],
				0));
	return out;
}

}  // namespace

bool Parser::type_is_template_dependent(TypePtr type) const
{
	return template_type_has_template_parameter(type,
	                                           record_template_arguments_);
}

TypePtr Parser::substitute_template_type_parameter(TypePtr type,
                                                   const string& name,
                                                   TypePtr replacement) const
{
	if (type.get() == NULL)
		return type;
	if (type->kind == pa11::TypeKind::TemplateParameter &&
	    type->name == name)
		return replacement;
	if (type->kind == pa11::TypeKind::TemplateParameter &&
	    type->is_dependent_typename)
	{
		TypePtr out = pa11::make_dependent_typename_type(
			type->name,
			type->dependent_typename_qualified,
			type->dependent_typename_template_id,
			type->dependent_typename_decltype);
		out->template_primary_name = type->template_primary_name;
			for (size_t i = 0; i < type->template_arguments.size(); ++i)
			{
				TemplateArgument arg =
					template_argument_from_instance_argument(
						type->template_arguments[i]);
			arg = substitute_template_argument_type_parameter(arg,
			                                                  name,
			                                                  replacement);
			out->template_arguments.push_back(template_instance_argument(arg));
		}
		for (size_t i = 0;
		     i < type->dependent_typename_template_argument_lists.size();
		     ++i)
		{
			vector<pa11::TemplateInstanceArgument> argument_list;
			for (size_t j = 0;
			     j < type->dependent_typename_template_argument_lists[i].size();
			     ++j)
			{
				TemplateArgument arg =
					template_argument_from_instance_argument(
						type->dependent_typename_template_argument_lists[i][j]);
				arg = substitute_template_argument_type_parameter(
					arg,
					name,
					replacement);
				argument_list.push_back(template_instance_argument(arg));
			}
			out->dependent_typename_template_argument_lists.push_back(
				argument_list);
		}
		if (type->dependent_typename_qualified)
		{
		vector<string> parts;
		size_t begin = 0;
		for (;;)
		{
			size_t pos = type->name.find("::", begin);
				parts.push_back(type->name.substr(begin, pos - begin));
				if (pos == string::npos)
					break;
				begin = pos + 2;
			}
			string root_name = parts.empty() ? string() : parts[0];
			size_t root_template = root_name.find('<');
			if (root_template != string::npos)
				root_name = root_name.substr(0, root_template);
			TypePtr resolved = replacement;
			if (root_name == name && parts.size() >= 2)
			{
				bool resolved_ok = true;
				for (size_t i = 1; i < parts.size(); ++i)
				{
					TypePtr owner = resolved.get() != NULL
						? pa11::strip_cv(resolved) : TypePtr();
					if (owner.get() == NULL ||
					    owner->kind != pa11::TypeKind::Record ||
					    owner->scope == NULL)
					{
						resolved_ok = false;
						break;
					}
					try
					{
						const_cast<Parser*>(this)->
							complete_template_record(owner);
					}
					catch (const runtime_error&)
					{
					}
					string member_name = parts[i];
					size_t member_template = member_name.find('<');
					if (member_template != string::npos)
					{
						member_name =
							member_name.substr(0, member_template);
						if (out->template_arguments.empty())
						{
							resolved_ok = false;
							break;
						}
						vector<TemplateArgument> arguments;
						for (size_t j = 0;
						     j < out->template_arguments.size();
						     ++j)
							arguments.push_back(
								template_argument_from_instance_argument(
									out->template_arguments[j]));
						TemplateDeclaration* alias =
							const_cast<Parser*>(this)->
								find_alias_template(owner->scope,
								                    member_name);
						TemplateDeclaration* klass = alias == NULL
							? const_cast<Parser*>(this)->
								find_class_template(owner->scope,
								                    member_name)
							: NULL;
						if (alias == NULL && klass == NULL)
						{
							resolved_ok = false;
							break;
						}
						resolved = alias != NULL
							? const_cast<Parser*>(this)->
								instantiate_alias_template(alias,
								                           arguments)
							: const_cast<Parser*>(this)->
								instantiate_class_template(klass,
								                           arguments);
					}
					else
					{
						vector<Binding*> found =
							const_cast<Parser*>(this)->
								lookup_qualified_set(owner->scope,
								                     member_name,
								                     pa11::LOOKUP_TYPE);
						if (found.empty())
						{
							resolved_ok = false;
							break;
						}
						resolved = found[0]->type;
						const_cast<Parser*>(this)->
							complete_member_class_template_record(
								found[0]);
					}
				}
				if (resolved_ok)
					return resolved;
			}
		}
		return out;
	}
	if (type->kind == pa11::TypeKind::Cv)
		return pa11::make_cv(
			substitute_template_type_parameter(type->base,
			                                   name,
			                                   replacement),
			type->cv);
	if (type->kind == pa11::TypeKind::Pointer)
		return pa11::make_pointer(
			substitute_template_type_parameter(type->base,
			                                   name,
			                                   replacement));
	if (type->kind == pa11::TypeKind::LValueReference)
	{
		TypePtr base = substitute_template_type_parameter(type->base,
		                                                  name,
		                                                  replacement);
		if (base->kind == pa11::TypeKind::LValueReference ||
		    base->kind == pa11::TypeKind::RValueReference)
			return pa11::make_lvalue_reference(base->base);
		return pa11::make_lvalue_reference(base);
	}
	if (type->kind == pa11::TypeKind::RValueReference)
	{
		TypePtr base = substitute_template_type_parameter(type->base,
		                                                  name,
		                                                  replacement);
		if (base->kind == pa11::TypeKind::LValueReference)
			return base;
		if (base->kind == pa11::TypeKind::RValueReference)
			return pa11::make_rvalue_reference(base->base);
		return pa11::make_rvalue_reference(base);
	}
	if (type->kind == pa11::TypeKind::Array)
	{
		TypePtr out = pa11::make_array(
			substitute_template_type_parameter(type->base,
			                                   name,
			                                   replacement),
			type->unknown_bound,
			type->bound);
		out->name = type->name;
		out->tag = type->tag;
		return out;
	}
	if (type->kind == pa11::TypeKind::Function)
	{
		vector<TypePtr> params;
		bool consumed_variadic_pack = false;
		for (size_t i = 0; i < type->parameters.size(); ++i)
		{
			if (type->variadic && i + 1 == type->parameters.size())
			{
				string pack_name;
				bool has_pack_name = template_type_has_template_parameter_name(
					type->parameters[i],
					pack_name);
				if (has_pack_name && pack_name == name)
					consumed_variadic_pack = true;
			}
			params.push_back(
				substitute_template_type_parameter(type->parameters[i],
				                                   name,
				                                   replacement));
		}
		TypePtr out = pa11::make_function(
			substitute_template_type_parameter(type->base,
			                                   name,
			                                   replacement),
			params,
			type->variadic && !consumed_variadic_pack);
		out->cv = type->cv;
		out->ref_qualifier = type->ref_qualifier;
		return out;
	}
	if (type->kind == pa11::TypeKind::MemberPointer)
		return pa11::make_member_pointer(
			substitute_template_type_parameter(type->member_class,
			                                   name,
			                                   replacement),
			substitute_template_type_parameter(type->base,
			                                   name,
			                                   replacement));
	if (type->kind == pa11::TypeKind::Record &&
	    type->is_template_specialization)
	{
		for (size_t i = active_class_instantiations_.size(); i > 0; --i)
		{
			TypePtr active =
				pa11::strip_cv(active_class_instantiations_[i - 1].type);
			if (active.get() == type.get())
				return type;
		}
		TemplateArgument template_subst;
		if (!type->template_primary_name.empty() &&
		    find_template_value_substitution(type->template_primary_name,
		                                     template_subst) &&
		    template_subst.kind == TemplateArgumentKind::Template &&
		    template_subst.template_declaration != NULL)
		{
			map<const void*, vector<TemplateArgument> >::const_iterator args =
				record_template_arguments_.find(type.get());
			vector<TemplateArgument> substituted;
			if (args != record_template_arguments_.end())
			{
				for (size_t i = 0; i < args->second.size(); ++i)
				{
					TemplateArgument arg =
						substitute_template_argument_type_parameter(
							args->second[i],
							name,
							replacement);
					vector<TemplateArgument> expanded =
						expand_template_argument_pack(arg);
					for (size_t j = 0; j < expanded.size(); ++j)
					{
						TemplateArgument element =
							substitute_template_argument_type_parameter(
								expanded[j],
								name,
								replacement);
						if (element.kind == TemplateArgumentKind::Pack)
							substituted.insert(substituted.end(),
							                   element.pack.begin(),
							                   element.pack.end());
						else
							substituted.push_back(element);
					}
				}
			}
			else
			{
				for (size_t i = 0; i < type->template_arguments.size(); ++i)
				{
					TemplateArgument arg =
						raw_template_argument_from_instance_argument(
							type->template_arguments[i]);
					arg = substitute_template_argument_type_parameter(
						arg,
						name,
						replacement);
					vector<TemplateArgument> expanded =
						expand_template_argument_pack(arg);
					for (size_t j = 0; j < expanded.size(); ++j)
					{
						TemplateArgument element =
							substitute_template_argument_type_parameter(
								expanded[j],
								name,
								replacement);
						if (element.kind == TemplateArgumentKind::Pack)
							substituted.insert(substituted.end(),
							                   element.pack.begin(),
							                   element.pack.end());
						else
							substituted.push_back(element);
					}
				}
			}
			substituted = flatten_template_argument_packs(substituted);
			return template_subst.template_declaration->kind ==
				TemplateDeclarationKind::Alias
				? const_cast<Parser*>(this)->instantiate_alias_template(
					template_subst.template_declaration,
					substituted)
				: const_cast<Parser*>(this)->instantiate_class_template(
					template_subst.template_declaration,
					substituted);
		}
		map<const void*, TemplateDeclaration*>::const_iterator decl =
			record_template_declarations_.find(type.get());
		map<const void*, vector<TemplateArgument> >::const_iterator args =
			record_template_arguments_.find(type.get());
		vector<TemplateArgument> fallback_args;
		const vector<TemplateArgument>* source_args = NULL;
		if (args != record_template_arguments_.end())
			source_args = &args->second;
		else if (!type->template_arguments.empty())
		{
			for (size_t i = 0; i < type->template_arguments.size(); ++i)
				fallback_args.push_back(
					raw_template_argument_from_instance_argument(
						type->template_arguments[i]));
			source_args = &fallback_args;
		}
		TemplateDeclaration* record_decl =
			decl != record_template_declarations_.end()
			? decl->second : NULL;
		if (record_decl == NULL &&
		    source_args != NULL &&
		    !type->template_primary_name.empty())
			record_decl = const_cast<Parser*>(this)->
				find_class_template(NULL,
				                    type->template_primary_name);
		if (record_decl != NULL &&
		    find(completing_class_template_arguments_.begin(),
		         completing_class_template_arguments_.end(),
		         record_decl) !=
			    completing_class_template_arguments_.end())
			return type;
		if (record_decl != NULL && source_args != NULL)
		{
			bool needs_substitution = false;
			for (size_t i = 0; i < source_args->size(); ++i)
				if (template_argument_has_template_parameter(
					    (*source_args)[i],
					    record_template_arguments_))
					needs_substitution = true;
			if (needs_substitution)
			{
				vector<TemplateArgument> substituted;
				for (size_t i = 0; i < source_args->size(); ++i)
					substituted.push_back(
						substitute_template_argument_type_parameter(
							(*source_args)[i],
							name,
							replacement));
				return const_cast<Parser*>(this)->instantiate_class_template(
					record_decl,
					substituted);
			}
		}
	}
	return type;
}

TemplateArgument Parser::substitute_template_argument_type_parameter(
	const TemplateArgument& arg,
	const string& name,
	TypePtr replacement) const
{
	if (arg.kind == TemplateArgumentKind::Type)
		return TemplateArgument::type_arg(
			substitute_template_type_parameter(arg.type,
			                                   name,
			                                   replacement));
	if (arg.kind == TemplateArgumentKind::Value)
	{
		TemplateArgument out = arg;
		if (out.type.get() != NULL)
			out.type = substitute_template_type_parameter(out.type,
			                                             name,
			                                             replacement);
		for (size_t i = 0; i < out.value_owner_template_arguments.size(); ++i)
		{
			TemplateArgument owner_arg =
				template_argument_from_instance_argument(
					out.value_owner_template_arguments[i]);
			owner_arg = substitute_template_argument_type_parameter(
				owner_arg,
				name,
				replacement);
			out.value_owner_template_arguments[i] =
				template_instance_argument(owner_arg);
		}
		if (out.dependent &&
		    out.value_owner_template_name == name)
		{
			TypePtr owner = replacement.get() != NULL
				? pa11::strip_cv(replacement) : TypePtr();
			if (owner.get() != NULL &&
			    owner->kind == pa11::TypeKind::Record)
			{
					out.value_owner_template_name =
						owner->template_primary_name.empty()
						? owner->name
						: owner->template_primary_name;
					out.value_owner_template_arguments.clear();
					if (!owner->template_arguments.empty())
						out.value_owner_template_arguments =
							owner->template_arguments;
					else
					{
						map<const void*, vector<TemplateArgument> >::const_iterator args =
							record_template_arguments_.find(owner.get());
						if (args != record_template_arguments_.end() &&
						    !args->second.empty())
							for (size_t i = 0; i < args->second.size(); ++i)
								out.value_owner_template_arguments.push_back(
									template_instance_argument(args->second[i]));
					}
				}
			}
		return out;
	}
	if (arg.kind == TemplateArgumentKind::Pack)
	{
		vector<TemplateArgument> pack;
		for (size_t i = 0; i < arg.pack.size(); ++i)
			pack.push_back(substitute_template_argument_type_parameter(
				arg.pack[i],
				name,
				replacement));
		return TemplateArgument::pack_arg(pack);
	}
	return arg;
}

bool Parser::resolve_dependent_value_member_argument(
	const TemplateArgument& arg,
	TemplateArgument& out) const
{
	if (arg.kind != TemplateArgumentKind::Value ||
	    !arg.dependent ||
	    arg.value_owner_template_name.empty())
		return false;
	size_t active_hash = dependent_value_member_cache_prefix(arg);
	string active_key = to_string(active_hash);
	if (find(active_dependent_value_member_keys_.begin(),
	         active_dependent_value_member_keys_.end(),
	         active_key) != active_dependent_value_member_keys_.end())
		return false;
	size_t cache_hash = active_hash;
	cache_hash = dependent_cache_hash_combine(
		cache_hash,
		dependent_cache_type_identity(arg.type));
	cache_hash = dependent_cache_hash_combine(cache_hash,
	                                          arg.value_negated);
	cache_hash = dependent_cache_hash_combine(
		cache_hash,
		reinterpret_cast<uintptr_t>(current_scope()));
	cache_hash = dependent_cache_hash_combine(
		cache_hash,
		validating_template_definition_);
	cache_hash = dependent_cache_hash_combine(
		cache_hash,
		function_template_candidate_instantiation_depth_);
	for (size_t si = 0; si < template_type_substitutions_.size(); ++si)
	{
		cache_hash = dependent_cache_hash_combine(cache_hash, si);
		for (map<string, TypePtr>::const_iterator it =
			     template_type_substitutions_[si].begin();
		     it != template_type_substitutions_[si].end();
		     ++it)
		{
			cache_hash = dependent_cache_hash_combine(
				cache_hash,
				dependent_cache_string_hash(it->first));
			cache_hash = dependent_cache_hash_combine(
				cache_hash,
				dependent_cache_type_identity(it->second));
		}
	}
	for (size_t si = 0; si < template_value_substitutions_.size(); ++si)
	{
		cache_hash = dependent_cache_hash_combine(cache_hash, si);
		for (map<string, TemplateArgument>::const_iterator it =
			     template_value_substitutions_[si].begin();
		     it != template_value_substitutions_[si].end();
		     ++it)
		{
			cache_hash = dependent_cache_hash_combine(
				cache_hash,
				dependent_cache_string_hash(it->first));
			cache_hash = dependent_cache_hash_combine(
				cache_hash,
				dependent_cache_template_argument_identity(it->second,
				                                           0));
		}
	}
	string cache_key = to_string(cache_hash);
	map<string, TemplateArgument>::const_iterator cached =
		dependent_value_member_argument_cache_.find(cache_key);
	if (cached != dependent_value_member_argument_cache_.end())
	{
		out = cached->second;
		return true;
	}
	auto cache_result = [&](const TemplateArgument& result) -> bool {
		dependent_value_member_argument_cache_[cache_key] = result;
		out = result;
		return true;
	};
	struct ActiveDependentValueMember
	{
		vector<string>& keys;
		ActiveDependentValueMember(vector<string>& k, const string& key)
		  : keys(k)
		{
			keys.push_back(key);
		}
		~ActiveDependentValueMember()
		{
			keys.pop_back();
		}
	} active_dependent_value_member(active_dependent_value_member_keys_,
	                                active_key);
	vector<TemplateArgument> owner_args;
	bool still_dependent = false;
	for (size_t i = 0; i < arg.value_owner_template_arguments.size(); ++i)
	{
		TemplateArgument owner_arg =
			template_argument_from_instance_argument(
				arg.value_owner_template_arguments[i]);
		owner_arg = substitute_template_argument(owner_arg);
		if (owner_arg.kind == TemplateArgumentKind::Type &&
		    owner_arg.type.get() != NULL &&
		    owner_arg.type->is_dependent_typename)
		{
			try
			{
				TypePtr resolved =
					resolve_dependent_typename_type(owner_arg.type);
				if (resolved.get() != NULL)
				{
					owner_arg.type = substitute_template_type(resolved);
					owner_arg.dependent = type_structurally_dependent(
						owner_arg.type);
				}
			}
			catch (const runtime_error&)
			{
			}
		}
		if (template_argument_has_template_parameter(
			    owner_arg,
			    record_template_arguments_))
			still_dependent = true;
		owner_args.push_back(owner_arg);
	}
		if (still_dependent)
		{
			return false;
		}
			string trait_owner_unqualified = arg.value_owner_template_name;
		size_t owner_sep = trait_owner_unqualified.rfind("::");
		if (owner_sep != string::npos)
			trait_owner_unqualified =
				trait_owner_unqualified.substr(owner_sep + 2);
		auto bool_result = [&](bool value) -> bool {
			TemplateArgument result = TemplateArgument::value_arg(
				pa11::make_fundamental(FT_BOOL),
				arg.value_negated ? (value ? 0 : 1) : (value ? 1 : 0));
			result.value_name = arg.value_name;
			return cache_result(result);
		};
		function<void(vector<TemplateArgument>&, const TemplateArgument&)>
			append_trait_arg =
				[&](vector<TemplateArgument>& out,
				    const TemplateArgument& elem) {
					if (elem.kind == TemplateArgumentKind::Pack)
					{
						for (size_t pi = 0; pi < elem.pack.size(); ++pi)
							append_trait_arg(out, elem.pack[pi]);
					}
					else
						out.push_back(elem);
				};
		function<bool(TypePtr, bool&)> evaluate_trait_type =
			[&](TypePtr trait_type, bool& value) -> bool {
				TypePtr record = trait_type.get() != NULL
					? pa11::strip_cv(trait_type) : TypePtr();
				if (record.get() == NULL ||
				    record->kind != pa11::TypeKind::Record)
					return false;
				string primary = record->template_primary_name;
				if (primary.empty() && record->scope != NULL)
					primary = record->scope->name;
				size_t primary_sep = primary.rfind("::");
				if (primary_sep != string::npos)
					primary = primary.substr(primary_sep + 2);
				vector<TemplateArgument> trait_args;
				map<const void*, vector<TemplateArgument> >::const_iterator stored =
					record_template_arguments_.find(record.get());
				if (stored != record_template_arguments_.end())
					for (size_t ai = 0; ai < stored->second.size(); ++ai)
						append_trait_arg(trait_args, stored->second[ai]);
				else
					for (size_t ai = 0; ai < record->template_arguments.size(); ++ai)
						append_trait_arg(
							trait_args,
							template_argument_from_instance_argument(
								record->template_arguments[ai]));
				if ((primary == "integral_constant" ||
				     primary == "__bool_constant") &&
				    trait_args.size() >= 2 &&
				    trait_args[1].kind == TemplateArgumentKind::Value &&
				    !trait_args[1].dependent)
				{
					value = trait_args[1].value != 0;
					return true;
				}
				if ((primary == "is_same" || primary == "__are_same") &&
				    trait_args.size() >= 2 &&
				    trait_args[0].kind == TemplateArgumentKind::Type &&
				    trait_args[1].kind == TemplateArgumentKind::Type)
				{
					value = pa11::same_type(trait_args[0].type,
					                        trait_args[1].type);
					return true;
				}
				if (primary == "is_class" &&
				    !trait_args.empty() &&
				    trait_args[0].kind == TemplateArgumentKind::Type)
				{
					TypePtr bare = trait_args[0].type.get() != NULL
						? pa11::strip_cv(trait_args[0].type) : TypePtr();
					value = bare.get() != NULL &&
					        bare->kind == pa11::TypeKind::Record;
					return true;
				}
				if (((hosted_compatibility_ && primary == "is_convertible") ||
				     primary == "__is_convertible") &&
				    trait_args.size() >= 2 &&
				    trait_args[0].kind == TemplateArgumentKind::Type &&
				    trait_args[1].kind == TemplateArgumentKind::Type)
				{
					Expr probe;
					probe.valid = true;
					probe.type = trait_args[0].type;
					probe.category = pa11::is_reference_type(trait_args[0].type)
						? ValueCategory::LValue : ValueCategory::PRValue;
					probe.node = Node("type-trait-probe " +
					                  pa11::describe_type(trait_args[0].type));
					try
					{
						value = const_cast<Parser*>(this)->
							convert_to(probe, trait_args[1].type).viable;
					}
					catch (const runtime_error&)
					{
						value = false;
					}
					return true;
				}
				if (primary == "__not_" &&
				    trait_args.size() == 1 &&
				    trait_args[0].kind == TemplateArgumentKind::Type)
				{
					bool inner = false;
					if (!evaluate_trait_type(trait_args[0].type, inner))
						return false;
					value = !inner;
					return true;
				}
					if (primary == "__and_" || primary == "__or_")
					{
						value = primary == "__and_";
						for (size_t ai = 0; ai < trait_args.size(); ++ai)
					{
						if (trait_args[ai].kind != TemplateArgumentKind::Type)
							return false;
						bool elem = false;
						if (!evaluate_trait_type(trait_args[ai].type, elem))
							return false;
						if (primary == "__and_" && !elem)
						{
							value = false;
							return true;
						}
						if (primary == "__or_" && elem)
						{
							value = true;
							return true;
						}
						}
						return true;
					}
					auto evaluate_dependent_value_typename =
						[&](TypePtr value_type, bool& value_out) -> bool {
							if (value_type.get() == NULL ||
							    !value_type->is_dependent_typename)
								return false;
							size_t member_pos = value_type->name.rfind("::");
							if (member_pos == string::npos)
								return false;
							string owner_name =
								value_type->name.substr(0, member_pos);
							string member_name =
								value_type->name.substr(member_pos + 2);
							size_t owner_template = owner_name.find('<');
							if (owner_template != string::npos)
								owner_name = owner_name.substr(0,
								                               owner_template);
							size_t nested = owner_name.rfind("::");
							if (nested != string::npos)
								owner_name = owner_name.substr(nested + 2);
							if (member_name == "value" ||
							    member_name == "__value")
							{
								vector<TemplateArgument> owner_args;
								const vector<pa11::TemplateInstanceArgument>* stored_args =
									&value_type->template_arguments;
								if (stored_args->empty() &&
								    !value_type->
									    dependent_typename_template_argument_lists.empty())
									stored_args =
										&value_type->
											dependent_typename_template_argument_lists[0];
								for (size_t ai = 0; ai < stored_args->size(); ++ai)
									owner_args.push_back(
										substitute_template_argument(
											template_argument_from_instance_argument(
												(*stored_args)[ai])));
								owner_args =
									flatten_template_argument_packs(owner_args);
								TemplateDeclaration* owner_template =
									const_cast<Parser*>(this)->find_class_template(
										NULL,
										owner_name);
								if (owner_template == NULL)
									for (map<Scope*, map<string, TemplateDeclaration*> >::
										     const_iterator sit =
											     class_templates_.begin();
									     sit != class_templates_.end() &&
										     owner_template == NULL;
									     ++sit)
									{
										map<string, TemplateDeclaration*>::
											const_iterator found =
												sit->second.find(owner_name);
										if (found != sit->second.end())
											owner_template = found->second;
									}
								if (owner_template != NULL)
								{
									TypePtr owner_type =
										const_cast<Parser*>(this)->
											instantiate_class_template(
												owner_template,
												owner_args);
									if (evaluate_trait_type(owner_type, value_out))
										return true;
								}
							}
							TemplateArgument value_arg =
								TemplateArgument::dependent_value_arg(
									pa11::make_fundamental(FT_BOOL));
							value_arg.value_name = value_type->name;
							value_arg.value_owner_template_name = owner_name;
							value_arg.value_member_name = member_name;
							value_arg.value_owner_template_arguments =
								value_type->template_arguments;
							if (value_arg.value_owner_template_arguments.empty() &&
							    !value_type->
								    dependent_typename_template_argument_lists.empty())
								value_arg.value_owner_template_arguments =
									value_type->
										dependent_typename_template_argument_lists[0];
							TemplateArgument resolved_value;
							if (!resolve_dependent_value_member_argument(
								    value_arg,
								    resolved_value))
								return false;
							resolved_value =
								substitute_template_argument(resolved_value);
							if (resolved_value.kind ==
								    TemplateArgumentKind::Value &&
							    !resolved_value.dependent)
							{
								value_out = resolved_value.value != 0;
								return true;
							}
							if (resolved_value.kind ==
							    TemplateArgumentKind::Type)
								return evaluate_trait_type(resolved_value.type,
								                           value_out);
							return false;
						};
					auto evaluate_conditional_typename =
						[&](TypePtr conditional_type, bool& conditional_value) -> bool {
							if (conditional_type.get() == NULL ||
							    !conditional_type->is_dependent_typename)
								return false;
							vector<string> conditional_parts;
							size_t begin = 0;
							for (;;)
							{
								size_t pos =
									conditional_type->name.find("::", begin);
								conditional_parts.push_back(
									conditional_type->name.substr(begin,
									                              pos - begin));
								if (pos == string::npos)
									break;
								begin = pos + 2;
							}
							if (conditional_parts.size() < 2 ||
							    conditional_parts[1] != "type")
								return false;
							string root = conditional_parts[0];
							size_t root_template = root.find('<');
							if (root_template != string::npos)
								root = root.substr(0, root_template);
							if (root != "conditional")
								return false;
							size_t list_index = 0;
							vector<TemplateArgument> stored;
							if (!dependent_typename_template_argument_list(
								    conditional_type,
								    list_index,
								    stored))
								return false;
							vector<TemplateArgument> conditional_args;
							for (size_t ai = 0; ai < stored.size(); ++ai)
								conditional_args.push_back(
									substitute_template_argument(stored[ai]));
							conditional_args =
								flatten_template_argument_packs(conditional_args);
							bool condition_value = false;
							bool condition_known = false;
							if (conditional_args.size() >= 3 &&
							    conditional_args[0].kind ==
								    TemplateArgumentKind::Value &&
							    !conditional_args[0].dependent)
							{
								condition_value =
									conditional_args[0].value != 0;
								condition_known = true;
							}
							else if (conditional_args.size() >= 3 &&
							         conditional_args[0].kind ==
								         TemplateArgumentKind::Type &&
							         (evaluate_trait_type(
								          conditional_args[0].type,
								          condition_value) ||
							          evaluate_dependent_value_typename(
								          conditional_args[0].type,
								          condition_value)))
								condition_known = true;
							if (conditional_args.size() < 3 ||
							    !condition_known ||
							    conditional_args[1].kind !=
								    TemplateArgumentKind::Type ||
							    conditional_args[2].kind !=
								    TemplateArgumentKind::Type)
								return false;
							TypePtr selected = condition_value
								? conditional_args[1].type
								: conditional_args[2].type;
							if (conditional_parts.size() == 2)
								return evaluate_trait_type(selected,
								                           conditional_value);
							TypePtr resolved =
								resolve_dependent_typename_type(
									conditional_type);
							if (resolved.get() != NULL)
								return evaluate_trait_type(resolved,
								                           conditional_value);
							return false;
						};
					try
					{
						const_cast<Parser*>(this)->complete_template_record(record);
					}
					catch (const runtime_error&)
					{
					}
					TypePtr base = record->base;
					if (base.get() != NULL)
					{
						if (evaluate_conditional_typename(base, value))
							return true;
						try
						{
							base = substitute_template_type_in_scope(base,
							                                         record->scope);
						}
						catch (const runtime_error&)
						{
						}
						if (base.get() != NULL && base->is_dependent_typename)
						{
							TypePtr resolved =
								resolve_dependent_typename_type(base);
							if (resolved.get() != NULL)
								base = resolved;
						}
						if (base.get() != NULL && base != trait_type)
							return evaluate_trait_type(base, value);
					}
					return false;
				};
			if ((arg.value_member_name == "value" ||
			     arg.value_member_name == "__value") &&
			    trait_owner_unqualified == "conditional" &&
			    owner_args.size() >= 3)
			{
				bool condition_value = false;
				bool condition_known = false;
				if (owner_args[0].kind == TemplateArgumentKind::Value &&
				    !owner_args[0].dependent)
				{
					condition_value = owner_args[0].value != 0;
					condition_known = true;
				}
				else if (owner_args[0].kind == TemplateArgumentKind::Type &&
				         evaluate_trait_type(owner_args[0].type,
				                             condition_value))
					condition_known = true;
				const TemplateArgument& selected =
					condition_value ? owner_args[1] : owner_args[2];
				if (condition_known &&
				    selected.kind == TemplateArgumentKind::Type)
				{
					bool value = false;
					if (evaluate_trait_type(selected.type, value))
						return bool_result(value);
				}
			}
			if ((arg.value_member_name == "value" ||
			     arg.value_member_name == "__value") &&
			    (trait_owner_unqualified == "is_class" ||
			     (hosted_compatibility_ &&
		      trait_owner_unqualified == "is_convertible") ||
		     trait_owner_unqualified == "__is_convertible" ||
		     trait_owner_unqualified == "__and_" ||
		     trait_owner_unqualified == "__or_" ||
		     trait_owner_unqualified == "__not_"))
		{
			bool value = false;
			TypePtr synthetic = pa11::make_record_type(
				trait_owner_unqualified + "<>",
				"struct",
				false,
				NULL);
			synthetic->template_primary_name = trait_owner_unqualified;
			synthetic->template_arguments =
				template_instance_arguments(owner_args);
			if (evaluate_trait_type(synthetic, value))
				return bool_result(value);
		}
		if ((arg.value_member_name == "value" ||
		     arg.value_member_name == "__value") &&
		    (trait_owner_unqualified == "is_same" ||
		     trait_owner_unqualified == "__are_same") &&
		    owner_args.size() >= 2 &&
	    owner_args[0].kind == TemplateArgumentKind::Type &&
	    owner_args[1].kind == TemplateArgumentKind::Type)
	{
		bool value = pa11::same_type(owner_args[0].type,
		                             owner_args[1].type);
			return bool_result(value);
		}
		if ((arg.value_member_name == "value" ||
		     arg.value_member_name == "__value") &&
		    (trait_owner_unqualified == "__is_convertible" ||
		     (hosted_compatibility_ &&
		      trait_owner_unqualified == "is_convertible")) &&
		    owner_args.size() >= 2 &&
		    owner_args[0].kind == TemplateArgumentKind::Type &&
		    owner_args[1].kind == TemplateArgumentKind::Type)
	{
		Expr probe;
		probe.valid = true;
		probe.type = owner_args[0].type;
		probe.category = pa11::is_reference_type(owner_args[0].type)
			? ValueCategory::LValue : ValueCategory::PRValue;
		probe.node = Node("type-trait-probe " +
		                  pa11::describe_type(owner_args[0].type));
		bool value = false;
		try
		{
			value = const_cast<Parser*>(this)->
				convert_to(probe, owner_args[1].type).viable;
		}
		catch (const runtime_error&)
		{
			value = false;
		}
		TemplateArgument result = TemplateArgument::value_arg(
			pa11::make_fundamental(FT_BOOL),
			arg.value_negated ? (value ? 0 : 1) : (value ? 1 : 0));
		result.value_name = arg.value_name;
		return cache_result(result);
	}
	if (arg.value_member_name.empty())
	{
		TemplateDeclaration* declaration = NULL;
		for (Scope* cur = current_scope(); cur != NULL && declaration == NULL;
		     cur = cur->parent)
		{
			map<Scope*, map<string, vector<TemplateDeclaration*> > >::const_iterator
				sit = variable_templates_.find(cur);
			if (sit == variable_templates_.end())
				continue;
			map<string, vector<TemplateDeclaration*> >::const_iterator it =
				sit->second.find(arg.value_owner_template_name);
			if (it != sit->second.end() && !it->second.empty())
				declaration = it->second[0];
		}
		if (declaration == NULL)
			for (map<Scope*, map<string, vector<TemplateDeclaration*> > >::const_iterator
				     sit = variable_templates_.begin();
			     sit != variable_templates_.end() && declaration == NULL;
			     ++sit)
			{
				map<string, vector<TemplateDeclaration*> >::const_iterator it =
					sit->second.find(arg.value_owner_template_name);
				if (it != sit->second.end() && !it->second.empty())
					declaration = it->second[0];
			}
		if (declaration == NULL)
			return false;
		Binding* binding =
			const_cast<Parser*>(this)->instantiate_variable_template(
				declaration,
				owner_args);
		if (binding == NULL || !binding->has_constant)
			throw runtime_error("dependent variable template not resolved");
		TemplateArgument result = TemplateArgument::value_arg(
			arg.value_negated
			? pa11::make_fundamental(FT_BOOL)
			: expression_object_type(binding->type),
			arg.value_negated
			? (binding->constant_value == 0 ? 1 : 0)
			: binding->constant_value);
		result.value_name = arg.value_name;
		return cache_result(result);
	}
	TypePtr owner;
	if (!arg.value_owner_template_name.empty())
	{
		TemplateArgument owner_pack;
		if (find_template_value_substitution(
			    arg.value_owner_template_name,
			    owner_pack) &&
		    owner_pack.kind == TemplateArgumentKind::Pack)
		{
			if (owner_pack.pack.size() != 1 ||
			    owner_pack.pack[0].kind != TemplateArgumentKind::Type)
				return false;
			owner = owner_pack.pack[0].type;
		}
		if (owner.get() == NULL)
		{
			TypePtr owner_parameter =
				pa11::make_template_parameter_type(
					arg.value_owner_template_name);
			TypePtr substituted_owner =
				substitute_template_type(owner_parameter);
			TypePtr bare_substituted =
				substituted_owner.get() != NULL
				? pa11::strip_cv(substituted_owner) : TypePtr();
			if (bare_substituted.get() != NULL &&
			    bare_substituted->kind != pa11::TypeKind::TemplateParameter)
				owner = substituted_owner;
		}
	}
	TemplateDeclaration* alias_declaration = NULL;
	TemplateDeclaration* declaration = NULL;
	if (owner.get() == NULL)
	{
		for (Scope* cur = current_scope();
		     cur != NULL && alias_declaration == NULL && declaration == NULL;
		     cur = cur->parent)
		{
			alias_declaration =
				const_cast<Parser*>(this)->find_alias_template(
					cur,
					arg.value_owner_template_name);
			if (alias_declaration == NULL)
				declaration =
					const_cast<Parser*>(this)->find_class_template(
						cur,
						arg.value_owner_template_name);
		}
		if (alias_declaration == NULL && declaration == NULL)
			alias_declaration =
				const_cast<Parser*>(this)->find_alias_template(
					NULL,
					arg.value_owner_template_name);
		if (alias_declaration == NULL && declaration == NULL)
			for (map<Scope*, map<string, TemplateDeclaration*> >::const_iterator
				     sit = alias_templates_.begin();
			     sit != alias_templates_.end() && alias_declaration == NULL;
			     ++sit)
			{
				map<string, TemplateDeclaration*>::const_iterator it =
					sit->second.find(arg.value_owner_template_name);
				if (it != sit->second.end())
					alias_declaration = it->second;
			}
		if (alias_declaration == NULL && declaration == NULL)
			declaration =
				const_cast<Parser*>(this)->find_class_template(
					NULL,
					arg.value_owner_template_name);
		if (alias_declaration == NULL && declaration == NULL)
		{
			for (map<Scope*, map<string, TemplateDeclaration*> >::const_iterator
				     sit = class_templates_.begin();
			     sit != class_templates_.end() && declaration == NULL;
			     ++sit)
			{
				map<string, TemplateDeclaration*>::const_iterator it =
					sit->second.find(arg.value_owner_template_name);
				if (it != sit->second.end())
					declaration = it->second;
			}
		}
			if (alias_declaration == NULL && declaration == NULL)
			{
				return false;
			}
			if (declaration != NULL && !owner_args.empty())
			{
				bool owner_args_too_large = true;
				for (size_t pi = 0; pi < declaration->parameters.size(); ++pi)
					if (declaration->parameters[pi].is_pack)
						owner_args_too_large = false;
				owner_args_too_large =
					owner_args_too_large &&
					owner_args.size() > declaration->parameters.size();
				if (owner_args_too_large)
				{
					for (size_t ci = 0;
					     ci < declaration->class_specialization_declarations.size() &&
					     owner_args_too_large;
					     ++ci)
					{
						TemplateDeclaration* candidate =
							declaration->class_specialization_declarations[ci];
						if (candidate == NULL ||
						    candidate->parameters.size() != owner_args.size())
							continue;
						Parser* self = const_cast<Parser*>(this);
						vector<map<string, TypePtr> > save_type_subst =
							self->template_type_substitutions_;
						vector<map<string, TemplateArgument> > save_value_subst =
							self->template_value_substitutions_;
						vector<set<string> > save_pack_subst =
							self->template_type_parameter_packs_;
						map<string, TypePtr> type_subst;
						map<string, TemplateArgument> value_subst;
						set<string> pack_subst;
						for (size_t pi = 0; pi < candidate->parameters.size(); ++pi)
						{
							const TemplateParameterInfo& parameter =
								candidate->parameters[pi];
							if (parameter.name.empty())
								continue;
							const TemplateArgument& owner_arg = owner_args[pi];
							if (parameter.kind == TemplateParameterKind::Type)
							{
								if (parameter.is_pack)
								{
									type_subst[parameter.name] =
										pa11::make_template_parameter_type(
											parameter.name);
									value_subst[parameter.name] = owner_arg;
									pack_subst.insert(parameter.name);
								}
								else if (owner_arg.kind == TemplateArgumentKind::Type)
									type_subst[parameter.name] = owner_arg.type;
							}
							else
								value_subst[parameter.name] = owner_arg;
						}
						self->template_type_substitutions_.push_back(type_subst);
						self->template_value_substitutions_.push_back(value_subst);
						self->template_type_parameter_packs_.push_back(pack_subst);
						vector<TemplateArgument> recovered_args;
						try
						{
							for (size_t pi = 0;
							     pi < candidate->class_specialization_pattern.size();
							     ++pi)
								recovered_args.push_back(
									substitute_template_argument(
										candidate->
											class_specialization_pattern[pi]));
						}
						catch (...)
						{
							self->template_type_substitutions_ = save_type_subst;
							self->template_value_substitutions_ = save_value_subst;
							self->template_type_parameter_packs_ = save_pack_subst;
							throw;
						}
						self->template_type_substitutions_ = save_type_subst;
						self->template_value_substitutions_ = save_value_subst;
						self->template_type_parameter_packs_ = save_pack_subst;
						bool recovered_too_large = true;
						for (size_t pi = 0; pi < declaration->parameters.size(); ++pi)
							if (declaration->parameters[pi].is_pack)
								recovered_too_large = false;
						recovered_too_large =
							recovered_too_large &&
							recovered_args.size() > declaration->parameters.size();
						if (!recovered_too_large)
						{
							owner_args = recovered_args;
							owner_args_too_large = false;
						}
					}
					if (owner_args_too_large)
						for (size_t ai = active_class_instantiations_.size();
						     ai > 0;
						     --ai)
						{
							const ActiveClassInstantiation& active =
								active_class_instantiations_[ai - 1];
							if (active.declaration == NULL ||
							    active.declaration->name != declaration->name ||
							    active.declaration->owner != declaration->owner)
								continue;
							TypePtr active_type = active.type.get() != NULL
								? pa11::strip_cv(active.type) : TypePtr();
							if (active_type.get() == NULL ||
							    active_type->kind != pa11::TypeKind::Record ||
							    active_type->template_arguments.empty())
								continue;
							vector<TemplateArgument> canonical_args;
							for (size_t ti = 0;
							     ti < active_type->template_arguments.size();
							     ++ti)
								canonical_args.push_back(
									template_argument_from_instance_argument(
										active_type->template_arguments[ti]));
							owner_args = canonical_args;
							break;
						}
				}
			}
			owner = alias_declaration != NULL
				? const_cast<Parser*>(this)->instantiate_alias_template(
					alias_declaration,
					owner_args)
			: const_cast<Parser*>(this)->instantiate_class_template(
				declaration,
				owner_args);
	}
	owner = owner.get() != NULL ? pa11::strip_cv(owner) : TypePtr();
	if (owner.get() == NULL ||
	    owner->kind != pa11::TypeKind::Record ||
	    owner->scope == NULL)
		return false;
	string owner_primary_precomplete = owner->template_primary_name.empty()
		? owner->name : owner->template_primary_name;
	size_t owner_name_pos_precomplete =
		owner_primary_precomplete.rfind("::");
	string owner_unqualified_precomplete =
		owner_name_pos_precomplete == string::npos
		? owner_primary_precomplete
		: owner_primary_precomplete.substr(owner_name_pos_precomplete + 2);
	size_t owner_template_pos_precomplete =
		owner_unqualified_precomplete.find('<');
	if (owner_template_pos_precomplete != string::npos)
		owner_unqualified_precomplete =
			owner_unqualified_precomplete.substr(0,
			                                     owner_template_pos_precomplete);
	if (hosted_compatibility_ &&
	    arg.value_member_name == "value" &&
	    owner_unqualified_precomplete == "_Callable")
	{
		auto normalize_callable_type = [&](TypePtr type) -> TypePtr {
			try
			{
				type = substitute_template_type(type);
			}
			catch (const runtime_error&)
			{
			}
			if (type.get() == NULL)
				return type;
			if (type->kind == pa11::TypeKind::LValueReference ||
			    type->kind == pa11::TypeKind::RValueReference)
			{
				TypePtr base = type->base;
				try
				{
					base = substitute_template_type(base);
				}
				catch (const runtime_error&)
				{
				}
				if (base.get() != NULL && base->is_dependent_typename)
				{
					TypePtr resolved =
						resolve_dependent_typename_type(base);
					if (resolved.get() != NULL)
						base = resolved;
				}
				if (base != type->base)
					return type->kind == pa11::TypeKind::LValueReference
						? pa11::make_lvalue_reference(base)
						: pa11::make_rvalue_reference(base);
				return type;
			}
			if (type->is_dependent_typename)
			{
				TypePtr resolved = resolve_dependent_typename_type(type);
				if (resolved.get() != NULL)
					return resolved;
			}
			TypePtr bare = pa11::strip_cv(type);
			if (bare.get() != NULL &&
			    bare->kind == pa11::TypeKind::Record &&
			    bare->scope != NULL)
			{
				string primary = bare->template_primary_name.empty()
					? bare->name : bare->template_primary_name;
				size_t sep = primary.rfind("::");
				if (sep != string::npos)
					primary = primary.substr(sep + 2);
				size_t arg_pos = primary.find('<');
				if (arg_pos != string::npos)
					primary = primary.substr(0, arg_pos);
				if (primary == "decay")
				{
					try
					{
						const_cast<Parser*>(this)->
							complete_template_record(bare);
					}
					catch (const runtime_error&)
					{
					}
					try
					{
						vector<Binding*> found =
							const_cast<Parser*>(this)->
								lookup_qualified_set(
									bare->scope,
									"type",
									pa11::LOOKUP_TYPE);
						if (!found.empty() &&
						    found[0]->type.get() != NULL)
							return substitute_template_type_in_scope(
								found[0]->type,
								bare->scope);
					}
					catch (const runtime_error&)
					{
					}
				}
			}
			return type;
		};
		auto append_invoke_result_call_types =
			[&](TypePtr invoke_result,
			    vector<TypePtr>& call_types) -> bool {
				TypePtr bare = invoke_result.get() != NULL
					? pa11::strip_cv(invoke_result) : TypePtr();
				if (bare.get() == NULL ||
				    bare->kind != pa11::TypeKind::Record)
					return false;
				string primary = bare->template_primary_name.empty()
					? bare->name : bare->template_primary_name;
				size_t sep = primary.rfind("::");
				if (sep != string::npos)
					primary = primary.substr(sep + 2);
				size_t arg_pos = primary.find('<');
				if (arg_pos != string::npos)
					primary = primary.substr(0, arg_pos);
				if (primary != "__invoke_result")
					return false;
				vector<TemplateArgument> invoke_args;
				map<const void*, vector<TemplateArgument> >::const_iterator
					stored = record_template_arguments_.find(bare.get());
				if (stored != record_template_arguments_.end())
					invoke_args = stored->second;
				else
					for (size_t ti = 0;
					     ti < bare->template_arguments.size();
					     ++ti)
						invoke_args.push_back(
							template_argument_from_instance_argument(
								bare->template_arguments[ti]));
				invoke_args = flatten_template_argument_packs(invoke_args);
				for (size_t ti = 0; ti < invoke_args.size(); ++ti)
				{
					TemplateArgument invoke_arg =
						substitute_template_argument(invoke_args[ti]);
					if (invoke_arg.kind == TemplateArgumentKind::Pack)
					{
						for (size_t pi = 0;
						     pi < invoke_arg.pack.size();
						     ++pi)
						{
							TemplateArgument elem =
								substitute_template_argument(
									invoke_arg.pack[pi]);
							if (elem.kind != TemplateArgumentKind::Type)
								return false;
							call_types.push_back(
								normalize_callable_type(elem.type));
						}
						continue;
					}
					if (invoke_arg.kind != TemplateArgumentKind::Type)
						return false;
					call_types.push_back(
						normalize_callable_type(invoke_arg.type));
				}
				return !call_types.empty();
			};
		vector<TemplateArgument> callable_args;
		map<const void*, vector<TemplateArgument> >::const_iterator stored =
			record_template_arguments_.find(owner.get());
		if (stored != record_template_arguments_.end())
			callable_args = stored->second;
		else
			for (size_t ti = 0; ti < owner->template_arguments.size(); ++ti)
				callable_args.push_back(
					template_argument_from_instance_argument(
						owner->template_arguments[ti]));
		callable_args = flatten_template_argument_packs(callable_args);
		for (size_t ci = 0; ci < callable_args.size(); ++ci)
			callable_args[ci] = substitute_template_argument(
				callable_args[ci]);
		TypePtr result_type;
		for (size_t si = template_type_substitutions_.size(); si > 0; --si)
		{
			map<string, TypePtr>::const_iterator it =
				template_type_substitutions_[si - 1].find("_Res");
			if (it != template_type_substitutions_[si - 1].end())
			{
				result_type = normalize_callable_type(it->second);
				break;
			}
		}
		vector<TypePtr> call_types;
		if (callable_args.size() >= 3 &&
		    callable_args[2].kind == TemplateArgumentKind::Type)
			append_invoke_result_call_types(callable_args[2].type,
			                                call_types);
		if (call_types.empty() &&
		    callable_args.size() >= 2 &&
		    callable_args[1].kind == TemplateArgumentKind::Type)
		{
			TypePtr dfunc = normalize_callable_type(callable_args[1].type);
			if (dfunc.get() != NULL)
				call_types.push_back(pa11::make_lvalue_reference(dfunc));
			for (size_t si = template_value_substitutions_.size();
			     si > 0;
			     --si)
			{
				map<string, TemplateArgument>::const_iterator it =
					template_value_substitutions_[si - 1].find("_ArgTypes");
				if (it == template_value_substitutions_[si - 1].end() ||
				    it->second.kind != TemplateArgumentKind::Pack)
					continue;
				for (size_t pi = 0; pi < it->second.pack.size(); ++pi)
					if (it->second.pack[pi].kind ==
					    TemplateArgumentKind::Type)
						call_types.push_back(normalize_callable_type(
							it->second.pack[pi].type));
				break;
			}
		}
		bool concrete = result_type.get() != NULL && !call_types.empty();
		if (concrete && type_structurally_dependent(result_type))
			concrete = false;
		for (size_t ci = 0; ci < call_types.size(); ++ci)
			if (type_structurally_dependent(call_types[ci]))
				concrete = false;
		if (concrete)
		{
			vector<TypePtr> trait_types;
			trait_types.push_back(result_type);
			trait_types.insert(trait_types.end(),
			                   call_types.begin(),
			                   call_types.end());
			bool value = const_cast<Parser*>(this)->
				is_invocable_r_type_trait(trait_types, false);
			return bool_result(value);
		}
	}
	const_cast<Parser*>(this)->complete_template_record(owner);
	string owner_primary = owner->template_primary_name;
	size_t owner_name_pos = owner_primary.rfind("::");
	string owner_unqualified = owner_name_pos == string::npos
		? owner_primary : owner_primary.substr(owner_name_pos + 2);
	if (hosted_compatibility_ &&
	    arg.value_member_name == "value" &&
	    owner_unqualified == "__is_nothrow_invocable")
	{
		map<const void*, vector<TemplateArgument> >::const_iterator args =
			record_template_arguments_.find(owner.get());
		if (args != record_template_arguments_.end())
		{
			vector<TypePtr> types;
			bool type_args = true;
			for (size_t i = 0; i < args->second.size(); ++i)
			{
				const TemplateArgument& owner_arg = args->second[i];
				if (owner_arg.kind == TemplateArgumentKind::Type)
					types.push_back(owner_arg.type);
				else if (owner_arg.kind == TemplateArgumentKind::Pack)
				{
					for (size_t j = 0; j < owner_arg.pack.size(); ++j)
					{
						if (owner_arg.pack[j].kind !=
						    TemplateArgumentKind::Type)
						{
							type_args = false;
							break;
						}
						types.push_back(owner_arg.pack[j].type);
					}
				}
				else
					type_args = false;
				if (!type_args)
					break;
			}
			if (type_args)
			{
				bool value = const_cast<Parser*>(this)->
					is_invocable_type_trait(types, true);
				TemplateArgument result = TemplateArgument::value_arg(
					pa11::make_fundamental(FT_BOOL),
					arg.value_negated ? (value ? 0 : 1)
					                  : (value ? 1 : 0));
				result.value_name = arg.value_name;
				return cache_result(result);
			}
		}
	}
	vector<Binding*> found =
		const_cast<Parser*>(this)->lookup_qualified_set(
			owner->scope,
			arg.value_member_name,
			pa11::LOOKUP_VALUE);
	if (found.empty())
	{
		vector<string> parts;
		size_t begin = 0;
		for (;;)
		{
			size_t pos = arg.value_name.find("::", begin);
			parts.push_back(arg.value_name.substr(begin, pos - begin));
			if (pos == string::npos)
				break;
			begin = pos + 2;
		}
		if (parts.size() > 2)
		{
			TypePtr nested_owner = owner;
			for (size_t pi = 1; pi + 1 < parts.size(); ++pi)
			{
				TypePtr bare_nested = nested_owner.get() != NULL
					? pa11::strip_cv(nested_owner) : TypePtr();
				if (bare_nested.get() == NULL ||
				    bare_nested->kind != pa11::TypeKind::Record ||
				    bare_nested->scope == NULL)
					break;
				const_cast<Parser*>(this)->complete_template_record(
					bare_nested);
				vector<Binding*> nested_type =
					const_cast<Parser*>(this)->lookup_qualified_set(
						bare_nested->scope,
						parts[pi],
						pa11::LOOKUP_TYPE);
				if (nested_type.empty())
				{
					nested_owner.reset();
					break;
				}
				const_cast<Parser*>(this)->
					complete_member_class_template_record(nested_type[0]);
				nested_owner = substitute_template_type_in_scope(
					nested_type[0]->type,
					nested_type[0]->owner);
			}
			TypePtr bare_nested = nested_owner.get() != NULL
				? pa11::strip_cv(nested_owner) : TypePtr();
			if (bare_nested.get() != NULL &&
			    bare_nested->kind == pa11::TypeKind::Record &&
			    bare_nested->scope != NULL)
			{
				const_cast<Parser*>(this)->complete_template_record(
					bare_nested);
				found =
					const_cast<Parser*>(this)->lookup_qualified_set(
						bare_nested->scope,
						arg.value_member_name,
						pa11::LOOKUP_VALUE);
			}
		}
	}
	if (found.empty())
	{
		TypePtr base = owner->base;
		if (base.get() != NULL && base->is_dependent_typename)
		{
			try
			{
				base = substitute_template_type_in_scope(base,
				                                         owner->scope);
			}
			catch (const runtime_error&)
			{
			}
		}
		base = base.get() != NULL ? pa11::strip_cv(base) : TypePtr();
		if (base.get() != NULL &&
		    base->kind == pa11::TypeKind::Record &&
		    base->scope != NULL)
		{
			const_cast<Parser*>(this)->complete_template_record(base);
			found =
				const_cast<Parser*>(this)->lookup_qualified_set(
					base->scope,
					arg.value_member_name,
					pa11::LOOKUP_VALUE);
		}
	}
		if (found.empty())
		{
			vector<Binding*> type_found =
			const_cast<Parser*>(this)->lookup_qualified_set(
				owner->scope,
				arg.value_member_name,
				pa11::LOOKUP_TYPE);
		if (type_found.empty())
		{
			TypePtr base = owner->base;
			if (base.get() != NULL && base->is_dependent_typename)
			{
				try
				{
					base = substitute_template_type_in_scope(base,
					                                         owner->scope);
				}
				catch (const runtime_error&)
				{
				}
			}
			base = base.get() != NULL ? pa11::strip_cv(base) : TypePtr();
			if (base.get() != NULL &&
			    base->kind == pa11::TypeKind::Record &&
			    base->scope != NULL)
			{
				const_cast<Parser*>(this)->complete_template_record(base);
				type_found =
					const_cast<Parser*>(this)->lookup_qualified_set(
						base->scope,
						arg.value_member_name,
						pa11::LOOKUP_TYPE);
			}
		}
		if (!type_found.empty())
		{
			TypePtr resolved = type_found[0]->type;
			const_cast<Parser*>(this)->
				complete_member_class_template_record(type_found[0]);
			TemplateArgument result = TemplateArgument::type_arg(
				substitute_template_type_in_scope(
					resolved,
					type_found[0]->owner));
			return cache_result(result);
		}
		if (arg.value_member_name == "type" &&
		    owner->base.get() != NULL &&
		    owner->base->is_dependent_typename)
		{
			TypePtr inherited_type = owner->base;
			try
			{
				inherited_type =
					substitute_template_type_in_scope(inherited_type,
					                                  owner->scope);
			}
			catch (const runtime_error&)
			{
			}
			TemplateArgument result =
				TemplateArgument::type_arg(inherited_type);
			return cache_result(result);
		}
		if (validating_template_definition_)
			return false;
		throw runtime_error("dependent value member not resolved");
	}
	TypePtr target = arg.type.get() != NULL
		? pa11::strip_cv(substitute_template_type(arg.type)) : TypePtr();
	if (target.get() != NULL &&
	    target->kind == pa11::TypeKind::MemberPointer)
	{
		TypePtr target_class = target->member_class.get() != NULL
			? pa11::strip_cv(target->member_class) : TypePtr();
		if (target_class.get() != NULL &&
		    (target_class->kind == pa11::TypeKind::TemplateParameter ||
		     target_class->is_dependent_typename))
			target = pa11::make_member_pointer(owner, target->base);
		Parser* self = const_cast<Parser*>(this);
		Binding* first = found[0];
		Expr inner;
		inner.valid = true;
		inner.binding = first;
		inner.type = first->type;
		inner.category = ValueCategory::LValue;
		for (size_t i = 0; i < found.size(); ++i)
			if (found[i]->kind == BindingKind::Function)
				inner.overloads.push_back(found[i]);
		inner.node = Node("id-expression lvalue " +
		                  pa11::describe_type(inner.type) + " " +
		                  qualified_decl_name(first));
		inner.node.binding = first;
		annotate_expr_node(inner);
		Expr address = self->make_address_expr("&", inner);
		Conversion conv = self->convert_to(address, target);
		if (!conv.viable ||
		    !conv.expr.node.has_op ||
		    conv.expr.node.op != OP_AMP ||
		    conv.expr.node.children.empty() ||
		    conv.expr.node.children[0].binding == NULL)
			return false;
		Binding* member = conv.expr.node.children[0].binding;
		if (member->aliased_binding != NULL &&
		    member->target_scope != NULL)
			member = member->aliased_binding;
		TemplateArgument result = TemplateArgument::value_arg(
			expression_object_type(conv.expr.type),
			reinterpret_cast<uint64_t>(member));
		result.value_binding = member;
		result.value_name = arg.value_name;
		return cache_result(result);
	}
	Binding* binding = found[0];
	if (!binding->has_constant)
	{
		ConstexprValue value;
		bool evaluated =
			const_cast<Parser*>(this)->try_evaluate_constexpr_binding(
				binding,
				value);
		if ((!evaluated || value.is_object || value.is_pointer) &&
		    owner.get() != NULL)
		{
			map<const void*, TemplateDeclaration*>::const_iterator owner_decl =
				record_template_declarations_.find(owner.get());
			map<const void*, vector<TemplateArgument> >::const_iterator
				owner_args = record_template_arguments_.find(owner.get());
			if (owner_decl != record_template_declarations_.end() &&
			    owner_args != record_template_arguments_.end())
			{
				Parser* self = const_cast<Parser*>(this);
				vector<map<string, TypePtr> > save_subst =
					self->template_type_substitutions_;
				vector<map<string, TemplateArgument> > save_value_subst =
					self->template_value_substitutions_;
				vector<set<string> > save_pack_subst =
					self->template_type_parameter_packs_;
				vector<Scope*> save_scopes = self->scopes_;
				map<string, TypePtr> subst;
				map<string, TemplateArgument> value_subst;
				set<string> pack_subst;
				for (size_t i = 0;
				     i < owner_args->second.size() &&
				     i < owner_decl->second->parameters.size();
				     ++i)
				{
					const TemplateParameterInfo& parameter =
						owner_decl->second->parameters[i];
					if (parameter.name.empty())
						continue;
					const TemplateArgument& owner_arg =
						owner_args->second[i];
					if (parameter.kind == TemplateParameterKind::Type)
					{
						if (parameter.is_pack)
						{
							subst[parameter.name] =
								pa11::make_template_parameter_type(
									parameter.name);
							value_subst[parameter.name] = owner_arg;
							pack_subst.insert(parameter.name);
						}
						else if (owner_arg.kind == TemplateArgumentKind::Type)
							subst[parameter.name] = owner_arg.type;
					}
					else
						value_subst[parameter.name] = owner_arg;
				}
				self->template_type_substitutions_.push_back(subst);
				self->template_value_substitutions_.push_back(value_subst);
				self->template_type_parameter_packs_.push_back(pack_subst);
				self->scopes_.clear();
				self->scopes_.push_back(owner->scope);
				evaluated = self->try_evaluate_constexpr_binding(
					binding,
					value);
				self->template_type_substitutions_ = save_subst;
				self->template_value_substitutions_ = save_value_subst;
				self->template_type_parameter_packs_ = save_pack_subst;
				self->scopes_ = save_scopes;
			}
		}
		if (!evaluated || value.is_object || value.is_pointer)
			throw runtime_error("dependent value member is not constant");
		binding->has_constant = true;
		binding->constant_value = value.int_value;
		TemplateArgument result = TemplateArgument::value_arg(
			arg.value_negated
			? pa11::make_fundamental(FT_BOOL)
			: expression_object_type(binding->type),
			arg.value_negated ? (value.int_value == 0 ? 1 : 0)
			                  : value.int_value);
		result.value_name = arg.value_name;
		return cache_result(result);
	}
	TemplateArgument result = TemplateArgument::value_arg(
		arg.value_negated
		? pa11::make_fundamental(FT_BOOL)
		: expression_object_type(binding->type),
		arg.value_negated
		? (binding->constant_value == 0 ? 1 : 0)
		: binding->constant_value);
	result.value_name = arg.value_name;
	return cache_result(result);
}

	TemplateArgument Parser::substitute_template_argument(
		const TemplateArgument& arg) const
	{
		if (arg.kind == TemplateArgumentKind::Pack &&
		    arg.pack_expansion &&
		    !arg.value_name.empty())
		{
			TemplateArgument out = arg;
			out.pack_expansion = false;
			return out;
		}
		string active_key = template_argument_key_part(arg);
		if (find(active_template_argument_substitution_keys_.begin(),
		         active_template_argument_substitution_keys_.end(),
		         active_key) !=
		    active_template_argument_substitution_keys_.end())
			return arg;
		struct ActiveTemplateArgumentSubstitution
		{
			vector<string>& keys;
			ActiveTemplateArgumentSubstitution(vector<string>& k,
			                                   const string& key)
			  : keys(k)
			{
				keys.push_back(key);
			}
			~ActiveTemplateArgumentSubstitution()
			{
				keys.pop_back();
			}
		} active_template_argument_substitution(
			active_template_argument_substitution_keys_,
			active_key);
		TemplateArgument resolved_member_value;
		bool dependent_value_expression =
			arg.kind == TemplateArgumentKind::Value &&
			arg.dependent &&
			arg.value_expr_end > arg.value_expr_begin;
		if (dependent_value_expression)
		{
			TemplateArgument evaluated;
			if (const_cast<Parser*>(this)->
				    try_evaluate_dependent_value_expression_argument(
					    arg,
					    evaluated))
			{
				if (!evaluated.dependent)
					return evaluated;
				if (template_argument_key_part(evaluated) ==
				    template_argument_key_part(arg))
					return evaluated;
				return substitute_template_argument(evaluated);
			}
		}
		bool simple_dependent_member_value =
			arg.kind == TemplateArgumentKind::Value &&
			arg.dependent &&
			!arg.value_owner_template_name.empty() &&
			!arg.value_member_name.empty() &&
			arg.value_name.find("()") == string::npos;
		if (dependent_value_expression && !simple_dependent_member_value)
			return arg;
		if (arg.kind == TemplateArgumentKind::Value &&
		    arg.dependent &&
		    !arg.value_name.empty() &&
		    arg.value_name.find("::") == string::npos)
	{
		TemplateArgument subst;
		if (find_template_value_substitution(arg.value_name, subst) &&
		    subst.kind == TemplateArgumentKind::Value)
		{
			if (template_argument_key_part(subst) ==
			    template_argument_key_part(arg))
				return arg;
			return substitute_template_argument(subst);
		}
	}
	if (arg.kind == TemplateArgumentKind::Value &&
	    arg.dependent &&
	    !arg.value_owner_template_name.empty() &&
	    arg.value_name.find("()") == string::npos &&
	    resolve_dependent_value_member_argument(arg, resolved_member_value))
	{
		return substitute_template_argument(resolved_member_value);
	}
		if (arg.kind == TemplateArgumentKind::Value &&
		    arg.dependent &&
		    resolve_dependent_value_member_argument(arg, resolved_member_value))
		return substitute_template_argument(resolved_member_value);
	if (arg.kind == TemplateArgumentKind::Value &&
	    arg.dependent &&
	    !arg.value_owner_template_name.empty() &&
	    !arg.value_owner_template_arguments.empty())
	{
		TemplateArgument deferred = arg;
		deferred.value_owner_template_arguments.clear();
		bool still_dependent = false;
		for (size_t i = 0; i < arg.value_owner_template_arguments.size(); ++i)
		{
			TemplateArgument owner_arg =
				template_argument_from_instance_argument(
					arg.value_owner_template_arguments[i]);
			owner_arg = substitute_template_argument(owner_arg);
			if (template_argument_has_template_parameter(
				    owner_arg,
				    record_template_arguments_))
				still_dependent = true;
			deferred.value_owner_template_arguments.push_back(
				template_instance_argument(owner_arg));
		}
		if (still_dependent)
			return deferred;
	}
	if (arg.kind == TemplateArgumentKind::Value &&
	    !arg.value_name.empty())
	{
		TemplateArgument subst;
		if (find_template_value_substitution(arg.value_name, subst))
		{
			if (subst.kind == TemplateArgumentKind::Value &&
			    subst.dependent == arg.dependent &&
			    subst.value_name == arg.value_name &&
			    subst.value_binding == arg.value_binding)
				subst = arg;
			if (arg.pack_expansion)
			{
				if (subst.kind == TemplateArgumentKind::Pack)
					return substitute_template_argument(subst);
			}
			else if (subst.kind == TemplateArgumentKind::Pack &&
			         parameter_pack_expansion_name(arg.value_name))
			{
				bool self_substitution =
					subst.pack.size() == 1 &&
					same_template_argument_value(
						subst.pack[0],
						arg,
						record_template_arguments_);
				if (!self_substitution)
					return substitute_template_argument(subst);
			}
			else if (subst.kind == TemplateArgumentKind::Value &&
			        !(subst.dependent == arg.dependent &&
			          subst.value_name == arg.value_name &&
			          subst.value_binding == arg.value_binding))
			{
				if (subst.dependent &&
				    !subst.value_owner_template_arguments.empty())
				{
					bool owner_still_dependent = false;
					for (size_t i = 0;
					     i < subst.value_owner_template_arguments.size();
					     ++i)
						if (template_instance_argument_has_template_parameter(
							    subst.value_owner_template_arguments[i],
							    record_template_arguments_))
							owner_still_dependent = true;
					if (owner_still_dependent)
						return subst;
				}
				return substitute_template_argument(subst);
			}
		}
	}
	if (arg.kind == TemplateArgumentKind::Template &&
	    !arg.value_name.empty())
	{
		TemplateArgument subst;
		if (find_template_value_substitution(arg.value_name, subst) &&
		    subst.kind == TemplateArgumentKind::Template &&
		    !(subst.template_declaration == arg.template_declaration &&
		      subst.value_name == arg.value_name))
			return subst;
		if (arg.template_declaration == NULL)
		{
			size_t member_sep = arg.value_name.rfind("::");
			if (member_sep != string::npos)
			{
				string owner_name = arg.value_name.substr(0, member_sep);
				string member_name = arg.value_name.substr(member_sep + 2);
				TypePtr owner_type;
					if (find_template_type_substitution(owner_name, owner_type))
					{
						owner_type = substitute_template_type(owner_type);
						TypePtr owner = owner_type.get() != NULL
							? pa11::strip_cv(owner_type) : TypePtr();
						if (owner.get() != NULL &&
					    owner->kind == pa11::TypeKind::Record &&
					    owner->scope != NULL)
					{
						const_cast<Parser*>(this)->
							complete_template_record(owner);
						TemplateDeclaration* declaration =
							const_cast<Parser*>(this)->
								find_class_template(owner->scope,
								                    member_name);
						if (declaration == NULL)
						{
							declaration = const_cast<Parser*>(this)->
								find_alias_template(owner->scope,
								                    member_name);
						}
							if (declaration != NULL)
							{
								return TemplateArgument::template_arg(
									declaration);
						}
					}
				}
			}
			Scope* qualifier = NULL;
			string lookup_name = arg.value_name;
			if (const_cast<Parser*>(this)->
				    resolve_template_name_spelling(arg.value_name,
				                                   qualifier,
				                                   lookup_name))
			{
				TemplateDeclaration* declaration =
					const_cast<Parser*>(this)->
						find_class_template(qualifier,
						                    lookup_name);
				if (declaration == NULL)
					declaration = const_cast<Parser*>(this)->
						find_alias_template(qualifier,
						                    lookup_name);
				if (declaration != NULL)
					return TemplateArgument::template_arg(declaration);
			}
		}
	}
	TemplateArgument out = arg;
	if (arg.kind == TemplateArgumentKind::Type)
	{
		if (arg.pack_expansion)
		{
			string pack_name;
			TemplateArgument subst;
			TypePtr bare = arg.type.get() != NULL
				? pa11::strip_cv(arg.type) : TypePtr();
			if (bare.get() != NULL &&
			    bare->is_dependent_typename &&
			    (bare->kind != pa11::TypeKind::TemplateParameter ||
			     bare->is_dependent_typename))
			{
				TemplateArgument single = arg;
				single.pack_expansion = false;
				TemplateArgument substituted =
					substitute_template_argument(single);
				if (substituted.kind == TemplateArgumentKind::Type &&
				    !template_argument_has_template_parameter(
					    substituted,
					    record_template_arguments_))
					return substituted;
			}
			if (bare.get() != NULL &&
			    bare->kind == pa11::TypeKind::TemplateParameter &&
			    !bare->is_dependent_typename &&
			    template_type_has_template_parameter_name(arg.type,
			                                              pack_name) &&
			    bare->name == pack_name &&
			    find_template_value_substitution(pack_name, subst) &&
			    subst.kind == TemplateArgumentKind::Pack)
				return substitute_template_argument(subst);
			vector<TemplateArgument> expanded =
				expand_template_argument_pack(arg);
			if (expanded.size() != 1 ||
			    template_argument_key_part(expanded[0]) !=
				    template_argument_key_part(arg))
			{
				vector<TemplateArgument> pack;
				for (size_t i = 0; i < expanded.size(); ++i)
				{
					TemplateArgument element =
						substitute_template_argument(expanded[i]);
					if (element.kind == TemplateArgumentKind::Pack)
						pack.insert(pack.end(),
						            element.pack.begin(),
						            element.pack.end());
					else
						pack.push_back(element);
				}
				return TemplateArgument::pack_arg(pack);
			}
		}
			try
			{
				out.type = substitute_template_type(arg.type);
				string substituted_pack_name;
				if (out.pack_expansion &&
				    !template_type_has_template_parameter_name(
					    out.type,
					    substituted_pack_name))
					out.pack_expansion = false;
			}
		catch (const runtime_error& err)
		{
			TypePtr bare = arg.type.get() != NULL
				? pa11::strip_cv(arg.type) : TypePtr();
			if (string(err.what()) != "dependent typename not resolved" ||
			    bare.get() == NULL ||
			    !bare->is_dependent_typename ||
			    !bare->dependent_typename_qualified)
				throw;
			size_t member_pos = bare->name.rfind("::");
			if (member_pos == string::npos)
				throw;
			if (bare->name.substr(member_pos + 2) == "type")
			{
				string parameter_name;
				if (function_template_candidate_instantiation_depth_ == 0 ||
				    template_type_has_template_parameter_name(arg.type,
				                                             parameter_name))
					return arg;
			}
			TemplateArgument value_arg =
				TemplateArgument::dependent_value_arg(TypePtr());
			value_arg.value_name = bare->name;
			value_arg.value_member_name =
				bare->name.substr(member_pos + 2);
			string owner_name = bare->template_primary_name;
			if (owner_name.empty())
			{
				string root = bare->name.substr(0, member_pos);
				size_t template_pos = root.find('<');
				owner_name = root.substr(0, template_pos);
			}
			value_arg.value_owner_template_name = owner_name;
			for (size_t ai = 0; ai < bare->template_arguments.size(); ++ai)
			{
				TemplateArgument owner_arg =
					template_argument_from_instance_argument(
						bare->template_arguments[ai]);
				owner_arg = substitute_template_argument(owner_arg);
				value_arg.value_owner_template_arguments.push_back(
					template_instance_argument(owner_arg));
			}
			return substitute_template_argument(value_arg);
		}
	}
	else if (arg.kind == TemplateArgumentKind::Value)
	{
		if (out.type.get() != NULL)
			out.type = substitute_template_type(out.type);
	}
	else if (arg.kind == TemplateArgumentKind::Pack)
	{
		if (!arg.value_name.empty())
		{
			TemplateArgument subst;
			if (find_template_value_substitution(arg.value_name, subst) &&
			    subst.kind != TemplateArgumentKind::Pack)
				return substitute_template_argument(subst);
		}
		if (arg.value_name.empty() &&
		    arg.pack.size() == 1 &&
		    arg.pack[0].kind == TemplateArgumentKind::Type)
		{
			string pack_name;
			TemplateArgument subst;
			TypePtr bare = arg.pack[0].type.get() != NULL
				? pa11::strip_cv(arg.pack[0].type) : TypePtr();
			if (bare.get() != NULL &&
			    bare->kind == pa11::TypeKind::TemplateParameter &&
			    !bare->is_dependent_typename &&
			    template_type_has_template_parameter_name(arg.pack[0].type,
			                                              pack_name) &&
			    bare->name == pack_name &&
			    find_template_value_substitution(pack_name, subst) &&
			    subst.kind == TemplateArgumentKind::Pack)
			{
					bool self_substitution =
						subst.pack.size() == 1 &&
						subst.pack[0].kind == TemplateArgumentKind::Type &&
						subst.pack[0].type.get() != NULL &&
						arg.pack[0].type.get() != NULL &&
						pa11::same_type(subst.pack[0].type,
						                arg.pack[0].type);
					if (!self_substitution)
						return substitute_template_argument(subst);
				}
			TemplateArgument pattern = arg.pack[0];
			string wrapped_pack_name;
			TemplateArgument wrapped_subst;
			if (template_type_has_template_parameter_name(pattern.type,
			                                              wrapped_pack_name) &&
			    find_template_value_substitution(wrapped_pack_name,
			                                     wrapped_subst) &&
			    wrapped_subst.kind == TemplateArgumentKind::Pack)
			{
				pattern.pack_expansion = true;
				vector<TemplateArgument> expanded =
					expand_template_argument_pack(pattern);
				if (expanded.size() != 1 ||
				    template_argument_key_part(expanded[0]) !=
					    template_argument_key_part(pattern))
				{
					vector<TemplateArgument> pack;
					for (size_t i = 0; i < expanded.size(); ++i)
					{
						TemplateArgument elem =
							substitute_template_argument(expanded[i]);
						if (elem.kind == TemplateArgumentKind::Pack)
							pack.insert(pack.end(),
							            elem.pack.begin(),
							            elem.pack.end());
						else
							pack.push_back(elem);
					}
					return TemplateArgument::pack_arg(pack);
				}
			}
			}
		out.pack.clear();
		for (size_t i = 0; i < arg.pack.size(); ++i)
		{
			TemplateArgument elem =
				substitute_template_argument(arg.pack[i]);
			if (elem.kind == TemplateArgumentKind::Pack)
				out.pack.insert(out.pack.end(),
				                elem.pack.begin(),
				                elem.pack.end());
			else
				out.pack.push_back(elem);
		}
	}
	return out;
}


}  // namespace internal
}  // namespace pa12
