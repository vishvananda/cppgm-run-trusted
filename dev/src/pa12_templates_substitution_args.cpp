#include "pa12_templates_instance_support.h"

#include <algorithm>
#include <cstdint>
#include <sstream>
#include <stdexcept>
#include <utility>

#include "posttoken_pipeline.h"
#include "pp_token.h"

using namespace std;

namespace pa12 {
namespace internal {

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
		if (decl != record_template_declarations_.end() &&
		    find(completing_class_template_arguments_.begin(),
		         completing_class_template_arguments_.end(),
		         decl->second) !=
			    completing_class_template_arguments_.end())
			return type;
		if (decl != record_template_declarations_.end() &&
		    args != record_template_arguments_.end())
		{
			bool needs_substitution = false;
			for (size_t i = 0; i < args->second.size(); ++i)
				if (template_argument_has_template_parameter(
					    args->second[i],
					    record_template_arguments_))
					needs_substitution = true;
			if (needs_substitution)
			{
				vector<TemplateArgument> substituted;
				for (size_t i = 0; i < args->second.size(); ++i)
					substituted.push_back(
						substitute_template_argument_type_parameter(
							args->second[i],
							name,
							replacement));
				return const_cast<Parser*>(this)->instantiate_class_template(
					decl->second,
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
				map<const void*, vector<TemplateArgument> >::const_iterator args =
					record_template_arguments_.find(owner.get());
				if (args != record_template_arguments_.end() &&
				    !args->second.empty())
				{
					for (size_t i = 0; i < args->second.size(); ++i)
						out.value_owner_template_arguments.push_back(
							template_instance_argument(args->second[i]));
				}
				else
					out.value_owner_template_arguments =
						owner->template_arguments;
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
	string active_key = dependent_value_member_key(arg);
	if (find(active_dependent_value_member_keys_.begin(),
	         active_dependent_value_member_keys_.end(),
	         active_key) != active_dependent_value_member_keys_.end())
		return false;
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
		if (template_argument_has_template_parameter(
			    owner_arg,
			    record_template_arguments_))
			still_dependent = true;
		owner_args.push_back(owner_arg);
	}
	if (still_dependent)
		return false;
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
		out = TemplateArgument::value_arg(
			arg.value_negated
			? pa11::make_fundamental(FT_BOOL)
			: expression_object_type(binding->type),
			arg.value_negated
			? (binding->constant_value == 0 ? 1 : 0)
			: binding->constant_value);
		out.value_name = arg.value_name;
		return true;
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
		if (alias_declaration == NULL && declaration == NULL)
		{
			return false;
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
	const_cast<Parser*>(this)->complete_template_record(owner);
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
			out = TemplateArgument::type_arg(
				substitute_template_type_in_scope(
					resolved,
					type_found[0]->owner));
			return true;
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
			out = TemplateArgument::type_arg(inherited_type);
			return true;
		}
		throw runtime_error("dependent value member not resolved");
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
		out = TemplateArgument::value_arg(
			arg.value_negated
			? pa11::make_fundamental(FT_BOOL)
			: expression_object_type(binding->type),
			arg.value_negated ? (value.int_value == 0 ? 1 : 0)
			                  : value.int_value);
		out.value_name = arg.value_name;
		return true;
	}
	out = TemplateArgument::value_arg(
		arg.value_negated
		? pa11::make_fundamental(FT_BOOL)
		: expression_object_type(binding->type),
		arg.value_negated
		? (binding->constant_value == 0 ? 1 : 0)
		: binding->constant_value);
	out.value_name = arg.value_name;
	return true;
}

TemplateArgument Parser::substitute_template_argument(
	const TemplateArgument& arg) const
{
	TemplateArgument resolved_member_value;
	if (arg.kind == TemplateArgumentKind::Value &&
	    arg.dependent &&
	    !arg.value_owner_template_name.empty() &&
	    arg.value_name.find("()") == string::npos &&
	    resolve_dependent_value_member_argument(arg, resolved_member_value))
		return substitute_template_argument(resolved_member_value);
	if (arg.kind == TemplateArgumentKind::Value &&
	    arg.dependent &&
	    arg.value_expr_end > arg.value_expr_begin)
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
		if (arg.pack.size() == 1 &&
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
