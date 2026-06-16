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
size_t dependent_cache_hash_combine(size_t seed, size_t value);
size_t dependent_cache_string_hash(const string& value);
size_t dependent_cache_type_identity(TypePtr type);
size_t dependent_cache_template_argument_identity(
	const TemplateArgument& argument,
	int depth);
size_t dependent_value_member_cache_prefix(const TemplateArgument& arg);

bool Parser::resolve_dependent_value_member_argument(
	const TemplateArgument& arg,
	TemplateArgument& out) const
{
	if (arg.kind != TemplateArgumentKind::Value ||
	    !arg.dependent ||
	    arg.value_owner_template_name.empty())
		return false;
	if (resolve_hosted_dependent_value_member_argument(arg, out))
		return true;
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
			try
			{
				owner = alias_declaration != NULL
					? const_cast<Parser*>(this)->instantiate_alias_template(
						alias_declaration,
						owner_args)
				: const_cast<Parser*>(this)->instantiate_class_template(
					declaration,
					owner_args);
			}
			catch (const runtime_error& err)
			{
				string message = err.what();
				if (hosted_compatibility_ &&
				    (message == "missing template argument" ||
				     message == "template argument kind mismatch" ||
				     message == "template pack argument kind mismatch"))
					return false;
				throw;
			}
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

}  // namespace internal
}  // namespace pa12
