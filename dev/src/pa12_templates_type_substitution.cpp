#include "pa12_templates_instance_support.h"
#include "pa12_types_support.h"

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
namespace {

bool active_class_instantiation_named(
	const vector<ActiveClassInstantiation>& active,
	const string& name)
{
	for (size_t i = 0; i < active.size(); ++i)
		if (active[i].declaration != NULL &&
		    active[i].declaration->name == name)
			return true;
	return false;
}

bool hosted_nonrecord_member_typename_probe(
	bool hosted_compatibility,
	const vector<ActiveClassInstantiation>& active,
	const string& root_name,
	const string& suffix,
	TypePtr root_substitution)
{
	if (!hosted_compatibility ||
	    root_name.empty() ||
	    suffix.empty() ||
	    !active_class_instantiation_named(active, "allocator_traits"))
		return false;
	TypePtr bare_root = root_substitution.get() != NULL
		? pa11::strip_cv(root_substitution) : TypePtr();
	return bare_root.get() != NULL &&
	       !bare_root->is_dependent_typename &&
	       bare_root->kind != pa11::TypeKind::Record &&
	       bare_root->kind != pa11::TypeKind::TemplateParameter;
}

}  // namespace

TypePtr Parser::substitute_template_type(TypePtr type) const
{
	if (type.get() == NULL)
		return type;
	TypePtr bare_input = pa11::strip_cv(type);
	for (size_t si = template_type_substitutions_.size(); si > 0; --si)
		for (map<string, TypePtr>::const_iterator it =
			     template_type_substitutions_[si - 1].begin();
		     it != template_type_substitutions_[si - 1].end();
		     ++it)
		{
			TypePtr subst = it->second.get() != NULL
				? pa11::strip_cv(it->second) : TypePtr();
			if (subst.get() != NULL &&
			    subst.get() == bare_input.get() &&
			    type_contains_parameter_name(it->second,
			                                 it->first,
			                                 record_template_arguments_))
				return type;
		}
	if (type->is_dependent_typename)
	{
		if (!type->dependent_typename_qualified &&
		    !type->dependent_typename_template_id &&
		    !type->dependent_typename_decltype &&
		    type->template_arguments.empty() &&
		    type->dependent_typename_template_argument_lists.empty())
		{
			TypePtr subst;
			if (find_template_type_substitution(type->name, subst))
			{
				if (type_contains_parameter_name(subst,
				                                 type->name,
				                                 record_template_arguments_))
					return subst;
				return substitute_template_type(subst);
			}
		}
		string active_key =
			type->name + "|" + type->template_primary_name + "|" +
			to_string(type->template_arguments.size()) + "|" +
			to_string(type->dependent_typename_template_argument_lists.size());
		if (!type->template_arguments.empty())
		{
			vector<TemplateArgument> active_args;
			for (size_t i = 0; i < type->template_arguments.size(); ++i)
				active_args.push_back(
					raw_template_argument_from_instance_argument(
						type->template_arguments[i]));
			active_key += "|" + template_argument_key(active_args);
		}
		for (size_t i = 0;
		     i < type->dependent_typename_template_argument_lists.size();
		     ++i)
		{
			vector<TemplateArgument> active_args;
			for (size_t j = 0;
			     j < type->dependent_typename_template_argument_lists[i].size();
			     ++j)
				active_args.push_back(
					raw_template_argument_from_instance_argument(
						type->dependent_typename_template_argument_lists[i][j]));
			active_key += "|" + template_argument_key(active_args);
		}
		for (size_t i = 0; i < template_value_substitutions_.size(); ++i)
		{
			for (map<string, TemplateArgument>::const_iterator it =
				     template_value_substitutions_[i].begin();
			     it != template_value_substitutions_[i].end();
			     ++it)
				active_key += "|V:" + it->first + "=" +
				              template_argument_key_part(it->second);
		}
		if (find(active_dependent_type_substitution_keys_.begin(),
		         active_dependent_type_substitution_keys_.end(),
		         active_key) != active_dependent_type_substitution_keys_.end())
			return type;
		struct ActiveDependentTypeSubstitution
		{
			vector<string>& keys;
			ActiveDependentTypeSubstitution(vector<string>& k,
			                                const string& key)
			  : keys(k)
			{
				keys.push_back(key);
			}
			~ActiveDependentTypeSubstitution()
			{
				keys.pop_back();
			}
			} active_dependent_type_substitution(
				active_dependent_type_substitution_keys_,
				active_key);
		bool concrete_substitution_context =
			!validating_template_definition_ &&
			(!template_type_substitutions_.empty() ||
			 !template_value_substitutions_.empty());
		if (concrete_substitution_context)
		{
			if (!template_type_substitutions_.empty())
				for (map<string, TypePtr>::const_iterator it =
					     template_type_substitutions_.back().begin();
				     it != template_type_substitutions_.back().end();
				     ++it)
				{
					bool concrete_pack_placeholder = false;
					TypePtr bare = it->second.get() != NULL
						? pa11::strip_cv(it->second) : TypePtr();
					if (bare.get() != NULL &&
					    bare->kind == pa11::TypeKind::TemplateParameter &&
					    active_type_parameter_pack(it->first) &&
					    !template_value_substitutions_.empty())
					{
						map<string, TemplateArgument>::const_iterator pack =
							template_value_substitutions_.back().find(
								it->first);
						concrete_pack_placeholder =
							pack != template_value_substitutions_.back().end() &&
							pack->second.kind == TemplateArgumentKind::Pack;
						for (size_t pi = 0;
						     concrete_pack_placeholder &&
						     pi < pack->second.pack.size();
						     ++pi)
							if (template_argument_has_template_parameter(
								    pack->second.pack[pi],
								    record_template_arguments_))
								concrete_pack_placeholder = false;
					}
					if (!concrete_pack_placeholder &&
					    type_is_template_dependent(it->second))
						concrete_substitution_context = false;
				}
			if (!template_value_substitutions_.empty())
				for (map<string, TemplateArgument>::const_iterator it =
					     template_value_substitutions_.back().begin();
				     it != template_value_substitutions_.back().end();
				     ++it)
					if (template_argument_has_template_parameter(
						    it->second,
						    record_template_arguments_))
						concrete_substitution_context = false;
		}
		const bool replay_errors_are_hard =
			function_template_candidate_instantiation_depth_ != 0 ||
			(concrete_substitution_context &&
			 !active_class_instantiation_dependent());
		if (type->dependent_typename_decltype &&
		    type->name.compare(0, 9, "decltype(") == 0 &&
		    (!template_type_substitutions_.empty() ||
		     !template_value_substitutions_.empty() ||
		     function_template_candidate_instantiation_depth_ != 0))
		{
			vector<Token> replay_tokens;
			if (!collect_replay_tokens(type->name, replay_tokens))
			{
				if (replay_errors_are_hard)
					throw runtime_error(
						"failed to tokenize dependent decltype");
			}
			else
			{
				Parser* self = const_cast<Parser*>(this);
				vector<Token> saved_tokens;
				size_t saved_pos = self->pos_;
				bool saved_replaying_decltype =
					self->replaying_dependent_decltype_;
				TypePtr replayed;
				try
				{
					self->tokens_.swap(saved_tokens);
					self->tokens_.swap(replay_tokens);
					self->pos_ = 0;
					self->replaying_dependent_decltype_ = true;
					replayed = self->parse_decltype_specifier();
					self->expect_eof();
					self->tokens_.swap(replay_tokens);
					self->tokens_.swap(saved_tokens);
					self->pos_ = saved_pos;
					self->replaying_dependent_decltype_ =
						saved_replaying_decltype;
					}
					catch (const runtime_error& err)
					{
						self->tokens_.swap(replay_tokens);
						self->tokens_.swap(saved_tokens);
						self->pos_ = saved_pos;
						self->replaying_dependent_decltype_ =
							saved_replaying_decltype;
						bool unresolved_candidate_local =
							function_template_candidate_instantiation_depth_ != 0 &&
							string(err.what()).compare(0, 16,
							                           "name not found: ") == 0;
						if (replay_errors_are_hard &&
						    !unresolved_candidate_local)
							throw;
						replayed.reset();
					}
					if (replayed.get() != NULL)
					{
						if (replayed->is_dependent_typename &&
						    replayed->dependent_typename_decltype &&
						    replayed->name == type->name &&
						    replayed->template_arguments.empty())
							return type;
						return substitute_template_type(replayed);
					}
				}
			}
			TypePtr resolved = resolve_dependent_typename_type(type);
			if (resolved.get() != NULL && resolved != type)
			{
				if (resolved->is_dependent_typename &&
				    type->is_dependent_typename &&
				    resolved->name == type->name &&
				    resolved->template_primary_name ==
					    type->template_primary_name &&
				    resolved->template_arguments.size() ==
					    type->template_arguments.size())
					return type;
				return substitute_template_type(resolved);
			}
		if (!type->template_arguments.empty() ||
		    !type->dependent_typename_template_argument_lists.empty())
		{
				vector<TemplateArgument> original_args;
				vector<TemplateArgument> substituted_args;
				string primary_name = type->template_primary_name.empty()
					? type->name : type->template_primary_name;
				size_t primary_sep = primary_name.rfind("::");
				if (primary_sep != string::npos)
					primary_name = primary_name.substr(primary_sep + 2);
				size_t primary_args = primary_name.find('<');
				if (primary_args != string::npos)
					primary_name = primary_name.substr(0, primary_args);
				TemplateDeclaration* primary_template =
					primary_name.empty()
					? NULL
					: const_cast<Parser*>(this)->
						find_class_template(NULL, primary_name);
				for (size_t i = 0; i < type->template_arguments.size(); ++i)
				{
					TemplateArgument arg =
						raw_template_argument_from_instance_argument(
							type->template_arguments[i]);
					original_args.push_back(arg);
					TemplateArgument substituted =
						substitute_template_argument(arg);
					bool primary_pack_argument =
						primary_template != NULL &&
						i < primary_template->parameters.size() &&
						primary_template->parameters[i].is_pack &&
						template_argument_has_template_parameter(
							arg,
							record_template_arguments_);
					if (primary_pack_argument ||
					    substituted.kind == TemplateArgumentKind::Pack ||
					    substituted.pack_expansion)
					{
						vector<TemplateArgument> expanded =
							expand_template_argument_pack(substituted);
						for (size_t ei = 0; ei < expanded.size(); ++ei)
						{
							TemplateArgument element =
								substitute_template_argument(expanded[ei]);
							if (element.kind == TemplateArgumentKind::Pack)
								substituted_args.insert(
									substituted_args.end(),
									element.pack.begin(),
									element.pack.end());
							else
								substituted_args.push_back(element);
						}
					}
					else
						substituted_args.push_back(substituted);
				}
				substituted_args =
					flatten_template_argument_packs(substituted_args);
			vector<vector<TemplateArgument> > original_argument_lists;
			vector<vector<TemplateArgument> > substituted_argument_lists;
			for (size_t i = 0;
			     i < type->dependent_typename_template_argument_lists.size();
			     ++i)
			{
				vector<TemplateArgument> original_list;
				vector<TemplateArgument> substituted_list;
				for (size_t j = 0;
				     j < type->dependent_typename_template_argument_lists[i].size();
				     ++j)
				{
					TemplateArgument arg =
						raw_template_argument_from_instance_argument(
							type->dependent_typename_template_argument_lists[i][j]);
					original_list.push_back(arg);
					substituted_list.push_back(
						substitute_template_argument(arg));
				}
				original_argument_lists.push_back(original_list);
				substituted_argument_lists.push_back(substituted_list);
			}
			bool arguments_changed =
				template_argument_key(original_args) !=
				template_argument_key(substituted_args);
			if (!arguments_changed &&
			    original_argument_lists.size() !=
			    substituted_argument_lists.size())
				arguments_changed = true;
			for (size_t i = 0;
			     !arguments_changed && i < original_argument_lists.size();
			     ++i)
				if (template_argument_key(original_argument_lists[i]) !=
				    template_argument_key(substituted_argument_lists[i]))
					arguments_changed = true;
			if (arguments_changed)
			{
				TypePtr out = pa11::make_dependent_typename_type(
					type->name,
					type->dependent_typename_qualified,
					type->dependent_typename_template_id,
					type->dependent_typename_decltype);
				out->template_primary_name = type->template_primary_name;
				for (size_t i = 0; i < substituted_args.size(); ++i)
					out->template_arguments.push_back(
						template_instance_argument(substituted_args[i]));
				for (size_t i = 0;
				     i < substituted_argument_lists.size();
				     ++i)
				{
					vector<pa11::TemplateInstanceArgument> argument_list;
					for (size_t j = 0;
					     j < substituted_argument_lists[i].size();
					     ++j)
						argument_list.push_back(
							template_instance_argument(
								substituted_argument_lists[i][j]));
					out->dependent_typename_template_argument_lists.push_back(
						argument_list);
				}
				type = out;
				TypePtr retry = resolve_dependent_typename_type(type);
				if (retry.get() != NULL && retry != type)
					return substitute_template_type(retry);
				}
			else if (concrete_substitution_context ||
			         function_template_candidate_instantiation_depth_ != 0)
			{
				TypePtr retry = resolve_dependent_typename_type(type);
				if (retry.get() != NULL && retry != type)
					return substitute_template_type(retry);
				}
				}
				string transform_name = !type->template_primary_name.empty()
					? type->template_primary_name : type->name;
				size_t transform_args = transform_name.find('<');
				if (transform_args != string::npos)
					transform_name = transform_name.substr(0, transform_args);
				if (internal_type_transform_name(transform_name) &&
				    type->template_arguments.size() == 1)
				{
					TemplateArgument arg =
						raw_template_argument_from_instance_argument(
							type->template_arguments[0]);
					arg = substitute_template_argument(arg);
					if (arg.kind == TemplateArgumentKind::Type &&
					    !type_structurally_dependent(arg.type))
						return apply_internal_type_transform(transform_name,
						                                     arg.type);
				}
				if (type->template_primary_name == "__type_pack_element" ||
				    type->name == "__type_pack_element")
				{
				vector<TemplateArgument> arguments;
				for (size_t i = 0; i < type->template_arguments.size(); ++i)
					arguments.push_back(
						raw_template_argument_from_instance_argument(
							type->template_arguments[i]));
				if (arguments.empty())
				{
					map<const void*, vector<TemplateArgument> >::const_iterator
						stored = record_template_arguments_.find(type.get());
					if (stored != record_template_arguments_.end())
						arguments = stored->second;
				}
				TypePtr selected;
				if (const_cast<Parser*>(this)->
					    try_resolve_type_pack_element(arguments,
					                                  selected) &&
				    selected.get() != NULL)
					return selected;
			}
			if (type->template_primary_name == "__make_integer_seq" ||
			    type->name == "__make_integer_seq")
			{
				vector<TemplateArgument> arguments;
				for (size_t i = 0; i < type->template_arguments.size(); ++i)
				{
					TemplateArgument arg =
						raw_template_argument_from_instance_argument(
							type->template_arguments[i]);
					arguments.push_back(substitute_template_argument(arg));
				}
				TypePtr expanded =
					const_cast<Parser*>(this)->make_integer_sequence_type(
						arguments);
				if (expanded.get() != NULL &&
				    !type_is_template_dependent(expanded))
					return expanded;
			}
			if (type->dependent_typename_qualified)
			{
			string root_name = type->name;
			size_t root_sep = root_name.find("::");
			string suffix;
			if (root_sep != string::npos)
			{
				suffix = type->name.substr(root_sep);
				root_name = root_name.substr(0, root_sep);
			}
			size_t root_template = root_name.find('<');
			if (root_template != string::npos)
				root_name = root_name.substr(0, root_template);
			TypePtr root_subst;
			bool have_root_subst =
				find_template_type_substitution(root_name, root_subst);
			if (!have_root_subst &&
			    !type->template_primary_name.empty() &&
			    !type->template_arguments.empty())
			{
				TemplateDeclaration* alias =
					const_cast<Parser*>(this)->find_alias_template(
						NULL,
						type->template_primary_name);
				if (alias != NULL)
					for (size_t ai = 0;
					     ai < alias->parameters.size() &&
					     ai < type->template_arguments.size();
					     ++ai)
					{
						if (alias->parameters[ai].name != root_name ||
						    alias->parameters[ai].kind !=
							    TemplateParameterKind::Type)
							continue;
						TemplateArgument arg =
							template_argument_from_instance_argument(
								type->template_arguments[ai]);
						arg = substitute_template_argument(arg);
						if (arg.kind == TemplateArgumentKind::Type)
						{
							root_subst = arg.type;
							have_root_subst = true;
						}
						break;
					}
				if (!have_root_subst &&
				    root_name == "_Tp" &&
				    type->template_arguments.size() == 1)
				{
					TemplateArgument arg =
						template_argument_from_instance_argument(
							type->template_arguments[0]);
					arg = substitute_template_argument(arg);
					if (arg.kind == TemplateArgumentKind::Type)
					{
						root_subst = arg.type;
						have_root_subst = true;
					}
				}
				if (!have_root_subst &&
				    root_name == "_Tp" &&
				    (type->template_primary_name == "__pointer" ||
				     type->template_primary_name == "__c_pointer" ||
				     type->template_primary_name == "__v_pointer" ||
				     type->template_primary_name == "__cv_pointer"))
					have_root_subst =
						find_template_type_substitution("_Alloc",
						                                root_subst);
			}
			if (have_root_subst)
			{
				TypePtr substituted_root = substitute_template_type(root_subst);
				if (type_is_template_dependent(substituted_root))
				{
					string replacement_root;
					TypePtr bare_root = pa11::strip_cv(substituted_root);
					if (bare_root->kind == pa11::TypeKind::TemplateParameter)
						replacement_root = bare_root->name;
					else if (!bare_root->template_primary_name.empty())
						replacement_root = bare_root->template_primary_name +
						                   "<>";
					if (!replacement_root.empty() &&
					    replacement_root != root_name)
					{
						TypePtr out =
							pa11::make_dependent_typename_type(
								replacement_root + suffix,
								type->dependent_typename_qualified,
								type->dependent_typename_template_id,
								type->dependent_typename_decltype);
						out->template_primary_name =
							type->template_primary_name;
							for (size_t i = 0;
							     i < type->template_arguments.size();
							     ++i)
							{
							TemplateArgument arg =
								template_argument_from_instance_argument(
									type->template_arguments[i]);
							arg = substitute_template_argument(arg);
								out->template_arguments.push_back(
									template_instance_argument(arg));
							}
							for (size_t i = 0;
							     i < type->dependent_typename_template_argument_lists.size();
							     ++i)
							{
								vector<pa11::TemplateInstanceArgument>
									argument_list;
								for (size_t j = 0;
								     j < type->dependent_typename_template_argument_lists[i].size();
								     ++j)
								{
									TemplateArgument arg =
										template_argument_from_instance_argument(
											type->dependent_typename_template_argument_lists[i][j]);
									arg = substitute_template_argument(arg);
									argument_list.push_back(
										template_instance_argument(arg));
								}
									out->dependent_typename_template_argument_lists.push_back(
										argument_list);
							}
							return out;
						}
				}
				else if (concrete_substitution_context &&
				         !active_class_instantiation_dependent())
					{
						if (hosted_nonrecord_member_typename_probe(
							    hosted_compatibility_,
							    active_class_instantiations_,
							    root_name,
							    suffix,
							    substituted_root))
							return type;
							TypePtr resolved = resolve_dependent_typename_type(type);
							if (resolved.get() != NULL && resolved != type)
								return substitute_template_type(resolved);
								throw runtime_error("dependent typename not resolved");
							}
			}
		}
		bool still_dependent = false;
		if (type->dependent_typename_qualified)
		{
			string root_name = type->name;
			size_t root_sep = root_name.find("::");
			string suffix;
			if (root_sep != string::npos)
			{
				suffix = root_name.substr(root_sep);
				root_name = root_name.substr(0, root_sep);
			}
			size_t root_template = root_name.find('<');
			if (root_template != string::npos)
				root_name = root_name.substr(0, root_template);
			TypePtr root_subst;
			bool have_root_subst =
				find_template_type_substitution(root_name, root_subst);
			if (!have_root_subst &&
			    !type->template_primary_name.empty() &&
			    !type->template_arguments.empty())
			{
				TemplateDeclaration* alias =
					const_cast<Parser*>(this)->find_alias_template(
						NULL,
						type->template_primary_name);
				if (alias != NULL)
					for (size_t ai = 0;
					     ai < alias->parameters.size() &&
					     ai < type->template_arguments.size();
					     ++ai)
					{
						if (alias->parameters[ai].name != root_name ||
						    alias->parameters[ai].kind !=
							    TemplateParameterKind::Type)
							continue;
						TemplateArgument arg =
							template_argument_from_instance_argument(
								type->template_arguments[ai]);
						arg = substitute_template_argument(arg);
						if (arg.kind == TemplateArgumentKind::Type)
						{
							root_subst = arg.type;
							have_root_subst = true;
						}
						break;
					}
				if (!have_root_subst &&
				    root_name == "_Tp" &&
				    type->template_arguments.size() == 1)
				{
					TemplateArgument arg =
						template_argument_from_instance_argument(
							type->template_arguments[0]);
					arg = substitute_template_argument(arg);
					if (arg.kind == TemplateArgumentKind::Type)
					{
						root_subst = arg.type;
						have_root_subst = true;
					}
				}
				if (!have_root_subst &&
				    root_name == "_Tp" &&
				    (type->template_primary_name == "__pointer" ||
				     type->template_primary_name == "__c_pointer" ||
				     type->template_primary_name == "__v_pointer" ||
				     type->template_primary_name == "__cv_pointer"))
					have_root_subst =
						find_template_type_substitution("_Alloc",
						                                root_subst);
			}
			if (have_root_subst)
			{
				TypePtr substituted_root = substitute_template_type(root_subst);
				if (hosted_nonrecord_member_typename_probe(
					    hosted_compatibility_,
					    active_class_instantiations_,
					    root_name,
					    suffix,
					    substituted_root))
					return type;
				if (type_is_template_dependent(substituted_root))
					still_dependent = true;
			}
		}
			if (!type->template_primary_name.empty())
			{
				TemplateArgument template_subst;
			if (find_template_value_substitution(type->template_primary_name,
			                                     template_subst))
			{
				if (template_subst.kind == TemplateArgumentKind::Template &&
				    template_subst.template_declaration == NULL)
					still_dependent = true;
			}
			else
			{
				TypePtr bare = pa11::strip_cv(type);
					if (bare->kind == pa11::TypeKind::Record &&
					    bare->is_template_specialization &&
					    const_cast<Parser*>(this)->
						    class_template_declaration_for_match(bare) == NULL)
						still_dependent = true;
				}
			}
			if (type->template_arguments.empty())
				still_dependent = still_dependent ||
				template_type_has_template_parameter(
					type,
					record_template_arguments_);
			else
				for (size_t i = 0; i < type->template_arguments.size(); ++i)
				{
					if (template_instance_argument_has_template_parameter(
					    type->template_arguments[i],
					    record_template_arguments_) &&
				    function_template_candidate_instantiation_depth_ == 0 &&
				    active_template_match_parser != this)
				{
					still_dependent = true;
					continue;
				}
				TemplateArgument arg =
					template_argument_from_instance_argument(
						type->template_arguments[i]);
				if (template_argument_has_template_parameter(
					    arg,
						    record_template_arguments_))
						still_dependent = true;
				}
			for (size_t i = 0;
			     i < type->dependent_typename_template_argument_lists.size();
			     ++i)
				for (size_t j = 0;
				     j < type->dependent_typename_template_argument_lists[i].size();
				     ++j)
				{
					if (template_instance_argument_has_template_parameter(
						    type->dependent_typename_template_argument_lists[i][j],
						    record_template_arguments_) &&
					    function_template_candidate_instantiation_depth_ == 0 &&
					    active_template_match_parser != this)
					{
						still_dependent = true;
						continue;
					}
					TemplateArgument arg =
						template_argument_from_instance_argument(
							type->dependent_typename_template_argument_lists[i][j]);
					if (template_argument_has_template_parameter(
						    arg,
						    record_template_arguments_))
						still_dependent = true;
				}
							if (!still_dependent)
							{
									throw runtime_error("dependent typename not resolved");
								}
	}
	if (type->kind == pa11::TypeKind::TemplateParameter)
	{
		TypePtr subst;
		if (find_template_type_substitution(type->name, subst))
			return subst;
		return type;
	}
	if (type->kind == pa11::TypeKind::Cv)
		return pa11::make_cv(substitute_template_type(type->base), type->cv);
	if (type->kind == pa11::TypeKind::Pointer)
		return pa11::make_pointer(substitute_template_type(type->base));
	if (type->kind == pa11::TypeKind::LValueReference)
	{
		TypePtr base = substitute_template_type(type->base);
		if (base->kind == pa11::TypeKind::LValueReference ||
		    base->kind == pa11::TypeKind::RValueReference)
			return pa11::make_lvalue_reference(base->base);
		return pa11::make_lvalue_reference(base);
	}
	if (type->kind == pa11::TypeKind::RValueReference)
	{
		TypePtr base = substitute_template_type(type->base);
		if (base->kind == pa11::TypeKind::LValueReference)
			return base;
		if (base->kind == pa11::TypeKind::RValueReference)
			return pa11::make_rvalue_reference(base->base);
		return pa11::make_rvalue_reference(base);
	}
	if (type->kind == pa11::TypeKind::Array)
	{
		bool unknown_bound = type->unknown_bound;
		uint64_t bound = type->bound;
		string bound_name = type->name;
		if (unknown_bound && !bound_name.empty())
		{
			TemplateArgument subst;
			if (find_template_value_substitution(bound_name, subst) &&
			    subst.kind == TemplateArgumentKind::Value &&
			    !subst.dependent)
			{
				unknown_bound = false;
				bound = subst.value;
				bound_name.clear();
			}
		}
		TypePtr out = pa11::make_array(substitute_template_type(type->base),
		                               unknown_bound,
		                               bound);
		out->name = bound_name;
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
					TemplateArgument subst;
					if (template_type_has_template_parameter_name(
						    type->parameters[i],
						    pack_name) &&
					    find_template_value_substitution(pack_name, subst) &&
					    subst.kind == TemplateArgumentKind::Pack)
					{
						for (size_t p = 0; p < subst.pack.size(); ++p)
						{
							if (subst.pack[p].kind != TemplateArgumentKind::Type)
								throw runtime_error(
									"type parameter pack required");
							TypePtr element =
								substitute_template_type_parameter(
									type->parameters[i],
									pack_name,
									subst.pack[p].type);
							params.push_back(
								substitute_template_type(element));
						}
						consumed_variadic_pack = true;
						continue;
					}
				}
				params.push_back(substitute_template_type(type->parameters[i]));
			}
			TypePtr out = pa11::make_function(substitute_template_type(type->base),
			                                  params,
			                                  type->variadic &&
			                                  !consumed_variadic_pack);
			out->cv = type->cv;
			out->ref_qualifier = type->ref_qualifier;
			return out;
	}
	if (type->kind == pa11::TypeKind::MemberPointer)
		return pa11::make_member_pointer(
			substitute_template_type(type->member_class),
			substitute_template_type(type->base));
	if (type->kind == pa11::TypeKind::Record &&
	    type->is_template_specialization &&
	    !type_structurally_dependent(type))
	{
		bool stored_arguments_dependent = false;
		map<const void*, vector<TemplateArgument> >::const_iterator args =
			record_template_arguments_.find(type.get());
		if (args != record_template_arguments_.end())
			for (size_t i = 0; i < args->second.size(); ++i)
				if (template_argument_has_template_parameter(
					    args->second[i],
					    record_template_arguments_))
					stored_arguments_dependent = true;
		if (args == record_template_arguments_.end())
			for (size_t i = 0; i < type->template_arguments.size(); ++i)
				if (template_instance_argument_has_template_parameter(
					    type->template_arguments[i],
					    record_template_arguments_))
					stored_arguments_dependent = true;
		if (!stored_arguments_dependent)
			return type;
	}
	if (type->kind == pa11::TypeKind::Record &&
	    type->is_template_specialization)
	{
		string record_primary_name = type->template_primary_name.empty()
			? type->name : type->template_primary_name;
		size_t record_primary_args = record_primary_name.find('<');
		if (record_primary_args != string::npos)
			record_primary_name =
				record_primary_name.substr(0, record_primary_args);
		auto substituted_argument_count_too_large =
			[](TemplateDeclaration* declaration,
			   const vector<TemplateArgument>& substituted) {
				if (declaration == NULL)
					return false;
				for (size_t i = 0; i < declaration->parameters.size(); ++i)
					if (declaration->parameters[i].is_pack)
						return false;
				return substituted.size() > declaration->parameters.size();
		};
		TemplateArgument template_subst;
		if (!record_primary_name.empty() &&
		    find_template_value_substitution(record_primary_name,
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
						substitute_template_argument(args->second[i]);
					vector<TemplateArgument> expanded =
						expand_template_argument_pack(arg);
					for (size_t j = 0; j < expanded.size(); ++j)
					{
						TemplateArgument element =
							substitute_template_argument(expanded[j]);
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
					arg = substitute_template_argument(arg);
					vector<TemplateArgument> expanded =
						expand_template_argument_pack(arg);
					for (size_t j = 0; j < expanded.size(); ++j)
					{
						TemplateArgument element =
							substitute_template_argument(expanded[j]);
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
			if (substituted_argument_count_too_large(
				    template_subst.template_declaration,
				    substituted))
				return type;
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
			{
				TemplateArgument arg =
					raw_template_argument_from_instance_argument(
						type->template_arguments[i]);
				if (arg.kind == TemplateArgumentKind::Pack &&
				    arg.pack.size() == 1 &&
				    arg.pack[0].kind != TemplateArgumentKind::Pack &&
				    single_instance_pack_element_is_expansion(arg.pack[0]))
				{
					arg = arg.pack[0];
					arg.pack_expansion = true;
				}
				else if (arg.kind == TemplateArgumentKind::Type &&
				         arg.type.get() != NULL)
				{
					TypePtr bare_arg = pa11::strip_cv(arg.type);
					if (bare_arg->kind == pa11::TypeKind::TemplateParameter &&
					    active_type_parameter_pack(bare_arg->name))
						arg.pack_expansion = true;
				}
				fallback_args.push_back(arg);
			}
			source_args = &fallback_args;
		}
		TemplateDeclaration* record_decl =
			decl != record_template_declarations_.end()
			? decl->second : NULL;
			if (record_decl == NULL &&
			    source_args != NULL &&
			    !record_primary_name.empty())
			{
				if (type->scope != NULL && type->scope->parent != NULL)
					record_decl = const_cast<Parser*>(this)->
						find_class_template(type->scope->parent,
						                    record_primary_name);
				if (record_decl == NULL)
					record_decl = const_cast<Parser*>(this)->
						class_template_declaration_for_match(type);
			}
			if (record_decl == NULL &&
			    source_args != NULL &&
			    !record_primary_name.empty())
			{
				record_decl = const_cast<Parser*>(this)->
					find_class_template(NULL,
					                    record_primary_name);
				if (record_decl == NULL)
				{
					TemplateDeclaration* unique = NULL;
					for (map<Scope*, map<string, TemplateDeclaration*> >::const_iterator
						     sit = class_templates_.begin();
					     sit != class_templates_.end();
					     ++sit)
					{
						map<string, TemplateDeclaration*>::const_iterator it =
							sit->second.find(record_primary_name);
						if (it == sit->second.end())
							continue;
						if (it->second->class_specialization)
							continue;
						if (unique != NULL && unique != it->second)
						{
							unique = NULL;
							break;
						}
						unique = it->second;
					}
					record_decl = unique;
				}
			}
		if (record_decl != NULL &&
		    find(completing_class_template_arguments_.begin(),
		         completing_class_template_arguments_.end(),
		         record_decl) !=
			    completing_class_template_arguments_.end())
			return type;
			if (record_decl != NULL && record_decl->class_specialization)
			{
				TemplateDeclaration* primary =
					const_cast<Parser*>(this)->find_class_template(
						record_decl->owner,
						record_decl->name);
				if (primary != NULL && !primary->class_specialization)
					record_decl = primary;
				}
				if (record_decl != NULL && source_args != NULL)
				{
					if (record_decl->class_specialization &&
			    template_instance_arguments_have_pack(
				    type->template_arguments))
			{
				TemplateDeclaration* primary =
					const_cast<Parser*>(this)->find_class_template(
						record_decl->owner,
						record_decl->name);
				bool primary_has_pack_parameter = false;
				if (primary != NULL)
					for (size_t pi = 0; pi < primary->parameters.size(); ++pi)
						if (primary->parameters[pi].is_pack)
							primary_has_pack_parameter = true;
				if (primary != NULL &&
				    (type->template_arguments.size() <=
					     primary->parameters.size() ||
				     primary_has_pack_parameter))
				{
					vector<TemplateArgument> substituted;
						for (size_t i = 0;
						     i < type->template_arguments.size();
						     ++i)
						{
							TemplateArgument original_arg =
								raw_template_argument_from_instance_argument(
									type->template_arguments[i]);
							TemplateArgument arg = original_arg;
							arg = substitute_template_argument(arg);
							TypePtr original_arg_type =
								original_arg.kind == TemplateArgumentKind::Type
								? pa11::strip_cv(original_arg.type) : TypePtr();
							bool whole_primary_type_argument =
								i < primary->parameters.size() &&
								!primary->parameters[i].is_pack &&
								original_arg_type.get() != NULL &&
								(original_arg_type->kind ==
								     pa11::TypeKind::Function ||
								 original_arg_type->kind ==
								     pa11::TypeKind::MemberPointer);
							vector<TemplateArgument> expanded =
								whole_primary_type_argument
								? vector<TemplateArgument>(1, arg)
								: expand_template_argument_pack(arg);
						for (size_t j = 0; j < expanded.size(); ++j)
						{
							TemplateArgument element =
								substitute_template_argument(
									expanded[j]);
							if (element.kind ==
							    TemplateArgumentKind::Pack)
								substituted.insert(
									substituted.end(),
									element.pack.begin(),
									element.pack.end());
							else
								substituted.push_back(element);
						}
					}
					substituted =
						flatten_template_argument_packs(substituted);
					return const_cast<Parser*>(this)->
						instantiate_class_template(primary,
						                           substituted);
				}
			}
			vector<TemplateArgument> substituted;
			for (size_t i = 0; i < source_args->size(); ++i)
			{
					const TemplateArgument& original_arg = (*source_args)[i];
					TemplateArgument arg =
						substitute_template_argument(original_arg);
					size_t produced_pack_size =
						arg.kind == TemplateArgumentKind::Pack
					? arg.pack.size() : 0;
					TypePtr original_arg_type =
						original_arg.kind == TemplateArgumentKind::Type
						? pa11::strip_cv(original_arg.type) : TypePtr();
						bool function_type_argument =
							original_arg_type.get() != NULL &&
							(original_arg_type->kind == pa11::TypeKind::Function ||
							 original_arg_type->kind ==
							     pa11::TypeKind::MemberPointer);
						bool primary_pack_slot =
							(i < record_decl->parameters.size() &&
							 record_decl->parameters[i].is_pack) ||
							(i >= record_decl->parameters.size() &&
							 !record_decl->parameters.empty() &&
							 record_decl->parameters.back().is_pack);
						bool original_arg_uses_active_pack = false;
						bool original_arg_is_active_pack_parameter = false;
						bool original_arg_matches_record_parameter = false;
						if (original_arg.kind == TemplateArgumentKind::Type &&
						    original_arg.type.get() != NULL)
						{
							string pack_name;
							if (template_type_has_template_parameter_name(
								    original_arg.type,
								    pack_name) &&
							    active_type_parameter_pack(pack_name))
								original_arg_uses_active_pack = true;
							TypePtr bare_original_arg =
								pa11::strip_cv(original_arg.type);
							if (bare_original_arg.get() != NULL &&
							    bare_original_arg->kind ==
								    pa11::TypeKind::TemplateParameter &&
							    active_type_parameter_pack(
								    bare_original_arg->name))
								original_arg_is_active_pack_parameter = true;
							if (bare_original_arg.get() != NULL &&
							    bare_original_arg->kind ==
								    pa11::TypeKind::TemplateParameter &&
							    i < record_decl->parameters.size() &&
							    record_decl->parameters[i].name ==
								    bare_original_arg->name)
								original_arg_matches_record_parameter = true;
						}
						else if (original_arg.kind == TemplateArgumentKind::Pack)
							original_arg_uses_active_pack = true;
						bool primary_pack_argument =
							primary_pack_slot &&
							(original_arg.pack_expansion ||
							 original_arg.kind == TemplateArgumentKind::Pack ||
							 original_arg_uses_active_pack);
						bool active_pack_argument =
							!function_type_argument &&
							original_arg_is_active_pack_parameter &&
							(original_arg_matches_record_parameter ||
							 (record_decl->owner != NULL &&
							  record_decl->owner->kind == ScopeKind::Class &&
							  source_args->size() > 1 &&
							  i + 1 == source_args->size()));
						if (primary_pack_argument &&
						    arg.kind != TemplateArgumentKind::Pack)
							arg.pack_expansion = true;
						if (active_pack_argument &&
						    arg.kind != TemplateArgumentKind::Pack)
							arg.pack_expansion = true;
						vector<TemplateArgument> expanded;
						if (!function_type_argument &&
						    primary_pack_argument &&
						    arg.kind == TemplateArgumentKind::Pack &&
						    arg.pack.size() == 1 &&
						    arg.pack[0].kind != TemplateArgumentKind::Pack)
						{
							TemplateArgument pattern = arg.pack[0];
							pattern.pack_expansion = true;
							expanded = expand_template_argument_pack(pattern);
						}
						else if (!function_type_argument &&
						    (original_arg.pack_expansion ||
						     primary_pack_argument ||
						     active_pack_argument ||
						     original_arg.kind == TemplateArgumentKind::Pack ||
					     arg.pack_expansion ||
					     arg.kind == TemplateArgumentKind::Pack))
					expanded = expand_template_argument_pack(arg);
				else
					expanded.push_back(arg);
				for (size_t j = 0; j < expanded.size(); ++j)
				{
					TemplateArgument element = expanded[j];
					if (element.kind == TemplateArgumentKind::Pack)
						substituted.insert(substituted.end(),
						                   element.pack.begin(),
						                   element.pack.end());
					else
						substituted.push_back(element);
				}
					size_t skip_defaults =
						(original_arg.pack_expansion ||
						 primary_pack_argument ||
						 original_arg.kind == TemplateArgumentKind::Pack) &&
						produced_pack_size > 1
					? produced_pack_size - 1 : 0;
				while (skip_defaults != 0 &&
				       i + 1 < source_args->size() &&
				       !template_argument_has_template_parameter(
					       (*source_args)[i + 1],
					       record_template_arguments_))
				{
					++i;
					--skip_defaults;
				}
			}
				substituted = flatten_template_argument_packs(substituted);
				if (template_argument_key(substituted) !=
				    template_argument_key(*source_args))
				{
					if (substituted_argument_count_too_large(record_decl,
					                                        substituted))
					return type;
				return const_cast<Parser*>(this)->instantiate_class_template(
					record_decl,
					substituted);
			}
		}
	}
	return type;
}

}  // namespace internal
}  // namespace pa12
