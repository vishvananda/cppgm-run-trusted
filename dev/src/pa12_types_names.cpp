#include "pa12_types_support.h"

#include <algorithm>
#include <set>
#include <stdexcept>

using namespace std;

namespace pa12 {
namespace internal {
namespace {

void collect_alias_dependency_names_from_instance_argument(
	const pa11::TemplateInstanceArgument& argument,
	set<string>& names);
void collect_alias_dependency_names_from_argument(const TemplateArgument& argument,
                                                  set<string>& names);
bool type_has_replayable_dependent_value(TypePtr type);
bool argument_has_replayable_dependent_value(const TemplateArgument& argument);

bool instance_argument_has_replayable_dependent_value(
	const pa11::TemplateInstanceArgument& argument)
{
	if (argument.kind == pa11::TemplateInstanceArgumentKind::Value &&
	    argument.dependent &&
	    argument.value_expr_end > argument.value_expr_begin &&
	    argument.value_name.find("()") != string::npos)
		return true;
	if (argument.kind == pa11::TemplateInstanceArgumentKind::Type &&
	    type_has_replayable_dependent_value(argument.type))
		return true;
	for (size_t i = 0; i < argument.value_owner_template_arguments.size(); ++i)
		if (instance_argument_has_replayable_dependent_value(
			    argument.value_owner_template_arguments[i]))
			return true;
	for (size_t i = 0; i < argument.pack.size(); ++i)
		if (instance_argument_has_replayable_dependent_value(argument.pack[i]))
			return true;
	return false;
}

bool type_has_replayable_dependent_value(TypePtr type)
{
	TypePtr bare = type.get() != NULL ? pa11::strip_cv(type) : TypePtr();
	if (bare.get() == NULL)
		return false;
	for (size_t i = 0; i < bare->template_arguments.size(); ++i)
		if (instance_argument_has_replayable_dependent_value(
			    bare->template_arguments[i]))
			return true;
	for (size_t i = 0; i < bare->dependent_typename_template_argument_lists.size();
	     ++i)
		for (size_t j = 0;
		     j < bare->dependent_typename_template_argument_lists[i].size();
		     ++j)
			if (instance_argument_has_replayable_dependent_value(
				    bare->dependent_typename_template_argument_lists[i][j]))
				return true;
	return false;
}

bool argument_has_replayable_dependent_value(const TemplateArgument& argument)
{
	if (argument.kind == TemplateArgumentKind::Value &&
	    argument.dependent &&
	    argument.value_expr_end > argument.value_expr_begin &&
	    argument.value_name.find("()") != string::npos)
		return true;
	if (argument.kind == TemplateArgumentKind::Type &&
	    type_has_replayable_dependent_value(argument.type))
		return true;
	for (size_t i = 0; i < argument.value_owner_template_arguments.size(); ++i)
		if (instance_argument_has_replayable_dependent_value(
			    argument.value_owner_template_arguments[i]))
			return true;
	for (size_t i = 0; i < argument.pack.size(); ++i)
		if (argument_has_replayable_dependent_value(argument.pack[i]))
			return true;
	return false;
}

bool hosted_library_record_type(TypePtr type)
{
	TypePtr bare = type.get() != NULL ? pa11::strip_cv(type) : TypePtr();
	if (bare.get() == NULL || bare->kind != pa11::TypeKind::Record)
		return false;
	for (Scope* scope = bare->scope; scope != NULL; scope = scope->parent)
		if (scope->kind == ScopeKind::Namespace &&
		    (scope->name == "std" || scope->name == "__gnu_cxx"))
			return true;
	return false;
}

void collect_alias_dependency_names_from_type(TypePtr type, set<string>& names)
{
	if (type.get() == NULL)
		return;
	type = pa11::strip_cv(type);
	if (type->kind == pa11::TypeKind::TemplateParameter)
	{
		if (type->is_dependent_typename)
		{
			for (size_t i = 0; i < type->template_arguments.size(); ++i)
				collect_alias_dependency_names_from_instance_argument(
					type->template_arguments[i],
					names);
			for (size_t i = 0;
			     i < type->dependent_typename_template_argument_lists.size();
			     ++i)
				for (size_t j = 0;
				     j < type->dependent_typename_template_argument_lists[i].size();
				     ++j)
					collect_alias_dependency_names_from_instance_argument(
						type->dependent_typename_template_argument_lists[i][j],
						names);
		}
		if (pa11::is_deducible_template_parameter_type(type))
			names.insert(type->name);
		return;
	}
	if (type->kind == pa11::TypeKind::Pointer ||
	    type->kind == pa11::TypeKind::LValueReference ||
	    type->kind == pa11::TypeKind::RValueReference ||
	    type->kind == pa11::TypeKind::Array)
	{
		collect_alias_dependency_names_from_type(type->base, names);
		return;
	}
	if (type->kind == pa11::TypeKind::Function)
	{
		collect_alias_dependency_names_from_type(type->base, names);
		for (size_t i = 0; i < type->parameters.size(); ++i)
			collect_alias_dependency_names_from_type(type->parameters[i],
			                                         names);
		return;
	}
	if (type->kind == pa11::TypeKind::MemberPointer)
	{
		collect_alias_dependency_names_from_type(type->member_class, names);
		collect_alias_dependency_names_from_type(type->base, names);
		return;
	}
	if (type->is_dependent_typename &&
	    type->dependent_typename_template_id &&
	    !type->template_primary_name.empty())
		names.insert(type->template_primary_name);
	if (type->is_template_specialization)
		for (size_t i = 0; i < type->template_arguments.size(); ++i)
			collect_alias_dependency_names_from_instance_argument(
				type->template_arguments[i],
				names);
}

void collect_alias_dependency_names_from_instance_argument(
	const pa11::TemplateInstanceArgument& argument,
	set<string>& names)
{
	if (argument.kind == pa11::TemplateInstanceArgumentKind::Type)
	{
		collect_alias_dependency_names_from_type(argument.type, names);
		return;
	}
	if (argument.kind == pa11::TemplateInstanceArgumentKind::Value)
	{
		for (size_t i = 0;
		     i < argument.value_owner_template_arguments.size();
		     ++i)
			collect_alias_dependency_names_from_instance_argument(
				argument.value_owner_template_arguments[i],
				names);
		if (!argument.value_owner_template_name.empty())
			names.insert(argument.value_owner_template_name);
		if (argument.dependent && !argument.value_name.empty())
			names.insert(argument.value_name);
		collect_alias_dependency_names_from_type(argument.type, names);
		return;
	}
	if (argument.kind == pa11::TemplateInstanceArgumentKind::Template)
	{
		if (argument.dependent && !argument.template_name.empty())
			names.insert(argument.template_name);
		return;
	}
	if (argument.kind == pa11::TemplateInstanceArgumentKind::Pack)
		for (size_t i = 0; i < argument.pack.size(); ++i)
			collect_alias_dependency_names_from_instance_argument(
				argument.pack[i],
				names);
}

void collect_alias_dependency_names_from_argument(const TemplateArgument& argument,
                                                  set<string>& names)
{
	if (argument.kind == TemplateArgumentKind::Type)
	{
		collect_alias_dependency_names_from_type(argument.type, names);
		return;
	}
	if (argument.kind == TemplateArgumentKind::Value)
	{
		for (size_t i = 0;
		     i < argument.value_owner_template_arguments.size();
		     ++i)
			collect_alias_dependency_names_from_instance_argument(
				argument.value_owner_template_arguments[i],
				names);
		if (!argument.value_owner_template_name.empty())
			names.insert(argument.value_owner_template_name);
		if (argument.dependent && !argument.value_name.empty())
			names.insert(argument.value_name);
		collect_alias_dependency_names_from_type(argument.type, names);
		return;
	}
	if (argument.kind == TemplateArgumentKind::Template)
	{
		if (argument.template_declaration == NULL &&
		    !argument.value_name.empty())
			names.insert(argument.value_name);
		return;
	}
	if (argument.kind == TemplateArgumentKind::Pack)
	{
		if (!argument.value_name.empty())
			names.insert(argument.value_name);
		for (size_t i = 0; i < argument.pack.size(); ++i)
			collect_alias_dependency_names_from_argument(argument.pack[i],
			                                             names);
	}
}

}  // namespace

bool Parser::try_parse_type_name(TypePtr& out)
{
	size_t save = pos_;
	string spelling;
	Scope* qualifier = NULL;
	bool typename_disambiguator = consume(KW_TYPENAME);
	if (!typename_disambiguator &&
	    at_identifier() &&
	    lookahead(OP_LPAREN, 1))
	{
		string transform = current().source;
		if (internal_type_transform_name(transform))
			{
				consume_identifier();
				expect(OP_LPAREN);
				TypePtr inner = parse_type_id();
				expect(OP_RPAREN);
				if (type_structurally_dependent(inner))
				{
					vector<TemplateArgument> arguments;
					arguments.push_back(TemplateArgument::type_arg(inner));
					out = pa11::make_dependent_typename_type(
						transform,
						false,
						true,
						false);
					out->template_primary_name = transform;
					out->template_arguments =
						dependent_template_instance_arguments(arguments);
					return true;
				}
				out = apply_internal_type_transform(transform, inner);
				return true;
			}
	}
	bool template_id_qualifier = false;
	if (at_identifier() && lookahead(OP_LT, 1))
	{
		size_t p = pos_ + 1;
		int depth = 0;
		while (p < tokens_.size())
		{
			if (tokens_[p].kind == posttoken::TokenKind::Simple &&
			    tokens_[p].type == OP_LT)
				++depth;
			else if (tokens_[p].kind == posttoken::TokenKind::Simple &&
			         tokens_[p].type == OP_GT)
			{
				--depth;
				if (depth == 0)
				{
					template_id_qualifier =
						p + 1 < tokens_.size() &&
						tokens_[p + 1].kind == posttoken::TokenKind::Simple &&
						tokens_[p + 1].type == OP_COLON2;
					break;
				}
			}
			++p;
		}
	}
	bool dependent_base_qualifier = false;
	if (!typename_disambiguator &&
	    parsing_base_specifier_ &&
	    at_identifier() &&
	    lookahead(OP_COLON2, 1))
	{
		TypePtr root_subst;
		if (find_template_type_substitution(current().source,
		                                    root_subst))
		{
			root_subst = root_subst.get() != NULL
				? pa11::strip_cv(root_subst) : TypePtr();
			dependent_base_qualifier =
				root_subst.get() != NULL &&
				root_subst->kind == pa11::TypeKind::TemplateParameter;
		}
		Binding* root_binding =
			pa11::lookup_unqualified(current_scope(),
			                         current().source,
			                         pa11::LOOKUP_TYPE);
		TypePtr root_type = root_binding != NULL
			? root_binding->type : TypePtr();
		root_type = root_type.get() != NULL
			? pa11::strip_cv(root_type) : TypePtr();
		dependent_base_qualifier =
			dependent_base_qualifier ||
			(root_type.get() != NULL &&
			 root_type->kind == pa11::TypeKind::TemplateParameter);
	}
	auto hosted_invoke_result_type = [&](TypePtr invoke_result) -> TypePtr {
		if (!hosted_compatibility_)
			return TypePtr();
		TypePtr bare = invoke_result.get() != NULL
			? pa11::strip_cv(invoke_result) : TypePtr();
		if (bare.get() == NULL ||
		    bare->kind != pa11::TypeKind::Record)
			return TypePtr();
		string primary = bare->template_primary_name.empty()
			? bare->name : bare->template_primary_name;
		size_t sep = primary.rfind("::");
		if (sep != string::npos)
			primary = primary.substr(sep + 2);
		size_t arg_pos = primary.find('<');
		if (arg_pos != string::npos)
			primary = primary.substr(0, arg_pos);
		if (primary != "__invoke_result")
			return TypePtr();
		vector<TemplateArgument> args;
		map<const void*, vector<TemplateArgument> >::const_iterator stored =
			record_template_arguments_.find(bare.get());
		if (stored != record_template_arguments_.end())
			args = stored->second;
		else
			for (size_t ai = 0; ai < bare->template_arguments.size(); ++ai)
				args.push_back(template_argument_from_instance_argument(
					bare->template_arguments[ai]));
		vector<TemplateArgument> flat_args;
		for (size_t ai = 0; ai < args.size(); ++ai)
		{
			vector<TemplateArgument> expanded =
				expand_template_argument_pack(args[ai]);
			flat_args.insert(flat_args.end(),
			                 expanded.begin(),
			                 expanded.end());
		}
		args = flat_args;
		vector<TypePtr> call_types;
		for (size_t ai = 0; ai < args.size(); ++ai)
		{
			TemplateArgument arg = substitute_template_argument(args[ai]);
			if (arg.kind == TemplateArgumentKind::Pack)
			{
				for (size_t pi = 0; pi < arg.pack.size(); ++pi)
				{
					TemplateArgument elem =
						substitute_template_argument(arg.pack[pi]);
					if (elem.kind != TemplateArgumentKind::Type)
						return TypePtr();
					TypePtr type = substitute_template_type(elem.type);
					if (type_structurally_dependent(type))
						return TypePtr();
					call_types.push_back(type);
				}
				continue;
			}
			if (arg.kind != TemplateArgumentKind::Type)
				return TypePtr();
			TypePtr type = substitute_template_type(arg.type);
			if (type_structurally_dependent(type))
				return TypePtr();
			call_types.push_back(type);
		}
		Expr call;
		if (try_make_invocable_type_trait_call(call_types, call))
			return call.type;
		return TypePtr();
	};
	if ((typename_disambiguator ||
	     (template_id_qualifier && parsing_base_specifier_) ||
	     dependent_base_qualifier) &&
	    at_identifier())
	{
		size_t dep_save = pos_;
		string dep_name = consume_identifier();
		bool dependent_root = false;
		bool dep_name_qualified = false;
		bool dep_name_template_id = false;
		bool dep_name_decltype = false;
		TypePtr subst;
		bool have_type_subst =
			find_template_type_substitution(dep_name, subst);
		string root_name = dep_name;
		TypePtr concrete_root;
		Binding* concrete_root_binding = NULL;
		bool concrete_root_lookup_failed = false;
		if (have_type_subst &&
		    pa11::strip_cv(subst)->kind !=
		    pa11::TypeKind::TemplateParameter)
			concrete_root = subst;
		else if (!have_type_subst)
		{
			concrete_root_binding =
				pa11::lookup_unqualified(current_scope(),
				                         dep_name,
				                         pa11::LOOKUP_TYPE);
			if (concrete_root_binding != NULL)
				concrete_root = concrete_root_binding->type;
			if (concrete_root.get() != NULL)
			{
				complete_member_class_template_record(
					concrete_root_binding);
				if (concrete_root->is_dependent_typename)
					concrete_root = substitute_template_type(
						concrete_root);
				if (!type_is_template_dependent(concrete_root))
					complete_template_record(concrete_root);
				if (pa11::strip_cv(concrete_root)->kind ==
				    pa11::TypeKind::TemplateParameter)
					concrete_root.reset();
			}
		}
			if (concrete_root.get() != NULL && at(OP_COLON2))
			{
					TypePtr resolved = concrete_root;
					Scope* resolved_type_scope = NULL;
					bool resolved_ok = true;
					while (consume(OP_COLON2))
			{
				consume(KW_TEMPLATE);
				if (!at_identifier())
				{
					resolved_ok = false;
					break;
				}
							TypePtr owner = pa11::strip_cv(resolved);
								if (owner->kind != pa11::TypeKind::Record ||
							    owner->scope == NULL)
							{
								resolved_ok = false;
								break;
							}
				complete_template_record(owner);
				string member_name = consume_identifier();
				if (hosted_compatibility_ && member_name == "type")
				{
					TypePtr invoke_type = hosted_invoke_result_type(owner);
					if (invoke_type.get() != NULL)
					{
						resolved = invoke_type;
						resolved_type_scope = NULL;
						continue;
					}
				}
				if (at(OP_LT))
				{
					vector<TemplateArgument> member_args;
					TemplateDeclaration* alias =
						find_alias_template(owner->scope, member_name);
					TemplateDeclaration* klass =
						alias == NULL
						? find_class_template(owner->scope, member_name)
						: NULL;
					if (alias == NULL && klass == NULL)
					{
						resolved_ok = false;
						break;
					}
						parse_template_argument_list(member_args);
						resolved = alias != NULL
							? instantiate_alias_template(alias, member_args)
							: instantiate_class_template(klass, member_args);
						resolved_type_scope = NULL;
					}
				else
				{
								vector<Binding*> found =
									lookup_qualified_set(owner->scope,
									                     member_name,
									                     pa11::LOOKUP_TYPE);
									if (found.empty())
								{
									resolved_ok = false;
									break;
								}
						resolved = found[0]->type;
						resolved_type_scope = owner->scope;
						complete_member_class_template_record(found[0]);
					}
				}
				if (resolved_ok && pos_ != dep_save)
				{
								out = substitute_template_type_in_scope(
									resolved,
									resolved_type_scope);
							if (active_class_instantiations_.empty() &&
						    template_type_substitutions_.empty() &&
						    template_value_substitutions_.empty() &&
						    !type_is_template_dependent(out) &&
						    !type_parse_mentions_active_record(
							    out,
							    active_class_instantiations_,
							    record_template_arguments_))
						complete_template_record(out);
				return true;
			}
			if (pos_ != dep_save)
				concrete_root_lookup_failed = true;
			pos_ = dep_save;
			dep_name = consume_identifier();
		}
		if (at(OP_COLON2))
		{
			Binding* ns_binding =
				pa11::lookup_unqualified(current_scope(),
				                         dep_name,
				                         pa11::LOOKUP_NAMESPACE);
			Scope* resolved_scope =
				ns_binding != NULL ? ns_binding->target_scope : NULL;
			if (resolved_scope != NULL)
			{
				size_t concrete_save = pos_;
					TypePtr resolved;
					Scope* resolved_type_scope = NULL;
					bool have_resolved_type = false;
					bool resolved_ok = true;
				while (consume(OP_COLON2))
				{
					consume(KW_TEMPLATE);
					if (!at_identifier())
					{
						resolved_ok = false;
						break;
					}
					string member_name = consume_identifier();
					if (!have_resolved_type)
					{
						if (at(OP_LT))
						{
							vector<TemplateArgument> member_args;
							TemplateDeclaration* alias =
								find_alias_template(resolved_scope,
								                    member_name);
							TemplateDeclaration* klass =
								alias == NULL
								? find_class_template(resolved_scope,
								                      member_name)
								: NULL;
							if (alias == NULL && klass == NULL)
							{
								resolved_ok = false;
								break;
							}
							parse_template_argument_list(member_args);
							if (klass != NULL &&
							    template_arguments_dependent(member_args))
							{
								resolved_ok = false;
								break;
							}
								resolved = alias != NULL
									? instantiate_alias_template(alias,
									                             member_args)
									: instantiate_class_template(klass,
									                             member_args);
								resolved_type_scope = NULL;
								have_resolved_type = true;
								continue;
						}
						vector<Binding*> namespaces =
							lookup_qualified_set(resolved_scope,
							                     member_name,
							                     pa11::LOOKUP_NAMESPACE);
							if (!namespaces.empty())
							{
								resolved_scope = namespaces[0]->target_scope;
								resolved_type_scope = NULL;
								continue;
							}
						vector<Binding*> found =
							lookup_qualified_set(resolved_scope,
							                     member_name,
							                     pa11::LOOKUP_TYPE);
						if (found.empty())
						{
							resolved_ok = false;
							break;
						}
							resolved = found[0]->type;
							resolved_type_scope = resolved_scope;
							complete_member_class_template_record(found[0]);
							have_resolved_type = true;
							continue;
					}
							TypePtr owner = pa11::strip_cv(resolved);
								if (owner->kind != pa11::TypeKind::Record ||
							    owner->scope == NULL)
							{
								resolved_ok = false;
								break;
							}
					complete_template_record(owner);
					if (at(OP_LT))
					{
						vector<TemplateArgument> member_args;
						TemplateDeclaration* alias =
							find_alias_template(owner->scope, member_name);
						TemplateDeclaration* klass = alias == NULL
							? find_class_template(owner->scope, member_name)
							: NULL;
						if (alias == NULL && klass == NULL)
						{
							resolved_ok = false;
							break;
						}
							parse_template_argument_list(member_args);
							resolved = alias != NULL
								? instantiate_alias_template(alias,
								                             member_args)
								: instantiate_class_template(klass,
								                             member_args);
							resolved_type_scope = NULL;
						}
					else
					{
									vector<Binding*> found =
										lookup_qualified_set(owner->scope,
										                     member_name,
										                     pa11::LOOKUP_TYPE);
										if (found.empty())
									{
										resolved_ok = false;
										break;
									}
							resolved = found[0]->type;
							resolved_type_scope = owner->scope;
							complete_member_class_template_record(found[0]);
						}
					}
					if (resolved_ok && have_resolved_type && pos_ != concrete_save)
					{
								out = substitute_template_type_in_scope(
									resolved,
									resolved_type_scope);
							if (active_class_instantiations_.empty() &&
						    template_type_substitutions_.empty() &&
						    template_value_substitutions_.empty() &&
						    !type_is_template_dependent(out) &&
						    !type_parse_mentions_active_record(
							    out,
							    active_class_instantiations_,
							    record_template_arguments_))
							complete_template_record(out);
					return true;
				}
				pos_ = concrete_save;
			}
		}
		if (have_type_subst)
		{
			TypePtr bare_subst = pa11::strip_cv(subst);
			if (bare_subst->kind == pa11::TypeKind::TemplateParameter ||
			    bare_subst->is_dependent_typename ||
			    type_is_template_dependent(subst))
				dependent_root = true;
		}
		if (dependent_base_qualifier)
			dependent_root = true;
		vector<TemplateArgument> root_arguments;
		bool have_root_arguments = false;
		bool concrete_root_template_failed = false;
		if (at(OP_LT))
		{
			bool root_has_decltype =
				angle_tokens_contain_decltype(tokens_, pos_);
			try
			{
				parse_template_argument_list(root_arguments);
				if (!template_type_substitutions_.empty() ||
				    !template_value_substitutions_.empty())
				{
					for (size_t i = 0; i < root_arguments.size(); ++i)
						if (!argument_has_replayable_dependent_value(
							    root_arguments[i]))
							root_arguments[i] =
								substitute_template_argument(
									root_arguments[i]);
					vector<TemplateArgument> flattened;
					for (size_t i = 0; i < root_arguments.size(); ++i)
					{
						if (root_arguments[i].kind ==
						    TemplateArgumentKind::Pack)
						{
							flattened.insert(
								flattened.end(),
								root_arguments[i].pack.begin(),
								root_arguments[i].pack.end());
							continue;
						}
						flattened.push_back(root_arguments[i]);
					}
					root_arguments.swap(flattened);
				}
			}
			catch (const exception&)
			{
				pos_ = dep_save;
				root_arguments.clear();
			}
				if (pos_ != dep_save)
				{
					have_root_arguments = true;
					dep_name_template_id = true;
				dep_name_decltype = dep_name_decltype || root_has_decltype;
				dep_name += root_has_decltype
					? "<decltype>" : "<>";
				for (size_t i = 0; i < root_arguments.size(); ++i)
				{
					vector<TemplateArgument> pending;
					pending.push_back(root_arguments[i]);
					while (!pending.empty())
					{
						TemplateArgument arg = pending.back();
						pending.pop_back();
						if (arg.kind == TemplateArgumentKind::Type)
						{
							if (type_is_template_dependent(arg.type))
								dependent_root = true;
						}
						else if (arg.kind == TemplateArgumentKind::Value)
						{
							if (arg.dependent ||
							    type_is_template_dependent(arg.type))
								dependent_root = true;
						}
						else if (arg.kind == TemplateArgumentKind::Template)
						{
							if (arg.template_declaration == NULL)
								dependent_root = true;
						}
						else
						{
							for (size_t p = 0; p < arg.pack.size(); ++p)
								pending.push_back(arg.pack[p]);
						}
					}
				}
			}
		}
		if (!dependent_root && have_root_arguments && at(OP_COLON2))
		{
			size_t concrete_save = pos_;
			TemplateDeclaration* alias = find_alias_template(NULL, root_name);
			TemplateDeclaration* klass = alias == NULL
				? find_class_template(NULL, root_name) : NULL;
			if (alias != NULL || klass != NULL)
			{
						TypePtr resolved = alias != NULL
							? instantiate_alias_template(alias, root_arguments)
							: instantiate_class_template(klass, root_arguments);
						Scope* resolved_type_scope = NULL;
					bool resolved_ok = true;
				while (consume(OP_COLON2))
				{
					consume(KW_TEMPLATE);
					if (!at_identifier())
					{
						resolved_ok = false;
						break;
					}
							TypePtr owner = pa11::strip_cv(resolved);
							if (owner->kind != pa11::TypeKind::Record ||
							    owner->scope == NULL)
							{
								resolved_ok = false;
								break;
							}
					complete_template_record(owner);
					string member_name = consume_identifier();
						if (at(OP_LT))
						{
							vector<TemplateArgument> member_args;
							TemplateDeclaration* member_alias =
								find_alias_template(owner->scope, member_name);
							TemplateDeclaration* member_class =
								member_alias == NULL
								? find_class_template(owner->scope, member_name)
								: NULL;
							if (member_alias == NULL && member_class == NULL)
							{
								resolved_ok = false;
								break;
							}
								parse_template_argument_list(member_args);
							resolved = member_alias != NULL
								? instantiate_alias_template(member_alias,
								                             member_args)
								: instantiate_class_template(member_class,
								                             member_args);
							resolved_type_scope = NULL;
						}
						else
					{
									vector<Binding*> found =
										lookup_qualified_set(owner->scope,
										                     member_name,
										                     pa11::LOOKUP_TYPE);
									if (found.empty())
									{
										resolved_ok = false;
										break;
									}
							resolved = found[0]->type;
							resolved_type_scope = owner->scope;
							complete_member_class_template_record(found[0]);
						}
					}
					if (resolved_ok && pos_ != concrete_save)
					{
								out = substitute_template_type_in_scope(
									resolved,
									resolved_type_scope);
							if (active_class_instantiations_.empty() &&
						    template_type_substitutions_.empty() &&
						    template_value_substitutions_.empty() &&
						    !type_is_template_dependent(out) &&
						    !type_parse_mentions_active_record(
							    out,
							    active_class_instantiations_,
							    record_template_arguments_))
							complete_template_record(out);
					return true;
				}
				concrete_root_template_failed = true;
			}
			pos_ = concrete_save;
		}
		if (dependent_root && at(OP_COLON2))
		{
			vector<TemplateArgument> member_template_arguments;
			bool have_member_template_arguments = false;
			vector<vector<TemplateArgument> > template_argument_lists;
			if (have_root_arguments)
				template_argument_lists.push_back(root_arguments);
			while (consume(OP_COLON2))
			{
				dep_name_qualified = true;
				dep_name += "::";
				consume(KW_TEMPLATE);
				if (!at_identifier())
				{
					pos_ = dep_save;
					break;
				}
				dep_name += consume_identifier();
				if (at(OP_LT))
				{
					dep_name_decltype =
						dep_name_decltype ||
						angle_tokens_contain_decltype(tokens_, pos_);
					dep_name_template_id = true;
					dep_name += "<>";
					vector<TemplateArgument> member_args;
					parse_template_argument_list(member_args);
					template_argument_lists.push_back(member_args);
					if (!have_root_arguments &&
					    !have_member_template_arguments)
					{
						member_template_arguments = member_args;
						have_member_template_arguments = true;
					}
				}
			}
				if (pos_ != dep_save)
				{
					out = pa11::make_dependent_typename_type(
						dep_name,
						dep_name_qualified,
					dep_name_template_id,
					dep_name_decltype);
				if (have_root_arguments)
				{
					out->template_primary_name = root_name;
					out->template_arguments =
						dependent_template_instance_arguments(
							root_arguments);
				}
				else if (have_member_template_arguments)
					out->template_arguments =
						dependent_template_instance_arguments(
							member_template_arguments);
				if (!template_argument_lists.empty())
					out->dependent_typename_template_argument_lists =
						dependent_template_instance_argument_lists(
							template_argument_lists);
				return true;
			}
		}
		pos_ = dep_save;
		if (typename_disambiguator ||
		    (parsing_base_specifier_ &&
		     (template_id_qualifier || dependent_base_qualifier)))
		{
				bool hosted_active_instantiation =
					hosted_compatibility_ &&
					!active_class_instantiations_.empty();
				if (concrete_root_lookup_failed &&
				    !validating_template_definition_ &&
				    !hosted_active_instantiation &&
				    (!template_type_substitutions_.empty() ||
				     !template_value_substitutions_.empty()))
				{
					pos_ = save;
					return false;
				}
				if (concrete_root_template_failed)
				{
					bool allow_dependent_fallback =
						validating_template_definition_ ||
						hosted_active_instantiation ||
						!template_type_substitutions_.empty() ||
						!template_value_substitutions_.empty();
					if (!allow_dependent_fallback)
					{
						pos_ = save;
						return false;
					}
				}
			string dependent_name;
			bool dependent_name_template_id = false;
			bool dependent_name_decltype = false;
			if (at_identifier())
				{
					vector<TemplateArgument> dependent_name_arguments;
					bool have_dependent_name_arguments = false;
					vector<vector<TemplateArgument> >
						dependent_name_argument_lists;
					dependent_name = consume_identifier();
					if (at(OP_LT))
					{
					bool root_has_decltype =
						angle_tokens_contain_decltype(tokens_, pos_);
					dependent_name_template_id = true;
					dependent_name_decltype =
						dependent_name_decltype || root_has_decltype;
					dependent_name += root_has_decltype
						? "<decltype>" : "<>";
						parse_template_argument_list(
							dependent_name_arguments);
						have_dependent_name_arguments = true;
						dependent_name_argument_lists.push_back(
							dependent_name_arguments);
					}
					bool qualified_dependent = false;
				while (consume(OP_COLON2))
				{
					qualified_dependent = true;
					dependent_name += "::";
					consume(KW_TEMPLATE);
						if (!at_identifier())
						{
							pos_ = save;
							return false;
						}
					dependent_name += consume_identifier();
					if (at(OP_LT))
					{
						bool member_has_decltype =
							angle_tokens_contain_decltype(tokens_, pos_);
						dependent_name_template_id = true;
						dependent_name_decltype =
							dependent_name_decltype || member_has_decltype;
						dependent_name += member_has_decltype
							? "<decltype>" : "<>";
							vector<TemplateArgument> member_args;
							parse_template_argument_list(member_args);
							dependent_name_argument_lists.push_back(
								member_args);
							if (!have_dependent_name_arguments)
							{
							dependent_name_arguments = member_args;
							have_dependent_name_arguments = true;
						}
					}
				}
				if (qualified_dependent)
				{
					out = pa11::make_dependent_typename_type(
						dependent_name,
						true,
						dependent_name_template_id,
						dependent_name_decltype);
						if (have_dependent_name_arguments)
							out->template_arguments =
								dependent_template_instance_arguments(
									dependent_name_arguments);
						if (!dependent_name_argument_lists.empty())
							out->dependent_typename_template_argument_lists =
								dependent_template_instance_argument_lists(
									dependent_name_argument_lists);
						return true;
					}
				}
					pos_ = save;
					return false;
				}
	}
	if (at(KW_DECLTYPE) &&
	    !decltype_nested_name_specifier_ahead(tokens_, pos_))
	{
		pos_ = save;
		return false;
	}
	if (at(KW_DECLTYPE) ||
	    at(OP_COLON2) ||
	    (at_identifier() &&
	     (lookahead(OP_COLON2, 1) || template_id_qualifier)))
		qualifier = parse_nested_name_specifier(&spelling);
	if (qualifier != NULL)
		consume(KW_TEMPLATE);
	if (!at_identifier())
	{
		pos_ = save;
		return false;
	}
		string name = consume_identifier();
		if (qualifier == NULL)
	{
		TemplateArgument template_subst;
		bool template_id_value_subst =
			at(OP_LT) &&
			find_template_value_substitution(name, template_subst) &&
			template_subst.kind == TemplateArgumentKind::Template;
		TypePtr subst;
		if (!template_id_value_subst &&
		    find_template_type_substitution(name, subst))
		{
			out = subst;
			return true;
		}
		}
			if (at(OP_LT))
{ if (qualifier == NULL && name == "__type_pack_element") { vector<TemplateArgument> arguments; parse_template_argument_list(arguments); return try_resolve_type_pack_element(arguments, out); } if (qualifier == NULL &&
!active_class_instantiations_.empty() && active_class_instantiations_.back().declaration != NULL && active_class_instantiations_.back().declaration->name == name) { size_t template_id_save = pos_;
vector<TemplateArgument> arguments; bool parsed_template_id = false; try { parse_template_argument_list(arguments); parsed_template_id = true; } catch (const exception&) { pos_ = template_id_save; }
	if (parsed_template_id) { TypePtr active_type = active_class_instantiations_.back().type; TypePtr active_record = active_type.get() != NULL ? pa11::strip_cv(active_type) : TypePtr();
	map<const void*, vector<TemplateArgument> >::iterator active_args = active_record.get() != NULL ? record_template_arguments_.find( active_record.get()) : record_template_arguments_.end();
	if (active_args != record_template_arguments_.end() && template_argument_key(arguments) == template_argument_key(active_args->second)) { out = active_type; return true; } pos_ = template_id_save; } }
	if (qualifier == NULL && name == "__make_integer_seq") { vector<TemplateArgument> arguments; parse_template_argument_list(arguments); out = make_integer_sequence_type(arguments); return true; } if (qualifier == NULL) {
	TemplateArgument subst; if (find_template_value_substitution(name, subst) && subst.kind == TemplateArgumentKind::Template) { vector<TemplateArgument> arguments; parse_template_argument_list(arguments);
	if (subst.template_declaration != NULL) { if (subst.template_declaration->kind == TemplateDeclarationKind::Alias) { if (template_arguments_dependent(arguments) && function_template_candidate_instantiation_depth_ == 0 &&
!parsing_default_template_argument_) { out = pa11::make_dependent_typename_type( name, false, true, false); out->template_primary_name = name; out->template_arguments = dependent_template_instance_arguments( arguments);
record_template_arguments_[out.get()] = arguments; record_template_declarations_[out.get()] = subst.template_declaration; } else { out = instantiate_alias_template( subst.template_declaration, arguments); } } else if (template_arguments_dependent(arguments) &&
function_template_candidate_instantiation_depth_ == 0 && !parsing_default_template_argument_) { out = pa11::make_record_type( subst.template_declaration->name + "<>", "struct", false, NULL);
out->is_template_specialization = true; out->is_dependent_typename = true; out->dependent_typename_template_id = true; out->template_primary_name = qualified_template_declaration_name( subst.template_declaration);
out->template_arguments = dependent_template_instance_arguments( arguments); record_template_declarations_[out.get()] = subst.template_declaration; record_template_arguments_[out.get()] = arguments; } else
out = instantiate_class_template( subst.template_declaration, arguments); } else { out = pa11::make_record_type(name + "<>", "struct", false, NULL); out->is_template_specialization = true;
out->is_dependent_typename = true; out->dependent_typename_template_id = true; out->template_primary_name = name; out->template_arguments = dependent_template_instance_arguments(arguments);
record_template_arguments_[out.get()] = arguments; } return true; } } TemplateDeclaration* alias = find_alias_template(qualifier, name); if (alias != NULL) { vector<TemplateArgument> arguments;
	try { parse_template_argument_list(arguments); } catch (const exception&) { pos_ = save; return false; } bool dependent_arguments = template_arguments_dependent(arguments); bool dependent_pack_arguments = false; for (size_t ai = 0; ai < arguments.size(); ++ai) { set<string> dependency_names;
	collect_alias_dependency_names_from_argument(arguments[ai], dependency_names); for (set<string>::const_iterator ni = dependency_names.begin(); ni != dependency_names.end(); ++ni) if (active_type_parameter_pack(*ni))
		dependent_pack_arguments = true; } if (dependent_arguments &&
		name != "conditional_t" && (dependent_pack_arguments || parsing_class_specialization_pattern_)) { out = pa11::make_dependent_typename_type( name, qualifier != NULL, true, false); out->template_primary_name = name; out->template_arguments =
dependent_template_instance_arguments(arguments); record_template_arguments_[out.get()] = arguments; record_template_declarations_[out.get()] = alias; return true; } try { out = instantiate_alias_template(alias, arguments); } catch (const exception&) {
if (!dependent_arguments && template_type_substitutions_.empty() && template_value_substitutions_.empty()) throw; out = pa11::make_dependent_typename_type( name, qualifier != NULL, true, false);
out->template_primary_name = name; out->template_arguments = dependent_template_instance_arguments(arguments); record_template_arguments_[out.get()] = arguments; } return true; }
TemplateDeclaration* templ = find_class_template(qualifier, name); if (templ != NULL) { vector<TemplateArgument> arguments; try { parse_template_argument_list(arguments); } catch (const exception&) { pos_ = save; return false; }
if (template_arguments_dependent(arguments) && at(OP_DOTS)) { out = pa11::make_record_type(name + "<>", "struct", false, NULL); out->is_template_specialization = true; out->is_dependent_typename = true;
out->dependent_typename_template_id = true; out->template_primary_name = qualified_template_declaration_name(templ); out->template_arguments = dependent_template_instance_arguments(arguments);
record_template_declarations_[out.get()] = templ; record_template_arguments_[out.get()] = arguments; return true; } if (typename_disambiguator && template_arguments_dependent(arguments) && at(OP_COLON2)) {
string dependent_name = name + "<>"; vector<vector<TemplateArgument> > argument_lists; argument_lists.push_back(arguments); while (consume(OP_COLON2)) { dependent_name += "::"; consume(KW_TEMPLATE); if (!at_identifier())
{ pos_ = save; return false; } dependent_name += consume_identifier(); if (at(OP_LT)) { dependent_name += "<>"; vector<TemplateArgument> member_args; parse_template_argument_list(member_args);
	argument_lists.push_back(member_args); } } out = pa11::make_dependent_typename_type( dependent_name, true, true, false); out->template_primary_name = name; out->template_arguments =
	dependent_template_instance_arguments(arguments); out->dependent_typename_template_argument_lists = dependent_template_instance_argument_lists( argument_lists); return true; } bool defer_completion = true; if (defer_completion) ++defer_class_template_completion_depth_; try {
out = instantiate_class_template(templ, arguments); } catch (...) { if (defer_completion) --defer_class_template_completion_depth_; throw; } if (defer_completion) --defer_class_template_completion_depth_;
if (typename_disambiguator && at(OP_COLON2)) { TypePtr resolved = out; Scope* resolved_type_scope = NULL; string dependent_name = name + "<>"; vector<vector<TemplateArgument> > argument_lists;
argument_lists.push_back(arguments); bool dependent_lookup = false; bool resolved_ok = true; while (consume(OP_COLON2)) { dependent_name += "::"; consume(KW_TEMPLATE); if (!at_identifier()) { resolved_ok = false; break;
} string member_name = consume_identifier(); dependent_name += member_name; TypePtr owner = resolved.get() != NULL ? pa11::strip_cv(resolved) : TypePtr(); if (owner.get() != NULL &&
	owner->kind == pa11::TypeKind::Record && owner->scope != NULL) { complete_template_record_for_member_lookup(owner); if (hosted_compatibility_ && member_name == "type") { TypePtr invoke_type = hosted_invoke_result_type(owner); if (invoke_type.get() != NULL) { resolved = invoke_type; resolved_type_scope = NULL; continue; } } if (at(OP_LT)) { vector<TemplateArgument> member_args; TemplateDeclaration* member_alias =
find_alias_template(owner->scope, member_name); TemplateDeclaration* member_class = member_alias == NULL ? find_class_template(owner->scope, member_name) : NULL; if (member_alias == NULL && member_class == NULL) {
resolved_ok = false; break; } parse_template_argument_list(member_args); argument_lists.push_back(member_args); resolved = member_alias != NULL ? instantiate_alias_template(member_alias, member_args)
: instantiate_class_template(member_class, member_args); resolved_type_scope = NULL; continue; } vector<Binding*> found = lookup_qualified_set(owner->scope, member_name, pa11::LOOKUP_TYPE); if (found.empty()) {
resolved_ok = false; break; } Binding* member_binding = complete_member_class_template_record(found[0], owner->scope); resolved = member_binding->type; resolved_type_scope = owner->scope; continue; } dependent_lookup = true; if (at(OP_LT)) { dependent_name += "<>";
vector<TemplateArgument> member_args; parse_template_argument_list(member_args); argument_lists.push_back(member_args); } } if (!resolved_ok) { pos_ = save; return false; } if (dependent_lookup) {
out = pa11::make_dependent_typename_type( dependent_name, true, true, false); out->template_primary_name = name; out->template_arguments = dependent_template_instance_arguments(arguments);
out->dependent_typename_template_argument_lists = dependent_template_instance_argument_lists( argument_lists); return true; } out = substitute_template_type_in_scope( resolved, resolved_type_scope); return true; }
return true; } }
		if (qualifier == NULL && !at(OP_LT))
			for (size_t ai = active_class_instantiations_.size();
			     ai > 0;
			     --ai)
			{
				const ActiveClassInstantiation& active =
					active_class_instantiations_[ai - 1];
				TypePtr active_record = active.type.get() != NULL
					? pa11::strip_cv(active.type) : TypePtr();
				if (active_record.get() == NULL ||
				    active_record->kind != pa11::TypeKind::Record)
					continue;
				bool current_instantiation_name =
					(active.declaration != NULL &&
					 active.declaration->name == name) ||
					name == active_record->name ||
					name == active_record->template_primary_name;
				if (current_instantiation_name)
				{
					out = active.type;
					return true;
				}
			}
		if (qualifier == NULL && !at(OP_LT))
			for (Scope* scope = current_scope(); scope != NULL;
			     scope = scope->parent)
			{
				TypePtr current_record = pa11::record_type_for_scope(scope);
				TypePtr current_bare = current_record.get() != NULL
					? pa11::strip_cv(current_record) : TypePtr();
				bool current_instantiation_name =
					current_bare.get() != NULL &&
					current_bare->kind == pa11::TypeKind::Record &&
					(name == scope->name ||
					 name == current_bare->name ||
					 name == current_bare->template_primary_name);
				if (current_instantiation_name)
				{
					out = current_record;
					return true;
				}
			}
		vector<Binding*> found = qualifier != NULL
			? lookup_qualified_set(qualifier, name, pa11::LOOKUP_TYPE)
			: lookup_unqualified_set(current_scope(), name, pa11::LOOKUP_TYPE);
		if (found.empty())
		{
			TypePtr qualifier_record = qualifier != NULL
				? pa11::record_type_for_scope(qualifier) : TypePtr();
		qualifier_record = qualifier_record.get() != NULL
			? pa11::strip_cv(qualifier_record) : TypePtr();
			if ((typename_disambiguator || parsing_base_specifier_) &&
			    qualifier_record.get() != NULL &&
			    qualifier_record->kind == pa11::TypeKind::Record &&
			    qualifier_record->is_template_specialization &&
		    type_is_template_dependent(qualifier_record) &&
		    !qualifier_record->template_primary_name.empty())
		{
			out = pa11::make_dependent_typename_type(
				qualifier_record->template_primary_name + "<>::" + name,
				true,
				true,
				false);
				out->template_primary_name =
					qualifier_record->template_primary_name;
				out->template_arguments = qualifier_record->template_arguments;
				out->dependent_typename_template_argument_lists =
					qualifier_record->
						dependent_typename_template_argument_lists;
				if (out->dependent_typename_template_argument_lists.empty() &&
				    !out->template_arguments.empty())
					out->dependent_typename_template_argument_lists.push_back(
						out->template_arguments);
				return true;
			}
		pos_ = save;
		return false;
	}
	Binding* binding = found[0];
	if (binding->is_private || binding->is_protected_member)
	{
		if (binding->is_private &&
		    !active_context_has_class_access(binding->owner))
			throw runtime_error("private type access");
			if (binding->is_protected_member &&
			    !active_context_has_class_access(binding->owner))
				throw runtime_error("protected type access");
	}
	binding = complete_member_class_template_record(binding, qualifier);
		out = qualifier != NULL
			? substitute_template_type_in_scope(binding->type, qualifier)
			: binding->type;
		TypePtr out_bare = out.get() != NULL ? pa11::strip_cv(out) : TypePtr();
		bool deferred_template_specialization =
			out_bare.get() != NULL &&
			out_bare->kind == pa11::TypeKind::Record &&
			out_bare->is_template_specialization &&
			(!out_bare->complete ||
			 out_bare->template_record_shallow_complete);
				if (active_class_instantiations_.empty() &&
				    template_type_substitutions_.empty() &&
				    template_value_substitutions_.empty() &&
				    defer_class_template_completion_depth_ == 0 &&
				    !deferred_template_specialization &&
				    !(hosted_compatibility_ &&
				      hosted_library_record_type(out)) &&
			    !type_is_template_dependent(out) &&
			    !type_parse_mentions_active_record(out,
			                                 active_class_instantiations_,
		                                 record_template_arguments_))
		complete_template_record(out);
	(void)typename_disambiguator;
	return true;
}

}  // namespace internal
}  // namespace pa12
