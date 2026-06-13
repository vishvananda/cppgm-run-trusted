#include "pa12_templates_instance_support.h"

#include <cstdint>
#include <stdexcept>

using namespace std;

namespace pa12 {
namespace internal {

TypePtr Parser::make_integer_sequence_type(
	const vector<TemplateArgument>& arguments)
{
	if (arguments.size() != 3 ||
	    arguments[0].kind != TemplateArgumentKind::Template ||
	    arguments[1].kind != TemplateArgumentKind::Type ||
	    arguments[2].kind != TemplateArgumentKind::Value)
		throw runtime_error("invalid __make_integer_seq");
	TypePtr value_type = arguments[1].type;
	bool dependent =
		value_type.get() == NULL ||
		type_is_template_dependent(value_type) ||
		arguments[2].dependent ||
		type_is_template_dependent(arguments[2].type);
	if (dependent)
	{
		TypePtr out = pa11::make_dependent_typename_type(
			"__make_integer_seq",
			false,
			true,
			false);
		out->template_primary_name = "__make_integer_seq";
		out->template_arguments = template_instance_arguments(arguments);
		return out;
	}
	TemplateDeclaration* sequence_template =
		arguments[0].template_declaration;
	if (sequence_template == NULL && !arguments[0].value_name.empty())
		sequence_template = find_class_template(NULL, arguments[0].value_name);
	if (sequence_template == NULL)
		throw runtime_error("invalid __make_integer_seq template");
	vector<TemplateArgument> sequence_arguments;
	sequence_arguments.push_back(TemplateArgument::type_arg(value_type));
	for (uint64_t i = 0; i < arguments[2].value; ++i)
		sequence_arguments.push_back(
			TemplateArgument::value_arg(value_type, i));
	return instantiate_class_template(sequence_template, sequence_arguments);
}

TypePtr Parser::substitute_type_for_template_match(
	TypePtr type,
	const map<string, TemplateArgument>& deduced)
{
	vector<map<string, TypePtr> > save_subst = template_type_substitutions_;
	vector<map<string, TemplateArgument> > save_value_subst =
		template_value_substitutions_;
	vector<set<string> > save_pack_subst = template_type_parameter_packs_;
	map<string, TypePtr> subst;
	map<string, TemplateArgument> value_subst;
	set<string> pack_subst;
	for (map<string, TemplateArgument>::const_iterator it = deduced.begin();
	     it != deduced.end();
	     ++it)
	{
		const TemplateArgument& arg = it->second;
		if (arg.kind == TemplateArgumentKind::Type)
			subst[it->first] = arg.type;
		else
			value_subst[it->first] = arg;
		if (arg.kind == TemplateArgumentKind::Pack)
		{
			value_subst[it->first] = arg;
			pack_subst.insert(it->first);
			subst[it->first] =
				pa11::make_template_parameter_type(it->first);
		}
	}
	template_type_substitutions_.push_back(subst);
	template_value_substitutions_.push_back(value_subst);
	template_type_parameter_packs_.push_back(pack_subst);
	TypePtr out;
	try
	{
		out = substitute_template_type(type);
	}
	catch (...)
	{
		template_type_substitutions_ = save_subst;
		template_value_substitutions_ = save_value_subst;
		template_type_parameter_packs_ = save_pack_subst;
		throw;
	}
	template_type_substitutions_ = save_subst;
	template_value_substitutions_ = save_value_subst;
	template_type_parameter_packs_ = save_pack_subst;
	return out;
}

TypePtr Parser::expand_alias_template_for_match(
	TypePtr type,
	const map<string, TemplateArgument>& deduced)
{
	if (type.get() == NULL ||
	    !type->is_dependent_typename ||
	    type->dependent_typename_qualified ||
	    !type->dependent_typename_template_id ||
	    type->template_arguments.empty())
		return TypePtr();
	string root_name = !type->template_primary_name.empty()
		? type->template_primary_name
		: type->name;
	size_t root_template = root_name.find('<');
	if (root_template != string::npos)
		root_name = root_name.substr(0, root_template);
	TemplateDeclaration* alias = find_alias_template(NULL, root_name);
	if (alias == NULL)
	{
		for (map<Scope*, map<string, TemplateDeclaration*> >::const_iterator
			     sit = alias_templates_.begin();
		     sit != alias_templates_.end() && alias == NULL;
			     ++sit)
			{
				map<string, TemplateDeclaration*>::const_iterator it =
					sit->second.find(root_name);
				if (it != sit->second.end())
					alias = it->second;
			}
	}
	if (alias == NULL)
		return TypePtr();

	vector<TemplateArgument> arguments;
	for (size_t i = 0; i < type->template_arguments.size(); ++i)
		arguments.push_back(
			raw_template_argument_from_instance_argument(
				type->template_arguments[i]));
	vector<TemplateArgument> full_args =
		complete_template_arguments(alias, arguments);

	size_t save_pos = pos_;
	vector<Scope*> save_scopes = scopes_;
	vector<map<string, TypePtr> > save_subst = template_type_substitutions_;
	vector<map<string, TemplateArgument> > save_value_subst =
		template_value_substitutions_;
	vector<set<string> > save_pack_subst = template_type_parameter_packs_;

	map<string, TypePtr> deduced_subst;
	map<string, TemplateArgument> deduced_value_subst;
	set<string> deduced_pack_subst;
	for (map<string, TemplateArgument>::const_iterator it = deduced.begin();
	     it != deduced.end();
	     ++it)
	{
		const TemplateArgument& arg = it->second;
		if (arg.kind == TemplateArgumentKind::Type)
			deduced_subst[it->first] = arg.type;
		else
			deduced_value_subst[it->first] = arg;
		if (arg.kind == TemplateArgumentKind::Pack)
		{
			deduced_value_subst[it->first] = arg;
			deduced_pack_subst.insert(it->first);
			deduced_subst[it->first] =
				pa11::make_template_parameter_type(it->first);
		}
	}
		TypePtr out;
		try
		{
			template_type_substitutions_.push_back(deduced_subst);
			template_value_substitutions_.push_back(deduced_value_subst);
		template_type_parameter_packs_.push_back(deduced_pack_subst);
		template_type_substitutions_.insert(
			template_type_substitutions_.end(),
			alias->outer_type_substitutions.begin(),
			alias->outer_type_substitutions.end());
			template_value_substitutions_.insert(
				template_value_substitutions_.end(),
				alias->outer_value_substitutions.begin(),
				alias->outer_value_substitutions.end());

			vector<TemplateArgument> substituted_full_args = full_args;
			for (size_t i = 0; i < substituted_full_args.size(); ++i)
				substituted_full_args[i] =
					substitute_template_argument(substituted_full_args[i]);

			map<string, TypePtr> subst;
			map<string, TemplateArgument> value_subst;
			set<string> pack_subst;
			for (size_t i = 0; i < substituted_full_args.size() &&
			     i < alias->parameters.size(); ++i)
				if (!alias->parameters[i].name.empty())
				{
					const string& name = alias->parameters[i].name;
					if (alias->parameters[i].kind == TemplateParameterKind::Type)
					{
						if (alias->parameters[i].is_pack)
						{
							subst[name] =
								pa11::make_template_parameter_type(name);
							value_subst[name] = substituted_full_args[i];
							pack_subst.insert(name);
						}
						else
							subst[name] = substituted_full_args[i].type;
					}
					else
						value_subst[name] = substituted_full_args[i];
				}
			template_type_substitutions_.push_back(subst);
			template_value_substitutions_.push_back(value_subst);
			template_type_parameter_packs_.push_back(pack_subst);
		scopes_.clear();
		scopes_.push_back(alias->lexical_scope != NULL
		                  ? alias->lexical_scope
		                  : alias->owner);
		pos_ = alias->decl_begin;
		expect(KW_USING);
		consume_identifier();
		expect(OP_ASS);
		out = parse_type_id();
	}
	catch (...)
	{
		template_type_substitutions_ = save_subst;
		template_value_substitutions_ = save_value_subst;
		template_type_parameter_packs_ = save_pack_subst;
		scopes_ = save_scopes;
		pos_ = save_pos;
		throw;
	}
	template_type_substitutions_ = save_subst;
	template_value_substitutions_ = save_value_subst;
	template_type_parameter_packs_ = save_pack_subst;
	scopes_ = save_scopes;
	pos_ = save_pos;
	return out;
}

TypePtr Parser::resolve_dependent_typename_for_template_match(
	TypePtr type) const
{
	if (type.get() == NULL || !type->is_dependent_typename)
		return TypePtr();
	try
	{
		TypePtr resolved = resolve_dependent_typename_type(type);
		if (resolved.get() == NULL || resolved == type)
			return TypePtr();
		return substitute_template_type(resolved);
	}
	catch (const exception&)
	{
		return TypePtr();
	}
}

TemplateDeclaration* Parser::class_template_declaration_for_match(
	TypePtr type) const
{
	TypePtr bare = type.get() != NULL ? pa11::strip_cv(type) : TypePtr();
	if (bare.get() == NULL ||
	    bare->kind != pa11::TypeKind::Record ||
	    !bare->is_template_specialization)
		return NULL;
	map<const void*, TemplateDeclaration*>::const_iterator found =
		record_template_declarations_.find(bare.get());
	if (found != record_template_declarations_.end())
		return found->second;
	if (bare->template_primary_name.empty())
		return NULL;
	Scope* owner = bare->scope != NULL ? bare->scope->parent : NULL;
		if (owner != NULL)
		{
			TemplateDeclaration* resolved =
				const_cast<Parser*>(this)->find_class_template(
					owner,
					bare->template_primary_name);
			if (resolved != NULL)
				return resolved;
		}
		{
			Scope* qualifier = NULL;
			string name = bare->template_primary_name;
		const_cast<Parser*>(this)->resolve_template_name_spelling(
			bare->template_primary_name,
			qualifier,
			name);
		TemplateDeclaration* resolved =
			const_cast<Parser*>(this)->find_class_template(qualifier, name);
		if (resolved != NULL)
			return resolved;
		TemplateDeclaration* unique = NULL;
		for (map<Scope*, map<string, TemplateDeclaration*> >::const_iterator
			     sit = class_templates_.begin();
		     sit != class_templates_.end();
		     ++sit)
		{
			map<string, TemplateDeclaration*>::const_iterator it =
				sit->second.find(name);
			if (it == sit->second.end())
				continue;
			if (unique != NULL && unique != it->second)
				return NULL;
			unique = it->second;
			}
			return unique;
		}
	}

TemplateArgument Parser::template_argument_from_instance_argument(
	const pa11::TemplateInstanceArgument& argument) const
{
	if (argument.kind == pa11::TemplateInstanceArgumentKind::Type)
	{
		try
		{
			return TemplateArgument::type_arg(
				substitute_template_type(argument.type));
		}
		catch (const runtime_error& err)
		{
			TypePtr bare = argument.type.get() != NULL
				? pa11::strip_cv(argument.type) : TypePtr();
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
			value_arg.value_member_name = bare->name.substr(member_pos + 2);
			string owner_name = bare->template_primary_name;
			if (owner_name.empty())
			{
				string root = bare->name.substr(0, member_pos);
				size_t template_pos = root.find('<');
				owner_name = root.substr(0, template_pos);
			}
			value_arg.value_owner_template_name = owner_name;
			const vector<pa11::TemplateInstanceArgument>* owner_arguments =
				!bare->template_arguments.empty()
				? &bare->template_arguments
				: (!bare->dependent_typename_template_argument_lists.empty()
				   ? &bare->dependent_typename_template_argument_lists[0]
				   : NULL);
			if (owner_arguments != NULL)
				for (size_t ai = 0; ai < owner_arguments->size(); ++ai)
				{
					TemplateArgument owner_arg =
						raw_template_argument_from_instance_argument(
							(*owner_arguments)[ai]);
					owner_arg = substitute_template_argument(owner_arg);
					value_arg.value_owner_template_arguments.push_back(
						template_instance_argument(owner_arg));
				}
			return substitute_template_argument(value_arg);
		}
	}
	if (argument.kind == pa11::TemplateInstanceArgumentKind::Value)
	{
		TypePtr type = argument.type.get() != NULL
			? substitute_template_type(argument.type) : TypePtr();
		if (argument.dependent)
		{
			TemplateArgument out = TemplateArgument::dependent_value_arg(type);
			out.value_name = argument.value_name;
			out.value_negated = argument.value_negated;
			out.value_owner_template_name =
				argument.value_owner_template_name;
			out.value_member_name = argument.value_member_name;
			out.value_owner_template_arguments =
				argument.value_owner_template_arguments;
			out.value_expr_begin = argument.value_expr_begin;
			out.value_expr_end = argument.value_expr_end;
			return substitute_template_argument(out);
		}
		TemplateArgument out = TemplateArgument::value_arg(type,
		                                                   argument.value);
		out.value_name = argument.value_name;
		out.value_negated = argument.value_negated;
		out.value_owner_template_name =
			argument.value_owner_template_name;
		out.value_member_name = argument.value_member_name;
		out.value_owner_template_arguments =
			argument.value_owner_template_arguments;
		out.value_expr_begin = argument.value_expr_begin;
		out.value_expr_end = argument.value_expr_end;
		return out;
	}
	if (argument.kind == pa11::TemplateInstanceArgumentKind::Template)
	{
		TemplateArgument subst;
			string template_name = argument.template_name;
			Scope* qualifier = NULL;
			string unqualified_name = template_name;
			const_cast<Parser*>(this)->resolve_template_name_spelling(
				template_name,
				qualifier,
				unqualified_name);
		if (qualifier == NULL &&
		    find_template_value_substitution(template_name, subst))
			return subst;
		TemplateDeclaration* declaration =
			const_cast<Parser*>(this)->find_class_template(
				qualifier,
				unqualified_name);
		if (declaration == NULL)
			declaration = const_cast<Parser*>(this)->find_alias_template(
				qualifier,
				unqualified_name);
		if (declaration != NULL)
			return TemplateArgument::template_arg(declaration);
		TemplateArgument out = TemplateArgument::template_arg(NULL);
		out.value_name = template_name;
		return out;
	}
	if (argument.pack.size() == 1)
	{
		TemplateArgument element =
			raw_template_argument_from_instance_argument(argument.pack[0]);
		if (element.kind != TemplateArgumentKind::Pack &&
		    single_instance_pack_element_is_expansion(element))
		{
			element.pack_expansion = true;
			return element;
		}
	}
	vector<TemplateArgument> pack;
	for (size_t i = 0; i < argument.pack.size(); ++i)
		pack.push_back(
			template_argument_from_instance_argument(argument.pack[i]));
	if (pack.size() == 1 &&
	    pack[0].kind != TemplateArgumentKind::Pack &&
	    single_instance_pack_element_is_expansion(pack[0]))
	{
		pack[0].pack_expansion = true;
		return pack[0];
	}
	return TemplateArgument::pack_arg(pack);
}

bool Parser::dependent_typename_template_argument_list(
	TypePtr type,
	size_t& index,
	vector<TemplateArgument>& arguments) const
{
	arguments.clear();
	if (type.get() == NULL)
		return false;
	if (!type->dependent_typename_template_argument_lists.empty())
	{
		if (index >= type->dependent_typename_template_argument_lists.size())
			return false;
		const vector<pa11::TemplateInstanceArgument>& stored =
			type->dependent_typename_template_argument_lists[index++];
		arguments.reserve(stored.size());
		for (size_t i = 0; i < stored.size(); ++i)
			arguments.push_back(
				template_argument_from_instance_argument(stored[i]));
		return true;
	}
	if (type->template_arguments.empty())
		return false;
	arguments.reserve(type->template_arguments.size());
	for (size_t i = 0; i < type->template_arguments.size(); ++i)
		arguments.push_back(
			template_argument_from_instance_argument(
				type->template_arguments[i]));
	++index;
	return true;
}

}  // namespace internal
}  // namespace pa12
