#include "pa12_internal.h"

#include <stdexcept>

using namespace std;

namespace pa12 {
namespace internal {
namespace {

pa11::TemplateInstanceArgument completed_instance_argument(
	const TemplateArgument& argument)
{
	if (argument.pack_expansion && argument.kind != TemplateArgumentKind::Pack)
	{
		TemplateArgument element = argument;
		element.pack_expansion = false;
		vector<pa11::TemplateInstanceArgument> pack;
		pack.push_back(completed_instance_argument(element));
		return pa11::TemplateInstanceArgument::pack_arg(pack);
	}
	if (argument.kind == TemplateArgumentKind::Type)
		return pa11::TemplateInstanceArgument::type_arg(argument.type);
	if (argument.kind == TemplateArgumentKind::Value)
	{
		pa11::TemplateInstanceArgument out = argument.dependent
			? pa11::TemplateInstanceArgument::dependent_value_arg(argument.type)
			: pa11::TemplateInstanceArgument::value_arg(argument.type,
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
	if (argument.kind == TemplateArgumentKind::Template)
	{
		pa11::TemplateInstanceArgument out =
			pa11::TemplateInstanceArgument::template_arg(
				argument.template_declaration != NULL
				? qualified_template_declaration_name(
					argument.template_declaration)
				: argument.value_name);
		out.dependent = argument.template_declaration == NULL;
		return out;
	}
	vector<pa11::TemplateInstanceArgument> pack;
	for (size_t i = 0; i < argument.pack.size(); ++i)
	{
		TemplateArgument element = argument.pack[i];
		if (element.kind == TemplateArgumentKind::Value &&
		    !element.dependent)
			element.pack_expansion = false;
		pack.push_back(completed_instance_argument(element));
	}
	pa11::TemplateInstanceArgument out =
		pa11::TemplateInstanceArgument::pack_arg(pack);
	out.value_name = argument.value_name;
	out.template_name = argument.value_name;
	return out;
}

bool template_argument_kind_matches_parameter(
	const TemplateArgument& argument,
	const TemplateParameterInfo& parameter)
{
	if (parameter.kind == TemplateParameterKind::Type)
		return argument.kind == TemplateArgumentKind::Type;
	if (parameter.kind == TemplateParameterKind::NonType)
		return argument.kind == TemplateArgumentKind::Value;
	if (argument.kind != TemplateArgumentKind::Template)
		return false;
	if (argument.template_declaration == NULL)
		return true;
	if (argument.template_declaration->kind == TemplateDeclarationKind::Alias)
		return true;
	const vector<TemplateParameterInfo>& params =
		argument.template_declaration->parameters;
	if (parameter.template_parameters.size() == 1 &&
	    parameter.template_parameters[0].kind == TemplateParameterKind::Type)
	{
		size_t required = 0;
		for (size_t i = 0; i < params.size(); ++i)
		{
			if (params[i].kind != TemplateParameterKind::Type)
				return false;
			if (!params[i].has_default && !params[i].is_pack)
				++required;
		}
		return required <= 1;
	}
	size_t actual = 0;
	for (size_t expected = 0;
	     expected < parameter.template_parameters.size();
	     ++expected)
	{
		const TemplateParameterInfo& expected_param =
			parameter.template_parameters[expected];
		if (expected_param.is_pack)
		{
			for (; actual < params.size(); ++actual)
				if (params[actual].kind != expected_param.kind)
					return false;
			return true;
		}
		if (actual >= params.size())
			return false;
		if (params[actual].kind != expected_param.kind ||
		    params[actual].is_pack != expected_param.is_pack)
			return false;
		++actual;
	}
	return actual == params.size();
}

bool unsigned_integral_template_parameter(TypePtr type)
{
	TypePtr bare = type.get() != NULL ? pa11::strip_cv(type) : TypePtr();
	if (bare.get() == NULL)
		return false;
	if (bare->kind == pa11::TypeKind::Enum)
	{
		switch (bare->enum_underlying)
		{
		case FT_UNSIGNED_CHAR:
		case FT_UNSIGNED_SHORT_INT:
		case FT_UNSIGNED_INT:
		case FT_UNSIGNED_LONG_INT:
		case FT_UNSIGNED_LONG_LONG_INT:
			return true;
		default:
			return false;
		}
	}
	if (bare->kind != pa11::TypeKind::Fundamental)
		return false;
	switch (bare->fundamental)
	{
	case FT_BOOL:
	case FT_UNSIGNED_CHAR:
	case FT_UNSIGNED_SHORT_INT:
	case FT_UNSIGNED_INT:
	case FT_UNSIGNED_LONG_INT:
	case FT_UNSIGNED_LONG_LONG_INT:
	case FT_CHAR16_T:
	case FT_CHAR32_T:
		return true;
	default:
		return false;
	}
}

TemplateArgument convert_non_type_template_argument(
	TemplateArgument argument,
	TypePtr parameter_type)
{
	if (argument.kind != TemplateArgumentKind::Value ||
	    parameter_type.get() == NULL)
		return argument;
	if (argument.value_binding != NULL)
	{
		TypePtr parameter_bare = pa11::strip_cv(parameter_type);
		TypePtr argument_bare = argument.type.get() != NULL
			? pa11::strip_cv(argument.type) : TypePtr();
		if (parameter_bare->kind == pa11::TypeKind::LValueReference ||
		    parameter_bare->kind == pa11::TypeKind::RValueReference)
		{
			TypePtr target = pa11::strip_cv(parameter_bare->base);
			TypePtr source = argument.value_binding->type.get() != NULL
				? pa11::strip_cv(argument.value_binding->type)
				: TypePtr();
			if (source.get() == NULL || !pa11::same_type(target, source))
				throw runtime_error("invalid non-type template argument");
			argument.type = parameter_type;
			return argument;
		}
		if (argument.value_binding->kind == BindingKind::Function &&
		    (pa11::same_type(argument.type, parameter_type) ||
		     (parameter_bare->kind == pa11::TypeKind::Function &&
		      argument_bare.get() != NULL &&
		      argument_bare->kind == pa11::TypeKind::Pointer &&
		      pa11::same_type(argument_bare->base, parameter_bare))))
		{
			argument.type = parameter_type;
			return argument;
		}
		if (parameter_bare->kind == pa11::TypeKind::MemberPointer &&
		    argument_bare.get() != NULL &&
		    argument_bare->kind == pa11::TypeKind::MemberPointer &&
		    pa11::same_type(argument_bare, parameter_bare))
		{
			argument.type = parameter_type;
			return argument;
		}
		throw runtime_error("invalid non-type template argument");
	}
	TypePtr bare = pa11::strip_cv(parameter_type);
	if (bare->kind == pa11::TypeKind::Fundamental &&
	    bare->fundamental == FT_BOOL)
		argument.value = argument.value != 0 ? 1 : 0;
	else
	{
		size_t size = 0;
		try
		{
			size = pa11::type_size(parameter_type);
		}
		catch (const runtime_error&)
		{
			size = 0;
		}
		if (size > 0 && size < 8)
		{
			uint64_t mask = (uint64_t(1) << (size * 8)) - 1;
			argument.value &= mask;
			if (!unsigned_integral_template_parameter(parameter_type))
			{
				uint64_t sign = uint64_t(1) << (size * 8 - 1);
				if ((argument.value & sign) != 0)
					argument.value |= ~mask;
			}
		}
	}
	argument.type = parameter_type;
	return argument;
}

bool dependent_typename_disabled_enable_if_argument(
	TypePtr type,
	const vector<TemplateArgument>& arguments)
{
	if (type.get() == NULL || arguments.empty() ||
	    arguments[0].kind != TemplateArgumentKind::Value ||
	    arguments[0].dependent || arguments[0].value != 0)
		return false;
	string root_name = type->name;
	size_t type_suffix = root_name.find("::type");
	if (type_suffix != string::npos)
		root_name = root_name.substr(0, type_suffix);
	size_t template_suffix = root_name.find('<');
	if (template_suffix != string::npos)
		root_name = root_name.substr(0, template_suffix);
	size_t qualifier = root_name.rfind("::");
	if (qualifier != string::npos)
		root_name = root_name.substr(qualifier + 2);
	return root_name == "enable_if" ||
	       root_name == "enable_if_t" ||
	       root_name == "__enable_if_t";
}

}  // namespace

struct TemplateArgumentCompleter
{
	Parser& parser;
	TemplateDeclaration* declaration;
	const vector<TemplateArgument>& explicit_arguments;
	vector<TemplateArgument> explicit_expanded;
	vector<TemplateArgument> out;
	size_t explicit_index;

	TemplateArgumentCompleter(Parser& p,
	                          TemplateDeclaration* d,
	                          const vector<TemplateArgument>& args)
		: parser(p),
		  declaration(d),
		  explicit_arguments(args),
		  explicit_index(0)
	{
	}

	struct SubstitutionScope
	{
		Parser& parser;
		size_t type_size;
		size_t value_size;
		size_t pack_size;

		SubstitutionScope(Parser& p,
		                  TemplateDeclaration* declaration,
		                  const map<string, TypePtr>& subst,
		                  const map<string, TemplateArgument>& value_subst,
		                  const set<string>& pack_subst)
			: parser(p),
			  type_size(p.template_type_substitutions_.size()),
			  value_size(p.template_value_substitutions_.size()),
			  pack_size(p.template_type_parameter_packs_.size())
		{
			parser.template_type_substitutions_.insert(
				parser.template_type_substitutions_.end(),
				declaration->outer_type_substitutions.begin(),
				declaration->outer_type_substitutions.end());
			parser.template_value_substitutions_.insert(
				parser.template_value_substitutions_.end(),
				declaration->outer_value_substitutions.begin(),
				declaration->outer_value_substitutions.end());
			parser.template_type_substitutions_.push_back(subst);
			parser.template_value_substitutions_.push_back(value_subst);
			parser.template_type_parameter_packs_.push_back(pack_subst);
		}

		~SubstitutionScope()
		{
			parser.template_type_substitutions_.resize(type_size);
			parser.template_value_substitutions_.resize(value_size);
			parser.template_type_parameter_packs_.resize(pack_size);
		}
	};

	vector<TemplateArgument> run()
	{
		expand_explicit_arguments();
		for (size_t i = 0; i < declaration->parameters.size(); ++i)
			append_parameter(i);
		if (explicit_index != explicit_expanded.size())
			throw runtime_error("too many template arguments");
		finalize_non_type_arguments();
		return out;
	}

	void expand_explicit_arguments()
	{
		for (size_t i = 0; i < explicit_arguments.size(); ++i)
		{
			vector<TemplateArgument> expansion;
			bool keep_explicit_pack =
				explicit_arguments.size() == declaration->parameters.size() &&
				i < declaration->parameters.size() &&
				declaration->parameters[i].is_pack &&
				explicit_arguments[i].kind == TemplateArgumentKind::Pack;
			bool keep_single_type_pattern =
				i < declaration->parameters.size() &&
				!declaration->parameters[i].is_pack &&
				explicit_arguments[i].kind == TemplateArgumentKind::Type;
			if (keep_single_type_pattern)
				keep_single_type_pattern =
					kept_single_type_pattern(explicit_arguments[i]);
			if (keep_explicit_pack || keep_single_type_pattern)
				expansion.push_back(explicit_arguments[i]);
			else
				expansion =
					parser.expand_template_argument_pack(explicit_arguments[i]);
			explicit_expanded.insert(explicit_expanded.end(),
			                         expansion.begin(),
			                         expansion.end());
		}
	}

	bool kept_single_type_pattern(const TemplateArgument& argument) const
	{
		TypePtr bare_arg = argument.type.get() != NULL
			? pa11::strip_cv(argument.type) : TypePtr();
		return bare_arg.get() != NULL &&
		       (bare_arg->kind == pa11::TypeKind::Function ||
		        bare_arg->kind == pa11::TypeKind::MemberPointer);
	}

	void append_parameter(size_t parameter_index)
	{
		const TemplateParameterInfo& parameter =
			declaration->parameters[parameter_index];
		TypePtr parameter_type = substituted_parameter_type(parameter);
		if (parameter.is_pack)
		{
			parser.append_completed_template_pack_argument(
				declaration,
				parameter_index,
				parameter_type,
				explicit_expanded,
				explicit_index,
				out);
			return;
		}
		if (explicit_index < explicit_expanded.size())
		{
			append_explicit_argument(parameter, parameter_type);
			return;
		}
		append_default_argument(parameter_index, parameter, parameter_type);
	}

	TypePtr substituted_parameter_type(const TemplateParameterInfo& parameter)
	{
		TypePtr parameter_type = parameter.type;
		if (parameter.kind != TemplateParameterKind::NonType ||
		    parameter_type.get() == NULL)
			return parameter_type;
		map<string, TypePtr> subst;
		map<string, TemplateArgument> value_subst;
		set<string> pack_subst;
		collect_current_substitutions(subst, value_subst, pack_subst, NULL);
		try
		{
			SubstitutionScope scope(parser,
			                        declaration,
			                        subst,
			                        value_subst,
			                        pack_subst);
			return parser.substitute_template_type(parameter_type);
		}
		catch (const runtime_error& err)
		{
			if (!can_leave_parameter_type_dependent(parameter_type, err))
				throw;
			return parameter_type;
		}
	}

	bool can_leave_parameter_type_dependent(TypePtr parameter_type,
	                                        const runtime_error& err)
	{
		if (parser.function_template_candidate_instantiation_depth_ == 0 ||
		    string(err.what()) != "dependent typename not resolved")
			return false;
		TypePtr bare_parameter_type = parameter_type.get() != NULL
			? pa11::strip_cv(parameter_type) : TypePtr();
		if (bare_parameter_type.get() == NULL ||
		    !bare_parameter_type->is_dependent_typename ||
		    bare_parameter_type->template_arguments.empty())
			return true;
		vector<TemplateArgument> candidate_args;
		try
		{
			for (size_t ai = 0;
			     ai < bare_parameter_type->template_arguments.size();
			     ++ai)
			{
				TemplateArgument candidate_arg =
					parser.template_argument_from_instance_argument(
						bare_parameter_type->template_arguments[ai]);
				candidate_args.push_back(
					parser.substitute_template_argument(candidate_arg));
			}
		}
		catch (const runtime_error&)
		{
			return true;
		}
		return !dependent_typename_disabled_enable_if_argument(
			bare_parameter_type,
			candidate_args);
	}

	void collect_current_substitutions(
		map<string, TypePtr>& subst,
		map<string, TemplateArgument>& value_subst,
		set<string>& pack_subst,
		bool* concrete_completion) const
	{
		for (size_t i = 0;
		     i < out.size() && i < declaration->parameters.size();
		     ++i)
		{
			const TemplateParameterInfo& parameter =
				declaration->parameters[i];
			if (parameter.name.empty())
				continue;
			if (parameter.kind == TemplateParameterKind::Type)
			{
				if (parameter.is_pack)
				{
					subst[parameter.name] =
						pa11::make_template_parameter_type(parameter.name);
					value_subst[parameter.name] = out[i];
					pack_subst.insert(parameter.name);
				}
				else
					subst[parameter.name] = out[i].type;
			}
			else
				value_subst[parameter.name] = out[i];
		}
		if (concrete_completion == NULL)
			return;
		for (map<string, TypePtr>::const_iterator it = subst.begin();
		     it != subst.end();
		     ++it)
			if (parser.type_is_template_dependent(it->second))
				*concrete_completion = false;
		for (map<string, TemplateArgument>::const_iterator it =
			     value_subst.begin();
		     it != value_subst.end();
		     ++it)
			if (template_argument_has_template_parameter(
				    it->second,
				    parser.record_template_arguments_))
				*concrete_completion = false;
	}

	void append_explicit_argument(const TemplateParameterInfo& parameter,
	                              TypePtr parameter_type)
	{
		TemplateArgument arg = explicit_expanded[explicit_index++];
		TemplateArgument original_arg = arg;
		if (parameter.kind == TemplateParameterKind::NonType &&
		    arg.kind == TemplateArgumentKind::Value &&
		    arg.dependent &&
		    parameter_type.get() != NULL)
			arg.type = parameter_type;
		if (parameter.kind == TemplateParameterKind::Type &&
		    arg.kind == TemplateArgumentKind::Value &&
		    arg.type.get() != NULL &&
		    (arg.dependent ||
		     pa11::strip_cv(arg.type)->kind != pa11::TypeKind::Fundamental))
		{
			bool pack_expansion = arg.pack_expansion;
			arg = TemplateArgument::type_arg(arg.type);
			arg.pack_expansion = pack_expansion;
		}
		substitute_explicit_argument(arg);
		if (parameter.kind == TemplateParameterKind::TemplateTemplate &&
		    arg.kind == TemplateArgumentKind::Type)
		{
			TemplateDeclaration* recovered =
				parser.class_template_declaration_for_match(arg.type);
			if (recovered != NULL)
				arg = TemplateArgument::template_arg(recovered);
		}
		if (!template_argument_kind_matches_parameter(arg, parameter))
			arg = dependent_value_argument_from_type(parameter,
			                                     parameter_type,
			                                     arg,
			                                     original_arg);
		arg = parser.convert_completed_non_type_template_argument(
			arg,
			parameter_type);
		out.push_back(arg);
	}

	void substitute_explicit_argument(TemplateArgument& arg)
	{
		map<string, TypePtr> subst;
		map<string, TemplateArgument> value_subst;
		set<string> pack_subst;
		collect_current_substitutions(subst, value_subst, pack_subst, NULL);
		SubstitutionScope scope(parser,
		                        declaration,
		                        subst,
		                        value_subst,
		                        pack_subst);
		if (!explicit_value_name_collides(arg))
			arg = parser.substitute_template_argument(arg);
	}

	bool explicit_value_name_collides(const TemplateArgument& arg) const
	{
		if (arg.kind != TemplateArgumentKind::Value ||
		    !arg.dependent ||
		    arg.value_name.empty())
			return false;
		for (size_t pi = 0; pi < declaration->parameters.size(); ++pi)
			if (declaration->parameters[pi].name == arg.value_name)
				return true;
		return false;
	}

	TemplateArgument dependent_value_argument_from_type(
		const TemplateParameterInfo& parameter,
		TypePtr parameter_type,
		const TemplateArgument& arg,
		const TemplateArgument& original_arg)
	{
		TypePtr dependent_type = arg.type;
		TypePtr dependent_bare = dependent_type.get() != NULL
			? pa11::strip_cv(dependent_type) : TypePtr();
		if ((dependent_bare.get() == NULL ||
		     !dependent_bare->is_dependent_typename ||
		     !dependent_bare->dependent_typename_qualified) &&
		    original_arg.kind == TemplateArgumentKind::Type)
		{
			TypePtr original_bare = original_arg.type.get() != NULL
				? pa11::strip_cv(original_arg.type) : TypePtr();
			if (original_bare.get() != NULL &&
			    original_bare->is_dependent_typename &&
			    original_bare->dependent_typename_qualified)
			{
				dependent_type = original_arg.type;
				dependent_bare = original_bare;
			}
		}
		if (parameter.kind == TemplateParameterKind::NonType &&
		    arg.kind == TemplateArgumentKind::Type &&
		    dependent_bare.get() != NULL &&
		    dependent_bare->kind == pa11::TypeKind::Function &&
		    dependent_bare->parameters.size() == 1 &&
		    parameter_type.get() != NULL &&
		    pa11::same_type(dependent_bare->base, parameter_type))
			dependent_type = dependent_bare->parameters[0];
		dependent_bare = dependent_type.get() != NULL
			? pa11::strip_cv(dependent_type) : TypePtr();
		if (parameter.kind != TemplateParameterKind::NonType ||
		    arg.kind != TemplateArgumentKind::Type ||
		    dependent_type.get() == NULL ||
		    !dependent_bare->is_dependent_typename ||
		    !dependent_bare->dependent_typename_qualified)
			throw runtime_error("template argument kind mismatch");
		TemplateArgument value_arg =
			TemplateArgument::dependent_value_arg(parameter_type);
		value_arg.value_name = dependent_type->name;
		attach_dependent_value_owner(dependent_bare, value_arg);
		return parser.substitute_template_argument(value_arg);
	}

	void attach_dependent_value_owner(TypePtr dependent_bare,
	                                  TemplateArgument& value_arg)
	{
		size_t member_pos = dependent_bare->name.rfind("::");
		string member_name = member_pos != string::npos
			? dependent_bare->name.substr(member_pos + 2) : string();
		string owner_name = dependent_bare->template_primary_name;
		if (owner_name.empty())
		{
			string root = member_pos != string::npos
				? dependent_bare->name.substr(0, member_pos)
				: dependent_bare->name;
			size_t template_pos = root.find('<');
			owner_name = root.substr(0, template_pos);
		}
		if (owner_name.empty() || member_name.empty())
			return;
		value_arg.value_owner_template_name = owner_name;
		value_arg.value_member_name = member_name;
		for (size_t ai = 0;
		     ai < dependent_bare->template_arguments.size();
		     ++ai)
		{
			TemplateArgument owner_arg =
				parser.template_argument_from_instance_argument(
					dependent_bare->template_arguments[ai]);
			owner_arg = parser.substitute_template_argument(owner_arg);
			value_arg.value_owner_template_arguments.push_back(
				completed_instance_argument(owner_arg));
		}
	}

	void append_default_argument(size_t parameter_index,
	                             const TemplateParameterInfo& parameter,
	                             TypePtr parameter_type)
	{
		if (!parameter.has_default)
			throw runtime_error("missing template argument");
		TemplateArgument arg;
		try
		{
			arg = parser.parse_default_template_argument(declaration,
			                                            parameter_index,
			                                            out);
			if (parameter.kind == TemplateParameterKind::Type)
				arg = parser.substitute_template_argument(arg);
		}
		catch (const runtime_error& err)
		{
			if (!use_dependent_default(parameter, err))
				throw;
			string default_name = parameter.name.empty()
				? declaration->name + "__default" +
				  to_string(parameter_index)
				: parameter.name;
			arg = TemplateArgument::type_arg(
				pa11::make_dependent_typename_type(default_name,
				                                   false,
				                                   false,
				                                   false));
		}
		arg = parser.convert_completed_non_type_template_argument(
			arg,
			parameter_type);
		out.push_back(arg);
	}

	bool use_dependent_default(const TemplateParameterInfo& parameter,
	                           const runtime_error& err) const
	{
		if (parser.function_template_candidate_instantiation_depth_ == 0 ||
		    parameter.kind != TemplateParameterKind::Type ||
		    string(err.what()) != "dependent typename not resolved")
			return false;
		for (size_t ai = 0; ai < out.size(); ++ai)
			if (template_argument_has_template_parameter(
				    out[ai],
				    parser.record_template_arguments_))
				return true;
		return false;
	}

	void finalize_non_type_arguments()
	{
		map<string, TypePtr> subst;
		map<string, TemplateArgument> value_subst;
		set<string> pack_subst;
		bool concrete_completion = true;
		collect_current_substitutions(subst,
		                              value_subst,
		                              pack_subst,
		                              &concrete_completion);
		SubstitutionScope scope(parser,
		                        declaration,
		                        subst,
		                        value_subst,
		                        pack_subst);
		for (size_t i = 0; i < out.size() && i < declaration->parameters.size();
		     ++i)
		{
			if (declaration->parameters[i].kind !=
				    TemplateParameterKind::NonType ||
			    declaration->parameters[i].type.get() == NULL)
				continue;
			TypePtr parameter_type =
				final_non_type_parameter_type(i, concrete_completion);
			out[i] = parser.convert_completed_non_type_template_argument(
				out[i],
				parameter_type);
		}
	}

	TypePtr final_non_type_parameter_type(size_t parameter_index,
	                                      bool& concrete_completion)
	{
		TypePtr parameter_type = declaration->parameters[parameter_index].type;
		try
		{
			parameter_type = parser.substitute_template_type(parameter_type);
		}
			catch (const runtime_error& err)
			{
				if (parser.function_template_candidate_instantiation_depth_ != 0 &&
				    string(err.what()) == "dependent typename not resolved" &&
				    can_leave_parameter_type_dependent(parameter_type, err))
				{
					concrete_completion = false;
					return parameter_type;
				}
			throw;
		}
		resolve_dependent_parameter_type(parameter_type,
		                                 concrete_completion);
		return parameter_type;
	}

	void resolve_dependent_parameter_type(TypePtr& parameter_type,
	                                      bool& concrete_completion)
	{
		TypePtr parameter_bare = parameter_type.get() != NULL
			? pa11::strip_cv(parameter_type) : TypePtr();
		if (parameter_bare.get() == NULL ||
		    !parameter_bare->is_dependent_typename)
			return;
		TypePtr resolved =
			parser.resolve_dependent_typename_type(parameter_bare);
		if (resolved.get() != NULL && resolved != parameter_bare)
		{
			parameter_type = parser.substitute_template_type(resolved);
			return;
		}
		if (parameter_bare->dependent_typename_qualified &&
		    !parameter_bare->template_primary_name.empty() &&
		    !parameter_bare->template_arguments.empty())
		{
			resolve_qualified_parameter_type(parameter_type,
			                                 parameter_bare,
			                                 concrete_completion);
			return;
		}
		mark_unresolved_dependent_parameter(concrete_completion);
	}

	void mark_unresolved_dependent_parameter(bool& concrete_completion)
	{
		if (!concrete_completion)
			return;
		if (parser.function_template_candidate_instantiation_depth_ != 0)
			concrete_completion = false;
		else
			throw runtime_error("dependent typename not resolved");
	}

	void resolve_qualified_parameter_type(TypePtr& parameter_type,
	                                      TypePtr parameter_bare,
	                                      bool& concrete_completion)
	{
		string member_name = parameter_bare->name;
		size_t member_pos = member_name.rfind("::");
		if (member_pos != string::npos)
			member_name = member_name.substr(member_pos + 2);
		vector<TemplateArgument> owner_args;
		bool owner_args_dependent = false;
		collect_owner_arguments(parameter_bare,
		                        owner_args,
		                        owner_args_dependent);
		if (!owner_args_dependent)
			resolve_owner_member_type(parameter_bare,
			                          member_name,
			                          owner_args,
			                          parameter_type);
		TypePtr current_bare = parameter_type.get() != NULL
			? pa11::strip_cv(parameter_type) : TypePtr();
		if (concrete_completion &&
		    !owner_args_dependent &&
		    current_bare.get() != NULL &&
		    current_bare->is_dependent_typename)
			mark_unresolved_dependent_parameter(concrete_completion);
	}

	void collect_owner_arguments(TypePtr parameter_bare,
	                             vector<TemplateArgument>& owner_args,
	                             bool& owner_args_dependent)
	{
		for (size_t ai = 0;
		     ai < parameter_bare->template_arguments.size();
		     ++ai)
		{
			TemplateArgument owner_arg =
				parser.template_argument_from_instance_argument(
					parameter_bare->template_arguments[ai]);
			resolve_owner_value_argument(owner_arg,
			                             owner_args_dependent);
			try
			{
				owner_arg = parser.substitute_template_argument(owner_arg);
			}
			catch (const runtime_error&)
			{
				if (owner_arg.kind == TemplateArgumentKind::Value &&
				    owner_arg.dependent &&
				    owner_arg.value_expr_end > owner_arg.value_expr_begin &&
				    parser.function_template_candidate_instantiation_depth_ != 0)
					owner_args_dependent = true;
				else
					throw;
			}
			if (template_argument_has_template_parameter(
				    owner_arg,
				    parser.record_template_arguments_))
				owner_args_dependent = true;
			if (owner_arg.kind == TemplateArgumentKind::Value &&
			    owner_arg.dependent &&
			    owner_arg.value_expr_end > owner_arg.value_expr_begin &&
			    parser.function_template_candidate_instantiation_depth_ != 0)
				owner_args_dependent = true;
			owner_args.push_back(owner_arg);
		}
	}

	void resolve_owner_value_argument(TemplateArgument& owner_arg,
	                                  bool& owner_args_dependent)
	{
		if (owner_arg.kind != TemplateArgumentKind::Value ||
		    !owner_arg.dependent ||
		    owner_arg.value_owner_template_name.empty())
			return;
		TemplateArgument resolved_value;
		try
		{
			if (parser.resolve_dependent_value_member_argument(
				    owner_arg,
				    resolved_value))
				owner_arg = resolved_value;
		}
		catch (const runtime_error&)
		{
			if (owner_arg.value_expr_end > owner_arg.value_expr_begin &&
			    parser.function_template_candidate_instantiation_depth_ != 0)
				owner_args_dependent = true;
			else
				throw;
		}
	}

	void resolve_owner_member_type(TypePtr parameter_bare,
	                               const string& member_name,
	                               const vector<TemplateArgument>& owner_args,
	                               TypePtr& parameter_type)
	{
		string lookup_name = parameter_bare->template_primary_name;
		Scope* qualifier = NULL;
		parser.resolve_template_name_spelling(
			parameter_bare->template_primary_name,
			qualifier,
			lookup_name);
		TemplateDeclaration* klass =
			find_owner_class_template(qualifier,
			                          lookup_name,
			                          parameter_bare);
		if (klass == NULL)
			return;
		TypePtr owner = parser.instantiate_class_template(klass, owner_args);
		TypePtr owner_bare = owner.get() != NULL
			? pa11::strip_cv(owner) : TypePtr();
		if (owner_bare.get() == NULL ||
		    owner_bare->kind != pa11::TypeKind::Record ||
		    owner_bare->scope == NULL)
			return;
		parser.complete_template_record(owner_bare);
		vector<Binding*> found =
			parser.lookup_qualified_set(owner_bare->scope,
			                            member_name,
			                            pa11::LOOKUP_TYPE);
		if (!found.empty() && found[0]->type.get() != NULL)
			parameter_type =
				parser.substitute_template_type_in_scope(found[0]->type,
				                                         owner_bare->scope);
	}

	TemplateDeclaration* find_owner_class_template(
		Scope* qualifier,
		const string& lookup_name,
		TypePtr parameter_bare)
	{
		TemplateDeclaration* klass =
			parser.find_class_template(qualifier, lookup_name);
		if (klass == NULL && qualifier != NULL)
			klass = parser.find_class_template(NULL, lookup_name);
		if (klass == NULL)
			klass = parser.find_class_template(
				NULL,
				parameter_bare->template_primary_name);
		if (klass != NULL)
			return klass;
		for (map<Scope*, map<string, TemplateDeclaration*> >::const_iterator
			     sit = parser.class_templates_.begin();
		     sit != parser.class_templates_.end();
		     ++sit)
		{
			map<string, TemplateDeclaration*>::const_iterator found =
				sit->second.find(lookup_name);
			if (found == sit->second.end())
				found = sit->second.find(
					parameter_bare->template_primary_name);
			if (found != sit->second.end())
				return found->second;
		}
		return NULL;
	}
};

TemplateArgument Parser::convert_completed_non_type_template_argument(
	TemplateArgument argument,
	TypePtr parameter_type)
{
	if (argument.kind == TemplateArgumentKind::Value &&
	    argument.value_binding != NULL &&
	    argument.value_binding->kind == BindingKind::Function &&
	    parameter_type.get() != NULL)
	{
		TypePtr parameter_bare = pa11::strip_cv(parameter_type);
		if (parameter_bare->kind == pa11::TypeKind::MemberPointer)
		{
			Binding* binding = argument.value_binding;
			Expr inner;
			inner.valid = true;
			inner.binding = binding;
			inner.type = binding->type;
			inner.category = ValueCategory::LValue;
			if (binding->owner != NULL)
			{
				vector<Binding*> overloads =
					lookup_qualified_set(binding->owner,
					                     binding->name,
					                     pa11::LOOKUP_FUNCTION);
				for (size_t i = 0; i < overloads.size(); ++i)
					if (overloads[i]->kind == BindingKind::Function)
						inner.overloads.push_back(overloads[i]);
			}
			if (inner.overloads.empty())
				inner.overloads.push_back(binding);
			inner.node = Node("id-expression lvalue " +
			                  pa11::describe_type(binding->type) + " " +
			                  qualified_decl_name(binding));
			inner.node.binding = binding;
			annotate_expr_node(inner);
			try
			{
				Expr address = make_address_expr("&", inner);
				Conversion conv = convert_to(address, parameter_type);
				if (conv.viable &&
				    conv.expr.node.has_op &&
				    conv.expr.node.op == OP_AMP &&
				    !conv.expr.node.children.empty() &&
				    conv.expr.node.children[0].binding != NULL)
				{
					Binding* member = conv.expr.node.children[0].binding;
					if (member->aliased_binding != NULL &&
					    member->target_scope != NULL)
						member = member->aliased_binding;
					TemplateArgument resolved =
						TemplateArgument::value_arg(
							expression_object_type(conv.expr.type),
							reinterpret_cast<uint64_t>(member));
					resolved.value_binding = member;
					resolved.value_name = argument.value_name;
					return convert_non_type_template_argument(resolved,
					                                          parameter_type);
				}
			}
			catch (const runtime_error&)
			{
			}
		}
	}
	return convert_non_type_template_argument(argument, parameter_type);
}

vector<TemplateArgument> Parser::complete_template_arguments(
	TemplateDeclaration* declaration,
	const vector<TemplateArgument>& explicit_arguments)
{
	TemplateArgumentCompleter completer(*this,
	                                    declaration,
	                                    explicit_arguments);
	return completer.run();
}

}  // namespace internal
}  // namespace pa12
