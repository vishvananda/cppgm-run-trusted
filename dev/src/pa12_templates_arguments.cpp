#include "pa12_internal.h"
#include "pa12_templates_instance_support.h"

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
			? pa11::TemplateInstanceArgument::dependent_value_arg(
				argument.type)
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
	if (argument.kind != TemplateArgumentKind::Template ||
	    argument.template_declaration == NULL)
		return false;
	const vector<TemplateParameterInfo>& params =
		argument.template_declaration->parameters;
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
		TypePtr argument_bare = argument.type.get() != NULL
			? pa11::strip_cv(argument.type) : TypePtr();
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

void collect_template_pack_names_from_instance_argument(
	const pa11::TemplateInstanceArgument& argument,
	set<string>& names,
	const map<const void*, vector<TemplateArgument> >* record_arguments = NULL);
void collect_template_pack_names_from_argument(const TemplateArgument& argument,
                                               set<string>& names,
                                               const map<const void*, vector<TemplateArgument> >* record_arguments = NULL);

bool type_is_pack_element_builtin(TypePtr type)
{
	if (type.get() == NULL)
		return false;
	type = pa11::strip_cv(type);
	return type->template_primary_name == "__type_pack_element" ||
	       type->name == "__type_pack_element";
}

bool type_pack_element_arguments(
	TypePtr type,
	const map<const void*, vector<TemplateArgument> >& record_arguments,
	vector<TemplateArgument>& arguments)
{
	if (type.get() == NULL)
		return false;
	TypePtr bare = pa11::strip_cv(type);
	if (!type_is_pack_element_builtin(bare))
		return false;
	const void* keys[2] = {
		type.get(),
		bare.get()
	};
	for (size_t k = 0; k < 2; ++k)
	{
		map<const void*, vector<TemplateArgument> >::const_iterator found =
			record_arguments.find(keys[k]);
		if (found != record_arguments.end())
		{
			arguments = found->second;
			return true;
		}
	}
	if (bare->template_arguments.empty())
		return false;
	for (size_t i = 0; i < bare->template_arguments.size(); ++i)
		arguments.push_back(raw_template_argument_from_instance_argument(
			bare->template_arguments[i]));
	return true;
}

void collect_template_pack_names_from_type(
	TypePtr type,
	set<string>& names,
	const map<const void*, vector<TemplateArgument> >* record_arguments = NULL)
{
	if (type.get() == NULL)
		return;
	TypePtr original = type;
	type = pa11::strip_cv(type);
	if (record_arguments != NULL &&
	    (type->template_primary_name == "__type_pack_element" ||
	     type->name == "__type_pack_element"))
	{
		const void* keys[2] = {
			original.get(),
			type.get()
		};
		for (size_t k = 0; k < 2; ++k)
		{
			if (keys[k] == NULL)
				continue;
			map<const void*, vector<TemplateArgument> >::const_iterator
				found = record_arguments->find(keys[k]);
			if (found == record_arguments->end())
				continue;
			size_t limit = found->second.empty() ? 0 : 1;
			for (size_t i = 0; i < limit; ++i)
				collect_template_pack_names_from_argument(
					found->second[i],
					names,
					record_arguments);
		}
	}
	if (type->template_primary_name == "__type_pack_element" ||
	    type->name == "__type_pack_element")
	{
		if (!type->template_arguments.empty())
			collect_template_pack_names_from_instance_argument(
				type->template_arguments[0],
				names,
				record_arguments);
		return;
	}
	if (type->kind == pa11::TypeKind::TemplateParameter)
	{
		if (type->is_dependent_typename)
		{
			for (size_t i = 0; i < type->template_arguments.size(); ++i)
				collect_template_pack_names_from_instance_argument(
					type->template_arguments[i],
					names,
					record_arguments);
			for (size_t i = 0;
			     i < type->dependent_typename_template_argument_lists.size();
			     ++i)
				for (size_t j = 0;
				     j < type->dependent_typename_template_argument_lists[i].size();
				     ++j)
					collect_template_pack_names_from_instance_argument(
						type->dependent_typename_template_argument_lists[i][j],
						names,
						record_arguments);
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
		collect_template_pack_names_from_type(type->base,
		                                      names,
		                                      record_arguments);
		return;
	}
	if (type->kind == pa11::TypeKind::Function)
	{
		collect_template_pack_names_from_type(type->base,
		                                      names,
		                                      record_arguments);
		for (size_t i = 0; i < type->parameters.size(); ++i)
			collect_template_pack_names_from_type(type->parameters[i],
			                                      names,
			                                      record_arguments);
		return;
	}
	if (type->kind == pa11::TypeKind::MemberPointer)
	{
		collect_template_pack_names_from_type(type->member_class,
		                                      names,
		                                      record_arguments);
		collect_template_pack_names_from_type(type->base,
		                                      names,
		                                      record_arguments);
		return;
	}
	if (type->is_template_specialization)
		for (size_t i = 0; i < type->template_arguments.size(); ++i)
			collect_template_pack_names_from_instance_argument(
				type->template_arguments[i],
				names,
				record_arguments);
}

void collect_template_pack_names_from_instance_argument(
	const pa11::TemplateInstanceArgument& argument,
	set<string>& names,
	const map<const void*, vector<TemplateArgument> >* record_arguments)
{
	if (argument.kind == pa11::TemplateInstanceArgumentKind::Type)
	{
		collect_template_pack_names_from_type(argument.type,
		                                      names,
		                                      record_arguments);
		return;
	}
	if (argument.kind == pa11::TemplateInstanceArgumentKind::Value)
	{
		for (size_t i = 0;
		     i < argument.value_owner_template_arguments.size();
		     ++i)
			collect_template_pack_names_from_instance_argument(
				argument.value_owner_template_arguments[i],
				names,
				record_arguments);
		if (!argument.value_owner_template_name.empty())
			names.insert(argument.value_owner_template_name);
		if (argument.dependent && !argument.value_name.empty())
			names.insert(argument.value_name);
		collect_template_pack_names_from_type(argument.type,
		                                      names,
		                                      record_arguments);
		return;
	}
	if (argument.kind == pa11::TemplateInstanceArgumentKind::Template)
	{
		if (argument.dependent && !argument.template_name.empty())
			names.insert(argument.template_name);
		return;
	}
		if (argument.kind == pa11::TemplateInstanceArgumentKind::Pack)
		{
			for (size_t i = 0; i < argument.pack.size(); ++i)
				collect_template_pack_names_from_instance_argument(
					argument.pack[i],
					names,
					record_arguments);
			return;
	}
}

void collect_template_pack_names_from_argument(const TemplateArgument& argument,
                                               set<string>& names,
                                               const map<const void*, vector<TemplateArgument> >* record_arguments)
{
	if (argument.pack_expansion && argument.kind != TemplateArgumentKind::Pack)
		return;
	if (argument.kind == TemplateArgumentKind::Type)
	{
		collect_template_pack_names_from_type(argument.type,
		                                      names,
		                                      record_arguments);
		return;
	}
	if (argument.kind == TemplateArgumentKind::Value)
	{
		for (size_t i = 0;
		     i < argument.value_owner_template_arguments.size();
		     ++i)
			collect_template_pack_names_from_instance_argument(
				argument.value_owner_template_arguments[i],
				names,
				record_arguments);
		if (!argument.value_owner_template_name.empty())
			names.insert(argument.value_owner_template_name);
		if (argument.dependent && !argument.value_name.empty())
			names.insert(argument.value_name);
		collect_template_pack_names_from_type(argument.type,
		                                      names,
		                                      record_arguments);
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
		{
			names.insert(argument.value_name);
			return;
		}
		for (size_t i = 0; i < argument.pack.size(); ++i)
			collect_template_pack_names_from_argument(argument.pack[i],
			                                          names,
			                                          record_arguments);
	}
}

	bool has_selected_pack_name(const set<string>& haystack,
	                            const set<string>& selected)
	{
		for (set<string>::const_iterator it = haystack.begin();
		     it != haystack.end();
		     ++it)
			if (selected.count(*it) != 0)
				return true;
		return false;
	}

	TypePtr select_template_instance_pack_element(TypePtr type,
	                                              size_t index,
	                                              size_t pack_size,
	                                              const set<string>& names);

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
		return root_name == "enable_if" || root_name == "__enable_if_t";
	}

	pa11::TemplateInstanceArgument select_template_instance_pack_argument_element(
		const pa11::TemplateInstanceArgument& argument,
		size_t index,
		size_t pack_size,
		const set<string>& names)
	{
		set<string> argument_names;
		collect_template_pack_names_from_instance_argument(argument,
		                                                   argument_names);
		if (!has_selected_pack_name(argument_names, names))
			return argument;
		if (argument.kind == pa11::TemplateInstanceArgumentKind::Pack)
		{
			if (argument.pack.size() != pack_size)
			{
				if (argument.pack.size() == 1)
				{
					pa11::TemplateInstanceArgument out = argument;
					out.pack[0] =
						select_template_instance_pack_argument_element(
							argument.pack[0],
							index,
							pack_size,
							names);
					return out;
				}
				throw runtime_error("template argument pack length mismatch");
			}
			return argument.pack[index];
	}
		pa11::TemplateInstanceArgument out = argument;
		if (out.type.get() != NULL)
			out.type = select_template_instance_pack_element(out.type,
			                                                 index,
			                                                 pack_size,
			                                                 names);
		for (size_t i = 0; i < out.value_owner_template_arguments.size(); ++i)
			out.value_owner_template_arguments[i] =
				select_template_instance_pack_argument_element(
					out.value_owner_template_arguments[i],
					index,
					pack_size,
					names);
		for (size_t i = 0; i < out.pack.size(); ++i)
			out.pack[i] = select_template_instance_pack_argument_element(
				out.pack[i],
				index,
				pack_size,
				names);
		return out;
	}

	TemplateArgument select_template_argument_pack_element(
		const TemplateArgument& argument,
		size_t index,
		size_t pack_size,
		const set<string>& names)
	{
		set<string> argument_names;
		collect_template_pack_names_from_argument(argument,
		                                          argument_names,
		                                          NULL);
		bool unnamed_matching_pack =
			argument.kind == TemplateArgumentKind::Pack &&
			argument.value_name.empty() &&
			argument.pack.size() == pack_size &&
			pack_size != 0;
		if (!has_selected_pack_name(argument_names, names) &&
		    !unnamed_matching_pack)
			return argument;
		if (argument.kind == TemplateArgumentKind::Pack)
		{
			if (argument.pack.size() != pack_size)
			{
				if (!argument.value_name.empty())
				{
					TemplateArgument out = argument;
					out.value_name.clear();
					return out;
				}
				throw runtime_error("template argument pack length mismatch");
			}
			return argument.pack[index];
		}
		TemplateArgument out = argument;
		if (out.type.get() != NULL)
			out.type = select_template_instance_pack_element(out.type,
			                                                 index,
			                                                 pack_size,
			                                                 names);
		for (size_t i = 0; i < out.value_owner_template_arguments.size(); ++i)
			out.value_owner_template_arguments[i] =
				select_template_instance_pack_argument_element(
					out.value_owner_template_arguments[i],
					index,
					pack_size,
					names);
		for (size_t i = 0; i < out.pack.size(); ++i)
			out.pack[i] = select_template_argument_pack_element(out.pack[i],
			                                                    index,
			                                                    pack_size,
			                                                    names);
		return out;
	}

	TypePtr select_template_instance_pack_element(TypePtr type,
	                                              size_t index,
	                                              size_t pack_size,
	                                              const set<string>& names)
	{
		if (type.get() == NULL)
			return type;
		set<string> type_names;
		collect_template_pack_names_from_type(type, type_names);
		if (!has_selected_pack_name(type_names, names))
			return type;
		TypePtr out(new pa11::Type(*type));
		if (out->base.get() != NULL)
			out->base = select_template_instance_pack_element(out->base,
			                                                  index,
			                                                  pack_size,
			                                                  names);
		if (out->member_class.get() != NULL)
			out->member_class =
				select_template_instance_pack_element(out->member_class,
				                                      index,
				                                      pack_size,
				                                      names);
		for (size_t i = 0; i < out->parameters.size(); ++i)
			out->parameters[i] =
				select_template_instance_pack_element(out->parameters[i],
				                                      index,
				                                      pack_size,
				                                      names);
		for (size_t i = 0; i < out->template_arguments.size(); ++i)
			out->template_arguments[i] =
				select_template_instance_pack_argument_element(
					out->template_arguments[i],
					index,
					pack_size,
					names);
		for (size_t i = 0;
		     i < out->dependent_typename_template_argument_lists.size();
		     ++i)
		for (size_t j = 0;
		     j < out->dependent_typename_template_argument_lists[i].size();
		     ++j)
				out->dependent_typename_template_argument_lists[i][j] =
					select_template_instance_pack_argument_element(
						out->dependent_typename_template_argument_lists[i][j],
						index,
						pack_size,
						names);
		return out;
	}

}  // namespace

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
					Binding* member =
						conv.expr.node.children[0].binding;
					if (member->aliased_binding != NULL &&
					    member->target_scope != NULL)
						member = member->aliased_binding;
					TemplateArgument resolved =
						TemplateArgument::value_arg(
							expression_object_type(conv.expr.type),
							reinterpret_cast<uint64_t>(member));
					resolved.value_binding = member;
					resolved.value_name = argument.value_name;
					return convert_non_type_template_argument(
						resolved,
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

vector<TemplateArgument> Parser::expand_template_argument_pack(
	const TemplateArgument& argument) const
{
	if (!argument.pack_expansion)
	{
		vector<TemplateArgument> single;
		single.push_back(argument);
		return single;
	}
	if (argument.kind == TemplateArgumentKind::Pack)
		return argument.pack;
	string pack_name;
	if (argument.kind == TemplateArgumentKind::Type)
	{
		set<string> names;
		collect_template_pack_names_from_type(argument.type,
		                                      names,
		                                      &record_template_arguments_);
		if (names.empty() && type_is_pack_element_builtin(argument.type))
		{
			vector<TemplateArgument> pack_element_arguments;
			if (type_pack_element_arguments(argument.type,
			                                record_template_arguments_,
			                                pack_element_arguments) &&
			    !pack_element_arguments.empty())
			{
				TemplateArgument index =
					substitute_template_argument(
						pack_element_arguments[0]);
				if (index.kind == TemplateArgumentKind::Pack)
				{
					vector<TemplateArgument> out;
					for (size_t i = 0; i < index.pack.size(); ++i)
					{
						vector<TemplateArgument> selected_arguments =
							pack_element_arguments;
						selected_arguments[0] =
							substitute_template_argument(
								index.pack[i]);
						TypePtr selected;
						if (!const_cast<Parser*>(this)->
							    try_resolve_type_pack_element(
								    selected_arguments,
								    selected) ||
						    selected.get() == NULL)
							throw runtime_error(
								"invalid __type_pack_element");
						TemplateArgument element =
							TemplateArgument::type_arg(selected);
						out.push_back(element);
					}
					return out;
				}
			}
		}
		if (names.empty() &&
		    !template_type_has_template_parameter_name(argument.type,
		                                               pack_name))
			goto no_type_pack_expansion;
		if (names.empty())
			names.insert(pack_name);
		vector<pair<string, TemplateArgument> > packs;
		bool missing_active_pack = false;
		for (set<string>::const_iterator it = names.begin();
		     it != names.end();
		     ++it)
		{
			TemplateArgument subst;
			bool found_subst = find_template_value_substitution(*it, subst);
			if (found_subst && subst.kind == TemplateArgumentKind::Pack)
				packs.push_back(make_pair(*it, subst));
			else if (active_type_parameter_pack(*it))
				missing_active_pack = true;
		}
		if (missing_active_pack)
		{
			vector<TemplateArgument> unresolved;
			unresolved.push_back(argument);
			return unresolved;
		}
		if (packs.empty())
		{
			vector<TemplateArgument> unresolved;
			unresolved.push_back(argument);
			return unresolved;
		}
			size_t pack_size = packs[0].second.pack.size();
			for (size_t i = 1; i < packs.size(); ++i)
				if (packs[i].second.pack.size() != pack_size)
					throw runtime_error("template argument pack length mismatch");
		TypePtr exact_pack_type = argument.type;
		if (packs.size() == 1 &&
		    exact_pack_type.get() != NULL &&
		    exact_pack_type->kind == pa11::TypeKind::TemplateParameter &&
		    !exact_pack_type->is_dependent_typename &&
		    exact_pack_type->name == packs[0].first)
		{
			vector<TemplateArgument> out;
			for (size_t i = 0; i < pack_size; ++i)
			{
				TemplateArgument element = packs[0].second.pack[i];
				element.pack_expansion = false;
				out.push_back(element);
			}
			return out;
		}
		vector<TemplateArgument> out;
		for (size_t i = 0; i < pack_size; ++i)
		{
			Parser* self = const_cast<Parser*>(this);
			vector<map<string, TypePtr> > save_type_subst =
				self->template_type_substitutions_;
			vector<map<string, TemplateArgument> > save_value_subst =
				self->template_value_substitutions_;
			map<string, TypePtr> type_subst;
			map<string, TemplateArgument> value_subst;
			for (size_t p = 0; p < packs.size(); ++p)
			{
				const TemplateArgument& elem = packs[p].second.pack[i];
				if (elem.kind == TemplateArgumentKind::Type)
					type_subst[packs[p].first] = elem.type;
				else if (elem.kind == TemplateArgumentKind::Value ||
				         elem.kind == TemplateArgumentKind::Template)
					value_subst[packs[p].first] = elem;
				else
					throw runtime_error("template argument pack kind mismatch");
			}
			self->template_type_substitutions_.push_back(type_subst);
			self->template_value_substitutions_.push_back(value_subst);
			TypePtr expanded;
			const void* selected_record_key = NULL;
			bool restore_selected_record = false;
			bool erase_selected_record = false;
			vector<TemplateArgument> saved_selected_record;
			bool restore_selected_declaration = false;
			bool erase_selected_declaration = false;
			TemplateDeclaration* saved_selected_declaration = NULL;
				try
				{
					TypePtr selected_pattern =
						select_template_instance_pack_element(argument.type,
						                                      i,
						                                      pack_size,
						                                      names);
					TypePtr selected_bare =
						selected_pattern.get() != NULL
						? pa11::strip_cv(selected_pattern) : TypePtr();
					map<const void*, vector<TemplateArgument> >::const_iterator
						stored_record_args =
							record_template_arguments_.find(argument.type.get());
					if (stored_record_args == record_template_arguments_.end() &&
					    selected_pattern.get() != NULL)
						stored_record_args =
							record_template_arguments_.find(
								selected_pattern.get());
					if (stored_record_args != record_template_arguments_.end() &&
					    selected_pattern.get() != NULL)
					{
						selected_record_key = selected_pattern.get();
						map<const void*, TemplateDeclaration*>::const_iterator
							stored_record_decl =
								record_template_declarations_.find(
									argument.type.get());
						if (stored_record_decl ==
							    record_template_declarations_.end())
							stored_record_decl =
								record_template_declarations_.find(
									selected_pattern.get());
						map<const void*, vector<TemplateArgument> >::const_iterator
							previous_record =
								self->record_template_arguments_.find(
									selected_record_key);
						if (previous_record !=
						    self->record_template_arguments_.end())
						{
							restore_selected_record = true;
							saved_selected_record = previous_record->second;
						}
						else
							erase_selected_record = true;
						vector<TemplateArgument> selected_record_args;
						for (size_t rai = 0;
						     rai < stored_record_args->second.size();
						     ++rai)
						{
							TemplateArgument selected_record_arg =
								select_template_argument_pack_element(
									stored_record_args->second[rai],
									i,
									pack_size,
									names);
							for (size_t p = 0; p < packs.size(); ++p)
								if (!selected_record_arg.value_name.empty() &&
								    selected_record_arg.value_name ==
									    packs[p].first)
									selected_record_arg =
										packs[p].second.pack[i];
							if (selected_record_arg.kind ==
							    TemplateArgumentKind::Type)
							{
								string selected_pack_name;
								if (template_type_has_template_parameter_name(
									    selected_record_arg.type,
									    selected_pack_name))
									for (size_t p = 0; p < packs.size(); ++p)
										if (selected_pack_name ==
										    packs[p].first)
											selected_record_arg =
												packs[p].second.pack[i];
							}
							selected_record_args.push_back(selected_record_arg);
						}
						self->record_template_arguments_[selected_record_key] =
							selected_record_args;
						if (stored_record_decl !=
						    record_template_declarations_.end())
						{
							map<const void*, TemplateDeclaration*>::const_iterator
								previous_decl =
									self->record_template_declarations_.find(
										selected_record_key);
							if (previous_decl !=
							    self->record_template_declarations_.end())
							{
								restore_selected_declaration = true;
								saved_selected_declaration =
									previous_decl->second;
							}
							else
								erase_selected_declaration = true;
							self->record_template_declarations_[selected_record_key] =
								stored_record_decl->second;
							if (stored_record_decl->second->kind ==
							    TemplateDeclarationKind::Alias)
								expanded =
									self->instantiate_alias_template(
										stored_record_decl->second,
										selected_record_args);
							else if (stored_record_decl->second->kind ==
							         TemplateDeclarationKind::Class)
								expanded =
									self->instantiate_class_template(
										stored_record_decl->second,
										selected_record_args);
						}
					}
					if (expanded.get() == NULL &&
					    selected_bare.get() != NULL &&
					    selected_bare->kind == pa11::TypeKind::Record &&
					    selected_bare->is_template_specialization &&
					    !selected_bare->template_primary_name.empty() &&
					    !selected_bare->template_arguments.empty() &&
					    record_template_declarations_.find(
						    selected_bare.get()) ==
						    record_template_declarations_.end())
					{
						vector<TemplateArgument> selected_args;
						for (size_t ai = 0;
						     ai < selected_bare->template_arguments.size();
						     ++ai)
						{
							TemplateArgument selected_arg =
								template_argument_from_instance_argument(
									selected_bare->template_arguments[ai]);
							selected_args.push_back(
								substitute_template_argument(selected_arg));
						}
						vector<TemplateArgument> flattened_args;
						for (size_t fi = 0; fi < selected_args.size(); ++fi)
						{
							if (selected_args[fi].kind == TemplateArgumentKind::Pack)
								flattened_args.insert(
									flattened_args.end(),
									selected_args[fi].pack.begin(),
									selected_args[fi].pack.end());
							else
								flattened_args.push_back(selected_args[fi]);
						}
						selected_args = flattened_args;
						Scope* owner = selected_bare->scope != NULL
							? selected_bare->scope->parent : NULL;
						TemplateDeclaration* alias =
							self->find_alias_template(
								owner,
								selected_bare->template_primary_name);
						TemplateDeclaration* klass = alias == NULL
							? self->find_class_template(
								owner,
								selected_bare->template_primary_name)
							: NULL;
						if (alias == NULL && klass == NULL && owner != NULL)
						{
							alias = self->find_alias_template(
								NULL,
								selected_bare->template_primary_name);
							klass = alias == NULL
								? self->find_class_template(
									NULL,
									selected_bare->template_primary_name)
								: NULL;
						}
						if (alias == NULL && klass == NULL)
						{
							size_t member_sep =
								selected_bare->template_primary_name.rfind("::");
							if (member_sep != string::npos)
							{
								string owner_name =
									selected_bare->template_primary_name.substr(
										0,
										member_sep);
								string member_name =
									selected_bare->template_primary_name.substr(
										member_sep + 2);
								Scope* owner_qualifier = NULL;
								string owner_lookup_name = owner_name;
								self->resolve_template_name_spelling(
									owner_name,
									owner_qualifier,
									owner_lookup_name);
								TemplateDeclaration* owner_template =
									self->find_class_template(
										owner_qualifier,
										owner_lookup_name);
								if (owner_template != NULL)
								{
									map<pair<TemplateDeclaration*, string>,
									    TemplateDeclaration*>::const_iterator mit =
										member_class_templates_.find(
											make_pair(owner_template,
											          member_name));
									if (mit != member_class_templates_.end())
										klass = mit->second;
								}
							}
						}
						if (alias != NULL)
							expanded =
								self->instantiate_alias_template(
									alias,
									selected_args);
						else if (klass != NULL)
							expanded =
								self->instantiate_class_template(
									klass,
									selected_args);
					}
					if (expanded.get() == NULL)
						expanded = substitute_template_type(selected_pattern);
				}
			catch (...)
			{
				if (selected_record_key != NULL)
				{
					if (restore_selected_record)
						self->record_template_arguments_[selected_record_key] =
							saved_selected_record;
					else if (erase_selected_record)
						self->record_template_arguments_.erase(
							selected_record_key);
					if (restore_selected_declaration)
						self->record_template_declarations_[selected_record_key] =
							saved_selected_declaration;
					else if (erase_selected_declaration)
						self->record_template_declarations_.erase(
							selected_record_key);
				}
				self->template_type_substitutions_ = save_type_subst;
				self->template_value_substitutions_ = save_value_subst;
				throw;
			}
			if (selected_record_key != NULL)
			{
				if (restore_selected_record)
					self->record_template_arguments_[selected_record_key] =
						saved_selected_record;
				else if (erase_selected_record)
					self->record_template_arguments_.erase(
						selected_record_key);
				if (restore_selected_declaration)
					self->record_template_declarations_[selected_record_key] =
						saved_selected_declaration;
				else if (erase_selected_declaration)
					self->record_template_declarations_.erase(
						selected_record_key);
			}
			self->template_type_substitutions_ = save_type_subst;
			self->template_value_substitutions_ = save_value_subst;
			out.push_back(TemplateArgument::type_arg(expanded));
			}
			return out;
		}
no_type_pack_expansion:
	if (argument.kind == TemplateArgumentKind::Type &&
	    !validating_template_definition_ &&
	    (!template_type_substitutions_.empty() ||
	     !template_value_substitutions_.empty() ||
	     function_template_candidate_instantiation_depth_ != 0))
	{
		TemplateArgument single = argument;
		single.pack_expansion = false;
		vector<TemplateArgument> out;
		out.push_back(single);
		return out;
	}
	if (argument.kind == TemplateArgumentKind::Value)
	{
		if (argument.dependent &&
		    argument.value_name == "__integer_pack" &&
		    argument.value_expr_end > argument.value_expr_begin)
		{
			TemplateArgument evaluated;
			if (const_cast<Parser*>(this)->
				    try_evaluate_dependent_value_expression_argument(
					    argument,
					    evaluated) &&
			    evaluated.kind == TemplateArgumentKind::Value &&
			    !evaluated.dependent)
			{
				vector<TemplateArgument> out;
				for (uint64_t i = 0; i < evaluated.value; ++i)
					out.push_back(TemplateArgument::value_arg(
						argument.type,
						i));
				return out;
			}
			vector<TemplateArgument> unresolved;
			unresolved.push_back(argument);
			return unresolved;
		}
		if (argument.dependent &&
		    argument.value_expr_end > argument.value_expr_begin)
		{
			TemplateArgument evaluated;
			if (const_cast<Parser*>(this)->
				    try_evaluate_dependent_value_expression_argument(
					    argument,
					    evaluated))
			{
				if (evaluated.kind == TemplateArgumentKind::Pack)
					return evaluated.pack;
				vector<TemplateArgument> single;
				single.push_back(evaluated);
				return single;
			}
		}
		TemplateArgument subst;
		if (!argument.value_name.empty() &&
		    find_template_value_substitution(argument.value_name, subst) &&
		    subst.kind == TemplateArgumentKind::Pack)
		{
			vector<TemplateArgument> out;
			TemplateArgument element_pattern = argument;
			element_pattern.pack_expansion = false;
			for (size_t i = 0; i < subst.pack.size(); ++i)
			{
				if (subst.pack[i].kind != TemplateArgumentKind::Value)
					throw runtime_error("value template argument pack required");
				Parser* self = const_cast<Parser*>(this);
				vector<map<string, TemplateArgument> > save_value_subst =
					self->template_value_substitutions_;
				map<string, TemplateArgument> value_subst;
				value_subst[argument.value_name] = subst.pack[i];
				self->template_value_substitutions_.push_back(value_subst);
				try
				{
					out.push_back(substitute_template_argument(
						element_pattern));
				}
				catch (...)
				{
					self->template_value_substitutions_ = save_value_subst;
					throw;
				}
				self->template_value_substitutions_ = save_value_subst;
			}
			return out;
		}
		if (!argument.value_owner_template_name.empty() &&
		    find_template_value_substitution(
			    argument.value_owner_template_name,
			    subst) &&
		    subst.kind == TemplateArgumentKind::Pack)
		{
			vector<TemplateArgument> out;
			TemplateArgument element_pattern = argument;
			element_pattern.pack_expansion = false;
			for (size_t i = 0; i < subst.pack.size(); ++i)
			{
				if (subst.pack[i].kind != TemplateArgumentKind::Type)
					throw runtime_error("type template argument pack required");
				Parser* self = const_cast<Parser*>(this);
				vector<map<string, TypePtr> > save_type_subst =
					self->template_type_substitutions_;
				vector<map<string, TemplateArgument> > save_value_subst =
					self->template_value_substitutions_;
				map<string, TypePtr> type_subst;
				map<string, TemplateArgument> value_subst;
				type_subst[argument.value_owner_template_name] =
					subst.pack[i].type;
				value_subst[argument.value_owner_template_name] =
					subst.pack[i];
				self->template_type_substitutions_.push_back(type_subst);
				self->template_value_substitutions_.push_back(value_subst);
				try
				{
					out.push_back(substitute_template_argument(
						element_pattern));
				}
				catch (...)
				{
					self->template_type_substitutions_ = save_type_subst;
					self->template_value_substitutions_ = save_value_subst;
					throw;
				}
				self->template_type_substitutions_ = save_type_subst;
				self->template_value_substitutions_ = save_value_subst;
			}
			return out;
		}
		if (argument.type.get() != NULL &&
		    template_type_has_template_parameter_name(argument.type, pack_name) &&
			    find_template_value_substitution(pack_name, subst) &&
			    subst.kind == TemplateArgumentKind::Pack)
			{
				vector<TemplateArgument> out;
			for (size_t i = 0; i < subst.pack.size(); ++i)
			{
				if (subst.pack[i].kind == TemplateArgumentKind::Value)
				{
					out.push_back(subst.pack[i]);
					continue;
				}
				if (subst.pack[i].kind != TemplateArgumentKind::Type)
					throw runtime_error("value template argument pack required");
				Parser* self = const_cast<Parser*>(this);
				vector<map<string, TypePtr> > save_type_subst =
					self->template_type_substitutions_;
				vector<map<string, TemplateArgument> > save_value_subst =
					self->template_value_substitutions_;
				map<string, TypePtr> type_subst;
				map<string, TemplateArgument> value_subst;
				type_subst[pack_name] = subst.pack[i].type;
				value_subst[pack_name] = subst.pack[i];
				self->template_type_substitutions_.push_back(type_subst);
				self->template_value_substitutions_.push_back(value_subst);
				TemplateArgument element_pattern = argument;
				element_pattern.pack_expansion = false;
				try
				{
					out.push_back(substitute_template_argument(
						element_pattern));
				}
				catch (...)
				{
					self->template_type_substitutions_ = save_type_subst;
					self->template_value_substitutions_ = save_value_subst;
					throw;
				}
				self->template_type_substitutions_ = save_type_subst;
				self->template_value_substitutions_ = save_value_subst;
			}
			return out;
		}
		vector<TemplateArgument> unresolved;
		unresolved.push_back(argument);
		return unresolved;
	}
	throw runtime_error("unsupported template argument pack expansion");
}

void Parser::append_completed_template_pack_argument(
	TemplateDeclaration* declaration,
	size_t parameter_index,
	TypePtr parameter_type,
	const vector<TemplateArgument>& explicit_expanded,
	size_t& explicit_index,
	vector<TemplateArgument>& out)
{
	const TemplateParameterInfo& parameter =
		declaration->parameters[parameter_index];
	vector<TemplateArgument> pack;
	auto append_element = [&](TemplateArgument elem) {
		if (parameter.kind == TemplateParameterKind::Type &&
		    elem.kind == TemplateArgumentKind::Value &&
		    elem.type.get() != NULL &&
		    (elem.dependent ||
		     pa11::strip_cv(elem.type)->kind !=
			     pa11::TypeKind::Fundamental))
			elem = TemplateArgument::type_arg(elem.type);
		if (!template_argument_kind_matches_parameter(elem, parameter))
			throw runtime_error("template pack argument kind mismatch");
		elem = convert_completed_non_type_template_argument(elem,
		                                                    parameter_type);
		if (elem.kind == TemplateArgumentKind::Value &&
		    !template_argument_has_template_parameter(
			    elem,
			    record_template_arguments_))
			elem.pack_expansion = false;
		pack.push_back(elem);
	};
	auto append_expanded_argument = [&](const TemplateArgument& argument) {
		vector<TemplateArgument> expanded =
			expand_template_argument_pack(argument);
		for (size_t e = 0; e < expanded.size(); ++e)
		{
			TemplateArgument substituted =
				substitute_template_argument(expanded[e]);
			if (substituted.kind == TemplateArgumentKind::Pack)
			{
				for (size_t p = 0; p < substituted.pack.size(); ++p)
					append_element(substituted.pack[p]);
			}
			else
				append_element(substituted);
		}
	};

	size_t required_after = 0;
	for (size_t j = parameter_index + 1;
	     j < declaration->parameters.size();
	     ++j)
		if (!declaration->parameters[j].is_pack &&
		    !declaration->parameters[j].has_default)
			++required_after;
	if (explicit_index + required_after > explicit_expanded.size())
		throw runtime_error("missing template argument");

	bool consumed_explicit_pack_argument = false;
	if (explicit_index < explicit_expanded.size() &&
	    explicit_expanded[explicit_index].kind == TemplateArgumentKind::Pack)
	{
		TemplateArgument arg = explicit_expanded[explicit_index++];
		consumed_explicit_pack_argument = true;
		for (size_t i = 0; i < arg.pack.size(); ++i)
		{
			if (arg.pack[i].kind == TemplateArgumentKind::Pack)
			{
				for (size_t p = 0; p < arg.pack[i].pack.size(); ++p)
					append_expanded_argument(arg.pack[i].pack[p]);
			}
			else
				append_expanded_argument(arg.pack[i]);
		}
	}

	size_t take = consumed_explicit_pack_argument
		? 0 : explicit_expanded.size() - explicit_index - required_after;
	for (size_t i = 0; i < take; ++i)
	{
		TemplateArgument arg = explicit_expanded[explicit_index++];
		if (arg.kind == TemplateArgumentKind::Pack)
		{
			for (size_t p = 0; p < arg.pack.size(); ++p)
				append_expanded_argument(arg.pack[p]);
		}
		else
			append_expanded_argument(arg);
	}
	TemplateArgument completed_pack = TemplateArgument::pack_arg(pack);
	completed_pack.value_name = parameter.name;
	out.push_back(completed_pack);
}

TemplateArgument Parser::parse_non_type_default_template_argument(
	const TemplateParameterInfo& parameter,
	const vector<TemplateArgument>& completed_args)
{
	bool default_dependent = type_is_template_dependent(parameter.type);
	for (size_t i = 0; i < completed_args.size(); ++i)
		if (template_argument_has_template_parameter(completed_args[i],
		                                             record_template_arguments_))
			default_dependent = true;

	int save_expression_depth = template_argument_expression_depth_;
	++template_argument_expression_depth_;
	Expr expr;
	try
	{
		expr = parse_assignment_expression();
	}
	catch (...)
	{
		template_argument_expression_depth_ = save_expression_depth;
		if (!default_dependent)
			throw;
		expr = Expr();
	}
	template_argument_expression_depth_ = save_expression_depth;

	if (expr.valid && !expr.has_constant_value)
	{
		ConstexprValue value;
		if (try_evaluate_constexpr_expr(expr.node, value) && !value.is_object)
		{
			expr.has_constant_value = true;
			expr.constant_value = value.int_value;
			expr.node.has_constant_value = true;
			expr.node.constant_value = value.int_value;
		}
	}
	if (expr.valid && !expr.has_constant_value)
	{
		try
		{
			Conversion conv = convert_to(expr, pa11::make_fundamental(FT_BOOL));
			if (conv.viable && !conv.expr.has_constant_value)
			{
				ConstexprValue value;
				if (try_evaluate_constexpr_expr(conv.expr.node, value))
					apply_constexpr_value(conv.expr, value);
			}
			if (conv.viable && conv.expr.has_constant_value)
				expr = conv.expr;
		}
		catch (const runtime_error&)
		{
		}
	}
	if (!expr.has_constant_value &&
	    !default_dependent &&
	    expr.dependent_value_name.empty())
		throw runtime_error("invalid default template argument");

	if (expr.has_constant_value)
		return TemplateArgument::value_arg(expression_object_type(expr.type),
		                                   expr.constant_value);

	TemplateArgument arg = TemplateArgument::dependent_value_arg(parameter.type);
	if (expr.valid)
	{
		arg.value_name = expr.dependent_value_name;
		arg.value_owner_template_name =
			expr.dependent_value_owner_template_name;
		arg.value_member_name = expr.dependent_value_member_name;
		arg.value_negated = expr.dependent_value_negated;
		arg.value_owner_template_arguments =
			expr.dependent_value_owner_template_arguments;
	}
	return arg;
}

TemplateArgument Parser::parse_default_template_argument(
	TemplateDeclaration* declaration,
	size_t parameter_index,
	const vector<TemplateArgument>& completed_args)
{
	const TemplateParameterInfo& parameter =
		declaration->parameters[parameter_index];
	bool tokens_are_declaration_tokens =
		tokens_.size() == declaration_tokens_.size() &&
		(tokens_.empty() ||
		 (tokens_.front().source == declaration_tokens_.front().source &&
		  tokens_.back().source == declaration_tokens_.back().source));
	vector<Token> save_tokens;
	if (!tokens_are_declaration_tokens)
		save_tokens = tokens_;
	size_t save_pos = pos_;
	vector<Scope*> save_scopes = scopes_;
	size_t save_type_subst_size = template_type_substitutions_.size();
	size_t save_value_subst_size = template_value_substitutions_.size();
	size_t save_pack_subst_size = template_type_parameter_packs_.size();
	bool save_default_argument = parsing_default_template_argument_;

	map<string, TypePtr> subst;
	map<string, TemplateArgument> value_subst;
	set<string> pack_subst;
	for (size_t i = 0; i < completed_args.size(); ++i)
	{
		if (declaration->parameters[i].name.empty())
			continue;
		const TemplateParameterInfo& completed_parameter =
			declaration->parameters[i];
		if (completed_parameter.is_pack)
		{
			subst[completed_parameter.name] =
				pa11::make_template_parameter_type(
					completed_parameter.name);
			value_subst[completed_parameter.name] = completed_args[i];
			pack_subst.insert(completed_parameter.name);
		}
		else if (completed_parameter.kind == TemplateParameterKind::Type)
			subst[completed_parameter.name] = completed_args[i].type;
		else
			value_subst[completed_parameter.name] = completed_args[i];
	}

	template_type_substitutions_.insert(
		template_type_substitutions_.end(),
		declaration->outer_type_substitutions.begin(),
		declaration->outer_type_substitutions.end());
	template_value_substitutions_.insert(
		template_value_substitutions_.end(),
		declaration->outer_value_substitutions.begin(),
		declaration->outer_value_substitutions.end());
	template_type_substitutions_.push_back(subst);
	template_value_substitutions_.push_back(value_subst);
	template_type_parameter_packs_.push_back(pack_subst);
	scopes_.clear();
	scopes_.push_back(declaration->lexical_scope != NULL
	                  ? declaration->lexical_scope
	                  : declaration->owner);
	if (!tokens_are_declaration_tokens)
		tokens_ = declaration_tokens_;
	pos_ = parameter.default_begin;
	parsing_default_template_argument_ = true;

	TemplateArgument arg;
	try
	{
		if (parameter.kind == TemplateParameterKind::Type)
		{
			arg = TemplateArgument::type_arg(parse_type_id());
			arg = substitute_template_argument(arg);
		}
		else if (parameter.kind == TemplateParameterKind::TemplateTemplate)
		{
			if (!try_parse_template_template_argument(arg))
				throw runtime_error("invalid default template argument");
		}
		else
		{
			arg = parse_non_type_default_template_argument(parameter,
			                                              completed_args);
		}
		if (pos_ != parameter.default_end)
			throw runtime_error("invalid default template argument");
	}
	catch (...)
	{
		if (!tokens_are_declaration_tokens)
			tokens_ = save_tokens;
		scopes_ = save_scopes;
		template_type_substitutions_.resize(save_type_subst_size);
		template_value_substitutions_.resize(save_value_subst_size);
		template_type_parameter_packs_.resize(save_pack_subst_size);
		parsing_default_template_argument_ = save_default_argument;
		pos_ = save_pos;
		throw;
	}

	if (!tokens_are_declaration_tokens)
		tokens_ = save_tokens;
	scopes_ = save_scopes;
	template_type_substitutions_.resize(save_type_subst_size);
	template_value_substitutions_.resize(save_value_subst_size);
	template_type_parameter_packs_.resize(save_pack_subst_size);
	parsing_default_template_argument_ = save_default_argument;
	pos_ = save_pos;
	return arg;
}

vector<TemplateArgument> Parser::complete_template_arguments(
	TemplateDeclaration* declaration,
	const vector<TemplateArgument>& explicit_arguments)
{ vector<TemplateArgument> explicit_expanded; for (size_t i = 0; i < explicit_arguments.size(); ++i) { vector<TemplateArgument> expansion; bool keep_explicit_pack = explicit_arguments.size() == declaration->parameters.size() && i < declaration->parameters.size() && declaration->parameters[i].is_pack && explicit_arguments[i].kind == TemplateArgumentKind::Pack; bool keep_single_type_pattern = i < declaration->parameters.size() && !declaration->parameters[i].is_pack && explicit_arguments[i].kind == TemplateArgumentKind::Type; if (keep_single_type_pattern) { TypePtr bare_arg = explicit_arguments[i].type.get() != NULL ? pa11::strip_cv(explicit_arguments[i].type) : TypePtr(); keep_single_type_pattern = bare_arg.get() != NULL && (bare_arg->kind == pa11::TypeKind::Function || bare_arg->kind == pa11::TypeKind::MemberPointer); } if (keep_explicit_pack || keep_single_type_pattern) expansion.push_back(explicit_arguments[i]); else expansion = expand_template_argument_pack(explicit_arguments[i]);
explicit_expanded.insert(explicit_expanded.end(), expansion.begin(), expansion.end()); } vector<TemplateArgument> out; size_t explicit_index = 0; for (size_t param_index = 0; param_index < declaration->parameters.size();
++param_index) { const TemplateParameterInfo& parameter = declaration->parameters[param_index]; TypePtr parameter_type = parameter.type; if (parameter.kind == TemplateParameterKind::NonType &&
	parameter_type.get() != NULL) { map<string, TypePtr> subst; map<string, TemplateArgument> value_subst; set<string> pack_subst; for (size_t i = 0; i < out.size() && i < declaration->parameters.size(); ++i)
if (!declaration->parameters[i].name.empty()) { if (declaration->parameters[i].kind == TemplateParameterKind::Type) { if (declaration->parameters[i].is_pack) { subst[declaration->parameters[i].name] =
	pa11::make_template_parameter_type( declaration->parameters[i].name); value_subst[declaration->parameters[i].name] = out[i]; pack_subst.insert(declaration->parameters[i].name); } else subst[declaration->parameters[i].name] = out[i].type; } else
	value_subst[declaration->parameters[i].name] = out[i]; } size_t save_type_subst_size = template_type_substitutions_.size(); size_t save_value_subst_size = template_value_substitutions_.size(); size_t save_pack_subst_size = template_type_parameter_packs_.size();
template_type_substitutions_.insert( template_type_substitutions_.end(), declaration->outer_type_substitutions.begin(), declaration->outer_type_substitutions.end()); template_value_substitutions_.insert(
	template_value_substitutions_.end(), declaration->outer_value_substitutions.begin(), declaration->outer_value_substitutions.end()); template_type_substitutions_.push_back(subst);
	template_value_substitutions_.push_back(value_subst); template_type_parameter_packs_.push_back(pack_subst); try { parameter_type = substitute_template_type(parameter_type); } catch (const runtime_error& err) { bool disabled_enable_if = false; if (function_template_candidate_instantiation_depth_ != 0 && string(err.what()) == "dependent typename not resolved") { TypePtr bare_parameter_type = parameter_type.get() != NULL ? pa11::strip_cv(parameter_type) : TypePtr(); if (bare_parameter_type.get() != NULL && bare_parameter_type->is_dependent_typename && !bare_parameter_type->template_arguments.empty()) { vector<TemplateArgument> candidate_args; try { for (size_t ai = 0; ai < bare_parameter_type->template_arguments.size(); ++ai) { TemplateArgument candidate_arg = template_argument_from_instance_argument( bare_parameter_type->template_arguments[ai]); candidate_args.push_back(substitute_template_argument(candidate_arg)); } disabled_enable_if = dependent_typename_disabled_enable_if_argument( bare_parameter_type, candidate_args); } catch (const runtime_error&) { disabled_enable_if = false; } } } template_type_substitutions_.resize(save_type_subst_size);
	template_value_substitutions_.resize(save_value_subst_size); template_type_parameter_packs_.resize(save_pack_subst_size); if (function_template_candidate_instantiation_depth_ == 0 || string(err.what()) != "dependent typename not resolved" || disabled_enable_if) throw; } template_type_substitutions_.resize(save_type_subst_size); template_value_substitutions_.resize(save_value_subst_size); template_type_parameter_packs_.resize(save_pack_subst_size); } if (parameter.is_pack) {
append_completed_template_pack_argument(declaration, param_index, parameter_type, explicit_expanded, explicit_index, out); continue; } if (explicit_index < explicit_expanded.size()) {
TemplateArgument arg = explicit_expanded[explicit_index++]; TemplateArgument original_arg = arg; if (parameter.kind == TemplateParameterKind::NonType && arg.kind == TemplateArgumentKind::Value && arg.dependent && parameter_type.get() != NULL) arg.type = parameter_type; if (parameter.kind == TemplateParameterKind::Type && arg.kind == TemplateArgumentKind::Value && arg.type.get() != NULL &&
(arg.dependent || pa11::strip_cv(arg.type)->kind != pa11::TypeKind::Fundamental)) { bool pack_expansion = arg.pack_expansion; arg = TemplateArgument::type_arg(arg.type); arg.pack_expansion = pack_expansion; } {
	map<string, TypePtr> subst; map<string, TemplateArgument> value_subst; set<string> pack_subst; for (size_t i = 0; i < out.size() && i < declaration->parameters.size(); ++i) if (!declaration->parameters[i].name.empty()) {
if (declaration->parameters[i].kind == TemplateParameterKind::Type) { if (declaration->parameters[i].is_pack) { subst[declaration->parameters[i].name] = pa11::make_template_parameter_type(
	declaration->parameters[i].name); value_subst[declaration->parameters[i].name] = out[i]; pack_subst.insert(declaration->parameters[i].name); } else subst[declaration->parameters[i].name] = out[i].type; } else value_subst[declaration->parameters[i].name] = out[i]; }
bool explicit_value_name_collides = false;
if (arg.kind == TemplateArgumentKind::Value &&
    arg.dependent &&
    !arg.value_name.empty())
{
	for (size_t pi = 0; pi < declaration->parameters.size(); ++pi)
		if (declaration->parameters[pi].name == arg.value_name)
			explicit_value_name_collides = true;
}
	size_t save_type_subst_size = template_type_substitutions_.size(); size_t save_value_subst_size = template_value_substitutions_.size(); size_t save_pack_subst_size = template_type_parameter_packs_.size(); template_type_substitutions_.insert(
template_type_substitutions_.end(), declaration->outer_type_substitutions.begin(), declaration->outer_type_substitutions.end()); template_value_substitutions_.insert( template_value_substitutions_.end(),
	declaration->outer_value_substitutions.begin(), declaration->outer_value_substitutions.end()); template_type_substitutions_.push_back(subst); template_value_substitutions_.push_back(value_subst); template_type_parameter_packs_.push_back(pack_subst); try {
if (!explicit_value_name_collides)
	arg = substitute_template_argument(arg); } catch (...) { template_type_substitutions_.resize(save_type_subst_size); template_value_substitutions_.resize(save_value_subst_size); template_type_parameter_packs_.resize(save_pack_subst_size); throw; } template_type_substitutions_.resize(save_type_subst_size);
	template_value_substitutions_.resize(save_value_subst_size); template_type_parameter_packs_.resize(save_pack_subst_size); } if (parameter.kind == TemplateParameterKind::TemplateTemplate && arg.kind == TemplateArgumentKind::Type) { TemplateDeclaration* recovered_template =
class_template_declaration_for_match(arg.type); if (recovered_template != NULL) arg = TemplateArgument::template_arg(recovered_template); } if (!template_argument_kind_matches_parameter(arg, parameter)) { TypePtr dependent_type = arg.type; TypePtr dependent_bare = dependent_type.get() != NULL
? pa11::strip_cv(dependent_type) : TypePtr(); if ((dependent_bare.get() == NULL || !dependent_bare->is_dependent_typename || !dependent_bare->dependent_typename_qualified) &&
original_arg.kind == TemplateArgumentKind::Type) { TypePtr original_bare = original_arg.type.get() != NULL ? pa11::strip_cv(original_arg.type) : TypePtr(); if (original_bare.get() != NULL &&
original_bare->is_dependent_typename && original_bare->dependent_typename_qualified) { dependent_type = original_arg.type; dependent_bare = original_bare; } } if (parameter.kind == TemplateParameterKind::NonType &&
arg.kind == TemplateArgumentKind::Type && dependent_bare.get() != NULL && dependent_bare->kind == pa11::TypeKind::Function && dependent_bare->parameters.size() == 1 && parameter_type.get() != NULL &&
	pa11::same_type(dependent_bare->base, parameter_type)) { dependent_type = dependent_bare->parameters[0]; } if (parameter.kind != TemplateParameterKind::NonType || arg.kind != TemplateArgumentKind::Type ||
		dependent_type.get() == NULL || !dependent_type->is_dependent_typename || !dependent_type->dependent_typename_qualified) { throw runtime_error("template argument kind mismatch"); } TemplateArgument value_arg =
TemplateArgument::dependent_value_arg(parameter_type); value_arg.value_name = dependent_type->name; size_t member_pos = dependent_type->name.rfind("::"); string member_name = member_pos != string::npos
? dependent_type->name.substr(member_pos + 2) : string(); string owner_name = dependent_type->template_primary_name; if (owner_name.empty()) { string root = member_pos != string::npos
? dependent_type->name.substr(0, member_pos) : dependent_type->name; size_t template_pos = root.find('<'); owner_name = root.substr(0, template_pos); } if (!owner_name.empty() && !member_name.empty()) {
value_arg.value_owner_template_name = owner_name; value_arg.value_member_name = member_name; for (size_t ai = 0; ai < dependent_type->template_arguments.size(); ++ai) { TemplateArgument owner_arg =
template_argument_from_instance_argument( dependent_type->template_arguments[ai]); owner_arg = substitute_template_argument(owner_arg); value_arg.value_owner_template_arguments.push_back(
completed_instance_argument(owner_arg)); } } arg = value_arg; arg = substitute_template_argument(arg); } arg = convert_completed_non_type_template_argument(arg, parameter_type); out.push_back(arg); continue; }
	if (!parameter.has_default) { throw runtime_error("missing template argument"); } TemplateArgument arg; try { arg = parse_default_template_argument(declaration, param_index, out);
	if (parameter.kind == TemplateParameterKind::Type) arg = substitute_template_argument(arg); } catch (const runtime_error& err) { if (function_template_candidate_instantiation_depth_ == 0 || parameter.kind != TemplateParameterKind::Type || string(err.what()) != "dependent typename not resolved") throw; bool dependent_context = false; for (size_t ai = 0; ai < out.size(); ++ai) if (template_argument_has_template_parameter(out[ai], record_template_arguments_)) dependent_context = true; if (!dependent_context) throw; string default_name = parameter.name.empty() ? declaration->name + "__default" + to_string(param_index) : parameter.name; arg = TemplateArgument::type_arg(pa11::make_dependent_typename_type(default_name, false, false, false)); } arg = convert_completed_non_type_template_argument(arg, parameter_type); out.push_back(arg); } if (explicit_index != explicit_expanded.size()) throw runtime_error("too many template arguments");
	{
			map<string, TypePtr> subst;
			map<string, TemplateArgument> value_subst;
			set<string> pack_subst;
			bool concrete_completion = true;
		for (size_t i = 0; i < out.size() && i < declaration->parameters.size(); ++i)
		{
			if (declaration->parameters[i].name.empty())
				continue;
			if (declaration->parameters[i].kind == TemplateParameterKind::Type)
			{
				if (declaration->parameters[i].is_pack)
				{
						subst[declaration->parameters[i].name] =
							pa11::make_template_parameter_type(
								declaration->parameters[i].name);
						value_subst[declaration->parameters[i].name] = out[i];
						pack_subst.insert(declaration->parameters[i].name);
					}
				else
					subst[declaration->parameters[i].name] = out[i].type;
			}
			else
				value_subst[declaration->parameters[i].name] = out[i];
		}
		for (map<string, TypePtr>::const_iterator it = subst.begin();
		     it != subst.end(); ++it)
			if (type_is_template_dependent(it->second))
				concrete_completion = false;
		for (map<string, TemplateArgument>::const_iterator it =
			     value_subst.begin(); it != value_subst.end(); ++it)
			if (template_argument_has_template_parameter(
				    it->second,
				    record_template_arguments_))
				concrete_completion = false;
		size_t save_type_subst_size = template_type_substitutions_.size();
			size_t save_value_subst_size =
				template_value_substitutions_.size();
			size_t save_pack_subst_size =
				template_type_parameter_packs_.size();
			template_type_substitutions_.insert(
			template_type_substitutions_.end(),
			declaration->outer_type_substitutions.begin(),
			declaration->outer_type_substitutions.end());
		template_value_substitutions_.insert(
			template_value_substitutions_.end(),
			declaration->outer_value_substitutions.begin(),
			declaration->outer_value_substitutions.end());
			template_type_substitutions_.push_back(subst);
			template_value_substitutions_.push_back(value_subst);
			template_type_parameter_packs_.push_back(pack_subst);
			try
		{
			for (size_t i = 0; i < out.size() && i < declaration->parameters.size(); ++i)
			{
				if (declaration->parameters[i].kind != TemplateParameterKind::NonType ||
				    declaration->parameters[i].type.get() == NULL)
					continue;
				TypePtr parameter_type = declaration->parameters[i].type;
				try
				{
					parameter_type = substitute_template_type(parameter_type);
				}
				catch (const runtime_error& err)
				{
					if (function_template_candidate_instantiation_depth_ != 0 &&
					    string(err.what()) == "dependent typename not resolved")
					{
						concrete_completion = false;
						continue;
					}
					throw;
				}
				TypePtr parameter_bare =
					parameter_type.get() != NULL
					? pa11::strip_cv(parameter_type)
					: TypePtr();
				if (parameter_bare.get() != NULL &&
				    parameter_bare->is_dependent_typename)
				{
					TypePtr resolved =
						resolve_dependent_typename_type(parameter_bare);
					if (resolved.get() != NULL && resolved != parameter_bare)
						parameter_type = substitute_template_type(resolved);
					else if (parameter_bare->dependent_typename_qualified &&
					         !parameter_bare->template_primary_name.empty() &&
					         !parameter_bare->template_arguments.empty())
					{
						string member_name = parameter_bare->name;
						size_t member_pos = member_name.rfind("::");
						if (member_pos != string::npos)
							member_name = member_name.substr(member_pos + 2);
						vector<TemplateArgument> owner_args;
						bool owner_args_dependent = false;
						for (size_t ai = 0;
						     ai < parameter_bare->template_arguments.size();
						     ++ai)
						{
							TemplateArgument owner_arg =
								template_argument_from_instance_argument(
									parameter_bare->template_arguments[ai]);
							if (owner_arg.kind == TemplateArgumentKind::Value &&
							    owner_arg.dependent &&
							    !owner_arg.value_owner_template_name.empty())
							{
								TemplateArgument resolved_value;
								try
								{
									if (resolve_dependent_value_member_argument(
										    owner_arg,
										    resolved_value))
										owner_arg = resolved_value;
								}
								catch (const runtime_error&)
								{
									if (owner_arg.value_expr_end >
										    owner_arg.value_expr_begin &&
									    function_template_candidate_instantiation_depth_ != 0)
										owner_args_dependent = true;
									else
										throw;
								}
							}
							try
							{
								owner_arg = substitute_template_argument(owner_arg);
							}
							catch (const runtime_error&)
							{
								if (owner_arg.kind == TemplateArgumentKind::Value &&
								    owner_arg.dependent &&
								    owner_arg.value_expr_end >
									    owner_arg.value_expr_begin &&
								    function_template_candidate_instantiation_depth_ != 0)
									owner_args_dependent = true;
								else
									throw;
							}
							if (template_argument_has_template_parameter(
								    owner_arg,
								    record_template_arguments_))
								owner_args_dependent = true;
							if (owner_arg.kind == TemplateArgumentKind::Value &&
							    owner_arg.dependent &&
							    owner_arg.value_expr_end > owner_arg.value_expr_begin &&
							    function_template_candidate_instantiation_depth_ != 0)
								owner_args_dependent = true;
							owner_args.push_back(owner_arg);
						}
						if (!owner_args_dependent)
						{
							Scope* qualifier = NULL;
							string lookup_name =
								parameter_bare->template_primary_name;
							resolve_template_name_spelling(
								parameter_bare->template_primary_name,
								qualifier,
								lookup_name);
							TemplateDeclaration* klass =
								find_class_template(qualifier, lookup_name);
							if (klass == NULL && qualifier != NULL)
								klass = find_class_template(NULL,
								                            lookup_name);
							if (klass == NULL)
								klass = find_class_template(
									NULL,
									parameter_bare->template_primary_name);
							if (klass == NULL)
							{
								for (map<Scope*, map<string, TemplateDeclaration*> >::const_iterator
									     sit = class_templates_.begin();
								     sit != class_templates_.end() && klass == NULL;
								     ++sit)
								{
									map<string, TemplateDeclaration*>::const_iterator
										found = sit->second.find(lookup_name);
									if (found == sit->second.end())
										found = sit->second.find(
											parameter_bare->template_primary_name);
									if (found != sit->second.end())
										klass = found->second;
								}
							}
							if (klass != NULL)
							{
								TypePtr owner =
									instantiate_class_template(klass,
									                           owner_args);
								TypePtr owner_bare = owner.get() != NULL
									? pa11::strip_cv(owner)
									: TypePtr();
								if (owner_bare.get() != NULL &&
								    owner_bare->kind == pa11::TypeKind::Record &&
								    owner_bare->scope != NULL)
								{
									complete_template_record(owner_bare);
									vector<Binding*> found =
										lookup_qualified_set(
											owner_bare->scope,
											member_name,
											pa11::LOOKUP_TYPE);
									if (!found.empty() &&
									    found[0]->type.get() != NULL)
										parameter_type =
											substitute_template_type_in_scope(
												found[0]->type,
												owner_bare->scope);
								}
							}
						}
						parameter_bare = parameter_type.get() != NULL
							? pa11::strip_cv(parameter_type)
							: TypePtr();
							if (concrete_completion &&
							    !owner_args_dependent &&
							    parameter_bare.get() != NULL &&
							    parameter_bare->is_dependent_typename)
							{
								if (function_template_candidate_instantiation_depth_ != 0)
									concrete_completion = false;
								else
								throw runtime_error(
									"dependent typename not resolved");
							}
						}
						else if (concrete_completion)
						{
							if (function_template_candidate_instantiation_depth_ != 0)
								concrete_completion = false;
							else
							throw runtime_error("dependent typename not resolved");
						}
					}
				out[i] = convert_completed_non_type_template_argument(
					out[i],
					parameter_type);
			}
		}
			catch (...)
			{
				template_type_substitutions_.resize(save_type_subst_size);
				template_value_substitutions_.resize(save_value_subst_size);
				template_type_parameter_packs_.resize(save_pack_subst_size);
				throw;
			}
			template_type_substitutions_.resize(save_type_subst_size);
			template_value_substitutions_.resize(save_value_subst_size);
			template_type_parameter_packs_.resize(save_pack_subst_size);
		}
	return out; }

}  // namespace internal
}  // namespace pa12
