#include "pa12_templates_function_abi_internal.h"
#include "pa12_templates_instance_support.h"
#include "pa12_types_support.h"

using namespace std;

namespace pa12 {
namespace internal {

vector<string> abi_qualified_type_scope_names(TypePtr type)
{
	TypePtr bare = type.get() != NULL ? pa11::strip_cv(type) : TypePtr();
	if (bare.get() == NULL)
		return vector<string>();
	string name = bare->is_template_specialization &&
	              !bare->template_primary_name.empty()
		? bare->template_primary_name : bare->name;
	size_t args = name.find('<');
	if (args != string::npos)
		name = name.substr(0, args);
	vector<string> parts = abi_split_qualified_name(name);
	if (parts.size() <= 1)
		return vector<string>();
	parts.pop_back();
	return parts;
}

static string abi_named_scope_component(const string& name)
{
	return name == "std" ? string("St") : abi_source_name(name);
}

string abi_named_scope_prefix_with_substitutions(
	const vector<string>& scopes,
	AbiSubstitutionContext& ctx)
{
	string raw_prefix;
	for (size_t i = 0; i < scopes.size(); ++i)
		raw_prefix += abi_named_scope_component(scopes[i]);
	if (!raw_prefix.empty())
	{
		size_t full = abi_find_substitution(ctx, "N" + raw_prefix + "E");
		if (full != static_cast<size_t>(-1))
			return abi_substitution_code(full);
	}
	string out;
	string prefix_key;
	for (size_t i = 0; i < scopes.size(); ++i)
	{
		string component = abi_named_scope_component(scopes[i]);
		if (component.empty())
			continue;
		string key = prefix_key.empty()
			? component : string("N") + prefix_key + component + "E";
		if (component == "St")
		{
			out += component;
			prefix_key = key;
			continue;
		}
		size_t found = abi_find_substitution(ctx, key);
		if (found != static_cast<size_t>(-1))
			out += abi_substitution_code(found);
		else
		{
			out += component;
			abi_add_substitution(ctx, key);
		}
		prefix_key = key;
	}
	return out;
}

string abi_named_scope_prefix_probe_with_substitutions(
	const vector<string>& scopes,
	AbiSubstitutionContext& ctx)
{
	string out;
	string prefix_key;
	for (size_t i = 0; i < scopes.size(); ++i)
	{
		string component = abi_named_scope_component(scopes[i]);
		if (component.empty())
			continue;
		string key = prefix_key.empty()
			? component : string("N") + prefix_key + component + "E";
		size_t found = component == "St" ? static_cast<size_t>(-1) :
			abi_find_substitution(ctx, key);
		out += found == static_cast<size_t>(-1)
			? component : abi_substitution_code(found);
		prefix_key = key;
	}
	return out;
}

string abi_scope_prefix_probe_with_substitutions(const vector<Scope*>& scopes,
                                                AbiSubstitutionContext& ctx)
{
	string out;
	string prefix_key;
	for (size_t i = 0; i < scopes.size(); ++i)
	{
		string component;
		if (scopes[i]->kind == ScopeKind::Namespace)
			component = abi_scope_component_with_substitutions(scopes[i],
			                                                  ctx);
		else if (scopes[i]->kind == ScopeKind::Class)
			component = abi_record_type_probe_with_substitutions(
				pa11::record_type_for_scope(scopes[i]), ctx, false);
		if (component.empty())
			continue;
		string key = prefix_key.empty()
			? component : string("N") + prefix_key + component + "E";
		size_t found = component == "St" ? static_cast<size_t>(-1) :
			abi_find_substitution(ctx, key);
		out += found == static_cast<size_t>(-1)
			? component : abi_substitution_code(found);
		prefix_key = key;
	}
	return out;
}

string abi_template_instance_argument_probe_with_substitutions(
	const pa11::TemplateInstanceArgument& arg,
	AbiSubstitutionContext& ctx)
{
	if (arg.kind == pa11::TemplateInstanceArgumentKind::Type)
		return abi_type_probe_with_substitutions(arg.type, ctx);
	if (arg.kind == pa11::TemplateInstanceArgumentKind::Value)
	{
		if (!arg.value_name.empty())
			return "L" + abi_type_probe_with_substitutions(arg.type, ctx) +
			       abi_encoded_stable_value_name(arg.value_name) + "E";
		if (abi_type_is_dependent_parameter(arg.type))
			return "Li" + to_string(arg.value) + "E";
		return "L" + abi_type_probe_with_substitutions(arg.type, ctx) +
		       to_string(arg.value) + "E";
	}
	if (arg.kind == pa11::TemplateInstanceArgumentKind::Pack)
	{
		const pa11::TemplateInstanceArgument* expansion =
			abi_pack_expansion_element(arg);
		if (expansion != NULL)
			return "Dp" +
			       abi_template_instance_argument_probe_with_substitutions(
				       *expansion, ctx);
		string out = "J";
		for (size_t i = 0; i < arg.pack.size(); ++i)
			out += abi_template_instance_argument_probe_with_substitutions(
				arg.pack[i], ctx);
		out += "E";
		return out;
	}
	return abi_template_name(arg.template_name);
}

string abi_record_type_probe_with_substitutions(TypePtr type,
                                                AbiSubstitutionContext& ctx,
                                                bool include_namespace)
{
	TypePtr bare = type.get() != NULL ? pa11::strip_cv(type) : TypePtr();
	if (bare.get() == NULL)
		return "v";
	string special = abi_std_abbreviation(bare, &ctx);
	string name = bare->is_template_specialization &&
	              !bare->template_primary_name.empty()
		? bare->template_primary_name : bare->name;
	size_t args = name.find('<');
	if (args != string::npos)
		name = name.substr(0, args);
	string leaf = special.empty() ? abi_source_name(name) : special;
	vector<Scope*> scopes;
	vector<string> named_scopes;
	string scope_prefix;
	if (special.empty() && include_namespace && bare->scope != NULL)
	{
		scopes = abi_scope_path_outer_first(bare->scope->parent);
		if (!scopes.empty() &&
		    !(scopes.size() == 1 && abi_scope_is_std_namespace(scopes[0])))
			scope_prefix =
				abi_scope_prefix_probe_with_substitutions(scopes, ctx);
	}
	else if (special.empty() && include_namespace && bare->scope == NULL)
		named_scopes = abi_qualified_type_scope_names(bare);
	if (bare->is_template_specialization &&
	    !abi_std_abbreviation_is_terminal(special))
	{
		leaf += "I";
		for (size_t i = 0; i < bare->template_arguments.size(); ++i)
			leaf += abi_template_instance_argument_probe_with_substitutions(
				bare->template_arguments[i], ctx);
		leaf += "E";
	}
	if (!special.empty())
		return leaf;
	if (!scopes.empty())
	{
		if (scopes.size() == 1 && abi_scope_is_std_namespace(scopes[0]))
			return "St" + leaf;
		return "N" + scope_prefix + leaf + "E";
	}
	if (!named_scopes.empty())
	{
		string named_prefix =
			abi_named_scope_prefix_probe_with_substitutions(named_scopes,
			                                               ctx);
		if (named_scopes.size() == 1 && named_scopes[0] == "std")
			return "St" + leaf;
		return "N" + named_prefix + leaf + "E";
	}
	return leaf;
}

string abi_type_probe_with_substitutions(TypePtr type,
                                         AbiSubstitutionContext& ctx)
{
	if (type.get() == NULL)
		return "v";
	if (type->is_dependent_typename)
		return abi_dependent_typename_type(type,
		                                   ctx.template_parameters,
		                                   ctx.expression_tokens,
		                                   !ctx.suppress_dependent_typename_marker);
	if (type->kind == pa11::TypeKind::Cv)
	{
		string quals;
		if ((type->cv & pa11::CV_CONST) != 0)
			quals += "K";
		if ((type->cv & pa11::CV_VOLATILE) != 0)
			quals += "V";
		return quals + abi_type_probe_with_substitutions(type->base, ctx);
	}
	if (type->kind == pa11::TypeKind::Pointer)
		return "P" + abi_type_probe_with_substitutions(type->base, ctx);
	if (type->kind == pa11::TypeKind::LValueReference)
		return "R" + abi_type_probe_with_substitutions(type->base, ctx);
	if (type->kind == pa11::TypeKind::RValueReference)
		return "O" + abi_type_probe_with_substitutions(type->base, ctx);
	if (type->kind == pa11::TypeKind::Array)
		return "A" + (type->unknown_bound ? string("") :
		       to_string(type->bound)) + "_" +
		       abi_type_probe_with_substitutions(type->base, ctx);
	if (type->kind == pa11::TypeKind::Function)
	{
		string out;
		if ((type->cv & pa11::CV_CONST) != 0)
			out += "K";
		if ((type->cv & pa11::CV_VOLATILE) != 0)
			out += "V";
		out += "F" + abi_type_probe_with_substitutions(type->base, ctx);
		for (size_t i = 0; i < type->parameters.size(); ++i)
			out += abi_type_probe_with_substitutions(type->parameters[i],
			                                        ctx);
		if (type->parameters.empty())
			out += "v";
		return out + "E";
	}
	if (type->kind == pa11::TypeKind::Record ||
	    type->kind == pa11::TypeKind::Enum)
		return abi_record_type_probe_with_substitutions(type, ctx, true);
	if (type->kind == pa11::TypeKind::TemplateParameter ||
	    type->kind == pa11::TypeKind::TemplateTemplateParameter)
	{
		map<string, size_t>::const_iterator found =
			ctx.template_parameters.find(type->name);
		size_t index = found == ctx.template_parameters.end() ? 0 : found->second;
		return index == 0 ? string("T_") :
		       string("T") + to_string(index - 1) + "_";
	}
	if (type->kind == pa11::TypeKind::MemberPointer)
		return "M" + abi_type_probe_with_substitutions(type->member_class,
		                                               ctx) +
		       abi_type_probe_with_substitutions(type->base, ctx);
	return abi_fundamental_type(type->fundamental);
}

}  // namespace internal
}  // namespace pa12
