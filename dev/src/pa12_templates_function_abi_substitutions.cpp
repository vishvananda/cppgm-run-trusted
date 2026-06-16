#include "pa12_templates_function_abi_internal.h"
#include "pa12_templates_instance_support.h"
#include "pa12_types_support.h"
#include <algorithm>
#include <stdexcept>
using namespace std;
namespace pa12 {
namespace internal {
string abi_base36_number(size_t value)
{
	static const char digits[] = "0123456789ABCDEFGHIJKLMNOPQRSTUVWXYZ";
	string encoded;
	do
	{
		encoded.insert(encoded.begin(), digits[value % 36]);
		value /= 36;
	}
	while (value != 0);
	return encoded;
}
string abi_substitution_code(size_t index)
{
	if (index == 0)
		return "S_";
	return "S" + abi_base36_number(index - 1) + "_";
}
size_t abi_find_substitution(const AbiSubstitutionContext& ctx,
                             const string& encoded)
{
	map<string, size_t>::const_iterator alias =
		ctx.substitution_aliases.find(encoded);
	if (alias != ctx.substitution_aliases.end())
		return alias->second;
	for (size_t i = 0; i < ctx.substitutions.size(); ++i)
		if (ctx.substitutions[i] == encoded)
			return i;
	return static_cast<size_t>(-1);
}
void abi_add_substitution_alias(AbiSubstitutionContext& ctx,
                                const string& alias,
                                const string& target)
{
	if (alias.empty() || alias == target)
		return;
	size_t found = abi_find_substitution(ctx, target);
	if (found == static_cast<size_t>(-1))
		return;
	ctx.substitution_aliases[alias] = found;
}
void abi_add_substitution(AbiSubstitutionContext& ctx, const string& encoded)
{
	if (encoded.empty() ||
	    abi_find_substitution(ctx, encoded) != static_cast<size_t>(-1))
		return;
	ctx.substitutions.push_back(encoded);
}
string abi_use_or_add_substitution(AbiSubstitutionContext& ctx,
                                   const string& encoded)
{
	size_t found = abi_find_substitution(ctx, encoded);
	if (found != static_cast<size_t>(-1))
		return abi_substitution_code(found);
	abi_add_substitution(ctx, encoded);
	return encoded;
}
string abi_type_probe_with_substitutions(TypePtr type,
                                         AbiSubstitutionContext& ctx);
string abi_use_or_add_type_substitution(AbiSubstitutionContext& ctx,
                                        TypePtr type,
                                        const string& encoded,
                                        const string& initial_probe)
{
	string out = abi_use_or_add_substitution(ctx, encoded);
	abi_add_substitution_alias(ctx, initial_probe, encoded);
	string substituted_probe = abi_type_probe_with_substitutions(type, ctx);
	abi_add_substitution_alias(ctx, substituted_probe, encoded);
	return out;
}
string abi_type_with_substitutions(TypePtr type,
                                   AbiSubstitutionContext& ctx);
string abi_type_probe_with_substitutions(TypePtr type,
                                         AbiSubstitutionContext& ctx);
bool abi_type_encoding_active(const AbiSubstitutionContext& ctx,
                              const void* key)
{
	return key != NULL &&
	       find(ctx.active_type_encodings.begin(),
	            ctx.active_type_encodings.end(),
	            key) != ctx.active_type_encodings.end();
}
struct AbiActiveTypeEncoding
{
	AbiSubstitutionContext& ctx;
	const void* key;
	bool pushed;
	AbiActiveTypeEncoding(AbiSubstitutionContext& context, const void* value)
		: ctx(context), key(value), pushed(false)
	{
		if (key != NULL)
		{
			ctx.active_type_encodings.push_back(key);
			pushed = true;
		}
	}
	~AbiActiveTypeEncoding()
	{
		if (pushed)
			ctx.active_type_encodings.pop_back();
	}
};
string abi_template_parameter_type_with_substitutions(
	const string& name,
	AbiSubstitutionContext& ctx)
{
	map<string, size_t>::const_iterator found =
		ctx.template_parameters.find(name);
	size_t index = found == ctx.template_parameters.end() ? 0 : found->second;
	if (ctx.use_actual_template_parameter_types &&
	    index < ctx.actual_template_arguments.size() &&
	    ctx.actual_template_arguments[index].kind == TemplateArgumentKind::Type)
	{
		map<string, size_t>::const_iterator existing =
			ctx.actual_template_parameter_substitutions.find(name);
		if (existing != ctx.actual_template_parameter_substitutions.end())
			return abi_substitution_code(existing->second);
		string encoded = abi_type_probe_with_substitutions(
			ctx.actual_template_arguments[index].type,
			ctx);
		size_t sub = ctx.substitutions.size();
		ctx.substitutions.push_back(encoded);
		ctx.actual_template_parameter_substitutions[name] = sub;
		return abi_substitution_code(sub);
	}
	string encoded = index == 0 ? string("T_") :
	                 string("T") + to_string(index - 1) + "_";
	if (ctx.force_template_parameter_spelling)
	{
		abi_add_substitution(ctx, encoded);
		return encoded;
	}
	return abi_use_or_add_substitution(ctx, encoded);
}
string abi_record_type_with_substitutions(TypePtr type,
                                          AbiSubstitutionContext& ctx,
                                          bool include_namespace);
string abi_record_type_probe_with_substitutions(TypePtr type,
                                                AbiSubstitutionContext& ctx,
                                                bool include_namespace);
string abi_scope_prefix_probe_with_substitutions(const vector<Scope*>& scopes,
                                                AbiSubstitutionContext& ctx);
	string abi_dependent_typename_type_with_substitutions(
		TypePtr type,
		AbiSubstitutionContext& ctx,
		bool include_typename_marker);
string abi_template_argument_with_substitutions(
	const TemplateArgument& arg,
	AbiSubstitutionContext& ctx);
	string abi_template_instance_argument_with_substitutions(
		const pa11::TemplateInstanceArgument& arg,
		AbiSubstitutionContext& ctx);
const pa11::TemplateInstanceArgument* abi_pack_expansion_element(
	const pa11::TemplateInstanceArgument& arg)
{
	if (arg.kind != pa11::TemplateInstanceArgumentKind::Pack ||
	    !arg.template_name.empty() ||
	    arg.pack.size() != 1)
		return NULL;
	const pa11::TemplateInstanceArgument* element = &arg.pack[0];
	while (element->kind == pa11::TemplateInstanceArgumentKind::Pack &&
	       element->template_name.empty() &&
	       element->pack.size() == 1)
		element = &element->pack[0];
	if (element->kind == pa11::TemplateInstanceArgumentKind::Type &&
	    element->type.get() != NULL)
	{
		TypePtr bare = pa11::strip_cv(element->type);
		if (bare->kind == pa11::TypeKind::TemplateParameter ||
		    bare->kind == pa11::TypeKind::TemplateTemplateParameter)
			return element;
	}
	if (element->kind == pa11::TemplateInstanceArgumentKind::Value &&
	    element->dependent &&
	    !element->value_name.empty())
		return element;
	if (element->kind == pa11::TemplateInstanceArgumentKind::Template &&
	    element->dependent)
		return element;
	return NULL;
}
	string abi_dependent_template_argument_type_with_substitutions(
		TypePtr type,
		AbiSubstitutionContext& ctx)
	{
		if (type.get() != NULL &&
		    type->is_dependent_typename &&
		    (type->dependent_typename_decltype ||
		     type->name.compare(0, 9, "decltype(") == 0))
			return abi_type_with_substitutions(type, ctx);
		return abi_use_or_add_substitution(
			ctx,
			abi_dependent_typename_type_with_substitutions(type, ctx, false));
	}
string abi_vendor_transform_type_argument_with_substitutions(
	TypePtr type,
	AbiSubstitutionContext& ctx)
{
	if (type.get() == NULL)
		return "v";
	TypePtr bare = pa11::strip_cv(type);
	if (type->kind == pa11::TypeKind::Cv)
	{
		string quals;
		if ((type->cv & pa11::CV_CONST) != 0)
			quals += "K";
		if ((type->cv & pa11::CV_VOLATILE) != 0)
			quals += "V";
		return quals + abi_vendor_transform_type_argument_with_substitutions(
			type->base, ctx);
	}
	if (bare->kind == pa11::TypeKind::TemplateParameter ||
	    bare->kind == pa11::TypeKind::TemplateTemplateParameter)
	{
		string encoded =
			abi_template_parameter_expression(bare->name,
			                                  ctx.template_parameters);
		if (!encoded.empty())
		{
			abi_add_substitution(ctx, encoded);
			return encoded;
		}
	}
	if (type->is_dependent_typename)
		return abi_dependent_typename_type_with_substitutions(type,
		                                                      ctx,
		                                                      false);
	if (type->kind == pa11::TypeKind::Pointer)
		return "P" + abi_vendor_transform_type_argument_with_substitutions(
			type->base, ctx);
	if (type->kind == pa11::TypeKind::LValueReference)
		return "R" + abi_vendor_transform_type_argument_with_substitutions(
			type->base, ctx);
	if (type->kind == pa11::TypeKind::RValueReference)
		return "O" + abi_vendor_transform_type_argument_with_substitutions(
			type->base, ctx);
	if (type->kind == pa11::TypeKind::Array)
		return "A" + (type->unknown_bound ? string("") :
		       to_string(type->bound)) + "_" +
		       abi_vendor_transform_type_argument_with_substitutions(
			       type->base, ctx);
	return abi_type_with_substitutions(type, ctx);
}
string abi_vendor_transform_instance_argument_with_substitutions(
	const pa11::TemplateInstanceArgument& arg,
	AbiSubstitutionContext& ctx)
{
	if (arg.kind == pa11::TemplateInstanceArgumentKind::Type)
		return abi_vendor_transform_type_argument_with_substitutions(
			arg.type, ctx);
	return abi_template_instance_argument_with_substitutions(arg, ctx);
}
string abi_dependent_typename_scope_prefix_with_substitutions(
	AbiSubstitutionContext& ctx)
{
	if (ctx.dependent_typename_scope_prefix.empty())
		return "";
	string raw_prefix;
	for (size_t i = 0; i < ctx.dependent_typename_scope_prefix.size(); ++i)
	{
		Scope* scope = ctx.dependent_typename_scope_prefix[i];
		if (scope == NULL)
			continue;
		if (abi_scope_is_std_namespace(scope))
			raw_prefix += "St";
		else if (scope->kind == ScopeKind::Namespace)
		{
			string name = scope->name == "<unnamed>"
				? string("_GLOBAL__N_1") : scope->name;
			raw_prefix += abi_source_name(name);
		}
	}
	string key = "N" + raw_prefix + "E";
	size_t found = abi_find_substitution(ctx, key);
	if (found != static_cast<size_t>(-1))
		return abi_substitution_code(found);
	return abi_scope_prefix_with_substitutions(
		ctx.dependent_typename_scope_prefix, ctx);
}
string abi_dependent_typename_type_with_substitutions(
	TypePtr type,
	AbiSubstitutionContext& ctx,
	bool include_typename_marker)
{
	vector<string> parts = abi_split_qualified_name(type->name);
	if (parts.empty())
		return abi_source_name(type->name);
	if (!type->dependent_typename_qualified &&
	    type->dependent_typename_template_id)
	{
		string root = type->template_primary_name.empty()
			? parts[0] : type->template_primary_name;
		size_t template_pos = root.find('<');
		if (template_pos != string::npos)
			root = root.substr(0, template_pos);
		if (internal_type_transform_name(root))
		{
			string out = include_typename_marker ? "Tn" : "";
			out += "u" + abi_source_name(root);
			vector<pa11::TemplateInstanceArgument> arguments;
			if (!type->dependent_typename_template_argument_lists.empty())
				arguments =
					type->dependent_typename_template_argument_lists[0];
			else
				arguments = type->template_arguments;
			if (!arguments.empty())
			{
				out += "I";
				for (size_t i = 0; i < arguments.size(); ++i)
					out +=
						abi_vendor_transform_instance_argument_with_substitutions(
						arguments[i], ctx);
				out += "E";
			}
			return out;
		}
	}
	if (!type->dependent_typename_qualified &&
	    type->dependent_typename_template_id)
	{
		string root = type->template_primary_name.empty()
			? parts[0] : type->template_primary_name;
		size_t template_pos = root.find('<');
		if (template_pos != string::npos)
			root = root.substr(0, template_pos);
		if (root == "enable_if_t")
		{
			vector<pa11::TemplateInstanceArgument> arguments;
			if (!type->dependent_typename_template_argument_lists.empty())
				arguments =
					type->dependent_typename_template_argument_lists[0];
			else
				arguments = type->template_arguments;
			string out = include_typename_marker ? "TnN" : "N";
			out += abi_source_name("enable_if");
			if (!arguments.empty())
			{
				out += "I";
				for (size_t i = 0; i < arguments.size(); ++i)
					out += abi_template_instance_argument_with_substitutions(
						arguments[i], ctx);
				out += "E";
			}
			out += abi_source_name("type") + "E";
			return out;
		}
	}
	if (!type->dependent_typename_qualified &&
	    type->dependent_typename_template_id)
	{
		string root = type->template_primary_name.empty()
			? parts[0] : type->template_primary_name;
		size_t template_pos = root.find('<');
		if (template_pos != string::npos)
			root = root.substr(0, template_pos);
		string parameter = abi_template_parameter_expression(
			root, ctx.template_parameters);
		if (!parameter.empty())
		{
			string out = parameter;
			vector<pa11::TemplateInstanceArgument> arguments;
			if (!type->dependent_typename_template_argument_lists.empty())
				arguments =
					type->dependent_typename_template_argument_lists[0];
			else
				arguments = type->template_arguments;
			if (!arguments.empty())
			{
				out += "I";
				for (size_t i = 0; i < arguments.size(); ++i)
					out += abi_template_instance_argument_with_substitutions(
						arguments[i], ctx);
				out += "E";
			}
			return out;
		}
	}
	string out;
	string root_part = parts[0];
	bool unqualified_template_root =
		root_part.find('<') != string::npos &&
		type->template_primary_name.find("::") == string::npos;
	string root_template_name = root_part;
	size_t root_template_pos = root_template_name.find('<');
	if (root_template_pos != string::npos)
		root_template_name = root_template_name.substr(0, root_template_pos);
	bool suppress_context_scope_prefix =
		unqualified_template_root && root_template_name == "enable_if";
	bool prefix_with_context_scope =
		!ctx.dependent_typename_scope_prefix.empty() &&
		(!type->dependent_typename_qualified || unqualified_template_root) &&
		!suppress_context_scope_prefix;
	if (type->dependent_typename_qualified || prefix_with_context_scope)
		out = include_typename_marker ? "TnN" : "N";
	else
		out = include_typename_marker ? "Tn" : "";
	if (prefix_with_context_scope)
		out += abi_dependent_typename_scope_prefix_with_substitutions(ctx);
	size_t list_index = 0;
	size_t implicit_template_part_index =
		type->dependent_typename_qualified && parts.size() > 1
		? parts.size() - 2
		: 0;
	if (type->dependent_typename_template_id &&
	    !type->template_primary_name.empty())
	{
		vector<string> primary_parts =
			abi_split_qualified_name(type->template_primary_name);
		string primary_leaf = primary_parts.empty()
			? type->template_primary_name
			: primary_parts[primary_parts.size() - 1];
		size_t primary_template_pos = primary_leaf.find('<');
		if (primary_template_pos != string::npos)
			primary_leaf = primary_leaf.substr(0, primary_template_pos);
		size_t matched_part = implicit_template_part_index;
		bool matched_primary = false;
		for (size_t j = 0; j < parts.size(); ++j)
		{
			string part_leaf = parts[j];
			size_t part_template_pos = part_leaf.find('<');
			if (part_template_pos != string::npos)
				part_leaf = part_leaf.substr(0, part_template_pos);
			if (part_leaf == primary_leaf)
			{
				matched_part = j;
				matched_primary = true;
			}
		}
		bool first_qualified_scope =
			matched_part == 0 &&
			type->dependent_typename_qualified &&
			parts.size() > 1 &&
			parts[0].find('<') == string::npos;
		if (matched_primary && !first_qualified_scope)
			implicit_template_part_index = matched_part;
	}
	for (size_t i = 0; i < parts.size(); ++i)
	{
		string part = parts[i];
		size_t template_pos = part.find('<');
		bool has_template_id = template_pos != string::npos;
		bool implicit_template_id =
			!has_template_id &&
			i == implicit_template_part_index &&
			type->dependent_typename_template_id &&
			(!type->template_arguments.empty() ||
			 !type->dependent_typename_template_argument_lists.empty());
		if (has_template_id)
			part = part.substr(0, template_pos);
		string source = abi_source_name(part);
		if (has_template_id || implicit_template_id)
		{
			size_t source_sub = abi_find_substitution(ctx, source);
			if (source_sub != static_cast<size_t>(-1))
				source = abi_substitution_code(source_sub);
			else
				abi_add_substitution(ctx, source);
		}
		out += source;
		vector<pa11::TemplateInstanceArgument> arguments;
		if ((has_template_id || implicit_template_id) &&
		    list_index <
			    type->dependent_typename_template_argument_lists.size())
			arguments =
				type->dependent_typename_template_argument_lists[list_index++];
		else if ((has_template_id || implicit_template_id) &&
		         i == implicit_template_part_index &&
		         !type->template_arguments.empty())
			arguments = type->template_arguments;
		if (!arguments.empty())
		{
			out += "I";
			for (size_t j = 0; j < arguments.size(); ++j)
				out += abi_template_instance_argument_with_substitutions(
					arguments[j],
					ctx);
			out += "E";
		}
	}
	if (type->dependent_typename_qualified || prefix_with_context_scope)
		out += "E";
	return out;
}
bool abi_scope_is_std_namespace(Scope* scope)
{
	return scope != NULL &&
	       scope->kind == ScopeKind::Namespace &&
	       scope->name == "std";
}
bool abi_record_in_std_namespace(TypePtr type)
{
	TypePtr bare = type.get() != NULL ? pa11::strip_cv(type) : TypePtr();
	if (bare.get() == NULL || bare->scope == NULL)
		return false;
	for (Scope* scope = bare->scope->parent; scope != NULL;
	     scope = scope->parent)
	{
		if (abi_scope_is_std_namespace(scope))
			return true;
		if (scope->kind == ScopeKind::Class)
			return false;
	}
	return false;
}
bool abi_record_directly_in_std_namespace(TypePtr type)
{
	TypePtr bare = type.get() != NULL ? pa11::strip_cv(type) : TypePtr();
	return bare.get() != NULL &&
	       bare->scope != NULL &&
	       bare->scope->parent != NULL &&
	       abi_scope_is_std_namespace(bare->scope->parent);
}
TypePtr abi_resolve_template_parameter_argument_type(TypePtr type,
                                                     AbiSubstitutionContext* ctx)
{
	TypePtr bare = type.get() != NULL ? pa11::strip_cv(type) : TypePtr();
	if (bare.get() == NULL ||
	    ctx == NULL ||
	    !ctx->use_actual_template_parameter_types ||
	    (bare->kind != pa11::TypeKind::TemplateParameter &&
	     bare->kind != pa11::TypeKind::TemplateTemplateParameter))
		return bare;
	map<string, size_t>::const_iterator found =
		ctx->template_parameters.find(bare->name);
	if (found == ctx->template_parameters.end() ||
	    found->second >= ctx->actual_template_arguments.size() ||
	    ctx->actual_template_arguments[found->second].kind !=
		    TemplateArgumentKind::Type)
		return bare;
	return pa11::strip_cv(ctx->actual_template_arguments[found->second].type);
}
bool abi_template_argument_is_fundamental(
	const pa11::TemplateInstanceArgument& arg,
	EFundamentalType fundamental,
	AbiSubstitutionContext* ctx)
{
	TypePtr type = arg.kind == pa11::TemplateInstanceArgumentKind::Type
		? pa11::strip_cv(arg.type) : TypePtr();
	type = abi_resolve_template_parameter_argument_type(type, ctx);
	return type.get() != NULL &&
	       type->kind == pa11::TypeKind::Fundamental &&
	       type->fundamental == fundamental;
}
bool abi_template_argument_is_std_unary_type_template(
	const pa11::TemplateInstanceArgument& arg,
	const string& primary,
	EFundamentalType parameter,
	AbiSubstitutionContext* ctx)
{
	TypePtr type = arg.kind == pa11::TemplateInstanceArgumentKind::Type
		? pa11::strip_cv(arg.type) : TypePtr();
	type = abi_resolve_template_parameter_argument_type(type, ctx);
	if (type.get() == NULL ||
	    !type->is_template_specialization ||
	    !abi_record_directly_in_std_namespace(type))
		return false;
	string name = !type->template_primary_name.empty()
		? type->template_primary_name : type->name;
	size_t args = name.find('<');
	if (args != string::npos)
		name = name.substr(0, args);
	return name == primary &&
	       type->template_arguments.size() == 1 &&
	       abi_template_argument_is_fundamental(
		       type->template_arguments[0], parameter, ctx);
}
bool abi_template_argument_is_char_traits_char(
	const pa11::TemplateInstanceArgument& arg,
	AbiSubstitutionContext* ctx)
{
	return abi_template_argument_is_std_unary_type_template(
		arg, "char_traits", FT_CHAR, ctx);
}
bool abi_template_argument_is_allocator_char(
	const pa11::TemplateInstanceArgument& arg,
	AbiSubstitutionContext* ctx)
{
	return abi_template_argument_is_std_unary_type_template(
		arg, "allocator", FT_CHAR, ctx);
}
bool abi_std_abbreviation_is_terminal(const string& abbreviation)
{
	return abbreviation == "Ss" ||
	       abbreviation == "Si" ||
	       abbreviation == "So" ||
	       abbreviation == "Sd";
}
string abi_std_abbreviation(TypePtr type, AbiSubstitutionContext* ctx = NULL)
{
	TypePtr bare = type.get() != NULL ? pa11::strip_cv(type) : TypePtr();
	if (bare.get() == NULL || !abi_record_in_std_namespace(bare))
		return "";
	bool directly_in_std = abi_record_directly_in_std_namespace(bare);
	string name = bare->is_template_specialization &&
	              !bare->template_primary_name.empty()
		? bare->template_primary_name : bare->name;
	size_t args = name.find('<');
	if (args != string::npos)
		name = name.substr(0, args);
	if (directly_in_std && name == "allocator")
		return "Sa";
	if (!directly_in_std || !bare->is_template_specialization)
		return "";
	if ((name == "basic_istream" ||
	     name == "basic_ostream" ||
	     name == "basic_iostream") &&
	    bare->template_arguments.size() == 2 &&
	    abi_template_argument_is_fundamental(
		    bare->template_arguments[0], FT_CHAR, ctx) &&
	    abi_template_argument_is_char_traits_char(
		    bare->template_arguments[1], ctx))
	{
		if (name == "basic_istream")
			return "Si";
		if (name == "basic_ostream")
			return "So";
		return "Sd";
	}
	if (name == "basic_string" &&
	    bare->template_arguments.size() == 3 &&
	    abi_template_argument_is_fundamental(
		    bare->template_arguments[0], FT_CHAR, ctx) &&
	    abi_template_argument_is_char_traits_char(
		    bare->template_arguments[1], ctx) &&
	    abi_template_argument_is_allocator_char(
		    bare->template_arguments[2], ctx))
		return "Ss";
	if (name == "basic_string")
		return "Sb";
	return "";
}
string abi_record_unscoped_with_substitutions(TypePtr type,
                                              AbiSubstitutionContext& ctx)
{
	TypePtr bare = type.get() != NULL ? pa11::strip_cv(type) : TypePtr();
	if (bare.get() == NULL)
		return abi_source_name("v");
	string special = abi_std_abbreviation(bare, &ctx);
	string name = bare->is_template_specialization &&
	              !bare->template_primary_name.empty()
		? bare->template_primary_name : bare->name;
	size_t args = name.find('<');
	if (args != string::npos)
		name = name.substr(0, args);
	string primary = special.empty() ? abi_source_name(name) : special;
	string out = primary;
	if (bare->is_template_specialization &&
	    !abi_std_abbreviation_is_terminal(special))
	{
		if (special.empty())
		{
			size_t primary_sub = abi_find_substitution(ctx, primary);
			if (primary_sub != static_cast<size_t>(-1))
				out = abi_substitution_code(primary_sub);
			else
				abi_add_substitution(ctx, primary);
		}
		out += "I";
		for (size_t i = 0; i < bare->template_arguments.size(); ++i)
			out += abi_template_instance_argument_with_substitutions(
				bare->template_arguments[i], ctx);
		out += "E";
	}
	return out;
}
vector<Scope*> abi_scope_path_outer_first(Scope* scope)
{
	vector<Scope*> reversed;
	for (Scope* cur = scope; cur != NULL; cur = cur->parent)
	{
		if (cur->kind == ScopeKind::Namespace && !cur->name.empty())
			reversed.push_back(cur);
		else if (cur->kind == ScopeKind::Class &&
		         !cur->name.empty() &&
		         cur->name != "<unnamed>")
			reversed.push_back(cur);
	}
	return vector<Scope*>(reversed.rbegin(), reversed.rend());
}
string abi_scope_component_with_substitutions(Scope* scope,
                                             AbiSubstitutionContext& ctx)
{
	if (scope->kind == ScopeKind::Namespace)
	{
		if (scope->name == "std")
			return "St";
		string name = scope->name == "<unnamed>"
			? string("_GLOBAL__N_1") : scope->name;
		return abi_source_name(name);
	}
	if (scope->kind == ScopeKind::Class)
	{
		TypePtr record = pa11::record_type_for_scope(scope);
		return abi_record_unscoped_with_substitutions(record, ctx);
	}
	return "";
}
string abi_scope_prefix_with_substitutions(const vector<Scope*>& scopes,
                                          AbiSubstitutionContext& ctx)
{
	string raw_prefix;
	bool namespace_only = true;
	for (size_t i = 0; i < scopes.size(); ++i)
	{
		if (scopes[i]->kind != ScopeKind::Namespace)
		{
			namespace_only = false;
			break;
		}
		if (scopes[i]->name == "std")
			raw_prefix += "St";
		else if (!scopes[i]->name.empty())
		{
			string name = scopes[i]->name == "<unnamed>"
				? string("_GLOBAL__N_1") : scopes[i]->name;
			raw_prefix += abi_source_name(name);
		}
	}
	if (namespace_only && !raw_prefix.empty())
	{
		size_t full = abi_find_substitution(ctx, "N" + raw_prefix + "E");
		if (full != static_cast<size_t>(-1))
			return abi_substitution_code(full);
	}
	string out;
	string prefix_key;
	string prefix_text;
	for (size_t i = 0; i < scopes.size(); ++i)
	{
		string component = abi_scope_component_with_substitutions(scopes[i],
		                                                         ctx);
		if (component.empty())
			continue;
		bool terminal_standard =
			abi_std_abbreviation_is_terminal(component);
		if (terminal_standard && prefix_key == "St")
		{
			if (out.size() >= 2 && out.compare(out.size() - 2, 2, "St") == 0)
				out.resize(out.size() - 2);
			prefix_key.clear();
			prefix_text.clear();
		}
		string key = prefix_key.empty()
			? component : string("N") + prefix_text + component + "E";
		if (prefix_key == "St" && scopes[i]->kind == ScopeKind::Class)
			key = "St" + component;
		if (component == "St")
		{
			out += component;
			prefix_key = key;
			prefix_text += component;
			continue;
		}
		size_t found = terminal_standard ? static_cast<size_t>(-1) :
			abi_find_substitution(ctx, key);
		if (found != static_cast<size_t>(-1))
			out += abi_substitution_code(found);
		else
		{
			out += component;
			if (!terminal_standard)
				abi_add_substitution(ctx, key);
			if (!terminal_standard &&
			    scopes[i]->kind == ScopeKind::Class &&
			    prefix_key == "St")
				abi_add_substitution_alias(ctx, "St" + component, key);
		}
		prefix_key = key;
		prefix_text += component;
	}
	return out;
}
string abi_namespace_scope_prefix_key(const vector<Scope*>& scopes)
{
	string key;
	for (size_t i = 0; i < scopes.size(); ++i)
	{
		if (scopes[i]->kind != ScopeKind::Namespace)
			return "";
		if (scopes[i]->name.empty())
			continue;
		string name = scopes[i]->name == "<unnamed>"
			? string("_GLOBAL__N_1") : scopes[i]->name;
		string component = name == "std" ? string("St") : abi_source_name(name);
		key = key.empty() ? component : string("N") + key + component + "E";
	}
	return key;
}
void abi_alias_function_template_argument_scope(
	AbiSubstitutionContext& ctx,
	const vector<Scope*>& scopes,
	const string& encoded)
{
	if (!ctx.function_template_argument_list ||
	    scopes.size() != 1 ||
	    abi_scope_is_std_namespace(scopes[0]))
		return;
	string key = abi_namespace_scope_prefix_key(scopes);
	if (key.empty())
		return;
	size_t found = abi_find_substitution(ctx, key);
	if (found != static_cast<size_t>(-1) &&
	    found < ctx.function_template_argument_substitution_floor)
		return;
	abi_add_substitution_alias(ctx, key, encoded);
}
string abi_record_type_with_substitutions(TypePtr type,
                                          AbiSubstitutionContext& ctx,
                                          bool include_namespace)
{
	TypePtr bare = type.get() != NULL ? pa11::strip_cv(type) : TypePtr();
	if (bare.get() == NULL)
		return "v";
	string special = abi_std_abbreviation(bare, &ctx);
	if (!special.empty())
	{
		string encoded = abi_record_unscoped_with_substitutions(bare, ctx);
		return abi_std_abbreviation_is_terminal(special)
			? encoded : abi_use_or_add_substitution(ctx, encoded);
	}
	vector<Scope*> scopes;
	vector<string> named_scopes;
	string scope_prefix;
	if (include_namespace && bare->scope != NULL)
	{
		scopes = abi_scope_path_outer_first(bare->scope->parent);
		if (!scopes.empty() &&
		    !(scopes.size() == 1 && abi_scope_is_std_namespace(scopes[0])))
			scope_prefix = abi_scope_prefix_with_substitutions(scopes, ctx);
	}
	else if (include_namespace && bare->scope == NULL)
		named_scopes = abi_qualified_type_scope_names(bare);
	if (bare->is_template_specialization && !scopes.empty() &&
	    !(scopes.size() == 1 && abi_scope_is_std_namespace(scopes[0])))
	{
		string name = !bare->template_primary_name.empty()
			? bare->template_primary_name : bare->name;
		size_t pos = name.find('<');
		if (pos != string::npos)
			name = name.substr(0, pos);
		string source = abi_source_name(name);
		string qualified_prefix = "N" + scope_prefix + source + "E";
		size_t prefix_sub = abi_find_substitution(ctx, qualified_prefix);
		if (prefix_sub == static_cast<size_t>(-1))
			abi_add_substitution(ctx, qualified_prefix);
		abi_add_substitution_alias(
			ctx,
			"N" + abi_scope_prefix_probe_with_substitutions(scopes, ctx) +
				source + "E",
			qualified_prefix);
		string args = "I";
		for (size_t i = 0; i < bare->template_arguments.size(); ++i)
			args += abi_template_instance_argument_with_substitutions(
				bare->template_arguments[i], ctx);
		args += "E";
		string encoded = prefix_sub == static_cast<size_t>(-1)
			? "N" + scope_prefix + source + args + "E"
			: "N" + abi_substitution_code(prefix_sub) + args + "E";
		string result = abi_use_or_add_substitution(ctx, encoded);
		abi_add_substitution_alias(
			ctx,
			abi_record_type_probe_with_substitutions(bare,
			                                         ctx,
			                                         include_namespace),
			encoded);
		abi_alias_function_template_argument_scope(ctx, scopes, encoded);
		return result;
	}
	string leaf = abi_record_unscoped_with_substitutions(bare, ctx);
	string encoded = leaf;
	if (!scopes.empty())
	{
		if (scopes.size() == 1 && abi_scope_is_std_namespace(scopes[0]))
			encoded = "St" + leaf;
		else
			encoded = "N" + scope_prefix + leaf + "E";
	}
	else if (!named_scopes.empty())
	{
		string named_prefix =
			abi_named_scope_prefix_with_substitutions(named_scopes, ctx);
		encoded = named_scopes.size() == 1 && named_scopes[0] == "std"
			? "St" + leaf : "N" + named_prefix + leaf + "E";
	}
	else if (include_namespace &&
	         bare->is_template_specialization &&
	         bare->scope == NULL &&
	         bare->template_primary_name.find("::") == string::npos &&
	         !ctx.dependent_typename_scope_prefix.empty())
	{
		encoded = "N" +
		          abi_dependent_typename_scope_prefix_with_substitutions(ctx) +
		          leaf + "E";
	}
	string result = abi_use_or_add_substitution(ctx, encoded);
	abi_add_substitution_alias(
		ctx,
		abi_record_type_probe_with_substitutions(bare, ctx, include_namespace),
		encoded);
	abi_alias_function_template_argument_scope(ctx, scopes, encoded);
	return result;
}
string abi_template_instance_argument_with_substitutions(
	const pa11::TemplateInstanceArgument& arg,
	AbiSubstitutionContext& ctx)
{
	if (arg.kind == pa11::TemplateInstanceArgumentKind::Type)
		return abi_type_with_substitutions(arg.type, ctx);
	if (arg.kind == pa11::TemplateInstanceArgumentKind::Value)
	{
		if (arg.dependent)
		{
			if (!arg.value_owner_template_name.empty() &&
			    !arg.value_member_name.empty())
			{
				string owner_name = arg.value_owner_template_name;
				size_t owner_args = owner_name.find('<');
				if (owner_args != string::npos)
					owner_name = owner_name.substr(0, owner_args);
				string owner = abi_unresolved_name_path(owner_name);
				if (!ctx.function_template_argument_list)
					abi_add_substitution(ctx, owner);
				string out = "Xsr" + owner;
				bool owner_has_dependent_typename_argument = false;
				if (!arg.value_owner_template_arguments.empty())
				{
					out += "I";
					for (size_t i = 0;
					     i < arg.value_owner_template_arguments.size();
					     ++i)
					{
						const pa11::TemplateInstanceArgument& owner_arg =
							arg.value_owner_template_arguments[i];
						if (owner_arg.kind ==
						        pa11::TemplateInstanceArgumentKind::Type &&
						    owner_arg.type.get() != NULL &&
						    owner_arg.type->is_dependent_typename)
						{
							owner_has_dependent_typename_argument = true;
								out +=
									abi_dependent_template_argument_type_with_substitutions(
										owner_arg.type, ctx);
						}
						else
							out += abi_template_instance_argument_with_substitutions(
								owner_arg, ctx);
					}
					out += "E";
					out += "E";
				}
				out += abi_source_name(arg.value_member_name) + "E";
				if (arg.value_negated)
					out = "Xnt" + out.substr(1);
				if (ctx.function_template_argument_list &&
				    owner_has_dependent_typename_argument)
					abi_add_substitution(ctx, owner);
				if (owner_has_dependent_typename_argument)
					abi_add_substitution(ctx, out);
				return out;
			}
			if (ctx.expression_tokens != NULL &&
			    arg.value_expr_end > arg.value_expr_begin)
			{
				string expression = abi_template_value_expression(
					*ctx.expression_tokens,
					arg.value_expr_begin,
					arg.value_expr_end,
					ctx.template_parameters);
				if (!expression.empty())
					return "X" + expression + "E";
			}
			if (!arg.value_name.empty())
			{
				string parameter_expr =
					abi_template_parameter_expression(
						arg.value_name,
						ctx.template_parameters);
				if (!parameter_expr.empty())
					return "X" + parameter_expr + "E";
			}
		}
		if (!arg.value_name.empty())
			return "L" + abi_type_with_substitutions(arg.type, ctx) +
			       abi_encoded_stable_value_name(arg.value_name) + "E";
		if (abi_type_is_dependent_parameter(arg.type))
			return "Li" + to_string(arg.value) + "E";
		return "L" + abi_type_with_substitutions(arg.type, ctx) +
		       to_string(arg.value) + "E";
	}
	if (arg.kind == pa11::TemplateInstanceArgumentKind::Pack)
	{
		const pa11::TemplateInstanceArgument* expansion =
			abi_pack_expansion_element(arg);
		if (expansion != NULL)
			return "Dp" +
			       abi_template_instance_argument_with_substitutions(
				       *expansion, ctx);
		string out = "J";
		for (size_t i = 0; i < arg.pack.size(); ++i)
			out += abi_template_instance_argument_with_substitutions(
				arg.pack[i], ctx);
		out += "E";
		return out;
	}
	return abi_template_name(arg.template_name);
}
string abi_template_argument_with_substitutions(
	const TemplateArgument& arg,
	AbiSubstitutionContext& ctx)
{
	if (arg.kind == TemplateArgumentKind::Type)
		return abi_type_with_substitutions(arg.type, ctx);
	if (arg.kind == TemplateArgumentKind::Value)
	{
		if (arg.dependent)
		{
			if (!arg.value_owner_template_name.empty() &&
			    !arg.value_member_name.empty())
			{
				string owner_name = arg.value_owner_template_name;
				size_t owner_args = owner_name.find('<');
				if (owner_args != string::npos)
					owner_name = owner_name.substr(0, owner_args);
				string owner = abi_unresolved_name_path(owner_name);
				if (!ctx.function_template_argument_list)
					abi_add_substitution(ctx, owner);
				string out = "Xsr" + owner;
				bool owner_has_dependent_typename_argument = false;
				if (!arg.value_owner_template_arguments.empty())
				{
					out += "I";
					for (size_t i = 0;
					     i < arg.value_owner_template_arguments.size();
					     ++i)
					{
						const pa11::TemplateInstanceArgument& owner_arg =
							arg.value_owner_template_arguments[i];
						if (owner_arg.kind ==
						        pa11::TemplateInstanceArgumentKind::Type &&
						    owner_arg.type.get() != NULL &&
						    owner_arg.type->is_dependent_typename)
						{
							owner_has_dependent_typename_argument = true;
								out +=
									abi_dependent_template_argument_type_with_substitutions(
										owner_arg.type, ctx);
						}
						else
							out += abi_template_instance_argument_with_substitutions(
								owner_arg, ctx);
					}
					out += "E";
					out += "E";
				}
				out += abi_source_name(arg.value_member_name) + "E";
				if (arg.value_negated)
					out = "Xnt" + out.substr(1);
				if (ctx.function_template_argument_list &&
				    owner_has_dependent_typename_argument)
					abi_add_substitution(ctx, owner);
				if (owner_has_dependent_typename_argument)
					abi_add_substitution(ctx, out);
				return out;
			}
			if (ctx.expression_tokens != NULL &&
			    arg.value_expr_end > arg.value_expr_begin)
			{
				string expression = abi_template_value_expression(
					*ctx.expression_tokens,
					arg.value_expr_begin,
					arg.value_expr_end,
					ctx.template_parameters);
				if (!expression.empty())
					return "X" + expression + "E";
			}
			if (!arg.value_name.empty())
			{
				string parameter_expr =
					abi_template_parameter_expression(
						arg.value_name,
						ctx.template_parameters);
				if (!parameter_expr.empty())
					return "X" + parameter_expr + "E";
				return "X" + abi_encoded_stable_value_name(arg.value_name) +
				       "E";
			}
		}
		if (arg.value_binding != NULL)
			return "XadL" +
			       abi_binding_symbol_with_substitutions(
				       arg.value_binding,
				       ctx.template_parameters) +
			       "E";
		if (abi_type_is_dependent_parameter(arg.type))
			return "Li" + to_string(arg.value) + "E";
		return "L" + abi_type_with_substitutions(arg.type, ctx) +
		       to_string(arg.value) + "E";
	}
	if (arg.kind == TemplateArgumentKind::Pack)
	{
		string out = "J";
		for (size_t i = 0; i < arg.pack.size(); ++i)
			out += abi_template_argument_with_substitutions(arg.pack[i],
			                                               ctx);
		out += "E";
		return out;
	}
	string name = arg.template_declaration != NULL
		? qualified_template_declaration_name(arg.template_declaration)
		: !arg.value_name.empty()
		  ? arg.value_name
		  : string("v");
	return abi_template_name(name);
}
string abi_template_argument_for_parameter_with_substitutions(
	const TemplateParameterInfo& parameter,
	const TemplateArgument& arg,
	AbiSubstitutionContext& ctx)
{
	if (parameter.kind == TemplateParameterKind::NonType &&
	    parameter.type.get() != NULL &&
	    abi_type_is_dependent_parameter(parameter.type))
	{
		if (arg.kind == TemplateArgumentKind::Value)
			return abi_type_with_substitutions(parameter.type, ctx) +
			       abi_template_argument_with_substitutions(arg, ctx);
		if (arg.kind == TemplateArgumentKind::Pack)
		{
			string out = "J";
			for (size_t i = 0; i < arg.pack.size(); ++i)
			{
				if (arg.pack[i].kind == TemplateArgumentKind::Value)
					out += abi_type_with_substitutions(
						       parameter.type, ctx) +
					       abi_template_argument_with_substitutions(
						       arg.pack[i], ctx);
				else
					out += abi_template_argument_with_substitutions(
						arg.pack[i], ctx);
			}
			out += "E";
			return out;
		}
	}
	return abi_template_argument_with_substitutions(arg, ctx);
}
string abi_type_with_substitutions(TypePtr type,
                                   AbiSubstitutionContext& ctx)
{
	if (type.get() == NULL)
		return "v";
	if (abi_type_encoding_active(ctx, type.get()))
		return abi_type_probe_with_substitutions(type, ctx);
	AbiActiveTypeEncoding active_type(ctx, type.get());
	if (ctx.force_template_parameter_spelling)
	{
		TypePtr bare_force = pa11::strip_cv(type);
		if (bare_force->kind == pa11::TypeKind::TemplateParameter ||
		    bare_force->kind == pa11::TypeKind::TemplateTemplateParameter)
			return abi_template_parameter_type_with_substitutions(
				bare_force->name, ctx);
	}
	string probe = abi_type_probe_with_substitutions(type, ctx);
	size_t whole = abi_find_substitution(ctx, probe);
	if (whole != static_cast<size_t>(-1))
		return abi_substitution_code(whole);
	if (type->is_dependent_typename)
	{
		string decltype_type =
			abi_dependent_decltype_type_with_substitutions(type, ctx);
		if (!decltype_type.empty())
			return abi_use_or_add_substitution(ctx, decltype_type);
		return abi_use_or_add_substitution(
			ctx,
			abi_dependent_typename_type_with_substitutions(
				type,
				ctx,
				!ctx.suppress_dependent_typename_marker));
	}
	if (type->kind == pa11::TypeKind::Cv)
	{
		string quals;
		if ((type->cv & pa11::CV_CONST) != 0)
			quals += "K";
		if ((type->cv & pa11::CV_VOLATILE) != 0)
			quals += "V";
		return abi_use_or_add_type_substitution(
			ctx,
			type,
			quals + abi_type_with_substitutions(type->base, ctx),
			probe);
	}
	if (type->kind == pa11::TypeKind::Pointer)
		return abi_use_or_add_type_substitution(
			ctx,
			type,
			"P" + abi_type_with_substitutions(type->base, ctx),
			probe);
	if (type->kind == pa11::TypeKind::LValueReference)
		return abi_use_or_add_type_substitution(
			ctx,
			type,
			"R" + abi_type_with_substitutions(type->base, ctx),
			probe);
	if (type->kind == pa11::TypeKind::RValueReference)
		return abi_use_or_add_type_substitution(
			ctx,
			type,
			"O" + abi_type_with_substitutions(type->base, ctx),
			probe);
	if (type->kind == pa11::TypeKind::Array)
		return abi_use_or_add_type_substitution(
			ctx,
			type,
			"A" + (type->unknown_bound ? string("") :
			       to_string(type->bound)) + "_" +
			abi_type_with_substitutions(type->base, ctx),
			probe);
	if (type->kind == pa11::TypeKind::Function)
	{
		string out;
		if ((type->cv & pa11::CV_CONST) != 0)
			out += "K";
		if ((type->cv & pa11::CV_VOLATILE) != 0)
			out += "V";
		out += "F" + abi_type_with_substitutions(type->base, ctx);
		for (size_t i = 0; i < type->parameters.size(); ++i)
			out += abi_type_with_substitutions(type->parameters[i], ctx);
		if (type->parameters.empty())
			out += "v";
		out += "E";
		return abi_use_or_add_type_substitution(ctx, type, out, probe);
	}
	if (type->kind == pa11::TypeKind::Record ||
	    type->kind == pa11::TypeKind::Enum)
		return abi_record_type_with_substitutions(type, ctx, true);
	if (type->kind == pa11::TypeKind::TemplateParameter ||
	    type->kind == pa11::TypeKind::TemplateTemplateParameter)
		return abi_template_parameter_type_with_substitutions(type->name,
		                                                      ctx);
	if (type->kind == pa11::TypeKind::MemberPointer)
	{
		string semantic_key =
			abi_type(type, ctx.template_parameters, ctx.expression_tokens);
		map<string, size_t>::const_iterator semantic =
			ctx.semantic_type_substitutions.find(semantic_key);
		if (semantic != ctx.semantic_type_substitutions.end())
			return abi_substitution_code(semantic->second);
		string member_class =
			abi_type_with_substitutions(type->member_class, ctx);
		string member_type = abi_type_with_substitutions(type->base, ctx);
		string encoded = "M" + member_class + member_type;
		string out = abi_use_or_add_substitution(ctx, encoded);
		size_t index = abi_find_substitution(ctx, encoded);
		if (index != static_cast<size_t>(-1))
			ctx.semantic_type_substitutions[semantic_key] = index;
		return out;
	}
	return abi_fundamental_type(type->fundamental);
}
string abi_function_return_type_with_substitutions(
	TypePtr type,
	AbiSubstitutionContext& ctx)
{
	if (type.get() != NULL && type->is_dependent_typename)
	{
			string decltype_type =
				abi_dependent_decltype_type_with_substitutions(type, ctx);
			if (!decltype_type.empty())
			{
				if (!type->template_primary_name.empty() ||
				    !type->template_arguments.empty())
					return abi_use_or_add_substitution(ctx,
					                                   decltype_type);
				abi_add_substitution(ctx, decltype_type);
				return decltype_type;
			}
		bool saved = ctx.use_actual_template_parameter_types;
		ctx.use_actual_template_parameter_types = true;
		string encoded =
			abi_dependent_typename_type_with_substitutions(type, ctx, false);
		ctx.use_actual_template_parameter_types = saved;
		return encoded;
	}
	return abi_type_with_substitutions(type, ctx);
}
string abi_function_parameter_type_with_substitutions(
	TypePtr type,
	AbiSubstitutionContext& ctx)
{
	bool saved = ctx.suppress_dependent_typename_marker;
	ctx.suppress_dependent_typename_marker = true;
	TypePtr encoded_type = pa11::is_reference_type(type)
		? type : pa11::strip_top_level_cv(type);
	string out = abi_type_with_substitutions(encoded_type, ctx);
	ctx.suppress_dependent_typename_marker = saved;
	return out;
}
}  // namespace internal
}  // namespace pa12
