#include "pa12_internal.h"
#include "pa12_templates_function_support.h"

using namespace std;

namespace pa12 {
namespace internal {
namespace {

string template_primary(TypePtr type)
{
	TypePtr bare = type.get() != NULL ? pa11::strip_cv(type) : TypePtr();
	if (bare.get() == NULL)
		return "";
	string primary = bare->template_primary_name.empty()
		? bare->name : bare->template_primary_name;
	size_t args = primary.find('<');
	if (args != string::npos)
		primary = primary.substr(0, args);
	size_t scope = primary.rfind("::");
	if (scope != string::npos)
		primary = primary.substr(scope + 2);
	return primary;
}

bool hosted_character_type(TypePtr type)
{
	TypePtr bare = type.get() != NULL ? pa11::strip_cv(type) : TypePtr();
	if (bare.get() == NULL || bare->kind != pa11::TypeKind::Fundamental)
		return false;
	return bare->fundamental == FT_CHAR ||
	       bare->fundamental == FT_SIGNED_CHAR ||
	       bare->fundamental == FT_UNSIGNED_CHAR ||
	       bare->fundamental == FT_WCHAR_T;
}

bool hosted_char_insertion_argument(TypePtr type)
{
	TypePtr bare = type.get() != NULL ? pa11::strip_cv(type) : TypePtr();
	if (bare.get() == NULL)
		return false;
	if (bare->kind == pa11::TypeKind::LValueReference ||
	    bare->kind == pa11::TypeKind::RValueReference)
		bare = pa11::strip_cv(bare->base);
	if (bare.get() == NULL)
		return false;
	if (bare->kind == pa11::TypeKind::Record)
	{
		string primary = template_primary(bare);
		if (primary == "string")
			return true;
		if (primary == "basic_string" &&
		    !bare->template_arguments.empty() &&
		    bare->template_arguments[0].kind ==
			    pa11::TemplateInstanceArgumentKind::Type)
			return hosted_character_type(
				bare->template_arguments[0].type);
		return false;
	}
	if (bare->kind == pa11::TypeKind::Pointer)
		bare = pa11::strip_cv(bare->base);
	if (bare.get() == NULL || bare->kind != pa11::TypeKind::Fundamental)
		return false;
	return bare->fundamental == FT_CHAR ||
	       bare->fundamental == FT_SIGNED_CHAR ||
	       bare->fundamental == FT_UNSIGNED_CHAR;
}

bool hosted_string_type(TypePtr type)
{
	TypePtr bare = type.get() != NULL ? pa11::strip_cv(type) : TypePtr();
	if (bare.get() == NULL || bare->kind != pa11::TypeKind::Record)
		return false;
	string primary = template_primary(bare);
	if (primary == "string")
		return true;
	if (primary != "basic_string" ||
	    bare->template_arguments.empty() ||
	    bare->template_arguments[0].kind !=
		    pa11::TemplateInstanceArgumentKind::Type)
		return false;
	return hosted_character_type(bare->template_arguments[0].type);
}

bool hosted_char_ostream(TypePtr type)
{
	TypePtr bare = type.get() != NULL ? pa11::strip_cv(type) : TypePtr();
	if (bare.get() == NULL || bare->kind != pa11::TypeKind::Record)
		return false;
	string primary = template_primary(bare);
	if (primary == "ostream")
		return true;
	if (primary != "basic_ostream" ||
	    bare->template_arguments.empty() ||
	    bare->template_arguments[0].kind !=
		    pa11::TemplateInstanceArgumentKind::Type)
		return false;
	return hosted_character_type(bare->template_arguments[0].type);
}

bool hosted_char_istream(TypePtr type)
{
	TypePtr bare = type.get() != NULL ? pa11::strip_cv(type) : TypePtr();
	if (bare.get() == NULL || bare->kind != pa11::TypeKind::Record)
		return false;
	string primary = template_primary(bare);
	if (primary == "istream")
		return true;
	if (primary != "basic_istream" ||
	    bare->template_arguments.empty() ||
	    bare->template_arguments[0].kind !=
		    pa11::TemplateInstanceArgumentKind::Type)
		return false;
	return hosted_character_type(bare->template_arguments[0].type);
}

}  // namespace

bool Parser::mark_hosted_stream_function_template_symbol(
	Binding* function,
	Binding* template_binding) const
{
	if (!function->function_specialization_symbol.empty())
		return true;
	if (template_binding->aliased_binding != NULL &&
	    !template_binding->aliased_binding
		    ->function_specialization_symbol.empty())
	{
		function->function_specialization_symbol =
			template_binding->aliased_binding
				->function_specialization_symbol;
		return true;
	}
	map<Binding*, TemplateDeclaration*>::const_iterator declaration =
		function_template_placeholders_.find(template_binding);
	if (declaration == function_template_placeholders_.end() &&
	    template_binding->aliased_binding != NULL)
	{
		template_binding = template_binding->aliased_binding;
		declaration =
			function_template_placeholders_.find(template_binding);
	}
	if (declaration == function_template_placeholders_.end())
		return false;
	map<Binding*, vector<TemplateArgument> >::const_iterator args =
		function_template_specialization_arguments_.find(function);
	if (args == function_template_specialization_arguments_.end() &&
	    template_binding != function)
		args =
			function_template_specialization_arguments_.find(
				template_binding);
	if (args == function_template_specialization_arguments_.end())
		return false;
	string symbol = abi_function_template_specialization_symbol(
		declaration->second,
		args->second,
		template_binding,
		&declaration_tokens_);
	if (symbol.empty())
		return false;
	template_binding->function_specialization_symbol = symbol;
	function->function_specialization_symbol = symbol;
	return true;
}

bool Parser::mark_hosted_stream_insertion_extern_template(
	Binding* function) const
{
	if (function == NULL ||
	    function->name != "operator<<" ||
	    function->owner == NULL ||
	    function->owner->kind != ScopeKind::Namespace ||
	    function->owner->name != "std" ||
	    function->type.get() == NULL ||
	    function->type->kind != pa11::TypeKind::Function ||
	    function->type->parameters.size() != 2)
		return false;
	TypePtr stream = pa11::strip_cv(function->type->parameters[0]);
	if (stream.get() == NULL ||
	    stream->kind != pa11::TypeKind::LValueReference ||
	    !hosted_char_ostream(stream->base))
		return false;
	TypePtr stream_record = pa11::strip_cv(stream->base);
	if (stream_record.get() == NULL ||
	    stream_record->kind != pa11::TypeKind::Record ||
	    !stream_record->is_extern_template_instantiation ||
	    !hosted_char_insertion_argument(function->type->parameters[1]))
		return false;
	return mark_hosted_stream_function_template_symbol(function, function);
}

bool Parser::mark_hosted_getline_extern_template(Binding* function) const
{
	if (function == NULL ||
	    function->name != "getline" ||
	    function->owner == NULL ||
	    function->owner->kind != ScopeKind::Namespace ||
	    function->owner->name != "std" ||
	    function->type.get() == NULL ||
	    function->type->kind != pa11::TypeKind::Function ||
	    function->type->parameters.size() < 2 ||
	    function->type->parameters.size() > 3)
		return false;
	TypePtr stream = pa11::strip_cv(function->type->parameters[0]);
	if (stream.get() == NULL ||
	    stream->kind != pa11::TypeKind::LValueReference ||
	    !hosted_char_istream(stream->base))
		return false;
	TypePtr stream_record = pa11::strip_cv(stream->base);
	if (stream_record.get() == NULL ||
	    stream_record->kind != pa11::TypeKind::Record ||
	    !stream_record->is_extern_template_instantiation)
		return false;
	TypePtr string_arg = pa11::strip_cv(function->type->parameters[1]);
	if (string_arg.get() == NULL ||
	    string_arg->kind != pa11::TypeKind::LValueReference ||
	    !hosted_string_type(string_arg->base))
		return false;
	if (function->type->parameters.size() == 3 &&
	    !hosted_character_type(function->type->parameters[2]))
		return false;
	return mark_hosted_stream_function_template_symbol(function, function);
}

bool Parser::mark_hosted_endl_extern_template(Binding* function) const
{
	if (function == NULL ||
	    function->name != "endl" ||
	    function->owner == NULL ||
	    function->owner->kind != ScopeKind::Namespace ||
	    function->owner->name != "std" ||
	    function->type.get() == NULL ||
	    function->type->kind != pa11::TypeKind::Function ||
	    function->type->parameters.size() != 1)
		return false;
	TypePtr stream = pa11::strip_cv(function->type->parameters[0]);
	if (stream.get() == NULL ||
	    stream->kind != pa11::TypeKind::LValueReference ||
	    !hosted_char_ostream(stream->base))
		return false;
	TypePtr stream_record = pa11::strip_cv(stream->base);
	if (stream_record.get() == NULL ||
	    stream_record->kind != pa11::TypeKind::Record ||
	    !stream_record->is_extern_template_instantiation)
		return false;
	return mark_hosted_stream_function_template_symbol(function, function);
}

}  // namespace internal
}  // namespace pa12
