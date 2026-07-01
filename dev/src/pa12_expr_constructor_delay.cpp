#include "pa12_expr_semantics_support.h"
#include "pa12_templates_instance_support.h"

namespace pa12 {
namespace internal {
namespace {

bool hosted_std_vector_record(TypePtr type)
{
	TypePtr bare = type.get() != NULL ? pa11::strip_cv(type) : TypePtr();
	if (bare.get() == NULL ||
	    bare->kind != pa11::TypeKind::Record ||
	    !bare->is_template_specialization ||
	    bare->scope == NULL)
		return false;
	string primary = bare->template_primary_name.empty()
		? bare->name : bare->template_primary_name;
	size_t sep = primary.rfind("::");
	if (sep != string::npos)
		primary = primary.substr(sep + 2);
	size_t args = primary.find('<');
	if (args != string::npos)
		primary = primary.substr(0, args);
	if (primary != "vector")
		return false;
	for (Scope* scope = bare->scope; scope != NULL; scope = scope->parent)
		if (scope->kind == ScopeKind::Namespace && scope->name == "std")
			return true;
	return false;
}

}  // namespace

bool Parser::hosted_vector_initializer_list_constructor(TypePtr record,
                                                        Binding* ctor)
{
	bool hosted_vector = hosted_std_vector_record(record);
	bool function_type = ctor != NULL &&
	                     ctor->type.get() != NULL &&
	                     ctor->type->kind == pa11::TypeKind::Function;
	bool enough_params = function_type && ctor->type->parameters.size() >= 2;
	if (!hosted_compatibility_ ||
	    ctor == NULL ||
	    !hosted_vector ||
	    !function_type ||
	    !enough_params)
		return false;
	TypePtr param = ctor->type->parameters[1];
	if (pa11::is_reference_type(param))
		param = param->base;
	return is_std_initializer_list_type(pa11::strip_cv(param), NULL);
}

bool Parser::constructor_body_can_be_delayed(TypePtr record, Binding* ctor)
{
	if (ctor == NULL || ctor->is_object_root)
		return false;
	TypePtr bare_record = record.get() != NULL ? pa11::strip_cv(record) : TypePtr();
	if (bare_record.get() != NULL &&
	    bare_record->kind == pa11::TypeKind::Record &&
	    bare_record->scope != NULL &&
	    ctor->name == bare_record->scope->name)
		return false;
	if (hosted_vector_initializer_list_constructor(record, ctor))
		return true;
	if (hosted_extern_template_class_function(ctor))
		return true;
	if (hosted_compatibility_ &&
	    !ctor->is_object_root &&
	    hosted_library_function(ctor))
		return true;
	return hosted_compatibility_ &&
	       ctor->is_inline_definition &&
	       !(ctor->owner != NULL &&
	         ctor->owner->kind == ScopeKind::Class &&
	         ctor->name == ctor->owner->name);
}

bool Parser::constructor_selection_instantiation_can_be_delayed(TypePtr record,
                                                                Binding* ctor)
{
	return hosted_vector_initializer_list_constructor(record, ctor) ||
	       (hosted_compatibility_ &&
	        ctor != NULL &&
	        !ctor->is_object_root &&
	        hosted_library_function(ctor));
}

}  // namespace internal
}  // namespace pa12
