#include "pa12_expr_semantics_support.h"
#include "pa12_templates_function_support.h"
#include "pa12_types_support.h"

using namespace std;

namespace pa12 {
namespace internal {

bool hosted_call_scope_has_namespace_named(Scope* scope, const string& name)
{
	for (Scope* cur = scope; cur != NULL; cur = cur->parent)
		if (cur->kind == ScopeKind::Namespace && cur->name == name)
			return true;
	return false;
}

bool hosted_std_basic_string_comparison_template_declaration(
	const TemplateDeclaration* declaration)
{
	return hosted_std_function_template_declaration(declaration,
	                                                "operator==") ||
	       hosted_std_function_template_declaration(declaration,
	                                                "operator!=") ||
	       hosted_std_function_template_declaration(declaration,
	                                                "operator<") ||
	       hosted_std_function_template_declaration(declaration,
	                                                "operator>") ||
	       hosted_std_function_template_declaration(declaration,
	                                                "operator<=") ||
	       hosted_std_function_template_declaration(declaration,
	                                                "operator>=");
}

bool hosted_basic_string_type(TypePtr type)
{
	TypePtr bare = type.get() != NULL ? pa11::strip_cv(type) : TypePtr();
	return bare.get() != NULL &&
	       bare->kind == pa11::TypeKind::Record &&
	       bare->is_template_specialization &&
	       bare->template_primary_name == "basic_string" &&
	       hosted_call_scope_has_namespace_named(bare->scope, "std");
}

string hosted_call_unqualified_template_primary_name(TypePtr type)
{
	TypePtr bare = type.get() != NULL ? pa11::strip_cv(type) : TypePtr();
	if (bare.get() == NULL)
		return "";
	string primary = bare->template_primary_name.empty()
		? bare->name : bare->template_primary_name;
	size_t pos = primary.rfind("::");
	return pos == string::npos ? primary : primary.substr(pos + 2);
}

bool hosted_basic_string_pattern(TypePtr type)
{
	TypePtr bare = type.get() != NULL ? pa11::strip_cv(type) : TypePtr();
	if (bare.get() == NULL)
		return false;
	if (bare->kind == pa11::TypeKind::LValueReference ||
	    bare->kind == pa11::TypeKind::RValueReference ||
	    bare->kind == pa11::TypeKind::Pointer ||
	    bare->kind == pa11::TypeKind::Cv)
		return hosted_basic_string_pattern(bare->base);
	return hosted_basic_string_type(bare);
}

TypePtr substitute_hosted_basic_string_operator_type(TypePtr pattern,
                                                     TypePtr string_type,
                                                     TypePtr char_type)
{
	if (pattern.get() == NULL)
		return pattern;
	if (pattern->kind == pa11::TypeKind::Cv)
		return pa11::make_cv(
			substitute_hosted_basic_string_operator_type(pattern->base,
			                                             string_type,
			                                             char_type),
			pattern->cv);
	if (pattern->kind == pa11::TypeKind::Pointer)
		return pa11::make_pointer(
			substitute_hosted_basic_string_operator_type(pattern->base,
			                                             string_type,
			                                             char_type));
	if (pattern->kind == pa11::TypeKind::LValueReference)
		return pa11::make_lvalue_reference(
			substitute_hosted_basic_string_operator_type(pattern->base,
			                                             string_type,
			                                             char_type));
	if (pattern->kind == pa11::TypeKind::RValueReference)
		return pa11::make_rvalue_reference(
			substitute_hosted_basic_string_operator_type(pattern->base,
			                                             string_type,
			                                             char_type));
	TypePtr bare = pa11::strip_cv(pattern);
	if (bare->kind == pa11::TypeKind::TemplateParameter &&
	    pa11::is_deducible_template_parameter_type(bare))
		return char_type;
	if (hosted_basic_string_type(pattern))
		return string_type;
	return pattern;
}

bool hosted_std_function_type(TypePtr type)
{
	TypePtr bare = type.get() != NULL ? pa11::strip_cv(type) : TypePtr();
	return bare.get() != NULL &&
	       bare->kind == pa11::TypeKind::Record &&
	       bare->is_template_specialization &&
	       hosted_call_unqualified_template_primary_name(bare) == "function" &&
	       hosted_call_scope_has_namespace_named(bare->scope, "std");
}

bool hosted_std_vector_type(TypePtr type)
{
	TypePtr bare = type.get() != NULL ? pa11::strip_cv(type) : TypePtr();
	return bare.get() != NULL &&
	       bare->kind == pa11::TypeKind::Record &&
	       bare->is_template_specialization &&
	       hosted_call_unqualified_template_primary_name(bare) == "vector" &&
	       hosted_call_scope_has_namespace_named(bare->scope, "std");
}

bool hosted_call_enable_shared_from_this_type(TypePtr type)
{
	TypePtr bare = type.get() != NULL ? pa11::strip_cv(type) : TypePtr();
	return bare.get() != NULL &&
	       bare->kind == pa11::TypeKind::Record &&
	       hosted_call_unqualified_template_primary_name(bare) ==
		       "enable_shared_from_this";
}

bool hosted_record_has_esft_base(TypePtr type, set<const void*>& seen)
{
	TypePtr bare = type.get() != NULL ? pa11::strip_cv(type) : TypePtr();
	if (bare.get() == NULL ||
	    bare->kind != pa11::TypeKind::Record ||
	    !seen.insert(bare.get()).second)
		return false;
	vector<TypePtr> bases = pa11::record_direct_bases(bare);
	for (size_t i = 0; i < bases.size(); ++i)
		if (hosted_call_enable_shared_from_this_type(bases[i]) ||
		    hosted_record_has_esft_base(bases[i], seen))
			return true;
	return false;
}

bool hosted_esft_enable_if_condition(TypePtr result,
                                     bool argument_has_base,
                                     bool& enabled)
{
	TypePtr bare = result.get() != NULL ? pa11::strip_cv(result) : TypePtr();
	if (bare.get() == NULL ||
	    (hosted_call_unqualified_template_primary_name(bare) != "enable_if" &&
	     hosted_call_unqualified_template_primary_name(bare) != "__enable_if_t") ||
	    bare->dependent_typename_template_argument_lists.empty() ||
	    bare->dependent_typename_template_argument_lists[0].empty())
		return false;
	const pa11::TemplateInstanceArgument& condition =
		bare->dependent_typename_template_argument_lists[0][0];
	if (condition.kind != pa11::TemplateInstanceArgumentKind::Value ||
	    condition.value_owner_template_name != "__has_esft_base" ||
	    condition.value_member_name != "value")
		return false;
	enabled = condition.value_negated
		? !argument_has_base : argument_has_base;
	return true;
}

bool hosted_std_function_member_template_declaration(
	const TemplateDeclaration* declaration,
	const string& name)
{
	if (declaration == NULL || declaration->name != name ||
	    declaration->owner == NULL ||
	    declaration->owner->kind != ScopeKind::Class)
		return false;
	return hosted_std_function_type(
		pa11::record_type_for_scope(declaration->owner));
}

bool hosted_std_vector_member_template_declaration(
	const TemplateDeclaration* declaration,
	const string& name)
{
	if (declaration == NULL || declaration->name != name ||
	    declaration->owner == NULL ||
	    declaration->owner->kind != ScopeKind::Class)
		return false;
	return hosted_std_vector_type(
		pa11::record_type_for_scope(declaration->owner));
}

bool hosted_forwarding_template_parameter(TypePtr type)
{
	TypePtr bare = type.get() != NULL ? pa11::strip_cv(type) : TypePtr();
	if (bare.get() == NULL ||
	    bare->kind != pa11::TypeKind::RValueReference)
		return false;
	TypePtr base = pa11::strip_cv(bare->base);
	return base.get() != NULL &&
	       base->kind == pa11::TypeKind::TemplateParameter &&
	       pa11::is_deducible_template_parameter_type(base);
}

bool complete_hosted_template_argument_prefix(
	const TemplateDeclaration* declaration,
	vector<TemplateArgument>& arguments)
{
	if (declaration == NULL || arguments.size() > declaration->parameters.size())
		return false;
	for (size_t i = arguments.size(); i < declaration->parameters.size(); ++i)
	{
		const TemplateParameterInfo& parameter = declaration->parameters[i];
		if (!parameter.has_default)
			return false;
		if (parameter.kind == TemplateParameterKind::Type)
		{
			string name = parameter.name.empty()
				? declaration->name + "__default" + to_string(i)
				: parameter.name;
			arguments.push_back(TemplateArgument::type_arg(
				pa11::make_dependent_typename_type(name,
				                                   false,
				                                   false,
				                                   false)));
		}
		else
		{
			TypePtr type = parameter.type.get() != NULL
				? parameter.type : pa11::make_fundamental(FT_INT);
			arguments.push_back(TemplateArgument::dependent_value_arg(type));
		}
	}
	return true;
}

TypePtr hosted_expression_object_type(TypePtr type)
{
	if (type.get() != NULL &&
	    (type->kind == pa11::TypeKind::LValueReference ||
	     type->kind == pa11::TypeKind::RValueReference))
		return type->base;
	return type;
}

TypePtr hosted_lvalue_to_rvalue_type(TypePtr type)
{
	return hosted_expression_object_type(type);
}

bool hosted_basic_string_template_arguments(TypePtr type,
                                            vector<TemplateArgument>& out)
{
	TypePtr bare = type.get() != NULL
		? pa11::strip_cv(hosted_expression_object_type(type)) : TypePtr();
	if (!hosted_basic_string_type(bare))
		return false;
	out.clear();
	for (size_t i = 0; i < bare->template_arguments.size(); ++i)
	{
		if (bare->template_arguments[i].kind !=
		    pa11::TemplateInstanceArgumentKind::Type)
			break;
		out.push_back(
			TemplateArgument::type_arg(bare->template_arguments[i].type));
	}
	return !out.empty();
}

bool hosted_template_parameter_name(TypePtr type, string& name)
{
	TypePtr bare = type.get() != NULL ? pa11::strip_cv(type) : TypePtr();
	while (bare.get() != NULL &&
	       (bare->kind == pa11::TypeKind::LValueReference ||
	        bare->kind == pa11::TypeKind::RValueReference ||
	        bare->kind == pa11::TypeKind::Pointer ||
	        bare->kind == pa11::TypeKind::Array))
		bare = pa11::strip_cv(bare->base);
	if (bare.get() == NULL || bare->name.empty())
		return false;
	if (bare->kind == pa11::TypeKind::TemplateParameter ||
	    bare->is_dependent_typename)
	{
		name = bare->name;
		return true;
	}
	return false;
}

TypePtr substitute_hosted_named_type(TypePtr type,
                                     const string& name,
                                     TypePtr value)
{
	if (type.get() == NULL || name.empty())
		return type;
	TypePtr bare = pa11::strip_cv(type);
	if ((bare->kind == pa11::TypeKind::TemplateParameter ||
	     bare->is_dependent_typename) &&
	    bare->name == name)
		return value;
	if (type->kind == pa11::TypeKind::Cv)
		return pa11::make_cv(
			substitute_hosted_named_type(type->base, name, value),
			type->cv);
	if (type->kind == pa11::TypeKind::Pointer)
		return pa11::make_pointer(
			substitute_hosted_named_type(type->base, name, value));
	if (type->kind == pa11::TypeKind::LValueReference)
		return pa11::make_lvalue_reference(
			substitute_hosted_named_type(type->base, name, value));
	if (type->kind == pa11::TypeKind::RValueReference)
		return pa11::make_rvalue_reference(
			substitute_hosted_named_type(type->base, name, value));
	if (type->kind == pa11::TypeKind::Function)
	{
		vector<TypePtr> params;
		for (size_t i = 0; i < type->parameters.size(); ++i)
			params.push_back(
				substitute_hosted_named_type(type->parameters[i],
				                             name,
				                             value));
		TypePtr out = pa11::make_function(
			substitute_hosted_named_type(type->base, name, value),
			params,
			type->variadic);
		out->cv = type->cv;
		out->ref_qualifier = type->ref_qualifier;
		return out;
	}
	return type;
}

TypePtr hosted_forwarding_parameter_for_argument(const Expr& arg)
{
	TypePtr object = hosted_expression_object_type(arg.type);
	if (arg.category == ValueCategory::LValue)
		return pa11::make_lvalue_reference(object);
	return pa11::make_rvalue_reference(hosted_lvalue_to_rvalue_type(arg.type));
}

bool hosted_std_function_template_declaration(
	const TemplateDeclaration* declaration,
	const string& name)
{
	if (declaration == NULL || declaration->name != name)
		return false;
	Scope* scope =
		declaration->placeholder != NULL
		? declaration->placeholder->owner
		: declaration->owner;
	return hosted_call_scope_has_namespace_named(scope, "std");
}

bool hosted_std_basic_string_operator_template_declaration(
	const TemplateDeclaration* declaration)
{
	return hosted_std_function_template_declaration(declaration,
	                                                "operator+") ||
	       hosted_std_function_template_declaration(declaration,
	                                                "operator==") ||
	       hosted_std_function_template_declaration(declaration,
	                                                "operator!=") ||
	       hosted_std_function_template_declaration(declaration,
	                                                "operator<") ||
	       hosted_std_function_template_declaration(declaration,
	                                                "operator>") ||
	       hosted_std_function_template_declaration(declaration,
	                                                "operator<=") ||
	       hosted_std_function_template_declaration(declaration,
	                                                "operator>=");
}

TypePtr modeled_hosted_function_assignment_type(Binding* fn,
                                                const vector<Expr>& args,
                                                vector<TemplateArgument>& out)
{
	if (fn == NULL ||
	    fn->type.get() == NULL ||
	    fn->type->kind != pa11::TypeKind::Function ||
	    fn->owner == NULL ||
	    fn->owner->kind != ScopeKind::Class ||
	    fn->name != "operator=" ||
	    args.size() != 2 ||
	    args[1].type.get() == NULL ||
	    fn->type->parameters.size() != 2 ||
	    !hosted_std_function_type(pa11::record_type_for_scope(fn->owner)))
		return TypePtr();
	string parameter_name;
	if (!hosted_template_parameter_name(fn->type->parameters[1],
	                                    parameter_name))
		return TypePtr();
	TypePtr owner_record = pa11::strip_cv(pa11::record_type_for_scope(fn->owner));
	TypePtr functor_type = args[1].category == ValueCategory::LValue
		? hosted_expression_object_type(args[1].type)
		: hosted_lvalue_to_rvalue_type(args[1].type);
	if (owner_record.get() == NULL ||
	    functor_type.get() == NULL ||
	    type_structurally_dependent(functor_type))
		return TypePtr();
	vector<TypePtr> params;
	params.push_back(fn->type->parameters[0]);
	params.push_back(hosted_forwarding_parameter_for_argument(args[1]));
	TypePtr modeled = pa11::make_function(
		pa11::make_lvalue_reference(owner_record),
		params,
		false);
	modeled->cv = fn->type->cv;
	modeled->ref_qualifier = fn->type->ref_qualifier;
	out.clear();
	out.push_back(TemplateArgument::type_arg(functor_type));
	return modeled;
}

TypePtr modeled_hosted_vector_insert_type(Binding* fn,
                                          const vector<Expr>& args,
                                          vector<TemplateArgument>& out)
{
	if (fn == NULL ||
	    fn->type.get() == NULL ||
	    fn->type->kind != pa11::TypeKind::Function ||
	    fn->owner == NULL ||
	    fn->owner->kind != ScopeKind::Class ||
	    fn->name != "insert" ||
	    args.size() != 4 ||
	    args[2].type.get() == NULL ||
	    args[3].type.get() == NULL ||
	    fn->type->parameters.size() != 4 ||
	    !hosted_std_vector_type(pa11::record_type_for_scope(fn->owner)))
		return TypePtr();
	string parameter_name;
	if (!hosted_template_parameter_name(fn->type->parameters[2],
	                                    parameter_name))
		return TypePtr();
	string last_parameter_name;
	if (!hosted_template_parameter_name(fn->type->parameters[3],
	                                    last_parameter_name) ||
	    last_parameter_name != parameter_name)
		return TypePtr();
	TypePtr first = hosted_lvalue_to_rvalue_type(args[2].type);
	TypePtr last = hosted_lvalue_to_rvalue_type(args[3].type);
	if (first.get() == NULL ||
	    last.get() == NULL ||
	    !pa11::same_type(first, last) ||
	    type_structurally_dependent(first))
		return TypePtr();
	TypePtr modeled =
		substitute_hosted_named_type(fn->type, parameter_name, first);
	if (modeled.get() == NULL || type_structurally_dependent(modeled))
		return TypePtr();
	out.clear();
	out.push_back(TemplateArgument::type_arg(first));
	return modeled;
}

TypePtr modeled_hosted_dependent_pointer_member_type(
	Binding* fn,
	const TemplateDeclaration* declaration,
	const vector<Expr>& args,
	vector<TemplateArgument>& out)
{
	if (fn == NULL ||
	    declaration == NULL ||
	    fn->type.get() == NULL ||
	    fn->type->kind != pa11::TypeKind::Function ||
	    fn->type->parameters.size() != 2 ||
	    fn->owner == NULL ||
	    fn->owner->kind != ScopeKind::Class ||
	    fn->is_static_member ||
	    args.size() != 2 ||
	    args[1].type.get() == NULL)
		return TypePtr();
	TypePtr self = pa11::strip_cv(fn->type->parameters[0]);
	if (self.get() == NULL ||
	    self->kind != pa11::TypeKind::Pointer)
		return TypePtr();
	TypePtr owner = pa11::strip_cv(self->base);
	if (owner.get() == NULL ||
	    owner->kind != pa11::TypeKind::Record)
		return TypePtr();
	string parameter_name;
	if (!hosted_template_parameter_name(fn->type->parameters[1],
	                                    parameter_name))
		return TypePtr();
	TypePtr argument_pointer = pa11::strip_cv(args[1].type);
	if (argument_pointer.get() == NULL ||
	    argument_pointer->kind != pa11::TypeKind::Pointer)
		return TypePtr();
	TypePtr pointee = pa11::strip_cv(argument_pointer->base);
	set<const void*> seen;
	bool has_base = hosted_record_has_esft_base(pointee, seen);
	bool enabled = false;
	if (!hosted_esft_enable_if_condition(fn->type->base, has_base, enabled) ||
	    !enabled)
		return TypePtr();
	vector<TypePtr> params = fn->type->parameters;
	params[1] = args[1].type;
	TypePtr modeled = pa11::make_function(pa11::make_fundamental(FT_VOID),
	                                      params,
	                                      false);
	modeled->cv = fn->type->cv;
	modeled->ref_qualifier = fn->type->ref_qualifier;
	out.clear();
	out.push_back(TemplateArgument::type_arg(pointee));
	if (declaration->parameters.size() > 1 &&
	    declaration->parameters[1].kind == TemplateParameterKind::Type)
		out.push_back(TemplateArgument::type_arg(remove_cv_type(pointee)));
	return modeled;
}

TypePtr hosted_make_pair_result_argument(const Expr& arg)
{
	TypePtr object = hosted_expression_object_type(arg.type);
	if (object.get() == NULL)
		return TypePtr();
	return remove_cv_type(object);
}

TypePtr Parser::modeled_hosted_make_pair_type(
	Binding* fn,
	const TemplateDeclaration* declaration,
	const vector<Expr>& args,
	vector<TemplateArgument>& out)
{
	if (fn == NULL ||
	    declaration == NULL ||
	    !hosted_std_function_template_declaration(declaration, "make_pair") ||
	    args.size() != 2 ||
	    args[0].type.get() == NULL ||
	    args[1].type.get() == NULL)
		return TypePtr();
	TypePtr first_arg = hosted_make_pair_result_argument(args[0]);
	TypePtr second_arg = hosted_make_pair_result_argument(args[1]);
	if (first_arg.get() == NULL ||
	    second_arg.get() == NULL ||
	    type_structurally_dependent(first_arg) ||
	    type_structurally_dependent(second_arg))
		return TypePtr();
	Scope* owner = declaration->placeholder != NULL
		? declaration->placeholder->owner : declaration->owner;
	TemplateDeclaration* pair_template =
		find_class_template(owner, "pair");
	if (pair_template == NULL)
		pair_template = find_class_template(NULL, "pair");
	if (pair_template == NULL)
		return TypePtr();
	vector<TemplateArgument> pair_args;
	pair_args.push_back(TemplateArgument::type_arg(first_arg));
	pair_args.push_back(TemplateArgument::type_arg(second_arg));
	TypePtr pair_type = instantiate_class_template(pair_template,
	                                               pair_args);
	if (pair_type.get() == NULL)
		return TypePtr();
	vector<TypePtr> params;
	params.push_back(hosted_forwarding_parameter_for_argument(args[0]));
	params.push_back(hosted_forwarding_parameter_for_argument(args[1]));
	TypePtr modeled = pa11::make_function(pair_type, params, false);
	if (fn->type.get() != NULL && fn->type->kind == pa11::TypeKind::Function)
	{
		modeled->cv = fn->type->cv;
		modeled->ref_qualifier = fn->type->ref_qualifier;
	}
	out.clear();
	out.push_back(
		TemplateArgument::type_arg(hosted_forwarding_parameter_for_argument(
			args[0])));
	out.push_back(
		TemplateArgument::type_arg(hosted_forwarding_parameter_for_argument(
			args[1])));
	return modeled;
}

bool recover_hosted_call_template_arguments(
	const TemplateDeclaration* declaration,
	const vector<Expr>& args,
	vector<TemplateArgument>& deduced)
{
	if (hosted_std_function_member_template_declaration(declaration,
	                                                    "operator=") &&
	    args.size() == 2 &&
	    args[1].type.get() != NULL &&
	    !declaration->parameters.empty() &&
	    declaration->parameters[0].kind == TemplateParameterKind::Type)
	{
		deduced.clear();
		deduced.push_back(TemplateArgument::type_arg(
			args[1].category == ValueCategory::LValue
			? hosted_expression_object_type(args[1].type)
			: hosted_lvalue_to_rvalue_type(args[1].type)));
		return complete_hosted_template_argument_prefix(declaration, deduced);
	}
	if (hosted_std_vector_member_template_declaration(declaration, "insert") &&
	    args.size() == 4 &&
	    args[2].type.get() != NULL &&
	    args[3].type.get() != NULL &&
	    !declaration->parameters.empty() &&
	    declaration->parameters[0].kind == TemplateParameterKind::Type)
	{
		TypePtr first = hosted_lvalue_to_rvalue_type(args[2].type);
		TypePtr last = hosted_lvalue_to_rvalue_type(args[3].type);
		if (!pa11::same_type(first, last))
			return false;
		deduced.clear();
		deduced.push_back(TemplateArgument::type_arg(first));
		return complete_hosted_template_argument_prefix(declaration, deduced);
	}
	if (hosted_std_basic_string_comparison_template_declaration(declaration) &&
	    args.size() == 2 &&
	    args[0].type.get() != NULL &&
	    args[1].type.get() != NULL)
	{
		if (hosted_basic_string_template_arguments(args[0].type, deduced) ||
		    hosted_basic_string_template_arguments(args[1].type, deduced))
			return complete_hosted_template_argument_prefix(declaration,
			                                               deduced);
	}
	return false;
}

}  // namespace internal
}  // namespace pa12
