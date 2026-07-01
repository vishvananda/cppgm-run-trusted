#include "pa12_expr_semantics_support.h"
#include "pa12_templates_instance_support.h"

#include <stdexcept>

using namespace std;

namespace pa12 {
namespace internal {

bool no_matching_constructor_error(const runtime_error& err)
{
	return string(err.what()).compare(0, 23, "no matching constructor") == 0;
}

namespace {

TypePtr constructor_owner_record(Binding* ctor)
{
	if (ctor == NULL ||
	    ctor->type.get() == NULL ||
	    ctor->type->kind != pa11::TypeKind::Function ||
	    ctor->type->parameters.empty())
		return TypePtr();
	TypePtr this_type = pa11::strip_cv(ctor->type->parameters[0]);
	if (this_type.get() == NULL ||
	    this_type->kind != pa11::TypeKind::Pointer)
		return TypePtr();
	TypePtr owner = pa11::strip_cv(this_type->base);
	return owner.get() != NULL &&
	       owner->kind == pa11::TypeKind::Record ? owner : TypePtr();
}

TypePtr local_expression_object_type(TypePtr type)
{
	if (type.get() != NULL &&
	    (type->kind == pa11::TypeKind::LValueReference ||
	     type->kind == pa11::TypeKind::RValueReference))
		return type->base;
	return type;
}

}  // namespace

bool exact_copy_reference_constructor_for_order_args(
	Binding* ctor,
	const vector<Expr>& template_order_args)
{
	if (ctor == NULL ||
	    ctor->type.get() == NULL ||
	    ctor->type->kind != pa11::TypeKind::Function ||
	    ctor->type->parameters.size() != 2 ||
	    template_order_args.size() != 2)
		return false;
	TypePtr param = ctor->type->parameters[1];
	if (param.get() == NULL ||
	    (param->kind != pa11::TypeKind::LValueReference &&
	     param->kind != pa11::TypeKind::RValueReference))
		return false;
	TypePtr owner = constructor_owner_record(ctor);
	TypePtr param_record = pa11::strip_cv(param->base);
	TypePtr source = local_expression_object_type(template_order_args[1].type);
	TypePtr source_record = source.get() != NULL
		? pa11::strip_cv(source) : TypePtr();
	if (owner.get() == NULL ||
	    param_record.get() == NULL ||
	    source_record.get() == NULL ||
	    param_record->kind != pa11::TypeKind::Record ||
	    source_record->kind != pa11::TypeKind::Record)
		return false;
	if (!pa11::same_type(owner, param_record) &&
	    !same_template_specialization_record(owner, param_record))
		return false;
	return pa11::same_type(source_record, param_record) ||
	       same_template_specialization_record(source_record, param_record);
}

bool ranks_equal_allowing_copy_reference_rank(
	const vector<int>& copy_ranks,
	const vector<int>& other_ranks)
{
	if (copy_ranks.size() != 1 || other_ranks.size() != 1)
		return false;
	return copy_ranks[0] == other_ranks[0] ||
	       copy_ranks[0] == other_ranks[0] + 1;
}

bool Parser::constructor_accepts_argument_count(Binding* ctor,
                                                size_t arg_count) const
{
	pair<Binding*, size_t> cache_key(ctor, arg_count);
	pair<size_t, size_t> generation(default_arguments_.size(),
	                                function_template_placeholders_.size());
	map<pair<Binding*, size_t>,
	    pair<pair<size_t, size_t>, bool> >::iterator cached =
		constructor_arg_count_cache_.find(cache_key);
	if (cached != constructor_arg_count_cache_.end() &&
	    cached->second.first == generation)
		return cached->second.second;
	size_t param_count = ctor->type->parameters.size() - 1;
	map<Binding*, TemplateDeclaration*>::const_iterator templ =
		function_template_placeholders_.find(ctor);
	if (templ != function_template_placeholders_.end() &&
	    templ->second != NULL)
	{
		for (size_t i = 1; i < ctor->type->parameters.size(); ++i)
		{
			string pack_name;
			bool pack_parameter =
				function_parameter_type_pack_expansion_name(
					ctor->type->parameters[i],
					pack_name);
			if (!pack_parameter)
			{
				for (size_t pi = 0;
				     pi < templ->second->parameters.size();
				     ++pi)
				{
					const TemplateParameterInfo& parameter =
						templ->second->parameters[pi];
					if (!parameter.is_pack ||
					    parameter.name.empty())
						continue;
					if (type_contains_parameter_name(
						    ctor->type->parameters[i],
						    parameter.name,
						    record_template_arguments_))
					{
						pack_parameter = true;
						break;
					}
				}
			}
			if (!pack_parameter)
				continue;
			size_t before_pack = i - 1;
			size_t after_pack = param_count - i;
			if (arg_count >= before_pack + after_pack)
			{
				constructor_arg_count_cache_[cache_key] =
					make_pair(generation, true);
				return true;
			}
		}
	}
	if (arg_count > param_count && !ctor->type->variadic)
	{
		constructor_arg_count_cache_[cache_key] =
			make_pair(generation, false);
		return false;
	}
	if (arg_count >= param_count)
	{
		constructor_arg_count_cache_[cache_key] =
			make_pair(generation, true);
		return true;
	}
	map<Binding*, vector<Expr> >::const_iterator defaults =
		default_arguments_.find(ctor);
	if (defaults == default_arguments_.end())
	{
		constructor_arg_count_cache_[cache_key] =
			make_pair(generation, false);
		return false;
	}
	for (size_t j = arg_count + 1; j < ctor->type->parameters.size(); ++j)
		if (j >= defaults->second.size() || !defaults->second[j].valid)
		{
			constructor_arg_count_cache_[cache_key] =
				make_pair(generation, false);
			return false;
		}
	constructor_arg_count_cache_[cache_key] =
		make_pair(generation, true);
	return true;
}

}  // namespace internal
}  // namespace pa12
