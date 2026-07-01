#include "pa12_internal.h"

#include <stdexcept>

using namespace std;

namespace pa12 {
namespace internal {
namespace {

bool record_has_nonpublic_field(TypePtr record)
{
	TypePtr bare = pa11::strip_cv(record);
	if (bare->kind != pa11::TypeKind::Record)
		return false;
	for (size_t i = 0; i < bare->fields.size(); ++i)
		if (bare->fields[i]->is_private ||
		    bare->fields[i]->is_protected_member)
			return true;
	vector<TypePtr> bases = pa11::record_direct_bases(bare);
	for (size_t i = 0; i < bases.size(); ++i)
		if (record_has_nonpublic_field(bases[i]))
			return true;
	return false;
}

}  // namespace

void Parser::validate_record_copy_initialization(TypePtr type, const Expr& init)
{
	TypePtr record = pa11::strip_cv(type);
	pa11::layout_record_type(record);
	TypePtr init_record = init.type.get() != NULL
		? pa11::strip_cv(expression_object_type(init.type)) : TypePtr();
	if (init_record.get() != NULL &&
	    init_record->kind == pa11::TypeKind::Record &&
	    pa11::same_type(init_record, record) &&
	    (init.node.direct_call != NULL ||
	     !init.braced_init_list ||
	     init.category == ValueCategory::PRValue))
		return;
	if (record->scope != NULL &&
	    init.node.direct_call != NULL &&
	    init.node.direct_call->owner == record->scope &&
	    init.node.direct_call->name == record->scope->name)
	{
		if (init.node.direct_call->is_explicit)
			throw runtime_error("explicit constructor in copy initialization");
		return;
	}
	if (init.braced_init_list && init.node.direct_call != NULL)
		return;
	if (init.braced_init_list && record->scope != NULL)
	{
		map<string, vector<Binding*> >::const_iterator ctors =
			record->scope->members.find(record->scope->name);
		if (ctors != record->scope->members.end())
		{
			for (size_t i = 0; i < ctors->second.size(); ++i)
			{
				Binding* ctor = ctors->second[i];
				if (ctor->kind == BindingKind::Function &&
				    ctor->type->kind == pa11::TypeKind::Function &&
				    !ctor->is_explicit &&
				    ctor->type->parameters.size() ==
					    init.node.children.size() + 1)
					return;
			}
		}
	}
	if (init.braced_init_list)
		validate_aggregate_braced_initialization(record);
	if (!init.braced_init_list &&
	    init_record.get() != NULL &&
	    init_record->kind == pa11::TypeKind::Record &&
	    !pa11::same_type(init_record, record))
	{
		try
		{
			Conversion conv = convert_to(init, type);
			if (conv.viable)
				return;
		}
		catch (const runtime_error&)
		{
		}
	}
	size_t arg_count = init.braced_init_list ? init.node.children.size() : 1;
	if (record->scope == NULL)
		return;
	map<string, vector<Binding*> >::const_iterator found =
		record->scope->members.find(record->scope->name);
	if (found == record->scope->members.end())
		return;
	for (size_t i = 0; i < found->second.size(); ++i)
	{
		Binding* ctor = found->second[i];
		if (ctor->kind != BindingKind::Function ||
		    !ctor->is_explicit ||
		    ctor->type->parameters.size() != arg_count + 1)
			continue;
		bool viable = true;
		for (size_t j = 0; j < arg_count; ++j)
		{
			Expr arg;
			if (init.braced_init_list)
			{
				arg.valid = true;
				arg.node = init.node.children[j];
				arg.type = arg.node.type;
				arg.category = arg.node.category;
				arg.binding = arg.node.binding;
			}
			else
				arg = init;
			try
			{
				Conversion conv =
					convert_to(arg, ctor->type->parameters[j + 1]);
				if (!conv.viable)
					viable = false;
			}
			catch (const runtime_error&)
			{
				viable = false;
			}
		if (!viable)
			break;
	}
		if (viable)
			throw runtime_error("explicit constructor in copy initialization");
	}
}

void Parser::validate_aggregate_braced_initialization(TypePtr record)
{
	TypePtr bare = pa11::strip_cv(record);
	if (bare->kind != pa11::TypeKind::Record)
		return;
	pa11::layout_record_type(bare);
	if (record_has_aggregate_blocking_constructor(bare))
		return;
	if (record_has_nonpublic_field(bare))
		throw runtime_error("non-public member disqualifies aggregate");
	for (size_t i = 0; i < bare->fields.size(); ++i)
		if (default_member_initializers_.find(bare->fields[i]) !=
		    default_member_initializers_.end())
			throw runtime_error(
				"default member initializer disqualifies aggregate");
}

}  // namespace internal
}  // namespace pa12
