#include "pa14_lowir_internal.h"

namespace pa14 {
namespace internal {
namespace {

bool hosted_basic_streambuf_virtual_function_definition(const Node& node)
{
	if (!starts_with(node.line, "function-definition ") ||
	    node.binding == NULL ||
	    !node.binding->is_inline_definition ||
	    !node.binding->is_virtual)
		return false;
	if (!hosted_library_binding(node.binding))
		return false;
	TypePtr owner = class_record_for_member(node.binding);
	owner = owner.get() != NULL ? pa11::strip_cv(owner) : TypePtr();
	if (owner.get() == NULL || owner->kind != TypeKind::Record)
		return false;
	string primary = owner->template_primary_name.empty()
		? owner->name : owner->template_primary_name;
	return primary == "basic_streambuf" ||
	       primary == "std::basic_streambuf";
}

bool record_matches_template_argument(
	TypePtr record,
	const pa11::TemplateInstanceArgument& arg)
{
	record = record.get() != NULL ? pa11::strip_cv(record) : TypePtr();
	if (record.get() == NULL || record->kind != TypeKind::Record)
		return false;
	if (arg.kind == pa11::TemplateInstanceArgumentKind::Type)
	{
		TypePtr type = arg.type.get() != NULL
			? pa11::strip_cv(arg.type) : TypePtr();
		return type.get() != NULL &&
		       type->kind == TypeKind::Record &&
		       pa11::same_type(record, type);
	}
	if (arg.kind == pa11::TemplateInstanceArgumentKind::Pack)
		for (size_t i = 0; i < arg.pack.size(); ++i)
			if (record_matches_template_argument(record, arg.pack[i]))
				return true;
	return false;
}

bool hosted_streambuf_virtual_dependency(const Binding* source,
                                         const Binding* target)
{
	if (source == NULL || target == NULL)
		return false;
	if (!hosted_library_binding(target))
		return false;
	if (target->owner == source->owner)
		return true;
	TypePtr source_record = class_record_for_member(source);
	source_record = source_record.get() != NULL
		? pa11::strip_cv(source_record) : TypePtr();
	TypePtr target_record = target->owner != NULL &&
	                        target->owner->kind == ScopeKind::Class
		? pa11::record_type_for_scope(target->owner) : TypePtr();
	target_record = target_record.get() != NULL
		? pa11::strip_cv(target_record) : TypePtr();
	if (source_record.get() != NULL &&
	    source_record->kind == TypeKind::Record &&
	    target_record.get() != NULL &&
	    target_record->kind == TypeKind::Record)
		for (size_t i = 0; i < source_record->template_arguments.size(); ++i)
			if (record_matches_template_argument(
				    target_record,
				    source_record->template_arguments[i]))
				return true;
	if (target->owner != NULL &&
	    target->owner->kind == ScopeKind::Namespace &&
	    target->owner->name == "std" &&
	    target->name == "min")
		return true;
	return false;
}

void collect_hosted_streambuf_virtual_body_demands(
	const Node& node,
	const Binding* source,
	set<const Binding*>& out)
{
	if (node.direct_call != NULL &&
	    hosted_streambuf_virtual_dependency(source, node.direct_call) &&
	    !suppress_noop_generated_constructor_call(node))
		out.insert(node.direct_call);
	for (size_t i = 0; i < node.children.size(); ++i)
		collect_hosted_streambuf_virtual_body_demands(
			node.children[i],
			source,
			out);
}

}  // namespace

bool suppress_noop_generated_constructor_call(const Node& node)
{
	const Binding* binding = node.direct_call;
	if (binding == NULL ||
	    !(binding->is_generated_aggregate_constructor ||
	      starts_with(node.line, "base-init-action") ||
	      starts_with(node.line, "member-init-action")) ||
	    !binding->is_generated_default_constructor ||
	    !binding->is_noop_constructor ||
	    !binding->unwind_no)
		return false;
	TypePtr record = class_record_for_member(binding);
	record = record.get() != NULL ? pa11::strip_cv(record) : TypePtr();
	return record.get() == NULL ||
	       record->kind != TypeKind::Record ||
	       hidden_virtual_bases_for_record(record).empty();
}

void collect_hosted_streambuf_virtual_body_demands(
	const vector<Node>& extra,
	set<const Binding*>& out)
{
	for (size_t i = 0; i < extra.size(); ++i)
	{
		if (!hosted_basic_streambuf_virtual_function_definition(extra[i]))
			continue;
		collect_hosted_streambuf_virtual_body_demands(
			extra[i],
			extra[i].binding,
			out);
	}
}

}  // namespace internal
}  // namespace pa14
