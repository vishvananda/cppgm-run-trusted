#include "pa12_internal.h"

using namespace std;

namespace pa12 {
namespace internal {

void copy_member_template_placeholder_state(
	Binding* placeholder,
	Binding* source,
	map<Binding*, vector<string> >& function_parameter_names,
	map<Binding*, vector<Expr> >& default_arguments,
	bool copy_static_member)
{
	if (placeholder == NULL || source == NULL)
		return;
	if (copy_static_member)
		placeholder->is_static_member = source->is_static_member;
	placeholder->is_explicit = source->is_explicit;
	placeholder->is_constexpr = source->is_constexpr;
	placeholder->is_inline_definition =
		placeholder->is_inline_definition || source->is_inline_definition;
	placeholder->is_defaulted = source->is_defaulted;
	placeholder->is_explicit_specialization_member =
		source->is_explicit_specialization_member;
	placeholder->is_explicit_defaulted_definition =
		source->is_explicit_defaulted_definition;
	placeholder->is_generated_default_constructor =
		source->is_generated_default_constructor;
	placeholder->is_generated_copy_move_constructor =
		source->is_generated_copy_move_constructor;
	placeholder->is_noop_constructor = source->is_noop_constructor;
	placeholder->unwind_no = source->unwind_no;
	placeholder->dynamic_exception_spec = source->dynamic_exception_spec;
	placeholder->dynamic_exception_types = source->dynamic_exception_types;
	placeholder->ref_qualifier = source->ref_qualifier;
	map<Binding*, vector<string> >::iterator names =
		function_parameter_names.find(source);
	if (names != function_parameter_names.end())
	{
		function_parameter_names[placeholder] = names->second;
		placeholder->function_parameter_names = names->second;
	}
	map<Binding*, vector<Expr> >::iterator defaults =
		default_arguments.find(source);
	if (defaults != default_arguments.end())
		default_arguments[placeholder] = defaults->second;
}

void assign_member_template_alias_state(Binding* alias, Binding* source)
{
	if (alias == NULL || source == NULL)
		return;
	alias->is_inline_definition = source->is_inline_definition;
	alias->is_explicit = source->is_explicit;
	alias->is_defaulted = source->is_defaulted;
	alias->is_explicit_specialization_member =
		source->is_explicit_specialization_member;
	alias->is_explicit_defaulted_definition =
		source->is_explicit_defaulted_definition;
	alias->is_generated_default_constructor =
		source->is_generated_default_constructor;
	alias->is_generated_copy_move_constructor =
		source->is_generated_copy_move_constructor;
	alias->is_noop_constructor = source->is_noop_constructor;
	alias->is_constexpr = source->is_constexpr;
	alias->unwind_no = source->unwind_no;
	alias->dynamic_exception_spec = source->dynamic_exception_spec;
	alias->dynamic_exception_types = source->dynamic_exception_types;
	alias->ref_qualifier = source->ref_qualifier;
}

void merge_member_template_alias_state(Binding* concrete, Binding* source)
{
	if (concrete == NULL || source == NULL)
		return;
	concrete->is_inline_definition =
		concrete->is_inline_definition || source->is_inline_definition;
	concrete->is_defaulted = concrete->is_defaulted || source->is_defaulted;
	concrete->is_explicit_specialization_member =
		concrete->is_explicit_specialization_member ||
		source->is_explicit_specialization_member;
	concrete->is_explicit_defaulted_definition =
		concrete->is_explicit_defaulted_definition ||
		source->is_explicit_defaulted_definition;
	concrete->is_generated_default_constructor =
		concrete->is_generated_default_constructor ||
		source->is_generated_default_constructor;
	concrete->is_generated_copy_move_constructor =
		concrete->is_generated_copy_move_constructor ||
		source->is_generated_copy_move_constructor;
	concrete->is_noop_constructor =
		concrete->is_noop_constructor || source->is_noop_constructor;
}

}  // namespace internal
}  // namespace pa12
