#include "pa14_lowir_internal.h"

namespace pa14 {
namespace internal {
map<const Binding*, bool>& inline_class_constructor_cache()
{
	static map<const Binding*, bool> cache;
	return cache;
}
map<const Binding*, bool>& inline_constructor_reference_parameter_cache()
{
	static map<const Binding*, bool> cache;
	return cache;
}
map<const Binding*, TypePtr>& inline_function_record_result_cache()
{
	static map<const Binding*, TypePtr> cache;
	return cache;
}
map<const Binding*, bool>& inline_constructor_no_explicit_parameter_cache()
{
	static map<const Binding*, bool> cache;
	return cache;
}
map<const Binding*, TypePtr>& inline_first_this_record_cache()
{
	static map<const Binding*, TypePtr> cache;
	return cache;
}
map<const Binding*, size_t>& inline_template_owner_depth_cache()
{
	static map<const Binding*, size_t> cache;
	return cache;
}
map<const Binding*, bool>& inline_template_record_owner_cache()
{
	static map<const Binding*, bool> cache;
	return cache;
}
void clear_lowir_inline_order_caches()
{
	inline_class_constructor_cache().clear();
	inline_constructor_reference_parameter_cache().clear();
	inline_function_record_result_cache().clear();
	inline_constructor_no_explicit_parameter_cache().clear();
	inline_first_this_record_cache().clear();
	inline_template_owner_depth_cache().clear();
	inline_template_record_owner_cache().clear();
}
}  // namespace internal
}  // namespace pa14
