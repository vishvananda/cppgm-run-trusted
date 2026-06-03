#include "pa12_internal.h"

#include <stdexcept>

using namespace std;

namespace pa12 {
namespace internal {

TypePtr Parser::make_member_function_type(Scope* class_scope, TypePtr type)
{
	TypePtr class_type = pa11::make_record_type(class_scope->name,
	                                            "struct",
	                                            true,
	                                            class_scope);
	if (type->cv & pa11::CV_CONST)
		class_type = pa11::make_cv(class_type, pa11::CV_CONST);
	vector<TypePtr> params;
	params.push_back(pa11::make_pointer(class_type));
	for (size_t i = 0; i < type->parameters.size(); ++i)
		params.push_back(type->parameters[i]);
	return pa11::make_function(type->base, params, type->variadic);
}

void Parser::ensure_default_constructor(TypePtr type)
{
	TypePtr bare = pa11::strip_cv(type);
	if (bare->kind != pa11::TypeKind::Record)
		return;
	string ctor_name = bare->name + "::" + bare->name;
	if (generated_default_ctors_.find(ctor_name) != generated_default_ctors_.end())
		return;
	generated_default_ctors_.insert(ctor_name);

	TypePtr this_type = pa11::make_pointer(bare);
	vector<TypePtr> params;
	params.push_back(this_type);
	TypePtr fn_type = pa11::make_function(pa11::make_fundamental(FT_VOID),
	                                      params,
	                                      false);
	Node fn("function-definition " + ctor_name + " " +
	        pa11::describe_type(fn_type));
	add_child(fn, Node("parameter this " + pa11::describe_type(this_type)));
	add_child(fn, Node("compound-statement"));
	generated_nodes_.push_back(fn);
}

Node Parser::default_constructor_action(Binding* variable)
{
	TypePtr bare = pa11::strip_cv(variable->type);
	if (bare->kind != pa11::TypeKind::Record)
		throw runtime_error("default constructor action requires record");
	string ctor_name = bare->name + "::" + bare->name;
	TypePtr this_type = pa11::make_pointer(bare);
	vector<TypePtr> params;
	params.push_back(this_type);
	TypePtr fn_type = pa11::make_function(pa11::make_fundamental(FT_VOID),
	                                      params,
	                                      false);

	Node action("constructor-action " + ctor_name);
	Node call("call-expression prvalue void");
	add_child(call, Node("callee " + ctor_name + " " + pa11::describe_type(fn_type)));
	Node amp("unary-expression prvalue " + pa11::describe_type(this_type) +
	         " OP_AMP:&");
	TypePtr object_type = expression_object_type(variable->type);
	add_child(amp, Node("id-expression lvalue " +
	                    pa11::describe_type(object_type) + " " +
	                    variable->name));
	add_child(call, amp);
	add_child(action, call);
	return action;
}

void Parser::inject_anonymous_union_members(Scope* class_scope, Binding* storage)
{
	for (size_t i = 0; i < class_scope->binding_order.size(); ++i)
	{
		Binding* member = class_scope->binding_order[i];
		if (member->kind != BindingKind::Variable)
			continue;
		Binding* injected = add_value(storage->owner,
		                              BindingKind::Variable,
		                              member->name,
		                              member->type);
		injected->target_scope = class_scope;
		injected->aliased_binding = storage;
	}
}

}  // namespace internal
}  // namespace pa12
