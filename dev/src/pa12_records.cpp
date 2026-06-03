#include "pa12_internal.h"

#include <stdexcept>

using namespace std;

namespace pa12 {
namespace internal {

TypePtr Parser::make_member_function_type(Scope* class_scope, TypePtr type)
{
	TypePtr class_type = pa11::record_type_for_scope(class_scope);
	if (class_type.get() == NULL)
		class_type = pa11::make_record_type(class_scope->name,
		                                    "struct",
		                                    true,
		                                    class_scope);
	if (type->cv != pa11::CV_NONE)
		class_type = pa11::make_cv(class_type, type->cv);
	vector<TypePtr> params;
	params.push_back(pa11::make_pointer(class_type));
	for (size_t i = 0; i < type->parameters.size(); ++i)
		params.push_back(type->parameters[i]);
	return pa11::make_function(type->base, params, type->variadic);
}

Binding* Parser::find_default_constructor(TypePtr type) const
{
	TypePtr bare = pa11::strip_cv(type);
	if (bare->kind != pa11::TypeKind::Record || bare->scope == NULL)
		return NULL;
	map<string, vector<Binding*> >::iterator found =
		bare->scope->members.find(bare->scope->name);
	if (found == bare->scope->members.end())
		return NULL;
	for (size_t i = 0; i < found->second.size(); ++i)
	{
		Binding* binding = found->second[i];
		if (binding->kind == BindingKind::Function &&
		    binding->type->kind == pa11::TypeKind::Function &&
		    binding->type->parameters.size() == 1)
			return binding;
		if (binding->kind == BindingKind::Function &&
		    binding->type->kind == pa11::TypeKind::Function)
		{
			map<Binding*, vector<Expr> >::const_iterator defaults =
				default_arguments_.find(binding);
			if (defaults == default_arguments_.end())
				continue;
			bool have_defaults = true;
			for (size_t j = 1; j < binding->type->parameters.size(); ++j)
				if (j >= defaults->second.size() || !defaults->second[j].valid)
					have_defaults = false;
			if (have_defaults)
				return binding;
		}
	}
	return NULL;
}

Binding* Parser::ensure_default_constructor(TypePtr type, bool force_trivial)
{
	TypePtr bare = pa11::strip_cv(type);
	if (bare->kind != pa11::TypeKind::Record)
		return NULL;
	Binding* existing = find_default_constructor(bare);
	if (existing != NULL)
		return existing;
	pa11::layout_record_type(bare);
	vector<Node> init_actions;
	if (!force_trivial || !bare->fields.empty())
	{
		TypePtr direct_base = bare->base.get() != NULL ? pa11::strip_cv(bare->base) :
			TypePtr();
		if (direct_base.get() != NULL &&
		    direct_base->kind == pa11::TypeKind::Record &&
		    ensure_default_constructor(direct_base) != NULL)
			init_actions.push_back(make_base_init_action(direct_base, NULL));
		for (size_t i = 0; i < bare->fields.size(); ++i)
		{
			Binding* field = bare->fields[i];
			map<Binding*, Node>::const_iterator init =
				default_member_initializers_.find(field);
			if (init != default_member_initializers_.end())
				init_actions.push_back(make_member_init_action(field, &init->second));
			else
			{
				TypePtr field_bare = pa11::strip_cv(field->type);
				if (ensure_default_constructor(field->type) != NULL ||
				    (field_bare->kind == pa11::TypeKind::Array &&
				     ensure_default_constructor(field_bare->base) != NULL))
					init_actions.push_back(make_member_init_action(field, NULL));
				else if (field_bare->kind == pa11::TypeKind::Record &&
				         field_bare->scope != NULL)
				{
					map<string, vector<Binding*> >::const_iterator ctors =
						field_bare->scope->members.find(field_bare->scope->name);
					if (ctors != field_bare->scope->members.end() &&
					    !ctors->second.empty())
						throw runtime_error("member has no default constructor");
				}
			}
		}
	}
	bool has_declared_constructor = false;
	if (bare->scope != NULL)
	{
		map<string, vector<Binding*> >::const_iterator ctors =
			bare->scope->members.find(bare->scope->name);
		if (ctors != bare->scope->members.end())
			for (size_t i = 0; i < ctors->second.size(); ++i)
				if (ctors->second[i]->kind == BindingKind::Function)
					has_declared_constructor = true;
	}
	bool empty_implicit_record =
		bare->fields.empty() && bare->base.get() == NULL &&
		!has_declared_constructor;
	bool union_record = bare->tag == "union" && !has_declared_constructor;
	if (init_actions.empty() && !force_trivial &&
	    !empty_implicit_record && !union_record)
	{
		return NULL;
	}

	string ctor_name = bare->name + "::" + bare->name;
	if (generated_default_ctors_.find(ctor_name) != generated_default_ctors_.end())
		return find_default_constructor(bare);
	generated_default_ctors_.insert(ctor_name);

	TypePtr this_type = pa11::make_pointer(bare);
	vector<TypePtr> params;
	params.push_back(this_type);
	TypePtr fn_type = pa11::make_function(pa11::make_fundamental(FT_VOID),
	                                      params,
	                                      false);
	Binding* ctor = add_value(bare->scope, BindingKind::Function,
	                          bare->scope->name, fn_type);
	ctor->is_inline_definition = true;
	ctor->is_generated_default_constructor = true;
	Node fn("function-definition " + qualified_decl_name(ctor) + " " +
	        pa11::describe_type(fn_type));
	fn.binding = ctor;
	fn.type = fn_type;
	Node param("parameter this " + pa11::describe_type(this_type));
	param.type = this_type;
	add_child(fn, param);
	Node body("compound-statement");
	for (size_t i = 0; i < init_actions.size(); ++i)
		add_child(body, init_actions[i]);
	add_child(fn, body);
	generated_nodes_.push_back(fn);
	extra_lowir_nodes_.push_back(fn);
	return ctor;
}

Binding* Parser::ensure_aggregate_constructor(TypePtr type, size_t arg_count)
{
	TypePtr bare = pa11::strip_cv(type);
	if (bare->kind != pa11::TypeKind::Record || bare->scope == NULL ||
	    arg_count == 0)
		return NULL;
	map<string, vector<Binding*> >::const_iterator existing =
		bare->scope->members.find(bare->scope->name);
	if (existing != bare->scope->members.end())
	{
		for (size_t i = 0; i < existing->second.size(); ++i)
		{
			Binding* binding = existing->second[i];
			if (binding->kind == BindingKind::Function &&
			    binding->type->kind == pa11::TypeKind::Function &&
			    binding->type->parameters.size() == arg_count + 1)
				return binding;
		}
	}
	pa11::layout_record_type(bare);
	if (arg_count > bare->fields.size())
		return NULL;
	string key = bare->name + "::aggregate:" + to_string(arg_count);
	if (generated_aggregate_ctors_.find(key) != generated_aggregate_ctors_.end())
	{
		existing = bare->scope->members.find(bare->scope->name);
		if (existing != bare->scope->members.end())
			for (size_t i = 0; i < existing->second.size(); ++i)
				if (existing->second[i]->kind == BindingKind::Function &&
				    existing->second[i]->type->parameters.size() == arg_count + 1)
					return existing->second[i];
		return NULL;
	}
	generated_aggregate_ctors_.insert(key);
	TypePtr this_type = pa11::make_pointer(bare);
	vector<TypePtr> params;
	vector<string> names;
	params.push_back(this_type);
	names.push_back("this");
	for (size_t i = 0; i < arg_count; ++i)
	{
		params.push_back(bare->fields[i]->type);
		names.push_back(bare->fields[i]->name.empty()
		                ? "__param" + to_string(i + 1)
		                : bare->fields[i]->name);
	}
	TypePtr fn_type = pa11::make_function(pa11::make_fundamental(FT_VOID),
	                                      params,
	                                      false);
	Binding* ctor = add_value(bare->scope, BindingKind::Function,
	                          bare->scope->name, fn_type);
	ctor->is_inline_definition = true;
	ctor->unwind_no = true;
	function_parameter_names_[ctor] = names;
	Node fn("function-definition " + qualified_decl_name(ctor) + " " +
	        pa11::describe_type(fn_type));
	fn.binding = ctor;
	fn.type = fn_type;
	Scope* function_scope =
		pa11::create_child_scope(bare->scope, ScopeKind::Function, ctor->name);
	Binding* this_binding =
		pa11::add_binding(function_scope,
		                  BindingKind::Parameter,
		                  "this",
		                  this_type);
	Node this_node("parameter this " + pa11::describe_type(this_type));
	this_node.binding = this_binding;
	this_node.type = this_type;
	add_child(fn, this_node);
	Node body("compound-statement");
	for (size_t i = 0; i < arg_count; ++i)
	{
		Binding* param_binding =
			pa11::add_binding(function_scope,
			                  BindingKind::Parameter,
			                  names[i + 1],
			                  params[i + 1]);
		Node param("parameter " + names[i + 1] + " " +
		           pa11::describe_type(params[i + 1]));
		param.binding = param_binding;
		param.type = params[i + 1];
		add_child(fn, param);
		Node arg("id-expression lvalue " + pa11::describe_type(params[i + 1]) +
		         " " + names[i + 1]);
		arg.binding = param_binding;
		arg.type = params[i + 1];
		arg.category = ValueCategory::LValue;
		add_child(body, make_member_init_action(bare->fields[i], &arg));
	}
	add_child(fn, body);
	extra_lowir_nodes_.push_back(fn);
	return ctor;
}

namespace {

Binding* find_destructor_binding(TypePtr type)
{
	TypePtr bare = pa11::strip_cv(type);
	if (bare->kind != pa11::TypeKind::Record || bare->scope == NULL)
		return NULL;
	string name = "~" + bare->scope->name;
	map<string, vector<Binding*> >::const_iterator found =
		bare->scope->members.find(name);
	if (found == bare->scope->members.end())
		return NULL;
	for (size_t i = 0; i < found->second.size(); ++i)
		if (found->second[i]->kind == BindingKind::Function)
			return found->second[i];
	return NULL;
}

}  // namespace

Binding* Parser::ensure_default_destructor(TypePtr type, bool force_trivial)
{
	TypePtr bare = pa11::strip_cv(type);
	if (bare->kind == pa11::TypeKind::Array)
		return ensure_default_destructor(bare->base, force_trivial);
	if (bare->kind != pa11::TypeKind::Record || bare->scope == NULL)
		return NULL;
	Binding* existing = find_destructor_binding(bare);
	if (existing != NULL)
		return existing;
	pa11::layout_record_type(bare);
	vector<Node> fini_actions;
	if (!force_trivial || !bare->fields.empty())
	{
		for (size_t n = 0; n < bare->fields.size(); ++n)
		{
			size_t i = bare->fields.size() - 1 - n;
			if (ensure_default_destructor(bare->fields[i]->type) != NULL)
				fini_actions.push_back(make_member_fini_action(bare->fields[i]));
		}
		TypePtr direct_base = bare->base.get() != NULL
			? pa11::strip_cv(bare->base) : TypePtr();
		if (direct_base.get() != NULL &&
		    direct_base->kind == pa11::TypeKind::Record &&
		    ensure_default_destructor(direct_base) != NULL)
			fini_actions.push_back(make_base_fini_action(direct_base));
	}
	if (fini_actions.empty() && !force_trivial)
		return NULL;
	string key = bare->name + "::~";
	if (generated_dtors_.find(key) != generated_dtors_.end())
		return find_destructor_binding(bare);
	generated_dtors_.insert(key);
	TypePtr this_type = pa11::make_pointer(bare);
	vector<TypePtr> params(1, this_type);
	TypePtr fn_type = pa11::make_function(pa11::make_fundamental(FT_VOID),
	                                      params,
	                                      false);
	Binding* dtor = add_value(bare->scope, BindingKind::Function,
	                          "~" + bare->scope->name, fn_type);
	dtor->is_inline_definition = true;
	function_parameter_names_[dtor] = vector<string>(1, "this");
	Node fn("function-definition " + qualified_decl_name(dtor) + " " +
	        pa11::describe_type(fn_type));
	fn.binding = dtor;
	fn.type = fn_type;
	Scope* function_scope =
		pa11::create_child_scope(bare->scope, ScopeKind::Function, dtor->name);
	Binding* this_binding =
		pa11::add_binding(function_scope,
		                  BindingKind::Parameter,
		                  "this",
		                  this_type);
	Node param("parameter this " + pa11::describe_type(this_type));
	param.binding = this_binding;
	param.type = this_type;
	add_child(fn, param);
	Node body("compound-statement");
	for (size_t i = 0; i < fini_actions.size(); ++i)
		add_child(body, fini_actions[i]);
	add_child(fn, body);
	extra_lowir_nodes_.push_back(fn);
	return dtor;
}

void Parser::ensure_aggregate_constructors_for_init(TypePtr type, const Node& init)
{
	if (init.line.compare(0, 16, "braced-init-list") != 0)
		return;
	TypePtr bare = pa11::strip_cv(type);
	if (bare->kind == pa11::TypeKind::Array)
	{
		for (size_t i = 0; i < init.children.size(); ++i)
			ensure_aggregate_constructors_for_init(bare->base, init.children[i]);
		return;
	}
	if (bare->kind != pa11::TypeKind::Record)
		return;
	if (pa11::type_has_const(type))
		ensure_aggregate_constructor(bare, init.children.size());
	pa11::layout_record_type(bare);
	for (size_t i = 0; i < init.children.size() && i < bare->fields.size(); ++i)
		ensure_aggregate_constructors_for_init(bare->fields[i]->type,
		                                       init.children[i]);
}

Node Parser::make_member_init_action(Binding* field, const Node* init)
{
	Node action("member-init-action " + field->name);
	action.binding = field;
	action.type = field->type;
	if (init != NULL)
	{
		Node child = *init;
		if (child.line == "braced-init-list")
		{
			child.line += " lvalue " + pa11::describe_type(field->type);
			child.type = field->type;
		}
		add_child(action, child);
	}
	TypePtr bare = pa11::strip_cv(field->type);
	if (bare->kind == pa11::TypeKind::Record)
	{
		action.direct_call = ensure_default_constructor(field->type);
		if (init == NULL && action.direct_call != NULL)
		{
			map<Binding*, vector<Expr> >::const_iterator defaults =
				default_arguments_.find(action.direct_call);
			if (defaults != default_arguments_.end())
				for (size_t j = 1;
				     j < action.direct_call->type->parameters.size(); ++j)
					add_child(action, defaults->second[j].node);
		}
	}
	return action;
}

Node Parser::make_member_fini_action(Binding* field)
{
	Node action("member-fini-action " + field->name);
	action.binding = field;
	action.type = field->type;
	return action;
}

Node Parser::make_base_init_action(TypePtr base, const Node* init)
{
	TypePtr bare = pa11::strip_cv(base);
	Node action("base-init-action " + bare->name);
	action.type = bare;
	if (init != NULL)
	{
		Node child = *init;
		add_child(action, child);
	}
	else
	{
		Binding* ctor = find_default_constructor(bare);
		if (ctor != NULL)
		{
			map<Binding*, vector<Expr> >::const_iterator defaults =
				default_arguments_.find(ctor);
			if (defaults != default_arguments_.end())
				for (size_t j = 1; j < ctor->type->parameters.size(); ++j)
					add_child(action, defaults->second[j].node);
		}
	}
	return action;
}

Node Parser::make_base_fini_action(TypePtr base)
{
	TypePtr bare = pa11::strip_cv(base);
	Node action("base-fini-action " + bare->name);
	action.type = bare;
	return action;
}

bool Parser::initializer_names_direct_base(Scope* class_scope,
                                           TypePtr direct_base,
                                           const string& name)
{
	TypePtr bare = pa11::strip_cv(direct_base);
	if (bare->kind != pa11::TypeKind::Record || bare->scope == NULL)
		return false;
	if (name == bare->scope->name)
		return true;
	vector<Binding*> types =
		lookup_unqualified_set(class_scope, name, pa11::LOOKUP_TYPE);
	for (size_t i = 0; i < types.size(); ++i)
		if (pa11::same_type(pa11::strip_cv(types[i]->type), bare))
			return true;
	return false;
}

Node Parser::default_constructor_action(Binding* variable)
{
	TypePtr bare = pa11::strip_cv(variable->type);
	if (bare->kind != pa11::TypeKind::Record)
		throw runtime_error("default constructor action requires record");
	string ctor_name = bare->name + "::" + bare->name;
	Binding* ctor = ensure_default_constructor(bare);
	if (ctor == NULL)
		throw runtime_error("missing default constructor");

	Node action("constructor-action " + ctor_name);
	Node call("call-expression prvalue void");
	call.direct_call = ctor;
	call.type = ctor->type->base;
	add_child(call, Node("callee " + qualified_decl_name(ctor) + " " +
	                     pa11::describe_type(ctor->type)));
	TypePtr this_type = ctor->type->parameters[0];
	Node amp("unary-expression prvalue " + pa11::describe_type(this_type) +
	         " OP_AMP:&");
	amp.type = this_type;
	amp.category = ValueCategory::PRValue;
	amp.has_op = true;
	amp.op = OP_AMP;
	amp.token_text = "&";
	TypePtr object_type = expression_object_type(variable->type);
	Node object("id-expression lvalue " +
	            pa11::describe_type(object_type) + " " + variable->name);
	object.binding = variable;
	object.type = object_type;
	object.category = ValueCategory::LValue;
	add_child(amp, object);
	add_child(call, amp);
	map<Binding*, vector<Expr> >::const_iterator defaults =
		default_arguments_.find(ctor);
	if (defaults != default_arguments_.end())
		for (size_t j = 1; j < ctor->type->parameters.size(); ++j)
			add_child(call, defaults->second[j].node);
	add_child(action, call);
	return action;
}

void Parser::resolve_pending_member_initializers(Scope* class_scope, Node& node)
{
	if (node.line.compare(0, 18, "member-init-action") == 0 &&
	    node.binding == NULL &&
	    !node.token_text.empty())
	{
		Binding* field = pa11::lookup_qualified(class_scope,
		                                        node.token_text,
		                                        pa11::LOOKUP_VARIABLE);
		if (field != NULL && !field->is_static_member)
		{
			node.binding = field;
			node.type = field->type;
			if (!node.children.empty())
			{
				node.children[0].type = field->type;
				if (node.children[0].line == "braced-init-list")
					node.children[0].line += " lvalue " +
						pa11::describe_type(field->type);
			}
			TypePtr bare = pa11::strip_cv(field->type);
			if (bare->kind == pa11::TypeKind::Record)
				node.direct_call = ensure_default_constructor(field->type);
		}
	}
	for (size_t i = 0; i < node.children.size(); ++i)
		resolve_pending_member_initializers(class_scope, node.children[i]);
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
