#include "pa12_internal.h"
#include <stdexcept>
using namespace std;
namespace pa12 {
namespace internal {
namespace {
bool record_has_reference_field(TypePtr type);
}  // namespace
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
	complete_template_record(bare);
	bool reemit_stale_generated_default = false;
	Binding* existing = find_default_constructor(bare);
	if (existing != NULL)
	{
		parse_pending_member_body(existing);
		bool have_extra_definition = false;
		for (size_t i = 0; i < extra_lowir_nodes_.size(); ++i)
			if (extra_lowir_nodes_[i].binding == existing)
				have_extra_definition = true;
		if (existing->is_generated_default_constructor &&
		    existing->is_inline_definition &&
		    !have_extra_definition)
			existing->is_inline_definition = false;
		bool stale_generated_default =
			!existing->is_inline_definition &&
			existing->is_generated_default_constructor;
		if (!stale_generated_default)
			return existing;
		existing->is_generated_default_constructor = true;
		reemit_stale_generated_default = true;
	}
	pa11::layout_record_type(bare);
	vector<Node> init_actions;
	if (!force_trivial || !bare->fields.empty())
	{
		TypePtr direct_base = bare->base.get() != NULL ? pa11::strip_cv(bare->base) :
			TypePtr();
		Binding* base_ctor = direct_base.get() != NULL &&
		                      direct_base->kind == pa11::TypeKind::Record
			? ensure_default_constructor(direct_base) : NULL;
		if (direct_base.get() != NULL &&
		    direct_base->kind == pa11::TypeKind::Record &&
		    base_ctor != NULL &&
		    (!(base_ctor->is_generated_default_constructor && base_ctor->unwind_no) ||
		     direct_base->is_polymorphic))
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
				Binding* field_ctor = ensure_default_constructor(field->type);
				Binding* elem_ctor = field_bare->kind == pa11::TypeKind::Array
					? ensure_default_constructor(field_bare->base) : NULL;
				bool field_noop = field_ctor != NULL &&
				                  field_ctor->is_generated_default_constructor &&
				                  field_ctor->unwind_no;
				bool elem_noop = elem_ctor != NULL &&
				                 elem_ctor->is_generated_default_constructor &&
				                 elem_ctor->unwind_no;
				if ((field_ctor != NULL && !field_noop) ||
				    (elem_ctor != NULL && !elem_noop))
					init_actions.push_back(make_member_init_action(field, NULL));
				else if (field_ctor == NULL &&
				         elem_ctor == NULL &&
				         field_bare->kind == pa11::TypeKind::Record &&
				         field_bare->scope != NULL)
				{
					map<string, vector<Binding*> >::const_iterator ctors =
						field_bare->scope->members.find(field_bare->scope->name);
					bool has_user_ctor = false;
					if (ctors != field_bare->scope->members.end())
						for (size_t j = 0; j < ctors->second.size(); ++j)
						{
							Binding* ctor = ctors->second[j];
							if (ctor->kind == BindingKind::Function &&
							    !ctor->is_generated_default_constructor &&
							    !ctor->is_generated_aggregate_constructor &&
							    !ctor->is_generated_copy_move_constructor)
								has_user_ctor = true;
						}
					if (has_user_ctor)
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
				if (ctors->second[i]->kind == BindingKind::Function &&
				    !ctors->second[i]->is_generated_default_constructor &&
				    !ctors->second[i]->is_generated_aggregate_constructor &&
				    !ctors->second[i]->is_generated_copy_move_constructor)
					has_declared_constructor = true;
	}
	bool empty_implicit_record =
		(bare->tag == "union" ||
		 (bare->fields.empty() && bare->base.get() == NULL)) &&
		!has_declared_constructor;
	if (has_declared_constructor)
		return NULL;
	if (init_actions.empty() && !force_trivial &&
	    !empty_implicit_record && !bare->is_polymorphic)
	{
		return NULL;
	}
	const void* key = bare.get();
	if (generated_default_ctors_.find(key) != generated_default_ctors_.end())
	{
		Binding* generated = find_default_constructor(bare);
		if (!(generated != NULL &&
		      generated->is_generated_default_constructor &&
		      !generated->is_inline_definition))
			return generated;
		existing = generated;
	}
	generated_default_ctors_.insert(key);
	TypePtr this_type = pa11::make_pointer(bare);
	vector<TypePtr> params;
	params.push_back(this_type);
	TypePtr fn_type = pa11::make_function(pa11::make_fundamental(FT_VOID),
	                                      params,
	                                      false);
	Binding* ctor = existing != NULL
		? existing
		: add_value(bare->scope, BindingKind::Function,
		            bare->scope->name, fn_type);
	ctor->type = fn_type;
	ctor->is_inline_definition = true;
	if (reemit_stale_generated_default)
		ctor->is_inline_definition = false;
	ctor->is_generated_default_constructor = true;
	ctor->is_noop_constructor = init_actions.empty();
	ctor->unwind_no = init_actions.empty();
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
	remember_function_body(ctor, fn);
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
	pair<const void*, size_t> key(bare.get(), arg_count);
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
	ctor->is_generated_aggregate_constructor = true;
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
		remember_function_body(ctor, fn);
		extra_lowir_nodes_.push_back(fn);
		return ctor;
	}
namespace {
bool constructor_trailing_parameters_have_defaults(
	Binding* binding,
	const map<Binding*, vector<Expr> >* default_arguments)
{
	if (binding->type->parameters.size() <= 2)
		return true;
	if (default_arguments == NULL)
		return false;
	map<Binding*, vector<Expr> >::const_iterator found =
		default_arguments->find(binding);
	if (found == default_arguments->end())
		return false;
	for (size_t i = 2; i < binding->type->parameters.size(); ++i)
		if (i >= found->second.size() || !found->second[i].valid)
			return false;
	return true;
}
Binding* find_copy_move_constructor_binding(
	TypePtr type,
	bool move,
	const map<Binding*, vector<Expr> >* default_arguments = NULL)
{
	TypePtr bare = pa11::strip_cv(type);
	if (bare->kind != pa11::TypeKind::Record || bare->scope == NULL)
		return NULL;
	map<string, vector<Binding*> >::const_iterator found =
		bare->scope->members.find(bare->scope->name);
	if (found == bare->scope->members.end())
		return NULL;
	for (size_t i = 0; i < found->second.size(); ++i)
	{
		Binding* binding = found->second[i];
		if (binding->kind != BindingKind::Function ||
		    binding->type->kind != pa11::TypeKind::Function ||
		    binding->type->parameters.size() < 2 ||
		    !pa11::is_reference_type(binding->type->parameters[1]))
			continue;
		if (!constructor_trailing_parameters_have_defaults(binding,
		                                                   default_arguments))
			continue;
		TypePtr param = binding->type->parameters[1];
		if (move && param->kind != pa11::TypeKind::RValueReference)
			continue;
		if (!move && param->kind != pa11::TypeKind::LValueReference)
			continue;
		if (pa11::same_type(pa11::strip_cv(param->base), bare))
			return binding;
	}
	return NULL;
}
bool is_copy_move_assignment_for_record(Binding* binding, TypePtr record)
{
	if (binding->kind != BindingKind::Function ||
	    binding->name != "operator=" ||
	    !binding->function_specialization_symbol.empty() ||
	    binding->type->kind != pa11::TypeKind::Function ||
	    binding->type->parameters.size() != 2)
		return false;
	TypePtr param = binding->type->parameters[1];
	TypePtr param_object = pa11::is_reference_type(param) ? param->base : param;
	return pa11::same_type(pa11::strip_cv(param_object),
	                       pa11::strip_cv(record));
}
Binding* find_copy_move_assignment_binding(TypePtr type, bool move)
{
	TypePtr bare = pa11::strip_cv(type);
	if (bare->kind != pa11::TypeKind::Record || bare->scope == NULL)
		return NULL;
	map<string, vector<Binding*> >::const_iterator found =
		bare->scope->members.find("operator=");
	if (found == bare->scope->members.end())
		return NULL;
	for (size_t i = 0; i < found->second.size(); ++i)
	{
		Binding* binding = found->second[i];
		if (!is_copy_move_assignment_for_record(binding, bare))
			continue;
		TypePtr param = binding->type->parameters[1];
		if (move && param->kind == pa11::TypeKind::RValueReference)
			return binding;
		if (!move && param->kind != pa11::TypeKind::RValueReference)
			return binding;
	}
	return NULL;
}
bool suppresses_implicit_move(
	TypePtr type,
	const map<Binding*, vector<Expr> >* default_arguments)
{
	TypePtr bare = pa11::strip_cv(type);
	if (bare->kind != pa11::TypeKind::Record || bare->scope == NULL)
		return false;
	map<string, vector<Binding*> >::const_iterator ctors =
		bare->scope->members.find(bare->scope->name);
	if (ctors != bare->scope->members.end())
		for (size_t i = 0; i < ctors->second.size(); ++i)
			if (!ctors->second[i]->is_generated_copy_move_constructor &&
			    (find_copy_move_constructor_binding(
				     bare, false, default_arguments) == ctors->second[i] ||
			     find_copy_move_constructor_binding(
				     bare, true, default_arguments) == ctors->second[i]))
				return true;
	map<string, vector<Binding*> >::const_iterator dtors =
		bare->scope->members.find("~" + bare->scope->name);
	if (dtors != bare->scope->members.end())
		for (size_t i = 0; i < dtors->second.size(); ++i)
			if (dtors->second[i]->kind == BindingKind::Function)
			{
				if (!dtors->second[i]->is_generated_default_destructor)
					return true;
			}
	map<string, vector<Binding*> >::const_iterator assigns =
		bare->scope->members.find("operator=");
	if (assigns != bare->scope->members.end())
		for (size_t i = 0; i < assigns->second.size(); ++i)
			if (!assigns->second[i]->is_generated_copy_move_assignment &&
			    is_copy_move_assignment_for_record(assigns->second[i], bare))
				return true;
	return false;
}
bool type_needs_copy_move_helper(
	TypePtr type,
	bool move,
	const map<Binding*, vector<Expr> >* default_arguments);
bool constructor_binding_needs_helper(Binding* binding)
{
	return binding != NULL &&
	       binding->is_inline_definition &&
	       !binding->is_defaulted;
}
bool record_needs_copy_move_helper(
	TypePtr type,
	bool move,
	const map<Binding*, vector<Expr> >* default_arguments)
{
	TypePtr bare = pa11::strip_cv(type);
	Binding* exact =
		find_copy_move_constructor_binding(bare, move, default_arguments);
	if (constructor_binding_needs_helper(exact))
		return true;
	if (move &&
	    constructor_binding_needs_helper(
		    find_copy_move_constructor_binding(
			    bare, false, default_arguments)))
		return true;
	pa11::layout_record_type(bare);
	if (bare->base.get() != NULL &&
	    type_needs_copy_move_helper(bare->base, move, default_arguments))
		return true;
	for (size_t i = 0; i < bare->fields.size(); ++i)
	{
		if (bare->fields[i]->is_bit_field)
			continue;
		if (type_needs_copy_move_helper(
			    bare->fields[i]->type, move, default_arguments))
			return true;
	}
	return false;
}
bool type_needs_copy_move_helper(
	TypePtr type,
	bool move,
	const map<Binding*, vector<Expr> >* default_arguments)
{
	TypePtr bare = pa11::strip_cv(type);
	if (bare->kind == pa11::TypeKind::Array)
		return type_needs_copy_move_helper(
			bare->base, move, default_arguments);
	if (bare->kind != pa11::TypeKind::Record || bare->scope == NULL)
		return false;
	return record_needs_copy_move_helper(bare, move, default_arguments);
}
bool type_needs_copy_move_assignment_helper(TypePtr type, bool move);
bool assignment_binding_needs_helper(Binding* binding)
{
	return binding != NULL && binding->is_inline_definition;
}
bool record_needs_copy_move_assignment_helper(TypePtr type, bool move)
{
	TypePtr bare = pa11::strip_cv(type);
	Binding* exact = find_copy_move_assignment_binding(bare, move);
	if (assignment_binding_needs_helper(exact))
		return true;
	if (move &&
	    assignment_binding_needs_helper(
		    find_copy_move_assignment_binding(bare, false)))
		return true;
	pa11::layout_record_type(bare);
	if (bare->base.get() != NULL &&
	    type_needs_copy_move_assignment_helper(bare->base, move))
		return true;
	for (size_t i = 0; i < bare->fields.size(); ++i)
	{
		if (bare->fields[i]->is_bit_field)
			continue;
		if (type_needs_copy_move_assignment_helper(bare->fields[i]->type, move))
			return true;
	}
	return false;
}
bool type_needs_copy_move_assignment_helper(TypePtr type, bool move)
{
	TypePtr bare = pa11::strip_cv(type);
	if (bare->kind == pa11::TypeKind::Array)
		return type_needs_copy_move_assignment_helper(bare->base, move);
	if (bare->kind != pa11::TypeKind::Record || bare->scope == NULL)
		return false;
	return record_needs_copy_move_assignment_helper(bare, move);
}
Node make_parameter_lvalue(Binding* binding, TypePtr expr_type)
{
	Node node("id-expression lvalue " + pa11::describe_type(expr_type) +
	          " " + binding->name);
	node.binding = binding;
	node.type = expr_type;
	node.category = ValueCategory::LValue;
	return node;
}
Node make_this_pointer_node(Binding* binding, TypePtr type)
{
	Node node("id-expression prvalue " + pa11::describe_type(type) +
	          " this");
	node.binding = binding;
	node.type = type;
	node.category = ValueCategory::PRValue;
	return node;
}
Node make_deref_node(TypePtr type, const Node& inner)
{
	Node node("unary-expression lvalue " + pa11::describe_type(type) +
	          " OP_STAR:*");
	node.type = type;
	node.category = ValueCategory::LValue;
	node.has_op = true;
	node.op = OP_STAR;
	node.token_text = "*";
	add_child(node, inner);
	return node;
}
Expr expr_from_node(const Node& node)
{
	Expr expr;
	expr.valid = true;
	expr.node = node;
	expr.type = node.type;
	expr.category = node.category;
	expr.binding = node.binding;
	return expr;
}
Expr target_field_expr(Binding* field, const Node& object)
{
	Node member("member-expression lvalue " +
	            pa11::describe_type(field->type) + " " + field->name);
	member.binding = field;
	member.type = field->type;
	member.category = ValueCategory::LValue;
	add_child(member, object);
	return expr_from_node(member);
}
Expr target_base_expr(TypePtr base, const Node& object)
{
	TypePtr bare = pa11::strip_cv(base);
	Node node("base-subobject-expression lvalue " +
	          pa11::describe_type(bare));
	node.type = bare;
	node.category = ValueCategory::LValue;
	add_child(node, object);
	return expr_from_node(node);
}
Node make_move_cast(TypePtr type, const Node& inner)
{
	Node node("cast-expression xvalue " + pa11::describe_type(type));
	node.type = type;
	node.category = ValueCategory::XValue;
	add_child(node, inner);
	return node;
}
Node source_field_expr(Binding* field, const Node& object, bool move)
{
	Node member("member-expression lvalue " +
	            pa11::describe_type(field->type) + " OP_DOT:" + field->name);
	member.binding = field;
	member.type = field->type;
	member.category = ValueCategory::LValue;
	member.has_op = true;
	member.op = OP_DOT;
	member.token_text = field->name;
	add_child(member, object);
	if (move)
		return make_move_cast(field->type, member);
	return member;
}
Node source_base_expr(TypePtr base, const Node& object, bool move)
{
	TypePtr bare = pa11::strip_cv(base);
	Node node("base-subobject-expression lvalue " +
	          pa11::describe_type(bare));
	node.type = bare;
	node.category = ValueCategory::LValue;
	add_child(node, object);
	if (move)
		return make_move_cast(bare, node);
	return node;
}
}  // namespace
bool Parser::copy_move_constructor_available(TypePtr type, bool move)
{
	TypePtr bare = pa11::strip_cv(type);
	if (bare->kind == pa11::TypeKind::Array)
		return copy_move_constructor_available(bare->base, move);
	if (bare->kind != pa11::TypeKind::Record)
		return true;
	Binding* exact =
		find_copy_move_constructor_binding(bare, move, &default_arguments_);
	if (exact != NULL)
	{
		if (exact->is_defaulted)
			ensure_copy_move_constructor(bare, move);
		return deleted_functions_.find(exact) == deleted_functions_.end();
	}
	if (move)
	{
		Binding* copy =
			find_copy_move_constructor_binding(
				bare, false, &default_arguments_);
		if (copy != NULL)
			return deleted_functions_.find(copy) == deleted_functions_.end();
		if (suppresses_implicit_move(bare, &default_arguments_))
			return false;
	}
	if (!record_needs_copy_move_helper(bare, move, &default_arguments_))
		return true;
	Binding* generated = ensure_copy_move_constructor(bare, move);
	return generated != NULL &&
	       deleted_functions_.find(generated) == deleted_functions_.end();
}
Binding* Parser::ensure_copy_move_constructor(TypePtr type, bool move)
{
	TypePtr bare = pa11::strip_cv(type);
	if (bare->kind != pa11::TypeKind::Record || bare->scope == NULL)
		return NULL;
	Binding* existing =
		find_copy_move_constructor_binding(bare, move, &default_arguments_);
	if (existing == NULL &&
	    move &&
	    suppresses_implicit_move(bare, &default_arguments_))
		return NULL;
	TypePtr source_record = move ? bare : pa11::make_cv(bare, pa11::CV_CONST);
	TypePtr source_ref = move
		? pa11::make_rvalue_reference(bare)
		: pa11::make_lvalue_reference(source_record);
	TypePtr this_type = pa11::make_pointer(bare);
	vector<TypePtr> params;
	params.push_back(this_type);
	params.push_back(source_ref);
	TypePtr fn_type = pa11::make_function(pa11::make_fundamental(FT_VOID),
	                                      params,
	                                      false);
	set<const void*>& generated = move ? generated_move_ctors_ : generated_copy_ctors_;
	const void* key = bare.get();
	Binding* ctor = existing;
	if (ctor == NULL)
	{
		ctor = add_value(bare->scope, BindingKind::Function,
		                 bare->scope->name, fn_type);
		ctor->is_generated_copy_move_constructor = true;
		ctor->is_defaulted = true;
		ctor->is_inline_definition = true;
		ctor->type = fn_type;
		function_parameter_names_[ctor] = vector<string>(2, "this");
		function_parameter_names_[ctor][1] = "other";
	}
	try
	{
		pa11::layout_record_type(bare);
	}
	catch (const runtime_error& err)
	{
		if ((string(err.what()) != "incomplete class type" &&
		     string(err.what()) != "incomplete object type") ||
		    active_class_instantiations_.empty())
			throw;
		return ctor;
	}
	bool needs_helper =
		record_needs_copy_move_helper(bare, move, &default_arguments_);
	bool defaulted_storage_copy = false;
	if (existing != NULL &&
	    !existing->is_generated_copy_move_constructor &&
	    (!existing->is_defaulted || (!needs_helper && !defaulted_storage_copy)))
		return existing;
	if (!needs_helper && !defaulted_storage_copy)
		return ctor;
	if (generated.find(key) != generated.end())
		return find_copy_move_constructor_binding(
			bare, move, &default_arguments_);
	generated.insert(key);
	bool deleted = false;
	vector<Node> init_actions;
	TypePtr direct_base = bare->base.get() != NULL
		? pa11::strip_cv(bare->base) : TypePtr();
	ctor->is_inline_definition = true;
	ctor->type = fn_type;
	string other_name = "other";
	if (existing != NULL)
	{
		map<Binding*, vector<string> >::const_iterator names =
			function_parameter_names_.find(existing);
		if (names != function_parameter_names_.end() &&
		    names->second.size() > 1 &&
		    !names->second[1].empty())
			other_name = names->second[1];
		else if (existing->is_defaulted)
			other_name = "__param1";
	}
	function_parameter_names_[ctor] = vector<string>(2, "this");
	function_parameter_names_[ctor][1] = other_name;
	Scope* function_scope =
		pa11::create_child_scope(bare->scope, ScopeKind::Function, ctor->name);
	Binding* this_binding =
		pa11::add_binding(function_scope,
		                  BindingKind::Parameter,
		                  "this",
		                  this_type);
	Binding* other_binding =
		pa11::add_binding(function_scope,
		                  BindingKind::Parameter,
		                  other_name,
		                  source_ref);
	Node other = make_parameter_lvalue(other_binding, source_record);
	uint64_t copied_prefix = 0;
	if (direct_base.get() != NULL && direct_base->kind == pa11::TypeKind::Record)
	{
		if (!copy_move_constructor_available(direct_base, move))
			deleted = true;
		Node source = source_base_expr(direct_base, other, move);
		init_actions.push_back(
			make_base_init_action(direct_base, &source));
	}
	else
	{
		for (size_t i = 0; i < bare->fields.size(); ++i)
		{
			Binding* field = bare->fields[i];
			if (!type_needs_copy_move_helper(
				    field->type, move, &default_arguments_))
				continue;
			copied_prefix = field->member_offset;
			break;
		}
		if (copied_prefix != 0)
		{
			Node action("storage-copy-action");
			action.type = bare;
			action.has_constant_value = true;
			action.constant_value = copied_prefix;
			add_child(action, other);
			init_actions.push_back(action);
		}
	}
	for (size_t i = 0; i < bare->fields.size(); ++i)
	{
		Binding* field = bare->fields[i];
		if (!copy_move_constructor_available(field->type, move))
			deleted = true;
		if (copied_prefix != 0 &&
		    field->member_offset < copied_prefix &&
		    !type_needs_copy_move_helper(
			    field->type, move, &default_arguments_))
			continue;
		if (!type_needs_copy_move_helper(
			    field->type, move, &default_arguments_))
			continue;
		Node source = source_field_expr(field, other, move);
		init_actions.push_back(
			make_member_init_action(field, &source));
	}
	if (init_actions.empty() &&
	    existing != NULL &&
	    existing->is_defaulted &&
	    !bare->fields.empty())
	{
		Node action("storage-copy-action");
		action.type = bare;
		action.has_constant_value = true;
		action.constant_value = pa11::type_size(bare);
		add_child(action, other);
		init_actions.push_back(action);
	}
	if (deleted)
		deleted_functions_.insert(ctor);
	Node fn("function-definition " + qualified_decl_name(ctor) + " " +
	        pa11::describe_type(fn_type));
	fn.binding = ctor;
	fn.type = fn_type;
		if (existing != NULL && existing->is_defaulted &&
		    !record_has_reference_field(bare))
			fn.token_text = "copy-move-helper";
	Node this_node("parameter this " + pa11::describe_type(this_type));
	this_node.binding = this_binding;
	this_node.type = this_type;
	add_child(fn, this_node);
	Node other_node("parameter " + other_name + " " +
	                pa11::describe_type(source_ref));
	other_node.binding = other_binding;
	other_node.type = source_ref;
	add_child(fn, other_node);
	Node body("compound-statement");
	for (size_t i = 0; i < init_actions.size(); ++i)
		add_child(body, init_actions[i]);
	add_child(fn, body);
	extra_lowir_nodes_.push_back(fn);
	return ctor;
}
bool Parser::copy_move_assignment_available(TypePtr type, bool move)
{
	TypePtr bare = pa11::strip_cv(type);
	if (bare->kind == pa11::TypeKind::Array)
		return copy_move_assignment_available(bare->base, move);
	if (bare->kind != pa11::TypeKind::Record)
		return true;
	Binding* exact = find_copy_move_assignment_binding(bare, move);
	if (exact != NULL)
		return deleted_functions_.find(exact) == deleted_functions_.end();
	if (move)
	{
		Binding* copy = find_copy_move_assignment_binding(bare, false);
		if (copy != NULL)
			return deleted_functions_.find(copy) == deleted_functions_.end();
		if (suppresses_implicit_move(bare, &default_arguments_))
			return false;
	}
	Binding* generated = ensure_copy_move_assignment(bare, move);
	return generated != NULL &&
	       deleted_functions_.find(generated) == deleted_functions_.end();
}
Binding* Parser::ensure_copy_move_assignment(TypePtr type, bool move)
{
	TypePtr bare = pa11::strip_cv(type);
	if (bare->kind != pa11::TypeKind::Record || bare->scope == NULL)
		return NULL;
	Binding* existing = find_copy_move_assignment_binding(bare, move);
	if (existing != NULL)
		return existing;
	if (move && suppresses_implicit_move(bare, &default_arguments_))
		return NULL;
	set<const void*>& generated =
		move ? generated_move_assignments_ : generated_copy_assignments_;
	const void* key = bare.get();
	if (generated.find(key) != generated.end())
		return find_copy_move_assignment_binding(bare, move);
	generated.insert(key);
	pa11::layout_record_type(bare);
	TypePtr source_record = move ? bare : pa11::make_cv(bare, pa11::CV_CONST);
	TypePtr source_ref = move
		? pa11::make_rvalue_reference(bare)
		: pa11::make_lvalue_reference(source_record);
	TypePtr this_type = pa11::make_pointer(bare);
	vector<TypePtr> params;
	params.push_back(this_type);
	params.push_back(source_ref);
	TypePtr fn_type =
		pa11::make_function(pa11::make_lvalue_reference(bare),
		                    params,
		                    false);
	Binding* op =
		add_value(bare->scope, BindingKind::Function, "operator=", fn_type);
	op->is_generated_copy_move_assignment = true;
	op->unwind_no = !record_needs_copy_move_assignment_helper(bare, move);
	function_parameter_names_[op] = vector<string>(2, "this");
	function_parameter_names_[op][1] = "other";
	bool has_bitfield = false;
	for (size_t i = 0; i < bare->fields.size(); ++i)
		if (bare->fields[i]->is_bit_field)
			has_bitfield = true;
	if (has_bitfield)
		return op;
	op->is_inline_definition = true;
	Scope* function_scope =
		pa11::create_child_scope(bare->scope, ScopeKind::Function, op->name);
	Binding* this_binding =
		pa11::add_binding(function_scope,
		                  BindingKind::Parameter,
		                  "this",
		                  this_type);
	Binding* other_binding =
		pa11::add_binding(function_scope,
		                  BindingKind::Parameter,
		                  "other",
		                  source_ref);
	Node this_ptr = make_this_pointer_node(this_binding, this_type);
	Node this_object = make_deref_node(bare, this_ptr);
	Node other = make_parameter_lvalue(other_binding, source_record);
	bool deleted = false;
	Node fn("function-definition " + qualified_decl_name(op) + " " +
	        pa11::describe_type(fn_type));
	fn.binding = op;
	fn.type = fn_type;
	Node this_node("parameter this " + pa11::describe_type(this_type));
	this_node.binding = this_binding;
	this_node.type = this_type;
	add_child(fn, this_node);
	Node other_node("parameter other " + pa11::describe_type(source_ref));
	other_node.binding = other_binding;
	other_node.type = source_ref;
	add_child(fn, other_node);
	Node body("compound-statement");
	TypePtr direct_base = bare->base.get() != NULL
		? pa11::strip_cv(bare->base) : TypePtr();
	bool base_needs_helper =
		direct_base.get() != NULL &&
		direct_base->kind == pa11::TypeKind::Record &&
		type_needs_copy_move_assignment_helper(direct_base, move);
	if (direct_base.get() != NULL &&
	    direct_base->kind == pa11::TypeKind::Record)
	{
		if (!copy_move_assignment_available(direct_base, move))
			deleted = true;
		if (base_needs_helper)
		{
			Expr target = target_base_expr(direct_base, this_object);
			Expr callee = make_member_expr(target, "operator=", ".");
			vector<Expr> args;
			args.push_back(expr_from_node(source_base_expr(direct_base,
			                                               other,
			                                               move)));
			Expr call = make_call_expr(callee, args);
			Node stmt("expression-statement");
			add_child(stmt, call.node);
			add_child(body, stmt);
		}
	}
	uint64_t copied_prefix = pa11::type_size(bare);
	if (base_needs_helper)
		copied_prefix = 0;
	else
	{
		for (size_t i = 0; i < bare->fields.size(); ++i)
		{
			Binding* field = bare->fields[i];
			if (type_needs_copy_move_assignment_helper(field->type, move))
			{
				copied_prefix = field->member_offset;
				break;
			}
		}
	}
	if (copied_prefix != 0)
	{
		Node action("storage-copy-action");
		action.type = bare;
		action.has_constant_value = true;
		action.constant_value = copied_prefix;
		add_child(action, other);
		add_child(body, action);
	}
	for (size_t i = 0; i < bare->fields.size(); ++i)
	{
		Binding* field = bare->fields[i];
		bool field_needs_helper =
			type_needs_copy_move_assignment_helper(field->type, move);
		Binding* field_assignment =
			find_copy_move_assignment_binding(field->type, move);
		if (field_assignment == NULL && move)
			field_assignment =
				find_copy_move_assignment_binding(field->type, false);
		if (pa11::type_has_const(field->type) ||
		    pa11::is_reference_type(field->type) ||
		    ((field_needs_helper || field_assignment != NULL) &&
		     !copy_move_assignment_available(field->type, move)))
			deleted = true;
		if (copied_prefix != 0 &&
		    field->member_offset < copied_prefix &&
		    !field_needs_helper)
			continue;
		if (!field_needs_helper)
			continue;
		Expr target = target_field_expr(field, this_object);
		Expr callee = make_member_expr(target, "operator=", ".");
		vector<Expr> args;
		args.push_back(expr_from_node(source_field_expr(field, other, move)));
		Expr call = make_call_expr(callee, args);
		Node stmt("expression-statement");
		add_child(stmt, call.node);
		add_child(body, stmt);
	}
	if (deleted)
		deleted_functions_.insert(op);
	Node ret("return-statement");
	add_child(ret, make_deref_node(bare, this_ptr));
	add_child(body, ret);
	add_child(fn, body);
	extra_lowir_nodes_.push_back(fn);
	return op;
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
bool destructor_needs_call(Binding* dtor)
{
	return dtor != NULL &&
	       (dtor->is_virtual ||
	       (!dtor->is_noop_destructor ||
	        (!dtor->is_generated_default_destructor &&
	         (dtor->is_private || dtor->is_protected_member))));
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
	{
		parse_pending_member_body(existing);
		return existing;
	}
	try
	{
		pa11::layout_record_type(bare);
	}
	catch (const runtime_error& err)
	{
		if ((string(err.what()) != "incomplete class type" &&
		     string(err.what()) != "incomplete object type") ||
		    active_class_instantiations_.empty())
			throw;
		return NULL;
	}
	vector<Node> fini_actions;
	TypePtr direct_base = bare->base.get() != NULL
		? pa11::strip_cv(bare->base) : TypePtr();
	bool forced_nontrivial = false;
	if (force_trivial &&
	    direct_base.get() != NULL &&
	    direct_base->kind == pa11::TypeKind::Record)
	{
		Binding* base_dtor = ensure_default_destructor(direct_base);
		forced_nontrivial = destructor_needs_call(base_dtor);
	}
	if (!force_trivial || !bare->fields.empty())
	{
		for (size_t n = 0; n < bare->fields.size(); ++n)
		{
			size_t i = bare->fields.size() - 1 - n;
			Binding* field_dtor =
				ensure_default_destructor(bare->fields[i]->type);
			if (destructor_needs_call(field_dtor))
				fini_actions.push_back(make_member_fini_action(bare->fields[i]));
		}
		if (direct_base.get() != NULL &&
		    direct_base->kind == pa11::TypeKind::Record)
		{
			Binding* base_dtor = ensure_default_destructor(direct_base);
			if (destructor_needs_call(base_dtor))
				fini_actions.push_back(make_base_fini_action(direct_base));
		}
	}
	if (fini_actions.empty() && !force_trivial)
		return NULL;
	const void* key = bare.get();
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
	dtor->is_generated_default_destructor = true;
	dtor->is_noop_destructor = fini_actions.empty() && !forced_nontrivial;
	Binding* overridden_virtual_dtor = find_overridden_virtual(bare, dtor);
	if (overridden_virtual_dtor != NULL)
	{
		dtor->is_virtual = true;
		dtor->is_noop_destructor = false;
		complete_class_virtuals(bare);
	}
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
namespace {
bool record_has_ordinary_member_function(TypePtr type)
{
	TypePtr bare = pa11::strip_cv(type);
	if (bare->kind != pa11::TypeKind::Record || bare->scope == NULL)
		return false;
	for (map<string, vector<Binding*> >::const_iterator it =
	     bare->scope->members.begin();
	     it != bare->scope->members.end();
	     ++it)
	{
		if (it->first == bare->scope->name ||
		    it->first == "~" + bare->scope->name)
			continue;
		for (size_t i = 0; i < it->second.size(); ++i)
			if (it->second[i]->kind == BindingKind::Function)
				return true;
	}
	return false;
}
bool record_has_reference_field(TypePtr type)
{
	TypePtr bare = pa11::strip_cv(type);
	if (bare->kind != pa11::TypeKind::Record)
		return false;
	pa11::layout_record_type(bare);
	for (size_t i = 0; i < bare->fields.size(); ++i)
	{
		TypePtr field = bare->fields[i]->type;
		if (field->kind == pa11::TypeKind::LValueReference ||
		    field->kind == pa11::TypeKind::RValueReference)
			return true;
	}
	return false;
}
}  // namespace
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
	bool has_reference_field = false;
	try
	{
		has_reference_field = record_has_reference_field(bare);
	}
	catch (const runtime_error& err)
	{
		if ((string(err.what()) != "incomplete class type" &&
		     string(err.what()) != "incomplete object type") ||
		    active_class_instantiations_.empty())
			throw;
		return;
	}
	if (pa11::type_has_const(type) ||
	    has_reference_field ||
	    record_has_ordinary_member_function(bare))
	{
		try
		{
			ensure_aggregate_constructor(bare, init.children.size());
		}
		catch (const runtime_error& err)
		{
			if ((string(err.what()) != "incomplete class type" &&
			     string(err.what()) != "incomplete object type") ||
			    active_class_instantiations_.empty())
				throw;
			return;
		}
	}
	try
	{
		pa11::layout_record_type(bare);
	}
	catch (const runtime_error& err)
	{
		if ((string(err.what()) != "incomplete class type" &&
		     string(err.what()) != "incomplete object type") ||
		    active_class_instantiations_.empty())
			throw;
		return;
	}
	for (size_t i = 0; i < init.children.size() && i < bare->fields.size(); ++i)
		ensure_aggregate_constructors_for_init(bare->fields[i]->type,
		                                       init.children[i]);
}
Node Parser::make_member_init_action(Binding* field, const Node* init)
{
	Node action("member-init-action " + field->name);
	action.binding = field;
	action.type = field->type;
	TypePtr bare = pa11::strip_cv(field->type);
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
	if (bare->kind == pa11::TypeKind::Record && init == NULL)
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
			action.direct_call = ctor;
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
                                           const string& name,
                                           const vector<TemplateArgument>* template_arguments)
{
	TypePtr bare = pa11::strip_cv(direct_base);
	if (bare->kind != pa11::TypeKind::Record || bare->scope == NULL)
		return false;
	if (name == bare->scope->name)
		return true;
	TypePtr substituted;
	if (find_template_type_substitution(name, substituted) &&
	    pa11::same_type(pa11::strip_cv(substituted), bare))
		return true;
	vector<Binding*> types =
		lookup_unqualified_set(class_scope, name, pa11::LOOKUP_TYPE);
	for (size_t i = 0; i < types.size(); ++i)
	{
		TypePtr named = substitute_template_type(types[i]->type);
		if (pa11::same_type(pa11::strip_cv(named), bare))
			return true;
	}
	if (template_arguments != NULL)
	{
		TemplateDeclaration* alias = find_alias_template(NULL, name);
		if (alias != NULL)
		{
			try
			{
				TypePtr named =
					instantiate_alias_template(alias, *template_arguments);
				if (pa11::same_type(pa11::strip_cv(named), bare))
					return true;
			}
			catch (const runtime_error&)
			{
			}
		}
	}
	return false;
}
Node Parser::default_constructor_action(Binding* variable, bool force_trivial)
{
	TypePtr bare = pa11::strip_cv(variable->type);
	if (bare->kind != pa11::TypeKind::Record)
		throw runtime_error("default constructor action requires record");
	string ctor_name = bare->name + "::" + bare->name;
	Binding* ctor = ensure_default_constructor(bare, force_trivial);
	if (ctor == NULL)
		throw runtime_error("missing default constructor");
	Node action("constructor-action " + ctor_name);
	if (force_trivial)
		action.token_text = "force-trivial";
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
		else
		{
			TypePtr record = pa11::record_type_for_scope(class_scope);
			TypePtr direct_base =
				record.get() != NULL ? pa11::strip_cv(record)->base : TypePtr();
			if (direct_base.get() != NULL &&
			    initializer_names_direct_base(class_scope,
			                                  direct_base,
			                                  node.token_text))
			{
				TypePtr bare_base = pa11::strip_cv(direct_base);
				node.line = "base-init-action " + bare_base->name;
				node.type = direct_base;
				node.binding = NULL;
			}
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
