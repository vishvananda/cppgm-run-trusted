#include "pa12_internal.h"

using namespace std;

namespace pa12 {
namespace internal {
namespace {

bool record_has_reference_field(TypePtr type)
{
	TypePtr bare = pa11::strip_cv(type);
	if (bare->kind != pa11::TypeKind::Record)
		return false;
	for (size_t i = 0; i < bare->fields.size(); ++i)
	{
		TypePtr field = bare->fields[i]->type;
		if (pa11::is_reference_type(field))
			return true;
		if (record_has_reference_field(field))
			return true;
	}
	return bare->base.get() != NULL && record_has_reference_field(bare->base);
}

vector<Binding*> declared_instance_fields(TypePtr type)
{
	vector<Binding*> fields;
	TypePtr bare = pa11::strip_cv(type);
	if (bare->kind != pa11::TypeKind::Record || bare->scope == NULL)
		return fields;
	for (size_t i = 0; i < bare->scope->binding_order.size(); ++i)
	{
		Binding* member = bare->scope->binding_order[i];
		if (member->kind == BindingKind::Variable &&
		    !member->is_static_member &&
		    member->aliased_binding == NULL)
			fields.push_back(member);
	}
	return fields;
}

}  // namespace

bool Parser::parse_qualified_destructor_definition(Node& out, bool emit_node)
{
	if (current_scope()->kind == ScopeKind::Class ||
	    !at_identifier() || !lookahead(OP_COLON2, 1))
		return false;
	size_t save = pos_;
	string class_name = consume_identifier();
	expect(OP_COLON2);
	if (!consume(OP_COMPL) || !at_identifier())
	{
		pos_ = save;
		return false;
	}
	string dtor_type_name = consume_identifier();
	if (!at(OP_LPAREN))
	{
		pos_ = save;
		return false;
	}
	Binding* class_binding =
		pa11::lookup_unqualified(current_scope(),
		                         class_name,
		                         pa11::LOOKUP_QUALIFIER);
	Scope* class_scope = resolve_qualifier(class_binding);
	if (class_scope == NULL ||
	    class_scope->kind != ScopeKind::Class ||
	    dtor_type_name != class_scope->name)
	{
		pos_ = save;
		return false;
	}
	TypePtr class_type = pa11::record_type_for_scope(class_scope);
	if (class_type.get() == NULL)
	{
		pos_ = save;
		return false;
	}

	expect(OP_LPAREN);
	vector<ParameterInfo> parameters;
	bool variadic = false;
	scopes_.push_back(class_scope);
	parse_parameter_clause(parameters, variadic);
	scopes_.pop_back();
	expect(OP_RPAREN);
	if (!parameters.empty() || variadic)
		throw runtime_error("destructor cannot have parameters");
	Suffix suffix(SuffixKind::Function);
	parse_function_suffix_tail(suffix);
	bool defaulted = false;
	if (consume(OP_ASS))
	{
		if (!consume(KW_DEFAULT))
			throw runtime_error("unsupported destructor definition");
		expect(OP_SEMICOLON);
		defaulted = true;
	}
	if (!at(OP_LBRACE))
	{
		if (!defaulted)
		{
			pos_ = save;
			return false;
		}
	}

	TypePtr this_type = pa11::make_pointer(class_type);
	vector<TypePtr> fn_params(1, this_type);
	TypePtr fn_type = pa11::make_function(pa11::make_fundamental(FT_VOID),
	                                      fn_params,
	                                      false);
	string dtor_name = "~" + class_scope->name;
	Binding* dtor = add_value(class_scope,
	                          BindingKind::Function,
	                          dtor_name,
	                          fn_type);
	dtor->unwind_no = suffix.noexcept_decl;
	function_parameter_names_[dtor] = vector<string>(1, "this");
	Node fn("function-definition " + qualified_decl_name(dtor) + " " +
	        pa11::describe_type(fn_type));
	fn.binding = dtor;
	fn.type = fn_type;
	if (dtor->is_inline_definition)
	{
		PendingFunctionBody pending;
		pending.function = dtor;
		pending.node = fn;
		pending.body_pos = pos_;
		skip_balanced(OP_LBRACE, OP_RBRACE);
		enqueue_pending_member_body(class_scope, pending);
		return true;
	}
	Scope* function_scope =
		pa11::create_child_scope(class_scope, ScopeKind::Function, dtor->name);
	Binding* this_binding =
		pa11::add_binding(function_scope,
		                  BindingKind::Parameter,
		                  "this",
		                  this_type);
	Node this_node("parameter this " + pa11::describe_type(this_type));
	this_node.binding = this_binding;
	this_node.type = this_type;
	add_child(fn, this_node);
	Node body;
	if (defaulted)
		body = Node("compound-statement");
	else
	{
		scopes_.push_back(function_scope);
		function_returns_.push_back(pa11::make_fundamental(FT_VOID));
		active_functions_.push_back(dtor);
		body = parse_compound_statement();
		active_functions_.pop_back();
		function_returns_.pop_back();
		scopes_.pop_back();
	}
	if (body.children.empty() && !dtor->is_virtual)
	{
		dtor->is_noop_destructor = true;
		map<string, vector<Binding*> >::iterator found =
			class_scope->members.find(dtor_name);
		if (found != class_scope->members.end())
			for (size_t i = 0; i < found->second.size(); ++i)
				if (found->second[i]->kind == BindingKind::Function &&
				    pa11::same_type(found->second[i]->type, dtor->type))
					found->second[i]->is_noop_destructor = true;
	}
	add_child(fn, body);
	if (emit_node)
		add_child(out, fn);
	else
		extra_lowir_nodes_.push_back(fn);
	return true;
}

void Parser::parse_constructor_body_from_parameters(
	Binding* function,
	TypePtr class_type,
	const vector<ParameterInfo>& parameters,
	Node& function_node)
{
	if (function_node.children.empty())
		throw runtime_error("missing function node");
	Node& fn = function_node.children.back();
	Scope* class_scope = function->owner;
	if (class_scope == NULL || class_scope->kind != ScopeKind::Class)
		throw runtime_error("constructor without class scope");
	TypePtr this_type = function->type->parameters.empty()
		? pa11::make_pointer(class_type) : function->type->parameters[0];
	Scope* function_scope =
		pa11::create_child_scope(class_scope, ScopeKind::Function, function->name);
	Binding* this_binding =
		pa11::add_binding(function_scope,
		                  BindingKind::Parameter,
		                  "this",
		                  this_type);
	Node this_node("parameter this " + pa11::describe_type(this_type));
	this_node.binding = this_binding;
	this_node.type = this_type;
	add_child(fn, this_node);
	for (size_t i = 0; i < parameters.size(); ++i)
	{
		string pname = parameters[i].name;
		string node_name = pname;
		map<Binding*, vector<string> >::const_iterator saved_names =
			function_parameter_names_.find(function);
		if (node_name.empty() &&
		    saved_names != function_parameter_names_.end() &&
		    i + 1 < saved_names->second.size())
			node_name = saved_names->second[i + 1];
		if (node_name.empty())
			node_name = "__param" + to_string(i + 1);
		if (pname.empty() && node_name.compare(0, 7, "__param") != 0)
			pname = node_name;
		Binding* param = NULL;
		if (!pname.empty())
			param = pa11::add_binding(function_scope,
			                          BindingKind::Parameter,
			                          pname,
			                          parameters[i].type);
		Node param_node("parameter " + node_name + " " +
		                pa11::describe_type(parameters[i].type));
		param_node.binding = param;
		param_node.type = parameters[i].type;
		add_child(fn, param_node);
	}

	scopes_.push_back(function_scope);
	function_returns_.push_back(pa11::make_fundamental(FT_VOID));
	active_functions_.push_back(function);
	Node body("compound-statement");
	map<Binding*, Node> explicit_member_initializers;
	bool explicit_base = false;
	bool delegating = false;
	Node explicit_base_action;
	TypePtr direct_base = class_type->base.get() != NULL
		? pa11::strip_cv(class_type->base) : TypePtr();
	if (consume(OP_COLON))
	{
		for (;;)
		{
			string name = consume_identifier();
			if (at(OP_LT))
			{
				vector<TemplateArgument> ignored;
				parse_template_argument_list(ignored);
			}
			Binding* field = pa11::lookup_qualified(class_scope,
			                                        name,
			                                        pa11::LOOKUP_VARIABLE);
			Expr init;
			bool have_init = false;
			if (at(OP_LBRACE))
			{
				init = parse_braced_init_list();
				have_init = true;
			}
			else if (consume(OP_LPAREN))
			{
				if (!at(OP_RPAREN))
				{
					vector<Expr> args = parse_argument_list();
					TypePtr init_target;
					if (name == class_scope->name)
						init_target = class_type;
					else if (direct_base.get() != NULL &&
					    initializer_names_direct_base(class_scope,
					                                  direct_base,
					                                  name))
						init_target = direct_base;
					else if (field != NULL)
						init_target = field->type;
					if (init_target.get() != NULL &&
					    pa11::strip_cv(init_target)->kind ==
					    pa11::TypeKind::Record)
					{
						try
						{
							init = make_constructor_init_expr(init_target,
							                                  args,
							                                  false);
							have_init = true;
						}
						catch (const runtime_error& err)
						{
							if (string(err.what()) != "no matching constructor" ||
							    args.size() != 1 ||
							    !pa11::same_type(
								    pa11::strip_cv(init_target),
								    pa11::strip_cv(
									    expression_object_type(args[0].type))))
								throw;
							init = args[0];
							have_init = true;
						}
					}
					else if (args.size() == 1)
					{
						init = args[0];
						have_init = true;
					}
				}
				else
				{
					TypePtr init_target;
					if (name == class_scope->name)
						init_target = class_type;
					else if (direct_base.get() != NULL &&
					    initializer_names_direct_base(class_scope,
					                                  direct_base,
					                                  name))
						init_target = direct_base;
					else if (field != NULL)
						init_target = field->type;
					if (init_target.get() != NULL &&
					    pa11::strip_cv(init_target)->kind ==
					    pa11::TypeKind::Record)
						init = make_constructor_init_expr(init_target,
						                                  vector<Expr>(),
						                                  false);
					else
					{
						init.valid = true;
						init.category = ValueCategory::PRValue;
						init.braced_init_list = true;
						init.node = Node("braced-init-list");
					}
					have_init = true;
				}
				expect(OP_RPAREN);
			}
			if (direct_base.get() != NULL &&
			    initializer_names_direct_base(class_scope, direct_base, name))
			{
				explicit_base_action =
					make_base_init_action(direct_base,
					                      have_init ? &init.node : NULL);
				explicit_base = true;
			}
			else if (name == class_scope->name && have_init)
			{
				Node action("delegating-init-action " + name);
				action.type = class_type;
				action.direct_call = init.node.direct_call;
				add_child(action, init.node);
				add_child(body, action);
				delegating = true;
			}
			else if (field != NULL && have_init)
			{
				explicit_member_initializers[field] =
					make_member_init_action(field, &init.node);
			}
			else if (have_init)
			{
				Node action("member-init-action " + name);
				action.token_text = name;
				add_child(action, init.node);
				add_child(body, action);
			}
			if (!consume(OP_COMMA))
				break;
		}
	}
	if (delegating)
	{
	}
	else if (explicit_base)
		add_child(body, explicit_base_action);
	else if (direct_base.get() != NULL &&
	         direct_base->kind == pa11::TypeKind::Record &&
	         ensure_default_constructor(direct_base) != NULL)
	{
		Node base_action = make_base_init_action(direct_base, NULL);
		add_child(body, base_action);
	}
	vector<Binding*> fields;
	try
	{
		pa11::layout_record_type(class_type);
		fields = class_type->fields;
	}
	catch (const runtime_error& err)
	{
		if ((string(err.what()) != "incomplete class type" &&
		     string(err.what()) != "incomplete object type") ||
		    active_class_instantiations_.empty())
			throw;
		fields = declared_instance_fields(class_type);
	}
	for (size_t i = 0; i < fields.size(); ++i)
	{
		Binding* field = fields[i];
		map<Binding*, Node>::const_iterator explicit_init =
			explicit_member_initializers.find(field);
		if (explicit_init != explicit_member_initializers.end())
		{
			add_child(body, explicit_init->second);
			continue;
		}
			map<Binding*, Node>::const_iterator init =
				default_member_initializers_.find(field);
			if (init != default_member_initializers_.end())
				add_child(body, make_member_init_action(field, &init->second));
			else if (pa11::strip_cv(field->type)->kind == pa11::TypeKind::Record)
			{
				try
				{
					if (ensure_default_constructor(field->type) != NULL)
						add_child(body, make_member_init_action(field, NULL));
				}
				catch (const runtime_error& err)
				{
					if (string(err.what()) !=
					    "member has no default constructor")
						throw;
				}
			}
	}
	Node parsed_body = parse_compound_statement();
	for (size_t i = 0; i < parsed_body.children.size(); ++i)
		add_child(body, parsed_body.children[i]);
	active_functions_.pop_back();
	function_returns_.pop_back();
	scopes_.pop_back();
	add_child(fn, body);
	remember_function_body(function, fn);
}

bool Parser::parse_qualified_constructor_definition(Node& out, bool emit_node)
{
	if (current_scope()->kind == ScopeKind::Class ||
	    !(at(OP_COLON2) || at_identifier()))
		return false;
	size_t save = pos_;
	QualifiedName name;
	try
	{
		name = parse_id_expression_name();
	}
	catch (const exception&)
	{
		pos_ = save;
		return false;
	}
	if (name.qualifier == NULL ||
	    name.qualifier->kind != ScopeKind::Class ||
	    name.name != name.qualifier->name ||
	    !at(OP_LPAREN))
	{
		pos_ = save;
		return false;
	}
	Scope* class_scope = name.qualifier;
	TypePtr class_type = pa11::record_type_for_scope(class_scope);
	if (class_type.get() == NULL)
	{
		pos_ = save;
		return false;
	}

	expect(OP_LPAREN);
	vector<ParameterInfo> parameters;
	bool variadic = false;
	scopes_.push_back(class_scope);
	parse_parameter_clause(parameters, variadic);
	scopes_.pop_back();
	expect(OP_RPAREN);
	Suffix suffix(SuffixKind::Function);
	parse_function_suffix_tail(suffix);
	bool defaulted = false;
	if (consume(OP_ASS))
	{
		if (!consume(KW_DEFAULT))
			throw runtime_error("unsupported constructor definition");
		expect(OP_SEMICOLON);
		defaulted = true;
	}
	if (!defaulted && !at(OP_LBRACE) && !at(OP_COLON))
	{
		pos_ = save;
		return false;
	}

	vector<TypePtr> fn_params;
	fn_params.push_back(pa11::make_pointer(class_type));
	for (size_t i = 0; i < parameters.size(); ++i)
		fn_params.push_back(parameters[i].type);
	TypePtr fn_type = pa11::make_function(pa11::make_fundamental(FT_VOID),
	                                      fn_params,
	                                      variadic);
	Binding* existing_ctor = NULL;
	map<string, vector<Binding*> >::iterator existing_it =
		class_scope->members.find(class_scope->name);
	if (existing_it != class_scope->members.end())
		for (size_t i = 0; i < existing_it->second.size(); ++i)
		{
			Binding* candidate = existing_it->second[i];
			if (candidate->kind == BindingKind::Function &&
			    pa11::same_type(candidate->type, fn_type))
			{
				existing_ctor = candidate;
				break;
			}
		}
	if (existing_ctor != NULL &&
	    existing_ctor->unwind_no != suffix.noexcept_decl)
		throw runtime_error("exception specification mismatch");
	Binding* ctor =
		add_function_binding(class_scope, class_scope->name, fn_type, false);
	ctor->unwind_no = suffix.noexcept_decl;
	if (defaulted)
	{
		ctor->is_defaulted = true;
		ctor->is_generated_default_constructor = parameters.empty();
	}
	Node fn("function-definition " + qualified_decl_name(ctor) + " " +
	        pa11::describe_type(fn_type));
	fn.binding = ctor;
		fn.type = fn_type;
		if (ctor->is_inline_definition)
		{
			if (force_new_function_binding_ &&
			    active_class_instantiations_.empty())
			{
				Node holder("constructor-definition-holder");
				add_child(holder, fn);
				parse_constructor_body_from_parameters(ctor,
				                                       class_type,
				                                       parameters,
				                                       holder);
				extra_lowir_nodes_.push_back(holder.children.back());
				return true;
			}
			PendingFunctionBody pending;
			pending.function = ctor;
		pending.node = fn;
		pending.parameters = parameters;
		pending.body_pos = pos_;
		pending.constructor_body = true;
		pending.class_type = class_type;
		if (consume(OP_COLON))
		{
			for (;;)
			{
				while (!at(OP_LPAREN) && !at(OP_LBRACE) && !at_eof())
					++pos_;
				if (at(OP_LPAREN))
					skip_balanced(OP_LPAREN, OP_RPAREN);
				else if (at(OP_LBRACE))
					skip_balanced(OP_LBRACE, OP_RBRACE);
				if (!consume(OP_COMMA))
					break;
			}
		}
		skip_balanced(OP_LBRACE, OP_RBRACE);
		enqueue_pending_member_body(class_scope, pending);
		return true;
	}
	Scope* function_scope =
		pa11::create_child_scope(class_scope, ScopeKind::Function, ctor->name);
	Binding* this_binding =
		pa11::add_binding(function_scope,
		                  BindingKind::Parameter,
		                  "this",
		                  fn_params[0]);
	Node this_node("parameter this " + pa11::describe_type(fn_params[0]));
	this_node.binding = this_binding;
	this_node.type = fn_params[0];
	add_child(fn, this_node);
	for (size_t i = 0; i < parameters.size(); ++i)
	{
		string pname = parameters[i].name.empty()
			? "__param" + to_string(i + 1) : parameters[i].name;
		Binding* param =
			pa11::add_binding(function_scope,
			                  BindingKind::Parameter,
			                  pname,
			                  parameters[i].type);
		Node param_node("parameter " + pname + " " +
		                pa11::describe_type(parameters[i].type));
		param_node.binding = param;
		param_node.type = parameters[i].type;
		add_child(fn, param_node);
	}
	if (!defaulted)
	{
		scopes_.push_back(function_scope);
		function_returns_.push_back(pa11::make_fundamental(FT_VOID));
		active_functions_.push_back(ctor);
	}
	Node body("compound-statement");
	map<Binding*, Node> explicit_member_initializers;
	bool explicit_base = false;
	bool delegating = false;
	Node explicit_base_action;
	TypePtr direct_base = class_type->base.get() != NULL
		? pa11::strip_cv(class_type->base) : TypePtr();
	if (!defaulted && consume(OP_COLON))
	{
		for (;;)
		{
			string init_name = consume_identifier();
			if (at(OP_LT))
			{
				vector<TemplateArgument> ignored;
				parse_template_argument_list(ignored);
			}
			Binding* field = pa11::lookup_qualified(class_scope,
			                                        init_name,
			                                        pa11::LOOKUP_VARIABLE);
			Expr init;
			bool have_init = false;
			if (at(OP_LBRACE))
			{
				init = parse_braced_init_list();
				have_init = true;
			}
			else if (consume(OP_LPAREN))
			{
				if (!at(OP_RPAREN))
				{
					vector<Expr> args = parse_argument_list();
					TypePtr init_target;
					if (init_name == class_scope->name)
						init_target = class_type;
					else if (direct_base.get() != NULL &&
					    initializer_names_direct_base(class_scope,
					                                  direct_base,
					                                  init_name))
						init_target = direct_base;
					else if (field != NULL)
						init_target = field->type;
					if (init_target.get() != NULL &&
					    pa11::strip_cv(init_target)->kind ==
					    pa11::TypeKind::Record)
					{
						try
						{
							init = make_constructor_init_expr(init_target,
							                                  args,
							                                  false);
							have_init = true;
						}
						catch (const runtime_error& err)
						{
							if (string(err.what()) != "no matching constructor" ||
							    args.size() != 1 ||
							    !pa11::same_type(
								    pa11::strip_cv(init_target),
								    pa11::strip_cv(
									    expression_object_type(args[0].type))))
								throw;
							init = args[0];
							have_init = true;
						}
					}
					else if (args.size() == 1)
					{
						init = args[0];
						have_init = true;
					}
				}
				else
				{
					TypePtr init_target;
					if (init_name == class_scope->name)
						init_target = class_type;
					else if (direct_base.get() != NULL &&
					    initializer_names_direct_base(class_scope,
					                                  direct_base,
					                                  init_name))
						init_target = direct_base;
					else if (field != NULL)
						init_target = field->type;
					if (init_target.get() != NULL &&
					    pa11::strip_cv(init_target)->kind ==
					    pa11::TypeKind::Record)
						init = make_constructor_init_expr(init_target,
						                                  vector<Expr>(),
						                                  false);
					else
					{
						init.valid = true;
						init.category = ValueCategory::PRValue;
						init.braced_init_list = true;
						init.node = Node("braced-init-list");
					}
					have_init = true;
				}
				expect(OP_RPAREN);
			}
			if (direct_base.get() != NULL &&
			    initializer_names_direct_base(class_scope, direct_base, init_name))
			{
				explicit_base_action =
					make_base_init_action(direct_base,
					                      have_init ? &init.node : NULL);
				explicit_base = true;
			}
			else if (init_name == class_scope->name && have_init)
			{
				Node action("delegating-init-action " + init_name);
				action.type = class_type;
				action.direct_call = init.node.direct_call;
				add_child(action, init.node);
				add_child(body, action);
				delegating = true;
			}
			else if (field != NULL && have_init)
				explicit_member_initializers[field] =
					make_member_init_action(field, &init.node);
			else if (have_init)
			{
				Node action("member-init-action " + init_name);
				action.token_text = init_name;
				add_child(action, init.node);
				add_child(body, action);
			}
			if (!consume(OP_COMMA))
				break;
		}
	}
	if (delegating)
	{
	}
	else if (explicit_base)
		add_child(body, explicit_base_action);
	else if (direct_base.get() != NULL &&
	         direct_base->kind == pa11::TypeKind::Record &&
	         ensure_default_constructor(direct_base) != NULL)
	{
		Node base_action = make_base_init_action(direct_base, NULL);
		add_child(body, base_action);
	}
	vector<Binding*> fields;
	try
	{
		pa11::layout_record_type(class_type);
		fields = class_type->fields;
	}
	catch (const runtime_error& err)
	{
		if ((string(err.what()) != "incomplete class type" &&
		     string(err.what()) != "incomplete object type") ||
		    active_class_instantiations_.empty())
			throw;
		fields = declared_instance_fields(class_type);
	}
	for (size_t i = 0; i < fields.size(); ++i)
	{
		Binding* field = fields[i];
		map<Binding*, Node>::const_iterator explicit_init =
			explicit_member_initializers.find(field);
		if (explicit_init != explicit_member_initializers.end())
		{
			add_child(body, explicit_init->second);
			continue;
		}
			map<Binding*, Node>::const_iterator init =
				default_member_initializers_.find(field);
			if (init != default_member_initializers_.end())
				add_child(body, make_member_init_action(field, &init->second));
			else if (pa11::strip_cv(field->type)->kind == pa11::TypeKind::Record)
			{
				try
				{
					if (ensure_default_constructor(field->type) != NULL)
						add_child(body, make_member_init_action(field, NULL));
				}
				catch (const runtime_error& err)
				{
					if (string(err.what()) !=
					    "member has no default constructor")
						throw;
				}
			}
	}
	if (!defaulted)
	{
		Node parsed_body = parse_compound_statement();
		for (size_t i = 0; i < parsed_body.children.size(); ++i)
			add_child(body, parsed_body.children[i]);
		active_functions_.pop_back();
		function_returns_.pop_back();
		scopes_.pop_back();
	}
	add_child(fn, body);
	remember_function_body(ctor, fn);
	if (emit_node)
		add_child(out, fn);
	else
		extra_lowir_nodes_.push_back(fn);
	return true;
}

bool Parser::parse_qualified_conversion_definition(Node& out, bool emit_node)
{
	if (current_scope()->kind == ScopeKind::Class ||
	    !(at(OP_COLON2) || (at_identifier() && lookahead(OP_COLON2, 1))))
		return false;
	size_t save = pos_;
	Scope* class_scope = NULL;
	try
	{
		class_scope = parse_nested_name_specifier(NULL);
	}
	catch (const exception&)
	{
		pos_ = save;
		return false;
	}
	if (class_scope == NULL ||
	    class_scope->kind != ScopeKind::Class ||
	    !consume(KW_OPERATOR))
	{
		pos_ = save;
		return false;
	}
	TypePtr result;
	try
	{
		result = parse_conversion_type_id();
	}
	catch (const exception&)
	{
		pos_ = save;
		return false;
	}
	expect(OP_LPAREN);
	expect(OP_RPAREN);
	Suffix suffix(SuffixKind::Function);
	parse_function_suffix_tail(suffix);
	if (!at(OP_LBRACE))
	{
		pos_ = save;
		return false;
	}
	TypePtr class_type = pa11::record_type_for_scope(class_scope);
	if (class_type.get() == NULL)
		throw runtime_error("conversion function without class type");
	vector<TypePtr> params(
		1,
		pa11::make_pointer(pa11::make_cv(class_type, suffix.function_cv)));
	TypePtr fn_type = pa11::make_function(result, params, false);
	Binding* function =
		add_function_binding(class_scope,
		                     conversion_operator_name(result),
		                     fn_type,
		                     false);
	function->unwind_no = suffix.noexcept_decl;
	function->ref_qualifier = suffix.ref_qualifier;
	function_parameter_names_[function] = vector<string>(1, "this");
	Node node;
	Node fn("function-definition " + qualified_decl_name(function) + " " +
	        pa11::describe_type(fn_type));
	fn.binding = function;
	fn.type = fn_type;
	add_child(node, fn);
	vector<ParameterInfo> parameters;
	parse_function_body_from_parameters(function, parameters, node);
	if (emit_node)
		add_child(out, node.children.back());
	else if (!node.children.empty())
		extra_lowir_nodes_.push_back(node.children.back());
	return true;
}

bool Parser::parse_conversion_function_member(bool explicit_conv,
                                              bool constexpr_conv)
{
	if (current_scope()->kind != ScopeKind::Class || !at(KW_OPERATOR))
		return false;
	Scope* class_scope = current_scope();
	TypePtr class_type = pa11::record_type_for_scope(class_scope);
	if (class_type.get() == NULL)
		throw runtime_error("conversion function without class type");
	expect(KW_OPERATOR);
	TypePtr result = parse_conversion_type_id();
	expect(OP_LPAREN);
	expect(OP_RPAREN);
	Suffix suffix(SuffixKind::Function);
	parse_function_suffix_tail(suffix);
	TypePtr this_type =
		pa11::make_pointer(pa11::make_cv(class_type, suffix.function_cv));
	vector<TypePtr> params(1, this_type);
	TypePtr fn_type = pa11::make_function(result, params, false);
	Binding* function =
		add_function_binding(class_scope,
		                     conversion_operator_name(result),
		                     fn_type,
		                     false);
	function->is_constexpr = function->is_constexpr || constexpr_conv;
	function->is_explicit = explicit_conv;
	function->is_inline_definition = at(OP_LBRACE) || constexpr_conv;
	function->unwind_no = suffix.noexcept_decl;
	function->ref_qualifier = suffix.ref_qualifier;
	function->is_private = !class_private_access_.empty() &&
	                       class_private_access_.back();
	function->is_protected_member = !class_protected_access_.empty() &&
	                                class_protected_access_.back();
	function_parameter_names_[function] = vector<string>(1, "this");
	if (consume(OP_ASS))
	{
		if (consume(KW_DELETE))
		{
			deleted_functions_.insert(function);
			expect(OP_SEMICOLON);
			return true;
		}
		throw runtime_error("unsupported conversion function definition");
	}
	if (consume(OP_SEMICOLON))
		return true;
	if (!at(OP_LBRACE))
		throw runtime_error("conversion function missing body");
	Node fn("function-definition " + qualified_decl_name(function) + " " +
	        pa11::describe_type(fn_type));
	fn.binding = function;
	fn.type = fn_type;
	if (force_new_function_binding_ &&
	    active_class_instantiations_.empty())
	{
		Node node("simple-declaration");
		add_child(node, fn);
		vector<ParameterInfo> parameters;
		parse_function_body_from_parameters(function, parameters, node);
		if (!node.children.empty())
			extra_lowir_nodes_.push_back(node.children.back());
		return true;
	}
	PendingFunctionBody pending;
	pending.function = function;
	pending.node = fn;
	pending.body_pos = pos_;
	skip_balanced(OP_LBRACE, OP_RBRACE);
	enqueue_pending_member_body(class_scope, pending);
	return true;
}

bool Parser::parse_constructor_like_member(bool explicit_ctor,
                                           bool constexpr_ctor)
{
	if (current_scope()->kind != ScopeKind::Class || !at_identifier())
		return false;
	if (current().source != current_scope()->name)
		return false;
	if (!lookahead(OP_LPAREN, 1))
		return false;
	Scope* class_scope = current_scope();
	TypePtr class_type = pa11::record_type_for_scope(class_scope);
	if (class_type.get() == NULL)
		throw runtime_error("constructor without class type");
	consume_identifier();
	expect(OP_LPAREN);
	vector<ParameterInfo> parameters;
	bool variadic = false;
	parse_parameter_clause(parameters, variadic);
	expect(OP_RPAREN);
	Suffix suffix(SuffixKind::Function);
	parse_function_suffix_tail(suffix);

	TypePtr this_type = pa11::make_pointer(class_type);
	vector<TypePtr> fn_params;
	fn_params.push_back(this_type);
	for (size_t i = 0; i < parameters.size(); ++i)
		fn_params.push_back(parameters[i].type);
	TypePtr fn_type = pa11::make_function(pa11::make_fundamental(FT_VOID),
	                                      fn_params,
	                                      variadic);
	Binding* ctor = add_value(class_scope,
	                          BindingKind::Function,
	                          class_scope->name,
	                          fn_type);
	ctor->is_constexpr = ctor->is_constexpr || constexpr_ctor;
	vector<string> ctor_names(1, "this");
	for (size_t i = 0; i < parameters.size(); ++i)
		ctor_names.push_back(parameters[i].name);
	function_parameter_names_[ctor] = ctor_names;
	vector<Expr> ctor_defaults(fn_params.size());
	bool have_ctor_defaults = false;
	for (size_t i = 0; i < parameters.size(); ++i)
	{
		if (parameters[i].has_default)
		{
			ctor_defaults[i + 1] = parameters[i].default_value;
			have_ctor_defaults = true;
		}
	}
	if (have_ctor_defaults)
		default_arguments_[ctor] = ctor_defaults;
	ctor->is_inline_definition = at(OP_LBRACE) || at(OP_COLON) ||
	                             constexpr_ctor;
	ctor->is_explicit = explicit_ctor;
	ctor->unwind_no = suffix.noexcept_decl;
	ctor->is_private = !class_private_access_.empty() &&
	                   class_private_access_.back();
	ctor->is_protected_member = !class_protected_access_.empty() &&
	                            class_protected_access_.back();
	if (consume(OP_ASS))
	{
		if (consume(KW_DEFAULT))
		{
			ctor->is_defaulted = true;
			ctor->is_inline_definition = true;
			ctor->unwind_no = true;
			if (parameters.empty())
			{
				Node fn("function-definition " + qualified_decl_name(ctor) +
				        " " + pa11::describe_type(fn_type));
				fn.binding = ctor;
				fn.type = fn_type;
				Node this_node("parameter this " +
				               pa11::describe_type(fn_params[0]));
				this_node.type = fn_params[0];
				add_child(fn, this_node);
				add_child(fn, Node("compound-statement"));
				PendingFunctionBody pending;
				pending.function = ctor;
				pending.node = fn;
				pending.prebuilt_node = true;
				enqueue_pending_member_body(class_scope, pending);
			}
				if (parameters.size() == 1 &&
				    pa11::is_reference_type(parameters[0].type) &&
				    pa11::same_type(pa11::strip_cv(parameters[0].type->base),
				                    pa11::strip_cv(class_type)) &&
				    !record_has_reference_field(class_type))
				{
					Node fn("function-definition " + qualified_decl_name(ctor) +
					        " " + pa11::describe_type(fn_type));
					fn.binding = ctor;
					fn.type = fn_type;
					fn.token_text = "copy-move-helper";
					Node this_node("parameter this " +
					               pa11::describe_type(fn_params[0]));
				this_node.type = fn_params[0];
				add_child(fn, this_node);
				string pname = parameters[0].name.empty()
					? "__param1" : parameters[0].name;
				Node param_node("parameter " + pname + " " +
				                pa11::describe_type(parameters[0].type));
				param_node.type = parameters[0].type;
				add_child(fn, param_node);
				add_child(fn, Node("compound-statement"));
				PendingFunctionBody pending;
				pending.function = ctor;
				pending.node = fn;
				pending.prebuilt_node = true;
				enqueue_pending_member_body(class_scope, pending);
			}
			expect(OP_SEMICOLON);
			return true;
		}
		if (consume(KW_DELETE))
		{
			deleted_functions_.insert(ctor);
			expect(OP_SEMICOLON);
			return true;
		}
		throw runtime_error("unsupported constructor definition");
	}
	if (consume(OP_SEMICOLON))
	{
		if (force_new_function_binding_ &&
		    active_class_instantiations_.empty())
		{
			Node fn("function-declaration " + qualified_decl_name(ctor) +
			        " " + pa11::describe_type(fn_type));
			fn.binding = ctor;
			fn.type = fn_type;
			extra_lowir_nodes_.push_back(fn);
		}
		return true;
	}

	Node fn("function-definition " + qualified_decl_name(ctor) + " " +
	        pa11::describe_type(fn_type));
	fn.binding = ctor;
	fn.type = fn_type;
	if (ctor->is_inline_definition)
	{
		if (force_new_function_binding_ &&
		    active_class_instantiations_.empty())
		{
			Node holder("constructor-definition-holder");
			add_child(holder, fn);
			parse_constructor_body_from_parameters(ctor,
			                                       class_type,
			                                       parameters,
			                                       holder);
			extra_lowir_nodes_.push_back(holder.children.back());
			return true;
		}
		PendingFunctionBody pending;
		pending.function = ctor;
		pending.node = fn;
		pending.parameters = parameters;
		pending.body_pos = pos_;
		pending.constructor_body = true;
		pending.class_type = class_type;
		if (consume(OP_COLON))
		{
			for (;;)
			{
				while (!at(OP_LPAREN) && !at(OP_LBRACE) && !at_eof())
					++pos_;
				if (at(OP_LPAREN))
					skip_balanced(OP_LPAREN, OP_RPAREN);
				else if (at(OP_LBRACE))
					skip_balanced(OP_LBRACE, OP_RBRACE);
				if (!consume(OP_COMMA))
					break;
			}
		}
		skip_balanced(OP_LBRACE, OP_RBRACE);
		enqueue_pending_member_body(class_scope, pending);
		return true;
	}
	Node holder("constructor-definition-holder");
	add_child(holder, fn);
	parse_constructor_body_from_parameters(ctor, class_type, parameters, holder);
	extra_lowir_nodes_.push_back(holder.children.back());
	return true;
}

bool Parser::parse_destructor_like_member()
{
	if (current_scope()->kind != ScopeKind::Class)
		return false;
	size_t save = pos_;
	bool virtual_decl = consume(KW_VIRTUAL);
	if (!at(OP_COMPL))
	{
		pos_ = save;
		return false;
	}
	++pos_;
	if (!at_identifier() || current().source != current_scope()->name)
	{
		pos_ = save;
		return false;
	}
	Scope* class_scope = current_scope();
	TypePtr class_type = pa11::record_type_for_scope(class_scope);
	if (class_type.get() == NULL)
		throw runtime_error("destructor without class type");
	string dtor_name = "~" + consume_identifier();
	expect(OP_LPAREN);
	vector<ParameterInfo> parameters;
	bool variadic = false;
	parse_parameter_clause(parameters, variadic);
	expect(OP_RPAREN);
	if (!parameters.empty() || variadic)
		throw runtime_error("destructor cannot have parameters");
	Suffix suffix(SuffixKind::Function);
	parse_function_suffix_tail(suffix);

	TypePtr this_type = pa11::make_pointer(class_type);
	vector<TypePtr> fn_params(1, this_type);
	TypePtr fn_type = pa11::make_function(pa11::make_fundamental(FT_VOID),
	                                      fn_params,
	                                      false);
	Binding* dtor = add_value(class_scope,
	                          BindingKind::Function,
	                          dtor_name,
	                          fn_type);
	function_parameter_names_[dtor] = vector<string>(1, "this");
	dtor->is_inline_definition = at(OP_LBRACE);
	dtor->unwind_no = suffix.noexcept_decl;
	dtor->is_virtual = dtor->is_virtual || virtual_decl;
	dtor->is_override_specified =
		dtor->is_override_specified || suffix.override_decl;
	dtor->is_final_virtual = dtor->is_final_virtual || suffix.final_decl;
	dtor->is_private = !class_private_access_.empty() &&
	                   class_private_access_.back();
	dtor->is_protected_member = !class_protected_access_.empty() &&
	                            class_protected_access_.back();
	if (consume(OP_ASS))
	{
		if (consume(KW_DEFAULT) || consume(KW_DELETE))
		{
			expect(OP_SEMICOLON);
			return true;
		}
		throw runtime_error("unsupported destructor definition");
	}
	if (consume(OP_SEMICOLON))
		return true;

	Node fn("function-definition " + qualified_decl_name(dtor) + " " +
	        pa11::describe_type(fn_type));
	fn.binding = dtor;
	fn.type = fn_type;
	if (dtor->is_inline_definition)
	{
		PendingFunctionBody pending;
		pending.function = dtor;
		pending.node = fn;
		pending.body_pos = pos_;
		skip_balanced(OP_LBRACE, OP_RBRACE);
		enqueue_pending_member_body(class_scope, pending);
		return true;
	}
	Scope* function_scope =
		pa11::create_child_scope(class_scope, ScopeKind::Function, dtor->name);
	Binding* this_binding =
		pa11::add_binding(function_scope, BindingKind::Parameter, "this", this_type);
	Node this_node("parameter this " + pa11::describe_type(this_type));
	this_node.binding = this_binding;
	this_node.type = this_type;
	add_child(fn, this_node);

	scopes_.push_back(function_scope);
	function_returns_.push_back(pa11::make_fundamental(FT_VOID));
	active_functions_.push_back(dtor);
	Node body = parse_compound_statement();
	active_functions_.pop_back();
	function_returns_.pop_back();
	scopes_.pop_back();
	if (body.children.empty() && !dtor->is_virtual)
	{
		dtor->is_noop_destructor = true;
		map<string, vector<Binding*> >::iterator found =
			class_scope->members.find(dtor_name);
		if (found != class_scope->members.end())
			for (size_t i = 0; i < found->second.size(); ++i)
				if (found->second[i]->kind == BindingKind::Function &&
				    pa11::same_type(found->second[i]->type, dtor->type))
					found->second[i]->is_noop_destructor = true;
	}
	add_child(fn, body);
	extra_lowir_nodes_.push_back(fn);
	return true;
}


}  // namespace internal
}  // namespace pa12
