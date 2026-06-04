#include "pa12_internal.h"

using namespace std;

namespace pa12 {
namespace internal {

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
		pending_member_bodies_[class_scope].push_back(pending);
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
	if (body.children.empty())
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
						init = make_constructor_init_expr(init_target,
						                                  args,
						                                  false);
						have_init = true;
					}
					else if (args.size() == 1)
					{
						init = args[0];
						have_init = true;
					}
				}
				else
				{
					init.valid = true;
					init.category = ValueCategory::PRValue;
					init.braced_init_list = true;
					init.node = Node("braced-init-list");
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
	pa11::layout_record_type(class_type);
	for (size_t i = 0; i < class_type->fields.size(); ++i)
	{
		Binding* field = class_type->fields[i];
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
			add_child(body, make_member_init_action(field, NULL));
	}
	Node parsed_body = parse_compound_statement();
	for (size_t i = 0; i < parsed_body.children.size(); ++i)
		add_child(body, parsed_body.children[i]);
	active_functions_.pop_back();
	function_returns_.pop_back();
	scopes_.pop_back();
	add_child(fn, body);
}

bool Parser::parse_qualified_constructor_definition(Node& out, bool emit_node)
{
	if (current_scope()->kind == ScopeKind::Class ||
	    !(at(OP_COLON2) || (at_identifier() && lookahead(OP_COLON2, 1))))
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
		pending_member_bodies_[class_scope].push_back(pending);
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
						init = make_constructor_init_expr(init_target,
						                                  args,
						                                  false);
						have_init = true;
					}
					else if (args.size() == 1)
					{
						init = args[0];
						have_init = true;
					}
				}
				else
				{
					init.valid = true;
					init.category = ValueCategory::PRValue;
					init.braced_init_list = true;
					init.node = Node("braced-init-list");
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
	pa11::layout_record_type(class_type);
	for (size_t i = 0; i < class_type->fields.size(); ++i)
	{
		Binding* field = class_type->fields[i];
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
			add_child(body, make_member_init_action(field, NULL));
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

bool Parser::parse_conversion_function_member(bool explicit_conv)
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
	function->is_explicit = explicit_conv;
	function->is_inline_definition = at(OP_LBRACE);
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
	PendingFunctionBody pending;
	pending.function = function;
	pending.node = fn;
	pending.body_pos = pos_;
	skip_balanced(OP_LBRACE, OP_RBRACE);
	pending_member_bodies_[class_scope].push_back(pending);
	return true;
}

bool Parser::parse_constructor_like_member(bool explicit_ctor)
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
	ctor->is_inline_definition = at(OP_LBRACE) || at(OP_COLON);
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
		return true;

	Node fn("function-definition " + qualified_decl_name(ctor) + " " +
	        pa11::describe_type(fn_type));
	fn.binding = ctor;
	fn.type = fn_type;
	if (ctor->is_inline_definition)
	{
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
		pending_member_bodies_[class_scope].push_back(pending);
		return true;
	}
	Scope* function_scope =
		pa11::create_child_scope(class_scope, ScopeKind::Function, ctor->name);
	Binding* this_binding =
		pa11::add_binding(function_scope, BindingKind::Parameter, "this", this_type);
	Node this_node("parameter this " + pa11::describe_type(this_type));
	this_node.binding = this_binding;
	this_node.type = this_type;
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

	scopes_.push_back(function_scope);
	function_returns_.push_back(pa11::make_fundamental(FT_VOID));
	active_functions_.push_back(ctor);
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
						init = make_constructor_init_expr(init_target,
						                                  args,
						                                  false);
						have_init = true;
					}
					else if (args.size() == 1)
					{
						init = args[0];
						have_init = true;
					}
				}
				else
				{
					init.valid = true;
					init.category = ValueCategory::PRValue;
					init.braced_init_list = true;
					init.node = Node("braced-init-list");
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
	pa11::layout_record_type(class_type);
	for (size_t i = 0; i < class_type->fields.size(); ++i)
	{
		Binding* field = class_type->fields[i];
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
			add_child(body, make_member_init_action(field, NULL));
	}
	Node parsed_body = parse_compound_statement();
	for (size_t i = 0; i < parsed_body.children.size(); ++i)
		add_child(body, parsed_body.children[i]);
	active_functions_.pop_back();
	function_returns_.pop_back();
	scopes_.pop_back();
	add_child(fn, body);
	extra_lowir_nodes_.push_back(fn);
	return true;
}

bool Parser::parse_destructor_like_member()
{
	if (current_scope()->kind != ScopeKind::Class || !at(OP_COMPL))
		return false;
	size_t save = pos_;
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
		pending_member_bodies_[class_scope].push_back(pending);
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
	if (body.children.empty())
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
