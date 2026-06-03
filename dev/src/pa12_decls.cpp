#include "pa12_internal.h"

#include <stdexcept>

using namespace std;

namespace pa12 {
namespace internal {

void Parser::parse_declaration_into(Node& out)
{
	if (consume(OP_SEMICOLON))
		return;
	if ((at(KW_INLINE) && lookahead(KW_NAMESPACE, 1)) || at(KW_NAMESPACE))
	{
		parse_namespace_or_alias(out);
		return;
	}
	if (at(KW_USING))
	{
		parse_using_family(out);
		return;
	}
	if (at(KW_EXTERN) && lookahead(OP_LBRACE, 1))
	{
		parse_linkage_specification(out);
		return;
	}
	if (at(KW_EXTERN) && pos_ + 1 < tokens_.size() &&
	    tokens_[pos_ + 1].kind == posttoken::TokenKind::Literal)
	{
		parse_linkage_specification(out);
		return;
	}
	if (at(KW_TEMPLATE))
	{
		parse_template_declaration();
		return;
	}
	parse_simple_or_function_declaration(out, true);
}

void Parser::parse_namespace_or_alias(Node& out)
{
	bool inline_ns = consume(KW_INLINE);
	expect(KW_NAMESPACE);
	if (!inline_ns && at_identifier() && lookahead(OP_ASS, 1))
	{
		string alias = consume_identifier();
		expect(OP_ASS);
		Scope* target = parse_qualified_namespace_specifier();
		expect(OP_SEMICOLON);
		pa11::add_namespace_alias(current_scope(), alias, target);
		return;
	}

	string name;
	bool named = false;
	if (at_identifier())
	{
		named = true;
		name = consume_identifier();
	}
	expect(OP_LBRACE);
	Scope* child = NULL;
	if (named)
		child = pa11::get_or_create_namespace(current_scope(), name, inline_ns);
	else
	{
		if (current_scope()->unnamed_namespace == NULL)
		{
			current_scope()->unnamed_namespace =
				pa11::create_child_scope(current_scope(),
				                         ScopeKind::Namespace,
				                         "<unnamed>");
			pa11::add_using_directive(current_scope(),
			                          current_scope()->unnamed_namespace);
		}
		child = current_scope()->unnamed_namespace;
		name = "<unnamed>";
	}

	Node node("namespace-definition " + name);
	scopes_.push_back(child);
	while (!at(OP_RBRACE))
		parse_declaration_into(node);
	scopes_.pop_back();
	expect(OP_RBRACE);
	add_child(out, node);
}

void Parser::parse_using_family(Node& out)
{
	expect(KW_USING);
	if (consume(KW_NAMESPACE))
	{
		Scope* target = parse_qualified_namespace_specifier();
		expect(OP_SEMICOLON);
		pa11::add_using_directive(current_scope(), target);
		return;
	}
	if (at_identifier() && lookahead(OP_ASS, 1))
	{
		string name = consume_identifier();
		expect(OP_ASS);
		TypePtr type = parse_type_id();
		expect(OP_SEMICOLON);
		add_alias(current_scope(), name, type);
		Node node("type-alias " + name + " " + pa11::describe_type(type));
		add_child(out, node);
		return;
	}
	string spelling;
	Scope* qualifier = parse_nested_name_specifier(&spelling);
	string name = consume_identifier();
	expect(OP_SEMICOLON);
	vector<Binding*> targets = lookup_qualified_set(qualifier, name, pa11::LOOKUP_ANY);
	if (targets.empty())
		throw runtime_error("using declaration target not found");
	if (current_scope()->kind == ScopeKind::Class &&
	    qualifier->kind == ScopeKind::Class &&
	    name == qualifier->name)
	{
			TypePtr derived = pa11::record_type_for_scope(current_scope());
			TypePtr base = pa11::record_type_for_scope(qualifier);
			if (derived.get() == NULL || base.get() == NULL)
				throw runtime_error("invalid inheriting constructor");
			for (size_t i = 0; i < targets.size(); ++i)
			{
				Binding* inherited = targets[i];
				if (inherited->kind != BindingKind::Function ||
				    inherited->type->parameters.empty())
					continue;
				vector<TypePtr> params;
				params.push_back(pa11::make_pointer(derived));
				for (size_t j = 1; j < inherited->type->parameters.size(); ++j)
					params.push_back(inherited->type->parameters[j]);
				TypePtr fn_type = pa11::make_function(pa11::make_fundamental(FT_VOID),
				                                      params,
				                                      inherited->type->variadic);
				Binding* ctor = add_value(current_scope(),
				                          BindingKind::Function,
				                          current_scope()->name,
				                          fn_type);
				map<Binding*, vector<string> >::const_iterator nit =
					function_parameter_names_.find(inherited);
				vector<string> inherited_names =
					nit != function_parameter_names_.end()
					? nit->second : vector<string>();
				vector<string> ctor_names(1, "this");
				ctor->is_inline_definition = true;
				Node fn("function-definition " + qualified_decl_name(ctor) + " " +
				        pa11::describe_type(fn_type));
				fn.binding = ctor;
				fn.type = fn_type;
				Scope* function_scope =
					pa11::create_child_scope(current_scope(),
					                         ScopeKind::Function,
					                         ctor->name);
				Binding* this_binding =
					pa11::add_binding(function_scope,
					                  BindingKind::Parameter,
					                  "this",
					                  params[0]);
				Node this_node("parameter this " + pa11::describe_type(params[0]));
				this_node.binding = this_binding;
				this_node.type = params[0];
				add_child(fn, this_node);
				Node init("braced-init-list");
				for (size_t j = 1; j < params.size(); ++j)
				{
					string pname = j < inherited_names.size() &&
					               !inherited_names[j].empty()
						? inherited_names[j] : "__param" + to_string(j);
					ctor_names.push_back(pname);
					Binding* param =
						pa11::add_binding(function_scope,
						                  BindingKind::Parameter,
						                  pname,
						                  params[j]);
					Node param_node("parameter " + pname + " " +
					                pa11::describe_type(params[j]));
					param_node.binding = param;
					param_node.type = params[j];
					add_child(fn, param_node);
					Node arg("id-expression lvalue " +
					         pa11::describe_type(params[j]) + " " + pname);
					arg.binding = param;
					arg.type = params[j];
					arg.category = ValueCategory::LValue;
					add_child(init, arg);
				}
				Node body("compound-statement");
				add_child(body, make_base_init_action(base, &init));
				add_child(fn, body);
				function_parameter_names_[ctor] = ctor_names;
				extra_lowir_nodes_.push_back(fn);
			}
			return;
		}
	for (size_t i = 0; i < targets.size(); ++i)
		pa11::add_using_declaration(current_scope(), name, targets[i]);
}

void Parser::parse_linkage_specification(Node& out)
{
	expect(KW_EXTERN);
	string language = current_language_linkage();
	if (at_literal())
	{
		if (current().source == "\"C\"")
			language = "c";
		else if (current().source == "\"C++\"")
			language = "cpp";
		++pos_;
	}
	if (consume(OP_LBRACE))
	{
		language_linkages_.push_back(language);
		while (!at(OP_RBRACE))
			parse_declaration_into(out);
		language_linkages_.pop_back();
		expect(OP_RBRACE);
		return;
	}
	language_linkages_.push_back(language);
	parse_simple_or_function_declaration(out, true);
	language_linkages_.pop_back();
}

void Parser::parse_template_declaration()
{
	expect(KW_TEMPLATE);
	skip_template_parameter_clause();
	Node ignored;
	parse_declaration_into(ignored);
}

void Parser::skip_template_parameter_clause()
{
	expect(OP_LT);
	int depth = 1;
	while (depth > 0 && !at_eof())
	{
		if (consume(OP_LT))
			++depth;
		else if (consume(OP_GT))
			--depth;
		else
			++pos_;
	}
}

void Parser::parse_simple_or_function_declaration(Node& out, bool emit_node)
{
	if (parse_qualified_constructor_definition(out, emit_node))
		return;
	if (current_scope()->kind == ScopeKind::Class && consume(KW_EXPLICIT))
	{
		if (parse_constructor_like_member(true))
			return;
		throw runtime_error("explicit specifier without constructor");
	}
	if (parse_constructor_like_member())
		return;
	DeclSpecs specs = parse_decl_specifier_seq(false);
	TypePtr base = type_from_decl_specs(specs);
	if (consume(OP_SEMICOLON))
	{
		if (current_scope()->kind != ScopeKind::Namespace)
		{
			TypePtr bare = pa11::strip_cv(base);
			Node simple("simple-declaration");
			if (bare->kind == pa11::TypeKind::Record &&
			    bare->tag == "union" &&
			    bare->name.find("__anonymous_union_type__") == 0)
			{
				string storage_name = bare->name;
				const string prefix = "__anonymous_union_type__";
				storage_name.replace(0,
				                     prefix.size(),
				                     "__anonymous_union_storage__");
				Binding* storage = add_value(current_scope(),
				                             BindingKind::Variable,
				                             storage_name,
				                             bare);
				Node var("variable " + storage_name + " " +
				         pa11::describe_type(bare));
				if (ensure_default_constructor(bare) != NULL)
					add_child(var, default_constructor_action(storage));
				add_child(simple, var);
				if (bare->scope != NULL)
					inject_anonymous_union_members(bare->scope, storage);
			}
			add_child(out, simple);
		}
		return;
	}

	if (current_scope()->kind == ScopeKind::Class && at(OP_COLON))
	{
		expect(OP_COLON);
		Expr width = parse_expression();
		if (!width.has_constant_value)
			throw runtime_error("invalid bit-field width");
		Binding* field = add_value(current_scope(),
		                           BindingKind::Variable,
		                           "__anonymous_bitfield_" + to_string(pos_),
		                           base);
		field->is_bit_field = true;
		field->bit_width = width.constant_value;
		TypePtr record = pa11::record_type_for_scope(current_scope());
		if (record.get() != NULL)
			record->layout_valid = false;
		expect(OP_SEMICOLON);
		return;
	}

	Declarator declarator = parse_declarator(false);
	bool bit_field = false;
	uint64_t bit_width = 0;
	if (current_scope()->kind == ScopeKind::Class && consume(OP_COLON))
	{
		Expr width = parse_expression();
		if (!width.has_constant_value)
			throw runtime_error("invalid bit-field width");
		bit_field = true;
		bit_width = width.constant_value;
	}
	if (at(OP_LBRACE) && declarator_function_suffix(declarator) != NULL)
	{
		Node node(current_scope()->kind == ScopeKind::Namespace ? "" :
		          "simple-declaration");
		Binding* function =
			declare_one(specs, base, declarator, NULL, true, node);
		if (current_scope()->kind == ScopeKind::Class)
		{
			const Suffix* suffix = declarator_function_suffix(declarator);
			PendingFunctionBody pending;
			pending.function = function;
			pending.node = node.children.back();
			if (suffix != NULL)
				pending.parameters = suffix->parameters;
			pending.body_pos = pos_;
			skip_balanced(OP_LBRACE, OP_RBRACE);
			pending_member_bodies_[current_scope()].push_back(pending);
			return;
		}
		parse_function_body(function, declarator, node);
		if (emit_node)
		{
			if (node.line.empty())
				add_child(out, node.children.back());
			else
				add_child(out, node);
		}
		else if (current_scope()->kind == ScopeKind::Class &&
		         !node.children.empty())
			extra_lowir_nodes_.push_back(node.children.back());
		return;
	}

	if (at(OP_ASS) && lookahead(KW_DELETE, 1) &&
	    declarator_function_suffix(declarator) != NULL)
	{
		Node node(current_scope()->kind == ScopeKind::Namespace ? "" :
		          "simple-declaration");
		Binding* function =
			declare_one(specs, base, declarator, NULL, false, node);
		deleted_functions_.insert(function);
		for (size_t i = 0; i < node.children.size(); ++i)
			if (node.children[i].binding == function)
				node.children[i].token_text = "deleted";
		expect(OP_ASS);
		expect(KW_DELETE);
		expect(OP_SEMICOLON);
		if (emit_node && !node.children.empty())
		{
			if (node.line.empty())
			{
				for (size_t i = 0; i < node.children.size(); ++i)
					add_child(out, node.children[i]);
			}
			else
				add_child(out, node);
		}
		return;
	}

	Expr init;
	bool has_init = false;
	bool brace_init = false;
	if (consume(OP_ASS))
	{
		if (at(OP_LBRACE))
		{
			has_init = true;
			init = parse_braced_init_list();
		}
		else
		{
			has_init = true;
			init = parse_expression();
		}
		if (has_init)
			init.copy_initialization = true;
	}
	else if ((brace_init = consume(OP_LBRACE)))
	{
		has_init = true;
		--pos_;
		init = parse_braced_init_list();
	}
	else if (at(OP_LPAREN) && !declarator_function_suffix(declarator))
	{
		expect(OP_LPAREN);
		if (!at(OP_RPAREN))
		{
			vector<Expr> args = parse_argument_list();
			if (args.size() == 1)
				init = args[0];
			else
			{
				TypePtr decl_type = apply_declarator(declarator, base);
				if (pa11::strip_cv(decl_type)->kind != pa11::TypeKind::Record)
					throw runtime_error("unsupported direct initializer");
				init.valid = true;
				init.braced_init_list = true;
				init.node = Node("braced-init-list");
				for (size_t i = 0; i < args.size(); ++i)
					add_child(init.node, args[i].node);
			}
			has_init = true;
		}
		expect(OP_RPAREN);
	}

	Node node(current_scope()->kind == ScopeKind::Namespace ? "" :
	          "simple-declaration");
	Binding* first =
		declare_one(specs, base, declarator, has_init ? &init : NULL, false, node);
	if (bit_field)
	{
		first->is_bit_field = true;
		first->bit_width = bit_width;
	}
	while (consume(OP_COMMA))
	{
		Declarator next = parse_declarator(false);
		Expr next_init;
		bool next_has_init = false;
		if (consume(OP_ASS))
		{
			next_has_init = true;
			next_init = at(OP_LBRACE) ? parse_braced_init_list() :
				parse_expression();
			next_init.copy_initialization = true;
		}
		declare_one(specs, base, next, next_has_init ? &next_init : NULL, false, node);
	}
	expect(OP_SEMICOLON);
	if (emit_node && !node.children.empty())
	{
		if (node.line.empty())
		{
			for (size_t i = 0; i < node.children.size(); ++i)
				add_child(out, node.children[i]);
		}
		else
			add_child(out, node);
	}
}

bool Parser::parse_friend_declaration()
{
	if (current_scope()->kind != ScopeKind::Class || !at(KW_FRIEND))
		return false;
	Scope* class_scope = current_scope();
	expect(KW_FRIEND);
	if (starts_class_key())
	{
		ETokenType key = current().type;
		++pos_;
		QualifiedName name = parse_id_expression_name();
		Scope* target = name.qualifier != NULL
			? name.qualifier : nearest_namespace_scope(class_scope);
		vector<Binding*> found = lookup_qualified_set(target,
		                                              name.name,
		                                              pa11::LOOKUP_TYPE);
		TypePtr friend_type;
		if (!found.empty() &&
		    found[0]->type.get() != NULL &&
		    pa11::strip_cv(found[0]->type)->kind == pa11::TypeKind::Record)
			friend_type = found[0]->type;
		else
			friend_type = add_record(target,
			                         name.name,
			                         class_tag(key),
			                         false,
			                         NULL);
		add_friend_class(class_scope, friend_type);
		expect(OP_SEMICOLON);
		return true;
	}

	DeclSpecs specs = parse_decl_specifier_seq(false);
	specs.friend_decl = true;
	TypePtr base = type_from_decl_specs(specs);
	Declarator declarator = parse_declarator(false);
	TypePtr type = apply_declarator(declarator, base);
	if (type->kind != pa11::TypeKind::Function)
		throw runtime_error("unsupported friend declaration");
	const QualifiedName& qname = declarator_name(declarator);
	Scope* target = qname.qualifier != NULL
		? qname.qualifier : nearest_namespace_scope(class_scope);
	Binding* function =
		add_function_binding(target, qname.name, type, !qname.qualified);
	function->language_linkage = current_language_linkage();
	const Suffix* suffix = declarator_function_suffix(declarator);
	function->unwind_no = suffix != NULL && suffix->noexcept_decl;
	if (suffix != NULL)
	{
		vector<Expr> defaults;
		vector<string> names;
		for (size_t i = 0; i < suffix->parameters.size(); ++i)
		{
			defaults.push_back(suffix->parameters[i].default_value);
			names.push_back(suffix->parameters[i].name);
		}
		default_arguments_[function] = defaults;
		function_parameter_names_[function] = names;
	}
	add_friend_function(class_scope, function);

	if (at(OP_LBRACE))
	{
		function->is_inline_definition = true;
		Node node;
		Node fn("function-definition " + qualified_decl_name(function) + " " +
		        pa11::describe_type(type));
		fn.binding = function;
		fn.type = type;
		add_child(node, fn);
		parse_function_body(function, declarator, node);
		if (!node.children.empty())
			extra_lowir_nodes_.push_back(node.children.back());
		return true;
	}
	expect(OP_SEMICOLON);
	return true;
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
	if (!at(OP_LBRACE) && !at(OP_COLON))
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
	Binding* ctor = add_value(class_scope,
	                          BindingKind::Function,
	                          class_scope->name,
	                          fn_type);
	ctor->unwind_no = suffix.noexcept_decl;
	Node fn("function-definition " + qualified_decl_name(ctor) + " " +
	        pa11::describe_type(fn_type));
	fn.binding = ctor;
	fn.type = fn_type;
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
	if (consume(OP_COLON))
		throw runtime_error("unsupported out-of-class constructor initializer");
	scopes_.push_back(function_scope);
	function_returns_.push_back(pa11::make_fundamental(FT_VOID));
	active_functions_.push_back(ctor);
	Node body = parse_compound_statement();
	active_functions_.pop_back();
	function_returns_.pop_back();
	scopes_.pop_back();
	add_child(fn, body);
	if (emit_node)
		add_child(out, fn);
	else
		extra_lowir_nodes_.push_back(fn);
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
		if (consume(KW_DEFAULT) || consume(KW_DELETE))
		{
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
					if (args.size() == 1)
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
	if (explicit_base)
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
	add_child(fn, body);
	extra_lowir_nodes_.push_back(fn);
	return true;
}

void Parser::validate_record_copy_initialization(TypePtr type, const Expr& init)
{
	TypePtr record = pa11::strip_cv(type);
	pa11::layout_record_type(record);
	if (init.braced_init_list)
	{
		for (size_t i = 0; i < record->fields.size(); ++i)
			if (default_member_initializers_.find(record->fields[i]) !=
			    default_member_initializers_.end())
				throw runtime_error("default member initializer disqualifies aggregate");
	}
	size_t arg_count = init.braced_init_list ? init.node.children.size() : 1;
	if (record->scope == NULL)
		return;
	map<string, vector<Binding*> >::const_iterator found =
		record->scope->members.find(record->scope->name);
	if (found == record->scope->members.end())
		return;
	for (size_t i = 0; i < found->second.size(); ++i)
		if (found->second[i]->kind == BindingKind::Function &&
		    found->second[i]->is_explicit &&
		    found->second[i]->type->parameters.size() == arg_count + 1)
				throw runtime_error("explicit constructor in copy initialization");
}

Binding* Parser::declare_function_entity(const DeclSpecs& specs,
                                         Scope* target,
                                         const string& name,
                                         TypePtr type,
                                         const Declarator& declarator,
                                         bool function_definition,
                                         bool nonstatic_member_function,
                                         Node& out)
{
	Binding* function = add_value(target, BindingKind::Function, name, type);
	function->language_linkage = current_language_linkage();
	function->is_static_member =
		target->kind == ScopeKind::Class && specs.static_decl;
	function->is_inline_definition =
		function_definition && current_scope()->kind == ScopeKind::Class;
	function->is_private =
		target->kind == ScopeKind::Class &&
		!class_private_access_.empty() &&
		class_private_access_.back();
	function->is_protected_member =
		target->kind == ScopeKind::Class &&
		!class_protected_access_.empty() &&
		class_protected_access_.back();
	const Suffix* suffix = declarator_function_suffix(declarator);
	function->unwind_no = suffix != NULL && suffix->noexcept_decl;
	if (suffix != NULL)
	{
		vector<Expr> defaults;
		vector<string> names;
		if (nonstatic_member_function)
		{
			defaults.push_back(Expr());
			names.push_back("this");
		}
		for (size_t i = 0; i < suffix->parameters.size(); ++i)
		{
			defaults.push_back(suffix->parameters[i].default_value);
			names.push_back(suffix->parameters[i].name);
		}
		default_arguments_[function] = defaults;
		function_parameter_names_[function] = names;
	}
	string keyword = function_definition ? "function-definition " :
		"function-declaration ";
	Node fn(keyword + qualified_decl_name(function) + " " +
	        pa11::describe_type(type));
	fn.binding = function;
	fn.type = type;
	add_child(out, fn);
	return function;
}

void Parser::apply_variable_initializer(const DeclSpecs& specs,
                                        Scope* target,
                                        Binding* variable,
                                        TypePtr type,
                                        const Expr* init,
                                        Node& var)
{
	if (init != NULL &&
	    init->copy_initialization &&
	    pa11::strip_cv(type)->kind == pa11::TypeKind::Record)
		validate_record_copy_initialization(type, *init);
	if (init != NULL)
	{
		if (init->braced_init_list)
		{
			Node list = init->node;
			ensure_aggregate_constructors_for_init(type, list);
			list.line += " lvalue " + pa11::describe_type(type);
			list.type = type;
			if (target->kind == ScopeKind::Class && !variable->is_static_member)
				default_member_initializers_[variable] = list;
			add_child(var, list);
			return;
		}
		if (pa11::strip_cv(type)->kind == pa11::TypeKind::Record)
		{
			if (target->kind == ScopeKind::Class && !variable->is_static_member)
				default_member_initializers_[variable] = init->node;
			add_child(var, init->node);
			return;
		}
		Conversion conv = convert_to(*init, type);
		if (!conv.viable)
			throw runtime_error("invalid initializer conversion");
		if (target->kind == ScopeKind::Class && !variable->is_static_member)
			default_member_initializers_[variable] = conv.expr.node;
		add_child(var, conv.expr.node);
		if ((specs.constexpr_decl || pa11::type_has_const(type)) &&
		    conv.expr.has_constant_value)
		{
			variable->has_constant = true;
			variable->constant_value = conv.expr.constant_value;
		}
	}
	else if (pa11::strip_cv(type)->kind == pa11::TypeKind::Record &&
	         ensure_default_constructor(type) != NULL)
	{
		add_child(var, default_constructor_action(variable));
	}
}

Binding* Parser::declare_one(const DeclSpecs& specs,
                             TypePtr base,
                             const Declarator& declarator,
                             const Expr* init,
                             bool function_definition,
                             Node& out)
{
	const QualifiedName& qname = declarator_name(declarator);
	Scope* target = qname.qualifier != NULL ? qname.qualifier : current_scope();
	TypePtr type = apply_declarator(declarator, base);
	if (specs.typedef_decl)
	{
		Binding* alias = add_alias(target, qname.name, type);
		add_child(out, Node("type-alias " + qname.name + " " +
		                    pa11::describe_type(alias->type)));
		return alias;
	}

	if (specs.constexpr_decl && !pa11::is_reference_type(type))
		type = pa11::make_cv(type, pa11::CV_CONST);
	if (init != NULL &&
	    init->braced_init_list &&
	    type->kind == pa11::TypeKind::Array &&
	    type->unknown_bound)
		type = pa11::make_array(type->base, false, init->node.children.size());
	bool nonstatic_member_function =
		target->kind == ScopeKind::Class &&
		type->kind == pa11::TypeKind::Function &&
		!specs.static_decl;
	if (nonstatic_member_function)
		type = make_member_function_type(target, type);
	if (type->kind == pa11::TypeKind::Function || function_definition)
	{
		return declare_function_entity(specs,
		                               target,
		                               qname.name,
		                               type,
		                               declarator,
		                               function_definition,
		                               nonstatic_member_function,
		                               out);
	}

	Binding* variable = NULL;
	if ((target->kind == ScopeKind::Namespace ||
	     target->kind == ScopeKind::Class) &&
	    (qname.qualifier != NULL || target->kind == ScopeKind::Namespace))
	{
		Binding* existing =
			pa11::find_owned_binding(target, qname.name, BindingKind::Variable);
		if (existing != NULL && pa11::same_type(existing->type, type))
			variable = existing;
	}
	if (variable == NULL)
		variable = add_value(target, BindingKind::Variable, qname.name, type);
	variable->language_linkage = current_language_linkage();
	variable->is_static_member =
		variable->is_static_member ||
		(target->kind == ScopeKind::Class &&
		 (specs.static_decl || qname.qualifier != NULL));
	variable->is_thread_local =
		variable->is_thread_local || specs.thread_local_decl;
	variable->is_mutable_member =
		target->kind == ScopeKind::Class && specs.mutable_decl;
	variable->is_private =
		target->kind == ScopeKind::Class &&
		!class_private_access_.empty() &&
		class_private_access_.back();
	variable->is_protected_member =
		target->kind == ScopeKind::Class &&
		!class_protected_access_.empty() &&
		class_protected_access_.back();
	if (target->kind == ScopeKind::Class)
	{
		TypePtr record = pa11::record_type_for_scope(target);
		if (record.get() != NULL)
			record->layout_valid = false;
	}
	ensure_default_destructor(type);
	Node var("variable " + qname.name + " " + pa11::describe_type(type));
	var.binding = variable;
	var.type = type;
	if (specs.extern_decl && target->kind == ScopeKind::Namespace && init == NULL)
		return variable;
	apply_variable_initializer(specs, target, variable, type, init, var);
	add_child(out, var);
	return variable;
}

}  // namespace internal
}  // namespace pa12
