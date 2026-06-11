#include "pa12_internal.h"
#include "pa12_templates_function_support.h"
using namespace std;
namespace pa12 {
namespace internal {
bool record_has_reference_field(TypePtr type) {
	TypePtr bare = pa11::strip_cv(type);
	if (bare->kind != pa11::TypeKind::Record)
		return false;
	vector<TypePtr> bases = pa11::record_direct_bases(bare);
	for (size_t i = 0; i < bases.size(); ++i)
		if (record_has_reference_field(bases[i]))
			return true;
	for (size_t i = 0; i < bare->fields.size(); ++i) {
		TypePtr field = bare->fields[i]->type;
		if (pa11::is_reference_type(field))
			return true;
		if (record_has_reference_field(field))
			return true; }
	return false; }
vector<Binding*> declared_instance_fields(TypePtr type) {
	vector<Binding*> fields;
	TypePtr bare = pa11::strip_cv(type);
	if (bare->kind != pa11::TypeKind::Record || bare->scope == NULL)
		return fields;
	for (size_t i = 0; i < bare->scope->binding_order.size(); ++i) {
		Binding* member = bare->scope->binding_order[i];
		if (member->kind == BindingKind::Variable &&
		    !member->is_static_member &&
		    member->aliased_binding == NULL)
			fields.push_back(member); }
	return fields; }
void Parser::append_constructor_base_init_actions(
	TypePtr class_type,
	const vector<TypePtr>& direct_bases,
	const vector<Node>& explicit_base_actions,
	Node& body) {
	TypePtr bare = pa11::strip_cv(class_type);
	vector<TypePtr> bases;
	if (bare.get() != NULL && bare->kind == pa11::TypeKind::Record) {
		vector<TypePtr> virtual_bases = pa11::record_virtual_bases(bare);
		for (size_t i = 0; i < virtual_bases.size(); ++i) {
			TypePtr base = virtual_bases[i].get() != NULL
				? pa11::strip_cv(virtual_bases[i]) : TypePtr();
			if (base.get() != NULL && base->kind == pa11::TypeKind::Record)
				bases.push_back(base); } }
	for (size_t i = 0; i < direct_bases.size(); ++i) {
		if (bare.get() != NULL && bare->kind == pa11::TypeKind::Record &&
		    pa11::record_direct_base_is_virtual(bare, i))
			continue;
		TypePtr base = direct_bases[i].get() != NULL
			? pa11::strip_cv(direct_bases[i]) : TypePtr();
		if (base.get() != NULL && base->kind == pa11::TypeKind::Record)
			bases.push_back(base); }
	for (size_t b = 0; b < bases.size(); ++b) {
		TypePtr base = bases[b];
		bool explicit_init = false;
		for (size_t i = 0; i < explicit_base_actions.size(); ++i) {
			TypePtr explicit_base =
				explicit_base_actions[i].type.get() != NULL
				? pa11::strip_cv(explicit_base_actions[i].type)
				: TypePtr();
			if (explicit_base.get() != NULL &&
			    pa11::same_type(explicit_base, base)) {
				add_child(body, explicit_base_actions[i]);
				explicit_init = true;
				break; } }
		if (explicit_init)
			continue;
		Binding* base_ctor = ensure_default_constructor(base);
		if (base_ctor != NULL &&
		    suppress_implicit_template_base_init_ &&
		    base_ctor->is_generated_default_constructor)
			mark_suppressed_generated_constructor_dependencies(base_ctor);
		else if (base_ctor != NULL) {
			Node base_action = make_base_init_action(base, NULL);
			add_child(body, base_action); }
	} }
void stamp_template_member_function_symbol(Binding* binding) {
	if (binding == NULL ||
	    binding->kind != BindingKind::Function ||
	    !binding->function_specialization_symbol.empty() ||
	    binding->owner == NULL ||
	    binding->owner->kind != ScopeKind::Class)
		return;
	TypePtr record = pa11::record_type_for_scope(binding->owner);
	record = record.get() != NULL ? pa11::strip_cv(record) : TypePtr();
	if (record.get() == NULL ||
	    record->kind != pa11::TypeKind::Record ||
	    !record->is_template_specialization)
		return;
	binding->function_specialization_symbol =
		abi_binding_symbol(binding, map<string, size_t>()); }
bool Parser::parse_qualified_destructor_definition(Node& out, bool emit_node) {
	if (current_scope()->kind == ScopeKind::Class ||
	    !at_identifier() || !lookahead(OP_COLON2, 1))
		return false;
	size_t save = pos_;
	string class_name = consume_identifier();
	expect(OP_COLON2);
	if (!consume(OP_COMPL) || !at_identifier()) {
		pos_ = save;
		return false; }
	string dtor_type_name = consume_identifier();
	if (!at(OP_LPAREN)) {
		pos_ = save;
		return false; }
	Binding* class_binding =
		pa11::lookup_unqualified(current_scope(),
		                         class_name,
		                         pa11::LOOKUP_QUALIFIER);
	Scope* class_scope = resolve_qualifier(class_binding);
	if (class_scope == NULL ||
	    class_scope->kind != ScopeKind::Class ||
	    dtor_type_name != class_scope->name) {
		pos_ = save;
		return false; }
	TypePtr class_type = pa11::record_type_for_scope(class_scope);
	if (class_type.get() == NULL) {
		pos_ = save;
		return false; }
	complete_template_record(class_type);
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
	if (consume(OP_ASS)) {
		if (!consume(KW_DEFAULT))
			throw runtime_error("unsupported destructor definition");
		expect(OP_SEMICOLON);
		defaulted = true; }
	if (!at(OP_LBRACE)) {
		if (!defaulted) {
			pos_ = save;
			return false; } }
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
	if (!active_class_instantiation_dependent())
		stamp_template_member_function_symbol(dtor);
	Node fn("function-definition " + qualified_decl_name(dtor) + " " +
	        pa11::describe_type(fn_type));
	fn.binding = dtor;
	fn.type = fn_type;
	if (dtor->is_inline_definition) {
		PendingFunctionBody pending;
		pending.function = dtor;
		pending.node = fn;
		pending.body_pos = pos_;
		skip_balanced(OP_LBRACE, OP_RBRACE);
		enqueue_pending_member_body(class_scope, pending);
		return true; }
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
	else {
		scopes_.push_back(function_scope);
		function_returns_.push_back(pa11::make_fundamental(FT_VOID));
		active_functions_.push_back(dtor);
		body = parse_compound_statement();
		active_functions_.pop_back();
		function_returns_.pop_back();
		scopes_.pop_back(); }
	if (body.children.empty() && !dtor->is_virtual) {
		dtor->is_noop_destructor = true;
		map<string, vector<Binding*> >::iterator found =
			class_scope->members.find(dtor_name);
		if (found != class_scope->members.end())
			for (size_t i = 0; i < found->second.size(); ++i)
				if (found->second[i]->kind == BindingKind::Function &&
				    pa11::same_type(found->second[i]->type, dtor->type))
					found->second[i]->is_noop_destructor = true; }
	add_child(fn, body);
	if (emit_node)
		add_child(out, fn);
	else
		extra_lowir_nodes_.push_back(fn);
	return true; }
void Parser::parse_constructor_body_from_parameters(
	Binding* function,
	TypePtr class_type,
	const vector<ParameterInfo>& parameters,
	Node& function_node) {
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
	map<string, vector<Binding*> > parameter_packs;
	for (size_t i = 0; i < parameters.size(); ++i) {
		if (!parameters[i].pack_expression_name.empty() &&
		    !parameters[i].pack_name.empty()) {
			TemplateArgument subst;
			if (find_template_value_substitution(parameters[i].pack_name,
			                                     subst) &&
			    subst.kind == TemplateArgumentKind::Pack &&
			    subst.pack.empty()) {
				parameter_packs[parameters[i].pack_expression_name];
				continue; } }
		TypePtr parameter_type =
			parameters[i].type.get() != NULL
			? substitute_template_type(parameters[i].type) : TypePtr();
		if (parameter_type.get() == NULL &&
		    i + 1 < function->type->parameters.size())
			parameter_type = function->type->parameters[i + 1];
		if (parameter_type.get() == NULL) {
			if (!parameters[i].pack_expression_name.empty())
				parameter_packs[parameters[i].pack_expression_name];
			continue; }
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
		if (!pname.empty()) {
				param = pa11::add_binding(function_scope,
				                          BindingKind::Parameter,
				                          pname,
				                          parameter_type);
				if (!parameters[i].pack_expression_name.empty())
					parameter_packs[parameters[i].pack_expression_name]
						.push_back(param); }
			Node param_node("parameter " + node_name + " " +
			                pa11::describe_type(parameter_type));
			param_node.binding = param;
			param_node.type = parameter_type;
			add_child(fn, param_node); }
		map<Binding*, vector<string> >::const_iterator saved_names =
			function_parameter_names_.find(function);
		for (size_t pi = parameters.size() + 1;
		     pi < function->type->parameters.size();
		     ++pi) {
			string pname =
				saved_names != function_parameter_names_.end() &&
				pi < saved_names->second.size() &&
				!saved_names->second[pi].empty()
				? saved_names->second[pi]
				: "__param" + to_string(pi);
			Binding* param =
				pa11::add_binding(function_scope,
				                  BindingKind::Parameter,
				                  pname,
				                  function->type->parameters[pi]);
			Node param_node("parameter " + pname + " " +
			                pa11::describe_type(
				                function->type->parameters[pi]));
			param_node.binding = param;
			param_node.type = function->type->parameters[pi];
			add_child(fn, param_node); }
		scopes_.push_back(function_scope);
	function_returns_.push_back(pa11::make_fundamental(FT_VOID));
	active_functions_.push_back(function);
	function_parameter_pack_substitutions_.push_back(parameter_packs);
	Node body("compound-statement");
	bool function_try_block = consume(KW_TRY);
	map<Binding*, Node> explicit_member_initializers;
	vector<Node> explicit_base_actions;
	bool delegating = false;
	vector<TypePtr> direct_bases = pa11::record_direct_bases(class_type);
	TypePtr direct_base = !direct_bases.empty() && direct_bases[0].get() != NULL
		? pa11::strip_cv(direct_bases[0]) : TypePtr();
	if (consume(OP_COLON)) {
		for (;;) {
			string name = consume_identifier();
			vector<TemplateArgument> init_template_args;
			bool have_init_template_args = false;
			if (at(OP_LT)) {
				parse_template_argument_list(init_template_args);
				have_init_template_args = true; }
			Binding* field = pa11::lookup_qualified(class_scope,
			                                        name,
			                                        pa11::LOOKUP_VARIABLE);
			Expr init;
			vector<Expr> parsed_args;
			size_t parsed_args_begin = 0;
			size_t parsed_args_end = 0;
			bool have_paren_init = false;
			bool init_target_is_base = false;
			bool have_init = false;
			if (at(OP_LBRACE)) {
				init = parse_braced_init_list();
				have_init = true; }
			else if (consume(OP_LPAREN)) {
				have_paren_init = true;
				if (!at(OP_RPAREN)) {
					parsed_args_begin = pos_;
					vector<Expr> args = parse_argument_list();
					parsed_args_end = pos_;
					parsed_args = args;
					TypePtr init_target;
					if (name == class_scope->name)
						init_target = class_type;
					else if (direct_base.get() != NULL &&
					    initializer_names_direct_base(class_scope,
					                                  direct_base,
					                                  name,
					                                  have_init_template_args
					                                  ? &init_template_args : NULL)) {
						init_target = direct_base;
						init_target_is_base = true; }
					else if (field != NULL)
						init_target = field->type;
					if (init_target.get() != NULL &&
					    pa11::strip_cv(init_target)->kind ==
					    pa11::TypeKind::Record) {
						if (init_target_is_base) { }
						else
						try {
							init = make_constructor_init_expr(init_target,
							                                  args,
							                                  false);
							have_init = true; }
						catch (const runtime_error& err) {
							if (string(err.what()) != "no matching constructor" ||
							    args.size() != 1 ||
							    !pa11::same_type(
								    pa11::strip_cv(init_target),
								    pa11::strip_cv(
									    expression_object_type(args[0].type))))
								throw;
							init = args[0];
							have_init = true; } }
					else if (args.size() == 1) {
						init = args[0];
						have_init = true; } }
				else {
					TypePtr init_target;
					if (name == class_scope->name)
						init_target = class_type;
					else if (direct_base.get() != NULL &&
					    initializer_names_direct_base(class_scope,
					                                  direct_base,
					                                  name,
					                                  have_init_template_args
					                                  ? &init_template_args : NULL)) {
						init_target = direct_base;
						init_target_is_base = true; }
					else if (field != NULL)
						init_target = field->type;
					if (init_target.get() != NULL &&
					    pa11::strip_cv(init_target)->kind ==
					    pa11::TypeKind::Record) {
						if (!init_target_is_base)
							init = make_constructor_init_expr(init_target,
							                                  vector<Expr>(),
							                                  false); }
					else {
						init.valid = true;
						init.category = ValueCategory::PRValue;
						init.braced_init_list = true;
						init.node = Node("braced-init-list"); }
					have_init = true; }
				expect(OP_RPAREN); }
			bool init_pack_expansion = consume(OP_DOTS);
			vector<TypePtr> matching_bases;
			for (size_t b = 0; b < direct_bases.size(); ++b) {
				TypePtr base = direct_bases[b].get() != NULL
					? pa11::strip_cv(direct_bases[b]) : TypePtr();
				if (base.get() != NULL &&
				    initializer_names_direct_base(
					    class_scope,
					    base,
					    name,
					    have_init_template_args
					    ? &init_template_args : NULL))
					matching_bases.push_back(base); }
			if (!matching_bases.empty()) {
				vector<Expr> expanded_inits;
				if (init_pack_expansion && parsed_args.size() == 1) {
					if (parsed_args[0].pack_expansion &&
					    !parsed_args[0].pack.empty())
						expanded_inits = parsed_args[0].pack;
					else try {
						try_expand_expression_pack_pattern(
							parsed_args_begin,
							parsed_args_end,
							expanded_inits); }
					catch (const runtime_error&) {
						expanded_inits.clear(); } }
				for (size_t b = 0; b < matching_bases.size(); ++b) {
					if (have_paren_init) {
						vector<Expr> base_args = parsed_args;
						if (init_pack_expansion) {
							if (expanded_inits.size() !=
							    matching_bases.size())
								throw runtime_error(
									"pack expansion size mismatch");
							base_args.clear();
							base_args.push_back(expanded_inits[b]); }
						Expr base_init =
							make_constructor_init_expr(matching_bases[b],
							                           base_args,
							                           false);
						explicit_base_actions.push_back(
							make_base_init_action(matching_bases[b],
							                      &base_init.node)); }
					else
						explicit_base_actions.push_back(
							make_base_init_action(
								matching_bases[b],
								have_init ? &init.node : NULL)); } }
			else if (name == class_scope->name && have_init) {
				Node action("delegating-init-action " + name);
				action.type = class_type;
				action.direct_call = init.node.direct_call;
				add_child(action, init.node);
				add_child(body, action);
				delegating = true; }
			else if (field != NULL && have_init) {
				explicit_member_initializers[field] =
					make_member_init_action(field, &init.node); }
			else if (have_init) {
				Node action("member-init-action " + name);
				action.token_text = name;
				add_child(action, init.node);
				add_child(body, action); }
			if (!consume(OP_COMMA))
				break; } }
	if (delegating) { }
	else
		append_constructor_base_init_actions(class_type,
		                                     direct_bases,
		                                     explicit_base_actions,
		                                     body);
	vector<Binding*> fields;
	try {
		pa11::layout_record_type(class_type);
		fields = class_type->fields; }
	catch (const runtime_error& err) {
		if ((string(err.what()) != "incomplete class type" &&
		     string(err.what()) != "incomplete object type") ||
		    active_class_instantiations_.empty())
			throw;
		fields = declared_instance_fields(class_type); }
	for (size_t i = 0; i < fields.size(); ++i) {
		Binding* field = fields[i];
		map<Binding*, Node>::const_iterator explicit_init =
			explicit_member_initializers.find(field);
		if (explicit_init != explicit_member_initializers.end()) {
			add_child(body, explicit_init->second);
			continue; }
			map<Binding*, Node>::const_iterator init =
				default_member_initializers_.find(field);
			if (init != default_member_initializers_.end())
				add_child(body, make_member_init_action(field, &init->second));
			else if (pa11::strip_cv(field->type)->kind == pa11::TypeKind::Record) {
				try {
					if (ensure_default_constructor(field->type) != NULL)
						add_child(body, make_member_init_action(field, NULL)); }
				catch (const runtime_error& err) {
					if (string(err.what()) !=
					    "member has no default constructor")
						throw; }
			} }
	Node parsed_body = parse_compound_statement();
	for (size_t i = 0; i < parsed_body.children.size(); ++i)
		add_child(body, parsed_body.children[i]);
	if (function_try_block) {
		Node try_node("try-statement");
		Node try_block("try-block");
		add_child(try_block, body);
		add_child(try_node, try_block);
		do {
			expect(KW_CATCH);
			expect(OP_LPAREN);
			Node catch_node("catch-clause");
			string catch_name;
			if (consume(OP_DOTS))
				catch_node.token_text = "catch-all";
			else {
				TypePtr catch_type = parse_type_id();
				if (at_identifier())
					catch_name = consume_identifier();
				catch_node.type = catch_type;
				catch_node.line += " " + pa11::describe_type(catch_type); }
			expect(OP_RPAREN);
			expect(OP_LBRACE);
			Node catch_body("compound-statement");
			Scope* catch_scope = pa11::create_child_scope(current_scope(),
			                                              ScopeKind::Block,
			                                              "");
			scopes_.push_back(catch_scope);
			if (!catch_name.empty()) {
				Binding* catch_binding = add_value(catch_scope,
				                                   BindingKind::Variable,
				                                   catch_name,
				                                   catch_node.type);
				catch_node.binding = catch_binding; }
			while (!at(OP_RBRACE)) {
				Node item = parse_block_item();
				if (!item.line.empty())
					add_child(catch_body, item); }
			scopes_.pop_back();
			expect(OP_RBRACE);
			add_child(catch_node, catch_body);
			add_child(try_node, catch_node); }
		while (at(KW_CATCH));
		Node wrapped("compound-statement");
		add_child(wrapped, try_node);
		body = wrapped; }
	function_parameter_pack_substitutions_.pop_back();
	active_functions_.pop_back();
	function_returns_.pop_back();
	scopes_.pop_back();
	function->is_noop_constructor = body.children.empty();
	add_child(fn, body);
	remember_function_body(function, fn); }
void Parser::mark_suppressed_generated_constructor_dependencies(Binding* ctor) {
	if (ctor == NULL || !ctor->is_generated_default_constructor)
		return;
	map<Binding*, Node>::const_iterator found = function_bodies_.find(ctor);
	if (found == function_bodies_.end())
		return;
	vector<const Node*> pending;
	pending.push_back(&found->second);
	set<Binding*> seen;
	while (!pending.empty()) {
		const Node* node = pending.back();
		pending.pop_back();
		if (node->direct_call != NULL &&
		    seen.insert(node->direct_call).second) {
			if (node->direct_call->is_generated_default_constructor)
				mark_suppressed_generated_constructor_dependencies(
					node->direct_call);
			else {
				parse_pending_function_body(node->direct_call);
				parse_pending_member_body(node->direct_call);
				bool marked = false;
				for (size_t i = 0; i < extra_lowir_nodes_.size(); ++i)
					if (extra_lowir_nodes_[i].binding == node->direct_call) {
						extra_lowir_nodes_[i].token_text =
							"inline-object-root";
						marked = true; }
				if (!marked)
					node->direct_call->is_object_root = true; } }
		for (size_t i = 0; i < node->children.size(); ++i)
			pending.push_back(&node->children[i]); } }
bool Parser::parse_qualified_constructor_definition(Node& out,
                                                    bool emit_node,
                                                    bool inline_spec,
                                                    bool constexpr_spec) {
	if (current_scope()->kind == ScopeKind::Class ||
	    !(at(OP_COLON2) || at_identifier()))
		return false;
	size_t save = pos_;
	QualifiedName name;
	try {
		name = parse_id_expression_name(); }
	catch (const exception&) {
		pos_ = save;
		return false; }
	if (name.qualifier == NULL ||
	    name.qualifier->kind != ScopeKind::Class ||
	    !constructor_name_matches_scope(name.qualifier, name.name) ||
	    !at(OP_LPAREN)) {
		pos_ = save;
		return false; }
	Scope* class_scope = name.qualifier;
	TypePtr class_type = pa11::record_type_for_scope(class_scope);
	if (class_type.get() == NULL) {
		pos_ = save;
		return false; }
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
	if (consume(OP_ASS)) {
		if (!consume(KW_DEFAULT))
			throw runtime_error("unsupported constructor definition");
		expect(OP_SEMICOLON);
		defaulted = true; }
	if (!defaulted && !at(OP_LBRACE) && !at(OP_COLON) && !at(KW_TRY)) {
		pos_ = save;
		return false; }
	vector<TypePtr> fn_params;
	fn_params.push_back(pa11::make_pointer(class_type));
	for (size_t i = 0; i < parameters.size(); ++i)
		fn_params.push_back(parameters[i].type);
	TypePtr fn_type = pa11::make_function(pa11::make_fundamental(FT_VOID),
	                                      fn_params,
	                                      variadic);
	fn_type = substitute_template_type(fn_type);
	for (size_t i = 0;
	     i < parameters.size() && i + 1 < fn_type->parameters.size();
	     ++i)
		parameters[i].type = fn_type->parameters[i + 1];
	Binding* existing_ctor = NULL;
	map<string, vector<Binding*> >::iterator existing_it =
		class_scope->members.find(class_scope->name);
	if (existing_it != class_scope->members.end())
		for (size_t i = 0; i < existing_it->second.size(); ++i) {
			Binding* candidate = existing_it->second[i];
			if (candidate->kind == BindingKind::Function &&
			    pa11::same_type(candidate->type, fn_type)) {
				existing_ctor = candidate;
				break; } }
	if (existing_ctor != NULL &&
	    existing_ctor->unwind_no != suffix.noexcept_decl)
		throw runtime_error("exception specification mismatch");
	Binding* ctor = existing_ctor != NULL
		? existing_ctor
		: add_function_binding(class_scope, class_scope->name, fn_type, false);
	for (size_t i = 0; i < parameters.size(); ++i)
		if (parameters[i].has_default)
			ctor->has_default_arguments = true;
	ctor->is_constexpr = ctor->is_constexpr || constexpr_spec;
	ctor->is_inline_definition =
		ctor->is_inline_definition || inline_spec || constexpr_spec;
	TypePtr bare_class_type = pa11::strip_cv(class_type);
	bool qualified_inline_object_root =
		ctor->is_inline_definition &&
		bare_class_type->is_template_specialization &&
		!active_class_instantiation_dependent();
	ctor->unwind_no = suffix.noexcept_decl;
	if (defaulted) {
		ctor->is_defaulted = true;
		ctor->is_generated_default_constructor = parameters.empty(); }
	if (!active_class_instantiation_dependent())
		stamp_template_member_function_symbol(ctor);
	Node fn("function-definition " + qualified_decl_name(ctor) + " " +
	        pa11::describe_type(fn_type));
	fn.binding = ctor;
	if (qualified_inline_object_root)
		fn.token_text = "inline-object-root";
	fn.type = fn_type;
	bool dependent_template_member_definition =
		!defaulted &&
		(type_is_template_dependent(class_type) ||
		 !template_type_substitutions_.empty() ||
		 !template_value_substitutions_.empty());
	if (dependent_template_member_definition)
		ctor->is_inline_definition = true;
	if (ctor->is_inline_definition) {
		if ((force_new_function_binding_ ||
		     qualified_inline_object_root) &&
		    active_class_instantiations_.empty()) {
			Node holder("constructor-definition-holder");
			add_child(holder, fn);
			parse_constructor_body_from_parameters(ctor,
			                                       class_type,
			                                       parameters,
			                                       holder);
			extra_lowir_nodes_.push_back(holder.children.back());
			return true; }
		PendingFunctionBody pending;
		pending.function = ctor;
		pending.node = fn;
		pending.parameters = parameters;
		pending.body_pos = pos_;
		pending.constructor_body = true;
		pending.class_type = class_type;
		consume(KW_TRY);
		if (consume(OP_COLON)) {
			for (;;) {
				while (!at(OP_LPAREN) && !at(OP_LBRACE) && !at_eof())
					++pos_;
				if (at(OP_LPAREN))
					skip_balanced(OP_LPAREN, OP_RPAREN);
				else if (at(OP_LBRACE))
					skip_balanced(OP_LBRACE, OP_RBRACE);
				if (!consume(OP_COMMA))
					break; } }
		skip_balanced(OP_LBRACE, OP_RBRACE);
		while (at(KW_CATCH)) {
			consume(KW_CATCH);
			skip_balanced(OP_LPAREN, OP_RPAREN);
			skip_balanced(OP_LBRACE, OP_RBRACE); }
		enqueue_pending_member_body(class_scope, pending);
		return true; }
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
	for (size_t i = 0; i < parameters.size(); ++i) {
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
		add_child(fn, param_node); }
	if (!defaulted) {
		scopes_.push_back(function_scope);
		function_returns_.push_back(pa11::make_fundamental(FT_VOID));
		active_functions_.push_back(ctor); }
	Node body("compound-statement");
	bool function_try_block = !defaulted && consume(KW_TRY);
	map<Binding*, Node> explicit_member_initializers;
	vector<Node> explicit_base_actions;
	bool delegating = false;
	vector<TypePtr> direct_bases = pa11::record_direct_bases(class_type);
	TypePtr direct_base = !direct_bases.empty() && direct_bases[0].get() != NULL
		? pa11::strip_cv(direct_bases[0]) : TypePtr();
	if (!defaulted && consume(OP_COLON)) {
		for (;;) {
			string init_name = consume_identifier();
			vector<TemplateArgument> init_template_args;
			bool have_init_template_args = false;
			if (at(OP_LT)) {
				parse_template_argument_list(init_template_args);
				have_init_template_args = true; }
			Binding* field = pa11::lookup_qualified(class_scope,
			                                        init_name,
			                                        pa11::LOOKUP_VARIABLE);
			Expr init;
			vector<Expr> parsed_args;
			size_t parsed_args_begin = 0;
			size_t parsed_args_end = 0;
			bool have_paren_init = false;
			bool init_target_is_base = false;
			bool have_init = false;
			if (at(OP_LBRACE)) {
				init = parse_braced_init_list();
				have_init = true; }
			else if (consume(OP_LPAREN)) {
				have_paren_init = true;
				if (!at(OP_RPAREN)) {
					parsed_args_begin = pos_;
					vector<Expr> args = parse_argument_list();
					parsed_args_end = pos_;
					parsed_args = args;
					TypePtr init_target;
					if (init_name == class_scope->name)
						init_target = class_type;
					else if (direct_base.get() != NULL &&
					    initializer_names_direct_base(class_scope,
					                                  direct_base,
					                                  init_name,
					                                  have_init_template_args
					                                  ? &init_template_args : NULL)) {
						init_target = direct_base;
						init_target_is_base = true; }
					else if (field != NULL)
						init_target = field->type;
					if (init_target.get() != NULL &&
					    pa11::strip_cv(init_target)->kind ==
					    pa11::TypeKind::Record) {
						if (init_target_is_base) { }
						else
						try {
							init = make_constructor_init_expr(init_target,
							                                  args,
							                                  false);
							have_init = true; }
						catch (const runtime_error& err) {
							if (string(err.what()) != "no matching constructor" ||
							    args.size() != 1 ||
							    !pa11::same_type(
								    pa11::strip_cv(init_target),
								    pa11::strip_cv(
									    expression_object_type(args[0].type))))
								throw;
							init = args[0];
							have_init = true; } }
					else if (args.size() == 1) {
						init = args[0];
						have_init = true; } }
				else {
					TypePtr init_target;
					if (init_name == class_scope->name)
						init_target = class_type;
					else if (direct_base.get() != NULL &&
					    initializer_names_direct_base(class_scope,
					                                  direct_base,
					                                  init_name,
					                                  have_init_template_args
					                                  ? &init_template_args : NULL)) {
						init_target = direct_base;
						init_target_is_base = true; }
					else if (field != NULL)
						init_target = field->type;
					if (init_target.get() != NULL &&
					    pa11::strip_cv(init_target)->kind ==
					    pa11::TypeKind::Record) {
						if (!init_target_is_base)
							init = make_constructor_init_expr(init_target,
							                                  vector<Expr>(),
							                                  false); }
					else {
						init.valid = true;
						init.category = ValueCategory::PRValue;
						init.braced_init_list = true;
						init.node = Node("braced-init-list"); }
					have_init = true; }
				expect(OP_RPAREN); }
			bool init_pack_expansion = consume(OP_DOTS);
			vector<TypePtr> matching_bases;
			for (size_t b = 0; b < direct_bases.size(); ++b) {
				TypePtr base = direct_bases[b].get() != NULL
					? pa11::strip_cv(direct_bases[b]) : TypePtr();
				if (base.get() != NULL &&
				    initializer_names_direct_base(
					    class_scope,
					    base,
					    init_name,
					    have_init_template_args
					    ? &init_template_args : NULL))
					matching_bases.push_back(base); }
			if (!matching_bases.empty()) {
				vector<Expr> expanded_inits;
				if (init_pack_expansion && parsed_args.size() == 1) {
					if (parsed_args[0].pack_expansion &&
					    !parsed_args[0].pack.empty())
						expanded_inits = parsed_args[0].pack;
					else try {
						try_expand_expression_pack_pattern(
							parsed_args_begin,
							parsed_args_end,
							expanded_inits); }
					catch (const runtime_error&) {
						expanded_inits.clear(); } }
				for (size_t b = 0; b < matching_bases.size(); ++b) {
					if (have_paren_init) {
						vector<Expr> base_args = parsed_args;
						if (init_pack_expansion) {
							if (expanded_inits.size() !=
							    matching_bases.size())
								throw runtime_error(
									"pack expansion size mismatch");
							base_args.clear();
							base_args.push_back(expanded_inits[b]); }
						Expr base_init =
							make_constructor_init_expr(matching_bases[b],
							                           base_args,
							                           false);
						explicit_base_actions.push_back(
							make_base_init_action(matching_bases[b],
							                      &base_init.node)); }
					else
						explicit_base_actions.push_back(
							make_base_init_action(
								matching_bases[b],
								have_init ? &init.node : NULL)); } }
			else if (init_name == class_scope->name && have_init) {
				Node action("delegating-init-action " + init_name);
				action.type = class_type;
				action.direct_call = init.node.direct_call;
				add_child(action, init.node);
				add_child(body, action);
				delegating = true; }
			else if (field != NULL && have_init)
				explicit_member_initializers[field] =
					make_member_init_action(field, &init.node);
			else if (have_init) {
				Node action("member-init-action " + init_name);
				action.token_text = init_name;
				add_child(action, init.node);
				add_child(body, action); }
			if (!consume(OP_COMMA))
				break; } }
	if (delegating) { }
	else
		append_constructor_base_init_actions(class_type,
		                                     direct_bases,
		                                     explicit_base_actions,
		                                     body);
	vector<Binding*> fields;
	try {
		pa11::layout_record_type(class_type);
		fields = class_type->fields; }
	catch (const runtime_error& err) {
		if ((string(err.what()) != "incomplete class type" &&
		     string(err.what()) != "incomplete object type") ||
		    active_class_instantiations_.empty())
			throw;
		fields = declared_instance_fields(class_type); }
	for (size_t i = 0; i < fields.size(); ++i) {
		Binding* field = fields[i];
		map<Binding*, Node>::const_iterator explicit_init =
			explicit_member_initializers.find(field);
		if (explicit_init != explicit_member_initializers.end()) {
			add_child(body, explicit_init->second);
			continue; }
			map<Binding*, Node>::const_iterator init =
				default_member_initializers_.find(field);
			if (init != default_member_initializers_.end())
				add_child(body, make_member_init_action(field, &init->second));
			else if (pa11::strip_cv(field->type)->kind == pa11::TypeKind::Record) {
				try {
					if (ensure_default_constructor(field->type) != NULL)
						add_child(body, make_member_init_action(field, NULL)); }
				catch (const runtime_error& err) {
					if (string(err.what()) !=
					    "member has no default constructor")
						throw; }
			} }
	if (!defaulted) {
		Node parsed_body = parse_compound_statement();
		for (size_t i = 0; i < parsed_body.children.size(); ++i)
			add_child(body, parsed_body.children[i]);
		if (function_try_block) {
			Node try_node("try-statement");
			Node try_block("try-block");
			add_child(try_block, body);
			add_child(try_node, try_block);
			do {
				expect(KW_CATCH);
				expect(OP_LPAREN);
				Node catch_node("catch-clause");
				string catch_name;
				if (consume(OP_DOTS))
					catch_node.token_text = "catch-all";
				else {
					TypePtr catch_type = parse_type_id();
					if (at_identifier())
						catch_name = consume_identifier();
					catch_node.type = catch_type;
					catch_node.line += " " + pa11::describe_type(catch_type); }
				expect(OP_RPAREN);
				expect(OP_LBRACE);
				Node catch_body("compound-statement");
				Scope* catch_scope =
					pa11::create_child_scope(current_scope(),
					                         ScopeKind::Block,
					                         "");
				scopes_.push_back(catch_scope);
				if (!catch_name.empty()) {
					Binding* catch_binding =
						add_value(catch_scope,
						          BindingKind::Variable,
						          catch_name,
						          catch_node.type);
					catch_node.binding = catch_binding; }
				while (!at(OP_RBRACE)) {
					Node item = parse_block_item();
					if (!item.line.empty())
						add_child(catch_body, item); }
				scopes_.pop_back();
				expect(OP_RBRACE);
				add_child(catch_node, catch_body);
				add_child(try_node, catch_node); }
			while (at(KW_CATCH));
			Node wrapped("compound-statement");
			add_child(wrapped, try_node);
			body = wrapped; }
		active_functions_.pop_back();
		function_returns_.pop_back();
		scopes_.pop_back(); }
	ctor->is_noop_constructor = body.children.empty();
	add_child(fn, body);
	remember_function_body(ctor, fn);
	if (emit_node)
		add_child(out, fn);
	else
		extra_lowir_nodes_.push_back(fn);
	return true; }
bool Parser::parse_qualified_conversion_definition(Node& out, bool emit_node) {
	if (current_scope()->kind == ScopeKind::Class ||
	    !(at(OP_COLON2) || at_identifier()))
		return false;
	size_t save = pos_;
	Scope* class_scope = NULL;
	try {
		class_scope = parse_nested_name_specifier(NULL); }
	catch (const exception&) {
		pos_ = save;
		return false; }
	if (class_scope == NULL ||
	    class_scope->kind != ScopeKind::Class ||
	    !consume(KW_OPERATOR)) {
		pos_ = save;
		return false; }
	TypePtr result;
	try {
		scopes_.push_back(class_scope);
		result = parse_conversion_type_id();
		scopes_.pop_back(); }
	catch (const exception&) {
		if (!scopes_.empty() && scopes_.back() == class_scope)
			scopes_.pop_back();
		pos_ = save;
		return false; }
	expect(OP_LPAREN);
	expect(OP_RPAREN);
	Suffix suffix(SuffixKind::Function);
	parse_function_suffix_tail(suffix);
	if (!at(OP_LBRACE)) {
		pos_ = save;
		return false; }
	TypePtr class_type = pa11::record_type_for_scope(class_scope);
	if (class_type.get() == NULL)
		throw runtime_error("conversion function without class type");
	vector<TypePtr> params(
		1,
		pa11::make_pointer(pa11::make_cv(class_type, suffix.function_cv)));
	TypePtr fn_type = pa11::make_function(result, params, false);
	fn_type = substitute_template_type(fn_type);
	result = fn_type->base;
	string function_name = conversion_operator_name(result);
	Binding* existing_function = NULL;
	map<string, vector<Binding*> >::iterator existing_it =
		class_scope->members.find(function_name);
	if (existing_it != class_scope->members.end())
		for (size_t i = 0; i < existing_it->second.size(); ++i) {
			Binding* candidate = existing_it->second[i];
			if (candidate->kind == BindingKind::Function &&
			    pa11::same_type(candidate->type, fn_type)) {
				existing_function = candidate;
				break; } }
	Binding* function = force_new_function_binding_
		? add_value(class_scope,
		            BindingKind::Function,
		            function_name,
		            fn_type)
		: (existing_function != NULL
		   ? existing_function
		   : add_function_binding(class_scope,
		                          function_name,
		                          fn_type,
		                          false));
	function->unwind_no = suffix.noexcept_decl;
	function->ref_qualifier = suffix.ref_qualifier;
	function_parameter_names_[function] = vector<string>(1, "this");
	if (!active_class_instantiation_dependent())
		stamp_template_member_function_symbol(function);
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
	return true; }
bool Parser::parse_conversion_function_member(bool explicit_conv,
                                              bool constexpr_conv) {
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
	if (!active_class_instantiation_dependent())
		stamp_template_member_function_symbol(function);
	if (consume(OP_ASS)) {
		if (consume(KW_DELETE)) {
			deleted_functions_.insert(function);
			expect(OP_SEMICOLON);
			return true; }
		throw runtime_error("unsupported conversion function definition"); }
	if (consume(OP_SEMICOLON))
		return true;
	if (!at(OP_LBRACE))
		throw runtime_error("conversion function missing body");
	Node fn("function-definition " + qualified_decl_name(function) + " " +
	        pa11::describe_type(fn_type));
	fn.binding = function;
	fn.type = fn_type;
	if (force_new_function_binding_ &&
	    active_class_instantiations_.empty()) {
		Node node("simple-declaration");
		add_child(node, fn);
		vector<ParameterInfo> parameters;
		parse_function_body_from_parameters(function, parameters, node);
		if (!node.children.empty())
			extra_lowir_nodes_.push_back(node.children.back());
		return true; }
	PendingFunctionBody pending;
	pending.function = function;
	pending.node = fn;
	pending.body_pos = pos_;
	skip_balanced(OP_LBRACE, OP_RBRACE);
	enqueue_pending_member_body(class_scope, pending);
	return true; }
bool Parser::parse_destructor_like_member() {
	if (current_scope()->kind != ScopeKind::Class)
		return false;
	size_t save = pos_;
	bool virtual_decl = consume(KW_VIRTUAL);
	if (!at(OP_COMPL)) {
		pos_ = save;
		return false; }
	++pos_;
	if (!at_identifier() || current().source != current_scope()->name) {
		pos_ = save;
		return false; }
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
	if (!active_class_instantiation_dependent())
		stamp_template_member_function_symbol(dtor);
	if (consume(OP_ASS)) {
		if (consume(KW_DEFAULT) || consume(KW_DELETE)) {
			expect(OP_SEMICOLON);
			return true; }
		throw runtime_error("unsupported destructor definition"); }
	if (consume(OP_SEMICOLON))
		return true;
	Node fn("function-definition " + qualified_decl_name(dtor) + " " +
	        pa11::describe_type(fn_type));
	fn.binding = dtor;
	fn.type = fn_type;
	if (dtor->is_inline_definition) {
		PendingFunctionBody pending;
		pending.function = dtor;
		pending.node = fn;
		pending.body_pos = pos_;
		skip_balanced(OP_LBRACE, OP_RBRACE);
		enqueue_pending_member_body(class_scope, pending);
		return true; }
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
	if (body.children.empty() && !dtor->is_virtual) {
		dtor->is_noop_destructor = true;
		map<string, vector<Binding*> >::iterator found =
			class_scope->members.find(dtor_name);
		if (found != class_scope->members.end())
			for (size_t i = 0; i < found->second.size(); ++i)
				if (found->second[i]->kind == BindingKind::Function &&
				    pa11::same_type(found->second[i]->type, dtor->type))
					found->second[i]->is_noop_destructor = true; }
	add_child(fn, body);
	extra_lowir_nodes_.push_back(fn);
	return true; }
}  // namespace internal
}  // namespace pa12
