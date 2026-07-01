#include "pa12_internal.h"
#include "pa12_templates_function_support.h"
using namespace std;
namespace pa12 {
namespace internal {
namespace {

bool token_is_simple(const vector<Token>& tokens, size_t pos, ETokenType type)
{
	return pos < tokens.size() &&
	       tokens[pos].kind == posttoken::TokenKind::Simple &&
	       tokens[pos].type == type;
}

bool deferred_compound_body_is_empty(const vector<Token>& tokens, size_t pos)
{
	return token_is_simple(tokens, pos, OP_LBRACE) &&
	       token_is_simple(tokens, pos + 1, OP_RBRACE);
}

void mark_noop_destructor(Binding* dtor,
                          Scope* class_scope,
                          const string& dtor_name)
{
	if (dtor == NULL || dtor->is_virtual)
		return;
	dtor->is_noop_destructor = true;
	if (class_scope == NULL)
		return;
	map<string, vector<Binding*> >::iterator found =
		class_scope->members.find(dtor_name);
	if (found == class_scope->members.end())
		return;
	for (size_t i = 0; i < found->second.size(); ++i)
		if (found->second[i]->kind == BindingKind::Function &&
		    pa11::same_type(found->second[i]->type, dtor->type))
			found->second[i]->is_noop_destructor = true;
}

}  // namespace

void stamp_template_member_function_symbol(Binding* binding);

bool Parser::parse_qualified_destructor_definition(Node& out, bool emit_node)
{
	if (current_scope()->kind == ScopeKind::Class ||
	    !(at(OP_COLON2) || at_identifier()))
	{
		return false;
	}
	size_t save = pos_;
	Scope* class_scope = NULL;
	try {
		class_scope = parse_nested_name_specifier(NULL);
	} catch (const exception&) {
		pos_ = save;
		return false; }
	if (class_scope == NULL ||
	    class_scope->kind != ScopeKind::Class ||
	    !consume(OP_COMPL) || !at_identifier()) {
		pos_ = save;
		return false; }
	string dtor_type_name = consume_identifier();
	if (!at(OP_LPAREN)) {
		pos_ = save;
		return false; }
	if (class_scope == NULL ||
	    class_scope->kind != ScopeKind::Class ||
	    !constructor_name_matches_scope(class_scope, dtor_type_name)) {
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
	discard_implicit_default_destructor(class_type);
	Binding* dtor = NULL;
	map<string, vector<Binding*> >::iterator existing_dtors =
		class_scope->members.find(dtor_name);
	if (existing_dtors != class_scope->members.end())
		for (size_t i = 0; i < existing_dtors->second.size(); ++i)
			if (existing_dtors->second[i]->kind == BindingKind::Function &&
			    pa11::same_type(existing_dtors->second[i]->type, fn_type))
			{
				dtor = existing_dtors->second[i];
				break;
			}
	if (dtor == NULL)
		dtor = add_value(class_scope, BindingKind::Function, dtor_name, fn_type);
	dtor->unwind_no = suffix.noexcept_decl;
	dtor->dynamic_exception_spec = suffix.dynamic_exception_spec;
	dtor->dynamic_exception_types = suffix.dynamic_exception_types;
	if (defaulted)
	{
		dtor->is_defaulted = true;
		dtor->is_explicit_defaulted_definition = true;
		dtor->is_inline_definition = false;
		dtor->is_generated_default_destructor = false;
		dtor->is_noop_destructor = true;
		dtor->is_object_root = true;
		dtor->unwind_no = true;
	}
	if (!suffix.abi_tags.empty())
		dtor->abi_tags = suffix.abi_tags;
	function_parameter_names_[dtor] = vector<string>(1, "this");
	if (!active_class_instantiation_dependent())
		stamp_template_member_function_symbol(dtor);
	Node fn("function-definition " + qualified_decl_name(dtor) + " " +
	        pa11::describe_type(fn_type));
	fn.binding = dtor;
	fn.type = fn_type;
	if (defaulted)
		fn.token_text = "defaulted-definition";
	if (defaulted) {
		mark_noop_destructor(dtor, class_scope, dtor_name);
		Scope* function_scope =
			pa11::create_child_scope(class_scope,
			                         ScopeKind::Function,
			                         dtor->name);
		Binding* this_binding =
			pa11::add_binding(function_scope,
			                  BindingKind::Parameter,
			                  "this",
			                  this_type);
		Node this_node("parameter this " + pa11::describe_type(this_type));
		this_node.binding = this_binding;
		this_node.type = this_type;
		add_child(fn, this_node);
		add_child(fn, Node("compound-statement"));
		if (emit_node)
			add_child(out, fn);
		else
			extra_lowir_nodes_.push_back(fn);
		return true; }
	if (dtor->is_inline_definition &&
	    !(force_new_function_binding_ && active_class_instantiations_.empty())) {
		PendingFunctionBody pending;
		pending.function = dtor;
		pending.node = fn;
		pending.body_pos = pos_;
		if (deferred_compound_body_is_empty(tokens_, pos_))
			mark_noop_destructor(dtor, class_scope, dtor_name);
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
		try {
			body = parse_compound_statement();
		} catch (...) {
			active_functions_.pop_back();
			function_returns_.pop_back();
			scopes_.pop_back();
			throw;
		}
		active_functions_.pop_back();
		function_returns_.pop_back();
		scopes_.pop_back(); }
	if (body.children.empty())
		mark_noop_destructor(dtor, class_scope, dtor_name);
	add_child(fn, body);
	if (emit_node)
		add_child(out, fn);
	else
		extra_lowir_nodes_.push_back(fn);
	return true;
}

bool Parser::parse_destructor_like_member()
{
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
	discard_implicit_default_destructor(class_type);
	Binding* dtor = add_value(class_scope,
	                          BindingKind::Function,
	                          dtor_name,
	                          fn_type);
	function_parameter_names_[dtor] = vector<string>(1, "this");
	dtor->is_inline_definition = at(OP_LBRACE);
	dtor->unwind_no = suffix.noexcept_decl;
	dtor->dynamic_exception_spec = suffix.dynamic_exception_spec;
	dtor->dynamic_exception_types = suffix.dynamic_exception_types;
	if (!suffix.abi_tags.empty())
		dtor->abi_tags = suffix.abi_tags;
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
		if (consume(KW_DEFAULT)) {
			dtor->is_defaulted = true;
			dtor->is_inline_definition = true;
			dtor->is_noop_destructor = true;
			mark_noop_destructor(dtor, class_scope, dtor_name);
			expect(OP_SEMICOLON);
			Node fn("function-definition " + qualified_decl_name(dtor) + " " +
			        pa11::describe_type(fn_type));
			fn.binding = dtor;
			fn.type = fn_type;
			add_child(fn, Node("compound-statement"));
			extra_lowir_nodes_.push_back(fn);
			return true; }
		if (consume(KW_DELETE)) {
			deleted_functions_.insert(dtor);
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
		if (deferred_compound_body_is_empty(tokens_, pos_))
			mark_noop_destructor(dtor, class_scope, dtor_name);
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
	Node body;
	try {
		body = parse_compound_statement();
	} catch (...) {
		active_functions_.pop_back();
		function_returns_.pop_back();
		scopes_.pop_back();
		throw;
	}
	active_functions_.pop_back();
	function_returns_.pop_back();
	scopes_.pop_back();
	if (body.children.empty())
		mark_noop_destructor(dtor, class_scope, dtor_name);
	add_child(fn, body);
	extra_lowir_nodes_.push_back(fn);
	return true;
}

}  // namespace internal
}  // namespace pa12
