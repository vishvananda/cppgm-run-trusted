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
		add_constructor_this_parameter(fn,
		                                function_scope,
		                                function->name,
		                                this_type);
	map<string, vector<Binding*> > parameter_packs =
		bind_constructor_body_parameters(function,
		                                 parameters,
		                                 function_scope,
		                                 fn);
	scopes_.push_back(function_scope);
	function_returns_.push_back(pa11::make_fundamental(FT_VOID));
	active_functions_.push_back(function);
	function_parameter_pack_substitutions_.push_back(parameter_packs);
	Node body("compound-statement");
	try {
		bool function_try_block = consume_try_keyword();
		map<Binding*, Node> explicit_member_initializers;
		vector<Node> explicit_base_actions;
		vector<TypePtr> direct_bases = pa11::record_direct_bases(class_type);
		bool delegating =
			parse_constructor_initializer_list(class_scope,
			                                   class_type,
			                                   this_binding,
			                                   body,
			                                   explicit_member_initializers,
			                                   explicit_base_actions,
			                                   direct_bases);
		if (delegating) { }
		else
			append_constructor_base_init_actions(class_type,
			                                     direct_bases,
			                                     explicit_base_actions,
			                                     body);
		append_constructor_member_init_actions(class_type,
		                                       this_binding,
		                                       explicit_member_initializers,
		                                       body);
		append_constructor_compound_body(body, function_try_block);
	} catch (...) {
		function_parameter_pack_substitutions_.pop_back();
		active_functions_.pop_back();
		function_returns_.pop_back();
		scopes_.pop_back();
		throw;
	}
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
	Scope* class_scope = NULL;
	TypePtr class_type;
	vector<ParameterInfo> parameters;
	bool variadic = false;
	Suffix suffix(SuffixKind::Function);
	bool defaulted = false;
	vector<size_t> signature_parameter_indices;
	TypePtr fn_type;
	if (!parse_qualified_constructor_header(save,
	                                        class_scope,
	                                        class_type,
	                                        parameters,
	                                        variadic,
	                                        suffix,
	                                        defaulted,
	                                        signature_parameter_indices,
	                                        fn_type))
		return false;
	bool qualified_inline_object_root = false;
	Binding* ctor =
		prepare_qualified_constructor_binding(class_scope,
		                                      class_type,
		                                      parameters,
		                                      signature_parameter_indices,
		                                      fn_type,
		                                      suffix,
		                                      defaulted,
		                                      inline_spec,
		                                      constexpr_spec,
		                                      qualified_inline_object_root);
		Node fn("function-definition " + qualified_decl_name(ctor) + " " +
		        pa11::describe_type(fn_type));
		fn.binding = ctor;
		if (defaulted)
			fn.token_text = "defaulted-definition";
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
	if (!defaulted && ctor->is_inline_definition &&
	    defer_qualified_constructor_definition(class_scope,
	                                           class_type,
	                                           ctor,
	                                           parameters,
	                                           fn,
	                                           emit_node,
	                                           qualified_inline_object_root,
	                                           out))
		return true;
	parse_immediate_qualified_constructor_definition(class_scope,
	                                                class_type,
	                                                ctor,
	                                                parameters,
	                                                signature_parameter_indices,
	                                                fn_type,
	                                                defaulted,
	                                                fn);
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
		function->dynamic_exception_spec = suffix.dynamic_exception_spec;
		function->dynamic_exception_types = suffix.dynamic_exception_types;
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
		function->dynamic_exception_spec = suffix.dynamic_exception_spec;
		function->dynamic_exception_types = suffix.dynamic_exception_types;
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
}  // namespace internal
}  // namespace pa12
