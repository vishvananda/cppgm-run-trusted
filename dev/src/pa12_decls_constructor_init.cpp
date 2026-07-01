#include "pa12_internal.h"
#include "pa12_templates_function_support.h"
using namespace std;
namespace pa12 {
namespace internal {

void stamp_template_member_function_symbol(Binding* binding);
bool hosted_library_namespace_scope(Scope* scope);

namespace {

bool append_anonymous_storage_member_initializers(
	Node& body,
	Binding* storage,
	const map<Binding*, Node>& explicit_member_initializers)
{
	if (storage == NULL ||
	    pa11::strip_cv(storage->type)->kind != pa11::TypeKind::Record ||
	    pa11::strip_cv(storage->type)->scope == NULL)
		return false;
	Scope* target = pa11::strip_cv(storage->type)->scope;
	bool emitted = false;
	for (size_t i = 0; i < target->binding_order.size(); ++i) {
		Binding* member = target->binding_order[i];
		if (member->kind != BindingKind::Variable)
			continue;
		for (map<Binding*, Node>::const_iterator it =
			     explicit_member_initializers.begin();
		     it != explicit_member_initializers.end();
		     ++it) {
			Binding* injected = it->first;
			if (injected != NULL &&
			    injected->aliased_binding == storage &&
			    injected->target_scope == target &&
			    injected->name == member->name) {
				add_child(body, it->second);
				emitted = true;
				break;
			}
		}
	}
	return emitted;
}

bool same_constructor_owner_template_family(TypePtr left, TypePtr right)
{
	TypePtr l = left.get() != NULL ? pa11::strip_cv(left) : TypePtr();
	TypePtr r = right.get() != NULL ? pa11::strip_cv(right) : TypePtr();
	if (l.get() == NULL || r.get() == NULL ||
	    l->kind != pa11::TypeKind::Record ||
	    r->kind != pa11::TypeKind::Record)
		return false;
	string l_primary = l->template_primary_name.empty()
		? l->name : l->template_primary_name;
	string r_primary = r->template_primary_name.empty()
		? r->name : r->template_primary_name;
	return l_primary == r_primary &&
	       l->is_template_specialization == r->is_template_specialization;
}

bool same_constructor_self_record_family(TypePtr candidate, TypePtr current)
{
	TypePtr c = candidate.get() != NULL
		? pa11::strip_cv(candidate) : TypePtr();
	TypePtr self = current.get() != NULL
		? pa11::strip_cv(current) : TypePtr();
	if (c.get() == NULL || self.get() == NULL ||
	    c->kind != pa11::TypeKind::Record ||
	    self->kind != pa11::TypeKind::Record)
		return false;
	if (c.get() == self.get())
		return true;
	if (c->scope == NULL || self->scope == NULL ||
	    c->scope->name != self->scope->name ||
	    c->scope->parent == NULL || self->scope->parent == NULL)
		return false;
	TypePtr c_owner = pa11::record_type_for_scope(c->scope->parent);
	TypePtr self_owner = pa11::record_type_for_scope(self->scope->parent);
	return same_constructor_owner_template_family(c_owner, self_owner);
}

	TypePtr rebind_constructor_self_parameter_type(TypePtr type, TypePtr current)
	{
		if (type.get() == NULL)
			return type;
		switch (type->kind)
		{
		case pa11::TypeKind::Cv:
			return pa11::make_cv(
				rebind_constructor_self_parameter_type(type->base, current),
				type->cv);
	case pa11::TypeKind::Pointer:
		return pa11::make_pointer(
			rebind_constructor_self_parameter_type(type->base, current));
	case pa11::TypeKind::LValueReference:
		return pa11::make_lvalue_reference(
			rebind_constructor_self_parameter_type(type->base, current));
	case pa11::TypeKind::RValueReference:
		return pa11::make_rvalue_reference(
			rebind_constructor_self_parameter_type(type->base, current));
	case pa11::TypeKind::Array:
	{
		TypePtr rebound = pa11::make_array(
			rebind_constructor_self_parameter_type(type->base, current),
			type->unknown_bound,
			type->bound);
		rebound->name = type->name;
		return rebound;
	}
	case pa11::TypeKind::Function:
	{
		vector<TypePtr> params;
		for (size_t i = 0; i < type->parameters.size(); ++i)
			params.push_back(
				rebind_constructor_self_parameter_type(type->parameters[i],
				                                       current));
		TypePtr rebound = pa11::make_function(
			rebind_constructor_self_parameter_type(type->base, current),
			params,
			type->variadic);
		rebound->cv = type->cv;
		rebound->ref_qualifier = type->ref_qualifier;
		return rebound;
	}
		case pa11::TypeKind::MemberPointer:
			return pa11::make_member_pointer(
				rebind_constructor_self_parameter_type(type->member_class,
				                                       current),
				rebind_constructor_self_parameter_type(type->base, current));
		default:
			if (same_constructor_self_record_family(type, current))
				return current;
			return type;
		}
	}

}  // namespace

Binding* Parser::add_constructor_this_parameter(
	Node& fn,
	Scope* function_scope,
	const string& function_name,
	TypePtr this_type)
{
	Binding* this_binding =
		pa11::add_binding(function_scope,
		                  BindingKind::Parameter,
		                  "this",
		                  this_type);
	Node this_node("parameter this " + pa11::describe_type(this_type));
	this_node.binding = this_binding;
	this_node.type = this_type;
	add_child(fn, this_node);
	(void)function_name;
	return this_binding;
}

map<string, vector<Binding*> > Parser::bind_constructor_body_parameters(
	Binding* function,
	const vector<ParameterInfo>& parameters,
	Scope* function_scope,
	Node& fn)
{
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
				continue;
			}
		}
		TypePtr parameter_type = parameters[i].type.get() != NULL
			? substitute_template_type(parameters[i].type) : TypePtr();
		TypePtr class_type =
			function != NULL && function->owner != NULL &&
			function->owner->kind == ScopeKind::Class
			? pa11::record_type_for_scope(function->owner) : TypePtr();
		if (class_type.get() != NULL)
			parameter_type =
				rebind_constructor_self_parameter_type(parameter_type,
				                                       class_type);
		if (parameter_type.get() == NULL &&
		    i + 1 < function->type->parameters.size())
			parameter_type = function->type->parameters[i + 1];
		if (class_type.get() != NULL)
			parameter_type =
				rebind_constructor_self_parameter_type(parameter_type,
				                                       class_type);
		if (parameter_type.get() == NULL) {
			if (!parameters[i].pack_expression_name.empty())
				parameter_packs[parameters[i].pack_expression_name];
			continue;
		}
		string pname = parameters[i].name;
		string node_name = pname;
		map<Binding*, vector<string> >::const_iterator saved_names =
			function_parameter_names_.find(function);
		bool force_saved_name =
			override_function_parameter_name_bindings_.count(function) != 0;
		bool saved_name_reused_later = false;
		bool later_parameter_has_name = false;
		for (size_t j = i + 1; j < parameters.size(); ++j)
			if (!parameters[j].name.empty())
				later_parameter_has_name = true;
		if (saved_names != function_parameter_names_.end() &&
		    i + 1 < saved_names->second.size())
			for (size_t j = i + 2; j < saved_names->second.size(); ++j)
				if (!saved_names->second[i + 1].empty() &&
				    saved_names->second[i + 1] == saved_names->second[j])
					saved_name_reused_later = true;
		if ((force_saved_name ||
		     (node_name.empty() && !saved_name_reused_later &&
		      !later_parameter_has_name)) &&
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
					.push_back(param);
		}
		Node param_node("parameter " + node_name + " " +
		                pa11::describe_type(parameter_type));
		param_node.binding = param;
		param_node.type = parameter_type;
		add_child(fn, param_node);
	}
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
		                pa11::describe_type(function->type->parameters[pi]));
		param_node.binding = param;
		param_node.type = function->type->parameters[pi];
		add_child(fn, param_node);
	}
	return parameter_packs;
}

void Parser::bind_constructor_signature_parameters(
	Node& fn,
	Scope* function_scope,
	const vector<ParameterInfo>& parameters,
	const vector<size_t>& signature_parameter_indices)
{
	for (size_t i = 0; i < signature_parameter_indices.size(); ++i) {
		const ParameterInfo& parameter =
			parameters[signature_parameter_indices[i]];
		string pname = parameter.name.empty()
			? "__param" + to_string(i + 1) : parameter.name;
		Binding* param =
			pa11::add_binding(function_scope,
			                  BindingKind::Parameter,
			                  pname,
			                  parameter.type);
		Node param_node("parameter " + pname + " " +
		                pa11::describe_type(parameter.type));
		param_node.binding = param;
		param_node.type = parameter.type;
		add_child(fn, param_node);
	}
}

TypePtr Parser::constructor_initializer_target(
	Scope* class_scope,
	TypePtr class_type,
	TypePtr direct_base,
	const ConstructorInitializerParse& clause,
	bool& target_is_base)
{
	target_is_base = false;
	if (clause.name == class_scope->name)
		return class_type;
	if (direct_base.get() != NULL &&
	    initializer_names_direct_base(
		    class_scope,
		    direct_base,
		    clause.name,
		    clause.have_template_arguments ? &clause.template_arguments : NULL)) {
		target_is_base = true;
		return direct_base;
	}
	if (clause.field != NULL)
		return clause.field->type;
	return TypePtr();
}

ConstructorInitializerParse Parser::parse_constructor_initializer_clause(
	Scope* class_scope,
	TypePtr class_type,
	TypePtr direct_base)
{
	ConstructorInitializerParse clause;
	clause.name = consume_identifier();
	if (at(OP_LT)) {
		parse_template_argument_list(clause.template_arguments);
		clause.have_template_arguments = true;
	}
	while (consume(OP_COLON2)) {
		consume(KW_TEMPLATE);
		clause.name = consume_identifier();
		clause.template_arguments.clear();
		clause.have_template_arguments = false;
		if (at(OP_LT)) {
			parse_template_argument_list(clause.template_arguments);
			clause.have_template_arguments = true;
		}
	}
	clause.field = pa11::lookup_qualified(class_scope,
	                                      clause.name,
	                                      pa11::LOOKUP_VARIABLE);
	if (at(OP_LBRACE)) {
		clause.init = parse_braced_init_list();
		clause.have_init = true;
	} else if (consume(OP_LPAREN)) {
		clause.have_paren_init = true;
		if (!at(OP_RPAREN)) {
			clause.parsed_args_begin = pos_;
			clause.parsed_args = parse_argument_list();
			clause.parsed_args_end = pos_;
			bool target_is_base = false;
			TypePtr target = constructor_initializer_target(
				class_scope, class_type, direct_base, clause, target_is_base);
			if (target.get() != NULL &&
			    pa11::strip_cv(target)->kind == pa11::TypeKind::Record) {
				if (!target_is_base) {
					try {
						clause.init = make_constructor_init_expr(
							target, clause.parsed_args, false);
						clause.have_init = true;
					} catch (const runtime_error& err) {
						if (string(err.what()) !=
						        "no matching constructor" ||
						    clause.parsed_args.size() != 1 ||
						    !pa11::same_type(
							    pa11::strip_cv(target),
							    pa11::strip_cv(
								    expression_object_type(
									    clause.parsed_args[0].type))))
							throw;
						clause.init = clause.parsed_args[0];
						clause.have_init = true;
					}
				}
			} else if (clause.parsed_args.empty()) {
				clause.init.valid = true;
				clause.init.category = ValueCategory::PRValue;
				clause.init.braced_init_list = true;
				clause.init.node = Node("braced-init-list");
				clause.have_init = true;
			} else if (clause.parsed_args.size() == 1) {
				clause.init = clause.parsed_args[0];
				clause.have_init = true;
			}
		} else {
			bool target_is_base = false;
			TypePtr target = constructor_initializer_target(
				class_scope, class_type, direct_base, clause, target_is_base);
			if (target.get() != NULL &&
			    pa11::strip_cv(target)->kind == pa11::TypeKind::Record) {
				if (!target_is_base)
					clause.init = make_constructor_init_expr(
						target, vector<Expr>(), false);
			} else {
				clause.init.valid = true;
				clause.init.category = ValueCategory::PRValue;
				clause.init.braced_init_list = true;
				clause.init.node = Node("braced-init-list");
			}
			clause.have_init = true;
		}
		expect(OP_RPAREN);
	}
	clause.pack_expansion = consume(OP_DOTS);
	return clause;
}

vector<TypePtr> Parser::constructor_initializer_matching_bases(
	Scope* class_scope,
	const vector<TypePtr>& direct_bases,
	const ConstructorInitializerParse& clause)
{
	vector<TypePtr> matching_bases;
	for (size_t b = 0; b < direct_bases.size(); ++b) {
		TypePtr base = direct_bases[b].get() != NULL
			? pa11::strip_cv(direct_bases[b]) : TypePtr();
		if (base.get() != NULL &&
		    initializer_names_direct_base(
			    class_scope,
			    base,
			    clause.name,
			    clause.have_template_arguments
			    ? &clause.template_arguments : NULL))
			matching_bases.push_back(base);
	}
	return matching_bases;
}

vector<Expr> Parser::expand_constructor_initializer_pack(
	const ConstructorInitializerParse& clause,
	size_t match_count)
{
	vector<Expr> expanded_inits;
	if (!clause.pack_expansion || clause.parsed_args.size() != 1)
		return expanded_inits;
	if (clause.parsed_args[0].pack_expansion &&
	    !clause.parsed_args[0].pack.empty())
		expanded_inits = clause.parsed_args[0].pack;
	else {
		try {
			try_expand_expression_pack_pattern(clause.parsed_args_begin,
			                                   clause.parsed_args_end,
			                                   expanded_inits);
		} catch (const runtime_error&) {
			expanded_inits.clear();
		}
	}
	if (!expanded_inits.empty() && expanded_inits.size() != match_count)
		throw runtime_error("pack expansion size mismatch");
	return expanded_inits;
}

void Parser::append_constructor_base_initializer_actions(
	const ConstructorInitializerParse& clause,
	const vector<TypePtr>& matching_bases,
	const vector<Expr>& expanded_inits,
	vector<Node>& explicit_base_actions)
{
	for (size_t b = 0; b < matching_bases.size(); ++b) {
		if (clause.have_paren_init) {
			vector<Expr> base_args = clause.parsed_args;
			if (clause.pack_expansion) {
				if (expanded_inits.size() != matching_bases.size())
					throw runtime_error("pack expansion size mismatch");
				base_args.clear();
				base_args.push_back(expanded_inits[b]);
			}
			Expr base_init =
				make_constructor_init_expr(matching_bases[b],
				                           base_args,
				                           false);
			explicit_base_actions.push_back(
				make_base_init_action(matching_bases[b], &base_init.node));
		} else {
			explicit_base_actions.push_back(
				make_base_init_action(matching_bases[b],
				                      clause.have_init
				                      ? &clause.init.node : NULL));
		}
	}
}

void Parser::apply_constructor_initializer_clause(
	Scope* class_scope,
	TypePtr class_type,
	Binding* this_binding,
	const vector<TypePtr>& direct_bases,
	const ConstructorInitializerParse& clause,
	Node& body,
	map<Binding*, Node>& explicit_member_initializers,
	vector<Node>& explicit_base_actions,
	bool& delegating)
{
	vector<TypePtr> matching_bases =
		constructor_initializer_matching_bases(class_scope, direct_bases, clause);
	if (!matching_bases.empty()) {
		vector<Expr> expanded_inits =
			expand_constructor_initializer_pack(clause, matching_bases.size());
		append_constructor_base_initializer_actions(
			clause, matching_bases, expanded_inits, explicit_base_actions);
	} else if (clause.name == class_scope->name && clause.have_init) {
		Node action("delegating-init-action " + clause.name);
		action.type = class_type;
		action.direct_call = clause.init.node.direct_call;
		add_child(action, clause.init.node);
		add_child(body, action);
		delegating = true;
	} else if (clause.field != NULL && clause.have_init) {
		explicit_member_initializers[clause.field] =
			make_member_init_action(clause.field,
			                        &clause.init.node,
			                        this_binding);
	} else if (clause.have_init) {
		Node action("member-init-action " + clause.name);
		action.token_text = clause.name;
		add_child(action, clause.init.node);
		add_child(body, action);
	}
}

bool Parser::parse_constructor_initializer_list(
	Scope* class_scope,
	TypePtr class_type,
	Binding* this_binding,
	Node& body,
	map<Binding*, Node>& explicit_member_initializers,
	vector<Node>& explicit_base_actions,
	const vector<TypePtr>& direct_bases)
{
	if (!consume(OP_COLON))
		return false;
	bool delegating = false;
	TypePtr direct_base = !direct_bases.empty() && direct_bases[0].get() != NULL
		? pa11::strip_cv(direct_bases[0]) : TypePtr();
	for (;;) {
		ConstructorInitializerParse clause =
			parse_constructor_initializer_clause(class_scope,
			                                     class_type,
			                                     direct_base);
		apply_constructor_initializer_clause(class_scope,
		                                     class_type,
		                                     this_binding,
		                                     direct_bases,
		                                     clause,
		                                     body,
		                                     explicit_member_initializers,
		                                     explicit_base_actions,
		                                     delegating);
		if (!consume(OP_COMMA))
			break;
	}
	return delegating;
}

void Parser::append_constructor_member_init_actions(
	TypePtr class_type,
	Binding* this_binding,
	const map<Binding*, Node>& explicit_member_initializers,
	Node& body)
{
	vector<Binding*> fields;
	try {
		pa11::layout_record_type(class_type);
		fields = class_type->fields;
	} catch (const runtime_error& err) {
		if ((string(err.what()) != "incomplete class type" &&
		     string(err.what()) != "incomplete object type") ||
		    active_class_instantiations_.empty())
			throw;
		fields = declared_instance_fields(class_type);
	}
	for (size_t i = 0; i < fields.size(); ++i) {
		Binding* field = fields[i];
		map<Binding*, Node>::const_iterator explicit_init =
			explicit_member_initializers.find(field);
		if (explicit_init != explicit_member_initializers.end()) {
			add_child(body, explicit_init->second);
			continue;
		}
		if (append_anonymous_storage_member_initializers(
			    body, field, explicit_member_initializers))
			continue;
		map<Binding*, Node>::const_iterator init =
			default_member_initializers_.find(field);
		if (init != default_member_initializers_.end())
			add_child(body,
			          make_member_init_action(field,
			                                  &init->second,
			                                  this_binding));
		else if (pa11::strip_cv(field->type)->kind == pa11::TypeKind::Record) {
			try {
				if (ensure_default_constructor(field->type) != NULL)
					add_child(body,
					          make_member_init_action(field,
					                                  NULL,
					                                  this_binding));
			} catch (const runtime_error& err) {
				if (string(err.what()) !=
				    "member has no default constructor")
					throw;
			}
		}
	}
}

void Parser::append_constructor_compound_body(
	Node& body,
	bool function_try_block)
{
	Node parsed_body = parse_compound_statement();
	for (size_t i = 0; i < parsed_body.children.size(); ++i)
		add_child(body, parsed_body.children[i]);
	if (!function_try_block)
		return;
	Node try_node("try-statement");
	Node try_block("try-block");
	add_child(try_block, body);
	add_child(try_node, try_block);
	do {
		expect_catch_keyword();
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
			catch_node.line += " " + pa11::describe_type(catch_type);
		}
		expect(OP_RPAREN);
		expect(OP_LBRACE);
		Node catch_body("compound-statement");
		Scope* catch_scope =
			pa11::create_child_scope(current_scope(), ScopeKind::Block, "");
		scopes_.push_back(catch_scope);
		if (!catch_name.empty()) {
			Binding* catch_binding =
				add_value(catch_scope,
				          BindingKind::Variable,
				          catch_name,
				          catch_node.type);
			catch_node.binding = catch_binding;
		}
		while (!at(OP_RBRACE)) {
			Node item = parse_block_item();
			if (!item.line.empty())
				add_child(catch_body, item);
		}
		scopes_.pop_back();
		expect(OP_RBRACE);
		add_child(catch_node, catch_body);
		add_child(try_node, catch_node);
	} while (at_catch_keyword());
	Node wrapped("compound-statement");
	add_child(wrapped, try_node);
	body = wrapped;
}

bool Parser::parse_qualified_constructor_header(
	size_t save,
	Scope*& class_scope,
	TypePtr& class_type,
	vector<ParameterInfo>& parameters,
	bool& variadic,
	Suffix& suffix,
	bool& defaulted,
	vector<size_t>& signature_parameter_indices,
	TypePtr& fn_type)
{
	QualifiedName name;
	try {
		name = parse_id_expression_name();
	} catch (const exception&) {
		pos_ = save;
		return false;
	}
	if (name.qualifier == NULL ||
	    name.qualifier->kind != ScopeKind::Class ||
	    !constructor_name_matches_scope(name.qualifier, name.name) ||
	    !at(OP_LPAREN)) {
		pos_ = save;
		return false;
	}
	class_scope = name.qualifier;
	class_type = pa11::record_type_for_scope(class_scope);
	if (class_type.get() == NULL) {
		pos_ = save;
		return false;
	}
	expect(OP_LPAREN);
	scopes_.push_back(class_scope);
	parse_parameter_clause(parameters, variadic);
	scopes_.pop_back();
	expect(OP_RPAREN);
	parse_function_suffix_tail(suffix);
	if (consume(OP_ASS)) {
		if (!consume(KW_DEFAULT))
			throw runtime_error("unsupported constructor definition");
		expect(OP_SEMICOLON);
		defaulted = true;
	}
	if (!defaulted && !at(OP_LBRACE) && !at(OP_COLON) && !at_try_keyword()) {
		pos_ = save;
		return false;
	}
	vector<TypePtr> fn_params;
	fn_params.push_back(pa11::make_pointer(class_type));
	for (size_t i = 0; i < parameters.size(); ++i) {
		if (parameters[i].type.get() == NULL)
			continue;
		signature_parameter_indices.push_back(i);
		fn_params.push_back(parameters[i].type);
	}
	fn_type = pa11::make_function(pa11::make_fundamental(FT_VOID),
	                              fn_params,
	                              variadic);
	fn_type = substitute_template_type(fn_type);
	for (size_t i = 0;
	     i < signature_parameter_indices.size() &&
	     i + 1 < fn_type->parameters.size();
	     ++i)
		parameters[signature_parameter_indices[i]].type =
			fn_type->parameters[i + 1];
	return true;
}

Binding* Parser::prepare_qualified_constructor_binding(
	Scope* class_scope,
	TypePtr class_type,
	vector<ParameterInfo>& parameters,
	const vector<size_t>& signature_parameter_indices,
	TypePtr fn_type,
	const Suffix& suffix,
	bool defaulted,
	bool inline_spec,
	bool constexpr_spec,
	bool& qualified_inline_object_root)
{
	Binding* existing_ctor = NULL;
	map<string, vector<Binding*> >::iterator existing_it =
		class_scope->members.find(class_scope->name);
	if (existing_it != class_scope->members.end())
		for (size_t i = 0; i < existing_it->second.size(); ++i) {
			Binding* candidate = existing_it->second[i];
			if (candidate->kind == BindingKind::Function &&
			    pa11::same_type(candidate->type, fn_type)) {
				existing_ctor = candidate;
				break;
			}
		}
		bool merged_noexcept =
			(existing_ctor != NULL && existing_ctor->unwind_no) ||
			suffix.noexcept_decl;
		bool merged_dynamic_exception_spec =
			(existing_ctor != NULL &&
			 existing_ctor->dynamic_exception_spec) ||
			suffix.dynamic_exception_spec;
		vector<TypePtr> merged_dynamic_exception_types =
			suffix.dynamic_exception_types;
		if (merged_dynamic_exception_types.empty() &&
		    existing_ctor != NULL)
			merged_dynamic_exception_types =
				existing_ctor->dynamic_exception_types;
		bool hosted_mismatch_allowed =
			hosted_compatibility_ &&
			hosted_library_namespace_scope(class_scope);
		if (existing_ctor != NULL &&
		    existing_ctor->unwind_no != suffix.noexcept_decl &&
		    !hosted_mismatch_allowed)
			throw runtime_error("function exception specification mismatch");
	bool reused_implicit_default_ctor =
		existing_ctor != NULL &&
		existing_ctor->is_generated_default_constructor &&
		!existing_ctor->is_defaulted;
	Binding* ctor = existing_ctor != NULL
		? existing_ctor
		: add_function_binding(class_scope, class_scope->name, fn_type, false);
	discard_implicit_default_constructor(class_type, ctor);
	if (reused_implicit_default_ctor) {
		ctor->is_generated_default_constructor = false;
		ctor->is_noop_constructor = false;
	}
	for (size_t i = 0; i < signature_parameter_indices.size(); ++i)
		if (parameters[signature_parameter_indices[i]].has_default)
			ctor->has_default_arguments = true;
		ctor->unwind_no = merged_noexcept;
		ctor->dynamic_exception_spec = merged_dynamic_exception_spec;
		ctor->dynamic_exception_types = merged_dynamic_exception_types;
	ctor->is_constexpr = ctor->is_constexpr || constexpr_spec;
	ctor->is_inline_definition =
		ctor->is_inline_definition || inline_spec || constexpr_spec;
	TypePtr bare_class_type = pa11::strip_cv(class_type);
	map<const void*, TemplateDeclaration*>::const_iterator class_template =
		record_template_declarations_.find(bare_class_type.get());
	bool explicit_full_class_specialization =
		class_template != record_template_declarations_.end() &&
		class_template->second != NULL &&
		class_template->second->class_specialization &&
		class_template->second->parameters.empty();
	if (explicit_full_class_specialization)
	{
		ctor->is_declared_inline = inline_spec || constexpr_spec;
		ctor->is_inline_definition = inline_spec || constexpr_spec;
		ctor->is_explicit_specialization_member = true;
	}
	qualified_inline_object_root =
		ctor->is_inline_definition &&
		bare_class_type->is_template_specialization &&
		!active_class_instantiation_dependent();
		ctor->unwind_no = suffix.noexcept_decl;
		ctor->dynamic_exception_spec = suffix.dynamic_exception_spec;
		ctor->dynamic_exception_types = suffix.dynamic_exception_types;
	if (!suffix.abi_tags.empty())
		ctor->abi_tags = suffix.abi_tags;
		if (defaulted) {
			ctor->is_defaulted = true;
			ctor->is_explicit_defaulted_definition = true;
			ctor->is_inline_definition = inline_spec || constexpr_spec;
			ctor->is_generated_default_constructor = false;
			ctor->is_generated_copy_move_constructor = false;
			ctor->is_noop_constructor = signature_parameter_indices.empty();
			ctor->is_object_root = !ctor->is_inline_definition;
			ctor->unwind_no = true;
		}
	if (!active_class_instantiation_dependent())
		stamp_template_member_function_symbol(ctor);
	return ctor;
}

bool Parser::defer_qualified_constructor_definition(
	Scope* class_scope,
	TypePtr class_type,
	Binding* ctor,
	const vector<ParameterInfo>& parameters,
	const Node& fn,
	bool emit_node,
	bool qualified_inline_object_root,
	Node& out)
{
	if ((force_new_function_binding_ || qualified_inline_object_root) &&
	    active_class_instantiations_.empty()) {
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
	consume_try_keyword();
	if (consume(OP_COLON)) {
		for (;;) {
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
	while (at_catch_keyword()) {
		consume_catch_keyword();
		skip_balanced(OP_LPAREN, OP_RPAREN);
		skip_balanced(OP_LBRACE, OP_RBRACE);
	}
	enqueue_pending_member_body(class_scope, pending);
	if (force_new_function_binding_ && defer_function_template_bodies_) {
		if (emit_node)
			add_child(out, fn);
		else
			extra_lowir_nodes_.push_back(fn);
	}
	return true;
}

void Parser::parse_immediate_qualified_constructor_definition(
	Scope* class_scope,
	TypePtr class_type,
	Binding* ctor,
	const vector<ParameterInfo>& parameters,
	const vector<size_t>& signature_parameter_indices,
	TypePtr fn_type,
	bool defaulted,
	Node& fn)
{
	Scope* function_scope =
		pa11::create_child_scope(class_scope, ScopeKind::Function, ctor->name);
	Binding* this_binding =
		add_constructor_this_parameter(fn, function_scope, ctor->name,
		                               fn_type->parameters[0]);
	bind_constructor_signature_parameters(fn,
	                                      function_scope,
	                                      parameters,
	                                      signature_parameter_indices);
	if (!defaulted) {
		scopes_.push_back(function_scope);
		function_returns_.push_back(pa11::make_fundamental(FT_VOID));
		active_functions_.push_back(ctor);
	}
	Node body("compound-statement");
	if (!defaulted) {
		try {
			bool function_try_block = consume_try_keyword();
			map<Binding*, Node> explicit_member_initializers;
			vector<Node> explicit_base_actions;
			bool delegating = false;
			vector<TypePtr> direct_bases = pa11::record_direct_bases(class_type);
			delegating = parse_constructor_initializer_list(
				class_scope, class_type, this_binding, body,
				explicit_member_initializers, explicit_base_actions, direct_bases);
			if (!delegating)
			{
				append_constructor_base_init_actions(class_type,
				                                     direct_bases,
				                                     explicit_base_actions,
				                                     body);
				append_constructor_member_init_actions(class_type,
				                                       this_binding,
				                                       explicit_member_initializers,
				                                       body);
			}
			append_constructor_compound_body(body, function_try_block);
		} catch (...) {
			active_functions_.pop_back();
			function_returns_.pop_back();
			scopes_.pop_back();
			throw;
		}
		active_functions_.pop_back();
		function_returns_.pop_back();
		scopes_.pop_back();
	} else {
		vector<Node> explicit_base_actions;
		vector<TypePtr> direct_bases = pa11::record_direct_bases(class_type);
		append_constructor_base_init_actions(class_type,
		                                     direct_bases,
		                                     explicit_base_actions,
		                                     body);
		map<Binding*, Node> explicit_member_initializers;
		append_constructor_member_init_actions(class_type,
		                                       this_binding,
		                                       explicit_member_initializers,
		                                       body);
	}
	ctor->is_noop_constructor = body.children.empty();
	add_child(fn, body);
	remember_function_body(ctor, fn);
}

}  // namespace internal
}  // namespace pa12
