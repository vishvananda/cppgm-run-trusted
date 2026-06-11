#include "pa14_lowir_internal.h"

namespace pa14 {
namespace internal {
namespace {

void collect_direct_calls(const Node& node, set<const Binding*>& out)
{
	if (node.direct_call != NULL)
		out.insert(node.direct_call);
	for (size_t i = 0; i < node.children.size(); ++i)
		collect_direct_calls(node.children[i], out);
}

void collect_base_constructor_calls(const Node& node, set<const Binding*>& out)
{
	if (node.direct_call != NULL && starts_with(node.line, "base-init-action"))
		out.insert(node.direct_call);
	for (size_t i = 0; i < node.children.size(); ++i)
		collect_base_constructor_calls(node.children[i], out);
}

bool contains_call_expression(const Node& node)
{
	if (starts_with(node.line, "call-expression") ||
	    starts_with(node.line, "constructor-action") ||
	    node.direct_call != NULL)
		return true;
	for (size_t i = 0; i < node.children.size(); ++i)
		if (contains_call_expression(node.children[i]))
			return true;
	return false;
}

bool generated_copy_move_constructor_node(const Node& node)
{
	if (node.binding == NULL ||
	    (!node.binding->is_generated_copy_move_constructor &&
	     node.token_text != "copy-move-helper"))
		return false;
	if (node.token_text == "copy-move-helper" &&
	    !node.children.empty() &&
	    starts_with(node.children.back().line, "compound-statement") &&
	    node.children.back().children.empty())
		return false;
	bool template_context = false;
	for (Scope* scope = node.binding->owner; scope != NULL; scope = scope->parent)
	{
		if (scope->kind != ScopeKind::Class)
			continue;
		TypePtr record = pa11::record_type_for_scope(scope);
		record = record.get() != NULL ? pa11::strip_cv(record) : TypePtr();
		if (record_is_template_specialization(record))
		{
			template_context = true;
			break;
		}
	}
	if (!template_context)
		return false;
	if (node.binding->is_defaulted && !contains_call_expression(node))
	{
		TypePtr record = pa11::record_type_for_scope(node.binding->owner);
		record = record.get() != NULL ? pa11::strip_cv(record) : TypePtr();
		if (record.get() != NULL &&
		    !defaulted_copy_move_constructor_needs_helper(
			    node.binding,
			    record))
			return false;
	}
	if (node.binding->is_defaulted &&
	    node.binding->owner != NULL &&
	    node.binding->owner->kind == ScopeKind::Class)
	{
		TypePtr record = pa11::record_type_for_scope(node.binding->owner);
		record = record.get() != NULL ? pa11::strip_cv(record) : TypePtr();
		if (record.get() != NULL)
		{
			pa11::layout_record_type(record);
			for (size_t i = 0; i < record->fields.size(); ++i)
				if (pa11::is_reference_type(record->fields[i]->type))
					return false;
		}
	}
	return true;
}

bool type_mentions_template_specialization(TypePtr type)
{
	type = type.get() != NULL ? pa11::strip_cv(type) : TypePtr();
	if (type.get() == NULL)
		return false;
	if (record_is_template_specialization(type))
		return true;
	if (type->kind == TypeKind::Pointer ||
	    type->kind == TypeKind::LValueReference ||
	    type->kind == TypeKind::RValueReference ||
	    type->kind == TypeKind::Array ||
	    type->kind == TypeKind::MemberPointer)
		return type_mentions_template_specialization(type->base) ||
		       type_mentions_template_specialization(type->member_class);
	if (type->kind == TypeKind::Function)
	{
		if (type_mentions_template_specialization(type->base))
			return true;
		for (size_t i = 0; i < type->parameters.size(); ++i)
			if (type_mentions_template_specialization(type->parameters[i]))
				return true;
	}
	return false;
}

bool binding_mentions_template_specialization(const Binding* binding)
{
	return binding != NULL &&
	       type_mentions_template_specialization(binding->type);
}

bool same_binding_or_alias(const Binding* left, const Binding* right)
{
	return left == right ||
	       (left != NULL && left->aliased_binding == right) ||
	       (right != NULL && right->aliased_binding == left);
}

bool early_hidden_friend_definition(const Node& node,
                                    const set<const Binding*>& direct_calls)
{
	if (node.binding == NULL || !node.binding->is_hidden_friend)
		return false;
	for (set<const Binding*>::const_iterator it = direct_calls.begin();
	     it != direct_calls.end(); ++it)
		if (same_binding_or_alias(node.binding, *it))
			return true;
	if (node.binding->is_constexpr)
		return false;
	return !contains_call_expression(node) &&
	       !binding_mentions_template_specialization(node.binding);
}

bool extra_variable_has_deferred_storage(const Node& node)
{
	if (node.binding == NULL)
		return false;
	pa11::TypePtr node_type =
		node.type.get() != NULL ? node.type : node.binding->type;
	pa11::TypePtr object = strip_for_value(node_type);
	pa11::TypePtr bare = pa11::strip_cv(object);
	bool braced_storage = !node.children.empty() &&
	                      starts_with(node.children[0].line, "braced-init-list");
	if (node.binding->is_dependent_template_artifact &&
	    (bare->kind == pa11::TypeKind::Array ||
	     bare->kind == pa11::TypeKind::Record ||
	     braced_storage))
		return false;
	return bare->kind == pa11::TypeKind::Array ||
	       bare->kind == pa11::TypeKind::Record ||
	       braced_storage;
}

void collect_extra_variable(ProgramLowerer& program, const Node& node)
{
	if (!starts_with(node.line, "variable ") || node.binding == NULL)
		return;
	if (extra_variable_has_deferred_storage(node))
		program.deferred_global_definitions[node.binding] = node;
	else
		program.collect_node(node);
}

bool referenced_extra_function(const Node& node,
                               const set<const Binding*>& direct_calls)
{
	if (!starts_with(node.line, "function-definition ") ||
	    node.binding == NULL ||
	    node.binding->is_inline_definition)
		return false;
	if (node.binding->is_object_root)
		return true;
	for (set<const Binding*>::const_iterator it = direct_calls.begin();
	     it != direct_calls.end(); ++it)
		if (same_binding_or_alias(node.binding, *it))
			return true;
	return false;
}

void collect_referenced_extra_functions(ProgramLowerer& program,
                                        const vector<Node>& extra,
                                        const set<const Binding*>& direct_calls)
{
	set<string> collected;
	for (size_t i = 0; i < extra.size(); ++i)
	{
		if (!referenced_extra_function(extra[i], direct_calls))
			continue;
		string name = program.symbol_for(extra[i].binding);
		if (program.defined_functions.find(name) !=
		        program.defined_functions.end() ||
		    !collected.insert(name).second)
			continue;
		program.collect_node(extra[i]);
	}
}

void demand_object_roots(ProgramLowerer& program, const vector<Node>& extra)
{
	for (size_t i = 0; i < extra.size(); ++i)
	{
		if (extra[i].binding == NULL ||
		    (!extra[i].binding->is_object_root &&
		     extra[i].token_text != "inline-object-root"))
			continue;
		program.demand_inline_function(extra[i].binding);
		program.emit_pending_inline_definitions();
	}
}

void demand_early_hidden_friends(ProgramLowerer& program,
                                 const vector<Node>& extra,
                                 const set<const Binding*>& direct_calls)
{
	for (size_t i = 0; i < extra.size(); ++i)
	{
		if (!early_hidden_friend_definition(extra[i], direct_calls))
			continue;
		program.demand_inline_function(extra[i].binding);
		program.emit_pending_inline_definitions();
	}
}

void demand_generated_copy_move_dependencies(ProgramLowerer& program,
                                             const vector<Node>& extra)
{
	for (size_t i = 0; i < extra.size(); ++i)
	{
		if (!generated_copy_move_constructor_node(extra[i]))
			continue;
		program.demand_inline_function(extra[i].binding);
		set<const Binding*> generated_calls;
		collect_direct_calls(extra[i], generated_calls);
		for (set<const Binding*>::const_iterator it = generated_calls.begin();
		     it != generated_calls.end(); ++it)
			program.demand_inline_function(*it);
	}
}

const Node* extra_node_for_binding(const vector<Node>& extra,
                                   const Binding* binding)
{
	for (size_t i = 0; i < extra.size(); ++i)
		if (extra[i].binding == binding)
			return &extra[i];
	return NULL;
}

void demand_noop_generated_default_dependencies(
	ProgramLowerer& program,
	const vector<Node>& extra,
	const Binding* binding,
	set<const Binding*>& seen)
{
	if (binding == NULL || !seen.insert(binding).second)
		return;
	Binding* mutable_binding = const_cast<Binding*>(binding);
	TypePtr owner = class_record_for_member(binding);
	if (!binding->is_generated_default_constructor ||
	    owner.get() == NULL ||
	    !no_op_generated_default_constructor(mutable_binding, owner))
		return;
	const Node* node = extra_node_for_binding(extra, binding);
	if (node == NULL)
		return;
	set<const Binding*> generated_calls;
	collect_direct_calls(*node, generated_calls);
	set<const Binding*> base_constructor_calls;
	collect_base_constructor_calls(*node, base_constructor_calls);
	for (set<const Binding*>::const_iterator it = generated_calls.begin();
	     it != generated_calls.end();
	     ++it)
	{
		if (*it == NULL)
			continue;
		if ((*it)->is_generated_default_constructor)
		{
			demand_noop_generated_default_dependencies(program,
			                                           extra,
			                                           *it,
			                                           seen);
		}
		else
		{
			if (base_constructor_calls.count(*it) != 0 &&
			    is_class_constructor_binding(*it))
				program.constructor_symbol_for(*it, true);
			program.demand_inline_function(*it);
		}
	}
}

void demand_noop_generated_default_dependencies(
	ProgramLowerer& program,
	const vector<Node>& extra,
	const set<const Binding*>& direct_calls)
{
	set<const Binding*> seen;
	for (set<const Binding*>::const_iterator it = direct_calls.begin();
	     it != direct_calls.end();
	     ++it)
		demand_noop_generated_default_dependencies(program,
		                                           extra,
		                                           *it,
		                                           seen);
}

void collect_parser_output(ProgramLowerer& program,
                           pa12::internal::Parser& parser)
{
	const vector<Node>& extra = parser.extra_lowir_nodes();
	set<const Binding*> direct_calls;
	collect_direct_calls(parser.root(), direct_calls);
	for (size_t i = 0; i < extra.size(); ++i)
		program.register_inline_definition(extra[i]);
	for (size_t i = 0; i < extra.size(); ++i)
		collect_extra_variable(program, extra[i]);
	demand_object_roots(program, extra);
	demand_early_hidden_friends(program, extra, direct_calls);
	program.collect_translation_unit(parser.root());
	collect_referenced_extra_functions(program, extra, direct_calls);
	demand_noop_generated_default_dependencies(program, extra, direct_calls);
	demand_generated_copy_move_dependencies(program, extra);
	program.emit_pending_inline_definitions();
	program.emit_pending_synthetic_assignment_functions();
}

}  // namespace
}  // namespace internal

void emit_lowir(const vector<string>& srcfiles,
                const string& outfile,
                const Options& options)
{
	internal::ProgramLowerer program(options.native_lowering);
	vector<unique_ptr<pa12::internal::Parser> > parsers;
	for (size_t i = 0; i < srcfiles.size(); ++i)
	{
		pa12::Options pa12_options;
		pa12_options.preprocess = options.preprocess;
		unique_ptr<pa12::internal::Parser> parser(
			new pa12::internal::Parser(srcfiles[i], pa12_options));
		parser->parse_translation_unit();
		internal::collect_parser_output(program, *parser);
		parsers.push_back(std::move(parser));
	}
	program.emit_global_lifecycle_functions();
	program.write(outfile);
}

}  // namespace pa14
