#include "pa12_internal.h"
#include "pa12_templates_function_support.h"

using namespace std;

namespace pa12 {
namespace internal {

bool record_has_reference_field(TypePtr type);
void stamp_template_member_function_symbol(Binding* binding);

bool Parser::parse_constructor_like_member(bool explicit_ctor,
                                           bool constexpr_ctor)
{
	if (current_scope()->kind != ScopeKind::Class || !at_identifier())
		return false;
	Scope* class_scope = current_scope();
	TypePtr class_type = pa11::record_type_for_scope(class_scope);
	if (class_type.get() == NULL)
		throw runtime_error("constructor without class type");
	if (!constructor_name_matches_scope(class_scope, current().source))
		return false;
	if (!lookahead(OP_LPAREN, 1))
		return false;
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
	fn_type = substitute_template_type(fn_type);
	for (size_t i = 0;
	     i < parameters.size() && i + 1 < fn_type->parameters.size();
	     ++i)
		parameters[i].type = fn_type->parameters[i + 1];
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
				ctor->has_default_arguments = true;
			}
		}
	if (have_ctor_defaults)
		default_arguments_[ctor] = ctor_defaults;
	ctor->is_inline_definition = at(OP_LBRACE) || at(OP_COLON) || at(KW_TRY) ||
	                             constexpr_ctor;
	ctor->is_explicit = explicit_ctor;
	ctor->unwind_no = suffix.noexcept_decl;
	ctor->is_private = !class_private_access_.empty() &&
	                   class_private_access_.back();
	ctor->is_protected_member = !class_protected_access_.empty() &&
	                            class_protected_access_.back();
	if (!active_class_instantiation_dependent())
		stamp_template_member_function_symbol(ctor);
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
		consume(KW_TRY);
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
		while (at(KW_CATCH))
		{
			consume(KW_CATCH);
			skip_balanced(OP_LPAREN, OP_RPAREN);
			skip_balanced(OP_LBRACE, OP_RBRACE);
		}
		enqueue_pending_member_body(class_scope, pending);
		return true;
	}
	Node holder("constructor-definition-holder");
	add_child(holder, fn);
	parse_constructor_body_from_parameters(ctor, class_type, parameters, holder);
	extra_lowir_nodes_.push_back(holder.children.back());
	return true;
}

}  // namespace internal
}  // namespace pa12
