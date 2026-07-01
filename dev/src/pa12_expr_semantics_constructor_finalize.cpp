#include "pa12_expr_semantics_support.h"
#include "pa12_templates_instance_support.h"
#include "pa12_types_support.h"

#include <algorithm>
#include <stdexcept>

using namespace std;

namespace pa12 {
namespace internal {

bool Parser::use_hosted_allocator_constructor_fallback(
	TypePtr record,
	const vector<Expr>& args,
	Binding*& best,
	vector<Expr>& best_args,
	bool& ambiguous)
{
	if (best != NULL || ambiguous || !hosted_compatibility_ ||
	    args.size() != 1)
		return false;
	auto hosted_allocator_primary = [](const string& primary) {
		return primary == "allocator" || primary == "__new_allocator";
	};
	if (args[0].type.get() == NULL)
		return false;
	TypePtr source = expression_object_type(args[0].type);
	TypePtr source_record = source.get() != NULL
		? pa11::strip_cv(source) : TypePtr();
	string target_primary = hosted_unqualified_primary(record);
	string source_primary = hosted_unqualified_primary(source_record);
	if (!record->is_template_specialization ||
	    !hosted_library_namespace_scope(record->scope) ||
	    source_record.get() == NULL ||
	    source_record->kind != pa11::TypeKind::Record ||
	    !source_record->is_template_specialization ||
	    !hosted_library_namespace_scope(source_record->scope) ||
	    !hosted_allocator_primary(target_primary) ||
	    target_primary != source_primary)
		return false;
	TypePtr param_type = pa11::make_lvalue_reference(
		pa11::make_cv(source_record, pa11::CV_CONST));
	vector<TypePtr> params;
	params.push_back(pa11::make_pointer(record));
	params.push_back(param_type);
	TypePtr fn_type = pa11::make_function(pa11::make_fundamental(FT_VOID),
	                                      params,
	                                      false);
	Binding* ctor = NULL;
	map<string, vector<Binding*> >::iterator existing =
		record->scope->members.find(record->scope->name);
	if (existing != record->scope->members.end())
		for (size_t ci = 0; ci < existing->second.size(); ++ci)
			if (existing->second[ci]->kind == BindingKind::Function &&
			    pa11::same_type(existing->second[ci]->type, fn_type))
				ctor = existing->second[ci];
	if (ctor == NULL)
	{
		ctor = add_value(record->scope,
		                 BindingKind::Function,
		                 record->scope->name,
		                 fn_type);
		ctor->is_inline_definition = true;
		ctor->is_defaulted = true;
		function_parameter_names_[ctor] = vector<string>(2, "this");
		function_parameter_names_[ctor][1] = "other";
	}
	best = ctor;
	best_args = args;
	ambiguous = false;
	return true;
}

Binding* Parser::instantiate_selected_constructor_body(Binding* best)
{
	if (best == NULL ||
	    unevaluated_expression_depth_ != 0)
		return best;
	map<Binding*, TemplateDeclaration*>::iterator template_it =
		function_template_placeholders_.find(best);
	map<Binding*, vector<TemplateArgument> >::iterator args_it =
		function_template_specialization_arguments_.find(best);
	if (template_it == function_template_placeholders_.end() &&
	    args_it == function_template_specialization_arguments_.end() &&
	    best->is_inline_definition &&
	    function_bodies_.find(best) != function_bodies_.end())
		return best;
	TemplateDeclaration* replay_declaration =
		template_it != function_template_placeholders_.end()
		? template_it->second : NULL;
	if (replay_declaration == NULL)
		return best;
	bool inherited_constructor_replay =
		replay_declaration->inherited_constructor_base != NULL;
	if (!inherited_constructor_replay)
		replay_declaration = replacement_function_template_definition(replay_declaration);
	if (!inherited_constructor_replay &&
	    !template_declaration_has_body(declaration_tokens_, replay_declaration))
	{
		TemplateDeclaration* compatible_body = NULL;
		for (map<pair<TemplateDeclaration*, string>,
		     vector<TemplateDeclaration*> >::iterator mit =
			     member_function_templates_.begin();
		     mit != member_function_templates_.end();
		     ++mit)
		{
			if (mit->first.second != replay_declaration->name)
				continue;
			for (size_t di = 0; di < mit->second.size(); ++di)
			{
				TemplateDeclaration* candidate = mit->second[di];
				if (candidate == replay_declaration ||
				    !candidate->constructor_template ||
				    !template_declaration_has_body(declaration_tokens_,
				                                   candidate) ||
				    candidate->generic_function_type.get() == NULL ||
				    !expr_template_parameter_lists_match(
					    candidate->parameters,
					    replay_declaration->parameters))
					continue;
				if (compatible_body == NULL)
					compatible_body = candidate;
				if (!same_template_signature_type(
					    candidate->generic_function_type,
					    replay_declaration->generic_function_type))
					continue;
				replay_declaration = candidate;
				break;
			}
			if (template_declaration_has_body(declaration_tokens_,
			                                  replay_declaration))
				break;
		}
		if (!template_declaration_has_body(declaration_tokens_,
		                                   replay_declaration) &&
		    compatible_body != NULL)
		{
			unique_ptr<TemplateDeclaration> clone(
				new TemplateDeclaration(*compatible_body));
			clone->owner = replay_declaration->owner;
			clone->placeholder = replay_declaration->placeholder;
			clone->class_template_member = replay_declaration->class_template_member;
			clone->outer_type_substitutions =
				replay_declaration->outer_type_substitutions;
			clone->outer_value_substitutions =
				replay_declaration->outer_value_substitutions;
			clone->function_specializations.clear();
			clone->completing_specializations.clear();
			replay_declaration = clone.get();
			template_declarations_.push_back(std::move(clone));
		}
	}
	if (template_it == function_template_placeholders_.end() ||
	    args_it == function_template_specialization_arguments_.end() ||
	    (!inherited_constructor_replay &&
	     !template_declaration_has_body(declaration_tokens_, replay_declaration)))
		return best;
	vector<TemplateArgument> selected_args = args_it->second;
	if (selected_args.size() < replay_declaration->parameters.size())
	{
		++function_template_candidate_instantiation_depth_;
		try
		{
			selected_args = complete_template_arguments(replay_declaration,
			                                           selected_args);
		}
		catch (...)
		{
			--function_template_candidate_instantiation_depth_;
			throw;
		}
		--function_template_candidate_instantiation_depth_;
	}
	bool saved_force_body_instantiation =
		force_function_template_body_instantiation_;
	force_function_template_body_instantiation_ = true;
	Binding* instantiated = NULL;
	try
	{
		instantiated =
			instantiate_function_template(replay_declaration, selected_args);
	}
	catch (...)
	{
		force_function_template_body_instantiation_ =
			saved_force_body_instantiation;
		throw;
	}
	force_function_template_body_instantiation_ =
		saved_force_body_instantiation;
	if (instantiated != NULL && best != instantiated)
		best->aliased_binding = instantiated;
	return instantiated != NULL ? instantiated : best;
}

Binding* Parser::wrap_inherited_constructor_if_needed(TypePtr record,
                                                      Binding* best)
{
	if (best == NULL ||
	    best->owner == NULL ||
	    best->owner->kind != ScopeKind::Class ||
	    best->type.get() == NULL ||
	    best->type->kind != pa11::TypeKind::Function ||
	    best->type->parameters.empty() ||
	    record->scope == NULL ||
	    best->owner == record->scope)
		return best;
	TypePtr base_record = pa11::record_type_for_scope(best->owner);
	base_record = base_record.get() != NULL
		? pa11::strip_cv(base_record) : TypePtr();
	if (base_record.get() == NULL ||
	    base_record->kind != pa11::TypeKind::Record ||
	    !record_has_base_type(record, base_record))
		return best;
	vector<TypePtr> params = best->type->parameters;
	params[0] = pa11::make_pointer(record);
	TypePtr fn_type = pa11::make_function(pa11::make_fundamental(FT_VOID),
	                                      params,
	                                      best->type->variadic);
	fn_type->cv = best->type->cv;
	fn_type->ref_qualifier = best->type->ref_qualifier;
	Binding* wrapper = NULL;
	map<string, vector<Binding*> >::iterator existing =
		record->scope->members.find(record->scope->name);
	if (existing != record->scope->members.end())
		for (size_t i = 0; i < existing->second.size(); ++i)
		{
			Binding* candidate = existing->second[i];
			if (candidate->kind == BindingKind::Function &&
			    candidate->owner == record->scope &&
			    candidate->type.get() != NULL &&
			    pa11::same_type(candidate->type, fn_type) &&
			    function_bodies_.find(candidate) != function_bodies_.end())
				return candidate;
		}
	wrapper = add_value(record->scope,
	                    BindingKind::Function,
	                    record->scope->name,
	                    fn_type);
	wrapper->is_inline_definition = true;
		wrapper->is_explicit = best->is_explicit;
		wrapper->is_constexpr = best->is_constexpr;
		wrapper->unwind_no = best->unwind_no;
		wrapper->dynamic_exception_spec = best->dynamic_exception_spec;
		wrapper->dynamic_exception_types = best->dynamic_exception_types;
		wrapper->ref_qualifier = best->ref_qualifier;
	vector<string> names(1, "this");
	map<Binding*, vector<string> >::const_iterator base_names =
		function_parameter_names_.find(best);
	for (size_t i = 1; i < params.size(); ++i)
		names.push_back(base_names != function_parameter_names_.end() &&
		                i < base_names->second.size() &&
		                !base_names->second[i].empty()
		                ? base_names->second[i]
		                : "__param" + to_string(i));
	function_parameter_names_[wrapper] = names;
	Node fn("function-definition " + qualified_decl_name(wrapper) + " " +
	        pa11::describe_type(fn_type));
	fn.binding = wrapper;
	fn.type = fn_type;
	Scope* function_scope =
		pa11::create_child_scope(record->scope, ScopeKind::Function, wrapper->name);
	Binding* this_binding =
		pa11::add_binding(function_scope, BindingKind::Parameter, "this", params[0]);
	Node this_node("parameter this " + pa11::describe_type(params[0]));
	this_node.binding = this_binding;
	this_node.type = params[0];
	add_child(fn, this_node);
	Node init("braced-init-list");
	for (size_t i = 1; i < params.size(); ++i)
	{
		Binding* param = pa11::add_binding(function_scope,
		                                   BindingKind::Parameter,
		                                   names[i],
		                                   params[i]);
		Node param_node("parameter " + names[i] + " " +
		                pa11::describe_type(params[i]));
		param_node.binding = param;
		param_node.type = params[i];
		add_child(fn, param_node);
		Node arg("id-expression lvalue " + pa11::describe_type(params[i]) +
		         " " + names[i]);
		arg.binding = param;
		arg.type = params[i];
		arg.category = ValueCategory::LValue;
		add_child(init, arg);
	}
	init.type = base_record;
	init.category = ValueCategory::LValue;
	Node body("compound-statement");
	Node base_action = make_base_init_action(base_record, &init);
	base_action.direct_call = best;
	base_action.token_text = "inherited-constructor";
	add_child(body, base_action);
	add_child(fn, body);
	remember_function_body(wrapper, fn);
	extra_lowir_nodes_.push_back(fn);
	return wrapper;
}

void Parser::finalize_constructor_candidate(TypePtr record, Binding*& best)
{
	bool delay_body = constructor_body_can_be_delayed(record, best);
	if (best != NULL &&
	    unevaluated_expression_depth_ == 0 &&
	    !delay_body)
	{
		parse_pending_function_body(best);
		parse_pending_member_body(best);
		ensure_function_body_extra_node(best);
	}
	bool inherited_template =
		inherited_constructor_template_candidate(function_template_placeholders_,
		                                         best);
	if (!inherited_template)
	{
		Binding* canonical = canonical_function_binding(best);
		if (constructor_binding_for_record(record, canonical))
			best = canonical;
	}
	mark_template_specialization_demanded(best->type);
	if (best->is_defaulted &&
	    best->type->kind == pa11::TypeKind::Function &&
	    best->type->parameters.size() == 2 &&
	    pa11::is_reference_type(best->type->parameters[1]) &&
	    pa11::same_type(pa11::strip_cv(best->type->parameters[1]->base), record))
		ensure_copy_move_constructor(
			record,
			best->type->parameters[1]->kind == pa11::TypeKind::RValueReference);
	if (deleted_functions_.find(best) != deleted_functions_.end())
		throw runtime_error("call to deleted function");
}

}  // namespace internal
}  // namespace pa12
