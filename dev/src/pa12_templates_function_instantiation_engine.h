#pragma once

#include "pa12_expr_semantics_support.h"
#include "pa12_templates_function_support.h"
#include "pa12_types_support.h"

namespace pa12 {
namespace internal {

struct FunctionTemplateInstantiationEngine
{
	Parser& p;
	TemplateDeclaration* declaration;
	const vector<TemplateArgument>& arguments;
	vector<TemplateArgument> full_args;
	string key;
	Binding* replaced_specialization;
	size_t save_pos;
	vector<Scope*> save_scopes;
	vector<map<string, TypePtr> > save_subst;
	vector<map<string, TemplateArgument> > save_value_subst;
	vector<set<string> > save_pack_subst;
	bool save_force_new_function_binding;
	bool save_defer_function_template_bodies;
	bool save_suppress_implicit_template_base_init;
	Scope* save_replay_function_type_override_owner;
	string save_replay_function_type_override_name;
	TemplateDeclaration* save_replay_function_template_declaration;
	vector<TemplateArgument> save_replay_function_template_arguments;
	bool save_override_function_parameter_names;
	vector<string> save_function_parameter_name_override;
	bool completion_active;

	FunctionTemplateInstantiationEngine(
		Parser& parser,
		TemplateDeclaration* declaration,
		const vector<TemplateArgument>& arguments);

	Binding* run();

	void complete_arguments();
	Binding* redirect_to_matching_definition();
		Binding* reuse_existing_specialization(
			map<string, Binding*>::iterator existing,
			bool full_args_dependent);
		void share_existing_specialization_if_available();
		TemplateDeclaration* specialization_body_source(
			TemplateDeclaration* source);
		void remember_reused_specialization_body(
			Binding* binding,
			TemplateDeclaration* source);
		bool specialization_matches_declaration_owner(Binding* binding);
		bool specialization_signature_matches(Binding* binding);
		void begin_completion();
	void enter_substitution_scope();
	void restore_parser_state();
	void restore_state();
	Binding* finish_with_restore(Binding* binding);
	bool instantiated_arguments_are_dependent() const;

	Binding* instantiate_with_substitutions(bool full_args_dependent);
	Binding* instantiate_dependent_signature();
	Binding* instantiate_candidate_signature(bool argument_dependent);
	Binding* instantiate_constructor_candidate();
	TypePtr substitute_dependent_signature_type();
	TypePtr substitute_candidate_signature_type(
		bool generic_return_is_decltype,
		bool& deferred_candidate_return);
	TypePtr substitute_constructor_candidate_type();
	TypePtr generic_return_type() const;
	bool generic_return_is_decltype() const;
	bool should_create_candidate_signature(bool has_template_default) const;
	bool has_template_parameter_default() const;
	bool invalid_candidate_signature(TypePtr type,
	                                 bool deferred_candidate_return) const;
	void model_hosted_candidate_type(TypePtr& type);
	void model_hosted_write_type(TypePtr& type);
	void model_hosted_function_assignment_type(TypePtr& type);
	void model_hosted_vector_insert_type(TypePtr& type);
	void model_hosted_make_pair_type(TypePtr& type);
	bool resolve_dependent_enable_if_return_type(TypePtr& type);

	Binding* create_specialization_binding(TypePtr type, bool force_value);
	void copy_placeholder_properties(Binding* binding, bool copy_defaults);
	void assign_specialization_symbol(Binding* binding,
	                                  bool include_non_member);
	void assign_aliased_class_member_symbol(Binding* binding);
	void register_specialization(Binding* binding,
	                             bool keep_placeholder_for_member);

	Binding* instantiate_deferred_member_body();
	bool ordinary_class_template_member() const;
	Binding* instantiate_ordinary_member_body(size_t body_pos);
	Binding* instantiate_out_of_line_member_body(size_t body_pos);
		void load_parameter_names(Binding* source,
		                          Binding* target,
		                          TypePtr type,
		                          vector<string>& names);
		PendingFunctionBody build_pending_body(Binding* binding,
		                                       const vector<string>& names,
		                                       size_t body_pos);
	void parse_or_queue_pending_body(PendingFunctionBody& pending);

	Binding* replay_function_template();
	void prepare_replay_parameter_names();
	vector<string> build_replay_parameter_names(
		const vector<string>& saved_names);
	bool replay_generic_has_owner_parameter() const;
	bool class_template_constructor_replay() const;
	size_t enter_friend_scopes();
	Node replay_template_declaration(size_t replay_extra_begin,
	                                 TypePtr& replay_substituted_function_type);
	Node replay_inherited_constructor();
	Node replay_constructor_template(size_t extra_before);
	Node replay_ordinary_function(size_t extra_before);
	Binding* finish_replayed_function(Node node,
	                                  TypePtr replay_substituted_function_type,
	                                  size_t replay_extra_begin);
	Node selected_replayed_function_node(const Node& node) const;
	void copy_replayed_placeholder_properties(Binding* binding);
	void merge_replayed_parameter_names(Binding* binding);
	void finish_replayed_defaults(Binding* binding);
	void parse_replayed_pending_bodies(Binding* binding);
	void prune_candidate_replay_bodies(Binding* binding,
	                                  size_t replay_extra_begin);
	Binding* finish_replayed_declaration(Node& fn);
	Binding* finish_replayed_definition(Node& fn, size_t replay_extra_begin);
};

Binding* instantiate_function_template_with_engine(
	Parser& parser,
	TemplateDeclaration* declaration,
	const vector<TemplateArgument>& arguments);

}  // namespace internal
}  // namespace pa12
