#pragma once

#include <cstddef>
#include <map>
#include <vector>

#include "pa12_internal.h"

namespace pa12 {
namespace internal {

struct TemplateCallCandidateInstantiator
{
	Parser& p;
	Binding* fn;
	const std::map<Binding*, std::vector<TemplateArgument> >& explicit_template_arguments;
	const std::vector<Expr>& args;
	Binding* placeholder;
	TemplateDeclaration* original_declaration;
	TemplateDeclaration* declaration;
	bool placeholder_candidate;
	bool specialization_candidate;
	bool fn_type_dependent;
	bool recovered_effective_declaration;
	bool have_call_explicit_args;
	std::vector<TemplateArgument> explicit_args;
	std::vector<TemplateArgument> deduced;
	TemplateCallCandidateInstantiator(
		Parser& parser,
		Binding* function,
		const std::map<Binding*, std::vector<TemplateArgument> >& explicit_args_map,
		const std::vector<Expr>& call_args)
		: p(parser), fn(function), explicit_template_arguments(explicit_args_map),
		  args(call_args), placeholder(function), original_declaration(NULL),
		  declaration(NULL), placeholder_candidate(false),
		  specialization_candidate(false), fn_type_dependent(false),
		  recovered_effective_declaration(false),
		  have_call_explicit_args(false) {}
	Binding* run();
	bool load_template_declaration();
	bool cached_function_type_dependent();
	bool cached_binding_type_dependent(Binding* binding);
	void choose_declaration_with_body();
	void recover_effective_declaration();
	void select_explicit_arguments();
	size_t stored_concrete_specialization_cache_key() const;
	bool try_stored_concrete_specialization(Binding*& out);
	bool try_explicit_specialization_for_call(Binding*& out);
	bool try_modeled_hosted_candidate(Binding*& out);
	bool member_call_owner_matches(Binding* binding) const;
	Binding* canonical_call_binding(Binding* binding) const;
	bool deduce_arguments();
	std::vector<size_t> deduction_cache_key() const;
	void append_expr_key(std::vector<size_t>& key,
	                     const Expr& expr,
	                     size_t depth) const;
	void add_recovered_friend_bindings();
	void apply_basic_string_result(Binding* instantiated);
	void apply_std_function_assignment_result(Binding* instantiated);
	void record_replacement(Binding* instantiated);
	Binding* instantiate_deduced();
};

}  // namespace internal
}  // namespace pa12
