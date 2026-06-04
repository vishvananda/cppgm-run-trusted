#include "pa12_internal.h"

#include <stdexcept>

using namespace std;

namespace pa12 {
namespace internal {

struct TemplateValidationState
{
	size_t pos;
	vector<Scope*> scopes;
	vector<TypePtr> function_returns;
	vector<Binding*> active_functions;
	vector<string> language_linkages;
	vector<bool> class_private_access;
	vector<bool> class_protected_access;
	Node root;
	vector<Node> generated_nodes;
	vector<map<string, TypePtr> > template_type_substitutions;
	vector<map<string, TemplateArgument> > template_value_substitutions;
	vector<ActiveClassInstantiation> active_class_instantiations;
	int local_type_counter;
	bool force_new_function_binding;
	bool override_function_parameter_names;
	vector<string> function_parameter_name_override;
	set<const void*> generated_default_ctors;
	set<pair<const void*, size_t> > generated_aggregate_ctors;
	set<const void*> generated_copy_ctors;
	set<const void*> generated_move_ctors;
	set<const void*> generated_copy_assignments;
	set<const void*> generated_move_assignments;
	set<const void*> generated_dtors;
	map<Binding*, Node> default_member_initializers;
	map<Binding*, vector<Expr> > default_arguments;
	map<Binding*, vector<string> > function_parameter_names;
	set<Binding*> override_function_parameter_name_bindings;
	set<Binding*> deleted_functions;
	map<const void*, Scope*> enum_owner_scopes;
	map<Scope*, vector<Binding*> > class_friend_functions;
	map<Scope*, vector<TypePtr> > class_friend_classes;
	map<Scope*, vector<PendingFunctionBody> > pending_member_bodies;
	map<Scope*, vector<Scope*> > deferred_nested_member_body_scopes;
	vector<Binding*> defaulted_move_assignments;
	int template_argument_expression_depth;
	size_t template_declaration_count;
	vector<TemplateDeclaration> template_values;
	map<Scope*, map<string, TemplateDeclaration*> > class_templates;
	map<Scope*, map<string, vector<TemplateDeclaration*> > > function_templates;
	map<pair<TemplateDeclaration*, string>, TemplateDeclaration*>
		member_class_templates;
	map<pair<TemplateDeclaration*, string>, vector<TemplateDeclaration*> >
		member_function_templates;
	map<pair<TemplateDeclaration*, string>, vector<TemplateDeclaration*> >
		member_variable_templates;
	map<Binding*, TemplateDeclaration*> function_template_placeholders;
	map<const void*, TemplateDeclaration*> record_template_declarations;
	map<const void*, vector<TemplateArgument> > record_template_arguments;
	set<TemplateDeclaration*> class_templates_with_dependent_base;
	set<const void*> record_dependent_base_lookup_skips;
	vector<Node> extra_lowir_nodes;
	bool validation_found_dependent_base;

	TemplateValidationState(Parser& parser, TemplateDeclaration* declaration);
	void save_core(Parser& parser, TemplateDeclaration* declaration);
	void save_generated(Parser& parser);
	void save_semantic_tables(Parser& parser);
	void save_template_tables(Parser& parser);
	void restore(Parser& parser, TemplateDeclaration* declaration);
	void restore_core(Parser& parser);
	void restore_generated(Parser& parser);
	void restore_semantic_tables(Parser& parser);
	void restore_template_tables(Parser& parser,
	                             TemplateDeclaration* declaration,
	                             bool keep_dependent_base);
};

TemplateValidationState::TemplateValidationState(
	Parser& parser,
	TemplateDeclaration* declaration)
{
	save_core(parser, declaration);
	save_generated(parser);
	save_semantic_tables(parser);
	save_template_tables(parser);
}

void TemplateValidationState::save_core(Parser& parser,
                                        TemplateDeclaration* declaration)
{
	pos = parser.pos_;
	scopes = parser.scopes_;
	function_returns = parser.function_returns_;
	active_functions = parser.active_functions_;
	language_linkages = parser.language_linkages_;
	class_private_access = parser.class_private_access_;
	class_protected_access = parser.class_protected_access_;
	root = parser.root_;
	generated_nodes = parser.generated_nodes_;
	template_type_substitutions = parser.template_type_substitutions_;
	template_value_substitutions = parser.template_value_substitutions_;
	active_class_instantiations = parser.active_class_instantiations_;
	local_type_counter = parser.local_type_counter_;
	force_new_function_binding = parser.force_new_function_binding_;
	override_function_parameter_names =
		parser.override_function_parameter_names_;
	function_parameter_name_override =
		parser.function_parameter_name_override_;
	template_argument_expression_depth =
		parser.template_argument_expression_depth_;
	extra_lowir_nodes = parser.extra_lowir_nodes_;
	validation_found_dependent_base =
		parser.class_templates_with_dependent_base_.count(declaration) != 0;
}

void TemplateValidationState::save_generated(Parser& parser)
{
	generated_default_ctors = parser.generated_default_ctors_;
	generated_aggregate_ctors = parser.generated_aggregate_ctors_;
	generated_copy_ctors = parser.generated_copy_ctors_;
	generated_move_ctors = parser.generated_move_ctors_;
	generated_copy_assignments = parser.generated_copy_assignments_;
	generated_move_assignments = parser.generated_move_assignments_;
	generated_dtors = parser.generated_dtors_;
}

void TemplateValidationState::save_semantic_tables(Parser& parser)
{
	default_member_initializers = parser.default_member_initializers_;
	default_arguments = parser.default_arguments_;
	function_parameter_names = parser.function_parameter_names_;
	override_function_parameter_name_bindings =
		parser.override_function_parameter_name_bindings_;
	deleted_functions = parser.deleted_functions_;
	enum_owner_scopes = parser.enum_owner_scopes_;
	class_friend_functions = parser.class_friend_functions_;
	class_friend_classes = parser.class_friend_classes_;
	pending_member_bodies = parser.pending_member_bodies_;
	deferred_nested_member_body_scopes =
		parser.deferred_nested_member_body_scopes_;
	defaulted_move_assignments = parser.defaulted_move_assignments_;
}

void TemplateValidationState::save_template_tables(Parser& parser)
{
	template_declaration_count = parser.template_declarations_.size();
	for (size_t i = 0; i < parser.template_declarations_.size(); ++i)
		template_values.push_back(*parser.template_declarations_[i]);
	class_templates = parser.class_templates_;
	function_templates = parser.function_templates_;
	member_class_templates = parser.member_class_templates_;
	member_function_templates = parser.member_function_templates_;
	member_variable_templates = parser.member_variable_templates_;
	function_template_placeholders = parser.function_template_placeholders_;
	record_template_declarations = parser.record_template_declarations_;
	record_template_arguments = parser.record_template_arguments_;
	class_templates_with_dependent_base =
		parser.class_templates_with_dependent_base_;
	record_dependent_base_lookup_skips =
		parser.record_dependent_base_lookup_skips_;
}

void TemplateValidationState::restore(Parser& parser,
                                      TemplateDeclaration* declaration)
{
	bool keep_dependent_base =
		validation_found_dependent_base ||
		parser.class_templates_with_dependent_base_.count(declaration) != 0;
	restore_core(parser);
	restore_generated(parser);
	restore_semantic_tables(parser);
	restore_template_tables(parser, declaration, keep_dependent_base);
}

void TemplateValidationState::restore_core(Parser& parser)
{
	parser.pos_ = pos;
	parser.scopes_ = scopes;
	parser.function_returns_ = function_returns;
	parser.active_functions_ = active_functions;
	parser.language_linkages_ = language_linkages;
	parser.class_private_access_ = class_private_access;
	parser.class_protected_access_ = class_protected_access;
	parser.root_ = root;
	parser.generated_nodes_ = generated_nodes;
	parser.extra_lowir_nodes_ = extra_lowir_nodes;
	parser.local_type_counter_ = local_type_counter;
	parser.force_new_function_binding_ = force_new_function_binding;
	parser.override_function_parameter_names_ =
		override_function_parameter_names;
	parser.function_parameter_name_override_ =
		function_parameter_name_override;
	parser.template_argument_expression_depth_ =
		template_argument_expression_depth;
	parser.template_type_substitutions_ = template_type_substitutions;
	parser.template_value_substitutions_ = template_value_substitutions;
	parser.active_class_instantiations_ = active_class_instantiations;
}

void TemplateValidationState::restore_generated(Parser& parser)
{
	parser.generated_default_ctors_ = generated_default_ctors;
	parser.generated_aggregate_ctors_ = generated_aggregate_ctors;
	parser.generated_copy_ctors_ = generated_copy_ctors;
	parser.generated_move_ctors_ = generated_move_ctors;
	parser.generated_copy_assignments_ = generated_copy_assignments;
	parser.generated_move_assignments_ = generated_move_assignments;
	parser.generated_dtors_ = generated_dtors;
}

void TemplateValidationState::restore_semantic_tables(Parser& parser)
{
	parser.default_member_initializers_ = default_member_initializers;
	parser.default_arguments_ = default_arguments;
	parser.function_parameter_names_ = function_parameter_names;
	parser.override_function_parameter_name_bindings_ =
		override_function_parameter_name_bindings;
	parser.deleted_functions_ = deleted_functions;
	parser.enum_owner_scopes_ = enum_owner_scopes;
	parser.class_friend_functions_ = class_friend_functions;
	parser.class_friend_classes_ = class_friend_classes;
	parser.pending_member_bodies_ = pending_member_bodies;
	parser.deferred_nested_member_body_scopes_ =
		deferred_nested_member_body_scopes;
	parser.defaulted_move_assignments_ = defaulted_move_assignments;
}

void TemplateValidationState::restore_template_tables(
	Parser& parser,
	TemplateDeclaration* declaration,
	bool keep_dependent_base)
{
	while (parser.template_declarations_.size() > template_declaration_count)
		parser.template_declarations_.pop_back();
	for (size_t i = 0; i < template_values.size(); ++i)
		*parser.template_declarations_[i] = template_values[i];
	parser.class_templates_ = class_templates;
	parser.function_templates_ = function_templates;
	parser.member_class_templates_ = member_class_templates;
	parser.member_function_templates_ = member_function_templates;
	parser.member_variable_templates_ = member_variable_templates;
	parser.function_template_placeholders_ = function_template_placeholders;
	parser.record_template_declarations_ = record_template_declarations;
	parser.record_template_arguments_ = record_template_arguments;
	parser.class_templates_with_dependent_base_ =
		class_templates_with_dependent_base;
	if (keep_dependent_base)
		parser.class_templates_with_dependent_base_.insert(declaration);
	parser.record_dependent_base_lookup_skips_ =
		record_dependent_base_lookup_skips;
}

void Parser::validate_class_template_definition(TemplateDeclaration* declaration)
{
	if (declaration == NULL || !declaration->has_definition)
		return;
	TemplateValidationState saved(*this, declaration);

	map<string, TypePtr> subst;
	map<string, TemplateArgument> value_subst;
	vector<TemplateArgument> args;
	for (size_t i = 0; i < declaration->parameters.size(); ++i)
	{
		string name = declaration->parameters[i].name;
		if (name.empty())
			name = "__template_param" + to_string(i);
		if (declaration->parameters[i].kind == TemplateParameterKind::Type)
		{
			TypePtr param = pa11::make_template_parameter_type(name);
			if (declaration->parameters[i].is_pack)
			{
				vector<TemplateArgument> pack;
				pack.push_back(TemplateArgument::type_arg(param));
				TemplateArgument arg = TemplateArgument::pack_arg(pack);
				args.push_back(arg);
				if (!declaration->parameters[i].name.empty())
				{
					subst[declaration->parameters[i].name] = param;
					value_subst[declaration->parameters[i].name] =
						arg;
				}
			}
			else
			{
				args.push_back(TemplateArgument::type_arg(param));
				if (!declaration->parameters[i].name.empty())
					subst[declaration->parameters[i].name] = param;
			}
		}
		else
		{
			TypePtr type = declaration->parameters[i].type.get() != NULL
				? declaration->parameters[i].type
				: pa11::make_fundamental(FT_INT);
			TemplateArgument arg =
				TemplateArgument::dependent_value_arg(type);
			if (declaration->parameters[i].is_pack)
			{
				vector<TemplateArgument> pack;
				pack.push_back(arg);
				arg = TemplateArgument::pack_arg(pack);
			}
			args.push_back(arg);
			if (!declaration->parameters[i].name.empty())
				value_subst[declaration->parameters[i].name] = arg;
		}
	}
	ScopeKind owner_kind = declaration->owner != NULL
		? declaration->owner->kind : ScopeKind::Namespace;
	string owner_name = declaration->owner != NULL ? declaration->owner->name : "";
	unique_ptr<Scope> validation_owner(
		new Scope(owner_kind, owner_name, declaration->owner));
	Scope* class_scope =
		pa11::create_child_scope(validation_owner.get(),
		                         ScopeKind::Class,
		                         declaration->name);
	TypePtr validation_type =
		pa11::make_record_type(declaration->name,
		                       declaration->tag.empty() ? "struct" :
		                       declaration->tag,
		                       false,
		                       class_scope);
	Binding* validation_binding =
		pa11::add_binding(validation_owner.get(),
		                  BindingKind::Type,
		                  declaration->name,
		                  validation_type);
	validation_binding->target_scope = class_scope;
	Binding* injected =
		pa11::add_binding(class_scope,
		                  BindingKind::Type,
		                  declaration->name,
		                  validation_type);
	injected->target_scope = class_scope;
	template_type_substitutions_.push_back(subst);
	template_value_substitutions_.push_back(value_subst);
	active_class_instantiations_.push_back(
		ActiveClassInstantiation(declaration,
		                         template_specialization_name(declaration,
		                                                      args),
		                         validation_type));
	scopes_.clear();
	scopes_.push_back(declaration->lexical_scope != NULL
	                  ? declaration->lexical_scope
	                  : declaration->owner);
	pos_ = declaration->decl_begin;
	try
	{
		TypePtr parsed = parse_class_specifier();
		(void)parsed;
	}
	catch (const runtime_error& err)
	{
		saved.restore(*this, declaration);
		if (string(err.what()) == "incomplete object type" ||
		    string(err.what()) == "incomplete class type" ||
		    string(err.what()) == "no matching constructor" ||
		    string(err.what()) == "invalid initializer conversion" ||
		    string(err.what()) == "decltype qualifier is not a scope" ||
		    string(err.what()) == "qualified lookup root not found")
			return;
		throw;
	}
	catch (const exception&)
	{
		saved.restore(*this, declaration);
		throw;
	}
	saved.restore(*this, declaration);
}

}  // namespace internal
}  // namespace pa12
