#include "pa12_internal.h"

using namespace std;

namespace pa12 {
namespace internal {

Binding* Parser::instantiate_variable_template(
	TemplateDeclaration* declaration,
	const vector<TemplateArgument>& arguments)
{
	vector<TemplateArgument> full_args =
		complete_template_arguments(declaration, arguments);
	string key = template_argument_key(full_args);
	Binding*& cached = variable_template_specializations_[declaration][key];
	if (cached != NULL)
		return cached;
	pair<TemplateDeclaration*, string> active_key =
		make_pair(declaration, key);
	if (!active_variable_template_specializations_.insert(active_key).second)
		throw runtime_error("recursive variable template instantiation");

	size_t save_pos = pos_;
	vector<Scope*> save_scopes = scopes_;
	vector<map<string, TypePtr> > save_subst = template_type_substitutions_;
	vector<map<string, TemplateArgument> > save_value_subst =
		template_value_substitutions_;
	TemplateDeclaration* selected_declaration = declaration;
	vector<TemplateArgument> selected_args = full_args;
	try
	{
		select_variable_template_specialization(declaration,
		                                        full_args,
		                                        arguments.size(),
		                                        selected_declaration,
		                                        selected_args);
	}
	catch (...)
	{
		template_type_substitutions_ = save_subst;
		template_value_substitutions_ = save_value_subst;
		scopes_ = save_scopes;
		pos_ = save_pos;
		active_variable_template_specializations_.erase(active_key);
		throw;
	}
	try
	{
		bool dependent = template_arguments_dependent(selected_args);
		map<string, TypePtr> subst;
		map<string, TemplateArgument> value_subst;
		for (size_t i = 0; i < selected_args.size() &&
		     i < selected_declaration->parameters.size(); ++i)
			if (!selected_declaration->parameters[i].name.empty())
			{
				if (selected_declaration->parameters[i].is_pack)
				{
					subst[selected_declaration->parameters[i].name] =
						pa11::make_template_parameter_type(
							selected_declaration->parameters[i].name);
					value_subst[selected_declaration->parameters[i].name] =
						selected_args[i];
				}
				else if (selected_declaration->parameters[i].kind ==
				         TemplateParameterKind::Type)
					subst[selected_declaration->parameters[i].name] =
						selected_args[i].type;
				else
					value_subst[selected_declaration->parameters[i].name] =
						selected_args[i];
			}
		template_type_substitutions_.push_back(subst);
		template_value_substitutions_.push_back(value_subst);
		scopes_.clear();
		scopes_.push_back(selected_declaration->lexical_scope != NULL
		                  ? selected_declaration->lexical_scope
		                  : selected_declaration->owner);
		pos_ = selected_declaration->decl_begin;
		DeclSpecs specs = parse_decl_specifier_seq(false);
		TypePtr base = type_from_decl_specs(specs);
		Declarator declarator = parse_declarator(false);
		TypePtr type = apply_declarator(declarator, base);
		if (specs.constexpr_decl && !pa11::type_has_const(type))
			type = pa11::make_cv(type, pa11::CV_CONST);
		Expr init;
		if (consume(OP_ASS))
			init = parse_assignment_expression();
		string special_name =
			template_specialization_name(declaration, full_args);
		bool constant_init =
			!dependent && init.valid && init.has_constant_value;
		Binding* binding =
			add_value(declaration->owner,
			          constant_init
			          ? BindingKind::Enumerator : BindingKind::Variable,
			          special_name,
			          type);
		if (constant_init)
		{
			binding->has_constant = true;
			binding->constant_value = init.constant_value;
		}
		cached = binding;
		template_type_substitutions_ = save_subst;
		template_value_substitutions_ = save_value_subst;
		scopes_ = save_scopes;
		pos_ = save_pos;
		active_variable_template_specializations_.erase(active_key);
		return binding;
	}
	catch (...)
	{
		template_type_substitutions_ = save_subst;
		template_value_substitutions_ = save_value_subst;
		scopes_ = save_scopes;
		pos_ = save_pos;
		active_variable_template_specializations_.erase(active_key);
		throw;
	}
}

}  // namespace internal
}  // namespace pa12
