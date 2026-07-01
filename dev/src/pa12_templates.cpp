#include "pa12_internal.h"
#include "pa12_expr_semantics_support.h"
#include "pa12_templates_function_support.h"
#include <algorithm>
#include <sstream>
#include <stdexcept>
using namespace std;
namespace pa12 {
namespace internal {
bool has_token(const vector<Token>& tokens, size_t begin, size_t end, ETokenType type);
void merge_template_defaults(vector<TemplateParameterInfo>& target, const vector<TemplateParameterInfo>& source);
Binding* find_matching_function_template_placeholder(const map<Binding*, TemplateDeclaration*>& placeholders, Scope* scope, const string& name, TypePtr type, const vector<TemplateParameterInfo>& parameters);
void collect_template_parameter_placeholders(const vector<TemplateParameterInfo>& parameters, map<string, TypePtr>& parameter_types, map<string, TemplateArgument>& parameter_values);
set<string> collect_template_type_parameter_packs(const vector<TemplateParameterInfo>& parameters);
vector<string> function_parameter_names_from_tokens(const vector<Token>& tokens, size_t lparen, size_t end, bool include_this);
bool function_header_has_noexcept(const vector<Token>& tokens, size_t lparen, size_t end);
Scope* primary_class_template_scope(TemplateDeclaration* declaration);
size_t explicit_function_parameter_name_count(const vector<string>& names);
vector<pa11::TemplateInstanceArgument> template_instance_arguments(
	const vector<TemplateArgument>& arguments);
bool hosted_library_namespace_scope(Scope* scope);
bool owner_pattern_is_primary_parameter_list(
	const vector<TemplateArgument>& pattern,
	const vector<TemplateParameterInfo>& parameters);
bool skip_template_id_argument_tokens(const vector<Token>& tokens, size_t& pos);
bool template_parameter_lists_match(const vector<TemplateParameterInfo>& left,
                                    const vector<TemplateParameterInfo>& right);
bool Parser::substitute_explicit_function_template_type(
	TemplateDeclaration* declaration,
	const vector<TemplateArgument>& full_args,
	TypePtr& out)
{
	if (declaration == NULL ||
	    declaration->generic_function_type.get() == NULL ||
	    declaration->generic_function_type->kind != pa11::TypeKind::Function)
		return false;
	vector<map<string, TypePtr> > save_subst = template_type_substitutions_;
	vector<map<string, TemplateArgument> > save_value_subst =
		template_value_substitutions_;
	vector<set<string> > save_pack_subst = template_type_parameter_packs_;
	map<string, TypePtr> subst;
	map<string, TemplateArgument> value_subst;
	set<string> pack_subst;
	for (size_t ai = 0;
	     ai < full_args.size() && ai < declaration->parameters.size();
	     ++ai)
	{
		const TemplateParameterInfo& parameter =
			declaration->parameters[ai];
		if (parameter.name.empty())
			continue;
		if (parameter.kind == TemplateParameterKind::Type)
		{
			if (parameter.is_pack)
			{
				subst[parameter.name] =
					template_parameter_placeholder_type(parameter);
				value_subst[parameter.name] = full_args[ai];
				pack_subst.insert(parameter.name);
			}
			else if (full_args[ai].kind == TemplateArgumentKind::Type)
				subst[parameter.name] = full_args[ai].type;
		}
		else
			value_subst[parameter.name] = full_args[ai];
	}
	template_type_substitutions_.insert(
		template_type_substitutions_.end(),
		declaration->outer_type_substitutions.begin(),
		declaration->outer_type_substitutions.end());
	template_value_substitutions_.insert(
		template_value_substitutions_.end(),
		declaration->outer_value_substitutions.begin(),
		declaration->outer_value_substitutions.end());
	template_type_substitutions_.push_back(subst);
	template_value_substitutions_.push_back(value_subst);
	template_type_parameter_packs_.push_back(pack_subst);
	try
	{
		out = substitute_function_template_type(
			declaration,
			declaration->generic_function_type);
	}
	catch (const runtime_error&)
	{
		template_type_substitutions_ = save_subst;
		template_value_substitutions_ = save_value_subst;
		template_type_parameter_packs_ = save_pack_subst;
		return false;
	}
	template_type_substitutions_ = save_subst;
	template_value_substitutions_ = save_value_subst;
	template_type_parameter_packs_ = save_pack_subst;
	return out.get() != NULL && out->kind == pa11::TypeKind::Function;
}
}  // namespace internal
}  // namespace pa12
