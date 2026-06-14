#pragma once

#include <map>
#include <set>
#include <string>
#include <vector>

#include "pa11_internal.h"

using namespace std;

namespace pa12 {
namespace internal {

using pa11::Binding;
using pa11::Scope;
using pa11::TypePtr;

enum class TemplateParameterKind
{
	Type,
	NonType,
	TemplateTemplate
};
enum class TemplateArgumentKind
{
	Type,
	Value,
	Template,
	Pack
};
struct TemplateDeclaration;
struct TemplateArgument
{
	TemplateArgumentKind kind;
	TypePtr type;
	TemplateDeclaration* template_declaration;
	Binding* value_binding;
	string value_name;
	string value_owner_template_name;
	string value_member_name;
	uint64_t value;
	bool dependent;
	bool value_negated;
	bool pack_expansion;
	size_t value_expr_begin;
	size_t value_expr_end;
	vector<TemplateArgument> pack;
	vector<pa11::TemplateInstanceArgument> value_owner_template_arguments;
	TemplateArgument();
	static TemplateArgument type_arg(TypePtr type);
	static TemplateArgument value_arg(TypePtr type, uint64_t value);
	static TemplateArgument dependent_value_arg(TypePtr type);
	static TemplateArgument template_arg(TemplateDeclaration* declaration);
	static TemplateArgument pack_arg(const vector<TemplateArgument>& values);
};
bool template_argument_has_template_parameter(
	const TemplateArgument& arg,
	const map<const void*, vector<TemplateArgument> >& record_template_arguments);
bool template_instance_argument_has_template_parameter(
	const pa11::TemplateInstanceArgument& argument,
	const map<const void*, vector<TemplateArgument> >& record_template_arguments);
bool template_type_has_template_parameter_name(TypePtr type, string& name);
bool template_type_has_template_parameter(
	TypePtr type,
	const map<const void*, vector<TemplateArgument> >& record_template_arguments);

struct TemplateParameterInfo
{
	TemplateParameterKind kind;
	string name;
	TypePtr type;
	vector<TemplateParameterInfo> template_parameters;
	bool is_pack;
	bool has_default;
	size_t default_begin;
	size_t default_end;
	TemplateParameterInfo();
};
enum class TemplateDeclarationKind
{
	Unknown,
	Class,
	Function,
	Variable,
	Alias
};
struct TemplateDeclaration
{
	TemplateDeclarationKind kind;
	Scope* owner;
	Scope* lexical_scope;
	string name;
	string tag;
	vector<TemplateParameterInfo> parameters;
	size_t decl_begin;
	size_t decl_end;
	bool has_definition;
	bool constructor_template;
	bool class_template_member;
	bool class_specialization;
	bool hidden_friend;
	bool class_definition_validated;
	bool function_definition_validated;
	Scope* friend_class_scope;
	TypePtr generic_function_type;
	vector<string> function_parameter_names;
	Binding* placeholder;
	Binding* inherited_constructor_base;
	TypePtr inherited_constructor_base_type;
	vector<map<string, TypePtr> > outer_type_substitutions;
	vector<map<string, TemplateArgument> > outer_value_substitutions;
	vector<TemplateArgument> class_specialization_pattern;
	vector<TemplateDeclaration*> class_specialization_declarations;
	map<string, TypePtr> class_specializations;
	map<string, Binding*> function_specializations;
	set<string> completing_specializations;
	set<string> emitted_variable_specializations;
	TemplateDeclaration();
};
string qualified_template_declaration_name(
	const TemplateDeclaration* declaration);

struct ActiveClassInstantiation
{
	TemplateDeclaration* declaration;
	string specialization_name;
	TypePtr type;
	ActiveClassInstantiation();
	ActiveClassInstantiation(TemplateDeclaration* d, const string& n, TypePtr t);
};

}  // namespace internal
}  // namespace pa12
