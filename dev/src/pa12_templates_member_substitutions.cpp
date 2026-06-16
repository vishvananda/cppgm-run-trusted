#include "pa12_templates_function_support.h"
#include "pa12_templates_instance_support.h"

#include <stdexcept>

using namespace std;

namespace pa12 {
namespace internal {

void Parser::make_concrete_outer_substitutions(
	TemplateDeclaration* declaration,
	TemplateDeclaration* owner_declaration,
	const vector<TemplateArgument>& owner_arguments,
	const map<string, TypePtr>& owner_type_subst,
	const map<string, TemplateArgument>& owner_value_subst,
	vector<map<string, TypePtr> >& type_substitutions,
	vector<map<string, TemplateArgument> >& value_substitutions)
{
	type_substitutions.clear();
	value_substitutions.clear();
	map<string, TypePtr> renamed_types;
	map<string, TemplateArgument> renamed_values;
	for (size_t p = declaration->decl_begin;
	     owner_declaration != NULL && p + 1 < declaration->decl_end;
	     ++p)
	{
		if (tokens_[p].kind != posttoken::TokenKind::Identifier ||
		    tokens_[p].source != owner_declaration->name ||
		    tokens_[p + 1].kind != posttoken::TokenKind::Simple ||
		    tokens_[p + 1].type != OP_LT)
			continue;
		size_t after_args = p + 1;
		int angle = 0;
		int paren = 0;
		int square = 0;
		int brace = 0;
		while (after_args < declaration->decl_end)
		{
			const Token& tok = tokens_[after_args];
			if (tok.kind == posttoken::TokenKind::Simple)
			{
				if (tok.type == OP_LPAREN)
					++paren;
				else if (tok.type == OP_RPAREN && paren > 0)
					--paren;
				else if (tok.type == OP_LSQUARE)
					++square;
				else if (tok.type == OP_RSQUARE && square > 0)
					--square;
				else if (tok.type == OP_LBRACE)
					++brace;
				else if (tok.type == OP_RBRACE && brace > 0)
					--brace;
				else if (paren == 0 && square == 0 && brace == 0)
				{
					if (tok.type == OP_LT)
						++angle;
					else if (tok.type == OP_GT)
					{
						--angle;
						if (angle == 0)
						{
							++after_args;
							break;
						}
					}
				}
			}
			++after_args;
		}
		if (after_args >= declaration->decl_end ||
		    tokens_[after_args].kind != posttoken::TokenKind::Simple ||
		    tokens_[after_args].type != OP_COLON2)
			continue;
		vector<TemplateArgument> pattern_args;
		size_t save_pos = pos_;
		vector<map<string, TypePtr> > save_subst =
			template_type_substitutions_;
		vector<map<string, TemplateArgument> > save_value_subst =
			template_value_substitutions_;
		try
		{
			template_type_substitutions_.insert(
				template_type_substitutions_.end(),
				declaration->outer_type_substitutions.begin(),
				declaration->outer_type_substitutions.end());
			template_value_substitutions_.insert(
				template_value_substitutions_.end(),
				declaration->outer_value_substitutions.begin(),
				declaration->outer_value_substitutions.end());
			pos_ = p + 1;
			parse_template_argument_list(pattern_args);
		}
		catch (const exception&)
		{
			pos_ = save_pos;
			template_type_substitutions_ = save_subst;
			template_value_substitutions_ = save_value_subst;
			continue;
		}
		pos_ = save_pos;
		template_type_substitutions_ = save_subst;
		template_value_substitutions_ = save_value_subst;
		for (size_t a = 0;
		     a < pattern_args.size() && a < owner_arguments.size();
		     ++a)
		{
			const TemplateArgument& pattern = pattern_args[a];
			const TemplateArgument& actual = owner_arguments[a];
			string pack_name;
			if (pack_argument_parameter_name(pattern, pack_name))
			{
				renamed_types[pack_name] =
					pa11::make_template_parameter_type(pack_name);
				renamed_values[pack_name] = actual;
				continue;
			}
			if (pattern.kind == TemplateArgumentKind::Type)
			{
				TypePtr pattern_type = pa11::strip_cv(pattern.type);
				if (pattern_type.get() != NULL &&
				    pattern_type->kind == pa11::TypeKind::TemplateParameter &&
				    actual.kind == TemplateArgumentKind::Type)
					renamed_types[pattern_type->name] = actual.type;
			}
			else if (pattern.kind == TemplateArgumentKind::Value &&
			         pattern.dependent &&
			         !pattern.value_name.empty())
				renamed_values[pattern.value_name] = actual;
			else if (pattern.kind == TemplateArgumentKind::Template &&
			         !pattern.value_name.empty())
				renamed_values[pattern.value_name] = actual;
		}
		break;
	}
	type_substitutions.push_back(owner_type_subst);
	value_substitutions.push_back(owner_value_subst);
	if (!renamed_types.empty())
		type_substitutions.push_back(renamed_types);
	if (!renamed_values.empty())
		value_substitutions.push_back(renamed_values);
}

}  // namespace internal
}  // namespace pa12
