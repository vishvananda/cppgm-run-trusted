#include "pa12_templates_instance_support.h"
#include "pa12_types_support.h"

#include <algorithm>
#include <cstdint>
#include <sstream>
#include <stdexcept>
#include <utility>

#include "posttoken_pipeline.h"
#include "pp_token.h"

using namespace std;

namespace pa12 {
namespace internal {

TypePtr Parser::substitute_template_type_in_scope(TypePtr type,
                                                  Scope* scope) const
{
	if (scope == NULL)
		return substitute_template_type(type);
	Parser* self = const_cast<Parser*>(this);
	vector<Scope*> save_scopes = self->scopes_;
	vector<map<string, TypePtr> > save_subst =
		self->template_type_substitutions_;
	vector<map<string, TemplateArgument> > save_value_subst =
		self->template_value_substitutions_;
	vector<set<string> > save_pack_subst =
		self->template_type_parameter_packs_;
	self->scopes_.clear();
	self->scopes_.push_back(scope);
	TypePtr record = pa11::record_type_for_scope(scope);
	record = record.get() != NULL ? pa11::strip_cv(record) : TypePtr();
	map<const void*, TemplateDeclaration*>::const_iterator decl =
		record.get() != NULL
		? record_template_declarations_.find(record.get())
		: record_template_declarations_.end();
	map<const void*, vector<TemplateArgument> >::const_iterator args =
		record.get() != NULL
		? record_template_arguments_.find(record.get())
		: record_template_arguments_.end();
	auto push_record_template_substitutions =
		[&](TemplateDeclaration* declaration,
		    const vector<TemplateArgument>& arguments) {
			map<string, TypePtr> subst;
			map<string, TemplateArgument> value_subst;
			set<string> pack_subst;
			for (size_t i = 0;
			     i < arguments.size() && i < declaration->parameters.size();
			     ++i)
				if (!declaration->parameters[i].name.empty())
				{
					const TemplateParameterInfo& parameter =
						declaration->parameters[i];
					if (parameter.kind == TemplateParameterKind::Type)
					{
						if (parameter.is_pack)
						{
							subst[parameter.name] =
								pa11::make_template_parameter_type(
									parameter.name);
							value_subst[parameter.name] = arguments[i];
							if (arguments[i].kind ==
							        TemplateArgumentKind::Pack &&
							    arguments[i].pack.size() == 1 &&
							    arguments[i].pack[0].kind ==
								    TemplateArgumentKind::Type)
								subst[parameter.name] =
									arguments[i].pack[0].type;
							else if (arguments[i].kind ==
							         TemplateArgumentKind::Type)
								subst[parameter.name] =
									arguments[i].type;
							pack_subst.insert(parameter.name);
						}
						else
							subst[parameter.name] = arguments[i].type;
					}
					else
						value_subst[parameter.name] = arguments[i];
				}
			self->template_type_substitutions_.insert(
				self->template_type_substitutions_.end(),
				declaration->outer_type_substitutions.begin(),
				declaration->outer_type_substitutions.end());
			self->template_value_substitutions_.insert(
				self->template_value_substitutions_.end(),
				declaration->outer_value_substitutions.begin(),
				declaration->outer_value_substitutions.end());
			self->template_type_substitutions_.push_back(subst);
			self->template_value_substitutions_.push_back(value_subst);
			self->template_type_parameter_packs_.push_back(pack_subst);
		};
	vector<TypePtr> enclosing_records;
	for (Scope* cur = scope->parent; cur != NULL; cur = cur->parent)
	{
		TypePtr cur_record = pa11::record_type_for_scope(cur);
		cur_record = cur_record.get() != NULL
			? pa11::strip_cv(cur_record) : TypePtr();
		if (cur_record.get() != NULL &&
		    record_template_declarations_.find(cur_record.get()) !=
			    record_template_declarations_.end() &&
		    record_template_arguments_.find(cur_record.get()) !=
			    record_template_arguments_.end())
			enclosing_records.push_back(cur_record);
	}
	for (size_t i = enclosing_records.size(); i > 0; --i)
	{
		TypePtr enclosing = enclosing_records[i - 1];
		push_record_template_substitutions(
			record_template_declarations_.find(enclosing.get())->second,
			record_template_arguments_.find(enclosing.get())->second);
	}
	if (decl != record_template_declarations_.end() &&
	    args != record_template_arguments_.end())
		push_record_template_substitutions(decl->second, args->second);
	try
	{
		TypePtr out = substitute_template_type(type);
		self->scopes_ = save_scopes;
		self->template_type_substitutions_ = save_subst;
		self->template_value_substitutions_ = save_value_subst;
		self->template_type_parameter_packs_ = save_pack_subst;
		return out;
	}
	catch (...)
	{
		self->scopes_ = save_scopes;
		self->template_type_substitutions_ = save_subst;
		self->template_value_substitutions_ = save_value_subst;
		self->template_type_parameter_packs_ = save_pack_subst;
		throw;
	}
}

}  // namespace internal
}  // namespace pa12
