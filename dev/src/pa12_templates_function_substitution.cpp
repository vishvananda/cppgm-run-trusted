#include "pa12_templates_function_support.h"

#include <algorithm>
#include <functional>
#include <stdexcept>

using namespace std;

namespace pa12 {
namespace internal {

	TypePtr Parser::substitute_function_template_type(
		TemplateDeclaration* declaration,
		TypePtr type) const
	{
		if (type.get() == NULL || type->kind != pa11::TypeKind::Function)
			return substitute_template_type(type);
		vector<TypePtr> params;
		map<Binding*, vector<string> >::const_iterator saved_names =
			declaration != NULL && declaration->placeholder != NULL
			? function_parameter_names_.find(declaration->placeholder)
			: function_parameter_names_.end();
		Parser* self = const_cast<Parser*>(this);
		struct ActiveParameterScope
		{
			Parser* self;
			vector<Scope*> saved_scopes;
			Scope* scope;

			ActiveParameterScope(Parser* p, bool active)
			  : self(p), scope(NULL)
			{
				if (!active)
					return;
				saved_scopes = self->scopes_;
				scope = pa11::create_child_scope(self->current_scope(),
				                                 ScopeKind::Function,
				                                 "");
				self->scopes_.push_back(scope);
			}

			~ActiveParameterScope()
			{
				if (scope != NULL)
					self->scopes_ = saved_scopes;
			}
		} active_parameter_scope(
			self,
			saved_names != function_parameter_names_.end());
		vector<string> replay_parameter_names;
		vector<string> replay_parameter_pack_names;
		vector<string> replay_empty_pack_names;
		bool generic_has_owner_parameter =
			declaration != NULL &&
			declaration->placeholder != NULL &&
			declaration->placeholder->owner != NULL &&
			declaration->placeholder->owner->kind == ScopeKind::Class &&
			!declaration->placeholder->is_static_member &&
			!type->parameters.empty();
		bool saved_names_have_owner =
			saved_names != function_parameter_names_.end() &&
			!saved_names->second.empty() &&
			saved_names->second[0] == "this";
			for (size_t i = 0; i < type->parameters.size(); ++i)
			{
				TypePtr pattern = type->parameters[i];
				string pack_name;
			TemplateArgument subst;
			size_t name_index = i;
			if (generic_has_owner_parameter &&
			    !saved_names_have_owner &&
			    saved_names != function_parameter_names_.end())
				name_index = i == 0 ? saved_names->second.size() : i - 1;
			string replay_pack_name =
				saved_names != function_parameter_names_.end() &&
				name_index < saved_names->second.size()
				? saved_names->second[name_index] : string();
			bool parameter_pack =
				declaration != NULL &&
				function_parameter_pack_name(declaration, pattern, pack_name);
			if (!parameter_pack)
				parameter_pack =
					function_parameter_type_pack_expansion_name(pattern,
					                                            pack_name);
			if (parameter_pack &&
			    find_template_value_substitution(pack_name, subst) &&
			    subst.kind == TemplateArgumentKind::Pack)
			{
				if (subst.pack.empty() && !replay_pack_name.empty())
					replay_empty_pack_names.push_back(replay_pack_name);
				for (size_t p = 0; p < subst.pack.size(); ++p)
				{
					if (subst.pack[p].kind != TemplateArgumentKind::Type)
						throw runtime_error("type parameter pack required");
					TypePtr element =
					substitute_template_type_parameter(pattern,
						                                   pack_name,
						                                   subst.pack[p].type);
					TypePtr substituted = substitute_template_type(element);
					params.push_back(substituted);
					replay_parameter_pack_names.push_back(replay_pack_name);
					if (replay_pack_name.empty())
						replay_parameter_names.push_back(string());
					else if (p == 0)
						replay_parameter_names.push_back(replay_pack_name);
					else
						replay_parameter_names.push_back(
							replay_pack_name + "__pack" + to_string(p + 1));
					if (active_parameter_scope.scope != NULL &&
					    !replay_parameter_names.back().empty())
						pa11::add_binding(
							active_parameter_scope.scope,
							BindingKind::Parameter,
							replay_parameter_names.back(),
							substituted);
				}
				continue;
			}
				TypePtr substituted = substitute_template_type(pattern);
			params.push_back(substituted);
			replay_parameter_pack_names.push_back(string());
			replay_parameter_names.push_back(replay_pack_name);
			if (active_parameter_scope.scope != NULL &&
			    !replay_pack_name.empty())
				pa11::add_binding(active_parameter_scope.scope,
				                  BindingKind::Parameter,
				                  replay_pack_name,
				                  substituted);
		}
		TypePtr substituted_return;
		TypePtr bare_return = type->base.get() != NULL
			? pa11::strip_cv(type->base) : TypePtr();
		bool replay_with_parameter_scope =
			bare_return.get() != NULL &&
			bare_return->is_dependent_typename &&
		bare_return->dependent_typename_decltype &&
		saved_names != function_parameter_names_.end();
	if (replay_with_parameter_scope)
	{
		vector<Scope*> saved_scopes = self->scopes_;
		vector<map<string, vector<Binding*> > > saved_pack_bindings =
			self->function_parameter_pack_substitutions_;
			Scope* parameter_scope =
				pa11::create_child_scope(self->current_scope(),
				                         ScopeKind::Function,
				                         "");
			map<string, vector<Binding*> > parameter_packs;
			for (size_t i = 0; i < replay_empty_pack_names.size(); ++i)
				parameter_packs[replay_empty_pack_names[i]];
			for (size_t i = 0; i < params.size(); ++i)
			{
				string name;
				if (i < replay_parameter_names.size())
					name = replay_parameter_names[i];
				if (name.empty())
					continue;
				Binding* binding =
				pa11::add_binding(parameter_scope,
					                  BindingKind::Parameter,
					                  name,
					                  params[i]);
				if (i < replay_parameter_pack_names.size() &&
				    !replay_parameter_pack_names[i].empty())
					parameter_packs[replay_parameter_pack_names[i]].
						push_back(binding);
			}
		self->scopes_.push_back(parameter_scope);
		self->function_parameter_pack_substitutions_.push_back(
			parameter_packs);
		try
		{
			substituted_return = substitute_template_type(type->base);
			self->function_parameter_pack_substitutions_ =
				saved_pack_bindings;
			self->scopes_ = saved_scopes;
		}
		catch (...)
		{
			self->function_parameter_pack_substitutions_ =
				saved_pack_bindings;
			self->scopes_ = saved_scopes;
			throw;
		}
	}
	else
		substituted_return = substitute_template_type(type->base);
	TypePtr out = pa11::make_function(substituted_return,
	                                  params,
	                                  type->variadic);
	out->cv = type->cv;
	out->ref_qualifier = type->ref_qualifier;
	return out;
}

}  // namespace internal
}  // namespace pa12
