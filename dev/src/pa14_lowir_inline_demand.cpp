#include "pa14_lowir_internal.h"
#include "pa12_types_support.h"
namespace pa14 {
namespace internal {
namespace {

bool hidden_vbase_vector_contains(const vector<TypePtr>& bases, TypePtr record)
{
	TypePtr bare = record.get() != NULL ? pa11::strip_cv(record) : TypePtr();
	for (size_t i = 0; i < bases.size(); ++i)
		if (pa11::same_type(pa11::strip_cv(bases[i]), bare))
			return true;
	return false;
}

void collect_parameter_virtual_base_member_uses(const Node& node,
                                                const Binding* parameter,
                                                const vector<TypePtr>& all_vbases,
                                                vector<TypePtr>& used)
{
	if (starts_with(node.line, "member-expression") &&
	    node.binding != NULL &&
	    !node.children.empty() &&
	    starts_with(node.children[0].line, "id-expression") &&
	    node.children[0].binding == parameter)
	{
		Binding* member =
			node.binding->aliased_binding != NULL &&
			node.binding->target_scope != NULL
			? node.binding->aliased_binding : node.binding;
		if (!member->is_static_member && member->owner != NULL)
		{
			TypePtr owner = pa11::record_type_for_scope(member->owner);
			owner = owner.get() != NULL ? pa11::strip_cv(owner) : TypePtr();
			for (size_t i = 0; i < all_vbases.size(); ++i)
			{
				TypePtr vbase = pa11::strip_cv(all_vbases[i]);
				if (owner.get() != NULL &&
				    (pa11::same_type(vbase, owner) ||
				     record_has_base_subobject(vbase, owner)) &&
				    !hidden_vbase_vector_contains(used, vbase))
					used.push_back(vbase);
			}
		}
	}
	for (size_t i = 0; i < node.children.size(); ++i)
		collect_parameter_virtual_base_member_uses(node.children[i],
		                                           parameter,
		                                           all_vbases,
		                                           used);
	}

	const Node* recorded_inline_body(const ProgramLowerer& program,
	                                 const Binding* binding)
	{
		map<const Binding*, const Node*>::const_iterator found =
			program.inline_definitions.find(binding);
		if (found != program.inline_definitions.end())
			return found->second;
		map<const Binding*, Node>::const_iterator synthetic =
			program.synthetic_inline_definitions.find(binding);
		return synthetic != program.synthetic_inline_definitions.end()
			? &synthetic->second
			: NULL;
	}

	bool binding_has_recorded_inline_body(const ProgramLowerer& program,
	                                      const Binding* binding)
	{
		return recorded_inline_body(program, binding) != NULL;
	}

	bool recorded_inline_body_shape_matches_binding(
		const ProgramLowerer& program,
		const Binding* binding)
	{
		const Node* body = recorded_inline_body(program, binding);
		if (body == NULL ||
		    binding == NULL ||
		    binding->type.get() == NULL ||
		    binding->type->kind != TypeKind::Function)
			return false;
		size_t parameter_count = 0;
		for (size_t i = 0; i < body->children.size(); ++i)
			if (starts_with(body->children[i].line, "parameter "))
				++parameter_count;
		return parameter_count == binding->type->parameters.size();
	}

	string class_template_family(TypePtr record)
	{
		TypePtr bare = record.get() != NULL ? pa11::strip_cv(record) : TypePtr();
		if (bare.get() == NULL || bare->kind != TypeKind::Record)
			return "";
		return bare->template_primary_name.empty()
			? bare->name : bare->template_primary_name;
	}

	bool alias_member_shape_matches(const Binding* concrete,
	                                const Binding* candidate)
	{
		if (concrete == NULL ||
		    candidate == NULL ||
		    concrete->name != candidate->name ||
		    concrete->is_static_member != candidate->is_static_member ||
		    concrete->type.get() == NULL ||
		    candidate->type.get() == NULL ||
		    concrete->type->kind != TypeKind::Function ||
		    candidate->type->kind != TypeKind::Function ||
		    concrete->type->parameters.size() !=
			    candidate->type->parameters.size())
			return false;
		TypePtr concrete_owner = class_record_for_member(concrete);
		TypePtr candidate_owner = class_record_for_member(candidate);
		concrete_owner = concrete_owner.get() != NULL
			? pa11::strip_cv(concrete_owner) : TypePtr();
		candidate_owner = candidate_owner.get() != NULL
			? pa11::strip_cv(candidate_owner) : TypePtr();
		if (concrete_owner.get() == NULL ||
		    candidate_owner.get() == NULL ||
		    !concrete_owner->is_template_specialization)
			return false;
		string concrete_family = class_template_family(concrete_owner);
		return !concrete_family.empty() &&
		       concrete_family == class_template_family(candidate_owner) &&
		       !pa11::same_type(concrete_owner, candidate_owner);
	}

	const Binding* find_concrete_member_alias_body(
		const ProgramLowerer& program,
		const Binding* binding)
	{
		if (binding == NULL ||
		    binding->kind != BindingKind::Function ||
		    binding->aliased_binding != NULL ||
		    binding_has_recorded_inline_body(program, binding))
			return NULL;
		for (map<const Binding*, const Node*>::const_iterator it =
			     program.inline_definitions.begin();
		     it != program.inline_definitions.end();
		     ++it)
		{
			if (recorded_inline_body_shape_matches_binding(program,
			                                               it->first) &&
			    alias_member_shape_matches(binding, it->first))
				return it->first;
		}
		for (map<const Binding*, Node>::const_iterator it =
			     program.synthetic_inline_definitions.begin();
		     it != program.synthetic_inline_definitions.end();
		     ++it)
			if (recorded_inline_body_shape_matches_binding(program,
			                                               it->first) &&
			    alias_member_shape_matches(binding, it->first))
				return it->first;
		return NULL;
	}

	bool explicit_alias_specialization_symbol(const Binding* binding)
	{
		return binding != NULL &&
		       binding->kind == BindingKind::Function &&
		       binding->aliased_binding != NULL &&
		       !binding->function_specialization_symbol.empty() &&
		       (binding->aliased_binding->function_specialization_symbol.empty() ||
		        binding->aliased_binding->function_specialization_symbol !=
			        binding->function_specialization_symbol);
	}

	bool concrete_class_template_alias_body(const Binding* binding)
	{
		if (binding == NULL ||
		    binding->kind != BindingKind::Function ||
		    binding->aliased_binding == NULL)
			return false;
		TypePtr owner = class_record_for_member(binding);
		TypePtr alias_owner = class_record_for_member(binding->aliased_binding);
		owner = owner.get() != NULL ? pa11::strip_cv(owner) : TypePtr();
		alias_owner = alias_owner.get() != NULL
			? pa11::strip_cv(alias_owner) : TypePtr();
		return owner.get() != NULL &&
		       alias_owner.get() != NULL &&
		       owner->kind == TypeKind::Record &&
		       alias_owner->kind == TypeKind::Record &&
		       owner->is_template_specialization &&
		       !pa11::same_type(owner, alias_owner);
	}

	bool concrete_alias_body_needs_own_definition(const Binding* binding)
	{
		return explicit_alias_specialization_symbol(binding) ||
		       concrete_class_template_alias_body(binding);
	}

		void replace_node_binding_refs(Node& node,
		                               const map<Binding*, Binding*>& replacements)
		{
			if (node.binding != NULL)
			{
				map<Binding*, Binding*>::const_iterator found =
					replacements.find(node.binding);
				if (found != replacements.end())
					node.binding = found->second;
			}
			if (node.direct_call != NULL)
			{
				map<Binding*, Binding*>::const_iterator found =
					replacements.find(node.direct_call);
				if (found != replacements.end())
					node.direct_call = found->second;
			}
		for (size_t i = 0; i < node.overloads.size(); ++i)
		{
			map<Binding*, Binding*>::const_iterator found =
				replacements.find(node.overloads[i]);
			if (found != replacements.end())
				node.overloads[i] = found->second;
		}
		if (!node.explicit_template_arguments.empty())
		{
			map<Binding*, vector<pa12::internal::TemplateArgument> > updated;
			for (map<Binding*,
			         vector<pa12::internal::TemplateArgument> >::const_iterator it =
				     node.explicit_template_arguments.begin();
			     it != node.explicit_template_arguments.end();
			     ++it)
			{
				Binding* key = it->first;
				map<Binding*, Binding*>::const_iterator found =
					replacements.find(key);
				if (found != replacements.end())
					key = found->second;
				updated[key] = it->second;
			}
			node.explicit_template_arguments.swap(updated);
		}
		for (size_t i = 0; i < node.children.size(); ++i)
			replace_node_binding_refs(node.children[i], replacements);
	}

	void adapt_function_parameters_for_binding(ProgramLowerer& program,
	                                           Node& fn,
	                                           const Binding* binding)
	{
		if (binding == NULL ||
		    binding->type.get() == NULL ||
		    binding->type->kind != TypeKind::Function)
			return;
		map<Binding*, Binding*> replacements;
		size_t param_index = 0;
		for (size_t i = 0; i < fn.children.size() &&
		     param_index < binding->type->parameters.size(); ++i)
		{
			if (!starts_with(fn.children[i].line, "parameter "))
				continue;
			Binding* source = fn.children[i].binding;
			TypePtr param_type = binding->type->parameters[param_index++];
			if (source != NULL)
			{
				unique_ptr<Binding> cloned(new Binding(*source));
				cloned->type = param_type;
				Binding* replacement = cloned.get();
				program.synthetic_bindings.push_back(move(cloned));
				replacements[source] = replacement;
				fn.children[i].binding = replacement;
			}
			fn.children[i].type = param_type;
			string text = fn.children[i].line.substr(10);
			size_t space = text.find(' ');
			string name = space == string::npos ? text : text.substr(0, space);
			fn.children[i].line =
				"parameter " + name + " " + pa11::describe_type(param_type);
		}
		if (!replacements.empty())
			replace_node_binding_refs(fn, replacements);
	}

	void seed_alias_owner_type_substitutions(
		const Binding* binding,
		const Binding* alias,
		map<string, TypePtr>& substitutions);

	void seed_alias_function_type_substitutions(
		const Binding* binding,
		const Binding* alias,
		map<string, TypePtr>& substitutions);

	void seed_alias_body_parameter_substitutions(
		const Node& fn,
		const Binding* binding,
		map<string, TypePtr>& substitutions);

		void substitute_alias_node_types(ProgramLowerer& program,
		                                 Node& node,
		                                 const map<string, TypePtr>& substitutions,
		                                 map<Binding*, Binding*>& replacements,
		                                 Scope* concrete_owner,
		                                 Scope* alias_owner);

	bool materialize_concrete_alias_inline_body(ProgramLowerer& program,
	                                            const Binding* binding)
	{
		if (!concrete_alias_body_needs_own_definition(binding))
			return false;
		const Node* alias_body =
			recorded_inline_body(program, binding->aliased_binding);
		if (alias_body == NULL ||
		    !recorded_inline_body_shape_matches_binding(
			    program,
			    binding->aliased_binding))
			return false;
		Node adapted = *alias_body;
		adapted.binding = const_cast<Binding*>(binding);
		adapted.type = binding->type;
		map<string, TypePtr> substitutions;
		seed_alias_owner_type_substitutions(binding,
		                                    binding->aliased_binding,
		                                    substitutions);
		seed_alias_function_type_substitutions(binding,
		                                       binding->aliased_binding,
		                                       substitutions);
		seed_alias_body_parameter_substitutions(adapted,
		                                        binding,
		                                        substitutions);
		if (!substitutions.empty())
		{
				map<Binding*, Binding*> replacements;
				substitute_alias_node_types(program,
				                            adapted,
				                            substitutions,
				                            replacements,
				                            binding->owner,
				                            binding->aliased_binding->owner);
			}
		adapt_function_parameters_for_binding(program, adapted, binding);
		program.synthetic_inline_definitions[binding] = adapted;
		program.inline_definitions[binding] =
			&program.synthetic_inline_definitions[binding];
		return true;
	}

	string simple_type_substitution_key(TypePtr type)
	{
		TypePtr bare = type.get() != NULL ? pa11::strip_cv(type) : TypePtr();
		if (bare.get() == NULL)
			return "";
		if (bare->kind == TypeKind::TemplateParameter ||
		    bare->kind == TypeKind::TemplateTemplateParameter)
			return bare->name;
		if (bare->is_dependent_typename &&
		    !bare->dependent_typename_qualified &&
		    !bare->dependent_typename_template_id &&
		    !bare->dependent_typename_decltype)
			return !bare->template_primary_name.empty()
				? bare->template_primary_name : bare->name;
		return "";
	}

	TypePtr hosted_pointer_traits_rebind_type(
		TypePtr type,
		const vector<vector<pa11::TemplateInstanceArgument> >& lists)
	{
		TypePtr bare = type.get() != NULL ? pa11::strip_cv(type) : TypePtr();
		if (bare.get() == NULL ||
		    !bare->is_dependent_typename ||
		    !bare->dependent_typename_template_id ||
		    bare->template_primary_name != "pointer_traits" ||
		    bare->name.find("rebind") == string::npos ||
		    lists.empty() ||
		    lists.back().empty() ||
		    lists.back()[0].kind != pa11::TemplateInstanceArgumentKind::Type)
			return TypePtr();
		TypePtr rebound = lists.back()[0].type;
		if (rebound.get() == NULL)
			return TypePtr();
		TypePtr pointer = pa11::make_pointer(rebound);
		return type->cv == pa11::CV_NONE
			? pointer
			: pa11::make_cv(pointer, type->cv);
	}

	pa11::TemplateInstanceArgument substitute_alias_template_argument(
		const pa11::TemplateInstanceArgument& argument,
		const map<string, TypePtr>& substitutions,
		bool& changed);

	void seed_alias_type_match_substitutions(
		TypePtr pattern,
		TypePtr actual,
		map<string, TypePtr>& substitutions);

	void seed_alias_argument_match_substitutions(
		const pa11::TemplateInstanceArgument& pattern,
		const pa11::TemplateInstanceArgument& actual,
		map<string, TypePtr>& substitutions)
	{
		if (pattern.kind == pa11::TemplateInstanceArgumentKind::Type &&
		    actual.kind == pa11::TemplateInstanceArgumentKind::Type)
			seed_alias_type_match_substitutions(pattern.type,
			                                    actual.type,
			                                    substitutions);
		else if (pattern.kind == pa11::TemplateInstanceArgumentKind::Value &&
		         actual.kind == pa11::TemplateInstanceArgumentKind::Value)
			seed_alias_type_match_substitutions(pattern.type,
			                                    actual.type,
			                                    substitutions);
		else if (pattern.kind == pa11::TemplateInstanceArgumentKind::Pack &&
		         actual.kind == pa11::TemplateInstanceArgumentKind::Pack)
		{
			size_t count = min(pattern.pack.size(), actual.pack.size());
			for (size_t i = 0; i < count; ++i)
				seed_alias_argument_match_substitutions(pattern.pack[i],
				                                        actual.pack[i],
				                                        substitutions);
		}
	}

	void seed_alias_type_match_substitutions(
		TypePtr pattern,
		TypePtr actual,
		map<string, TypePtr>& substitutions)
	{
		TypePtr p = pattern.get() != NULL ? pa11::strip_cv(pattern) : TypePtr();
		TypePtr a = actual.get() != NULL ? pa11::strip_cv(actual) : TypePtr();
		if (p.get() == NULL || a.get() == NULL)
			return;
		string key = simple_type_substitution_key(p);
		if (!key.empty())
		{
			substitutions[key] = actual;
			return;
		}
		if (p->kind != a->kind)
			return;
		switch (p->kind)
		{
		case TypeKind::Pointer:
		case TypeKind::LValueReference:
		case TypeKind::RValueReference:
		case TypeKind::Array:
			seed_alias_type_match_substitutions(p->base,
			                                    a->base,
			                                    substitutions);
			break;
		case TypeKind::Function:
		{
			seed_alias_type_match_substitutions(p->base,
			                                    a->base,
			                                    substitutions);
			size_t count = min(p->parameters.size(), a->parameters.size());
			for (size_t i = 0; i < count; ++i)
				seed_alias_type_match_substitutions(p->parameters[i],
				                                    a->parameters[i],
				                                    substitutions);
			break;
		}
		case TypeKind::MemberPointer:
			seed_alias_type_match_substitutions(p->member_class,
			                                    a->member_class,
			                                    substitutions);
			seed_alias_type_match_substitutions(p->base,
			                                    a->base,
			                                    substitutions);
			break;
		case TypeKind::Record:
		{
			size_t count = min(p->template_arguments.size(),
			                   a->template_arguments.size());
			for (size_t i = 0; i < count; ++i)
				seed_alias_argument_match_substitutions(
					p->template_arguments[i],
					a->template_arguments[i],
					substitutions);
			break;
		}
		default:
			break;
		}
	}

	void seed_alias_function_type_substitutions(
		const Binding* binding,
		const Binding* alias,
		map<string, TypePtr>& substitutions)
	{
		if (binding == NULL ||
		    alias == NULL ||
		    binding->type.get() == NULL ||
		    alias->type.get() == NULL ||
		    binding->type->kind != TypeKind::Function ||
		    alias->type->kind != TypeKind::Function)
			return;
		seed_alias_type_match_substitutions(alias->type,
		                                    binding->type,
		                                    substitutions);
	}

	void seed_alias_body_parameter_substitutions(
		const Node& fn,
		const Binding* binding,
		map<string, TypePtr>& substitutions)
	{
		if (binding == NULL ||
		    binding->type.get() == NULL ||
		    binding->type->kind != TypeKind::Function)
			return;
		size_t param_index = 0;
		for (size_t i = 0; i < fn.children.size() &&
		     param_index < binding->type->parameters.size(); ++i)
		{
			if (!starts_with(fn.children[i].line, "parameter "))
				continue;
			seed_alias_type_match_substitutions(
				fn.children[i].type,
				binding->type->parameters[param_index],
				substitutions);
			++param_index;
		}
	}

	TypePtr substitute_alias_type(TypePtr type,
	                              const map<string, TypePtr>& substitutions,
	                              bool& changed)
	{
		if (type.get() == NULL || substitutions.empty())
			return type;
		if (type->kind == TypeKind::Cv)
		{
			bool base_changed = false;
			TypePtr base = substitute_alias_type(type->base,
			                                     substitutions,
			                                     base_changed);
			if (!base_changed)
				return type;
			changed = true;
			return pa11::make_cv(base, type->cv);
		}
		string key = simple_type_substitution_key(type);
		map<string, TypePtr>::const_iterator subst =
			substitutions.find(key);
		if (subst != substitutions.end())
		{
			changed = true;
			return type->cv == pa11::CV_NONE
				? subst->second
				: pa11::make_cv(subst->second, type->cv);
		}
		bool local_changed = false;
		TypePtr base = substitute_alias_type(type->base, substitutions,
		                                     local_changed);
		TypePtr member_class = substitute_alias_type(type->member_class,
		                                             substitutions,
		                                             local_changed);
		vector<TypePtr> parameters = type->parameters;
		for (size_t i = 0; i < parameters.size(); ++i)
			parameters[i] = substitute_alias_type(parameters[i],
			                                     substitutions,
			                                     local_changed);
		vector<pa11::TemplateInstanceArgument> template_arguments =
			type->template_arguments;
		for (size_t i = 0; i < template_arguments.size(); ++i)
			template_arguments[i] =
				substitute_alias_template_argument(template_arguments[i],
				                                   substitutions,
				                                   local_changed);
		vector<vector<pa11::TemplateInstanceArgument> > dependent_lists =
			type->dependent_typename_template_argument_lists;
		for (size_t i = 0; i < dependent_lists.size(); ++i)
			for (size_t j = 0; j < dependent_lists[i].size(); ++j)
				dependent_lists[i][j] =
					substitute_alias_template_argument(dependent_lists[i][j],
					                                   substitutions,
					                                   local_changed);
		TypePtr hosted_rebind =
			hosted_pointer_traits_rebind_type(type, dependent_lists);
		if (hosted_rebind.get() != NULL)
		{
			changed = true;
			return hosted_rebind;
		}
		if (!local_changed)
			return type;
		TypePtr out(new pa11::Type(*type));
		out->base = base;
		out->member_class = member_class;
		out->parameters = parameters;
		out->template_arguments = template_arguments;
		out->dependent_typename_template_argument_lists = dependent_lists;
		changed = true;
		return out;
	}

	pa11::TemplateInstanceArgument substitute_alias_template_argument(
		const pa11::TemplateInstanceArgument& argument,
		const map<string, TypePtr>& substitutions,
		bool& changed)
	{
		pa11::TemplateInstanceArgument out = argument;
		if (out.kind == pa11::TemplateInstanceArgumentKind::Type)
			out.type = substitute_alias_type(out.type,
			                                 substitutions,
			                                 changed);
		else if (out.kind == pa11::TemplateInstanceArgumentKind::Pack)
			for (size_t i = 0; i < out.pack.size(); ++i)
				out.pack[i] = substitute_alias_template_argument(out.pack[i],
				                                                 substitutions,
				                                                 changed);
		for (size_t i = 0; i < out.value_owner_template_arguments.size(); ++i)
			out.value_owner_template_arguments[i] =
				substitute_alias_template_argument(
					out.value_owner_template_arguments[i],
					substitutions,
					changed);
		if (out.kind == pa11::TemplateInstanceArgumentKind::Value)
			out.type = substitute_alias_type(out.type,
			                                 substitutions,
			                                 changed);
		return out;
	}

	void seed_alias_call_argument_substitutions(
		const Node& node,
		map<string, TypePtr>& substitutions)
	{
		if (!starts_with(node.line, "call-expression") ||
		    node.children.empty() ||
		    node.children[0].binding == NULL ||
		    node.children[0].binding->type.get() == NULL ||
		    node.children[0].binding->type->kind != TypeKind::Function)
			return;
		TypePtr function = node.children[0].binding->type;
		size_t count = min(function->parameters.size(),
		                   node.children.size() - 1);
		for (size_t i = 0; i < count; ++i)
		{
			TypePtr pattern = function->parameters[i];
			TypePtr actual = node.children[i + 1].type;
			bool changed = false;
			actual = substitute_alias_type(actual, substitutions, changed);
			TypePtr bare_pattern = pattern.get() != NULL
				? pa11::strip_cv(pattern) : TypePtr();
			if (bare_pattern.get() != NULL &&
			    (bare_pattern->kind == TypeKind::LValueReference ||
			     bare_pattern->kind == TypeKind::RValueReference))
				pattern = bare_pattern->base;
			seed_alias_type_match_substitutions(pattern,
			                                    actual,
			                                    substitutions);
		}
	}

	string alias_member_expression_name(const Node& node)
	{
		size_t op = node.line.find("OP_DOT:");
		size_t prefix = 7;
		if (op == string::npos)
		{
			op = node.line.find("OP_ARROW:");
			prefix = 9;
		}
		if (op == string::npos)
			return "";
		string name = node.line.substr(op + prefix);
		size_t space = name.find(' ');
		if (space != string::npos)
			name = name.substr(0, space);
		return name;
	}

	bool alias_function_template_specialization(const Binding* binding)
	{
		return binding != NULL &&
		       (!binding->function_specialization_symbol.empty() ||
		        (binding->aliased_binding != NULL &&
		         !binding->aliased_binding->function_specialization_symbol.empty()));
	}

	void collect_alias_members_in_record(TypePtr record,
	                                     const string& name,
	                                     set<const void*>& seen,
	                                     vector<Binding*>& out)
	{
		TypePtr bare = record.get() != NULL ? pa11::strip_cv(record) : TypePtr();
		if (bare.get() == NULL ||
		    bare->kind != TypeKind::Record ||
		    !seen.insert(bare.get()).second)
			return;
		if (bare->scope != NULL)
		{
			map<string, vector<Binding*> >::const_iterator found =
				bare->scope->members.find(name);
			if (found != bare->scope->members.end())
				for (size_t i = 0; i < found->second.size(); ++i)
					out.push_back(found->second[i]);
		}
		for (size_t i = 0; i < bare->direct_bases.size(); ++i)
			collect_alias_members_in_record(bare->direct_bases[i],
			                                name,
			                                seen,
			                                out);
		if (bare->base.get() != NULL)
			collect_alias_members_in_record(bare->base, name, seen, out);
	}

	Binding* find_alias_member_in_record(TypePtr record,
	                                     const string& name,
	                                     set<const void*>& seen)
	{
		vector<Binding*> members;
		collect_alias_members_in_record(record, name, seen, members);
		for (size_t i = 0; i < members.size(); ++i)
			if (members[i]->kind != BindingKind::Function)
				return members[i];
		if (members.size() == 1)
			return members[0];
		return NULL;
	}

	TypePtr alias_member_object_type(const Node& callee)
	{
		if (callee.children.empty())
			return TypePtr();
		TypePtr object = callee.children[0].type;
		if (object.get() == NULL)
			return TypePtr();
		if (object->kind == TypeKind::LValueReference ||
		    object->kind == TypeKind::RValueReference)
			object = object->base;
		TypePtr bare = object.get() != NULL
			? pa11::strip_cv(object) : TypePtr();
		if (bare.get() != NULL &&
		    bare->kind == TypeKind::Pointer &&
		    callee.line.find("OP_ARROW:") != string::npos)
			object = bare->base;
		return object;
	}

	bool alias_member_function_this_matches(Binding* fn, TypePtr object)
	{
		if (fn == NULL ||
		    fn->is_static_member ||
		    fn->owner == NULL ||
		    fn->owner->kind != ScopeKind::Class)
			return true;
		if (fn->type.get() == NULL ||
		    fn->type->kind != TypeKind::Function ||
		    fn->type->parameters.empty())
			return false;
		TypePtr this_param = pa11::strip_cv(fn->type->parameters[0]);
		if (this_param.get() == NULL ||
		    this_param->kind != TypeKind::Pointer)
			return false;
		TypePtr this_object = this_param->base;
		if (object.get() != NULL &&
		    pa11::type_has_const(object) &&
		    !pa11::type_has_const(this_object))
			return false;
		return true;
	}

	bool alias_member_function_arity_matches(Binding* fn, size_t call_args)
	{
		if (fn == NULL ||
		    fn->type.get() == NULL ||
		    fn->type->kind != TypeKind::Function)
			return false;
		size_t implicit_this =
			fn->owner != NULL &&
			fn->owner->kind == ScopeKind::Class &&
			!fn->is_static_member ? 1 : 0;
		size_t expected = call_args + implicit_this;
		if (fn->type->parameters.size() == expected)
			return true;
		return fn->type->variadic && fn->type->parameters.size() <= expected;
	}

	Binding* resolve_alias_member_call_binding(const Node& node)
	{
		if (!starts_with(node.line, "call-expression") ||
		    node.children.empty())
			return NULL;
		const Node& callee = node.children[0];
		if (!starts_with(callee.line, "member-expression") ||
		    callee.binding != NULL)
			return NULL;
		string name = alias_member_expression_name(callee);
		if (name.empty())
			return NULL;
		TypePtr object = alias_member_object_type(callee);
		TypePtr record = object.get() != NULL ? pa11::strip_cv(object) : TypePtr();
		if (record.get() == NULL ||
		    record->kind != TypeKind::Record ||
		    record->scope == NULL)
			return NULL;
		vector<Binding*> members;
		set<const void*> seen;
		collect_alias_members_in_record(record, name, seen, members);
		size_t call_args = node.children.size() - 1;
		Binding* best = NULL;
		Binding* best_template = NULL;
		for (size_t i = 0; i < members.size(); ++i)
		{
			Binding* fn = members[i];
			if (fn->kind != BindingKind::Function ||
			    !alias_member_function_arity_matches(fn, call_args) ||
			    !alias_member_function_this_matches(fn, object))
				continue;
			if (!alias_function_template_specialization(fn))
			{
				if (best == NULL)
					best = fn;
			}
			else if (best_template == NULL)
				best_template = fn;
		}
		return best != NULL ? best : best_template;
	}

	Binding* resolve_alias_member_expression_binding(const Node& node)
	{
		if (!starts_with(node.line, "member-expression") ||
		    node.binding != NULL ||
		    node.children.empty())
			return NULL;
		string name = alias_member_expression_name(node);
		if (name.empty())
			return NULL;
		TypePtr object = node.children[0].type;
		object = object.get() != NULL ? pa11::strip_cv(object) : TypePtr();
		if (object.get() == NULL)
			return NULL;
		if (object->kind == TypeKind::Pointer ||
		    object->kind == TypeKind::LValueReference ||
		    object->kind == TypeKind::RValueReference)
			object = pa11::strip_cv(object->base);
		if (object.get() == NULL ||
		    object->kind != TypeKind::Record ||
		    object->scope == NULL)
			return NULL;
		set<const void*> seen;
		Binding* member = find_alias_member_in_record(object, name, seen);
		if (member != NULL)
			return member;
		bool tree_node_base_member =
			name == "_M_base_ptr" ||
			name == "_M_parent" ||
			name == "_M_left" ||
			name == "_M_right" ||
			name == "_M_color";
		if (!tree_node_base_member || object->scope == NULL)
			return NULL;
		for (Scope* scope = object->scope; scope != NULL; scope = scope->parent)
		{
			map<string, vector<Binding*> >::const_iterator found =
				scope->members.find("_Rb_tree_node_base");
			if (found == scope->members.end())
				continue;
			for (size_t i = 0; i < found->second.size(); ++i)
			{
				TypePtr type = found->second[i]->type;
				type = type.get() != NULL ? pa11::strip_cv(type) : TypePtr();
				if (type.get() == NULL || type->kind != TypeKind::Record)
					continue;
				seen.clear();
				member = find_alias_member_in_record(type, name, seen);
				if (member != NULL)
					return member;
			}
		}
		return NULL;
	}

	void seed_alias_owner_type_substitutions(
		const Binding* binding,
		const Binding* alias,
		map<string, TypePtr>& substitutions)
	{
		TypePtr pattern = class_record_for_member(alias);
		TypePtr actual = class_record_for_member(binding);
		pattern = pattern.get() != NULL ? pa11::strip_cv(pattern) : TypePtr();
		actual = actual.get() != NULL ? pa11::strip_cv(actual) : TypePtr();
		if (pattern.get() == NULL ||
		    actual.get() == NULL ||
		    pattern->template_arguments.size() !=
			    actual->template_arguments.size())
			return;
		for (size_t i = 0; i < pattern->template_arguments.size(); ++i)
		{
			const pa11::TemplateInstanceArgument& p =
				pattern->template_arguments[i];
			const pa11::TemplateInstanceArgument& a =
				actual->template_arguments[i];
			if (p.kind != pa11::TemplateInstanceArgumentKind::Type ||
			    a.kind != pa11::TemplateInstanceArgumentKind::Type)
				continue;
			string key = simple_type_substitution_key(p.type);
			if (!key.empty() && a.type.get() != NULL)
				substitutions[key] = a.type;
		}
	}

	Binding* substituted_alias_binding(ProgramLowerer& program,
	                                   Binding* binding,
	                                   const map<string, TypePtr>& substitutions,
	                                   map<Binding*, Binding*>& replacements,
	                                   Scope* concrete_owner,
	                                   Scope* alias_owner)
	{
		if (binding == NULL || substitutions.empty())
			return binding;
		if (binding->kind == BindingKind::Type ||
		    binding->kind == BindingKind::TypeAlias)
			return binding;
		bool changed = false;
		TypePtr type = substitute_alias_type(binding->type,
		                                     substitutions,
		                                     changed);
		bool owner_changed =
			binding->kind == BindingKind::Function &&
			binding->owner != NULL &&
			binding->owner == alias_owner &&
			concrete_owner != NULL;
		if (!changed && !owner_changed)
			return binding;
		map<Binding*, Binding*>::const_iterator found =
			replacements.find(binding);
		if (found != replacements.end())
		{
			bool type_matches =
				!changed ||
				(found->second->type.get() != NULL &&
				 type.get() != NULL &&
				 pa11::same_type(found->second->type, type));
			bool owner_matches =
				!owner_changed || found->second->owner == concrete_owner;
			if (type_matches && owner_matches)
				return found->second;
		}
			unique_ptr<Binding> cloned(new Binding(*binding));
			if (changed)
				cloned->type = type;
			if (owner_changed)
				cloned->owner = concrete_owner;
			if (binding->kind == BindingKind::Function)
				cloned->function_specialization_symbol.clear();
			Binding* replacement = cloned.get();
			program.synthetic_bindings.push_back(move(cloned));
			replacements[binding] = replacement;
		return replacement;
	}

		void substitute_alias_node_types(ProgramLowerer& program,
		                                 Node& node,
		                                 const map<string, TypePtr>& substitutions,
		                                 map<Binding*, Binding*>& replacements,
		                                 Scope* concrete_owner,
		                                 Scope* alias_owner)
		{
			map<string, TypePtr> local_substitutions = substitutions;
			seed_alias_call_argument_substitutions(node, local_substitutions);
			bool changed = false;
			if (starts_with(node.line, "call-expression") &&
			    !node.children.empty() &&
			    node.children[0].binding != NULL &&
			    node.children[0].binding->type.get() != NULL &&
			    node.children[0].binding->type->kind == TypeKind::Function)
			{
				node.type = substitute_alias_type(
					node.children[0].binding->type->base,
					local_substitutions,
					changed);
			}
			else
				node.type = substitute_alias_type(node.type,
				                                  local_substitutions,
				                                  changed);
			node.binding = substituted_alias_binding(program,
			                                         node.binding,
			                                         local_substitutions,
			                                         replacements,
			                                         concrete_owner,
			                                         alias_owner);
			node.direct_call = substituted_alias_binding(program,
			                                             node.direct_call,
			                                             local_substitutions,
			                                             replacements,
			                                             concrete_owner,
			                                             alias_owner);
			for (size_t i = 0; i < node.overloads.size(); ++i)
				node.overloads[i] = substituted_alias_binding(program,
				                                              node.overloads[i],
				                                              local_substitutions,
				                                              replacements,
				                                              concrete_owner,
				                                              alias_owner);
			for (size_t i = 0; i < node.children.size(); ++i)
				substitute_alias_node_types(program,
				                            node.children[i],
				                            local_substitutions,
				                            replacements,
				                            concrete_owner,
				                            alias_owner);
			Binding* resolved_member =
				resolve_alias_member_expression_binding(node);
			if (resolved_member != NULL)
			{
				node.binding = substituted_alias_binding(program,
				                                        resolved_member,
				                                        local_substitutions,
				                                        replacements,
				                                        concrete_owner,
				                                        alias_owner);
				if (node.binding != NULL)
					node.type = node.binding->type;
			}
			if (starts_with(node.line, "call-expression") &&
			    !node.children.empty() &&
			    node.children[0].binding == NULL)
			{
				Binding* resolved_call =
					resolve_alias_member_call_binding(node);
				if (resolved_call != NULL)
				{
					node.children[0].binding =
						substituted_alias_binding(program,
						                         resolved_call,
						                         local_substitutions,
						                         replacements,
						                         concrete_owner,
						                         alias_owner);
					if (node.children[0].binding != NULL)
						node.children[0].type =
							node.children[0].binding->type;
				}
			}
			if (starts_with(node.line, "call-expression") &&
			    !node.children.empty() &&
			    node.children[0].binding != NULL &&
			    node.children[0].binding->type.get() != NULL &&
			    node.children[0].binding->type->kind == TypeKind::Function)
			{
				bool result_changed = false;
				node.direct_call = node.children[0].binding;
				node.type = substitute_alias_type(
					node.children[0].binding->type->base,
					local_substitutions,
					result_changed);
			}
			if (starts_with(node.line, "assignment-expression") &&
			    !node.children.empty())
				node.type = node.children[0].type;
			if (starts_with(node.line, "cast-expression") &&
			    !node.children.empty() &&
			    node.type.get() != NULL &&
			    pa12::internal::type_structurally_dependent(node.type))
				node.type = node.children[0].type;
		}

}  // namespace

namespace {

const Binding* resolve_inline_alias_demand_binding(ProgramLowerer& program,
                                                   const Binding* binding)
{
	if (binding != NULL &&
	    binding->kind == BindingKind::Function &&
	    binding->aliased_binding == NULL)
	{
		const Binding* alias =
			find_concrete_member_alias_body(program, binding);
		if (alias != NULL)
			const_cast<Binding*>(binding)->aliased_binding =
				const_cast<Binding*>(alias);
	}
	if (binding != NULL &&
	    binding->kind == BindingKind::Function &&
	    binding->aliased_binding != NULL)
	{
		bool binding_has_body =
			binding_has_recorded_inline_body(program, binding);
		bool alias_has_body =
			binding_has_recorded_inline_body(program,
			                                 binding->aliased_binding);
		if (!binding_has_body &&
		    alias_has_body &&
		    concrete_alias_body_needs_own_definition(binding))
			binding_has_body =
				materialize_concrete_alias_inline_body(program, binding);
		if (!binding_has_body &&
		    (binding->aliased_binding->is_inline_definition ||
		     alias_has_body))
			binding = binding->aliased_binding;
	}
	return binding;
}

}  // namespace

vector<TypePtr> ProgramLowerer::hidden_virtual_bases_for_function_parameter(
	const Binding* binding,
	size_t parameter_index,
	TypePtr type)
{
	vector<TypePtr> defaults = hidden_virtual_bases_for_parameter(type);
	if (defaults.empty() || binding == NULL)
		return defaults;
	pair<const Binding*, size_t> key(binding, parameter_index);
	map<pair<const Binding*, size_t>, vector<TypePtr> >::const_iterator cached =
		hidden_parameter_virtual_bases.find(key);
	if (cached != hidden_parameter_virtual_bases.end())
		return cached->second;
	vector<TypePtr> selected = defaults;
	const Node* fn = NULL;
	map<const Binding*, const Node*>::const_iterator found =
		inline_definitions.find(binding);
	if (found != inline_definitions.end())
		fn = found->second;
	map<const Binding*, Node>::const_iterator synthetic =
		synthetic_inline_definitions.find(binding);
	if (fn == NULL && synthetic != synthetic_inline_definitions.end())
		fn = &synthetic->second;
	if (fn != NULL)
	{
		Binding* param_binding = NULL;
		size_t param = 0;
		for (size_t i = 0; i < fn->children.size(); ++i)
		{
			if (!starts_with(fn->children[i].line, "parameter "))
				continue;
			if (param == parameter_index)
			{
				param_binding = fn->children[i].binding;
				break;
			}
			++param;
		}
		TypePtr bare = pa11::strip_cv(type);
		bool record_reference =
			(bare->kind == TypeKind::LValueReference ||
			 bare->kind == TypeKind::RValueReference) &&
			pa11::strip_cv(bare->base)->kind == TypeKind::Record;
		bool record_pointer =
			bare->kind == TypeKind::Pointer &&
			pa11::strip_cv(bare->base)->kind == TypeKind::Record;
		if (param_binding != NULL && (record_reference || record_pointer))
		{
			vector<TypePtr> used;
			collect_parameter_virtual_base_member_uses(*fn,
			                                           param_binding,
			                                           defaults,
			                                           used);
			if (record_pointer)
				selected = used;
			else if (!used.empty())
				selected = used;
		}
	}
	hidden_parameter_virtual_bases[key] = selected;
	return selected;
}

	void ProgramLowerer::demand_inline_function(const Binding* binding,
	                                            bool complete_entry)
	{
		binding = resolve_inline_alias_demand_binding(*this, binding);
		if (binding == NULL)
			return;
		if (function_signature_has_unresolved_storage(binding))
			return;
	if (lowir_extern_template_class_external_binding(binding))
	{
		demand_function_declaration(binding);
		return;
	}
		bool has_recorded_body =
			inline_definitions.find(binding) != inline_definitions.end() ||
			synthetic_inline_definitions.find(binding) !=
				synthetic_inline_definitions.end();
		if (!has_recorded_body)
	{
		string wanted_name = symbol_for(binding);
		string wanted_object = global_object_symbol(binding);
		for (map<const Binding*, const Node*>::const_iterator it =
			     inline_definitions.begin();
		     it != inline_definitions.end();
		     ++it)
		{
			string candidate_object = global_object_symbol(it->first);
			if (it->first == NULL ||
			    it->first->kind != BindingKind::Function ||
			    (symbol_for(it->first) != wanted_name &&
			     (wanted_object.empty() ||
			      candidate_object.empty() ||
			      candidate_object != wanted_object)))
				continue;
			if (it->first != binding)
				symbols[binding] = symbol_for(it->first);
			binding = it->first;
			has_recorded_body = true;
			break;
		}
	}
	if (!binding->is_inline_definition)
	{
		if (!has_recorded_body &&
		    lowir_synthesizable_noop_constructor(binding))
		{
			string name = symbol_for(binding);
			emit_generated_empty_constructor(
				binding,
				complete_entry ? name : name + "__base_entry");
		}
		if (!has_recorded_body)
			return;
	}
	bool class_ctor = is_class_constructor_binding(binding);
	bool class_dtor = is_class_destructor_binding(binding);
	if (complete_entry)
		demanded_inline_complete_entries.insert(binding);
	else if (!class_ctor && !class_dtor)
		return;
	else if (class_ctor &&
	         !binding->is_generated_default_constructor &&
	         !binding->is_generated_aggregate_constructor &&
	         !binding->is_generated_copy_move_constructor)
	{
		TypePtr active_record =
			active_inline_definition != NULL
			? class_record_for_member(active_inline_definition)
			: TypePtr();
		active_record = active_record.get() != NULL
			? pa11::strip_cv(active_record) : TypePtr();
		if (active_record.get() != NULL &&
		    active_record->kind == TypeKind::Record &&
		    !pa11::record_virtual_bases(active_record).empty())
			demanded_inline_complete_entries.insert(binding);
	}
	demand_move_assignment_copy_dependency(binding);
	string name = symbol_for(binding);
	if (complete_entry && defined_functions.find(name) != defined_functions.end())
	{
		demand_template_static_member_definitions_for_function(binding);
		return;
	}
	if (!complete_entry &&
	    defined_functions.find(name + "__base_entry") != defined_functions.end())
		return;
		for (size_t i = 0; i < pending_inline_definitions.size(); ++i)
			if (pending_inline_definitions[i] == binding)
				return;
		map<const Binding*, const Node*>::const_iterator found =
			inline_definitions.find(binding);
		if (found == inline_definitions.end() &&
		    lowir_synthesizable_noop_constructor(binding))
	{
		emit_generated_empty_constructor(
			binding,
			complete_entry ? name : name + "__base_entry");
		return;
	}
	if (found == inline_definitions.end() &&
	    lowir_synthesizable_defaulted_storage_copy_constructor(binding))
	{
		synthetic_inline_definitions[binding] =
			lowir_make_defaulted_storage_copy_constructor_node(binding);
		inline_definitions[binding] =
			&synthetic_inline_definitions[binding];
		found = inline_definitions.find(binding);
	}
		if (found != inline_definitions.end())
		{
			bool concrete_alias_body =
				concrete_alias_body_needs_own_definition(binding) &&
				synthetic_inline_definitions.find(binding) !=
					synthetic_inline_definitions.end();
			if (binding_has_template_specialization_context(binding) ||
			    !binding->function_specialization_symbol.empty())
				demand_template_static_member_definitions_for_function(binding);
				bool unresolved_body =
					!concrete_alias_body &&
					node_tree_has_unresolved_storage(*found->second);
				bool concrete_function_template_body =
					!binding->function_specialization_symbol.empty() ||
					(binding->aliased_binding != NULL &&
					 !binding->aliased_binding
						  ->function_specialization_symbol.empty());
				bool concrete_user_body =
					!hosted_library_binding(binding) &&
					((!binding_has_template_specialization_context(binding) &&
					  binding->function_specialization_symbol.empty() &&
					  (binding->aliased_binding == NULL ||
					   binding->aliased_binding
						   ->function_specialization_symbol.empty())) ||
					 concrete_function_template_body);
				if (unresolved_body && concrete_user_body)
					unresolved_body = false;
				if (lowir_hosted_tree_copy_move_constructor(binding) ||
				    unresolved_body)
					return;
				demand_template_static_member_definitions_for_function(binding);
				insert_pending_inline_definition(binding);
	}
}

}  // namespace internal
}  // namespace pa14
