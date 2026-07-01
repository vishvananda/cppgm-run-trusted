#pragma once
#define PA12_DEPENDENT_VALUE_MEMBER_BODY_B \
			} \
		} \
			if (alias_declaration == NULL && declaration == NULL) \
			{ \
				return false; \
			} \
			if (declaration != NULL && !owner_args.empty()) \
			{ \
				bool owner_args_too_large = true; \
				for (size_t pi = 0; pi < declaration->parameters.size(); ++pi) \
					if (declaration->parameters[pi].is_pack) \
						owner_args_too_large = false; \
				owner_args_too_large = \
					owner_args_too_large && \
					owner_args.size() > declaration->parameters.size(); \
				if (owner_args_too_large) \
				{ \
					for (size_t ci = 0; \
					     ci < declaration->class_specialization_declarations.size() && \
					     owner_args_too_large; \
					     ++ci) \
					{ \
						TemplateDeclaration* candidate = \
							declaration->class_specialization_declarations[ci]; \
						if (candidate == NULL || \
						    candidate->parameters.size() != owner_args.size()) \
							continue; \
						Parser* self = const_cast<Parser*>(this); \
						vector<map<string, TypePtr> > save_type_subst = \
							self->template_type_substitutions_; \
						vector<map<string, TemplateArgument> > save_value_subst = \
							self->template_value_substitutions_; \
						vector<set<string> > save_pack_subst = \
							self->template_type_parameter_packs_; \
						map<string, TypePtr> type_subst; \
						map<string, TemplateArgument> value_subst; \
						set<string> pack_subst; \
						for (size_t pi = 0; pi < candidate->parameters.size(); ++pi) \
						{ \
							const TemplateParameterInfo& parameter = \
								candidate->parameters[pi]; \
							if (parameter.name.empty()) \
								continue; \
							const TemplateArgument& owner_arg = owner_args[pi]; \
							if (parameter.kind == TemplateParameterKind::Type) \
							{ \
								if (parameter.is_pack) \
								{ \
									type_subst[parameter.name] = \
										pa11::make_template_parameter_type( \
											parameter.name); \
									value_subst[parameter.name] = owner_arg; \
									pack_subst.insert(parameter.name); \
								} \
								else if (owner_arg.kind == TemplateArgumentKind::Type) \
									type_subst[parameter.name] = owner_arg.type; \
							} \
							else \
								value_subst[parameter.name] = owner_arg; \
						} \
						self->template_type_substitutions_.push_back(type_subst); \
						self->template_value_substitutions_.push_back(value_subst); \
						self->template_type_parameter_packs_.push_back(pack_subst); \
						vector<TemplateArgument> recovered_args; \
						try \
						{ \
							for (size_t pi = 0; \
							     pi < candidate->class_specialization_pattern.size(); \
							     ++pi) \
								recovered_args.push_back( \
									substitute_template_argument( \
										candidate-> \
											class_specialization_pattern[pi])); \
						} \
						catch (...) \
						{ \
							self->template_type_substitutions_ = save_type_subst; \
							self->template_value_substitutions_ = save_value_subst; \
							self->template_type_parameter_packs_ = save_pack_subst; \
							throw; \
						} \
						self->template_type_substitutions_ = save_type_subst; \
						self->template_value_substitutions_ = save_value_subst; \
						self->template_type_parameter_packs_ = save_pack_subst; \
						bool recovered_too_large = true; \
						for (size_t pi = 0; pi < declaration->parameters.size(); ++pi) \
							if (declaration->parameters[pi].is_pack) \
								recovered_too_large = false; \
						recovered_too_large = \
							recovered_too_large && \
							recovered_args.size() > declaration->parameters.size(); \
						if (!recovered_too_large) \
						{ \
							owner_args = recovered_args; \
							owner_args_too_large = false; \
						} \
					} \
					if (owner_args_too_large) \
						for (size_t ai = active_class_instantiations_.size(); \
						     ai > 0; \
						     --ai) \
						{ \
							const ActiveClassInstantiation& active = \
								active_class_instantiations_[ai - 1]; \
							if (active.declaration == NULL || \
							    active.declaration->name != declaration->name || \
							    active.declaration->owner != declaration->owner) \
								continue; \
							TypePtr active_type = active.type.get() != NULL \
								? pa11::strip_cv(active.type) : TypePtr(); \
							if (active_type.get() == NULL || \
							    active_type->kind != pa11::TypeKind::Record || \
							    active_type->template_arguments.empty()) \
								continue; \
							vector<TemplateArgument> canonical_args; \
							for (size_t ti = 0; \
							     ti < active_type->template_arguments.size(); \
							     ++ti) \
								canonical_args.push_back( \
									template_argument_from_instance_argument( \
										active_type->template_arguments[ti])); \
							owner_args = canonical_args; \
							break; \
						} \
				} \
			} \
			try \
			{ \
				owner = alias_declaration != NULL \
					? const_cast<Parser*>(this)->instantiate_alias_template( \
						alias_declaration, \
						owner_args) \
				: const_cast<Parser*>(this)->instantiate_class_template( \
					declaration, \
					owner_args); \
			} \
			catch (const runtime_error& err) \
			{ \
				string message = err.what(); \
				if (hosted_compatibility_ && \
				    (message == "missing template argument" || \
				     message == "template argument kind mismatch" || \
				     message == "template pack argument kind mismatch")) \
					return false; \
				throw; \
			} \
	} \
	owner = owner.get() != NULL ? pa11::strip_cv(owner) : TypePtr(); \
	if (owner.get() == NULL || \
	    owner->kind != pa11::TypeKind::Record || \
	    owner->scope == NULL) \
		return false; \
	string owner_primary_precomplete = owner->template_primary_name.empty() \
		? owner->name : owner->template_primary_name; \
	size_t owner_name_pos_precomplete = \
		owner_primary_precomplete.rfind("::"); \
	string owner_unqualified_precomplete = \
		owner_name_pos_precomplete == string::npos \
		? owner_primary_precomplete \
		: owner_primary_precomplete.substr(owner_name_pos_precomplete + 2); \
	size_t owner_template_pos_precomplete = \
		owner_unqualified_precomplete.find('<'); \
	if (owner_template_pos_precomplete != string::npos) \
		owner_unqualified_precomplete = \
			owner_unqualified_precomplete.substr(0, \
			                                     owner_template_pos_precomplete); \
	if (hosted_compatibility_ && \
	    arg.value_member_name == "value" && \
	    owner_unqualified_precomplete == "_Callable") \
	{ \
		auto normalize_callable_type = [&](TypePtr type) -> TypePtr { \
			try \
			{ \
				type = substitute_template_type(type); \
			} \
			catch (const runtime_error&) \
			{ \
			} \
			if (type.get() == NULL) \
				return type; \
			if (type->kind == pa11::TypeKind::LValueReference || \
			    type->kind == pa11::TypeKind::RValueReference) \
			{ \
				TypePtr base = type->base; \
				try \
				{ \
					base = substitute_template_type(base); \
				} \
				catch (const runtime_error&) \
				{ \
				} \
				if (base.get() != NULL && base->is_dependent_typename) \
				{ \
					TypePtr resolved = \
						resolve_dependent_typename_type(base); \
					if (resolved.get() != NULL) \
						base = resolved; \
				} \
				if (base != type->base) \
					return type->kind == pa11::TypeKind::LValueReference \
						? pa11::make_lvalue_reference(base) \
						: pa11::make_rvalue_reference(base); \
				return type; \
			} \
			if (type->is_dependent_typename) \
			{ \
				TypePtr resolved = resolve_dependent_typename_type(type); \
				if (resolved.get() != NULL) \
					return resolved; \
			} \
			TypePtr bare = pa11::strip_cv(type); \
			if (bare.get() != NULL && \
			    bare->kind == pa11::TypeKind::Record && \
			    bare->scope != NULL) \
			{ \
				string primary = bare->template_primary_name.empty() \
					? bare->name : bare->template_primary_name; \
				size_t sep = primary.rfind("::"); \
				if (sep != string::npos) \
					primary = primary.substr(sep + 2); \
				size_t arg_pos = primary.find('<'); \
				if (arg_pos != string::npos) \
					primary = primary.substr(0, arg_pos); \
				if (primary == "decay") \
				{ \
					try \
					{ \
						const_cast<Parser*>(this)-> \
							complete_template_record(bare); \
					} \
					catch (const runtime_error&) \
					{ \
					} \
					try \
					{ \
						vector<Binding*> found = \
							const_cast<Parser*>(this)-> \
								lookup_qualified_set( \
									bare->scope, \
									"type", \
									pa11::LOOKUP_TYPE); \
						if (!found.empty() && \
						    found[0]->type.get() != NULL) \
							return substitute_template_type_in_scope( \
								found[0]->type, \
								bare->scope); \
					} \
					catch (const runtime_error&) \
					{ \
					} \
				} \
			} \
			return type; \
		}; \
		auto append_invoke_result_call_types = \
			[&](TypePtr invoke_result, \
			    vector<TypePtr>& call_types) -> bool { \
				TypePtr bare = invoke_result.get() != NULL \
					? pa11::strip_cv(invoke_result) : TypePtr(); \
				if (bare.get() == NULL || \
				    bare->kind != pa11::TypeKind::Record) \
					return false; \
				string primary = bare->template_primary_name.empty() \
					? bare->name : bare->template_primary_name; \
				size_t sep = primary.rfind("::"); \
				if (sep != string::npos) \
					primary = primary.substr(sep + 2); \
				size_t arg_pos = primary.find('<'); \
				if (arg_pos != string::npos) \
					primary = primary.substr(0, arg_pos); \
				if (primary != "__invoke_result") \
					return false; \
				vector<TemplateArgument> invoke_args; \
				map<const void*, vector<TemplateArgument> >::const_iterator \
					stored = record_template_arguments_.find(bare.get()); \
				if (stored != record_template_arguments_.end()) \
					invoke_args = stored->second; \
				else \
					for (size_t ti = 0; \
					     ti < bare->template_arguments.size(); \
					     ++ti) \
						invoke_args.push_back( \
							template_argument_from_instance_argument( \
								bare->template_arguments[ti])); \
				invoke_args = flatten_template_argument_packs(invoke_args); \
				for (size_t ti = 0; ti < invoke_args.size(); ++ti) \
				{ \
					TemplateArgument invoke_arg = \
						substitute_template_argument(invoke_args[ti]); \
					if (invoke_arg.kind == TemplateArgumentKind::Pack) \
					{ \
						for (size_t pi = 0; \
						     pi < invoke_arg.pack.size(); \
						     ++pi) \
						{ \
							TemplateArgument elem = \
								substitute_template_argument( \
									invoke_arg.pack[pi]); \
							if (elem.kind != TemplateArgumentKind::Type) \
								return false; \
							call_types.push_back( \
								normalize_callable_type(elem.type)); \
						} \
						continue; \
					} \
					if (invoke_arg.kind != TemplateArgumentKind::Type) \
						return false; \
					call_types.push_back( \
						normalize_callable_type(invoke_arg.type)); \
				} \
				return !call_types.empty(); \
			}; \
		vector<TemplateArgument> callable_args; \
		map<const void*, vector<TemplateArgument> >::const_iterator stored = \
			record_template_arguments_.find(owner.get()); \
		if (stored != record_template_arguments_.end()) \
			callable_args = stored->second; \
		else \
			for (size_t ti = 0; ti < owner->template_arguments.size(); ++ti) \
				callable_args.push_back( \
					template_argument_from_instance_argument( \
						owner->template_arguments[ti])); \
		callable_args = flatten_template_argument_packs(callable_args); \
		for (size_t ci = 0; ci < callable_args.size(); ++ci) \
			callable_args[ci] = substitute_template_argument( \
				callable_args[ci]); \
		TypePtr result_type; \
		for (size_t si = template_type_substitutions_.size(); si > 0; --si) \
		{ \
			map<string, TypePtr>::const_iterator it = \
				template_type_substitutions_[si - 1].find("_Res"); \
			if (it != template_type_substitutions_[si - 1].end()) \
			{ \
				result_type = normalize_callable_type(it->second); \
				break; \
			} \
		} \
		vector<TypePtr> call_types; \
		if (callable_args.size() >= 3 && \
		    callable_args[2].kind == TemplateArgumentKind::Type) \
			append_invoke_result_call_types(callable_args[2].type, \
			                                call_types); \
		if (call_types.empty() && \
		    callable_args.size() >= 2 && \
		    callable_args[1].kind == TemplateArgumentKind::Type) \
		{ \
			TypePtr dfunc = normalize_callable_type(callable_args[1].type); \
			if (dfunc.get() != NULL) \
				call_types.push_back(pa11::make_lvalue_reference(dfunc)); \
			for (size_t si = template_value_substitutions_.size(); \
			     si > 0; \
			     --si) \
			{ \
				map<string, TemplateArgument>::const_iterator it = \
					template_value_substitutions_[si - 1].find("_ArgTypes"); \
				if (it == template_value_substitutions_[si - 1].end() || \
				    it->second.kind != TemplateArgumentKind::Pack) \
					continue; \
				for (size_t pi = 0; pi < it->second.pack.size(); ++pi) \
					if (it->second.pack[pi].kind == \
					    TemplateArgumentKind::Type) \
						call_types.push_back(normalize_callable_type( \
							it->second.pack[pi].type)); \
				break; \
			} \
		} \
		bool concrete = result_type.get() != NULL && !call_types.empty(); \
		if (concrete && type_structurally_dependent(result_type)) \
			concrete = false; \
		for (size_t ci = 0; ci < call_types.size(); ++ci) \
			if (type_structurally_dependent(call_types[ci])) \
				concrete = false; \
		if (concrete) \
		{ \
			vector<TypePtr> trait_types; \
			trait_types.push_back(result_type); \
			trait_types.insert(trait_types.end(), \
			                   call_types.begin(), \
			                   call_types.end()); \
			bool value = const_cast<Parser*>(this)-> \
				is_invocable_r_type_trait(trait_types, false); \
			return bool_result(value); \
		} \
	} \
	if (hosted_compatibility_ && \
	    arg.value_member_name == "type" && \
	    owner_unqualified_precomplete == "common_type") \
	{ \
		vector<TemplateArgument> common_args = owner_args; \
		if (common_args.empty()) \
		{ \
			map<const void*, vector<TemplateArgument> >::const_iterator \
				stored = record_template_arguments_.find(owner.get()); \
			if (stored != record_template_arguments_.end()) \
				common_args = stored->second; \
			else \
				for (size_t ti = 0; ti < owner->template_arguments.size(); ++ti) \
					common_args.push_back( \
						template_argument_from_instance_argument( \
							owner->template_arguments[ti])); \
		} \
		common_args = flatten_template_argument_packs(common_args); \
		TypePtr common_type; \
		bool same_concrete_type = !common_args.empty(); \
		for (size_t ci = 0; ci < common_args.size(); ++ci) \
		{ \
			TemplateArgument elem = substitute_template_argument( \
				common_args[ci]); \
			if (elem.kind != TemplateArgumentKind::Type || \
			    type_structurally_dependent(elem.type)) \
			{ \
				same_concrete_type = false; \
				break; \
			} \
			if (common_type.get() == NULL) \
				common_type = elem.type; \
			else if (!pa11::same_type(common_type, elem.type)) \
			{ \
				same_concrete_type = false; \
				break; \
			} \
		} \
		if (same_concrete_type) \
			return cache_result(TemplateArgument::type_arg(common_type)); \
	} \
	const_cast<Parser*>(this)->complete_template_record(owner); \
	string owner_primary = owner->template_primary_name; \
	size_t owner_name_pos = owner_primary.rfind("::"); \
	string owner_unqualified = owner_name_pos == string::npos \
		? owner_primary : owner_primary.substr(owner_name_pos + 2); \
	if (hosted_compatibility_ && \
	    arg.value_member_name == "value" && \
	    owner_unqualified == "__is_nothrow_invocable") \
	{ \
		map<const void*, vector<TemplateArgument> >::const_iterator args = \
			record_template_arguments_.find(owner.get()); \
		if (args != record_template_arguments_.end()) \
		{ \
			vector<TypePtr> types; \
			bool type_args = true; \
			for (size_t i = 0; i < args->second.size(); ++i) \
			{ \
				const TemplateArgument& owner_arg = args->second[i]; \
				if (owner_arg.kind == TemplateArgumentKind::Type) \
					types.push_back(owner_arg.type); \
				else if (owner_arg.kind == TemplateArgumentKind::Pack) \
				{ \
					for (size_t j = 0; j < owner_arg.pack.size(); ++j) \
					{ \
						if (owner_arg.pack[j].kind != \
						    TemplateArgumentKind::Type) \
						{ \
							type_args = false; \
							break; \
						} \
						types.push_back(owner_arg.pack[j].type); \
					} \
				} \
				else \
					type_args = false; \
				if (!type_args) \
					break; \
			} \
			if (type_args) \
			{ \
				bool value = const_cast<Parser*>(this)-> \
					is_invocable_type_trait(types, true); \
				TemplateArgument result = TemplateArgument::value_arg( \
					pa11::make_fundamental(FT_BOOL), \
					arg.value_negated ? (value ? 0 : 1) \
					                  : (value ? 1 : 0)); \
				result.value_name = arg.value_name; \
				return cache_result(result); \
			} \
		} \
	} \
		vector<Binding*> found = \
			const_cast<Parser*>(this)->lookup_qualified_set( \
				owner->scope, \
				arg.value_member_name, \
				pa11::LOOKUP_VALUE); \
		if (found.empty()) \
	{ \
		vector<string> parts; \
		size_t begin = 0; \
		for (;;) \
		{ \
			size_t pos = arg.value_name.find("::", begin); \
			parts.push_back(arg.value_name.substr(begin, pos - begin)); \
			if (pos == string::npos) \
				break; \
			begin = pos + 2; \
		} \
		if (parts.size() > 2) \
		{ \
			TypePtr nested_owner = owner; \
			for (size_t pi = 1; pi + 1 < parts.size(); ++pi) \
			{ \
				TypePtr bare_nested = nested_owner.get() != NULL \
					? pa11::strip_cv(nested_owner) : TypePtr(); \
				if (bare_nested.get() == NULL || \
				    bare_nested->kind != pa11::TypeKind::Record || \
				    bare_nested->scope == NULL) \
					break; \
				const_cast<Parser*>(this)->complete_template_record( \
					bare_nested); \
				vector<Binding*> nested_type = \
					const_cast<Parser*>(this)->lookup_qualified_set( \
						bare_nested->scope, \
						parts[pi], \
						pa11::LOOKUP_TYPE); \
				if (nested_type.empty()) \
				{ \
					nested_owner.reset(); \
					break; \
				} \
				const_cast<Parser*>(this)-> \
					complete_member_class_template_record(nested_type[0]); \
				nested_owner = substitute_template_type_in_scope( \
					nested_type[0]->type, \
					nested_type[0]->owner); \
			} \
			TypePtr bare_nested = nested_owner.get() != NULL \
				? pa11::strip_cv(nested_owner) : TypePtr(); \
			if (bare_nested.get() != NULL && \
			    bare_nested->kind == pa11::TypeKind::Record && \
			    bare_nested->scope != NULL) \
			{ \
				const_cast<Parser*>(this)->complete_template_record( \
					bare_nested); \
				found = \
					const_cast<Parser*>(this)->lookup_qualified_set( \
						bare_nested->scope, \
						arg.value_member_name, \
						pa11::LOOKUP_VALUE); \
			} \
		} \
	} \
	if (found.empty()) \
	{ \
		TypePtr base = owner->base; \
		if (base.get() != NULL && base->is_dependent_typename) \
		{ \
			try \
			{ \
				Scope* base_scope = base->scope != NULL \
					? base->scope : owner->scope; \
				base = substitute_template_type_in_scope(base, \
				                                         base_scope); \
			} \
			catch (const runtime_error&) \
			{ \
			} \
		} \
		base = base.get() != NULL ? pa11::strip_cv(base) : TypePtr(); \
		if (base.get() != NULL && \
		    base->kind == pa11::TypeKind::Record && \
		    base->scope != NULL) \
		{ \
			const_cast<Parser*>(this)->complete_template_record(base); \
			found = \
				const_cast<Parser*>(this)->lookup_qualified_set( \
					base->scope, \
					arg.value_member_name, \
					pa11::LOOKUP_VALUE); \
		} \
	} \
		if (found.empty()) \
		{ \
			vector<Binding*> type_found = \
			const_cast<Parser*>(this)->lookup_qualified_set( \
				owner->scope, \
				arg.value_member_name, \
				pa11::LOOKUP_TYPE); \
		if (type_found.empty()) \
		{ \
			TypePtr base = owner->base; \
			if (base.get() != NULL && base->is_dependent_typename) \
			{ \
				try \
				{ \
					Scope* base_scope = base->scope != NULL \
						? base->scope : owner->scope; \
					base = substitute_template_type_in_scope(base, \
					                                         base_scope); \
				} \
				catch (const runtime_error&) \
				{ \
				} \
			} \
			base = base.get() != NULL ? pa11::strip_cv(base) : TypePtr(); \
			if (base.get() != NULL && \
			    base->kind == pa11::TypeKind::Record && \
			    base->scope != NULL) \
			{ \
				const_cast<Parser*>(this)->complete_template_record(base); \
				type_found = \
					const_cast<Parser*>(this)->lookup_qualified_set( \
						base->scope, \
						arg.value_member_name, \
						pa11::LOOKUP_TYPE); \
			} \
		} \
		if (!type_found.empty()) \
		{ \
			TypePtr resolved = type_found[0]->type; \
			const_cast<Parser*>(this)-> \
				complete_member_class_template_record(type_found[0]); \
			TemplateArgument result = TemplateArgument::type_arg( \
				substitute_template_type_in_scope( \
					resolved, \
					type_found[0]->owner)); \
			return cache_result(result); \
		} \
		if (arg.value_member_name == "type" && \
		    owner->base.get() != NULL && \
		    owner->base->is_dependent_typename) \
		{ \
			TypePtr inherited_type = owner->base; \
			try \
			{ \
				Scope* inherited_scope = \
					inherited_type->scope != NULL \
					? inherited_type->scope : owner->scope; \
				inherited_type = \
					substitute_template_type_in_scope(inherited_type, \
					                                  inherited_scope); \
			} \
			catch (const runtime_error&) \
			{ \
			} \
			TemplateArgument result = \
				TemplateArgument::type_arg(inherited_type); \
			return cache_result(result); \
		} \
		if (validating_template_definition_) \
			return false; \
		throw runtime_error("dependent value member not resolved"); \
	} \
	TypePtr target = arg.type.get() != NULL \
		? pa11::strip_cv(substitute_template_type(arg.type)) : TypePtr(); \
	if (target.get() != NULL && \
	    target->kind == pa11::TypeKind::MemberPointer) \
	{ \
		TypePtr target_class = target->member_class.get() != NULL \
			? pa11::strip_cv(target->member_class) : TypePtr(); \
		if (target_class.get() != NULL && \
		    (target_class->kind == pa11::TypeKind::TemplateParameter || \
		     target_class->is_dependent_typename)) \
			target = pa11::make_member_pointer(owner, target->base); \
		Parser* self = const_cast<Parser*>(this); \
		Binding* first = found[0]; \
		Expr inner; \
		inner.valid = true; \
		inner.binding = first; \
		inner.type = first->type; \
		inner.category = ValueCategory::LValue; \
		for (size_t i = 0; i < found.size(); ++i) \
			if (found[i]->kind == BindingKind::Function) \
				inner.overloads.push_back(found[i]); \
		inner.node = Node("id-expression lvalue " + \
		                  pa11::describe_type(inner.type) + " " + \
		                  qualified_decl_name(first)); \
		inner.node.binding = first; \
		annotate_expr_node(inner); \
		Expr address = self->make_address_expr("&", inner); \
		Conversion conv = self->convert_to(address, target); \
		if (!conv.viable || \
		    !conv.expr.node.has_op || \
		    conv.expr.node.op != OP_AMP || \
		    conv.expr.node.children.empty() || \
		    conv.expr.node.children[0].binding == NULL) \
			return false; \
		Binding* member = conv.expr.node.children[0].binding; \
		if (member->aliased_binding != NULL && \
		    member->target_scope != NULL) \
			member = member->aliased_binding; \
		TemplateArgument result = TemplateArgument::value_arg( \
			expression_object_type(conv.expr.type), \
			reinterpret_cast<uint64_t>(member)); \
		result.value_binding = member; \
		result.value_name = arg.value_name; \
		return cache_result(result); \
	} \
	Binding* binding = found[0]; \
	if (!binding->has_constant) \
	{ \
		ConstexprValue value; \
		bool evaluated = \
			const_cast<Parser*>(this)->try_evaluate_constexpr_binding( \
				binding, \
				value); \
		if ((!evaluated || value.is_object || value.is_pointer) && \
		    owner.get() != NULL) \
		{ \
			map<const void*, TemplateDeclaration*>::const_iterator owner_decl = \
				record_template_declarations_.find(owner.get()); \
			map<const void*, vector<TemplateArgument> >::const_iterator \
				owner_args = record_template_arguments_.find(owner.get()); \
			if (owner_decl != record_template_declarations_.end() && \
			    owner_args != record_template_arguments_.end()) \
			{ \
				Parser* self = const_cast<Parser*>(this); \
				vector<map<string, TypePtr> > save_subst = \
					self->template_type_substitutions_; \
				vector<map<string, TemplateArgument> > save_value_subst = \
					self->template_value_substitutions_; \
				vector<set<string> > save_pack_subst = \
					self->template_type_parameter_packs_; \
				vector<Scope*> save_scopes = self->scopes_; \
				map<string, TypePtr> subst; \
				map<string, TemplateArgument> value_subst; \
				set<string> pack_subst; \
				for (size_t i = 0; \
				     i < owner_args->second.size() && \
				     i < owner_decl->second->parameters.size(); \
				     ++i) \
				{ \
					const TemplateParameterInfo& parameter = \
						owner_decl->second->parameters[i]; \
					if (parameter.name.empty()) \
						continue; \
					const TemplateArgument& owner_arg = \
						owner_args->second[i]; \
					if (parameter.kind == TemplateParameterKind::Type) \
					{ \
						if (parameter.is_pack) \
						{ \
							subst[parameter.name] = \
								pa11::make_template_parameter_type( \
									parameter.name); \
							value_subst[parameter.name] = owner_arg; \
							pack_subst.insert(parameter.name); \
						} \
						else if (owner_arg.kind == TemplateArgumentKind::Type) \
							subst[parameter.name] = owner_arg.type; \
					} \
					else \
						value_subst[parameter.name] = owner_arg; \
				} \
				self->template_type_substitutions_.push_back(subst); \
				self->template_value_substitutions_.push_back(value_subst); \
				self->template_type_parameter_packs_.push_back(pack_subst); \
				self->scopes_.clear(); \
				self->scopes_.push_back(owner->scope); \
				evaluated = self->try_evaluate_constexpr_binding( \
					binding, \
					value); \
				self->template_type_substitutions_ = save_subst; \
				self->template_value_substitutions_ = save_value_subst; \
				self->template_type_parameter_packs_ = save_pack_subst; \
				self->scopes_ = save_scopes; \
			} \
		} \
		if (!evaluated || value.is_object || value.is_pointer) \
			throw runtime_error("dependent value member is not constant"); \
		binding->has_constant = true; \
		binding->constant_value = value.int_value; \
		TemplateArgument result = TemplateArgument::value_arg( \
			arg.value_negated \
			? pa11::make_fundamental(FT_BOOL) \
			: expression_object_type(binding->type), \
			arg.value_negated ? (value.int_value == 0 ? 1 : 0) \
			                  : value.int_value); \
		result.value_name = arg.value_name; \
		return cache_result(result); \
	} \
	TemplateArgument result = TemplateArgument::value_arg( \
		arg.value_negated \
		? pa11::make_fundamental(FT_BOOL) \
		: expression_object_type(binding->type), \
		arg.value_negated \
		? (binding->constant_value == 0 ? 1 : 0) \
		: binding->constant_value); \
	result.value_name = arg.value_name; \
	return cache_result(result);
