#pragma once
#define PA12_DEPENDENT_VALUE_MEMBER_BODY_A \
	if (arg.kind != TemplateArgumentKind::Value || \
	    !arg.dependent || \
	    arg.value_owner_template_name.empty()) \
		return false; \
	size_t active_hash = dependent_value_member_cache_prefix(arg); \
	size_t active_key = active_hash; \
	if (find(active_dependent_value_member_keys_.begin(), \
	         active_dependent_value_member_keys_.end(), \
	         active_key) != active_dependent_value_member_keys_.end()) \
		return false; \
	size_t cache_hash = active_hash; \
	cache_hash = dependent_cache_hash_combine( \
		cache_hash, \
		dependent_cache_type_identity(arg.type)); \
	cache_hash = dependent_cache_hash_combine(cache_hash, \
	                                          arg.value_negated); \
	cache_hash = dependent_cache_hash_combine( \
		cache_hash, \
		reinterpret_cast<uintptr_t>(current_scope())); \
	cache_hash = dependent_cache_hash_combine( \
		cache_hash, \
		validating_template_definition_); \
	cache_hash = dependent_cache_hash_combine( \
		cache_hash, \
		function_template_candidate_instantiation_depth_); \
	for (size_t si = 0; si < template_type_substitutions_.size(); ++si) \
	{ \
		cache_hash = dependent_cache_hash_combine(cache_hash, si); \
		for (map<string, TypePtr>::const_iterator it = \
			     template_type_substitutions_[si].begin(); \
		     it != template_type_substitutions_[si].end(); \
		     ++it) \
		{ \
			cache_hash = dependent_cache_hash_combine( \
				cache_hash, \
				dependent_cache_string_hash(it->first)); \
			cache_hash = dependent_cache_hash_combine( \
				cache_hash, \
				dependent_cache_type_identity(it->second)); \
		} \
	} \
	for (size_t si = 0; si < template_value_substitutions_.size(); ++si) \
	{ \
		cache_hash = dependent_cache_hash_combine(cache_hash, si); \
		for (map<string, TemplateArgument>::const_iterator it = \
			     template_value_substitutions_[si].begin(); \
		     it != template_value_substitutions_[si].end(); \
		     ++it) \
		{ \
			cache_hash = dependent_cache_hash_combine( \
				cache_hash, \
				dependent_cache_string_hash(it->first)); \
			cache_hash = dependent_cache_hash_combine( \
				cache_hash, \
				dependent_cache_template_argument_identity(it->second, \
				                                           0)); \
		} \
	} \
	size_t cache_key = cache_hash; \
		map<size_t, TemplateArgument>::const_iterator cached = \
			dependent_value_member_argument_cache_.find(cache_key); \
		if (cached != dependent_value_member_argument_cache_.end()) \
		{ \
			out = cached->second; \
			return true; \
		} \
		auto cache_result = [&](const TemplateArgument& result) -> bool { \
			dependent_value_member_argument_cache_[cache_key] = result; \
			out = result; \
			return true; \
	}; \
	TypePtr owner; \
	auto resolve_nested_owner_type = [&](TypePtr& nested_owner) -> bool { \
		if (arg.value_owner_template_name.find("::") == string::npos) \
			return false; \
		vector<string> parts; \
		size_t begin = 0; \
		for (;;) \
		{ \
			size_t pos = arg.value_owner_template_name.find("::", begin); \
			parts.push_back( \
				arg.value_owner_template_name.substr(begin, pos - begin)); \
			if (pos == string::npos) \
				break; \
			begin = pos + 2; \
		} \
		if (parts.size() < 2) \
			return false; \
		TypePtr current_type; \
		if (!find_template_type_substitution(parts[0], current_type)) \
			return false; \
		try \
		{ \
			current_type = substitute_template_type(current_type); \
		} \
		catch (const runtime_error&) \
		{ \
			return false; \
		} \
		for (size_t pi = 1; pi < parts.size(); ++pi) \
		{ \
			TypePtr current = current_type.get() != NULL \
				? pa11::strip_cv(current_type) : TypePtr(); \
			if (current.get() == NULL || \
			    current->kind != pa11::TypeKind::Record || \
			    current->scope == NULL) \
				return false; \
			try \
			{ \
				const_cast<Parser*>(this)->complete_template_record(current); \
			} \
			catch (const runtime_error&) \
			{ \
				return false; \
			} \
			vector<Binding*> found_type = \
				const_cast<Parser*>(this)->lookup_qualified_set( \
					current->scope, \
					parts[pi], \
					pa11::LOOKUP_TYPE); \
			if (found_type.empty()) \
				return false; \
			const_cast<Parser*>(this)-> \
				complete_member_class_template_record(found_type[0]); \
			try \
			{ \
				current_type = substitute_template_type_in_scope( \
					found_type[0]->type, \
					found_type[0]->owner); \
			} \
			catch (const runtime_error&) \
			{ \
				return false; \
			} \
		} \
		nested_owner = current_type; \
		return nested_owner.get() != NULL; \
	}; \
	resolve_nested_owner_type(owner); \
	struct ActiveDependentValueMember \
	{ \
		vector<size_t>& keys; \
		ActiveDependentValueMember(vector<size_t>& k, size_t key) \
		  : keys(k) \
		{ \
			keys.push_back(key); \
		} \
		~ActiveDependentValueMember() \
		{ \
			keys.pop_back(); \
		} \
	} active_dependent_value_member(active_dependent_value_member_keys_, \
	                                active_key); \
	vector<TemplateArgument> owner_args; \
	bool still_dependent = false; \
	for (size_t i = 0; i < arg.value_owner_template_arguments.size(); ++i) \
	{ \
		TemplateArgument owner_arg = \
			template_argument_from_instance_argument( \
				arg.value_owner_template_arguments[i]); \
		owner_arg = substitute_template_argument(owner_arg); \
		if (owner_arg.kind == TemplateArgumentKind::Type && \
		    owner_arg.type.get() != NULL && \
		    owner_arg.type->is_dependent_typename) \
		{ \
			try \
			{ \
				TypePtr resolved = \
					resolve_dependent_typename_type(owner_arg.type); \
				if (resolved.get() != NULL) \
				{ \
					owner_arg.type = substitute_template_type(resolved); \
					owner_arg.dependent = type_structurally_dependent( \
						owner_arg.type); \
				} \
			} \
			catch (const runtime_error&) \
			{ \
			} \
		} \
		if (owner_arg.kind == TemplateArgumentKind::Type && \
		    owner_arg.type.get() != NULL) \
		{ \
			TypePtr owner_record = pa11::strip_cv(owner_arg.type); \
			if (owner_record.get() != NULL && \
			    owner_record->kind == pa11::TypeKind::Record) \
			{ \
				try \
				{ \
					const_cast<Parser*>(this)-> \
						complete_template_record(owner_record); \
				} \
				catch (const runtime_error&) \
				{ \
				} \
			} \
		} \
		if (template_argument_has_template_parameter( \
			    owner_arg, \
			    record_template_arguments_)) \
			still_dependent = true; \
		owner_args.push_back(owner_arg); \
	} \
		if (still_dependent) \
		{ \
			return false; \
		} \
			string trait_owner_unqualified = arg.value_owner_template_name; \
		size_t owner_sep = trait_owner_unqualified.rfind("::"); \
		if (owner_sep != string::npos) \
			trait_owner_unqualified = \
				trait_owner_unqualified.substr(owner_sep + 2); \
		auto bool_result = [&](bool value) -> bool { \
			TemplateArgument result = TemplateArgument::value_arg( \
				pa11::make_fundamental(FT_BOOL), \
				arg.value_negated ? (value ? 0 : 1) : (value ? 1 : 0)); \
			result.value_name = arg.value_name; \
			return cache_result(result); \
		}; \
		function<void(vector<TemplateArgument>&, const TemplateArgument&)> \
			append_trait_arg = \
				[&](vector<TemplateArgument>& out, \
				    const TemplateArgument& elem) { \
					if (elem.kind == TemplateArgumentKind::Pack) \
					{ \
						for (size_t pi = 0; pi < elem.pack.size(); ++pi) \
							append_trait_arg(out, elem.pack[pi]); \
					} \
					else \
						out.push_back(elem); \
				}; \
		function<bool(TypePtr, bool&)> evaluate_trait_type = \
			[&](TypePtr trait_type, bool& value) -> bool { \
				TypePtr record = trait_type.get() != NULL \
					? pa11::strip_cv(trait_type) : TypePtr(); \
				if (record.get() == NULL || \
				    record->kind != pa11::TypeKind::Record) \
					return false; \
				string primary = record->template_primary_name; \
				if (primary.empty() && record->scope != NULL) \
					primary = record->scope->name; \
				size_t primary_sep = primary.rfind("::"); \
				if (primary_sep != string::npos) \
					primary = primary.substr(primary_sep + 2); \
				vector<TemplateArgument> trait_args; \
				map<const void*, vector<TemplateArgument> >::const_iterator stored = \
					record_template_arguments_.find(record.get()); \
				if (stored != record_template_arguments_.end()) \
					for (size_t ai = 0; ai < stored->second.size(); ++ai) \
						append_trait_arg(trait_args, stored->second[ai]); \
				else \
					for (size_t ai = 0; ai < record->template_arguments.size(); ++ai) \
						append_trait_arg( \
							trait_args, \
							template_argument_from_instance_argument( \
								record->template_arguments[ai])); \
				if ((primary == "integral_constant" || \
				     primary == "__bool_constant") && \
				    !trait_args.empty()) \
				{ \
					size_t value_index = trait_args.size() >= 2 ? 1 : 0; \
					if (trait_args[value_index].kind == \
						    TemplateArgumentKind::Value && \
					    !trait_args[value_index].dependent) \
					{ \
						value = trait_args[value_index].value != 0; \
						return true; \
					} \
				} \
				if ((primary == "is_same" || primary == "__are_same") && \
				    trait_args.size() >= 2 && \
				    trait_args[0].kind == TemplateArgumentKind::Type && \
				    trait_args[1].kind == TemplateArgumentKind::Type) \
				{ \
					value = pa11::same_type(trait_args[0].type, \
					                        trait_args[1].type); \
					return true; \
				} \
					if (primary == "is_class" && \
					    !trait_args.empty() && \
					    trait_args[0].kind == TemplateArgumentKind::Type) \
					{ \
						TypePtr bare = trait_args[0].type.get() != NULL \
							? pa11::strip_cv(trait_args[0].type) : TypePtr(); \
						value = bare.get() != NULL && \
						        bare->kind == pa11::TypeKind::Record; \
						return true; \
					} \
					if ((primary == "is_pointer" || \
					     primary == "__is_pointer") && \
					    !trait_args.empty() && \
					    trait_args[0].kind == TemplateArgumentKind::Type) \
					{ \
						TypePtr bare = trait_args[0].type.get() != NULL \
							? pa11::strip_cv(trait_args[0].type) : TypePtr(); \
						value = bare.get() != NULL && \
						        bare->kind == pa11::TypeKind::Pointer; \
						return true; \
					} \
					if ((primary == "is_reference" || \
					     primary == "__is_reference" || \
					     primary == "is_lvalue_reference" || \
					     primary == "is_rvalue_reference") && \
					    !trait_args.empty() && \
					    trait_args[0].kind == TemplateArgumentKind::Type) \
					{ \
						TypePtr bare = trait_args[0].type.get() != NULL \
							? pa11::strip_cv(trait_args[0].type) : TypePtr(); \
						bool lvalue = bare.get() != NULL && \
						              bare->kind == pa11::TypeKind::LValueReference; \
						bool rvalue = bare.get() != NULL && \
						              bare->kind == pa11::TypeKind::RValueReference; \
						if (primary == "is_lvalue_reference") \
							value = lvalue; \
						else if (primary == "is_rvalue_reference") \
							value = rvalue; \
						else \
							value = lvalue || rvalue; \
						return true; \
					} \
				if (primary == "__has_esft_base" && \
				    !trait_args.empty() && \
				    trait_args[0].kind == TemplateArgumentKind::Type) \
				{ \
					TypePtr bare = trait_args[0].type.get() != NULL \
						? pa11::strip_cv(trait_args[0].type) : TypePtr(); \
					set<const void*> seen; \
					value = bare.get() != NULL && \
					        bare->kind == pa11::TypeKind::Record && \
					        hosted_record_has_esft_base_type(bare, seen); \
					return true; \
				} \
				if ((primary == "is_constructible" || \
				     primary == "__is_constructible" || \
				     primary == "is_nothrow_constructible" || \
				     primary == "__is_nothrow_constructible" || \
				     primary == "is_trivially_constructible" || \
				     primary == "__is_trivially_constructible" || \
				     primary == "is_copy_constructible" || \
				     primary == "is_nothrow_copy_constructible" || \
				     primary == "is_trivially_copy_constructible" || \
				     primary == "is_move_constructible" || \
				     primary == "is_nothrow_move_constructible" || \
				     primary == "is_trivially_move_constructible" || \
				     primary == "is_assignable" || \
				     primary == "__is_assignable" || \
				     primary == "is_nothrow_assignable" || \
				     primary == "__is_nothrow_assignable" || \
				     primary == "is_trivially_assignable" || \
				     primary == "__is_trivially_assignable" || \
				     primary == "is_copy_assignable" || \
				     primary == "is_nothrow_copy_assignable" || \
				     primary == "is_trivially_copy_assignable" || \
				     primary == "is_move_assignable" || \
				     primary == "is_nothrow_move_assignable" || \
				     primary == "is_trivially_move_assignable") && \
				    !trait_args.empty()) \
				{ \
					vector<TypePtr> types; \
					for (size_t ti = 0; ti < trait_args.size(); ++ti) \
					{ \
						if (trait_args[ti].kind != TemplateArgumentKind::Type) \
							return false; \
						TypePtr resolved_type; \
						if (!resolve_dependent_trait_subject_type( \
							    trait_args[ti].type, \
							    resolved_type)) \
							return false; \
						types.push_back(resolved_type); \
					} \
					if (const_cast<Parser*>(this)-> \
						    evaluate_standard_constructible_trait( \
							    primary, types, value)) \
						return true; \
				} \
				if ((primary == "is_constructible" || \
				     primary == "__is_constructible") && \
				    !trait_args.empty()) \
				{ \
					vector<TypePtr> types; \
						for (size_t ti = 0; ti < trait_args.size(); ++ti) \
						{ \
							if (trait_args[ti].kind != TemplateArgumentKind::Type) \
								return false; \
							TypePtr resolved_type; \
							if (!resolve_dependent_trait_subject_type( \
								    trait_args[ti].type, \
								    resolved_type)) \
								return false; \
							types.push_back(resolved_type); \
						} \
						value = const_cast<Parser*>(this)-> \
							is_constructible_type_trait(types); \
					return true; \
				} \
				if (((hosted_compatibility_ && primary == "is_convertible") || \
				     primary == "__is_convertible") && \
				    trait_args.size() >= 2 && \
				    trait_args[0].kind == TemplateArgumentKind::Type && \
				    trait_args[1].kind == TemplateArgumentKind::Type) \
				{ \
					TypePtr from_type; \
					TypePtr to_type; \
					if (!resolve_dependent_trait_subject_type( \
						    trait_args[0].type, \
						    from_type) || \
					    !resolve_dependent_trait_subject_type( \
						    trait_args[1].type, \
						    to_type)) \
						return false; \
					vector<TypePtr> types; \
					types.push_back(from_type); \
					types.push_back(to_type); \
					value = const_cast<Parser*>(this)-> \
						evaluate_builtin_type_trait("__is_convertible", types); \
					return true; \
				} \
				if (primary == "__not_" && \
				    trait_args.size() == 1 && \
				    trait_args[0].kind == TemplateArgumentKind::Type) \
				{ \
					bool inner = false; \
					if (!evaluate_trait_type(trait_args[0].type, inner)) \
						return false; \
					value = !inner; \
					return true; \
				} \
					if (primary == "__and_" || primary == "__or_") \
					{ \
						value = primary == "__and_"; \
						for (size_t ai = 0; ai < trait_args.size(); ++ai) \
					{ \
						if (trait_args[ai].kind != TemplateArgumentKind::Type) \
							return false; \
						bool elem = false; \
						if (!evaluate_trait_type(trait_args[ai].type, elem)) \
							return false; \
						if (primary == "__and_" && !elem) \
						{ \
							value = false; \
							return true; \
						} \
						if (primary == "__or_" && elem) \
						{ \
							value = true; \
							return true; \
						} \
						} \
						return true; \
					} \
					auto evaluate_dependent_value_typename = \
						[&](TypePtr value_type, bool& value_out) -> bool { \
							if (value_type.get() == NULL || \
							    !value_type->is_dependent_typename) \
								return false; \
							size_t member_pos = value_type->name.rfind("::"); \
							if (member_pos == string::npos) \
								return false; \
							string owner_name = \
								value_type->name.substr(0, member_pos); \
							string member_name = \
								value_type->name.substr(member_pos + 2); \
							size_t owner_template = owner_name.find('<'); \
							if (owner_template != string::npos) \
								owner_name = owner_name.substr(0, \
								                               owner_template); \
							size_t nested = owner_name.rfind("::"); \
							if (nested != string::npos) \
								owner_name = owner_name.substr(nested + 2); \
							if (member_name == "value" || \
							    member_name == "__value") \
							{ \
								vector<TemplateArgument> owner_args; \
								const vector<pa11::TemplateInstanceArgument>* stored_args = \
									&value_type->template_arguments; \
								if (stored_args->empty() && \
								    !value_type-> \
									    dependent_typename_template_argument_lists.empty()) \
									stored_args = \
										&value_type-> \
											dependent_typename_template_argument_lists[0]; \
								for (size_t ai = 0; ai < stored_args->size(); ++ai) \
									owner_args.push_back( \
										substitute_template_argument( \
											template_argument_from_instance_argument( \
												(*stored_args)[ai]))); \
								owner_args = \
									flatten_template_argument_packs(owner_args); \
								TemplateDeclaration* owner_template = \
									const_cast<Parser*>(this)->find_class_template( \
										NULL, \
										owner_name); \
								if (owner_template == NULL) \
									for (map<Scope*, map<string, TemplateDeclaration*> >:: \
										     const_iterator sit = \
											     class_templates_.begin(); \
									     sit != class_templates_.end() && \
										     owner_template == NULL; \
									     ++sit) \
									{ \
										map<string, TemplateDeclaration*>:: \
											const_iterator found = \
												sit->second.find(owner_name); \
										if (found != sit->second.end()) \
											owner_template = found->second; \
									} \
								if (owner_template != NULL) \
								{ \
									TypePtr owner_type = \
										const_cast<Parser*>(this)-> \
											instantiate_class_template( \
												owner_template, \
												owner_args); \
									if (evaluate_trait_type(owner_type, value_out)) \
										return true; \
								} \
							} \
							TemplateArgument value_arg = \
								TemplateArgument::dependent_value_arg( \
									pa11::make_fundamental(FT_BOOL)); \
							value_arg.value_name = value_type->name; \
							value_arg.value_owner_template_name = owner_name; \
							value_arg.value_member_name = member_name; \
							value_arg.value_owner_template_arguments = \
								value_type->template_arguments; \
							if (value_arg.value_owner_template_arguments.empty() && \
							    !value_type-> \
								    dependent_typename_template_argument_lists.empty()) \
								value_arg.value_owner_template_arguments = \
									value_type-> \
										dependent_typename_template_argument_lists[0]; \
							TemplateArgument resolved_value; \
							if (!resolve_dependent_value_member_argument( \
								    value_arg, \
								    resolved_value)) \
								return false; \
							resolved_value = \
								substitute_template_argument(resolved_value); \
							if (resolved_value.kind == \
								    TemplateArgumentKind::Value && \
							    !resolved_value.dependent) \
							{ \
								value_out = resolved_value.value != 0; \
								return true; \
							} \
							if (resolved_value.kind == \
							    TemplateArgumentKind::Type) \
								return evaluate_trait_type(resolved_value.type, \
								                           value_out); \
							return false; \
						}; \
					auto evaluate_conditional_typename = \
						[&](TypePtr conditional_type, bool& conditional_value) -> bool { \
							if (conditional_type.get() == NULL || \
							    !conditional_type->is_dependent_typename) \
								return false; \
							vector<string> conditional_parts; \
							size_t begin = 0; \
							for (;;) \
							{ \
								size_t pos = \
									conditional_type->name.find("::", begin); \
								conditional_parts.push_back( \
									conditional_type->name.substr(begin, \
									                              pos - begin)); \
								if (pos == string::npos) \
									break; \
								begin = pos + 2; \
							} \
							if (conditional_parts.size() < 2 || \
							    conditional_parts[1] != "type") \
								return false; \
							string root = conditional_parts[0]; \
							size_t root_template = root.find('<'); \
							if (root_template != string::npos) \
								root = root.substr(0, root_template); \
							if (root != "conditional") \
								return false; \
							size_t list_index = 0; \
							vector<TemplateArgument> stored; \
							if (!dependent_typename_template_argument_list( \
								    conditional_type, \
								    list_index, \
								    stored)) \
								return false; \
							vector<TemplateArgument> conditional_args; \
							for (size_t ai = 0; ai < stored.size(); ++ai) \
								conditional_args.push_back( \
									substitute_template_argument(stored[ai])); \
							conditional_args = \
								flatten_template_argument_packs(conditional_args); \
							bool condition_value = false; \
							bool condition_known = false; \
							if (conditional_args.size() >= 3 && \
							    conditional_args[0].kind == \
								    TemplateArgumentKind::Value && \
							    !conditional_args[0].dependent) \
							{ \
								condition_value = \
									conditional_args[0].value != 0; \
								condition_known = true; \
							} \
							else if (conditional_args.size() >= 3 && \
							         conditional_args[0].kind == \
								         TemplateArgumentKind::Type && \
							         (evaluate_trait_type( \
								          conditional_args[0].type, \
								          condition_value) || \
							          evaluate_dependent_value_typename( \
								          conditional_args[0].type, \
								          condition_value))) \
								condition_known = true; \
							if (conditional_args.size() < 3 || \
							    !condition_known || \
							    conditional_args[1].kind != \
								    TemplateArgumentKind::Type || \
							    conditional_args[2].kind != \
								    TemplateArgumentKind::Type) \
								return false; \
							TypePtr selected = condition_value \
								? conditional_args[1].type \
								: conditional_args[2].type; \
							if (conditional_parts.size() == 2) \
								return evaluate_trait_type(selected, \
								                           conditional_value); \
							TypePtr resolved = \
								resolve_dependent_typename_type( \
									conditional_type); \
							if (resolved.get() != NULL) \
								return evaluate_trait_type(resolved, \
								                           conditional_value); \
							return false; \
						}; \
					try \
					{ \
						const_cast<Parser*>(this)->complete_template_record(record); \
					} \
					catch (const runtime_error&) \
					{ \
					} \
					TypePtr base = record->base; \
					if (base.get() != NULL) \
					{ \
						if (evaluate_conditional_typename(base, value)) \
							return true; \
						try \
						{ \
							base = substitute_template_type_in_scope(base, \
							                                         record->scope); \
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
						if (base.get() != NULL && base != trait_type) \
							return evaluate_trait_type(base, value); \
					} \
					return false; \
				}; \
			if ((arg.value_member_name == "value" || \
			     arg.value_member_name == "__value") && \
			    owner_args.empty()) \
			{ \
				TypePtr owner_type; \
				if (find_template_type_substitution(arg.value_owner_template_name, \
				                                    owner_type)) \
				{ \
					try \
					{ \
						owner_type = substitute_template_type(owner_type); \
						bool value = false; \
						if (evaluate_trait_type(owner_type, value)) \
							return bool_result(value); \
					} \
					catch (const runtime_error&) \
					{ \
					} \
				} \
			} \
			if ((arg.value_member_name == "value" || \
			     arg.value_member_name == "__value") && \
			    (trait_owner_unqualified == "And" || \
			     trait_owner_unqualified == "conjunction" || \
			     trait_owner_unqualified == "Or" || \
			     trait_owner_unqualified == "disjunction") && \
			    !owner_args.empty()) \
			{ \
				bool is_and = trait_owner_unqualified == "And" || \
				              trait_owner_unqualified == "conjunction"; \
				bool value = is_and; \
				bool all_known = true; \
				for (size_t ai = 0; ai < owner_args.size(); ++ai) \
				{ \
					if (owner_args[ai].kind != TemplateArgumentKind::Type) \
					{ \
						all_known = false; \
						break; \
					} \
					bool elem = false; \
					if (!evaluate_trait_type(owner_args[ai].type, elem)) \
					{ \
						all_known = false; \
						continue; \
					} \
					if (is_and && !elem) \
						return bool_result(false); \
					if (!is_and && elem) \
						return bool_result(true); \
				} \
				if (all_known) \
					return bool_result(value); \
			} \
			if ((arg.value_member_name == "value" || \
			     arg.value_member_name == "__value") && \
			    !owner_args.empty()) \
			{ \
				TemplateDeclaration* alias = \
					const_cast<Parser*>(this)->find_alias_template( \
						NULL, \
						trait_owner_unqualified); \
				if (alias != NULL) \
				{ \
					try \
					{ \
						TypePtr alias_type = \
							const_cast<Parser*>(this)-> \
								instantiate_alias_template(alias, \
								                           owner_args); \
						bool value = false; \
						if (evaluate_trait_type(alias_type, value)) \
							return bool_result(value); \
					} \
					catch (const runtime_error&) \
					{ \
					} \
					if (function_template_candidate_instantiation_depth_ != 0) \
						return false; \
				} \
			} \
			if ((arg.value_member_name == "value" || \
			     arg.value_member_name == "__value") && \
			    trait_owner_unqualified == "conditional" && \
			    owner_args.size() >= 3) \
			{ \
				bool condition_value = false; \
				bool condition_known = false; \
				if (owner_args[0].kind == TemplateArgumentKind::Value && \
				    !owner_args[0].dependent) \
				{ \
					condition_value = owner_args[0].value != 0; \
					condition_known = true; \
				} \
				else if (owner_args[0].kind == TemplateArgumentKind::Type && \
				         evaluate_trait_type(owner_args[0].type, \
				                             condition_value)) \
					condition_known = true; \
				const TemplateArgument& selected = \
					condition_value ? owner_args[1] : owner_args[2]; \
				if (condition_known && \
				    selected.kind == TemplateArgumentKind::Type) \
				{ \
					bool value = false; \
					if (evaluate_trait_type(selected.type, value)) \
						return bool_result(value); \
				} \
			} \
			if ((arg.value_member_name == "value" || \
			     arg.value_member_name == "__value") && \
				    (trait_owner_unqualified == "is_class" || \
				     trait_owner_unqualified == "is_pointer" || \
				     trait_owner_unqualified == "__is_pointer" || \
				     trait_owner_unqualified == "is_reference" || \
				     trait_owner_unqualified == "__is_reference" || \
				     trait_owner_unqualified == "is_lvalue_reference" || \
				     trait_owner_unqualified == "is_rvalue_reference" || \
				     trait_owner_unqualified == "is_constructible" || \
				     trait_owner_unqualified == "__is_constructible" || \
				     trait_owner_unqualified == "is_nothrow_constructible" || \
				     trait_owner_unqualified == "__is_nothrow_constructible" || \
				     trait_owner_unqualified == "is_trivially_constructible" || \
				     trait_owner_unqualified == "__is_trivially_constructible" || \
				     trait_owner_unqualified == "is_copy_constructible" || \
				     trait_owner_unqualified == "is_nothrow_copy_constructible" || \
				     trait_owner_unqualified == "is_trivially_copy_constructible" || \
				     trait_owner_unqualified == "is_move_constructible" || \
				     trait_owner_unqualified == "is_nothrow_move_constructible" || \
				     trait_owner_unqualified == "is_trivially_move_constructible" || \
				     trait_owner_unqualified == "is_assignable" || \
				     trait_owner_unqualified == "__is_assignable" || \
				     trait_owner_unqualified == "is_nothrow_assignable" || \
				     trait_owner_unqualified == "__is_nothrow_assignable" || \
				     trait_owner_unqualified == "is_trivially_assignable" || \
				     trait_owner_unqualified == "__is_trivially_assignable" || \
				     trait_owner_unqualified == "is_copy_assignable" || \
				     trait_owner_unqualified == "is_nothrow_copy_assignable" || \
				     trait_owner_unqualified == "is_trivially_copy_assignable" || \
				     trait_owner_unqualified == "is_move_assignable" || \
				     trait_owner_unqualified == "is_nothrow_move_assignable" || \
				     trait_owner_unqualified == "is_trivially_move_assignable" || \
				     (hosted_compatibility_ && \
			      trait_owner_unqualified == "is_convertible") || \
			     trait_owner_unqualified == "__is_convertible" || \
			     trait_owner_unqualified == "__and_" || \
			     trait_owner_unqualified == "__or_" || \
			     trait_owner_unqualified == "__not_" || \
			     trait_owner_unqualified == "__has_esft_base")) \
		{ \
			bool value = false; \
			TypePtr synthetic = pa11::make_record_type( \
				trait_owner_unqualified + "<>", \
				"struct", \
				false, \
				NULL); \
			synthetic->template_primary_name = trait_owner_unqualified; \
			synthetic->template_arguments = \
				template_instance_arguments(owner_args); \
			if (evaluate_trait_type(synthetic, value)) \
				return bool_result(value); \
		} \
		if ((arg.value_member_name == "value" || \
		     arg.value_member_name == "__value") && \
		    (trait_owner_unqualified == "is_same" || \
		     trait_owner_unqualified == "__are_same") && \
		    owner_args.size() >= 2 && \
	    owner_args[0].kind == TemplateArgumentKind::Type && \
	    owner_args[1].kind == TemplateArgumentKind::Type) \
	{ \
		bool value = pa11::same_type(owner_args[0].type, \
		                             owner_args[1].type); \
			return bool_result(value); \
		} \
		if ((arg.value_member_name == "value" || \
		     arg.value_member_name == "__value") && \
		    (trait_owner_unqualified == "is_constructible" || \
		     trait_owner_unqualified == "__is_constructible") && \
		    !owner_args.empty()) \
		{ \
			vector<TypePtr> types; \
			bool valid_types = true; \
			for (size_t ti = 0; ti < owner_args.size(); ++ti) \
			{ \
				if (owner_args[ti].kind != TemplateArgumentKind::Type) \
				{ \
					valid_types = false; \
					break; \
					} \
					TypePtr resolved_type; \
					if (!resolve_dependent_trait_subject_type( \
						    owner_args[ti].type, \
						    resolved_type)) \
						return false; \
					types.push_back(resolved_type); \
				} \
				if (!valid_types) \
					return false; \
			bool value = const_cast<Parser*>(this)-> \
				is_constructible_type_trait(types); \
			TemplateArgument result = TemplateArgument::value_arg( \
				pa11::make_fundamental(FT_BOOL), \
				arg.value_negated ? (value ? 0 : 1) : (value ? 1 : 0)); \
			result.value_name = arg.value_name; \
			return cache_result(result); \
		} \
		if ((arg.value_member_name == "value" || \
		     arg.value_member_name == "__value") && \
		    (trait_owner_unqualified == "__is_convertible" || \
		     (hosted_compatibility_ && \
		      trait_owner_unqualified == "is_convertible")) && \
		    owner_args.size() >= 2 && \
		    owner_args[0].kind == TemplateArgumentKind::Type && \
		    owner_args[1].kind == TemplateArgumentKind::Type) \
		{ \
			Expr probe; \
			probe.valid = true; \
			TypePtr from_type; \
			TypePtr to_type; \
			if (!resolve_dependent_trait_subject_type( \
				    owner_args[0].type, \
				    from_type) || \
			    !resolve_dependent_trait_subject_type( \
				    owner_args[1].type, \
				    to_type)) \
				return false; \
			vector<TypePtr> types; \
			types.push_back(from_type); \
			types.push_back(to_type); \
			bool value = const_cast<Parser*>(this)-> \
				evaluate_builtin_type_trait("__is_convertible", types); \
		TemplateArgument result = TemplateArgument::value_arg( \
			pa11::make_fundamental(FT_BOOL), \
			arg.value_negated ? (value ? 0 : 1) : (value ? 1 : 0)); \
		result.value_name = arg.value_name; \
		return cache_result(result); \
	} \
	if (arg.value_member_name.empty()) \
	{ \
		TemplateDeclaration* declaration = NULL; \
		for (Scope* cur = current_scope(); cur != NULL && declaration == NULL; \
		     cur = cur->parent) \
		{ \
			map<Scope*, map<string, vector<TemplateDeclaration*> > >::const_iterator \
				sit = variable_templates_.find(cur); \
			if (sit == variable_templates_.end()) \
				continue; \
			map<string, vector<TemplateDeclaration*> >::const_iterator it = \
				sit->second.find(arg.value_owner_template_name); \
			if (it != sit->second.end() && !it->second.empty()) \
				declaration = it->second[0]; \
		} \
		if (declaration == NULL) \
			for (map<Scope*, map<string, vector<TemplateDeclaration*> > >::const_iterator \
				     sit = variable_templates_.begin(); \
			     sit != variable_templates_.end() && declaration == NULL; \
			     ++sit) \
			{ \
				map<string, vector<TemplateDeclaration*> >::const_iterator it = \
					sit->second.find(arg.value_owner_template_name); \
				if (it != sit->second.end() && !it->second.empty()) \
					declaration = it->second[0]; \
			} \
		if (declaration == NULL) \
			return false; \
		Binding* binding = \
			const_cast<Parser*>(this)->instantiate_variable_template( \
				declaration, \
				owner_args); \
		if (binding == NULL || !binding->has_constant) \
			throw runtime_error("dependent variable template not resolved"); \
		TemplateArgument result = TemplateArgument::value_arg( \
			arg.value_negated \
			? pa11::make_fundamental(FT_BOOL) \
			: expression_object_type(binding->type), \
			arg.value_negated \
			? (binding->constant_value == 0 ? 1 : 0) \
			: binding->constant_value); \
		result.value_name = arg.value_name; \
		return cache_result(result); \
	} \
	if (!arg.value_owner_template_name.empty()) \
	{ \
		TemplateArgument owner_pack; \
		if (find_template_value_substitution( \
			    arg.value_owner_template_name, \
			    owner_pack) && \
		    owner_pack.kind == TemplateArgumentKind::Pack) \
		{ \
			if (owner_pack.pack.size() != 1 || \
			    owner_pack.pack[0].kind != TemplateArgumentKind::Type) \
				return false; \
			owner = owner_pack.pack[0].type; \
		} \
		if (owner.get() == NULL) \
		{ \
			TypePtr owner_parameter = \
				pa11::make_template_parameter_type( \
					arg.value_owner_template_name); \
			TypePtr substituted_owner = \
				substitute_template_type(owner_parameter); \
			TypePtr bare_substituted = \
				substituted_owner.get() != NULL \
				? pa11::strip_cv(substituted_owner) : TypePtr(); \
			if (bare_substituted.get() != NULL && \
			    bare_substituted->kind != pa11::TypeKind::TemplateParameter) \
				owner = substituted_owner; \
		} \
	} \
	TemplateDeclaration* alias_declaration = NULL; \
	TemplateDeclaration* declaration = NULL; \
	if (owner.get() == NULL) \
	{ \
		for (Scope* cur = current_scope(); \
		     cur != NULL && alias_declaration == NULL && declaration == NULL; \
		     cur = cur->parent) \
		{ \
			alias_declaration = \
				const_cast<Parser*>(this)->find_alias_template( \
					cur, \
					arg.value_owner_template_name); \
			if (alias_declaration == NULL) \
				declaration = \
					const_cast<Parser*>(this)->find_class_template( \
						cur, \
						arg.value_owner_template_name); \
		} \
		if (alias_declaration == NULL && declaration == NULL) \
			alias_declaration = \
				const_cast<Parser*>(this)->find_alias_template( \
					NULL, \
					arg.value_owner_template_name); \
		if (alias_declaration == NULL && declaration == NULL) \
			for (map<Scope*, map<string, TemplateDeclaration*> >::const_iterator \
				     sit = alias_templates_.begin(); \
			     sit != alias_templates_.end() && alias_declaration == NULL; \
			     ++sit) \
			{ \
				map<string, TemplateDeclaration*>::const_iterator it = \
					sit->second.find(arg.value_owner_template_name); \
				if (it != sit->second.end()) \
					alias_declaration = it->second; \
			} \
		if (alias_declaration == NULL && declaration == NULL) \
			declaration = \
				const_cast<Parser*>(this)->find_class_template( \
					NULL, \
					arg.value_owner_template_name); \
		if (alias_declaration == NULL && declaration == NULL) \
		{ \
			for (map<Scope*, map<string, TemplateDeclaration*> >::const_iterator \
				     sit = class_templates_.begin(); \
			     sit != class_templates_.end() && declaration == NULL; \
			     ++sit) \
			{ \
				map<string, TemplateDeclaration*>::const_iterator it = \
					sit->second.find(arg.value_owner_template_name); \
				if (it != sit->second.end()) \
					declaration = it->second;
