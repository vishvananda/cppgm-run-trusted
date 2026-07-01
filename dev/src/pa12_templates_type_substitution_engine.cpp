#include "pa12_templates_function_support.h"
#include "pa12_templates_instance_support.h"
#include "pa12_templates_type_substitution_engine.h"
#include "pa12_types_support.h"

#include <algorithm>
#include <stdexcept>
#include <utility>
using namespace std;

namespace pa12 {
namespace internal {

const size_t kDependentTypeSubstitutionCacheLimit = 65536;

size_t dependent_type_cache_hash_combine(size_t seed, size_t value);
size_t dependent_type_cache_string_hash(const string& value);
bool hosted_nonrecord_member_typename_probe(
	bool hosted_compatibility,
	const vector<ActiveClassInstantiation>& active,
	const string& root_name,
	const string& suffix,
	TypePtr root_substitution);
bool dependent_typename_member_type_name(TypePtr type);
size_t shallow_type_cache_hash(TypePtr type);
size_t shallow_template_argument_cache_hash(const TemplateArgument& argument);
bool replayable_dependent_value_argument(const TemplateArgument& argument);
bool replayable_dependent_value_instance_argument(const pa11::TemplateInstanceArgument& argument);
bool dependent_decltype_has_template_argument_name(const string& spelling, const string& name);

bool TypeSubstitutionEngine::preserves_self_reference(const TypePtr& type) const
	{
		TypePtr bare_input = pa11::strip_cv(type);
		if (!type_structurally_dependent(bare_input) &&
		    !record_arguments_are_still_dependent(bare_input))
			return false;
		map<pair<const void*, string>, bool> contains_cache;
	bool cache_ready = false;
	size_t cache_key = 0;
	for (size_t si = p.template_type_substitutions_.size(); si > 0; --si)
		for (map<string, TypePtr>::const_iterator it =
			     p.template_type_substitutions_[si - 1].begin();
		     it != p.template_type_substitutions_[si - 1].end();
		     ++it) {
			TypePtr subst = it->second.get() != NULL
				? pa11::strip_cv(it->second) : TypePtr();
			if (subst.get() == NULL || subst.get() != bare_input.get())
				continue;
			if (!cache_ready)
			{
				cache_key = dependent_type_cache_hash_combine(
					0x51f,
					active_dependent_key(type));
				cache_key = dependent_type_cache_hash_combine(
					cache_key,
					p.record_template_arguments_.size());
				map<size_t, bool>::const_iterator cached =
					p.preserves_self_reference_cache_.find(cache_key);
				if (cached != p.preserves_self_reference_cache_.end())
					return cached->second;
				cache_ready = true;
			}
			pair<const void*, string> key(subst.get(), it->first);
			map<pair<const void*, string>, bool>::iterator cached =
				contains_cache.find(key);
			bool self_reference = cached != contains_cache.end()
				? cached->second
				: type_contains_parameter_name(it->second,
				                               it->first,
				                               p.record_template_arguments_);
			if (cached == contains_cache.end())
				contains_cache[key] = self_reference;
			if (self_reference ||
			    (subst->is_dependent_typename &&
			     !self_substitution_can_change(it->second)))
			{
				p.preserves_self_reference_cache_[cache_key] = true;
				return true;
			}
		}
	if (cache_ready)
		p.preserves_self_reference_cache_[cache_key] = false;
	return false;
}

bool TypeSubstitutionEngine::self_substitution_can_change(const TypePtr& type) const
{
	set<string> parameter_names;
	collect_type_parameter_names(type,
	                             p.record_template_arguments_,
	                             parameter_names);
	if (parameter_names.empty())
		return false;
	for (size_t si = p.template_type_substitutions_.size(); si > 0; --si)
		for (map<string, TypePtr>::const_iterator it =
			     p.template_type_substitutions_[si - 1].begin();
		     it != p.template_type_substitutions_[si - 1].end();
		     ++it) {
			if (parameter_names.count(it->first) == 0)
				continue;
			TypePtr subst = it->second.get() != NULL
				? pa11::strip_cv(it->second) : TypePtr();
			if (subst.get() == NULL)
				continue;
			if (subst->kind == pa11::TypeKind::TemplateParameter &&
			    subst->name == it->first)
				continue;
			return true;
		}
	return false;
}

TypeSubstitutionResult
TypeSubstitutionEngine::substitute_plain_dependent(const TypePtr& type) const
{
	if (type->dependent_typename_qualified ||
	    type->dependent_typename_template_id ||
	    type->dependent_typename_decltype ||
	    !type->template_arguments.empty() ||
	    !type->dependent_typename_template_argument_lists.empty())
		return TypeSubstitutionResult::none();
	TypePtr subst;
	if (!p.find_template_type_substitution(type->name, subst))
		return TypeSubstitutionResult::none();
	if (type_contains_parameter_name(subst,
	                                 type->name,
	                                 p.record_template_arguments_))
		return TypeSubstitutionResult::done(subst);
	return TypeSubstitutionResult::done(p.substitute_template_type(subst));
}

size_t TypeSubstitutionEngine::active_dependent_key(const TypePtr& type) const
{
	size_t key = shallow_type_cache_hash(type);
	key = dependent_type_cache_hash_combine(
		key,
		reinterpret_cast<uintptr_t>(p.current_scope()));
	key = dependent_type_cache_hash_combine(
		key,
		p.validating_template_definition_ ? 1 : 0);
	key = dependent_type_cache_hash_combine(
		key,
		p.function_template_candidate_instantiation_depth_);
	key = dependent_type_cache_hash_combine(
		key,
		p.template_type_substitutions_.size());
	key = dependent_type_cache_hash_combine(
		key,
		p.template_value_substitutions_.size());
	for (size_t i = 0; i < p.template_type_substitutions_.size(); ++i)
	{
		key = dependent_type_cache_hash_combine(key, i);
		for (map<string, TypePtr>::const_iterator it =
			     p.template_type_substitutions_[i].begin();
		     it != p.template_type_substitutions_[i].end();
		     ++it)
		{
			key = dependent_type_cache_hash_combine(
				key,
				dependent_type_cache_string_hash(it->first));
			key = dependent_type_cache_hash_combine(
				key,
				shallow_type_cache_hash(it->second));
		}
	}
	for (size_t i = 0; i < p.template_value_substitutions_.size(); ++i)
	{
		key = dependent_type_cache_hash_combine(key, i);
		for (map<string, TemplateArgument>::const_iterator it =
			     p.template_value_substitutions_[i].begin();
		     it != p.template_value_substitutions_[i].end();
		     ++it)
		{
			key = dependent_type_cache_hash_combine(
				key,
				dependent_type_cache_string_hash(it->first));
			key = dependent_type_cache_hash_combine(
				key,
				shallow_template_argument_cache_hash(it->second));
		}
	}
	return key;
}

bool TypeSubstitutionEngine::active_dependent_substitution(const TypePtr& type) const
{
	if (type.get() == NULL || !type->is_dependent_typename)
		return false;
	size_t type_key = reinterpret_cast<size_t>(type.get());
	if (find(p.active_dependent_type_substitution_types_.begin(),
	         p.active_dependent_type_substitution_types_.end(),
	         type_key) != p.active_dependent_type_substitution_types_.end())
		return true;
	for (size_t i = 0; i < p.active_dependent_type_substitution_types_.size();
	     ++i)
	{
		const pa11::Type* active =
			reinterpret_cast<const pa11::Type*>(
				p.active_dependent_type_substitution_types_[i]);
		if (active != NULL &&
		    active->is_dependent_typename &&
		    active->name == type->name &&
		    active->template_primary_name == type->template_primary_name &&
		    active->dependent_typename_qualified ==
			    type->dependent_typename_qualified &&
		    active->dependent_typename_template_id ==
			    type->dependent_typename_template_id &&
		    active->dependent_typename_decltype ==
			    type->dependent_typename_decltype &&
		    active->template_arguments.size() ==
			    type->template_arguments.size() &&
		    active->dependent_typename_template_argument_lists.size() ==
			    type->dependent_typename_template_argument_lists.size())
			return true;
	}
	if (p.active_dependent_type_substitution_keys_.empty())
		return false;
	size_t key = active_dependent_key(type);
	return find(p.active_dependent_type_substitution_keys_.begin(),
	            p.active_dependent_type_substitution_keys_.end(),
	            key) != p.active_dependent_type_substitution_keys_.end();
}

bool TypeSubstitutionEngine::concrete_substitution_context() const
{
	bool concrete =
		!p.validating_template_definition_ &&
		(!p.template_type_substitutions_.empty() ||
		 !p.template_value_substitutions_.empty());
	if (!concrete)
		return false;
	if (!p.template_type_substitutions_.empty())
		for (map<string, TypePtr>::const_iterator it =
			     p.template_type_substitutions_.back().begin();
		     it != p.template_type_substitutions_.back().end();
		     ++it) {
			bool pack_placeholder = false;
			TypePtr bare = it->second.get() != NULL
				? pa11::strip_cv(it->second) : TypePtr();
			if (bare.get() != NULL &&
			    bare->kind == pa11::TypeKind::TemplateParameter &&
			    p.active_type_parameter_pack(it->first) &&
			    !p.template_value_substitutions_.empty()) {
				map<string, TemplateArgument>::const_iterator pack =
					p.template_value_substitutions_.back().find(it->first);
				pack_placeholder =
					pack != p.template_value_substitutions_.back().end() &&
					pack->second.kind == TemplateArgumentKind::Pack;
				for (size_t pi = 0;
				     pack_placeholder && pi < pack->second.pack.size();
				     ++pi)
					if (template_argument_has_template_parameter(
						    pack->second.pack[pi],
						    p.record_template_arguments_))
						pack_placeholder = false;
			}
			if (!pack_placeholder && p.type_is_template_dependent(it->second))
				concrete = false;
		}
	if (!p.template_value_substitutions_.empty())
		for (map<string, TemplateArgument>::const_iterator it =
			     p.template_value_substitutions_.back().begin();
		     it != p.template_value_substitutions_.back().end();
		     ++it)
			if (template_argument_has_template_parameter(
				    it->second,
				    p.record_template_arguments_))
				concrete = false;
	return concrete;
}

bool TypeSubstitutionEngine::has_template_substitution_name(
	const string& name) const
{
	for (size_t i = 0; i < p.template_type_substitutions_.size(); ++i)
		if (p.template_type_substitutions_[i].find(name) !=
		    p.template_type_substitutions_[i].end())
			return true;
	for (size_t i = 0; i < p.template_value_substitutions_.size(); ++i)
		if (p.template_value_substitutions_[i].find(name) !=
		    p.template_value_substitutions_[i].end())
			return true;
	return false;
}

bool TypeSubstitutionEngine::unresolved_foreign_decltype_template_argument(
	const TypePtr& type,
	const string& message) const
{
	if (message.compare(0, 16, "name not found: ") != 0)
		return false;
	string name = message.substr(16);
	return type.get() != NULL &&
	       dependent_decltype_has_template_argument_name(type->name, name) &&
	       !has_template_substitution_name(name);
}

bool token_is_simple(const vector<Token>& tokens, size_t index, ETokenType type)
{
	return index < tokens.size() &&
	       tokens[index].kind == posttoken::TokenKind::Simple &&
	       tokens[index].type == type;
}

bool token_is_inside_template_argument_list(const vector<Token>& tokens,
                                            size_t index)
{
	int depth = 0;
	for (size_t i = 0; i < index && i < tokens.size(); ++i)
	{
		if (token_is_simple(tokens, i, OP_LT))
			++depth;
		else if (token_is_simple(tokens, i, OP_GT) && depth > 0)
			--depth;
	}
	return depth > 0;
}

bool decltype_identifier_is_template_argument(
	const vector<Token>& tokens,
	size_t index)
{
	if (index == 0 ||
	    !token_is_inside_template_argument_list(tokens, index) ||
	    (!token_is_simple(tokens, index - 1, OP_LT) &&
	     !token_is_simple(tokens, index - 1, OP_COMMA)))
		return false;
	size_t next = index + 1;
	if (token_is_simple(tokens, next, OP_DOTS))
		++next;
	return token_is_simple(tokens, next, OP_GT) ||
	       token_is_simple(tokens, next, OP_COMMA);
}

bool TypeSubstitutionEngine::dependent_decltype_has_unsubstituted_template_argument(
	const TypePtr& type,
	const vector<Token>& tokens) const
{
	if (type.get() == NULL)
		return false;
	set<string> seen;
	for (size_t i = 0; i < tokens.size(); ++i) {
		const Token& token = tokens[i];
		if (token.kind != posttoken::TokenKind::Identifier)
			continue;
		const string& name = token.source;
		if (!seen.insert(name).second)
			continue;
		if (!decltype_identifier_is_template_argument(tokens, i))
			continue;
		if (has_template_substitution_name(name))
			continue;
		Binding* binding = pa11::lookup_unqualified(p.current_scope(),
		                                            name,
		                                            pa11::LOOKUP_TYPE);
		TypePtr bound_type = binding != NULL && binding->type.get() != NULL
			? pa11::strip_cv(binding->type) : TypePtr();
		if (bound_type.get() != NULL &&
		    bound_type->kind != pa11::TypeKind::TemplateParameter &&
		    bound_type->kind != pa11::TypeKind::TemplateTemplateParameter)
			continue;
		return true;
	}
	return false;
}

TypeSubstitutionResult TypeSubstitutionEngine::substitute_dependent_decltype(
	const TypePtr& type,
	bool replay_errors_are_hard) const
{
	if (!type->dependent_typename_decltype ||
	    type->name.compare(0, 9, "decltype(") != 0 ||
	    (p.template_type_substitutions_.empty() &&
	     p.template_value_substitutions_.empty() &&
	     p.function_template_candidate_instantiation_depth_ == 0))
		return TypeSubstitutionResult::none();
	if (!replay_errors_are_hard)
		return TypeSubstitutionResult::none();
	vector<Token> replay_tokens;
	if (!collect_replay_tokens(type->name, replay_tokens)) {
		if (replay_errors_are_hard)
			throw runtime_error("failed to tokenize dependent decltype");
		return TypeSubstitutionResult::none();
	}
	if (dependent_decltype_has_unsubstituted_template_argument(type,
	                                                          replay_tokens))
		return TypeSubstitutionResult::none();
	Parser* self = const_cast<Parser*>(&p);
	vector<Token> saved_tokens;
	size_t saved_pos = self->pos_;
	bool saved_replaying = self->replaying_dependent_decltype_;
	TypePtr replayed;
	try {
		self->tokens_.swap(saved_tokens);
		self->tokens_.swap(replay_tokens);
		self->pos_ = 0;
		self->replaying_dependent_decltype_ = true;
		replayed = self->parse_decltype_specifier();
		self->expect_eof();
		} catch (const runtime_error& err) {
			string message = err.what();
			bool concrete = concrete_substitution_context();
		bool unresolved_candidate =
			p.function_template_candidate_instantiation_depth_ != 0 &&
			(message.compare(0, 16, "name not found: ") == 0 ||
			 (message == "cannot resolve call overload" &&
			  !(concrete && !p.active_class_instantiation_dependent())));
		bool unresolved_foreign_template_argument =
			unresolved_foreign_decltype_template_argument(type, message);
		self->tokens_.swap(replay_tokens);
		self->tokens_.swap(saved_tokens);
		self->pos_ = saved_pos;
		self->replaying_dependent_decltype_ = saved_replaying;
		if (replay_errors_are_hard &&
		    !unresolved_candidate &&
		    !unresolved_foreign_template_argument)
			throw;
		return TypeSubstitutionResult::none();
	}
	self->tokens_.swap(replay_tokens);
	self->tokens_.swap(saved_tokens);
	self->pos_ = saved_pos;
	self->replaying_dependent_decltype_ = saved_replaying;
	if (replayed.get() == NULL)
		return TypeSubstitutionResult::none();
		if (replayed->is_dependent_typename &&
		    replayed->dependent_typename_decltype &&
		    replayed->name == type->name &&
		    replayed->template_arguments.empty())
		{
			if (!type->template_arguments.empty() ||
			    !type->dependent_typename_template_argument_lists.empty())
				return TypeSubstitutionResult::none();
			return TypeSubstitutionResult::done(type);
		}
	return TypeSubstitutionResult::done(p.substitute_template_type(replayed));
}

TypeSubstitutionResult
TypeSubstitutionEngine::substitute_dependent_arguments(
	const TypePtr& type,
	bool concrete_context) const
{
	if (type->template_arguments.empty() &&
	    type->dependent_typename_template_argument_lists.empty())
		return TypeSubstitutionResult::none();
	vector<TemplateArgument> original_args;
	vector<TemplateArgument> substituted_args;
	string primary_name = type->template_primary_name.empty()
		? type->name : type->template_primary_name;
	size_t primary_sep = primary_name.rfind("::");
	if (primary_sep != string::npos)
		primary_name = primary_name.substr(primary_sep + 2);
	size_t primary_args = primary_name.find('<');
	if (primary_args != string::npos)
		primary_name = primary_name.substr(0, primary_args);
	TemplateDeclaration* primary_template = primary_name.empty()
		? NULL
		: const_cast<Parser*>(&p)->find_class_template(NULL, primary_name);
	for (size_t i = 0; i < type->template_arguments.size(); ++i) {
		TemplateArgument arg =
			raw_template_argument_from_instance_argument(
				type->template_arguments[i]);
		original_args.push_back(arg);
		TemplateArgument substituted = p.substitute_template_argument(arg);
		bool primary_pack =
			primary_template != NULL &&
			i < primary_template->parameters.size() &&
			primary_template->parameters[i].is_pack &&
			template_argument_has_template_parameter(
				arg,
				p.record_template_arguments_);
		if (primary_pack ||
		    substituted.kind == TemplateArgumentKind::Pack ||
		    substituted.pack_expansion) {
			vector<TemplateArgument> expanded =
				p.expand_template_argument_pack(substituted);
			for (size_t ei = 0; ei < expanded.size(); ++ei) {
				TemplateArgument element =
					p.substitute_template_argument(expanded[ei]);
				if (element.kind == TemplateArgumentKind::Pack)
					substituted_args.insert(substituted_args.end(),
					                        element.pack.begin(),
					                        element.pack.end());
				else
					substituted_args.push_back(element);
			}
		} else {
			substituted_args.push_back(substituted);
		}
	}
	substituted_args = flatten_template_argument_packs(substituted_args);
	vector<vector<TemplateArgument> > original_lists;
	vector<vector<TemplateArgument> > substituted_lists;
	for (size_t i = 0;
	     i < type->dependent_typename_template_argument_lists.size();
	     ++i) {
		vector<TemplateArgument> original_list;
		vector<TemplateArgument> substituted_list;
		for (size_t j = 0;
		     j < type->dependent_typename_template_argument_lists[i].size();
		     ++j) {
			TemplateArgument arg =
				raw_template_argument_from_instance_argument(
					type->dependent_typename_template_argument_lists[i][j]);
			original_list.push_back(arg);
			substituted_list.push_back(p.substitute_template_argument(arg));
		}
		original_lists.push_back(original_list);
		substituted_lists.push_back(substituted_list);
	}
	bool changed =
		p.template_argument_key(original_args) !=
		p.template_argument_key(substituted_args);
	for (size_t i = 0; !changed && i < original_lists.size(); ++i)
		if (p.template_argument_key(original_lists[i]) !=
		    p.template_argument_key(substituted_lists[i]))
			changed = true;
	if (!changed &&
	    (concrete_context ||
	     p.function_template_candidate_instantiation_depth_ != 0)) {
		TypePtr retry = p.resolve_dependent_typename_type(type);
		if (retry.get() != NULL && retry != type)
			return TypeSubstitutionResult::done(
				p.substitute_template_type(retry));
	}
	if (!changed)
		return TypeSubstitutionResult::none();
	TypePtr out = pa11::make_dependent_typename_type(
		type->name,
		type->dependent_typename_qualified,
		type->dependent_typename_template_id,
		type->dependent_typename_decltype);
	out->template_primary_name = type->template_primary_name;
	out->is_extern_template_instantiation =
		type->is_extern_template_instantiation;
	for (size_t i = 0; i < substituted_args.size(); ++i)
		out->template_arguments.push_back(
			template_instance_argument(substituted_args[i]));
	for (size_t i = 0; i < substituted_lists.size(); ++i) {
		vector<pa11::TemplateInstanceArgument> argument_list;
		for (size_t j = 0; j < substituted_lists[i].size(); ++j)
			argument_list.push_back(
				template_instance_argument(substituted_lists[i][j]));
		out->dependent_typename_template_argument_lists.push_back(
			argument_list);
	}
	TypePtr retry = p.resolve_dependent_typename_type(out);
	if (retry.get() != NULL && retry != out)
		return TypeSubstitutionResult::done(p.substitute_template_type(retry));
	return TypeSubstitutionResult::done(out);
}

TypeSubstitutionResult
TypeSubstitutionEngine::substitute_dependent_builtin(const TypePtr& type) const
{
	string transform_name = !type->template_primary_name.empty()
		? type->template_primary_name : type->name;
	size_t transform_args = transform_name.find('<');
	if (transform_args != string::npos)
		transform_name = transform_name.substr(0, transform_args);
	if (internal_type_transform_name(transform_name) &&
	    type->template_arguments.size() == 1) {
		TemplateArgument arg =
			raw_template_argument_from_instance_argument(
				type->template_arguments[0]);
		arg = p.substitute_template_argument(arg);
		if (arg.kind == TemplateArgumentKind::Type &&
		    !type_structurally_dependent(arg.type))
			return TypeSubstitutionResult::done(
				apply_internal_type_transform(transform_name, arg.type));
	}
	if (type->template_primary_name == "__type_pack_element" ||
	    type->name == "__type_pack_element") {
		vector<TemplateArgument> arguments;
		for (size_t i = 0; i < type->template_arguments.size(); ++i)
			arguments.push_back(raw_template_argument_from_instance_argument(
				type->template_arguments[i]));
		if (arguments.empty()) {
			map<const void*, vector<TemplateArgument> >::const_iterator stored =
				p.record_template_arguments_.find(type.get());
			if (stored != p.record_template_arguments_.end())
				arguments = stored->second;
		}
		TypePtr selected;
		if (const_cast<Parser*>(&p)->try_resolve_type_pack_element(
			    arguments,
			    selected) &&
		    selected.get() != NULL)
			return TypeSubstitutionResult::done(selected);
	}
	if (type->template_primary_name == "__make_integer_seq" ||
	    type->name == "__make_integer_seq") {
		vector<TemplateArgument> arguments;
		for (size_t i = 0; i < type->template_arguments.size(); ++i) {
			TemplateArgument arg =
				raw_template_argument_from_instance_argument(
					type->template_arguments[i]);
			arguments.push_back(p.substitute_template_argument(arg));
		}
		TypePtr expanded =
			const_cast<Parser*>(&p)->make_integer_sequence_type(arguments);
		if (expanded.get() != NULL && !p.type_is_template_dependent(expanded))
			return TypeSubstitutionResult::done(expanded);
	}
	return TypeSubstitutionResult::none();
}

bool TypeSubstitutionEngine::split_dependent_root(
	const TypePtr& type,
	string& root_name,
	string& suffix) const
{
	root_name = type->name;
	size_t root_sep = root_name.find("::");
	if (root_sep != string::npos) {
		suffix = type->name.substr(root_sep);
		root_name = root_name.substr(0, root_sep);
	}
	size_t root_template = root_name.find('<');
	if (root_template != string::npos)
		root_name = root_name.substr(0, root_template);
	return !root_name.empty();
}

bool TypeSubstitutionEngine::find_dependent_root_substitution(
	const TypePtr& type,
	const string& root_name,
	TypePtr& root_subst) const
{
	if (p.find_template_type_substitution(root_name, root_subst))
		return true;
	if (type->template_primary_name.empty() || type->template_arguments.empty())
		return false;
	TemplateDeclaration* alias =
		const_cast<Parser*>(&p)->find_alias_template(
			NULL,
			type->template_primary_name);
	if (alias != NULL)
		for (size_t ai = 0;
		     ai < alias->parameters.size() &&
		     ai < type->template_arguments.size();
		     ++ai) {
			if (alias->parameters[ai].name != root_name ||
			    alias->parameters[ai].kind != TemplateParameterKind::Type)
				continue;
			TemplateArgument arg =
				p.template_argument_from_instance_argument(
					type->template_arguments[ai]);
			arg = p.substitute_template_argument(arg);
			if (arg.kind == TemplateArgumentKind::Type) {
				root_subst = arg.type;
				return true;
			}
			break;
		}
	if (root_name == "_Tp" && type->template_arguments.size() == 1) {
		TemplateArgument arg =
			p.template_argument_from_instance_argument(
				type->template_arguments[0]);
		arg = p.substitute_template_argument(arg);
		if (arg.kind == TemplateArgumentKind::Type) {
			root_subst = arg.type;
			return true;
		}
	}
	if (root_name == "_Tp" &&
	    (type->template_primary_name == "__pointer" ||
	     type->template_primary_name == "__c_pointer" ||
	     type->template_primary_name == "__v_pointer" ||
	     type->template_primary_name == "__cv_pointer"))
		return p.find_template_type_substitution("_Alloc", root_subst);
	return false;
}

TypeSubstitutionResult
TypeSubstitutionEngine::substitute_dependent_qualified_root(
	const TypePtr& type,
	bool concrete_context) const
{
	if (!type->dependent_typename_qualified)
		return TypeSubstitutionResult::none();
	string root_name;
	string suffix;
	split_dependent_root(type, root_name, suffix);
	TypePtr root_subst;
	if (!find_dependent_root_substitution(type, root_name, root_subst))
		return TypeSubstitutionResult::none();
	TypePtr substituted_root = p.substitute_template_type(root_subst);
	if (p.type_is_template_dependent(substituted_root)) {
		string replacement_root;
		TypePtr bare_root = pa11::strip_cv(substituted_root);
		if (bare_root->kind == pa11::TypeKind::TemplateParameter)
			replacement_root = bare_root->name;
		else if (!bare_root->template_primary_name.empty())
			replacement_root = bare_root->template_primary_name + "<>";
		if (!replacement_root.empty() && replacement_root != root_name) {
			TypePtr out = pa11::make_dependent_typename_type(
				replacement_root + suffix,
				type->dependent_typename_qualified,
				type->dependent_typename_template_id,
				type->dependent_typename_decltype);
			out->template_primary_name = type->template_primary_name;
			for (size_t i = 0; i < type->template_arguments.size(); ++i) {
				TemplateArgument arg =
					p.template_argument_from_instance_argument(
						type->template_arguments[i]);
				arg = p.substitute_template_argument(arg);
				out->template_arguments.push_back(
					template_instance_argument(arg));
			}
			for (size_t i = 0;
			     i < type->dependent_typename_template_argument_lists.size();
			     ++i) {
				vector<pa11::TemplateInstanceArgument> argument_list;
				for (size_t j = 0;
				     j < type->dependent_typename_template_argument_lists[i].size();
				     ++j) {
					TemplateArgument arg =
						p.template_argument_from_instance_argument(
							type->dependent_typename_template_argument_lists[i][j]);
					arg = p.substitute_template_argument(arg);
					argument_list.push_back(template_instance_argument(arg));
				}
				out->dependent_typename_template_argument_lists.push_back(
					argument_list);
			}
			return TypeSubstitutionResult::done(out);
		}
	} else if (concrete_context && !p.active_class_instantiation_dependent()) {
		if (hosted_nonrecord_member_typename_probe(p.hosted_compatibility_,
		                                           p.active_class_instantiations_,
		                                           root_name,
		                                           suffix,
		                                           substituted_root))
			return TypeSubstitutionResult::done(type);
		TypePtr resolved = p.resolve_dependent_typename_type(type);
		if (resolved.get() != NULL && resolved != type)
			return TypeSubstitutionResult::done(
				p.substitute_template_type(resolved));
			throw runtime_error("dependent typename not resolved");
	}
	return TypeSubstitutionResult::none();
}

bool TypeSubstitutionEngine::dependent_root_still_dependent(const TypePtr& type) const
{
	if (!type->dependent_typename_qualified)
		return false;
	string root_name;
	string suffix;
	split_dependent_root(type, root_name, suffix);
	TypePtr root_subst;
	if (!find_dependent_root_substitution(type, root_name, root_subst))
		return false;
	TypePtr substituted_root = p.substitute_template_type(root_subst);
	if (hosted_nonrecord_member_typename_probe(p.hosted_compatibility_,
	                                           p.active_class_instantiations_,
	                                           root_name,
	                                           suffix,
	                                           substituted_root))
		return true;
	return p.type_is_template_dependent(substituted_root);
}

bool TypeSubstitutionEngine::dependent_primary_still_dependent(const TypePtr& type) const
{
	if (type->template_primary_name.empty())
		return false;
	TemplateArgument template_subst;
	if (p.find_template_value_substitution(type->template_primary_name,
	                                       template_subst))
		return template_subst.kind == TemplateArgumentKind::Template &&
		       template_subst.template_declaration == NULL;
	TypePtr bare = pa11::strip_cv(type);
	return bare->kind == pa11::TypeKind::Record &&
	       bare->is_template_specialization &&
	       const_cast<Parser*>(&p)->class_template_declaration_for_match(bare) ==
		       NULL;
}

bool TypeSubstitutionEngine::dependent_arguments_still_dependent(
	const TypePtr& type) const
{
	if (type->template_arguments.empty())
		return template_type_has_template_parameter(
			type,
			p.record_template_arguments_);
	for (size_t i = 0; i < type->template_arguments.size(); ++i) {
		if (template_instance_argument_has_template_parameter(
			    type->template_arguments[i],
			    p.record_template_arguments_) &&
		    p.function_template_candidate_instantiation_depth_ == 0 &&
		    active_template_match_parser != &p)
			return true;
		TemplateArgument arg =
			p.template_argument_from_instance_argument(
				type->template_arguments[i]);
		if (template_argument_has_template_parameter(
			    arg,
			    p.record_template_arguments_))
			return true;
	}
	for (size_t i = 0;
	     i < type->dependent_typename_template_argument_lists.size();
	     ++i)
		for (size_t j = 0;
		     j < type->dependent_typename_template_argument_lists[i].size();
		     ++j) {
			const pa11::TemplateInstanceArgument& inst =
				type->dependent_typename_template_argument_lists[i][j];
			if (template_instance_argument_has_template_parameter(
				    inst,
				    p.record_template_arguments_) &&
			    p.function_template_candidate_instantiation_depth_ == 0 &&
			    active_template_match_parser != &p)
				return true;
			TemplateArgument arg =
				p.template_argument_from_instance_argument(inst);
			if (template_argument_has_template_parameter(
				    arg,
				    p.record_template_arguments_))
				return true;
		}
	return false;
}

bool TypeSubstitutionEngine::dependent_typename_still_dependent(
	const TypePtr& type) const
{
	return dependent_root_still_dependent(type) ||
	       dependent_primary_still_dependent(type) ||
	       dependent_arguments_still_dependent(type);
}

TypePtr TypeSubstitutionEngine::substitute_dependent_typename(
	const TypePtr& type) const
{
	TypeSubstitutionResult plain = substitute_plain_dependent(type);
	if (plain.handled)
		return plain.type;
	const void* type_key = type.get();
	if (active_dependent_substitution(type))
		return type;
	size_t cache_key = active_dependent_key(type);
	bool cacheable_dependent_type = true;
	if (cacheable_dependent_type)
	{
		map<size_t, TypePtr>::const_iterator cached =
			p.dependent_type_substitution_cache_.find(cache_key);
		if (cached != p.dependent_type_substitution_cache_.end())
			return cached->second;
	}
	auto remember_dependent_cache = [&](TypePtr result) -> TypePtr {
		if (cacheable_dependent_type)
		{
			p.dependent_type_substitution_cache_[cache_key] = result;
			if (p.dependent_type_substitution_cache_.size() >
			    kDependentTypeSubstitutionCacheLimit)
				p.dependent_type_substitution_cache_.clear();
		}
		return result;
	};
	ActiveDependentTypeSubstitution active(
		p.active_dependent_type_substitution_keys_,
		p.active_dependent_type_substitution_types_,
		cache_key,
		type_key);
	bool concrete = concrete_substitution_context();
	bool replay_hard =
		p.function_template_candidate_instantiation_depth_ != 0 ||
		(concrete && !p.active_class_instantiation_dependent());
	TypeSubstitutionResult replay =
		substitute_dependent_decltype(type, replay_hard);
	if (replay.handled)
		return remember_dependent_cache(replay.type);
	TypePtr resolved = p.resolve_dependent_typename_type(type);
	if (resolved.get() != NULL && resolved != type) {
		if (resolved->is_dependent_typename &&
		    resolved->name == type->name &&
		    resolved->template_primary_name == type->template_primary_name &&
			    resolved->template_arguments.size() ==
				    type->template_arguments.size()) {
				return remember_dependent_cache(type);
			}
			TypePtr substituted = p.substitute_template_type(resolved);
			return remember_dependent_cache(substituted);
		}
	TypePtr current = type;
	TypeSubstitutionResult arguments =
		substitute_dependent_arguments(current, concrete);
	if (arguments.handled)
		current = arguments.type;
	TypeSubstitutionResult builtin = substitute_dependent_builtin(current);
	if (builtin.handled)
		return remember_dependent_cache(builtin.type);
	TypeSubstitutionResult qualified =
		substitute_dependent_qualified_root(current, concrete);
		if (qualified.handled)
			return remember_dependent_cache(qualified.type);
		if (current->dependent_typename_qualified &&
		    current->dependent_typename_template_id &&
		    dependent_typename_member_type_name(current) &&
		    !p.active_class_instantiations_.empty() &&
		    p.function_template_candidate_instantiation_depth_ == 0)
		{
			return remember_dependent_cache(current);
		}
			if (!dependent_typename_still_dependent(current))
				throw runtime_error("dependent typename not resolved");
	return remember_dependent_cache(current);
}

TypeSubstitutionResult TypeSubstitutionEngine::substitute_simple(
	const TypePtr& type) const
{
	if (type->kind == pa11::TypeKind::TemplateParameter) {
		TypePtr subst;
		if (p.find_template_type_substitution(type->name, subst))
			return TypeSubstitutionResult::done(subst);
		return TypeSubstitutionResult::done(type);
	}
	if (type->kind == pa11::TypeKind::Cv)
		return TypeSubstitutionResult::done(
			pa11::make_cv(p.substitute_template_type(type->base), type->cv));
	if (type->kind == pa11::TypeKind::Pointer)
		return TypeSubstitutionResult::done(
			pa11::make_pointer(p.substitute_template_type(type->base)));
	if (type->kind == pa11::TypeKind::LValueReference) {
		TypePtr base = p.substitute_template_type(type->base);
		if (base->kind == pa11::TypeKind::LValueReference ||
		    base->kind == pa11::TypeKind::RValueReference)
			return TypeSubstitutionResult::done(
				pa11::make_lvalue_reference(base->base));
		return TypeSubstitutionResult::done(pa11::make_lvalue_reference(base));
	}
	if (type->kind == pa11::TypeKind::RValueReference) {
		TypePtr base = p.substitute_template_type(type->base);
		if (base->kind == pa11::TypeKind::LValueReference)
			return TypeSubstitutionResult::done(base);
		if (base->kind == pa11::TypeKind::RValueReference)
			return TypeSubstitutionResult::done(
				pa11::make_rvalue_reference(base->base));
		return TypeSubstitutionResult::done(pa11::make_rvalue_reference(base));
	}
	if (type->kind == pa11::TypeKind::MemberPointer)
		return TypeSubstitutionResult::done(
			pa11::make_member_pointer(
				p.substitute_template_type(type->member_class),
				p.substitute_template_type(type->base)));
	return TypeSubstitutionResult::none();
}

bool TypeSubstitutionEngine::record_arguments_are_still_dependent(
	const TypePtr& type) const
{
	if (type.get() == NULL)
		return false;
	size_t cache_key = dependent_type_cache_hash_combine(
		0x5a1d,
		reinterpret_cast<uintptr_t>(type.get()));
	cache_key = dependent_type_cache_hash_combine(
		cache_key,
		p.record_template_arguments_.size());
	map<const void*, vector<TemplateArgument> >::const_iterator args =
		p.record_template_arguments_.find(type.get());
	if (args != p.record_template_arguments_.end())
	{
		cache_key = dependent_type_cache_hash_combine(
			cache_key,
			args->second.size());
		for (size_t i = 0; i < args->second.size(); ++i)
			cache_key = dependent_type_cache_hash_combine(
				cache_key,
				shallow_template_argument_cache_hash(args->second[i]));
	}
	else
		cache_key = dependent_type_cache_hash_combine(
			cache_key,
			type->template_arguments.size());
	map<size_t, bool>::const_iterator cached =
		p.record_arguments_still_dependent_cache_.find(cache_key);
	if (cached != p.record_arguments_still_dependent_cache_.end())
		return cached->second;
	bool result = false;
	if (args != p.record_template_arguments_.end()) {
		for (size_t i = 0; i < args->second.size(); ++i)
			if (template_argument_has_template_parameter(
				    args->second[i],
				    p.record_template_arguments_) ||
			    replayable_dependent_value_argument(args->second[i]))
			{
				result = true;
				break;
		}
		p.record_arguments_still_dependent_cache_[cache_key] = result;
		if (p.record_arguments_still_dependent_cache_.size() >
		    kDependentTypeSubstitutionCacheLimit)
			p.record_arguments_still_dependent_cache_.clear();
		return result;
	}
	for (size_t i = 0; i < type->template_arguments.size(); ++i)
		if (template_instance_argument_has_template_parameter(
			    type->template_arguments[i],
			    p.record_template_arguments_) ||
		    replayable_dependent_value_instance_argument(
			    type->template_arguments[i]))
		{
			result = true;
			break;
		}
	p.record_arguments_still_dependent_cache_[cache_key] = result;
	if (p.record_arguments_still_dependent_cache_.size() >
	    kDependentTypeSubstitutionCacheLimit)
		p.record_arguments_still_dependent_cache_.clear();
	return result;
}

string TypeSubstitutionEngine::record_primary_name(const TypePtr& type) const
{
	string name = type->template_primary_name.empty()
		? type->name : type->template_primary_name;
	size_t args = name.find('<');
	if (args != string::npos)
		name = name.substr(0, args);
	return name;
}

bool TypeSubstitutionEngine::argument_count_too_large(
	TemplateDeclaration* declaration,
	const vector<TemplateArgument>& args) const
{
	if (declaration == NULL)
		return false;
	for (size_t i = 0; i < declaration->parameters.size(); ++i)
		if (declaration->parameters[i].is_pack)
			return false;
	return args.size() > declaration->parameters.size();
}

bool TypeSubstitutionEngine::argument_count_too_small(
	TemplateDeclaration* declaration,
	const vector<TemplateArgument>& args) const
{
	if (declaration == NULL)
		return false;
	size_t required = 0;
	for (size_t i = 0; i < declaration->parameters.size(); ++i)
		if (!declaration->parameters[i].has_default &&
		    !declaration->parameters[i].is_pack)
			++required;
	return args.size() < required;
}

TypeSubstitutionResult
TypeSubstitutionEngine::substitute_template_template_record(
	const TypePtr& type,
	const string& primary_name) const
{
	TemplateArgument template_subst;
	if (primary_name.empty() ||
	    !p.find_template_value_substitution(primary_name, template_subst) ||
	    template_subst.kind != TemplateArgumentKind::Template ||
	    template_subst.template_declaration == NULL)
		return TypeSubstitutionResult::none();
	map<const void*, vector<TemplateArgument> >::const_iterator stored =
		p.record_template_arguments_.find(type.get());
	vector<TemplateArgument> substituted;
	if (stored != p.record_template_arguments_.end()) {
		for (size_t i = 0; i < stored->second.size(); ++i) {
			TemplateArgument arg =
				p.substitute_template_argument(stored->second[i]);
			vector<TemplateArgument> expanded =
				p.expand_template_argument_pack(arg);
			for (size_t j = 0; j < expanded.size(); ++j) {
				TemplateArgument element =
					p.substitute_template_argument(expanded[j]);
				if (element.kind == TemplateArgumentKind::Pack)
					substituted.insert(substituted.end(),
					                   element.pack.begin(),
					                   element.pack.end());
				else
					substituted.push_back(element);
			}
		}
	} else {
		for (size_t i = 0; i < type->template_arguments.size(); ++i) {
			TemplateArgument arg =
				raw_template_argument_from_instance_argument(
					type->template_arguments[i]);
			arg = p.substitute_template_argument(arg);
			vector<TemplateArgument> expanded =
				p.expand_template_argument_pack(arg);
			substituted.insert(substituted.end(),
			                   expanded.begin(),
			                   expanded.end());
		}
	}
	substituted = flatten_template_argument_packs(substituted);
	if (argument_count_too_large(template_subst.template_declaration,
	                             substituted) ||
	    argument_count_too_small(template_subst.template_declaration,
	                             substituted))
		throw runtime_error("template argument arity mismatch");
	Parser* self = const_cast<Parser*>(&p);
	return TypeSubstitutionResult::done(
		template_subst.template_declaration->kind ==
		TemplateDeclarationKind::Alias
		? self->instantiate_alias_template(template_subst.template_declaration,
		                                   substituted)
		: self->instantiate_class_template(template_subst.template_declaration,
		                                   substituted));
}

void TypeSubstitutionEngine::record_source_arguments(
	const TypePtr& type,
	vector<TemplateArgument>& fallback_args,
	const vector<TemplateArgument>*& source_args) const
{
	map<const void*, vector<TemplateArgument> >::const_iterator stored =
		p.record_template_arguments_.find(type.get());
	if (stored != p.record_template_arguments_.end()) {
		source_args = &stored->second;
		return;
	}
	if (type->template_arguments.empty())
		return;
	for (size_t i = 0; i < type->template_arguments.size(); ++i) {
		TemplateArgument arg =
			raw_template_argument_from_instance_argument(
				type->template_arguments[i]);
			if (arg.kind == TemplateArgumentKind::Pack &&
			    arg.pack.size() == 1 &&
			    arg.pack[0].kind != TemplateArgumentKind::Pack &&
			    single_instance_pack_element_is_expansion(arg.pack[0])) {
				arg = arg.pack[0];
				arg.pack_expansion = true;
			} else if (arg.kind == TemplateArgumentKind::Type &&
			           arg.type.get() != NULL) {
				TypePtr bare_arg = pa11::strip_cv(arg.type);
				if (bare_arg->kind == pa11::TypeKind::TemplateParameter &&
				    p.active_type_parameter_pack(bare_arg->name))
					arg.pack_expansion = true;
			}
			fallback_args.push_back(arg);
		}
	source_args = &fallback_args;
}

TemplateDeclaration* TypeSubstitutionEngine::find_record_declaration(
	const TypePtr& type,
	const string& primary_name,
	const vector<TemplateArgument>* source_args) const
{
	map<const void*, TemplateDeclaration*>::const_iterator decl =
		p.record_template_declarations_.find(type.get());
	TemplateDeclaration* record_decl =
		decl != p.record_template_declarations_.end() ? decl->second : NULL;
	Parser* self = const_cast<Parser*>(&p);
	if (record_decl == NULL && source_args != NULL && !primary_name.empty()) {
		if (type->scope != NULL && type->scope->parent != NULL)
			record_decl = self->find_class_template(type->scope->parent,
			                                        primary_name);
		if (record_decl == NULL)
			record_decl = self->class_template_declaration_for_match(type);
	}
	if (record_decl == NULL && source_args != NULL && !primary_name.empty()) {
		record_decl = self->find_class_template(NULL, primary_name);
		if (record_decl == NULL) {
			TemplateDeclaration* unique = NULL;
			for (map<Scope*, map<string, TemplateDeclaration*> >::const_iterator
				     sit = p.class_templates_.begin();
			     sit != p.class_templates_.end();
			     ++sit) {
				map<string, TemplateDeclaration*>::const_iterator it =
					sit->second.find(primary_name);
				if (it == sit->second.end() ||
				    it->second->class_specialization)
					continue;
				if (unique != NULL && unique != it->second) {
					unique = NULL;
					break;
				}
				unique = it->second;
			}
			record_decl = unique;
		}
	}
	if (record_decl != NULL && record_decl->class_specialization) {
		TemplateDeclaration* primary =
			self->find_class_template(record_decl->owner, record_decl->name);
		if (primary != NULL && !primary->class_specialization)
			record_decl = primary;
	}
	return record_decl;
}

TypeSubstitutionResult
TypeSubstitutionEngine::substitute_primary_pack_record(
	const TypePtr& type,
	TemplateDeclaration* record_decl) const
{
	if (record_decl == NULL ||
	    !record_decl->class_specialization ||
	    !template_instance_arguments_have_pack(type->template_arguments))
		return TypeSubstitutionResult::none();
	Parser* self = const_cast<Parser*>(&p);
	TemplateDeclaration* primary =
		self->find_class_template(record_decl->owner, record_decl->name);
	bool primary_has_pack = false;
	if (primary != NULL)
		for (size_t pi = 0; pi < primary->parameters.size(); ++pi)
			if (primary->parameters[pi].is_pack)
				primary_has_pack = true;
	if (primary == NULL ||
	    (type->template_arguments.size() > primary->parameters.size() &&
	     !primary_has_pack))
		return TypeSubstitutionResult::none();
	vector<TemplateArgument> substituted;
	for (size_t i = 0; i < type->template_arguments.size(); ++i) {
		TemplateArgument original =
			raw_template_argument_from_instance_argument(
				type->template_arguments[i]);
		TemplateArgument arg = p.substitute_template_argument(original);
		TypePtr original_type = original.kind == TemplateArgumentKind::Type
			? pa11::strip_cv(original.type) : TypePtr();
		bool whole_primary_type =
			i < primary->parameters.size() &&
			!primary->parameters[i].is_pack &&
			original_type.get() != NULL &&
			(original_type->kind == pa11::TypeKind::Function ||
			 original_type->kind == pa11::TypeKind::MemberPointer);
		vector<TemplateArgument> expanded = whole_primary_type
			? vector<TemplateArgument>(1, arg)
			: p.expand_template_argument_pack(arg);
		for (size_t j = 0; j < expanded.size(); ++j) {
			TemplateArgument element =
				p.substitute_template_argument(expanded[j]);
			if (element.kind == TemplateArgumentKind::Pack)
				substituted.insert(substituted.end(),
				                   element.pack.begin(),
				                   element.pack.end());
			else
				substituted.push_back(element);
		}
	}
	substituted = flatten_template_argument_packs(substituted);
	return TypeSubstitutionResult::done(
		self->instantiate_class_template(primary, substituted));
}

vector<TemplateArgument>
TypeSubstitutionEngine::expand_substituted_record_argument(
	TemplateDeclaration* record_decl,
	const vector<TemplateArgument>& source_args,
	size_t& index) const
{
	const TemplateArgument& original = source_args[index];
	TemplateArgument arg = p.substitute_template_argument(original);
	size_t produced_pack_size =
		arg.kind == TemplateArgumentKind::Pack ? arg.pack.size() : 0;
	TypePtr original_type = original.kind == TemplateArgumentKind::Type
		? pa11::strip_cv(original.type) : TypePtr();
	bool function_type =
		original_type.get() != NULL &&
		(original_type->kind == pa11::TypeKind::Function ||
		 original_type->kind == pa11::TypeKind::MemberPointer);
	bool primary_pack_slot =
		(index < record_decl->parameters.size() &&
		 record_decl->parameters[index].is_pack) ||
		(index >= record_decl->parameters.size() &&
		 !record_decl->parameters.empty() &&
		 record_decl->parameters.back().is_pack);
	bool uses_active_pack = false;
	bool active_pack_parameter = false;
	bool matches_record_parameter = false;
	if (original.kind == TemplateArgumentKind::Type &&
	    original.type.get() != NULL) {
		string pack_name;
		if (template_type_has_template_parameter_name(original.type,
		                                              pack_name) &&
		    p.active_type_parameter_pack(pack_name))
			uses_active_pack = true;
		TypePtr bare_original = pa11::strip_cv(original.type);
		active_pack_parameter =
			bare_original.get() != NULL &&
			bare_original->kind == pa11::TypeKind::TemplateParameter &&
			p.active_type_parameter_pack(bare_original->name);
		matches_record_parameter =
			bare_original.get() != NULL &&
			bare_original->kind == pa11::TypeKind::TemplateParameter &&
			index < record_decl->parameters.size() &&
			record_decl->parameters[index].name == bare_original->name;
	} else if (original.kind == TemplateArgumentKind::Pack)
		uses_active_pack = true;
	bool primary_pack =
		primary_pack_slot &&
		(original.pack_expansion ||
		 original.kind == TemplateArgumentKind::Pack ||
		 uses_active_pack);
	bool active_pack =
		!function_type && active_pack_parameter &&
		(matches_record_parameter ||
		 (record_decl->owner != NULL &&
		  record_decl->owner->kind == ScopeKind::Class &&
		  source_args.size() > 1 &&
		  index + 1 == source_args.size()));
	if ((primary_pack || active_pack) && arg.kind != TemplateArgumentKind::Pack)
		arg.pack_expansion = true;
	vector<TemplateArgument> expanded;
	if (!function_type && primary_pack &&
	    arg.kind == TemplateArgumentKind::Pack && arg.pack.size() == 1 &&
	    arg.pack[0].kind != TemplateArgumentKind::Pack) {
		TemplateArgument pattern = arg.pack[0];
		pattern.pack_expansion = true;
		expanded = p.expand_template_argument_pack(pattern);
	} else if (!function_type &&
	           (original.pack_expansion || primary_pack || active_pack ||
	            original.kind == TemplateArgumentKind::Pack ||
	            arg.pack_expansion || arg.kind == TemplateArgumentKind::Pack))
		expanded = p.expand_template_argument_pack(arg);
	else
		expanded.push_back(arg);
	vector<TemplateArgument> result;
	for (size_t j = 0; j < expanded.size(); ++j) {
		TemplateArgument element = expanded[j];
		if (element.kind == TemplateArgumentKind::Pack)
			result.insert(result.end(), element.pack.begin(), element.pack.end());
		else
			result.push_back(element);
	}
	size_t skip_defaults =
		(original.pack_expansion || primary_pack ||
		 original.kind == TemplateArgumentKind::Pack) &&
		produced_pack_size > 1 ? produced_pack_size - 1 : 0;
	while (skip_defaults != 0 && index + 1 < source_args.size() &&
	       !template_argument_has_template_parameter(
		       source_args[index + 1],
		       p.record_template_arguments_)) {
		++index;
		--skip_defaults;
	}
	return result;
}

vector<TemplateArgument> TypeSubstitutionEngine::substitute_record_arguments(
	TemplateDeclaration* record_decl,
	const vector<TemplateArgument>& source_args) const
{
	vector<TemplateArgument> substituted;
	for (size_t i = 0; i < source_args.size(); ++i) {
		vector<TemplateArgument> expanded =
			expand_substituted_record_argument(record_decl, source_args, i);
		substituted.insert(substituted.end(),
		                   expanded.begin(),
		                   expanded.end());
	}
	return flatten_template_argument_packs(substituted);
}

TypeSubstitutionResult
TypeSubstitutionEngine::instantiate_substituted_record(
	const TypePtr& type,
	TemplateDeclaration* record_decl,
	const vector<TemplateArgument>& source_args) const
{
	vector<TemplateArgument> substituted =
		substitute_record_arguments(record_decl, source_args);
	if (p.template_argument_key(substituted) ==
	    p.template_argument_key(source_args))
		return TypeSubstitutionResult::none();
	if (argument_count_too_large(record_decl, substituted) ||
	    argument_count_too_small(record_decl, substituted))
		return TypeSubstitutionResult::done(type);
	return TypeSubstitutionResult::done(
		const_cast<Parser*>(&p)->instantiate_class_template(record_decl,
		                                                    substituted));
}

TypePtr TypeSubstitutionEngine::substitute(const TypePtr& type) const
{
	if (type.get() == NULL)
		return type;
	if (active_dependent_substitution(type))
		return type;
	if (preserves_self_reference(type))
		return type;
	if (type->is_dependent_typename)
		return substitute_dependent_typename(type);
	TypeSubstitutionResult simple = substitute_simple(type);
	if (simple.handled)
		return simple.type;
	if (type->kind == pa11::TypeKind::Array) {
		bool unknown_bound = type->unknown_bound;
		uint64_t bound = type->bound;
		string bound_name = type->name;
		if (unknown_bound && !bound_name.empty()) {
			TemplateArgument subst;
			if (p.find_template_value_substitution(bound_name, subst) &&
			    subst.kind == TemplateArgumentKind::Value &&
			    !subst.dependent) {
				unknown_bound = false;
				bound = subst.value;
				bound_name.clear();
			}
		}
		TypePtr out = pa11::make_array(p.substitute_template_type(type->base),
		                               unknown_bound,
		                               bound);
		out->name = bound_name;
		out->tag = type->tag;
		return out;
	}
	if (type->kind == pa11::TypeKind::Function) {
		vector<TypePtr> params;
		bool consumed_variadic_pack = false;
		for (size_t i = 0; i < type->parameters.size(); ++i) {
			string pack_name;
			TemplateArgument subst;
			bool variadic_pack_tail = false;
			if (type->variadic && i + 1 == type->parameters.size())
				variadic_pack_tail =
					template_type_has_template_parameter_name(
						type->parameters[i],
						pack_name);
			if ((p.function_parameter_type_pack_expansion_name(
				     type->parameters[i],
				     pack_name) ||
			     variadic_pack_tail) &&
			    p.find_template_value_substitution(pack_name, subst) &&
			    subst.kind == TemplateArgumentKind::Pack) {
					for (size_t pi = 0; pi < subst.pack.size(); ++pi)
						if (subst.pack[pi].kind == TemplateArgumentKind::Type)
							params.push_back(p.substitute_template_type(
								p.substitute_template_type_parameter(
									type->parameters[i],
									pack_name,
									subst.pack[pi].type)));
						else
							throw runtime_error(
								"type parameter pack required");
					if (variadic_pack_tail)
						consumed_variadic_pack = true;
					continue;
			}
			params.push_back(p.substitute_template_type(type->parameters[i]));
		}
		TypePtr out = pa11::make_function(p.substitute_template_type(type->base),
		                                  params,
		                                  type->variadic &&
		                                  !consumed_variadic_pack);
		out->cv = type->cv;
		out->ref_qualifier = type->ref_qualifier;
		return out;
	}
	TypeSubstitutionResult record = substitute_record(type);
	if (record.handled)
		return record.type;
	TypeSubstitutionResult member = substitute_member_record_owner(type);
	if (member.handled)
		return member.type;
	return type;
}

TypePtr substitute_template_type_with_engine(const Parser& parser, TypePtr type)
{
	TypeSubstitutionEngine engine(parser);
	return engine.substitute(type);
}

}  // namespace internal
}  // namespace pa12
