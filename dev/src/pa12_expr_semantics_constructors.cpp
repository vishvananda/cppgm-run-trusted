#include "pa12_expr_semantics_support.h"
#include "pa12_templates_instance_support.h"
#include "pa12_types_support.h"

#include <algorithm>
#include <stdexcept>

using namespace std;

namespace pa12 {
namespace internal {

bool hosted_library_namespace_scope(Scope* scope);

static bool constructor_this_matches_record(TypePtr record, Binding* ctor)
{
	if (record.get() == NULL ||
	    ctor == NULL ||
	    ctor->type.get() == NULL ||
	    ctor->type->kind != pa11::TypeKind::Function ||
	    ctor->type->parameters.empty())
		return false;
	TypePtr this_type = pa11::strip_cv(ctor->type->parameters[0]);
	if (this_type.get() == NULL ||
	    this_type->kind != pa11::TypeKind::Pointer)
		return false;
	TypePtr this_record = pa11::strip_cv(this_type->base);
	record = pa11::strip_cv(record);
	return this_record.get() != NULL &&
	       record.get() != NULL &&
	       this_record->kind == pa11::TypeKind::Record &&
	       record->kind == pa11::TypeKind::Record &&
	       (pa11::same_type(this_record, record) ||
	        same_template_specialization_record(this_record, record));
}

bool constructor_binding_for_record(TypePtr record, Binding* ctor)
{
	record = record.get() != NULL ? pa11::strip_cv(record) : TypePtr();
	return record.get() != NULL &&
	       record->kind == pa11::TypeKind::Record &&
	       record->scope != NULL &&
	       ctor != NULL &&
	       constructor_this_matches_record(record, ctor) &&
	       (ctor->aliased_binding == NULL ||
	        constructor_this_matches_record(record,
		                                        ctor->aliased_binding));
}

vector<Expr> default_arguments_for_binding(Binding* binding,
                                           const vector<Expr>& defaults)
{
	if (binding == NULL ||
	    binding->type.get() == NULL ||
	    binding->type->kind != pa11::TypeKind::Function ||
	    binding->type->parameters.empty() ||
	    defaults.size() + 1 != binding->type->parameters.size())
		return defaults;
	TypePtr first = pa11::strip_cv(binding->type->parameters[0]);
	if (first.get() == NULL || first->kind != pa11::TypeKind::Pointer)
		return defaults;
	TypePtr object = pa11::strip_cv(first->base);
	if (object.get() == NULL || object->kind != pa11::TypeKind::Record)
		return defaults;
	vector<Expr> shifted(binding->type->parameters.size());
	for (size_t i = 0; i < defaults.size(); ++i)
		shifted[i + 1] = defaults[i];
	return shifted;
}

vector<Binding*> Parser::constructor_members_for_record(TypePtr record) const
{
	vector<Binding*> out;
	TypePtr bare = record.get() != NULL ? pa11::strip_cv(record) : TypePtr();
	if (bare.get() == NULL ||
	    bare->kind != pa11::TypeKind::Record ||
	    bare->scope == NULL)
		return out;
	for (map<string, vector<Binding*> >::const_iterator it =
		     bare->scope->members.begin();
	     it != bare->scope->members.end();
	     ++it)
	{
		if (!constructor_name_matches_scope(bare->scope, it->first))
			continue;
		out.insert(out.end(), it->second.begin(), it->second.end());
	}
	return out;
}

string hosted_unqualified_primary(TypePtr type)
{
	string primary = type.get() != NULL
		? (type->template_primary_name.empty()
		   ? type->name : type->template_primary_name)
		: string();
	size_t sep = primary.rfind("::");
	if (sep != string::npos)
		primary = primary.substr(sep + 2);
	size_t arg_pos = primary.find('<');
	if (arg_pos != string::npos)
		primary = primary.substr(0, arg_pos);
	return primary;
}

static bool hosted_pair_record(TypePtr record)
{
	TypePtr bare = record.get() != NULL ? pa11::strip_cv(record) : TypePtr();
	return bare.get() != NULL &&
	       bare->kind == pa11::TypeKind::Record &&
	       bare->scope != NULL &&
	       hosted_library_namespace_scope(bare->scope) &&
	       hosted_unqualified_primary(bare) == "pair";
}

static Binding* hosted_pair_field(TypePtr record,
                                  const string& name,
                                  size_t fallback)
{
	TypePtr bare = record.get() != NULL ? pa11::strip_cv(record) : TypePtr();
	if (bare.get() == NULL || bare->kind != pa11::TypeKind::Record)
		return NULL;
	pa11::layout_record_type(bare);
	for (size_t i = 0; i < bare->fields.size(); ++i)
		if (bare->fields[i] != NULL && bare->fields[i]->name == name)
			return bare->fields[i];
	return fallback < bare->fields.size() ? bare->fields[fallback] : NULL;
}

bool no_matching_constructor_error(const runtime_error& err);
bool exact_copy_reference_constructor_for_order_args(
	Binding* ctor,
	const vector<Expr>& template_order_args);
bool ranks_equal_allowing_copy_reference_rank(
	const vector<int>& copy_ranks,
	const vector<int>& other_ranks);

bool inherited_constructor_template_candidate(
	const map<Binding*, TemplateDeclaration*>& placeholders,
	Binding* binding)
{
	TemplateDeclaration* origin =
		function_template_origin(placeholders, binding);
	return origin != NULL &&
	       origin->constructor_template &&
	       origin->inherited_constructor_base != NULL;
}

static bool cached_binding_type_structurally_dependent(Binding* binding)
{
	if (binding == NULL || binding->type.get() == NULL)
		return false;
	typedef pair<const Binding*, const void*> Key;
	static map<Key, bool> cache;
	Key key(binding, binding->type.get());
	map<Key, bool>::const_iterator found = cache.find(key);
	if (found != cache.end())
		return found->second;
	bool dependent = type_structurally_dependent(binding->type);
	cache[key] = dependent;
	return dependent;
}

bool record_has_conversion_function_candidate(TypePtr record,
                                              set<Scope*>& seen)
{
	TypePtr bare = record.get() != NULL ? pa11::strip_cv(record) : TypePtr();
	if (bare.get() == NULL ||
	    bare->kind != pa11::TypeKind::Record ||
	    bare->scope == NULL ||
	    !seen.insert(bare->scope).second)
		return false;
	for (map<string, vector<Binding*> >::const_iterator it =
		     bare->scope->members.begin();
	     it != bare->scope->members.end();
	     ++it)
		if (it->first.compare(0, 9, "operator ") == 0)
			for (size_t i = 0; i < it->second.size(); ++i)
				if (it->second[i]->kind == BindingKind::Function)
					return true;
	vector<TypePtr> bases = pa11::record_direct_bases(bare);
	for (size_t i = 0; i < bases.size(); ++i)
		if (record_has_conversion_function_candidate(bases[i], seen))
			return true;
	return false;
}

Binding* Parser::ensure_hosted_pair_constructor(TypePtr record,
                                                const vector<Expr>& args)
{
	record = record.get() != NULL ? pa11::strip_cv(record) : TypePtr();
	if (!hosted_compatibility_ ||
	    !hosted_pair_record(record) ||
	    args.size() != 2)
		return NULL;
	Binding* first = NULL;
	Binding* second = NULL;
	try
	{
		first = hosted_pair_field(record, "first", 0);
		second = hosted_pair_field(record, "second", 1);
	}
	catch (const runtime_error&)
	{
		return NULL;
	}
	if (first == NULL || second == NULL)
		return NULL;
	vector<TypePtr> params;
	params.push_back(pa11::make_pointer(record));
	params.push_back(first->type);
	params.push_back(second->type);
	TypePtr fn_type = pa11::make_function(pa11::make_fundamental(FT_VOID),
	                                      params,
	                                      false);
	map<string, vector<Binding*> >::iterator existing =
		record->scope->members.find(record->scope->name);
	if (existing != record->scope->members.end())
		for (size_t i = 0; i < existing->second.size(); ++i)
			if (existing->second[i]->kind == BindingKind::Function &&
			    existing->second[i]->type.get() != NULL &&
			    pa11::same_type(existing->second[i]->type, fn_type))
				return existing->second[i];
	Binding* ctor = add_value(record->scope,
	                         BindingKind::Function,
	                         record->scope->name,
	                         fn_type);
	ctor->is_inline_definition = true;
	ctor->is_defaulted = true;
	function_parameter_names_[ctor] = vector<string>(3, "this");
	function_parameter_names_[ctor][1] = "__first";
	function_parameter_names_[ctor][2] = "__second";
	ctor->function_parameter_names = function_parameter_names_[ctor];
	return ctor;
}

void Parser::prepare_constructor_template_candidates(TypePtr record,
                                                     const vector<Expr>& args)
{
	complete_template_record(record);
	bool hosted_record =
		hosted_compatibility_ &&
		hosted_library_namespace_scope(record->scope);
	if (record->is_template_specialization && !hosted_record)
		instantiate_member_function_templates(record);
	if (record->scope != NULL &&
	    record->scope->parent != NULL &&
	    record->scope->parent->kind == ScopeKind::Class)
	{
		TypePtr owner_record = pa11::record_type_for_scope(record->scope->parent);
		owner_record = owner_record.get() != NULL
			? pa11::strip_cv(owner_record) : TypePtr();
		if (owner_record.get() != NULL &&
		    owner_record->kind == pa11::TypeKind::Record &&
		    owner_record->is_template_specialization &&
		    !(hosted_compatibility_ &&
		      hosted_library_namespace_scope(owner_record->scope)))
			instantiate_member_function_templates(owner_record);
	}
	if (record->scope == NULL)
		return;
	if (hosted_record)
	{
		static set<vector<size_t> > hosted_prepared;
		vector<size_t> key;
		key.push_back(reinterpret_cast<uintptr_t>(this));
		key.push_back(reinterpret_cast<uintptr_t>(record.get()));
		key.push_back(member_function_template_generation_);
		key.push_back(args.size());
		for (size_t i = 0; i < args.size(); ++i)
		{
			key.push_back(reinterpret_cast<uintptr_t>(args[i].type.get()));
			key.push_back(static_cast<size_t>(args[i].category));
			key.push_back(reinterpret_cast<uintptr_t>(args[i].binding));
			key.push_back(reinterpret_cast<uintptr_t>(args[i].node.direct_call));
			key.push_back(args[i].pack.size());
		}
		if (!hosted_prepared.insert(key).second)
			return;
	}
	vector<TypePtr> owners;
	set<const void*> seen_owners;
	for (map<pair<TemplateDeclaration*, string>,
	     vector<TemplateDeclaration*> >::iterator it =
		     member_function_templates_.begin();
	     it != member_function_templates_.end();
	     ++it)
	{
		if (it->first.second != record->scope->name)
			continue;
		bool constructor_template = false;
		for (size_t i = 0; i < it->second.size(); ++i)
			if (it->second[i]->constructor_template)
				constructor_template = true;
		if (!constructor_template || it->first.first == NULL)
			continue;
		for (map<string, TypePtr>::const_iterator spec =
			     it->first.first->class_specializations.begin();
		     spec != it->first.first->class_specializations.end();
		     ++spec)
		{
			TypePtr owner = pa11::strip_cv(spec->second);
			if (owner.get() == NULL ||
			    owner->kind != pa11::TypeKind::Record ||
			    owner->scope == NULL)
				continue;
			if (owner.get() != record.get())
			{
				string owner_primary = owner->template_primary_name.empty()
					? owner->name : owner->template_primary_name;
				string record_primary =
					record->template_primary_name.empty()
					? record->name : record->template_primary_name;
				if (owner->scope != record->scope &&
				    owner->name != record->name &&
				    owner_primary != record_primary)
					continue;
				if (!pa11::same_type(owner, record))
					continue;
			}
			if (seen_owners.insert(owner.get()).second)
				owners.push_back(owner);
		}
	}
	for (size_t i = 0; i < owners.size(); ++i)
		if (!(hosted_compatibility_ &&
		      hosted_library_namespace_scope(owners[i]->scope)))
			instantiate_member_function_templates(owners[i]);

	Expr this_arg;
	this_arg.valid = true;
	this_arg.type = pa11::make_pointer(record);
	this_arg.category = ValueCategory::PRValue;
	this_arg.node = Node("id-expression prvalue " +
	                     pa11::describe_type(this_arg.type) + " this");
	annotate_expr_node(this_arg);
	vector<Expr> deduction_args;
	deduction_args.push_back(this_arg);
	deduction_args.insert(deduction_args.end(), args.begin(), args.end());
	map<Binding*, vector<TemplateArgument> > explicit_args;
	for (map<pair<TemplateDeclaration*, string>,
	     vector<TemplateDeclaration*> >::iterator it =
		     member_function_templates_.begin();
	     it != member_function_templates_.end();
	     ++it)
	{
		if (it->first.second != record->scope->name)
			continue;
		for (size_t i = 0; i < it->second.size(); ++i)
		{
			TemplateDeclaration* declaration = it->second[i];
			if (!declaration->constructor_template ||
			    declaration->placeholder == NULL)
				continue;
			Binding* active = active_functions_.empty()
				? NULL : active_functions_.back();
			TemplateDeclaration* active_declaration =
				function_template_origin(function_template_placeholders_,
				                         active);
			if (active_declaration == NULL &&
			    active != NULL &&
			    replay_function_template_declaration_ != NULL &&
			    active->owner == replay_function_template_declaration_->owner &&
			    active->name == replay_function_template_declaration_->name)
				active_declaration = replay_function_template_declaration_;
			if (same_function_template_declaration_family(active_declaration,
			                                              declaration))
				continue;
			map<Binding*, TemplateDeclaration*>::iterator saved =
				function_template_placeholders_.find(declaration->placeholder);
			TemplateDeclaration* saved_declaration =
				saved != function_template_placeholders_.end()
				? saved->second : NULL;
			function_template_placeholders_[declaration->placeholder] =
				declaration;
			instantiate_template_call_candidate(declaration->placeholder,
			                                    explicit_args,
			                                    deduction_args);
			if (saved_declaration != NULL)
				function_template_placeholders_[declaration->placeholder] =
					saved_declaration;
			else
				function_template_placeholders_.erase(declaration->placeholder);
		}
	}
}

Binding* Parser::instantiate_constructor_template_candidate(
	TypePtr record,
	Binding* ctor,
	const vector<Expr>& args)
{
	map<Binding*, TemplateDeclaration*>::iterator template_it =
		function_template_placeholders_.find(ctor);
	if (template_it == function_template_placeholders_.end() &&
	    ctor != NULL &&
	    ctor->type.get() != NULL &&
	    cached_binding_type_structurally_dependent(ctor))
	{
		for (map<Binding*, TemplateDeclaration*>::iterator it =
			     function_template_placeholders_.begin();
		     it != function_template_placeholders_.end();
		     ++it)
		{
			Binding* placeholder = it->first;
			TemplateDeclaration* declaration = it->second;
			if (placeholder == NULL ||
			    declaration == NULL ||
			    !declaration->constructor_template ||
			    placeholder->owner != ctor->owner ||
			    placeholder->name != ctor->name ||
			    placeholder->type.get() == NULL ||
			    !same_template_signature_type(placeholder->type,
			                                  ctor->type))
				continue;
			ctor = placeholder;
			template_it = it;
			break;
		}
	}
	if (template_it == function_template_placeholders_.end())
		return ctor;
	TemplateDeclaration* declaration = template_it->second;
	Binding* active = active_functions_.empty() ? NULL : active_functions_.back();
	TemplateDeclaration* active_declaration =
		function_template_origin(function_template_placeholders_, active);
	if (active_declaration == NULL &&
	    active != NULL &&
	    replay_function_template_declaration_ != NULL &&
	    active->owner == replay_function_template_declaration_->owner &&
	    active->name == replay_function_template_declaration_->name)
		active_declaration = replay_function_template_declaration_;
	if (same_function_template_declaration_family(active_declaration,
	                                              declaration))
		return NULL;
	TypePtr bare_record = record.get() != NULL ? pa11::strip_cv(record) : TypePtr();
	map<const void*, TemplateDeclaration*>::iterator owner_template =
		bare_record.get() != NULL
		? record_template_declarations_.find(bare_record.get())
		: record_template_declarations_.end();
	if (declaration != NULL &&
	    declaration->constructor_template &&
	    declaration->class_template_member &&
	    owner_template != record_template_declarations_.end() &&
	    expr_template_parameter_lists_match(declaration->parameters,
	                                        owner_template->second->parameters))
		return ctor;
	Expr this_arg;
	this_arg.valid = true;
	this_arg.type = pa11::make_pointer(record);
	this_arg.category = ValueCategory::PRValue;
	this_arg.node = Node("id-expression prvalue " +
	                     pa11::describe_type(this_arg.type) + " this");
	annotate_expr_node(this_arg);
	vector<Expr> deduction_args;
	deduction_args.push_back(this_arg);
	deduction_args.insert(deduction_args.end(), args.begin(), args.end());
	map<Binding*, vector<TemplateArgument> > explicit_args;
	ctor = instantiate_template_call_candidate(ctor, explicit_args, deduction_args);
	if (ctor == NULL)
		return NULL;
	if (declaration != NULL &&
	    declaration->constructor_template &&
	    declaration->inherited_constructor_base == NULL &&
	    !constructor_this_matches_record(record, ctor))
		return NULL;
	if (default_arguments_.find(ctor) == default_arguments_.end())
	{
		map<Binding*, TemplateDeclaration*>::iterator instantiated_template =
			function_template_placeholders_.find(ctor);
		if (instantiated_template != function_template_placeholders_.end() &&
		    instantiated_template->second->placeholder != NULL)
		{
				map<Binding*, vector<Expr> >::const_iterator defaults =
					default_arguments_.find(
						instantiated_template->second->placeholder);
				if (defaults != default_arguments_.end())
					default_arguments_[ctor] =
						default_arguments_for_binding(ctor, defaults->second);
			}
		}
		return ctor;
	}

}  // namespace internal
}  // namespace pa12
