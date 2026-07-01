#include "pa12_internal.h"
#include "pa12_templates_function_support.h"
#include "pa12_templates_instance_support.h"

#include <stdexcept>

using namespace std;

namespace pa12 {
namespace internal {

const size_t kCompletedTemplateArgumentCacheLimit = 65536;

size_t dependent_cache_string_hash(const string& value);
size_t dependent_cache_type_identity(TypePtr type);
size_t dependent_cache_template_argument_identity(
	const TemplateArgument& argument,
	int depth);
pa11::TemplateInstanceArgument completed_instance_argument(
	const TemplateArgument& argument);
bool template_argument_kind_matches_parameter(
	const TemplateArgument& argument,
	const TemplateParameterInfo& parameter);
bool unsigned_integral_template_parameter(TypePtr type);
TemplateArgument convert_non_type_template_argument(
	TemplateArgument argument,
	TypePtr parameter_type);
bool dependent_typename_condition_false(TypePtr type);
bool hosted_library_namespace_scope(Scope* scope);
namespace {


	bool dependent_typename_is_enable_if(TypePtr type)
	{
		if (type.get() == NULL)
			return false;
		string root_name = type->name;
		size_t type_suffix = root_name.find("::type");
		if (type_suffix != string::npos)
			root_name = root_name.substr(0, type_suffix);
		size_t template_suffix = root_name.find('<');
		if (template_suffix != string::npos)
			root_name = root_name.substr(0, template_suffix);
		size_t qualifier = root_name.rfind("::");
		if (qualifier != string::npos)
			root_name = root_name.substr(qualifier + 2);
		return root_name == "enable_if" ||
		       root_name == "enable_if_t" ||
		       root_name == "__enable_if_t";
	}

	bool dependent_typename_disabled_enable_if_argument(
		TypePtr type,
		const vector<TemplateArgument>& arguments)
	{
		return dependent_typename_is_enable_if(type) &&
		       !arguments.empty() &&
		       arguments[0].kind == TemplateArgumentKind::Value &&
		       !arguments[0].dependent &&
		       arguments[0].value == 0;
	}

	string unqualified_template_owner(string name)
	{
		size_t args = name.find('<');
		if (args != string::npos)
			name = name.substr(0, args);
		size_t scope = name.rfind("::");
		if (scope != string::npos)
			name = name.substr(scope + 2);
		return name;
	}

	bool cheap_hosted_enable_if_condition(const TemplateArgument& arg)
	{
		if (arg.value_member_name != "value" &&
		    arg.value_member_name != "__value")
			return false;
		string owner = unqualified_template_owner(
			arg.value_owner_template_name);
		return owner == "__and_" ||
		       owner == "__or_" ||
		       owner == "__not_" ||
		       owner == "is_same" ||
		       owner == "__are_same" ||
		       owner == "__same_value_type" ||
		       owner == "is_pointer" ||
		       owner == "__is_pointer" ||
		       owner == "is_reference" ||
		       owner == "__is_reference" ||
		       owner == "is_lvalue_reference" ||
		       owner == "is_rvalue_reference" ||
		       owner == "is_constructible" ||
		       owner == "__is_constructible" ||
		       owner == "is_nothrow_constructible" ||
		       owner == "__is_nothrow_constructible" ||
		       owner == "is_trivially_constructible" ||
		       owner == "__is_trivially_constructible" ||
		       owner == "is_copy_constructible" ||
		       owner == "is_nothrow_copy_constructible" ||
		       owner == "is_trivially_copy_constructible" ||
		       owner == "is_move_constructible" ||
		       owner == "is_nothrow_move_constructible" ||
		       owner == "is_trivially_move_constructible" ||
		       owner == "is_assignable" ||
		       owner == "__is_assignable" ||
		       owner == "is_nothrow_assignable" ||
		       owner == "__is_nothrow_assignable" ||
		       owner == "is_trivially_assignable" ||
		       owner == "__is_trivially_assignable" ||
		       owner == "is_copy_assignable" ||
		       owner == "is_nothrow_copy_assignable" ||
		       owner == "is_trivially_copy_assignable" ||
		       owner == "is_move_assignable" ||
		       owner == "is_nothrow_move_assignable" ||
		       owner == "is_trivially_move_assignable" ||
		       owner == "is_convertible" ||
		       owner == "__is_convertible";
	}

	bool hosted_trait_record(TypePtr type)
	{
		TypePtr bare = type.get() != NULL ? pa11::strip_cv(type) : TypePtr();
		return bare.get() != NULL &&
		       bare->kind == pa11::TypeKind::Record &&
		       bare->scope != NULL &&
		       hosted_library_namespace_scope(bare->scope);
	}

	Binding* hosted_trait_declared_copy_move_constructor(TypePtr record,
	                                                     bool move)
	{
		TypePtr bare = record.get() != NULL ? pa11::strip_cv(record) : TypePtr();
		if (bare.get() == NULL ||
		    bare->kind != pa11::TypeKind::Record ||
		    bare->scope == NULL)
			return NULL;
		map<string, vector<Binding*> >::const_iterator found =
			bare->scope->members.find(bare->scope->name);
		if (found == bare->scope->members.end())
			return NULL;
		for (size_t i = 0; i < found->second.size(); ++i)
		{
			Binding* binding = found->second[i];
			if (binding == NULL ||
			    binding->kind != BindingKind::Function ||
			    binding->type.get() == NULL ||
			    binding->type->kind != pa11::TypeKind::Function ||
			    binding->type->parameters.size() < 2 ||
			    !pa11::is_reference_type(binding->type->parameters[1]))
				continue;
			TypePtr param = binding->type->parameters[1];
			if (move != (param->kind == pa11::TypeKind::RValueReference))
				continue;
			if (pa11::same_type(pa11::strip_cv(param->base), bare))
				return binding;
		}
		return NULL;
	}

	bool evaluate_hosted_constructible_trait(TypePtr target,
	                                         const vector<TypePtr>& types,
	                                         const set<Binding*>& deleted,
	                                         bool& value)
	{
		TypePtr bare = target.get() != NULL ? pa11::strip_cv(target) : TypePtr();
		if (!hosted_trait_record(bare))
			return false;
		if (types.size() == 2)
		{
			TypePtr arg = pa11::strip_cv(types[1]);
			if (pa11::is_reference_type(arg) &&
			    pa11::same_type(pa11::strip_cv(arg->base), bare))
			{
				bool move = arg->kind == pa11::TypeKind::RValueReference;
				Binding* ctor =
					hosted_trait_declared_copy_move_constructor(bare, move);
				if (ctor == NULL && move)
					ctor =
						hosted_trait_declared_copy_move_constructor(bare, false);
				if (ctor == NULL && !move &&
				    unqualified_template_owner(
					    bare->template_primary_name.empty()
					    ? bare->name : bare->template_primary_name) ==
					    "unique_ptr")
				{
					value = false;
					return true;
				}
				value = ctor == NULL || deleted.find(ctor) == deleted.end();
				return true;
			}
		}
		value = true;
		return true;
	}

			}  // namespace

struct TemplateArgumentCompleter
{
	Parser& parser;
	TemplateDeclaration* declaration;
	const vector<TemplateArgument>& explicit_arguments;
	vector<TemplateArgument> explicit_expanded;
	vector<TemplateArgument> out;
	size_t explicit_index;

	TemplateArgumentCompleter(Parser& p,
	                          TemplateDeclaration* d,
	                          const vector<TemplateArgument>& args)
		: parser(p),
		  declaration(d),
		  explicit_arguments(args),
		  explicit_index(0)
	{
	}

	struct SubstitutionScope
	{
		Parser& parser;
		size_t type_size;
		size_t value_size;
		size_t pack_size;

		SubstitutionScope(Parser& p,
		                  TemplateDeclaration* declaration,
		                  const map<string, TypePtr>& subst,
		                  const map<string, TemplateArgument>& value_subst,
		                  const set<string>& pack_subst)
			: parser(p),
			  type_size(p.template_type_substitutions_.size()),
			  value_size(p.template_value_substitutions_.size()),
			  pack_size(p.template_type_parameter_packs_.size())
		{
			parser.template_type_substitutions_.insert(
				parser.template_type_substitutions_.end(),
				declaration->outer_type_substitutions.begin(),
				declaration->outer_type_substitutions.end());
			parser.template_value_substitutions_.insert(
				parser.template_value_substitutions_.end(),
				declaration->outer_value_substitutions.begin(),
				declaration->outer_value_substitutions.end());
			parser.template_type_substitutions_.push_back(subst);
			parser.template_value_substitutions_.push_back(value_subst);
			parser.template_type_parameter_packs_.push_back(pack_subst);
		}

		~SubstitutionScope()
		{
			parser.template_type_substitutions_.resize(type_size);
			parser.template_value_substitutions_.resize(value_size);
			parser.template_type_parameter_packs_.resize(pack_size);
		}
	};

	vector<TemplateArgument> run()
	{
		expand_explicit_arguments();
		for (size_t i = 0; i < declaration->parameters.size(); ++i)
			append_parameter(i);
		if (explicit_index != explicit_expanded.size())
			throw runtime_error("too many template arguments");
		finalize_non_type_arguments();
		return out;
	}

	void expand_explicit_arguments()
	{
		for (size_t i = 0; i < explicit_arguments.size(); ++i)
		{
			vector<TemplateArgument> expansion;
			bool keep_explicit_pack =
				explicit_arguments.size() == declaration->parameters.size() &&
				i < declaration->parameters.size() &&
				declaration->parameters[i].is_pack &&
				explicit_arguments[i].kind == TemplateArgumentKind::Pack;
			bool keep_single_non_type_argument =
				explicit_arguments.size() == declaration->parameters.size() &&
				i < declaration->parameters.size() &&
				!declaration->parameters[i].is_pack &&
				declaration->parameters[i].kind ==
					TemplateParameterKind::NonType &&
				explicit_arguments[i].kind == TemplateArgumentKind::Value;
			bool keep_single_type_pattern =
				i < declaration->parameters.size() &&
				!declaration->parameters[i].is_pack &&
				explicit_arguments[i].kind == TemplateArgumentKind::Type;
			if (keep_single_type_pattern)
				keep_single_type_pattern =
					kept_single_type_pattern(explicit_arguments[i]);
			if (keep_explicit_pack ||
			    keep_single_non_type_argument ||
			    keep_single_type_pattern)
				expansion.push_back(explicit_arguments[i]);
			else
				expansion =
					parser.expand_template_argument_pack(explicit_arguments[i]);
			explicit_expanded.insert(explicit_expanded.end(),
			                         expansion.begin(),
			                         expansion.end());
		}
	}

	bool kept_single_type_pattern(const TemplateArgument& argument) const
	{
		TypePtr bare_arg = argument.type.get() != NULL
			? pa11::strip_cv(argument.type) : TypePtr();
		return bare_arg.get() != NULL &&
		       (bare_arg->kind == pa11::TypeKind::Function ||
		        bare_arg->kind == pa11::TypeKind::MemberPointer);
	}

	void append_parameter(size_t parameter_index)
	{
		const TemplateParameterInfo& parameter =
			declaration->parameters[parameter_index];
		TypePtr parameter_type = substituted_parameter_type(parameter);
		if (parameter.is_pack)
		{
			parser.append_completed_template_pack_argument(
				declaration,
				parameter_index,
				parameter_type,
				explicit_expanded,
				explicit_index,
				out);
			return;
		}
		if (explicit_index < explicit_expanded.size())
		{
			append_explicit_argument(parameter, parameter_type);
			return;
		}
		append_default_argument(parameter_index, parameter, parameter_type);
	}

	TypePtr substituted_parameter_type(const TemplateParameterInfo& parameter)
	{
		TypePtr parameter_type = parameter.type;
		if (parameter.kind != TemplateParameterKind::NonType ||
		    parameter_type.get() == NULL)
			return parameter_type;
		map<string, TypePtr> subst;
		map<string, TemplateArgument> value_subst;
		set<string> pack_subst;
		collect_current_substitutions(subst, value_subst, pack_subst, NULL);
		try
		{
			SubstitutionScope scope(parser,
			                        declaration,
			                        subst,
			                        value_subst,
			                        pack_subst);
			return substitute_parameter_type_in_declaration_scope(
				parameter_type);
		}
		catch (const runtime_error& err)
		{
			if (!can_leave_parameter_type_dependent(parameter_type, err))
				throw;
			return parameter_type;
		}
		}

	TypePtr substitute_parameter_type_in_declaration_scope(TypePtr type)
	{
		Scope* scope = declaration != NULL ? declaration->owner : NULL;
		if (scope == NULL &&
		    declaration != NULL &&
		    declaration->placeholder != NULL)
			scope = declaration->placeholder->owner;
		if (scope == NULL && declaration != NULL)
			scope = declaration->lexical_scope;
		if (scope == NULL)
			return parser.substitute_template_type(type);
		vector<Scope*> saved_scopes = parser.scopes_;
		parser.scopes_.clear();
		parser.scopes_.push_back(scope);
		try
		{
			TypePtr out = parser.substitute_template_type(type);
			parser.scopes_ = saved_scopes;
			return out;
		}
		catch (...)
		{
			parser.scopes_ = saved_scopes;
			throw;
		}
	}

		bool trait_instance_arguments(
			TypePtr type,
			const vector<pa11::TemplateInstanceArgument>*& args)
		{
			TypePtr record = type.get() != NULL ? pa11::strip_cv(type) : TypePtr();
			if (record.get() == NULL || record->kind != pa11::TypeKind::Record)
				return false;
			args = &record->template_arguments;
			if (args->empty() &&
			    !record->dependent_typename_template_argument_lists.empty())
				args = &record->dependent_typename_template_argument_lists[0];
			return true;
		}

		bool raw_trait_type_argument(
			const pa11::TemplateInstanceArgument& instance,
			TypePtr& out_type)
		{
			TemplateArgument arg =
				raw_template_argument_from_instance_argument(instance);
			if (arg.kind != TemplateArgumentKind::Type)
				return false;
			out_type = arg.type;
			return true;
		}

		bool resolve_trait_subject_type(TypePtr raw_type,
		                                TypePtr& out_type)
		{
			TypePtr bare = raw_type.get() != NULL
				? pa11::strip_cv(raw_type) : TypePtr();
			if (bare.get() == NULL)
				return false;
			if (bare->kind == pa11::TypeKind::TemplateParameter &&
			    !bare->is_dependent_typename)
			{
				TypePtr subst;
				if (!parser.find_template_type_substitution(bare->name,
				                                            subst))
					return false;
				out_type = subst;
				return true;
			}
			if (bare->is_dependent_typename ||
			    template_type_has_template_parameter(
				    raw_type,
				    parser.record_template_arguments_))
				return false;
			out_type = raw_type;
			return true;
		}

		bool trait_type_operand(
			const pa11::TemplateInstanceArgument& instance,
			TypePtr& out_type)
		{
			TemplateArgument arg =
				raw_template_argument_from_instance_argument(instance);
			if (arg.kind != TemplateArgumentKind::Type)
				return false;
			TypePtr record = arg.type.get() != NULL
				? pa11::strip_cv(arg.type) : TypePtr();
			if (record.get() != NULL &&
			    record->kind == pa11::TypeKind::Record)
			{
				string primary = record->template_primary_name.empty()
					? record->name : record->template_primary_name;
				primary = unqualified_template_owner(primary);
				if (primary == "__and_" ||
				    primary == "__or_" ||
				    primary == "__not_" ||
				    primary == "is_same" ||
				    primary == "__are_same" ||
				    primary == "__same_value_type" ||
				    primary == "is_pointer" ||
				    primary == "__is_pointer" ||
				    primary == "is_reference" ||
				    primary == "__is_reference" ||
				    primary == "is_lvalue_reference" ||
				    primary == "is_rvalue_reference" ||
				    primary == "is_constructible" ||
				    primary == "__is_constructible" ||
				    primary == "is_nothrow_constructible" ||
				    primary == "__is_nothrow_constructible" ||
				    primary == "is_trivially_constructible" ||
				    primary == "__is_trivially_constructible" ||
				    primary == "is_copy_constructible" ||
				    primary == "is_nothrow_copy_constructible" ||
				    primary == "is_trivially_copy_constructible" ||
				    primary == "is_move_constructible" ||
				    primary == "is_nothrow_move_constructible" ||
				    primary == "is_trivially_move_constructible" ||
				    primary == "is_assignable" ||
				    primary == "__is_assignable" ||
				    primary == "is_nothrow_assignable" ||
				    primary == "__is_nothrow_assignable" ||
				    primary == "is_trivially_assignable" ||
				    primary == "__is_trivially_assignable" ||
				    primary == "is_copy_assignable" ||
				    primary == "is_nothrow_copy_assignable" ||
				    primary == "is_trivially_copy_assignable" ||
				    primary == "is_move_assignable" ||
				    primary == "is_nothrow_move_assignable" ||
				    primary == "is_trivially_move_assignable" ||
				    primary == "is_convertible" ||
				    primary == "__is_convertible")
				{
					out_type = arg.type;
					return true;
				}
			}
			return false;
		}

		bool evaluate_cheap_trait_arguments(
			const string& owner,
			const vector<pa11::TemplateInstanceArgument>& args,
			bool& value)
		{
			if ((owner == "is_same" || owner == "__are_same") &&
			    args.size() >= 2)
			{
				TypePtr left;
				TypePtr right;
				if (!raw_trait_type_argument(args[0], left) ||
				    !raw_trait_type_argument(args[1], right))
					return false;
				if (!resolve_trait_subject_type(left, left) ||
				    !resolve_trait_subject_type(right, right))
					return false;
				value = pa11::same_type(left, right);
				return true;
			}
			if ((owner == "is_pointer" || owner == "__is_pointer") &&
			    !args.empty())
			{
				TypePtr type;
				if (!raw_trait_type_argument(args[0], type))
					return false;
				TypePtr bare = type.get() != NULL
					? pa11::strip_cv(type) : TypePtr();
				if (bare.get() != NULL &&
				    bare->kind == pa11::TypeKind::Pointer)
				{
					value = true;
					return true;
				}
				if (bare.get() != NULL &&
				    (bare->kind == pa11::TypeKind::LValueReference ||
				     bare->kind == pa11::TypeKind::RValueReference))
				{
					value = false;
					return true;
				}
				if (!resolve_trait_subject_type(type, type))
					return false;
				bare = type.get() != NULL ? pa11::strip_cv(type) : TypePtr();
				value = bare.get() != NULL &&
				        bare->kind == pa11::TypeKind::Pointer;
				return true;
			}
			if ((owner == "is_reference" ||
			     owner == "__is_reference" ||
			     owner == "is_lvalue_reference" ||
			     owner == "is_rvalue_reference") &&
			    !args.empty())
			{
				TypePtr type;
				if (!raw_trait_type_argument(args[0], type))
					return false;
				TypePtr bare = type.get() != NULL
					? pa11::strip_cv(type) : TypePtr();
				if (bare.get() != NULL &&
				    (bare->kind == pa11::TypeKind::LValueReference ||
				     bare->kind == pa11::TypeKind::RValueReference ||
				     bare->kind == pa11::TypeKind::Pointer ||
				     bare->kind == pa11::TypeKind::Function ||
				     bare->kind == pa11::TypeKind::Record ||
				     bare->kind == pa11::TypeKind::Enum ||
				     bare->kind == pa11::TypeKind::Fundamental))
				{
					bool lvalue = bare->kind ==
					              pa11::TypeKind::LValueReference;
					bool rvalue = bare->kind ==
					              pa11::TypeKind::RValueReference;
					if (owner == "is_lvalue_reference")
						value = lvalue;
					else if (owner == "is_rvalue_reference")
						value = rvalue;
					else
						value = lvalue || rvalue;
					return true;
				}
				if (!resolve_trait_subject_type(type, type))
					return false;
				bare = type.get() != NULL ? pa11::strip_cv(type) : TypePtr();
				bool lvalue = bare.get() != NULL &&
				              bare->kind == pa11::TypeKind::LValueReference;
				bool rvalue = bare.get() != NULL &&
				              bare->kind == pa11::TypeKind::RValueReference;
				if (owner == "is_lvalue_reference")
					value = lvalue;
				else if (owner == "is_rvalue_reference")
					value = rvalue;
				else
					value = lvalue || rvalue;
				return true;
			}
			if ((owner == "is_constructible" ||
			     owner == "__is_constructible" ||
			     owner == "is_nothrow_constructible" ||
			     owner == "__is_nothrow_constructible" ||
			     owner == "is_trivially_constructible" ||
			     owner == "__is_trivially_constructible" ||
			     owner == "is_copy_constructible" ||
			     owner == "is_nothrow_copy_constructible" ||
			     owner == "is_trivially_copy_constructible" ||
			     owner == "is_move_constructible" ||
			     owner == "is_nothrow_move_constructible" ||
			     owner == "is_trivially_move_constructible" ||
			     owner == "is_assignable" ||
			     owner == "__is_assignable" ||
			     owner == "is_nothrow_assignable" ||
			     owner == "__is_nothrow_assignable" ||
			     owner == "is_trivially_assignable" ||
			     owner == "__is_trivially_assignable" ||
			     owner == "is_copy_assignable" ||
			     owner == "is_nothrow_copy_assignable" ||
			     owner == "is_trivially_copy_assignable" ||
			     owner == "is_move_assignable" ||
			     owner == "is_nothrow_move_assignable" ||
			     owner == "is_trivially_move_assignable") &&
			    !args.empty())
			{
				vector<TypePtr> types;
				for (size_t i = 0; i < args.size(); ++i)
				{
					TypePtr type;
					if (!raw_trait_type_argument(args[i], type))
						return false;
					if (!resolve_trait_subject_type(type, type))
						return false;
					types.push_back(type);
				}
				if (parser.hosted_compatibility_ &&
				    evaluate_hosted_constructible_trait(
					    types[0],
					    types,
					    parser.deleted_functions_,
					    value))
					return true;
				return parser.evaluate_standard_constructible_trait(
					owner, types, value);
			}
			if ((owner == "is_convertible" ||
			     owner == "__is_convertible") &&
			    args.size() >= 2)
			{
				TypePtr from;
				TypePtr to;
				if (!raw_trait_type_argument(args[0], from) ||
				    !raw_trait_type_argument(args[1], to))
					return false;
				if (!resolve_trait_subject_type(from, from) ||
				    !resolve_trait_subject_type(to, to))
					return false;
				Expr probe;
				probe.valid = true;
				probe.type = from;
				probe.category = parser.call_category(from);
				probe.node = Node("type-trait-probe " +
				                  pa11::describe_type(from));
				try
				{
					value = parser.convert_to(probe, to).viable;
				}
				catch (const runtime_error&)
				{
					value = false;
				}
				return true;
			}
			if (owner == "__not_" && args.size() == 1)
			{
				TypePtr type;
				bool inner = false;
				if (!trait_type_operand(args[0], type) ||
				    !evaluate_cheap_trait_type(type, inner))
					return false;
				value = !inner;
				return true;
			}
			if (owner == "__and_")
			{
				bool all_known = true;
				value = true;
				for (size_t i = 0; i < args.size(); ++i)
				{
					TypePtr type;
					bool elem = false;
					if (!trait_type_operand(args[i], type) ||
					    !evaluate_cheap_trait_type(type, elem))
					{
						all_known = false;
						continue;
					}
					if (!elem)
					{
						value = false;
						return true;
					}
				}
				return all_known;
			}
			if (owner == "__or_")
			{
				bool all_known = true;
				value = false;
				for (size_t i = 0; i < args.size(); ++i)
				{
					TypePtr type;
					bool elem = false;
					if (!trait_type_operand(args[i], type) ||
					    !evaluate_cheap_trait_type(type, elem))
					{
						all_known = false;
						continue;
					}
					if (elem)
					{
						value = true;
						return true;
					}
				}
				return all_known;
			}
			return false;
		}

		bool evaluate_cheap_trait_type(TypePtr type, bool& value)
		{
			TypePtr record = type.get() != NULL ? pa11::strip_cv(type) : TypePtr();
			if (record.get() == NULL || record->kind != pa11::TypeKind::Record)
				return false;
			string primary = record->template_primary_name.empty()
				? record->name : record->template_primary_name;
			primary = unqualified_template_owner(primary);
			const vector<pa11::TemplateInstanceArgument>* args = NULL;
			if (!trait_instance_arguments(record, args))
				return false;
			return evaluate_cheap_trait_arguments(primary, *args, value);
		}

		bool cheap_hosted_enable_if_condition_false(
			const TemplateArgument& arg)
		{
			if (!cheap_hosted_enable_if_condition(arg))
				return false;
			string owner = unqualified_template_owner(
				arg.value_owner_template_name);
			bool value = false;
			return evaluate_cheap_trait_arguments(
				       owner,
				       arg.value_owner_template_arguments,
				       value) &&
			       !value;
		}

			bool can_leave_parameter_type_dependent(TypePtr parameter_type,
			                                        const runtime_error& err)
			{
		if (parser.function_template_candidate_instantiation_depth_ == 0 ||
		    string(err.what()) != "dependent typename not resolved")
			return false;
		TypePtr bare_parameter_type = parameter_type.get() != NULL
			? pa11::strip_cv(parameter_type) : TypePtr();
			if (bare_parameter_type.get() == NULL ||
			    !bare_parameter_type->is_dependent_typename ||
			    bare_parameter_type->template_arguments.empty())
				return true;
			if (!dependent_typename_is_enable_if(bare_parameter_type))
				return true;
			if (!parser.hosted_compatibility_)
				return !substituted_condition_false(bare_parameter_type);
			if (dependent_typename_condition_false(bare_parameter_type))
				return false;
			return !dependent_value_condition_false(bare_parameter_type);
		}

		bool substituted_condition_false(TypePtr type)
		{
			vector<TemplateArgument> candidate_args;
			try
			{
				for (size_t ai = 0; ai < type->template_arguments.size(); ++ai)
				{
					TemplateArgument candidate_arg =
						parser.template_argument_from_instance_argument(
							type->template_arguments[ai]);
					candidate_args.push_back(
						parser.substitute_template_argument(candidate_arg));
				}
			}
			catch (const runtime_error&)
			{
				return false;
			}
			return dependent_typename_disabled_enable_if_argument(
				type,
				candidate_args);
		}

		bool dependent_value_condition_false(TypePtr type)
		{
			if (type.get() == NULL || type->template_arguments.empty())
				return false;
			const pa11::TemplateInstanceArgument& condition =
				type->template_arguments[0];
			if (condition.kind != pa11::TemplateInstanceArgumentKind::Value ||
			    !condition.dependent)
				return false;
			try
			{
				TemplateArgument arg =
					raw_template_argument_from_instance_argument(condition);
				if (!arg.value_owner_template_name.empty() &&
				    !arg.value_member_name.empty())
				{
					if (cheap_hosted_enable_if_condition_false(arg))
						return true;
					TemplateArgument resolved;
					if (parser.resolve_dependent_value_member_argument(
						    arg,
						    resolved))
						arg = resolved;
				}
				arg = parser.substitute_template_argument(arg);
				if (arg.kind == TemplateArgumentKind::Value &&
				    !arg.dependent)
					return arg.value == 0;
			}
			catch (const runtime_error&)
			{
			}
			return false;
		}

	void collect_current_substitutions(
		map<string, TypePtr>& subst,
		map<string, TemplateArgument>& value_subst,
		set<string>& pack_subst,
		bool* concrete_completion) const
	{
		for (size_t i = 0;
		     i < out.size() && i < declaration->parameters.size();
		     ++i)
		{
			const TemplateParameterInfo& parameter =
				declaration->parameters[i];
			if (parameter.name.empty())
				continue;
			if (parameter.kind == TemplateParameterKind::Type)
			{
				if (parameter.is_pack)
				{
					subst[parameter.name] =
						template_parameter_placeholder_type(parameter);
					value_subst[parameter.name] = out[i];
					pack_subst.insert(parameter.name);
				}
				else
					subst[parameter.name] = out[i].type;
			}
			else
				value_subst[parameter.name] = out[i];
		}
		if (concrete_completion == NULL)
			return;
		for (map<string, TypePtr>::const_iterator it = subst.begin();
		     it != subst.end();
		     ++it)
			if (parser.type_is_template_dependent(it->second))
				*concrete_completion = false;
		for (map<string, TemplateArgument>::const_iterator it =
			     value_subst.begin();
		     it != value_subst.end();
		     ++it)
			if (template_argument_has_template_parameter(
				    it->second,
				    parser.record_template_arguments_))
				*concrete_completion = false;
	}

	void append_explicit_argument(const TemplateParameterInfo& parameter,
	                              TypePtr parameter_type)
	{
		TemplateArgument arg = explicit_expanded[explicit_index++];
		TemplateArgument original_arg = arg;
		if (parameter.kind == TemplateParameterKind::NonType &&
		    arg.kind == TemplateArgumentKind::Value &&
		    arg.dependent &&
		    parameter_type.get() != NULL)
			arg.type = parameter_type;
		if (parameter.kind == TemplateParameterKind::Type &&
		    arg.kind == TemplateArgumentKind::Value &&
		    arg.type.get() != NULL &&
		    (arg.dependent ||
		     pa11::strip_cv(arg.type)->kind != pa11::TypeKind::Fundamental))
		{
			bool pack_expansion = arg.pack_expansion;
			arg = TemplateArgument::type_arg(arg.type);
			arg.pack_expansion = pack_expansion;
		}
		substitute_explicit_argument(arg);
		if (parameter.kind == TemplateParameterKind::TemplateTemplate &&
		    arg.kind == TemplateArgumentKind::Type)
		{
			TemplateDeclaration* recovered =
				parser.class_template_declaration_for_match(arg.type);
			if (recovered != NULL)
				arg = TemplateArgument::template_arg(recovered);
		}
		if (!template_argument_kind_matches_parameter(arg, parameter))
			arg = dependent_value_argument_from_type(parameter,
			                                     parameter_type,
			                                     arg,
			                                     original_arg);
		arg = parser.convert_completed_non_type_template_argument(
			arg,
			parameter_type);
		out.push_back(arg);
	}

	void substitute_explicit_argument(TemplateArgument& arg)
	{
		map<string, TypePtr> subst;
		map<string, TemplateArgument> value_subst;
		set<string> pack_subst;
		collect_current_substitutions(subst, value_subst, pack_subst, NULL);
		SubstitutionScope scope(parser,
		                        declaration,
		                        subst,
		                        value_subst,
		                        pack_subst);
		if (!explicit_value_name_collides(arg))
			arg = parser.substitute_template_argument(arg);
	}

	bool explicit_value_name_collides(const TemplateArgument& arg) const
	{
		if (arg.kind != TemplateArgumentKind::Value ||
		    !arg.dependent ||
		    arg.value_name.empty())
			return false;
		for (size_t pi = 0; pi < declaration->parameters.size(); ++pi)
			if (declaration->parameters[pi].name == arg.value_name)
				return true;
		return false;
	}

	TemplateArgument dependent_value_argument_from_type(
		const TemplateParameterInfo& parameter,
		TypePtr parameter_type,
		const TemplateArgument& arg,
		const TemplateArgument& original_arg)
	{
		TypePtr dependent_type = arg.type;
		TypePtr dependent_bare = dependent_type.get() != NULL
			? pa11::strip_cv(dependent_type) : TypePtr();
		if ((dependent_bare.get() == NULL ||
		     !dependent_bare->is_dependent_typename ||
		     !dependent_bare->dependent_typename_qualified) &&
		    original_arg.kind == TemplateArgumentKind::Type)
		{
			TypePtr original_bare = original_arg.type.get() != NULL
				? pa11::strip_cv(original_arg.type) : TypePtr();
			if (original_bare.get() != NULL &&
			    original_bare->is_dependent_typename &&
			    original_bare->dependent_typename_qualified)
			{
				dependent_type = original_arg.type;
				dependent_bare = original_bare;
			}
		}
		if (parameter.kind == TemplateParameterKind::NonType &&
		    arg.kind == TemplateArgumentKind::Type &&
		    dependent_bare.get() != NULL &&
		    dependent_bare->kind == pa11::TypeKind::Function &&
		    dependent_bare->parameters.size() == 1 &&
		    parameter_type.get() != NULL &&
		    pa11::same_type(dependent_bare->base, parameter_type))
			dependent_type = dependent_bare->parameters[0];
		dependent_bare = dependent_type.get() != NULL
			? pa11::strip_cv(dependent_type) : TypePtr();
		if (parameter.kind != TemplateParameterKind::NonType ||
		    arg.kind != TemplateArgumentKind::Type ||
		    dependent_type.get() == NULL ||
		    !dependent_bare->is_dependent_typename ||
		    !dependent_bare->dependent_typename_qualified)
			throw runtime_error("template argument kind mismatch");
		TemplateArgument value_arg =
			TemplateArgument::dependent_value_arg(parameter_type);
		value_arg.value_name = dependent_type->name;
		attach_dependent_value_owner(dependent_bare, value_arg);
		return parser.substitute_template_argument(value_arg);
	}

	void attach_dependent_value_owner(TypePtr dependent_bare,
	                                  TemplateArgument& value_arg)
	{
		size_t member_pos = dependent_bare->name.rfind("::");
		string member_name = member_pos != string::npos
			? dependent_bare->name.substr(member_pos + 2) : string();
		string owner_name = dependent_bare->template_primary_name;
		if (owner_name.empty())
		{
			string root = member_pos != string::npos
				? dependent_bare->name.substr(0, member_pos)
				: dependent_bare->name;
			size_t template_pos = root.find('<');
			owner_name = root.substr(0, template_pos);
		}
		if (owner_name.empty() || member_name.empty())
			return;
		value_arg.value_owner_template_name = owner_name;
		value_arg.value_member_name = member_name;
		for (size_t ai = 0;
		     ai < dependent_bare->template_arguments.size();
		     ++ai)
		{
			TemplateArgument owner_arg =
				parser.template_argument_from_instance_argument(
					dependent_bare->template_arguments[ai]);
			owner_arg = parser.substitute_template_argument(owner_arg);
			value_arg.value_owner_template_arguments.push_back(
				completed_instance_argument(owner_arg));
		}
	}

	void append_default_argument(size_t parameter_index,
	                             const TemplateParameterInfo& parameter,
	                             TypePtr parameter_type)
	{
		if (!parameter.has_default)
			throw runtime_error("missing template argument");
		TemplateArgument arg;
		try
		{
			arg = parser.parse_default_template_argument(declaration,
			                                            parameter_index,
			                                            out);
			if (parameter.kind == TemplateParameterKind::Type)
				arg = parser.substitute_template_argument(arg);
		}
		catch (const runtime_error& err)
		{
			if (!use_dependent_default(parameter, err))
				throw;
			string default_name = parameter.name.empty()
				? declaration->name + "__default" +
				  to_string(parameter_index)
				: parameter.name;
			arg = TemplateArgument::type_arg(
				pa11::make_dependent_typename_type(default_name,
				                                   false,
				                                   false,
				                                   false));
		}
		arg = parser.convert_completed_non_type_template_argument(
			arg,
			parameter_type);
		out.push_back(arg);
	}

	bool use_dependent_default(const TemplateParameterInfo& parameter,
	                           const runtime_error& err) const
	{
		if (parser.function_template_candidate_instantiation_depth_ == 0 ||
		    parameter.kind != TemplateParameterKind::Type ||
		    string(err.what()) != "dependent typename not resolved")
			return false;
		for (size_t ai = 0; ai < out.size(); ++ai)
			if (template_argument_has_template_parameter(
				    out[ai],
				    parser.record_template_arguments_))
				return true;
		return false;
	}

	void finalize_non_type_arguments()
	{
		map<string, TypePtr> subst;
		map<string, TemplateArgument> value_subst;
		set<string> pack_subst;
		bool concrete_completion = true;
		collect_current_substitutions(subst,
		                              value_subst,
		                              pack_subst,
		                              &concrete_completion);
		SubstitutionScope scope(parser,
		                        declaration,
		                        subst,
		                        value_subst,
		                        pack_subst);
		for (size_t i = 0; i < out.size() && i < declaration->parameters.size();
		     ++i)
		{
			if (declaration->parameters[i].kind !=
				    TemplateParameterKind::NonType ||
			    declaration->parameters[i].type.get() == NULL)
				continue;
			TypePtr parameter_type =
				final_non_type_parameter_type(i, concrete_completion);
			out[i] = parser.convert_completed_non_type_template_argument(
				out[i],
				parameter_type);
		}
	}

	TypePtr final_non_type_parameter_type(size_t parameter_index,
	                                      bool& concrete_completion)
	{
		TypePtr parameter_type = declaration->parameters[parameter_index].type;
		try
		{
			parameter_type =
				substitute_parameter_type_in_declaration_scope(parameter_type);
		}
			catch (const runtime_error& err)
			{
				if (parser.function_template_candidate_instantiation_depth_ != 0 &&
				    string(err.what()) == "dependent typename not resolved" &&
				    can_leave_parameter_type_dependent(parameter_type, err))
				{
					concrete_completion = false;
					return parameter_type;
				}
			throw;
		}
		resolve_dependent_parameter_type(parameter_type,
		                                 concrete_completion);
		return parameter_type;
	}

	void resolve_dependent_parameter_type(TypePtr& parameter_type,
	                                      bool& concrete_completion)
	{
		TypePtr parameter_bare = parameter_type.get() != NULL
			? pa11::strip_cv(parameter_type) : TypePtr();
		if (parameter_bare.get() == NULL ||
		    !parameter_bare->is_dependent_typename)
			return;
		TypePtr resolved =
			parser.resolve_dependent_typename_type(parameter_bare);
		if (resolved.get() != NULL && resolved != parameter_bare)
		{
			parameter_type = parser.substitute_template_type(resolved);
			return;
		}
		if (parameter_bare->dependent_typename_qualified &&
		    !parameter_bare->template_primary_name.empty() &&
		    !parameter_bare->template_arguments.empty())
		{
			resolve_qualified_parameter_type(parameter_type,
			                                 parameter_bare,
			                                 concrete_completion);
			return;
		}
		mark_unresolved_dependent_parameter(concrete_completion);
	}

	void mark_unresolved_dependent_parameter(bool& concrete_completion)
	{
		if (!concrete_completion)
			return;
		if (parser.function_template_candidate_instantiation_depth_ != 0)
			concrete_completion = false;
		else
			throw runtime_error("dependent typename not resolved");
	}

	void resolve_qualified_parameter_type(TypePtr& parameter_type,
	                                      TypePtr parameter_bare,
	                                      bool& concrete_completion)
	{
		string member_name = parameter_bare->name;
		size_t member_pos = member_name.rfind("::");
		if (member_pos != string::npos)
			member_name = member_name.substr(member_pos + 2);
		vector<TemplateArgument> owner_args;
		bool owner_args_dependent = false;
		collect_owner_arguments(parameter_bare,
		                        owner_args,
		                        owner_args_dependent);
		if (!owner_args_dependent)
			resolve_owner_member_type(parameter_bare,
			                          member_name,
			                          owner_args,
			                          parameter_type);
		TypePtr current_bare = parameter_type.get() != NULL
			? pa11::strip_cv(parameter_type) : TypePtr();
		if (concrete_completion &&
		    !owner_args_dependent &&
		    current_bare.get() != NULL &&
		    current_bare->is_dependent_typename)
			mark_unresolved_dependent_parameter(concrete_completion);
	}

	void collect_owner_arguments(TypePtr parameter_bare,
	                             vector<TemplateArgument>& owner_args,
	                             bool& owner_args_dependent)
	{
		for (size_t ai = 0;
		     ai < parameter_bare->template_arguments.size();
		     ++ai)
		{
			TemplateArgument owner_arg =
				parser.template_argument_from_instance_argument(
					parameter_bare->template_arguments[ai]);
			resolve_owner_value_argument(owner_arg,
			                             owner_args_dependent);
			try
			{
				owner_arg = parser.substitute_template_argument(owner_arg);
			}
			catch (const runtime_error&)
			{
				if (owner_arg.kind == TemplateArgumentKind::Value &&
				    owner_arg.dependent &&
				    owner_arg.value_expr_end > owner_arg.value_expr_begin &&
				    parser.function_template_candidate_instantiation_depth_ != 0)
					owner_args_dependent = true;
				else
					throw;
			}
			if (template_argument_has_template_parameter(
				    owner_arg,
				    parser.record_template_arguments_))
				owner_args_dependent = true;
			if (owner_arg.kind == TemplateArgumentKind::Value &&
			    owner_arg.dependent &&
			    owner_arg.value_expr_end > owner_arg.value_expr_begin &&
			    parser.function_template_candidate_instantiation_depth_ != 0)
				owner_args_dependent = true;
			owner_args.push_back(owner_arg);
		}
	}

	void resolve_owner_value_argument(TemplateArgument& owner_arg,
	                                  bool& owner_args_dependent)
	{
		if (owner_arg.kind != TemplateArgumentKind::Value ||
		    !owner_arg.dependent ||
		    owner_arg.value_owner_template_name.empty())
			return;
		TemplateArgument resolved_value;
		try
		{
			if (parser.resolve_dependent_value_member_argument(
				    owner_arg,
				    resolved_value))
				owner_arg = resolved_value;
		}
		catch (const runtime_error&)
		{
			if (owner_arg.value_expr_end > owner_arg.value_expr_begin &&
			    parser.function_template_candidate_instantiation_depth_ != 0)
				owner_args_dependent = true;
			else
				throw;
		}
	}

	void resolve_owner_member_type(TypePtr parameter_bare,
	                               const string& member_name,
	                               const vector<TemplateArgument>& owner_args,
	                               TypePtr& parameter_type)
	{
		string lookup_name = parameter_bare->template_primary_name;
		Scope* qualifier = NULL;
		parser.resolve_template_name_spelling(
			parameter_bare->template_primary_name,
			qualifier,
			lookup_name);
		TemplateDeclaration* klass =
			find_owner_class_template(qualifier,
			                          lookup_name,
			                          parameter_bare);
		if (klass == NULL)
			return;
		TypePtr owner = parser.instantiate_class_template(klass, owner_args);
		TypePtr owner_bare = owner.get() != NULL
			? pa11::strip_cv(owner) : TypePtr();
		if (owner_bare.get() == NULL ||
		    owner_bare->kind != pa11::TypeKind::Record ||
		    owner_bare->scope == NULL)
			return;
		parser.complete_template_record(owner_bare);
		vector<Binding*> found =
			parser.lookup_qualified_set(owner_bare->scope,
			                            member_name,
			                            pa11::LOOKUP_TYPE);
		if (!found.empty() && found[0]->type.get() != NULL)
			parameter_type =
				parser.substitute_template_type_in_scope(found[0]->type,
				                                         owner_bare->scope);
	}

	TemplateDeclaration* find_owner_class_template(
		Scope* qualifier,
		const string& lookup_name,
		TypePtr parameter_bare)
	{
		TemplateDeclaration* klass =
			parser.find_class_template(qualifier, lookup_name);
		if (klass == NULL && qualifier != NULL)
			klass = parser.find_class_template(NULL, lookup_name);
		if (klass == NULL)
			klass = parser.find_class_template(
				NULL,
				parameter_bare->template_primary_name);
		if (klass != NULL)
			return klass;
		for (map<Scope*, map<string, TemplateDeclaration*> >::const_iterator
			     sit = parser.class_templates_.begin();
		     sit != parser.class_templates_.end();
		     ++sit)
		{
			map<string, TemplateDeclaration*>::const_iterator found =
				sit->second.find(lookup_name);
			if (found == sit->second.end())
				found = sit->second.find(
					parameter_bare->template_primary_name);
			if (found != sit->second.end())
				return found->second;
		}
		return NULL;
	}
};

TemplateArgument Parser::convert_completed_non_type_template_argument(
	TemplateArgument argument,
	TypePtr parameter_type)
{
	if (argument.kind == TemplateArgumentKind::Value &&
	    argument.value_binding != NULL &&
	    argument.value_binding->kind == BindingKind::Function &&
	    parameter_type.get() != NULL)
	{
		TypePtr parameter_bare = pa11::strip_cv(parameter_type);
		if (parameter_bare->kind == pa11::TypeKind::MemberPointer)
		{
			Binding* binding = argument.value_binding;
			Expr inner;
			inner.valid = true;
			inner.binding = binding;
			inner.type = binding->type;
			inner.category = ValueCategory::LValue;
			if (binding->owner != NULL)
			{
				vector<Binding*> overloads =
					lookup_qualified_set(binding->owner,
					                     binding->name,
					                     pa11::LOOKUP_FUNCTION);
				for (size_t i = 0; i < overloads.size(); ++i)
					if (overloads[i]->kind == BindingKind::Function)
						inner.overloads.push_back(overloads[i]);
			}
			if (inner.overloads.empty())
				inner.overloads.push_back(binding);
			inner.node = Node("id-expression lvalue " +
			                  pa11::describe_type(binding->type) + " " +
			                  qualified_decl_name(binding));
			inner.node.binding = binding;
			annotate_expr_node(inner);
			try
			{
				Expr address = make_address_expr("&", inner);
				Conversion conv = convert_to(address, parameter_type);
				if (conv.viable &&
				    conv.expr.node.has_op &&
				    conv.expr.node.op == OP_AMP &&
				    !conv.expr.node.children.empty() &&
				    conv.expr.node.children[0].binding != NULL)
				{
					Binding* member = conv.expr.node.children[0].binding;
					if (member->aliased_binding != NULL &&
					    member->target_scope != NULL)
						member = member->aliased_binding;
					TemplateArgument resolved =
						TemplateArgument::value_arg(
							expression_object_type(conv.expr.type),
							reinterpret_cast<uint64_t>(member));
					resolved.value_binding = member;
					resolved.value_name = argument.value_name;
					return convert_non_type_template_argument(resolved,
					                                          parameter_type);
				}
			}
			catch (const runtime_error&)
			{
			}
		}
	}
	return convert_non_type_template_argument(argument, parameter_type);
}

vector<TemplateArgument> Parser::complete_template_arguments(
	TemplateDeclaration* declaration,
	const vector<TemplateArgument>& explicit_arguments)
{
	vector<size_t> cache_key;
	cache_key.reserve(16 + explicit_arguments.size() * 2);
	cache_key.push_back(reinterpret_cast<uintptr_t>(declaration));
	cache_key.push_back(declaration != NULL ? declaration->parameters.size() : 0);
	cache_key.push_back(explicit_arguments.size());
	for (size_t i = 0; i < explicit_arguments.size(); ++i)
		cache_key.push_back(dependent_cache_template_argument_identity(
			explicit_arguments[i],
			0));
	cache_key.push_back(template_type_substitutions_.size());
	for (size_t i = 0; i < template_type_substitutions_.size(); ++i)
	{
		cache_key.push_back(template_type_substitutions_[i].size());
		for (map<string, TypePtr>::const_iterator it =
			     template_type_substitutions_[i].begin();
		     it != template_type_substitutions_[i].end();
		     ++it)
		{
			cache_key.push_back(dependent_cache_string_hash(it->first));
			cache_key.push_back(dependent_cache_type_identity(it->second));
		}
	}
	cache_key.push_back(template_value_substitutions_.size());
	for (size_t i = 0; i < template_value_substitutions_.size(); ++i)
	{
		cache_key.push_back(template_value_substitutions_[i].size());
		for (map<string, TemplateArgument>::const_iterator it =
			     template_value_substitutions_[i].begin();
		     it != template_value_substitutions_[i].end();
		     ++it)
		{
			cache_key.push_back(dependent_cache_string_hash(it->first));
			cache_key.push_back(dependent_cache_template_argument_identity(
				it->second,
				0));
		}
	}
	cache_key.push_back(template_type_parameter_packs_.size());
	for (size_t i = 0; i < template_type_parameter_packs_.size(); ++i)
	{
		cache_key.push_back(template_type_parameter_packs_[i].size());
		for (set<string>::const_iterator it =
			     template_type_parameter_packs_[i].begin();
		     it != template_type_parameter_packs_[i].end();
		     ++it)
			cache_key.push_back(dependent_cache_string_hash(*it));
	}
	map<vector<size_t>, vector<TemplateArgument> >::const_iterator cached =
		completed_template_argument_cache_.find(cache_key);
	if (cached != completed_template_argument_cache_.end())
		return cached->second;
	TemplateArgumentCompleter completer(*this,
	                                    declaration,
	                                    explicit_arguments);
	vector<TemplateArgument> out = completer.run();
	completed_template_argument_cache_[cache_key] = out;
	if (completed_template_argument_cache_.size() >
	    kCompletedTemplateArgumentCacheLimit)
		completed_template_argument_cache_.clear();
	return out;
}

}  // namespace internal
}  // namespace pa12
