#include "pa12_expr_parser_support.h"
#include "pa12_types_support.h"

#include <cstdint>
#include <stdexcept>

using namespace std;

namespace pa12 {
namespace internal {

bool hosted_library_namespace_scope(Scope* scope);

size_t dependent_cache_hash_combine(size_t seed, size_t value);
size_t dependent_cache_string_hash(const string& value);
size_t dependent_cache_type_identity(TypePtr type);
size_t dependent_cache_template_argument_identity(
	const TemplateArgument& argument,
	int depth);

namespace {

size_t builtin_trait_type_cache_identity(TypePtr type, int depth)
{
	if (type.get() == NULL)
		return 0;
	size_t out = static_cast<size_t>(type->kind);
	out = dependent_cache_hash_combine(out, type->fundamental);
	out = dependent_cache_hash_combine(out, type->cv);
	out = dependent_cache_hash_combine(out, type->ref_qualifier);
	out = dependent_cache_hash_combine(out, type->unknown_bound);
	out = dependent_cache_hash_combine(out, type->bound);
	out = dependent_cache_hash_combine(out, type->variadic);
	out = dependent_cache_hash_combine(
		out,
		dependent_cache_string_hash(type->name));
	out = dependent_cache_hash_combine(
		out,
		dependent_cache_string_hash(type->template_primary_name));
	if (type->kind == pa11::TypeKind::Record ||
	    type->kind == pa11::TypeKind::Enum ||
	    type->kind == pa11::TypeKind::TemplateParameter ||
	    type->kind == pa11::TypeKind::TemplateTemplateParameter)
		return dependent_cache_hash_combine(
			out,
			dependent_cache_type_identity(type));
	if (depth > 8)
		return dependent_cache_hash_combine(out, 0x717);
	out = dependent_cache_hash_combine(
		out,
		builtin_trait_type_cache_identity(type->base, depth + 1));
	out = dependent_cache_hash_combine(
		out,
		builtin_trait_type_cache_identity(type->member_class, depth + 1));
	for (size_t i = 0; i < type->parameters.size(); ++i)
		out = dependent_cache_hash_combine(
			out,
			builtin_trait_type_cache_identity(type->parameters[i],
			                                  depth + 1));
	return out;
}

bool trait_record_has_user_destructor(TypePtr record)
{
	TypePtr bare = pa11::strip_cv(record);
	if (bare->kind != pa11::TypeKind::Record || bare->scope == NULL)
		return false;
	map<string, vector<Binding*> >::const_iterator found =
		bare->scope->members.find("~" + bare->scope->name);
	if (found == bare->scope->members.end())
		return false;
	for (size_t i = 0; i < found->second.size(); ++i)
	{
		Binding* fn = found->second[i];
		if (fn != NULL && !fn->is_defaulted &&
		    !fn->is_generated_default_destructor)
			return true;
	}
	return false;
}

bool trait_type_has_nontrivial_record_transfer(TypePtr type)
{
	TypePtr bare = pa11::strip_cv(type);
	if (bare->kind == pa11::TypeKind::Array)
		return trait_type_has_nontrivial_record_transfer(
			bare->base);
	if (bare->kind != pa11::TypeKind::Record)
		return false;
	if (bare->tag == "union" ||
	    bare->is_polymorphic ||
	    trait_record_has_user_copy_constructor(bare) ||
	    trait_record_has_user_assignment(bare) ||
	    trait_record_has_user_destructor(bare) ||
	    trait_record_has_virtual_destructor(bare))
		return true;
	pa11::layout_record_type(bare);
	vector<TypePtr> bases = pa11::record_direct_bases(bare);
	for (size_t i = 0; i < bases.size(); ++i)
		if (trait_type_has_nontrivial_record_transfer(bases[i]))
			return true;
	for (size_t i = 0; i < bare->fields.size(); ++i)
		if (trait_type_has_nontrivial_record_transfer(
			    bare->fields[i]->type))
			return true;
	return false;
}

Binding* trait_declared_copy_move_constructor(TypePtr record, bool move)
{
	TypePtr bare = pa11::strip_cv(record);
	if (bare->kind != pa11::TypeKind::Record || bare->scope == NULL)
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

bool hosted_trait_record(TypePtr type)
{
	TypePtr bare = type.get() != NULL ? pa11::strip_cv(type) : TypePtr();
	return bare.get() != NULL &&
	       bare->kind == pa11::TypeKind::Record &&
	       bare->scope != NULL &&
	       hosted_library_namespace_scope(bare->scope);
}

string trait_unqualified_template_primary(TypePtr type)
{
	TypePtr bare = type.get() != NULL ? pa11::strip_cv(type) : TypePtr();
	if (bare.get() == NULL)
		return "";
	string primary = bare->template_primary_name.empty()
		? bare->name : bare->template_primary_name;
	size_t args = primary.find('<');
	if (args != string::npos)
		primary = primary.substr(0, args);
	size_t scope = primary.rfind("::");
	if (scope != string::npos)
		primary = primary.substr(scope + 2);
	return primary;
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
			Binding* ctor = trait_declared_copy_move_constructor(bare, move);
			if (ctor == NULL && move)
				ctor = trait_declared_copy_move_constructor(bare, false);
			if (ctor == NULL && !move &&
			    trait_unqualified_template_primary(bare) == "unique_ptr")
			{
				value = false;
				return true;
			}
			value = ctor == NULL ||
			        deleted.find(ctor) == deleted.end();
			return true;
		}
	}
	value = true;
	return true;
}

}  // namespace

void Parser::parse_type_trait_operand_list(const string& name,
                                           vector<TypePtr>& types,
                                           bool& dependent,
                                           string& spelling)
{
	expect(OP_LPAREN);
	if (!at(OP_RPAREN))
	{
		for (;;)
		{
			size_t type_begin = pos_;
			TypePtr type = parse_type_id();
			size_t type_end = pos_;
			bool pack_expansion = consume(OP_DOTS);
			if (pack_expansion)
			{
				string pack_name;
				TemplateArgument subst;
				if (type_contains_template_parameter_name(type, pack_name) &&
				    find_template_value_substitution(pack_name, subst) &&
				    subst.kind == TemplateArgumentKind::Pack)
				{
					TemplateArgument pattern =
						TemplateArgument::type_arg(type);
					pattern.pack_expansion = true;
					vector<TemplateArgument> expanded =
						expand_template_argument_pack(pattern);
					for (size_t i = 0; i < expanded.size(); ++i)
					{
						TemplateArgument elem =
							substitute_template_argument(expanded[i]);
						if (elem.kind != TemplateArgumentKind::Type)
							throw runtime_error("type pack required");
						if (!types.empty())
							spelling += ", ";
						spelling += pa11::describe_type(elem.type);
						types.push_back(elem.type);
						if (type_is_template_dependent(elem.type))
							dependent = true;
					}
					if (!consume(OP_COMMA))
						break;
					continue;
				}
				if (type_end == type_begin + 1 &&
				    parameter_pack_expansion_name(tokens_[type_begin].source) &&
				    find_template_value_substitution(tokens_[type_begin].source,
				                                     subst) &&
				    subst.kind == TemplateArgumentKind::Pack)
				{
					for (size_t i = 0; i < subst.pack.size(); ++i)
					{
						TemplateArgument elem =
							substitute_template_argument(subst.pack[i]);
						if (elem.kind != TemplateArgumentKind::Type)
							throw runtime_error("type pack required");
						if (!types.empty())
							spelling += ", ";
						spelling += pa11::describe_type(elem.type);
						types.push_back(elem.type);
						if (type_is_template_dependent(elem.type))
							dependent = true;
					}
					if (!consume(OP_COMMA))
						break;
					continue;
				}
				dependent = true;
			}
			else if (type_is_template_dependent(type))
				dependent = true;
			if (!types.empty())
				spelling += ", ";
			spelling += pa11::describe_type(type);
			if (pack_expansion)
				spelling += "...";
			types.push_back(type);
			if (!consume(OP_COMMA))
				break;
		}
	}
	expect(OP_RPAREN);
	spelling += ")";
	(void)name;
}

Expr Parser::make_dependent_type_trait_expr(const string& spelling)
{
	Expr out;
	out.type = pa11::make_fundamental(FT_BOOL);
	out.category = ValueCategory::PRValue;
	out.valid = true;
	out.constant_expression = true;
	out.has_constant_value = false;
	out.dependent_value_name = spelling;
	out.node = Node("type-trait-expression prvalue bool");
	out.node.token_text = spelling;
	annotate_expr_node(out);
	return out;
}

bool Parser::evaluate_assignable_type_trait(const string& name,
                                            const vector<TypePtr>& types,
                                            bool& value)
{
	if (types.size() != 2)
		return false;
	bool require_noexcept =
		name == "__is_nothrow_assignable" ||
		name == "is_nothrow_assignable" ||
		name == "is_nothrow_copy_assignable" ||
		name == "is_nothrow_move_assignable";
	bool require_trivial =
		name == "__is_trivially_assignable" ||
		name == "is_trivially_assignable" ||
		name == "is_trivially_copy_assignable" ||
		name == "is_trivially_move_assignable";
	value = false;
	if (types[0].get() == NULL || types[1].get() == NULL)
		return true;
	TypePtr lhs = pa11::strip_cv(types[0]);
	if (lhs->kind != pa11::TypeKind::LValueReference)
		return true;
	TypePtr object = lhs->base;
	if (object.get() == NULL || pa11::type_has_const(object))
		return true;
	TypePtr record = trait_object_type(object);
	if (record->kind == pa11::TypeKind::Array)
		return true;
	TypePtr rhs = pa11::strip_cv(types[1]);
	TypePtr rhs_object = rhs;
	bool rhs_rvalue = false;
	if (rhs->kind == pa11::TypeKind::LValueReference ||
	    rhs->kind == pa11::TypeKind::RValueReference)
	{
		rhs_object = rhs->base;
		rhs_rvalue = rhs->kind == pa11::TypeKind::RValueReference;
	}
	if (record->kind == pa11::TypeKind::Record)
	{
		complete_template_record(record);
		TypePtr rhs_record = rhs_object.get() != NULL
			? trait_object_type(rhs_object) : TypePtr();
		if (rhs_record.get() != NULL &&
		    rhs_record->kind == pa11::TypeKind::Record &&
		    pa11::same_type(rhs_record, record))
		{
			bool move = rhs_rvalue && !pa11::type_has_const(rhs_object);
			value = copy_move_assignment_available(record, move);
			if (value && require_noexcept)
			{
				Binding* op = ensure_copy_move_assignment(record, move);
				if (op == NULL && move)
					op = ensure_copy_move_assignment(record, false);
				value = op != NULL &&
				        deleted_functions_.find(op) ==
					        deleted_functions_.end() &&
				        op->unwind_no;
			}
			if (value && require_trivial)
				value = !trait_record_has_user_assignment(record) &&
				        !trait_type_has_nontrivial_record_transfer(record);
			return true;
		}
		Expr lhs_expr;
		lhs_expr.valid = true;
		lhs_expr.type = types[0];
		lhs_expr.category = ValueCategory::LValue;
		lhs_expr.node = Node("id-expression lvalue " +
		                     pa11::describe_type(types[0]) +
		                     " <assignable-lhs>");
		lhs_expr.node.type = types[0];
		lhs_expr.node.category = lhs_expr.category;
		annotate_expr_node(lhs_expr);
		Expr rhs_expr;
		rhs_expr.valid = true;
		rhs_expr.type = types[1];
		rhs_expr.category = call_category(types[1]);
		rhs_expr.node = Node("id-expression " +
		                     value_category_name(rhs_expr.category) +
		                     " " + pa11::describe_type(types[1]) +
		                     " <assignable-rhs>");
		rhs_expr.node.type = types[1];
		rhs_expr.node.category = rhs_expr.category;
		annotate_expr_node(rhs_expr);
		try
		{
			++unevaluated_expression_depth_;
			Expr assignment =
				make_assignment_expr(OP_ASS, "=", lhs_expr, rhs_expr);
			--unevaluated_expression_depth_;
			value = true;
			if (require_noexcept)
				value = node_is_noexcept(assignment.node);
			if (value && require_trivial)
				value = !trait_record_has_user_assignment(record) &&
				        !trait_type_has_nontrivial_record_transfer(record);
		}
		catch (const runtime_error&)
		{
			--unevaluated_expression_depth_;
			value = false;
		}
		return true;
	}
	value = true;
	return true;
}

bool Parser::evaluate_builtin_type_relation_trait(const string& name,
                                                  const vector<TypePtr>& types,
                                                  bool& value)
{
	if (name == "__is_same")
	{
		value = types.size() == 2 && pa11::same_type(types[0], types[1]);
		return true;
	}
	if (name == "__is_constructible" ||
	    name == "__is_nothrow_constructible" ||
	    name == "__is_trivially_constructible")
	{
		value = name == "__is_nothrow_constructible"
			? is_nothrow_constructible_type_trait(types)
			: is_constructible_type_trait(types);
		if (value && name == "__is_trivially_constructible" && !types.empty())
		{
			TypePtr target = trait_object_type(types[0]);
			if (target->kind == pa11::TypeKind::Record)
			{
				complete_template_record(target);
				if (types.size() == 2)
					value = !trait_record_has_user_copy_constructor(target);
				value = value &&
					!trait_type_has_nontrivial_record_transfer(target);
			}
		}
		return true;
	}
	if ((name == "__is_assignable" ||
	     name == "__is_nothrow_assignable" ||
	     name == "__is_trivially_assignable") && types.size() == 2)
	{
		return evaluate_assignable_type_trait(name, types, value);
	}
	if (name == "__is_convertible" && types.size() == 2)
	{
		TypePtr scalar_source = lvalue_to_rvalue_type(types[0]);
		TypePtr scalar_target = pa11::strip_top_level_cv(types[1]);
		if (trait_is_scalar(scalar_source) && trait_is_scalar(scalar_target))
		{
			value = scalar_conversion_rank(types[0], types[1]) < 1000000;
			return true;
		}
		TypePtr source_record = trait_object_type(types[0]);
		TypePtr target_record = trait_object_type(types[1]);
		if (source_record.get() != NULL &&
		    target_record.get() != NULL &&
		    source_record->kind == pa11::TypeKind::Record &&
		    target_record->kind == pa11::TypeKind::Record &&
		    hosted_trait_record(source_record) &&
		    hosted_trait_record(target_record))
		{
			if (pa11::same_type(source_record, target_record))
			{
				TypePtr source = pa11::strip_cv(types[0]);
				TypePtr source_object_for_cv =
					source->kind == pa11::TypeKind::LValueReference ||
					source->kind == pa11::TypeKind::RValueReference
					? source->base : source;
				bool move =
					source->kind == pa11::TypeKind::RValueReference ||
					(source->kind != pa11::TypeKind::LValueReference &&
					 !pa11::type_has_const(source));
				if (source->kind == pa11::TypeKind::LValueReference ||
				    pa11::type_has_const(source_object_for_cv))
					move = false;
				Binding* ctor =
					trait_declared_copy_move_constructor(target_record, move);
				if (ctor == NULL && move)
					ctor = trait_declared_copy_move_constructor(target_record,
					                                           false);
				if (ctor == NULL && !move &&
				    trait_unqualified_template_primary(target_record) ==
					    "unique_ptr")
					value = false;
				else
					value = ctor == NULL ||
					        deleted_functions_.find(ctor) ==
						        deleted_functions_.end();
				return true;
			}
			if (record_base_distance(source_record, target_record) < 1000000)
			{
				value = true;
				return true;
			}
		}
		Expr probe;
		probe.valid = true;
		probe.type = types[0];
		probe.category = call_category(types[0]);
		probe.node = Node("type-trait-probe " + pa11::describe_type(types[0]));
		try
		{
			value = convert_to(probe, types[1]).viable;
		}
		catch (const runtime_error&)
		{
			value = false;
		}
		return true;
	}
	if (name == "__is_invocable" || name == "__is_nothrow_invocable")
	{
		value = is_invocable_type_trait(types, name == "__is_nothrow_invocable");
		return true;
	}
	if (name == "__is_invocable_r")
	{
		value = is_invocable_r_type_trait(types, false);
		return true;
	}
	return false;
}

bool Parser::evaluate_unary_builtin_type_trait(const string& name,
                                               TypePtr type,
                                               bool& value)
{
	TypePtr bare = pa11::strip_cv(type);
	if (bare->kind == pa11::TypeKind::Record)
		complete_template_record(bare);
	if (name == "__is_trivially_destructible" ||
	    name == "__is_trivially_copyable" ||
	    name == "__has_trivial_constructor" ||
	    name == "__has_trivial_destructor")
		value = !trait_type_has_nontrivial_record_transfer(type);
	else if (name == "__is_destructible" ||
	         name == "__is_literal_type")
		value = true;
	else if (name == "__is_integral")
		value = pa11::is_integral_or_bool_type(type);
	else if (name == "__is_signed")
	{
		TypePtr object = trait_object_type(type);
		if (object->kind == pa11::TypeKind::Enum)
			value = !FundamentalTypeIsUnsigned(object->enum_underlying);
		else if (object->kind == pa11::TypeKind::Fundamental)
		{
			value = object->fundamental == FT_SIGNED_CHAR ||
			        object->fundamental == FT_SHORT_INT ||
			        object->fundamental == FT_INT ||
			        object->fundamental == FT_LONG_INT ||
			        object->fundamental == FT_LONG_LONG_INT ||
			        object->fundamental == FT_INT128 ||
			        object->fundamental == FT_WCHAR_T ||
			        object->fundamental == FT_CHAR ||
			        object->fundamental == FT_FLOAT ||
			        object->fundamental == FT_DOUBLE ||
			        object->fundamental == FT_LONG_DOUBLE;
		}
		else
			value = false;
	}
	else if (name == "__is_floating_point")
	{
		TypePtr object = pa11::strip_cv(type);
		value = object->kind == pa11::TypeKind::Fundamental &&
		        (object->fundamental == FT_FLOAT ||
		         object->fundamental == FT_DOUBLE ||
		         object->fundamental == FT_LONG_DOUBLE);
	}
	else if (name == "__is_scalar")
		value = trait_is_scalar(type);
	else if (name == "__is_enum")
		value = bare->kind == pa11::TypeKind::Enum;
	else if (name == "__is_union")
		value = bare->kind == pa11::TypeKind::Record && bare->tag == "union";
	else if (name == "__is_class")
		value = bare->kind == pa11::TypeKind::Record && bare->tag != "union";
	else if (name == "__is_function")
		value = bare->kind == pa11::TypeKind::Function;
	else if (name == "__is_empty")
		value = trait_record_is_empty(type);
	else if (name == "__is_final")
		value = bare->kind == pa11::TypeKind::Record && bare->is_final_record;
	else if (name == "__is_pod" || name == "__is_trivial")
		value = (bare->kind != pa11::TypeKind::Record ||
		         !trait_record_has_nonpublic_field(type)) &&
		        !trait_type_has_nontrivial_record_transfer(type);
	else if (name == "__is_standard_layout")
		value = bare->kind != pa11::TypeKind::Record ||
		        !trait_record_has_nonpublic_field(type);
	else if (name == "__is_abstract")
		value = trait_record_is_abstract(type);
	else if (name == "__is_polymorphic")
		value = bare->kind == pa11::TypeKind::Record && bare->is_polymorphic;
	else if (name == "__has_virtual_destructor")
		value = trait_record_has_virtual_destructor(type);
	else if (name == "__is_member_pointer")
		value = bare->kind == pa11::TypeKind::MemberPointer;
	else if (name == "__is_member_object_pointer")
		value = bare->kind == pa11::TypeKind::MemberPointer &&
		        bare->base.get() != NULL &&
		        bare->base->kind != pa11::TypeKind::Function;
	else if (name == "__is_member_function_pointer")
		value = bare->kind == pa11::TypeKind::MemberPointer &&
		        bare->base.get() != NULL &&
		        bare->base->kind == pa11::TypeKind::Function;
	else if (name == "__is_complete_or_unbounded")
		value = bare->kind != pa11::TypeKind::Record || bare->complete;
	else if (name == "__reference_constructs_from_temporary" ||
	         name == "__reference_binds_to_temporary")
		value = false;
	else
		return false;
	return true;
}

bool Parser::builtin_type_trait_cache_key(const string& name,
                                          const vector<TypePtr>& types,
                                          size_t& key) const
{
	key = dependent_cache_hash_combine(0xb711, dependent_cache_string_hash(name));
	key = dependent_cache_hash_combine(key, member_function_template_generation_);
	key = dependent_cache_hash_combine(key, types.size());
	for (size_t i = 0; i < types.size(); ++i)
	{
		if (type_structurally_dependent(types[i]))
			return false;
		key = dependent_cache_hash_combine(
			key,
			builtin_trait_type_cache_identity(types[i], 0));
	}
	return true;
}

bool Parser::evaluate_builtin_type_trait(const string& name,
                                         const vector<TypePtr>& types)
{
	size_t cache_key = 0;
	bool use_cache = builtin_type_trait_cache_key(name, types, cache_key);
	if (use_cache)
	{
		map<size_t, bool>::const_iterator cached =
			builtin_type_trait_cache_.find(cache_key);
		if (cached != builtin_type_trait_cache_.end())
			return cached->second;
	}
	bool value = false;
	if (name == "__is_base_of" && types.size() == 2)
	{
		TypePtr source = pa11::strip_cv(types[1]);
		TypePtr target = pa11::strip_cv(types[0]);
		if (source->kind == pa11::TypeKind::Record)
			complete_template_record(source);
		if (target->kind == pa11::TypeKind::Record)
			complete_template_record(target);
		value = trait_record_derives_from(source, target);
		if (use_cache)
			builtin_type_trait_cache_[cache_key] = value;
		return value;
	}
	if (evaluate_builtin_type_relation_trait(name, types, value) ||
	    (!types.empty() &&
	     evaluate_unary_builtin_type_trait(name, types[0], value)))
	{
		if (use_cache)
			builtin_type_trait_cache_[cache_key] = value;
		return value;
	}
	if (use_cache)
		builtin_type_trait_cache_[cache_key] = false;
	return false;
}

Expr Parser::parse_builtin_type_trait_expression()
{
	if (!at_builtin_type_trait_expression())
		throw runtime_error("expected builtin type trait");
	string name = current().source;
	++pos_;
	vector<TypePtr> types;
	bool dependent = false;
	string spelling = name + "(";
	parse_type_trait_operand_list(name, types, dependent, spelling);
	if (dependent)
		return make_dependent_type_trait_expr(spelling);
	return make_bool_trait_expr(evaluate_builtin_type_trait(name, types));
}

bool Parser::constructible_type_trait_cache_key(const vector<TypePtr>& types,
                                                size_t& key) const
{
	if (types.empty())
		return false;
	key = dependent_cache_hash_combine(0x1c0a57, types.size());
	key = dependent_cache_hash_combine(
		key,
		member_function_template_generation_);
	for (size_t i = 0; i < types.size(); ++i)
	{
		if (type_structurally_dependent(types[i]))
			return false;
		key = dependent_cache_hash_combine(
			key,
			builtin_trait_type_cache_identity(types[i], 0));
	}
	return true;
}

Expr Parser::parse_is_constructible_expression()
{
	if (!at_identifier() || current().source != "__is_constructible")
		throw runtime_error("expected __is_constructible");
	++pos_;
	vector<TypePtr> types;
	bool dependent = false;
	string spelling = "__is_constructible(";
	parse_type_trait_operand_list("__is_constructible",
	                              types,
	                              dependent,
	                              spelling);
	if (types.empty())
		return make_bool_trait_expr(false);
	if (dependent)
		return make_dependent_type_trait_expr(spelling);
	return make_bool_trait_expr(is_constructible_type_trait(types));
}

bool Parser::is_constructible_type_trait(const vector<TypePtr>& types)
{
	if (types.empty())
		return false;
	size_t cache_key = 0;
	bool use_cache = constructible_type_trait_cache_key(types, cache_key);
	if (use_cache)
	{
		map<size_t, bool>::const_iterator cached =
			constructible_type_trait_cache_.find(cache_key);
		if (cached != constructible_type_trait_cache_.end())
			return cached->second;
	}
	auto finish = [&](bool value) -> bool
	{
		if (use_cache)
			constructible_type_trait_cache_[cache_key] = value;
		return value;
	};
	TypePtr target = types[0];
	TypePtr bare = pa11::strip_cv(target);
		if (bare->kind == pa11::TypeKind::LValueReference ||
		    bare->kind == pa11::TypeKind::RValueReference)
	{
		if (types.size() != 2)
			return finish(false);
		TypePtr target_object = pa11::strip_cv(bare->base);
		TypePtr source_object = expression_object_type(types[1]);
		source_object = source_object.get() != NULL
			? pa11::strip_cv(source_object) : TypePtr();
		if (target_object.get() != NULL &&
		    source_object.get() != NULL &&
		    target_object->kind == pa11::TypeKind::Function &&
		    pa11::same_type(target_object, source_object))
			return finish(true);
		Expr arg;
		arg.valid = true;
		arg.type = types[1];
		arg.category = call_category(types[1]);
		arg.node = Node("id-expression " + value_category_name(arg.category) +
		                " " + pa11::describe_type(types[1]) +
		                " <constructible-arg>");
		arg.node.type = types[1];
		arg.node.category = arg.category;
		annotate_expr_node(arg);
		try
		{
			return finish(convert_to(arg, target).viable);
		}
		catch (const runtime_error&)
		{
			return finish(false);
		}
	}
	if (bare->kind == pa11::TypeKind::Fundamental &&
	    bare->fundamental == FT_VOID)
		return finish(false);
	if (bare->kind == pa11::TypeKind::Function)
		return finish(false);
	if (types.size() == 1)
	{
		if (bare->kind == pa11::TypeKind::Array)
		{
			vector<TypePtr> elem;
			elem.push_back(bare->base);
			return finish(is_constructible_type_trait(elem));
		}
		if (bare->kind != pa11::TypeKind::Record)
			return finish(true);
		try
		{
			return finish(ensure_default_constructor(target, true) != NULL);
		}
		catch (const runtime_error&)
		{
			return finish(false);
		}
	}
	vector<Expr> args;
	for (size_t i = 1; i < types.size(); ++i)
	{
		Expr arg;
		arg.valid = true;
		arg.type = types[i];
		arg.category = call_category(types[i]);
		arg.node = Node("id-expression " + value_category_name(arg.category) +
		                " " + pa11::describe_type(types[i]) +
		                " <constructible-arg>");
		arg.node.type = types[i];
		arg.node.category = arg.category;
		annotate_expr_node(arg);
		args.push_back(arg);
	}
	if (bare->kind == pa11::TypeKind::Record)
	{
		if (types.size() > 1)
		{
			bool hosted_value = false;
			if (evaluate_hosted_constructible_trait(target,
			                                        types,
			                                        deleted_functions_,
			                                        hosted_value))
				return finish(hosted_value);
		}
		bool entered = false;
		try
		{
			complete_template_record(bare);
			++unevaluated_expression_depth_;
			entered = true;
			make_constructor_init_expr(target, args, false);
			--unevaluated_expression_depth_;
			return finish(true);
		}
		catch (const runtime_error&)
		{
			if (entered)
				--unevaluated_expression_depth_;
			return finish(false);
		}
	}
	if (args.size() != 1)
		return finish(false);
	try
	{
		return finish(convert_to(args[0], target).viable);
	}
	catch (const runtime_error&)
	{
		return finish(false);
	}
}

bool Parser::is_nothrow_constructible_type_trait(const vector<TypePtr>& types)
{
	if (!is_constructible_type_trait(types) || types.empty())
		return false;
	TypePtr target = types[0];
	TypePtr bare = pa11::strip_cv(target);
	if (bare->kind == pa11::TypeKind::Array)
	{
		vector<TypePtr> elem;
		elem.push_back(bare->base);
		return is_nothrow_constructible_type_trait(elem);
	}
	if (bare->kind != pa11::TypeKind::Record)
		return true;
	if (types.size() == 1)
		return default_constructor_is_nothrow(target);
	if (types.size() == 2)
	{
		TypePtr arg = pa11::strip_cv(types[1]);
		bool move = arg->kind == pa11::TypeKind::RValueReference;
		bool copy_ref = arg->kind == pa11::TypeKind::LValueReference ||
		                arg->kind == pa11::TypeKind::RValueReference;
		if (copy_ref && pa11::same_type(pa11::strip_cv(arg->base), bare))
		{
			Binding* ctor = ensure_copy_move_constructor(bare, move);
			if (ctor == NULL && move)
				ctor = ensure_copy_move_constructor(bare, false);
			if (ctor == NULL ||
			    deleted_functions_.find(ctor) != deleted_functions_.end())
				return false;
			return copy_move_constructor_is_nothrow(bare, move);
		}
	}
	if (types.size() > 1)
	{
		bool hosted_value = false;
		if (evaluate_hosted_constructible_trait(target,
		                                        types,
		                                        deleted_functions_,
		                                        hosted_value))
			return hosted_value;
	}
	vector<Expr> args;
	for (size_t i = 1; i < types.size(); ++i)
	{
		Expr arg;
		arg.valid = true;
		arg.type = types[i];
		arg.category = call_category(types[i]);
		arg.node = Node("id-expression " + value_category_name(arg.category) +
		                " " + pa11::describe_type(types[i]) +
		                " <constructible-arg>");
		arg.node.type = types[i];
		arg.node.category = arg.category;
		annotate_expr_node(arg);
		args.push_back(arg);
	}
	try
	{
		++unevaluated_expression_depth_;
		Expr init = make_constructor_init_expr(target, args, false);
		--unevaluated_expression_depth_;
		return node_is_noexcept(init.node);
	}
	catch (const runtime_error&)
	{
		--unevaluated_expression_depth_;
		return false;
	}
}

bool Parser::evaluate_standard_constructible_trait(
	const string& name,
	const vector<TypePtr>& types,
	bool& value)
{
	if (name == "is_constructible" || name == "__is_constructible")
	{
		value = is_constructible_type_trait(types);
		return true;
	}
	if (name == "is_nothrow_constructible" ||
	    name == "__is_nothrow_constructible")
	{
		value = is_nothrow_constructible_type_trait(types);
		return true;
	}
	if ((name == "is_assignable" ||
	     name == "__is_assignable" ||
	     name == "is_nothrow_assignable" ||
	     name == "__is_nothrow_assignable" ||
	     name == "is_trivially_assignable" ||
	     name == "__is_trivially_assignable") &&
	    types.size() == 2)
	{
		return evaluate_assignable_type_trait(name, types, value);
	}
	if ((name == "is_copy_assignable" ||
	     name == "is_nothrow_copy_assignable" ||
	     name == "is_trivially_copy_assignable" ||
	     name == "is_move_assignable" ||
	     name == "is_nothrow_move_assignable" ||
	     name == "is_trivially_move_assignable") &&
	    types.size() == 1)
	{
		TypePtr subject = types[0];
		TypePtr lhs = pa11::make_lvalue_reference(subject);
		TypePtr rhs =
			(name == "is_move_assignable" ||
			 name == "is_nothrow_move_assignable" ||
			 name == "is_trivially_move_assignable")
			? pa11::make_rvalue_reference(subject)
			: pa11::make_lvalue_reference(
				pa11::make_cv(subject, pa11::CV_CONST));
		vector<TypePtr> assignable;
		assignable.push_back(lhs);
		assignable.push_back(rhs);
		return evaluate_assignable_type_trait(name, assignable, value);
	}
	if ((name == "is_copy_constructible" ||
	     name == "is_nothrow_copy_constructible" ||
	     name == "is_trivially_copy_constructible") &&
	    types.size() == 1)
	{
		TypePtr subject = pa11::strip_cv(types[0]);
		if (subject->kind == pa11::TypeKind::Record)
		{
			complete_template_record(subject);
			Binding* declared =
				trait_declared_copy_move_constructor(subject, false);
			if (declared != NULL)
			{
				value = deleted_functions_.find(declared) ==
					deleted_functions_.end();
				if (value && name == "is_nothrow_copy_constructible")
					value = declared->unwind_no;
			}
			else
			{
				value = true;
				pa11::layout_record_type(subject);
				for (size_t i = 0; value && i < subject->fields.size(); ++i)
				{
					vector<TypePtr> field_types(1, subject->fields[i]->type);
					evaluate_standard_constructible_trait(
						name, field_types, value);
				}
			}
			if (value && name == "is_nothrow_copy_constructible")
				value = declared != NULL ? declared->unwind_no : value;
			if (value && name == "is_trivially_copy_constructible")
				value = !trait_record_has_user_copy_constructor(subject) &&
				        !trait_type_has_nontrivial_record_transfer(subject);
			return true;
		}
		TypePtr source = pa11::make_lvalue_reference(
			pa11::make_cv(types[0], pa11::CV_CONST));
		vector<TypePtr> constructible;
		constructible.push_back(types[0]);
		constructible.push_back(source);
		value = name == "is_nothrow_copy_constructible"
			? is_nothrow_constructible_type_trait(constructible)
			: is_constructible_type_trait(constructible);
		if (value && name == "is_trivially_copy_constructible")
		{
			TypePtr target = trait_object_type(types[0]);
			if (target->kind == pa11::TypeKind::Record)
			{
				complete_template_record(target);
				value = !trait_record_has_user_copy_constructor(target) &&
				        !trait_type_has_nontrivial_record_transfer(target);
			}
		}
		return true;
	}
	if ((name == "is_move_constructible" ||
	     name == "is_nothrow_move_constructible" ||
	     name == "is_trivially_move_constructible") &&
	    types.size() == 1)
	{
		TypePtr subject = pa11::strip_cv(types[0]);
		if (subject->kind == pa11::TypeKind::Record)
		{
			complete_template_record(subject);
			Binding* declared =
				trait_declared_copy_move_constructor(subject, true);
			if (declared == NULL)
				declared = trait_declared_copy_move_constructor(subject, false);
			if (declared != NULL)
			{
				value = deleted_functions_.find(declared) ==
					deleted_functions_.end();
				if (value && name == "is_nothrow_move_constructible")
					value = declared->unwind_no;
			}
			else
			{
				value = true;
				pa11::layout_record_type(subject);
				for (size_t i = 0; value && i < subject->fields.size(); ++i)
				{
					vector<TypePtr> field_types(1, subject->fields[i]->type);
					evaluate_standard_constructible_trait(
						name, field_types, value);
				}
			}
			if (value && name == "is_nothrow_move_constructible")
				value = declared != NULL ? declared->unwind_no : value;
			if (value && name == "is_trivially_move_constructible")
				value = !trait_record_has_user_copy_constructor(subject) &&
				        !trait_type_has_nontrivial_record_transfer(subject);
			return true;
		}
		TypePtr source = pa11::make_rvalue_reference(types[0]);
		vector<TypePtr> constructible;
		constructible.push_back(types[0]);
		constructible.push_back(source);
		value = name == "is_nothrow_move_constructible"
			? is_nothrow_constructible_type_trait(constructible)
			: is_constructible_type_trait(constructible);
		if (value && name == "is_trivially_move_constructible")
		{
			TypePtr target = trait_object_type(types[0]);
			if (target->kind == pa11::TypeKind::Record)
			{
				complete_template_record(target);
				value = !trait_record_has_user_copy_constructor(target) &&
				        !trait_type_has_nontrivial_record_transfer(target);
			}
		}
		return true;
	}
	if (name == "is_trivially_constructible" ||
	    name == "__is_trivially_constructible")
	{
		value = is_constructible_type_trait(types);
		if (value && !types.empty())
		{
			TypePtr target = trait_object_type(types[0]);
			if (target->kind == pa11::TypeKind::Record)
			{
				complete_template_record(target);
				if (types.size() == 2)
					value = !trait_record_has_user_copy_constructor(target);
				value = value &&
					!trait_type_has_nontrivial_record_transfer(target);
			}
		}
		return true;
	}
	return false;
}

bool Parser::try_make_invocable_type_trait_call(const vector<TypePtr>& types,
                                                Expr& call)
{
	if (types.empty())
		return false;
	Expr callee;
	callee.valid = true;
	callee.type = types[0];
	callee.category = call_category(types[0]);
	TypePtr callee_object = expression_object_type(types[0]);
	callee_object = callee_object.get() != NULL
		? pa11::strip_cv(callee_object) : TypePtr();
	if (callee_object.get() != NULL &&
	    callee_object->kind == pa11::TypeKind::Function)
		callee.category = ValueCategory::LValue;
	callee.node = Node("id-expression " + value_category_name(callee.category) +
	                   " " + pa11::describe_type(types[0]) +
	                   " <invocable-callee>");
	callee.node.type = types[0];
	callee.node.category = callee.category;
	annotate_expr_node(callee);

	vector<Expr> args;
	for (size_t i = 1; i < types.size(); ++i)
	{
		Expr arg;
		arg.valid = true;
		arg.type = types[i];
		arg.category = call_category(types[i]);
		arg.node = Node("id-expression " + value_category_name(arg.category) +
		                " " + pa11::describe_type(types[i]) +
		                " <invocable-arg>");
		arg.node.type = types[i];
		arg.node.category = arg.category;
		annotate_expr_node(arg);
		args.push_back(arg);
	}

	++unevaluated_expression_depth_;
	try
	{
		call = make_call_expr(callee, args);
		--unevaluated_expression_depth_;
		return true;
	}
	catch (const runtime_error&)
	{
		--unevaluated_expression_depth_;
		return false;
	}
}

bool Parser::is_invocable_type_trait(const vector<TypePtr>& types,
                                     bool require_noexcept)
{
	Expr call;
	if (!try_make_invocable_type_trait_call(types, call))
		return false;
	return !require_noexcept || node_is_noexcept(call.node);
}

bool Parser::is_invocable_r_type_trait(const vector<TypePtr>& types,
                                       bool require_noexcept)
{
	if (types.size() < 2)
		return false;
	vector<TypePtr> call_types(types.begin() + 1, types.end());
	Expr call;
	if (!try_make_invocable_type_trait_call(call_types, call))
		return false;
	TypePtr result = trait_object_type(types[0]);
	if (result->kind == pa11::TypeKind::Fundamental &&
	    result->fundamental == FT_VOID)
		return !require_noexcept || node_is_noexcept(call.node);
	try
	{
		++unevaluated_expression_depth_;
		Conversion conv = convert_to(call, types[0]);
		--unevaluated_expression_depth_;
		if (!conv.viable)
			return false;
		return !require_noexcept || node_is_noexcept(conv.expr.node);
	}
	catch (const runtime_error&)
	{
		--unevaluated_expression_depth_;
		return false;
	}
}

}  // namespace internal
}  // namespace pa12
