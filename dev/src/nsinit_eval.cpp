#include "nsinit_internal.h"

#include <cctype>
#include <stdexcept>

using namespace std;

namespace nsinit {
namespace {

ExprValue make_invalid()
{
	return ExprValue();
}

ExprValue make_integer(TypePtr type, uint64_t value)
{
	ExprValue out;
	out.type = type;
	out.valid = true;
	out.known_integer = true;
	out.integer = value;
	return out;
}

ExprValue make_pointer(TypePtr type,
                       Entity* entity,
                       StringLiteral* literal,
                       bool is_null)
{
	ExprValue out;
	out.type = type;
	out.valid = true;
	out.is_null_pointer = is_null;
	out.address_entity = entity;
	out.address_string = literal;
	return out;
}

ExprValue make_lvalue(TypePtr type, Entity* entity, StringLiteral* literal)
{
	ExprValue out;
	out.type = type;
	out.valid = true;
	out.category = ValueCategory::Lvalue;
	out.address_entity = entity;
	out.address_string = literal;
	out.string_literal = literal != NULL;
	return out;
}

bool is_floating_literal_source(const string& source)
{
	for (size_t i = 0; i < source.size(); ++i)
	{
		const char c = source[i];
		if (c == '.' || c == 'e' || c == 'E' || c == 'p' || c == 'P')
			return true;
	}
	return false;
}

EFundamentalType floating_literal_type(const string& source)
{
	if (source.empty())
		return FT_DOUBLE;
	if (source.size() >= 4)
	{
		const string suffix4 = source.substr(source.size() - 4);
		if (suffix4 == "f128" || suffix4 == "F128")
			return FT_LONG_DOUBLE;
		if (suffix4 == "bf16" || suffix4 == "BF16")
			return FT_FLOAT;
	}
	if (source.size() >= 3)
	{
		const string suffix3 = source.substr(source.size() - 3);
		if (suffix3 == "f16" || suffix3 == "F16" ||
		    suffix3 == "f32" || suffix3 == "F32")
			return FT_FLOAT;
		if (suffix3 == "f64" || suffix3 == "F64")
			return FT_DOUBLE;
	}
	const char suffix = source[source.size() - 1];
	if (suffix == 'f' || suffix == 'F')
		return FT_FLOAT;
	if (suffix == 'l' || suffix == 'L' || suffix == 'q' || suffix == 'Q')
		return FT_LONG_DOUBLE;
	return FT_DOUBLE;
}

ExprValue eval_literal(const shared_ptr<Expr>& expr)
{
	if (expr->string_literal != NULL)
		return make_lvalue(expr->string_literal->type, NULL, expr->string_literal);
	IntegerLiteralInfo int_info;
	if (AnalyzeIntegerLiteral(expr->literal_source, int_info) &&
	    !int_info.user_defined)
		return make_integer(make_fundamental(int_info.type), int_info.value);
	CharacterLiteralInfo char_info;
	if (AnalyzeCharacterLiteral(expr->literal_source, false, char_info))
		return make_integer(make_fundamental(char_info.type), char_info.code_point);
	if (is_floating_literal_source(expr->literal_source))
	{
		ExprValue out;
		out.type = make_fundamental(floating_literal_type(expr->literal_source));
		out.valid = true;
		out.known_floating = true;
		out.floating_source = expr->literal_source;
		out.floating_type = strip_cv(out.type)->fundamental;
		return out;
	}
	return make_invalid();
}

Entity* lookup_id_entity(const shared_ptr<Expr>& expr, int mask)
{
	if (expr->name.qualifier != NULL)
		return lookup_qualified(expr->name.qualifier, expr->name.name, mask);
	return lookup_unqualified(expr->lookup_scope, expr->name.name, mask);
}

bool reference_target(Entity* entity, Entity*& target, StringLiteral*& literal)
{
	target = NULL;
	literal = NULL;
	if (entity == NULL || !is_reference_type(entity->type) ||
	    !entity->has_initializer)
		return false;
	ExprValue init = eval_expression(entity->initializer.expr);
	if (init.category == ValueCategory::Lvalue)
	{
		target = init.address_entity;
		literal = init.address_string;
		return target != NULL || literal != NULL;
	}
	return false;
}

ExprValue eval_id(const shared_ptr<Expr>& expr)
{
	Entity* entity = lookup_id_entity(expr, LOOKUP_VALUE);
	if (entity == NULL)
		return make_invalid();
	if (entity->kind == EntityKind::Function)
		return make_lvalue(entity->type, entity, NULL);
	if (entity->kind != EntityKind::Variable)
		return make_invalid();
	if (is_reference_type(entity->type))
	{
		Entity* target = NULL;
		StringLiteral* literal = NULL;
		if (reference_target(entity, target, literal))
			return make_lvalue(entity->type->base, target, literal);
		return make_lvalue(entity->type->base, entity, NULL);
	}
	return make_lvalue(entity->type, entity, NULL);
}

bool entity_can_be_integral_constant(Entity* entity)
{
	if (entity == NULL || entity->kind != EntityKind::Variable)
		return false;
	if (!is_integral_or_bool_type(entity->type))
		return false;
	return entity->is_constexpr || type_has_const(entity->type);
}

bool convert_integer_to_bool(uint64_t value)
{
	return value != 0;
}

}  // namespace

ExprValue eval_expression(const shared_ptr<Expr>& expr)
{
	if (!expr.get())
		return make_invalid();
	switch (expr->kind)
	{
	case ExprKind::BoolLiteral:
		return make_integer(make_fundamental(FT_BOOL), expr->bool_value ? 1 : 0);
	case ExprKind::NullptrLiteral:
		return make_pointer(make_fundamental(FT_NULLPTR_T), NULL, NULL, true);
	case ExprKind::Literal:
		return eval_literal(expr);
	case ExprKind::Id:
		return eval_id(expr);
	case ExprKind::Paren:
		return eval_expression(expr->inner);
	}
	return make_invalid();
}

bool eval_array_bound(const shared_ptr<Expr>& expr, uint64_t& bound)
{
	ExprValue value = eval_expression(expr);
	if (!expr_value_to_integer_constant(value, bound))
		return false;
	return bound != 0;
}

bool eval_static_assert_condition(const shared_ptr<Expr>& expr)
{
	ExprValue value = eval_expression(expr);
	uint64_t integer = 0;
	if (expr_value_to_integer_constant(value, integer))
		return convert_integer_to_bool(integer);
	Entity* entity = NULL;
	StringLiteral* literal = NULL;
	bool is_null = false;
	if (expr_value_to_pointer_target(value, entity, literal, is_null))
		return !is_null;
	if (value.category == ValueCategory::Lvalue &&
	    value.address_entity != NULL)
	{
		if (eval_entity_pointer_constant(value.address_entity,
		                                 entity,
		                                 literal,
		                                 is_null))
			return !is_null;
	}
	return false;
}

bool eval_entity_integer_constant(Entity* entity, uint64_t& value)
{
	if (entity == NULL || entity->kind != EntityKind::Variable)
		return false;
	if (entity->constant_ready)
	{
		value = entity->constant_integer;
		return entity->constant_valid;
	}
	if (entity->evaluating_constant)
		return false;
	entity->evaluating_constant = true;
	entity->constant_ready = true;
	entity->constant_valid = false;
	if (is_reference_type(entity->type))
	{
		Entity* target = NULL;
		StringLiteral* literal = NULL;
		if (reference_target(entity, target, literal) &&
		    target != NULL &&
		    eval_entity_integer_constant(target, value))
			entity->constant_valid = true;
	}
	else if (entity_can_be_integral_constant(entity) &&
	         entity->has_initializer)
	{
		ExprValue init = eval_expression(entity->initializer.expr);
		if (expr_value_to_integer_constant(init, value))
			entity->constant_valid = true;
	}
	entity->constant_integer = value;
	entity->evaluating_constant = false;
	return entity->constant_valid;
}

bool eval_entity_pointer_constant(Entity* entity,
                                  Entity*& address_entity,
                                  StringLiteral*& address_string,
                                  bool& is_null)
{
	address_entity = NULL;
	address_string = NULL;
	is_null = false;
	if (entity == NULL || entity->kind != EntityKind::Variable)
		return false;
	if (entity->constant_pointer_ready)
	{
		address_entity = entity->constant_pointer_entity;
		address_string = entity->constant_pointer_string;
		is_null = entity->constant_pointer_valid &&
		          address_entity == NULL &&
		          address_string == NULL;
		return entity->constant_pointer_valid;
	}
	entity->constant_pointer_ready = true;
	entity->constant_pointer_valid = false;
	if (!entity->is_constexpr || !entity->has_initializer)
		return false;
	ExprValue init = eval_expression(entity->initializer.expr);
	if (!expr_value_to_pointer_target(init, address_entity, address_string, is_null))
		return false;
	entity->constant_pointer_valid = true;
	entity->constant_pointer_entity = address_entity;
	entity->constant_pointer_string = address_string;
	return true;
}

bool expr_value_to_integer_constant(const ExprValue& value, uint64_t& out)
{
	if (!value.valid)
		return false;
	if (value.known_integer)
	{
		out = value.integer;
		return true;
	}
	if (value.category == ValueCategory::Lvalue &&
	    value.address_entity != NULL)
		return eval_entity_integer_constant(value.address_entity, out);
	return false;
}

bool expr_value_to_pointer_target(const ExprValue& value,
                                  Entity*& entity,
                                  StringLiteral*& literal,
                                  bool& is_null)
{
	entity = NULL;
	literal = NULL;
	is_null = false;
	if (!value.valid)
		return false;
	if (value.is_null_pointer)
	{
		is_null = true;
		return true;
	}
	TypePtr bare = strip_cv(value.type);
	if (value.category == ValueCategory::Lvalue &&
	    bare->kind == TypeKind::Array)
	{
		entity = value.address_entity;
		literal = value.address_string;
		return entity != NULL || literal != NULL;
	}
	if (value.category == ValueCategory::Lvalue &&
	    bare->kind == TypeKind::Function)
	{
		entity = value.address_entity;
		return entity != NULL;
	}
	if (value.category == ValueCategory::Prvalue &&
	    (value.address_entity != NULL || value.address_string != NULL))
	{
		entity = value.address_entity;
		literal = value.address_string;
		return true;
	}
	return false;
}

}  // namespace nsinit
