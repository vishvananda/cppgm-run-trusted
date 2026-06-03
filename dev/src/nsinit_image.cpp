#include "nsinit_internal.h"

#include <algorithm>
#include <cstring>
#include <map>
#include <sstream>
#include <stdexcept>

using namespace std;

namespace nsinit {
namespace {

string pointer_id(const void* ptr)
{
	ostringstream out;
	out << reinterpret_cast<uintptr_t>(ptr);
	return out.str();
}

void append_namespace_path(Namespace* ns, vector<string>& parts)
{
	if (ns == NULL)
		return;
	append_namespace_path(ns->parent, parts);
	if (ns->named)
		parts.push_back(ns->name);
}

string namespace_path(Namespace* ns)
{
	vector<string> parts;
	append_namespace_path(ns, parts);
	string out;
	for (size_t i = 0; i < parts.size(); ++i)
	{
		if (i != 0)
			out += "::";
		out += parts[i];
	}
	return out;
}

bool variable_has_internal_linkage(Entity* entity)
{
	if (entity->storage == StorageClass::Static ||
	    namespace_has_internal_linkage(entity->owner))
		return true;
	if (entity->kind == EntityKind::Variable &&
	    type_has_const(entity->type) &&
	    !entity->declared_extern)
		return true;
	return false;
}

bool entity_has_internal_linkage(Entity* entity)
{
	if (entity->storage == StorageClass::Static ||
	    namespace_has_internal_linkage(entity->owner))
		return true;
	if (entity->kind == EntityKind::Variable)
		return variable_has_internal_linkage(entity);
	return false;
}

string link_key(Entity* entity)
{
	if (entity_has_internal_linkage(entity))
		return "I|" + pointer_id(entity);
	string key = entity->kind == EntityKind::Function ? "F|" : "V|";
	key += namespace_path(entity->owner);
	key += "|";
	key += entity->name;
	if (entity->kind == EntityKind::Function)
	{
		key += "|";
		key += describe_type(entity->type);
	}
	return key;
}

LinkedEntity* make_linked(Program& program, Entity* entity, const string& key)
{
	unique_ptr<LinkedEntity> linked(new LinkedEntity());
	linked->kind = entity->kind;
	linked->key = key;
	linked->first = entity;
	linked->type = entity->type;
	linked->order = entity->order;
	LinkedEntity* raw = linked.get();
	program.linked_entities.push_back(std::move(linked));
	return raw;
}

bool image_entity_less(LinkedEntity* left, LinkedEntity* right)
{
	return left->order < right->order;
}

bool string_literal_less(StringLiteral* left, StringLiteral* right)
{
	return left->order < right->order;
}

size_t align_up(size_t offset, size_t alignment)
{
	if (alignment == 0)
		return offset;
	const size_t remainder = offset % alignment;
	return remainder == 0 ? offset : offset + alignment - remainder;
}

void append_raw_bytes(vector<unsigned char>& out, const void* data, size_t size)
{
	const unsigned char* begin = static_cast<const unsigned char*>(data);
	out.insert(out.end(), begin, begin + size);
}

bool string_array_compatible(TypePtr dest, StringLiteral* literal)
{
	TypePtr element = strip_cv(dest->base);
	if (element->kind != TypeKind::Fundamental)
		return false;
	if (literal->element_type == FT_CHAR)
		return element->fundamental == FT_CHAR ||
		       element->fundamental == FT_SIGNED_CHAR ||
		       element->fundamental == FT_UNSIGNED_CHAR;
	return element->fundamental == literal->element_type;
}

unsigned top_level_cv(TypePtr type)
{
	return type->kind == TypeKind::Cv ? type->cv : CV_NONE;
}

bool same_unqualified_type(TypePtr left, TypePtr right)
{
	return same_type(strip_cv(left), strip_cv(right));
}

bool cv_qualification_convertible(TypePtr dest, TypePtr source)
{
	return same_unqualified_type(dest, source) &&
	       (top_level_cv(source) & ~top_level_cv(dest)) == 0;
}

TypePtr string_literal_lvalue_type(const ExprValue& value)
{
	TypePtr bare = strip_cv(value.type);
	if (!value.string_literal || bare->kind != TypeKind::Array)
		return value.type;
	return make_array(make_cv(bare->base, CV_CONST),
	                  bare->unknown_bound,
	                  bare->bound);
}

TypePtr effective_lvalue_type(const ExprValue& value)
{
	if (value.string_literal)
		return string_literal_lvalue_type(value);
	return value.type;
}

bool is_arithmetic_fundamental(TypePtr type)
{
	TypePtr bare = strip_cv(type);
	return is_integral_or_bool_type(bare) || is_floating_type(bare);
}

bool is_nullptr_type(TypePtr type)
{
	TypePtr bare = strip_cv(type);
	return bare->kind == TypeKind::Fundamental &&
	       bare->fundamental == FT_NULLPTR_T;
}

bool decode_floating_value(const ExprValue& value, long double& out)
{
	if (!value.known_floating)
		return false;
	out = PA2Decode_long_double(value.floating_source);
	return true;
}

void append_converted_integer(vector<unsigned char>& bytes,
                              TypePtr dest,
                              uint64_t value)
{
	TypePtr bare = strip_cv(dest);
	if (bare->kind == TypeKind::Fundamental &&
	    bare->fundamental == FT_BOOL)
		value = value == 0 ? 0 : 1;
	append_integer_le(bytes, value, type_size(dest));
}

void append_converted_float(vector<unsigned char>& bytes,
                            TypePtr dest,
                            long double value)
{
	TypePtr bare = strip_cv(dest);
	if (bare->fundamental == FT_FLOAT)
	{
		float out = static_cast<float>(value);
		append_raw_bytes(bytes, &out, sizeof(out));
	}
	else if (bare->fundamental == FT_DOUBLE)
	{
		double out = static_cast<double>(value);
		append_raw_bytes(bytes, &out, sizeof(out));
	}
	else
	{
		long double out = value;
		append_raw_bytes(bytes, &out, sizeof(out));
	}
}

bool null_pointer_constant_expr(const shared_ptr<Expr>& expr)
{
	if (!expr.get())
		return false;
	if (expr->kind == ExprKind::Paren)
		return null_pointer_constant_expr(expr->inner);
	if (expr->kind == ExprKind::NullptrLiteral)
		return true;
	if (expr->kind == ExprKind::BoolLiteral)
		return !expr->bool_value;
	if (expr->kind != ExprKind::Literal)
		return false;
	ExprValue value = eval_expression(expr);
	uint64_t integer = 0;
	return expr_value_to_integer_constant(value, integer) && integer == 0;
}

StringLiteral* expr_string_literal(const shared_ptr<Expr>& expr)
{
	if (!expr.get())
		return NULL;
	if (expr->kind == ExprKind::Paren)
		return expr_string_literal(expr->inner);
	if (expr->kind == ExprKind::Literal)
		return expr->string_literal;
	return NULL;
}

InitPlan zero_init(TypePtr type)
{
	InitPlan init;
	init.bytes.resize(type_size(type), 0);
	return init;
}

void resize_to_type(InitPlan& init, TypePtr type)
{
	const size_t size = type_size(type);
	if (init.bytes.size() < size)
		init.bytes.resize(size, 0);
	else if (init.bytes.size() > size)
		init.bytes.resize(size);
}

InitPlan build_object_initializer(Program& program,
                                  TypePtr dest,
                                  const shared_ptr<Expr>& expr);

Temporary* create_temporary(Program& program,
                            TypePtr type,
                            const shared_ptr<Expr>& expr)
{
	unique_ptr<Temporary> temp(new Temporary());
	temp->type = type;
	temp->order = program.temporaries.size();
	temp->init = build_object_initializer(program, type, expr);
	Temporary* raw = temp.get();
	program.temporaries.push_back(std::move(temp));
	return raw;
}

InitPlan build_reference_initializer(Program& program,
                                     TypePtr dest,
                                     const shared_ptr<Expr>& expr)
{
	if (dest->kind == TypeKind::RValueReference)
		throw runtime_error("invalid reference initializer");
	ExprValue value = eval_expression(expr);
	if (!value.valid)
		throw runtime_error("invalid reference initializer");
	InitPlan init;
	init.bytes.resize(8, 0);
	if (value.category == ValueCategory::Lvalue &&
	    (value.address_entity != NULL || value.address_string != NULL))
	{
		if (!cv_qualification_convertible(dest->base,
		                                  effective_lvalue_type(value)))
			throw runtime_error("invalid reference initializer");
		init.address_entity = value.address_entity;
		init.address_string = value.address_string;
		return init;
	}
	if (!type_has_const(dest->base))
		throw runtime_error("invalid reference initializer");
	if (!cv_qualification_convertible(dest->base, value.type))
		throw runtime_error("invalid reference initializer");
	Temporary* temp = create_temporary(program, dest->base, expr);
	init.address_temporary = temp;
	return init;
}

struct PointerSource
{
	TypePtr pointee;
	Entity* entity;
	StringLiteral* literal;
	bool is_function;
	bool constant;

	PointerSource()
		: entity(NULL),
		  literal(NULL),
		  is_function(false),
		  constant(false)
	{
	}
};

bool entity_is_top_level_const(Entity* entity)
{
	return entity != NULL && (top_level_cv(entity->type) & CV_CONST) != 0;
}

bool pointer_source_from_value(const ExprValue& value, PointerSource& source)
{
	if (!value.valid || value.category != ValueCategory::Lvalue)
		return false;
	TypePtr value_type = effective_lvalue_type(value);
	TypePtr bare = strip_cv(value_type);
	if (bare->kind == TypeKind::Array)
	{
		source.pointee = bare->base;
		source.entity = value.address_entity;
		source.literal = value.address_string;
		source.constant = true;
		return source.entity != NULL || source.literal != NULL;
	}
	if (bare->kind == TypeKind::Function)
	{
		source.pointee = bare;
		source.entity = value.address_entity;
		source.is_function = true;
		source.constant = true;
		return source.entity != NULL;
	}
	if (bare->kind == TypeKind::Pointer)
	{
		source.pointee = bare->base;
		source.entity = value.address_entity;
		source.constant = value.address_entity != NULL &&
		                  (value.address_entity->is_constexpr ||
		                   entity_is_top_level_const(value.address_entity));
		return source.entity != NULL;
	}
	return false;
}

bool pointer_pointee_compatible(TypePtr dest_pointee,
                                const PointerSource& source)
{
	TypePtr bare_dest = strip_cv(dest_pointee);
	if (source.is_function)
		return bare_dest->kind == TypeKind::Function &&
		       same_type(bare_dest, source.pointee);
	if (bare_dest->kind == TypeKind::Fundamental &&
	    bare_dest->fundamental == FT_VOID)
		return (top_level_cv(source.pointee) & ~top_level_cv(dest_pointee)) == 0;
	return cv_qualification_convertible(dest_pointee, source.pointee);
}

InitPlan build_pointer_initializer(TypePtr dest, const shared_ptr<Expr>& expr)
{
	ExprValue value = eval_expression(expr);
	InitPlan init;
	init.bytes.resize(8, 0);
	if (!value.valid)
		throw runtime_error("invalid pointer initializer");
	if (null_pointer_constant_expr(expr))
		return init;
	PointerSource source;
	if (!pointer_source_from_value(value, source))
		throw runtime_error("invalid pointer initializer");
	TypePtr bare_dest = strip_cv(dest);
	if (!pointer_pointee_compatible(bare_dest->base, source))
		throw runtime_error("invalid pointer initializer");
	init.address_entity = source.entity;
	init.address_string = source.literal;
	init.constant = source.constant;
	return init;
}

bool fundamental_source_valid(TypePtr dest, const ExprValue& value)
{
	(void)dest;
	return value.valid &&
	       (is_arithmetic_fundamental(value.type) || is_nullptr_type(value.type));
}

InitPlan build_integral_initializer(TypePtr dest, const ExprValue& value)
{
	InitPlan init;
	if (!fundamental_source_valid(dest, value))
		throw runtime_error("invalid integral initializer");
	if (is_nullptr_type(value.type))
	{
		append_converted_integer(init.bytes, dest, 0);
		return init;
	}
	uint64_t integer = 0;
	if (expr_value_to_integer_constant(value, integer))
	{
		append_converted_integer(init.bytes, dest, integer);
		return init;
	}
	long double floating = 0.0;
	if (decode_floating_value(value, floating))
	{
		append_converted_integer(init.bytes,
		                         dest,
		                         static_cast<uint64_t>(floating));
		return init;
	}
	init.bytes.resize(type_size(dest), 0);
	init.constant = false;
	return init;
}

InitPlan build_floating_initializer(TypePtr dest, const ExprValue& value)
{
	InitPlan init;
	if (!fundamental_source_valid(dest, value))
		throw runtime_error("invalid floating initializer");
	if (is_nullptr_type(value.type))
	{
		append_converted_float(init.bytes, dest, 0.0);
		return init;
	}
	uint64_t integer = 0;
	if (expr_value_to_integer_constant(value, integer))
	{
		append_converted_float(init.bytes,
		                       dest,
		                       static_cast<long double>(integer));
		return init;
	}
	long double floating = 0.0;
	if (decode_floating_value(value, floating))
	{
		append_converted_float(init.bytes, dest, floating);
		return init;
	}
	init.bytes.resize(type_size(dest), 0);
	init.constant = false;
	return init;
}

InitPlan build_fundamental_initializer(TypePtr dest,
                                       const shared_ptr<Expr>& expr)
{
	ExprValue value = eval_expression(expr);
	if (is_integral_or_bool_type(dest))
		return build_integral_initializer(dest, value);
	if (is_floating_type(dest))
		return build_floating_initializer(dest, value);
	throw runtime_error("invalid fundamental initializer");
}

InitPlan build_string_array_initializer(TypePtr dest, StringLiteral* literal)
{
	if (!string_array_compatible(dest, literal))
		throw runtime_error("invalid string initializer");
	const size_t dest_size = type_size(dest);
	if (literal->bytes.size() > dest_size)
		throw runtime_error("string initializer too long");
	InitPlan init;
	init.bytes = literal->bytes;
	init.bytes.resize(dest_size, 0);
	return init;
}

InitPlan build_array_initializer(Program&,
                                 TypePtr dest,
                                 const shared_ptr<Expr>& expr)
{
	StringLiteral* literal = expr_string_literal(expr);
	if (literal != NULL)
		return build_string_array_initializer(dest, literal);
	throw runtime_error("invalid array initializer");
}

InitPlan build_object_initializer(Program& program,
                                  TypePtr dest,
                                  const shared_ptr<Expr>& expr)
{
	TypePtr bare = strip_cv(dest);
	if (!expr.get())
		return zero_init(dest);
	if (is_reference_type(dest))
		return build_reference_initializer(program, dest, expr);
	if (bare->kind == TypeKind::Pointer)
		return build_pointer_initializer(dest, expr);
	if (bare->kind == TypeKind::Array)
		return build_array_initializer(program, dest, expr);
	if (bare->kind == TypeKind::Fundamental)
		return build_fundamental_initializer(dest, expr);
	return zero_init(dest);
}

size_t object_size(LinkedEntity* entity)
{
	if (entity->kind == EntityKind::Function)
		return 4;
	return type_size(entity->type);
}

size_t object_align(LinkedEntity* entity)
{
	if (entity->kind == EntityKind::Function)
		return 1;
	return type_align(entity->type);
}

uint64_t address_offset(const InitPlan& init)
{
	if (init.address_entity != NULL)
	{
		if (init.address_entity->linked == NULL)
			throw runtime_error("unlinked address target");
		return static_cast<uint64_t>(init.address_entity->linked->offset);
	}
	if (init.address_string != NULL)
		return static_cast<uint64_t>(init.address_string->offset);
	if (init.address_temporary != NULL)
		return static_cast<uint64_t>(init.address_temporary->offset);
	return 0;
}

void write_init_bytes(vector<char>& image, size_t offset, const InitPlan& init)
{
	for (size_t i = 0; i < init.bytes.size(); ++i)
		image[offset + i] = static_cast<char>(init.bytes[i]);
	if (init.address_entity != NULL ||
	    init.address_string != NULL ||
	    init.address_temporary != NULL)
	{
		const uint64_t target = address_offset(init);
		for (size_t i = 0; i < 8; ++i)
			image[offset + i] =
				static_cast<char>((target >> (i * 8)) & 0xff);
	}
}

void layout_program(Program& program, size_t& final_size)
{
	size_t offset = 4;
	for (size_t i = 0; i < program.image_entities.size(); ++i)
	{
		LinkedEntity* entity = program.image_entities[i];
		offset = align_up(offset, object_align(entity));
		entity->offset = offset;
		offset += object_size(entity);
	}
	for (size_t i = 0; i < program.temporaries.size(); ++i)
	{
		Temporary* temp = program.temporaries[i].get();
		offset = align_up(offset, type_align(temp->type));
		temp->offset = offset;
		offset += type_size(temp->type);
	}
	for (size_t i = 0; i < program.string_literals.size(); ++i)
	{
		StringLiteral* literal = program.string_literals[i];
		offset = align_up(offset, type_align(literal->type));
		literal->offset = offset;
		offset += type_size(literal->type);
	}
	final_size = offset;
}

void write_entity(vector<char>& image, LinkedEntity* entity)
{
	if (entity->kind == EntityKind::Function)
	{
		image[entity->offset + 0] = 'f';
		image[entity->offset + 1] = 'u';
		image[entity->offset + 2] = 'n';
		image[entity->offset + 3] = '\0';
		return;
	}
	write_init_bytes(image, entity->offset, entity->init);
}

}  // namespace

void link_program(Program& program)
{
	map<string, LinkedEntity*> linked_by_key;
	for (size_t t = 0; t < program.translation_units.size(); ++t)
	{
		TranslationUnit& tu = *program.translation_units[t];
		for (size_t i = 0; i < tu.entities.size(); ++i)
		{
			Entity* entity = tu.entities[i].get();
			if (entity->kind != EntityKind::Variable &&
			    entity->kind != EntityKind::Function)
				continue;
			const string key = link_key(entity);
			LinkedEntity*& linked = linked_by_key[key];
			if (linked == NULL)
				linked = make_linked(program, entity, key);
			entity->linked = linked;
			if (entity->kind == EntityKind::Variable)
			{
				if (entity->is_definition)
				{
					if (linked->has_definition)
						throw runtime_error("duplicate variable definition");
					linked->has_definition = true;
					linked->definition = entity;
					linked->type = entity->type;
				}
			}
			else if (entity->is_definition && !entity->is_inline)
			{
				if (linked->non_inline_definition_seen)
					throw runtime_error("duplicate function definition");
				linked->non_inline_definition_seen = true;
				linked->definition = entity;
				linked->has_definition = true;
			}
			else if (entity->is_definition)
			{
				linked->definition = entity;
				linked->has_definition = true;
			}
		}
		for (size_t i = 0; i < tu.string_literals.size(); ++i)
			program.string_literals.push_back(tu.string_literals[i].get());
	}
	for (size_t i = 0; i < program.linked_entities.size(); ++i)
	{
		LinkedEntity* linked = program.linked_entities[i].get();
		if (linked->kind == EntityKind::Function ||
		    (linked->kind == EntityKind::Variable && linked->has_definition))
		{
			linked->emitted = true;
			program.image_entities.push_back(linked);
		}
	}
	sort(program.image_entities.begin(),
	     program.image_entities.end(),
	     image_entity_less);
	sort(program.string_literals.begin(),
	     program.string_literals.end(),
	     string_literal_less);
}

void analyze_program_initializers(Program& program)
{
	for (size_t i = 0; i < program.image_entities.size(); ++i)
	{
		LinkedEntity* linked = program.image_entities[i];
		if (linked->kind != EntityKind::Variable)
			continue;
		Entity* definition = linked->definition;
		if (definition == NULL)
			throw runtime_error("missing variable definition");
		if (!definition->has_initializer &&
		    !can_default_initialize(definition->type))
			throw runtime_error("type cannot be default initialized");
		linked->init = build_object_initializer(
			program,
			definition->type,
			definition->has_initializer
				? definition->initializer.expr
				: shared_ptr<Expr>());
		resize_to_type(linked->init, definition->type);
		if (definition->is_constexpr && !linked->init.constant)
			throw runtime_error("constexpr initializer is not constant");
	}
}

void write_program_image(Program& program, vector<char>& image)
{
	size_t final_size = 0;
	layout_program(program, final_size);
	image.assign(final_size, 0);
	image[0] = 'P';
	image[1] = 'A';
	image[2] = '8';
	image[3] = '\0';
	for (size_t i = 0; i < program.image_entities.size(); ++i)
		write_entity(image, program.image_entities[i]);
	for (size_t i = 0; i < program.temporaries.size(); ++i)
	{
		Temporary* temp = program.temporaries[i].get();
		write_init_bytes(image, temp->offset, temp->init);
	}
	for (size_t i = 0; i < program.string_literals.size(); ++i)
	{
		StringLiteral* literal = program.string_literals[i];
		for (size_t j = 0; j < literal->bytes.size(); ++j)
			image[literal->offset + j] = static_cast<char>(literal->bytes[j]);
	}
}

}  // namespace nsinit
