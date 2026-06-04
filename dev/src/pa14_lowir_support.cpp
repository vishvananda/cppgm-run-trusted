#include "pa14_lowir_internal.h"

#include <cctype>

namespace pa14 {
namespace internal {

bool starts_with(const string& text, const string& prefix)
{
	return text.size() >= prefix.size() &&
	       text.compare(0, prefix.size(), prefix) == 0;
}

TypePtr object_type(TypePtr type)
{
	if (type->kind == TypeKind::LValueReference ||
	    type->kind == TypeKind::RValueReference)
		return type->base;
	return type;
}

TypePtr strip_for_value(TypePtr type)
{
	TypePtr object = object_type(type);
	if (object->kind == TypeKind::Array)
		return pa11::make_pointer(object->base);
	if (object->kind == TypeKind::Function)
		return pa11::make_pointer(object);
	return pa11::strip_top_level_cv(object);
}

bool is_reference(TypePtr type)
{
	return type->kind == TypeKind::LValueReference ||
	       type->kind == TypeKind::RValueReference;
}

bool is_float_type(TypePtr type)
{
	TypePtr bare = pa11::strip_cv(strip_for_value(type));
	return bare->kind == TypeKind::Fundamental &&
	       (bare->fundamental == FT_FLOAT ||
	        bare->fundamental == FT_DOUBLE ||
	        bare->fundamental == FT_LONG_DOUBLE);
}

bool is_unsigned_type(TypePtr type)
{
	TypePtr bare = pa11::strip_cv(strip_for_value(type));
	if (bare->kind == TypeKind::Enum)
	{
		switch (bare->enum_underlying)
		{
		case FT_UNSIGNED_CHAR:
		case FT_UNSIGNED_SHORT_INT:
		case FT_UNSIGNED_INT:
		case FT_UNSIGNED_LONG_INT:
		case FT_UNSIGNED_LONG_LONG_INT:
			return true;
		default:
			return false;
		}
	}
	if (bare->kind != TypeKind::Fundamental)
		return false;
	switch (bare->fundamental)
	{
	case FT_UNSIGNED_CHAR:
	case FT_UNSIGNED_SHORT_INT:
	case FT_UNSIGNED_INT:
	case FT_UNSIGNED_LONG_INT:
	case FT_UNSIGNED_LONG_LONG_INT:
	case FT_CHAR16_T:
	case FT_CHAR32_T:
	case FT_BOOL:
		return true;
	default:
		return false;
	}
}

string scalar_lowir_type(TypePtr type)
{
	TypePtr bare = pa11::strip_cv(object_type(type));
	if (is_reference(type))
		return "ptr";
	if (bare->kind == TypeKind::Pointer ||
	    bare->kind == TypeKind::Function ||
	    bare->kind == TypeKind::Array)
		return "ptr";
	if (bare->kind == TypeKind::Record)
	{
		ostringstream out;
		out << "obj<" << pa11::type_size(bare) << "x" << pa11::type_align(bare)
		    << ">";
		return out.str();
	}
	if (bare->kind == TypeKind::Enum)
	{
		switch (pa11::type_size(bare))
		{
		case 1: return "i8";
		case 2: return "i16";
		case 4: return "i32";
		default: return "i64";
		}
	}
	if (bare->kind != TypeKind::Fundamental)
		throw runtime_error("unsupported PA14 type");
	switch (bare->fundamental)
	{
	case FT_BOOL: return "u8";
	case FT_CHAR: case FT_SIGNED_CHAR: return "i8";
	case FT_UNSIGNED_CHAR: return "u8";
	case FT_SHORT_INT: return "i16";
	case FT_UNSIGNED_SHORT_INT: return "u16";
	case FT_INT: return "i32";
	case FT_UNSIGNED_INT: return "u32";
	case FT_LONG_INT:
	case FT_LONG_LONG_INT:
	case FT_UNSIGNED_LONG_INT:
	case FT_UNSIGNED_LONG_LONG_INT:
		return "i64";
	case FT_FLOAT: return "f32";
	case FT_DOUBLE: return "f64";
	case FT_LONG_DOUBLE: return "f80";
	case FT_VOID: return "void";
	case FT_NULLPTR_T: return "i64";
	case FT_WCHAR_T: return "i32";
	case FT_CHAR16_T: return "u16";
	case FT_CHAR32_T: return "u32";
	}
	throw runtime_error("unknown fundamental type");
}

int lowir_arithmetic_rank(TypePtr type)
{
	TypePtr bare = pa11::strip_cv(strip_for_value(type));
	if (bare->kind == TypeKind::Enum)
		return 3;
	if (bare->kind != TypeKind::Fundamental)
		return 0;
	switch (bare->fundamental)
	{
	case FT_BOOL:
	case FT_CHAR: case FT_SIGNED_CHAR: case FT_UNSIGNED_CHAR: return 1;
	case FT_SHORT_INT: case FT_UNSIGNED_SHORT_INT: return 2;
	case FT_CHAR16_T: return 2;
	case FT_WCHAR_T:
	case FT_CHAR32_T:
	case FT_INT: case FT_UNSIGNED_INT: return 3;
	case FT_LONG_INT: case FT_UNSIGNED_LONG_INT:
	case FT_LONG_LONG_INT: case FT_UNSIGNED_LONG_LONG_INT: return 4;
	case FT_FLOAT: return 5;
	case FT_DOUBLE: return 6;
	case FT_LONG_DOUBLE: return 7;
	default: return 0;
	}
}

TypePtr lowir_integral_promotion(TypePtr type)
{
	TypePtr bare = pa11::strip_cv(strip_for_value(type));
	if (bare->kind == TypeKind::Enum ||
	    (pa11::is_integral_or_bool_type(type) &&
	     lowir_arithmetic_rank(type) < 3))
		return pa11::make_fundamental(FT_INT);
	return strip_for_value(type);
}

TypePtr lowir_common_type(TypePtr left, TypePtr right)
{
	TypePtr l = lowir_integral_promotion(left);
	TypePtr r = lowir_integral_promotion(right);
	if (pa11::strip_cv(l)->kind == TypeKind::Pointer)
		return l;
	if (pa11::strip_cv(r)->kind == TypeKind::Pointer)
		return r;
	if (pa11::same_type(l, r))
		return l;
	if (is_float_type(l))
		return is_float_type(r) && lowir_arithmetic_rank(r) >
			lowir_arithmetic_rank(l) ? r : l;
	if (is_float_type(r))
		return r;
	return lowir_arithmetic_rank(r) > lowir_arithmetic_rank(l) ? r : l;
}

string slot_lowir_type(TypePtr type)
{
	TypePtr bare = pa11::strip_cv(type);
	if (is_reference(type))
		return "ptr";
	if (bare->kind == TypeKind::Array)
	{
		ostringstream out;
		out << "obj<" << pa11::type_size(bare) << "x" << pa11::type_align(bare)
		    << ">";
		return out.str();
	}
	if (bare->kind == TypeKind::Record)
	{
		ostringstream out;
		out << "obj<" << pa11::type_size(bare) << "x" << pa11::type_align(bare)
		    << ">";
		return out.str();
	}
	return scalar_lowir_type(type);
}

namespace {

bool is_copy_or_move_constructor(const Binding* binding, TypePtr record)
{
	if (binding == NULL ||
	    binding->kind != BindingKind::Function ||
	    binding->type->kind != TypeKind::Function ||
	    binding->type->parameters.size() < 2)
		return false;
	TypePtr param = binding->type->parameters[1];
	if (!is_reference(param))
		return false;
	return pa11::same_type(pa11::strip_cv(param->base), pa11::strip_cv(record));
}

bool is_move_constructor(const Binding* binding, TypePtr record)
{
	if (!is_copy_or_move_constructor(binding, record))
		return false;
	return binding->type->parameters[1]->kind == TypeKind::RValueReference;
}

bool type_has_user_copy_move_or_destructor(TypePtr type);
bool type_has_abi_indirect_special_member(TypePtr type);

bool defaulted_member_affects_call_abi(const Binding* binding)
{
	if (binding->owner == NULL || binding->owner->kind != ScopeKind::Class)
		return binding->is_inline_definition;
	TypePtr record = pa11::record_type_for_scope(binding->owner);
	if (record.get() == NULL)
		return binding->is_inline_definition;
	TypePtr bare = pa11::strip_cv(record);
	if (bare->tag == "union")
		return true;
	pa11::layout_record_type(bare);
	if (bare->base.get() != NULL &&
	    type_has_abi_indirect_special_member(bare->base))
		return true;
	for (size_t i = 0; i < bare->fields.size(); ++i)
		if (type_has_abi_indirect_special_member(bare->fields[i]->type))
			return true;
	return false;
}

bool special_member_affects_call_abi(const Binding* binding)
{
	if (binding->is_generated_copy_move_constructor ||
	    binding->is_generated_default_destructor)
		return false;
	if (!binding->is_defaulted)
		return true;
	return defaulted_member_affects_call_abi(binding);
}

bool record_has_user_copy_move_or_destructor(TypePtr type)
{
	TypePtr bare = pa11::strip_cv(type);
	if (bare->kind != TypeKind::Record || bare->scope == NULL)
		return false;
	if (bare->tag == "union")
		return true;
	map<string, vector<Binding*> >::const_iterator ctors =
		bare->scope->members.find(bare->scope->name);
	if (ctors != bare->scope->members.end())
	{
		for (size_t i = 0; i < ctors->second.size(); ++i)
		{
			Binding* ctor = ctors->second[i];
			if (is_copy_or_move_constructor(ctor, bare) &&
			    special_member_affects_call_abi(ctor))
				return true;
		}
	}
	string dtor_name = "~" + bare->scope->name;
	map<string, vector<Binding*> >::const_iterator dtors =
		bare->scope->members.find(dtor_name);
	if (dtors != bare->scope->members.end())
	{
		for (size_t i = 0; i < dtors->second.size(); ++i)
			if (dtors->second[i]->kind == BindingKind::Function &&
			    special_member_affects_call_abi(dtors->second[i]))
				return true;
	}
	if (bare->base.get() != NULL &&
	    type_has_user_copy_move_or_destructor(bare->base))
		return true;
	pa11::layout_record_type(bare);
	for (size_t i = 0; i < bare->fields.size(); ++i)
		if (type_has_user_copy_move_or_destructor(bare->fields[i]->type))
			return true;
	return false;
}

bool type_has_user_copy_move_or_destructor(TypePtr type)
{
	TypePtr bare = pa11::strip_cv(type);
	if (bare->kind == TypeKind::Array)
		return type_has_user_copy_move_or_destructor(bare->base);
	if (bare->kind == TypeKind::Record)
		return record_has_user_copy_move_or_destructor(bare);
	return false;
}

bool record_has_abi_indirect_special_member(TypePtr type)
{
	TypePtr bare = pa11::strip_cv(type);
	if (bare->kind != TypeKind::Record || bare->scope == NULL)
		return false;
	if (bare->tag == "union")
		return true;
	map<string, vector<Binding*> >::const_iterator ctors =
		bare->scope->members.find(bare->scope->name);
	if (ctors != bare->scope->members.end())
	{
		for (size_t i = 0; i < ctors->second.size(); ++i)
		{
			Binding* ctor = ctors->second[i];
			if (is_move_constructor(ctor, bare) &&
			    special_member_affects_call_abi(ctor))
				return true;
		}
	}
	string dtor_name = "~" + bare->scope->name;
	map<string, vector<Binding*> >::const_iterator dtors =
		bare->scope->members.find(dtor_name);
	if (dtors != bare->scope->members.end())
	{
		for (size_t i = 0; i < dtors->second.size(); ++i)
			if (dtors->second[i]->kind == BindingKind::Function &&
			    special_member_affects_call_abi(dtors->second[i]))
				return true;
	}
	if (bare->base.get() != NULL &&
	    type_has_abi_indirect_special_member(bare->base))
		return true;
	pa11::layout_record_type(bare);
	for (size_t i = 0; i < bare->fields.size(); ++i)
		if (type_has_abi_indirect_special_member(bare->fields[i]->type))
			return true;
	return false;
}

bool type_has_abi_indirect_special_member(TypePtr type)
{
	TypePtr bare = pa11::strip_cv(type);
	if (bare->kind == TypeKind::Array)
		return type_has_abi_indirect_special_member(bare->base);
	if (bare->kind == TypeKind::Record)
		return record_has_abi_indirect_special_member(bare);
	return false;
}

}  // namespace

bool record_pass_by_address(TypePtr type)
{
	TypePtr bare = pa11::strip_cv(type);
	if (bare->kind != TypeKind::Record)
		return false;
	if (pa11::type_size(bare) > 16)
		return true;
	return record_has_abi_indirect_special_member(bare);
}

bool record_return_by_address(TypePtr type)
{
	TypePtr bare = pa11::strip_cv(type);
	if (bare->kind != TypeKind::Record)
		return false;
	if (pa11::type_size(bare) > 16)
		return true;
	return record_has_user_copy_move_or_destructor(bare);
}

bool record_has_nontrivial_value_transfer(TypePtr type)
{
	return record_has_user_copy_move_or_destructor(type);
}

bool record_has_storage_copy(TypePtr type)
{
	TypePtr bare = pa11::strip_cv(type);
	if (bare->kind == TypeKind::Array)
		return record_has_storage_copy(bare->base);
	if (bare->kind != TypeKind::Record)
		return true;
	pa11::layout_record_type(bare);
	if (bare->base.get() != NULL &&
	    record_has_storage_copy(bare->base))
		return true;
	return !bare->fields.empty();
}

string lowir_literal(TypePtr type, const Node& node)
{
	if (node.token_text == "nullptr")
		return "nullptr";
	if (node.has_constant_value && !is_float_type(type))
		return to_string(node.constant_value);
	if (!node.token_text.empty())
		return node.token_text;
	return to_string(node.constant_value);
}

string lowir_parameter(TypePtr type)
{
	string out = scalar_lowir_type(type);
	if (is_reference(type))
		out += " [pass=reference]";
	else if (pa11::strip_cv(type)->kind == TypeKind::Record &&
	         record_pass_by_address(type))
		out = "ptr [pass=by_address]";
	return out;
}

string metadata_suffix(const vector<string>& items)
{
	if (items.empty())
		return "";
	ostringstream out;
	out << " [";
	for (size_t i = 0; i < items.size(); ++i)
	{
		if (i != 0)
			out << ", ";
		out << items[i];
	}
	out << "]";
	return out.str();
}

string sanitized_symbol_part(const string& part)
{
	ostringstream out;
	for (size_t i = 0; i < part.size(); ++i)
	{
		const unsigned char ch = static_cast<unsigned char>(part[i]);
		if (isalnum(ch) || ch == '_')
			out << part[i];
		else if (ch == '+')
			out << "_plus";
		else if (ch == '-')
			out << "_minus";
		else if (ch == '*')
			out << "_star";
		else if (ch == '/')
			out << "_slash";
		else if (ch == '%')
			out << "_percent";
		else if (ch == '&')
			out << "_amp";
		else if (ch == '|')
			out << "_bar";
		else if (ch == '^')
			out << "_caret";
		else if (ch == '~')
			out << "_tilde";
		else if (ch == '!')
			out << "_bang";
		else if (ch == '=')
			out << "_eq";
		else if (ch == '<')
			out << "_lt";
		else if (ch == '>')
			out << "_gt";
		else if (ch == '[')
			out << "_lb";
		else if (ch == ']')
			out << "_rb";
		else if (ch == '(')
			out << "_lp";
		else if (ch == ')')
			out << "_rp";
		else if (ch == ',')
			out << "_comma";
		else
			out << "_x" << static_cast<unsigned>(ch) << "_";
	}
	string text = out.str();
	if (text.empty())
		return "_";
	if (isdigit(static_cast<unsigned char>(text[0])))
		text = "_" + text;
	return text;
}

string template_record_symbol_part(TypePtr record);

vector<string> qualified_parts(const Binding* binding)
{
	vector<string> parts;
	for (Scope* s = binding->owner; s != NULL; s = s->parent)
	{
		if ((s->kind == ScopeKind::Namespace || s->kind == ScopeKind::Class) &&
		    !s->name.empty())
		{
			string part = s->name == "<unnamed>" ? "_GLOBAL__N_1" : s->name;
			if (s->kind == ScopeKind::Class)
			{
				TypePtr record = pa11::record_type_for_scope(s);
				if (record_is_template_specialization(record))
						part = template_record_symbol_part(record);
				}
				parts.push_back(part);
			}
	}
	vector<string> out;
	for (size_t i = parts.size(); i > 0; --i)
		out.push_back(parts[i - 1]);
	if (binding->owner != NULL &&
	    binding->owner->kind == ScopeKind::Class &&
	    !binding->name.empty() &&
	    binding->name[0] == '~')
		out.push_back("_" + binding->name.substr(1));
	else if (binding->name == "operator=")
		out.push_back("operator_");
	else
		out.push_back(binding->name);
	return out;
}

string source_symbol_base(const Binding* binding)
{
	if (binding != NULL && binding->is_local_static)
	{
		vector<string> parts;
		for (Scope* s = binding->owner; s != NULL; s = s->parent)
		{
			if ((s->kind == ScopeKind::Namespace ||
			     s->kind == ScopeKind::Class ||
			     s->kind == ScopeKind::Function) &&
			    !s->name.empty())
				parts.push_back(s->name);
		}
		ostringstream out;
		out << "__local_static";
		for (size_t i = parts.size(); i > 0; --i)
			out << "__" << sanitized_symbol_part(parts[i - 1]);
		out << "__" << sanitized_symbol_part(binding->name);
		if (!binding->local_static_discriminator.empty())
			out << "__" << sanitized_symbol_part(
				binding->local_static_discriminator);
		return out.str();
	}
	if (binding->owner != NULL &&
	    binding->owner->parent == NULL &&
	    binding->kind == BindingKind::Function)
	{
		if (binding->name == "operatornew")
			return "operator_new";
		if (binding->name == "operatordelete")
			return "operator_delete";
		if (binding->name == "operatornew[]")
			return "operator_new__";
		if (binding->name == "operatordelete[]")
			return "operator_delete__";
	}
	vector<string> parts = qualified_parts(binding);
	ostringstream out;
	for (size_t i = 0; i < parts.size(); ++i)
	{
		if (i != 0)
			out << "__";
		out << sanitized_symbol_part(parts[i]);
	}
	return out.str();
}

bool is_class_constructor_binding(const Binding* binding)
{
	return binding != NULL &&
	       binding->owner != NULL &&
	       binding->owner->kind == ScopeKind::Class &&
	       binding->name == binding->owner->name;
}

bool is_class_destructor_binding(const Binding* binding)
{
	return binding != NULL &&
	       binding->owner != NULL &&
	       binding->owner->kind == ScopeKind::Class &&
	       !binding->name.empty() &&
	       binding->name[0] == '~';
}

TypePtr class_record_for_member(const Binding* binding)
{
	if (binding == NULL || binding->owner == NULL ||
	    binding->owner->kind != ScopeKind::Class)
		return TypePtr();
	return pa11::record_type_for_scope(binding->owner);
}

bool record_is_template_specialization(TypePtr record)
{
	record = record.get() != NULL ? pa11::strip_cv(record) : TypePtr();
	return record.get() != NULL &&
	       record->kind == TypeKind::Record &&
	       record->is_template_specialization;
}

bool binding_has_template_specialization_context(const Binding* binding)
{
	if (binding == NULL)
		return false;
	for (Scope* scope = binding->owner; scope != NULL; scope = scope->parent)
		if (scope->kind == ScopeKind::Class &&
		    record_is_template_specialization(pa11::record_type_for_scope(scope)))
			return true;
	return false;
}

string template_display_symbol_text(string text)
{
	for (size_t i = 0; i < text.size(); ++i)
		if (text[i] == '<' || text[i] == '>' || text[i] == ',' ||
		    text[i] == ' ' || text[i] == '&' || text[i] == '*' ||
		    text[i] == ':')
			text[i] = '_';
	return sanitized_symbol_part(text);
}

string template_value_symbol_text(uint64_t value)
{
	return to_string(value);
}

string template_type_symbol_text(TypePtr type)
{
	TypePtr bare = type.get() != NULL ? pa11::strip_cv(type) : TypePtr();
	if (bare.get() != NULL &&
	    bare->kind == TypeKind::Record &&
	    record_is_template_specialization(bare))
		return record_lowir_name(bare);
	if (bare.get() != NULL &&
	    (bare->kind == TypeKind::Record || bare->kind == TypeKind::Enum))
		return template_display_symbol_text(bare->name);
	return template_display_symbol_text(pa11::describe_type(type));
}

string template_argument_symbol_part(
	const pa11::TemplateInstanceArgument& arg)
{
	if (arg.kind == pa11::TemplateInstanceArgumentKind::Type)
		return template_type_symbol_text(arg.type);
	if (arg.kind == pa11::TemplateInstanceArgumentKind::Value)
	{
		TypePtr bare = arg.type.get() != NULL
			? pa11::strip_cv(arg.type) : TypePtr();
		if (arg.dependent)
			return "_dependent_value";
		if (bare.get() != NULL &&
		    bare->kind == TypeKind::Fundamental &&
		    bare->fundamental == FT_BOOL)
			return arg.value != 0 ? "true" : "false";
		if (bare.get() != NULL && bare->kind == TypeKind::Enum)
			return "__" + template_type_symbol_text(bare) + "_" +
		       template_value_symbol_text(arg.value);
		return "_" + template_value_symbol_text(arg.value);
	}
	if (arg.kind == pa11::TemplateInstanceArgumentKind::Template)
		return "tmpl_" + template_display_symbol_text(arg.template_name);
	string out;
	for (size_t i = 0; i < arg.pack.size(); ++i)
	{
		if (i != 0)
			out += "_";
		out += template_argument_symbol_part(arg.pack[i]);
	}
	return out.empty() ? "_" : out;
}

string template_record_symbol_part(TypePtr record)
{
	TypePtr bare = pa11::strip_cv(record);
	string primary = !bare->template_primary_name.empty()
		? bare->template_primary_name
		: (bare->scope != NULL ? bare->scope->name : bare->name);
	string out = template_display_symbol_text(primary);
	if (!record_is_template_specialization(bare))
		return out;
	out += "_";
	for (size_t i = 0; i < bare->template_arguments.size(); ++i)
	{
		if (i != 0)
			out += "_";
		out += template_argument_symbol_part(bare->template_arguments[i]);
	}
	out += "_";
	return out;
}

string record_lowir_name(TypePtr record)
{
	TypePtr bare = pa11::strip_cv(record);
	vector<string> parts;
	for (Scope* s = bare->scope; s != NULL; s = s->parent)
	{
		if ((s->kind == ScopeKind::Namespace || s->kind == ScopeKind::Class) &&
		    !s->name.empty())
		{
			string part = s->name == "<unnamed>" ? "_GLOBAL__N_1" :
			              s->name;
			if (s->kind == ScopeKind::Class)
			{
					TypePtr scope_record = pa11::record_type_for_scope(s);
					if (record_is_template_specialization(scope_record))
						part = template_record_symbol_part(scope_record);
				}
				parts.push_back(part);
			}
	}
	if (parts.empty())
		parts.push_back(bare->name);
	ostringstream out;
	for (size_t i = parts.size(); i > 0; --i)
	{
		if (i != parts.size())
			out << "__";
		out << sanitized_symbol_part(parts[i - 1]);
	}
	return out.str();
}

string vtable_symbol_for_record(TypePtr record)
{
	return record_lowir_name(record) + "__vtable";
}

string rtti_symbol_for_record(TypePtr record)
{
	TypePtr bare = pa11::strip_cv(record);
	return "__rtti_" + bare->tag + "_" + record_lowir_name(bare);
}

string ProgramLowerer::symbol_for(const Binding* binding)
{
	map<const Binding*, string>::const_iterator found = symbols.find(binding);
	if (found != symbols.end())
		return found->second;
	string base = source_symbol_base(binding);
	if (binding->kind == BindingKind::Function)
	{
		string key = base + " " +
		             string(binding->is_static_member ? "static " : "nonstatic ") +
		             "refqual=" + to_string(binding->ref_qualifier) + " " +
		             pa11::describe_type(binding->type);
		map<string, string>::const_iterator fit = function_symbols.find(key);
		if (fit != function_symbols.end())
		{
			symbols[binding] = fit->second;
			return fit->second;
		}
	}
	int& count = used_symbols[base];
	++count;
	string name = base;
	if (count > 1)
		name += "__ov" + to_string(count);
	symbols[binding] = name;
	if (binding->kind == BindingKind::Function)
	{
		string key = base + " " +
		             string(binding->is_static_member ? "static " : "nonstatic ") +
		             "refqual=" + to_string(binding->ref_qualifier) + " " +
		             pa11::describe_type(binding->type);
		function_symbols[key] = name;
	}
	return name;
}

string ProgramLowerer::constructor_symbol_for(const Binding* binding,
                                              bool base_entry)
{
	string name = symbol_for(binding);
	if (base_entry &&
	    binding != NULL &&
	    binding->owner != NULL &&
	    binding->owner->kind == ScopeKind::Class &&
	    binding->name == binding->owner->name)
	{
		demanded_constructor_base_entries.insert(binding);
		name += "__base_entry";
	}
	return name;
}

string ProgramLowerer::destructor_symbol_for(const Binding* binding,
                                             bool base_entry)
{
	string name = symbol_for(binding);
	if (base_entry &&
	    is_class_destructor_binding(binding))
	{
		demanded_destructor_base_entries.insert(binding);
		name += "__base_entry";
	}
	return name;
}

vector<uint32_t> decode_simple_string(const string& text)
{
	size_t first = text.find('"');
	size_t last = text.rfind('"');
	if (first == string::npos || last == first)
		throw runtime_error("invalid string literal");
	vector<uint32_t> code_points;
	if (!DecodeOrdinaryBody(text, first + 1, last, code_points))
		throw runtime_error("invalid string literal");
	code_points.push_back(0);
	return code_points;
}

string string_literal_lowir_type(const string& text)
{
	if (!text.empty() && text[0] == 'L')
		return "i32";
	if (!text.empty() && text[0] == 'U')
		return "i32";
	if (!text.empty() && text[0] == 'u' &&
	    (text.size() < 2 || text[1] != '8'))
		return "i16";
	return "i8";
}

string ProgramLowerer::string_symbol(const string& token_text)
{
	map<string, string>::const_iterator found = string_literals.find(token_text);
	if (found != string_literals.end())
		return found->second;
	string name = "__strlit__" + to_string(string_literals.size() + 1);
	string_literals[token_text] = name;
	string_literal_types[name] = string_literal_lowir_type(token_text);
	string_defs.push_back(make_pair(name, decode_simple_string(token_text)));
	return name;
}


}  // namespace internal
}  // namespace pa14
