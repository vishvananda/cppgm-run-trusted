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

vector<string> qualified_parts(const Binding* binding)
{
	vector<string> parts;
	for (Scope* s = binding->owner; s != NULL; s = s->parent)
	{
		if ((s->kind == ScopeKind::Namespace || s->kind == ScopeKind::Class) &&
		    !s->name.empty() && s->name != "<unnamed>")
			parts.push_back(s->name);
	}
	vector<string> out;
	for (size_t i = parts.size(); i > 0; --i)
		out.push_back(parts[i - 1]);
	out.push_back(binding->name);
	return out;
}

string source_symbol_base(const Binding* binding)
{
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
		             pa11::describe_type(binding->type);
		function_symbols[key] = name;
	}
	return name;
}

vector<unsigned char> decode_simple_string(const string& text)
{
	size_t first = text.find('"');
	size_t last = text.rfind('"');
	if (first == string::npos || last == first)
		throw runtime_error("invalid string literal");
	vector<uint32_t> code_points;
	if (!DecodeOrdinaryBody(text, first + 1, last, code_points))
		throw runtime_error("invalid string literal");
	vector<unsigned char> bytes;
	for (size_t i = 0; i < code_points.size(); ++i)
		bytes.push_back(static_cast<unsigned char>(code_points[i] & 0xff));
	bytes.push_back(0);
	return bytes;
}

string ProgramLowerer::string_symbol(const string& token_text)
{
	map<string, string>::const_iterator found = string_literals.find(token_text);
	if (found != string_literals.end())
		return found->second;
	string name = "__strlit__" + to_string(string_literals.size() + 1);
	string_literals[token_text] = name;
	string_defs.push_back(make_pair(name, decode_simple_string(token_text)));
	return name;
}


}  // namespace internal
}  // namespace pa14
