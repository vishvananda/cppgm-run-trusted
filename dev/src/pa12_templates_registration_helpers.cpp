#include "pa12_internal.h"
#include "pa12_expr_semantics_support.h"
#include "pa12_templates_function_support.h"

#include <algorithm>
#include <cstdint>
#include <functional>
#include <stdexcept>

using namespace std;

namespace pa12 {
namespace internal {

bool template_parameter_lists_match(const vector<TemplateParameterInfo>& left,
                                    const vector<TemplateParameterInfo>& right);

namespace {

bool builtin_parameter_type_keyword(ETokenType type)
{
	return type == KW_BOOL ||
	       type == KW_CHAR ||
	       type == KW_CHAR16_T ||
	       type == KW_CHAR32_T ||
	       type == KW_DOUBLE ||
	       type == KW_FLOAT ||
	       type == KW_INT ||
	       type == KW_LONG ||
	       type == KW_SHORT ||
	       type == KW_SIGNED ||
	       type == KW_UNSIGNED ||
	       type == KW_VOID ||
	       type == KW_WCHAR_T;
}

bool single_void_parameter_segment(const vector<Token>& tokens,
                                   size_t begin,
                                   size_t end)
{
	if (begin + 1 != end)
		return false;
	return tokens[begin].kind == posttoken::TokenKind::Simple &&
	       tokens[begin].type == KW_VOID;
}

void collect_parameter_name_tokens(const vector<Token>& tokens,
                                   size_t begin,
                                   size_t end,
                                   string& last_identifier,
                                   size_t& identifier_count,
                                   bool& builtin_type_keyword)
{
	int paren = 0;
	int square = 0;
	int angle = 0;
	bool previous_nested_pointer = false;
	string nested_declarator_identifier;
	for (size_t p = begin; p < end && p < tokens.size(); ++p)
	{
		if (tokens[p].kind == posttoken::TokenKind::Simple)
		{
			ETokenType type = tokens[p].type;
			if (type == OP_ASS && paren == 0 && square == 0 && angle == 0)
				break;
			if (type == OP_LPAREN)
				++paren;
			else if (type == OP_RPAREN && paren > 0)
				--paren;
			else if (type == OP_LSQUARE)
				++square;
			else if (type == OP_RSQUARE && square > 0)
				--square;
			else if (type == OP_LT && square == 0)
				++angle;
			else if (type == OP_GT && angle > 0)
				--angle;
			if (angle == 0 && square == 0 &&
			    builtin_parameter_type_keyword(type))
				builtin_type_keyword = true;
			previous_nested_pointer =
				paren > 0 && angle == 0 && square == 0 &&
				(type == OP_STAR || type == OP_AMP);
			continue;
		}
		if (tokens[p].kind == posttoken::TokenKind::Identifier &&
		    angle == 0 && square == 0)
		{
			if (paren > 0 && previous_nested_pointer)
				nested_declarator_identifier = tokens[p].source;
			last_identifier = tokens[p].source;
			++identifier_count;
			previous_nested_pointer = false;
		}
	}
	if (!nested_declarator_identifier.empty())
		last_identifier = nested_declarator_identifier;
}

size_t matching_function_header_paren(const vector<Token>& tokens,
                                      size_t lparen,
                                      size_t end)
{
	if (lparen >= end ||
	    lparen >= tokens.size() ||
	    tokens[lparen].kind != posttoken::TokenKind::Simple ||
	    tokens[lparen].type != OP_LPAREN)
		return end;
	int depth = 0;
	for (size_t i = lparen; i < end && i < tokens.size(); ++i)
	{
		if (tokens[i].kind != posttoken::TokenKind::Simple)
			continue;
		if (tokens[i].type == OP_LPAREN)
			++depth;
		else if (tokens[i].type == OP_RPAREN)
		{
			--depth;
			if (depth == 0)
				return i;
		}
	}
	return end;
}

}  // namespace

bool has_token(const vector<Token>& tokens,
               size_t begin,
               size_t end,
               ETokenType type)
{
	for (size_t i = begin; i < end && i < tokens.size(); ++i)
		if (tokens[i].kind == posttoken::TokenKind::Simple &&
		    tokens[i].type == type)
			return true;
	return false;
}

void merge_template_defaults(vector<TemplateParameterInfo>& target,
                             const vector<TemplateParameterInfo>& source)
{
	size_t old_size = target.size();
	if (target.size() < source.size())
		target.resize(source.size());
	for (size_t i = 0; i < source.size(); ++i)
	{
		bool new_slot = i >= old_size;
		if (new_slot)
			target[i].kind = source[i].kind;
		if (!source[i].name.empty())
			target[i].name = source[i].name;
		if (target[i].type.get() == NULL && source[i].type.get() != NULL)
			target[i].type = source[i].type;
		if (target[i].template_parameters.empty() &&
		    !source[i].template_parameters.empty())
			target[i].template_parameters = source[i].template_parameters;
		if (new_slot)
			target[i].is_pack = source[i].is_pack;
		if (source[i].has_default)
		{
			target[i].has_default = true;
			target[i].default_begin = source[i].default_begin;
			target[i].default_end = source[i].default_end;
		}
	}
}

Binding* find_matching_function_template_placeholder(
	const map<Binding*, TemplateDeclaration*>& placeholders,
	Scope* scope,
	const string& name,
	TypePtr type,
	const vector<TemplateParameterInfo>& parameters)
{
	if (scope == NULL)
		return NULL;
	map<string, vector<Binding*> >::iterator it = scope->members.find(name);
	if (it == scope->members.end())
		return NULL;
	size_t cache_key = reinterpret_cast<uintptr_t>(&placeholders);
	auto mix = [&cache_key](size_t value) {
		cache_key ^= value + 0x9e3779b97f4a7c15ULL +
		             (cache_key << 6) + (cache_key >> 2);
	};
	mix(reinterpret_cast<uintptr_t>(scope));
	mix(hash<string>()(name));
	mix(reinterpret_cast<uintptr_t>(type.get()));
	mix(reinterpret_cast<uintptr_t>(&parameters));
	mix(parameters.size());
	mix(placeholders.size());
	mix(it->second.size());
	if (!it->second.empty())
	{
		mix(reinterpret_cast<uintptr_t>(it->second.front()));
		mix(reinterpret_cast<uintptr_t>(it->second.back()));
	}
	static map<size_t, Binding*> success_cache;
	static set<size_t> miss_cache;
	map<size_t, Binding*>::const_iterator cached =
		success_cache.find(cache_key);
	if (cached != success_cache.end())
		return cached->second;
	if (miss_cache.find(cache_key) != miss_cache.end())
		return NULL;
	for (size_t i = 0; i < it->second.size(); ++i)
	{
		Binding* binding = it->second[i];
		if (binding->kind != BindingKind::Function ||
		    !pa11::same_type(binding->type, type))
			continue;
		map<Binding*, TemplateDeclaration*>::const_iterator templ =
			placeholders.find(binding);
		if (templ != placeholders.end() &&
		    template_parameter_lists_match(templ->second->parameters,
		                                   parameters))
		{
			success_cache[cache_key] = binding;
			return binding;
		}
	}
	miss_cache.insert(cache_key);
	return NULL;
}

void collect_template_parameter_placeholders(
	const vector<TemplateParameterInfo>& parameters,
	map<string, TypePtr>& parameter_types,
	map<string, TemplateArgument>& parameter_values)
{
	for (size_t i = 0; i < parameters.size(); ++i)
	{
		const TemplateParameterInfo& parameter = parameters[i];
		if (parameter.name.empty())
			continue;
		if (parameter.kind == TemplateParameterKind::Type)
			parameter_types[parameter.name] =
				template_parameter_placeholder_type(parameter);
		else if (parameter.kind == TemplateParameterKind::NonType)
		{
			TemplateArgument arg = TemplateArgument::dependent_value_arg(
				parameter.type.get() != NULL
				? parameter.type
				: pa11::make_fundamental(FT_INT));
			arg.value_name = parameter.name;
			if (parameter.is_pack)
			{
				vector<TemplateArgument> pack;
				pack.push_back(arg);
				parameter_values[parameter.name] =
					TemplateArgument::pack_arg(pack);
			}
			else
				parameter_values[parameter.name] = arg;
		}
		else if (parameter.kind == TemplateParameterKind::TemplateTemplate)
		{
			TemplateArgument arg = TemplateArgument::template_arg(NULL);
			arg.value_name = parameter.name;
			parameter_values[parameter.name] = arg;
		}
	}
}

set<string> collect_template_type_parameter_packs(
	const vector<TemplateParameterInfo>& parameters)
{
	set<string> packs;
	for (size_t i = 0; i < parameters.size(); ++i)
		if (parameters[i].kind == TemplateParameterKind::Type &&
		    parameters[i].is_pack &&
		    !parameters[i].name.empty())
			packs.insert(parameters[i].name);
	return packs;
}

vector<string> function_parameter_names_from_tokens(
	const vector<Token>& tokens,
	size_t lparen,
	size_t end,
	bool include_this)
{
	vector<string> names;
	if (include_this)
		names.push_back("this");
	if (lparen >= end || lparen >= tokens.size() ||
	    tokens[lparen].kind != posttoken::TokenKind::Simple ||
	    tokens[lparen].type != OP_LPAREN)
		return names;
	size_t segment_begin = lparen + 1;
	int paren = 0;
	int square = 0;
	int angle = 0;
	for (size_t i = lparen + 1; i < end && i < tokens.size(); ++i)
	{
		bool finish = false;
		if (tokens[i].kind == posttoken::TokenKind::Simple)
		{
			ETokenType type = tokens[i].type;
			if (type == OP_LPAREN)
				++paren;
			else if (type == OP_RPAREN)
			{
				if (paren == 0 && square == 0 && angle == 0)
					finish = true;
				else if (paren > 0)
					--paren;
			}
			else if (type == OP_LSQUARE)
				++square;
			else if (type == OP_RSQUARE && square > 0)
				--square;
			else if (type == OP_LT && paren == 0 && square == 0)
				++angle;
			else if (type == OP_GT && angle > 0)
				--angle;
			else if (type == OP_COMMA && paren == 0 &&
			         square == 0 && angle == 0)
				finish = true;
		}
		if (!finish)
			continue;
		if (segment_begin == i ||
		    (tokens[i].kind == posttoken::TokenKind::Simple &&
		     tokens[i].type == OP_RPAREN &&
		     names.size() == (include_this ? 1u : 0u) &&
		     single_void_parameter_segment(tokens, segment_begin, i)))
		{
			if (tokens[i].kind == posttoken::TokenKind::Simple &&
			    tokens[i].type == OP_RPAREN)
				break;
			segment_begin = i + 1;
			continue;
		}
		string last_identifier;
		size_t identifier_count = 0;
		bool builtin_type_keyword = false;
		collect_parameter_name_tokens(tokens,
		                              segment_begin,
		                              i,
		                              last_identifier,
		                              identifier_count,
		                              builtin_type_keyword);
		names.push_back(identifier_count >= 2 ||
		                (identifier_count == 1 && builtin_type_keyword)
		                ? last_identifier : string());
		if (tokens[i].kind == posttoken::TokenKind::Simple &&
		    tokens[i].type == OP_RPAREN)
			break;
		segment_begin = i + 1;
	}
	return names;
}

bool function_header_has_noexcept(const vector<Token>& tokens,
                                  size_t lparen,
                                  size_t end)
{
	size_t rparen = matching_function_header_paren(tokens, lparen, end);
	if (rparen == end)
		return false;
	for (size_t i = rparen + 1; i < end && i < tokens.size(); ++i)
	{
		if (tokens[i].kind != posttoken::TokenKind::Simple)
			continue;
		if (tokens[i].type == OP_LBRACE)
			return false;
		if (tokens[i].type == KW_NOEXCEPT)
			return true;
	}
	return false;
}

Scope* primary_class_template_scope(TemplateDeclaration* declaration)
{
	if (declaration == NULL)
		return NULL;
	Binding* binding = pa11::lookup_qualified(declaration->owner,
	                                          declaration->name,
	                                          pa11::LOOKUP_TYPE);
	TypePtr type = binding != NULL ? binding->type : TypePtr();
	TypePtr bare = type.get() != NULL ? pa11::strip_cv(type) : TypePtr();
	return bare.get() != NULL && bare->kind == pa11::TypeKind::Record
		? bare->scope : NULL;
}

size_t explicit_function_parameter_name_count(const vector<string>& names)
{
	if (names.empty())
		return 0;
	return names[0] == "this" ? names.size() - 1 : names.size();
}

bool Parser::register_conversion_function_template(
	TemplateDeclaration* declaration)
{
	if (current_scope()->kind != ScopeKind::Class)
		return false;
	Scope* class_scope = current_scope();
	TypePtr class_type = pa11::record_type_for_scope(class_scope);
	if (class_type.get() == NULL)
		return false;
	map<string, TypePtr> parameter_types;
	map<string, TemplateArgument> parameter_values;
	collect_template_parameter_placeholders(declaration->parameters,
	                                        parameter_types,
	                                        parameter_values);
	size_t save_pos = pos_;
	vector<map<string, TypePtr> > save_subst = template_type_substitutions_;
	vector<map<string, TemplateArgument> > save_value_subst =
		template_value_substitutions_;
	vector<set<string> > save_pack_subst = template_type_parameter_packs_;
	template_type_substitutions_.push_back(parameter_types);
	template_value_substitutions_.push_back(parameter_values);
	template_type_parameter_packs_.push_back(
		collect_template_type_parameter_packs(declaration->parameters));
	pos_ = declaration->decl_begin;
	try
	{
		bool explicit_conv = consume_explicit_specifier();
		bool constexpr_conv = consume(KW_CONSTEXPR);
		if (!explicit_conv)
			explicit_conv = consume_explicit_specifier();
		if (!consume(KW_OPERATOR))
			throw runtime_error("not a conversion function template");
		TypePtr result = parse_conversion_type_id();
		expect(OP_LPAREN);
		expect(OP_RPAREN);
		Suffix suffix(SuffixKind::Function);
		parse_function_suffix_tail(suffix);
		TypePtr this_type =
			pa11::make_pointer(pa11::make_cv(class_type,
			                                 suffix.function_cv));
		vector<TypePtr> params(1, this_type);
		TypePtr fn_type = pa11::make_function(result, params, false);
		string name = conversion_operator_name(result);
		Binding* placeholder = find_matching_function_template_placeholder(
			function_template_placeholders_,
			class_scope,
			name,
			fn_type,
			declaration->parameters);
		TemplateDeclaration* previous_declaration = NULL;
		if (placeholder != NULL)
		{
			map<Binding*, TemplateDeclaration*>::iterator previous =
				function_template_placeholders_.find(placeholder);
			if (previous != function_template_placeholders_.end())
				previous_declaration = previous->second;
		}
		if (placeholder == NULL)
			placeholder = add_value(class_scope,
			                        BindingKind::Function,
			                        name,
			                        fn_type);
		placeholder->is_explicit = explicit_conv;
		placeholder->is_constexpr = placeholder->is_constexpr || constexpr_conv;
		placeholder->is_inline_definition = at(OP_LBRACE) || constexpr_conv;
		placeholder->unwind_no = suffix.noexcept_decl;
		placeholder->dynamic_exception_spec = suffix.dynamic_exception_spec;
		placeholder->dynamic_exception_types = suffix.dynamic_exception_types;
		placeholder->ref_qualifier = suffix.ref_qualifier;
		placeholder->is_private =
			!class_private_access_.empty() && class_private_access_.back();
		placeholder->is_protected_member =
			!class_protected_access_.empty() && class_protected_access_.back();
		function_parameter_names_[placeholder] = vector<string>(1, "this");
		placeholder->function_parameter_names =
			function_parameter_names_[placeholder];
		declaration->function_parameter_names =
			function_parameter_names_[placeholder];
		declaration->kind = TemplateDeclarationKind::Function;
		declaration->owner = class_scope;
		declaration->name = name;
		declaration->generic_function_type = fn_type;
		declaration->placeholder = placeholder;
		declaration->has_definition =
			has_token(tokens_, pos_, declaration->decl_end, OP_LBRACE);
		if (previous_declaration != NULL)
			merge_template_defaults(declaration->parameters,
			                        previous_declaration->parameters);
		function_template_placeholders_[placeholder] = declaration;
		vector<TemplateDeclaration*>& overloads =
			function_templates_[class_scope][name];
		if (find(overloads.begin(), overloads.end(), declaration) ==
		    overloads.end())
			overloads.push_back(declaration);
		TypePtr owner_record = pa11::record_type_for_scope(class_scope);
		if (owner_record.get() != NULL)
		{
			map<const void*, TemplateDeclaration*>::iterator outer =
				record_template_declarations_.find(
					pa11::strip_cv(owner_record).get());
			if (outer != record_template_declarations_.end())
				add_member_function_template(
					member_function_templates_[
						make_pair(outer->second, name)],
					declaration);
		}
		template_type_substitutions_ = save_subst;
		template_value_substitutions_ = save_value_subst;
		template_type_parameter_packs_ = save_pack_subst;
		pos_ = save_pos;
		return true;
	}
	catch (const exception&)
	{
		template_type_substitutions_ = save_subst;
		template_value_substitutions_ = save_value_subst;
		template_type_parameter_packs_ = save_pack_subst;
		pos_ = save_pos;
		return false;
	}
}

}  // namespace internal
}  // namespace pa12
