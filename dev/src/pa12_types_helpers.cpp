#include "pa12_types_support.h"

#include <algorithm>
#include <set>
#include <stdexcept>

using namespace std;

namespace pa12 {
namespace internal {

TypePtr decay_type(TypePtr type)
{
	if (type.get() == NULL)
		return type;
	if (type->kind == pa11::TypeKind::LValueReference ||
	    type->kind == pa11::TypeKind::RValueReference)
		type = type->base;
	TypePtr bare = pa11::strip_cv(type);
	if (bare->kind == pa11::TypeKind::Array)
		return pa11::make_pointer(bare->base);
	if (bare->kind == pa11::TypeKind::Function)
		return pa11::make_pointer(bare);
	return pa11::strip_top_level_cv(type);
}

TypePtr remove_reference_type(TypePtr type)
{
	if (type.get() == NULL)
		return type;
	if (type->kind == pa11::TypeKind::LValueReference ||
	    type->kind == pa11::TypeKind::RValueReference)
		return type->base;
	return type;
}

TypePtr remove_cv_type(TypePtr type)
{
	if (type.get() == NULL)
		return type;
	return pa11::strip_top_level_cv(type);
}

TypePtr remove_cvref_type(TypePtr type)
{
	return remove_cv_type(remove_reference_type(type));
}

bool dependent_spelling_word_char(char c)
{
	return (c >= 'a' && c <= 'z') ||
	       (c >= 'A' && c <= 'Z') ||
	       (c >= '0' && c <= '9') ||
	       c == '_';
}

bool decltype_operand_is_parenthesized(const vector<Token>& tokens,
                                       size_t begin,
                                       size_t end)
{
	if (begin >= end ||
	    tokens[begin].kind != posttoken::TokenKind::Simple ||
	    tokens[begin].type != OP_LPAREN)
		return false;
	int depth = 0;
	for (size_t i = begin; i < end; ++i)
	{
		if (tokens[i].kind != posttoken::TokenKind::Simple)
			continue;
		if (tokens[i].type == OP_LPAREN)
			++depth;
		else if (tokens[i].type == OP_RPAREN)
		{
			--depth;
			if (depth == 0)
				return i + 1 == end;
		}
	}
	return false;
}

bool instance_argument_structurally_dependent_seen(
	const pa11::TemplateInstanceArgument& argument,
	set<const void*>& seen);

bool type_structurally_dependent_seen(TypePtr type,
                                      set<const void*>& seen)
{
	if (type.get() == NULL)
		return false;
	type = pa11::strip_cv(type);
	if (!seen.insert(type.get()).second)
		return false;
	if (type->is_dependent_typename ||
	    type->kind == pa11::TypeKind::TemplateParameter ||
	    type->kind == pa11::TypeKind::TemplateTemplateParameter)
		return true;
	if (type->kind == pa11::TypeKind::Pointer ||
	    type->kind == pa11::TypeKind::LValueReference ||
	    type->kind == pa11::TypeKind::RValueReference ||
	    type->kind == pa11::TypeKind::Array)
		return type_structurally_dependent_seen(type->base, seen);
	if (type->kind == pa11::TypeKind::Function)
	{
		if (type_structurally_dependent_seen(type->base, seen))
			return true;
		for (size_t i = 0; i < type->parameters.size(); ++i)
			if (type_structurally_dependent_seen(type->parameters[i], seen))
				return true;
		return false;
	}
	if (type->kind == pa11::TypeKind::MemberPointer)
		return type_structurally_dependent_seen(type->member_class, seen) ||
		       type_structurally_dependent_seen(type->base, seen);
	for (size_t i = 0; i < type->template_arguments.size(); ++i)
		if (instance_argument_structurally_dependent_seen(
			    type->template_arguments[i],
			    seen))
			return true;
	for (size_t i = 0;
	     i < type->dependent_typename_template_argument_lists.size();
	     ++i)
		for (size_t j = 0;
		     j < type->dependent_typename_template_argument_lists[i].size();
		     ++j)
			if (instance_argument_structurally_dependent_seen(
				    type->dependent_typename_template_argument_lists[i][j],
				    seen))
				return true;
	return false;
}

bool type_structurally_dependent(TypePtr type)
{
	set<const void*> seen;
	return type_structurally_dependent_seen(type, seen);
}

bool instance_argument_structurally_dependent_seen(
	const pa11::TemplateInstanceArgument& argument,
	set<const void*>& seen)
{
	if (argument.dependent || !argument.value_name.empty() ||
	    !argument.value_owner_template_name.empty() ||
	    !argument.value_member_name.empty())
		return true;
	if (argument.kind == pa11::TemplateInstanceArgumentKind::Type ||
	    argument.kind == pa11::TemplateInstanceArgumentKind::Value)
		return type_structurally_dependent_seen(argument.type, seen);
	if (argument.kind == pa11::TemplateInstanceArgumentKind::Pack)
		for (size_t i = 0; i < argument.pack.size(); ++i)
			if (instance_argument_structurally_dependent_seen(
				    argument.pack[i],
				    seen))
				return true;
	for (size_t i = 0;
	     i < argument.value_owner_template_arguments.size();
	     ++i)
		if (instance_argument_structurally_dependent_seen(
			    argument.value_owner_template_arguments[i],
			    seen))
			return true;
	return false;
}

bool instance_argument_structurally_dependent(
	const pa11::TemplateInstanceArgument& argument)
{
	set<const void*> seen;
	return instance_argument_structurally_dependent_seen(argument, seen);
}

bool expr_node_structurally_dependent(const Node& node)
{
	if (type_structurally_dependent(node.type))
		return true;
	if (node.binding != NULL &&
	    type_structurally_dependent(node.binding->type))
		return true;
	if (node.direct_call != NULL &&
	    type_structurally_dependent(node.direct_call->type))
		return true;
	for (size_t i = 0; i < node.children.size(); ++i)
		if (expr_node_structurally_dependent(node.children[i]))
			return true;
	return false;
}

bool skip_template_id_syntax(const vector<Token>& tokens, size_t& pos)
{
	if (pos >= tokens.size() ||
	    tokens[pos].kind != posttoken::TokenKind::Simple ||
	    tokens[pos].type != OP_LT)
		return false;
	int depth = 0;
	int paren = 0;
	int square = 0;
	int brace = 0;
	while (pos < tokens.size())
	{
		const Token& tok = tokens[pos];
		if (tok.kind != posttoken::TokenKind::Simple)
		{
			++pos;
			continue;
		}
		if (tok.type == OP_LPAREN)
			++paren;
		else if (tok.type == OP_RPAREN && paren > 0)
			--paren;
		else if (tok.type == OP_LSQUARE)
			++square;
		else if (tok.type == OP_RSQUARE && square > 0)
			--square;
		else if (tok.type == OP_LBRACE)
			++brace;
		else if (tok.type == OP_RBRACE && brace > 0)
			--brace;
		else if (paren == 0 && square == 0 && brace == 0 &&
		         tok.type == OP_LT)
			++depth;
		else if (paren == 0 && square == 0 && brace == 0 &&
		         tok.type == OP_GT)
		{
			--depth;
			++pos;
			if (depth == 0)
				return true;
			continue;
		}
		++pos;
	}
	return false;
}

bool internal_type_transform_name(const string& name)
{
	return name == "__decay" ||
	       name == "__decay_t" ||
	       name == "__remove_reference_t" ||
	       name == "__remove_cv" ||
	       name == "__remove_cv_t" ||
	       name == "__remove_cvref" ||
	       name == "__remove_cvref_t" ||
	       name == "__add_lvalue_reference" ||
	       name == "__add_rvalue_reference" ||
	       name == "__add_pointer" ||
	       name == "__remove_const" ||
	       name == "__remove_volatile" ||
	       name == "__remove_pointer" ||
	       name == "__remove_all_extents" ||
	       name == "__underlying_type";
}

TypePtr apply_internal_type_transform(const string& name, TypePtr inner)
{
	if (name == "__decay" || name == "__decay_t")
		return decay_type(inner);
	if (name == "__remove_reference_t")
		return remove_reference_type(inner);
	if (name == "__remove_cv" || name == "__remove_cv_t")
		return remove_cv_type(inner);
	if (name == "__remove_cvref" || name == "__remove_cvref_t")
		return remove_cvref_type(inner);
	if (name == "__add_lvalue_reference")
		return pa11::is_void_type(inner) ? inner :
			pa11::make_lvalue_reference(inner);
	if (name == "__add_rvalue_reference")
		return pa11::is_void_type(inner) ? inner :
			pa11::make_rvalue_reference(inner);
	if (name == "__add_pointer")
		return pa11::make_pointer(remove_reference_type(inner));
	if (name == "__remove_const")
	{
		unsigned cv = inner->kind == pa11::TypeKind::Cv
			? inner->cv : pa11::CV_NONE;
		return pa11::make_cv(pa11::strip_cv(inner),
		                     cv & ~pa11::CV_CONST);
	}
	if (name == "__remove_volatile")
	{
		unsigned cv = inner->kind == pa11::TypeKind::Cv
			? inner->cv : pa11::CV_NONE;
		return pa11::make_cv(pa11::strip_cv(inner),
		                     cv & ~pa11::CV_VOLATILE);
	}
	if (name == "__remove_pointer")
	{
		TypePtr bare = pa11::strip_cv(inner);
		return bare->kind == pa11::TypeKind::Pointer ? bare->base : inner;
	}
	if (name == "__remove_all_extents")
	{
		TypePtr bare = pa11::strip_cv(inner);
		while (bare->kind == pa11::TypeKind::Array)
			bare = pa11::strip_cv(bare->base);
		return bare;
	}
	if (name == "__underlying_type")
	{
		TypePtr bare = pa11::strip_cv(inner);
		if (bare->kind == pa11::TypeKind::Enum)
			return pa11::make_fundamental(bare->enum_underlying);
		return pa11::make_fundamental(FT_INT);
	}
	return inner;
}

pa11::TemplateInstanceArgument dependent_template_instance_argument(
	const TemplateArgument& argument)
{
	if (argument.kind == TemplateArgumentKind::Type)
	{
		if (argument.pack_expansion)
		{
			vector<pa11::TemplateInstanceArgument> pack;
			pack.push_back(
				pa11::TemplateInstanceArgument::type_arg(
					argument.type));
			return pa11::TemplateInstanceArgument::pack_arg(pack);
		}
		return pa11::TemplateInstanceArgument::type_arg(argument.type);
	}
	if (argument.kind == TemplateArgumentKind::Value)
	{
		if (argument.dependent)
		{
			pa11::TemplateInstanceArgument out =
				pa11::TemplateInstanceArgument::dependent_value_arg(
					argument.type);
			out.value_name = argument.value_name;
			out.value_negated = argument.value_negated;
			out.value_owner_template_name =
				argument.value_owner_template_name;
			out.value_member_name = argument.value_member_name;
			out.value_owner_template_arguments =
				argument.value_owner_template_arguments;
			out.value_expr_begin = argument.value_expr_begin;
			out.value_expr_end = argument.value_expr_end;
			return out;
		}
		pa11::TemplateInstanceArgument out =
			pa11::TemplateInstanceArgument::value_arg(argument.type,
			                                          argument.value);
		out.value_name = argument.value_name;
		out.value_negated = argument.value_negated;
		out.value_owner_template_name =
			argument.value_owner_template_name;
		out.value_member_name = argument.value_member_name;
		out.value_owner_template_arguments =
			argument.value_owner_template_arguments;
		out.value_expr_begin = argument.value_expr_begin;
		out.value_expr_end = argument.value_expr_end;
		return out;
	}
	if (argument.kind == TemplateArgumentKind::Template)
	{
			pa11::TemplateInstanceArgument out =
				pa11::TemplateInstanceArgument::template_arg(
					argument.template_declaration != NULL
					? qualified_template_declaration_name(
						argument.template_declaration)
					: !argument.value_name.empty()
					  ? argument.value_name
				  : string("template_parameter"));
		out.dependent = argument.template_declaration == NULL;
		return out;
	}
	vector<pa11::TemplateInstanceArgument> pack;
	for (size_t i = 0; i < argument.pack.size(); ++i)
		pack.push_back(
			dependent_template_instance_argument(argument.pack[i]));
	pa11::TemplateInstanceArgument out =
		pa11::TemplateInstanceArgument::pack_arg(pack);
	out.value_name = argument.value_name;
	out.template_name = argument.value_name;
	return out;
}

vector<pa11::TemplateInstanceArgument> dependent_template_instance_arguments(
	const vector<TemplateArgument>& arguments)
{
	vector<pa11::TemplateInstanceArgument> out;
	for (size_t i = 0; i < arguments.size(); ++i)
		out.push_back(dependent_template_instance_argument(arguments[i]));
	return out;
}

vector<vector<pa11::TemplateInstanceArgument> >
dependent_template_instance_argument_lists(
	const vector<vector<TemplateArgument> >& argument_lists)
{
	vector<vector<pa11::TemplateInstanceArgument> > out;
	for (size_t i = 0; i < argument_lists.size(); ++i)
		out.push_back(
			dependent_template_instance_arguments(argument_lists[i]));
	return out;
}

bool angle_tokens_contain_decltype(const vector<Token>& tokens, size_t pos)
{
	if (pos >= tokens.size() ||
	    tokens[pos].kind != posttoken::TokenKind::Simple ||
	    tokens[pos].type != OP_LT)
		return false;
	int depth = 0;
	for (size_t i = pos; i < tokens.size(); ++i)
	{
		const Token& tok = tokens[i];
		if (tok.kind == posttoken::TokenKind::Simple &&
		    tok.type == OP_LT)
			++depth;
		else if (tok.kind == posttoken::TokenKind::Simple &&
		         tok.type == OP_GT)
		{
			--depth;
			if (depth == 0)
				return false;
		}
		else if (tok.kind == posttoken::TokenKind::Simple &&
		         tok.type == KW_DECLTYPE)
			return true;
	}
	return false;
}

bool decltype_nested_name_specifier_ahead(const vector<Token>& tokens,
                                          size_t pos)
{
	if (pos >= tokens.size() ||
	    tokens[pos].kind != posttoken::TokenKind::Simple ||
	    tokens[pos].type != KW_DECLTYPE)
		return false;
	++pos;
	if (pos >= tokens.size() ||
	    tokens[pos].kind != posttoken::TokenKind::Simple ||
	    tokens[pos].type != OP_LPAREN)
		return false;
	int paren = 0;
	while (pos < tokens.size())
	{
		const Token& tok = tokens[pos];
		if (tok.kind == posttoken::TokenKind::Simple &&
		    tok.type == OP_LPAREN)
			++paren;
		else if (tok.kind == posttoken::TokenKind::Simple &&
		         tok.type == OP_RPAREN)
		{
			--paren;
			++pos;
			if (paren == 0)
				return pos < tokens.size() &&
				       tokens[pos].kind == posttoken::TokenKind::Simple &&
				       tokens[pos].type == OP_COLON2;
			continue;
		}
		++pos;
	}
	return false;
}

bool type_parse_mentions_active_record(
	TypePtr type,
	const vector<ActiveClassInstantiation>& active,
	const map<const void*, vector<TemplateArgument> >& record_template_arguments);

bool type_parse_template_argument_mentions_active_record(
	const TemplateArgument& argument,
	const vector<ActiveClassInstantiation>& active,
	const map<const void*, vector<TemplateArgument> >& record_template_arguments)
{
	if (argument.kind == TemplateArgumentKind::Type)
		return type_parse_mentions_active_record(argument.type,
		                                   active,
		                                   record_template_arguments);
	if (argument.kind == TemplateArgumentKind::Value)
		return type_parse_mentions_active_record(argument.type,
		                                   active,
		                                   record_template_arguments);
	if (argument.kind == TemplateArgumentKind::Pack)
		for (size_t i = 0; i < argument.pack.size(); ++i)
			if (type_parse_template_argument_mentions_active_record(
				    argument.pack[i],
				    active,
				    record_template_arguments))
				return true;
	return false;
}

bool type_parse_mentions_active_record(
	TypePtr type,
	const vector<ActiveClassInstantiation>& active,
	const map<const void*, vector<TemplateArgument> >& record_template_arguments)
{
	if (type.get() == NULL)
		return false;
	type = pa11::strip_cv(type);
	for (size_t i = 0; i < active.size(); ++i)
	{
		TypePtr active_type = active[i].type.get() != NULL
			? pa11::strip_cv(active[i].type) : TypePtr();
		if (active_type.get() != NULL && type.get() == active_type.get())
			return true;
	}
	if (type->kind == pa11::TypeKind::Pointer ||
	    type->kind == pa11::TypeKind::LValueReference ||
	    type->kind == pa11::TypeKind::RValueReference ||
	    type->kind == pa11::TypeKind::Array)
		return type_parse_mentions_active_record(type->base,
		                                   active,
		                                   record_template_arguments);
	if (type->kind == pa11::TypeKind::Function)
	{
		if (type_parse_mentions_active_record(type->base,
		                                active,
		                                record_template_arguments))
			return true;
		for (size_t i = 0; i < type->parameters.size(); ++i)
			if (type_parse_mentions_active_record(type->parameters[i],
			                                active,
			                                record_template_arguments))
				return true;
	}
	if (type->kind == pa11::TypeKind::MemberPointer)
		return type_parse_mentions_active_record(type->member_class,
		                                   active,
		                                   record_template_arguments) ||
		       type_parse_mentions_active_record(type->base,
		                                   active,
		                                   record_template_arguments);
	if (type->kind == pa11::TypeKind::Record)
	{
		map<const void*, vector<TemplateArgument> >::const_iterator found =
			record_template_arguments.find(type.get());
		if (found != record_template_arguments.end())
			for (size_t i = 0; i < found->second.size(); ++i)
				if (type_parse_template_argument_mentions_active_record(
					    found->second[i],
					    active,
					    record_template_arguments))
					return true;
	}
	return false;
}

string dependent_token_spelling(const vector<Token>& tokens,
                                size_t begin,
                                size_t end)
{
	string out;
	for (size_t i = begin; i < end && i < tokens.size(); ++i)
	{
		if (!out.empty() &&
		    !tokens[i].source.empty() &&
		    dependent_spelling_word_char(out[out.size() - 1]) &&
		    dependent_spelling_word_char(tokens[i].source[0]))
			out += " ";
		out += tokens[i].source;
	}
	return out;
}


}  // namespace internal
}  // namespace pa12
