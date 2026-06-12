#include "pa12_templates_instance_support.h"

#include <algorithm>
#include <cstdint>
#include <sstream>
#include <stdexcept>
#include <utility>

#include "posttoken_pipeline.h"
#include "pp_token.h"

using namespace std;

namespace pa12 {
namespace internal {

Parser* active_template_match_parser = NULL;
const vector<TemplateParameterInfo>* active_template_match_parameters = NULL;

bool same_template_record_type(TypePtr left, TypePtr right)
{
	TypePtr l = left.get() != NULL ? pa11::strip_cv(left) : TypePtr();
	TypePtr r = right.get() != NULL ? pa11::strip_cv(right) : TypePtr();
	if (l.get() == NULL || r.get() == NULL)
		return false;
	if (pa11::same_type(l, r))
		return true;
	return l->kind == pa11::TypeKind::Record &&
	       r->kind == pa11::TypeKind::Record &&
	       l->is_template_specialization &&
	       r->is_template_specialization &&
	       l->template_primary_name == r->template_primary_name &&
	       l->name == r->name;
}

bool template_instance_argument_contains_parameter_name(
	const pa11::TemplateInstanceArgument& argument,
	const string& name,
	const map<const void*, vector<TemplateArgument> >& record_arguments);

bool template_argument_contains_parameter_name(
	const TemplateArgument& argument,
	const string& name,
	const map<const void*, vector<TemplateArgument> >& record_arguments);

bool type_contains_parameter_name(
	TypePtr type,
	const string& name,
	const map<const void*, vector<TemplateArgument> >& record_arguments)
{
	if (type.get() == NULL)
		return false;
	type = pa11::strip_cv(type);
	if (type->kind == pa11::TypeKind::TemplateParameter)
	{
		if (type->is_dependent_typename)
		{
			for (size_t i = 0; i < type->template_arguments.size(); ++i)
				if (template_instance_argument_contains_parameter_name(
					    type->template_arguments[i],
					    name,
					    record_arguments))
					return true;
			for (size_t i = 0;
			     i < type->dependent_typename_template_argument_lists.size();
			     ++i)
				for (size_t j = 0;
				     j < type->dependent_typename_template_argument_lists[i].size();
				     ++j)
					if (template_instance_argument_contains_parameter_name(
						    type->dependent_typename_template_argument_lists[i][j],
						    name,
						    record_arguments))
						return true;
		}
		return pa11::is_deducible_template_parameter_type(type) &&
		       type->name == name;
	}
	if (type->kind == pa11::TypeKind::Pointer ||
	    type->kind == pa11::TypeKind::LValueReference ||
	    type->kind == pa11::TypeKind::RValueReference ||
	    type->kind == pa11::TypeKind::Array)
		return type_contains_parameter_name(type->base,
		                                    name,
		                                    record_arguments);
	if (type->kind == pa11::TypeKind::Function)
	{
		if (type_contains_parameter_name(type->base,
		                                 name,
		                                 record_arguments))
			return true;
		for (size_t i = 0; i < type->parameters.size(); ++i)
			if (type_contains_parameter_name(type->parameters[i],
			                                 name,
			                                 record_arguments))
				return true;
		return false;
	}
	if (type->kind == pa11::TypeKind::MemberPointer)
		return type_contains_parameter_name(type->member_class,
		                                    name,
		                                    record_arguments) ||
		       type_contains_parameter_name(type->base,
		                                    name,
		                                    record_arguments);
	if (type->is_template_specialization)
	{
		for (size_t i = 0; i < type->template_arguments.size(); ++i)
			if (template_instance_argument_contains_parameter_name(
				    type->template_arguments[i],
				    name,
				    record_arguments))
				return true;
		map<const void*, vector<TemplateArgument> >::const_iterator found =
			record_arguments.find(type.get());
		if (found != record_arguments.end())
			for (size_t i = 0; i < found->second.size(); ++i)
				if (template_argument_contains_parameter_name(
					    found->second[i],
					    name,
					    record_arguments))
					return true;
	}
	return false;
}

bool template_instance_argument_contains_parameter_name(
	const pa11::TemplateInstanceArgument& argument,
	const string& name,
	const map<const void*, vector<TemplateArgument> >& record_arguments)
{
	if (argument.kind == pa11::TemplateInstanceArgumentKind::Type)
		return type_contains_parameter_name(argument.type,
		                                    name,
		                                    record_arguments);
	if (argument.kind == pa11::TemplateInstanceArgumentKind::Value)
	{
		for (size_t i = 0;
		     i < argument.value_owner_template_arguments.size();
		     ++i)
			if (template_instance_argument_contains_parameter_name(
				    argument.value_owner_template_arguments[i],
				    name,
				    record_arguments))
				return true;
		return argument.value_owner_template_name == name ||
		       (argument.dependent && argument.value_name == name) ||
		       type_contains_parameter_name(argument.type,
		                                    name,
		                                    record_arguments);
	}
	if (argument.kind == pa11::TemplateInstanceArgumentKind::Pack)
		for (size_t i = 0; i < argument.pack.size(); ++i)
			if (template_instance_argument_contains_parameter_name(
				    argument.pack[i],
				    name,
				    record_arguments))
				return true;
	return false;
}

bool template_argument_contains_parameter_name(
	const TemplateArgument& argument,
	const string& name,
	const map<const void*, vector<TemplateArgument> >& record_arguments)
{
	if (argument.kind == TemplateArgumentKind::Type)
		return type_contains_parameter_name(argument.type,
		                                    name,
		                                    record_arguments);
	if (argument.kind == TemplateArgumentKind::Value)
	{
		for (size_t i = 0;
		     i < argument.value_owner_template_arguments.size();
		     ++i)
			if (template_instance_argument_contains_parameter_name(
				    argument.value_owner_template_arguments[i],
				    name,
				    record_arguments))
				return true;
		return argument.value_owner_template_name == name ||
		       (argument.dependent && argument.value_name == name) ||
		       type_contains_parameter_name(argument.type,
		                                    name,
		                                    record_arguments);
	}
	if (argument.kind == TemplateArgumentKind::Pack)
		for (size_t i = 0; i < argument.pack.size(); ++i)
			if (template_argument_contains_parameter_name(
				    argument.pack[i],
				    name,
				    record_arguments))
				return true;
	if (argument.kind == TemplateArgumentKind::Template)
		return argument.template_declaration == NULL &&
		       argument.value_name == name;
	return false;
}

bool declaration_starts_class_key(const vector<Token>& tokens,
                                  const TemplateDeclaration* declaration)
{
	if (declaration == NULL || declaration->decl_begin >= tokens.size())
		return false;
	const Token& token = tokens[declaration->decl_begin];
	return token.kind == posttoken::TokenKind::Simple &&
	       (token.type == KW_CLASS ||
	        token.type == KW_STRUCT ||
	        token.type == KW_UNION);
}

bool same_constructor_type_for_owner(TypePtr candidate,
                                     TypePtr wanted,
                                     TypePtr owner)
{
	if (candidate.get() == NULL || wanted.get() == NULL ||
	    candidate->kind != pa11::TypeKind::Function ||
	    wanted->kind != pa11::TypeKind::Function ||
	    candidate->parameters.size() != wanted->parameters.size() ||
	    candidate->variadic != wanted->variadic ||
	    !pa11::same_type(candidate->base, wanted->base) ||
	    candidate->parameters.empty())
		return false;
	TypePtr candidate_this = pa11::strip_cv(candidate->parameters[0]);
	TypePtr wanted_this = pa11::strip_cv(wanted->parameters[0]);
	if (candidate_this->kind != pa11::TypeKind::Pointer ||
	    wanted_this->kind != pa11::TypeKind::Pointer ||
	    !same_template_record_type(candidate_this->base, owner) ||
	    !same_template_record_type(wanted_this->base, owner))
		return false;
	for (size_t i = 1; i < candidate->parameters.size(); ++i)
		if (!pa11::same_type(candidate->parameters[i],
		                     wanted->parameters[i]))
			return false;
	return true;
}

bool same_static_member_type_with_owner_parameter(TypePtr candidate,
                                                  TypePtr wanted,
                                                  TypePtr owner)
{
	if (candidate.get() == NULL || wanted.get() == NULL ||
	    candidate->kind != pa11::TypeKind::Function ||
	    wanted->kind != pa11::TypeKind::Function ||
	    candidate->parameters.size() + 1 != wanted->parameters.size() ||
	    candidate->variadic != wanted->variadic ||
	    !pa11::same_type(candidate->base, wanted->base) ||
	    wanted->parameters.empty())
		return false;
	TypePtr wanted_this = pa11::strip_cv(wanted->parameters[0]);
	if (wanted_this->kind != pa11::TypeKind::Pointer ||
	    !same_template_record_type(wanted_this->base, owner))
		return false;
	for (size_t i = 0; i < candidate->parameters.size(); ++i)
		if (!pa11::same_type(candidate->parameters[i],
		                     wanted->parameters[i + 1]))
			return false;
	return true;
}

map<Binding*, Node>::const_iterator find_static_member_initializer_for_binding(
	const map<Binding*, Node>& initializers,
	Binding* binding)
{
	map<Binding*, Node>::const_iterator found = initializers.find(binding);
	if (found != initializers.end())
		return found;
	if (binding != NULL && binding->aliased_binding != NULL)
	{
		found = initializers.find(binding->aliased_binding);
		if (found != initializers.end())
			return found;
	}
	for (map<Binding*, Node>::const_iterator it = initializers.begin();
	     it != initializers.end();
	     ++it)
	{
		Binding* candidate = it->first;
		if (candidate != NULL &&
		    binding != NULL &&
		    candidate->name == binding->name &&
		    candidate->owner == binding->owner &&
		    pa11::same_type(candidate->type, binding->type))
			return it;
	}
	return initializers.end();
}

TemplateMatchParserScope::TemplateMatchParserScope(Parser* parser)
	: saved(active_template_match_parser)
{
	active_template_match_parser = parser;
}

TemplateMatchParserScope::~TemplateMatchParserScope()
{
	active_template_match_parser = saved;
}

TemplateMatchParameterScope::TemplateMatchParameterScope(
	const vector<TemplateParameterInfo>* parameters)
	: saved(active_template_match_parameters)
{
	active_template_match_parameters = parameters;
}

TemplateMatchParameterScope::~TemplateMatchParameterScope()
{
	active_template_match_parameters = saved;
}

bool collect_replay_tokens(const string& source, vector<Token>& out)
{
	vector<PPToken> pp_tokens = TokenizePPString(source);
	vector<posttoken::Token> post_tokens;
	if (!posttoken::collect_posttokens_checked(pp_tokens, post_tokens))
		return false;

	out.clear();
	int rshift_group = 1;
	for (size_t i = 0; i < post_tokens.size(); ++i)
	{
		const posttoken::Token& in = post_tokens[i];
		if (in.kind == posttoken::TokenKind::Simple &&
		    in.token_type == OP_RSHIFT)
		{
			Token first(posttoken::TokenKind::Simple, ">", OP_GT);
			Token second(posttoken::TokenKind::Simple, ">", OP_GT);
			first.split_rshift = true;
			second.split_rshift = true;
			first.split_group = rshift_group;
			second.split_group = rshift_group;
			++rshift_group;
			out.push_back(first);
			out.push_back(second);
			continue;
		}

		out.push_back(Token(in.kind, in.source, in.token_type));
	}
	return true;
}

bool node_calls_function_template(
	const Node& node,
	const map<Binding*, TemplateDeclaration*>& function_template_placeholders)
{
	if (node.direct_call != NULL)
	{
		Binding* binding = node.direct_call->aliased_binding != NULL
			? node.direct_call->aliased_binding
			: node.direct_call;
		if (function_template_placeholders.find(binding) !=
		    function_template_placeholders.end() ||
		    function_template_placeholders.find(node.direct_call) !=
		    function_template_placeholders.end())
			return true;
	}
	for (size_t i = 0; i < node.children.size(); ++i)
		if (node_calls_function_template(node.children[i],
		                                 function_template_placeholders))
			return true;
	return false;
}

string template_type_spelling(TypePtr type)
{
	if (type.get() == NULL)
		return "";
	switch (type->kind)
	{
	case pa11::TypeKind::Fundamental:
		return pa11::describe_type(type);
	case pa11::TypeKind::Cv:
		if (type->cv == (pa11::CV_CONST | pa11::CV_VOLATILE))
			return "const volatile " + template_type_spelling(type->base);
		if (type->cv == pa11::CV_CONST)
			return "const " + template_type_spelling(type->base);
		return "volatile " + template_type_spelling(type->base);
	case pa11::TypeKind::Pointer:
		return "pointer to " + template_type_spelling(type->base);
	case pa11::TypeKind::LValueReference:
		return "lvalue-reference to " + template_type_spelling(type->base);
	case pa11::TypeKind::RValueReference:
		return "rvalue-reference to " + template_type_spelling(type->base);
	case pa11::TypeKind::Array:
		if (type->unknown_bound)
			return "array of unknown bound of " +
			       template_type_spelling(type->base);
		return "array of " + to_string(type->bound) + " " +
		       template_type_spelling(type->base);
	case pa11::TypeKind::Function:
	{
		ostringstream out;
		out << "function of (";
		for (size_t i = 0; i < type->parameters.size(); ++i)
		{
			if (i != 0)
				out << ", ";
			out << template_type_spelling(type->parameters[i]);
		}
		if (type->variadic)
			out << (type->parameters.empty() ? "..." : ", ...");
		out << ")";
		if (type->cv == pa11::CV_CONST)
			out << " const";
		else if (type->cv == pa11::CV_VOLATILE)
			out << " volatile";
		else if (type->cv == (pa11::CV_CONST | pa11::CV_VOLATILE))
			out << " const volatile";
		out << " returning " << template_type_spelling(type->base);
		return out.str();
	}
	case pa11::TypeKind::MemberPointer:
		return "member-pointer of " +
		       template_type_spelling(type->member_class) + " to " +
		       template_type_spelling(type->base);
	case pa11::TypeKind::Record:
	case pa11::TypeKind::Enum:
		return type->name;
	case pa11::TypeKind::TemplateParameter:
		return "typename " + type->name;
	case pa11::TypeKind::TemplateTemplateParameter:
		return "template-parameter " + type->name;
	}
	throw logic_error("unknown type kind");
}

string template_type_key(TypePtr type);

string template_instance_argument_key(
	const pa11::TemplateInstanceArgument& argument);

string template_instance_argument_pack_key(
	const vector<pa11::TemplateInstanceArgument>& arguments)
{
	ostringstream out;
	for (size_t i = 0; i < arguments.size(); ++i)
	{
		if (i != 0)
			out << ",";
		out << template_instance_argument_key(arguments[i]);
	}
	return out.str();
}

string template_instance_argument_key(
	const pa11::TemplateInstanceArgument& argument)
{
	if (argument.kind == pa11::TemplateInstanceArgumentKind::Type)
		return "T(" + template_type_key(argument.type) + ")";
	if (argument.kind == pa11::TemplateInstanceArgumentKind::Value)
		return string("V(") + template_type_key(argument.type) + "," +
		       (argument.dependent
		        ? string("?") + (argument.value_negated ? "!" : "") +
		          argument.value_name +
		          (argument.value_expr_end > argument.value_expr_begin
		           ? "@" + to_string(argument.value_expr_begin) + ":" +
		             to_string(argument.value_expr_end)
		           : "")
		        : to_string(argument.value)) + ")";
	if (argument.kind == pa11::TemplateInstanceArgumentKind::Template)
		return "M(" + argument.template_name + ")";
	return "P(" + template_instance_argument_pack_key(argument.pack) + ")";
}

string dependent_value_member_key(const TemplateArgument& arg)
{
	ostringstream out;
	out << arg.value_owner_template_name << "::"
	    << arg.value_member_name << "|" << arg.value_name << "|"
	    << template_instance_argument_pack_key(
		    arg.value_owner_template_arguments);
	return out.str();
}

string template_type_key(TypePtr type)
{
	if (type.get() == NULL)
		return "";
	switch (type->kind)
	{
	case pa11::TypeKind::Cv:
		return "cv(" + to_string(type->cv) + "," +
		       template_type_key(type->base) + ")";
	case pa11::TypeKind::Pointer:
		return "ptr(" + template_type_key(type->base) + ")";
	case pa11::TypeKind::LValueReference:
		return "lref(" + template_type_key(type->base) + ")";
	case pa11::TypeKind::RValueReference:
		return "rref(" + template_type_key(type->base) + ")";
	case pa11::TypeKind::Array:
		return string("array(") +
		       (type->unknown_bound ? "?" : to_string(type->bound)) + "," +
		       template_type_key(type->base) + ")";
	case pa11::TypeKind::Function:
	{
		ostringstream out;
		out << "fn";
		if (type->cv != pa11::CV_NONE)
			out << "cv" << type->cv;
		if (type->ref_qualifier != 0)
			out << "ref" << type->ref_qualifier;
		out << "(";
		for (size_t i = 0; i < type->parameters.size(); ++i)
		{
			if (i != 0)
				out << ",";
			out << template_type_key(type->parameters[i]);
		}
		if (type->variadic)
		{
			if (!type->parameters.empty())
				out << ",";
			out << "...";
		}
		out << ")->" << template_type_key(type->base);
		return out.str();
	}
	case pa11::TypeKind::MemberPointer:
		return "memptr(" + template_type_key(type->member_class) + "," +
		       template_type_key(type->base) + ")";
		case pa11::TypeKind::Record:
		case pa11::TypeKind::Enum:
		{
			if (type->kind == pa11::TypeKind::Record &&
			    type->is_template_specialization)
				return "spec(" + type->template_primary_name +
				       "<" +
				       template_instance_argument_pack_key(
					       type->template_arguments) +
				       ">)";
			ostringstream out;
			out << template_type_spelling(type) << "@" << type.get();
			return out.str();
		}
	default:
		return template_type_spelling(type);
	}
}

string template_argument_spelling(const TemplateArgument& argument)
{
	if (argument.kind == TemplateArgumentKind::Type)
		return template_type_spelling(argument.type) +
		       (argument.pack_expansion ? "..." : "");
	if (argument.kind == TemplateArgumentKind::Value)
	{
		if (argument.value_binding != NULL)
			return argument.value_binding->name +
			       (argument.pack_expansion ? "..." : "");
		if (argument.dependent)
			return "dependent-value";
		TypePtr bare = argument.type.get() != NULL
			? pa11::strip_cv(argument.type) : TypePtr();
		if (bare.get() != NULL && bare->kind == pa11::TypeKind::Enum)
			return template_type_spelling(bare) + " " +
			       to_string(argument.value) +
			       (argument.pack_expansion ? "..." : "");
		return to_string(argument.value) +
		       (argument.pack_expansion ? "..." : "");
	}
	if (argument.kind == TemplateArgumentKind::Template)
		return (argument.template_declaration != NULL
		        ? argument.template_declaration->name
		        : argument.value_name.empty()
		          ? string("template-parameter")
		          : argument.value_name) +
		       (argument.pack_expansion ? "..." : "");
	ostringstream out;
	for (size_t i = 0; i < argument.pack.size(); ++i)
	{
		if (i != 0)
			out << ",";
		out << template_argument_spelling(argument.pack[i]);
	}
	return out.str();
}

string template_argument_key_part(const TemplateArgument& argument)
{
	if (argument.kind == TemplateArgumentKind::Type)
		return string(argument.pack_expansion ? "TE(" : "T(") +
		       template_type_key(argument.type) + ")";
	if (argument.kind == TemplateArgumentKind::Value)
	{
		if (argument.value_binding != NULL)
			return string(argument.pack_expansion ? "VE(" : "V(") +
			       template_type_key(argument.type) + ",B@" +
			       to_string(reinterpret_cast<uintptr_t>(
				       argument.value_binding)) + ")";
		ostringstream out;
		out << (argument.pack_expansion ? "VE(" : "V(")
		    << template_type_key(argument.type) << ",";
		if (argument.dependent)
		{
			out << "?" << (argument.value_negated ? "!" : "")
			    << argument.value_name;
			if (!argument.value_owner_template_name.empty() ||
			    !argument.value_member_name.empty())
			{
				out << "@" << argument.value_owner_template_name
				    << "::" << argument.value_member_name
				    << "<" << template_instance_argument_pack_key(
					            argument.value_owner_template_arguments)
				    << ">";
			}
			if (argument.value_expr_end > argument.value_expr_begin)
				out << "#" << argument.value_expr_begin << ":"
				    << argument.value_expr_end;
		}
		else
			out << argument.value;
		out << ")";
		return out.str();
	}
	if (argument.kind == TemplateArgumentKind::Template)
	{
		ostringstream out;
		out << (argument.pack_expansion ? "ME(" : "M(")
		    << (argument.template_declaration != NULL
		        ? argument.template_declaration->owner : NULL)
		    << ":" << (argument.template_declaration != NULL
		               ? argument.template_declaration->name
		               : string("<dependent>") + argument.value_name)
		    << ":" << argument.template_declaration << ")";
		return out.str();
	}
	ostringstream out;
	out << "P(";
	for (size_t i = 0; i < argument.pack.size(); ++i)
	{
		if (i != 0)
			out << ",";
		out << template_argument_key_part(argument.pack[i]);
	}
	out << ")";
	return out.str();
}

string template_argument_spelling(const vector<TemplateArgument>& arguments)
{
	ostringstream out;
	for (size_t i = 0; i < arguments.size(); ++i)
	{
		if (i != 0)
			out << ",";
		out << template_argument_spelling(arguments[i]);
	}
	return out.str();
}

bool type_mentions_active_record(
	TypePtr type,
	const vector<ActiveClassInstantiation>& active)
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
		return type_mentions_active_record(type->base, active);
	if (type->kind == pa11::TypeKind::Function)
	{
		if (type_mentions_active_record(type->base, active))
			return true;
		for (size_t i = 0; i < type->parameters.size(); ++i)
			if (type_mentions_active_record(type->parameters[i], active))
				return true;
	}
	if (type->kind == pa11::TypeKind::MemberPointer)
		return type_mentions_active_record(type->member_class, active) ||
		       type_mentions_active_record(type->base, active);
	return false;
}

pa11::TemplateInstanceArgument template_instance_argument(
	const TemplateArgument& argument)
{
	if (argument.pack_expansion && argument.kind != TemplateArgumentKind::Pack)
	{
		TemplateArgument element = argument;
		element.pack_expansion = false;
		vector<pa11::TemplateInstanceArgument> pack;
		pack.push_back(template_instance_argument(element));
		return pa11::TemplateInstanceArgument::pack_arg(pack);
	}
	if (argument.kind == TemplateArgumentKind::Type)
	{
		return pa11::TemplateInstanceArgument::type_arg(argument.type);
	}
	if (argument.kind == TemplateArgumentKind::Value)
	{
		if (argument.value_binding != NULL)
		{
			Binding* binding = argument.value_binding->aliased_binding != NULL
				? argument.value_binding->aliased_binding
				: argument.value_binding;
			pa11::TemplateInstanceArgument out =
				pa11::TemplateInstanceArgument::value_arg(
					argument.type,
					argument.value);
			out.value_expr_begin = argument.value_expr_begin;
			out.value_expr_end = argument.value_expr_end;
			for (Scope* scope = binding->owner; scope != NULL; scope = scope->parent)
				if ((scope->kind == ScopeKind::Namespace ||
				     scope->kind == ScopeKind::Class) &&
				    !scope->name.empty() && scope->name != "<unnamed>")
					out.value_name = scope->name + "::" + out.value_name;
			out.value_name += binding->name;
			return out;
		}
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
	{
		TemplateArgument element = argument.pack[i];
		if (element.kind == TemplateArgumentKind::Value &&
		    !element.dependent)
			element.pack_expansion = false;
		pack.push_back(template_instance_argument(element));
	}
	pa11::TemplateInstanceArgument out =
		pa11::TemplateInstanceArgument::pack_arg(pack);
	out.value_name = argument.value_name;
	out.template_name = argument.value_name;
	return out;
}

	vector<pa11::TemplateInstanceArgument> template_instance_arguments(
		const vector<TemplateArgument>& arguments)
	{
		vector<pa11::TemplateInstanceArgument> out;
		for (size_t i = 0; i < arguments.size(); ++i)
			out.push_back(template_instance_argument(arguments[i]));
		return out;
	}

	bool single_instance_pack_element_is_expansion(
		const TemplateArgument& argument)
	{
		string pack_name;
		if (argument.kind == TemplateArgumentKind::Type)
			return template_type_has_template_parameter_name(argument.type,
			                                                pack_name);
		if (argument.kind == TemplateArgumentKind::Value)
		{
			if (!argument.value_name.empty() ||
			    !argument.value_owner_template_name.empty())
				return true;
			return template_type_has_template_parameter_name(argument.type,
			                                                pack_name);
		}
		if (argument.kind == TemplateArgumentKind::Template)
			return !argument.value_name.empty() ||
			       argument.template_declaration == NULL;
		return false;
	}

	TemplateArgument template_argument_from_instance_argument(
		const pa11::TemplateInstanceArgument& argument)
{
	if (argument.kind == pa11::TemplateInstanceArgumentKind::Type)
		return TemplateArgument::type_arg(argument.type);
	if (argument.kind == pa11::TemplateInstanceArgumentKind::Value)
	{
		TemplateArgument out = argument.dependent
			? TemplateArgument::dependent_value_arg(argument.type)
			: TemplateArgument::value_arg(argument.type, argument.value);
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
	if (argument.kind == pa11::TemplateInstanceArgumentKind::Template)
	{
		TemplateArgument out = TemplateArgument::template_arg(NULL);
		out.value_name = argument.template_name;
		return out;
	}
		vector<TemplateArgument> pack;
		for (size_t i = 0; i < argument.pack.size(); ++i)
			pack.push_back(
				template_argument_from_instance_argument(argument.pack[i]));
		bool anonymous_pack =
			argument.value_name.empty() && argument.template_name.empty();
		if (anonymous_pack &&
		    pack.size() == 1 &&
		    pack[0].kind != TemplateArgumentKind::Pack &&
		    single_instance_pack_element_is_expansion(pack[0]))
		{
			pack[0].pack_expansion = true;
			return pack[0];
		}
		TemplateArgument out = TemplateArgument::pack_arg(pack);
		out.value_name = argument.value_name.empty()
			? argument.template_name : argument.value_name;
		return out;
	}

TemplateArgument match_template_argument_from_instance_argument(
	const pa11::TemplateInstanceArgument& argument)
{
	if (argument.kind != pa11::TemplateInstanceArgumentKind::Pack)
		return template_argument_from_instance_argument(argument);
	vector<TemplateArgument> pack;
	for (size_t i = 0; i < argument.pack.size(); ++i)
		pack.push_back(
			match_template_argument_from_instance_argument(argument.pack[i]));
	TemplateArgument out = TemplateArgument::pack_arg(pack);
	out.value_name = argument.value_name.empty()
		? argument.template_name : argument.value_name;
	return out;
}

vector<TemplateArgument> match_template_arguments_from_instance_arguments(
	const vector<pa11::TemplateInstanceArgument>& arguments)
{
	vector<TemplateArgument> out;
	for (size_t i = 0; i < arguments.size(); ++i)
		out.push_back(
			match_template_argument_from_instance_argument(arguments[i]));
	return out;
}

TemplateArgument raw_template_argument_from_instance_argument(
	const pa11::TemplateInstanceArgument& argument)
{
	if (argument.kind == pa11::TemplateInstanceArgumentKind::Type)
		return TemplateArgument::type_arg(argument.type);
	if (argument.kind == pa11::TemplateInstanceArgumentKind::Value)
	{
		TemplateArgument out = argument.dependent
			? TemplateArgument::dependent_value_arg(argument.type)
			: TemplateArgument::value_arg(argument.type, argument.value);
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
	if (argument.kind == pa11::TemplateInstanceArgumentKind::Template)
	{
		TemplateArgument out = TemplateArgument::template_arg(NULL);
		out.value_name = argument.template_name;
		return out;
	}
		vector<TemplateArgument> pack;
		for (size_t i = 0; i < argument.pack.size(); ++i)
			pack.push_back(
				raw_template_argument_from_instance_argument(argument.pack[i]));
		bool anonymous_pack =
			argument.value_name.empty() && argument.template_name.empty();
		if (anonymous_pack &&
		    pack.size() == 1 &&
		    pack[0].kind != TemplateArgumentKind::Pack &&
		    single_instance_pack_element_is_expansion(pack[0]))
		{
			pack[0].pack_expansion = true;
			return pack[0];
		}
		TemplateArgument out = TemplateArgument::pack_arg(pack);
		out.value_name = argument.value_name.empty()
			? argument.template_name : argument.value_name;
		return out;
	}


}  // namespace internal
}  // namespace pa12
