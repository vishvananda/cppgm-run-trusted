#include "pa12_templates_instance_support.h"
#include <algorithm>
#include <cstdint>
#include <functional>
#include <map>
#include <set>
#include <sstream>
#include <stdexcept>
#include <utility>
#include "posttoken_pipeline.h"
#include "pp_token.h"
#include "pa12_types_support.h"
using namespace std;
namespace pa12 {
namespace internal {
Parser* active_template_match_parser = NULL;
const vector<TemplateParameterInfo>* active_template_match_parameters = NULL;
bool template_record_owner_name_match(TypePtr left, TypePtr right);
size_t dependent_cache_template_argument_identity(
	const TemplateArgument& argument,
	int depth);
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
static bool same_signature_template_argument(
	const pa11::TemplateInstanceArgument& left,
	const pa11::TemplateInstanceArgument& right);
static bool same_signature_template_argument_list(
	const vector<pa11::TemplateInstanceArgument>& left,
	const vector<pa11::TemplateInstanceArgument>& right)
{
	if (left.size() != right.size())
		return false;
	for (size_t i = 0; i < left.size(); ++i)
		if (!same_signature_template_argument(left[i], right[i]))
			return false;
	return true;
}
static bool same_signature_template_argument_lists(
	const vector<vector<pa11::TemplateInstanceArgument> >& left,
	const vector<vector<pa11::TemplateInstanceArgument> >& right)
{
	if (left.size() != right.size())
		return false;
	for (size_t i = 0; i < left.size(); ++i)
		if (!same_signature_template_argument_list(left[i], right[i]))
			return false;
	return true;
}
static bool same_signature_type(TypePtr left, TypePtr right)
{
	TypePtr l = left.get() != NULL ? pa11::strip_cv(left) : TypePtr();
	TypePtr r = right.get() != NULL ? pa11::strip_cv(right) : TypePtr();
	if (l.get() == NULL || r.get() == NULL)
		return l.get() == r.get();
	if (pa11::same_type(l, r))
		return true;
	if (l->kind != r->kind)
		return false;
	if (l->is_dependent_typename || r->is_dependent_typename)
		return l->is_dependent_typename == r->is_dependent_typename &&
		       l->name == r->name &&
		       l->template_primary_name == r->template_primary_name &&
		       l->dependent_typename_qualified ==
			       r->dependent_typename_qualified &&
		       l->dependent_typename_template_id ==
			       r->dependent_typename_template_id &&
		       l->dependent_typename_decltype ==
			       r->dependent_typename_decltype &&
		       same_signature_template_argument_list(
			       l->template_arguments,
			       r->template_arguments) &&
		       same_signature_template_argument_lists(
			       l->dependent_typename_template_argument_lists,
			       r->dependent_typename_template_argument_lists);
	if (l->kind == pa11::TypeKind::Pointer ||
	    l->kind == pa11::TypeKind::LValueReference ||
	    l->kind == pa11::TypeKind::RValueReference)
		return same_signature_type(l->base, r->base);
	if (l->kind == pa11::TypeKind::Array)
		return l->unknown_bound == r->unknown_bound &&
		       (l->unknown_bound || l->bound == r->bound) &&
		       same_signature_type(l->base, r->base);
	if (l->kind == pa11::TypeKind::Function)
	{
		if (l->parameters.size() != r->parameters.size() ||
		    l->variadic != r->variadic ||
		    l->ref_qualifier != r->ref_qualifier ||
		    !same_signature_type(l->base, r->base))
			return false;
		for (size_t i = 0; i < l->parameters.size(); ++i)
			if (!same_signature_type(l->parameters[i],
			                         r->parameters[i]))
				return false;
		return true;
	}
	if (l->kind == pa11::TypeKind::MemberPointer)
		return same_signature_type(l->member_class, r->member_class) &&
		       same_signature_type(l->base, r->base);
	if (l->kind == pa11::TypeKind::Record)
	{
		if (!same_template_record_type(l, r) ||
		    l->template_arguments.size() != r->template_arguments.size())
			return false;
		for (size_t i = 0; i < l->template_arguments.size(); ++i)
			if (!same_signature_template_argument(
				    l->template_arguments[i],
				    r->template_arguments[i]))
				return false;
		return true;
	}
	if (l->kind == pa11::TypeKind::Fundamental)
		return l->fundamental == r->fundamental;
	if (l->kind == pa11::TypeKind::Enum)
		return l->name == r->name &&
		       l->enum_underlying == r->enum_underlying;
	if (l->kind == pa11::TypeKind::TemplateParameter ||
	    l->kind == pa11::TypeKind::TemplateTemplateParameter)
		return l->name == r->name;
	return false;
}
static bool same_signature_template_argument(
	const pa11::TemplateInstanceArgument& left,
	const pa11::TemplateInstanceArgument& right)
{
	if (left.kind != right.kind)
		return false;
	if (left.kind == pa11::TemplateInstanceArgumentKind::Type)
		return same_signature_type(left.type, right.type);
	if (left.kind == pa11::TemplateInstanceArgumentKind::Value)
	{
		if (left.dependent != right.dependent)
			return same_signature_type(left.type, right.type);
		return left.value_negated == right.value_negated &&
		       left.value == right.value &&
		       left.value_name == right.value_name &&
		       same_signature_type(left.type, right.type);
	}
	if (left.kind == pa11::TemplateInstanceArgumentKind::Template)
		return left.template_name == right.template_name &&
		       left.dependent == right.dependent;
	if (left.pack.size() != right.pack.size())
		return false;
	for (size_t i = 0; i < left.pack.size(); ++i)
		if (!same_signature_template_argument(left.pack[i],
		                                      right.pack[i]))
			return false;
	return true;
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
		if (!same_signature_type(candidate->parameters[i],
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
		if (!same_signature_type(candidate->parameters[i],
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
		bool same_owner = false;
		bool template_owner_match = false;
		if (candidate != NULL && binding != NULL)
		{
			same_owner = candidate->owner == binding->owner;
			if (!same_owner &&
			    candidate->owner != NULL &&
			    binding->owner != NULL &&
			    candidate->owner->kind == ScopeKind::Class &&
			    binding->owner->kind == ScopeKind::Class)
			{
				TypePtr candidate_record =
					pa11::record_type_for_scope(candidate->owner);
				TypePtr binding_record =
					pa11::record_type_for_scope(binding->owner);
				template_owner_match =
					candidate_record.get() != NULL &&
					binding_record.get() != NULL &&
					(same_template_record_type(candidate_record,
					                           binding_record) ||
					 template_record_owner_name_match(candidate_record,
					                                  binding_record));
				same_owner = template_owner_match;
			}
		}
		if (candidate != NULL &&
		    binding != NULL &&
		    candidate->name == binding->name &&
		    same_owner &&
		    (template_owner_match ||
		     pa11::same_type(candidate->type, binding->type)))
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
	map<const void*, pair<size_t, string> >& template_type_key_cache()
	{
		static map<const void*, pair<size_t, string> > cache;
		return cache;
	}
	vector<size_t>& template_type_key_active_stack()
	{
		static vector<size_t> active;
		return active;
	}
	string template_type_key_placeholder(TypePtr type, const string& tag)
	{
		TypePtr bare = type.get() != NULL ? pa11::strip_cv(type) : TypePtr();
		ostringstream out;
		out << tag << "(";
		if (bare.get() != NULL)
			out << static_cast<int>(bare->kind) << "|" << bare->name << "|"
			    << bare->template_primary_name << "@" << bare.get();
		out << ")";
		return out.str();
	}
void clear_template_type_key_cache()
{
	template_type_key_cache().clear();
}
void discard_template_type_key_cache(TypePtr type)
{
	if (type.get() != NULL)
		template_type_key_cache().erase(type.get());
}
void remember_template_type_key(TypePtr type,
                                size_t fingerprint,
                                const string& key)
{
	if (key.size() > 65536)
	{
		template_type_key_cache().erase(type.get());
		return;
	}
	template_type_key_cache()[type.get()] = make_pair(fingerprint, key);
}
size_t template_key_hash_combine(size_t seed, size_t value)
{
	return seed ^ (value + 0x9e3779b97f4a7c15ULL + (seed << 6) +
	               (seed >> 2));
}
size_t template_key_string_hash(const string& value)
{
	return template_key_hash_combine(value.size(), hash<string>()(value));
}
size_t template_type_cache_hash(TypePtr type, int depth);
size_t instance_argument_cache_hash(
	const pa11::TemplateInstanceArgument& argument,
	int depth)
{
	size_t out = static_cast<size_t>(argument.kind);
	out = template_key_hash_combine(
		out,
		reinterpret_cast<uintptr_t>(argument.type.get()));
	out = template_key_hash_combine(out, argument.value);
	out = template_key_hash_combine(out, argument.dependent);
	out = template_key_hash_combine(out, argument.value_negated);
	out = template_key_hash_combine(out, argument.value_expr_begin);
	out = template_key_hash_combine(out, argument.value_expr_end);
	out = template_key_hash_combine(
		out,
		template_key_string_hash(argument.value_name));
	out = template_key_hash_combine(
		out,
		template_key_string_hash(argument.template_name));
	out = template_key_hash_combine(
		out,
		template_key_string_hash(argument.value_owner_template_name));
	out = template_key_hash_combine(
		out,
		template_key_string_hash(argument.value_member_name));
	out = template_key_hash_combine(out, argument.pack.size());
	out = template_key_hash_combine(
		out,
		argument.value_owner_template_arguments.size());
	if (depth > 8)
		return template_key_hash_combine(out, 0x51a7e);
	out = template_key_hash_combine(
		out,
		template_type_cache_hash(argument.type, depth + 1));
	for (size_t i = 0; i < argument.pack.size(); ++i)
		out = template_key_hash_combine(
			out,
			instance_argument_cache_hash(argument.pack[i], depth + 1));
	for (size_t i = 0; i < argument.value_owner_template_arguments.size(); ++i)
		out = template_key_hash_combine(
			out,
			instance_argument_cache_hash(
				argument.value_owner_template_arguments[i],
				depth + 1));
	return out;
}
size_t template_type_cache_hash(TypePtr type, int depth)
{
	if (type.get() == NULL)
		return 0;
	size_t out = static_cast<size_t>(type->kind);
	out = template_key_hash_combine(out, type->fundamental);
	out = template_key_hash_combine(out, type->cv);
	out = template_key_hash_combine(out, type->ref_qualifier);
	out = template_key_hash_combine(
		out,
		reinterpret_cast<uintptr_t>(type->base.get()));
	out = template_key_hash_combine(
		out,
		reinterpret_cast<uintptr_t>(type->member_class.get()));
	out = template_key_hash_combine(out, type->unknown_bound);
	out = template_key_hash_combine(out, type->bound);
	out = template_key_hash_combine(out, template_key_string_hash(type->name));
	out = template_key_hash_combine(
		out,
		template_key_string_hash(type->template_primary_name));
	out = template_key_hash_combine(
		out,
		reinterpret_cast<uintptr_t>(type->scope));
	out = template_key_hash_combine(out, type->is_template_specialization);
	out = template_key_hash_combine(out, type->is_extern_template_instantiation);
	out = template_key_hash_combine(out, type->is_dependent_typename);
	out = template_key_hash_combine(out, type->parameters.size());
	out = template_key_hash_combine(out, type->template_arguments.size());
	out = template_key_hash_combine(
		out,
		type->dependent_typename_template_argument_lists.size());
	if (depth > 8)
		return template_key_hash_combine(out, 0x62b31);
	out = template_key_hash_combine(
		out,
		template_type_cache_hash(type->base, depth + 1));
	out = template_key_hash_combine(
		out,
		template_type_cache_hash(type->member_class, depth + 1));
	for (size_t i = 0; i < type->parameters.size(); ++i)
	{
		TypePtr param = type->parameters[i].get() != NULL
			? pa11::strip_cv(type->parameters[i]) : TypePtr();
		out = template_key_hash_combine(
			out,
			reinterpret_cast<uintptr_t>(type->parameters[i].get()));
		out = template_key_hash_combine(
			out,
			param.get() != NULL ? static_cast<size_t>(param->kind)
			                    : static_cast<size_t>(-1));
		out = template_key_hash_combine(
			out,
			param.get() != NULL ? template_key_string_hash(param->name) : 0);
		out = template_key_hash_combine(
			out,
			param.get() != NULL
			? template_key_string_hash(param->template_primary_name)
			: 0);
		out = template_key_hash_combine(
			out,
			template_type_cache_hash(type->parameters[i], depth + 1));
	}
	for (size_t i = 0; i < type->template_arguments.size(); ++i)
		out = template_key_hash_combine(
			out,
			instance_argument_cache_hash(type->template_arguments[i],
			                             depth + 1));
	for (size_t i = 0;
	     i < type->dependent_typename_template_argument_lists.size();
	     ++i)
	{
		out = template_key_hash_combine(
			out,
			type->dependent_typename_template_argument_lists[i].size());
		for (size_t j = 0;
		     j < type->dependent_typename_template_argument_lists[i].size();
		     ++j)
			out = template_key_hash_combine(
				out,
				instance_argument_cache_hash(
					type->dependent_typename_template_argument_lists[i][j],
					depth + 1));
	}
	return out;
}
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
string template_instance_argument_lists_key(
	const vector<vector<pa11::TemplateInstanceArgument> >& lists)
{
	ostringstream out;
	for (size_t i = 0; i < lists.size(); ++i)
	{
		if (i != 0)
			out << ";";
		out << "[" << template_instance_argument_pack_key(lists[i])
		    << "]";
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
		vector<size_t>& active = template_type_key_active_stack();
		size_t active_key = reinterpret_cast<size_t>(type.get());
		if (find(active.begin(), active.end(), active_key) != active.end())
			return template_type_key_placeholder(type, "cycle");
		if (active.size() > 32)
			return template_type_key_placeholder(type, "depth");
		struct ActiveTemplateTypeKey
		{
			vector<size_t>& active;
			explicit ActiveTemplateTypeKey(vector<size_t>& a,
			                               size_t key)
				: active(a)
			{
				active.push_back(key);
			}
			~ActiveTemplateTypeKey()
			{
				active.pop_back();
			}
		} active_type_key(active, active_key);
		map<const void*, pair<size_t, string> >& cache =
			template_type_key_cache();
		map<const void*, pair<size_t, string> >::const_iterator cached =
			cache.find(type.get());
		if (cached != cache.end() && cached->second.second.size() > 4096)
			return cached->second.second;
		size_t fingerprint = template_type_cache_hash(type, 0);
	if (cached != cache.end() && cached->second.first == fingerprint)
		return cached->second.second;
	string result;
	if (type->is_dependent_typename)
	{
		ostringstream out;
		out << "dep(" << static_cast<int>(type->kind) << "|"
		    << type->name << "|" << type->template_primary_name << "|"
		    << type->dependent_typename_qualified << "|"
		    << type->dependent_typename_template_id << "|"
		    << type->dependent_typename_decltype << "<"
		    << template_instance_argument_pack_key(type->template_arguments)
		    << ">["
		    << template_instance_argument_lists_key(
			       type->dependent_typename_template_argument_lists)
		    << "])";
		result = out.str();
		remember_template_type_key(type, fingerprint, result);
		return result;
	}
	switch (type->kind)
	{
	case pa11::TypeKind::Cv:
		result = "cv(" + to_string(type->cv) + "," +
		         template_type_key(type->base) + ")";
		break;
	case pa11::TypeKind::Pointer:
		result = "ptr(" + template_type_key(type->base) + ")";
		break;
	case pa11::TypeKind::LValueReference:
		result = "lref(" + template_type_key(type->base) + ")";
		break;
	case pa11::TypeKind::RValueReference:
		result = "rref(" + template_type_key(type->base) + ")";
		break;
	case pa11::TypeKind::Array:
		result = string("array(") +
		         (type->unknown_bound ? "?" : to_string(type->bound)) + "," +
		         template_type_key(type->base) + ")";
		break;
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
		result = out.str();
		break;
	}
	case pa11::TypeKind::MemberPointer:
		result = "memptr(" + template_type_key(type->member_class) + "," +
		         template_type_key(type->base) + ")";
		break;
		case pa11::TypeKind::Record:
		case pa11::TypeKind::Enum:
		{
			if (type->kind == pa11::TypeKind::Record &&
			    type->is_template_specialization)
			{
				result = "spec(" + type->template_primary_name +
				         "<" +
				         template_instance_argument_pack_key(
					         type->template_arguments) +
				         ">)";
				break;
			}
			ostringstream out;
			out << template_type_spelling(type) << "@" << type.get();
			result = out.str();
			break;
		}
	default:
		result = template_type_spelling(type);
		break;
	}
	remember_template_type_key(type, fingerprint, result);
	return result;
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
	static map<const TemplateArgument*, pair<size_t, string> > cache;
	size_t fingerprint =
		dependent_cache_template_argument_identity(argument, 0);
	map<const TemplateArgument*, pair<size_t, string> >::const_iterator cached =
		cache.find(&argument);
	if (cached != cache.end() && cached->second.first == fingerprint)
		return cached->second.second;
	string result;
	if (argument.kind == TemplateArgumentKind::Type)
		result = string(argument.pack_expansion ? "TE(" : "T(") +
		         template_type_key(argument.type) + ")";
	else if (argument.kind == TemplateArgumentKind::Value)
	{
		if (argument.value_binding != NULL)
			result = string(argument.pack_expansion ? "VE(" : "V(") +
			         template_type_key(argument.type) + ",B@" +
			         to_string(reinterpret_cast<uintptr_t>(
				         argument.value_binding)) + ")";
		else
		{
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
			result = out.str();
		}
	}
	else if (argument.kind == TemplateArgumentKind::Template)
	{
		ostringstream out;
		out << (argument.pack_expansion ? "ME(" : "M(")
		    << (argument.template_declaration != NULL
		        ? argument.template_declaration->owner : NULL)
		    << ":" << (argument.template_declaration != NULL
		               ? argument.template_declaration->name
		               : string("<dependent>") + argument.value_name)
		    << ":" << argument.template_declaration << ")";
		result = out.str();
	}
	else
	{
		ostringstream out;
		out << "P(";
		for (size_t i = 0; i < argument.pack.size(); ++i)
		{
			if (i != 0)
				out << ",";
			out << template_argument_key_part(argument.pack[i]);
		}
		out << ")";
		result = out.str();
	}
	cache[&argument] = make_pair(fingerprint, result);
	return result;
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
bool instance_pack_needs_dependency_name(
	const vector<pa11::TemplateInstanceArgument>& pack)
{
	for (size_t i = 0; i < pack.size(); ++i)
		if (instance_argument_structurally_dependent(pack[i]))
			return true;
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
	if (!argument.value_name.empty() &&
	    instance_pack_needs_dependency_name(pack))
	{
		out.value_name = argument.value_name;
		out.template_name = argument.value_name;
	}
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
