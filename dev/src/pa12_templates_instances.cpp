#include "pa12_internal.h"

#include <algorithm>
#include <sstream>
#include <stdexcept>

using namespace std;

namespace pa12 {
namespace internal {
namespace {

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
		out << "fn(";
		for (size_t i = 0; i < type->parameters.size(); ++i)
		{
			if (i != 0)
				out << ",";
			out << template_type_key(type->parameters[i]);
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
		        : string("template-parameter")) +
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
		return string(argument.pack_expansion ? "VE(" : "V(") +
		       template_type_key(argument.type) + "," +
		       (argument.dependent ? string("?") :
		        to_string(argument.value)) + ")";
	if (argument.kind == TemplateArgumentKind::Template)
	{
		ostringstream out;
		out << (argument.pack_expansion ? "ME(" : "M(")
		    << (argument.template_declaration != NULL
		        ? argument.template_declaration->owner : NULL)
		    << ":" << (argument.template_declaration != NULL
		               ? argument.template_declaration->name
		               : string("<dependent>"))
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

pa11::TemplateInstanceArgument template_instance_argument(
	const TemplateArgument& argument)
{
	if (argument.kind == TemplateArgumentKind::Type)
		return pa11::TemplateInstanceArgument::type_arg(argument.type);
	if (argument.kind == TemplateArgumentKind::Value)
	{
		if (argument.dependent)
			return pa11::TemplateInstanceArgument::dependent_value_arg(
				argument.type);
		return pa11::TemplateInstanceArgument::value_arg(argument.type,
		                                                argument.value);
	}
	if (argument.kind == TemplateArgumentKind::Template)
		return pa11::TemplateInstanceArgument::template_arg(
			argument.template_declaration != NULL
			? argument.template_declaration->name
			: string("template_parameter"));
	vector<pa11::TemplateInstanceArgument> pack;
	for (size_t i = 0; i < argument.pack.size(); ++i)
		pack.push_back(template_instance_argument(argument.pack[i]));
	return pa11::TemplateInstanceArgument::pack_arg(pack);
}

vector<pa11::TemplateInstanceArgument> template_instance_arguments(
	const vector<TemplateArgument>& arguments)
{
	vector<pa11::TemplateInstanceArgument> out;
	for (size_t i = 0; i < arguments.size(); ++i)
		out.push_back(template_instance_argument(arguments[i]));
	return out;
}

bool same_template_argument_value(
	const TemplateArgument& left,
	const TemplateArgument& right,
	const map<const void*, vector<TemplateArgument> >& record_arguments);

bool match_template_argument_pattern(
	const TemplateArgument& pattern,
	const TemplateArgument& actual,
	map<string, TemplateArgument>& deduced,
	const map<const void*, vector<TemplateArgument> >& record_arguments);

bool same_template_record_primary(TypePtr left, TypePtr right)
{
	if (!left->is_template_specialization ||
	    !right->is_template_specialization)
		return false;
	if (left->template_primary_name != right->template_primary_name)
		return false;
	Scope* left_owner = left->scope != NULL ? left->scope->parent : NULL;
	Scope* right_owner = right->scope != NULL ? right->scope->parent : NULL;
	return left_owner == right_owner;
}

bool match_template_type_pattern(
	TypePtr pattern,
	TypePtr actual,
	map<string, TemplateArgument>& deduced,
	const map<const void*, vector<TemplateArgument> >& record_arguments)
{
	if (pattern.get() == NULL || actual.get() == NULL)
		return pattern.get() == actual.get();
	if (pattern->kind == pa11::TypeKind::TemplateParameter)
	{
		TemplateArgument arg = TemplateArgument::type_arg(actual);
		map<string, TemplateArgument>::iterator found =
			deduced.find(pattern->name);
		if (found == deduced.end())
		{
			deduced[pattern->name] = arg;
			return true;
		}
		return same_template_argument_value(found->second,
		                                    arg,
		                                    record_arguments);
	}
	if (pattern->kind != actual->kind)
		return false;
	switch (pattern->kind)
	{
	case pa11::TypeKind::Fundamental:
		return pattern->fundamental == actual->fundamental;
	case pa11::TypeKind::Cv:
		return pattern->cv == actual->cv &&
		       match_template_type_pattern(pattern->base,
		                                   actual->base,
		                                   deduced,
		                                   record_arguments);
	case pa11::TypeKind::Pointer:
	case pa11::TypeKind::LValueReference:
	case pa11::TypeKind::RValueReference:
		return match_template_type_pattern(pattern->base,
		                                   actual->base,
		                                   deduced,
		                                   record_arguments);
	case pa11::TypeKind::Array:
		return pattern->unknown_bound == actual->unknown_bound &&
		       pattern->bound == actual->bound &&
		       match_template_type_pattern(pattern->base,
		                                   actual->base,
		                                   deduced,
		                                   record_arguments);
	case pa11::TypeKind::Function:
		if (pattern->cv != actual->cv ||
		    pattern->variadic != actual->variadic ||
		    pattern->parameters.size() != actual->parameters.size())
			return false;
		if (!match_template_type_pattern(pattern->base,
		                                  actual->base,
		                                  deduced,
		                                  record_arguments))
			return false;
		for (size_t i = 0; i < pattern->parameters.size(); ++i)
			if (!match_template_type_pattern(pattern->parameters[i],
			                                  actual->parameters[i],
			                                  deduced,
			                                  record_arguments))
				return false;
		return true;
	case pa11::TypeKind::MemberPointer:
		return match_template_type_pattern(pattern->member_class,
		                                   actual->member_class,
		                                   deduced,
		                                   record_arguments) &&
		       match_template_type_pattern(pattern->base,
		                                   actual->base,
		                                   deduced,
		                                   record_arguments);
	case pa11::TypeKind::Record:
	{
		if (pa11::same_type(pattern, actual))
			return true;
		if (!same_template_record_primary(pattern, actual))
			return false;
		map<const void*, vector<TemplateArgument> >::const_iterator pit =
			record_arguments.find(pattern.get());
		map<const void*, vector<TemplateArgument> >::const_iterator ait =
			record_arguments.find(actual.get());
		if (pit == record_arguments.end() ||
		    ait == record_arguments.end() ||
		    pit->second.size() != ait->second.size())
			return false;
		for (size_t i = 0; i < pit->second.size(); ++i)
			if (!match_template_argument_pattern(pit->second[i],
			                                      ait->second[i],
			                                      deduced,
			                                      record_arguments))
				return false;
		return true;
	}
	case pa11::TypeKind::Enum:
	case pa11::TypeKind::TemplateTemplateParameter:
		return pa11::same_type(pattern, actual);
	case pa11::TypeKind::TemplateParameter:
		break;
	}
	throw logic_error("unknown type kind");
}

bool same_template_argument_value(
	const TemplateArgument& left,
	const TemplateArgument& right,
	const map<const void*, vector<TemplateArgument> >& record_arguments)
{
	if (left.kind != right.kind)
		return false;
	if (left.kind == TemplateArgumentKind::Type)
	{
		map<string, TemplateArgument> deduced;
		return match_template_type_pattern(left.type,
		                                   right.type,
		                                   deduced,
		                                   record_arguments) &&
		       deduced.empty();
	}
	if (left.kind == TemplateArgumentKind::Value)
		return !left.dependent && !right.dependent &&
		       left.value == right.value &&
		       (left.type.get() == NULL || right.type.get() == NULL ||
		        pa11::same_type(left.type, right.type));
	if (left.kind == TemplateArgumentKind::Template)
		return left.template_declaration == right.template_declaration;
	if (left.pack.size() != right.pack.size())
		return false;
	for (size_t i = 0; i < left.pack.size(); ++i)
		if (!same_template_argument_value(left.pack[i],
		                                  right.pack[i],
		                                  record_arguments))
			return false;
	return true;
}

bool match_template_argument_pattern(
	const TemplateArgument& pattern,
	const TemplateArgument& actual,
	map<string, TemplateArgument>& deduced,
	const map<const void*, vector<TemplateArgument> >& record_arguments)
{
	if (pattern.kind == TemplateArgumentKind::Type &&
	    pattern.type.get() != NULL &&
	    pattern.type->kind == pa11::TypeKind::TemplateParameter)
	{
		map<string, TemplateArgument>::iterator found =
			deduced.find(pattern.type->name);
		if (found == deduced.end())
		{
			deduced[pattern.type->name] = actual;
			return true;
		}
		return same_template_argument_value(found->second,
		                                    actual,
		                                    record_arguments);
	}
	if (pattern.kind != actual.kind)
		return false;
	if (pattern.kind == TemplateArgumentKind::Type)
		return match_template_type_pattern(pattern.type,
		                                   actual.type,
		                                   deduced,
		                                   record_arguments);
	if (pattern.kind == TemplateArgumentKind::Value)
		return !pattern.dependent && !actual.dependent &&
		       pattern.value == actual.value;
	if (pattern.kind == TemplateArgumentKind::Template)
		return pattern.template_declaration == actual.template_declaration;
	if (pattern.pack.size() != actual.pack.size())
		return false;
	for (size_t i = 0; i < pattern.pack.size(); ++i)
		if (!match_template_argument_pattern(pattern.pack[i],
		                                     actual.pack[i],
		                                     deduced,
		                                     record_arguments))
			return false;
	return true;
}

bool match_class_specialization(TemplateDeclaration* specialization,
                                const vector<TemplateArgument>& full_args,
                                vector<TemplateArgument>& selected_args,
                                const map<const void*, vector<TemplateArgument> >&
                                        record_arguments)
{
	if (specialization->class_specialization_pattern.size() != full_args.size())
		return false;
	map<string, TemplateArgument> deduced;
	for (size_t i = 0; i < full_args.size(); ++i)
		if (!match_template_argument_pattern(
			    specialization->class_specialization_pattern[i],
			    full_args[i],
			    deduced,
			    record_arguments))
			return false;
	for (size_t i = 0; i < specialization->parameters.size(); ++i)
	{
		const string& name = specialization->parameters[i].name;
		map<string, TemplateArgument>::iterator found = deduced.find(name);
		if (found == deduced.end())
			return false;
		selected_args.push_back(found->second);
	}
	return true;
}

}  // namespace

string Parser::template_argument_key(
	const vector<TemplateArgument>& arguments) const
{
	ostringstream out;
	for (size_t i = 0; i < arguments.size(); ++i)
	{
		if (i != 0)
			out << ",";
		out << template_argument_key_part(arguments[i]);
	}
	return out.str();
}

string Parser::template_specialization_name(
	TemplateDeclaration* declaration,
	const vector<TemplateArgument>& arguments) const
{
	return declaration->name + "<" + template_argument_spelling(arguments) + ">";
}

TemplateDeclaration* Parser::find_class_template(Scope* scope,
                                                 const string& name)
{
	if (scope != NULL)
	{
		map<Scope*, map<string, TemplateDeclaration*> >::iterator sit =
			class_templates_.find(scope);
		if (sit != class_templates_.end())
		{
			map<string, TemplateDeclaration*>::iterator it =
				sit->second.find(name);
			if (it != sit->second.end())
				return it->second;
		}
		for (size_t i = 0; i < scope->using_directives.size(); ++i)
		{
			TemplateDeclaration* found =
				find_class_template(scope->using_directives[i], name);
			if (found != NULL)
				return found;
		}
		return NULL;
	}
	for (Scope* cur = current_scope(); cur != NULL; cur = cur->parent)
	{
		TemplateDeclaration* found = find_class_template(cur, name);
		if (found != NULL)
			return found;
	}
	return NULL;
}

TemplateDeclaration* Parser::find_alias_template(Scope* scope,
                                                 const string& name)
{
	if (scope != NULL)
	{
		map<Scope*, map<string, TemplateDeclaration*> >::iterator sit =
			alias_templates_.find(scope);
		if (sit != alias_templates_.end())
		{
			map<string, TemplateDeclaration*>::iterator it =
				sit->second.find(name);
			if (it != sit->second.end())
				return it->second;
		}
		for (size_t i = 0; i < scope->using_directives.size(); ++i)
		{
			TemplateDeclaration* found =
				find_alias_template(scope->using_directives[i], name);
			if (found != NULL)
				return found;
		}
		return NULL;
	}
	for (Scope* cur = current_scope(); cur != NULL; cur = cur->parent)
	{
		TemplateDeclaration* found = find_alias_template(cur, name);
		if (found != NULL)
			return found;
	}
	return NULL;
}

TypePtr Parser::instantiate_alias_template(
	TemplateDeclaration* declaration,
	const vector<TemplateArgument>& arguments)
{
	vector<TemplateArgument> full_args =
		complete_template_arguments(declaration, arguments);
	size_t save_pos = pos_;
	vector<Scope*> save_scopes = scopes_;
	vector<map<string, TypePtr> > save_subst = template_type_substitutions_;
	vector<map<string, TemplateArgument> > save_value_subst =
		template_value_substitutions_;
	map<string, TypePtr> subst;
	map<string, TemplateArgument> value_subst;
	for (size_t i = 0; i < full_args.size() &&
	     i < declaration->parameters.size(); ++i)
		if (!declaration->parameters[i].name.empty())
		{
			if (declaration->parameters[i].kind ==
			    TemplateParameterKind::Type)
			{
				if (declaration->parameters[i].is_pack)
				{
					subst[declaration->parameters[i].name] =
						pa11::make_template_parameter_type(
							declaration->parameters[i].name);
					value_subst[declaration->parameters[i].name] =
						full_args[i];
				}
				else
					subst[declaration->parameters[i].name] =
						full_args[i].type;
			}
			else
				value_subst[declaration->parameters[i].name] =
					full_args[i];
		}
	template_type_substitutions_.push_back(subst);
	template_value_substitutions_.push_back(value_subst);
	scopes_.clear();
	scopes_.push_back(declaration->lexical_scope != NULL
	                  ? declaration->lexical_scope
	                  : declaration->owner);
	pos_ = declaration->decl_begin;
	TypePtr type;
	try
	{
		expect(KW_USING);
		consume_identifier();
		expect(OP_ASS);
		type = parse_type_id();
		expect(OP_SEMICOLON);
	}
	catch (...)
	{
		template_type_substitutions_ = save_subst;
		template_value_substitutions_ = save_value_subst;
		scopes_ = save_scopes;
		pos_ = save_pos;
		throw;
	}
	template_type_substitutions_ = save_subst;
	template_value_substitutions_ = save_value_subst;
	scopes_ = save_scopes;
	pos_ = save_pos;
	return type;
}

TypePtr Parser::instantiate_class_template(
	TemplateDeclaration* declaration,
	const vector<TemplateArgument>& arguments)
{
	vector<TemplateArgument> full_args =
		complete_template_arguments(declaration, arguments);
	TemplateDeclaration* selected_declaration = declaration;
	vector<TemplateArgument> selected_args = full_args;
	for (size_t i = 0; i < declaration->class_specialization_declarations.size(); ++i)
	{
		TemplateDeclaration* candidate =
			declaration->class_specialization_declarations[i];
		vector<TemplateArgument> candidate_args;
		if (match_class_specialization(candidate,
		                               full_args,
		                               candidate_args,
		                               record_template_arguments_))
		{
			selected_declaration = candidate;
			selected_args = candidate_args;
		}
	}
	bool dependent = false;
	for (size_t i = 0; i < full_args.size(); ++i)
		if (template_argument_has_template_parameter(
			    full_args[i],
			    record_template_arguments_))
			dependent = true;
	string key = template_argument_key(full_args);
	map<string, TypePtr>::iterator existing =
		declaration->class_specializations.find(key);
	if (existing != declaration->class_specializations.end())
	{
		if (!dependent)
			complete_template_record(existing->second);
		return existing->second;
	}

	string special_name = template_specialization_name(declaration, full_args);
	Scope* class_scope =
		pa11::create_child_scope(declaration->owner,
		                         ScopeKind::Class,
		                         declaration->name);
	TypePtr type =
		pa11::make_record_type(scoped_type_display_name(declaration->owner,
		                                                special_name),
		                       selected_declaration->tag.empty()
		                       ? (declaration->tag.empty() ? "struct" :
		                          declaration->tag)
		                       : selected_declaration->tag,
		                       false,
		                       class_scope);
	type->is_template_specialization = true;
	type->template_primary_name = declaration->name;
	type->template_arguments = template_instance_arguments(full_args);
	Binding* binding =
		pa11::add_binding(declaration->owner,
		                  BindingKind::Type,
		                  special_name,
		                  type);
	binding->target_scope = class_scope;
	Binding* injected =
		pa11::add_binding(class_scope,
		                  BindingKind::Type,
		                  declaration->name,
		                  type);
	injected->target_scope = class_scope;
	declaration->class_specializations[key] = type;
	record_template_declarations_[type.get()] = selected_declaration;
	record_template_arguments_[type.get()] = selected_args;
	if (!dependent)
		complete_template_record(type);
	return type;
}

void Parser::complete_template_record(TypePtr type)
{
	TypePtr bare = pa11::strip_cv(type);
	if (bare->kind != pa11::TypeKind::Record || bare->complete)
		return;
	map<const void*, TemplateDeclaration*>::iterator found =
		record_template_declarations_.find(bare.get());
	if (found == record_template_declarations_.end())
		return;
	TemplateDeclaration* declaration = found->second;
	if (!declaration->has_definition)
		return;
	vector<TemplateArgument> args = record_template_arguments_[bare.get()];
	bool dependent = false;
	for (size_t i = 0; i < args.size(); ++i)
		if (template_argument_has_template_parameter(
			    args[i],
			    record_template_arguments_))
			dependent = true;
	string key = template_argument_key(args);
	if (declaration->completing_specializations.count(key) != 0)
		return;
	declaration->completing_specializations.insert(key);

	size_t save_pos = pos_;
	vector<Scope*> save_scopes = scopes_;
	vector<map<string, TypePtr> > save_subst = template_type_substitutions_;
	vector<map<string, TemplateArgument> > save_value_subst =
		template_value_substitutions_;
	map<string, TypePtr> subst;
	map<string, TemplateArgument> value_subst;
	for (size_t i = 0; i < args.size() && i < declaration->parameters.size(); ++i)
		if (!declaration->parameters[i].name.empty())
		{
			if (declaration->parameters[i].kind ==
			    TemplateParameterKind::Type)
			{
				if (declaration->parameters[i].is_pack)
				{
					subst[declaration->parameters[i].name] =
						pa11::make_template_parameter_type(
							declaration->parameters[i].name);
					value_subst[declaration->parameters[i].name] =
						args[i];
				}
				else
					subst[declaration->parameters[i].name] =
						args[i].type;
			}
			else
				value_subst[declaration->parameters[i].name] = args[i];
		}
	template_type_substitutions_.push_back(subst);
	template_value_substitutions_.push_back(value_subst);
	active_class_instantiations_.push_back(
		ActiveClassInstantiation(
			declaration,
			template_specialization_name(declaration, args),
			bare));
	scopes_.clear();
	scopes_.push_back(declaration->lexical_scope != NULL
	                  ? declaration->lexical_scope
	                  : declaration->owner);
	pos_ = declaration->decl_begin;
	try
	{
		TypePtr parsed = parse_class_specifier();
		(void)parsed;
	}
	catch (const runtime_error& err)
	{
		active_class_instantiations_.pop_back();
		template_type_substitutions_ = save_subst;
		template_value_substitutions_ = save_value_subst;
		scopes_ = save_scopes;
		pos_ = save_pos;
		declaration->completing_specializations.erase(key);
		if (dependent &&
		    (string(err.what()) == "incomplete object type" ||
		     string(err.what()) == "incomplete class type" ||
		     string(err.what()) == "no matching constructor" ||
		     string(err.what()) == "invalid initializer conversion"))
			return;
		throw;
	}
	catch (...)
	{
		active_class_instantiations_.pop_back();
		template_type_substitutions_ = save_subst;
		template_value_substitutions_ = save_value_subst;
		scopes_ = save_scopes;
		pos_ = save_pos;
		declaration->completing_specializations.erase(key);
		throw;
	}
	active_class_instantiations_.pop_back();
	template_type_substitutions_ = save_subst;
	template_value_substitutions_ = save_value_subst;
	scopes_ = save_scopes;
	pos_ = save_pos;
	declaration->completing_specializations.erase(key);
	instantiate_member_function_templates(type);
	instantiate_member_variable_templates(type);
}

void Parser::complete_member_class_template_record(Binding* binding)
{
	if (binding == NULL || binding->type.get() == NULL)
		return;
	TypePtr bare = pa11::strip_cv(binding->type);
	if (bare->kind != pa11::TypeKind::Record ||
	    (bare->complete && bare->scope != NULL))
		return;
	TypePtr owner_record = binding->owner != NULL
		? pa11::record_type_for_scope(binding->owner) : TypePtr();
	if (owner_record.get() == NULL)
		return;
	owner_record = pa11::strip_cv(owner_record);
	map<const void*, TemplateDeclaration*>::iterator outer =
		record_template_declarations_.find(owner_record.get());
	if (outer == record_template_declarations_.end())
		return;
	map<pair<TemplateDeclaration*, string>, TemplateDeclaration*>::iterator found =
		member_class_templates_.find(make_pair(outer->second, binding->name));
	TemplateDeclaration* declaration = found != member_class_templates_.end()
		? found->second : NULL;
	if (declaration == NULL)
	{
		for (map<pair<TemplateDeclaration*, string>,
		         TemplateDeclaration*>::iterator it =
			     member_class_templates_.begin();
		     it != member_class_templates_.end();
		     ++it)
		{
			TemplateDeclaration* candidate_outer = it->first.first;
			if (it->first.second == binding->name &&
			    candidate_outer != NULL &&
			    candidate_outer->name == outer->second->name &&
			    candidate_outer->owner == outer->second->owner)
			{
				declaration = it->second;
				break;
			}
		}
	}
	if (declaration == NULL)
		return;
	if (!declaration->has_definition)
		return;
	vector<TemplateArgument> args = record_template_arguments_[owner_record.get()];
	string key = template_argument_key(args) + "::" + binding->name;
	if (declaration->completing_specializations.count(key) != 0)
		return;
	declaration->completing_specializations.insert(key);

	size_t save_pos = pos_;
	vector<Scope*> save_scopes = scopes_;
	vector<map<string, TypePtr> > save_subst = template_type_substitutions_;
	vector<map<string, TemplateArgument> > save_value_subst =
		template_value_substitutions_;
	map<string, TypePtr> subst;
	map<string, TemplateArgument> value_subst;
	for (size_t i = 0; i < args.size() && i < declaration->parameters.size(); ++i)
		if (!declaration->parameters[i].name.empty())
		{
			if (declaration->parameters[i].kind ==
			    TemplateParameterKind::Type)
			{
				if (declaration->parameters[i].is_pack)
				{
					subst[declaration->parameters[i].name] =
						pa11::make_template_parameter_type(
							declaration->parameters[i].name);
					value_subst[declaration->parameters[i].name] =
						args[i];
				}
				else
					subst[declaration->parameters[i].name] =
						args[i].type;
			}
			else
				value_subst[declaration->parameters[i].name] = args[i];
		}
	template_type_substitutions_.push_back(subst);
	template_value_substitutions_.push_back(value_subst);
	scopes_.clear();
	scopes_.push_back(declaration->lexical_scope != NULL
	                  ? declaration->lexical_scope
	                  : declaration->owner);
	pos_ = declaration->decl_begin;
	TypePtr parsed = parse_class_specifier();
	TypePtr parsed_bare = pa11::strip_cv(parsed);
	if (!bare->complete &&
	    parsed_bare.get() != NULL &&
	    parsed_bare->kind == pa11::TypeKind::Record &&
	    parsed_bare->complete &&
	    parsed_bare->scope != NULL)
	{
		*bare = *parsed_bare;
		binding->target_scope = bare->scope;
	}
	template_type_substitutions_ = save_subst;
	template_value_substitutions_ = save_value_subst;
	scopes_ = save_scopes;
	pos_ = save_pos;
	declaration->completing_specializations.erase(key);
}

void Parser::instantiate_member_function_templates(TypePtr type)
{
	TypePtr bare = pa11::strip_cv(type);
	if (bare->kind != pa11::TypeKind::Record)
		return;
	map<const void*, TemplateDeclaration*>::iterator outer =
		record_template_declarations_.find(bare.get());
	if (outer == record_template_declarations_.end())
		return;
	map<const void*, vector<TemplateArgument> >::iterator args_it =
		record_template_arguments_.find(bare.get());
	if (args_it == record_template_arguments_.end())
		return;
	for (map<pair<TemplateDeclaration*, string>,
	         vector<TemplateDeclaration*> >::iterator it =
		     member_function_templates_.begin();
	     it != member_function_templates_.end();
	     ++it)
	{
		if (it->first.first != outer->second)
		{
			TemplateDeclaration* candidate = it->first.first;
			if (candidate == NULL ||
			    candidate->name != outer->second->name ||
			    candidate->owner != outer->second->owner)
				continue;
		}
		for (size_t i = 0; i < it->second.size(); ++i)
		{
			string key = template_argument_key(args_it->second);
			if (it->second[i]->completing_specializations.count(key) != 0)
				continue;
			instantiate_function_template(it->second[i], args_it->second);
		}
	}
}

void Parser::instantiate_member_variable_templates(TypePtr type)
{
	TypePtr bare = pa11::strip_cv(type);
	if (bare->kind != pa11::TypeKind::Record)
		return;
	map<const void*, TemplateDeclaration*>::iterator outer =
		record_template_declarations_.find(bare.get());
	if (outer == record_template_declarations_.end())
		return;
	map<const void*, vector<TemplateArgument> >::iterator args_it =
		record_template_arguments_.find(bare.get());
	if (args_it == record_template_arguments_.end())
		return;
	for (map<pair<TemplateDeclaration*, string>,
	         vector<TemplateDeclaration*> >::iterator it =
		     member_variable_templates_.begin();
	     it != member_variable_templates_.end();
	     ++it)
	{
		if (it->first.first != outer->second)
			continue;
		bool owner_has_nontype_parameter = false;
		for (size_t i = 0; i < outer->second->parameters.size(); ++i)
			if (outer->second->parameters[i].kind ==
			    TemplateParameterKind::NonType)
				owner_has_nontype_parameter = true;
		for (size_t i = 0; i < it->second.size(); ++i)
		{
			TemplateDeclaration* declaration = it->second[i];
			string key = template_argument_key(args_it->second) +
			             "::" + declaration->name;
			if (!declaration->emitted_variable_specializations.insert(key).second)
				continue;
			size_t save_pos = pos_;
			vector<Scope*> save_scopes = scopes_;
			vector<map<string, TypePtr> > save_subst =
				template_type_substitutions_;
			vector<map<string, TemplateArgument> > save_value_subst =
				template_value_substitutions_;
			map<string, TypePtr> subst;
			map<string, TemplateArgument> value_subst;
			for (size_t j = 0; j < args_it->second.size() &&
			     j < declaration->parameters.size(); ++j)
				if (!declaration->parameters[j].name.empty())
				{
					if (declaration->parameters[j].kind ==
					    TemplateParameterKind::Type)
					{
						if (declaration->parameters[j].is_pack)
						{
							subst[declaration->parameters[j].name] =
								pa11::make_template_parameter_type(
									declaration->parameters[j].name);
							value_subst[declaration->parameters[j].name] =
								args_it->second[j];
						}
						else
							subst[declaration->parameters[j].name] =
								args_it->second[j].type;
					}
					else
						value_subst[declaration->parameters[j].name] =
							args_it->second[j];
				}
			template_type_substitutions_.push_back(subst);
			template_value_substitutions_.push_back(value_subst);
			scopes_.clear();
			scopes_.push_back(declaration->lexical_scope != NULL
			                  ? declaration->lexical_scope
			                  : declaration->owner);
			pos_ = declaration->decl_begin;
			Node node;
			parse_simple_or_function_declaration(node, true);
			if (!node.line.empty())
			{
				if (node.binding != NULL &&
				    node.binding->is_static_member &&
				    (!owner_has_nontype_parameter ||
				     node.children.empty()))
					add_child(root_, node);
			}
			else
				for (size_t j = 0; j < node.children.size(); ++j)
					if (node.children[j].binding != NULL &&
					    node.children[j].binding->is_static_member &&
					    (!owner_has_nontype_parameter ||
					     node.children[j].children.empty()))
						add_child(root_, node.children[j]);
			template_type_substitutions_ = save_subst;
			template_value_substitutions_ = save_value_subst;
			scopes_ = save_scopes;
			pos_ = save_pos;
		}
	}
}

bool Parser::type_is_template_dependent(TypePtr type) const
{
	return template_type_has_template_parameter(type,
	                                           record_template_arguments_);
}

TypePtr Parser::substitute_template_type_parameter(TypePtr type,
                                                   const string& name,
                                                   TypePtr replacement) const
{
	if (type.get() == NULL)
		return type;
	if (type->kind == pa11::TypeKind::TemplateParameter &&
	    type->name == name)
		return replacement;
	if (type->kind == pa11::TypeKind::Cv)
		return pa11::make_cv(
			substitute_template_type_parameter(type->base,
			                                   name,
			                                   replacement),
			type->cv);
	if (type->kind == pa11::TypeKind::Pointer)
		return pa11::make_pointer(
			substitute_template_type_parameter(type->base,
			                                   name,
			                                   replacement));
	if (type->kind == pa11::TypeKind::LValueReference)
	{
		TypePtr base = substitute_template_type_parameter(type->base,
		                                                  name,
		                                                  replacement);
		if (base->kind == pa11::TypeKind::LValueReference ||
		    base->kind == pa11::TypeKind::RValueReference)
			return pa11::make_lvalue_reference(base->base);
		return pa11::make_lvalue_reference(base);
	}
	if (type->kind == pa11::TypeKind::RValueReference)
	{
		TypePtr base = substitute_template_type_parameter(type->base,
		                                                  name,
		                                                  replacement);
		if (base->kind == pa11::TypeKind::LValueReference)
			return base;
		if (base->kind == pa11::TypeKind::RValueReference)
			return pa11::make_rvalue_reference(base->base);
		return pa11::make_rvalue_reference(base);
	}
	if (type->kind == pa11::TypeKind::Array)
		return pa11::make_array(
			substitute_template_type_parameter(type->base,
			                                   name,
			                                   replacement),
			type->unknown_bound,
			type->bound);
	if (type->kind == pa11::TypeKind::Function)
	{
		vector<TypePtr> params;
		for (size_t i = 0; i < type->parameters.size(); ++i)
			params.push_back(
				substitute_template_type_parameter(type->parameters[i],
				                                   name,
				                                   replacement));
		TypePtr out = pa11::make_function(
			substitute_template_type_parameter(type->base,
			                                   name,
			                                   replacement),
			params,
			type->variadic);
		out->cv = type->cv;
		return out;
	}
	if (type->kind == pa11::TypeKind::MemberPointer)
		return pa11::make_member_pointer(
			substitute_template_type_parameter(type->member_class,
			                                   name,
			                                   replacement),
			substitute_template_type_parameter(type->base,
			                                   name,
			                                   replacement));
	return type;
}

TypePtr Parser::substitute_template_type(TypePtr type) const
{
	if (type.get() == NULL)
		return type;
	if (type->kind == pa11::TypeKind::TemplateParameter)
	{
		TypePtr subst;
		if (find_template_type_substitution(type->name, subst))
			return subst;
		return type;
	}
	if (type->kind == pa11::TypeKind::Cv)
		return pa11::make_cv(substitute_template_type(type->base), type->cv);
	if (type->kind == pa11::TypeKind::Pointer)
		return pa11::make_pointer(substitute_template_type(type->base));
	if (type->kind == pa11::TypeKind::LValueReference)
	{
		TypePtr base = substitute_template_type(type->base);
		if (base->kind == pa11::TypeKind::LValueReference ||
		    base->kind == pa11::TypeKind::RValueReference)
			return pa11::make_lvalue_reference(base->base);
		return pa11::make_lvalue_reference(base);
	}
	if (type->kind == pa11::TypeKind::RValueReference)
	{
		TypePtr base = substitute_template_type(type->base);
		if (base->kind == pa11::TypeKind::LValueReference)
			return base;
		if (base->kind == pa11::TypeKind::RValueReference)
			return pa11::make_rvalue_reference(base->base);
		return pa11::make_rvalue_reference(base);
	}
	if (type->kind == pa11::TypeKind::Array)
		return pa11::make_array(substitute_template_type(type->base),
		                        type->unknown_bound,
		                        type->bound);
	if (type->kind == pa11::TypeKind::Function)
	{
		vector<TypePtr> params;
		for (size_t i = 0; i < type->parameters.size(); ++i)
			params.push_back(substitute_template_type(type->parameters[i]));
		TypePtr out = pa11::make_function(substitute_template_type(type->base),
		                                  params,
		                                  type->variadic);
		out->cv = type->cv;
		return out;
	}
	if (type->kind == pa11::TypeKind::MemberPointer)
		return pa11::make_member_pointer(
			substitute_template_type(type->member_class),
			substitute_template_type(type->base));
	return type;
}

vector<TemplateDeclaration*> Parser::find_function_templates(
	const QualifiedName& name)
{
	vector<TemplateDeclaration*> out;
	if (name.qualifier != NULL)
	{
		map<Scope*, map<string, vector<TemplateDeclaration*> > >::iterator sit =
			function_templates_.find(name.qualifier);
		if (sit != function_templates_.end())
		{
			map<string, vector<TemplateDeclaration*> >::iterator it =
				sit->second.find(name.name);
			if (it != sit->second.end())
				out = it->second;
			if (!out.empty())
				return out;
		}
		for (size_t i = 0; i < name.qualifier->using_directives.size(); ++i)
		{
			QualifiedName nested = name;
			nested.qualifier = name.qualifier->using_directives[i];
			out = find_function_templates(nested);
			if (!out.empty())
				return out;
		}
		return out;
	}
	for (Scope* cur = current_scope(); cur != NULL; cur = cur->parent)
	{
		map<Scope*, map<string, vector<TemplateDeclaration*> > >::iterator sit =
			function_templates_.find(cur);
		if (sit != function_templates_.end())
		{
			map<string, vector<TemplateDeclaration*> >::iterator it =
				sit->second.find(name.name);
			if (it != sit->second.end())
				return it->second;
		}
		for (size_t i = 0; i < cur->using_directives.size(); ++i)
		{
			QualifiedName nested = name;
			nested.qualifier = cur->using_directives[i];
			out = find_function_templates(nested);
			if (!out.empty())
				return out;
		}
	}
	return out;
}

bool Parser::visible_function_template_name(const QualifiedName& name)
{
	return !find_function_templates(name).empty();
}

vector<Binding*> Parser::instantiate_explicit_function_templates(
	const QualifiedName& name)
{
	vector<Binding*> out;
	vector<TemplateDeclaration*> declarations = find_function_templates(name);
	for (size_t i = 0; i < declarations.size(); ++i)
		out.push_back(instantiate_function_template(declarations[i],
		                                            name.template_arguments));
	return out;
}

void Parser::select_variable_template_specialization(
	TemplateDeclaration* declaration,
	const vector<TemplateArgument>& full_args,
	TemplateDeclaration*& selected_declaration,
	vector<TemplateArgument>& selected_args)
{
	map<Scope*, map<string, vector<TemplateDeclaration*> > >::iterator sit =
		variable_templates_.find(declaration->owner);
	if (sit == variable_templates_.end())
		return;
	map<string, vector<TemplateDeclaration*> >::iterator it =
		sit->second.find(declaration->name);
	if (it == sit->second.end())
		return;
	for (size_t i = 0; i < it->second.size(); ++i)
	{
		TemplateDeclaration* candidate = it->second[i];
		if (!candidate->class_specialization)
			continue;
		vector<TemplateArgument> pattern =
			candidate->class_specialization_pattern;
		if (pattern.size() != full_args.size())
		{
			try
			{
				pattern = complete_template_arguments(declaration, pattern);
			}
			catch (const runtime_error&)
			{
				continue;
			}
		}
		if (pattern.size() != full_args.size())
			continue;
		map<string, TemplateArgument> deduced;
		bool matched = true;
		for (size_t j = 0; j < full_args.size(); ++j)
			if (!match_template_argument_pattern(pattern[j],
			                                      full_args[j],
			                                      deduced,
			                                      record_template_arguments_))
				matched = false;
		if (!matched)
			continue;
		vector<TemplateArgument> candidate_args;
		for (size_t j = 0; j < candidate->parameters.size(); ++j)
		{
			const string& name = candidate->parameters[j].name;
			map<string, TemplateArgument>::iterator found = deduced.find(name);
			if (found == deduced.end())
			{
				matched = false;
				break;
			}
			candidate_args.push_back(found->second);
		}
		if (!matched)
			continue;
		selected_declaration = candidate;
		selected_args = candidate_args;
	}
}

Binding* Parser::instantiate_variable_template(
	TemplateDeclaration* declaration,
	const vector<TemplateArgument>& arguments)
{
	vector<TemplateArgument> full_args =
		complete_template_arguments(declaration, arguments);
	TemplateDeclaration* selected_declaration = declaration;
	vector<TemplateArgument> selected_args = full_args;
	select_variable_template_specialization(declaration,
	                                        full_args,
	                                        selected_declaration,
	                                        selected_args);
	string key = template_argument_key(full_args);
	Binding*& cached = variable_template_specializations_[declaration][key];
	if (cached != NULL)
		return cached;

	size_t save_pos = pos_;
	vector<Scope*> save_scopes = scopes_;
	vector<map<string, TypePtr> > save_subst = template_type_substitutions_;
	vector<map<string, TemplateArgument> > save_value_subst =
		template_value_substitutions_;
	map<string, TypePtr> subst;
	map<string, TemplateArgument> value_subst;
	for (size_t i = 0; i < selected_args.size() &&
	     i < selected_declaration->parameters.size(); ++i)
		if (!selected_declaration->parameters[i].name.empty())
		{
			if (selected_declaration->parameters[i].is_pack)
			{
				subst[selected_declaration->parameters[i].name] =
					pa11::make_template_parameter_type(
						selected_declaration->parameters[i].name);
				value_subst[selected_declaration->parameters[i].name] =
					selected_args[i];
			}
			else if (selected_declaration->parameters[i].kind ==
			         TemplateParameterKind::Type)
				subst[selected_declaration->parameters[i].name] =
					selected_args[i].type;
			else
				value_subst[selected_declaration->parameters[i].name] =
					selected_args[i];
		}
	template_type_substitutions_.push_back(subst);
	template_value_substitutions_.push_back(value_subst);
	scopes_.clear();
	scopes_.push_back(selected_declaration->lexical_scope != NULL
	                  ? selected_declaration->lexical_scope
	                  : selected_declaration->owner);
	pos_ = selected_declaration->decl_begin;
	DeclSpecs specs = parse_decl_specifier_seq(false);
	TypePtr base = type_from_decl_specs(specs);
	Declarator declarator = parse_declarator(false);
	TypePtr type = apply_declarator(declarator, base);
	if (specs.constexpr_decl && !pa11::type_has_const(type))
		type = pa11::make_cv(type, pa11::CV_CONST);
	Expr init;
	if (consume(OP_ASS))
		init = parse_assignment_expression();
	string special_name = template_specialization_name(declaration, full_args);
	bool constant_init = init.valid && init.has_constant_value;
	Binding* binding =
		add_value(declaration->owner,
		          constant_init ? BindingKind::Enumerator : BindingKind::Variable,
		          special_name,
		          type);
	if (constant_init)
	{
		binding->has_constant = true;
		binding->constant_value = init.constant_value;
	}
	cached = binding;
	template_type_substitutions_ = save_subst;
	template_value_substitutions_ = save_value_subst;
	scopes_ = save_scopes;
	pos_ = save_pos;
	return binding;
}

}  // namespace internal
}  // namespace pa12
