#include "pa12_internal.h"

#include <stdexcept>

using namespace std;

namespace pa12 {
namespace internal {

string Parser::conversion_operator_name(TypePtr type) const
{
	return "operator " + pa11::describe_type(type);
}

TypePtr Parser::parse_conversion_type_id()
{
	DeclSpecs specs = parse_decl_specifier_seq(true);
	TypePtr type = type_from_decl_specs(specs);
	vector<PtrOp> ops;
	parse_ptr_prefix(ops);
	return apply_ptr_ops(type, ops);
}

string Parser::consume_operator_function_name()
{
	expect(KW_OPERATOR);
	if (consume(KW_NEW))
	{
		if (consume(OP_LSQUARE))
		{
			expect(OP_RSQUARE);
			return "operatornew[]";
		}
		return "operatornew";
	}
	if (consume(KW_DELETE))
	{
		if (consume(OP_LSQUARE))
		{
			expect(OP_RSQUARE);
			return "operatordelete[]";
		}
		return "operatordelete";
	}
	{
		size_t save = pos_;
		try
		{
			return conversion_operator_name(parse_conversion_type_id());
		}
		catch (const exception&)
		{
			pos_ = save;
		}
	}
	if (consume(OP_LPAREN))
	{
		expect(OP_RPAREN);
		return "operator()";
	}
	if (consume(OP_LSQUARE))
	{
		expect(OP_RSQUARE);
		return "operator[]";
	}
	if (at_literal())
		return "operator" + consume_literal();
	if (current().kind != posttoken::TokenKind::Simple)
		throw runtime_error("expected operator token");
	string name = "operator" + current().source;
	++pos_;
	return name;
}

QualifiedName Parser::parse_id_expression_name()
{
	QualifiedName name;
	bool template_id_qualifier = false;
	if (at_identifier() && lookahead(OP_LT, 1))
	{
		size_t p = pos_ + 1;
		int depth = 0;
		while (p < tokens_.size())
		{
			if (tokens_[p].kind == posttoken::TokenKind::Simple &&
			    tokens_[p].type == OP_LT)
				++depth;
			else if (tokens_[p].kind == posttoken::TokenKind::Simple &&
			         tokens_[p].type == OP_GT)
			{
				--depth;
				if (depth == 0)
				{
					template_id_qualifier =
						p + 1 < tokens_.size() &&
						tokens_[p + 1].kind == posttoken::TokenKind::Simple &&
						tokens_[p + 1].type == OP_COLON2;
					break;
				}
			}
			++p;
		}
	}
	if (at(KW_DECLTYPE) ||
	    at(OP_COLON2) ||
	    (at_identifier() &&
	     (lookahead(OP_COLON2, 1) || template_id_qualifier)))
	{
		string spelling;
		name.qualifier = parse_nested_name_specifier(&spelling);
		name.spelling = spelling;
		name.qualified = true;
	}
	if (name.qualified)
		consume(KW_TEMPLATE);
	if (consume(KW_OPERATOR))
	{
		--pos_;
		name.name = consume_operator_function_name();
	}
	else
		name.name = consume_identifier();
	if (at(OP_LT))
	{
		size_t template_save = pos_;
		try
		{
			name.has_template_arguments = true;
			parse_template_argument_list(name.template_arguments);
		}
		catch (const exception&)
		{
			vector<TemplateDeclaration*> templates =
				find_function_templates(name);
			if (!templates.empty())
				throw;
			name.has_template_arguments = false;
			name.template_arguments.clear();
			pos_ = template_save;
		}
	}
	if (name.qualified)
		name.spelling += name.name;
	else
		name.spelling = name.name;
	return name;
}

Scope* Parser::parse_nested_name_specifier(string* spelling)
{
	Scope* scope = NULL;
	string text;
	if (consume(OP_COLON2))
	{
		scope = global_scope();
		text = "::";
	}
	else if (at(KW_DECLTYPE))
	{
		TypePtr type = parse_decltype_specifier();
		expect(OP_COLON2);
		type = expression_object_type(type);
		type = pa11::strip_cv(type);
		complete_template_record(type);
		if ((type->kind != pa11::TypeKind::Record &&
		     type->kind != pa11::TypeKind::Enum) ||
		    type->scope == NULL)
			throw runtime_error("decltype qualifier is not a scope");
		scope = type->scope;
		text = "decltype::";
	}
	else if (at_identifier())
	{
		size_t save = pos_;
		string root = consume_identifier();
		if (at(OP_LT))
		{
			TemplateDeclaration* templ = find_class_template(NULL, root);
			if (templ != NULL)
			{
				vector<TemplateArgument> arguments;
				parse_template_argument_list(arguments);
				if (consume(OP_COLON2))
				{
					TypePtr type = instantiate_class_template(templ, arguments);
					complete_template_record(type);
					type = pa11::strip_cv(type);
					if (type->kind != pa11::TypeKind::Record ||
					    type->scope == NULL)
						throw runtime_error("template-id qualifier is not a scope");
					scope = type->scope;
					text = root + "::";
				}
				else
					pos_ = save;
			}
			else
				pos_ = save;
		}
		else
			pos_ = save;
		if (scope == NULL)
		{
			string ordinary_root = consume_identifier();
			expect(OP_COLON2);
			TypePtr subst_root;
			if (find_template_type_substitution(ordinary_root, subst_root))
			{
				subst_root = pa11::strip_cv(subst_root);
				complete_template_record(subst_root);
				if (subst_root->kind == pa11::TypeKind::Record &&
				    subst_root->scope != NULL)
				{
					scope = subst_root->scope;
					text = ordinary_root + "::";
				}
			}
			if (scope != NULL)
				;
			else
			{
			Binding* binding =
				pa11::lookup_unqualified(current_scope(),
				                         ordinary_root,
				                         pa11::LOOKUP_QUALIFIER);
			if (binding != NULL && binding->type.get() != NULL)
				complete_template_record(binding->type);
			scope = resolve_qualifier(binding);
			if (scope == NULL)
				throw runtime_error("qualified lookup root not found");
			text = ordinary_root + "::";
			}
		}
	}
	else
	{
		string root = consume_identifier();
		expect(OP_COLON2);
		Binding* binding =
			pa11::lookup_unqualified(current_scope(), root, pa11::LOOKUP_QUALIFIER);
		if (binding != NULL && binding->type.get() != NULL)
			complete_template_record(binding->type);
		scope = resolve_qualifier(binding);
		if (scope == NULL)
			throw runtime_error("qualified lookup root not found");
		text = root + "::";
	}
	while (at_identifier() && lookahead(OP_COLON2, 1))
	{
		string component = consume_identifier();
		expect(OP_COLON2);
		vector<Binding*> found =
			lookup_qualified_set(scope, component, pa11::LOOKUP_QUALIFIER);
		if (found.empty())
			throw runtime_error("qualified lookup component not found");
		if (found[0]->type.get() != NULL)
			complete_member_class_template_record(found[0]);
		if (found[0]->type.get() != NULL)
			complete_template_record(found[0]->type);
		scope = resolve_qualifier(found[0]);
		if (scope == NULL)
			throw runtime_error("qualified lookup component not a scope");
		text += component + "::";
	}
	for (;;)
	{
		size_t save = pos_;
		consume(KW_TEMPLATE);
		if (!at_identifier())
		{
			pos_ = save;
			break;
		}
		string component = consume_identifier();
		if (!at(OP_LT))
		{
			pos_ = save;
			break;
		}
		TemplateDeclaration* templ = find_class_template(scope, component);
		if (templ == NULL)
		{
			pos_ = save;
			break;
		}
		vector<TemplateArgument> arguments;
		parse_template_argument_list(arguments);
		if (!consume(OP_COLON2))
		{
			pos_ = save;
			break;
		}
		TypePtr type = instantiate_class_template(templ, arguments);
		complete_template_record(type);
		type = pa11::strip_cv(type);
		if (type->kind != pa11::TypeKind::Record || type->scope == NULL)
			throw runtime_error("template-id qualifier is not a scope");
		scope = type->scope;
		text += component + "::";
		while (at_identifier() && lookahead(OP_COLON2, 1))
		{
			string nested = consume_identifier();
			expect(OP_COLON2);
			vector<Binding*> found =
				lookup_qualified_set(scope, nested, pa11::LOOKUP_QUALIFIER);
			if (found.empty())
				throw runtime_error("qualified lookup component not found");
			if (found[0]->type.get() != NULL)
				complete_member_class_template_record(found[0]);
			if (found[0]->type.get() != NULL)
				complete_template_record(found[0]->type);
			scope = resolve_qualifier(found[0]);
			if (scope == NULL)
				throw runtime_error("qualified lookup component not a scope");
			text += nested + "::";
		}
	}
	if (spelling != NULL)
		*spelling = text;
	return scope;
}

Scope* Parser::parse_qualified_namespace_specifier()
{
	string spelling;
	Scope* qualifier = NULL;
	if (at(OP_COLON2) || (at_identifier() && lookahead(OP_COLON2, 1)))
		qualifier = parse_nested_name_specifier(&spelling);
	string name = consume_identifier();
	vector<Binding*> found = qualifier != NULL
		? lookup_qualified_set(qualifier, name, pa11::LOOKUP_NAMESPACE)
		: lookup_unqualified_set(current_scope(), name, pa11::LOOKUP_NAMESPACE);
	if (found.empty())
		throw runtime_error("namespace specifier not found");
	Scope* scope = resolve_qualifier(found[0]);
	if (scope == NULL || scope->kind != ScopeKind::Namespace)
		throw runtime_error("namespace specifier is not namespace");
	return scope;
}

bool Parser::is_assignment_operator(ETokenType& op) const
{
	if (current().kind != posttoken::TokenKind::Simple)
		return false;
	switch (current().type)
	{
	case OP_ASS:
	case OP_PLUSASS:
	case OP_MINUSASS:
	case OP_STARASS:
	case OP_DIVASS:
	case OP_MODASS:
	case OP_XORASS:
	case OP_BANDASS:
	case OP_BORASS:
	case OP_LSHIFTASS:
	case OP_RSHIFTASS:
		op = current().type;
		return true;
	default:
		return false;
	}
}

bool Parser::binary_operator(ETokenType& op, int& prec) const
{
	if (current().kind != posttoken::TokenKind::Simple)
		return false;
	op = current().type;
	if (current().type == OP_GT && current().split_rshift &&
	    pos_ + 1 < tokens_.size() && tokens_[pos_ + 1].split_rshift &&
	    tokens_[pos_ + 1].split_group == current().split_group)
		op = OP_RSHIFT;
	switch (op)
	{
	case OP_LOR: prec = 1; return true;
	case OP_LAND: prec = 2; return true;
	case OP_BOR: prec = 3; return true;
	case OP_XOR: prec = 4; return true;
	case OP_AMP: prec = 5; return true;
	case OP_EQ: case OP_NE: prec = 6; return true;
	case OP_LT: case OP_GT: case OP_LE: case OP_GE: prec = 7; return true;
	case OP_LSHIFT: case OP_RSHIFT: prec = 8; return true;
	case OP_PLUS: case OP_MINUS: prec = 9; return true;
	case OP_STAR: case OP_DIV: case OP_MOD: prec = 10; return true;
	case OP_ARROWSTAR: prec = 11; return true;
	default:
		return false;
	}
}

string Parser::operator_function_name(ETokenType type, const string& source) const
{
	if (type == OP_LPAREN)
		return "operator()";
	if (type == OP_LSQUARE)
		return "operator[]";
	return "operator" + source;
}

bool Parser::expression_starts_type_name(TypePtr& type)
{
	size_t save = pos_;
	try
	{
		DeclSpecs specs = parse_decl_specifier_seq(true);
		type = type_from_decl_specs(specs);
		if (at(OP_LPAREN) || at(OP_LBRACE))
			return true;
	}
	catch (const exception&)
	{
	}
	pos_ = save;
	type.reset();
	return false;
}

}  // namespace internal
}  // namespace pa12
