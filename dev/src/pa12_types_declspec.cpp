#include "pa12_types_support.h"

#include <algorithm>
#include <stdexcept>

using namespace std;

namespace pa12 {
namespace internal {

bool Parser::try_resolve_type_pack_element(
	const vector<TemplateArgument>& arguments,
	TypePtr& out)
{
	if (arguments.size() < 2)
		throw runtime_error("invalid __type_pack_element");
	TemplateArgument index = substitute_template_argument(arguments[0]);
	bool dependent = index.kind != TemplateArgumentKind::Value ||
	                 index.dependent ||
	                 template_argument_has_template_parameter(
		                 index,
		                 record_template_arguments_);
	vector<TemplateArgument> elements;
	for (size_t i = 1; i < arguments.size(); ++i)
	{
		vector<TemplateArgument> expanded =
			expand_template_argument_pack(arguments[i]);
		for (size_t j = 0; j < expanded.size(); ++j)
		{
			TemplateArgument elem =
				substitute_template_argument(expanded[j]);
			if (elem.kind == TemplateArgumentKind::Pack)
			{
				for (size_t p = 0; p < elem.pack.size(); ++p)
				{
					TemplateArgument pack_elem =
						substitute_template_argument(elem.pack[p]);
					if (pack_elem.kind != TemplateArgumentKind::Type)
						throw runtime_error(
							"__type_pack_element requires types");
					if (template_argument_has_template_parameter(
						    pack_elem,
						    record_template_arguments_))
						dependent = true;
					elements.push_back(pack_elem);
				}
				continue;
			}
			if (elem.kind != TemplateArgumentKind::Type)
				throw runtime_error("__type_pack_element requires types");
			if (template_argument_has_template_parameter(
				    elem,
				    record_template_arguments_))
				dependent = true;
			elements.push_back(elem);
		}
	}
	if (dependent)
	{
		out = pa11::make_dependent_typename_type(
			"__type_pack_element",
			false,
			true,
			false);
		out->template_primary_name = "__type_pack_element";
		out->template_arguments =
			dependent_template_instance_arguments(arguments);
		record_template_arguments_[out.get()] = arguments;
		return true;
	}
	if (index.value >= elements.size())
		throw runtime_error("__type_pack_element index out of range");
	out = elements[static_cast<size_t>(index.value)].type;
	return true;
}

DeclSpecs Parser::parse_decl_specifier_seq(bool type_id_context)
{
	DeclSpecs specs;
	bool saw_any = false;
	bool saw_non_cv_type = false;
	for (;;)
	{
		if (!type_id_context && consume(KW_TYPEDEF))
		{
			specs.typedef_decl = true;
			saw_any = true;
		}
		else if (!type_id_context && consume(KW_CONSTEXPR))
		{
			specs.constexpr_decl = true;
			saw_any = true;
		}
		else if (!type_id_context && consume(KW_MUTABLE))
		{
			specs.mutable_decl = true;
			saw_any = true;
		}
		else if (!type_id_context && consume(KW_FRIEND))
		{
			specs.friend_decl = true;
			saw_any = true;
		}
		else if (!type_id_context && consume(KW_ALIGNAS))
		{
			skip_balanced(OP_LPAREN, OP_RPAREN);
			saw_any = true;
		}
		else if (!type_id_context &&
		         at_identifier() &&
		         current().source == "__attribute__")
		{
			++pos_;
			if (at(OP_LPAREN))
				skip_balanced(OP_LPAREN, OP_RPAREN);
			saw_any = true;
		}
		else if (!type_id_context &&
		         at(OP_LSQUARE) &&
		         lookahead(OP_LSQUARE, 1))
		{
			++pos_;
			skip_balanced(OP_LSQUARE, OP_RSQUARE);
			expect(OP_RSQUARE);
			saw_any = true;
		}
		else if (!type_id_context && at_simple_ignored_specifier())
		{
			if (at(KW_STATIC))
				specs.static_decl = true;
			if (at(KW_EXTERN))
				specs.extern_decl = true;
			if (at(KW_THREAD_LOCAL))
				specs.thread_local_decl = true;
			if (at(KW_VIRTUAL))
				specs.virtual_decl = true;
			if (at(KW_INLINE))
				specs.inline_decl = true;
			++pos_;
			saw_any = true;
		}
		else if (at_simple_cv())
		{
			specs.cv |= consume_cv_flag();
			saw_any = true;
		}
		else if (at_simple_builtin())
		{
			if (at(KW_AUTO))
				specs.auto_decl = true;
			else
				specs.builtin.push_back(tokens_[pos_].type);
			++pos_;
			saw_any = true;
			saw_non_cv_type = true;
		}
		else if (!saw_non_cv_type && at(KW_DECLTYPE))
		{
			specs.named_type = parse_decltype_specifier();
			saw_any = true;
			saw_non_cv_type = true;
		}
		else if (!saw_non_cv_type && starts_class_key())
		{
			specs.named_type = parse_class_specifier();
			saw_any = true;
			saw_non_cv_type = true;
		}
		else if (!saw_non_cv_type && at(KW_ENUM))
		{
			specs.named_type = parse_enum_specifier();
			saw_any = true;
			saw_non_cv_type = true;
		}
		else if (!saw_non_cv_type)
		{
			bool parsed_type_name = false;
			if (specs.typedef_decl)
				++defer_class_template_completion_depth_;
			try
			{
				parsed_type_name = try_parse_type_name(specs.named_type);
			}
			catch (...)
			{
				if (specs.typedef_decl)
					--defer_class_template_completion_depth_;
				throw;
			}
			if (specs.typedef_decl)
				--defer_class_template_completion_depth_;
			if (!parsed_type_name)
				break;
			saw_any = true;
			saw_non_cv_type = true;
		}
		else
			break;
		}
		if (!saw_any || !saw_non_cv_type)
			throw runtime_error("expected declaration specifiers");
		return specs;
	}

TypePtr Parser::type_from_decl_specs(const DeclSpecs& specs)
{
	TypePtr type = specs.named_type.get() != NULL ? specs.named_type :
		specs.auto_decl ? pa11::make_fundamental(FT_VOID) :
		pa11::make_fundamental(pa11::fundamental_from_specs(specs.builtin));
	return pa11::make_cv(type, specs.cv);
}

TypePtr Parser::parse_type_id()
{
	DeclSpecs specs = parse_decl_specifier_seq(true);
	TypePtr base = type_from_decl_specs(specs);
	if (!starts_abstract_declarator())
		return base;
	size_t save = pos_;
	try
	{
		return apply_declarator(parse_abstract_declarator(), base);
	}
	catch (const exception&)
	{
		pos_ = save;
		return base;
	}
}

TypePtr Parser::parse_decltype_specifier()
{
	expect(KW_DECLTYPE);
	expect(OP_LPAREN);
	if (at(KW_SIZEOF))
	{
		++unevaluated_expression_depth_;
		Expr expr;
		try
		{
			expr = parse_type_trait_expression(KW_SIZEOF);
		}
		catch (...)
		{
			--unevaluated_expression_depth_;
			throw;
		}
		--unevaluated_expression_depth_;
		expect(OP_RPAREN);
		return expr.type;
	}
	size_t save = pos_;
	if (at_identifier() && lookahead(OP_RPAREN, 1))
	{
		string name = consume_identifier();
		Binding* binding =
			pa11::lookup_unqualified(current_scope(),
			                          name,
			                          pa11::LOOKUP_VALUE);
		if (binding != NULL)
		{
			expect(OP_RPAREN);
			return binding->type;
		}
		pos_ = save;
	}
	try
	{
		if (!at(OP_LPAREN))
		{
			QualifiedName name = parse_id_expression_name();
			if (at(OP_RPAREN))
			{
				Binding* binding = resolve_single_name(name, pa11::LOOKUP_VALUE);
				if (binding == NULL)
					throw runtime_error("decltype target not found");
				expect(OP_RPAREN);
				return binding->type;
			}
		}
	}
	catch (const exception&)
	{
	}
	pos_ = save;
	++unevaluated_expression_depth_;
	Expr expr;
	try
	{
		expr = parse_expression();
	}
		catch (...)
		{
			--unevaluated_expression_depth_;
			bool concrete_substitution_context =
				!validating_template_definition_ &&
				(!template_type_substitutions_.empty() ||
				 !template_value_substitutions_.empty());
			if (concrete_substitution_context)
			{
				if (!template_type_substitutions_.empty())
					for (map<string, TypePtr>::const_iterator it =
						     template_type_substitutions_.back().begin();
					     it != template_type_substitutions_.back().end();
					     ++it)
					{
						bool concrete_pack_placeholder = false;
						TypePtr bare = it->second.get() != NULL
							? pa11::strip_cv(it->second) : TypePtr();
						if (bare.get() != NULL &&
						    bare->kind == pa11::TypeKind::TemplateParameter &&
						    active_type_parameter_pack(it->first) &&
						    !template_value_substitutions_.empty())
						{
							map<string, TemplateArgument>::const_iterator pack =
								template_value_substitutions_.back().find(
									it->first);
							concrete_pack_placeholder =
								pack != template_value_substitutions_.back().end() &&
								pack->second.kind == TemplateArgumentKind::Pack;
							for (size_t pi = 0;
							     concrete_pack_placeholder &&
							     pi < pack->second.pack.size();
							     ++pi)
								if (template_argument_has_template_parameter(
									    pack->second.pack[pi],
									    record_template_arguments_))
									concrete_pack_placeholder = false;
						}
						if (!concrete_pack_placeholder &&
						    type_is_template_dependent(it->second))
							concrete_substitution_context = false;
					}
				if (!template_value_substitutions_.empty())
					for (map<string, TemplateArgument>::const_iterator it =
						     template_value_substitutions_.back().begin();
					     it != template_value_substitutions_.back().end();
					     ++it)
						if (template_argument_has_template_parameter(
							    it->second,
							    record_template_arguments_))
							concrete_substitution_context = false;
			}
			if (function_template_candidate_instantiation_depth_ != 0 ||
			    (concrete_substitution_context &&
			     !active_class_instantiation_dependent()))
				throw;
			if (template_type_substitutions_.empty() &&
			    template_value_substitutions_.empty() &&
			    active_class_instantiations_.empty() &&
		    !validating_template_definition_)
			throw;
		pos_ = save;
		int paren = 0;
		int angle = 0;
		int square = 0;
		int brace = 0;
		while (!at_eof())
		{
			if (paren == 0 && angle == 0 && square == 0 &&
			    brace == 0 && at(OP_RPAREN))
				break;
			if (at(OP_LPAREN))
				++paren;
			else if (at(OP_RPAREN))
			{
				if (paren == 0)
					break;
				--paren;
			}
			else if (at(OP_LT))
				++angle;
			else if (at(OP_GT) && angle > 0)
				--angle;
			else if (at(OP_LSQUARE))
				++square;
			else if (at(OP_RSQUARE) && square > 0)
				--square;
			else if (at(OP_LBRACE))
				++brace;
			else if (at(OP_RBRACE) && brace > 0)
				--brace;
			++pos_;
		}
		TypePtr dependent = pa11::make_dependent_typename_type(
			"decltype(" +
			dependent_token_spelling(tokens_, save, pos_) + ")",
			false,
			false,
			true);
		expect(OP_RPAREN);
		return dependent;
	}
	--unevaluated_expression_depth_;
	bool parenthesized_operand =
		decltype_operand_is_parenthesized(tokens_, save, pos_);
	if (replaying_dependent_decltype_ &&
	    expr.valid &&
	    expr.type.get() != NULL &&
	    type_is_template_dependent(expr.type) &&
	    (!template_type_substitutions_.empty() ||
	     !template_value_substitutions_.empty() ||
	     function_template_candidate_instantiation_depth_ != 0))
	{
		try
		{
			TypePtr replayed_type = substitute_template_type(expr.type);
			if (replayed_type.get() != NULL)
				expr.type = replayed_type;
		}
		catch (const runtime_error&)
		{
		}
	}
	bool operand_mentions_active_template_parameter = false;
	if (!replaying_dependent_decltype_)
	{
		for (size_t i = save; i < pos_; ++i)
		{
			if (tokens_[i].kind != posttoken::TokenKind::Identifier)
				continue;
			TypePtr type_subst;
			TemplateArgument value_subst;
			if (find_template_type_substitution(tokens_[i].source,
			                                    type_subst) ||
			    find_template_value_substitution(tokens_[i].source,
			                                     value_subst) ||
			    active_type_parameter_pack(tokens_[i].source))
			{
				operand_mentions_active_template_parameter = true;
				break;
			}
		}
	}
	bool replayed_type_still_dependent = type_is_template_dependent(expr.type);
	bool defer_decltype =
		replayed_type_still_dependent ||
		(!replaying_dependent_decltype_ &&
		 (expr_node_structurally_dependent(expr.node) ||
		  operand_mentions_active_template_parameter));
	if (defer_decltype)
	{
		TypePtr dependent = pa11::make_dependent_typename_type(
			"decltype(" +
			dependent_token_spelling(tokens_, save, pos_) + ")",
			false,
			false,
			true);
		expect(OP_RPAREN);
		return dependent;
	}
	expect(OP_RPAREN);
	if (!parenthesized_operand &&
	    expr.binding != NULL &&
	    expr.node.line.compare(0, 17, "member-expression") == 0)
		return expr.binding->type;
	TypePtr object = expression_object_type(expr.type);
	if (expr.category == ValueCategory::LValue)
		return pa11::make_lvalue_reference(object);
	if (expr.category == ValueCategory::XValue)
		return pa11::make_rvalue_reference(object);
	return expr.type;
}

}  // namespace internal
}  // namespace pa12
