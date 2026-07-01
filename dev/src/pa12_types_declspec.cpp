#include "pa12_types_support.h"

#include <algorithm>
#include <stdexcept>

using namespace std;

namespace pa12 {
namespace internal {
namespace {

bool gnu_signed_alias(const string& name)
{
	return name == "__signed" || name == "__signed__";
}

bool gnu_inline_alias(const string& name)
{
	return name == "__inline" || name == "__inline__";
}

bool gnu_decltype_alias(const string& name)
{
	return name == "__decltype" || name == "__decltype__" ||
	       name == "__typeof" || name == "__typeof__";
}

bool gnu_extension_or_complex_marker(const string& name)
{
	return name == "__extension__" ||
	       name == "_Complex" ||
	       name == "__complex__" ||
	       name == "__complex";
}

bool hosted_float_type_alias(const string& name, EFundamentalType& type)
{
	if (name == "_Float16" || name == "_Float32")
	{
		type = FT_FLOAT;
		return true;
	}
	if (name == "_Float64" || name == "_Float32x")
	{
		type = FT_DOUBLE;
		return true;
	}
	if (name == "_Float128" || name == "_Float64x" || name == "__float128")
	{
		type = FT_LONG_DOUBLE;
		return true;
	}
	return false;
}

}  // namespace

bool Parser::try_resolve_type_pack_element(
	const vector<TemplateArgument>& arguments,
	TypePtr& out)
{
	if (arguments.size() < 2)
		throw runtime_error("invalid __type_pack_element");
	TemplateArgument index = substitute_template_argument(arguments[0]);
	if (index.kind == TemplateArgumentKind::Pack &&
	    index.pack.size() == 1)
		index = substitute_template_argument(index.pack[0]);
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

bool Parser::try_parse_builtin_va_list_decl_spec(DeclSpecs& specs,
                                                 bool& saw_non_cv_type)
{
	if (saw_non_cv_type ||
	    !at_identifier() ||
	    current().source != "__builtin_va_list")
		return false;
	++pos_;
	specs.named_type = pa11::make_pointer(pa11::make_fundamental(FT_VOID));
	saw_non_cv_type = true;
	return true;
}

bool Parser::parse_decl_storage_specifier(DeclSpecs& specs,
                                          bool type_id_context,
                                          bool& saw_any)
{
	if (starts_attribute())
	{
		Suffix attribute(SuffixKind::Attribute);
		if (parse_gnu_attribute_suffix(attribute))
		{
			if (attribute.vector_size != 0)
				specs.vector_size = attribute.vector_size;
		}
		else
			skip_attributes(&specs.no_unique_address_decl);
		saw_any = true;
		return true;
	}
	if (!type_id_context && consume(KW_TYPEDEF))
		specs.typedef_decl = true;
	else if (!type_id_context && consume(KW_CONSTEXPR))
		specs.constexpr_decl = true;
	else if (!type_id_context && consume(KW_MUTABLE))
		specs.mutable_decl = true;
	else if (!type_id_context && consume(KW_FRIEND))
		specs.friend_decl = true;
	else if (!type_id_context && at_simple_ignored_specifier())
	{
		string alias = at_identifier() ? current().source : string();
		if (at(KW_STATIC))
			specs.static_decl = true;
		if (at(KW_EXTERN))
			specs.extern_decl = true;
		if (at(KW_THREAD_LOCAL) || alias == "__thread")
			specs.thread_local_decl = true;
		if (at(KW_VIRTUAL))
			specs.virtual_decl = true;
		if (at(KW_INLINE) || gnu_inline_alias(alias))
			specs.inline_decl = true;
		++pos_;
	}
	else if (at_identifier() &&
	         gnu_extension_or_complex_marker(current().source))
		++pos_;
	else
		return false;
	saw_any = true;
	return true;
}

bool Parser::parse_decl_type_specifier(DeclSpecs& specs,
                                       bool type_id_context,
                                       bool& saw_any,
                                       bool& saw_non_cv_type)
{
	EFundamentalType hosted_float = FT_VOID;
	if (at_simple_cv())
		specs.cv |= consume_cv_flag();
	else if (at_identifier() &&
	         hosted_float_type_alias(current().source, hosted_float))
	{
		++pos_;
		specs.named_type = pa11::make_fundamental(hosted_float);
		saw_non_cv_type = true;
	}
	else if (at_simple_builtin())
	{
		ETokenType builtin = at_identifier() && gnu_signed_alias(current().source)
			? KW_SIGNED : tokens_[pos_].type;
		if (builtin == KW_AUTO)
			specs.auto_decl = true;
		else
			specs.builtin.push_back(builtin);
		++pos_;
		saw_non_cv_type = true;
	}
	else if (at_identifier() && current().source == "__int128")
	{
		++pos_;
		specs.int128_decl = true;
		saw_non_cv_type = true;
	}
	else if (at_identifier() && current().source == "_BitInt")
	{
		++pos_;
		expect(OP_LPAREN);
		if (!at(OP_RPAREN))
			parse_expression();
		expect(OP_RPAREN);
		specs.bitint_decl = true;
		saw_non_cv_type = true;
	}
	else if (!saw_non_cv_type && at_identifier() &&
	         current().source == "_Atomic")
	{
		++pos_;
		expect(OP_LPAREN);
		specs.named_type = parse_type_id();
		expect(OP_RPAREN);
		saw_non_cv_type = true;
	}
	else if (!saw_non_cv_type &&
	         (at(KW_DECLTYPE) ||
	          (at_identifier() && gnu_decltype_alias(current().source))))
	{
		if (at_identifier())
		{
			tokens_[pos_].kind = posttoken::TokenKind::Simple;
			tokens_[pos_].type = KW_DECLTYPE;
			tokens_[pos_].source = "decltype";
		}
		specs.named_type = parse_decltype_specifier();
		saw_non_cv_type = true;
	}
	else if (!saw_non_cv_type && starts_class_key())
	{
		specs.named_type = parse_class_specifier();
		saw_non_cv_type = true;
	}
	else if (!saw_non_cv_type && at(KW_ENUM))
	{
		specs.named_type = parse_enum_specifier();
		saw_non_cv_type = true;
	}
	else if (try_parse_builtin_va_list_decl_spec(specs, saw_non_cv_type))
		;
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
			return false;
		saw_non_cv_type = true;
	}
	else
		return false;
	saw_any = true;
	(void)type_id_context;
	return true;
}

DeclSpecs Parser::parse_decl_specifier_seq(bool type_id_context)
{
	DeclSpecs specs;
	bool saw_any = false;
	bool saw_non_cv_type = false;
	for (;;)
	{
		if (parse_decl_storage_specifier(specs, type_id_context, saw_any))
			continue;
		if (parse_decl_type_specifier(specs,
		                              type_id_context,
		                              saw_any,
		                              saw_non_cv_type))
			continue;
		break;
	}
	if (!saw_any || !saw_non_cv_type)
	{
		throw runtime_error("expected declaration specifiers");
	}
	return specs;
}

TypePtr Parser::type_from_decl_specs(const DeclSpecs& specs)
{
	if (specs.int128_decl || specs.bitint_decl)
	{
		EFundamentalType type =
			find(specs.builtin.begin(),
			     specs.builtin.end(),
			     KW_UNSIGNED) != specs.builtin.end()
			? FT_UNSIGNED_INT128 : FT_INT128;
		return pa11::make_cv(pa11::make_fundamental(type), specs.cv);
	}
	TypePtr type = specs.named_type.get() != NULL ? specs.named_type :
		specs.auto_decl ? pa11::make_fundamental(FT_VOID) :
		pa11::make_fundamental(pa11::fundamental_from_specs(specs.builtin));
	if (specs.vector_size != 0)
		type = pa11::make_gnu_vector(type, specs.vector_size);
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

TypePtr Parser::parse_decltype_sizeof_operand()
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

bool Parser::try_parse_decltype_named_operand(size_t save, TypePtr& out)
{
	if (at_identifier() && lookahead(OP_RPAREN, 1))
	{
		string name = consume_identifier();
		Binding* binding = pa11::lookup_unqualified(current_scope(),
		                                            name,
		                                            pa11::LOOKUP_VALUE);
		if (binding != NULL)
		{
			expect(OP_RPAREN);
			out = binding->type;
			return true;
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
				Binding* binding = resolve_single_name(name,
				                                       pa11::LOOKUP_VALUE);
				if (binding == NULL)
					throw runtime_error("decltype target not found");
				expect(OP_RPAREN);
				out = binding->type;
				return true;
			}
		}
	}
	catch (const exception&)
	{
	}
	pos_ = save;
	return false;
}

bool Parser::decltype_concrete_substitution_context() const
{
	bool concrete = !validating_template_definition_ &&
		(!template_type_substitutions_.empty() ||
		 !template_value_substitutions_.empty());
	if (!concrete)
		return false;
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
					template_value_substitutions_.back().find(it->first);
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
				concrete = false;
		}
	if (!template_value_substitutions_.empty())
		for (map<string, TemplateArgument>::const_iterator it =
			     template_value_substitutions_.back().begin();
		     it != template_value_substitutions_.back().end();
		     ++it)
			if (template_argument_has_template_parameter(
				    it->second,
				    record_template_arguments_))
				concrete = false;
	return concrete;
}

size_t Parser::dependent_decltype_operand_end(size_t save) const
{
	int paren = 0;
	int angle = 0;
	int square = 0;
	int brace = 0;
	size_t end = save;
	while (end < tokens_.size())
	{
		ETokenType type = tokens_[end].type;
		if (paren == 0 && angle == 0 && square == 0 && brace == 0 &&
		    type == OP_RPAREN)
			break;
		if (type == OP_LPAREN)
			++paren;
		else if (type == OP_RPAREN)
		{
			if (paren == 0)
				break;
			--paren;
		}
		else if (type == OP_LT)
			++angle;
		else if (type == OP_GT && angle > 0)
			--angle;
		else if (type == OP_LSQUARE)
			++square;
		else if (type == OP_RSQUARE && square > 0)
			--square;
		else if (type == OP_LBRACE)
			++brace;
		else if (type == OP_RBRACE && brace > 0)
			--brace;
		++end;
	}
	return end;
}

bool Parser::try_parse_dependent_decltype_operand(size_t save, TypePtr& out)
{
	bool concrete = decltype_concrete_substitution_context();
	if (function_template_candidate_instantiation_depth_ != 0 ||
	    (concrete && !active_class_instantiation_dependent()))
		return false;
	if (template_type_substitutions_.empty() &&
	    template_value_substitutions_.empty() &&
	    active_class_instantiations_.empty() &&
	    !validating_template_definition_)
		return false;
	size_t end = dependent_decltype_operand_end(save);
	if (end >= tokens_.size() || tokens_[end].type != OP_RPAREN)
		return false;
	if (!decltype_mentions_active_template_parameter(save, end))
		return false;
	out = parse_dependent_decltype_fallback(save);
	return true;
}

TypePtr Parser::parse_dependent_decltype_fallback(size_t save)
{
	pos_ = dependent_decltype_operand_end(save);
	TypePtr dependent = pa11::make_dependent_typename_type(
		"decltype(" + dependent_token_spelling(tokens_, save, pos_) + ")",
		false,
		false,
		true);
	dependent->scope = current_scope();
	expect(OP_RPAREN);
	return dependent;
}

void Parser::replay_decltype_substitution(Expr& expr)
{
	if (!replaying_dependent_decltype_ ||
	    !expr.valid ||
	    expr.type.get() == NULL ||
	    !type_is_template_dependent(expr.type) ||
	    (template_type_substitutions_.empty() &&
	     template_value_substitutions_.empty() &&
	     function_template_candidate_instantiation_depth_ == 0))
		return;
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

bool Parser::decltype_mentions_active_template_parameter(size_t begin,
                                                         size_t end) const
{
	for (size_t i = begin; i < end; ++i)
	{
		if (tokens_[i].kind != posttoken::TokenKind::Identifier)
			continue;
		TypePtr type_subst;
		TemplateArgument value_subst;
		if (find_template_type_substitution(tokens_[i].source, type_subst) ||
		    find_template_value_substitution(tokens_[i].source, value_subst) ||
		    active_type_parameter_pack(tokens_[i].source))
			return true;
	}
	return false;
}

TypePtr Parser::finish_decltype_expression_type(size_t save, Expr& expr)
{
	string spelling = dependent_token_spelling(tokens_, save, pos_);
	replay_decltype_substitution(expr);
	bool parenthesized_operand =
		decltype_operand_is_parenthesized(tokens_, save, pos_);
	TypePtr replay_record = expr.type.get() != NULL
		? pa11::strip_cv(expression_object_type(expr.type)) : TypePtr();
	bool replay_known_record =
		replaying_dependent_decltype_ &&
		replay_record.get() != NULL &&
		replay_record->kind == pa11::TypeKind::Record &&
		replay_record->scope != NULL &&
		!replay_record->is_dependent_typename;
	bool defer_decltype =
		(!replay_known_record && type_is_template_dependent(expr.type)) ||
		(!replaying_dependent_decltype_ &&
		 (expr_node_structurally_dependent(expr.node) ||
		  decltype_mentions_active_template_parameter(save, pos_)));
	if (defer_decltype)
	{
		TypePtr dependent = pa11::make_dependent_typename_type(
			"decltype(" + spelling + ")",
			false,
			false,
			true);
		dependent->scope = current_scope();
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

TypePtr Parser::parse_decltype_specifier()
{
	expect(KW_DECLTYPE);
	expect(OP_LPAREN);
	if (at(KW_SIZEOF))
		return parse_decltype_sizeof_operand();
	size_t save = pos_;
	TypePtr named;
	if (try_parse_decltype_named_operand(save, named))
		return named;
	if (try_parse_dependent_decltype_operand(save, named))
		return named;
	++unevaluated_expression_depth_;
	Expr expr;
	try
	{
		expr = parse_expression();
	}
	catch (...)
	{
		--unevaluated_expression_depth_;
		bool concrete = decltype_concrete_substitution_context();
		if (function_template_candidate_instantiation_depth_ != 0 ||
		    (concrete && !active_class_instantiation_dependent()))
			throw;
		if (template_type_substitutions_.empty() &&
		    template_value_substitutions_.empty() &&
		    active_class_instantiations_.empty() &&
		    !validating_template_definition_)
			throw;
		return parse_dependent_decltype_fallback(save);
	}
	--unevaluated_expression_depth_;
	return finish_decltype_expression_type(save, expr);
}

}  // namespace internal
}  // namespace pa12
