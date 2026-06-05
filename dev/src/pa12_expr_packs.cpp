#include "pa12_internal.h"

#include <stdexcept>

using namespace std;

namespace pa12 {
namespace internal {
namespace {

bool type_contains_template_parameter_name(TypePtr type, string& name)
{
	if (type.get() == NULL)
		return false;
	type = pa11::strip_cv(type);
	if (type->kind == pa11::TypeKind::TemplateParameter)
	{
		if (!pa11::is_deducible_template_parameter_type(type))
			return false;
		name = type->name;
		return true;
	}
	if (type->kind == pa11::TypeKind::Pointer ||
	    type->kind == pa11::TypeKind::LValueReference ||
	    type->kind == pa11::TypeKind::RValueReference ||
	    type->kind == pa11::TypeKind::Array)
		return type_contains_template_parameter_name(type->base, name);
	if (type->kind == pa11::TypeKind::Function)
	{
		if (type_contains_template_parameter_name(type->base, name))
			return true;
		for (size_t i = 0; i < type->parameters.size(); ++i)
			if (type_contains_template_parameter_name(type->parameters[i],
			                                          name))
				return true;
	}
	if (type->kind == pa11::TypeKind::MemberPointer)
		return type_contains_template_parameter_name(type->member_class,
		                                             name) ||
		       type_contains_template_parameter_name(type->base, name);
	return false;
}

void note_expression_pack_size(const Expr& expr,
                               bool& have_pack,
                               size_t& pack_size)
{
	if (!expr.pack_expansion)
		return;
	if (!have_pack)
	{
		have_pack = true;
		pack_size = expr.pack.size();
		return;
	}
	if (pack_size != expr.pack.size())
		throw runtime_error("pack expansion size mismatch");
}

Expr expression_pack_element(const Expr& expr, size_t index)
{
	return expr.pack_expansion ? expr.pack[index] : expr;
}

}  // namespace

bool Parser::make_binary_pack_expr(ETokenType op,
                                   const string& text,
                                   const Expr& lhs,
                                   const Expr& rhs,
                                   Expr& out)
{
	bool have_pack = false;
	size_t pack_size = 0;
	note_expression_pack_size(lhs, have_pack, pack_size);
	note_expression_pack_size(rhs, have_pack, pack_size);
	if (!have_pack)
		return false;
	out = Expr();
	out.valid = true;
	out.pack_expansion = true;
	out.type = op == OP_COMMA ? rhs.type : lhs.type;
	out.category = op == OP_COMMA ? rhs.category : ValueCategory::PRValue;
	out.node = Node("pack-expression binary");
	for (size_t i = 0; i < pack_size; ++i)
	{
		Expr elem = make_binary_expr(op,
		                             text,
		                             expression_pack_element(lhs, i),
		                             expression_pack_element(rhs, i));
		if (i == 0)
		{
			out.type = elem.type;
			out.category = elem.category;
		}
		out.pack.push_back(elem);
		add_child(out.node, elem.node);
	}
	annotate_expr_node(out);
	return true;
}

bool Parser::make_cast_pack_expr(TypePtr target,
                                 const string& op_text,
                                 const Expr& inner,
                                 bool suppress_target_pack,
                                 Expr& out)
{
	string target_pack_name;
	TemplateArgument target_pack;
	bool target_is_pack =
		!suppress_target_pack &&
		type_contains_template_parameter_name(target, target_pack_name) &&
		find_template_value_substitution(target_pack_name, target_pack) &&
		target_pack.kind == TemplateArgumentKind::Pack;
	if (!inner.pack_expansion && !target_is_pack)
		return false;

	size_t pack_size =
		inner.pack_expansion ? inner.pack.size() : target_pack.pack.size();
	if (target_is_pack && target_pack.pack.size() != pack_size)
		throw runtime_error("cast pack expansion mismatch");
	out = Expr();
	out.valid = true;
	out.pack_expansion = true;
	out.type = target;
	out.category = ValueCategory::PRValue;
	out.node = Node("pack-expression cast");
	for (size_t i = 0; i < pack_size; ++i)
	{
		TypePtr element_target = target;
		bool element_target_is_validation_placeholder = false;
		if (target_is_pack)
		{
			if (target_pack.pack[i].kind != TemplateArgumentKind::Type)
				throw runtime_error("type pack required for cast");
			string replacement_pack_name;
			element_target_is_validation_placeholder =
				type_contains_template_parameter_name(
					target_pack.pack[i].type,
					replacement_pack_name) &&
				replacement_pack_name == target_pack_name;
			element_target =
				substitute_template_type_parameter(target,
				                                   target_pack_name,
				                                   target_pack.pack[i].type);
		}
		Expr element_inner = inner.pack_expansion ? inner.pack[i] : inner;
		if (element_inner.pack_expansion)
			throw runtime_error("type pack required for cast");
		Expr elem = make_cast_expr(element_target,
		                           op_text,
		                           element_inner,
		                           element_target_is_validation_placeholder);
		if (i == 0)
			out.category = elem.category;
		out.pack.push_back(elem);
		add_child(out.node, elem.node);
	}
	annotate_expr_node(out);
	return true;
}

bool Parser::make_template_id_callee_pack_expr(const Expr& callee, Expr& out)
{
	if (callee.pack_expansion ||
	    !at(OP_DOTS) ||
	    callee.explicit_template_arguments.empty())
		return false;
	bool have_template_pack = false;
	size_t template_pack_size = 0;
	for (map<Binding*, vector<TemplateArgument> >::const_iterator it =
		     callee.explicit_template_arguments.begin();
	     it != callee.explicit_template_arguments.end(); ++it)
		for (size_t i = 0; i < it->second.size(); ++i)
		{
			const TemplateArgument& arg = it->second[i];
			size_t size = 0;
			bool is_pack = false;
			if (arg.kind == TemplateArgumentKind::Pack)
			{
				is_pack = true;
				size = arg.pack.size();
			}
			else if (arg.kind == TemplateArgumentKind::Type)
			{
				string pack_name;
				TemplateArgument subst;
				if (type_contains_template_parameter_name(arg.type, pack_name) &&
				    find_template_value_substitution(pack_name, subst) &&
				    subst.kind == TemplateArgumentKind::Pack)
				{
					is_pack = true;
					size = subst.pack.size();
				}
			}
			if (!is_pack)
				continue;
			if (!have_template_pack)
			{
				have_template_pack = true;
				template_pack_size = size;
			}
			else if (template_pack_size != size)
				throw runtime_error("pack expansion size mismatch");
		}
	if (!have_template_pack)
		return false;
	out = callee;
	out.pack_expansion = true;
	out.pack.clear();
	out.node = Node("pack-expression template-id callee");
	for (size_t p = 0; p < template_pack_size; ++p)
	{
		Expr elem = callee;
		elem.pack_expansion = false;
		elem.pack.clear();
		elem.explicit_template_arguments.clear();
		for (map<Binding*, vector<TemplateArgument> >::const_iterator it =
			     callee.explicit_template_arguments.begin();
		     it != callee.explicit_template_arguments.end(); ++it)
		{
			vector<TemplateArgument> elem_args = it->second;
			for (size_t i = 0; i < elem_args.size(); ++i)
			{
				TemplateArgument& arg = elem_args[i];
				if (arg.kind == TemplateArgumentKind::Pack)
				{
					arg = arg.pack[p];
					continue;
				}
				if (arg.kind != TemplateArgumentKind::Type)
					continue;
				string pack_name;
				TemplateArgument subst;
				if (!type_contains_template_parameter_name(arg.type, pack_name) ||
				    !find_template_value_substitution(pack_name, subst) ||
				    subst.kind != TemplateArgumentKind::Pack)
					continue;
				if (subst.pack[p].kind != TemplateArgumentKind::Type)
					throw runtime_error("type pack required");
				arg = TemplateArgument::type_arg(
					substitute_template_type_parameter(arg.type,
					                                   pack_name,
					                                   subst.pack[p].type));
			}
			elem.explicit_template_arguments[it->first] = elem_args;
		}
		out.pack.push_back(elem);
		add_child(out.node, elem.node);
	}
	annotate_expr_node(out);
	return true;
}

bool Parser::make_call_pack_expr(const Expr& callee,
                                 const vector<Expr>& args,
                                 Expr& out)
{
	Expr expanded_callee;
	const Expr* effective_callee = &callee;
	if (make_template_id_callee_pack_expr(callee, expanded_callee))
		effective_callee = &expanded_callee;
	bool have_pack = false;
	size_t pack_size = 0;
	note_expression_pack_size(*effective_callee, have_pack, pack_size);
	for (size_t i = 0; i < args.size(); ++i)
		note_expression_pack_size(args[i], have_pack, pack_size);
	if (!have_pack)
		return false;

	out = Expr();
	out.valid = true;
	out.pack_expansion = true;
	out.node = Node("pack-expression call");
	for (size_t i = 0; i < pack_size; ++i)
	{
		vector<Expr> element_args;
		for (size_t j = 0; j < args.size(); ++j)
			element_args.push_back(expression_pack_element(args[j], i));
		Expr elem = make_call_expr(expression_pack_element(*effective_callee, i),
		                           element_args);
		if (i == 0)
		{
			out.type = elem.type;
			out.category = elem.category;
		}
		out.pack.push_back(elem);
		add_child(out.node, elem.node);
	}
	if (pack_size == 0)
	{
		out.type = effective_callee->type;
		out.category = ValueCategory::PRValue;
	}
	annotate_expr_node(out);
	return true;
}

}  // namespace internal
}  // namespace pa12
