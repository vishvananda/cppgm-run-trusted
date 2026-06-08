#include "pa12_internal.h"

#include <stdexcept>

using namespace std;

namespace pa12 {
namespace internal {
namespace {

bool template_instance_argument_contains_template_parameter_name(
	const pa11::TemplateInstanceArgument& argument,
	string& name);

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
	if (type->is_template_specialization)
		for (size_t i = 0; i < type->template_arguments.size(); ++i)
			if (template_instance_argument_contains_template_parameter_name(
				    type->template_arguments[i],
				    name))
				return true;
	return false;
}

bool template_instance_argument_contains_template_parameter_name(
	const pa11::TemplateInstanceArgument& argument,
	string& name)
{
	if (argument.kind == pa11::TemplateInstanceArgumentKind::Type)
		return type_contains_template_parameter_name(argument.type, name);
	if (argument.kind == pa11::TemplateInstanceArgumentKind::Value)
		return type_contains_template_parameter_name(argument.type, name);
	if (argument.kind == pa11::TemplateInstanceArgumentKind::Pack)
		for (size_t i = 0; i < argument.pack.size(); ++i)
			if (template_instance_argument_contains_template_parameter_name(
				    argument.pack[i],
				    name))
				return true;
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
	const Expr* dependent_operand = NULL;
	if (!lhs.dependent_value_name.empty() &&
	    parameter_pack_expansion_name(lhs.dependent_value_name))
		dependent_operand = &lhs;
	else if (!rhs.dependent_value_name.empty() &&
	         parameter_pack_expansion_name(rhs.dependent_value_name))
		dependent_operand = &rhs;
	else if (!lhs.dependent_value_name.empty())
		dependent_operand = &lhs;
	else if (!rhs.dependent_value_name.empty())
		dependent_operand = &rhs;
	if (dependent_operand != NULL)
	{
		out.dependent_value_name = dependent_operand->dependent_value_name;
		out.dependent_value_owner_template_name =
			dependent_operand->dependent_value_owner_template_name;
		out.dependent_value_member_name =
			dependent_operand->dependent_value_member_name;
		out.dependent_value_owner_template_arguments =
			dependent_operand->dependent_value_owner_template_arguments;
		out.dependent_value_negated =
			dependent_operand->dependent_value_negated;
	}
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
	if (!at(OP_DOTS))
		return false;
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
	{
		if (replaying_dependent_decltype_ && inner.pack_expansion)
			target_is_pack = false;
		else
			throw runtime_error("cast pack expansion mismatch");
	}
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
			if (it->first != NULL && it->first->aliased_binding != NULL)
				elem.explicit_template_arguments[
					it->first->aliased_binding] = elem_args;
			for (size_t oi = 0; oi < elem.overloads.size(); ++oi)
			{
				Binding* overload = elem.overloads[oi];
				elem.explicit_template_arguments[overload] = elem_args;
				if (overload != NULL && overload->aliased_binding != NULL)
					elem.explicit_template_arguments[
						overload->aliased_binding] = elem_args;
			}
		}
		out.pack.push_back(elem);
		add_child(out.node, elem.node);
	}
	annotate_expr_node(out);
	return true;
}

bool Parser::try_expand_expression_pack_pattern(size_t begin,
                                                size_t end,
                                                vector<Expr>& out)
{
	struct NamedPack
	{
		string name;
		TemplateArgument pack;
	};
	struct NamedFunctionPack
	{
		string name;
		vector<Binding*> bindings;
	};
	vector<NamedPack> packs;
	vector<NamedFunctionPack> function_packs;
	set<string> seen;
	for (vector<map<string, TemplateArgument> >::const_reverse_iterator sit =
		     template_value_substitutions_.rbegin();
	     sit != template_value_substitutions_.rend();
	     ++sit)
		for (map<string, TemplateArgument>::const_iterator it =
			     sit->begin();
		     it != sit->end();
		     ++it)
			if (it->second.kind == TemplateArgumentKind::Pack &&
			    seen.insert(it->first).second)
			{
				NamedPack named;
				named.name = it->first;
				named.pack = it->second;
				packs.push_back(named);
			}
	if (!function_parameter_pack_substitutions_.empty())
		for (map<string, vector<Binding*> >::const_iterator it =
			     function_parameter_pack_substitutions_.back().begin();
		     it != function_parameter_pack_substitutions_.back().end();
		     ++it)
		{
			NamedFunctionPack named;
			named.name = it->first;
			named.bindings = it->second;
			function_packs.push_back(named);
		}
	if (packs.empty() && function_packs.empty())
		return false;
	size_t pack_size = !packs.empty()
		? packs[0].pack.pack.size() : function_packs[0].bindings.size();
	for (size_t i = 0; i < packs.size(); ++i)
		if (packs[i].pack.pack.size() != pack_size)
			throw runtime_error("pack expansion size mismatch");
	for (size_t i = 0; i < function_packs.size(); ++i)
		if (function_packs[i].bindings.size() != pack_size)
			throw runtime_error("pack expansion size mismatch");

	size_t save_pos = pos_;
	vector<map<string, TypePtr> > save_type_subst =
		template_type_substitutions_;
	vector<map<string, TemplateArgument> > save_value_subst =
		template_value_substitutions_;
	vector<set<string> > save_pack_subst =
		template_type_parameter_packs_;
	vector<map<string, vector<Binding*> > > save_function_pack_subst =
		function_parameter_pack_substitutions_;
	vector<Expr> expanded;
	try
	{
		for (size_t p = 0; p < pack_size; ++p)
		{
			map<string, TypePtr> type_subst;
			map<string, TemplateArgument> value_subst;
			map<string, vector<Binding*> > function_subst;
			for (size_t i = 0; i < packs.size(); ++i)
			{
				const TemplateArgument& elem = packs[i].pack.pack[p];
				if (elem.kind == TemplateArgumentKind::Type)
					type_subst[packs[i].name] = elem.type;
				else
					value_subst[packs[i].name] = elem;
			}
			for (size_t i = 0; i < function_packs.size(); ++i)
				if (p < function_packs[i].bindings.size())
					function_subst[function_packs[i].name]
						.push_back(function_packs[i].bindings[p]);
			template_type_substitutions_.push_back(type_subst);
			template_value_substitutions_.push_back(value_subst);
			template_type_parameter_packs_.push_back(set<string>());
			function_parameter_pack_substitutions_.push_back(function_subst);
			pos_ = begin;
			Expr elem = parse_assignment_expression();
			if (pos_ != end)
				throw runtime_error("pack expression replay did not consume pattern");
			expanded.push_back(elem);
			function_parameter_pack_substitutions_.pop_back();
			template_type_substitutions_.pop_back();
			template_value_substitutions_.pop_back();
			template_type_parameter_packs_.pop_back();
		}
	}
	catch (...)
	{
		pos_ = save_pos;
		template_type_substitutions_ = save_type_subst;
		template_value_substitutions_ = save_value_subst;
		template_type_parameter_packs_ = save_pack_subst;
		function_parameter_pack_substitutions_ = save_function_pack_subst;
		throw;
	}
	pos_ = save_pos;
	template_type_substitutions_ = save_type_subst;
	template_value_substitutions_ = save_value_subst;
	template_type_parameter_packs_ = save_pack_subst;
	function_parameter_pack_substitutions_ = save_function_pack_subst;
	out.swap(expanded);
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
	size_t save_pos = pos_;
	bool hide_current_ellipsis = at(OP_DOTS);
	if (hide_current_ellipsis)
		++pos_;
	try
	{
		for (size_t i = 0; i < pack_size; ++i)
		{
			vector<Expr> element_args;
			for (size_t j = 0; j < args.size(); ++j)
				element_args.push_back(expression_pack_element(args[j], i));
			Expr elem =
				make_call_expr(expression_pack_element(*effective_callee, i),
				               element_args);
			if (i == 0)
			{
				out.type = elem.type;
				out.category = elem.category;
			}
			out.pack.push_back(elem);
			add_child(out.node, elem.node);
		}
	}
	catch (...)
	{
		if (hide_current_ellipsis)
			pos_ = save_pos;
		throw;
	}
	if (hide_current_ellipsis)
		pos_ = save_pos;
	if (pack_size == 0)
	{
		out.type = replaying_dependent_decltype_
			? pa11::make_fundamental(FT_INT)
			: pa11::make_dependent_typename_type("__dependent_call",
			                                     false,
			                                     false,
			                                     false);
		out.category = ValueCategory::PRValue;
	}
	annotate_expr_node(out);
	return true;
}

}  // namespace internal
}  // namespace pa12
